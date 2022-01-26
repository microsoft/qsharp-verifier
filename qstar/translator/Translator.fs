namespace QStar.Translator

open Microsoft.Collections.Extensions
open Microsoft.Quantum.QsCompiler.DataTypes
open Microsoft.Quantum.QsCompiler.SyntaxTokens
open Microsoft.Quantum.QsCompiler.SyntaxTree
open Microsoft.Quantum.QsCompiler.Transformations.Core
open System
open System.IO

type internal ModuleName = string
type internal Declaration = string
type internal Translations = MultiValueDictionary<ModuleName, Declaration>

module private OperationTranslator =
    let private lowerCaseFirst (s: string) =
        if String.IsNullOrEmpty s then
            ""
        else
            string (Char.ToLower s.[0]) + s.[1..]

    let private specSuffix =
        function
        | QsBody -> ""
        | QsAdjoint -> "_adjoint"
        | QsControlled -> "_controlled"
        | QsControlledAdjoint -> "_controlled_adjoint"

    let private fail x = 
        failwith (sprintf "Translation error - Conversion to F* does not support %A" x)

    let rec translateType (ty : ResolvedType) =
        match ty.Resolution with
        | UnitType -> "unit"
        | Bool -> "bool"
        | Qubit -> "qref"
        | Result -> "result"
        | TupleType args -> Seq.map translateType args |> String.concat " & "
        | x -> fail x

    let getName (sym : QsLocalSymbol) =
        match sym with
        | ValidName x -> x
        | x -> fail x

    let translateParams (args : seq<LocalVariableDeclaration<QsLocalSymbol>>) =
        if Seq.isEmpty args
        then "()"
        else (Seq.map (fun x -> sprintf "(%s : %s)" (getName x.VariableName) (translateType x.Type)) args
             |> String.concat " ")
    
    // TODO: bad practice to do recursion on seqs
    let rec distinctPairs (s : seq<'a>) =
        if Seq.isEmpty s
        then Seq.empty
        else
            let hd = Seq.head s 
            let tl = Seq.tail s
            Seq.append (Seq.allPairs (Seq.singleton hd) tl) (distinctPairs tl)

    let rec getQubitArgs (args : seq<LocalVariableDeclaration<QsLocalSymbol>>) =
        Seq.map (fun x -> getName x.VariableName) (Seq.filter (fun x -> x.Type.Resolution = Qubit) args)

    let private buildPre (qs : seq<String>) =
        if Seq.isEmpty qs
        then "fun _ -> True"
        else
            // liveness constraints
            let ls = Seq.map (fun x -> sprintf "live s0__ %s" x) qs
            // distinctness constraints
            let ds = Seq.map (fun (x,y) -> sprintf "%s <> %s" x y) (distinctPairs qs)
            sprintf "fun s0__ -> %s" (Seq.append ds ls |> String.concat " /\\ ")

    let translateIdentifier (id : Identifier) =
        match id with
        | LocalVariable s -> s
        | GlobalCallable x -> 
            match x.Name with
            | "H" -> "had"
            | "X" -> "pauli_x"
            | "Z" -> "pauli_z"
            | "T" -> "t_rot"
            | "S" -> "s_rot"
            | "CNOT" -> "cnot"
            | "CZ" -> "cz"
            | "M" -> "meas"
            | x -> lowerCaseFirst x
        | x -> fail x

    let rec translateExpression (e : TypedExpression) =
        match e.Expression with
        | UnitValue -> "()"
        | Identifier (id,_) -> translateIdentifier id
        | ValueTuple es -> sprintf "(%s)" (Seq.map translateExpression es |> String.concat ", ")
        | BoolLiteral true -> "true"
        | BoolLiteral false -> "false"
        | ResultLiteral One -> "One"
        | ResultLiteral Zero -> "Zero"
        | EQ (e1,e2) -> sprintf "%s = %s" (translateExpression e1) (translateExpression e2)
        | AdjointApplication e -> sprintf "adjoint %s" (translateExpression e) // TODO
        | CallLikeExpression (e1,e2) -> sprintf "%s %s" (translateExpression e1) (translateExpression e2)
        | x -> fail x

    let translateSymbolTuple (st : SymbolTuple) =
        match st with
        | VariableName x -> x
        | x -> fail x
    
    // different handling for instructions (like H) vs. user-defined functions (like Bell)
    let translateCallLikeExpression binder e1 e2 rest =
        let e2' = match e2.Expression with
                  | ValueTuple es -> Seq.map translateExpression es |> String.concat " "
                  | _ -> translateExpression e2
        match e1.Expression with
        | Identifier (id,_) -> 
            let e1' = translateIdentifier id
            match e1' with
            | "had" | "pauli_x" | "pauli_z" | "t_rot" | "s_rot" | "cnot" | "cz" | "meas" ->
              (sprintf "Action (%s %s) (fun %s ->" e1' e2' binder) + Environment.NewLine + sprintf "%s)" rest
            | _ -> (sprintf "bind (%s %s) (fun %s ->" e1' e2' binder) + Environment.NewLine + sprintf "%s)" rest
        | AdjointApplication e ->
            match e.Expression with
            | Identifier (id, _) ->
                let e1' = translateIdentifier id
                match e1' with
                | "had" | "pauli_x" | "pauli_z" | "t_rot" | "s_rot" | "cnot" | "cz" | "meas" ->
                  (sprintf "Action (get_adj (%s %s)) (fun %s ->" e1' e2' binder) + Environment.NewLine + sprintf "%s)" rest
                | _ -> (sprintf "bind (adjoint (%s %s)) (fun %s ->" e1' e2' binder) + Environment.NewLine + sprintf "%s)" rest
            | _ -> fail e1
        | _ -> fail e1
       
    let rec translateStatement (s : QsStatement) (pre : seq<String>) (rest : String) =
        match s.Statement with
        | QsExpressionStatement e -> 
            match e.Expression with
            | CallLikeExpression (e1,e2) -> translateCallLikeExpression "_" e1 e2 rest
            | x -> fail x
        | QsReturnStatement e -> 
            if rest <> ""
            then failwith "Translation error - no statements should come after return"
            else (sprintf "Return eqpost %s" (translateExpression e)) + rest
        | QsVariableDeclaration bin ->
            if bin.Kind = MutableBinding
            then fail bin
            else match bin.Rhs.Expression with
                 | CallLikeExpression (e1,e2) -> translateCallLikeExpression (translateSymbolTuple bin.Lhs) e1 e2 rest
                 | _ -> (sprintf "let %s = %s in" (translateSymbolTuple bin.Lhs) (translateExpression bin.Rhs))
                        // need a Weaken inside let (alternatively, we could move all lets outside of their Weaken...
                        // but this is a little harder)
                        + Environment.NewLine
                        + (sprintf "Weaken (%s) eqpost () ()" (buildPre pre))
                        + Environment.NewLine 
                        + sprintf "(%s)" rest
        | QsConditionalStatement cond -> 
            (Seq.map (fun (e, blk : QsPositionedBlock) -> 
                "if " + (translateExpression e) + Environment.NewLine 
                + "then " + (translateStatements blk.Body pre rest))
                cond.ConditionalBlocks 
            |> String.concat (Environment.NewLine + "else "))
            + match cond.Default with
              | Null -> Environment.NewLine + "else " 
                        + (sprintf "Weaken (%s) eqpost () ()" (buildPre pre)) + Environment.NewLine
                        + sprintf "(%s)" rest
              | Value blk -> Environment.NewLine + "else " 
                             + (sprintf "Weaken (%s) eqpost () ()" (buildPre pre)) + Environment.NewLine
                             + sprintf "(%s)" (translateStatements blk.Body pre rest)
        | QsQubitScope qsc ->
            if qsc.Kind = Borrow || qsc.Binding.Kind = MutableBinding || qsc.Binding.Rhs.Type.Resolution <> Qubit
            then fail qsc
            else 
                let q = translateSymbolTuple qsc.Binding.Lhs
                let pre' = Seq.append pre (Seq.singleton q)
                (sprintf "using (%s) eqpost (fun %s ->" (buildPre pre) (translateSymbolTuple qsc.Binding.Lhs))
                 + Environment.NewLine 
                 + sprintf "%s)" (translateStatements qsc.Body pre' rest)
        | x -> fail x

    and translateStatements (body : QsScope) (pre : seq<String>) (rest : String) =
        //(sprintf "Weaken (%s) eqpost () ()" (buildPre pre)) + Environment.NewLine
        "Weaken _ _ () ()" + Environment.NewLine
        + sprintf "(%s)" (Seq.foldBack (fun st acc -> translateStatement st pre acc) body.Statements rest)

    let translateBody (body : QsScope) (pre : seq<String>) (returnType : ResolvedType) =
        // TODO: check if a unit return statement is already present
        let rest = if returnType.Resolution = UnitType
                   then "Return eqpost ()" else ""
        translateStatements body pre rest

    let private translateSpec (spec: QsSpecialization) =
        match spec.Implementation with
        | Provided (args, body) ->         
            let parameters = translateParams args.Items
            let returnType = translateType spec.Signature.ReturnType
            let qs = getQubitArgs args.Items
            let precondition = buildPre qs
            let implementation = translateBody body qs spec.Signature.ReturnType

            sprintf """let %s%s %s
  : inst_tree (%s) (%s) eqpost
  =
%s"""
                (lowerCaseFirst spec.Parent.Name)
                (specSuffix spec.Kind)
                parameters
                returnType
                precondition
                implementation

        | x -> fail x

    let translate operation =
        operation.Specializations
        |> Seq.map translateSpec
        |> String.concat (String.replicate 2 Environment.NewLine)

type private NamespaceTranslator(parent: SyntaxTreeTransformation<_>) =
    inherit NamespaceTransformation<Translations>(parent, TransformationOptions.NoRebuild)

    override translator.OnOperation operation =
        if QsNullable.isNull operation.Source.AssemblyFile then
            let moduleName =
                Path.GetFileNameWithoutExtension operation.Source.CodeFile

            let translation = OperationTranslator.translate operation
            translator.SharedState.Add(moduleName, translation)

        operation

module internal Translator =
    let create () =
        let translator =
            SyntaxTreeTransformation<_>(MultiValueDictionary(), TransformationOptions.NoRebuild)

        translator.Namespaces <- NamespaceTranslator translator
        translator
