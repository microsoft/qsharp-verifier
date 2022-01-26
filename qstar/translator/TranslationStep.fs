namespace QStar.Translator

open Microsoft.Quantum.QsCompiler
open Microsoft.Quantum.QsCompiler.ReservedKeywords
open System
open System.Collections.Generic
open System.IO

module private TranslationStep =
    let moduleContent name declarations =
        "// Auto-generated from "
        + name
        + ".qs"
        + (String.replicate 2 Environment.NewLine)
        + "module "
        + name
        + (String.replicate 2 Environment.NewLine)
        + """open FStar.Mul
open QInst
open QMap
open QState"""
        + (String.replicate 2 Environment.NewLine)
        + (declarations
           |> String.concat (String.replicate 2 Environment.NewLine))

type TranslationStep() =
    interface IRewriteStep with
        member val AssemblyConstants = Dictionary() :> IDictionary<_, _>

        member _.GeneratedDiagnostics = Seq.empty

        member _.ImplementsPostconditionVerification = false

        member _.ImplementsPreconditionVerification = false

        member _.ImplementsTransformation = true

        member _.Name = typeof<TranslationStep>.FullName

        member _.PostconditionVerification _ = true

        member _.PreconditionVerification _ = true

        member _.Priority = 0

        member step.Transformation(compilation, compilation') =
            let translator = Translator.create ()
            translator.OnCompilation compilation |> ignore

            let outputDir =
                Path.Combine((step :> IRewriteStep).AssemblyConstants.[AssemblyConstants.OutputPath], "..", "QStar")

            Directory.CreateDirectory outputDir |> ignore

            for file in translator.SharedState do
                let path =
                    Path.Combine(outputDir, Path.ChangeExtension(file.Key, "fst"))

                let content =
                    TranslationStep.moduleContent file.Key file.Value

                File.WriteAllText(path, content + Environment.NewLine)

            compilation' <- compilation
            true
