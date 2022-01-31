module Demo

open QInst
open QMap
open QState

(* ************************

Q# program:

    operation PrepareBell (q1 : Qubit, q2 : Qubit) : Unit is Adj {
        H(q1); CNOT(q1, q2);
    }
    
************************ *)

// Generated instruction tree
let prepareBell (q1 : qref) (q2 : qref)
  : inst_tree unit 
        (fun s0 -> q1 <> q2 /\ live s0 q1 /\ live s0 q2) 
        eqpost
  = Weaken _ _ () ()
      (Action (had q1) (fun _ ->
        Action (cnot q1 q2) (fun _ ->
          Return eqpost ())))

(* ************************

Q# program:

    operation Reset (q : Qubit) : Unit {
        let res = M(q);
        if res == One {
            X(q);
        }
    }

************************ *)

// Generated instruction tree
let reset (q: qref) : inst_tree unit (fun s0 -> live s0 q) eqpost =
  Weaken _ _ () ()
    (Action (meas q) (fun res ->
      if res = One
      then Weaken _ _ () () (Action (pauli_x q) (fun _ -> Return eqpost ()))
      else Weaken (fun s0 -> live s0 q) eqpost () () (Return eqpost ())))

(* ************************

Q# program:

    operation BadExample1 () : Unit {
        use q = Qubit();
        CNOT(q, q);
    }
    
************************ *)

// Generated instruction tree (won't typecheck!)
[@@expect_failure [19]] 
let badExample1 ()
  : inst_tree unit trivpre eqpost
  =
Weaken _ _ () ()
  (using trivpre eqpost (fun q ->
    Weaken _ _ () ()
      (Action (cnot q q) (fun _ ->
        Return eqpost ()))))

(* ************************

Q# program:

    operation InitQubit () : Qubit {
        use q = Qubit();
        return q;
    }

    operation BadExample2 () : Unit {
        let q = InitQubit ();
        X(q);
    }

************************ *)

// Generated instruction tree (won't typecheck!)
let initQubit ()
  : inst_tree (qref) trivpre eqpost
  =
Weaken _ _ () ()
  (using trivpre eqpost (fun q ->
    Weaken _ _ () ()
      (Return eqpost q)))

[@@expect_failure [19]] 
let badExample2 ()
  : inst_tree unit (fun _ -> True) eqpost
  =
Weaken _ _ () ()
  (bind (initQubit ()) (fun q ->
    Action (pauli_x q) (fun _ ->
      Return eqpost ())))

(* ************************

Q# program:

    operation Teleport(src: Qubit, target: Qubit) : Unit {
        use a = Qubit();

        // Entangle
        PrepareBell(a, target);

        // Encode
        CNOT(src, a);
        H(src);
        let m1 = M(src);
        let m2 = M(a);

        // Decode
        if (m2 == One) { X(target); }
        if (m1 == One)  { Z(target); }
    }

************************ *)

let teleport (src tgt: qref)
    : inst_tree unit (fun s0 -> src <> tgt /\ live s0 src /\ live s0 tgt) eqpost =
  Weaken _ _ () ()
    (using 
      (fun s0 -> src <> tgt /\ live s0 src /\ live s0 tgt)
      eqpost (fun a ->
      Weaken _ _ () ()
        (bind (prepareBell a tgt) (fun _ ->
          Action (cnot src a) (fun _ ->
            Action (had src) (fun _ ->
              Action (meas src) (fun m1 ->
                Action (meas a) (fun m2 ->
                  if m2 = One
                  then Weaken _ _ () ()
                         (Action (pauli_x tgt) (fun _ ->
                           if m1 = One
                           then Weaken _ _ () ()
                                  (Action (pauli_z tgt) (fun _ ->
                                    Return eqpost ()))
                           else Weaken (fun s0 -> src <> tgt /\ src <> a /\ tgt <> a /\ live s0 src /\ live s0 tgt /\ live s0 a) eqpost () ()
                                  (Return eqpost ())))
                  else Weaken (fun s0 -> src <> tgt /\ src <> a /\ tgt <> a /\ live s0 src /\ live s0 tgt /\ live s0 a) eqpost () ()
                         (if m1 = One
                          then Weaken _ _ () ()
                                 (Action (pauli_z tgt) (fun _ ->
                                   Return eqpost ()))
                          else Weaken (fun s0 -> src <> tgt /\ src <> a /\ tgt <> a /\ live s0 src /\ live s0 tgt /\ live s0 a) eqpost () ()
                                 (Return eqpost ()))))))))))

(* ************************

Q# program:

    // adapted from https://github.com/microsoft/QuantumLibraries/blob/main/Standard/src/Canon/And.qs
    operation ApplyAnd (control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            H(target);
            T(target);
            CNOT(control1, target);
            CNOT(control2, target);
            within {
                CNOT(target, control1);
                CNOT(target, control2);
            }
            apply {
                Adjoint T(control1);
                Adjoint T(control2);
                T(target);
            }
            H(target);
            S(target);
        }
        adjoint (...) {
            H(target);
            let res = M(target);
            Reset(target);
            if (res == One) {
                H(control2);
                CNOT(control1, control2);
                H(control2);
            }
        }
    }
    
************************ *)

let applyAnd (ctl1 ctl2 tgt: qref)
    : inst_tree unit
      (fun s0 -> ctl1 <> ctl2 /\ ctl1 <> tgt /\ ctl2 <> tgt /\ live s0 ctl1 /\ live s0 ctl2 /\ live s0 tgt)
      eqpost =
  Weaken _ _ () ()
    (Action (had tgt) (fun _ ->
      Action (t_rot tgt) (fun _ ->
        Action (cnot ctl1 tgt) (fun _ ->
          Action (cnot ctl2 tgt) (fun _ ->
             Action (cnot tgt ctl1) (fun _ ->
               Action (cnot tgt ctl2) (fun _ ->
                 Action (get_adj (t_rot ctl1)) (fun _ ->
                   Action (get_adj (t_rot ctl2)) (fun _ ->
                     Action (t_rot tgt) (fun _ ->
                       Action (get_adj (cnot tgt ctl2)) (fun _ ->
                         Action (get_adj (cnot tgt ctl1)) (fun _ ->
                           Action (had tgt) (fun _ ->
                             Action (s_rot tgt) (fun _ ->
                               Return eqpost ()))))))))))))))

let applyAnd_adjoint (ctl1 ctl2 tgt: qref)
    : inst_tree unit
      (fun s0 -> ctl1 <> ctl2 /\ ctl1 <> tgt /\ ctl2 <> tgt /\ live s0 ctl1 /\ live s0 ctl2 /\ live s0 tgt)
      eqpost =
  Weaken _ _ () ()
    (Action (had tgt) (fun _ ->
      Action (meas tgt) (fun res ->
        bind (reset tgt) (fun _ ->
          if res = One
          then Weaken _ _ () ()
                 (Action (had ctl2) (fun _ ->
                   Action (cnot ctl1 ctl2) (fun _ -> 
                     Action (had ctl2) (fun _ -> 
                       Return eqpost ()))))
          else Weaken (fun s0 -> ctl1 <> ctl2 /\ ctl1 <> tgt /\ ctl2 <> tgt /\ live s0 ctl1 /\ live s0 ctl2 /\ live s0 tgt) eqpost () ()
                 (Return eqpost ())))))




/// A few test examples (in-progress)

[@@expect_failure [19]]
let initQubit' ()
  : inst_tree qref trivpre (fun v s0 s1 -> s0 == s1 /\ live s0 v)
  =
Weaken _ _ () ()
  (using trivpre (fun v s0 s1 -> s0 == s1 /\ live s0 v) (fun q ->
    Weaken _ _ () ()
      (Return eqpost q)))

let returnQubit (qIn : qref)
  : inst_tree qref (fun s0 -> live s0 qIn) (fun v s0 s1 -> s0 == s1 /\ live s0 v)
  =
Weaken _ _ () ()
  (Return (fun v s0 s1 -> s0 == s1 /\ live s0 v) qIn)

let flipCoin ()
  : inst_tree result trivpre eqpost
  =
Weaken _ _ () ()
(using trivpre eqpost (fun q ->
Weaken _ _ () ()
(Action (had q) (fun _ ->
Action (meas q) (fun res ->
Return eqpost res)))))

let returnQubit' (qIn : qref)
  : inst_tree qref (fun s0 -> live s0 qIn) (fun v s0 s1 -> s0 == s1 /\ live s0 v)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 qIn) (fun v s0 s1 -> s0 == s1 /\ live s0 v) (fun q ->
    Weaken _ _ () ()
      (return (fun v s0 s1 -> s0 == s1 /\ live s0 v) qIn)))

let usingWithBind (q : qref)
  : inst_tree qref (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun _ ->
    Weaken _ _ () ()
      (bind (flipCoin ()) (fun res ->
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)))))

let chooseQubit (q1 q2 : qref)
  : inst_tree qref (fun s0 -> live s0 q1 /\ live s0 q2) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (bind (flipCoin ()) (fun res ->
    cond 
    (fun s0 -> live s0 q1 /\ live s0 q2) 
    (fun v s0 s1 -> live s1 v /\ s0 == s1)
    (res = Zero)
    (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q1)
    (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q2)))

[@@expect_failure [19]]
let possiblyInitQubit (q : qref)
  : inst_tree qref (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun qNew ->
    Weaken _ _ () ()
      (bind (flipCoin ()) (fun res ->
        cond 
        (fun s0 -> live s0 q) 
        (fun v s0 s1 -> live s1 v /\ s0 == s1)
        (res = Zero)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) qNew)))))

let possiblyInitQubit (q : qref)
  : inst_tree qref (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun qNew ->
    Weaken _ _ () ()
      (bind (flipCoin ()) (fun res ->
        cond 
        (fun s0 -> live s0 q) 
        // @Nik: how can we get rid of the v == q?
        (fun v s0 s1 -> live s1 v /\ s0 == s1 /\ v == q)
        (res = Zero)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)))))


let possiblyInitQubit' (q : qref)
  : inst_tree qref (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun qNew ->
    Weaken _ _ () ()
      (bind (flipCoin ()) (fun res ->
        cond' 
        (res = Zero)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)
        (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q)))))

let chooseQubitWithInit (q1 q2 : qref)
  : inst_tree qref (fun s0 -> live s0 q1 /\ live s0 q2) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q1 /\ live s0 q2) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun qNew ->
    Weaken _ _ () () (bind (flipCoin ()) (fun res ->
      cond 
      (fun s0 -> live s0 q1 /\ live s0 q2) 
      // @Nik: same as above, I'd rather the (v == q1 \/ v == q2) not be there
      (fun v s0 s1 -> live s1 v /\ s0 == s1 /\ (v == q1 \/ v = q2))
      (res = Zero)
      (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q1)
      (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q2)))))


let chooseQubitWithInit' (q1 q2 : qref)
  : inst_tree qref (fun s0 -> live s0 q1 /\ live s0 q2) (fun v s0 s1 -> live s1 v /\ s0 == s1)
  =
Weaken _ _ () ()
  (using (fun s0 -> live s0 q1 /\ live s0 q2) (fun v s0 s1 -> live s1 v /\ s0 == s1) (fun qNew ->
    Weaken _ _ () () (bind (flipCoin ()) (fun res ->
      cond' 
      (res = Zero)
      (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q1)
      (return (fun v s0 s1 -> live s1 v /\ s0 == s1) q2)))))
