module QStarRef
open Steel.ST.Util
open QStar.Steel.Util
open QVec
open QStarHeap
module M = Matrix
#push-options "--ide_id_info_off"

val pts_to (qs:qbits) ([@@@smt_fallback]state:qvec qs) : vprop

val apply_gate (#qs:qbits) (#state:qvec qs) (g:gate qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (apply g state))

val share (#o:_) (qs:qbits) (qs':qbits{ disjoint_qbits qs qs' }) (#state:qvec qs) (#state':qvec qs')
  : STGhostT unit o
    (pts_to (qs `OrdSet.union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')

val gather (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhostT (_:unit{disjoint_qbits qs qs'}) o
    (pts_to qs state `star` pts_to qs' state')
    (fun _ -> pts_to (qs `OrdSet.union` qs') (state `tensor` state'))

val measure (#qs:qbits)
            (q:qbit{ q `OrdSet.mem` qs })
            (state:qvec qs)
  : STT (b:bool { Some? (proj q b state) })
    (pts_to qs state)
    (fun b -> pts_to (single q) (singleton q b) `star`
           pts_to (qs `OrdSet.minus` (single q)) (disc q b state))

val alloc (_:unit)
  : STT qbit emp (fun q -> pts_to (single q) (singleton q false))

val discard (q:qbit) (qstate:qvec (single q))
  : STT unit (pts_to (single q) qstate) (fun _ -> emp)

let test1 (_:unit)
  : STT unit emp (fun _ -> emp)
  = //allocate a qbit q in |0>
    let q = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (apply (hadamard q) (apply (hadamard q) (singleton q false))));
    //call the lemma below, and prove that q is actually back to |0>
    hadamard_self_adjoint q;
    rewrite (pts_to (single q) _)
            (pts_to (single q) (singleton q false)); //use hadamard_self_adjoint to prove 
                                                     //that q is back to its initial state
    //discard it
    discard q _

// same as test1, but now with some other qbit around
let test2 (_:unit)
  : STT qbit emp (fun q1 -> pts_to (single q1) (apply (hadamard _) (singleton _ false)))
  = //allocate a qbit q in |0>
    let q = alloc () in
    let q1 = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (apply (hadamard q) (apply (hadamard q) (singleton q false))));
    //call the lemma below, and prove that q is actually back to |0>
    hadamard_self_adjoint q;
    rewrite (pts_to (single q) _)
            (pts_to (single q) (singleton q false)); //use hadamard_self_adjoint to prove 
                                                     //that q is back to its initial state
    //discard it
    discard q _;
    apply_gate (hadamard q1);
    return q1

// returning more than one qbit
let test3 (_:unit)
  : STT (qbit * qbit) emp 
        (fun qs -> pts_to (single (fst qs)) (singleton _ false) `star`
                pts_to (single (snd qs)) (singleton _ false))
  = //allocate a qbit q in |0>
    let q0 = alloc () in
    let q1 = alloc () in
    let res = q0, q1 in
    // This is kinda ugly, but Steel currently forces you to do this kind of rewrite
    // and doesn't implicitly convert (pts_to (single q0) _) to (pts_to (single (fst res)) _)
    rewrite (pts_to (single q0) _)
            (pts_to (single (fst res)) (singleton _ false));
    rewrite (pts_to (single q1) _)
            (pts_to (single (snd res)) (singleton _ false));            
    return res

// returning more than one qbit after gathering them
let test4 (_:unit)
  : STT (qbit * qbit)
        emp
        (fun qs -> exists_ (fun state -> 
                   pts_to (OrdSet.union (single (fst qs)) (single (snd qs))) state `star`
                   pure (fst qs =!= snd qs /\
                         state == (singleton (fst qs) false `tensor` singleton (snd qs) false))))
  = //allocate a qbit q in |0>
    let q0 = alloc () in
    let q1 = alloc () in
    let _ = gather (single q0) (single q1) #_ #_ in
    let res = (q0, q1) in
    rewrite (pts_to _ _)
            (pts_to (OrdSet.union (single (fst res)) (single (snd res)))
                    (singleton (fst res) false `tensor` singleton (snd res) false));
    (* This is super verbose, but once F* PR  2553 is merged, this should be automated *)
    intro_pure (fst res =!= snd res /\
               ((singleton (fst res) false `tensor` singleton (snd res) false) ==
                (singleton (fst res) false `tensor` singleton (snd res) false)));
    intro_exists (singleton (fst res) false `tensor` singleton (snd res) false)
                 (fun state -> 
                   pts_to (OrdSet.union (single (fst res)) (single (snd res))) state `star`
                   pure (fst res =!= snd res /\
                         state == (singleton (fst res) false `tensor` singleton (snd res) false)));
    return res

(*
operation Entangle (qAlice : Qubit, qBob : Qubit) : Unit is Adj {
    H(qAlice);
    CNOT(qAlice, qBob);
} 
*)
let entangle (qA:qbit) (qB:qbit{qA <> qB})
  : STT unit
        (pts_to (single qA) (singleton _ false) `star` 
           pts_to (single qB) (singleton _ false))
        (fun _ -> pts_to (double qA qB) (bell00 qA qB))
  = apply_gate (hadamard qA);
    gather (single qA) (single qB) #_ #_;
    apply_gate (cnot qA qB);
    lemma_bell00 qA qB;
    rewrite (pts_to _ _)
            (pts_to (double qA qB) (bell00 qA qB))

(*
operation SendMsg (qAlice : Qubit, qMsg : Qubit)
: (Bool, Bool) {
    Adjoint Entangle(qMsg, qAlice);
    let m1 = M(qMsg);
    let m2 = M(qAlice);
    return (m1 == One, m2 == One);
}
*)
let send_msg (#qs:_) (qA:qbit) (qM:qbit{qA <> qM}) (#state:_)
  : STT (bool * bool)
        (pts_to ((double qA qM) `OrdSet.union` qs) state)
        (fun bits -> let (b1, b2) = bits in
                  pts_to (single qM) (singleton _ b1) `star`
                  pts_to (single qA) (singleton _ b2))
                  //pts_to qs (disc qA b2 (disc qM b1 (apply (cnot qM qA) (apply (hadamard qA) state)))))
  = //CNOT(qM, qA);
    //H(qM);
    //let b1 = measure qM in
    //let b2 = measure qA in
    //return (b1, b2)
    admit__ ()

(*
operation DecodeMsg (qBob : Qubit, (b1 : Bool, b2 : Bool))
: Unit {
    if b1 { Z(qBob); }
    if b2 { X(qBob); }
}
*)
let decode_msg (qB:qbit) (#state:_) (bits:bool * bool) // why does state need to come after qB?
  : STT unit
        (pts_to (single qB) state)
        (fun _ -> pts_to (single qB) 
                 (let (b1, b2) = bits in
                  if b1
                  then 
                    if b2 
                    then apply (pauli_x _) (apply (pauli_z _) state) 
                    else apply (pauli_z _) state 
                  else 
                    if b2 
                    then apply (pauli_x _) state 
                    else state))
  = //let (b1, b2) = bits in
    //if b1 then apply_gate (pauli_z qB);
    //if b2 then apply_gate (pauli_x qB)
    admit__ ()

(*
operation Teleport (qMsg : Qubit, qBob : Qubit)
: Unit {
    use qAlice = Qubit();
    Entangle(qAlice, qBob);
    let classicalBits = SendMsg(qAlice, qMsg);
    DecodeMsg(qBob, classicalBits);
}
*)
let teleport (qM:qbit) (#state:qvec _) (qB:qbit)
  : STT unit
        (pts_to (single qM) state `star` 
         pts_to (single qB) (singleton _ false))
        (fun _ -> pts_to (single qB) state)
  = //let qA = alloc () in
    //entangle qA qB;
    //let bits = send_msg qA qM in
    //decode_msg qB bits;
    //discard qA _
    admit__ ()
