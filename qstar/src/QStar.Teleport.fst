module QStar.Teleport
open Steel.ST.Util
open QStar.Steel.Util
open QStar.Vec
module M = QStar.Matrix
open QStar.Ref
#push-options "--ide_id_info_off"

(*
operation Entangle (qAlice : Qubit, qBob : Qubit) : Unit is Adj {
    H(qAlice);
    CNOT(qAlice, qBob);
} 
*)
let entangle (qA:qbit) (qB:qbit)
  : STT unit
        (pts_to (single qA) (singleton _ false) `star` 
         pts_to (single qB) (singleton _ false))
        (fun _ -> pts_to (double qA qB) (bell00 qA qB))
  = apply_gate (hadamard qA);
    let _ = gather (single qA) (single qB) #_ #_ in
    apply_gate (cnot qA qB);
    lemma_bell00 qA qB;
    rewrite (pts_to _ _)
            (pts_to (double qA qB) (bell00 qA qB))

let opt_apply #qs (b:bool) (g:gate qs) (s:qvec qs) : qvec qs
  = if b then apply g s else s

let size_union (s0 s1:qbits)
  : Lemma (requires disjoint s0 s1)
          (ensures size (union s0 s1) == size s0 + size s1)
          [SMTPat (size (union s0 s1))]
  = admit() //TODO: need to add this to the OrdSet library

let rewrite_set #o #qs1 (#state:qvec qs1) (qs2:qbits{equal qs1 qs2})
  : STGhostT unit o
    (pts_to qs1 state)
    (fun _ -> pts_to qs2 state)
  = rewrite _ _ 

(*
operation SendMsg (qAlice : Qubit, qMsg : Qubit)
: (Bool, Bool) {
    Adjoint Entangle(qMsg, qAlice);
    let m1 = M(qMsg);
    let m2 = M(qAlice);
    return (m1 == One, m2 == One);
}
*)

let send_msg_lemma (qs:qbits) 
                   (qB:qbit) 
                   (qA:qbit{qA <> qB}) 
                   (qM:qbit{qM <> qA /\ qM <> qB /\ disjoint (triple qA qB qM) qs}) 
                   (state:qvec (single qM `union` qs))
                   (b1 b2 : bool)
  : Lemma 
    (let qs0 = proj_and_disc qA b2
                      (proj_and_disc qM b1
                          (apply (lift (single qM)
                                  (union (double qA qB) qs)
                                  (hadamard qM))
                              (coerce_qvec
                              (apply (lift (double qM qA)
                                      (union (single qB) qs)
                                      (cnot qM qA))
                                  (coerce_qvec (tensor (bell00 qA qB) state)))))) in
     let qs1 = opt_apply b1 (lift (single qB) qs (pauli_z _)) 
                            (opt_apply b2 (lift (single qB) qs (pauli_x _)) 
                                          (relabel_indices _ state)) in
    coerce_qvec qs0 == qs1)
  = admit()


#push-options "--fuel 0 --ifuel 1"
val send_msg (#qs:qbits) 
             (#qB:qbit) 
             (qA:qbit) 
             (qM:qbit { qA <> qB /\ 
                        qM <> qA /\ //these are ugly
                        qM <> qB /\ //we have them from the *
                        disjoint (triple qA qB qM) qs })
             (#state:qvec (single qM `union` qs))
  : STT (bool * bool)
        (pts_to (single qM `union` qs) state `star`
         pts_to (double qA qB) (bell00 qA qB))
        (fun bits ->
           let b1 = fst bits in
           let b2 = snd bits in
           pts_to (single qM) (singleton _ b1) `star`
           pts_to (single qA) (singleton _ b2) `star`
           pts_to (single qB `union` qs)
                  (opt_apply b1 (lift (single qB) qs (pauli_z _)) 
                             (opt_apply b2 (lift (single qB) qs (pauli_x _)) 
                                           (relabel_indices _ state))))
let send_msg #qs #qB qA qM #state
  = gather (double qA qB) (single qM `union` qs) #_ #_;
    rewrite_set (double qM qA `union` (single qB `union` qs));
    apply_gate (lift (double qM qA) _ (cnot qM qA));
    rewrite_set (single qM `union` (double qA qB `union` qs));
    apply_gate (lift _ _ (hadamard qM));
    rewrite_set (double qM qA `union` (single qB `union` qs));
    let bits = measure2 qM qA _ _ in
    send_msg_lemma qs qB qA qM state (fst bits) (snd bits);
    rewrite (pts_to (single qB `union` qs) _) _;
    return bits

let apply_if (b:bool) (#qs:qbits) (#s:qvec qs) (g:gate qs)
  : STT unit
    (pts_to qs s)
    (fun _ -> pts_to qs (opt_apply b g s))
  = if b returns STT unit (pts_to qs s) (fun _ -> pts_to qs (opt_apply b g s))
    then apply_gate g
    else (noop (); return ())
    
// operation DecodeMsg (qBob : Qubit, (b1 : Bool, b2 : Bool))
// : Unit {
//     if b1 { Z(qBob); }
//     if b2 { X(qBob); }
// }
// *)
let decode_msg (qB:qbit) 
               (qs:qbits { disjoint (single qB) qs })
               (#state:qvec (single qB `union` qs))
               (bits:bool * bool)
  : STT unit
        (pts_to (single qB `union` qs) state)
        (fun _ -> pts_to (single qB `union` qs) 
                      (opt_apply (snd bits) 
                                 (lift (single qB) qs (pauli_x _))
                                 (opt_apply (fst bits) 
                                            (lift (single qB) qs (pauli_z _))
                                            state)))
  = apply_if (fst bits) (lift (single qB) qs (pauli_z _));
    apply_if (snd bits) (lift (single qB) qs (pauli_x _))

let teleport_lemma (b1 b2:bool)
                   (qB: qbit)
                   (qs: qbits {disjoint (single qB) qs })
                   (s: qvec (union (single qB) qs))
  : Lemma (opt_apply b2 (lift (single qB) qs (pauli_x qB))
                        (opt_apply b1 (lift (single qB) qs (pauli_z qB))
                                      (opt_apply b1 (lift (single qB) qs (pauli_z qB))
                                                    (opt_apply b2 (lift (single qB) qs (pauli_x qB))
                                                                  s))) ==
           s)
  = admit()           
                                                                  
(*
// operation Teleport (qMsg : Qubit, qBob : Qubit)
// : Unit {
//     use qAlice = Qubit();
//     Entangle(qAlice, qBob);
//     let classicalBits = SendMsg(qAlice, qMsg);
//     DecodeMsg(qBob, classicalBits);
// }
// *)
let teleport (#qs:qbits) 
             (qM:qbit{disjoint (single qM) qs}) 
             (#state:qvec (union (single qM) qs)) 
             (qB:qbit{qB <> qM /\ disjoint (single qB) qs})
  : STT unit
        (pts_to (union (single qM) qs) state `star` 
         pts_to (single qB) (singleton _ false))
        (fun _ -> pts_to (union (single qB) qs) 
                      (relabel_indices _ state))
  = let qA = alloc () in
    (* this is a bit ugly, since our specs have explicit disjointnes 
       constraints in them rather than relying just on `star` *)
    disjointness (single qA) #_ (single qB) #_;
    disjointness (single qA) #_ (union _ _) #_;    
    entangle qA qB;
    let bits = send_msg qA qM #_ in
    decode_msg qB qs bits;
    discard qA _;
    discard qM _; //qM is discardable too
    teleport_lemma (fst bits) (snd bits) qB qs (relabel_indices (union (single qB) qs) state);
    rewrite (pts_to (union (single qB) qs) _)
            (pts_to (union (single qB) qs) (relabel_indices (union (single qB) qs) state))


