module QStar.Vec

open QStar.Complex
open QStar.Quantum
open QStar.Matrix
open FStar.Real
module Matrix = QStar.Matrix

(* This module defines our representation of quantum states, operations 
   acting on quantum states, and predicates for describing quantum
   states. *)

let qbit : eqtype = nat

let qbits = OrdSet.ordset qbit (<=)

let empty_qbits : qbits = OrdSet.empty

let disjoint (q0 q1:qbits) = (OrdSet.intersect q0 q1 `OrdSet.equal` empty_qbits)

let equal (q0 q1:qbits) = OrdSet.equal q0 q1
let union (q0 q1:qbits) : qbits = match q0 with _ -> OrdSet.union q0 q1

let dimension (qs:qbits) = pow2 (OrdSet.size qs)

// TODO: add restriction of unit norm?
[@@unifier_hint_injective]
val qvec (qs:qbits) : Type u#0 // = matrix complex (dimension qs) 1

val empty_qvec : qvec empty_qbits // = id_matrix complex 1

let qvec_equiv (#qs #qs':qbits) (qv:qvec qs) (qv':qvec qs') =
   qs `equal` qs' /\
   qv == qv'

let union_empty (q:qbits)
  : Lemma (union q empty_qbits `equal` q)
          [SMTPat (union q empty_qbits)]
  = ()
  
let union_ac (_:unit)
  : Lemma ((forall (qs0 qs1 qs2:qbits).
              union qs0 (union qs1 qs2) `equal` union (union qs0 qs1) qs2) /\
           (forall (qs0 qs1:qbits).
              union qs0 qs1 `equal` union qs1 qs0) /\
           (forall (q:qbits). union q empty_qbits `equal` q))
  = ()

let union_assoc (qs0 qs1 qs2:qbits)
  : Lemma (union qs0 (union qs1 qs2) `equal` union (union qs0 qs1) qs2)
  = ()

// Can we define tensor over any qs0 qs1, 
// and like proj it is meaingless with qs0 and qs1 are not disjoint
val tensor (#qs0:qbits)
           (#qs1:qbits)
           (v0:qvec qs0)
           (v1:qvec qs1)
  : qvec (union qs0 qs1)

val tensor_unit (qs:qbits) (v:qvec qs)
  : Lemma
    (ensures tensor v empty_qvec `qvec_equiv` v)

val tensor_comm (qs0 qs1:qbits) (v0:qvec qs0) (v1:qvec qs1)
  : Lemma
    (requires disjoint qs0 qs1)
    (ensures tensor v0 v1 `qvec_equiv` tensor v1 v0)

val tensor_assoc_l (#qs0:_)
                   (#qs1:_{disjoint qs0 qs1})
                   (#qs2:_{disjoint (union qs0 qs1) qs2})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (tensor (tensor v0 v1) v2 `qvec_equiv` tensor v0 (tensor v1 v2))

val tensor_assoc_r (#qs0:_)
                   (#qs1:_)
                   (#qs2:_{disjoint qs1 qs2 /\ disjoint qs0 (union qs1 qs2)})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (tensor (tensor v0 v1) v2 `qvec_equiv` tensor v0 (tensor v1 v2))

let single (q:qbit) : qbits = match q with _ -> OrdSet.singleton q

val singleton (q:qbit) (b:bool) : qvec (single q) // = ket b

let double (q1:qbit) (q2:qbit) : qbits = union (single q1) (single q2)

let triple (q1:qbit) (q2:qbit) (q3:qbit) : qbits =
  union (double q1 q2) (single q3)

let mem (q:qbit) (qs:qbits) : bool = OrdSet.mem q qs

// Can we define this even when q is not a mem in qs?
val proj (#qs:qbits)
         (q:qbit)
         (b:bool)
         (s:qvec qs)
  : qvec qs

let minus (qs0:qbits) (qs1:qbits) : qbits = OrdSet.minus qs0 qs1

val disc (#qs:qbits)
         (q:qbit)
         (s:qvec qs)
  : qvec (qs `minus` (single q))

let proj_and_disc (#qs:qbits)
                  (q:qbit)
                  (b:bool)
                  (s:qvec qs)
   : qvec (qs `minus` (single q))
   = disc q (proj q b s)

let size (qs:qbits) : nat = OrdSet.size qs
val relabel_indices : (#qs1:qbits) -> (qs2:qbits{size qs1 == size qs2}) -> 
                      qvec qs1 -> qvec qs2

val gate (qs:qbits) : Type0

val hadamard : (q:qbit) -> gate (single q)

val pauli_x : (q:qbit) -> gate (single q)

val pauli_z : (q:qbit) -> gate (single q)

val cnot : (q1:qbit) -> (q2:qbit{q1 <> q2}) -> gate (double q1 q2)

val apply : (#qs:qbits) -> gate qs -> qvec qs -> qvec qs

val lift : (qs:qbits) -> (qs':qbits) -> 
           gate qs -> gate (qs `union` qs')

val lift_preserves_frame (qs:qbits) (qs':qbits{qs' `disjoint` qs}) (g:gate qs) 
                         (v : qvec qs) (v' : qvec qs')
  : Lemma (ensures ((apply (lift qs qs' g) (v `tensor` v')) `qvec_equiv` (apply g v `tensor` v')))

let self_adjoint (#qs:qbits) (g: gate qs) =
  forall (s:qvec qs). apply g (apply g s) `qvec_equiv` s

val hadamard_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (hadamard q))

val pauli_x_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_x q))

val pauli_z_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_z q))

val cnot_self_adjoint (q1:qbit) (q2:qbit{q1 <> q2})
  : Lemma (ensures self_adjoint (cnot q1 q2))

/// Abstractions for defining vector states

val scale (#qs:qbits) (c:complex) (v:qvec qs) : qvec qs

val plus (#qs:qbits) (v1:qvec qs) (v2:qvec qs) : qvec qs

val build_vec (qs:qbits) (data:qbit -> bool) : qvec qs

val bell00 (q1:qbit) (q2:qbit) : qvec (double q1 q2)
  // scale (of_real (1.0R /. sqrt_2)) 
  //       ((build_vec _ (fun _ -> false)) `plus` (build_vec _ (fun _ -> true)))

val lemma_bell00 (q1:qbit) (q2:qbit{q1 <> q2}) 
  : Lemma (apply (cnot q1 q2) 
                 ((apply (hadamard q1) (singleton q1 false)) `tensor` 
                    (singleton q2 false))
           == bell00 q1 q2)
