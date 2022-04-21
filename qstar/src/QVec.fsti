module QVec

open Complex
open Matrix
open FStar.Seq
open FStar.OrdSet

(* This module defines our representation of quantum states, operations 
   acting on quantum states, and predicates for describing quantum
   states. *)

let qbit = nat

let qbits = OrdSet.ordset qbit (<=)

let dimension (qs:qbits) = pow2 (OrdSet.size qs)

// TODO: add restriction of unit norm?
let qvec (qs:qbits) = matrix complex (dimension qs) 1

let empty_qbits : qbits = OrdSet.empty

let empty_qvec : qvec empty_qbits = id_matrix complex 1

let disjoint_qbits (q0 q1:qbits) = (OrdSet.intersect q0 q1 `OrdSet.equal` empty_qbits)

let union_empty (q:qbits)
  : Lemma (union q empty_qbits `OrdSet.equal` q)
          [SMTPat (union q empty_qbits)]
  = ()

let union_ac ()
  : Lemma ((forall (qs0 qs1 qs2:qbits).
              union qs0 (union qs1 qs2) `OrdSet.equal` union (union qs0 qs1) qs2) /\
           (forall (qs0 qs1:qbits).
              union qs0 qs1 `OrdSet.equal` union qs1 qs0) /\
           (forall (q:qbits). union q empty_qbits `OrdSet.equal` q))
  = ()

val tensor (#qs0:qbits)
           (#qs1:qbits {disjoint_qbits qs0 qs1})
           (v0:qvec qs0)
           (v1:qvec qs1)
  : qvec (union qs0 qs1)

val tensor_unit (qs:qbits) (v:qvec qs)
  : Lemma
    (ensures tensor v empty_qvec == v)

val tensor_comm (qs0 qs1:qbits) (v0:qvec qs0) (v1:qvec qs1)
  : Lemma
    (requires disjoint qs0 qs1)
    (ensures tensor v0 v1 == tensor v1 v0)

val tensor_assoc_l (#qs0:_)
                   (#qs1:_{disjoint_qbits qs0 qs1})
                   (#qs2:_{disjoint_qbits (OrdSet.union qs0 qs1) qs2})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (union_ac();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))

val tensor_assoc_r (#qs0:_)
                   (#qs1:_)
                   (#qs2:_{disjoint_qbits qs1 qs2 /\ disjoint_qbits qs0 (OrdSet.union qs1 qs2)})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (union_ac ();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))

// operations:
// * init
// * disc
// * apply
// * meas

val init : (#qs:qbits) -> qvec qs -> (q:qbit) & qvec (union qs (singleton q))

val disc : (#qs:qbits) -> (q:qbit{mem q qs}) -> qvec qs -> qvec (remove q qs) 

val meas : (#qs:qbits) -> (q:qbit{mem q qs}) -> bool -> qvec qs -> qvec qs

val applyH : (#qs:qbits) -> (q:qbit{mem q qs}) -> qvec qs -> qvec qs

val applyCX : (#qs:qbits) -> (q1:qbit{mem q1 qs}) -> 
              (q2:qbit{mem q2 qs /\ q1 <> q2}) -> qvec qs -> qvec qs

(*
val lemma_applyH_fp
    { i = (v:qvec qs) `tensor` (v':qvec qs') }
      lift qs qs' op i
    { i = (op v:qvec qs) `tensor` (v':qvec qs') }
*)