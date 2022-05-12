module QVec

open Complex
open Quantum
open Matrix
open FStar.Real
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

let single (q:qbit) : qbits = OrdSet.singleton q

let singleton q (b:bool) : qvec (single q) = ket b

let double (q1:qbit) (q2:qbit{q1 <> q2}) : qbits = OrdSet.union (single q1) (single q2)

val proj (#qs:qbits)
         (q:qbit{q `OrdSet.mem` qs})
         (b:bool)
         (s:qvec qs)
  : option (qvec (qs `OrdSet.minus` single q))

val disc (#qs:qbits)
         (q:qbit{q `OrdSet.mem` qs})
         (b:bool)
         (s:qvec qs { Some? (proj q b s) })
  : qvec (qs `OrdSet.minus` single q)

val gate (qs:qbits) : Type0

val hadamard : (q:qbit) -> gate (single q)

val pauli_x : (q:qbit) -> gate (single q)

val pauli_z : (q:qbit) -> gate (single q)

val cnot : (q1:qbit) -> (q2:qbit{q1 <> q2}) -> gate (double q1 q2)

val apply : (#qs:qbits) -> gate qs -> qvec qs -> qvec qs

val lift : (qs:qbits) -> (qs':qbits{qs' `disjoint` qs}) -> 
           gate qs -> gate (qs `union` qs')

val lift_preserves_frame (qs:qbits) (qs':qbits{qs' `disjoint` qs}) (g:gate qs) 
                         (v : qvec qs) (v' : qvec qs')
  : Lemma (ensures (apply (lift qs qs' g) (v `tensor` v') == apply g v `tensor` v'))

let self_adjoint (#qs:qbits) (g: gate qs) =
  forall (s:qvec qs). apply g (apply g s) == s

val hadamard_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (hadamard q))

val pauli_x_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_x q))

val pauli_z_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_z q))

val cnot_self_adjoint (q1:qbit) (q2:qbit{q1 <> q2})
  : Lemma (ensures self_adjoint (cnot q1 q2))

/// Abstractions for defining vector states

let scale #qs (c:complex) (v:qvec qs) : qvec qs = Matrix.scale c v

let plus #qs (v1:qvec qs) (v2:qvec qs) : qvec qs = matrix_add v1 v2

// TODO: what type do we want for "data"?
let rec build_vec (qs:qbits) (data:qbit -> bool) 
  : Tot (qvec qs) (decreases (OrdSet.size qs)) =
  if OrdSet.size qs = 0
  then empty_qvec
  else let q = Some?.v (OrdSet.choose qs) in
       singleton q (data q) `tensor` build_vec (OrdSet.remove q qs) data

let bell00 (q1:qbit) (q2:qbit{q1 <> q2}) : qvec (double q1 q2) =
  scale (of_real (1.0R /. sqrt_2)) 
        ((build_vec _ (fun _ -> false)) `plus` (build_vec _ (fun _ -> true)))


// Old definition
(*
let ordset_size_union  (#a:eqtype) (#f:cmp a) (s0 s1:OrdSet.ordset a f)
  : Lemma (requires OrdSet.disjoint s0 s1)
          (ensures OrdSet.size (OrdSet.union s0 s1) == OrdSet.size s0 + OrdSet.size s1)
          [SMTPat (OrdSet.size (OrdSet.union s0 s1))]
  = admit() //TODO: need to add this to the OrdSet library

let ordset_size_double (q1:qbit) (q2:qbit{q1 =!= q2})
  : Lemma (ensures dimension (double q1 q2) == 4)
          [SMTPat (dimension (double q1 q2))]
  = assert (OrdSet.intersect (single q1) (single q2) `OrdSet.equal` OrdSet.empty)
    
let as_qvec (qs:qbits) (#n:nat{n == dimension qs}) (m:matrix complex n 1) : qvec qs = m

module F = FStar.FunctionalExtensionality

let bell00' (q1:qbit) (q2:qbit{q1 <> q2}) : matrix complex 4 1
  = F.on (knat 4 & knat 1) 
         (fun (i,j) -> cmul (of_real (1.0R /. sqrt_2)) (if i = j then c1 else c0))
  
let bell00 (q1:qbit) (q2:qbit{q1 <> q2}) : qvec (double q1 q2)
  = as_qvec _ (bell00' q1 q2)
*)


val lemma_bell00 (q1:qbit) (q2:qbit{q1 <> q2}) 
  : Lemma (apply (cnot q1 q2) 
                 ((apply (hadamard q1) (singleton q1 false)) `tensor` 
                    (singleton q2 false))
           == bell00 q1 q2)
