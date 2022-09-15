module QStar.Vec

open FStar.Mul
open FStar.List.Tot
open QStar.Quantum
module O = FStar.OrdSet
module F = FStar.FunctionalExtensionality

let qvec (qs:qbits) : Type u#0 = matrix complex (dimension qs) 1

let empty_qvec : qvec empty_qbits = id_matrix complex 1

let size_disjoint_union (#a:eqtype) (#f:O.cmp a) (s1 s2:O.ordset a f)
  : Lemma (requires (OrdSet.intersect s1 s2 `OrdSet.equal` OrdSet.empty))
          (ensures (OrdSet.size (O.union s1 s2) = OrdSet.size s1 + OrdSet.size s2))
          [SMTPat (O.size #a #f (O.union #a #f s1 s2))]
  = admit()

let dimension_union (qs0:qbits) (qs1:qbits{disjoint qs0 qs1})
  : Lemma (ensures dimension (O.union qs0 qs1) = dimension qs0 * dimension qs1)
          [SMTPat (dimension (O.union qs0 qs1))]
  = Math.Lemmas.pow2_plus (O.size qs0) (O.size qs1)

// SKETCH
// given seq s1, permutation s2, and matrix m, apply a permutation matrix that reorders 
// the elements of m to be consistent with s2, assuming they were originally ordered
// according to s1
//
// e.g., let s1 = [c, a, b] and s2 = [a, b, c]; then reorder_indices will apply a matrix
// that implements the following qubit permutation: {0 -> 2, 1 -> 0, 2 -> 1}
let reorder_indices #m #n s1 s2 (v : matrix complex m n) : matrix complex m n = 
  admit()

// Idea: apply the standard Kronecker product and then multiply by a permutation
// matrix (called reorder_indices) that orders the qubits according to their sorted order.
//
// We need to get rid of the assume in this function. In the case where 
// qs0, qs1 overlap, we should return some default value (like the zero vector).
let tensor #qs0 #qs1 v0 v1 = 
  assume (disjoint qs0 qs1); 
  reorder_indices (O.as_list qs0 @ O.as_list qs1) // input ordering
                  (O.as_list (qs0 `O.union` qs1)) // output ordering
                  (kronecker_product v0 v1)

let lemma_reorder_indices_same m n s1 s2 (v : matrix complex m n) 
  : Lemma (requires (s1 == s2))
          (ensures reorder_indices s1 s2 v == v)
  = admit()

let tensor_unit qs v
  : Lemma (ensures tensor v empty_qvec == v)
  = admit()

let tensor_comm qs0 qs1 v0 v1
  : Lemma (requires disjoint qs0 qs1)
          (ensures tensor v0 v1 == tensor v1 v0)
  = admit()

let tensor_assoc_l #qs0 #qs1 #qs2 v0 v1 v2
  : Lemma (tensor (tensor v0 v1) v2 `qvec_equiv` tensor v0 (tensor v1 v2))
  = admit()

let tensor_assoc_r #qs0 #qs1 #qs2 v0 v1 v2
  : Lemma (union_ac ();
           tensor (tensor v0 v1) v2 `qvec_equiv` tensor v0 (tensor v1 v2))
  = admit()

let singleton (q:qbit) (b:bool) : qvec (single q) = ket b

let proj (#qs:qbits)
         (q:qbit)
         (b:bool)
         (s:qvec qs)
  : qvec qs
  = admit()

let disc (#qs:qbits)
         (q:qbit)
         (s:qvec qs)
  : qvec (qs `OrdSet.minus` single q)
  = admit()

// The intention of this function is to "relabel" the qubits in s, which
// are originally labelled according to qs1, according to qs2. 
// The function probably also needs a bijection between qs1 and qs2 as input.
let relabel_indices #qs1 qs2 s = admit()

let gate (qs:qbits) = matrix complex (dimension qs) (dimension qs) 

let hadamard (q:qbit) = hadamard_mat

let pauli_x (q:qbit) = x_mat

let pauli_z (q:qbit) = z_mat

// 2q gates are a little more complicated than 1q gates because we need to
// keep in mind the ordering of qubits
let cnot (q1:qbit) (q2:qbit{q1 <> q2})
  = if q1 < q2 then cnot_mat
    else matrix_mul swap_mat (matrix_mul cnot_mat swap_mat)

let apply (#qs:qbits) (g:gate qs) (v:qvec qs) = matrix_mul g v

// Idea: tensor the gate g with an idntity matrix over |qs'| qubits, and then
// apply a permutation matrix to maintain the qubit ordering invariant.
let lift (qs:qbits) (qs':qbits) (g:gate qs)
  = admit()

let lift_preserves_frame (qs:qbits) (qs':qbits{qs' `disjoint` qs}) (g:gate qs) 
                         (v : qvec qs) (v' : qvec qs')
  : Lemma (ensures (apply (lift qs qs' g) (v `tensor` v') == apply g v `tensor` v'))
  = admit()

let hadamard_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (hadamard q))
  = admit()

let scale (#qs:qbits) (c:complex) (v:qvec qs) : qvec qs = Matrix.scale c v

let plus (#qs:qbits) (v1:qvec qs) (v2:qvec qs) : qvec qs = matrix_add v1 v2

let rec build_vec (qs:qbits) (data:qbit -> bool) 
  : Tot (qvec qs) (decreases (size qs))
  = if size qs = 0
    then empty_qvec
    else let q = Some?.v (OrdSet.choose qs) in
        singleton q (data q) `tensor` build_vec (OrdSet.remove q qs) data

let bell00 (q1:qbit) (q2:qbit) : qvec (double q1 q2) =
  scale (of_real (1.0R /. sqrt_2)) 
        ((build_vec _ (fun _ -> false)) `plus` (build_vec _ (fun _ -> true)))

let lemma_bell00 (q1:qbit) (q2:qbit{q1 <> q2}) 
  : Lemma (apply (cnot q1 q2) 
                 ((apply (hadamard q1) (singleton q1 false)) `tensor` 
                    (singleton q2 false))
           == bell00 q1 q2)
  = admit()
// proof sketch:
// 1. let := of_real (1.0R /. sqrt_2)
//    apply (hadamard q1) (singleton q1 false) == 
//       scale c ((singleton q1 false) `plus` (singleton q1 true))
// 2. apply (hadamard q1) (singleton q1 false) `tensor` (singleton q2 false) ==
//       scale c ((singleton q1 false `tensor` singleton q2 false) 
//                 `plus` (singleton q1 true `tensor` singleton q2 false))
// 3. apply (cnot q1 q2) ((apply (hadamard q1) (singleton q1 false)) `tensor` (singleton q2 false) ==
//       scale c ((singleton q1 false `tensor` singleton q2 false) 
//                 `plus` (singleton q1 true `tensor` singleton q2 true))
