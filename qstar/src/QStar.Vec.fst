module QStar.Vec

open FStar.Mul
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
  : Lemma (ensures dimension (union qs0 qs1) = dimension qs0 * dimension qs1)
          [SMTPat (dimension (union qs0 qs1))]
  = Math.Lemmas.pow2_plus (O.size qs0) (O.size qs1)

// permutation matrix
let perm_matrix (#a:Type) {| numeric a |} (m:dim) (p : knat m -> knat m) : matrix a m m = 
  F.on (knat m & knat m) 
       (fun (i,j) -> if i = p j then one else zero)

// given a permutation p over n qubits, construct a permutation over 2^n indices
let qubit_perm_to_nat_perm (n : dim) (p : knat n -> knat n) :=
  fun (x:knat n) -> funbool_to_nat n ((nat_to_funbool n x) ∘ p).

// convert a (0,...,n-1) permutation into a 2^n by 2^n matrix
// NOTE: the specialization to complex number isn't required, it just saves some keystrokes
let perm_to_matrix (n : dim) (p : knat n -> knat n) : matrix complex (2 ^ n) (2 ^ n)
  = perm_matrix (2 ^ n) (qubit_perm_to_nat_perm n p).

// given seq s1, permutation s2, and matrix m, apply a permutation matrix that reorders 
// the elements of m to be consistent with s2, assuming they were originally ordered
// according to s1
//
// e.g., let s1 = [c, a, b] and s2 = [a, b, c]; then reorder_indices will apply a matrix
// that implements the following qubit permutation: {0 -> 2, 1 -> 0, 2 -> 1}
let reorder_indices #m #n s1 s2 (v : matrix complex m n) : matrix complex m n = 
  matrix_mul (perm_to_matrix (length s1) ...) v

// TODO: can we expose this in the OrdSet interface?
assume
val as_list (#a:eqtype) (#f:O.cmp a) (s:O.ordset a f) : Tot (l:list a{O.sorted f l})

let tensor #qs0 #qs1 v0 v1 = 
  reorder_indices (as_list qs0 ++ as_list qs1)  // input ordering
                  (as_list (qs0 `O.union` qs1)) // output ordering
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
  : Lemma (tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))
  = admit()

let tensor_assoc_r #qs0 #qs1 #qs2 v0 v1 v2
  : Lemma (union_ac ();
           tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))
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

let relabel_indices #qs1 qs2 s = admit()
// let rename_qubit #qs q1 q2 (v : qvec qs) : qvec (qs `minus` q1 `union` q2)
//   = reorder_indices (as_list qs) (as_list (qs `minus` q1 `union` q2)) v

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

let lift (qs:qbits) (qs':qbits) (g:gate qs)
  = // matrix_mul (build_sort_matrix (as_list qs ++ as_list qs')) 
    //            (kronecker_product g (id_matrix complex (dimension qs') (dimension qs')))
    admit()

let lift_preserves_frame (qs:qbits) (qs':qbits{qs' `disjoint` qs}) (g:gate qs) 
                         (v : qvec qs) (v' : qvec qs')
  : Lemma (ensures (apply (lift qs qs' g) (v `tensor` v') == apply g v `tensor` v'))
  = // requires proving that (kron * reorder) * (kron * reorder) is the same as (kron * reorder),
    admit()

let hadamard_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (hadamard q))
  = admit()

let pauli_x_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_x q))
  = admit()

let pauli_z_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (pauli_z q))
  = admit()

let cnot_self_adjoint (q1:qbit) (q2:qbit{q1 <> q2})
  : Lemma (ensures self_adjoint (cnot q1 q2))
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
