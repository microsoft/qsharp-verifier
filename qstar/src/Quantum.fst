module Quantum

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Real
open FStar.FunctionalExtensionality
//open FStar.Tactics
open Numeric
open Matrix
open Complex

module F = FStar.FunctionalExtensionality
//#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

// common matrices
let hadamard_mat : matrix complex 2 2 =
  F.on (knat 2 & knat 2)
       (fun (i,j) -> cmul (of_real (1.0R /. sqrt_2)) 
                       (if i = 1 && j = 1 then of_real (0.0R -. 1.0R) else c1))

let x_mat : matrix complex 2 2 =
  F.on (knat 2 & knat 2)
       (fun (i,j) -> if j = i then c0 else c1)

let z_mat : matrix complex 2 2 =
  F.on (knat 2 & knat 2)
       (fun (i,j) -> if i = j 
                  then if i = 0 then c1 else of_real (0.0R -. 1.0R)
                  else c0)

let cnot_mat : matrix complex 4 4 =
  F.on (knat 4 & knat 4)
       (fun (i,j) ->
          if i = 0 && j = 0 then c1
          else if i = 1 && j = 1 then c1
          else if i = 2 && j = 3 then c1
          else if i = 3 && j = 2 then c1
          else c0)

// unitarity condition
// NOTE: we could also include this in the type of the matrices above
let unitary (#n:dim) (x:matrix complex n n) =
  forall i j. (matrix_mul x (conjugate_transpose x)) (i,j) == (id_matrix complex n) (i,j)

// TODO: need to add patterns to unitary to make these proof automatic
let lemma_hadamard_unitary () : Lemma (unitary hadamard_mat)
  = admit()

let lemma_x_unitary () : Lemma (unitary x_mat)
  = admit()

let lemma_z_unitary () : Lemma (unitary z_mat)
  = admit()

// vector norm
let norm #n (v:matrix complex n 1) : real =
  sqrt (fst (matrix_mul (conjugate_transpose v) v (0,0)))
let unit_norm #n (v:matrix complex n 1) = norm v = 1.0R

// unitary matrices preserve unit vector norm
let lemma_unitary_preserves_norm (n:dim) (mat:matrix complex n n) (v:matrix complex n 1)
  : Lemma (requires unit_norm v /\ unitary mat)
          (ensures unit_norm (matrix_mul mat v))
  = admit()

let lemma_pow2_prod n (q:knat n)
  : Lemma (ensures (pow2 q * (2 * pow2 (n - q - 1)) = pow2 n))
  = assert (q + 1 + (n - q - 1) = n);
    assert (2 = pow2 1);
    Math.Lemmas.pow2_plus q 1;
    Math.Lemmas.pow2_plus (q + 1) (n - q - 1)

// extend a 2x2 matrix to a n-dimensional space
let pad (n:dim) (q:knat n) (mat:matrix complex 2 2) 
  : matrix complex (pow2 n) (pow2 n)
  = lemma_pow2_prod n q;
    kronecker_product 
      (id_matrix complex (pow2 q)) 
      (kronecker_product mat (id_matrix complex (pow2 (n - q - 1))))

let lemma_pad_unitary (n:dim) (q:knat n) (mat:matrix complex 2 2) 
  : Lemma (requires (unitary mat))
          (ensures (unitary (pad n q mat)))
  = admit()

// |0> or |1>
let ket (b:bool) : matrix complex 2 1 = 
  if b then F.on (knat 2 & knat 1) (fun (i,j) -> if i = 0 then c1 else c0)
  else F.on (knat 2 & knat 1) (fun (i,j) -> if i = 1 then c1 else c0)

// projectors onto |0> and |1>
let proj0 : matrix complex 2 2 =
  matrix_mul (ket false) (conjugate_transpose (ket false))
let proj1 : matrix complex 2 2 = 
  matrix_mul (ket true) (conjugate_transpose (ket true))

// extend a controlled 2x2 matrix a n-dimensional space
let pad_control (n:dim) (q1 q2:knat n) (mat:matrix complex 2 2) 
  : matrix complex (pow2 n) (pow2 n)
  = matrix_add (pad n q1 proj0) (matrix_mul (pad n q1 proj1) (pad n q2 mat))

let lemma_pad_control_unitary (n:dim) (q1 q2:knat n) (mat:matrix complex 2 2)
  : Lemma (requires (unitary mat))
          (ensures (unitary (pad_control n q1 q2 mat)))
  = admit()

// normalize a vector
// ** requires that the input vector has nonzero 
let normalize (#n:dim) (v:matrix complex n 1) : matrix complex n 1 = 
  if norm v = 0.0R
  then zero_matrix complex n 1
  else scale (of_real (1.0R /. norm v)) v

let lemma_normalize_norm_1 (#n:dim) (v:matrix complex n 1)
  : Lemma (requires norm v <> 0.0R)
          (ensures unit_norm (normalize v))
  = admit()

// project a vector onto the subspace where qubit q is |0> or |1>
let project (#n:dim) (q:knat n) (b:bool) (v:matrix complex (pow2 n) 1) =
  let proj = if b then proj1 else proj0 in
  matrix_mul (pad n q proj) v
// TODO: generaize to arbitrary subspaces
