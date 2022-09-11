module QStar.QState

open FStar.Mul
open FStar.Real
open QStar.Complex
open QStar.Matrix
open QStar.Quantum

module F = FStar.FunctionalExtensionality

// qstate (p,v) = vector v with (classical) probability p
// TODO: we may want to add the restriction that v has unit norm,
//       but this will make the definitions below more painful
type qstate (n:nat) = real & matrix complex (pow2 n) 1

// we need to call auxiliary 
let apply_H #n q qs =
  let (p,v) = qs in
  (p, matrix_mul (pad 1 n q hadamard_mat) v)

// similar to apply_H
let apply_X #n q qs = admit()
let apply_Z #n q qs = admit()
let apply_T #n q qs = admit()
let apply_TDG #n q qs = admit()
let apply_S #n q qs = admit()
let apply_SDG #n q qs = admit()
let apply_CNOT #n q1 q2 qs = admit()
let apply_CZ #n q1 q2 qs = admit()

let measure #n q r qs = admit()
  //let (p,v) = qs in
  //let projv = project q (res_to_bool r) v in
  //(p *. norm projv, normalize projv)

let init #n qs = 
  let (p,v) = qs in
  (p, kronecker_product v (ket false))

let discard #n qs = admit()
//  let (p,v) = qs in
//  let projv = matrix_mul (pad n q false) v in
//  (p *. norm projv, normalize projv)

let classical_state r = admit() //Some (ket (res_to_bool r))
let plus_state = admit() //Some (F.on (knat 2 & knat 1) (fun (i,j) -> of_real (1.0R /. sqrt_2)))
let bell00 = admit() //F.on (knat 4 & knat 1) (fun (i,j) -> cmul (of_real (1.0R /. sqrt_2)) (if i = j then c1 else c0))

let extend1 #n q psi = admit()
let extend2 #n q1 q2 psi = admit()

// check if projecting the current state onto psi leaves the state unchanged
let in_state #n psi qs =
  admit() //match qs with
  //| Some v -> v == (matrix_mul (pad n q (matrix_mul psi (conjugate_transpose psi))) v)
  //| None -> False

let lemma_apply_H_self_adjoint #n q qs
  : Lemma (apply_H q (apply_H q qs) == qs)
  = admit()

let lemma_apply_X_self_adjoint #n q qs
  : Lemma (apply_X q (apply_X q qs) == qs)
  = admit()

let lemma_apply_Z_self_adjoint #n q qs
  : Lemma (apply_Z q (apply_Z q qs) == qs)
  = admit()

let lemma_apply_T_adjoint #n q qs
  : Lemma (apply_TDG q (apply_T q qs) == qs)
  = admit()

let lemma_apply_S_adjoint #n q qs
  : Lemma (apply_SDG q (apply_S q qs) == qs)
  = admit()

let lemma_apply_CNOT_self_adjoint #n q1 q2 qs
  : Lemma (apply_CNOT q1 q2 (apply_CNOT q1 q2 qs) == qs)
  = admit()
  
let lemma_apply_CZ_self_adjoint #n q1 q2 qs
  : Lemma (apply_CZ q1 q2 (apply_CZ q1 q2 qs) == qs)
  = admit()

let lemma_apply_H_zero #n q qs
  : Lemma (requires (in_1q_classical_state q Zero qs))
          (ensures (in_1q_state q plus_state (apply_H q qs)))
  = admit()

let lemma_apply_H_neq #n q1 q2 psi qs
  : Lemma (requires (in_1q_state q2 psi qs))
          (ensures (in_1q_state q2 psi (apply_H q1 qs)))
  = admit()

let lemma_apply_CNOT_plus #n q1 q2 qs
  : Lemma (requires (in_1q_state q1 plus_state qs /\ in_1q_classical_state q2 Zero qs))
          (ensures (in_2q_state q1 q2 bell00 (apply_CNOT q1 q2 qs)))
  = admit()

let lemma_meas_result #n q r qs
  : Lemma (ensures (in_1q_classical_state q r (snd (measure q r qs))))
  = admit()

let lemma_pauli_x #n q r qs
  : Lemma (requires (in_1q_classical_state q r qs))
          (ensures (in_1q_classical_state q (neg_res r) (apply_X q qs)))
  = admit()
