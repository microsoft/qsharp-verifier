module QState
open FStar.Real

(* This module defines our representation of quantum states, operations 
   acting on quantum states, and predicates for describing quantum
   states. 
   
   We leave everything abstract in the interface file to allow for
   different implementation choices down the road. *)

// type for a quantum state
val qstate (n:nat) : Type0

// type for an index into the quantum state
type qloc (k:nat) = n:nat{n < k}

// measurement outcome type
type result = | Zero | One
let res_to_bool r = match r with Zero -> false | One -> true
let bool_to_res b = if b then One else Zero

let neg_res r = match r with Zero -> One | One -> Zero

let xor_res r1 r2 = 
  match r1, r2 with 
  | Zero, Zero | One, One -> Zero 
  | _, _ -> One

let and_res r1 r2 = 
  match r1, r2 with 
  | One, One -> One
  | _, _ -> Zero

// apply a gate
val apply_H : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_X : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_Z : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_T : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_TDG : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_S : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_SDG : (#n:nat) -> qloc n -> qstate n -> qstate n
val apply_CNOT : (#n:nat) -> (q1:qloc n) -> (q2:qloc n{q1 <> q2}) -> qstate n -> qstate n
val apply_CZ : (#n:nat) -> (q1:qloc n) -> (q2:qloc n{q1 <> q2}) -> qstate n -> qstate n

// project a quantum state onto a given measurement outcome, returning
// the probability of that outcome and the resulting state
val measure : (#n:nat) -> qloc n -> result -> qstate n -> real & qstate n

// extend the state with a fresh |0> qubit
val init : (#n:nat) -> qstate n -> qstate (n+1)

// discard the last qubit
val discard : (#n:nat{n > 0}) -> qstate n -> qstate (n-1)

// some common states
val classical_state : result -> qstate 1 // |0> or |1>
val plus_state : qstate 1 // |+> = 1/sqrt(2) * (|0> + |1>)
val bell00 : qstate 2 // 1 / sqrt(2) * (|00> + |11>)

// extend a 1- or 2-qubit state to the full n dimensions
val extend1 : (#n:nat{n>=1}) -> qloc n -> qstate 1 -> qstate n
val extend2 : (#n:nat{n>=2}) -> q1:qloc n -> q2:qloc n{q1 <> q2} -> qstate 2 -> qstate n

// "in_state qs1 qs2" says that state qs2 is in state qs1
val in_state : (#n:nat) -> qstate n -> qstate n -> prop
let in_1q_state (#n:nat{n>=1}) (q:qloc n) (qs:qstate 1) (qs':qstate n) =
  in_state (extend1 q qs) qs'
let in_1q_classical_state (#n:nat{n>=1}) (q:qloc n) (r:result) (qs:qstate n) =
  in_1q_state q (classical_state r) qs
let in_2q_state (#n:nat{n>=2}) (q1:qloc n) (q2:qloc n{q1 <> q2}) (qs:qstate 2) (qs':qstate n) =
  in_state (extend2 q1 q2 qs) qs'

val lemma_apply_H_self_adjoint (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (apply_H q (apply_H q qs) == qs)
    [SMTPat (apply_H q (apply_H q qs))]

val lemma_apply_X_self_adjoint (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (apply_X q (apply_X q qs) == qs)
    [SMTPat (apply_X q (apply_X q qs))]

val lemma_apply_Z_self_adjoint (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (apply_Z q (apply_Z q qs) == qs)
    [SMTPat (apply_Z q (apply_Z q qs))]

val lemma_apply_T_adjoint (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (apply_TDG q (apply_T q qs) == qs)
    [SMTPat (apply_TDG q (apply_T q qs))]

val lemma_apply_S_adjoint (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (apply_SDG q (apply_S q qs) == qs)
    [SMTPat (apply_SDG q (apply_S q qs))]

val lemma_apply_CNOT_self_adjoint (#n:nat) (q1:qloc n) (q2:qloc n{q1 <> q2}) (qs:qstate n)
  : Lemma (apply_CNOT q1 q2 (apply_CNOT q1 q2 qs) == qs)
    [SMTPat (apply_CNOT q1 q2 (apply_CNOT q1 q2 qs))]

val lemma_apply_CZ_self_adjoint (#n:nat) (q1:qloc n) (q2:qloc n{q1 <> q2}) (qs:qstate n)
  : Lemma (apply_CZ q1 q2 (apply_CZ q1 q2 qs) == qs)
    [SMTPat (apply_CZ q1 q2 (apply_CZ q1 q2 qs))]

// axiomatic-style specs for gates
val lemma_apply_H_zero (#n:nat) (q:qloc n) (qs:qstate n)
  : Lemma (requires (in_1q_classical_state q Zero qs))
          (ensures (in_1q_state q plus_state (apply_H q qs)))

val lemma_apply_H_neq (#n:nat) (q1:qloc n) (q2:qloc n{q1 <> q2}) (psi:qstate 1) (qs:qstate n)
  : Lemma (requires (in_1q_state q2 psi qs))
          (ensures (in_1q_state q2 psi (apply_H q1 qs)))

val lemma_apply_CNOT_plus (#n:nat) (q1:qloc n) (q2:qloc n{q1 <> q2}) (qs:qstate n)
  : Lemma (requires (in_1q_state q1 plus_state qs /\ in_1q_classical_state q2 Zero qs))
          (ensures (in_2q_state q1 q2 bell00 (apply_CNOT q1 q2 qs)))

val lemma_meas_result (#n:nat) (q:qloc n) (r:result) (qs:qstate n)
  : Lemma (ensures (in_1q_classical_state q r (snd (measure q r qs))))

val lemma_pauli_x (#n:nat) (q:qloc n) (r:result) (qs:qstate n)
  : Lemma (requires (in_1q_classical_state q r qs))
          (ensures (in_1q_classical_state q (neg_res r) (apply_X q qs)))
