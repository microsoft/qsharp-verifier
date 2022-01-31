module DemoProofs

open FStar.Real

open QInst
open QMap
open QState
open Demo

// wrapper around eval_inst_tree
let run #a #pre #post (it: inst_tree a pre post) 
      (m0:valid_qmap{pre m0}) (bs:nat -> bool) (qs:qstate (size_of m0)) 
  : (v:a & m1:valid_qmap{post v m0 m1} & state (size_of m1)) 
  = let s = (1.0R, 0, qs) in // start with probability 1.0 and stream index 0
    eval_inst_tree it m0 bs s

// the output satisfies a predicate for all possible measurement choices (ignoring probabilities)
let output_sats_pred #a #pre #post 
      (it:inst_tree a pre post) 
      (m0:valid_qmap{pre m0}) 
      (qs:qstate (size_of m0))
      (pred:(v:a -> m1:valid_qmap{post v m0 m1} -> qstate (size_of m1) -> prop))
  : prop 
  = forall bs. let (| v, m1, (_, _, qs) |) = run it m0 bs qs in pred v m1 qs

// bell takes |00> to (|00> + |11>)/sqrt(2)
let lemma_bell (q1 q2:qref) (m:valid_qmap{live m q1 /\ live m q2 /\ q1 <> q2}) 
      (qs:qstate (size_of m))
  : Lemma (requires (in_1q_classical_state (sel m q1) Zero qs /\
                     in_1q_classical_state (sel m q2) Zero qs))
          (ensures (output_sats_pred (prepareBell q1 q2) m qs
              (fun _ m qs -> in_2q_state (sel m q1) (sel m q2) bell00 qs)))
  = lemma_apply_H_zero (sel m q1) qs;
    lemma_apply_H_neq (sel m q1) (sel m q2) (classical_state Zero) qs;
    lemma_apply_CNOT_plus (sel m q1) (sel m q2) (apply_H (sel m q1) qs)

// reset sets q to |0>
let lemma_reset (q:qref) (m:valid_qmap{live m q}) (qs:qstate (size_of m))
  : Lemma (output_sats_pred (reset q) m qs
              (fun _ m qs -> in_1q_classical_state (sel m q) Zero qs))
  = let aux (bs:nat -> bool)
      : Lemma (let (| v, m1, (_, _, qs) |) = run (reset q) m bs qs in 
               in_1q_classical_state (sel m1 q) Zero qs)
      = let (| v, m1, (_, _, qs') |) = run (reset q) m bs qs in
        if bs 0 = true
        then lemma_meas_result (sel m q) Zero qs
        else (
          lemma_meas_result (sel m q) One qs;
          lemma_pauli_x (sel m q) One (snd (measure (sel m q) One qs))
        ) in 
  Classical.forall_intro aux

// teleport moves |psi> from src to tgt
let lemma_teleport (src tgt: qref) (m:valid_qmap{src <> tgt /\ live m src /\ live m tgt}) (qs:qstate (size_of m)) (psi:qstate 1)
  : Lemma (requires (in_1q_state (sel m src) psi qs /\
                     in_1q_classical_state (sel m tgt) Zero qs))
          (ensures (output_sats_pred (teleport src tgt) m qs
                       (fun _ m qs -> in_1q_state (sel m tgt) psi qs)))
  = let aux (bs:nat -> bool)
      : Lemma (let (| v, m1, (_, _, qs) |) = run (teleport src tgt) m bs qs in 
               in_1q_state (sel m1 tgt) psi qs)
      = // assuming psi = (a|0> + b|1>), the state of (src, tgt, a) 
        // before measurement is:
        //     1/2 (a |000> + a |100> + a |011> + a |111> + 
        //          b |001> - b |101> + b |010> - b |110> )
        
        if (bs 0 = false) && (bs 1 = false) then (
          
          // case 1: a |000> + b |010>
          //         tgt is in state (a|0> + b|1>) 
          admit()
        
        ) else if (bs 0 = false) && (bs 1 = true) then (
          
          // case 2: a |011> + b |001>
          //         tgt is in state (a|1> + b|0>) 
          admit()
        
        ) else if (bs 0 = true) && (bs 1 = false) then (
          
          // case 3: a |100> - b |110>
          //         tgt is in state (a|0> - b|1>) 
          admit()
        
        ) else (
          
          // case 4: a |111> - b |101>
          //         tgt is in state (a|1> - b|0>) 
          admit()
        
        ) in 
  
  Classical.forall_intro aux

// applyAnd performs an AND operation: |a, b, c> maps to |a, b, c ^ (a & b)>
let lemma_applyAnd (ctl1 ctl2 tgt: qref) (m:valid_qmap{ctl1 <> ctl2 /\ ctl1 <> tgt /\ ctl2 <> tgt /\ live m ctl1 /\ live m ctl2 /\ live m tgt}) (qs:qstate (size_of m)) (a b:result)
  : Lemma (requires (in_1q_classical_state (sel m ctl1) a qs /\
                     in_1q_classical_state (sel m ctl2) b qs /\
                     in_1q_classical_state (sel m tgt) Zero qs))
          (ensures (output_sats_pred (applyAnd ctl1 ctl2 tgt) m qs
                       (fun _ m qs -> 
                         in_1q_classical_state (sel m ctl1) a qs /\
                         in_1q_classical_state (sel m ctl2) b qs /\
                         in_1q_classical_state (sel m tgt) (and_res a b) qs)))
  = admit()

// applyAnd_adjoint inverts applyAnd
let lemma_applyAnd_adjoint (ctl1 ctl2 tgt: qref) (m:valid_qmap{ctl1 <> ctl2 /\ ctl1 <> tgt /\ ctl2 <> tgt /\ live m ctl1 /\ live m ctl2 /\ live m tgt}) (qs:qstate (size_of m))
  : Lemma (requires (in_1q_classical_state (sel m tgt) Zero qs)) 
          (ensures (output_sats_pred 
                     (bind (applyAnd ctl1 ctl2 tgt) 
                           (fun _ -> applyAnd_adjoint ctl1 ctl2 tgt)) 
                           m qs
                           (fun _ m' qs' -> m == m' /\ qs == qs')))
  = admit()
