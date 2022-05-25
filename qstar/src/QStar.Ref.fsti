module QStar.Ref
open Steel.ST.Util
open QStar.Steel.Util
open QStar.Vec
open QStar.Heap
module M = QStar.Matrix
#push-options "--ide_id_info_off"

val pts_to (qs:qbits) ([@@@smt_fallback]state:qvec qs) : vprop

val apply_gate (#qs:qbits) (#state:qvec qs) (g:gate qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (apply g state))

val share (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhost unit o
    (pts_to (qs `union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')
    (requires disjoint qs qs')
    (ensures fun _ -> True)

val gather (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhost unit o
    (pts_to qs state `star` pts_to qs' state')
    (fun _ -> pts_to (qs `union` qs') (state `tensor` state'))
    (requires True)
    (ensures fun _ -> disjoint qs qs')

val measure (#qs:qbits)
            (#state:qvec qs)
            (q:qbit)
  : ST bool
    (pts_to qs state)
    (fun b -> pts_to (single q) (singleton q b) `star`
           pts_to (qs `minus` (single q)) (proj_and_disc q b state))
    (requires q `mem` qs)
    (ensures fun _ -> True)
    
val alloc (_:unit)
  : STT qbit emp (fun q -> pts_to (single q) (singleton q false))

val discard (q:qbit) (qstate:qvec (single q))
  : STT unit (pts_to (single q) qstate) (fun _ -> emp)

let test1 (_:unit)
  : STT unit emp (fun _ -> emp)
  = //allocate a qbit q in |0>
    let q = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (apply (hadamard q) (apply (hadamard q) (singleton q false))));
    //call the lemma below, and prove that q is actually back to |0>
    hadamard_self_adjoint q;
    rewrite (pts_to (single q) _)
            (pts_to (single q) (singleton q false)); //use hadamard_self_adjoint to prove 
                                                     //that q is back to its initial state
    //discard it
    discard q _

// same as test1, but now with some other qbit around
let test2 (_:unit)
  : STT qbit emp (fun q1 -> pts_to (single q1) (apply (hadamard _) (singleton _ false)))
  = //allocate a qbit q in |0>
    let q = alloc () in
    let q1 = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (apply (hadamard q) (apply (hadamard q) (singleton q false))));
    //call the lemma below, and prove that q is actually back to |0>
    hadamard_self_adjoint q;
    rewrite (pts_to (single q) _)
            (pts_to (single q) (singleton q false)); //use hadamard_self_adjoint to prove 
                                                     //that q is back to its initial state
    //discard it
    discard q _;
    apply_gate (hadamard q1);
    return q1

// returning more than one qbit
let test3 (_:unit)
  : STT (qbit * qbit) emp 
        (fun qs -> pts_to (single (fst qs)) (singleton _ false) `star`
                pts_to (single (snd qs)) (singleton _ false))
  = //allocate a qbit q in |0>
    let q0 = alloc () in
    let q1 = alloc () in
    let res = q0, q1 in
    // This is kinda ugly, but Steel currently forces you to do this kind of rewrite
    // and doesn't implicitly convert (pts_to (single q0) _) to (pts_to (single (fst res)) _)
    rewrite (pts_to (single q0) _)
            (pts_to (single (fst res)) (singleton _ false));
    rewrite (pts_to (single q1) _)
            (pts_to (single (snd res)) (singleton _ false));            
    return res

// returning more than one qbit after gathering them
let test4 (_:unit)
  : STT (qbit * qbit)
        emp
        (fun qs -> exists_ (fun state -> 
                   pts_to (union (single (fst qs)) (single (snd qs))) state `star`
                   pure (fst qs =!= snd qs /\
                         state == (singleton (fst qs) false `tensor` singleton (snd qs) false))))
  = //allocate a qbit q in |0>
    let q0 = alloc () in
    let q1 = alloc () in
    let _ = gather (single q0) (single q1) #_ #_ in
    let res = (q0, q1) in
    rewrite (pts_to _ _)
            (pts_to (union (single (fst res)) (single (snd res)))
                    (singleton (fst res) false `tensor` singleton (snd res) false));
    (* This is super verbose, but once F* PR  2553 is merged, this should be automated *)
    intro_pure (fst res =!= snd res /\
               ((singleton (fst res) false `tensor` singleton (snd res) false) ==
                (singleton (fst res) false `tensor` singleton (snd res) false)));
    intro_exists (singleton (fst res) false `tensor` singleton (snd res) false)
                 (fun state -> 
                   pts_to (union (single (fst res)) (single (snd res))) state `star`
                   pure (fst res =!= snd res /\
                         state == (singleton (fst res) false `tensor` singleton (snd res) false)));
    return res

let coerce_qvec (#qs:qbits) (#qs':qbits { equal qs qs' }) (qv:qvec qs)
  : qvec qs'
  = qv

let rewrite_pts_to_equiv #o (#qs:qbits) 
                         (#s:qvec qs)
                         (qs':qbits { equal qs qs' })
  : STGhostT unit o         
    (pts_to qs s)
    (fun _ -> pts_to qs' (coerce_qvec s))
  = rewrite _ _

let measure1 (qA:qbit) (qB:qbit { qA <> qB }) (s:qvec (double qA qB))
  : STT bool
    (pts_to (double qA qB) s)
    (fun b -> pts_to (single qA) (singleton _ b) `star`
           pts_to (single qB) (coerce_qvec (proj_and_disc qA b s)))
  = let b = measure qA in
    rewrite_pts_to_equiv #_ #(minus _ _) (single qB);
    return b

let fst (x:('a & 'b)) = fst x
let snd (x:('a & 'b)) = snd x

let measure2 (qA:qbit) (qB:qbit) (rest:qbits { qA <> qB /\ disjoint (double qA qB) rest })
             (s:qvec (union (double qA qB) rest))
  : STT (bool & bool)
    (pts_to _ s)
    (fun b12 -> pts_to (single qA) (singleton _ (fst b12)) `star`
             pts_to (single qB) (singleton _ (snd b12)) `star`
             pts_to rest (coerce_qvec 
                                (proj_and_disc qB (snd b12)
                                  (proj_and_disc qA (fst b12) s))))
  = let b1 = measure qA in
    let b2 = measure #(minus _ _) qB in
    rewrite_pts_to_equiv #_ #(minus _ _) rest;
    let res = b1, b2 in
    rewrite (pts_to (single qA) _)
            (pts_to (single qA) (singleton _ (fst res)));
    rewrite (pts_to (single qB) _)
            (pts_to (single qB) (singleton _ (snd res)));
    rewrite (pts_to rest _)
            (pts_to rest
                    (coerce_qvec 
                      (proj_and_disc qB (snd res)
                        (proj_and_disc qA (fst res) s))));
    return res

let disjointness #o (qs:qbits) (#qv:qvec qs)
                    (qs':qbits) (#qv':qvec qs')
  : STGhost unit o
    (pts_to qs qv `star` pts_to qs' qv')
    (fun _ -> pts_to qs qv `star` pts_to qs' qv')
    (requires True)
    (ensures fun _ -> disjoint qs qs')
  = gather qs qs' #_ #_;
    share qs qs' #_ #_
