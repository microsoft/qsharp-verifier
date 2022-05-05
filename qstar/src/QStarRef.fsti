module QStarRef
open Steel.ST.Util
open QStar.Steel.Util
open QVec
open QStarHeap
module M = Matrix
#push-options "--ide_id_info_off"

val pts_to (qs:qbits) ([@@@smt_fallback]state:qvec qs) : vprop

val apply_gate (#qs:qbits) (#state:qvec qs) (gate:qvec qs -> qvec qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (gate state))

val share (#o:_) (qs:qbits) (qs':qbits{ disjoint_qbits qs qs'}) (#state:qvec qs) (#state':qvec qs')
  : STGhostT unit o
    (pts_to (qs `OrdSet.union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')

val gather (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhostT (_:unit{disjoint_qbits qs qs'}) o
    (pts_to qs state `star` pts_to qs' state')
    (fun _ -> pts_to (qs `OrdSet.union` qs') (state `tensor` state'))


let single (q:qbit) : qbits = OrdSet.singleton q
let singleton q (b:bool) : qvec (single q) = M.create 2 1 (if b then Complex.c0 else Complex.c1)

val project (q:qbit)
            (qs:qbits {q `OrdSet.mem` qs })
            (b:bool)
            (s:qvec qs)
  : option (qvec (qs `OrdSet.minus` single q))

let disc (q:qbit)
         (qs:qbits {q `OrdSet.mem` qs })
         (b:bool)
         (s:qvec qs { Some? (project q qs b s) })
  : qvec (qs `OrdSet.minus` single q)
  = Some?.v (project q qs b s)

val measure (q:qbit)
            (qs:qbits { q `OrdSet.mem` qs })
            (state:qvec qs)
  : STT (b:bool { Some? (project q qs b state) })
    (pts_to qs state)
    (fun b -> pts_to (single q) (singleton q b) `star`
           pts_to (qs `OrdSet.minus` (single q)) (disc q qs b state))

val alloc (_:unit)
  : STT qbit emp (fun q -> pts_to (single q) (singleton q false))

val discard (q:qbit) (qstate:qvec (single q))
  : STT unit (pts_to (single q) qstate) (fun _ -> emp)

val hadamard (q:qbit) : qvec (single q) -> qvec (single q)

let self_adjoint (#qs:qbits) (gate: qvec qs -> qvec qs) =
  forall (s:qvec qs). gate (gate s) == s

val hadamard_self_adjoint (q:qbit)
  : Lemma (ensures self_adjoint (hadamard q))
          
  
let test1 (_:unit)
  : STT unit emp (fun _ -> emp)
  = //allocate a qbit q in |0>
    let q = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (hadamard q (hadamard q (singleton q false))));
    //call the lemma below, and prove that q is actually back to |0>
    hadamard_self_adjoint q;
    rewrite (pts_to (single q) _)
            (pts_to (single q) (singleton q false)); //use hadamard_self_adjoint to prove 
                                                     //that q is back to its initial state
    //discard it
    discard q _

// same as test1, but now with some other qbit around
let test2 (_:unit)
  : STT qbit emp (fun q1 -> pts_to (single q1) (hadamard _ (singleton _ false)))
  = //allocate a qbit q in |0>
    let q = alloc () in
    let q1 = alloc () in
    //apply H to it twice
    apply_gate (hadamard q);
    apply_gate (hadamard q);
    //now we know q is in state H (H |0>)
    assert_ (pts_to (single q) (hadamard q (hadamard q (singleton q false))));
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
                   pts_to (OrdSet.union (single (fst qs)) (single (snd qs))) state `star`
                   pure (fst qs =!= snd qs /\
                         state == (singleton (fst qs) false `tensor` singleton (snd qs) false))))
  = //allocate a qbit q in |0>
    let q0 = alloc () in
    let q1 = alloc () in
    let _ = gather (single q0) (single q1) #_ #_ in
    let res = (q0, q1) in
    rewrite (pts_to _ _)
            (pts_to (OrdSet.union (single (fst res)) (single (snd res)))
                    (singleton (fst res) false `tensor` singleton (snd res) false));
    (* This is super verbose, but once F* PR  2553 is merged, this should be automated *)
    intro_pure (fst res =!= snd res /\
               ((singleton (fst res) false `tensor` singleton (snd res) false) ==
                (singleton (fst res) false `tensor` singleton (snd res) false)));
    intro_exists (singleton (fst res) false `tensor` singleton (snd res) false)
                 (fun state -> 
                   pts_to (OrdSet.union (single (fst res)) (single (snd res))) state `star`
                   pure (fst res =!= snd res /\
                         state == (singleton (fst res) false `tensor` singleton (snd res) false)));
    return res
