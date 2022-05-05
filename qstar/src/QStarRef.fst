module QStarRef
open Steel.ST.Util
open QStar.Steel.Util
open QVec
open QStarHeap
module M = Matrix
module P = Steel.ST.GhostPCMReference

let core_ref = P.ref _ qstar_heap_pcm

//All the qubits are stores in this ref cell
assume
val qstar_state : core_ref

let pperm = p:perm {p `lesser_equal_perm` full_perm}

let pts_to (qs:qbits) ([@@@smt_fallback]state:qvec qs) : vprop =
  exists_ (fun (perm:pperm) -> P.pts_to qstar_state ({frac=Some perm; qs; state}))

let apply_gate (#qs:qbits) (#state:qvec qs) (gate:qvec qs -> qvec qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (gate state))
  = let perm = elim_exists () in
    P.upd_gen qstar_state ({frac=Some (Ghost.reveal perm); qs; state}) ({frac=Some (Ghost.reveal perm); qs;state=gate state})
      (QStarHeap.apply_fpupd #qs #perm #state gate);
    intro_exists_erased #pperm perm (fun perm -> P.pts_to qstar_state ({frac=Some perm; qs; state=gate state}))

let split_perm (p:pperm)
  : c:pperm{ composable_frac_opt (Some c) (Some c) }
  = half_perm p

let intro_pts_to #o (#p:pperm) qs #s ()
  : STGhostT unit o
    (P.pts_to qstar_state ({frac = Some p; qs; state=s}))
    (fun _ -> pts_to qs s)
  = intro_exists #pperm p (fun p -> P.pts_to qstar_state ({frac = Some p; qs; state=s}));
    ()

let share (#o:_) (qs:qbits) (qs':qbits{ disjoint_qbits qs qs'}) (#state:qvec qs) (#state':qvec qs')
  : STGhostT unit o
    (pts_to (qs `OrdSet.union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')
  = let perm = elim_exists #pperm () in
    P.share qstar_state _
      ({ frac = Some (Ghost.reveal (half_perm perm));
               qs = qs;
               state = state })
      ({ frac = Some (Ghost.reveal (half_perm perm));
               qs = qs';
               state = state' });
    intro_pts_to qs ();
    intro_pts_to qs' ()


let gather (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhostT (_:unit{ disjoint_qbits qs qs'}) o
    (pts_to qs state `star` pts_to qs' state')
    (fun _ -> pts_to (qs `OrdSet.union` qs') (state `tensor` state'))
  = let perm = elim_exists #pperm #_ #(fun pperm -> P.pts_to qstar_state ({frac = Some pperm; qs; state})) () in
    let perm' = elim_exists #pperm #_ #(fun pperm -> P.pts_to qstar_state ({frac = Some pperm; qs=qs'; state=state'})) () in
    P.gather qstar_state ({frac = Some (Ghost.reveal perm); qs; state})
                         ({frac = Some (Ghost.reveal perm'); qs=qs'; state=state'});
    rewrite (P.pts_to qstar_state _)
            (P.pts_to qstar_state ({frac=Some (sum_perm perm perm'); qs=(qs `OrdSet.union` qs'); state=(state `tensor` state')}));
    intro_pts_to _ ()


let project (q:qbit)
            (qs:qbits {q `OrdSet.mem` qs })
            (b:bool)
            (s:qvec qs)
  : option (qvec (qs `OrdSet.minus` single q))
  = admit ()


[@@warn_on_use "uses an axiom"]
noextract
assume //benign; this is defining admit__
val admit__ (#a:Type)
            (#p:pre_t)
            (#q:a -> vprop)
            (_:unit)
  : STF a p q True (fun _ -> False)

let measure (q:qbit)
            (qs:qbits { q `OrdSet.mem` qs })
            (state:qvec qs)
  : STT (b:bool { Some? (project q qs b state) })
    (pts_to qs state)
    (fun b -> pts_to (single q) (singleton q b) `star`
           pts_to (qs `OrdSet.minus` (single q)) (disc q qs b state))
  = admit__()

let alloc ()
  = admit__ ()
  
let discard (q:qbit) (qstate:qvec (single q))
  : STT unit (pts_to (single q) qstate) (fun _ -> emp)
  = admit__()
