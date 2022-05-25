module QStar.Ref
open Steel.ST.Util
open QStar.Steel.Util
open QStar.Vec
open QStar.Heap
module M = QStar.Matrix
module P = Steel.ST.GhostPCMReference

let core_ref = P.ref _ qstar_heap_pcm

//All the qubits are stores in this ref cell
assume
val qstar_state : core_ref

let pperm = p:perm {p `lesser_equal_perm` full_perm}

let pts_to (qs:qbits) ([@@@smt_fallback]state:qvec qs) : vprop =
  exists_ (fun (perm:pperm) -> P.pts_to qstar_state ({frac=Some perm; qs; state}))

let apply_gate (#qs:qbits) (#state:qvec qs) (g:gate qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (apply g state))
  = let perm = elim_exists () in
    P.upd_gen qstar_state ({frac=Some (Ghost.reveal perm); qs; state}) ({frac=Some (Ghost.reveal perm); qs;state=apply g state})
      (QStar.Heap.apply_fpupd #qs #perm #state g);
    intro_exists_erased #pperm perm (fun perm -> P.pts_to qstar_state ({frac=Some perm; qs; state=apply g state}))

let split_perm (p:pperm)
  : c:pperm{ composable_frac_opt (Some c) (Some c) }
  = half_perm p

let intro_pts_to #o (#p:pperm) qs #s ()
  : STGhostT unit o
    (P.pts_to qstar_state ({frac = Some p; qs; state=s}))
    (fun _ -> pts_to qs s)
  = intro_exists #pperm p (fun p -> P.pts_to qstar_state ({frac = Some p; qs; state=s}));
    ()

let share (#o:_) (qs:qbits) (qs':qbits) (#state:qvec qs) (#state':qvec qs')
  : STGhost unit o
    (pts_to (qs `union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')
    (requires disjoint qs qs')
    (ensures fun _ -> True)
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
  : STGhost unit o
    (pts_to qs state `star` pts_to qs' state')
    (fun _ -> pts_to (qs `union` qs') (state `tensor` state'))
    (requires True)
    (ensures fun _ -> disjoint qs qs')
  = let perm = elim_exists #pperm #_ #(fun pperm -> P.pts_to qstar_state ({frac = Some pperm; qs; state})) () in
    let perm' = elim_exists #pperm #_ #(fun pperm -> P.pts_to qstar_state ({frac = Some pperm; qs=qs'; state=state'})) () in
    P.gather qstar_state ({frac = Some (Ghost.reveal perm); qs; state})
                         ({frac = Some (Ghost.reveal perm'); qs=qs'; state=state'});
    rewrite (P.pts_to qstar_state _)
            (P.pts_to qstar_state ({frac=Some (sum_perm perm perm'); qs=(qs `union` qs'); state=(state `tensor` state')}));
    intro_pts_to _ ()


let measure (#qs:qbits)
            (#state:qvec qs)
            (q:qbit)
  : ST bool
    (pts_to qs state)
    (fun b -> pts_to (single q) (singleton q b) `star`
           pts_to (qs `minus` (single q)) (proj_and_disc q b state))
    (requires q `mem` qs)
    (ensures fun _ -> True)
  = admit__()

let alloc ()
  = admit__ ()
  
let discard (q:qbit) (qstate:qvec (single q))
  : STT unit (pts_to (single q) qstate) (fun _ -> emp)
  = admit__()
