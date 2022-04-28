module QStarRef
open Steel.ST.Util
open QVec
open QStarHeap
module P = Steel.ST.GhostPCMReference

let core_ref = P.ref _ qstar_heap_pcm

//All the qubits are stores in this ref cell
assume
val qstar_state : core_ref

let pts_to (qs:qbits) (state:qvec qs) =
  exists_ (fun perm -> P.pts_to qstar_state ({frac=Some perm; qs; state}))

let apply_gate (qs:qbits) (#state:qvec qs) (gate:qvec qs -> qvec qs)
  : STT unit
    (pts_to qs state)
    (fun _ -> pts_to qs (gate state))
  = let perm = elim_exists () in
    P.upd_gen qstar_state ({frac=Some (Ghost.reveal perm); qs; state}) ({frac=Some (Ghost.reveal perm); qs;state=gate state})
      (QStarHeap.apply_fpupd #qs #perm #state gate);
    intro_exists_erased perm (fun perm -> P.pts_to qstar_state ({frac=Some perm; qs; state=gate state}))

let share (#o:_) (qs:qbits) (qs':qbits{ disjoint_qbits qs qs'}) (#state:qvec qs) (#state':qvec qs')
  : STGhostT unit o
    (pts_to (qs `OrdSet.union` qs')
            (state `tensor` state'))
    (fun _ -> pts_to qs state `star` pts_to qs' state')
  = admit_()
