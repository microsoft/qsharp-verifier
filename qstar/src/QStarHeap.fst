module QStarHeap
open FStar.PCM
open FStar.OrdSet
open FStar.Real
module Frac = Steel.FractionalPermission

open QState

noeq
type qstate = {
  frac:option Frac.perm;
  qs:qbits;
  state:qvec qs;
}

let unit_qstate = { frac=None; qs=empty_qbits; state=empty_qvec}

let composable_frac_opt (f0 f1:option Frac.perm)
  : Type
  = match f0, f1 with
    | None, _
    | _, None -> True
    | Some p0, Some p1 ->
      Frac.(sum_perm p0 p1 `lesser_equal_perm` full_perm)

let compose_frac_opt (f0:option Frac.perm)
                     (f1:option Frac.perm { composable_frac_opt f0 f1 })
  : option Frac.perm
  = match f0, f1 with
    | None, f
    | f, None -> f
    | Some f0, Some f1 -> Some (Frac.sum_perm f0 f1)

let composable
  : symrel qstate
  = fun (q0 q1:qstate) ->
      composable_frac_opt q0.frac q1.frac /\
      disjoint_qbits q0.qs q1.qs

let compose (q0:qstate) (q1:qstate{composable q0 q1})
  : qstate
  = { frac = compose_frac_opt q0.frac q1.frac;
      qs = OrdSet.union q0.qs q1.qs;
      state = q0.state `tensor` q1.state }

let core : pcm' qstate = {
  composable;
  op = compose;
  one = unit_qstate
}

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 3"
let tensor_ac ()
  : Lemma (union_ac();
           // tensor is a PCM
           (forall (qs0:_) (qs1:_{disjoint_qbits qs0 qs1}) (v0:qvec qs0) (v1:qvec qs1).
              tensor v0 v1 == tensor v1 v0) /\
           (forall (qs0:_)
              (qs1:_{disjoint_qbits qs0 qs1})
              (qs2:_{disjoint_qbits (OrdSet.union qs0 qs1) qs2})
              (v0:qvec qs0)
              (v1:qvec qs1)
              (v2:qvec qs2).
              tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2)) /\
           (forall (qs0:_)
              (qs1:_)
              (qs2:_{disjoint_qbits qs1 qs2 /\ disjoint_qbits qs0 (OrdSet.union qs1 qs2)})
              (v0:qvec qs0)
              (v1:qvec qs1)
              (v2:qvec qs2).
              tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2)) /\
           (forall qs0 (v0:qvec qs0).
              tensor v0 empty_qvec == v0))
  = union_ac();
    introduce forall (qs0:_) (qs1:_{disjoint_qbits qs0 qs1}) (v0:qvec qs0) (v1:qvec qs1).
              tensor v0 v1 == tensor v1 v0
    with tensor_comm qs0 qs1 v0 v1;

    introduce forall qs0 (v0:qvec qs0). tensor v0 empty_qvec == v0
    with tensor_unit _ v0;

    introduce forall (qs0:_)
                (qs1:_{disjoint_qbits qs0 qs1})
                (qs2:_{disjoint_qbits (OrdSet.union qs0 qs1) qs2})
                (v0:qvec qs0)
                (v1:qvec qs1)
                (v2:qvec qs2).
              tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2)
    with tensor_assoc_l v0 v1 v2;

    introduce forall (qs0:_)
                (qs1:_)
                (qs2:_{disjoint_qbits qs1 qs2 /\ disjoint_qbits qs0 (OrdSet.union qs1 qs2)})
                (v0:qvec qs0)
                (v1:qvec qs1)
                (v2:qvec qs2).
              tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2)
    with tensor_assoc_r v0 v1 v2
#pop-options

// a bit lazy: just calling tensor AC and letting the SMT solver do the rest
#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 3"
let qstar_heap_pcm : pcm qstate =
  union_ac();
  tensor_ac ();
{
  p = core;
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun qs -> qs.frac == Some Frac.full_perm)
}
#pop-options

let applyH_fpupd (#qs:qbits)
                 (#perm:_)
                 (#qstate_init:_)
                 (q:qbit{mem q qs})
   : frame_preserving_upd qstar_heap_pcm
                          ({frac=Some perm; qs=qs; state=qstate_init})
                          ({frac=Some perm; qs=qs; state=(QState.applyH #qs q qstate_init)})
   = fun v ->
      assert (
          qstar_heap_pcm.refine v /\
          PCM.compatible qstar_heap_pcm ({frac=Some perm; qs=qs; state=qstate_init}) v
      );
      // (1) v.state = qstate_init `tensor` rest
      let init_knowledge = {frac=Some perm; qs=qs; state=qstate_init} in
      let vst : qvec v.qs = v.state in
      assert (exists frame_qs'. frame_qs' `disjoint` qs /\
                           (frame_qs' `union` qs == v.qs));
      assert (exists (frame: qstate).
                PCM.composable qstar_heap_pcm init_knowledge frame /\
                PCM.op qstar_heap_pcm frame init_knowledge == v /\
                frame.state `tensor` qstate_init == v.state);

      applyH q : qvec qs -> qvec qs
      lift qs
           (qs':_{qs' `disjoint` qs})
           (op: qvec qs -> qvec qs) : qvec (qs `union` qs') -> qvec (qs `union` qs')

    { i = (v:qvec qs) `tensor` (v':qvec qs') }
      lift qs qs' op i
    { i = (op v:qvec qs) `tensor` (v':qvec qs') }

      admit()
      // (2) vnew = {v with state (applyH q qstate_init) `tensor` rest }
      // (3) prove that vnew
      //     - is a "full" value
      //     - it's compatible with ({frac=Some perm; qs=qs; state=(QState.applyH #qs q qstate_init)})
      //     - and that it preserves all frames that were composaible with the initial knowledge (qs -> qstate_init)


      admit()


         } )


val applyH_raw (#qs:qbits)
               (#perm:_)
               (#qstate_init:qvec qs)
               (q:qbit{mem q qs})
               (qref: Ref.ref qstar_heap_pcm)
  : ST unit
    (Ref.pts_to qref
        ({frac=Some perm; qs=qs; state=qstate_init}))
    (fun _ ->
       Ref.pts_to qref
        ({frac=Some perm;
          qs=qs;
          state=(QState.applyH #qs q qstate_init)})


let pts_to (qs:qbits) (qv:qvec qs)
  : vprop
  = exists_ (fun p ->
    Ref.pts_to qstar_heap_ref
             ({frac = Some p;
               qs = qs;
               state = qv})

let applyH (#qs:qbits)
           (#perm:_)
           (#qstate_init:qvec qs)
           (q:qbit{mem q qs})
  : ST unit
    (qs `pts_to` qstate_init)
    (fun _ ->
      qs `pts_to` (QState.applyH q qstate_init))
   =

module Ref = Steel.ST.PCMReference

val qstar_heap_ref
  : Ref.ref qstar_heap_pcm
