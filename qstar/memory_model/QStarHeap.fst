module QStarHeap
open FStar.PCM
open FStar.OrdSet
open FStar.Real
module Frac = Steel.FractionalPermission

let qbit = nat

let qbits = FStar.OrdSet.ordset qbit (<=)

let complex = real & real

let dimension (qs:qbits) =
  if size qs = 0 then 0
  else pow2 (size qs)

let vector (a:Type) (l:nat) = FStar.Seq.lseq a l

let qvec (qs:qbits) = vector complex (dimension qs)

let empty_qbits : qbits = OrdSet.empty

let empty_qvec : qvec empty_qbits = Seq.empty

let disjoint_qbits (q0 q1:qbits) =
   (OrdSet.intersect q0 q1 `OrdSet.equal` empty_qbits)

let union_empty (q:qbits)
  : Lemma (union q empty_qbits `OrdSet.equal` q)
          [SMTPat (union q empty_qbits)]
  = ()

let union_ac ()
  : Lemma ((forall (qs0 qs1 qs2:qbits).
              union qs0 (union qs1 qs2) `OrdSet.equal` union (union qs0 qs1) qs2) /\
           (forall (qs0 qs1:qbits).
              union qs0 qs1 `OrdSet.equal` union qs1 qs0) /\
           (forall (q:qbits). union q empty_qbits `OrdSet.equal` q))
  = ()

assume
val tensor (#qs0:qbits)
           (#qs1:qbits {disjoint_qbits qs0 qs1})
           (v0:qvec qs0)
           (v1:qvec qs1)
  : qvec (union qs0 qs1)

assume
val tensor_unit (qs:qbits) (v:qvec qs)
  : Lemma
    (ensures tensor v empty_qvec == v)

assume
val tensor_comm (qs0 qs1:qbits) (v0:qvec qs0) (v1:qvec qs1)
  : Lemma
    (requires disjoint qs0 qs1)
    (ensures tensor v0 v1 == tensor v1 v0)

assume
val tensor_assoc_l (#qs0:_)
                   (#qs1:_{disjoint_qbits qs0 qs1})
                   (#qs2:_{disjoint_qbits (OrdSet.union qs0 qs1) qs2})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (union_ac();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))

assume
val tensor_assoc_r (#qs0:_)
                   (#qs1:_)
                   (#qs2:_{disjoint_qbits qs1 qs2 /\ disjoint_qbits qs0 (OrdSet.union qs1 qs2)})
                   (v0:qvec qs0)
                   (v1:qvec qs1)
                   (v2:qvec qs2)
   : Lemma (union_ac ();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))

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
