module QState

open FStar.Mul
//open FStar.Real
//open Complex
//open Matrix
//open Quantum

module F = FStar.FunctionalExtensionality

let size_disjoint_union (#a:eqtype) (#f:cmp a) (s1 s2:ordset a f)
  : Lemma (requires (OrdSet.intersect s1 s2 `OrdSet.equal` OrdSet.empty))
          (ensures (OrdSet.size (union s1 s2) = OrdSet.size s1 + OrdSet.size s2))
          [SMTPat (size #a #f (union #a #f s1 s2))]
  = admit()

let dimension_union (qs0:qbits) (qs1:qbits{disjoint_qbits qs0 qs1})
  : Lemma (ensures dimension (union qs0 qs1) = dimension qs0 * dimension qs1)
          [SMTPat (dimension (union qs0 qs1))]
  = Math.Lemmas.pow2_plus (size qs0) (size qs1)

// Facts about swap matrix (when finished, move to Quantum.fst)
let swap_mat : matrix complex 4 4 =
  F.on (knat 4 & knat 4)
       (fun (i,j) ->
          if i = 0 && j = 0 then c1
          else if i = 1 && j = 2 then c1
          else if i = 2 && j = 1 then c1
          else if i = 3 && j = 3 then c1
          else c0)

// can we expose this in the OrdSet interface?
assume
val as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{sorted f l})

// we need some "reorder_indices" function to make the operation commutative
let tensor #qs0 #qs1 v0 v1 = 
  admit()
  //reorder_indices (as_list qs0) (as_list qs1) (kronecker_product v0 v1)

let tensor_unit qs v
  : Lemma (ensures tensor v empty_qvec == v)
  = admit()

let tensor_comm qs0 qs1 v0 v1
  : Lemma (requires disjoint qs0 qs1)
          (ensures tensor v0 v1 == tensor v1 v0)
  = admit()

let tensor_assoc_l #qs0 #qs1 #qs2 v0 v1 v2
   : Lemma (union_ac();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))
   = admit()

let tensor_assoc_r #qs0 #qs1 #qs2 v0 v1 v2
   : Lemma (union_ac ();
            tensor (tensor v0 v1) v2 == tensor v0 (tensor v1 v2))
   = admit()

let init #qs v = admit()

let disc #qs q v = admit() 

let meas #qs q b v = admit() 

let applyH #qs q v = admit() 

let applyCX #qs q1 q2 v = admit() 
