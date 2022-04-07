module QInst

open FStar.List.Tot
open FStar.Mul

open FStar.Real

open QMap
open QState

let pre = valid_qmap -> prop
let post a = a -> valid_qmap -> valid_qmap -> prop

// common pre- and post-conditions
let trivpre : pre = fun _ -> True
let eqpost #a : post a = fun _ s0 s1 -> s0 == s1

// quantum state + index into a random boolean stream
// NOTE: rather than an index, we could pass around a source of 
//       nondeterminism directly
let state (n:nat) = qstate n & nat

// type for functions defining an instruction's semantics
type sem_ty (a:Type) (pre:pre) (post:post a) =
    m0:valid_qmap{pre m0} -> 
    (nat -> bool) -> // random bit stream to choose measurement result 
    state (size_of m0) -> 
    v:a & m1:valid_qmap{post v m0 m1} & state (size_of m1)

// In order for semantic function f to have an adjoint, we require that:
// * f's return type is unit
// * f's postcondition is eqpost
// TODO: check with Sarah - what are the requirements in Q# for an
//       operation to be controllable/adjointable? Are classical
//       parameters allowed? Non-unit return types? Qubit allocation?
let is_adj (pre:pre) (f:sem_ty unit pre eqpost) (fadj:sem_ty unit pre eqpost) : prop =
  forall m0 bs s0. 
    let (| _, m1, s1 |) = f m0 bs s0 in
    let (| _, m2, s2 |) = fadj m1 bs s1 in
    s0 == s2

// TODO: generalize to a list of controls
let is_ctl (pre:pre) (f:sem_ty unit pre eqpost) (fctl:qref -> sem_ty unit pre eqpost) : prop =
  forall q m0 bs s0. 
    let (qs0, n0) = s0 in
    let (| _, m1, (qs1, n1) |) = f m0 bs s0 in
    let (| _, m2, (qs2, n2) |) = fctl q m0 bs s0 in
    n1 == n2 /\ 
    (in_1q_classical_state (sel m0 q) Zero qs0 ==> qs0 == qs2) /\
    (in_1q_classical_state (sel m0 q) One qs0 ==> 
       in_1q_classical_state (sel m0 q) One qs2 /\
       qs1 == qs2) // the rest of qs2 is the same as qs1

noeq
type inst (a:Type) = {
 
   // pre- and post-conditions
   pre: pre;
   post: post a;

   // semantics function
   sem: sem_ty a pre post;
   
   // optional implementation of adjoint
   adj: option (sem_ty a pre post);
   adj_pf: squash (Some? adj ==> 
                     (a == unit /\ 
                      eqpost == post /\ 
                      is_adj pre sem (Some?.v adj)));
                          
   // optional implementation of control
   ctl: option (sem_ty a pre post);
   ctl_pf: squash (Some? ctl ==> 
                     (a == unit /\ 
                      eqpost == post /\ 
                      is_adj pre sem (Some?.v adj)));
                          
}

/// Example instructions

let had (q:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_H (sel s0 q) qs, n) |) in
{ 
  pre = (fun s -> live s q);
  post = eqpost;
  sem = sem;
  adj = Some sem;
  adj_pf = ()
}

let pauli_x (q:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_X (sel s0 q) qs, n) |) in
{ 
  pre = (fun (s:valid_qmap) -> live s q);
  post = eqpost;
  sem = sem;
  adj = Some sem;
  adj_pf = ()
} 

let pauli_z (q:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_Z (sel s0 q) qs, n) |) in
{ 
  pre = (fun (s:valid_qmap) -> live s q);
  post = eqpost;
  sem = sem;
  adj = Some sem;
  adj_pf = ()
} 

let t_rot (q:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_T (sel s0 q) qs, n) |) in
  let adj : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_TDG (sel s0 q) qs, n) |) in  
{ 
  pre = (fun (s:valid_qmap) -> live s q);
  post = eqpost;
  sem = sem;
  adj = Some adj;
  adj_pf = ()
} 

let s_rot (q:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_S (sel s0 q) qs, n) |) in
  let adj : sem_ty unit (fun s -> live s q) eqpost =
    fun s0 _ (qs, n) -> (| (), s0, (apply_SDG (sel s0 q) qs, n) |) in
{ 
  pre = (fun (s:valid_qmap) -> live s q);
  post = eqpost;
  sem = sem;
  adj = Some adj;
  adj_pf = ()
} 

let cnot (q0 q1:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q0 /\ live s q1 /\ q0 <> q1) eqpost =
    fun s0 _ (qs, n) -> 
      (| (), s0, (apply_CNOT (sel s0 q0) (sel s0 q1) qs, n) |) in
{ 
  pre = (fun s -> live s q0 /\ live s q1 /\ q0 <> q1);
  post = eqpost;
  sem = sem;
  adj = Some sem;
  adj_pf = ()
} 

let cz (q0 q1:qref) : inst unit = 
  let sem : sem_ty unit (fun s -> live s q0 /\ live s q1 /\ q0 <> q1) eqpost =
    fun s0 _ (qs, n) -> 
      (| (), s0, (apply_CZ (sel s0 q0) (sel s0 q1) qs, n) |) in
{ 
  pre = (fun s -> live s q0 /\ live s q1 /\ q0 <> q1);
  post = eqpost;
  sem = sem;
  adj = Some sem;
  adj_pf = ();
} 

let meas (q:qref) : inst result = 
{ 
  pre = (fun (s:valid_qmap) -> live s q);
  post = eqpost;
  sem = (fun s0 bs (qs, n) ->
    if (bs n) 
    then let (p', qs') = measure (sel s0 q) Zero qs in
         (| Zero, s0, (qs', n + 1) |)
    else let (p', qs') = measure (sel s0 q) One qs in
         (| One, s0, (qs', n + 1) |));
  adj = None;
  adj_pf = ();
  ctl = None;
  ctl_pf = ();
}

let init : inst qref = 
{ 
  pre = trivpre;
  post = (fun q s0 s1 -> q == fst (extend s0) /\
                      s1 == snd (extend s0));
  sem = (fun s0 _ st ->
    let (qs, n) = st in
    let (q, s0') = extend s0 in
    (| q , s0' , (init qs, n) |));
  adj = None;
  adj_pf = ();
  ctl = None;
  ctl_pf = ();
}

let discard : inst unit = 
{ 
  pre = (fun s -> size_of s > 0 == true);
  post = (fun _ s0 s1 -> size_of s0 > 0 /\ shrink s0 == s1);
  sem = (fun s0 _ (qs, n) -> 
    (| () , shrink s0 , (discard qs, n) |));
  adj = None;
  adj_pf = ();
  ctl = None;
  ctl_pf = ();
}

noeq
type inst_tree (a:Type0) : pre -> post a -> Type =
| Return : q:post a -> 
           x:a -> 
//           inst_tree a (fun s0 -> q x s0 s0) (fun y s0 s1 -> y == x /\ q y s0 s1)           
           inst_tree a (fun s0 -> q x s0 s0) q

// Don't lose any information when sequentially composing i with k
| Action : #b:Type0 ->
           #p:(b -> pre) ->
           #q:(b -> post a) ->
           i:inst b ->
           k:(x:b -> inst_tree a (p x) (q x)) ->
           inst_tree a 
                     (fun s0 -> i.pre s0 /\ (forall x s1. i.post x s0 s1 ==> p x s1))
                     (fun x s0 s2 -> (exists y s'. i.post y s0 s' /\ q y x s' s2))

// Allow reindexing by strengthening pre and weakening post
| Weaken : #p:pre -> #q:post a -> 
           p':pre -> q':post a ->
           _:squash (forall s0. p' s0 ==> p s0) ->
           _:squash (forall x s0 s1. p' s0 /\ q x s0 s1 ==> q' x s0 s1) -> 
           inst_tree a p q -> 
           inst_tree a p' q'

let rec eval_inst_tree #a #pre #post (it: inst_tree a pre post) 
      (m0:valid_qmap{pre m0}) (bs:nat -> bool) (s:state (size_of m0)) 
  : Tot (v:a & m1:valid_qmap{post v m0 m1} & state (size_of m1)) 
        (decreases it) 
  = match it with
    | Return _ v -> (| v, m0, s |)

    | Action i k -> 
        let (| v, m1, s1 |) = i.sem m0 bs s in
        let (| v', m2, s2 |) = eval_inst_tree (k v) m1 bs s1 in
        (| v', m2, s2 |) //repack for the expected type

    | Weaken _ _ _ _ f -> 
      let (| v, m1, qs' |) = eval_inst_tree f m0 bs s in
      (|v, m1, qs'|)

module I = FStar.IndefiniteDescription

#push-options "--warn_error -271"
let aux #a #b #c (q:post a)
                 (ipost:post c)
                 (kq:c -> post a)
                 (s:a -> post b)
  : Lemma (requires (forall (x:a) (s0 s1:valid_qmap). q x s0 s1 <==> (exists (z:c) s0'. ipost z s0 s0' /\ kq z x s0' s1)))
          (ensures  (forall (y:b) (s0 s2:valid_qmap). 
                        (exists (z:c) (s1:valid_qmap). ipost z s0 s1 /\ (exists (x:a) s1'. kq z x s1 s1' /\ s x y s1' s2)) ==>
                        (exists (x:a) (s1:valid_qmap). q x s0 s1 /\ s x y s1 s2)))
  = let aux (y:b) (s0 s2:valid_qmap)
      : Lemma (requires (exists (z:c) (s1:valid_qmap). ipost z s0 s1 /\ (exists (x:a) s1'. kq z x s1 s1' /\ s x y s1' s2)))
              (ensures   (exists (x:a) (s1:valid_qmap). q x s0 s1 /\ s x y s1 s2))
              [SMTPat()]
      = let z = I.indefinite_description_ghost _ (fun (z:c) -> exists (s1:valid_qmap). ipost z s0 s1 /\ (exists (x:a) s1'. kq z x s1 s1' /\ s x y s1' s2)) in
        let s1 = I.indefinite_description_ghost _ (fun (s1:valid_qmap) -> ipost z s0 s1 /\ (exists (x:a) s1'. kq z x s1 s1' /\ s x y s1' s2)) in
        let x = I.indefinite_description_ghost _ (fun (x:a) -> exists s1'. kq z x s1 s1' /\ s x y s1' s2) in
        let s1' = I.indefinite_description_ghost _ (fun s1' -> kq z x s1 s1' /\ s x y s1' s2) in        
        assert (ipost z s0 s1);
        assert (kq z x s1 s1');
        assert (q x s0 s1');
        assert (s x y s1' s2)
    in
    ()
#pop-options

// See that `bind` has morally the same signature as the Action node
// i.e., a generalized rule for sequential composition in admissible in our Hoare logic
// i.e., it's not necessary to nest a continuation to the right only
unfold
let bind_pre
      (#a:Type) 
      (p:pre) 
      (q:post a)
      (r:a -> pre)
   : pre
   = fun s0 -> p s0 /\ (forall x s1. q x s0 s1 ==> r x s1)

unfold
let bind_post
      (#a:Type) 
      (#b:Type) 
      (q:post a)
      (s:a -> post b)
  : post b 
  = (fun x s0 s2 -> exists y s1. q y s0 s1 /\ s y x s1 s2)
  
let rec bind 
      (#a:Type) 
      (#b:Type) 
      (#p:pre) 
      (#q:post a)
      (#r:a -> pre)
      (#s:a -> post b)
      (it1:inst_tree a p q) 
      (it2:(x:a -> inst_tree b (r x) (s x))) 
    : Tot (inst_tree b (bind_pre p q r) (bind_post q s))
      (decreases it1)
    = match it1 with
      | Return _ v ->
        Weaken _ _ () () (it2 v)

      | Action #_ #c #kp #kq i k ->
        let j 
          : inst_tree b
              (fun s0 -> i.pre s0 /\ 
                      (forall x s1. i.post x s0 s1 ==>
                           (kp x s1 /\ (forall y s2. kq x y s1 s2 ==> r y s2)
                       )))
              (fun x s0 s2 ->         
                      exists y s1. i.post y s0 s1 /\
                              (exists z s1'. kq y z s1 s1' /\ s z x s1' s2))
          = Action i (fun x -> 
              let r : inst_tree b 
                      (fun s0 -> kp x s0 /\ (forall y s1. kq x y s0 s1 ==> r y s1))
                      (fun y s0 s2 -> exists z s1. kq x z s0 s1 /\ s z y s1 s2)
                    = bind (k x) it2 in 
               r) in
        let j' : inst_tree b
              (fun s0 -> p s0 /\ (forall x s1. q x s0 s1 ==> r x s1))
              (fun x s0 s2 ->         
                      exists y s1. i.post y s0 s1 /\
                              (exists z s1'. kq y z s1 s1' /\ s z x s1' s2))
            = Weaken _ _ () () j in
        aux q i.post kq s;
        let j'' : inst_tree b
              (fun s0 -> p s0 /\ (forall x s1. q x s0 s1 ==> r x s1))
              (fun x s0 s2 ->         
                      exists y s1. q y s0 s1 /\ s y x s1 s2)
            = Weaken _ _ () () j' in
        j''
        
      | Weaken _p _q pf1 pf2 it1' -> 
        Weaken _ _ () () (bind it1' it2)

// adjoint requires that every instruction is adjointable
let rec is_adjointable #a #pre #post (it:inst_tree a pre post) : prop =
  match it with
  | Return post _ -> a == unit /\ post == eqpost
  | Action i k -> (Some? i.adj) /\ (forall v. is_adjointable (k v))
  | Weaken _ _ _ _ it' -> is_adjointable it'

let get_adj #a (i:inst a{Some? i.adj}) : inst a =
{
  pre = i.pre;
  post = eqpost;
  sem = Some?.v i.adj;
  adj = None;
  adj_pf = ()
}

let lemma_is_adjointable #a #pre #post (it:inst_tree a pre post) 
  : Lemma (requires (is_adjointable it))
          (ensures (a == unit /\ post == eqpost))
          [SMTPat (is_adjointable it)]
  = admit() // pretty sure this is true (and needed for the defn below) -KH

let rec adjoint #a #pre #post (it:inst_tree a pre post{is_adjointable it}) 
  : inst_tree a pre post
  = match it with
    | Return post v -> Return post v
    | Action i k -> Weaken pre post () ()
                     (bind (adjoint (k ())) 
                        (fun v -> Action (get_adj i) (fun _ -> Return post v))) 
    | Weaken _p _q pf1 pf2 it' -> Weaken _ _ () () (adjoint it')

// more generally, we can consider inst_tree it1 to be the adjoint of
// inst_tree it2 if it1 followed by it2 returns the state to its original
// value. TODO: this isn't necessarily the proper mathematical adjoint, which
// would also require that it2 followed by it1 is the identity -- what's
// a more precise name for this operation?
let is_adjoint #a1 #a2 #pre1 #pre2 #post1 #post2 
      (it1:inst_tree a1 pre1 post1) (it2:inst_tree a2 pre2 post2)
      (_:squash (forall v m0 m1. pre1 m0 /\ post1 v m0 m1 ==> pre2 m1)) : prop
  = forall m0 bs s0.
      let (| _, m1, s1 |) = eval_inst_tree it1 m0 bs s0 in
      let (| _, m2, s2 |) = eval_inst_tree it2 m1 bs s1 in
      m0 == m2 /\ s0 == s2

// our "adjoint" function will always produce a program that satisfies this criterion
let lemma_adjoint_is_adjoint #a #pre #post (it:inst_tree a pre post)
  : Lemma (requires (is_adjointable it))
          (ensures (is_adjoint it (adjoint it) ()))
  = admit()

let init_body_pre p : pre = fun s0 ->
    init.pre s0 /\
    (forall (x: qref) (s1: valid_qmap).
       init.post x s0 s1 ==>
       (exists (sinit: valid_qmap). p sinit /\ init.post x sinit s1))

let init_body_post #a q : post a = fun x s0 s2 ->
    exists (y: qref) (s': valid_qmap).
      init.post y s0 s' /\
      (discard.pre s2 /\
       (forall (sinit: valid_qmap) (sfinal: valid_qmap).
         init.post y sinit s' /\
         discard.post () s2 sfinal ==>
         q x sinit sfinal))
        
let init_body #a
      (pre:pre)
      (post:post a)
      (body : (qb:qref) -> 
              inst_tree a 
                (fun s0 -> 
                  exists sinit.
                    pre sinit /\
                    init.post qb sinit s0) 
                (fun v s0 s1 -> 
                   discard.pre s1 /\
                   (forall sinit sfinal. 
                     init.post qb sinit s0 /\
                     discard.post () s1 sfinal ==>
                     post v sinit sfinal)))
  : inst_tree a (init_body_pre pre) (init_body_post post)
  = Action init body

let return_v_post #a (v:a) : post a = fun x s0 s1 -> x == v /\ s0 == s1

let discard_return_pre #a (v:a) 
  : pre 
  = fun s0 -> discard.pre s0 /\
           (forall (x: Prims.unit) (s1: QMap.valid_qmap).
                  discard.post x s0 s1 ==> return_v_post v v s1 s1)

let discard_return_post #a (v:a) : post a = 
    fun x s0 s2 ->
        exists (y: Prims.unit) (s': QMap.valid_qmap).
          discard.post y s0 s' /\ return_v_post v x s' s2

let discard_return #a (post:post a) (v:a)
  : inst_tree a 
              (discard_return_pre v)
              (discard_return_post v)
  = Action discard (fun _ -> Return (return_v_post v) v)

let using_body #a
      (pre:pre)
      (post:post a)
      (body : (qb:qref) -> 
              inst_tree a 
                (fun s0 -> 
                  exists sinit.
                    pre sinit /\
                    init.post qb sinit s0) 
                (fun v s0 s1 -> 
                   discard.pre s1 /\
                   (forall sinit sfinal. 
                     init.post qb sinit s0 /\
                     discard.post _ s1 sfinal ==>
                     post v sinit sfinal)))
   : inst_tree a 
               (bind_pre (init_body_pre pre)
                         (init_body_post post)
                         (discard_return_pre))
               (bind_post (init_body_post post)
                          (discard_return_post))
   = bind (init_body pre post body)
          (discard_return post)

// This would be a nice type in the long run, but requires a sep logic
// of some sort

// let using #a
//       (pre:pre)
//       (post:post a)
//       (body : (qb:qref) -> 
//                 inst_tree a 
//                   (pre `star` perm qb)
//                   (fun x -> post x `star` perm qb))
//     : inst_tree a pre post

let using #a
      (pre:pre)
      (post:post a)
      (body : (qb:qref) -> 
              inst_tree a
                (fun s0 -> 
                  exists sinit.
                    pre sinit /\
                    init.post qb sinit s0) 
                (fun v s0 s1 -> 
                   discard.pre s1 /\
                   (forall sinit sfinal. 
                     init.post qb sinit s0 /\
                     discard.post _ s1 sfinal ==>
                     post v sinit sfinal)))
  : inst_tree a pre post
  = Weaken pre post () () (using_body pre post body)

let cond #a (#p1 #p2:pre) (#q1 #q2:post a) (p:pre) (q:post a) 
      (bexp:bool) 
      (it1:inst_tree a p1 q1{forall s0. (p s0 ==> p1 s0) /\ (p s0 ==> p2 s0)}) 
      (it2:inst_tree a p2 q2{forall x s0 s1. 
                             (p s0 /\ q1 x s0 s1 ==> q x s0 s1) /\
                             (p s0 /\ q2 x s0 s1 ==> q x s0 s1)})
  : inst_tree a p q
  = if bexp
    then Weaken _ _ () () it1 
    else Weaken _ _ () () it2

let cond' #a (#p1 #p2:pre) (#q1 #q2:post a)
      (bexp:bool) 
      (it1:inst_tree a p1 q1)
      (it2:inst_tree a p2 q2)
  : inst_tree a (fun s0 -> if bexp then p1 s0 else p2 s0)
                (fun x s0 s1 -> if bexp then q1 x s0 s1 else q2 x s0 s1)
  = if bexp
    then Weaken _ _ () () it1
    else Weaken _ _ () () it2

let return #a (p:post a) (v:a) = Return (fun x s0 s1 -> x == v /\ p x s0 s1) v
