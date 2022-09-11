module QStar.Matrix

open FStar.Mul
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
open FStar.Tactics
module Math = FStar.Math.Lemmas

open QStar.Numeric

(* general types useful for matrices *)
type dim = i:int{i > 0} // type for matrix dimensions; don't worry about #rows or #cols = 0

[@unifier_hint_injective]
let knat (k:dim) = i:nat{i < k} // bounded nats for indices

(** vectors **)
[@(unifier_hint_injective)]
type vector 'a (l:dim) = knat l ^-> 'a

(* Constructors and destructors *)
val index_vec: #a:Type -> #l:dim -> vector a l -> knat l -> Tot a
let index_vec #a #l v i = v i

val create_vec: #a:Type -> l:dim -> a -> Tot (vector a l)
let create_vec #a l v = F.on (knat l) (fun i -> v)

val lemma_index_create_vec: #a:Type -> l:dim -> v:a -> i:knat l -> Lemma
  (ensures (index_vec (create_vec l v) i == v))
  [SMTPat (index_vec (create_vec l v) i)]
let lemma_index_create_vec #a _ _ _ = ()

(* Equality *)
val equal_vec (#a:Type) (#l:dim) (v1:vector a l) (v2:vector a l) : Type0
let equal_vec #a #l v1 v2 = F.feq v1 v2

// TODO: abstract is a parse error here. What is it supposed to do?
(*abstract*) val lemma_eq_intro_vec: #a:Type -> #l:dim -> v1:vector a l -> v2:vector a l -> Lemma
     (requires (forall (i:knat l).
                  {:pattern (v1 i; v2 i)} 
                  (v1 i == v2 i)))
     (ensures (equal_vec v1 v2))
     [SMTPat (equal_vec v1 v2)]
let lemma_eq_intro_vec #a #l v1 v2 = ()

(*abstract*) val lemma_eq_refl_vec: #a:Type -> #l:dim -> v1:vector a l -> v2:vector a l -> Lemma
     (requires (v1 == v2))
     (ensures (equal_vec v1 v2))
     [SMTPat (equal_vec v1 v2)]
let lemma_eq_refl_vec #a #l _ _ = ()

(*abstract*) val lemma_eq_elim_vec: #a:Type -> #l:dim -> v1:vector a l -> v2:vector a l -> Lemma
     (requires (equal_vec v1 v2))
     (ensures (v1 == v2))
     [SMTPat (equal_vec v1 v2)]
let lemma_eq_elim_vec #a #l _ _ = ()

(** matrices **)
//this unifier hint helps F* prove `matrix t m n == matrix s p q`
//by proving the arguments equal (rather than unfolding definitions)
[@(unifier_hint_injective)]
type matrix 'a (m:dim) (n:dim) = knat m & knat n ^-> 'a

(* Constructors and destructors *)
val index: #a:Type -> #m:dim -> #n:dim -> matrix a m n -> knat m -> knat n -> Tot a
let index #a #m #n x i j = x (i,j)

val create: #a:Type -> m:dim -> n:dim -> a -> Tot (matrix a m n)
let create #a m n v = F.on (knat m & knat n) (fun _ -> v)

val row: #a:Type -> #m:dim -> #n:dim -> matrix a m n -> knat m -> Tot (vector a n)
let row #a #m #n x i =
  F.on (knat n) (fun j -> x (i,j))

val col: #a:Type -> #m:dim -> #n:dim -> matrix a m n -> knat n -> Tot (vector a m)
let col #a #m #n x j =
  F.on (knat m) (fun i -> x (i,j))

val upd: #a:Type -> #m:dim -> #n:dim -> matrix a m n -> knat m -> knat n -> a -> Tot (matrix a m n)
let upd #a #m #n x i j v =
    F.on (knat m & knat n)
         (fun (i',j') -> if i = i' && j = j'
                      then v
                      else x (i',j'))

val lemma_index_create: #a:Type -> m:dim -> n:dim -> v:a -> i:knat m -> j:knat n -> Lemma
  (ensures (index (create m n v) i j == v))
  [SMTPat (index (create m n v) i j)]
let lemma_index_create #a _ _ _ _ _ = ()

val lemma_index_upd1: #a:Type -> m:dim -> n:dim -> x:matrix a m n -> i:knat m -> j:knat n -> v:a -> Lemma
  (ensures (index (upd x i j v) i j == v))
  [SMTPat (index (upd x i j v) i j)]
let lemma_index_upd1 #a _ _ _ _ _ _ = ()

val lemma_index_upd2: #a:Type -> m:dim -> n:dim -> x:matrix a m n -> i:knat m -> j:knat n -> i':knat m -> j':knat n -> v:a -> Lemma
  (requires (i<>i' \/ j<>j'))
  (ensures (index (upd x i j v) i' j' == index x i' j'))
  [SMTPat (index (upd x i j v) i' j')]
let lemma_index_upd2 #a _ _ _ _ _ _ _ _ = ()

(* Equality *)
val equal (#a:Type) (#m:dim) (#n:dim) (x1:matrix a m n) (x2:matrix a m n) : Type0
let equal #a #m #n x1 x2 = F.feq x1 x2

// TODO: abstract is a parse error (see above)
(*abstract*) val lemma_eq_intro: #a:Type -> #m:dim -> #n:dim -> x1:matrix a m n -> x2:matrix a m n -> Lemma
     (requires (forall (i:knat m) (j:knat n).
                  {:pattern ((index x1 i j); (index x2 i j)) \/ (x1 (i, j); x2 (i, j))}
                  (index x1 i j == index x2 i j)))
     (ensures (equal x1 x2))
     [SMTPat (equal x1 x2)]
let lemma_eq_intro #a #m #n x1 x2 = ()

(*abstract*) val lemma_eq_refl: #a:Type -> #m:dim -> #n:dim -> x1:matrix a m n -> x2:matrix a m n -> Lemma
     (requires (x1 == x2))
     (ensures (equal x1 x2))
     [SMTPat (equal x1 x2)]
let lemma_eq_refl #a #m #n _ _ = ()

(*abstract*) val lemma_eq_elim: #a:Type -> #m:dim -> #n:dim -> x1:matrix a m n -> x2:matrix a m n -> Lemma
     (requires (equal x1 x2))
     (ensures (x1 == x2))
     [SMTPat (equal x1 x2)]
let lemma_eq_elim #a #m #n _ _ = ()

(* Example matrices/vectors *)
let zero_matrix (a:Type) {| numeric a |} (m n:dim) : matrix a m n = 
  create m n zero

let id_matrix (a:Type) {| numeric a |} (m:dim) : matrix a m m = 
  F.on (knat m & knat m) 
       (fun (i,j) -> if i = j then one else zero)

(** linear algebra operations **)

// sum over vector
private 
let rec sum_i (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l) 
  : Tot a (decreases (l-i)) 
  = if i = l - 1 then (v i) else add (v i) (sum_i v (i+1))

let sum (#a:Type) {|numeric a|} (#l:dim) (v:vector a l) = sum_i v 0

// vector sum
let vec_sum #a {| numeric a |} (#l:dim) (v1 v2: vector a l) : vector a l
  = F.on (knat l) (fun i -> add (v1 i) (v2 i))

// vector product (dot product)
private 
let vec_prod_pointwise (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l) 
  : vector a l
  = F.on (knat l) (fun i -> mul (v1 i) (v2 i))

let vec_prod (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l) 
  : a
  = sum (vec_prod_pointwise v1 v2)

// matrix scalar product
let scale (#a:Type) {| numeric a |} (#m #n:dim) (c:a) (x:matrix a m n) 
  : matrix a m n 
  = F.on (knat m & knat n)
         (fun (i,j) -> mul c (index x i j))

// matrix addition
let matrix_add (#a:Type) {| numeric a |} (#m #n:dim) (x1 x2:matrix a m n)
  : matrix a m n
  = F.on (knat m & knat n)
         (fun (i,j) -> add (index x1 i j) (index x2 i j))

// matrix multiplication
let matrix_mul (#a:Type) {| numeric a |} (#m #n #p:dim) (x1:matrix a m n) (x2:matrix a n p) 
  : matrix a m p
  = F.on (knat m & knat p)
          (fun (i,j) -> vec_prod (row x1 i) (col x2 j))

// transpose
let transpose (#a:Type) (#m #n:dim) (x:matrix a m n)
  : matrix a n m
  = F.on (knat n & knat m) (fun (i,j) -> index x j i)

// conjugate transpose
let conjugate_transpose (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : matrix a n m
  = F.on (knat n & knat m) (fun (i,j) -> conj (index x j i))

// trace
private
let diagonal (#a:Type) (#m:dim) (x:matrix a m m)
  : vector a m
  = F.on (knat m) (fun i -> x (i,i))

let trace (#a:Type) {| numeric a |} (#m:dim) (x:matrix a m m)
  : a
  = sum (diagonal x)

// Kronecker product
let kronecker_product (#a:Type) {| numeric a |} (#m #n #p #q:dim) 
    (x1:matrix a m n) (x2:matrix a p q) 
  : matrix a (m * p) (n * q)
  = F.on (knat (m * p) & knat (n * q))
         (fun (i,j) -> mul (index x1 (i / p) (j / q)) (index x2 (i % p) (j % q)))

(** proofs about linear algebra operations **)

(* proofs about sums *)
// I don't know why I need to use the following 'def' lemmas. Shouldn't z3 be able to figure this out?
let lemma_sum_i_def_base (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l)
  : Lemma (requires (i == l - 1))
          (ensures (sum_i v i == v i)) 
  = ()
let lemma_sum_i_def_rec (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l)
  : Lemma (requires (i < l - 1))
          (ensures (sum_i v i == add (v i) (sum_i v (i+1))))
  = ()

private 
let rec lemma_sum_i_zero (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l)
  : Lemma (requires (forall (i : knat l). v i == zero))
          (ensures (sum_i v i == zero))
          (decreases (l - i))
  = if i = l - 1 then () else lemma_sum_i_zero v (i+1)

let lemma_sum_zero (#a:Type) {| numeric a |} (#l:dim) (v:vector a l)
  : Lemma (requires (forall (i : knat l). v i == zero))
          (ensures (sum v == zero))
  = lemma_sum_i_zero v 0

private 
let rec lemma_sum_i_singleton (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l) (x:a) (j:knat l)
   : Lemma (requires (forall (i' : knat l). if i = i' then (v i') == x else (v i') == zero))
           (ensures (if j > i then sum_i v j == zero else sum_i v j == x))
           (decreases (l - j))
  = if j = l - 1 then () else lemma_sum_i_singleton v i x (j+1)

let lemma_sum_singleton (#a:Type) {| numeric a |} (#l:dim) (v:vector a l) (i:knat l) (x:a)
  : Lemma (requires (forall (i' : knat l). if i = i' then (v i') == x else (v i') == zero))
          (ensures (sum v == x))
  = lemma_sum_i_singleton v i x 0

private
let lemma_add_swap (#a:Type) {| numeric a |} (x y z w:a)
  : Lemma (add (add x y) (add z w) == add (add x z) (add y w))
  = add_assoc x y (add z w);
    add_assoc y z w;
    add_comm z y;
    add_assoc z y w;
    add_assoc x z (add y w)

private
let rec lemma_sum_i_add (#a:Type) {| numeric a |} (#l:dim) (v1v2 v1 v2:vector a l) (i:knat l)
  : Lemma (requires (forall i. v1v2 i == add (v1 i) (v2 i)))
          (ensures (sum_i v1v2 i == add (sum_i v1 i) (sum_i v2 i)))
          (decreases (l - i))
  = if i = l - 1 then () 
    else (lemma_sum_i_add v1v2 v1 v2 (i+1);
          lemma_add_swap (v1 i) (v2 i) (sum_i v1 (i+1)) (sum_i v2 (i+1)))

let lemma_sum_add (#a:Type) {| numeric a |} (#l:dim) (v1 v2 v1v2:vector a l)
  : Lemma (requires (forall i. v1v2 i == add (v1 i) (v2 i)))
          (ensures (sum v1v2 == add (sum v1) (sum v2)))
  = lemma_sum_i_add v1v2 v1 v2 0

private
let rec lemma_sum_i_mul_l (#a:Type) {| numeric a |} (#l:dim) (c:a) (cv v:vector a l) (i:knat l)
  : Lemma (requires (forall i. cv i == mul c (v i)))
          (ensures (sum_i cv i == mul c (sum_i v i)))
          (decreases (l - i))
  = if i = l - 1 then () 
    else (lemma_sum_i_mul_l c cv v (i+1);
          add_mul_distr_l c (v i) (sum_i v (i+1)))

let lemma_sum_mul_l (#a:Type) {| numeric a |} (#l:dim) (c:a) (v cv:vector a l)
  : Lemma (requires (forall i. cv i == mul c (v i)))
          (ensures (sum cv == mul c (sum v)))
  = lemma_sum_i_mul_l c cv v 0

private
let rec lemma_sum_i_mul_r (#a:Type) {| numeric a |} (#l:dim) (c:a) (vc v:vector a l) (i:knat l)
  : Lemma (requires (forall i. vc i == mul (v i) c))
          (ensures (sum_i vc i == mul (sum_i v i) c))
          (decreases (l - i))
  = if i = l - 1 then () 
    else (lemma_sum_i_mul_r c vc v (i+1);
          add_mul_distr_r (v i) (sum_i v (i+1)) c)

let lemma_sum_mul_r (#a:Type) {| numeric a |} (#l:dim) (c:a) (v vc:vector a l)
  : Lemma (requires (forall i. vc i == mul (v i) c))
          (ensures (sum vc == mul (sum v) c))
  = lemma_sum_i_mul_r c vc v 0

// switch the order of sums:
//     sum_i sum_j f(i,j) == sum_j sum_i f(i,j)
let rec lemma_sum_i_switch_sums (#a:Type) {| numeric a |} (#l1 #l2:dim) (f: knat l1 -> knat l2 -> a) (i':knat l1) (j':knat l2)
  : Lemma (ensures (let lhs = sum_i (F.on (knat l1) (fun i -> sum_i (F.on (knat l2) (fun j -> f i j)) j')) i' in
                    let rhs = sum_i (F.on (knat l2) (fun j -> sum_i (F.on (knat l1) (fun i -> f i j)) i')) j' in
                    lhs == rhs))
          (decreases (l1 - i'))
  = let lhs_inner (i:knat l1) : vector a l2 = F.on (knat l2) (fun j -> f i j) in
    let lhs_outer : vector a l1 = F.on (knat l1) (fun i -> sum_i (lhs_inner i) j') in
    let rhs_inner (j:knat l2) : vector a l1 = F.on (knat l1) (fun i -> f i j) in
    let rhs_outer : vector a l2 = F.on (knat l2) (fun j -> sum_i (rhs_inner j) i') in
    // auxiliary lemmas for applying the 'def' lemmas in the body of the RHS
    let lemma_aux1 (i':knat l1{i' = l1 - 1}) j 
      : Lemma (sum_i (F.on (knat l1) (fun i -> f i j)) i' == f i' j)
      = lemma_sum_i_def_base (rhs_inner j) i' in
    let lemma_aux2 (i':knat l1{i' <> l1 - 1}) j 
      : Lemma (sum_i (F.on (knat l1) (fun i -> f i j)) i' == add (f i' j) (sum_i (F.on (knat l1) (fun i -> f i j)) (i'+1)))
      = lemma_sum_i_def_rec (rhs_inner j) i' in
    if i' = l1 - 1
    then (// simplify LHS
          lemma_sum_i_def_base lhs_outer i';
          // simplify RHS
          FStar.Classical.forall_intro (lemma_aux1 i');
          lemma_eq_elim_vec rhs_outer (lhs_inner i')
         )
    else (// simplify LHS
          lemma_sum_i_def_rec lhs_outer i';
          // simplify RHS
          FStar.Classical.forall_intro (lemma_aux2 i');
          let e = F.on (knat l2) (fun j -> add (f i' j) (sum_i (rhs_inner j) (i'+1))) in
          lemma_eq_elim_vec rhs_outer e;
          // apply lemma_sum_i_add
          lemma_sum_i_add e (lhs_inner i') (F.on (knat l2) (fun j -> sum_i (rhs_inner j) (i'+1))) j';
          // recursive call to lemma_sum_i_switch_sums
          lemma_sum_i_switch_sums f (i'+1) j'
         )

let lemma_sum_switch_sums (#a:Type) {| numeric a |} (#l1 #l2:dim) (f: knat l1 -> knat l2 -> a)
  : Lemma (ensures (let lhs = sum (F.on (knat l1) (fun i -> sum (F.on (knat l2) (fun j -> f i j)))) in
                    let rhs = sum (F.on (knat l2) (fun j -> sum (F.on (knat l1) (fun i -> f i j)))) in
                    lhs == rhs)) 
  = let lhs_sum = F.on (knat l1) (fun i -> sum (F.on (knat l2) (fun j -> f i j))) in
    let rhs_sum = F.on (knat l2) (fun j -> sum (F.on (knat l1) (fun i -> f i j))) in
    let lhs_sum_i = F.on (knat l1) (fun i -> sum_i (F.on (knat l2) (fun j -> f i j)) 0) in
    let rhs_sum_i = F.on (knat l2) (fun j -> sum_i (F.on (knat l1) (fun i -> f i j)) 0) in
    lemma_sum_i_switch_sums f 0 0;
    lemma_eq_elim_vec lhs_sum lhs_sum_i;
    lemma_eq_elim_vec rhs_sum rhs_sum_i

let rec lemma_sum_i_product_of_sums (#a:Type) {| numeric a |} (#l1 #l2:dim) (v1: vector a l1) (v2:vector a l2) (i:knat l1)
  : Lemma (ensures (let v1v2 = F.on (knat l1) (fun i -> sum (F.on (knat l2) (fun j -> mul (v1 i) (v2 j)))) in
                    mul (sum_i v1 i) (sum v2) == sum_i v1v2 i))
          (decreases (l1 - i))
  = let v1v2_inner i = F.on (knat l2) (fun j -> mul (v1 i) (v2 j)) in
    let v1v2 = F.on (knat l1) (fun i -> sum (v1v2_inner i)) in
    if i = l1 - 1 
    then (lemma_sum_mul_l (v1 i) v2 (v1v2_inner i);
          lemma_sum_i_def_base (F.on (knat l1) (fun i -> sum (F.on (knat l2) (fun j -> mul (v1 i) (v2 j))))) i)
    else (lemma_sum_mul_l (v1 i) v2 (v1v2_inner i);
          add_mul_distr_r (v1 i) (sum_i v1 (i+1)) (sum v2);
          lemma_sum_i_def_rec v1v2 i;
          lemma_sum_i_product_of_sums v1 v2 (i+1))

let lemma_sum_product_of_sums (#a:Type) {| numeric a |} (#l1 #l2:dim) (v1: vector a l1) (v2:vector a l2)
  : Lemma (ensures (let lhs = mul (sum v1) (sum v2) in
                    let rhs = sum (F.on (knat l1) (fun i -> sum (F.on (knat l2) (fun j -> mul (v1 i) (v2 j))))) in
                    lhs == rhs))
  = lemma_sum_i_product_of_sums v1 v2 0

private
let rec lemma_sum_i_conj (#a:Type) {| numeric a |} (#l:dim) (v vconj: vector a l) (i: knat l)
  : Lemma (requires (forall (i : knat l). vconj i == conj (v i)))
          (ensures (conj (sum_i v i) == sum_i vconj i))
          (decreases (l - i))
  = if i = l - 1 then () else lemma_sum_i_conj v vconj (i+1)

let lemma_sum_conj (#a:Type) {| numeric a |} (#l:dim) (v vconj: vector a l)
  : Lemma (requires (forall (i : knat l). vconj i == conj (v i)))
          (ensures (conj (sum v) == sum vconj))
  = lemma_sum_i_conj v vconj 0

(* proofs about vector operations *)
let lemma_vec_sum_comm (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l)
  : Lemma (ensures (vec_sum v1 v2 == vec_sum v2 v1))
  = let vec_sum_comm_aux (i:knat l)
      : Lemma ((vec_sum v1 v2) i == (vec_sum v2 v1) i)
      = add_comm (v1 i) (v2 i)
    in
    FStar.Classical.forall_intro vec_sum_comm_aux;
    lemma_eq_elim_vec (vec_sum v1 v2) (vec_sum v2 v1)

let lemma_vec_sum_assoc (#a:Type) {| numeric a |} (#l:dim) (v1 v2 v3:vector a l)
  : Lemma (ensures (vec_sum (vec_sum v1 v2) v3 == vec_sum v1 (vec_sum v2 v3)))
  = let vec_sum_assoc_aux (i:knat l)
      : Lemma ((vec_sum (vec_sum v1 v2) v3) i == (vec_sum v1 (vec_sum v2 v3)) i)
      = add_assoc (v1 i) (v2 i) (v3 i) in
  FStar.Classical.forall_intro vec_sum_assoc_aux;
  lemma_eq_elim_vec (vec_sum (vec_sum v1 v2) v3) (vec_sum v1 (vec_sum v2 v3))

let lemma_vec_prod_comm (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l)
  : Lemma (ensures (vec_prod v1 v2 == vec_prod v2 v1))
  = let x = vec_prod_pointwise v1 v2 in
    let y = vec_prod_pointwise v2 v1 in
    let vec_prod_pointwise_comm (i:knat l)
      : Lemma ((vec_prod_pointwise v1 v2) i == (vec_prod_pointwise v2 v1) i)
      = mul_comm (v1 i) (v2 i) in
    FStar.Classical.forall_intro vec_prod_pointwise_comm;
    assert (equal_vec x y);
    assert (sum x == sum y)

let lemma_vec_prod_zero_l (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l) 
  : Lemma (requires (forall (i : knat l). v1 i == zero))
          (ensures (vec_prod v1 v2 == zero))
  = let v = vec_prod_pointwise v1 v2 in lemma_sum_zero v

let lemma_vec_prod_zero_r (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l)
  : Lemma (requires (forall (i : knat l). v2 i == zero))
          (ensures (vec_prod v1 v2 == zero))
  = lemma_vec_prod_comm v1 v2; 
    lemma_vec_prod_zero_l v2 v1

let lemma_vec_prod_singleton_l (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l) (i:knat l)
  : Lemma (requires (forall i'. if i = i' then (v1 i') == one else (v1 i') == zero))
          (ensures (vec_prod v1 v2 == v2 i))
  = let v = vec_prod_pointwise v1 v2 in lemma_sum_singleton v i (v2 i)

let lemma_vec_prod_singleton_r (#a:Type) {| numeric a |} (#l:dim) (v1 v2:vector a l) (i:knat l) 
  : Lemma (requires (forall i'. if i = i' then (v2 i') == one else (v2 i') == zero))
          (ensures (vec_prod v1 v2 == v1 i))
  = lemma_vec_prod_comm v1 v2; 
    lemma_vec_prod_singleton_l v2 v1 i

(* proofs about matrix operations *)

let lemma_scale_zero_l (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (scale zero x == zero_matrix a m n))
  = lemma_eq_elim (scale zero x) (zero_matrix a m n)

let lemma_scale_zero_r (#a:Type) {| numeric a |} (m n:dim) (c:a)
  : Lemma (ensures (scale c (zero_matrix a m n) == zero_matrix a m n))
  = lemma_eq_elim (scale c (zero_matrix a m n)) (zero_matrix a m n)

let lemma_scale_one_l (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (scale one x == x))
  = lemma_eq_elim (scale one x) x

let lemma_scale_one_r (#a:Type) {| numeric a |} (m:dim) (c:a)
  : Lemma (scale c (id_matrix a m) == F.on (knat m & knat m) (fun (i,j) -> if i = j then c else zero))
  = let x = F.on (knat m & knat m) (fun (i,j) -> if i = j then c else zero) in
    lemma_eq_elim (scale c (id_matrix a m)) x

let lemma_matrix_add_zero_l (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (matrix_add (zero_matrix a m n) x == x))
  = lemma_eq_elim (matrix_add (zero_matrix a m n) x) x

let lemma_matrix_add_zero_r (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (matrix_add x (zero_matrix a m n) == x))
  = lemma_eq_elim (matrix_add x (zero_matrix a m n)) x

let lemma_matrix_mul_zero_l (#a:Type) {| numeric a |} (#m #n #p:dim) (x:matrix a n p)
  : Lemma (ensures (matrix_mul (zero_matrix a m n) x == zero_matrix a m p))
  = let lemma_mult_zero_l_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul (zero_matrix a m n) x) i j == index (zero_matrix a m p) i j)
      = lemma_vec_prod_zero_l (row (zero_matrix a m n) i) (col x j) in
    FStar.Classical.forall_intro_2 lemma_mult_zero_l_aux;
    lemma_eq_elim (matrix_mul (zero_matrix a m n) x) (zero_matrix a m p)

let lemma_matrix_mul_zero_r (#a:Type) {| numeric a |} (#m #n #p:dim) (x:matrix a m n)
  : Lemma (ensures (matrix_mul x (zero_matrix a n p) == zero_matrix a m p))
  = let lemma_mult_zero_r_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul x (zero_matrix a n p)) i j == index (zero_matrix a m p) i j)
      = lemma_vec_prod_zero_r (row x i) (col (zero_matrix a n p) j) in
    FStar.Classical.forall_intro_2 lemma_mult_zero_r_aux;
    lemma_eq_elim (matrix_mul x (zero_matrix a n p)) (zero_matrix a m p)

let lemma_matrix_mul_id_l (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (matrix_mul (id_matrix a m) x == x))
  = let lemma_mult_id_l_aux (i:knat m) (j:knat n) 
      : Lemma (index (matrix_mul (id_matrix a m) x) i j == index x i j)
      = lemma_vec_prod_singleton_l (row (id_matrix a m) i) (col x j) i in
    FStar.Classical.forall_intro_2 lemma_mult_id_l_aux;
    lemma_eq_elim (matrix_mul (id_matrix a m) x) x

let lemma_matrix_mul_id_r (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (matrix_mul x (id_matrix a n) == x))
  = let lemma_mult_id_r_aux (i:knat m) (j:knat n) 
      : Lemma (index (matrix_mul x (id_matrix a n)) i j == index x i j)
      = lemma_vec_prod_singleton_r (row x i) (col (id_matrix a n) j) j in
    FStar.Classical.forall_intro_2 lemma_mult_id_r_aux;
    lemma_eq_elim (matrix_mul x (id_matrix a n)) x

let lemma_kron_zero_l (#a:Type) {| numeric a |} (m n #p #q:dim) (x:matrix a p q) 
  : Lemma (ensures kronecker_product (zero_matrix a m n) x == zero_matrix a (m * p) (n * q))
  = lemma_eq_elim (kronecker_product (zero_matrix a m n) x) (zero_matrix a (m * p) (n * q))

let lemma_kron_zero_r (#a:Type) {| numeric a |} (#m #n p q:dim) (x:matrix a m n)
  : Lemma (ensures kronecker_product x (zero_matrix a p q) == zero_matrix a (m * p) (n * q))
  = lemma_eq_elim (kronecker_product x (zero_matrix a p q)) (zero_matrix a (m * p) (n * q))

let lemma_kron_id (a:Type) {| numeric a |} (m p:dim)
  : Lemma (ensures (kronecker_product (id_matrix a m) (id_matrix a p) == id_matrix a (m * p)))
  = lemma_eq_elim (kronecker_product (id_matrix a m) (id_matrix a p)) (id_matrix a (m * p))

let lemma_scale_assoc (#a:Type) {| num:numeric a |} (#m #n:dim) (c1 c2:a) (x:matrix a m n)
  : Lemma (ensures (scale c1 (scale c2 x) == scale (mul c1 c2) x))
  = let scale_assoc_aux (i:knat m) (j:knat n)
      : Lemma (index (scale c1 (scale c2 x)) i j == index (scale (num.mul c1 c2) x) i j)
      = mul_assoc c1 c2 (index x i j) in
    FStar.Classical.forall_intro_2 scale_assoc_aux;
    lemma_eq_elim (scale c1 (scale c2 x)) (scale (mul c1 c2) x)

let lemma_matrix_add_comm (#a:Type) {| numeric a |} (#m #n:dim) (x1 x2:matrix a m n)
  : Lemma (ensures (matrix_add x1 x2 == matrix_add x2 x1))
  = let add_comm_aux (i:knat m) (j:knat n)
      : Lemma (index (matrix_add x1 x2) i j == index (matrix_add x2 x1) i j)
      = add_comm (index x1 i j) (index x2 i j) in
    FStar.Classical.forall_intro_2 add_comm_aux;
    lemma_eq_elim (matrix_add x1 x2) (matrix_add x2 x1)

let lemma_matrix_add_assoc (#a:Type) {| numeric a|} (#m #n:dim) (x1 x2 x3:matrix a m n)
  : Lemma (ensures (matrix_add (matrix_add x1 x2) x3 == matrix_add x1 (matrix_add x2 x3)))
  = let add_assoc_aux (i:knat m) (j:knat n)
      : Lemma (index (matrix_add (matrix_add x1 x2) x3) i j == index (matrix_add x1 (matrix_add x2 x3)) i j)
      = add_assoc (index x1 i j) (index x2 i j) (index x3 i j) in
    FStar.Classical.forall_intro_2 add_assoc_aux;
    lemma_eq_elim (matrix_add (matrix_add x1 x2) x3) (matrix_add x1 (matrix_add x2 x3))

let lemma_matrix_mul_assoc (#a:Type) {| numeric a |} (#m #n #p #q:dim) 
                     (x1:matrix a m n) (x2:matrix a n p) (x3:matrix a p q)
  : Lemma (ensures (matrix_mul (matrix_mul x1 x2) x3 == matrix_mul x1 (matrix_mul x2 x3)))
  = // rewrite LHS
    let rewrite_lhs (i:knat m) (j:knat q) (k:knat p) 
      : Lemma (let v = F.on (knat n) (fun l -> mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j))) in
               mul (vec_prod (row x1 i) (col x2 k)) (x3 (k,j)) == sum v)
      = let v = F.on (knat n) (fun l -> mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j))) in
        lemma_sum_mul_r (x3 (k,j)) (vec_prod_pointwise (row x1 i) (col x2 k)) v in
    // rewrite RHS
    let rewrite_rhs (i:knat m) (j:knat q) (l:knat n) 
      : Lemma (let v = F.on (knat p) (fun k -> mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j))) in
               mul (x1 (i,l)) (vec_prod (row x2 l) (col x3 j)) == sum v)
      = let v = F.on (knat p) (fun k -> mul (x1 (i,l)) (mul (x2 (l,k)) (x3 (k,j)))) in
        let v' = F.on (knat p) (fun k -> mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j))) in
        let lemma_assoc (k:knat p) 
          : Lemma (mul (x1 (i,l)) (mul (x2 (l,k)) (x3 (k,j))) == mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j)))
          = mul_assoc (x1 (i,l)) (x2 (l,k)) (x3 (k,j)) in
        lemma_sum_mul_l (x1 (i,l)) (vec_prod_pointwise (row x2 l) (col x3 j)) v;
        FStar.Classical.forall_intro lemma_assoc;
        lemma_eq_elim_vec v v' in
    // use the rewrite lemmas and lemma_sum_switch_sums
    let mul_assoc_aux (i:knat m) (j:knat q)
      : Lemma (ensures (index (matrix_mul (matrix_mul x1 x2) x3) i j == index (matrix_mul x1 (matrix_mul x2 x3)) i j))
      = let f (k:knat p) (l:knat n) = mul (mul (x1 (i,l)) (x2 (l,k))) (x3 (k,j)) in
        let lhs_rewritten = F.on (knat p) (fun k -> sum (F.on (knat n) (fun l -> f k l))) in
        let rhs_rewritten = F.on (knat n) (fun l -> sum (F.on (knat p) (fun k -> f k l))) in
        FStar.Classical.forall_intro (rewrite_lhs i j);
        FStar.Classical.forall_intro (rewrite_rhs i j);
        lemma_eq_elim_vec (vec_prod_pointwise (row (matrix_mul x1 x2) i) (col x3 j)) lhs_rewritten;
        lemma_eq_elim_vec (vec_prod_pointwise (row x1 i) (col (matrix_mul x2 x3) j)) rhs_rewritten;
        lemma_sum_switch_sums f in
    FStar.Classical.forall_intro_2 mul_assoc_aux;
    lemma_eq_elim (matrix_mul (matrix_mul x1 x2) x3) (matrix_mul x1 (matrix_mul x2 x3))

let lemma_scale_add_distr (#a:Type) {| numeric a |} (#m #n:dim) (c:a) (x1 x2:matrix a m n)
  : Lemma (ensures (scale c (matrix_add x1 x2) == matrix_add (scale c x1) (scale c x2)))
  = let scale_add_distr_aux (i:knat m) (j:knat n)
      : Lemma (index (scale c (matrix_add x1 x2)) i j == index (matrix_add (scale c x1) (scale c x2)) i j)
      = add_mul_distr_l c (index x1 i j) (index x2 i j) in
    FStar.Classical.forall_intro_2 scale_add_distr_aux;
    lemma_eq_elim (scale c (matrix_add x1 x2)) (matrix_add (scale c x1) (scale c x2))

let lemma_scale_mul_distr_l (#a:Type) {| numeric a |} (#m #n #p:dim) (c:a) (x1:matrix a m n) (x2:matrix a n p) 
  : Lemma (ensures (matrix_mul (scale c x1) x2 == scale c (matrix_mul x1 x2)))
  = let lemma_assoc (i:knat m) (j:knat p) (k:knat n)
      : Lemma ((vec_prod_pointwise (row (scale c x1) i) (col x2 j)) k == mul c (mul (x1 (i,k)) (x2 (k,j))))
      = mul_assoc c (x1 (i,k)) (x2 (k,j)) in 
   let scale_mul_distr_l_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul (scale c x1) x2) i j == index (scale c (matrix_mul x1 x2)) i j)
      = let v = vec_prod_pointwise (row x1 i) (col x2 j) in
        let cv = vec_prod_pointwise (row (scale c x1) i) (col x2 j) in
        FStar.Classical.forall_intro (lemma_assoc i j);
        lemma_sum_mul_l c v cv in
    FStar.Classical.forall_intro_2 scale_mul_distr_l_aux;
    lemma_eq_elim (matrix_mul (scale c x1) x2) (scale c (matrix_mul x1 x2))

let lemma_scale_mul_distr_r (#a:Type) {| numeric a |} (#m #n #p:dim) (c:a) (x1:matrix a m n) (x2:matrix a n p)
  : Lemma (ensures (matrix_mul x1 (scale c x2) == scale c (matrix_mul x1 x2)))
  = let lemma_comm_assoc (i:knat m) (j:knat p) (k:knat n)
      : Lemma ((vec_prod_pointwise (row x1 i) (col (scale c x2) j)) k == mul c (mul (x1 (i,k)) (x2 (k,j))))
      = mul_assoc (x1 (i,k)) c (x2 (k,j));
        mul_comm (x1 (i,k)) c;
        mul_assoc c (x1 (i,k)) (x2 (k,j)) in 
   let scale_mul_distr_r_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul x1 (scale c x2)) i j == index (scale c (matrix_mul x1 x2)) i j)
      = let v = vec_prod_pointwise (row x1 i) (col x2 j) in
        let cv = vec_prod_pointwise (row x1 i) (col (scale c x2) j) in
        FStar.Classical.forall_intro (lemma_comm_assoc i j);
        lemma_sum_mul_l c v cv in
    FStar.Classical.forall_intro_2 scale_mul_distr_r_aux;
    lemma_eq_elim (matrix_mul x1 (scale c x2)) (scale c (matrix_mul x1 x2))

let lemma_scale_kron_distr_l (#a:Type) {| numeric a |} (#m #n #p #q:dim) (c:a) (x1:matrix a m n) (x2:matrix a p q)
  : Lemma (ensures (kronecker_product (scale c x1) x2) == scale c (kronecker_product x1 x2))
  = let scale_kron_distr_l_aux (i:knat (m * p)) (j:knat (n * q)) 
       : Lemma (index (kronecker_product (scale c x1) x2) i j == index (scale c (kronecker_product x1 x2)) i j)
       = mul_assoc c (index x1 (i/p) (j/q)) (index x2 (i%p) (j%q)) in
     FStar.Classical.forall_intro_2 scale_kron_distr_l_aux;
     lemma_eq_elim (kronecker_product (scale c x1) x2) (scale c (kronecker_product x1 x2))

let lemma_scale_kron_distr_r (#a:Type) {| numeric a |} (#m #n #p #q:dim) (c:a) (x1:matrix a m n) (x2:matrix a p q)
  : Lemma (ensures (kronecker_product x1 (scale c x2)) == scale c (kronecker_product x1 x2))
  = let scale_kron_distr_r_aux (i:knat (m * p)) (j:knat (n * q)) 
       : Lemma (index (kronecker_product x1 (scale c x2)) i j == index (scale c (kronecker_product x1 x2)) i j)
       = mul_assoc (index x1 (i/p) (j/q)) c (index x2 (i%p) (j%q));
         mul_comm (index x1 (i/p) (j/q)) c;
         mul_assoc c (index x1 (i/p) (j/q)) (index x2 (i%p) (j%q)) in
     FStar.Classical.forall_intro_2 scale_kron_distr_r_aux;
     lemma_eq_elim (kronecker_product x1 (scale c x2)) (scale c (kronecker_product x1 x2))

let lemma_mul_add_distr_l (#a:Type) {| numeric a |} (#m #n #p:dim) 
                          (x1:matrix a m n) (x2:matrix a n p) (x3:matrix a n p)
  : Lemma (ensures (matrix_mul x1 (matrix_add x2 x3) == matrix_add (matrix_mul x1 x2) (matrix_mul x1 x3)))
  = let lemma_distr (i:knat m) (j:knat p) (k:knat n)
      : Lemma ((vec_prod_pointwise (row x1 i) (col (matrix_add x2 x3) j)) k == add (mul (x1 (i,k)) (x2 (k,j))) (mul (x1 (i,k)) (x3 (k,j))))
      = add_mul_distr_l (x1 (i,k)) (x2 (k,j)) (x3 (k,j)) in
    let mul_add_distr_l_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul x1 (matrix_add x2 x3)) i j == index (matrix_add (matrix_mul x1 x2) (matrix_mul x1 x3)) i j)
      = let v1 = vec_prod_pointwise (row x1 i) (col x2 j) in
        let v2 = vec_prod_pointwise (row x1 i) (col x3 j) in
        let v1v2 = vec_prod_pointwise (row x1 i) (col (matrix_add x2 x3) j) in
        FStar.Classical.forall_intro (lemma_distr i j);
        lemma_sum_add v1 v2 v1v2 in
    FStar.Classical.forall_intro_2 mul_add_distr_l_aux;
    lemma_eq_elim (matrix_mul x1 (matrix_add x2 x3)) (matrix_add (matrix_mul x1 x2) (matrix_mul x1 x3))

let lemma_mul_add_distr_r (#a:Type) {| numeric a |} (#m #n #p:dim) 
                            (x1:matrix a m n) (x2:matrix a m n) (x3:matrix a n p)
  : Lemma (ensures (matrix_mul (matrix_add x1 x2) x3 == matrix_add (matrix_mul x1 x3) (matrix_mul x2 x3)))
  = let lemma_distr (i:knat m) (j:knat p) (k:knat n)
      : Lemma ((vec_prod_pointwise (row (matrix_add x1 x2) i) (col x3 j)) k == add (mul (x1 (i,k)) (x3 (k,j))) (mul (x2 (i,k)) (x3 (k,j))))
      = add_mul_distr_r (x1 (i,k)) (x2 (i,k)) (x3 (k,j)) in
    let mul_add_distr_r_aux (i:knat m) (j:knat p) 
      : Lemma (index (matrix_mul (matrix_add x1 x2) x3) i j == index (matrix_add (matrix_mul x1 x3) (matrix_mul x2 x3)) i j)
      = let v1 = vec_prod_pointwise (row x1 i) (col x3 j) in
        let v2 = vec_prod_pointwise (row x2 i) (col x3 j) in
        let v1v2 = vec_prod_pointwise (row (matrix_add x1 x2) i) (col x3 j) in
        FStar.Classical.forall_intro (lemma_distr i j);
        lemma_sum_add v1 v2 v1v2 in
    FStar.Classical.forall_intro_2 mul_add_distr_r_aux;
    lemma_eq_elim (matrix_mul (matrix_add x1 x2) x3) (matrix_add (matrix_mul x1 x3) (matrix_mul x2 x3))

let lemma_kron_add_distr_l (#a:Type) {| numeric a |} (#m #n #p #q:dim) 
                           (x1:matrix a m n) (x2:matrix a p q) (x3:matrix a p q)
  : Lemma (ensures (kronecker_product x1 (matrix_add x2 x3) == matrix_add (kronecker_product x1 x2) (kronecker_product x1 x3)))
  = let kron_add_distr_l_aux (i:knat (m * p)) (j:knat (n * q)) 
      : Lemma (index (kronecker_product x1 (matrix_add x2 x3)) i j == index (matrix_add (kronecker_product x1 x2) (kronecker_product x1 x3)) i j)
      = add_mul_distr_l (index x1 (i/p) (j/q)) (index x2 (i%p) (j%q)) (index x3 (i%p) (j%q)) in
    FStar.Classical.forall_intro_2 kron_add_distr_l_aux;
    lemma_eq_elim (kronecker_product x1 (matrix_add x2 x3)) (matrix_add (kronecker_product x1 x2) (kronecker_product x1 x3))

let lemma_kron_add_distr_r (#a:Type) {| numeric a |} (#m #n #p #q:dim) 
                           (x1:matrix a m n) (x2:matrix a m n) (x3:matrix a p q)
  : Lemma (ensures (kronecker_product (matrix_add x1 x2) x3 == matrix_add (kronecker_product x1 x3) (kronecker_product x2 x3)))
  = let kron_add_distr_r_aux (i:knat (m * p)) (j:knat (n * q)) 
      : Lemma (index (kronecker_product (matrix_add x1 x2) x3) i j == index (matrix_add (kronecker_product x1 x3) (kronecker_product x2 x3)) i j)
      = add_mul_distr_r (index x1 (i/p) (j/q)) (index x2 (i/p) (j/q)) (index x3 (i%p) (j%q)) in
    FStar.Classical.forall_intro_2 kron_add_distr_r_aux;
    lemma_eq_elim (kronecker_product (matrix_add x1 x2) x3) (matrix_add (kronecker_product x1 x3) (kronecker_product x2 x3))

// TODO
let lemma_kron_mixed_product (#a:Type) {| numeric a |} (#m #n #p #q #r #s:dim) 
                             (x1:matrix a m n) (x2:matrix a q r) (x3:matrix a n p) (x4:matrix a r s)
  : Lemma (ensures (matrix_mul (kronecker_product x1 x2) (kronecker_product x3 x4) == kronecker_product (matrix_mul x1 x3) (matrix_mul x2 x4)))
  = admit() 

let lemma_transpose_zero (a:Type) {| numeric a |} (m n:dim)
  : Lemma (ensures (transpose (zero_matrix a m n) == zero_matrix a n m))
  = lemma_eq_elim (transpose (zero_matrix a m n)) (zero_matrix a n m)

let lemma_transpose_id (a:Type) {| numeric a |} (m:dim)
  : Lemma (ensures (transpose (id_matrix a m) == id_matrix a m))
  = lemma_eq_elim (transpose (id_matrix a m)) (id_matrix a m)

let lemma_transpose_row (#a:Type) (#m #n:dim) (x:matrix a m n) (i:knat n)
  : Lemma (row (transpose x) i == col x i)
  = lemma_eq_elim_vec (row (transpose x) i) (col x i)

let lemma_transpose_col (#a:Type) (#m #n:dim) (x:matrix a m n) (j:knat m)
  : Lemma (col (transpose x) j == row x j)
  = lemma_eq_elim_vec (col (transpose x) j) (row x j)

let lemma_transpose_involutive (#a:Type) (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (transpose (transpose x) == x))
  = lemma_eq_elim (transpose (transpose x)) x

let lemma_transpose_scale (#a:Type) {| numeric a |} (#m #n:dim) (c:a) (x:matrix a m n)
  : Lemma (ensures (transpose (scale c x) == scale c (transpose x)))
  = lemma_eq_elim (transpose (scale c x)) (scale c (transpose x))

let lemma_transpose_add (#a:Type) {| numeric a |} (#m #n:dim) (x1 x2:matrix a m n)
  : Lemma (ensures (transpose (matrix_add x1 x2) == matrix_add (transpose x1) (transpose x2)))
  = lemma_eq_elim (transpose (matrix_add x1 x2)) (matrix_add (transpose x1) (transpose x2))

let lemma_transpose_mul (#a:Type) {| numeric a |} (#m #n #p:dim) (x1:matrix a m n) (x2:matrix a n p)
  : Lemma (ensures (transpose (matrix_mul x1 x2) == matrix_mul (transpose x2) (transpose x1)))
  = let transpose_mul_aux (i:knat p) (j:knat m) 
      : Lemma (index (transpose (matrix_mul x1 x2)) i j == index (matrix_mul (transpose x2) (transpose x1)) i j)
      = lemma_transpose_row x2 i;
        lemma_transpose_col x1 j;
        lemma_vec_prod_comm (row x1 j) (col x2 i) in
    FStar.Classical.forall_intro_2 transpose_mul_aux;
    lemma_eq_elim (transpose (matrix_mul x1 x2)) (matrix_mul (transpose x2) (transpose x1))

let lemma_transpose_kron (#a:Type) {| numeric a |} (#m #n #p #q:dim) (x1:matrix a m n) (x2:matrix a p q)
  : Lemma (ensures (transpose (kronecker_product x1 x2) == kronecker_product (transpose x1) (transpose x2)))
  = lemma_eq_elim (transpose (kronecker_product x1 x2)) (kronecker_product (transpose x1) (transpose x2))

let lemma_conj_transpose_involutive (#a:Type) {| numeric a |} (#m #n:dim) (x:matrix a m n)
  : Lemma (ensures (conjugate_transpose (conjugate_transpose x) == x))
  = lemma_eq_elim (conjugate_transpose (conjugate_transpose x)) x

let lemma_conj_transpose_scale (#a:Type) {| numeric a |} (#m #n:dim) (c:a) (x:matrix a m n)
  : Lemma (ensures (conjugate_transpose (scale c x) == scale (conj c) (conjugate_transpose x)))
  = lemma_eq_elim (conjugate_transpose (scale c x)) (scale (conj c) (conjugate_transpose x))

let lemma_conj_transpose_add (#a:Type) {| numeric a |} (#m #n:dim) (x1 x2:matrix a m n)
  : Lemma (ensures (conjugate_transpose (matrix_add x1 x2) == matrix_add (conjugate_transpose x1) (conjugate_transpose x2)))
  = lemma_eq_elim (conjugate_transpose (matrix_add x1 x2)) (matrix_add (conjugate_transpose x1) (conjugate_transpose x2))

// TODO
let lemma_conj_transpose_mul (#a:Type) {| numeric a |} (#m #n #p:dim) (x1:matrix a m n) (x2:matrix a n p)
  : Lemma (ensures (conjugate_transpose (matrix_mul x1 x2) == matrix_mul (conjugate_transpose x2) (conjugate_transpose x1)))
  = admit()

let lemma_conj_transpose_kron (#a:Type) {| numeric a |} (#m #n #p #q:dim) (x1:matrix a m n) (x2:matrix a p q)
  : Lemma (ensures (conjugate_transpose (kronecker_product x1 x2) == kronecker_product (conjugate_transpose x1) (conjugate_transpose x2)))
  = lemma_eq_elim (conjugate_transpose (kronecker_product x1 x2)) (kronecker_product (conjugate_transpose x1) (conjugate_transpose x2))

let lemma_trace_zero (#a:Type) {| numeric a |} (m:dim)
  : Lemma (ensures (trace (zero_matrix a m m) == zero))
  = lemma_sum_zero (diagonal (zero_matrix a m m))

let lemma_trace_scale (#a:Type) {| numeric a |} (#m:dim) (c:a) (x:matrix a m m)
  : Lemma (ensures (trace (scale c x) == mul c (trace x)))
  = let d = diagonal x in
    let dscale = diagonal (scale c x) in
    lemma_sum_mul_l c d dscale

let lemma_trace_add (#a:Type) {| numeric a |} (#m:dim) (x1 x2:matrix a m m)
  : Lemma (ensures (trace (matrix_add x1 x2) == add (trace x1) (trace x2)))
  = let d1 = diagonal x1 in
    let d2 = diagonal x2 in
    let d12 = diagonal (matrix_add x1 x2) in
    lemma_sum_add d1 d2 d12

let lemma_trace_transpose (#a:Type) {| numeric a |} (#m:dim) (x:matrix a m m)
  : Lemma (ensures (trace (transpose x) == trace x))
  = let d = diagonal x in
    let dt = diagonal (transpose x) in
    assert (forall i. d i == dt i);
    lemma_eq_intro_vec d dt



// long associativity proof...
// TODO: there is admit below caused by some weirdness with typeclasses (it seems)

let lemma_kron_index (#a:Type) {| numeric a |} (#m #n #p #q:dim) 
    (x1:matrix a m n) (x2:matrix a p q) (i:knat (m * p)) (j:knat (n * q))
  : Lemma (ensures (index (kronecker_product x1 x2) i j == mul (index x1 (i / p) (j / q)) (index x2 (i % p) (j % q))))
    [SMTPat (index (kronecker_product x1 x2) i j)]
  = ()

/// The next section here is a proof of associative of
/// kronecker_product This involves a fair bit of non-linear
/// arithmetic, combined with reasoning about quantifiers etc. This
/// can be *EXTREMELY* unpredictable in Z3. So, a recommended proof
/// strategy in this setting is
///
/// 0. Use a few F* options that tune it well for arithmetic
///
/// 1. Turn of non-linear arithmetic in Z3, using smt.arith.nl=false
///
/// 2. Do all your proofs with linear arithmetic only, treating *, /, %
/// as uninterpreted functions, and relying on explicit calls to the
/// corpus of lemmas in FStar.Math.Lemmas to complete your proof

//Clear whatever options are in use so far
#reset-options

//This set of F* options is well-tuned for arithmetic
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

//We're not reasoning about recursive functions or inductive types
//So, set these fuels to zero (not really necessary, but a useful optimization)
#set-options "--max_fuel 0 --max_ifuel 0"

/// Now, we're going to set things up in a way so that many basic
/// proofs about non-linear arithmetic that are needed to even state
/// the lemmas are factored out.

/// `dprod`: A product of dimensions, itself a dimension
/// Even that need a bit on non-linear arithmetic
/// But, it's small and isolated enough that Z3 can do it easily
let dprod (m n:dim) : dim = m * n
let dprod_equiv (p q r:dim)
  : Lemma (dprod (dprod p q) r == dprod p (dprod q r))
          [SMTPat (dprod (dprod p q) r)]
  = ()

/// kdiv and kmod, divide or mod out the last factor in a dprod
///
/// Both of these need non-linear arithmetic, again small enough
/// that Z3 can do it
let kdiv (#m #n:dim) (i:knat (dprod m n)) : knat m = i / n
let kmod (#m #n:dim) (i:knat (dprod m n)) : knat n = i % n

/// `k` An abbreviation kronecker_product, expressed in terms of
/// our utility function on dimensions above
let k (#a:Type) {| numeric a |} (#m #n #p #q:dim) (x1:matrix a m n) (x2:matrix a p q)
  : matrix a (dprod m p) (dprod n q)
  = kronecker_product x1 x2

/// `k_index`: restating the definition of `k` in terms of its elements
let k_index (#a:Type) {| numeric a |} (#m #n #p #q:dim) (x1:matrix a m n) (x2:matrix a p q) (i:knat (dprod m p)) (j:knat (dprod n q))
  : Lemma (index (k x1 x2) i j == mul (index x1 (kdiv i) (kdiv j)) (index x2 (kmod i) (kmod j)))
  = lemma_kron_index x1 x2 i j

/// Now, we're ready to do the main proof turning the smt.arith.nl off

//Also, this module contains too much irrelevant stuff;
//it should probably be refactored into smaller, more related pieces

//Reset the solver, keeping only what we need using `using_facts_from`
#reset-options
  "--using_facts_from \
        'Prims QStar.Matrix.dprod \
         QStar.Matrix.dprod_equiv \
         QStar.Matrix.dim \
         QStar.Matrix.knat \
         QStar.Matrix.kdiv \
         QStar.Matrix.kmod' \
   --z3cliopt 'smt.arith.nl=false'" //TURN OFF non-linear arithmetic in Z3 for this proof; it's too flaky

//Use again our set of F* options well-tuned for arithmetic
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

//We're not reasoning about recursive functions or inductive types
#set-options "--max_fuel 0 --max_ifuel 0"

/// Three main identities about *, %, /
/// Proven without smt.arith.nl
/// But using lemmas in FStar.Math.Lemmas
let kdiv_kdiv (#m #p #r:dim) (i:knat (dprod (dprod m p) r))
  : Lemma (let i' : knat (dprod m (dprod p r)) = i in
           kdiv i' = kdiv (kdiv i))
  = let open Math in
    swap_mul p r;
    division_multiplication_lemma i r p

let kmod_kmod (#m #p #r:dim) (i:knat (dprod (dprod m p) r))
  : Lemma (let i' : knat (dprod m (dprod p r)) = i in
           kmod i = kmod (kmod i'))
  = let open Math in
    swap_mul p r;
    modulo_modulo_lemma i r p

let kmod_kdiv (#m #p #r:dim) (i:knat (dprod (dprod m p) r))
  : Lemma (let i' : knat (dprod m (dprod p r)) = i in
           kmod (kdiv i) == kdiv (kmod i'))
  = let open Math in
    swap_mul p r;
    modulo_division_lemma i r p

/// `kron_assosiative`: The main associativity proof for kronecker_product
let kron_associative
     (#a:Type) {| numeric a |}
     (#m #n #p #q #r #s:dim)
     (x1:matrix a m n)
     (x2:matrix a p q)
     (x3:matrix a r s)
  : Lemma (k (k x1 x2) x3 == k x1 (k x2 x3))
  = let lhs = k (k x1 x2) x3 in
    let rhs = k x1 (k x2 x3) in
    let kron_aux (i:knat (dprod (dprod m p) r))
                 (j:knat (dprod (dprod n q) s))
        : Lemma (index (k (k x1 x2) x3) i j == index (k x1 (k x2 x3)) i j)
        = let lhs = k (k x1 x2) x3 in
          let rhs = k x1 (k x2 x3) in
          k_index (k x1 x2) x3 i j;
          k_index x1 x2 (kdiv i) (kdiv j);
          assert (index lhs i j ==
                      (mul (mul (index x1 (kdiv (kdiv i)) (kdiv (kdiv j)))
                                 (index x2 (kmod (kdiv i)) (kmod (kdiv j))))
                           (index x3 (kmod i) (kmod j))));
          let i' : knat (dprod m (dprod p r)) = i in
          let j' : knat (dprod n (dprod q s)) = j in
          k_index x1 (k x2 x3) i' j';
          k_index x2 x3 (kmod i') (kmod j');
          assert (index rhs i j ==
                      mul (index x1 (kdiv i') (kdiv j'))
                          (mul (index x2 (kdiv (kmod i')) (kdiv (kmod j')))
                               (index x3 (kmod (kmod i')) (kmod (kmod j')))));
          kdiv_kdiv i;
          kdiv_kdiv j;
          kmod_kdiv i;
          kmod_kdiv j;
          kmod_kmod i;
          kmod_kmod j;
          let e1 : a = (index x1 (kdiv (kdiv i)) (kdiv (kdiv j))) in
          let e2 : a = (index x2 (kmod (kdiv i)) (kmod (kdiv j))) in
          let e3 : a = (index x3 (kmod i) (kmod j)) in
          assert (index lhs i j == mul (mul e1 e2) e3);
          mul_assoc e1 e2 e3;
          //assert (mul (mul e1 e2) e3 == mul e1 (mul e2 e3)); // fails -- but should succeed
          //assert (index lhs i j == mul e1 (mul e2 e3)); // fails
          admit()
    in
    FStar.Classical.forall_intro_2_with_pat (index lhs) kron_aux;
    lemma_eq_intro lhs rhs;
    lemma_eq_elim lhs rhs

#reset-options //Turn smt.arith.nl back on

//now, if we really care, we can restate the lemma in terms of
//`kronecker_product` instead of `k`

//This set of F* options is well-tuned for arithmetic
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"
//We're not reasoning about recursive functions or inductive types
#set-options "--max_fuel 0 --max_ifuel 0"
let lemma_kron_associative
      (#a:Type) {| num:numeric a |}
      (#m #n #p #q #r #s:dim)
      (x1:matrix a m n)
      (x2:matrix a p q)
      (x3:matrix a r s)
  : Lemma
    (ensures
      (kronecker_product #a #num #(m * p) #(n * q) #r #s (kronecker_product #a #num #m #n #p #q x1 x2) x3 ==
       kronecker_product #a #num #m #n #(p * r) #(q * s) x1 (kronecker_product x2 x3)))
  = kron_associative x1 x2 x3
#reset-options
