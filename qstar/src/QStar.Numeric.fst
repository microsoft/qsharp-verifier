module QStar.Numeric

open FStar.Mul

(*** numeric typeclass ***)

// TODO: give this a more descriptive name?
class numeric a = {
  zero : a;
  one : a;
  add : a -> a -> Tot a;
  mul : a -> a -> Tot a;
  conj : a -> Tot a;
  add_zero_l : squash (forall (x : a).{:pattern add zero x} add zero x == x);
  add_zero_r : squash (forall (x : a).{:pattern add x zero} add x zero == x);
  add_comm : (x : a) -> (y : a) -> Lemma (add x y == add y x);
  add_assoc : (x : a) -> (y : a) -> (z : a) -> Lemma (add (add x y) z == add x (add y z));
  mul_zero_l : squash (forall (x : a).{:pattern mul zero x} mul zero x == zero);
  mul_zero_r : squash (forall (x : a).{:pattern mul x zero} mul x zero == zero);
  mul_one_l : squash (forall (x : a).{:pattern mul one x} mul one x == x);
  mul_one_r : squash (forall (x : a).{:pattern mul x one} mul x one == x);
  mul_comm : (x : a) -> (y : a) -> Lemma (mul x y == mul y x);
  mul_assoc : (x : a) -> (y : a) -> (z : a) -> Lemma (mul (mul x y) z == mul x (mul y z));
  add_mul_distr_l : (x : a) -> (y : a) -> (z : a) -> Lemma (mul x (add y z) == add (mul x y) (mul x z));
  add_mul_distr_r : (x : a) -> (y : a) -> (z : a) -> Lemma (mul (add x y) z == add (mul x z) (mul y z));
  conj_involutive : squash (forall (x : a).{:pattern conj (conj x)} conj (conj x) == x);
  conj_add_distr : squash (forall (x : a) (y : a).{:pattern conj (add x y)} conj (add x y) == add (conj x) (conj y));
  conj_mul_distr : squash (forall (x : a) (y : a).{:pattern conj (mul x y)} conj (mul x y) == mul (conj x) (conj y))
  // other lemmas about add, mul, ...
}

instance numeric_int : numeric int =
  Mknumeric 0 1 ( + ) ( * ) (fun x -> x)
            () () (fun x y -> ()) (fun x y z -> ())
            () () () () (fun x y -> ()) (fun x y z -> ())
            (fun x y z -> ()) (fun x y z -> ())
            () () ()

open FStar.Real

let mul_dist_r (x y z : real) : Lemma ((x +. y) *. z = (x *. z) +. (y *. z)) = admit() // need to add to FStar.Real
let mul_assoc' (x y z : real) : Lemma ((x *. y) *. z = x *. (y *. z)) = admit() // need to fix in FStar.Real
let mul_dist' (x y z : real) : Lemma (x *. (y +. z) = (x *. y) +. (x *.z)) = admit() // no idea why I need to define this (using FStar.Real.mul_dist results in 'postcondition could not be proven')

instance numeric_real : numeric real = {
  zero = 0.0R;
  one = 1.0R;
  add = ( +. ); 
  mul = ( *. );
  conj = (fun x -> x); // identity
  add_zero_l = add_id_l;
  add_zero_r = add_id_r;
  add_comm = (fun _ _ -> add_comm);
  add_assoc = (fun _ _ _ -> add_assoc);
  mul_zero_l = mul_nil_l;
  mul_zero_r = mul_nil_r;
  mul_one_l = mul_id_l;
  mul_one_r = mul_id_r;
  mul_comm = (fun _ _ -> mul_comm);
  mul_assoc = mul_assoc';
  add_mul_distr_l = mul_dist';
  add_mul_distr_r = mul_dist_r;
  conj_involutive = ();
  conj_add_distr = ();
  conj_mul_distr = ()
  }

open QStar.Complex

instance numeric_complex : numeric complex = {
  zero = c0;
  one =  c1; 
  add = cadd; 
  mul = cmul;
  conj = cconj;
  add_zero_l = cmul_0_l;
  add_zero_r = cmul_0_r;
  add_comm = (fun _ _ -> cadd_comm);
  add_assoc = (fun _ _ _ -> cadd_assoc);
  mul_zero_l = cmul_0_l;
  mul_zero_r = cmul_0_r; //this doesn't have the right type
  mul_one_l = cmul_1_l;
  mul_one_r = cmul_1_r;
  mul_comm = cmul_comm;
  mul_assoc = cmul_assoc;
  add_mul_distr_l = cmul_dist_l;
  add_mul_distr_r = cmul_dist_r;
  conj_involutive = cconj_inv;
  conj_add_distr = cconj_cadd;
  conj_mul_distr = FStar.Classical.forall_intro_2 cconj_cmul
  }
