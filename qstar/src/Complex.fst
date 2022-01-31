module Complex

open FStar.Real
//Use again our set of F* options well-tuned for arithmetic
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

// More functions for reals
val sqrt : r:real -> r':real{r' *. r' = r}

val sqr : real -> real
let sqr r = r *. r

val pow : real -> nat -> real
let rec pow r n = if n = 0 then 1.0R else pow r (n-1) 

// Complex numbers
type complex = real * real

val of_real : real -> Tot complex
let of_real r = (r, 0.0R)

let ci : complex = (0.0R, 1.0R)
let c0 : complex = of_real 0.0R
let c1 : complex = of_real 1.0R

(* Will define notations later *)
val cadd : complex -> complex -> Tot complex
let cadd (r1,i1) (r2,i2) = (r1 +. r2, i1 +. i2)

val csub : complex -> complex -> Tot complex
let csub (r1,i1) (r2,i2) = (r1 -. r2, i1 -. i2)

val cmul : complex -> complex -> Tot complex
let cmul (r1,i1) (r2,i2) = (r1 *. r2 -. i1 *. i2, r1 *. i2 +. i1 *. r2)

(* Possible restrictions:
1) fst y <> 0.0R \/ snd y <> 0.0R
2) fst y *. fst y <> 0.0R \/ snd y *. snd y <> 0.0R
3) fst y *. fst y <> 0.0R + snd y *. snd y <> 0.0R
Unfortunately, 1 fails while 2 and 3 succeed. *)
val cinv : y:complex{fst y *. fst y <> 0.0R \/ snd y *. snd y <> 0.0R} -> Tot complex
let cinv (r,i) = (r /. (r *. r +. i *. i), 0.0R -. i /. (r *. r +. i *. i))

// val cmod : complex -> Tot real
// let cmod (r,i) = sqrt (sqr r +. sqr i)
val cmod : (c : complex) -> r:real{sqr r = (sqr (fst c) +. sqr (snd c))}

// let sqr0_test = assert (forall x . x *. x = 0.0R -> x = 0.0R) // Fails

(* Direct definition of cdiv
val cdiv : complex -> y:complex{fst y *. fst y +. snd y *. snd y <> 0.0R} -> Tot complex
let cdiv (r1,i1) (r2,i2) = ((r1 *. r2 +. i1 *. i2) /. (r2 *. r2 +. i2 *. i2), 
                            (i1 *. r2 -. r1 *. i2) /. (r2 *. r2 +. i2 *. i2))
*)

val cdiv : complex -> y:complex{fst y *. fst y <> 0.0R \/ snd y *. snd y <> 0.0R} -> Tot complex
let cdiv x y = cmul x (cinv y) 

val cpow : complex -> nat -> complex 
let rec cpow x n = if n = 0 then c1 else cpow x (n-1) 

val cconj : complex -> Tot complex
let cconj (r,i) = (r, 0.0R -. i)

let cconj_inv = assert (forall x. cconj (cconj x) = x)

let cadd_0_l = assert (forall x. cadd c0 x = x)
let cadd_0_r = assert (forall x. cadd x c0 = x)

let cmul_0_l = assert (forall x. cmul c0 x = c0)
let cmul_0_r = assert (forall x. cmul x c0 = c0)
let mul_nil_r = assert (forall x. x *. 0.0R = 0.0R)

let csub_0_r = assert (forall x. csub x c0 = x)
let csub_n_n = assert (forall x. csub x x = c0)

let cmul_1_l = assert (forall x. cmul c1 x = x)
let cmul_1_r = assert (forall x. cmul x c1 = x)

let cadd_comm = assert (forall x y. cadd x y = cadd y x)
let cadd_assoc = assert (forall x y z. cadd (cadd x y) z = cadd (cadd x y) z)

let cmul_comm (c1 c2 : complex)
  : Lemma (cmul c1 c2 == cmul c2 c1)
  = let r1, i1 = c1 in
    let r2, i2 = c2 in    
    assert ((r1 *. i2) +. (i1 *. r2) ==
           (r2 *. i1) +. (i2 *. r1));
    assert ((r1 *. r2) -. (i1 *. i2) ==
           (r2 *. r1) -. (i2 *. i1))

let cmul_assoc (c1 c2 c3 : complex) 
  : Lemma (cmul (cmul c1 c2) c3 = cmul c1 (cmul c2 c3))
  = let r1, i1 = c1 in
    let r2, i2 = c2 in
    let r3, i3 = c3 in
    let c1c2_r = (r1 *. r2) -. (i1 *. i2) in
    let c1c2_i = (r1 *. i2) +. (i1 *. r2) in
    let c2c3_r = (r2 *. r3) -. (i2 *. i3) in
    let c2c3_i = (r2 *. i3) +. (i2 *. r3) in
    assert ((c1c2_r *. r3) -. (c1c2_i *. i3) == (r1 *. c2c3_r) -. (i1 *. c2c3_i));
    assert ((c1c2_r *. i3) +. (c1c2_i *. r3) == (r1 *. c2c3_i) +. (i1 *. c2c3_r))

let cmul_dist_l (c1 c2 c3 : complex) 
  : Lemma (cmul c1 (cadd c2 c3) = cadd (cmul c1 c2) (cmul c1 c3))
  = let r1, i1 = c1 in
    let r2, i2 = c2 in    
    let r3, i3 = c3 in
    assert (r1 *. (r2 +. r3) -. i1 *. (i2 +. i3) == 
            r1 *. r2 +. r1 *. r3 -. i1 *. i2 -. i1 *. i3);
    assert (r1 *. (i2 +. i3) +. i1 *. (r2 +. r3) ==
            r1 *. i2 +. r1 *. i3 +. i1 *. r2 +. i1 *. r3)

let cmul_dist_r (c1 c2 c3 : complex)
  : Lemma (cmul (cadd c1 c2) c3 = cadd (cmul c1 c3) (cmul c2 c3))
  = cmul_comm (cadd c1 c2) c3;
    cmul_dist_l c3 c1 c2;
    cmul_comm c3 c1; 
    cmul_comm c3 c2

let test = assert (exists x. cmul c1 x = c0)

let cdiv_id (c:complex{fst c *. fst c <> 0.0R \/ snd c *. snd c <> 0.0R})
  : Lemma (cdiv c c == c1)
  = let r, i = c in
    assert (cinv (r,i) == (r /. (r *. r +. i *. i), 
                           0.0R -. i /. (r *. r +. i *. i)));
    assert (fst (cdiv (r,i) (r,i)) == r *. (r /. (r *. r +. i *. i)) 
                                   -. i *. (0.0R -. i /. (r *. r +. i *. i)));
    assert (r *. (r /. (r *. r +. i *. i)) -. 
            i *. (0.0R -. i /. (r *. r +. i *. i)) == 
            r *. (r /. (r *. r +. i *. i)) +. i *. (i /. (r *. r +. i *. i)));
    assert (r *. (r /. (r *. r +. i *. i)) +. i *. (i /. (r *. r +. i *. i)) == 
            r *. r /. (r *. r +. i *. i) +. i *. i /. (r *. r +. i *. i));
    assert (r *. r /. (r *. r +. i *. i) +. i *. i /. (r *. r +. i *. i) == 
            (r *. r +. i *. i) /. (r *. r +. i *. i));
    assert (forall x. x /. x == 1.0R);
    assert ((r *. r +. i *. i) /. (r *. r +. i *. i) == 1.0R)
    
let cdiv_1_r (c:complex) : Lemma (cdiv c c1 == c) = ()

let cconj0 = assert (cconj c0 = c0)
// let cconj0' = assert (forall n . cconj n = c0 -> n = c0) //Failed
let cconj1 = assert (cconj c1 = c1)

let cconj_cadd = assert (forall c1 c2. cconj (cadd c1 c2) == cadd (cconj c1) (cconj c2))

let cconj_cmul c1 c2 
  : Lemma (cconj (cmul c1 c2) == cmul (cconj c1) (cconj c2))
  = let r1, i1 = c1 in
    let r2, i2 = c2 in 
    assert (0.0R -. (r1 *. i2 +. i1 *. r2) == r1 *. (0.0R -. i2) +. (0.0R -. i1) *. r2)

let cconj_of_real = assert (forall x. cconj (of_real x) = of_real x)
let cadd_of_real = assert (forall x y. cadd (of_real x) (of_real y) = of_real (x +. y))
let csub_of_real = assert (forall x y. csub (of_real x) (of_real y) = of_real (x -. y))
let cmul_of_real = assert (forall x y. cmul (of_real x) (of_real y) = of_real (x *. y))
// let cdiv_of_real = assert (forall x (y:real{y<>0}). cdiv (of_real x) (of_real y) = of_real (x /. y)) // I don't know how to make this typecheck



(* From Leonardo de Moura's blog:

x = Complex("x")
s = Tactic('qfnra-nlsat').solver()
s.add(x*x + 2 == 0)
print(s.check())
m = s.model()
print('x = %s' % evaluate_cexpr(m, x))

Can we do this in F*?

*)
