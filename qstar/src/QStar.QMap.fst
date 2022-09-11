module QStar.QMap

assume
val qref : eqtype

let qmap = qref -> option nat

// A valid qmap with size n has two properties:
//  * every live qref is mapped to a nat bounded by n
//  * live qrefs are mapped to distinct nats 
let valid_qmap : Type0 =
  n:nat & 
  m:qmap{(forall q. Some? (m q) ==> Some?.v (m q) < n) /\
         (forall q1 q2. (Some? (m q1) /\ Some? (m q2) /\ q1 <> q2) ==> 
                   Some?.v (m q1) <> Some?.v (m q2))}

let live (m:valid_qmap) (q:qref) : prop = 
  let (| _, m |) = m in Some? (m q) == true

let sel (m:valid_qmap) (q:qref{live m q}) : nat = 
  let (| _, m |) = m in Some?.v (m q)

let size_of (m:valid_qmap) : nat =
  let (| n, _ |) = m in n

let is_fresh (m:valid_qmap) (q:qref) : prop =
  forall q'. live m q' ==> q <> q'

assume // we'll have to pass state for this
val fresh : (m:valid_qmap) -> (q:qref{is_fresh m q})

// extend the qmap by one
let extend (m:valid_qmap) : (qref & valid_qmap) =
  let q = fresh m in 
  assert (is_fresh m q);
  let (| n, m |) = m in
  ( q, (| n + 1, (fun q' -> if q = q' then Some n else m q') |) )

let lemma_fresh_q m q
  : Lemma (requires live m q)
          (ensures fresh m <> q)
    [SMTPat (fresh m <> q)]
  = ()

// shrink the qmap by one
let shrink (m:valid_qmap{size_of m > 0}) : valid_qmap =
  let (| n, m0 |) = m in
  let m0' q = if Some? (m0 q) && Some?.v (m0 q) = n - 1
              then None else m0 q in
  (| n - 1, m0' |)

let lemma_shrink_extend m
  : Lemma (shrink (snd (extend m)) == m)
    [SMTPat (shrink (snd (extend m)))]
  = admit() // requires functional extensionality

let lemma_shrink_live m q
  : Lemma (requires (live m q /\ sel m q < size_of m - 1))
          (ensures (live (shrink m) q))
    [SMTPat (live (shrink m) q)]
  = ()

let lemma_shrink_live_converse m q
  : Lemma (requires (live (shrink m) q))
          (ensures (live m q /\ sel m q < size_of m - 1))
    [SMTPat (live (shrink m) q)]
  = ()
