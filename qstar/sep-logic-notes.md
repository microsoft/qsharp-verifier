# Quantum Separation Logic Notes

Notes on implementing a quantum separation logic in Steel using a `qref` type, modelled after the `ref` type and associated operations in `Steel.HigherReference.fst(i)`.

## Quantum Reference Type

A quantum reference stores a pair of a set of defined qubits and a vector state over those qubits. Something along the lines of:
```
assume val qbit : eqtype
let qstate = (qs : set qbit) * (v : vector complex (pow2 (size_of qs)))
let qref = Steel.Memory.ref qstate <pcm proof>
```
Combining two quantum states takes the union of their defined qubits and the abstract tensor product of their vectors. Two states can only be combined if they define a disjoint set of qubits.
```
let composable (q0 q1:qstate) = disjoint (fst q0) (fst q1)
let compose (q0:qstate) (q1:qstate{composable q0 q1}) : qstate = 
  let (qs0, v0) = q0 in
  let (qs1, v1) = q1 in
  (union qs0 qs1, tensor qs0 qs1 v0 v1)
```
(Note: a `tensor` function with this signature doesn't exist in our matrix library, but I'm relatively confident that I can implement it.)

This definition of `compose` is commutative and associative. The unit element is the quantum state with no qubits defined.

## Predicates

We will want a `pts_to r qs v` predicate that says in the quantum reference `r` the set of qubits `qs` (which must be defined in `r`) are in vector state `v`, and are thus unentangled from the rest of the system.

## Quantum Operations

Allocate a new set of qubits, which have unentangled state ket(0).
```
val get_qbits : qref -> set qbit
val init
  : Steel qref emp (fun r -> pts_to r (get_qbits r) ket(0))
```

Discard a set of qubits, which must be unentangled with the rest of the state.
```
val free (#v:erased vector) (r:qref) (qs:set qbit)
  : SteelT unit (pts_to r qs v) (fun _ -> emp)
```

Measure a set of qubits, which unentangles them from the rest of the system. (The nondeterminism is reflected in the return value `n`.)
```
val measure (#v:erased vector) (r:qref) (qs:qbit)
  : SteelT bool (pts_to r (get_qbits r) v)
      (fun n -> pts_to r qs ket(n) `star` pts_to r (get_qbits r \ qs) (project r n v))
```
(We also need to add constraint in the post-condition that `project r n v` has non-zero norm, meaning that the measurement outcome `n` is possible.)

Various rules for applying quantum gates...
```
val applyH (#v:erased vector) (r:qref) (q:qbit)
  : SteelT unit (pts_to r (get_qbits r) v) 
      (fun _ -> pts_to r (get_qbits r) (apply H(q) to v))

val applyCX (#v:erased vector) (r:qref) (q0 q1:qbit{q0 <> q1})
  : SteelT unit (pts_to r (get_qbits r) v) 
      (fun _ -> pts_to r (get_qbits r) (apply CX(q0,q1) to v))
```

For proof, we will need some rule for splitting quantum states along the lines of HigherReference's `share`.
```
val split (#uses:_) (#qs0 #qs1:set qubit) (#v0 #v1:erased) (r:qref)
  : SteelGhostT unit uses
    (pts_to r (union qs0 qs1) (tensor qs0 qs1 v0 v1))
    (fun _ -> pts_to r qs0 v0 `star` pts_to r qs1 v1)
```

## Questions

* How do we verify soundness? Can it be done within F*? Can we reuse on any soundness proofs about Steel?
* Am I using `erased` right? I included it because it's used in HigherReference, but I'm not sure what it does.