# qstar/src

This directory contains the core F* code for Q*. Run `make` to compile.

General utilities:
- [`QStar.Numeric.fst`](QStar.Numeric.fst): Generic definition of a numeric datatype used in `Matrix`
- [`QStar.Matrix.fst`](QStar.Matrix.fst): Port of [inQWIRE/QuantumLib](https://github.com/inQWIRE/QuantumLib)'s Matrix.v file to F*
- [`QStar.Complex.fst`](QStar.Complex.fst): Definition of complex numbers
- [`QStar.Quantum.fst`](QStar.Quantum.fst): Common quantum constants and operations (e.g., pad, vector normalization)

Unique to the `sep-logic` branch:
- [`QStar.Vec.fst(i)`](QStar.Vec.fsti): Abstraction for vectors with a commutative tensor operation (warning: many admits)
- [`QStar.Heap.fst`](QStar.Heap.fst): Definition of quantum state and proof that it is a PCM
- [`QStar.Ref.fst(i)`](QStar.Ref.fsti): Definition of the `pts_to` predicate and various operations on the quantum state
- [`QStar.Teleport.fst`](QStar.Teleport.fst`): Quantum teleportation example
