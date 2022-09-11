# qstar/src

This directory contains the core F* code for Q*. Run `make` to compile.

General utilities:
- [`QStar.Numeric.fst`](QStar.Numeric.fst): Generic definition of a numeric datatype used in `Matrix`
- [`QStar.Matrix.fst`](QStar.Matrix.fst): Port of [inQWIRE/QuantumLib](https://github.com/inQWIRE/QuantumLib)'s Matrix.v file to F*
- [`QStar.Complex.fst`](QStar.Complex.fst): Definition of complex numbers
- [`QStar.Quantum.fst`](QStar.Quantum.fst): Common quantum constants and operations (e.g., pad, vector normalization)

Specific to Q*:
- [`QStar.QMap.fst`](QStar.QMap.fst): Map from qubit references to concrete indices
- [`QStar.QState.fst`](QStar.QState.fst): Interface for working with quantum state and an implementation in terms of complex vectors
- [`QStar.QInst.fst`](QStar.QInst.fst): Quantum instruction trees