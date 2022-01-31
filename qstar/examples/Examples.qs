namespace QStar.Translator.Example {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;

    operation ApplyH (q : Qubit) : Unit {
        H(q);
    }

    operation PrepareBell (q1 : Qubit, q2 : Qubit) : Unit is Adj {
        H(q1); CNOT(q1, q2);
    }

    operation PrepareGhz (q1 : Qubit, q2 : Qubit, q3 : Qubit) : Unit {
        H(q1); CNOT(q1, q2); CNOT(q1, q3);
    }

    operation Reset (q : Qubit) : Unit {
        let res = M(q);
        if res == One {
            X(q);
        }
    }

    operation FlipCoin () : Result {
        use q = Qubit();
        H(q);
        let res = M(q);
        return res;
    }

    operation MeasureBell () : (Result, Result) {
        use q1 = Qubit();
        use q2 = Qubit();
        PrepareBell(q1, q2);
        let res1 = M(q1);
        let res2 = M(q2);
        return (res1, res2);
    }

    operation MeasureGhz () : (Result, Result, Result) {
        use q1 = Qubit();
        use q2 = Qubit();
        use q3 = Qubit();
        PrepareGhz(q1, q2, q3);
        let res1 = M(q1);
        let res2 = M(q2);
        let res3 = M(q3);
        return (res1, res2, res3);
    }

    operation IntializeDependingOnMeasurement (q : Qubit) : Unit {
        let res = M(q);
        if (res == One) { 
            use qnew = Qubit(); 
            X(q); 
        }
    }

    operation BranchInsideInitialization () : Unit {
        use q = Qubit();
        let res = M(q);
        if (res == One) { 
            X(q); 
        }
    }

    operation PerformSuperdenseCoding(b1 : Bool, b2 : Bool) : (Result, Result) {
        use q1 = Qubit();
        use q2 = Qubit();
        PrepareBell(q1, q2);
        if b2 { X(q1); }
        if b1 { X(q1); }
        Adjoint PrepareBell(q1, q2);
        let res1 = M(q1);
        let res2 = M(q2);
        return (res1, res2);
    }

    operation Teleport(src: Qubit, target: Qubit) : Unit {
        use a = Qubit();

        // Entangle
        PrepareBell(a, target);

        // Encode
        CNOT(src, a);
        H(src);
        let m1 = M(src);
        let m2 = M(a);

        // Decode
        if (m2 == One) { X(target); }
        if (m1 == One)  { Z(target); }
    }

    operation DoSomethingBad1(q : Qubit) : Unit {
        CNOT(q, q);
    }

    operation DoSomethingBad2() : Unit {
        use q = Qubit();
        CNOT(q, q);
    }

    operation DoSomethingBad3(q1 : Qubit) : Unit {
        let q2 = q1;
        CNOT (q1, q2);
    }

    operation InitQubit() : Qubit {
        use q = Qubit();
        return q;
    }

    operation DoSomethingBad4() : Unit {
        let q = InitQubit ();
        X(q);
    }

    operation PossiblyInitQubit(qIn : Qubit) : Qubit {
        use qOut = Qubit();
        let res = FlipCoin();
        if res == Zero {
            return qIn;
        } else {
            return qOut;
        }
    }

    operation DoSomethingBad5(qIn : Qubit) : Unit {
        let qNew = PossiblyInitQubit(qIn);
        X(qNew);
    }

    // adapted from https://github.com/microsoft/QuantumLibraries/blob/main/Standard/src/Canon/And.qs
    operation ApplyAnd (control1 : Qubit, control2 : Qubit, target : Qubit) : Unit {
        body (...) {
            H(target);
            T(target);
            CNOT(control1, target);
            CNOT(control2, target);
            within {
                CNOT(target, control1);
                CNOT(target, control2);
            }
            apply {
                Adjoint T(control1);
                Adjoint T(control2);
                T(target);
            }
            H(target);
            S(target);
        }
        adjoint (...) {
            H(target);
            let res = M(target);
            Reset(target);
            if (res == One) {
                CZ(control1, control2);
            }
        }
    }
}
