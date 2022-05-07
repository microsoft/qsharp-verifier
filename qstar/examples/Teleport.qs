namespace QStar.Translator.Teleport {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;

    operation Entangle (qAlice : Qubit, qBob : Qubit)
    : Unit is Adj {
        H(qAlice);
        CNOT(qAlice, qBob);
    }

    operation SendMsg (qAlice : Qubit, qMsg : Qubit)
    : (Bool, Bool) {
        Adjoint Entangle(qMsg, qAlice);
        let m1 = M(qMsg);
        let m2 = M(qAlice);
        return (m1 == One, m2 == One);
    }

    operation DecodeMsg (qBob : Qubit, (b1 : Bool, b2 : Bool))
    : Unit {
        if b1 { Z(qBob); }
        if b2 { X(qBob); }
    }

    operation Teleport (qMsg : Qubit, qBob : Qubit)
    : Unit {
        use qAlice = Qubit();
        Entangle(qAlice, qBob);
        let classicalBits = SendMsg(qAlice, qMsg);
        DecodeMsg(qBob, classicalBits);
    }
}