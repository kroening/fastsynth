(set-logic BV)

(synth-fun someconst () (BitVec 32))

(constraint (< someconst #x00000021))
(constraint (>= someconst #x00000020))

(check-synth)
