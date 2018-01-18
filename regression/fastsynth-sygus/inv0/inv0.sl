(set-logic BV)

(synth-fun inv () (BitVec 8) )

(declare-var x (BitVec 8) )

(constraint (< #x00 inv))

(check-synth)
