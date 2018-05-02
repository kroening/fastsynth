(set-logic BV)

(synth-fun func ((w (BitVec 32))(x (BitVec 32))(y (BitVec 32))(z (BitVec 32))) (BitVec 32)
)

(declare-var w (BitVec 32))

(declare-var x (BitVec 32))

(declare-var y (BitVec 32))

(declare-var z (BitVec 32))

; any spec will do, we don't use the spec for function generation
(constraint 
(= (func x y z w) (func y x z w))
)

(check-synth)


