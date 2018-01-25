(set-logic BV)

(synth-fun fb ((in (BitVec 8) )) (BitVec 8))

(synth-fun fc ((in2 (BitVec 8)) ) (BitVec 8) )

(declare-var A (BitVec 8) )
(declare-var B (BitVec 8) )

(constraint (= ( fc B ) (bvadd (fb A ) #x10)))

(check-synth)
