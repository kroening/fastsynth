(set-logic BV)

(synth-fun mymax ((x (BitVec 32)) (y (BitVec 32))) (BitVec 32) )

(declare-var x (BitVec 32) )
(declare-var y (BitVec 32) )

; property
(constraint (<= (mymax x y) x))
(constraint (<= (mymax x y) y))

(constraint (or (= (mymax x y) x) (= (mymax x y) y)))

(check-synth)
