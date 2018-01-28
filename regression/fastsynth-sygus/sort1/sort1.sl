(set-logic BV)

(synth-fun mysort1 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) )
(synth-fun mysort2 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) )
(synth-fun mysort3 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) )

(declare-var x (BitVec 32) )
(declare-var y (BitVec 32) )
(declare-var z (BitVec 32) )

; property
(constraint (<= (mysort1 x y z) (mysort2 x y z)))
(constraint (<= (mysort2 x y z) (mysort3 x y z)))
(constraint (or (= (mysort1 x y z) x) (= (mysort2 x y z) x) (= (mysort3 x y z) x)))
(constraint (or (= (mysort1 x y z) y) (= (mysort2 x y z) y) (= (mysort3 x y z) y)))
(constraint (or (= (mysort1 x y z) z) (= (mysort2 x y z) z) (= (mysort3 x y z) z)))

(check-synth)
