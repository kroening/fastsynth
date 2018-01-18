(set-logic BV)

(synth-fun inv () (BitVec 32) )

; base case
(constraint (< #x00000000 inv))

(declare-var x (BitVec 32) )

; property
(constraint (=> (and (< x inv) (not (= (+ x #x00000001) #x0000000a)))
                (not (= (+ x #x00000001) #x000000ff))))

; step case
(constraint (=> (and (< x inv) (not (= (+ x #x00000001) #x0000000a)))
                (< (+ x #x00000001) inv)))

(check-synth)
