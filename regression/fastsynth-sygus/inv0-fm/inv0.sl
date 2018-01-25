(set-logic BV)

(synth-fun inv () (BitVec 32) )

; help
;(constraint (bvult inv #x00000020))

; base case
(constraint (bvult #x00000000 inv))

(declare-var x (BitVec 32) )

; property
(constraint (=> (and (bvult x inv) (not (= (bvadd x #x00000001) #x0000000a)))
                (not (= (bvadd x #x00000001) #x000000ff))))

; step case
(constraint (=> (and (bvult x inv) (not (= (bvadd x #x00000001) #x0000000a)))
                (bvult (bvadd x #x00000001) inv)))

(check-synth)
