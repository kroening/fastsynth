(set-logic BV)

(synth-fun inv ((x (BitVec 4))) Bool )

; base case
(constraint (inv #x0))

(declare-var x (BitVec 4) )

; property
(constraint (=> (and (inv x) (not (= (bvadd x #x1) #xa)))
                (not (= (bvadd x #x1) #xf))))

; step case
(constraint (=> (and (inv x) (not (= (bvadd x #x1) #xa)))
                (inv (bvadd x #x1))))

(check-synth)
