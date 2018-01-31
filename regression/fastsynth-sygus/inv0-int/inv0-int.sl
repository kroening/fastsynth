(set-logic LIA)

(synth-fun inv () Int)

; help
(constraint (< inv 20))

; base case
(constraint (< 0 inv))

(declare-var x Int )

; property
(constraint (=> (and (< x inv) (not (= (+ x 1) 10)))
                (not (= (+ x 1) 255))))

; step case
(constraint (=> (and (< x inv) (not (= (+ x 1) 10)))
                (< (+ x 1) inv)))

(check-synth)
