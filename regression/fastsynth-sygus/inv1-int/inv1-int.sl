(set-logic LIA)

(synth-fun inv ((x Int)) Bool)

; base case
(constraint (inv 0))

(declare-var x Int )

; property
(constraint (=> (and (inv x) (not (= (+ x 1) 10)))
                (not (= (+ x 1) 255))))

; step case
(constraint (=> (and (inv x) (not (= (+ x 1) 10)))
                (inv (+ x 1))))

(check-synth)
