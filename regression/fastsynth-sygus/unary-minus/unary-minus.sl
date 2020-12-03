(set-logic LIA)

(synth-fun someconst () Int)

(constraint (= someconst (+ 10 (- 1))))

(check-synth)
