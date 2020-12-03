(set-logic LIA)

(synth-fun someconst () Int)

(constraint (let ((x (+ 1 1))) (<= x someconst)))
(constraint (let ((x (+ 1 2))) (> x someconst)))

(check-synth)
