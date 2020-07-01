(set-logic BV)

; use this
(define-fun somefun () (_ BitVec 32) #x00000010)

; generate that
(synth-fun someconst () (_ BitVec 32))

(constraint (< someconst #x00000011))
(constraint (>= someconst somefun))

(check-synth)
