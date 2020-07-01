(set-logic QF_ABV)

; generate that
(synth-fun somefun ((a (Array (_ BitVec 32) (_ BitVec 8)))) (_ BitVec 8))

(declare-var a (Array (_ BitVec 32) (_ BitVec 8)))

(constraint (= (somefun a) (select a #x00000001)))

(check-synth)
