(set-logic BV)

(synth-fun inv () (BitVec 32) )

; help
(constraint (< inv #x00000020))

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

ATOMS: x<inv, x+1<inv, x<10, x>10, x<200, x>200
PLUS: 0<inv

CASE x<inv, x+1<inv, x<10, x<200:    x<inv, x<10
                                     TRUE

CASE x<inv, x+1>=inv, x<10, x<200:   inconsistent arith.

CASE x<inv, x+1<inv, x>10, x<200:    10<x<inv-1, x<200
                                     10<=inv

CASE x<inv, x+1>=inv, x>10, x<200:   inconsistent arith.

CASE x<inv, x+1<inv, x<10, x>200:    inconsistent arith.

CASE x<inv, x+1>=inv, x<10, x>200:   inconsistent arith.

CASE x<inv, x+1<inv, x>10, x>200:    200<x<inv-1
                                     200<=inv

CASE x<inv, x+1>=inv, x>10, x>200:   inconsistent arith.

CASE x>=inv, x+1<inv, x<10, x<200:   x=inv, x<10
                                     inv<10

CASE x>=inv, x+1>=inv, x<10, x<200:  x>=inv, x<10
                                     TRUE

CASE x>=inv, x+1<inv, x>10, x<200:   x=inv, 10<x<200
                                     10<inv<200

CASE x>=inv, x+1>=inv, x>10, x<200:  x>=inv, 10<x<200
                                     inv<200

CASE x>=inv, x+1<inv, x<10, x>200:   inconsistent arith.

CASE x>=inv, x+1>=inv, x<10, x>200:  inconsistent arith.

CASE x>=inv, x+1<inv, x>10, x>200:   x=inv, x>200
                                     inv>200

CASE x>=inv, x+1>=inv, x>10, x>200:  x>=inv, x>200
                                     TRUE
