; File name:    Sample2_bitvec.smt2
; 
; Copyright (c) March, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(define-sort IntValue () (_ BitVec 32))
(declare-const x IntValue)
(declare-const A (Array IntValue IntValue))
(declare-const i0 IntValue)
(declare-const f0 IntValue)

(declare-const f1 IntValue)
(declare-const f2 IntValue)
(declare-const i1 IntValue)
(declare-const i2 IntValue)

; Pre-condition: variables initialization
(assert
    (and
        (= i0 #x00000000)
        (= f0 #x00000000)
    )
)

; Transition funcion
(define-fun body ((_f IntValue) (i_0 IntValue) (i_1 IntValue)(_A (Array IntValue IntValue)) (_x IntValue)) Bool
    (and
        (= _f (ite (= _x (select _A i_0)) #x00000001 #x00000000))
        (= i_1 (bvadd i_0 #x00000001))
    )
)

; Post-condition function
(define-fun post ((_f IntValue) (_i IntValue) (_x IntValue) (_A (Array IntValue IntValue))) Bool
    (=
        (= _f #x00000001)
        (= _x (select _A _i))
    )   
)

; Transition function is called DIM times:
; for practical reasons, we are considering here DIM = 2
(assert (body f1 i0 i1 A x))
(assert (body f2 i1 i2 A x))

; Post-condition (negated) is called DIM times:
; for practical reasons, we are considering here DIM = 2
(assert
    (not
        (and
            (post f1 i0 x A)      
            (post f2 i1 x A)
        )
    )
)

; `unsat` expected
(check-sat)
(exit)