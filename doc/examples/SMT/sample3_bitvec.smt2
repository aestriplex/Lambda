; File name:    Sample3_bitvec.smt2
; 
; Copyright (c) March, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(define-sort Float () (_ BitVec 32))
(declare-const x0 Float)
(declare-const y0 Float)
(declare-const res0 Float)
(declare-const res1 Float)

(define-fun bound_perc ((_n Float)) Bool
    (and
        (or (bvugt _n #x00000000) (= _n #x00000000))
        (or (bvult _n #x00000001) (= _n #x00000001))
    )
)

(define-fun increase ((_x Float) (_y Float)) Float
    (bvadd _x _y)
)

(define-fun average_if ((_x Float) (_y Float)) Float
    (ite 
        (bvugt _x #x00000001)
        (bvneg #x00000001)
        (bvudiv (bvadd _x _y) #x00000002)
    )
)

(define-fun body ((_x Float) (_y Float) (r0 Float) (r1 Float)) Bool
    (=
        r1
        (ite
            (bvugt _x _y)
            (increase _x _y)
            (ite
                (bvult _x (bvudiv #x00000001 #x00000002))
                (average_if _x _y)
                r0
            )
        )
    )
)

(define-fun post ((_r Float)) Bool
    (= _r (bvneg #x00000001))
)

; initialization of the variable `res`
(assert (= res0 #x00000000))

; percentage constraints
(assert (bound_perc x0))
(assert (bound_perc y0))

; the main function
(assert (body x0 y0 res0 res1))

; the clause we have to check
(assert (post res1))

; `unsat` expected
(check-sat)
(exit)