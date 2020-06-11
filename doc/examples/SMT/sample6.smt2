; File name:    Sample6.smt2
; 
; BUBBLESORT  -  Copyright (c) June, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

; arrays declaration
(declare-const A0 (Array Int Int))
(declare-const A1 (Array Int Int))
(declare-const A2 (Array Int Int))
(declare-const A3 (Array Int Int))
(declare-const A4 (Array Int Int))
(declare-const A5 (Array Int Int))

; indexes declaration
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const i4 Int)
(declare-const i5 Int)

(declare-const j0 Int)
(declare-const j1 Int)
(declare-const j2 Int)
(declare-const j3 Int)
(declare-const j4 Int)
(declare-const j5 Int)

(declare-const tmp0 Int)
(declare-const tmp1 Int)
(declare-const tmp2 Int)
(declare-const tmp3 Int)
(declare-const tmp4 Int)
(declare-const tmp5 Int)

; lists declaration (for post condition)
(declare-const l0 (List Int))
(declare-const l1 (List Int))
(declare-const l2 (List Int))
(declare-const l3 (List Int))
(declare-const l4 (List Int))
(declare-const l5 (List Int))

(define-fun init_indexes ((_i Int) (_j Int)) Bool
    (and
        (= _i 0)
        (= _j 0)
    )
)

(define-fun increment ((_i0 Int) (_j0 Int) (_i1 Int) (_j1 Int)) Bool
    (and
        (= _j1 (+ _j0 1))
        (= _i1 (+ _i0 1))
    )
)

; the body of the bubblesort algorithm
(define-fun bsort_step ((_A0 (Array Int Int)) (_A1 (Array Int Int)) (tmp Int) (_i0 Int) (_j0 Int)) Bool
    (ite
        (< _j0 1)
        (ite
            (< _i0 1)
            (ite 
                (> (select _A0 _i0) (select _A0 (+ _i0 1)))
                (and 
                    (= tmp (select _A0 _i0))
                    (= _A1 (store _A0 _i0 (select _A0 (+ _i0 1))))
                    (= _A1 (store _A0 (+ _i0 1) tmp))
                )
                (= _A1 _A0)
            )
            true
        )
        true
    )
)

; the function b which we can check if the array is ordered
(define-fun-rec check ((_l (List Int))) Bool
    (ite 
        (= _l nil)
        true
        (ite
            (not (= (tail _l) nil))
            (and
                (>= (head _l) (head (tail _l)))
                (check (tail _l))
            )
            true
        )
    )
)

(echo "*** BUBBLESORT CHECK ***")

; initialization of the counters
(assert (init_indexes i0 j0))
; the first step of the sorting algorithm
(assert (bsort_step A0 A1 tmp0 i0 j0))

; filling the list for test
(assert
    (and
        (= l0 nil)
        (= l1 (insert (select A1 0) l0))
        (= l2 (insert (select A1 1) l1))
    )
)

; post condition
(assert (not (check l2)))

; `unsat` expected
(check-sat)
(exit)