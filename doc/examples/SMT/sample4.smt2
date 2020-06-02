; File name:    Sample4.smt2
; 
; Copyright (c) May, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(declare-const l0 (List Int))
(declare-const l1 (List Int))
(declare-const l2 (List Int))
(declare-const l3 (List Int))
(declare-const l4 (List Int))
(declare-const l5 (List Int))


(define-fun condition ((head Int) (next Int)) Bool
    (>= head next)
)

(define-fun-rec check ((_l (List Int))) Bool
    (ite 
        (= _l nil)
        true
        (ite
            (not (= (tail _l) nil))
            (and
                (condition (head _l) (head (tail _l)))
                (check (tail _l))
            )
            true
        )
    )
)

; filling the list
(assert
    (and
        (= l0 nil)
        (= l1 (insert 1 l0))
        (= l2 (insert 2 l1))
        (= l3 (insert 3 l2))
        (= l4 (insert 4 l3))
        (= l5 (insert 5 l4))
    )
)

(assert (not (check l5)))

; `unsat` expected
(check-sat)
(exit)