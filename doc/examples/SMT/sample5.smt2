; File name:    Sample5.smt2
; 
; Copyright (c) May, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(declare-const a Bool)
(declare-const b Bool)

(define-fun _and ((_a Bool) (_b Bool)) Bool
    (and _a _b)
)
(define-fun lazy ((_n Bool)) Bool
    _n
)

(assert (= a true))
(assert (= b false))

(echo "Eager evaluation")
(push)
(assert (not (= (_and a b) false)))
(check-sat)
(pop)

(echo "Lazy evaluation")
(assert (not (= (_and (lazy a) (lazy b)) false)))
(check-sat)
