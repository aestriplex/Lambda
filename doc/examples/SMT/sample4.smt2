; File name:    Sample4.smt2
; 
; Copyright (c) May, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(declare-datatypes (T U) 
    (
        (Stack (mk-pair (cont T) (index U)))
    )
)

(declare-const s (Stack String Int))
(declare-const input String)
(define-const LPAR String "(")
(define-const RPAR String ")")
(define-const EMPTY Int 0)

(define-fun init_stack ((_s (Stack String Int))) Bool
    (= (index _s) 0)
)

(define-fun search_err ((_s (Stack String Int))) Bool
    (ite 
        (= (index _s) EMPTY)
        false
        true
    )
)

(define-fun push_par ((_s (Stack String Int)) (_s1 (Stack String Int)) (_p String)) Bool
    (ite
        (= _p LPAR)
        (= (index _s1) (+ (index _s0) 1))
    )
)

(define-fun walk ((_s (Stack String Int)))
)
(assert (init_stack s))
