(declare-const x0 Real)
(declare-const y0 Real)
(declare-const res0 Real)
(declare-const res1 Real)

(define-fun bound_perc ((_n Real)) Bool
    (and
        (or (> _n 0) (= _n 0))
        (or (< _n 1) (= _n 1))
    )
)

(define-fun decrease ((_x Real) (_y Real)) Real
    (* 2 _x)
)

(define-fun increase ((_x Real) (_y Real)) Real
    (+ _x _y)
)

(define-fun average_if ((_x Real) (_y Real)) Real
    (ite 
        (> _x 1)
        -1
        (/ (+ _x _y) 2)
    )
)

(define-fun body ((_x Real) (_y Real) (r0 Real) (r1 Real)) Bool
    (=
        r1
        (ite
            (> _x _y)
            (increase _x _y)
            (ite
                (< _x (/ 1 2))
                (average_if _x _y)
                r0
            )
        )
    )
)

(define-fun post ((_r Real)) Bool
    (= _r -1)
)

(assert (bound_perc x0))
(assert (bound_perc y0))
(assert (= res0 0))
(assert (body x0 y0 res0 res1))
(assert (post res1))
(check-sat)
(exit)