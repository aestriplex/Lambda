; File name:    Sample5.smt2
; 
; Copyright (c) May, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(declare-const a  (List String))
(declare-const b  (List String))
(declare-const c  (List String))
(declare-const d  (List String))
(declare-const e  (List String))
(declare-const f  (List String))

(define-fun do ((head String)) Bool
    (<= (str.len head) 10)
)

(define-fun-rec walk ((_l (List String))) Bool
    (ite 
        (not (= _l nil))
        (and
            (do (head _l))
            (walk (tail _l))
        )
        true
    )
)

; filling the list
(assert
    (and
        (= a nil)
        (= b (insert "boNVAMt" a))
        (= c (insert "IywNRY7ef" b))
        (= d (insert "cT1" c))
        (= e (insert "kvvlaaU" d))
        (= f (insert "RueGM" e))
    )
)
(assert (not (walk f)))

; `unsat` expected
(check-sat)
(exit)