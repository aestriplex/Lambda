; File name:    Sample2.smt2
; 
; Copyright (c) March, 2020 - Matteo Nicoli
;
; /* Code wants to break free */


(declare-const x Int)
(declare-const A (Array Int Int))

(declare-const i0 Int)
(declare-const f0 Int)

(declare-const f1 Int)
(declare-const f2 Int)
(declare-const f3 Int)

(declare-const i1 Int)

(declare-const f4 Int)
(declare-const f5 Int)
(declare-const f6 Int)

(declare-const i2 Int)

; Precondizione: inizializzazione delle variabili
(assert
    (and
        (= i0 0)
        (= f0 0)
    )
)

; Funzione di transizione
(define-fun body ((f_0 Int) (f_1 Int) (f_2 Int) (f_3 Int) (i_0 Int) (i_1 Int)(_A (Array Int Int)) (_x Int)) Bool
    (and
        (= f_1 1)
        (= f_2 f_0)
        (= f_3 (ite (= _x (select _A i_0)) f_1 f_2))
        (= i_1 (+ i_0 1))
    )
)

; La funzione di transizione vinee chiamata DIM volte:
; Per praticita` consideriamo DIM = 2
; la procedura esposta, ovviamente, vale
; per DIM arbitrariamente grande
(assert (body f0 f1 f2 f3 i0 i1 A x))
(assert (body f3 f4 f5 f6 i1 i2 A x))

; Post-condizione (negata)
(assert
    (not
        (or
            (=
                (= f3 1)
                (= x (select A i0))
            )        
            (=
                (= f6 1)
                (= x (select A i1))
            )
        )
    )
)

; Deve ritornare `unsat`
(check-sat)
(exit)