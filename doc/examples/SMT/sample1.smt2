; File name:    Sample1.smt2
; 
; Copyright (c) March, 2020 - Matteo Nicoli
;
; /* Code wants to break free */

(declare-const y1 Int)
(declare-const y2 Int)
(declare-const y3 Int)
(declare-const y4 Int)
(declare-const x0 Bool)

; Precondizione, contiene l'inizializzazione delle variabili
(assert (= y1 8))

; Corpo del programma espresso in SSA
(assert
	(and
		(= y2 (- y1 1))
		(= y3 (+ y1 1))
		(=> 
			(= x0 true)
			(= y4 y2)
		)
		(=>
			(= x0 false)
			(= y4 y3)
		)
	)
)

; Negazione della post-condizione 
; (la condizione che voglio che si verifichi)
(assert
	(not
		(or
			(= y4 7)
			(= y4 9)
		)
	)
)

; Mi deve dare 'unsat' (cioe`, la negazione della
; post condizione deve essere insoddisfacibile. 
(check-sat)

; Se ritorna 'sat' significa che ho alemno un controesempio,
; che posso farmi ritornare con l'istruzione (get-model)