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

; Pre-condition: variables initialization
(assert (= y1 8))

; Body of the program
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

; Post-condition (negated)
(assert
	(not
		(or
			(= y4 7)
			(= y4 9)
		)
	)
)

; `unsat` expected
(check-sat)
(exit)