(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun f (Real) Real)
(assert (>= x y))
(assert (>= y z))
(assert (>= z x)) ; it follows that y >= x and hence that x = y
(assert (not (= (f y) (f x))))
(check-sat)
