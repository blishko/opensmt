(set-logic QF_ALIA)
(set-info :status unsat)
(declare-fun i () Int)
(declare-fun a () (Array Int Int))
(declare-fun j () Int)
(assert (and (= i 0) (= 1 (select a j)) (= a (store a 1 0)) (or (= 1 i) (= j 1))))
(check-sat)
