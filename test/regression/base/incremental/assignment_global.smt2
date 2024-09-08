(set-option :global-declarations true)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(push 1)
(assert (! a :named n0))
(check-sat)
(pop 1)
(assert (! (xor a b) :named n1))
(assert (! a :named n2))
(check-sat)
(get-assignment)
; NOTE: Because of global declarations, the name n0 (and variable a) are still valid even after pop
