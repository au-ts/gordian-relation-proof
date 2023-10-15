; runs fine on CVC5
(set-logic QF_UFLIAFS)
(set-option :produce-models true)

(declare-const As (Set Int))
(declare-const Bs (Set Int))
(declare-const Cs (Set Int))

(assert (= Cs (set.union As Bs)))
(assert (set.member 10 As))
; (assert (not (set.member 10 Cs)))
(check-sat)
(get-model)

