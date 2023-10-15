(set-option :auto_config false)
(set-option :smt.mbqi true)

(declare-const As (Array Int Bool))
(declare-const Bs (Array Int Bool))
(declare-const Cs (Array Int Bool))

; quantifying over all sets prevents z3 from finding counter models
; But if I instanciate the set.union definition, then it works.

; (declare-fun set.union ((Array Int Bool) (Array Int Bool)) (Array Int Bool))
; (assert (forall ((x Int) (Bs (Array Int Bool)) (As (Array Int Bool)))
;     (= (or (select As x) (select Bs x))
;        (select (set.union As Bs) x))
; ))
(assert (forall ((x Int))
    (= (or (select As x) (select Bs x))
        (select Cs x))
))

; (assert (= Cs (set.union As Bs)))
(assert (select As 10))
; (assert (not (select Cs 10)))
(check-sat)
(get-model)



