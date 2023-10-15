(set-logic ALL)
(set-option :produce-models true)

(declare-const As (Array Int Bool))
(declare-const Bs (Array Int Bool))
(declare-const Cs (Array Int Bool))


(assert (forall ((x Int))
    (= (or (select As x) (select Bs x))
        (select Cs x))
))

(assert (select As 10))
; (assert (not (select Cs 10)))
(check-sat)
(get-model) ; what? it gives me unknown but also gives a model?



