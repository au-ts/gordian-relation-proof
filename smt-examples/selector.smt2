(set-logic QF_DT)
(set-option :incremental true)
(set-option :produce-models true)

(declare-datatype Maybe (par (X) (
    (Nothing)
    (Just (just X))
)))

(declare-const a (Maybe Bool))


(push)
    ; From this, I deduce that (just a) where a is Nothing returns an
    ; arbitrary value of type bool
    (assert (= true (just a)))
    (assert (distinct a (Just false)))
    (assert (distinct a (Just true)))
    (check-sat)
    (get-model)
(pop)

; (push)
;     (assert (distinct (just a) true))
;     (check-sat)
;     (get-model)
;     (get-value (a))
; (pop)

