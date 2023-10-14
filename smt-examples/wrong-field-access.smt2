(set-logic QF_DT)
(set-option :produce-models true)
(declare-datatype MaybeBool ((Nothing) (Just (the Bool))))

(declare-const foo MaybeBool)
(assert (= (the foo) true))
(assert ((_ is Nothing) foo))
(check-sat)
(get-model)
