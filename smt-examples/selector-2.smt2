(set-logic QF_DT)
(set-option :incremental true)
(set-option :produce-models true)

(declare-datatype DT (
    (Foo (blah Bool))
    (Bar (blah (_ BitVec 64)))
))
