; exercise from https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Courses/SS2023/PV/slides/02-sat-smt-pt2.pdf


(set-logic ALL)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :verbose 10)


(declare-sort Pair 2)
; (define-sort Word64 () (_ BitVec 64))
(define-sort Word64 () Int)

(declare-fun pair (Word64 Word64) (Pair Word64 Word64))
(declare-fun fst ((Pair Word64 Word64)) Word64)
(declare-fun snd ((Pair Word64 Word64)) Word64)

(assert (forall ((a Word64) (b Word64))
    (! (= (fst (pair a b)) a))
    ; :pattern
    )
)

(assert (distinct (fst (pair 1 2)) 1))
(check-sat)
(get-info :reason-unknown)
