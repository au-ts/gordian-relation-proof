; exercise from https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Courses/SS2023/PV/slides/02-sat-smt-pt2.pdf
; ref https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Courses/SS2019/Program%20Verification/05-EncodingToSMT.pdf

(set-logic ALL)
(set-option :smt.mbqi false)
(set-option :auto_config false)


(declare-sort Pair 2)
; (define-sort Word64 () (_ BitVec 64))
(define-sort Word64 () Int)

(declare-fun pair (Word64 Word64) (Pair Word64 Word64))
(declare-fun fst ((Pair Word64 Word64)) Word64)
(declare-fun snd ((Pair Word64 Word64)) Word64)

(assert (forall ((a Word64) (b Word64))
    (! (= (fst (pair a b)) a)
        :pattern ((pair a b))
        :pattern ()
    )
))

(assert (forall ((a Word64) (b Word64))
    (= (snd (pair a b)) b))
)

(assert (forall ((p (Pair Word64 Word64)))
    (= (pair (fst p) (snd p)) p))
)

(push)
    (assert (distinct (fst (pair 1 2)) 1))
    (check-sat)
(pop)

(push)
    (assert (= (pair 1 2) (pair 2 3)))
    (check-sat)
(pop)

(push)
    (declare-const p (Pair Word64 Word64))
    (declare-const q (Pair Word64 Word64))
    (assert (= (fst p) (fst q)))
    (assert (= (snd p) (snd q)))
    (assert (distinct p q))
    (check-sat)
(pop)

(push)
    (declare-const p (Pair Word64 Word64))
    (declare-const q (Pair Word64 Word64))
    (assert (= (fst p) (fst q)))
    (assert (= (snd p) (snd q)))
    (assert (distinct p q))
    (check-sat)
(pop)

(push)
    (declare-const p (Pair Word64 Word64))
    (declare-const q (Pair Word64 Word64))
    (assert (= p q))
    (assert (distinct (fst p) (fst q)))
    (check-sat)
(pop)

(push)
    (declare-const p (Pair Word64 Word64))
    (declare-const q (Pair Word64 Word64))
    (assert (= p q))
    (assert (distinct (snd p) (snd q)))
    (check-sat)
(pop)

