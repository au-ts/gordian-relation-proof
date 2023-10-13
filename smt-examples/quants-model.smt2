(set-logic ALL)
; (set-option :incremental true)
(set-option :smt.mbqi false)
(set-option :auto-config false)

(push)
    (declare-datatype Point ((Point (x Int) (y Int))))
    (assert (= (x (Point 1 2)) 1))
    (check-sat) ; this correctly yields SAT
(pop)

(push)
    (declare-sort Point 2)
    (declare-fun x ((Point Int Int)) Int)
    (declare-fun y ((Point Int Int)) Int)
    (declare-fun Point (Int Int) (Point Int Int))

    (assert (forall ((a Int) (b Int))
        (! (= (x (Point a b)) a)
        :pattern ((x (Point a b))))
    ))

    (define-fun p () (Point Int Int) (Point 1 2))

    (assert (not (= (x p) 2)))

    (check-sat)
    (get-info :reason-unknown)
(pop)

