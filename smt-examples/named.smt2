(set-logic ALL)
(set-option :interactive-mode true)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (=> (! (> x y) :named p1)
            (! (= x z) :named p2 )))

(define-fun foo ((a Int) (b Int) (c Int)) Bool
    (=> (! (> a b) :named p11)
        (! (= a c) :named p22))
)

(check-sat)
(get-model)
(get-assertions)
(get-assignment)
