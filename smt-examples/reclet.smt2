(set-logic ALL)

(assert (let ((a 1) (b a)) (= a b)))
(check-sat)
