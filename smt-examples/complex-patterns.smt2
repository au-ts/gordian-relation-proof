(set-logic ALL)

(declare-datatype Maybe (
    par (X) ((Nothing) (Just (just X)))
))

(declare-const val (Maybe (Maybe Int)))

; (assert (match val (
;     (Nothing false)
;     (Nothing true)
;     (? false)
; )))

; We don't have complex patterns :(
; that's fair though.

(assert
    (match val (
        ((Just Nothing) false)
        ((Just (Just ?)) false)
        (? true)
    ))
)
(check-sat)
