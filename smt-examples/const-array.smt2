(declare-const arr (Array Int Bool))

(assert (= arr ((as const (Array Int Bool)) false)))
