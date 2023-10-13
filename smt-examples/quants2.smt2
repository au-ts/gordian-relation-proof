; using a map of 2 bits => mmr seems to work?
; but using 1 bit doesn't work weirdly.

(set-logic ALL)

(define-sort Word64 () (_ BitVec 64))
(define-sort Word8 () (_ BitVec 2))

(declare-sort _MMR 2)
(declare-fun mmr_addr ((_MMR Word64 Word64)) Word64)
(declare-fun mmr_size ((_MMR Word64 Word64)) Word64)
(define-sort MMR () (_MMR Word64 Word64))

(declare-fun all_mmrs () (Array Word8 MMR))
(declare-fun ms_writable_addrs () (Array Word64 Bool))

(define-fun mmr_contains ((addr Word64) (mmr MMR)) Bool (and
    (bvuge addr (mmr_addr mmr))
    (bvule addr (bvadd (mmr_addr mmr) (mmr_size mmr)))
))

(define-fun is_writable_addr ((addr Word64)) Bool
    (exists ((mmri Word8)) (and
        (mmr_contains addr (select all_mmrs mmri))
    ))
)

(assert (forall ((addr Word64)) (=
    (select ms_writable_addrs addr)
    (is_writable_addr addr)
)))
(check-sat)

(push)
    (declare-const myaddr Word64)
    (assert (select ms_writable_addrs myaddr))
    (check-sat)
    (get-model)
    (get-info :reason-unknown)
(pop)

