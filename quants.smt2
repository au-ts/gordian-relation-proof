(set-logic ALL)

(define-sort Word64 () (_ BitVec 64))
(declare-sort _MMR 2)
(declare-fun mmr_addr ((_MMR Word64 Word64)) Word64)
(declare-fun mmr_size ((_MMR Word64 Word64)) Word64)
(define-sort MMR () (_MMR Word64 Word64))

(declare-fun all_mmrs () (Array MMR Bool))
(declare-fun ms_writable_addrs () (Array Word64 Bool))

(define-fun mmr_contains ((addr Word64) (mmr MMR)) Bool (and
    (bvuge addr (mmr_addr mmr))
    (bvule addr (bvadd (mmr_addr mmr) (mmr_size mmr)))
))

(define-fun is_writable_addr ((addr Word64)) Bool
    (exists ((mmr MMR)) (and
        (select all_mmrs mmr)
        (mmr_contains addr mmr)
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
    (get-info :reason-unknown)
(pop)

