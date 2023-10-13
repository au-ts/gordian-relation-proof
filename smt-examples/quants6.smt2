; https://cvc5.github.io/docs/cvc5-1.0.2/theories/sets-and-relations.html

(set-logic ALL)

(set-option :produce-models true)
(set-option :incremental true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; we need sets extension to support set.universe operator
(set-option :sets-ext true)


(define-sort Word64 () (_ BitVec 64))
(declare-sort _MMR 2)
(declare-fun mmr_addr ((_MMR Word64 Word64)) Word64)
(declare-fun mmr_size ((_MMR Word64 Word64)) Word64)
(define-sort MMR () (_MMR Word64 Word64))

(declare-fun all_mmrs () (Set MMR))
(declare-fun ms_writable_addrs () (Set Word64))

(define-fun mmr_contains ((addr Word64) (mmr MMR)) Bool (and
    (bvuge addr (mmr_addr mmr))
    (bvule addr (bvadd (mmr_addr mmr) (mmr_size mmr)))
))

(define-fun is_writable_addr ((addr Word64)) Bool
    (exists ((mmr MMR)) (and
        (set.member mmr all_mmrs)
        (mmr_contains addr mmr)
    ))
)

(check-sat)
(declare-const addr Word64)
(assert (is_writable_addr addr))
(check-sat)



(assert (= ms_writable_addrs is_writable_addr))

(get-model)
(assert (forall ((addr Word64)) (=
    (set.member addr ms_writable_addrs)
    (is_writable_addr addr)
)))
(check-sat)

(push)
    (declare-const myaddr Word64)
    (assert (set.member myaddr ms_writable_addrs))
    (check-sat)
    (get-info :reason-unknown)
(pop)

