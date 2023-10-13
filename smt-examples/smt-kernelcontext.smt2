(set-logic ALL)
(declare-datatype Maybe (par (X) ((Just (just X)) (Nothing))))
(declare-datatype Prod (par (X Y) ((Prod (fst X) (snd Y)))))

(define-sort Word64 () (_ BitVec 64))

(define-sort SeL4_ObjRef () Word64)
(define-sort SeL4_IRQ () Word64)
(define-sort SeL4_CPtr () Word64)
(define-sort SeL4_Ntfn () Word64)

; (declare-sort SeL4_CapRights 0) ; TODO

(declare-datatype SeL4_CapRights (
    (CapRights
        (capAllowWrite Bool)
        (capAllowRead Bool)
        (capAllowGrant Bool)
        (capAllowGrantReply Bool)
    )
))

; data SeL4_Cap
;   = SeL4_Cap_Null
;   | SeL4_Cap_Endpoint SeL4_ObjRef Word64 SeL4_CapRights
;   | SeL4_Cap_Notification SeL4_ObjRef Word64 SeL4_CapRights -- obj_ref badge cap_rights
;   | SeL4_Cap_Reply SeL4_ObjRef Bool SeL4_CapRights
;   | SeL4_Cap_IRQHandler SeL4_IRQ
(declare-datatype SeL4_Cap (
    (SeL4_Cap_Null)
    (SeL4_Cap_Endpoint (ep_objref SeL4_ObjRef) (ep_badge Word64) (ep_cap_rights SeL4_CapRights))
    (SeL4_Cap_Notification (ntf_objref SeL4_ObjRef) (ntf_badge Word64) (ntf_cap_rights SeL4_CapRights))
    (SeL4_Cap_Reply (rep_objref SeL4_ObjRef) (rep_what Bool) (rep_cap_rights SeL4_CapRights))
    (SeL4_Cap_IRQHandler (irq SeL4_IRQ))
))

(declare-datatype SeL4_MessageInfo ((SeL4_MessageInfo
    (SeL4_mi_length Word64)
    (SeL4_mi_extra_caps Word64)
    (Sel4_mi_caps_unwrapped Word64)
    (SeL4_mi_label Word64)
)))


; data KernelContext = KC
;   { kc_thread_cnode :: SeL4_CNode
;   , kc_reply_obj_has_cap :: Set SeL4_Cap
;   , kc_recv_oracle :: Maybe (SeL4_MessageInfo, SeL4_Ntfn)
;   , kc_local_mem :: Mem
;   , kc_local_mem_writable :: Set Word64
;   , kc_local_mem_safe :: Set Word64
;   }
(declare-datatype KernelContext (
    (KC
        (kc_thread_cnode (Array SeL4_CPtr SeL4_Cap))
        (kc_reply_obj_has_cap (Array SeL4_Cap Bool))
        (kc_recv_oracle (Maybe (Prod SeL4_MessageInfo SeL4_Ntfn)))
        (kc_local_mem (Array Word64 Word64))
        (kc_local_mem_writable (Array Word64 Bool))
        (kc_local_mem_safe (Array Word64 Bool))
    )
))

; (Ignore for now)
; there are some things we know about our kernel context
; that is, there are some things we know about _all_ core platform systems

; encode SeL4_ReplyRecv pre and post condition

(define-fun SeL4_ReplyRecv_pre ((kc KernelContext) (cap SeL4_CPtr) (reply_cap SeL4_CPtr) (badge_ptr Word64)) Bool (and

    ; TODO: check rights on the cap (this information will come from the initialisation)
    ;       ie. We need the read right
    (= (select (kc_thread_cnode kc) cap) (select (kc_thread_cnode kc) (_ bv1 64)))

    (select (kc_local_mem_writable kc) badge_ptr)

    (let ((case!sub (select (kc_thread_cnode kc) reply_cap)))
        ; Trying to Send or Call without the Write right will fail and return an error.
        ; -- seL4 manual
        (ite ((_ is SeL4_Cap_Reply) case!sub) true  ; TODO: check rights
         (ite ((_ is SeL4_Cap_Null) case!sub) true  ; is that ok?
          false))
    )

    (not ((_ is Nothing) (kc_recv_oracle kc)))
))

(define-fun top_most_bit () Word64 (bvshl (_ bv1 64) (_ bv63 64)))

(define-fun SeL4_ReplyRecv_post ((kc KernelContext) (cap SeL4_CPtr) (reply_cap SeL4_CPtr) (badge_ptr Word64) (kc+ KernelContext) (ret SeL4_MessageInfo)) Bool (and
    (let ((recv_oracle! (kc_recv_oracle kc)))
        (and ((_ is Just) recv_oracle!)
            (let ((rv! (fst (just recv_oracle!)))
                  (badge_val! (snd (just recv_oracle!))))

                ; don't know if SMT has an update syntax, so for now we do
                ; this manually
                (= kc+
                    (KC (kc_thread_cnode kc)
                        ; we obtain a reply cap
                        (store (kc_reply_obj_has_cap kc) (select (kc_thread_cnode kc) reply_cap) (bvuge badge_val! top_most_bit))
                        ; we consume the oracle (forgotten in the haskell spec)
                        Nothing
                        ; the badge is written
                        (store (kc_local_mem kc) badge_ptr badge_val!)
                        (kc_local_mem_writable kc)
                        (kc_local_mem_safe kc))
                )
            )
        )
    )
))



(assert (let ((x 1)) (= x 1)))
(check-sat)
