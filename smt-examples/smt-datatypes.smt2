(set-logic ALL)

; ; (declare-datatypes ( (Color 0) ) ( ( (red) (green) (blue) ) ) )

(declare-datatype Color ( (red) (green) (blue) ))

; (declare-datatype IntList ( (IntNil) (IntInsert (head Int) (tail IntList)) ))

; (declare-datatype List (par (A) ( (nil) (cons (head A) (tail (List A))))  ))

(declare-datatype Option (par (A) ( (nothing ) (just (x A)))))

(declare-datatype Prod (par (X Y) ((prod (fst X) (snd Y)))))

; (define-fun a () Color red)

(declare-fun oi () (Option Int))

; (assert (= oi nothing))

(assert (or (= oi (just 2)) ((_ is nothing) oi)))
(assert ((_ is nothing) (just 2)))

(define-fun c () Color red)
(assert ((_ is red) c))
(check-sat)

; data SeL4_Cap
;   = SeL4_Cap_Null
;   | SeL4_Cap_Endpoint SeL4_ObjRef Word64 SeL4_CapRights
;   | SeL4_Cap_Notification SeL4_ObjRef Word64 SeL4_CapRights -- obj_ref badge cap_rights
;   | SeL4_Cap_Reply SeL4_ObjRef Bool SeL4_CapRights
;   | SeL4_Cap_IRQHandler SeL4_IRQ

(define-sort seL4_ObjRef () (_ BitVec 64))
(define-sort seL4_IRQ () (_ BitVec 64))
(define-sort seL4_CPtr () (_ BitVec 64))
(define-sort seL4_Ntfn () (_ BitVec 64))

(declare-sort seL4_CapRights 0) ; TODO



(declare-datatype seL4_Cap (
    (seL4_Cap_Null)
    (seL4_Cap_Endpoint (ep_objref seL4_ObjRef) (ep_badge (_ BitVec 64)) (ep_cap_rights seL4_CapRights))
    (seL4_Cap_Notification (ntf_objref seL4_ObjRef) (ntf_badge (_ BitVec 64)) (ntf_cap_rights seL4_CapRights))
    (seL4_Cap_Reply (rep_objref seL4_ObjRef) (rep_what Bool) (rep_cap_rights seL4_CapRights))
    (seL4_Cap_IRQHandler (irq seL4_IRQ))
))

; hacky way of defining
;
;    type SeL4_CNode = SeL4_CPtr -> SeL4_Cap
;
; inside a KernelContext (required because we don't have first-order
; functions)
;
; Maybe use arrays?
(define-sort seL4_CNode_Idx () Int)
(declare-fun seL4_CNode (seL4_CNode_Idx seL4_CPtr) seL4_Cap)

(declare-datatype seL4_MessageInfo ((seL4_MessageInfo
    (seL4_mi_length (_ BitVec 64))
    (seL4_mi_extra_caps (_ BitVec 64))
    (sel4_mi_caps_unwrapped (_ BitVec 64))
    (seL4_mi_label (_ BitVec 64))
)))

(declare-datatype KernelContext ((KC
    (kc_thread_cnode seL4_CNode_Idx)
    (kc_reply_obj_has_cap seL4_Cap))
    (kc_recv_oracle (Maybe (Prod seL4_MessageInfo seL4_Ntfn)))



    ; TODO: mem
))

