module KernelAbstractSpec where

import Data.Word
import Data.Set

-- A very simplified model of the seL4 kernel and calls, with just enough
-- information that our SMT solvers can handle it.

type SeL4_ObjRef = Word64
type SeL4_CapRights = () -- TODO: handle rights
type SeL4_IRQ = Word64

{- | __Kernel: Capabilities__

  Capabilities to endpoint (`KCap_Endpoint`), notification (`KCap_Notification`),
  thread and CNode objects allow manipulation of these standard kernel objects.
  Reply capabilities (`KCap_Reply`) allow sending a one-off message to a thread
  that is waiting for a reply. The `KCap_IRQHandler` and `KCap_IRQControl` caps
  allow a user to configure the way interrupts on IRQs are handled: the latter
  of these is elided from this kernel specification, as acknowledging IRQs is
  handled through the former.

  Our kernel specification currently elides thread and @CNode@ caps too, as these are
  not used by @libsel4cp@ (although the initializer will use them). Domain, untyped
  and zombie caps are similarly elided.

  Eventually, frames will be represented here via @SeL4_Cap_AARCH64_Frame@.
-}
data SeL4_Cap
  = SeL4_Cap_Null
  | SeL4_Cap_Endpoint SeL4_ObjRef Word64 SeL4_CapRights
  | SeL4_Cap_Notification SeL4_ObjRef Word64 SeL4_CapRights -- obj_ref badge cap_rights
  | SeL4_Cap_Reply SeL4_ObjRef Bool SeL4_CapRights
  | SeL4_Cap_IRQHandler SeL4_IRQ
  deriving (Show, Eq, Ord)

{- | An index into a @CNode@.

  The index of the slot inside a slot-containing object.
-}
type SeL4_CPtr = Word64

{- | A single @CNode@.

-}
type SeL4_CNode = SeL4_CPtr -> SeL4_Cap

{- | __Kernel: Capability space__

  The @CSpace@ of a thread is the full range of capabilities accessible to the thread,
  which in an seL4 system can consist of one or more @CNode@s. We only model enough
  to represent threads initialized by the sel4cp initializer, which always consist of
  exactly one `SeL4_CNode`.
-}
type SeL4_CSpace = SeL4_CNode

data SeL4_MessageInfo = SeL4_MessageInfo
  { seL4_mi_length :: Word64
  , seL4_mi_extra_caps :: Word64
  , sel4_mi_caps_unwrapped :: Word64
  , seL4_mi_label :: Word16
  } deriving (Eq, Show)

{- | __Kernel: Notification States__

  In seL4, a notification can be in three different states.

  1. @SeL4_Ntfn_Idle@: The word is clear, and nobody is waiting. If a thread decides to
  wait on the notification now using a @Recv@ call, then it will go into the
  @SeL4_Ntfn_Waiting@ state, which is not modeled in this kernel specification. If
  somebody calls the notification while nobody is waiting, it will go into the
  `SeL4_Ntfn_Active` state.

  2. @SeL4_Ntfn_Waiting@: There is a queue of objects waiting for this notification
  to fire. If the notification is signalled, the first in this queue will be woken
  up, the notification word will be copied into their IPC buffer, and then cleared.

  3. `SeL4_Ntfn_Idle`: Nobody is waiting, but the notification was signalled. If
  an object decides to wait on the notification, the notification word will
  be copied into their IPC buffer, and then cleared.

  However, in this spec, we only need to model what the call will eventually copy
  into the IPC buffer of the waiting thread.

  Hence, we model `SeL4_Ntfn` as just the state of the notification word itself.
-}
type SeL4_Ntfn = Word64
-- NB this is unnecessary in the present spec
-- > data SeL4_Ntfn
-- >  = SeL4_Ntfn_Idle
-- >  | SeL4_Ntfn_Waiting [SeL4_Thread]
-- >  | SeL4_Ntfn_Active Word64

{- | __Thread Local Memory__

  An extremely simplified model of the local @VSpace@ which fully elides frames
  and access control. This should (and will) be replaced by a more sophisticated
  model, even before the full export of the abstract spec is implemented.

  This will involve implementing frame caps, @VSpace@s and mappings, and extending
  the relation so that they can account for the correspondence between capabilities
  and Core Platform abstractions.
-}
type Mem = Word64 -> Word64

{- | Thanks to concurrency and shared memory, it is not safe to read from
  memory that is mapped to multiple virtual address spaces.

  This predicate is used to mark safe memory, memory that is mapped into
  the vspace of at most one thread.
-}
mem_is_safe :: Mem -> Word64 -> Bool
mem_is_safe _ _ = True -- placeholder for `kc_local_mem_safe`

mem_is_writable :: Mem -> Word64 -> Bool
mem_is_writable _ _ = True -- placeholder for `kc_local_mem_writable`

mem_update :: Word64 -> Word64 -> Mem -> Mem
mem_update taddr value mem = \raddr -> if raddr == taddr then value else mem raddr

{- | __Kernel Heap__
  This is a placeholder (/reminder/) not to model the kernel heap. Thanks to
  concurrency, it changes in unpredictable ways from the POV of a single thread.
-}
type KHeap = SeL4_ObjRef -> Word64

data KernelContext = KC
  { kc_thread_cnode :: SeL4_CNode
  , kc_reply_obj_has_cap :: Set SeL4_Cap
  , kc_recv_oracle :: Maybe (SeL4_MessageInfo, SeL4_Ntfn) -- how can this exist without a running_pd???
                                                          -- what are you fretting about past self?
                                                          -- we only need running_pd in LC to specify because
                                                          -- our relation talks about the capabilities
                                                          -- (that is, this is just our perspective of the kernel)
  , kc_local_mem :: Mem
  , kc_local_mem_writable :: Set Word64 -- mathieu: replace with a predicate
  , kc_local_mem_safe :: Set Word64     -- mathieu: replace with a predicate
  }

type KernelWP retval = (retval -> KernelContext -> Bool) -> KernelContext -> Bool

seL4_Recv_wp :: SeL4_CPtr -> Word64 -> SeL4_CPtr -> KernelWP SeL4_MessageInfo
seL4_Recv_wp cap badge_ptr reply_cap prop kc = and
  [ kc_thread_cnode kc cap == kc_thread_cnode kc 1
  , badge_ptr `elem` kc_local_mem_writable kc
  , case kc_thread_cnode kc reply_cap of
      SeL4_Cap_Reply _ _ _  -> True -- TODO: check rights
      --SeL4_Cap_Null -> True -- TODO: no cap to reply object, is that okay?
      --
      -- mathieu: it has to be ok, because otherwise how are you suppose to
      -- call Recv the first time? (TODO: confirm that the initially the
      -- reply cap is Null. Looking at the recieve_ipc, it is indeed fine
      -- because (1) null_cap leads to no reply object. (2) no reply object
      -- is allowed on the BlockedOnReceive TCP state).
      _ -> False
  , kc_recv_oracle kc /= Nothing
  , prop rv kc'
  ] where
  (rv,badge_val) = case kc_recv_oracle kc of
    Just (mi,badge) -> (mi,badge)
    Nothing -> error "seL4_Recv_wp: precondition violation."
  new_reply_obj_has_cap = case kc_recv_oracle kc of
    Just (mi,badge) -> if badge >= 2^63
      then kc_reply_obj_has_cap kc `union` singleton (kc_thread_cnode kc reply_cap)
      else kc_reply_obj_has_cap kc \\ singleton (kc_thread_cnode kc reply_cap)
    Nothing -> error "seL4_Recv_wp: precondition violation."
  kc' = kc
    { kc_local_mem = mem_update badge_ptr badge_val (kc_local_mem kc)
    , kc_reply_obj_has_cap = new_reply_obj_has_cap
    }
    -- mathieu: the oracle should be consumed here.

seL4_ReplyRecv_wp :: SeL4_CPtr -> Word64 -> SeL4_CPtr -> KernelWP SeL4_MessageInfo
seL4_ReplyRecv_wp cap badge_ptr reply_cap prop kc = and
  [ kc_thread_cnode kc cap == kc_thread_cnode kc 1
  , badge_ptr `elem` kc_local_mem_writable kc
  , case kc_thread_cnode kc reply_cap of
      SeL4_Cap_Reply _ _ _  -> (kc_thread_cnode kc reply_cap) `elem` kc_reply_obj_has_cap kc
      _ -> False
  , kc_recv_oracle kc /= Nothing
  , prop rv kc'
  ] where
  (rv,badge_val) = case kc_recv_oracle kc of
    Just (mi,badge) -> (mi,badge)
    Nothing -> error "seL4_ReplyRecv_wp: precondition violation."
  new_reply_obj_has_cap = case kc_recv_oracle kc of
    Just (mi,badge) -> if badge >= 2^63
      then kc_reply_obj_has_cap kc `union` singleton (kc_thread_cnode kc reply_cap)
      else kc_reply_obj_has_cap kc \\ singleton (kc_thread_cnode kc reply_cap)
    Nothing -> error "seL4_ReplyRecv_wp: precondition violation."
  kc' = kc
    { kc_local_mem = mem_update badge_ptr badge_val (kc_local_mem kc)
    , kc_reply_obj_has_cap = new_reply_obj_has_cap
    }


-- mathieu: check that we have grant right
seL4_Signal_wp :: SeL4_CPtr -> KernelWP ()
seL4_Signal_wp cap prop kc = and
  [ case kc_thread_cnode kc cap of
      SeL4_Cap_Notification _ _ _ -> True
      _ -> False
  , prop () kc
  ]

seL4_IRQHandler_Ack :: SeL4_CPtr -> KernelWP ()
seL4_IRQHandler_Ack cap prop kc = and
  [ case kc_thread_cnode kc cap of
      SeL4_Cap_IRQHandler _ -> True
      _ -> False
  , prop () kc
  ]
