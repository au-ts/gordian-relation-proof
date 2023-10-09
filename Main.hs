{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use &&" #-}
module Main (main) where

import Data.Bits
import Data.Word

import Data.Set (Set)
import Data.Set as S

import Preliminaries
import KernelAbstractSpec
import CoreAbstractSpec


relation_pd_obj_ref :: PD -> SeL4_ObjRef -> Bool
relation_pd_obj_ref pd obj_ref = True -- TODO: final implementation

relation_msginfo :: MsgInfo -> SeL4_MessageInfo -> Bool
relation_msginfo (MI x y) (SeL4_MessageInfo a b c d) = a == x && d == y

{- | Holds if the given `SeL4_Cap` is the `SeL4_Cap_Notification` corresponding to
  the @CNode@ of the given `CoreAbstractSpec.PD` according to the SDF-capabilities
  mapping specification, i.e. if the given `SeL4_Cap` is the one the initializer
  minted to serve as the input cap of the given `PD`.
-}
relation_pd_input_cap :: PD -> SeL4_Cap -> Bool
relation_pd_input_cap pd cap = case cap of
  SeL4_Cap_Notification obj_ref _ _ -> relation_pd_obj_ref pd obj_ref
  _ -> False

relation_pdch_notification_cap :: PDCh -> SeL4_Cap -> Bool
relation_pdch_notification_cap (pd,ch) cap = case cap of
  SeL4_Cap_Notification obj_ref badge _ -> and
    [ relation_pd_obj_ref pd obj_ref 
    , badge == 2^(indexOf ch)
    ]
  _ -> False

relation_pdch_endpoint_cap :: PDCh -> SeL4_Cap -> Bool
relation_pdch_endpoint_cap (pd,ch) cap = case cap of
  SeL4_Cap_Endpoint obj_ref badge _ -> and
    [ relation_pd_obj_ref pd obj_ref
    , badge == undefined -- TODO: correct badging according to final mapping spec!
    ]
  _ -> False

relation_is_irq_cap :: SeL4_Cap -> Bool
relation_is_irq_cap (SeL4_Cap_IRQHandler _) = True
relation_is_irq_cap _ = False

{- | __Local Capability Mapping Relation__

  This relation between the given `PlatformInvariants` and `KernelContext` holds
  if the capabilities implied by the SDF document describing the `PlatformInvariants`
  have been distributed correctly to the `KernelContext` of the thread executing
  the given `PD, as set forth in the SDF-capabilities mapping specification.

  In the SMT-based correctness proof we /assume/ that every kernel call preserves
  this relation: in the Isabelle initializer proofs, we are obliged to /prove/ that
  no call, made by /any/ user thread, in a system that obeys the capability distribution
  of an SDF file can put the system in a state that does not obey the capability
  distribution.
-}
relation_cap_map :: PlatformInvariants -> PD -> KernelContext -> Bool
relation_cap_map ci pd kc = and
  [ relation_pd_input_cap pd (kc_thread_cnode kc 1)
  , forall (ci_valid_comms ci) $ \((pd',ch),target) ->
    pd /= pd' || relation_pdch_notification_cap target (kc_thread_cnode kc (10 + indexOf ch))
  , forall (ci_valid_comms ci) $ \((pd',ch),target) -> or
    [ pd /= pd'
    , not (fst target `elem` ci_provides_pp ci)
    , ci_prio ci pd >= ci_prio ci (fst target)
    , relation_pdch_endpoint_cap target (kc_thread_cnode kc (74 + indexOf ch))
    ]
  , forall (ci_valid_irqns ci) $ \(pd',ch) ->
    pd /= pd' || relation_is_irq_cap (kc_thread_cnode kc (138 + indexOf ch))
  ]

{- | __Oracle Compatibility Relation__

  Holds if the contents of the receive oracles are compatible.
-}
relation_receive_oracle :: NextRecv -> Maybe (SeL4_MessageInfo, SeL4_Ntfn) -> Bool
relation_receive_oracle NR_Unknown Nothing = True
relation_receive_oracle (NR_Notification chs) (Just (_, knr_badge)) =
  knr_badge == sum (S.map (\ch -> 2^(indexOf ch)) chs)
relation_receive_oracle (NR_PPCall (ch,mi)) (Just (mi', knr_badge)) = -- undefined -- TODO: define this
  -- mathieu
  and [relation_msginfo mi mi'
      , knr_badge == 2^63 + indexOf ch
      ]
relation_receive_oracle _ _ = False

{- | __Memory Concurrency Safety Relation__

  Holds if memory marked concurrency-safe on the kernel side is not mapped into
  writable shared memory in any other protection domain. Only safe memory can
  be guaranteed not to change unexpectedly during execution.
-}
relation_mmrs_mem :: PlatformInvariants -> KernelContext -> Bool
relation_mmrs_mem ci kc = and
  [ forall (kc_local_mem_safe kc) $ \addr ->
    forall (ci_mmrs ci) $ \mmr ->
    not (mmr_perm_write mmr) || relation_pd_input_cap (mmr_pd mmr) (kc_thread_cnode kc 1)
    -- TODO: additional clauses for writability
  ]

{- | __Unhandled Reply relation__

  There is a dangling reply precisely if the reply object whose capability resides in
  the thread's @CNode@ holds a cap.
-}
relation_reply_cap :: PlatformContext -> KernelContext -> Bool
relation_reply_cap lc kc = case lc_unhandled_reply lc of
  Just _ -> case kc_thread_cnode kc 4 of
    x@(SeL4_Cap_Reply _ _ _) -> x `elem` kc_reply_obj_has_cap kc
    _                  -> False
  Nothing -> kc_thread_cnode kc 4 == SeL4_Cap_Null

{- | __Implementation Correctness Specification__

  The implementation relation between a `PlatformContext` and `KernelContext`.

  Each `PD` is modelled as a state transition system. The implementation relation
  relates each state of this Core Platform state machine to those kernel states
  that are compatible with it (i.e. that correctly implement the given state).

  Proving implementation correctness of libsel4cp involves showing that for every
  user-facing function @f@ provided by libsel4cp, if @f@ transforms the platform
  state @x@ into the platform state @y@, then the C implementation of @f@ transforms
  every kernel state @kX@ implementing @X@ into some kernel state @kY@ implementing @Y@.
-}
relation :: PlatformContext -> KernelContext -> Bool
relation lc kc = and
  [ relation_cap_map (ci lc) (lc_running_pd lc) kc
  , relation_mmrs_mem (ci lc) kc
  , relation_reply_cap lc kc
  , relation_receive_oracle (lc_receive_oracle lc) (kc_recv_oracle kc)
  ]

{- | __Handler Loop Specification: Iteration Precondition__

  When a handler loop iteration begins, the platform state should have no
  unhandled notifications and no unhandled protected procedure calls.

  There might be an unhandled reply, which is equal to the variable
  @lc_unhandled_reply_pre@.

  The receive oracle is initialized to be available.
-}
handler_loop_iter_pre :: Maybe MsgInfo -> NextRecv -> PlatformContext -> Bool
handler_loop_iter_pre lc_unhandled_reply_pre lc_receive_oracle_pre lc = and
  [ lc_unhandled_reply lc == lc_unhandled_reply_pre
  , lc_unhandled_notified lc == S.empty
  , lc_unhandled_ppcall lc == Nothing
  , lc_receive_oracle lc /= NR_Unknown
  , lc_receive_oracle lc /= NR_Notification S.empty
  , lc_receive_oracle lc == lc_receive_oracle_pre
  ]

{- | __Handler Loop Specification: Postcondition__

  When a handler loop iteration ends, the ghost state should have no
  unhandled notifications and no unhandled protected procedure calls.

  If the platform state at the start of the iteration had an unhandled reply,
  that reply should now be the last handled reply.

  The receive oracle should be consumed and unavailable (i.e. a receiving
  call must have been made inside the handler loop).
-}
handler_loop_iter_post :: Maybe MsgInfo -> NextRecv -> PlatformContext -> Bool
handler_loop_iter_post lc_unhandled_reply_pre lc_receive_oracle_pre lc = and
  [ lc_last_handled_reply lc == lc_unhandled_reply_pre
  , lc_unhandled_notified lc == S.empty
  , lc_unhandled_ppcall lc == Nothing
  , lc_receive_oracle lc == NR_Unknown
  , case lc_receive_oracle_pre of
      NR_Notification notis -> lc_last_handled_notified lc == notis
      _ -> True
  ]

main :: IO ()
main = return ()

