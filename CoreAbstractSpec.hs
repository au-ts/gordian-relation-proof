module CoreAbstractSpec where

import Data.Bits
import Data.Word
import Data.Set (Set)
import Data.Set as S

import Preliminaries

-- abstract protection domain ids
data PD
  = PD00 | PD01 | PD02 | PD03 | PD04 | PD05 | PD06 | PD07 | PD08 | PD09
  | PD10 | PD11 | PD12 | PD13 | PD14 | PD15 | PD16 | PD17 | PD18 | PD19
  | PD20 | PD21 | PD22 | PD23 | PD24 | PD25 | PD26 | PD27 | PD28 | PD29
  | PD30 | PD31 | PD32 | PD33 | PD34 | PD35 | PD36 | PD37 | PD38 | PD39
  | PD40 | PD41 | PD42 | PD43 | PD44 | PD45 | PD46 | PD47 | PD48 | PD49
  | PD50 | PD51 | PD52 | PD53 | PD54 | PD55 | PD56 | PD57 | PD58 | PD59
  | PD60 | PD61 | PD62
  deriving (Show, Eq, Ord)

possible_pds :: [PD]
possible_pds =
   [ PD00, PD01, PD02, PD03, PD04, PD05, PD06, PD07, PD08, PD09
   , PD10, PD11, PD12, PD13, PD14, PD15, PD16, PD17, PD18, PD19
   , PD20, PD21, PD22, PD23, PD24, PD25, PD26, PD27, PD28, PD29
   , PD30, PD31, PD32, PD33, PD34, PD35, PD36, PD37, PD38, PD39
   , PD40, PD41, PD42, PD43, PD44, PD45, PD46, PD47, PD48, PD49
   , PD50, PD51, PD52, PD53, PD54, PD55, PD56, PD57, PD58, PD59
   , PD60, PD61, PD62
   ]

instance Finite PD where
  inhabitants = possible_pds

-- abstract channel ids
data Ch
  = Ch00 | Ch01 | Ch02 | Ch03 | Ch04 | Ch05 | Ch06 | Ch07 | Ch08 | Ch09
  | Ch10 | Ch11 | Ch12 | Ch13 | Ch14 | Ch15 | Ch16 | Ch17 | Ch18 | Ch19
  | Ch20 | Ch21 | Ch22 | Ch23 | Ch24 | Ch25 | Ch26 | Ch27 | Ch28 | Ch29
  | Ch30 | Ch31 | Ch32 | Ch33 | Ch34 | Ch35 | Ch36 | Ch37 | Ch38 | Ch39
  | Ch40 | Ch41 | Ch42 | Ch43 | Ch44 | Ch45 | Ch46 | Ch47 | Ch48 | Ch49
  | Ch50 | Ch51 | Ch52 | Ch53 | Ch54 | Ch55 | Ch56 | Ch57 | Ch58 | Ch59
  | Ch60 | Ch61 | Ch62
  deriving (Show, Eq, Ord)

possible_chs :: [Ch]
possible_chs =
   [ Ch00, Ch01, Ch02, Ch03, Ch04, Ch05, Ch06, Ch07, Ch08, Ch09
   , Ch10, Ch11, Ch12, Ch13, Ch14, Ch15, Ch16, Ch17, Ch18, Ch19
   , Ch20, Ch21, Ch22, Ch23, Ch24, Ch25, Ch26, Ch27, Ch28, Ch29
   , Ch30, Ch31, Ch32, Ch33, Ch34, Ch35, Ch36, Ch37, Ch38, Ch39
   , Ch40, Ch41, Ch42, Ch43, Ch44, Ch45, Ch46, Ch47, Ch48, Ch49
   , Ch50, Ch51, Ch52, Ch53, Ch54, Ch55, Ch56, Ch57, Ch58, Ch59
   , Ch60, Ch61, Ch62
   ]

instance Finite Ch where
  inhabitants = possible_chs

type PDCh = (PD, Ch)
type Comm = (PDCh, PDCh)

{- | Scheduling Priorities

  Note: technically, priority 255 should be disallowed in the spec.
-}
type Prio = Word8


{- | A Mapped Memory Range (for a memory region)

  Mapped memory ranges are always associated with the `PD` they
  are mapped into, given by `mmr_pd`. They satisfy the invariants
  set forth in `wf_MMR`:

  1. They are not outside the bounds of the address space.

  2. The address and size are both page-aligned.
-}
data MMR = MMR
  { mmr_pd :: PD
  , mmr_addr :: Word64
  , mmr_size :: Word64
  , mmr_perm_write :: Bool
  , mmr_perm_execute :: Bool
  }

instance Finite MMR where
  inhabitants = undefined -- FIXME: we probably shouldn't quantify over MMRs in QF_ABV

wf_MMR :: MMR -> Bool
wf_MMR r = and
  [ mmr_addr r + mmr_size r > mmr_addr r
  , (mmr_size r .&. 4096) == 0
  , (mmr_addr r .&. 4096) == 0
  ]

contains :: MMR -> Word64 -> Bool
contains r addr = and
  [ addr >= mmr_addr r
  , mmr_addr r + mmr_size r > addr
  ]

{- | A message structure.

  Note: the size of this is usually architecture-dependent.
-}
data MsgInfo = MI
  { mi_label :: Word64
  , mi_count :: Word16
  } deriving (Eq, Show)

wf_MsgInfo :: MsgInfo -> Bool
wf_MsgInfo mi = and
  [ mi_label mi <= 0xffffffffffff
  , mi_count mi <= 127
  ]

{- | __The Core Platform Invariants__

  The /platform invariants/ of an sel4cp system arise from the protection
  domains, communication channels, interrupts and protected procedure
  call permissions defined in the SDF document that the sel4cp tool takes
  as its input to produce the appropriate system image which will be loaded
  onto the target board.

  The specification assumes that the core invariants hold for the currently
  executing protection domain, and /does not/ prove their preservation. Instead,
  preservation of core invariants will eventually be proved as part of the system
  initializer proofs, by showing that for all SDF inputs, the initializer starts
  up the system in a capability distribution satisfying the core invariants specified
  in the SDF input, and that every kernel call available in that distribution also
  results in a capability distribution that satisfies the core invariants.

  The Haskell specification represents these core invariants using the `PlatformInvariants`
  data type, which defines the same data as an SDF file, but abstracts away the names
  of the protection domains, and represents everything as finite sets, which facilitates
  correct implementation of our SMT-based prover, by being straightforwardly representable
  using common weak theories such as @QF_ABV@.
-}
data PlatformInvariants = CI
  { ci_valid_pds :: Set PD
  , ci_valid_pdchs :: Set PDCh
  , ci_valid_comms :: Set Comm
  , ci_valid_irqns :: Set PDCh
  , ci_prio :: PD -> Maybe Prio
  , ci_mmrs :: Set MMR
  , ci_provides_pp :: Set PD
  }



{- | Well-formedness of `PlatformInvariants`.

  We require core invariants to be well-formed. This means that the following
  conditions must hold about every inhabitant of `PlatformInvariants` that we construct:

  1. The protection domain of every valid `PDCh` is a valid `PD`.

  2. The ends of every valid communication channel (`Comm`) are valid `PDCh`s.

  3. Ends of communication channels are symmetric.

  4. Every `PDCh` has no more than one other end.

  5. Every IRQ notification channel is a valid `PDCh`.

  6. Every valid protection domain has a priority.

  7. Every mapped Virtual Address Range is well-formed and has a valid protection domain.
-}
wf_PlatformInvariants :: PlatformInvariants -> Bool
wf_PlatformInvariants ci = and
  [ wf_PlatformInvariants_1 ci
  , wf_PlatformInvariants_2 ci
  , wf_PlatformInvariants_3 ci
  , wf_PlatformInvariants_4 ci
  , wf_PlatformInvariants_5 ci
  , wf_PlatformInvariants_6 ci
  , wf_PlatformInvariants_7 ci
  ]

wf_PlatformInvariants_1 :: PlatformInvariants -> Bool
wf_PlatformInvariants_1 ci =
  forall (ci_valid_pdchs ci) $ \(pd,_) ->
  pd `elem` ci_valid_pds ci

wf_PlatformInvariants_2 :: PlatformInvariants -> Bool
wf_PlatformInvariants_2 ci =
  forall (ci_valid_comms ci) $ \(pc1,pc2) ->
  pc1 `elem` ci_valid_pdchs ci && pc2 `elem` ci_valid_pdchs ci

wf_PlatformInvariants_3 :: PlatformInvariants -> Bool
wf_PlatformInvariants_3 ci =
  forall (ci_valid_comms ci) $ \(pc1,pc2) ->
  (pc2,pc1) `elem` ci_valid_comms ci

wf_PlatformInvariants_4 :: PlatformInvariants -> Bool
wf_PlatformInvariants_4 ci =
  forall (ci_valid_comms ci) $ \(pc1,pc2) ->
  forall (ci_valid_comms ci) $ \(pc3,pc4) ->
  pc1 /= pc3 || pc2 == pc4

wf_PlatformInvariants_5 :: PlatformInvariants -> Bool
wf_PlatformInvariants_5 ci =
  forall (ci_valid_irqns ci) $ \pc ->
  pc `elem` ci_valid_pdchs ci

wf_PlatformInvariants_6 :: PlatformInvariants -> Bool
wf_PlatformInvariants_6 ci =
  forall (ci_valid_pds ci) $ \pd ->
  ci_prio ci pd /= Nothing

wf_PlatformInvariants_7 :: PlatformInvariants -> Bool
wf_PlatformInvariants_7 ci =
  forall (ci_mmrs ci) $ \r ->
  mmr_pd r `elem` ci_valid_pds ci && wf_MMR r



{- | Represents the relevant external state of a Core Platform system:
  what will be returned when the currently executing thread next invokes
  a Recv or ReplyRecv call on the input capability in its CNode.

  These could be:

  1. `NR_Notification`: a notification will be returned, with a set of channels ids to
     be notified.

  2. `NR_PPCall`: information describing a protected procedure call will be returned,
     with a channel id and a message information argument.

  3. `NR_Unknown`: it is not known what will be returned, so we pledge not to make a
     kernel call using the input capability until the local context changes.
-}
data NextRecv
  = NR_Notification (Set Ch)
  | NR_PPCall (Ch, MsgInfo)
  | NR_Unknown
  deriving (Eq, Show)

{- | __The Local Context__

  The local context holds all relevant information about the currently executing
  system thread. This includes:

  1. the core invariants `ci`,

  2. local invariants such as `lc_running_pd`, the currently running `PD`.

  3. the ghost state of the specification (`lc_receive_oracle`, `lc_unhandled_notified`, `lc_unhandled_ppcall`),

  4. the genuine state of the specification (including memory of the executing thread).
-}
data PlatformContext = LC
  { ci :: PlatformInvariants
  , lc_running_pd :: PD
  , lc_receive_oracle :: NextRecv
  , lc_unhandled_notified :: Set Ch
  , lc_last_handled_notified :: Set Ch
  , lc_unhandled_ppcall :: Maybe (Ch, MsgInfo)
  , lc_unhandled_reply :: Maybe MsgInfo
  , lc_last_handled_reply :: Maybe MsgInfo
  }


{- | The type of weakest preconditions.

   The @rv@ variable is used to keep track of conditions on the return value.
   Setting the `Maybe` to `Nothing` indicates that no information about the
   return value will be available (i.e. it will be fresh).
-}
type WP rv = (Maybe rv -> PlatformContext -> Bool) -> PlatformContext -> Bool

-- mathieu: technically, you have to prove that the relation is maintained
-- when calling notified as well.

notified_wp :: Ch -> WP ()
notified_wp ch prop lc = and
  [ ch `elem` lc_unhandled_notified lc
  , prop (Just ()) lc'
  ] where
  lc' = lc
    { lc_unhandled_notified = lc_unhandled_notified lc \\ S.singleton ch
    , lc_last_handled_notified = lc_last_handled_notified lc `union` S.singleton ch
    }

protected_wp :: Ch -> MsgInfo -> WP MsgInfo
protected_wp ch mi prop lc = and
  [ lc_unhandled_ppcall lc == Just (ch,mi)
  , wf_MsgInfo mi
  , prop rv lc'
  ] where
  rv = fresh_variable
  lc' = lc
    { lc_unhandled_ppcall = Nothing
    }

sel4cp_notify_wp :: Ch -> WP ()
sel4cp_notify_wp ch prop lc = let ci' = ci lc in and
  [ exists (ci_valid_comms ci') $ \(pc1,_) -> pc1 == (lc_running_pd lc, ch)
  , prop (Just ()) lc
  ]

sel4cp_irq_ack_wp :: Ch -> WP ()
sel4cp_irq_ack_wp ch prop lc = let ci' = ci lc in and
  [ (lc_running_pd lc, ch) `elem` ci_valid_irqns ci'
  , prop (Just ()) lc
  ]

sel4cp_ppcall_wp :: Ch -> MsgInfo -> WP MsgInfo
sel4cp_ppcall_wp ch mi prop lc = let ci' = ci lc in and
  [ exists (ci_valid_comms ci') $ \(pc1,pc2) -> and
      [ fst pc1 == lc_running_pd lc
      , snd pc1 == ch
      , (fst pc2) `elem` ci_provides_pp ci'
      , ci_prio ci' (fst pc2) > ci_prio ci' (fst pc1)
      ]
  , wf_MsgInfo mi
  , prop rv lc
  ] where
  rv = fresh_variable

sel4cp_msginfo_new_wp :: Word64 -> Word16 -> WP MsgInfo
sel4cp_msginfo_new_wp label count prop lc = or
  [ not (wf_MsgInfo $ MI label count)
  , prop (Just $ MI label count) lc
  ]

sel4cp_correspondence_recv_wp :: WP MsgInfo
sel4cp_correspondence_recv_wp prop lc = and
  [ lc_receive_oracle lc /= NR_Unknown
  , lc_receive_oracle lc /= NR_Notification S.empty
  , lc_unhandled_notified lc == S.empty
  , lc_unhandled_ppcall lc == Nothing
  , lc_unhandled_reply lc == Nothing
  , wf_MsgInfo rv
  , prop (Just rv) lc'
  ] where
  rv = case lc_receive_oracle lc of
    NR_Notification notis -> MI 0 0
    NR_PPCall (_, mi) -> mi
    _ -> error "sel4cp_correspondence_recv_wp: Precondition violation in rv."
  lc' = case lc_receive_oracle lc of
    NR_Notification notis -> lc
      { lc_receive_oracle = NR_Unknown
      , lc_unhandled_notified = notis
      }
    NR_PPCall ppc -> lc
      { lc_receive_oracle = NR_Unknown
      , lc_unhandled_ppcall = Just ppc
      }
    _ -> error "sel4cp_correspondence_recv_wp: Precondition violation."

sel4cp_correspondence_replyrecv_wp :: MsgInfo -> WP MsgInfo
sel4cp_correspondence_replyrecv_wp reply_tag prop lc = and
  [ lc_receive_oracle lc /= NR_Unknown
  , lc_receive_oracle lc /= NR_Notification S.empty
  , wf_MsgInfo reply_tag
  , lc_unhandled_notified lc == S.empty
  , lc_unhandled_ppcall lc == Nothing
  , lc_unhandled_reply lc /= Nothing
  , wf_MsgInfo rv
  , prop (Just rv) lc'
  ] where
  rv = case lc_receive_oracle lc of
    NR_Notification notis -> MI 0 0
    NR_PPCall (_, mi) -> mi
    _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation in rv."
  lc' = case lc_receive_oracle lc of
    NR_Notification notis -> lc
      { lc_receive_oracle = NR_Unknown
      , lc_unhandled_notified = notis
      , lc_unhandled_reply = Nothing
      , lc_last_handled_reply = lc_unhandled_reply lc
      }
    NR_PPCall ppc -> lc
      { lc_receive_oracle = NR_Unknown
      , lc_unhandled_ppcall = Just ppc
      , lc_unhandled_reply = Nothing
      , lc_last_handled_reply = lc_unhandled_reply lc
      }
    _ -> error "sel4cp_correspondence_replyrecv_wp: Precondition violation."


