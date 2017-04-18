---------------------- MODULE Channel ---------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about the communication channel.                                 *)
(*  Originally contributed by Saksham Chand, SBU.                          *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  TLAPS,
  Integers,
  Sequences,
  FiniteSets,
  TLC

CONSTANTS
  RELIABLE,     \* Channel type
  FIFO,         \* Channel type
  SECURE        \* Channel type

VARIABLES
  sent,         \* Global sequence of sent messages
  received,     \* Per process, Sequence of messages received
  channel_type  \* Type of channel based on Channel Type constants
                \* defined above. Default channel_type is {}
                \* i.e., unreliable, non-FIFO and unsecure

(*********************************************)
(* Channel Actions                           *)
(*********************************************)

(* Send `msg'. Source is `from'. `to' is the set of receivers. *)
Send(from, to, msg) ==
  \E S \in Permutations({[from |-> from, to |-> t, body |-> msg] : t \in to}):
    sent' = sent \o S

(* Process `p' receives `m' from the channel *)
Receive(p, m) ==
  /\ m.to = p
  /\ received' = [received EXCEPT![p] = @ \o << m >>]

Channel_setup ==
  /\ sent = {}
  /\ received = {}
  /\ channel_type = {}  \* No config, hence empty. Should be compiler generated

(*********************************************)
(* Channel Helpers                           *)
(*********************************************)
sent_to(p) ==
  {m \in sent: p = m.to}

sent_by(p) ==
  {m \in sent: p = m.from}
  
-----------------------------------------------------------------------------
(*********************************************)
(* Channel Properties                        *)
(*********************************************)

(*
  Eventually, every sent message is received on a RELIABLE channel
*)
THEOREM Reliable_channel ==
  ASSUME NEW m \in sent, RELIABLE \in channel_type
  PROVE  <>(m \in received[m.to])
PROOF OMITTED

(*
  If two messages were sent and received from the same source to the
  same receiver on a FIFO channel, they are received in the order
  they were sent according to their timestamp.
*)
THEOREM FIFO_channel_1 ==
  ASSUME NEW m1 \in sent, NEW m2 \in sent,
         m1.from = m2.from,
         m1.to = m2.to,
         m1.timestamp < m2.timestamp,
         NEW i1 \in Nat, NEW i2 \in Nat,
         m1 = received[m1.to][i1],
         m2 = received[m2.to][i2]
  PROVE  i1 < i2
PROOF OMITTED

(*
  If two messages were sent from the same source to the same receiver
  on a FIFO channel, and the earlier message has been received,
  then, the later message cannot have been received before the
  earlier one.
*)
THEOREM FIFO_channel_2 ==
  ASSUME NEW m1 \in sent, NEW m2 \in sent,
         m1.from = m2.from,
         m1.to = m2.to,
         m1.timestamp < m2.timestamp,
         NEW i1 \in Nat,
         m1 = received[m1.to][i1]
  PROVE  ~ \E i2 \in Nat: i2 < i1 /\ m2 = received[m2.to][i2]
PROOF OMITTED

(*
  If two messages were sent from the same source to the same receiver
  on a FIFO channel, and the earlier message has not been received,
  then, the later message cannot have been received too.
*)
THEOREM FIFO_channel_3 ==
  ASSUME NEW m1 \in sent, NEW m2 \in sent,
         m1.from = m2.from,
         m1.to = m2.to,
         m1.timestamp < m2.timestamp,
         m1 \notin received[m1.to]
  PROVE  m2 \notin received[m2.to]
PROOF OMITTED

(*
  If two messages were sent from the same source to the same receiver
  on a FIFO channel, and the later message has been received,
  then, the earlier message must have been received at some point
  already.
*)
THEOREM FIFO_channel_4 ==
  ASSUME NEW m1 \in sent, NEW m2 \in sent,
         m1.from = m2.from,
         m1.to = m2.to,
         m1.timestamp < m2.timestamp,
         NEW i2 \in Nat,
         m2 = received[m2.to][i2]
  PROVE  \E i1 \in Nat: i1 < i2 /\ m1 = received[m1.to][i1]
PROOF OMITTED
=============================================================================