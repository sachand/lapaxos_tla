---------------------- MODULE Aggregates ------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about aggregate functions.                                       *)
(*  Originally contributed by Saksham Chand, SBU.                          *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  TLAPS,
  Integers

CONSTANTS Undefined

ASSUME Undefined_Arithmetic_Properties ==
  \A S: \A e \in S: e \geq Undefined

(***************************************************************************)
(* Maximum of a set S is the element greater or equal than every element   *)
(* of S or Undefined if S is empty                                         *)
(***************************************************************************)
max(S) ==
  CHOOSE s \in S \cup {Undefined}: \A t \in S : s \geq t

-----------------------------------------------------------------------------
(***************************************************************************)
(* Maximum of a set is Undefined iff the set is a subset of {Undefined}    *)
(***************************************************************************)
THEOREM MaxUndefined ==
  ASSUME NEW S
  PROVE  max(S) = Undefined <=> S \in SUBSET {Undefined}
    <1>1. max(S) = Undefined => S \in SUBSET {Undefined}
      BY Undefined_Arithmetic_Properties DEF max
    <1>2. S \in SUBSET {Undefined} => max(S) = Undefined
      BY DEF max
    <1> QED BY <1>1, <1>2

(***************************************************************************)
(* Maximum of a non-empty set is a member of the set                       *)
(***************************************************************************)
THEOREM MaxMembership ==
  ASSUME NEW S
  PROVE  S # {} <=> max(S) \in S

(***************************************************************************)
(* For any set, no member of the set is greater than the maximum           *)
(***************************************************************************)
THEOREM MaxNoneGreater ==
  ASSUME NEW S
  PROVE  ~\E e \in S : e > max(S)

(***************************************************************************)
(* Maximum of any subset of any set is at most the maximum of the set      *)
(***************************************************************************)
THEOREM MaxSubsets ==
  ASSUME NEW S1, NEW S2
  PROVE  S1 \subseteq S2 => max(S1) \leq max(S2)

(***************************************************************************)
(* Maximum of union of two sets is either of the maximums of the           *)
(* individuals                                                             *)
(***************************************************************************)
THEOREM MaxSetUnion ==
  ASSUME NEW S1, NEW S2
  PROVE  max(S1 \cup S2) \in {max(S1), max(S2)}

(***************************************************************************)
(* Maximum of union of sets is one of the maximums of the individuals      *)
(***************************************************************************)
THEOREM MaxSetUnions ==
  ASSUME NEW S
  PROVE  max(UNION S) \in {max(s) : s \in S}
=======================================================