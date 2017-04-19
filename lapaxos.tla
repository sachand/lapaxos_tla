------------------ MODULE lapaxos ------------------
EXTENDS TLAPS, Integers, Sequences, FiniteSets, Aggregates, Channel

CONSTANTS
  Acceptors,
  Learners,
  Proposers

\* States of Program Counter
CONSTANTS
  START,
  END,
  PROPOSER_RUN_WHILE,
  PROPOSER_AWAIT

VARIABLES
  pc,
  acceptor_learners,
  proposer_acceptors, proposer_n, proposer_majority

vars == << sent, received, pc, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Processes == Acceptors \cup Learners \cup Proposers

anyof(S) ==
  CHOOSE s \in S \cup {Undefined}: TRUE

(*********************************************)
(* Spec BEGINS                               *)
(*********************************************)
Acceptor_setup(a(*, Learners*)) == 
  acceptor_learners[a] = Learners

Acceptor_receive_prepare(a) ==
  \E m \in sent_to(a):
    /\ Receive(a, m)
    /\ m.body[0] = "prepare"    
    /\ LET maxprop == anyof({<< m2.body[1], m2.body[2] >> : m2 \in 
            {m2 \in sent_by(a) : m2.body[0] = "accepted" /\ m2.body[1] = max(
            {m3.body[1] : m3 \in {m3 \in sent_by(a) : m3.body[0] = "accepted"}})}}) IN
       IF \A m2 \in sent_by(a): m2.body[0] = "respond" => m.body[1] > m2.body[1] THEN
         Send(a, {m.body[2]}, <<"respond", m.body[1], maxprop>>)
       ELSE UNCHANGED << sent >>
    /\ pc[a] # END
    /\ UNCHANGED << pc, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Acceptor_receive_accept(a) ==
  \E m \in sent_to(a):
    /\ Receive(a, m)
    /\ m.body[0] = "accept"
    /\ IF ~\E m2 \in sent_by(a):
         /\ m2.body[0] = "respond"
         /\ m2.body[1] > m.body[1]
         THEN Send(a, acceptor_learners[a], <<"accepted", m.body[1], m.body[2]>>)
         ELSE UNCHANGED << sent >>
    /\ pc[a] # END
    /\ UNCHANGED << pc, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Acceptor_receive_done(a) == \* Temporary. Goes after abstracting receive and act/ENABLED separately
  \E m \in sent_to(a):
    /\ Receive(a, m)
    /\ m.body[0] = "done"
    /\ pc[a] # END
    /\ UNCHANGED << sent, pc, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Acceptor_run_end(a) ==
  /\ \E m \in received[a]: m.body[0] = "done"
  /\ pc[a] = START
  /\ pc' = [pc EXCEPT![a] = END]
  /\ UNCHANGED << sent, received, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

(************************************************************************)
Proposer_setup(p(*, Acceptors*)) ==
  /\ proposer_acceptors[p] = Acceptors
  /\ proposer_n[p] = Undefined
  /\ proposer_majority[p] = Acceptors

Proposer_run_while(p) ==
  /\ ~\E m \in received[p]: m.body[0] = "done"
  /\ pc[p] \in {START}
  /\ pc' = [pc EXCEPT![p] = PROPOSER_RUN_WHILE]
  /\ UNCHANGED << sent, received, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Proposer_run_end(p) ==
  /\ \E m \in received[p]: m.body[0] = "done"
  /\ pc[p] \in {START}
  /\ pc' = [pc EXCEPT![p] = END]
  /\ UNCHANGED << sent, received, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Proposer_to_consent_start(p) ==
  /\ IF proposer_n[p] = Undefined THEN proposer_n' = [proposer_n EXCEPT![p] = <<0, p>>]
                         ELSE proposer_n' = [proposer_n EXCEPT![p] = <<proposer_n[p][0] + 1, p>>]
  /\ Send(p, proposer_majority[p], <<"prepare", proposer_n'[p]>>)  
  /\ pc[p] \in {PROPOSER_RUN_WHILE}
  /\ pc' = [pc EXCEPT![p] = PROPOSER_AWAIT]
  /\ UNCHANGED << received, acceptor_learners, proposer_acceptors, proposer_majority >>

Proposer_to_consent_await(p) ==
  /\ Cardinality({m.from: m \in {m \in received[p] : m.body[0] = "respond" /\ m.body[1] = proposer_n[p]}}) > Cardinality(proposer_acceptors[p]) \div 2
  /\ LET
     S == {m3.body[2][1] : m3 \in
          {m3 \in received[p]: m3.body[0] = "respond" /\ m3.body[1] = proposer_n[p] /\
           m3.body[2][0] = max({m2.body[2][0]: m2 \in 
            {m2 \in received[p] : m2.body[0] = "respond" /\ m2.body[1] = proposer_n[p]}})}}
     responded == {m2.from: m2 \in {m2 \in received[p] : m2.body[0] = "respond" /\ m2.body[1] = proposer_n[p]}} IN
     IF S = {} THEN Send(p, responded, <<"accept", proposer_n[p], anyof({1..100})>>)
               ELSE Send(p, responded, <<"accept", proposer_n[p], anyof(S)>>)
  /\ pc[p] = PROPOSER_AWAIT
  /\ pc' = [pc EXCEPT![p] = START]
  /\ UNCHANGED << received, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Proposer_to_consent_end(p) ==
  /\ ~(Cardinality({m.from: m \in {m \in received[p] : m.body[0] = "respond" /\ m.body[1] = proposer_n[p]}}) > Cardinality(proposer_acceptors[p]) \div 2)
  /\ pc[p] = PROPOSER_AWAIT
  /\ pc' = [pc EXCEPT![p] = START]
  /\ UNCHANGED << sent, received, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

Proposer_receive(p) ==
  \E m \in sent_to(p):
    /\ pc[p] # END
    /\ Receive(p, m)
    /\ UNCHANGED << sent, pc, acceptor_learners, proposer_acceptors, proposer_n, proposer_majority >>

---------------------------------------------
Init == \* Conjunction of setups
  /\ \A a \in Acceptors: Acceptor_setup(a)
  /\ \A p \in Proposers: Proposer_setup(p)
  /\ Channel_setup
  /\ \A p \in Processes: pc[p] = START

Next == \* Disjunction of all actions above
  \/ \E a \in Acceptors:
    \/ Acceptor_receive_prepare(a)
    \/ Acceptor_receive_accept(a)
    \/ Acceptor_receive_done(a)
    \/ Acceptor_run_end(a)
  \/ \E p \in Proposers:
    \/ Proposer_run_while(p)
    \/ Proposer_run_end(p)
    \/ Proposer_to_consent_start(p)
    \/ Proposer_to_consent_await(p)
    \/ Proposer_to_consent_end(p)
    \/ Proposer_receive(p)

Spec == Init /\ [Next]_<<vars>>
=============================================

(* NOTES:

1) After writing the actions, it can be concluded that acceptor_learners,
proposer_acceptors, and proposer_majority are constants. No action modifies them.
Thus, they can be moved to CONSTANTS in a second pass by compiler

*)