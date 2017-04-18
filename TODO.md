List all TODOs. Once addressed, I shall comment saying so. If the issue is resolved,
we can mark it done and move it to DONE TODOs.

1) AL: at end of setup for Proposer, you need to set pc to "run_while".

  (I assume you didn't "check" this spec, besides syntax checking)

  in general, at end of setup, for all processes P,
  should set pc to something like "P_run_start".

  "run_start" is the same as "run_while" in Proposer, as a short cut.
    >> Done

2) AL: better change the pc value "start" in Acceptor to "run_await".

  "run_start" is the same as "run_await" here.

  such generality is why Kain has some actions that just update pc.

  short cut in general could be done, but not important now.
"start" and "end" are two states that all processes will have.
To make that more explicit, I've pulled the pc[a] = "setup" from
setups to definition of Init. I think it makes more sense because
spec of setup should look exactly like the code of setup.

3) AL: there are still other inconsistent uses of pc:
  e.g., some test != and some test =
    >> The only statement with a != with pc will be `pc[p] # "end"`.
    This is basically pc[p] \in {all states} \ {end}. The idea is
    that all receive handlers may be (Lamport's) enabled at all
    yield points while the process is running.
    
4) AL: Proposer_start should be called Proposer_run_while 
  (short cut again by omitting Proposer_run_start).
    >> Done

5) AL: Acceptor_start should really be called Acceptor_end (or Acceptor_run_end).

  it is also missing UNCHCANGED.
  (crazy to have to write it explicitly. I wonder what happens otherwise).
   
  need to be consistent with Proposal_end.
    >> Done

6) AL: a small thing that I didn't mention yesterday for this particular spec,
  but is important in general: all names of variables and values
  should in general be prefixed with process/method names.
    >> I think Done

7) SC: Change states from strings to CONSTANTS to avoid spelling errors in proof

8) SC: Separate receiving and handling of messages
