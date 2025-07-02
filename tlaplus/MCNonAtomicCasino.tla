--------------------------- MODULE MCNonAtomicCasino --------------------------
(*****************************************************************************)
(* Instance of NonAtomicCasino suitable for model checking by bounding the   *)
(* state space. The operator MCEther overrides Ether for model checking and  *)
(* MCSpec is used as the specification for model checking.                   *)
(*****************************************************************************)
EXTENDS NonAtomicCasino

CONSTANT MaxEther
ASSUME MaxEther \in Nat

MCEther == 0 .. MaxEther

\* Strengthen the initial condition such that the initial funds of the
\* operator and player are such that all amounts always stay in the
\* restricted set MCEther.
MCInit == \E of, pf \in MCEther :
    /\ of + pf \in MCEther
    /\ operatorFunds = of
    /\ playerFunds = pf
    /\ Init

MCSpec == MCInit /\ [][Next]_vars /\ Fairness

(*****************************************************************************)
(* The typing invariant can be violated, at least temporarily. For example,  *)
(* the operator may remove money from the pot, then add money to the pot     *)
(* after the withdrawal has succeeded but before the money has been deduced  *)
(* from the pot, leading to the pot exceeding MaxEther. This also leads to a *)
(* violation of the first conjunct of the invariant Inv.                     *)
(*                                                                           *)
(* That invariant violation is a symptom of incomplete transactions being    *)
(* revealed to the environment due to non-atomicity of methods invoking the  *)
(* transfer method, but it is essentially harmless. Attempting to fix the    *)
(* property, as in the following version of type correctness, reveals more   *)
(* serious errors. First, the DecideBet function can be invoked twice in     *)
(* succession, leading to the amount in the pot becoming negative, at least  *)
(* temporarily. Second, when commenting out the conjunct "pot \in Nat", TLC  *)
(* exhibits a combination of a transfer invoked from RemoveFromPot and       *)
(* another transfer invoked from PlayerWins leads to the player being paid   *)
(* out more than is available in the pot, and would ultimately lead to the   *)
(* pot becoming negative.                                                    *)
(*****************************************************************************)
MCTypeOK ==
    /\ state \in State
    /\ IsABag(transfers)
    /\ DOMAIN transfers \subseteq TransferState
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot \in Nat
    /\ bet \in Ether
    /\ wallet \in [Address -> Ether]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

===============================================================================
