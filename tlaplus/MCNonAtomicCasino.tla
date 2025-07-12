--------------------------- MODULE MCNonAtomicCasino --------------------------
(*****************************************************************************)
(* Instance of NonAtomicCasino suitable for model checking by bounding the   *)
(* state space. The operator MCEther overrides Ether for model checking and  *)
(* MCSpec is used as the specification for model checking. The constant      *)
(* MaxTransfer bounds the size of the transfer stack, ensuring that the      *)
(* state space analyzed by TLC remains bounded.                              *)
(*****************************************************************************)
EXTENDS NonAtomicCasino

CONSTANT MaxEther, MaxTransfer
ASSUME MaxEther \in Nat /\ MaxTransfer \in Nat

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

StateConstraint == Len(transfers) <= MaxTransfer

(*****************************************************************************)
(* The typing invariant can be violated, at least temporarily. For example,  *)
(* the operator may remove money from the pot, then add money to the pot     *)
(* after the withdrawal has succeeded but before the money has been deduced  *)
(* from the pot, leading to the pot exceeding MaxEther. Also, the first      *)
(* conjunct of Inv is violated because the changes to the pot and the wallet *)
(* do not happen in a single atomic step.                                    *)
(*                                                                           *)
(* These effects are symptoms of incomplete transactions being exposed to    *)
(* the environment due to non-atomicity of methods invoking the transfer     *)
(* method, but they are essentially harmless. Attempting to fix the property *)
(* as in the following version of type correctness reveals more serious      *)
(* errors. For example, DecideBet can be called twice in succession, for     *)
(* example due to a callback from the transfer method on behalf of the       *)
(* player, which could eventually lead to the account of the casino to be    *)
(* overdrawn. When commenting out the conjunct concerning the variable pot,  *)
(* an even more serious error is found where a RemoveFromPot operation       *)
(* succeeds but is not completed. Subsequently, the game is created, a bet   *)
(* is placed based on the money present in the pot, and the game is won by   *)
(* the player, leading to a situation where the win of the player exceeds    *)
(* the overall amount of ether present in the system.                        *)
(*****************************************************************************)
RelaxedTypeOK ==
    /\ state \in State
    /\ transfers \in Seq(CallEntry)
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot \in Nat
    /\ bet \in Ether
    /\ wallet \in [Address -> Ether]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

===============================================================================
