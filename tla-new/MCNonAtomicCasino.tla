---------------------------- MODULE MCNonAtomicCasino -------------------------
(*****************************************************************************)
(* Instance of NonAtomicCasino suitable for model checking by bounding the   *)
(* state space. The operators MCEther and MCInit are used to override Ether  *)
(* and Init as indicated in the configuration file.                          *)
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
(* The typing invariant can be (temporarily) violated when the operator      *)
(* calls back AddtoPot after the transfer method from RemoveToPot has        *)
(* succeeded but before the pot is decremented following the transfer.       *)
(*                                                                           *)
(* Similarly, the first conjunct of the invariant is violated because the    *)
(* amount has already been deduced from the wallet of the casino but not     *)
(* yet from the pot.                                                         *)
(*                                                                           *)
(* Both invariant violations are symptoms of incomplete transactions being   *)
(* revealed to the environment due to non-atomicity of methods invoking the  *)
(* transfer method. Attempting to fix them as in the following version of    *)
(* type correctness reveals even more serious errors: the interleaving of    *) 
(* RemovePot and PlaceBet / DecideWin can lead to funds being overdrawn.     *)
(*****************************************************************************)
MCTypeOK ==
    /\ state \in State
    /\ rfpTransfer \in TransferState
    /\ dbTransfer \in TransferState
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot \in Nat
    /\ rfpTransfer[1] \in {"none", "invoked"} => pot \in MCEther
    /\ bet \in MCEther
    /\ wallet \in [Address -> MCEther]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

===============================================================================
