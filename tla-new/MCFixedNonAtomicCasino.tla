------------------------- MODULE MCFixedNonAtomicCasino -----------------------
(*****************************************************************************)
(* Instance of FixedNonAtomicCasino suitable for model checking by bounding  *)
(* the state space.                                                          *)
(*****************************************************************************)
EXTENDS FixedNonAtomicCasino

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

===============================================================================
