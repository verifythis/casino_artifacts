------------------------------ MODULE MCNaiveCasino ---------------------------
(*****************************************************************************)
(* Instance of NaiveCasino suitable for model checking by bounding the state *)
(* space. The operator MCEther overrides Ether for model checking and MCSpec *)
(* is used as the specification for model checking.                          *)
(*****************************************************************************)
EXTENDS NaiveCasino, TLC

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
