----------------------- MODULE MCNonAtomicCasinoFixedMT -----------------------
(*****************************************************************************)
(* Instance of NonAtomicCasinoFixedMT suitable for model checking by bounding*)
(* the state space. We also bound the number of pending calls to transfer    *)
(* from `removeFromPot` using the parameter MaxTransfers.                    *)
(*****************************************************************************)
EXTENDS NonAtomicCasinoFixedMT

CONSTANT MaxEther, MaxTransfers
ASSUME MaxEther \in Nat /\ MaxTransfers \in Nat

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

\* Count the number of pending transfers invoked from `removeFromPot`, 
\* including the multiplicity of bag elements.
CountRFPTransfers ==
    MapThenFoldBag(LAMBDA x,y : x+y,
                   0,
                   LAMBDA trf: IF trf.op \in {"TransferRFP", "SuccessTransferRFP", "FailureTransferRFP"}
                               THEN 1 ELSE 0,
                   LAMBDA B : CHOOSE x \in DOMAIN B : TRUE,
                   transfers)
StateConstraint == CountRFPTransfers <= MaxTransfers
===============================================================================
