------------------------- MODULE NonAtomicCasinoFixed -------------------------
(*****************************************************************************)
(* This version of the Casino specification is derived from the one in the   *)
(* module NonAtomicCasino, but it fixes the problems discovered when running *)
(* TLC on that specification.                                                *)
(*                                                                           *)
(* This specification relies on the BagsExt module from the TLA+ Community   *)
(* Modules (https://github.com/tlaplus/CommunityModules). If your IDE        *)
(* doesn't include those, you should clone the repository and add it to the  *)
(* search path.                                                              *)
(*****************************************************************************)
EXTENDS Integers, Bags, BagsExt, TLC

Ether == Nat   \* will be overridden for model checking

Address == {"operator", "player", "casino"}
\* Introduce an additional state to prevent `decideBet` to be called twice in succession
State == { "IDLE", "GAME_AVAILABLE", "BET_PLACED", "DECIDING_BET" }
\* states of pending transfers: rfp_XXX corresponds to transfers invoked from
\* RemoveFromPot, pw_XXX to transfers invoked from the PlayerWins branch of DecideBet
TransferState == {"rfp_invoked", "rfp_succeeded", "rfp_failed", "pw_invoked", "pw_succeeded", "pw_failed"} \X Ether
Heads == 0
Tails == 1

VARIABLES
    state,         \* state of the casino
    transfers,     \* pending transfers
    secret,        \* secret chosen at game creation
    guess,         \* player's guess when placing the bet
    pot,           \* value of the pot
    bet,           \* player's bet value
    wallet,        \* amount of ether for each address
    (************************************************************************)
    (* History variables representing the initial funds of the              *)
    (* operator and the player, used for checking that no money is lost.    *)
    (* We make these variables rather than constant parameters of the       *)
    (* specification so that TLC will check for all possible values         *)
    (* rather than for fixed values per model.                              *)
    (************************************************************************)
    operatorFunds,
    playerFunds

vars == <<state, transfers, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

TypeOK ==
    /\ state \in State
    /\ IsABag(transfers)
    /\ DOMAIN transfers \subseteq TransferState
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    \* The pot may temporarily become negative when removeFromPot is invoked, but
    \* not if the transfer method succeeds.
    /\ pot \in Int
    /\ (~\E trf \in DOMAIN transfers: trf[1] \in {"rfp_invoked", "rfp_failed"}) => pot \in Ether
    /\ bet \in Ether
    /\ wallet \in [Address -> Ether]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

Init ==
    /\ state = "IDLE"
    /\ transfers = EmptyBag
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot = 0
    /\ bet = 0
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether 
    /\ wallet = ("operator" :> operatorFunds) 
             @@ ("player" :> playerFunds) 
             @@ ("casino" :> 0)

AddToPot(amount) ==
    /\ wallet["operator"] >= amount  \* implicit "payable" precondition of the function
    /\ pot' = pot + amount
    /\ wallet' = [wallet EXCEPT !["operator"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<state, transfers, secret, guess, bet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method before the call to transfer
RemoveFromPot1(amount) ==
    /\ state \notin {"BET_PLACED", "DECIDING_BET"} \* precondition `noActiveBet' of the function, extended to new state
    \* We no longer assume that the operation fails if there are insufficient funds.
    \* Instead the failure will occur during the call to `transfer`.
    /\ \* adjust the money in the pot before invoking transfer
       pot' = pot - amount
    /\ transfers' = BagAdd(transfers, <<"rfp_invoked", amount>>)
    /\ UNCHANGED <<state, secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from RemoveToPot
RemoveFromPot2 == \E trf \in DOMAIN transfers :
    /\ trf[1] = "rfp_invoked"
    /\ \/ \* transfer succeeds: this requires that the casino has sufficient funds
          /\ wallet["casino"] >= trf[2]
          /\ wallet' = [wallet EXCEPT !["operator"] = @ + trf[2],
                                      !["casino"] = @ - trf[2]]
          /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                                 <<"rfp_succeeded", trf[2]>>)
       \/ \* transfer fails (may happen in any case)
          /\ wallet' = wallet 
          /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                                 <<"rfp_failed", trf[2]>>)
    /\ UNCHANGED <<state, secret, guess, pot, bet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method after the call to transfer
RemoveFromPot3 == \E trf \in DOMAIN transfers :
    /\ \/ \* complete transaction if the transfer succeeded
          /\ trf[1] = "rfp_succeeded"
          /\ pot' = pot
       \/ \* roll back the transaction if the transfer failed
          /\ trf[1] = "rfp_failed"
          /\ pot' = pot + trf[2]
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<state, secret, guess, bet, wallet, operatorFunds, playerFunds>>

CreateGame(_secret) ==
    /\ state = "IDLE"
    /\ secret' = _secret
    /\ state' = "GAME_AVAILABLE"
    /\ UNCHANGED <<guess, transfers, pot, bet, wallet, operatorFunds, playerFunds>>

PlaceBet(amount, _guess) ==
    /\ state = "GAME_AVAILABLE"
    /\ amount <= wallet["player"]  \* implicit precondition "payable"
    /\ amount <= pot  \* explicit precondition of function `placeBet`
    /\ state' = "BET_PLACED"
    /\ guess' = _guess
    /\ bet' = amount
    /\ wallet' = [wallet EXCEPT !["player"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<secret, transfers, pot, operatorFunds, playerFunds>>

\* part of PlayerWins up to call to transfer method
\* This now includes a transition to the intermediate state DECIDING_BET.
PlayerWins1 ==
    /\ pot' = pot - bet
    /\ transfers' = BagAdd(transfers, <<"pw_invoked", 2*bet>>)
    /\ state' = "DECIDING_BET"
    /\ UNCHANGED <<secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from PlayerWins
\* In order to express fairness more easily, we write two actions corresponding
\* to success or failure of the transfer.
PlayerWins2Success == \E trf \in DOMAIN transfers :
    /\ trf[1] = "pw_invoked"
    /\ wallet["casino"] >= trf[2]
    /\ wallet' = [wallet EXCEPT !["player"] = @ + trf[2],
                                !["casino"] = @ - trf[2]]
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           <<"pw_succeeded", trf[2]>>)
    /\ UNCHANGED <<state, secret, guess, pot, bet, operatorFunds, playerFunds>>

PlayerWins2Failure == \E trf \in DOMAIN transfers :
    /\ trf[1] = "pw_invoked"
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           <<"pw_failed", trf[2]>>)
    /\ UNCHANGED <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

\* part of PlayerWins after the call to transfer
PlayerWins3 == \E trf \in DOMAIN transfers :
    /\ \/ \* transfer succeeded, complete the transaction
          /\ trf[1] = "pw_succeeded"
          /\ bet' = 0
          /\ state' = "IDLE"
          /\ pot' = pot
       \/ \* transfer failed, roll back the transaction, including return to previous control state
          /\ trf[1] = "pw_failed"
          /\ state' = "BET_PLACED"
          /\ pot' = pot + bet  \* restore pot
          /\ UNCHANGED bet
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<secret, guess, wallet, operatorFunds, playerFunds>>

OperatorWins ==
    /\ pot' = pot + bet
    /\ wallet' = wallet
    /\ bet' = 0
    /\ state' = "IDLE"
    /\ UNCHANGED <<transfers, secret, guess, wallet, operatorFunds, playerFunds>>

DecideBet ==
    /\ state = "BET_PLACED"
    /\ \/ guess = secret /\ PlayerWins1
       \/ guess # secret /\ OperatorWins

Next ==
    \/ \E amount \in Ether : AddToPot(amount)
    \/ \E amount \in Ether : RemoveFromPot1(amount)
    \/ RemoveFromPot2 \/ RemoveFromPot3
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in Ether, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet \/ PlayerWins2Success \/ PlayerWins2Failure \/ PlayerWins3

\* We strengthen the fairness condition such that DecideBet must finish
\* and also such that some transfer to the player must eventually succeed.
Fairness == WF_vars(DecideBet) /\ SF_vars(PlayerWins2Success) /\ WF_vars(PlayerWins3)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariants, beyond type correctness
Inv == 
    \* the system does not create or lose money
    /\ wallet["operator"] + wallet["player"] + wallet["casino"] 
       = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved.
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
