-------------------------- MODULE FixedNonAtomicCasino ------------------------
(*****************************************************************************)
(* This version of the Casino specification models the transfer method as a  *)
(* separate atomic operation and fixes the problems discovered with the      *)
(* NonAtomicCasino specification.                                            *)
(*****************************************************************************)
EXTENDS Integers, TLC

(*****************************************************************************)
(* The participants in the system are the casino operator, the player, and   *)
(* the casino itself. We choose to represent them as singleton agents        *)
(* there is no interference between different casinos or different players.  *)
(* In particular, once a player has placed a bet, only that player can       *)
(* interact from that point onwards. This helps make the state space         *)
(* manageable for model checking. We also remove the `sender' argument from  *)
(* operations because each operation can only be performed by one agent.     *)
(*                                                                           *)
(* The casino can be in three different states as indicated in the problem   *)
(* description.                                                              *)
(*                                                                           *)
(* We do not model cryptographic hashing but store the secret and the guess  *)
(* of the player when the game is created, respectively the bet is placed.   *)
(* However, the player does not access the secret when placing the bet.      *)
(* Alternatively, we could just use non-determinism to resolve the game.     *)
(*****************************************************************************)

Ether == Nat   \* will be overridden for model checking

Address == {"operator", "player", "casino"}
State == { "IDLE", "GAME_AVAILABLE", "BET_PLACED" }
TransferState == {"none", "invoked", "succeeded", "failed"} \X Ether
Heads == 0
Tails == 1

VARIABLES
    state,         \* state of the casino
    rfpTransfer,   \* state of transfer corresponding to RemoveFromPot, if any
    dbTransfer,    \* state of transfer corresponding to DecideBet, if any
    secret,        \* secret chosen at game creation
    guess,         \* player's guess when placing the bet
    pot,           \* value of the pot
    bet,           \* player's bet value
    wallet,        \* amount of ether for each address
    \* history variables representing the initial funds of the
    \* operator and the player, used for checking that no money is lost
    operatorFunds,
    playerFunds

vars == <<state, rfpTransfer, dbTransfer, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

TypeOK ==
    /\ state \in State
    /\ rfpTransfer \in TransferState
    /\ dbTransfer \in TransferState
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot \in Ether
    /\ bet \in Ether
    /\ wallet \in [Address -> Ether]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

Init ==
    /\ state = "IDLE"
    /\ rfpTransfer = <<"none", 0>>
    /\ dbTransfer = <<"none", 0>>
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
    \* If the operator doesn't have sufficient funds, the operation must fail.
    \* A failed operation corresponds to stuttering and doesn't need to be 
    \* modeled explicitly.
    /\ wallet["operator"] >= amount
    /\ pot' = pot + amount
    /\ wallet' = [wallet EXCEPT !["operator"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<state, rfpTransfer, dbTransfer, secret, guess, bet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method before the call to transfer
RemoveFromPot1(amount) ==
    /\ state # "BET_PLACED" \* no active bet ongoing
    /\ rfpTransfer[1] = "none"
    /\ pot >= amount \* fail if insufficient funds
    /\ \* adjust the money in the pot before invoking transfer
       pot' = pot - amount
    /\ rfpTransfer' = <<"invoked", amount>>
    /\ UNCHANGED <<state, dbTransfer, secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from RemoveToPot
RemoveFromPot2 ==
    /\ rfpTransfer[1] = "invoked"
    /\ \/ \* transfer succeeds
          /\ wallet' = [wallet EXCEPT !["operator"] = @ + rfpTransfer[2],
                                      !["casino"] = @ - rfpTransfer[2]]
          /\ rfpTransfer' = <<"succeeded", rfpTransfer[2]>>
       \/ \* transfer fails
          /\ wallet' = wallet 
          /\ rfpTransfer' = <<"failed", rfpTransfer[2]>>
    /\ UNCHANGED <<state, dbTransfer, secret, guess, pot, bet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method after the call to transfer
RemoveFromPot3 ==    
    /\ \/ \* complete transaction if the transfer succeeded
          /\ rfpTransfer[1] = "succeeded"
          /\ pot' = pot
       \/ \* roll back the transaction if the transfer failed
          /\ rfpTransfer[1] = "failed"
          /\ pot' = pot + rfpTransfer[2]
    /\ rfpTransfer' = <<"none", 0>>
    /\ UNCHANGED <<state, dbTransfer, secret, guess, bet, wallet, operatorFunds, playerFunds>>

CreateGame(_secret) ==
    /\ state = "IDLE"
    /\ secret' = _secret
    /\ state' = "GAME_AVAILABLE"
    /\ UNCHANGED <<guess, rfpTransfer, dbTransfer, pot, bet, wallet, operatorFunds, playerFunds>>

PlaceBet(amount, _guess) ==
    /\ state = "GAME_AVAILABLE"
    /\ amount <= wallet["player"]
    /\ amount <= pot
    /\ state' = "BET_PLACED"
    /\ guess' = _guess
    /\ bet' = amount
    /\ wallet' = [wallet EXCEPT !["player"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<secret, rfpTransfer, dbTransfer, pot, operatorFunds, playerFunds>>

\* part of PlayerWins up to call to transfer method
PlayerWins1 ==
    /\ pot' = pot - bet
    /\ dbTransfer' = <<"invoked", 2*bet>>
    /\ UNCHANGED <<state, rfpTransfer, secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from PlayerWins
PlayerWins2 ==
    /\ dbTransfer[1] = "invoked"
    /\ \/ \* transfer succeeds
          /\ wallet' = [wallet EXCEPT !["player"] = @ + dbTransfer[2],
                                      !["casino"] = @ - dbTransfer[2]]
          /\ dbTransfer' = <<"succeeded", dbTransfer[2]>>
       \/ /\ wallet' = wallet
          /\ dbTransfer' = <<"failed", dbTransfer[2]>>
    /\ UNCHANGED <<state, rfpTransfer, secret, guess, pot, bet, operatorFunds, playerFunds>>

\* part of PlayerWins after the call to transfer
PlayerWins3 ==
    /\ \/ \* transfer succeeded, complete the transaction
          /\ dbTransfer[1] = "succeeded"
          /\ bet' = 0
          /\ state' = "IDLE"
          /\ pot' = pot
       \/ \* transfer failed, roll back the transaction
          /\ dbTransfer[1] = "failed"
          /\ pot' = pot + bet  \* restore pot
          /\ UNCHANGED <<bet, state>>
    /\ dbTransfer' = <<"none", 0>>
    /\ UNCHANGED <<rfpTransfer, secret, guess, wallet, operatorFunds, playerFunds>>

OperatorWins ==
    /\ pot' = pot + bet
    /\ wallet' = wallet
    /\ bet' = 0
    /\ state' = "IDLE"
    /\ UNCHANGED <<dbTransfer, rfpTransfer, secret, guess, wallet, operatorFunds, playerFunds>>

DecideBet ==
    /\ state = "BET_PLACED"
    /\ dbTransfer[1] = "none"
    /\ \/ guess = secret /\ PlayerWins1
       \/ guess # secret /\ OperatorWins

Next ==
    \/ \E amount \in 0 .. wallet["operator"] : AddToPot(amount)
    \/ \E amount \in 0 .. pot : RemoveFromPot1(amount)
    \/ RemoveFromPot2 \/ RemoveFromPot3
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in 0 .. pot, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet \/ PlayerWins2 \/ PlayerWins3

\* We strengthen the fairness condition such that DecideBet must finish
\* and also such that some transfer to the player must eventually succeed.
Fairness == 
    /\ WF_vars(DecideBet) /\ WF_vars(PlayerWins2) /\ WF_vars(PlayerWins3)
    /\ SF_vars(PlayerWins2 /\ dbTransfer'[1] = "succeeded")

Spec == Init /\ [][Next]_vars /\ Fairness /\ Fairness

\* Invariants, beyond type correctness
Inv == 
    /\ wallet["casino"]
       = IF rfpTransfer[1] \in {"invoked", "failed"} /\ dbTransfer[1] \in {"invoked", "failed"}
         THEN pot + rfpTransfer[2] + dbTransfer[2]
         ELSE IF rfpTransfer[1] \in {"invoked", "failed"} /\ dbTransfer[1] = "succeeded"
         THEN pot + rfpTransfer[2]
         ELSE IF rfpTransfer[1] \in {"invoked", "failed"}
         THEN pot + bet + rfpTransfer[2]
         ELSE IF dbTransfer[1] \in {"invoked", "failed"}
         THEN pot + dbTransfer[2]
         ELSE IF dbTransfer[1] = "succeeded"
         THEN pot
         ELSE pot + bet
    \* the system does not lose money
    /\ wallet["operator"] + wallet["player"] + wallet["casino"] 
       = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved.
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
