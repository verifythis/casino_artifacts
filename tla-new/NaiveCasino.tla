------------------------------- MODULE NaiveCasino ----------------------------
(*****************************************************************************)
(* This version of the Casino specification is an adaptation and correction  *)
(* of the TLA+ specification available in the VerifyThis zenodo. All         *)
(* operations are assumed to be performed atomically, including money        *)
(* transfers. Observe that this does not correspond to the actual semantics  *)
(* of Solidity smart contracts.                                              *)
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
States == { "IDLE", "GAME_AVAILABLE", "BET_PLACED" }
Heads == 0
Tails == 1

VARIABLES
    state,         \* state of the casino
    secret,        \* secret chosen at game creation
    guess,         \* player's guess when placing the bet
    pot,           \* value of the pot
    bet,           \* player's bet value
    wallet,        \* amount of ether for each address
    \* history variables representing the initial funds of the
    \* operator and the player, used for checking that no money is lost
    operatorFunds,
    playerFunds

vars == <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

TypeOK ==
    /\ state \in States
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    /\ pot \in Ether
    /\ bet \in Ether
    /\ wallet \in [Address -> Ether]
    /\ operatorFunds \in Ether
    /\ playerFunds \in Ether

Init ==
    /\ state = "IDLE"
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
    /\ UNCHANGED <<state, secret, guess, bet, operatorFunds, playerFunds>>

RemoveFromPot(amount) ==
    /\ state # "BET_PLACED" \* no active bet ongoing
    /\ pot >= amount \* fail if insufficient funds
    /\ pot' = pot - amount
    /\ wallet' = [wallet EXCEPT !["operator"] = @ + amount,
                                !["casino"] = @ - amount]
    /\ UNCHANGED <<state, secret, guess, bet, operatorFunds, playerFunds>>

CreateGame(_secret) ==
    /\ state = "IDLE"
    /\ secret' = _secret
    /\ state' = "GAME_AVAILABLE"
    /\ UNCHANGED <<guess, pot, bet, wallet, operatorFunds, playerFunds>>

PlaceBet(amount, _guess) ==
    /\ state = "GAME_AVAILABLE"
    /\ amount <= wallet["player"]
    /\ amount <= pot
    /\ state' = "BET_PLACED"
    /\ guess' = _guess
    /\ bet' = amount
    /\ wallet' = [wallet EXCEPT !["player"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<secret, pot, operatorFunds, playerFunds>>

PlayerWins ==
    /\ pot' = pot - bet
    /\ wallet' = [wallet EXCEPT !["player"] = @ + 2*bet,
                                !["casino"] = @ - 2*bet]

OperatorWins ==
    /\ pot' = pot + bet
    /\ wallet' = wallet

DecideBet ==
    \* Again, a failed operation corresponds to stuttering, so we only
    \* model the case where the transfer succeeds.
    /\ state = "BET_PLACED"
    /\ state' = "IDLE"
    /\ bet' = 0
    /\ \/ guess = secret /\ PlayerWins
       \/ guess # secret /\ OperatorWins
    /\ UNCHANGED <<secret, guess,   \* keep current values, but they don't matter
                   operatorFunds, playerFunds>>

Next ==
    \/ \E amount \in 0 .. wallet["operator"] : AddToPot(amount)
    \/ \E amount \in 0 .. pot : RemoveFromPot(amount)
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in 0 .. pot, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet

Fairness == WF_vars(DecideBet)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariant of the specification, beyond type correctness
Inv == 
    /\ wallet["casino"] = pot + bet
    \* the system does not lose money
    /\ wallet["operator"] + wallet["player"] + wallet["casino"] 
       = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
