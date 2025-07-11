------------------------------ MODULE AtomicCasino ----------------------------
(*****************************************************************************)
(* In this version of the Casino specification, all operations are assumed   *)
(* to be performed atomically, including money transfers. Observe that this  *)
(* is an idealization of the Solidity semantics, more faithful               *)
(* representations of the smart contract are analyzed in the non-atomic      *)
(* variants of the specification.                                            *)
(*                                                                           *)
(* The following properties are verified:                                    *)
(* - type correctness, which includes the fact that no overspending occurs,  *)
(* - the overall amount of Ether in the system remains constant, i.e., no    *)
(*   money is created or lost,                                               *)
(* - liveness: after a bet has been placed, the casino will return to the    *)
(*   initial (idle) state.                                                   *)
(* For applying the TLC model checker, verification is performed on the      *)
(* MC_AtomicCasino specification, which extends this module but imposes      *)
(* fixed, finite bounds on the state space.                                  *)
(*****************************************************************************)
EXTENDS Integers, TLC

(*****************************************************************************)
(* The participants in the system are the casino operator, the player, and   *)
(* the casino itself. We choose to represent them as singleton agents since  *)
(* there is no interference between different casinos or different players.  *)
(* In particular, once a player has placed a bet, only that player can       *)
(* interact until a new game is set up. This helps make the state space      *)
(* manageable for model checking. We also do not model the `sender' argument *)
(* of operations because each operation can only be performed by one agent.  *)
(*                                                                           *)
(* The casino can be in three different states as indicated in the problem   *)
(* description.                                                              *)
(*                                                                           *)
(* We do not model cryptographic hashing but store the secret and the guess  *)
(* of the player when the game is created, respectively when the bet is      *)
(* placed. However, the player does not access the secret when placing the   *)
(* bet. Alternatively, we could use non-determinism to resolve the game.     *)
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
    (************************************************************************)
    (* History variables representing the initial funds of the              *)
    (* operator and the player, used for checking that no money is lost.    *)
    (* We make these variables rather than constant parameters of the       *)
    (* specification so that TLC will check for all possible values         *)
    (* rather than for fixed values per model.                              *)
    (************************************************************************)
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
    /\ wallet["operator"] >= amount  \* implicit "payable" precondition of the smart contract
    /\ pot' = pot + amount
    /\ wallet' = [wallet EXCEPT !["operator"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<state, secret, guess, bet, operatorFunds, playerFunds>>

RemoveFromPot(amount) ==
    /\ state # "BET_PLACED" \* precondition `noActiveBet` of smart contract
    /\ wallet["casino"] >= amount \* fail if insufficient funds, due to failure of `transfer`
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
    /\ amount <= wallet["player"]  \* implicit precondition "payable"
    /\ amount <= pot  \* explicit precondition in smart contract
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
    \/ \E amount \in Ether : AddToPot(amount)
    \/ \E amount \in Ether : RemoveFromPot(amount)
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in Ether, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet

Fairness == WF_vars(DecideBet)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariant of the specification, beyond type correctness
Inv == 
    \* the ether held by the casino account equals the pot plus the player's bet
    /\ wallet["casino"] = pot + bet
    \* the system does not create or lose money
    /\ wallet["operator"] + wallet["player"] + wallet["casino"] 
       = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
