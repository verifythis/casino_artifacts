--------------------------- MODULE NonAtomicCasino ----------------------------
(*****************************************************************************)
(* This version of the Casino specification models the transfer method as a  *)
(* separate atomic operation, breaking the atomicity of the enclosing        *)
(* action. Several calls to transfer may be pending, which are represented   *)
(* using a multiset in the specification. Several properties are no longer   *)
(* verified, revealing problems with the smart contract.                     *)
(*                                                                           *)
(* This specification relies on the BagsExt module from the TLA+ Community   *)
(* Modules (https://github.com/tlaplus/CommunityModules). If your IDE        *)
(* doesn't include those, you should clone the repository and add it to the  *)
(* search path.                                                              *)
(*****************************************************************************)
EXTENDS Integers, Bags, BagsExt, TLC

Ether == Nat   \* will be overridden for model checking

Address == {"operator", "player", "casino"}
State == { "IDLE", "GAME_AVAILABLE", "BET_PLACED" }
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
    /\ pot \in Ether
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
    /\ wallet["operator"] >= amount   \* implicit "payable" precondition of the function
    /\ pot' = pot + amount
    /\ wallet' = [wallet EXCEPT !["operator"] = @ - amount,
                                !["casino"] = @ + amount]
    /\ UNCHANGED <<state, transfers, secret, guess, bet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method before the call to transfer
RemoveFromPot1(amount) ==
    /\ state # "BET_PLACED" \* precondition `noActiveBet` of the function
    \* We no longer assume that the operation fails if there are insufficient funds.
    \* Instead the failure will occur during the call to `transfer`.
    /\ transfers' = BagAdd(transfers, <<"rfp_invoked", amount>>)
    /\ UNCHANGED <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

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
          /\ pot' = pot - trf[2]
       \/ \* abort transaction if the transfer failed
          /\ trf[1] = "rfp_failed"
          /\ pot' = pot 
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
PlayerWins1 ==
    /\ pot' = pot - bet
    /\ transfers' = BagAdd(transfers, <<"pw_invoked", 2*bet>>)
    /\ UNCHANGED <<state, secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from PlayerWins
PlayerWins2 == \E trf \in DOMAIN transfers :
    /\ trf[1] = "pw_invoked"
    /\ \/ \* transfer succeeds, requiring sufficient funds
          /\ wallet["casino"] >= trf[2]
          /\ wallet' = [wallet EXCEPT !["player"] = @ + trf[2],
                                      !["casino"] = @ - trf[2]]
          /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                                 <<"pw_succeeded", trf[2]>>)
       \/ \* transfer fails
          /\ wallet' = wallet
          /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                                 <<"pw_failed", trf[2]>>)
    /\ UNCHANGED <<state, secret, guess, pot, bet, operatorFunds, playerFunds>>

\* part of PlayerWins after the call to transfer
PlayerWins3 == \E trf \in DOMAIN transfers :
    /\ \/ \* transfer succeeded, complete the transaction
          /\ trf[1] = "pw_succeeded"
          /\ bet' = 0
          /\ state' = "IDLE"
          /\ pot' = pot
       \/ \* transfer failed, roll back the transaction
          /\ trf[1] = "pw_failed"
          /\ pot' = pot + bet  \* restore pot
          /\ UNCHANGED <<bet, state>>
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<secret, guess, wallet, operatorFunds, playerFunds>>

OperatorWins ==
    /\ pot' = pot + bet
    /\ wallet' = wallet
    /\ bet' = 0
    /\ state' = "IDLE"
    /\ UNCHANGED <<transfers, secret, guess, wallet, operatorFunds, playerFunds>>

DecideBet ==
    \* This action corresponds to the invocation of `decideBet`.
    \* In case the player wins, we do not move to state IDLE yet.
    /\ state = "BET_PLACED"
    /\ \/ guess = secret /\ PlayerWins1
       \/ guess # secret /\ OperatorWins

Next ==
    \/ \E amount \in Ether : AddToPot(amount)
    \/ \E amount \in Ether : RemoveFromPot1(amount)
    \/ RemoveFromPot2 \/ RemoveFromPot3
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in Ether, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet \/ PlayerWins2 \/ PlayerWins3

\* Require fairness for the different subactions of DecideBet.
Fairness == WF_vars(DecideBet) /\ WF_vars(PlayerWins2) /\ WF_vars(PlayerWins3)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Invariants, beyond type correctness (these will fail)
Inv == 
    /\ wallet["casino"] = pot + bet
    \* the system does not lose money
    /\ wallet["operator"] + wallet["player"] + wallet["casino"] 
       = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved.
\* This property fails because transfers to the player can fail indefinitely,
\* for example if the player refuses to be paid out
\* (but since safety properties are violated, this is basically moot).
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
