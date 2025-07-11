------------------------- MODULE NonAtomicCasinoFixedMT -------------------------
(*****************************************************************************)
(* This version of the Casino specification is derived from the one in the   *)
(* module NonAtomicCasinoFixed, but it corresponds to a multi-threaded       *)
(* version of Solidity and represents pending transfer invocations using a   *)
(* bag (multiset) rather than a sequence.                                    *)
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
Heads == 0
Tails == 1

(*****************************************************************************)
(* We represent pending calls of the transfer function in a stack containing *)
(* entries of the form [op: Operation, arg: Ether] where `op' describes the  *)
(* state of the transfer operation (called, succeeded or failed). Since      *)
(* `transfer' is called from function `removeFromPot' and `decideBet', more  *)
(* specifically in case the player wins, we tag these operations with RFP    *)
(* (removeFromPot) and PW (playerWins).                                      *)
(*****************************************************************************)
Operation == {"TransferRFP", "SuccessTransferRFP", "FailureTransferRFP", 
               "TransferPW", "SuccessTransferPW", "FailureTransferPW"}
CallEntry == [op: Operation, arg: Ether]

VARIABLES
    state,         \* state of the casino
    transfers,     \* bag of pending transfers
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
    /\ DOMAIN transfers \subseteq CallEntry
    /\ secret \in {Heads, Tails}
    /\ guess \in {Heads, Tails}
    \* The pot may temporarily become negative when removeFromPot is invoked, but
    \* not if the transfer method succeeds.
    /\ pot \in Int
    /\ (\A trf \in DOMAIN transfers: trf.op \notin {"TransferRFP", "FailureTransferRFP"}) 
       => pot \in Ether
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
    \* precondition `noActivebet' extended to new state "DECIDING_BET"
    /\ state \notin {"BET_PLACED", "DECIDING_BET"}
    \* We no longer assume that the operation fails if there are insufficient funds.
    \* Instead the failure will occur during the call to `transfer`.
    /\ \* adjust the money in the pot before invoking transfer
       pot' = pot - amount
    /\ transfers' = BagAdd(transfers, [op |-> "TransferRFP", arg |-> amount])
    /\ UNCHANGED <<state, secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from RemoveToPot: successful execution
RemoveFromPot2Success == \E trf \in DOMAIN transfers :
    /\ trf.op = "TransferRFP"
    \* transfer can succeed only if the casino account holds enough money
    /\ wallet["casino"] >= trf.arg
    /\ wallet' = [wallet EXCEPT !["operator"] = @ + trf.arg,
                                !["casino"] = @ - trf.arg]
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           [op |-> "SuccessTransferRFP", arg |-> trf.arg])
    /\ UNCHANGED <<state, secret, guess, pot, bet, operatorFunds, playerFunds>>

RemoveFromPot2Failure == \E trf \in DOMAIN transfers :
    /\ trf.op = "TransferRFP"
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           [op |-> "FailureTransferRFP", arg |-> trf.arg])
    /\ UNCHANGED <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method after successful transfer
RemoveFromPot3Success == \E trf \in DOMAIN transfers :
    /\ trf.op = "SuccessTransferRFP"
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

\* part of the RemoveFromPot method after failed transfer
RemoveFromPot3Failure == \E trf \in DOMAIN transfers :
    /\ trf.op = "FailureTransferRFP"
    \* roll back the transaction and restore the pot
    /\ pot' = pot + trf.arg
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
    /\ state' = "DECIDING_BET"
    /\ transfers' = BagAdd(transfers, [op |-> "TransferPW", arg |-> 2*bet])
    /\ UNCHANGED <<secret, guess, bet, wallet, operatorFunds, playerFunds>>

\* transfer method called from PlayerWins: successful execution
PlayerWins2Success == \E trf \in DOMAIN transfers :
    /\ trf.op = "TransferPW"
    \* transfer can succeed only if the casino account holds enough money
    /\ wallet["casino"] >= trf.arg
    /\ wallet' = [wallet EXCEPT !["player"] = @ + trf.arg,
                                !["casino"] = @ - trf.arg]
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           [op |-> "SuccessTransferPW", arg |-> trf.arg])
    /\ UNCHANGED <<state, secret, guess, pot, bet, operatorFunds, playerFunds>>

\* transfer method called from PlayerWins: failing execution
PlayerWins2Failure == \E trf \in DOMAIN transfers :
    /\ trf.op = "TransferPW"
    /\ transfers' = BagAdd(BagRemove(transfers, trf), 
                           [op |-> "FailureTransferPW", arg |-> trf.arg])
    /\ UNCHANGED <<state, secret, guess, pot, bet, wallet, operatorFunds, playerFunds>>

\* part of PlayerWins after successful transfer
PlayerWins3Success == \E trf \in DOMAIN transfers :
    /\ trf.op = "SuccessTransferPW"
    /\ bet' = 0
    /\ state' = "IDLE"
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<secret, guess, pot, wallet, operatorFunds, playerFunds>>

\* part of PlayerWins after failed transfer
PlayerWins3Failure == \E trf \in DOMAIN transfers :
    /\ trf.op = "FailureTransferPW"
    /\ pot' = pot + bet  \* restore pot
    /\ state' = "BET_PLACED"  \* restore state of the contract
    /\ transfers' = BagRemove(transfers, trf)
    /\ UNCHANGED <<secret, guess, bet, wallet, operatorFunds, playerFunds>>

OperatorWins ==
    /\ pot' = pot + bet
    /\ wallet' = wallet
    /\ bet' = 0
    /\ state' = "IDLE"
    /\ UNCHANGED <<transfers, secret, guess, wallet, operatorFunds, playerFunds>>

DecideBet ==
    \* This action corresponds to the invocation of `decideBet`.
    \* If the secret was guessed correctly, we initiate PlayerWins, otherwise OperatorWins
    /\ state = "BET_PLACED"
    /\ \/ guess = secret /\ PlayerWins1
       \/ guess # secret /\ OperatorWins

Next ==
    \/ \E amount \in Ether : AddToPot(amount)
    \/ \E amount \in Ether : RemoveFromPot1(amount)
    \/ RemoveFromPot2Success \/ RemoveFromPot2Failure
    \/ RemoveFromPot3Success \/ RemoveFromPot3Failure
    \/ \E _secret \in {Heads, Tails} : CreateGame(_secret)
    \/ \E amount \in Ether, _guess \in {Heads, Tails} : PlaceBet(amount, _guess)
    \/ DecideBet 
    \/ PlayerWins2Success \/ PlayerWins2Failure 
    \/ PlayerWins3Success \/ PlayerWins3Failure

\* Require weak fairness for DecideBet and for the PlayerWins3 actions.
\* We still need strong fairness for PlayerWins2Success so that a non-cooperative
\* player cannot block the casino. However, we don't need fairness for the
\* other transfer actions because they cannot block the PlayerWins actions
\* due to the bag data structure.
Fairness == 
    /\ WF_vars(DecideBet) 
    /\ SF_vars(PlayerWins2Success) 
    /\ WF_vars(PlayerWins3Success) /\ WF_vars(PlayerWins3Failure)

Spec == Init /\ [][Next]_vars /\ Fairness

\* No money is created ot lost
Inv == 
    wallet["operator"] + wallet["player"] + wallet["casino"] 
    = operatorFunds + playerFunds

\* Liveness: whenever a bet is placed, it will eventually be resolved.
Liveness == (state = "BET_PLACED") ~> (state = "IDLE")

===============================================================================
