# TLA+ Solution for the Casino Challenge

This folder contains the solution to the [Casino challenge of VerifyThis](https://verifythis.github.io/casino/),
showcasing the specification with [TLA+](). The files are licensed under BSD 3-clause (see `LICENSE`).

## Description

The artifact consists the one TLA+ file `Casino.tla`, and the pretty-printed version `Casino.pdf`. 

It first defines a logical model of blockchain contracts and and general state, specifically, the type of `address`es, and resource predicates for `account`s and `payment`s, and some functions that can be used to compute with these resources.

Next, the Casino state is defined as a `struct casino`,
which together with the address `self` of the corresponding smart contract
satisfies the invariants expressed by predicate `game`.

The main steps of the game and the respective transitions are implemented by functions `init`, `add_to_pot`, `remove_from_pot`, `create_game`, `place_bet`, and `decide_bet`.

Function `sequential_game` models how the overall game is played out in terms of a loop that chooses the next actions nondeterministically. This outer loop also orchestrates the transfer of resources and makes explicit the decision of the operator to disclose the winning bet (assumption `secret :: low`).

## Repeat the Verification

### Requirements

Dependencies of TLA+. There are two environments for writing TLA+ specifications. You use the Eclipse-based IDE ([The Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html)), or the newer [VSCode environment](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) (building upon language server protocol).

In both cases, a recent Java is required.


### Download and compile SecC (requires Java):

    git clone https://bitbucket.org/covern/secc/
    cd secc
    make      # takes about one minute
    make test # optional, takes about two minutes
