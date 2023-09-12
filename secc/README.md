# Casino Specification and Verification Challenge: SecC Solution

This folder contains the solution to the [Casino challenge of VerifyThis](https://verifythis.github.io/casino/),
showcasing two specific features of the verification tool used, [SecC](https://bitbucket.org/covern/secc/),
and this case study is part of its [regression tests](https://bitbucket.org/covern/secc/src/master/examples/case-studies/).

SecC and this case study are licensed under BSD 3-clause (see `LICENSE`).

## Description

The artifact consists of two files

- `casino.c`: full solution
- `casino-statemachine.c` a simplified model that models the high-level state-transitions only

We describe `casino.c` only.

It first defines a logical model of blockchain contracts and and general state, specifically, the type of `address`es, and resource predicates for `account`s and `payment`s, and some functions that can be used to compute with these resources.

Next, the Casino state is defined as a `struct casino`,
which together with the address `self` of the corresponding smart contract
satisfies the invariants expressed by predicate `game`.

The main steps of the game and the respective transitions are implemented by functions `init`, `add_to_pot`, `remove_from_pot`, `create_game`, `place_bet`, and `decide_bet`.

Function `sequential_game` models how the overall game is played out in terms of a loop that chooses the next actions nondeterministically. This outer loop also orchestrates the transfer of resources and makes explicit the decision of the operator to disclose the winning bet (assumption `secret :: low`).

## Repeat the Verification

### Requirements

Dependencies of SecC

- Java (tested with various versions >= 8)
- `z3` command line binary (tested with various versions >= 4.4.0)

Supported Platforms

- Linux (tested with various Ubuntu versions >= 16.04 and current Arch)
- Mac OS (tested with 10.13 and 10.14)

### Download and compile SecC (requires Java):

    git clone https://bitbucket.org/covern/secc/
    cd secc
    make      # takes about one minute
    make test # optional, takes about two minutes


## Verify the Casino case study

    ./SecC.sh ../casino.c

Expected output (timing may vary)

    ../casino.c
    init ...   success ❤ (time 344ms)
    add_to_pot ...   success ❤ (time 180ms)
    remove_from_pot ...   success ❤ (time 232ms)
    create_game ...   success ❤ (time 186ms)
    place_bet ...   success ❤ (time 234ms)
    decide_bet ...   success ❤ (time 383ms)
    sequential_game ...   success ❤ (time 1922ms)

