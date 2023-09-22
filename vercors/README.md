# Casino Specification and Verification Challenge: VerCors Solution

This folder contains the [VerCors](https://vercors.ewi.utwente.nl/) solution to the [Casino challenge of VerifyThis](https://verifythis.github.io/casino/). 

## Description

In this solution, we verify the casino Solidity contract by translating it into an equivalent PVL program (`casino.pvl` in this same folder), and then annotating and verifying it with VerCors. PVL is VerCors own input prototypal language, very similar to Java. Annotations are contracts written in a combination of first order logic and permission based separation logic (for concurrency related properties).

In particular,  we include to safety invariants in `casino.pvl`:
  
- [A] The contract balance equals the sum of the pot and the bet. 
  
- [B] We always have enough money to pay the winner, this is, the pot is always at least the amount of the bet.

While invariant [B] is verified successfully, VerCors fails to verify invariant [A] for methods `removeFromPot` and `decideBet`. This is to be expected: the `transfer` method is payable and thus the balance of the contract changes when calling it. However, the contract accounting is only updated after returning from the alien call to `transfer`. If `transfer` is implemented in such a way that it calls back to the contract, then it will find the contract in a "violating" state. 


## Repeat the Verification

This verification can be repeated using VerCors version 1.4.0. VerCors can be run on Windows, Linux and Mac. Pre-compiled versions can be downloaded from https://github.com/utwente-fmt/vercors/releases/tag/v1.4.0. 

## Verify the Casino case study

You can repeat the results of the verification by running:

    vct --silicon casino.pvl

The verification time is around 10 seconds in a __2,3 GHz Quad-Core Intel Core i5__ equivalent machine.