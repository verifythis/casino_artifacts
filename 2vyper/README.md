# Casino Specification and Verification Challenge: 2vyper Solution

This folder contains two versions of the Casino smart contract for verification with 2vyper tool. 
Both versions contain the code from the original Solidity contract, rewritten in the Vyper lan-
guage, and modified to maintain all desired invariants. They differ only in their specifications:
- casino.vy is the version primarily discussed in the paper; its specification focuses on veri-
  fying the ownership of the Ether handled by the contract.
- casino_custom_resource.vy uses an additional custom resource representing a won bet to give
  additional guarantees to players.

To verify the code, simply run

        2vyper casino.vy

and analogous for the second version.
