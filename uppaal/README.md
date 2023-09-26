# Casino Specification and Verification Challenge: UPPAAL Solution

This folder contains the UPPAAL models of the [Casino challenge of VerifyThis](https://verifythis.github.io/casino/). UPPAAL is available for download [here](https://uppaal.org/downloads/), the models were created with version 4.1.

## Description

There are four different models provided:

- `CasinoBase.xml`: Model of the initial, flawed contract, not considering reentrancy.
- `CasinoFixed.xml`: Model of a fixed contract where no over- or underflows can be provoked.
- `CasinoReentrant.xml`: Model of the initial, flawed contract, taking reentrancy into account.
- `CasinoReentrantFixed.xml`: Model of a fixed contract where all reentrant behavior is suppressed, and no over- or underflows can be provoked.

## Reproducing the Verification

Installation instructions for UPPAAL are available on the [UPPAAL website](https://uppaal.org/downloads/).

All four models can be opened from the UPPAAL GUI. They contain exemplary proprties that can be run directly from the `Verifier` tab.
