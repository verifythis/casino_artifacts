# Casino Specification and Verification Challenge: SecC Solution

This folder contains the version of the Casino smart contract used originally for verification with
the solc-verify tool. All functions are annotated with formal annotations in solc-verify's
specification language. Verification of the `decideBet` function fails because solc-verify takes
into account that the `transfer` function might fail. If error handling is corrected, verification
succeeds.
