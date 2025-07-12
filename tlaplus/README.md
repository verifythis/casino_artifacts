# A TLA+ Solution for the Casino Challenge

This folder contains the [TLA+](https://foundation.tlapl.us) solution to the [Casino challenge of VerifyThis](https://verifythis.github.io/casino/). 

## Specification AtomicCasino

This specification models each function of the smart contract by a TLA+ action. For functions that call Solidity's transfer method for transferring Ether between accounts, the effect of transfer is included in the step representing the enclosing function. This corresponds to the simplifying assumption that transfers occur as part of the atomic step of the function that they are called from. In the case of failure of transfer, Solidity will abort the transaction corresponding to the enclosing method. Such an aborted transaction is represented as a stuttering transition in TLA+, which is always allowed. Therefore, only successful transactions need to be modeled explicitly.

Besides type correctness, an additional invariant asserting that no Ether is created or lost during system executions, and a liveness property asserting that once a bet has been placed, the bet will eventually be decided and the casino will revert to the idle state, are expressed as TLA+ formulas.

The MCAtomicCasino specification extends module AtomicCasino and allows the user to bound the maximum amount of Ether that is available, resulting in a finite state space, which is amenable to verification by model checking. The possible initial states are determined based on choosing initial funds for both the operator and the player such that the overall bound on the ether is not exceeded. Both invariants and the liveness property are successfully verified by TLC in a few seconds.

## Specification NonAtomicCasino

This specification models invocations of the transfer method as separate atomic actions. For example, the RemoveFromPot action is divided into separate actions, the first one modeling the part of the method before the invocation of transfer, the second one the effect of the transfer method (with two variants depending on whether transfer succeeds or fails), and the third one the part of the RemoveFromPot action following the call to transfer (again in two variants). The account from which money is transferred must hold enough Ether for the transfer to succeed, and if the transfer fails, the enclosing transaction is rolled back. Pending calls to transfer are represented by the variable transfers of the TLA+ specification, which holds a sequence (stack) of ongoing transfer operations. The same properties as for the AtomicCasino specification are defined.

The corresponding MCNonAtomicCasino specification again allows the specification to be analyzed using TLC for bounded state spaces. It reveals several issues with this specification:

- Because intermediate states of methods are revealed when transfer is called, invariants may be temporarily violated. Notably, the typing invariant asserting that the value held in the pot does not exceed the maximum ether value fails when AddToPot is invoked while a transfer invoked from a preceding RemoveFromPot is in progress. The invariant stating that the wallet of the casino holds the sum of the pot and the bet is violated because the variables are not updated in a single atomic transition.

- Although the above are warning signals indicating that the environment may observe casino states that do not correspond to the stated invariants, they may be considered as unimportant, and one may be tempted to repair the properties by weakening them appropriately during transient states. The invariant RelaxedTypeOK is an attempt to do so, but checking this property reveals a more serious error due the pot holding a negative value for a certain interleaving.

- Finally, the liveness property also fails due to an execution in which the attempt to transfer the payout to the player fails repeatedly. In particular, a non-cooperative player may block progress of the system by refusing to accept payments. However, given that the specification already violates essential safety property, this failure may be considered somewhat irrelevant.

## Specification NonAtomicCasinoFixed

This specification adjusts the implementation of the smart contract so that the previously detected problems are avoided. For example, the adjustment of the money in the pot takes place before the invocation of transfer. The fairness hypothesis is strengthened by assuming that repeated attempts to transfer the payout to the player must eventually succeed. (In particular, this rules out "denial of service" attacks by the player against the casino.) Properties analogous to the ones asserted for the preceding specifications are defined, however the simple relationship between the money held by the casino and the local variables pot and bet no longer holds due to asynchronous modifications. Moreover, the value of pot may temporarily become negative when RemoveFromPot has been called (but not if the corresponding transfer succeeds).

As before, the MCNonAtomicCasinoFixed is the version to be used for analyzing the specification over bounded state spaces. In addition to limiting the amount of available Ether, it also includes a state constraint bounding the number of ongoing calls to transfer. All asserted properties are verified. Verification takes about 7 minutes on a M3Pro MacBook Pro for a bound of 5 on the amount of Ether and with at most 3 pending transfer operations.

## Specification NonAtomicCasinoFixedMT

This variant corresponds to a multi-threaded version of Solidity where the call stack of specification NonAtomicCasinoFixed is replaced by a bag (multiset) of entries that can be handled in any order. The same properties as before are successfully verified, resulting in a smaller state space due to different orders of method invocations no longer being distinguished.

## Repeat the Verification

The preferred IDE for using TLA+ is the Visual Studio Code Extension, which can be downloaded from the VSCode marketplace for Linux, MacOS, and Windows. From there, the TLC model checker can be invoked from the MC*.tla modules.

Alternatively, the TLA+ tools can be downloaded from [GitHub](https://github.com/tlaplus/tlaplus/releases). Download tla2tools.jar and run TLC using

  java -cp tla2tools.jar tlc2.TLC MCAtomicCasino   (and similar for the other MC* modules)

Specification NonAtomicCasinoFixedMT (and its MC variant) depends on the module BagsExt.tla from the [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules), which itself depends on Folds.tla. Although the Community Modules are bundled with the VS Code Extension, both modules necessary for this case study are included here in order to avoid external dependencies and simplify running TLC from the command line.

Verification times range from a few seconds for checking the atomic version or for finding errors in the non-atomic specification to several minutes for checking the fixed non-atomic specification, for the model sizes specified in the configuration files in this directory.

## Going further

Beyond model checking, TLA+ supports interactive theorem proving based on the [TLA+ Proof System](https://proofs.tlapl.us/). TLAPS could be used to prove the correctness of the properties asserted for the atomic specification or the fixed non-atomic specification.
