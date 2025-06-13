# An Improved TLA+ Solution for the Casino Challenge

The Casino challenge was proposed to the VerifyThis community as a long-term, collaborative problem that different formalisms and tools could be used for. It concerns a smart contract, written in the Solidity language, where an operator can set up an online casino and players can bet money.

Different solutions to the challenge have been proposed and are available as a [Zenodo archive](https://doi.org/10.5281/zenodo.10258563), including a solution written in [TLA+](https://lamport.azurewebsites.net/tla/tla.html). Unfortunately, that solution contains multiple issues with the use of TLA+ and relating to the way the challenge is modeled. As a result, no properties can be verified, incorrectly attributed to limitations of the TLA+ verification tools by the authors. Even when the errors are corrected, the specification describes a highly simplified representation of the Solidity contract. In particular, if code calls the transfer method for transferring Ether between accounts, its effect is modeled as occurring atomically as part of the method invoking transfer, which does not correspond to the semantics of the Solidity language.

The TLA+ specifications proposed here are intended to remedy the weaknesses of the existing solution.

## The NaiveCasino specification

This is essentially a version of the specification available in the Zenodo archive, with corrections and completions. Since the agent in charge of invoking the different methods is fixed, the sender parameter has been removed from the actions modeling the methods of the Solidity contract. An address (in the sense of Solidity) for the casino has been added, with its own wallet. As in the existing specification, the effect of the transfer method has been inlined into the action definitions, corresponding to the simplifying assumption that it takes part within the atomic step of the calling method. An attractive feature of this model is that in the case of failure of transfer, Solidity will abort the transaction corresponding to the enclosing method. Such an aborted transaction is represented as a stuttering transition in TLA+, which is always allowed. Therefore, only successful transactions need to be modeled explicitly.

Besides type correctness, an additional invariant and a liveness property asserting that once a bet has been placed, the bet will eventually be decided (and the casino will revert to the idle state) have been added.

The MCNaiveCasino specification instantiates NaiveCasino and allows the user to bound the maximum amount of ether that is available, resulting in a finite state space. The possible initial states are determined based on choosing initial funds for both the operator and the player such that the overall bound on the ether is not exceeded. Both invariants and the liveness property asserted in the general specification are successfully verified by TLC.

## The NonAtomicCasino specification

This specification models invocations of the transfer method as separate atomic actions. For example, the RemoveFromPot action is divided up in three actions, the first one modeling the part of the method before the invocation of transfer, the second one the effect of the transfer method (which may non-deterministically succeed or fail), and the third one the part of the RemoveFromPot action following the invocation of transfer (which consists in aborting the transaction in the case of failure). Although transfer is modeled non-atomically, it is not reentrant, in the sense that for example, RemoveFromPot cannot be invoked while a transfer initiated by RemoveFromPot is in progress. The same properties as for the NaiveCasino specification are defined.

The corresponding MCNonAtomicCasino specification again allows the specification to be analyzed using TLC for bounded state spaces. It reveals several issues with this specification:

- Because intermediate states of methods are revealed when transfer is called, invariants may be temporarily violated. Notably, the typing invariant asserting that the value held in the pot does not exceed the maximum ether value fails when AddToPot is invoked while a transfer invoked from a preceding RemoveFromPot is in progress. A similar problem occurs with the invariant stating that the wallet of the casino holds the sum of the pot and the bet.

- Although the above are warning signals indicating that the environment may observe casino states that do not correspond to the stated invariants, one may be tempted to repair the properties by weakening them appropriately during transient states, cf. the definition of MCTypeOK. Checking this property reveals a more serious error due the pot holding a negative value for a certain interleaving.

- Finally, the liveness property also fails due to an execution in which the attempt to transfer the payout to the player fails repeatedly. (This corresponds to the problem identified in the Supremica solution.) However, given that the specification already violates essential safety property, this failure may be considered somewhat irrelevant.

## The FixedNonAtomicCasino specification

Finally, FixedNonAtomicCasino adjusts the implementation of the smart contract so that no inconsistent state can be observed by the environment. For example, the adjustment of the money in the pot takes place before transfer is invoked. The fairness hypothesis is strengthened by assuming that repeated attempts to transfer the payout to the player must eventually succeed. (In particular, this rules out "denial of service" attacks by the player against the casino.) Properties analogous to the ones asserted for the preceding specifications are defined: the invariant relating the casino's wallet to the values of pot and bet needs quite a delicate adjustment.

As before, the MCFixedNonAtomicCasino is the version to be used for analyzing the specification over bounded state spaces. All asserted properties are verified. Verification takes around 50 seconds on a M3Pro MacBook Pro, with 70% of that time spent for checking the liveness property, for a bound of 10 on the overall amount of ether available.


## Going further

As mentioned above, whereas the transfer method is now modeled as a separate atomic action, the methods invoking it are not reentrant, although different methods can be invoked when a transfer is pending. For example, AddToPot or CreateGame can be called during a transfer invoked from RemoveFromPot. Modeling fully reentrant behavior would require storing pending operations in a bag and would be an interesting exercise.

In a different dimension, one could verify the properties stated in FixedNonAtomicCasino using the interactive proof assistant TLAPS for TLA+, given that good confidence in its correctness has been reached with the help of TLC.
