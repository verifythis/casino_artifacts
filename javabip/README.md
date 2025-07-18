# Artefact for the section Deductive Verification and Run-time Monitoring with Verified JavaBIP

## Directory structure

This artefact comprises the following directories and files

```
.
├── casinoAdjusted
│   ├── Casino.java
│   ├── Constants.java
│   ├── Main.java
│   ├── Operator.java
│   └── Player.java
├── casinoBroken
│   ├── Casino.java
│   ├── Constants.java
│   ├── Main.java
│   ├── Operator.java
│   └── Player.java
├── adjusted-report.json
├── broken-report.json
├── casinoAdjusted-trace.txt
├── casinoAdjusted-vercorsOutput.txt
├── casinoBroken-error-trace.txt
├── casinoBroken-vercorsOutput.txt
└── README.md
```

The two directories, `casinoBroken` and `casinoAdjusted` contain the
files composing the `JavaBIP` Casino model for the two versions
described in the paper:

- The `casinoBroken` version corresponds to the initial specification.
  It exposes the described faulty behaviour.
  
- The `casinoAdjusted` version corresponds to the specification with
  the additional guards eliminating the fault and allowing `VerCors` to
  prove all the invariants.

The files `Constants.java` are identical in both directories and are
not needed for the understanding of the models.

The remaining 6 files are as follows:

- The two `*-trace.txt` files show the `JavaBIP` execution traces of
  the two models.  The trace of the broken model is terminated by a
  Java ERROR, thrown by the `JavaBIP` run-time monitor upon an
  invariant violation.  The (infinite) trace of the adjusted model is
  truncated.
  
- The two `*-vercorsOutput.txt` files show the printouts of the
  `VerCors` verification of the two models.  The printout
  corresponding to the broken model highlights the invariants that
  could not be proven.  The printout corresponding to the adjusted
  model shows the information about the input model and states that
  the verification has completed successfully.
  
- The two `*-report.json` files provide the lists of the invariants,
  pre- and post-conditions that were proven by `VerCors` for the
  corresponding model.  (In the case of the adjusted model, all were
  proven.)

## Notes

The printout fragments in the paper were redacted for clarity and
compactness.  While we strived to stay as close as possible to the
actual printouts, some discrepancies might have been introduced in the
process.

Furthermore, for the sake of compactness, we have replaced three data
variables -- `OUTGOING_FUNDS`, `INCOMING_FUNDS`, and `AVAILABLE_FUNDS`
in both `JavaBIP` models -- by `FUNDS`.  It should be noted that we
could have done so directly in the models without affecting their
behaviour.  However, the models would be less readable.
