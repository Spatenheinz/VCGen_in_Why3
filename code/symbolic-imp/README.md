# Symbolic IMP

Dependencies to build the interpreter:

- Why3 1.3.0 (or at least git commit 6cbc43d82)
- OCaml 4.04.0 or higher
- ZArith 1.7
- Alt-Ergo 2.2.0

Dependencies to replay the proofs:

- CVC4 1.6
- Alt-Ergo 2.2.0
- EProver 2.2

####################################

1) Replay the proofs by:

```shell
make replay
```

Other versions of the same provers may work, see the Why3 mechanism
for prover upgrade policy.

One extra lemma (not needed for the proof of the symbolic interpreter)
about the semantics requires Coq, preferably version 8.8.2


2) Extraction of executable and tests

Compilation needs the Alt-Ergo library for constraint solving. The
compilation will work with Alt-Ergo 2.2.0 (but not 2.3.0 so far)

Extract and compile the extracted code with

```shell
make
```

and run tests with

```shell
./interp.native
```
