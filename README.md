# Quivela

[![Build Status](https://travis-ci.org/awslabs/quivela.svg?branch=master)](https://travis-ci.org/awslabs/quivela) ![Apache-2.0](https://img.shields.io/badge/Licence-Apache%202.0-blue.svg)

Quivela is a prototype tool for proving the security of cryptographic protocols
(see an example proof in [`proofs/etm.sbl`](proofs/etm.sbl)),
developed by the AWS Automated Reasoning Group.

## Getting started

Quivela requires the following dependencies:

* Python 3 ([install](https://www.python.org/downloads/))
* Racket ([install](https://download.racket-lang.org/))
* Dafny ([install](https://github.com/Microsoft/dafny/wiki/INSTALL))
    * For Linux and Mac, you'll need to [install Mono](https://www.mono-project.com/download/stable/) first

### Setup

Check that you can run `racket -v` and `dafny`
(`racket.exe -v` and `Dafny.exe`, respectively, on Windows)
from the command line. On Windows, you might need to add these to your `PATH`.

Install Rosette (`raco` is Racket's package manager):

    $ raco pkg install rosette

Then from this repository's directory, run:

    $ pip3 install -r requirements.txt

to install the Python dependencies.

## Using Quivela

Quivela comes with two executables: `run.py` runs a Quivela program and prints
the output, while `prove.py` checks a proof and returns success or failure.

Both commands accept a `--backend` argument to specify which logical backend to use,
with two choices:

* `dafny` (default) uses Dafny to execute programs and check proofs. The Dafny
  backend is a deductive, unbounded verifier, but can require writing manual
  proof guidance.
* `rosette` uses Rosette to execute programs and check proofs. The Rosette
  backend is a bounded model checker, and so does not require writing manual
  proofs, but its verification results may be incomplete.

### Running a Quivela program

To run a Quivela program:

    $ python3 src/run.py tests/eval/test_method_call.sbl

Running this program should produce the following output:

    x = new () { get(y) { y };  };  ==> Ref(1)
    x.get(6) ==> 6

For each statement in the Quivela program, `run.py` prints the statement and
the value it evaluated to. This program first allocates a new object `x`,
and then calls `x`'s `get` method.

### Checking a Quivela proof

To check a Quivela proof:

    $ python3 src/prove.py tests/proofs/arg.sbl

Running this proof should produce the following output:

    Dafny 2.1.1.10209
    
    Dafny program verifier finished with 6 verified, 0 errors
    Program compiled successfully
    Running...
    
    Success!

This output indicates the proof succeeded.

### Debugging a failing proof

Consider the following failing proof:

    $ python3 src/prove.py tests/proofs/arg-fail.sbl

which produces the following (truncated) output:

    Dafny 2.1.1.10209
    [...]
    Dafny program verifier finished with 2 verified, 4 errors
    FAILED!

To debug why this proof is failing, we can use the Rosette backend to discover
a concrete counterexample:

    $ python3 src/prove.py --backend rosette tests/proofs/arg-fail.sbl

which produces this output:
    
    FAILED:
      FooA()
    ~
      FooB(2)
    
    could not prove equivalence. counterexample:
    | context 0:
    | this=1  nextAddr=2
    | * globals
    | * object 1 [methods: bar]
    |   * 'x = 1
    | context 1:
    | this=1  nextAddr=2
    | * globals
    | * object 1 [methods: bar]
    |   * 'x = 2
    method bar(0):
    * LHS returns 1
    * RHS returns 2
    | LHS context:
    | this=1  nextAddr=2
    | * globals
    | * object 1 [methods: bar]
    |   * 'x = 1
    | RHS context:
    | this=1  nextAddr=2
    | * globals
    | * object 1 [methods: bar]
    |   * 'x = 2
    * return values are not equal

    FAILED!

This output explains *why* the proof fails: when calling the method `bar` with
argument `0`, the two sides of the proof (`FooA()` and `FooB(2)`) return
different values (`1` and `2`), and so the two sides are not indistinguishable.

### Repairing a failing proof

Both `run.py` and `prove.py` accept an argument `-k`, which preserves the
generated backend program (Rosette or Dafny) for you to edit manually.

For example, running:

    $ python3 src/prove.py -k tests/proofs/arg-fail.sbl

produces this (truncated) output:

    Dafny 2.1.1.10209
    [...]
    Dafny program verifier finished with 3 verified, 2 errors
    FAILED!
      Script: <some path>/test-1fc33fd1.dfy

The file `test-1fc33fd1.dfy` contains the Dafny (or Rosette if that backend is used)
proof that fails. You can now edit that proof, and run `dafny` (or `racket`, respectively)
to see if your changes repair the proof. Because the generated proof includes
absolute references to the Quivela language definitions in `src/backend`,
you can also edit those and re-run the proof file to see changes.

## Running the tests

Quivela has a test suite covering both the language semantics (`tests/eval/`)
and proof techniques (`tests/proofs/`). To run the tests using the Dafny backend:

    $ make test-eval
    $ make test-proof

To run the tests using the Rosette backend:

    $ make test-eval BACKEND=rosette
    $ make test-proof BACKEND=rosette

## Limitations

The Dafny backend is not as feature-complete, nor as automated as the Rosette
backend (e.g., some tests are skipped for Dafny).
On the other hand, the Rosette backend functions only as a bounded
model checker, rather than a full unbounded verifier.
