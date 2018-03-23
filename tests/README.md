## Test syntax

Tests in `tests/eval` specify their expected output as a comment:

    // EXPECT: 11

    5 + 6

Some tests are expected to fail (i.e., they test proofs
that should not succeed), which is also specified with a comment:

    // XFAIL: *
    FooA() { new () { bar(z) { 1 } } }
    FooB() { new () { bar(z) { 2 } } }
    FooA() ~ FooB()

Tests marked with XFAIL will still be run, but they *must* fail:
an error will be thrown if they succeed.

Other tests are simply not expected to work; those are marked with SKIP:

    // SKIP: dafny
    FooA() { new () { bar(z) { 1 } } }
    FooB() { new () { bar(z) { 2 } } }
    FooA() ~ FooB()

These tests will not even be run.
