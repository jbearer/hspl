# hspl (coming soon)

[![Build Status](https://travis-ci.org/jbearer/hspl.svg?branch=master)](https://travis-ci.org/jbearer/hspl)
[![Coverage Status](https://coveralls.io/repos/github/jbearer/hspl/badge.svg?branch=master)](https://coveralls.io/github/jbearer/hspl?branch=master)

HSPL (Haskell Predicate Logic) is an embedded domain specific language that
brings logic programming to Haskell. HSPL uses resolution-based automated
theorem proving to make logical deductions, and will provide functionality
similar to that of logic programming languages like Prolog.

## Development

### Setup

1. Install [Stack](https://docs.haskellstack.org/en/stable/README/).
2. Pull the code:
```bash
git clone https://github.com/jbearer/hspl.git
cd hspl
```
3. Build the library:
```
stack build hspl
```
Or, to build all packages (including benchmarks):
```
stack build
```

### Unit tests

HSPL maintains a thorough suite of unit tests covering the library. To run,
```
stack test hspl
```

### Benchmarks

There are several benchmarks which can be used to assess the performance of HSPL by comparing the
running time of some example programs with that of comparable programs written in Prolog. To
simplify dependency management, each benchmark program lives in its own package. Common benchmarking
utilitiese are defined in the package `hspl-bench`. To build the utilities:

```
stack build hspl-bench
```

To run all benchmarks:
```
stack bench -j1 --dump-logs
```

Or, to run a specific benchmark:
```
stack bench <benchmark>
```

### Common plumbing tasks

#### Adding a new `Var` constructor

_In `Control.Hspl.Internal.Ast`_:

1. Add the constructor to the `data Var` definition.
2. Check if `alphaVar` in the `where` clause of `alphaEquivalent` needs to be updated. This will
   depend on the desired semantics of the new constructor. If necessary, update and add tests.

_In `Control.Hspl.Internal.Unification`_:

1. If necessary (depending on the desired semantics) update `freeIn` and its test case.
2. If necessary, update `mgu` and its test case.
3. If necessary, update `renameVar` and its test case.

_In `Control.Hspl`_:

1. If the new variable type is user-facing (as opposed to, say, `Fresh`, which is purely internal),
   add syntax for creating variables of this type, and add tests.

_In `Control.Hspl.Internal.UI`_:

1. Add a case in `formatVariable` and add a test.

_In `Bench` in package `hspl-bench`:_

1. Add a case to `genPrologTerm` to translate the variable to an analagous Prolog variable.

#### Adding a new `Goal` constructor

_In `Control.Hspl.Internal.Ast`_:

1. Add the constructor to the `data Goal` definition.
2. Add a case to the `Eq` instance for `Goal` and update the associated unit tests.

_In `Control.Hspl.Internal.Unification`_:

1. Add a case to `unifyGoal` and update the associated test.
2. Add a case to `renameGoal` and update the associated test.

_In `Control.Hspl.Internal.Solver`_:

1. Add a `Proof` constructor describing proofs of the new `Goal`.
2. Add a case to the `Eq` instance for `Proof` and update the test.
3. Add a case to the `Show` instance for `Proof`.
4. If the proof has any subproofs, add a case to `subProofs` in the `where` clause of `searchProof`.
5. Add a case to `matchGoal` in the `where` clause of `searchProof`.
6. Update tests for `searchProof`.
7. Add a method to `class MonadSolver` called `try<Constructor>`.
8. Add a function called `prove<Constructor>` which attempts to produce a proof of the new `Goal`,
   and define `try<Constructor> = prove<Constructor>` in the `MonadSolver` instance for `SolverT`.
   Add unit tests for `prove<Constructor>`.
9. Add a case to `Prove` which calls `prove<Constructor>`.

_In `Control.Hspl.Internal.Debugger`_:

1. Define the new method in the `MonadSolver` instance of `DebugSolverT`, and add example goals and
   traces to the test suite.

_In `Control.Hspl`_:

1. Define a predicate or a new syntactic primitive which users can use to create goals of the new
   type. Add tests that either check that the correct goal is created, or run a program that uses
   the new predicate and check the results, as appropriate.

_In `Control.Hspl.Internal.UI`_

1. Add a case to `formatGoal` which converts the new goal into a string consistent with the new
   syntax, and add a test case.
2. If the new syntax consists of a single token, add a `needsParens <NewGoal> = False` clause to
   `parensGoal`.
3. In the `parensGoal` test case, add an example of the new goal to either the list of goals which
   need parentheses, or the list of those which don't, as appropriate.

_In `Bench` in package `hspl-bench`:_

1. Add a case in `genPrologGoal` to translate the goal into an analagous Prolog goal.
