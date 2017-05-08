# Jasmin Verifier

#### Description:
Tool to verify safety and security properties of the [Jasmin](https://github.com/jasmin-lang/) pre-assembly language.

#### Requirements:
* [Haskell Platform](https://www.haskell.org/platform/) (with GHC version >= 8.x)
* [Dafny](https://dafny.codeplex.com/) (only for verification)
* [Boogie](https://boogie.codeplex.com/) (only for verification)
* [Z3](https://z3.codeplex.com/) (only for verification)

#### Installation:
```
cabal sandbox init
cabal sandbox add-source packages/boogaman/*
cabal install boogaman
cabal install
```
#### Usage:
For usage instructions, see
```
cabal exec -- jasminv --help
```

#### Examples:

By default, the tool will typecheck and verify an input Jasmin program:
```
> jasminv examples/test.mil --verify=bothv
```

#### Tests:
For running tests, you can simply run:
```
cabal test
```
For nice test output, you can run instead:
```
cabal exec -- runhaskell tests/Tests.hs
```