## File architecture

The file `Mimimal-Implementation.hs` contains the implementation of the elaboration algorithm described in section 7.
This is a minimal type theory, with no fancy features to emphasize the simplicity of the approach. This is building upon the minimal implementations of Kovács' [elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo).

The files in `src/` form a more advanced and complete implementation. Notably, we add datatypes and record types to the type theory. The file architecture is the following:

- `Main.hs`: main project file, calling the type-checking and evaluation function on the input
- `Evaluation.hs`: semantic domain and normalisation-by-evaluation (NbE) of the type theory
- `Conversion.hs`: Conversion checking (no holes and unification for simplicity)
- `Elaboration.hs`: Elaboration algorithm, including elaboration of datatypes descriptions
- `Parsing.hs` and `Printing.hs` : parsing and printing functions

## System Requirements

This project has been built and tested on:

+ `ghc` 9.10.3
+ `cabal-install` 3.16.1.0

To run the test script, you need to a POSIX-compatible shell.

## Compiling the project

To compile the project, run the following command :

```
cabal build
./test.sh
```

## Running the implementation

Once you have built the project as described above, you may execute it as follows:

```
cabal exec implem-fuss-free --
```

You should then see the following usage information:

```
usage: implem-fuss-free <mode> <filepath>
modes:
  nf <file>      : read & elaborate expression from file, print its normal form and type
  elab <file>    : read & elaborate expression from file, print output
  type <file>    : read & elaborate expression from file, print its type
```

To run one of the tests manually, do the following:

```
cabal exec implem-fuss-free -- elab test/pass/ex3
```

If you want to run all the test in a batch, you can use the helper bash script :

```
./test.sh
```
