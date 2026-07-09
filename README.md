# File architecture

The file `Mimimal-Implementation.hs` contains the implementation of the elaboration algorithm described in section 7.
This is a minimal type theory, with no fancy features to emphasize the simplicity of the approach. This is building upon the minimal and optimised
implementations of Kovács, and especially of his [elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo).

The files in `src/` form a more advanced and complete implementation. Notably, we add datatypes and record types to the type theory. The file architecture is the following:

- `Main.hs`: main project file, calling the type-checking and evaluation function on the input
- `Evaluation.hs`: semantic domain and normalisation-by-evaluation (NbE) of the type theory
- `Conversion.hs`: Conversion checking (no holes and unification for simplicity)
- `Elaboration.hs`: Elaboration algorithm, including elaboration of datatypes descriptions
- `Parsing.hs` and `Printing.hs` : parsing and printing functions

# Compiling the project

To compile the project, run the following command :

```
cabal build
```

You can then run several tests provided in the directory `test/` using the following command:

```
cabal exec implem-fuss-free -- nf test/[choose a test]
```

If you want to run all the test in a batch, you can use the helper bash script :

```
./test.sh
```