# Introduction

This is a minimal implementation of cumulative universe hierarchies for dependent type theory. It uses a new syntax
to simplify the implementation, first described [here](https://www.jonmsterling.com/01HX/).

# File architecture

The main file is `Main.hs`, and contains the implementation of a minimal type theory, with no fancy features to emphasize
the simplicity of the approach. 

The file `Datatypes.hs` adds datatypes in the type theory, following Dagand's thesis *Cosmology of datatypes* and adapting it to the new system for universes.

# Compiling the project

To compile the project, run the following command :

```
cabal build
```

You can then run several tests provided in the directory `test/` using the following command:

```
cabal exec implem-fuss-free -- nf test/[choose a test]
```