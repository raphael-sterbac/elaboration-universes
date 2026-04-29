# Introduction

This is a minimal implementation of cumulative universe hierarchies for dependent type theory. It uses a new syntax
to simplify the implementation, first described [here](https://www.jonmsterling.com/01HX/).

# File architecture

The main file is `Main.hs`, and contains the implementation of a minimal type theory, with no fancy features to emphasize
the simplicity of the approach. 

The file `Unification.hs` adds holes in the type theory, and implements unification.

# Compiling the project

To compile the project, run the following command :

```
cabal v2-run implem-fuss-free
```