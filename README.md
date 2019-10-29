
# Typed Quantum Lambda Calculus

[![Build Status](https://travis-ci.com/Suikaba/SelingerQuantumLambdaCalculus.svg?token=CZn36eTofNZzqtf7H2em&branch=master)](https://travis-ci.com/Suikaba/SelingerQuantumLambdaCalculus)

## Syntax

### Term

```
M, N, P := c | x | fun x -> M | M N |
           (M, N) | * | let (x, y) = M in N |
           injl(M) | injr(M) | match P with x -> M | y -> N |
           let rec f x = M in N
c := new | meas | cnot | X | Y | Z
```

Some notations (Convention 1.3.2 in the paper "Quantum Lambda Calculus") are also implemented.

### Types

```
Type A, B ::= qbit | !A | (A -> B) | T | (A * B) | (A + B)
```

## Build & Run

```
dune exec qlambda
```

## Run tests

```
dune runtest
```

## License
This software is released under the MIT License, see LICENSE.


## References

- P. Selinger and B. Valiron. A lambda calculus for quantum computation with classical control. Mathematical Structures in Computer Science, pages 527--552, 2006.
- P. Selinger and B. Valiron. Quantum lambda calculus. In S. Gay and I. Mackie, editors, Semantic Techniques in Quantum Computation, pages 135--172. Cambridge University Press, 2009.
