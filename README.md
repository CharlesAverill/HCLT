# Haskell Curry's Living Thesis

 A Coq implementation of "Foundations of Combinatory Logic," the 1930 Ph.D. thesis written by Haskell Curry.

[Thesis Translation PDF](https://www.overleaf.com/read/rzhdyjvrzbgy)

## Navigation

- `Definitions` contains any Coq definitions of terms or concepts used in the thesis
    - [`constructor_combinators.ml`](Definitions/constructor_combinators.ml) is an OCaml scratchpad I use to test definitions before I strongarm them into Coq
- `Proofs` contains proofs from the thesis organized by part and chapter

## Building

```bash
coq_makefile -f _CoqProject $(find . -name "*.v") -o Makefile

make
```
