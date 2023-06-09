# Haskell Curry's Living Thesis

 A Coq implementation of "Foundations of Combinatory Logic," the 1930 Ph.D. thesis written by Haskell Curry.

[Thesis Translation PDF](https://www.overleaf.com/read/rzhdyjvrzbgy)

## Navigation

- [`Definitions`](Definitions/) contains any Coq definitions of terms or concepts used in the thesis
    - [`constructor_combinators.ml`](Definitions/constructor_combinators.ml) is an OCaml scratchpad I use to test definitions before I strongarm them into Coq
- [`Proofs`](Proofs/) contains proofs from the thesis organized by part and chapter

## Contribution

I would greatly appreciate contributions! 
Any `Admitted` proofs are up for grabs, 
but I'll also accept proof simplifications 
or restructures.

Additionally, I want the code to read like 
a book or blog post. Documentation PRs 
are also kindly appreciated.

## Building

```bash
coq_makefile -f _CoqProject $(find . -name "*.v") -o Makefile

make
```
