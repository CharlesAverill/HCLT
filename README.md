# Haskell Curry's Living Thesis

 A Coq implementation of "Foundations of Combinatory Logic," the 1930 Ph.D. thesis written by Haskell Curry.

[Thesis Translation PDF](https://www.overleaf.com/read/rzhdyjvrzbgy)

## Building

```bash
coq_makefile -f _CoqProject $(find . -name "*.v") -o Makefile && make
make
```
