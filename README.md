# STLC with de Bruijn in Lean4
Simply Typed Lambda Calculus with de Bruijn indices in Lean4

The project is based on the paper "The Locally Nameless Representation" by Arthur Chargu´eraud. I mostly used his [Coq library](https://github.com/charguer/formalmetacoq) when I formalize the definitions in Lean4.

The two important parts of the library are:
1) We formalized the proof of confluence of the beta reduction in locally nameless syntax.
2) (Novel part) We proved and formalized that the beta reduction in locally nameless syntax is strongly normalizing.

Note: This work is a continuation of our project conducted in the Formalization of Mathematics (SLMATH) summer program, suggested by Jeremy Avigad. 

To use the library, Lean4 and mathlib library should be installed.
