
## Description
This directory contains an instrumentation of three translations of CCω into itself as Coq plugins.

Those plugins rely on the Coq Forcing plugin available here :

https://github.com/CoqHott/coq-forcing/

They are very experimental, and should be considered as a proof of concept.


## Compilation
To compile the project, generate the Makefile using:

   `coq_makefile -f _CoqProject -o Makefile`

And then run:

    make

(compile with Coq 8.5).


## Description of files
Three of the translations have been instrumented:

* The intensional functions translation

Files: src/\*Fun.\*

Demo: TestFun.v


* The intensional types translation

Files: src/\*Type.\*

Demo: TestType.v


* The intensional streams translation

Files: src/\*Stream.\*

Demo: TestStream.v




## Use
To add consistently add the axiom ax of type T use:

   `Implement ax : T.`

You then have to interactly prove the translation of T.
The term given by the proof will be nammed axᶠ.
The translation is then extended to ax by axᶠ.


To extend the translation to a constant c, use:

   `Translate c`.

If t is the body of c, it will add a new constant cᶠ of body the translation
of t, and extend the transltion to c by cᶠ.
