This directory contains an instrumentation of some translations of the article "The Next 700 Syntactical Models of Type Theory"
as Coq plugins.

Those plugins are very experimental, and should be considered as a proof of concept.


To compile the file, generate the Makefile using:
   coq_makefile -f _CoqProject -o Makefile

And then run:
    make

(compile with Coq 8.5).


Three of the translations have been instrumented:

* The intensional functions translation

Files: src/*Fun.*
Demo: TestFun.v


* The intensional types translation

Files: src/*Type.*
Demo: TestType.v


* The intensional streams translation

Files: src/*Stream.*
Demo: TestStream.v




Usage :

To add consistently add the axiom ax of type T use:
   Implement ax : T.

You then have to interactly prove the translation of T.
The term given by the proof will be nammed axᶠ.
The translation is then extended to ax by axᶠ.


To extend the translation to a constant c, use:
   Translate c.

If t is the body of c, it will add a new constant cᶠ of body the translation
of t, and extend the transltion to c by cᶠ.
