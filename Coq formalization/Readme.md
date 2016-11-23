This directory contains the formalization of some results of the article "The Next 700 Syntactical Models of Type Theory".
This formalization heavily rely uppon a previous formalization of Vincent Siles and Hugo Herbelin which is avialable here:
http://www.lix.polytechnique.fr/~vsiles/coq/PTSATR.html
http://www.lix.polytechnique.fr/coq/pylons/coq/pylons/contribs/view/PTSATR/trunk


To compile the file, generate the Makefile using:
   coq_makefile -f _CoqProject -o Makefile

And then run:
    make

(compile with Coq 8.5).


Three of the translations have been formalized:

* The intensional functions translation

Source system: PTS.v
Target system: PTS_SigmaBool.v
Translation: tsl_functions.v


* The intensional types translation

Source system: PTS_Prop.v
Target system: PTS_SigmaBoolProp.v
Translation: tsl_types.v

Remark: we use an intermediate typing predicate defined in PTS_Prop_weakend.v

Remark: thining has been admitted, but only to show consistency preservation, which is quite direct.


* The intensional streams translation

Source system: PTS_Stream.v
Target system: PTS_SigmaBoolStream.v
Translation: tsl_Streams.v

Remark: Some basic axioms of De Bruijn indices manipulation and thining are still admitted in this translation
	as their formalization is tedious and, we think, not so interesting.
	You can check them using the command "Print Assumptions" at the end of the file tsl_Streams.v.
