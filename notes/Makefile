doc: doc/stlc.html

pdf: doc/stlc.pdf

doc/%.html: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --dest doc --html ++convert svg $<

doc/%.pdf: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --dest doc --pdf $<

.PHONY: doc pdf
