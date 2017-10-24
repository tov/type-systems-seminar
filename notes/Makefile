out: out/poly.html

pdf: out/poly.pdf

out/%.html: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --dest out --html ++convert svg $<

out/%.pdf: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --dest out --pdf $<

.PHONY: out pdf
