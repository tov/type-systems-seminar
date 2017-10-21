doc: let-nl.scrbl
	raco make -j 4 $<
	scribble --dest doc --html ++convert svg $<

pdf: let-nl.scrbl
	raco make -j 4 $<
	scribble --dest doc --pdf $<

.PHONY: doc pdf
