GOAL = sub

html: out/$(GOAL).html

pdf: out/$(GOAL).pdf

upload: out/main/index.html
	rsync -avz --chmod a+rX out/main \
	  login.eecs.northwestern.edu:public_html/course/type-systems

out/main/index.html: main.scrbl $(wildcard *.scrbl) util.rkt
	raco make -j 4 $<
	scribble --style notes.css --dest out --htmls ++convert svg $<

out/%.html: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --style notes.css --dest out --html ++convert svg $<

out/%.pdf: %.scrbl util.rkt
	raco make -j 4 $<
	scribble --dest out --pdf $<

.PHONY: html pdf upload
