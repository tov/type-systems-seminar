GOAL = lcube

one: out/$(GOAL).html

all: out/main/index.html

SRCS = $(wildcard *.scrbl) $(wildcard redex/*.rkt)

out/main/index.html: main.scrbl $(SRCS) util.rkt
	raco make -j 4 $<
	scribble --style notes.css --dest out --htmls ++convert svg $<

out/%.html: %.scrbl redex/%.rkt util.rkt
	raco make -j 4 $<
	scribble --style notes.css --dest out --html ++convert svg $<

upload: out/main/index.html
	rsync -avz --delete --chmod a+rX out/main \
	  web1.cs.northwestern.edu:public_html/course/type-systems-wi18/

.PHONY: all one upload
