GOAL = lcube

all: out/main/index.html

one: out/$(GOAL).html

pdf: out/main.pdf

SRCS = $(wildcard *.scrbl) $(wildcard redex/*.rkt)

MAIN_ZO = compiled/main_scrbl.zo

out/%/index.html: compiled/%_scrbl.zo
	scribble --style notes.css --htmls ++convert svg --dest out $*.scrbl

out/%.html: compiled/%_scrbl.zo
	scribble --style notes.css --html ++convert svg --dest out $*.scrbl

out/%.pdf: compiled/%_scrbl.zo
	scribble --xelatex --dest-name $@ $*.scrbl

compiled/%_scrbl.zo: %.scrbl $(SRCS) util.rkt
	raco make -j 4 $<

upload: out/main/index.html
	rsync -avz --delete --chmod a+rX out/main \
	  web1.cs.northwestern.edu:public_html/course/type-systems-wi18/

.PHONY: all one upload
