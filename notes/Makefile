# Chapter to build for `make one`
GOAL    = lcube

# Build products
HTMLDIR = out/type-notes
HTML    = $(HTMLDIR)/index.html
PDF     = out/type-notes.pdf

# Source files
SRCS    = $(wildcard *.scrbl) $(wildcard redex/*.rkt)

# How to run `scribble`
SCRBL   = scribble --dest out

html: $(HTML)
one: out/$(GOAL).html
pdf: $(PDF)

out/%/index.html: compiled/%_scrbl.zo
	$(SCRBL) --htmls ++convert svg $*.scrbl

out/%.html: compiled/%_scrbl.zo
	$(SCRBL) --html ++convert svg $*.scrbl

out/%.pdf: compiled/%_scrbl.zo prefix.tex
	$(SCRBL) --xelatex --prefix prefix.tex $*.scrbl

compiled/%_scrbl.zo: %.scrbl $(SRCS) util.rkt
	raco make -j 4 $<

upload: $(HTML) $(PDF)
	rsync -avz --delete --chmod a+rX \
	  $(HTMLDIR) $(PDF) \
	  web1.cs.northwestern.edu:public_html/course/type-systems-wi18/

dist: $(HTML)
	cp -r $(HTMLDIR)/* ~/public_html/courses/496-2025-fall/

.PHONY: html one pdf upload
