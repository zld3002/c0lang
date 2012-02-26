TEX = \
	l5.tex \
	thesis.tex \
	$(NULL)

#default: $(TEX:.pdf=.tex)
default: $(subst tex,pdf,$(TEX))

l4.pdf: l4gen.tex

l5gen.tex: l5.py proof.py
	python l5.py > l5gen.tex

l5.pdf: l5gen.tex l5proof.tex

thesis.pdf: cmuthesis.cls abstract.tex introduction.tex description.tex properties.tex runtime.tex stdlib.tex conclusion.tex appendix.tex libraries.tex l5gen.tex grammar.tex l5proof.tex *.c *.c0 *.h thesis.bib
thesis.pdf: thesis.bbl

libdoc.pdf: libraries.tex

%.bbl: %.tex %.bib
	latex $< # pdflatex doesn't draw the edges for some reason...
	bibtex $(subst tex,aux,$<)
	latex $<

%.pdf: %.tex lang_common.sty
	latex $<
	dvipdf $(subst tex,dvi,$<) $(subst tex,pdf,$<)

clean:
	rm -f *.pdf *.log *.aux *.dvi *~ tmp.tex *.lof *.lot *.toc *.out *.bbl *.brf

