AGDA ?= agda
OPTS ?= --allow-unsolved-metas --latex -i . --latex-dir=.

all : fractypes.pdf

fractypes.pdf : fractypes.tex
	latexmk -pdf fractypes.tex

fractypes.tex : fractypes.lagda pibackground.tex groupoid.tex pifrac.tex opsem.tex limitations.tex appendix.tex
	$(AGDA) $(OPTS) fractypes.lagda
	perl postprocess-latex.pl fractypes.tex > fractypes.processed && \
	mv fractypes.processed fractypes.tex

pifrac.tex : pifrac.lagda
	$(AGDA) $(OPTS) pifrac.lagda

groupoid.tex : groupoid.lagda
	$(AGDA) $(OPTS) groupoid.lagda

opsem.tex : opsem.lagda
	$(AGDA) $(OPTS) opsem.lagda

limitations.tex : limitations.lagda
	$(AGDA) $(OPTS) limitations.lagda

appendix.tex : appendix.lagda
	$(AGDA) $(OPTS) appendix.lagda

clean:
	rm -f fractypes.pdf \
	*.{aux,bbl,bcf,blg,fdb_latexmk,fls,flx,ilg,lof,log,lop} \
	*.{lot,nlg,nlo,nls,pdf_tex,ptb,pyg,out,run.xml,toc} \
	*-{blx.bib}

.PHONY: all clean
