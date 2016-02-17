AGDALIB ?= /usr/share/agda-stdlib

all : frac.pdf

frac.pdf : frac.tex
	pdflatex frac.tex

frac.tex : frac.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(AGDALIB) frac.lagda

clean:
	rm -f *.{aux,bbl,bcf,blg,fdb_latexmk,fls,flx,ilg,lof,log,lop}	\
	*.{lot,nlg,nlo,nls,pdf,pdf_tex,ptb,pyg,out,run.xml,toc}		\
	*-{blx.bib}

.PHONY: all clean
