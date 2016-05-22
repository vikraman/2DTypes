all : popl.pdf

popl.pdf : popl.tex
	pdflatex popl.tex

popl.tex : popl.lagda pibackground.tex groupoid.tex pifrac.tex
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library popl.lagda

pibackground.tex : pibackground.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library pibackground.lagda

groupoid.tex : groupoid.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library groupoid.lagda

pifrac.tex : pifrac.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library pifrac.lagda

clean:
	rm -f *.{aux,bbl,bcf,blg,fdb_latexmk,fls,flx,ilg,lof,log,lop}	\
	*.{lot,nlg,nlo,nls,pdf,pdf_tex,ptb,pyg,out,run.xml,toc}		\
	*-{blx.bib}

.PHONY: all clean
