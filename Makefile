all : types.pdf

types.pdf : types.pdf
	pdflatex types.tex

types.tex : types.lagda pibackground.tex groupoid.tex pifrac.tex opsem.tex limitations.tex appendix.tex
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library types.lagda
	perl postprocess-latex.pl types.tex > types.processed && \
	mv types.processed types.tex

pifrac.tex : pifrac.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library pifrac.lagda

opsem.tex : opsem.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library opsem.lagda

limitations.tex : limitations.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library limitations.lagda

appendix.tex : appendix.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. -i $(CATLIB) -l standard-library appendix.lagda

clean:
	rm -f *.{aux,bbl,bcf,blg,fdb_latexmk,fls,flx,ilg,lof,log,lop}	\
	*.{lot,nlg,nlo,nls,pdf,pdf_tex,ptb,pyg,out,run.xml,toc}		\
	*-{blx.bib}

.PHONY: all clean
