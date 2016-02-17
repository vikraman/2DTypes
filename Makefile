all : frac.pdf

frac.pdf : latex/frac.tex
	pdflatex latex/frac.tex

latex/frac.tex : frac.lagda
	agda --allow-unsolved-metas --latex -i . -i $(AGDALIB) frac.lagda


