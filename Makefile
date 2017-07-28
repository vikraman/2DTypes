AGDA_LATEX_OPTIONS = --latex --latex-dir=.
AGDA_QUICK_OPTIONS = --only-scope-checking

all : upi.pdf

upi.pdf: upi.tex upi.bbl entcs*
	latexmk -pdf upi.tex

upi.tex: upi.lagda
	agda $(AGDA_LATEX_OPTIONS) -i. upi.lagda

cont: continuous

continuous: upi.lagda
	(while inotifywait upi.lagda; \
	 do agda $(AGDA_LATEX_OPTIONS) $(AGDA_QUICK_OPTIONS) -i. upi.lagda; \
	 done &)
	latexmk -pvc -pdf -interaction=nonstopmode upi.tex

clean:
	latexmk -C upi.pdf
	rm -f upi.agdai

.PHONY: all clean continuous
