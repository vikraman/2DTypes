all : upi.pdf

upi.pdf: upi.tex upi.bbl entcs*
	latexmk -pdf upi.tex

upi.tex: upi.lagda
	agda --latex -i . --latex-dir=. upi.lagda

cont: continuous

continuous: upi.lagda
	(while inotifywait -e close_write upi.lagda ; do agda --latex --latex-dir=. upi.lagda ; done &)
	latexmk -pvc -pdf -interaction=nonstopmode upi.tex

clean:
	latexmk -C upi.pdf
	rm -f upi.agdai

.PHONY: all clean continuous
