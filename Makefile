all : upi.pdf

upi.pdf: upi.tex upi.bbl entcs*
	latexmk -pdf upi.tex

cont: continuous

continuous:
	latexmk -pvc -pdf -interaction=nonstopmode upi.tex

clean:
	latexmk -C upi.pdf

.PHONY: all clean continuous
