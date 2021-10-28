TARGETS = popl22-rev.pdf
DEPS_DIR = .deps
LATEXMK = latexmk -recorder -use-make -deps
PDFTK = pdftk

# Builds both full and stripped versions, counts the pages in the
# stripped version, then cuts that many pages from the full version
popl22-rev.pdf: main.pdf popl22-rev-strip.pdf
	$(eval NUMPAGES=$(shell $(PDFTK) popl22-rev-strip.pdf dump_data | grep NumberOfPages | grep -o -E '[[:digit:]]+'))
	@echo Number of pages in final version is: $(NUMPAGES)
	$(PDFTK) main.pdf cat 1-$(NUMPAGES) output popl22-rev.pdf

all: $(TARGETS)
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: all
cont:
	$(MAKE) -B continuous

$(foreach file,$(TARGETS),$(eval -include $(DEPS_DIR)/$(file)P))

$(DEPS_DIR) :
	mkdir $@

%.pdf : %.tex ExamplesL.tex inkscape/qis1.pdf inkscape/qis2.pdf
	if [ ! -e $(DEPS_DIR) ]; then mkdir $(DEPS_DIR); fi
	$(LATEXMK) -pdf -deps-out=$(DEPS_DIR)/$@P $<

ExamplesL.tex: latex/Pi/Examples/ExamplesL.tex
	if [ ! -e ExamplesL.tex ]; then ln -s latex/Pi/Examples/ExamplesL.tex . ; fi

latex/Pi/Examples/ExamplesL.tex: ../Examples/ExamplesL.lagda
	agda --latex ../Examples/ExamplesL.lagda

inkscape/%.pdf : inkscape/%.svg
	inkscape -D $< -o $@

arxiv.tar.gz: ExamplesL.tex arxiv.tex discussion.tex equivalence.tex \
				examples.tex finite.tex introduction.tex reversible1.tex ufin.tex \
				arxiv.bbl bu1.bbl *.sty *.tikzstyles *.png
	tar acvfL $@ $^

clean:
	latexmk -c
distclean: clean
	latexmk -C
	rm -rf .deps/

.PHONY: continuous clean distclean
