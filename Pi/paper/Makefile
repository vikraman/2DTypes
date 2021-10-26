TARGETS = main.pdf arxiv.pdf
DEPS_DIR = .deps
LATEXMK = latexmk -recorder -use-make -deps

all: $(TARGETS)
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: all
cont:
	$(MAKE) -B continuous

$(foreach file,$(TARGETS),$(eval -include $(DEPS_DIR)/$(file)P))

$(DEPS_DIR) :
	mkdir $@

%.pdf : %.tex ExamplesL.tex
	if [ ! -e $(DEPS_DIR) ]; then mkdir $(DEPS_DIR); fi
	$(LATEXMK) -pdf -deps-out=$(DEPS_DIR)/$@P $<

ExamplesL.tex: latex/Pi/Examples/ExamplesL.tex
	if [ ! -e ExamplesL.tex ]; then ln -s latex/Pi/Examples/ExamplesL.tex . ; fi

latex/Pi/Examples/ExamplesL.tex: ../Examples/ExamplesL.lagda
	agda --latex ../Examples/ExamplesL.lagda

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
