TARGETS = popl22-short.pdf popl22-slides.pdf hottest22-slides.pdf cl-logsem-slides.pdf
DEPS_DIR = .deps
LATEXMK = latexmk -recorder -use-make -deps -pdflua

all: $(TARGETS)

$(foreach file,$(TARGETS),$(eval -include $(DEPS_DIR)/$(file)-deps))

$(DEPS_DIR):
	mkdir $@

%.pdf: %.tex *.sty
	if [ ! -e $(DEPS_DIR) ]; then mkdir $(DEPS_DIR); fi
	$(LATEXMK) -deps-out=$(DEPS_DIR)/$@-deps $<

ExamplesS.tex: latex/Pi/Examples/ExamplesS.tex
	if [ ! -e ExamplesS.tex ]; then ln -s latex/Pi/Examples/ExamplesS.tex . ; fi

latex/Pi/Examples/ExamplesS.tex: ../Examples/ExamplesS.lagda
	agda --latex ../Examples/ExamplesS.lagda

clean:
	rm -rf .deps
	latexmk -c

distclean: clean
	latexmk -C

.PHONY: continuous clean distclean
