TARGETS = main.pdf
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

%.pdf : %.tex latex/Pi/Indexed/ExamplesL.tex
	if [ ! -e $(DEPS_DIR) ]; then mkdir $(DEPS_DIR); fi
	$(LATEXMK) -pdf -deps-out=$(DEPS_DIR)/$@P $<

latex/Pi/Indexed/ExamplesL.tex: ../Indexed/ExamplesL.lagda
	agda --latex ../Indexed/ExamplesL.lagda

clean:
	latexmk -c
distclean: clean
	latexmk -C
	rm -rf .deps/

.PHONY: continuous clean distclean
