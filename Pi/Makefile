AGDA_SRCS = $(shell find . -type f -name '*.agda')
AGDA_BINS = $(subst .agda,.agdai,$(AGDA_SRCS))

all: Everything.agdai
reallyall: $(AGDA_BINS)

%.agdai: %.agda
	agda $<

todos: $(AGDA_SRCS)
	find . -type f -name '*.agda' \
		-not -path './Experiments/*' -not -path './FSMG/*' \
		-exec grep -E -n --colour=auto 'TODO' {} \+

clean:
	rm -f $(AGDA_BINS)

.PHONY: all clean
