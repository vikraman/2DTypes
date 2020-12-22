AGDA_SRCS = $(shell find Pi+ -type f -name '*.agda')
AGDA_BINS = $(subst .agda,.agdai,$(AGDA_SRCS))

all: $(AGDA_BINS)

%.agdai: %.agda
	agda $<

clean:
	rm -f $(AGDA_BINS)

.PHONY: all clean
