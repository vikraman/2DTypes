SUBDIRS := Pi Pi/paper

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

dist:
	tar acvf Pi.tar.gz Pi/Common Pi/Coxeter Pi/Equiv Pi/Everything.agda Pi/Examples Pi/Experiments Pi/FSMG Pi/Lehmer Pi/Makefile Pi/README.md Pi/Syntax Pi/UFin

.PHONY: all dist $(SUBDIRS)
