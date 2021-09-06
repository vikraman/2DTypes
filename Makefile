SUBDIRS := Pi+ Pi/paper

all: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

dist:
	tar acvf Pi+.tar.gz Pi/Common/ Pi/Coxeter/ Pi/Indexed/ Pi/Lehmer/ Pi/NonIndexed/ Pi/UFin/ Pi/Extra.agda Pi/Misc.agda Pi/UFinLehmer2Equiv.agda

.PHONY: all dist $(SUBDIRS)
