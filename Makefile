CCANDIR:=ccan
CFLAGS=-I$(CCANDIR) -Wall -g -O3
CCAN_OBJS:= $(CCANDIR)/ccan/err/err.o $(CCANDIR)/ccan/isaac/isaac64.o  $(CCANDIR)/ccan/ilog/ilog.o
OBJS:=test-trees.o maakutree.o spv.o

BINS := spv test-trees
all: $(BINS)

$(CCAN_OBJS) $(OBJS): ccan/config.h

ccan/config.h: ccan/tools/configurator/configurator
	ccan/tools/configurator/configurator > $@

ccan/tools/configurator/configurator: ccan/tools/configurator/configurator.o

test-trees: test-trees.o maakutree.o ccan/ccan/isaac/isaac64.o ccan/ccan/err/err.o ccan/ccan/ilog/ilog.o

spv: spv.o

clean:
	$(RM) $(CCAN_OBJS) *.o $(BINS)

distclean: clean
	$(RM) ccan/config.h ccan/tools/configurator/configurator ccan/tools/configurator/configurator.o
