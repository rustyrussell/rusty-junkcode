CCANDIR:=ccan
CFLAGS=-I$(CCANDIR) -Wall -g -O3
CCAN_OBJS:= $(CCANDIR)/ccan/err/err.o $(CCANDIR)/ccan/isaac/isaac64.o $(CCANDIR)/ccan/ilog/ilog.o $(CCANDIR)/ccan/opt/opt.o $(CCANDIR)/ccan/opt/usage.o $(CCANDIR)/ccan/opt/parse.o $(CCANDIR)/ccan/opt/helpers.o
OBJS:=test-trees.o maakutree.o spv.o

BINS := spv test-trees maakutree incremental-proof-tree
all: $(BINS)

$(CCAN_OBJS) $(OBJS): ccan/config.h

ccan/config.h: ccan/tools/configurator/configurator
	ccan/tools/configurator/configurator > $@

ccan/tools/configurator/configurator: ccan/tools/configurator/configurator.o

test-trees: test-trees.o $(CCAN_OBJS)

maakutree: maakutree.o

incremental-proof-tree: incremental-proof-tree.o $(CCAN_OBJS)

spv: spv.o

clean:
	$(RM) $(CCAN_OBJS) *.o $(BINS)

distclean: clean
	$(RM) ccan/config.h ccan/tools/configurator/configurator ccan/tools/configurator/configurator.o
