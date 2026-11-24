# C programs used by the experiment scripts: `make -C experiments`
CFLAGS ?= -O2
PROGRAMS = bf2 census_8/wallscan sqrt_model/rowgen \
	three_heaps/chain3 three_heaps/stream3 three_heaps/cyc3 three_heaps/phi3 \
	column_periods/slab column_periods/cert column_periods/sprof column_periods/damage \
	column_periods/t3 column_periods/colring column_periods/torus column_periods/colbox

all: $(PROGRAMS)

%: %.c
	$(CC) $(CFLAGS) -o $@ $< -lm

clean:
	rm -f $(PROGRAMS)
.PHONY: all clean
