# Run all the benchmarks

BENCHMARKS = nrev primes queens

all:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b all; \
	done

test:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b test; \
	done

stats:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b stats; \
	done

clean:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b clean; \
	done

.PHONY: all clean test stats