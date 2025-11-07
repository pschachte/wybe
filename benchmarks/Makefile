# Run all the benchmarks

BENCHMARKS = nrev primes queens

all:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b all; \
	done

test: all
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b test; \
	done

clean:
	@for b in $(BENCHMARKS); do \
	  $(MAKE) -C $$b clean; \
	done

.PHONY: all clean test