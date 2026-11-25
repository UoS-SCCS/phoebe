# Phoebe: build, test and reproduce.
#   make            build the model checker (./phoebe)
#   make test       build and run the two test programs
#   make tools      build the Alice-and-Bob code generator (./anbgen)
#   make reproduce  run every check and option into results/ (about 10 minutes)
#   make clean      remove build products
GHC      = ghc
GHCFLAGS = -O2 -isrc -iexamples -outputdir build
export LANG   = C.UTF-8
export LC_ALL = C.UTF-8

.PHONY: all test tools bench reproduce clean

all: phoebe

phoebe: Main.hs src/*.hs examples/*.hs
	$(GHC) $(GHCFLAGS) Main.hs -o phoebe

anbtest: tests/AnBTest.hs src/*.hs examples/*.hs
	$(GHC) $(GHCFLAGS) -outputdir build/anbtest tests/AnBTest.hs -o anbtest

littest: tests/LazyIntruderTest.hs src/*.hs
	$(GHC) $(GHCFLAGS) -outputdir build/littest tests/LazyIntruderTest.hs -o littest

anbgen: tools/AnBGen.hs src/*.hs
	$(GHC) $(GHCFLAGS) -outputdir build/anbgen tools/AnBGen.hs -o anbgen

lazyepi: tests/LazyEpi.hs src/*.hs examples/*.hs
	$(GHC) $(GHCFLAGS) -outputdir build/lazyepi tests/LazyEpi.hs -o lazyepi

test: anbtest littest
	./anbtest | tail -1
	./littest | sed -n 2,4p

tools: anbgen

bench: lazyepi

reproduce:
	./reproduce.sh

clean:
	rm -rf build results phoebe anbtest littest anbgen lazyepi
