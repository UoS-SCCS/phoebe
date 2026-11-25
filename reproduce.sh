#!/bin/bash
# Builds the tool and runs every check, every original option and the oracle
# comparisons.  Outputs go to results/<option>.out, times to results/times.txt.
# Compare with reference-results/ or summarise with:  python3 tools/mktables.py
set -e
cd "$(dirname "$0")"
export LANG=C.UTF-8 LC_ALL=C.UTF-8
make phoebe anbtest littest
mkdir -p results; : > results/times.txt
run() {
  name=$(echo "$*" | tr ' ' '_')
  s=$(date +%s.%N)
  ./phoebe "$@" > "results/$name.out" 2> /dev/null
  e=$(date +%s.%N)
  printf "%s %.2fs\n" "$*" "$(echo "$e - $s" | bc)" | tee -a results/times.txt
}
./anbtest | tail -1
./littest | sed -n 2,4p
for c in $(./phoebe list); do run "$c"; done
run sanity
for o in 1 2 a b c d e f A B C D F1 F2 F3 F4 H1 H2; do run "$o"; done
for o in H1+ H2+ F1+ F2+; do run "$o"; done
for o in AK1 AK2 AKP1 AKP2 AKA AKX AKNV AKPNV; do run "$o"; done
for c in S2 S7 S8 D2 D5 D7 D8 D11 D12 D13 D14 AKF3; do run pairwise "$c"; done
grep -h "UNEXPECTED" results/*.out && echo "SOME CHECK HAD AN UNEXPECTED OUTCOME" || echo "all checks as expected"
