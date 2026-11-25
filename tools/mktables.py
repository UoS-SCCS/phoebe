#!/usr/bin/env python3
"""Summarise the outputs written by reproduce.sh (directory results/).

Prints (1) one row per check: id, model, property, states, selected states,
outcome, time; (2) the original options with their outcome and time; (3) the
comparison of the two knowledge oracles.  With --latex the rows are printed
as LaTeX table rows.
"""
import os, re, sys
R = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else 'results'
latex = '--latex' in sys.argv
times = {}
for line in open(os.path.join(R, 'times.txt')):
    parts = line.split()
    times['_'.join(parts[:-1])] = parts[-1].rstrip('s')
def out(name):
    return open(os.path.join(R, name + '.out'), encoding='utf-8').read()
def row(cells):
    print(' & '.join(cells) + ' \\\\' if latex else '  '.join(cells))
ids = [n[:-4] for n in sorted(os.listdir(R)) if re.fullmatch(r'(S|D|AK[GAF])\d+\.out', n)]
ids.sort(key=lambda i: (('S', 'D', 'A').index(i[0]), ('G', 'A', 'F').index(i[2]) if i[0] == 'A' else 0, int(re.sub(r'\D', '', i))))
print('== checks ==')
bad = 0
for i in ids:
    f = [x.strip() for x in out(i).split('\n')[0].split(' | ')]
    st = re.search(r'states=(\d+) selected=(\d+)', f[4])
    if f[3] != 'as expected': bad += 1
    row([i, f[0].split('] ')[1], f[1], st.group(1), st.group(2), f[2], f[3], times[i]])
print('checks: %d, unexpected outcomes: %d, total time: %.1f s'
      % (len(ids), bad, sum(float(times[i]) for i in ids)))
print('== original options ==')
for o in '1 2 a b c d e f A B C D F1 F2 F3 F4 H1 H2'.split():
    row([o, 'attack' if out(o).startswith('Just') else 'none', times[o]])
print('== knowledge oracle: pairwise scan vs bucketed ==')
for o in 'H1 H2 F1 F2'.split():
    row([o, times[o], times[o + '+'], 'same output' if out(o) == out(o + '+') else 'DIFFERENT OUTPUT'])
for n in sorted(os.listdir(R)):
    m = re.fullmatch(r'pairwise_(\w+)\.out', n)
    if m:
        i = m.group(1)
        row([i, times['pairwise_' + i], times[i], 'same output' if out(i) == out('pairwise_' + i) else 'DIFFERENT OUTPUT'])
