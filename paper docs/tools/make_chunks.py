"""Split a paper's main text into numbered reading units for a progressive (prefix-only) review.

Usage: python3 make_chunks.py paper.tex out_dir

Writes out_dir/unit_001.tex, unit_002.tex, ... in reading order (the order of check_flow.py),
each with a header line naming its section and kind. A reviewer reads them strictly in order,
one file at a time, and judges unit N+1 with only units 1..N in mind.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_flow import load_units

def main():
    path, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    for f in os.listdir(out):
        if f.startswith('unit_'):
            os.remove(os.path.join(out, f))
    units = load_units(open(path).read())
    for i, u in enumerate(units, 1):
        head = '%% unit %d of %d | section: %s | kind: %s' % (i, len(units), u['sec'], u['kind'])
        if u['kind'] == 'float':
            head += ' | a float: it renders at the top of a page near this point'
        with open(os.path.join(out, 'unit_%03d.tex' % i), 'w') as f:
            f.write(head + '\n' + u['text'] + '\n')
    print('%d units written to %s' % (len(units), out))

if __name__ == '__main__':
    main()
