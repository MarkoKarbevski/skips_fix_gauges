"""Check that a paper's main text defines every term and symbol before it uses it.

Usage: python3 check_flow.py paper.tex [glossary.py] [allow.txt]

Exit code 1 when a use before definition is flagged that allow.txt does not accept
(one accepted term name per line, then " # reason").

The main text (from \\begin{abstract} to \\appendix) is split into reading units:
paragraphs, displays, statements and captions, in source order. Floats are reported with
their source position and flagged, because the reader may meet them earlier or later.

A term counts as defined in the unit where it appears inside \\emph{...}, or where a
glossary entry's definition pattern matches. For every term and symbol, the script prints
the first unit that uses it and the unit that defines it, and flags a use that comes first.
It also writes the flow graph (unit -> defines / uses) as Markdown next to the paper.
"""
import re, sys, os, importlib.util

def load_units(tex):
    m0 = tex.index('\\begin{abstract}')
    m1 = tex.index('\\appendix')
    body = tex[m0:m1]
    # A drawing is replaced by a placeholder, so that a reader of the units knows that it exists.
    body = re.sub(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}', '[a TikZ drawing, omitted here; the caption describes it]', body, flags=re.S)
    body = re.sub(r'(?m)^%.*$', '', body)
    units, sec = [], 'abstract'
    for raw in re.split(r'\n\s*\n', body):
        t = raw.strip()
        if not t:
            continue
        for m in re.finditer(r'\\(sub)?section\*?\{([^}]*)\}', t):
            sec = m.group(2)
        kind = 'para'
        if '\\caption' in t:
            kind = 'float'
        elif re.search(r'\\begin\{(restatable|theorem|proposition|lemma|remark|conjecture|definition)', t):
            kind = 'statement'
        units.append({'sec': sec, 'kind': kind, 'text': t})
    return units

def plain(t):
    t = re.sub(r'\\(cref|Cref|cpref|Cpref|rpref|ptlink|citep|citet|label|ref|eqref|specialof|proofin|followsfrom)\*?(\[[^\]]*\])?\{[^}]*\}(\{[^}]*\})?', ' ', t)
    return t

def main():
    path = sys.argv[1]
    tex = open(path).read()
    units = load_units(tex)
    gl = {'terms': [], 'symbols': []}
    if len(sys.argv) > 2:
        spec = importlib.util.spec_from_file_location('gl', sys.argv[2]); mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        gl['terms'] = getattr(mod, 'TERMS', []); gl['symbols'] = getattr(mod, 'SYMBOLS', [])
    # terms defined by \emph{...}
    emph = {}
    for i, u in enumerate(units):
        for m in re.finditer(r'\\emph\{([^{}]*)\}', u['text']):
            w = m.group(1).strip().lower()
            if 2 < len(w) < 40 and not w.startswith('\\') and '$' not in w:
                emph.setdefault(w, i)
    entries = []
    covered = {n.lower().rstrip('s') for n, _, _ in gl['terms'] + gl['symbols']}
    covered |= {n.lower().split(' ')[0].rstrip('s') for n, _, _ in gl['terms']}
    for w, i in emph.items():
        if w.rstrip('s') in covered or any(w.rstrip('s') in c for c in covered):
            continue
        stem = re.escape(w.rstrip('s'))
        entries.append((w, r'(?i)(?<![a-z])' + stem + r's?(?![a-z])', i))
    for name, use_pat, def_pat in gl['terms'] + gl['symbols']:
        d = next((i for i, u in enumerate(units) if re.search(def_pat, u['text'])), None)
        entries.append((name, use_pat, d))
    problems, graph = [], [[] for _ in units]
    for name, use_pat, d in entries:
        first = next((i for i, u in enumerate(units) if re.search(use_pat, plain(u['text']))), None)
        if first is None:
            continue
        graph[first].append(('uses', name))
        if d is not None:
            graph[d].append(('defines', name))
        if d is None:
            problems.append((first, name, 'never defined in the main text'))
        elif first < d:
            problems.append((first, name, 'used in unit %d, defined in unit %d (%s)' % (first, d, units[d]['sec'])))
    # The opening of the introduction hooks the reader in words: no formula in its first two paragraphs.
    intro = [i for i, u in enumerate(units) if u['sec'].lower() == 'introduction' and u['kind'] == 'para'
             and not u['text'].lstrip().startswith('\\section')][:2]
    for k, i in enumerate(intro):
        t = plain(units[i]['text'])
        if (k == 0 and '$' in t) or re.search(r'\$[^$]*(\(|\+|=|\\mapsto)[^$]*\$', t):
            problems.append((i, 'formula in the opening', 'a formula in the first paragraph of the introduction, or an expression in the second; say it in words'))
    problems.sort()
    allowed = {}
    if len(sys.argv) > 3:
        for line in open(sys.argv[3]):
            if line.strip() and not line.startswith('#'):
                name, _, why = line.partition('#')
                allowed[name.strip().lower()] = why.strip()
    print('%d units, %d entries checked' % (len(units), len(entries)))
    new = [pr for pr in problems if pr[1].lower() not in allowed]
    accepted = [pr for pr in problems if pr[1].lower() in allowed]
    if accepted:
        print('accepted, case by case: ' + '; '.join('%s (%s)' % (n, allowed[n.lower()]) for _, n, _ in accepted))
    problems = new
    print('FLOW CHECK: %d use(s) before definition to fix' % len(problems))
    for first, name, why in problems:
        u = units[first]
        snip = re.sub(r'\s+', ' ', u['text'])[:150]
        flag = ' [float: check where it renders]' if u['kind'] == 'float' else ''
        print('* %-28s %s%s\n    unit %d (%s, %s): %s' % (name, why, flag, first, u['sec'], u['kind'], snip))
    # Results graph: references to labels that the main text defines later.
    where = {}
    for i, u in enumerate(units):
        for m in re.finditer(r'\\label\{([^}]*)\}', u['text']):
            where.setdefault(m.group(1), i)
        for m in re.finditer(r'\\stpart\{([^}]*)\}\{([^}]*)\}', u['text']):
            if m.group(1):
                where.setdefault(m.group(1) + ':' + m.group(2), i)
    fwd = []
    for i, u in enumerate(units):
        for m in re.finditer(r'\\(?:cref|Cref|ref|eqref|autoref)\*?\{([^}]*)\}', u['text']):
            for lab in m.group(1).split(','):
                lab = lab.strip()
                if lab in where and where[lab] > i:
                    fwd.append((i, lab, where[lab]))
        for m in re.finditer(r'\\(?:cpref|Cpref|rpref|ptlink)\{([^}]*)\}\{([^}]*)\}', u['text']):
            lab = m.group(1) + ':' + m.group(2)
            if lab in where and where[lab] > i:
                fwd.append((i, lab, where[lab]))
    print('\nForward references inside the main text (unit -> label, defined in unit): pointer or premise?')
    for i, lab, j in fwd:
        u = units[i]
        print('  unit %d (%s, %s) -> %s (unit %d, %s)' % (i, u['sec'], u['kind'], lab, j, units[j]['sec']))
    out = os.path.splitext(path)[0] + '_flow.md'

    with open(out, 'w') as f:
        f.write('# Flow graph of the main text: what each unit defines and first uses\n\n')
        f.write('| Unit | Section | Kind | Defines | First uses | Start |\n|---|---|---|---|---|---|\n')
        for i, u in enumerate(units):
            defs = ', '.join(sorted(n for k, n in graph[i] if k == 'defines'))
            uses = ', '.join(sorted(n for k, n in graph[i] if k == 'uses'))
            start = re.sub(r'\s+', ' ', u['text'])[:70].replace('|', '/')
            f.write('| %d | %s | %s | %s | %s | %s |\n' % (i, u['sec'], u['kind'], defs, uses, start))
    print('flow graph written to', out)
    sys.exit(1 if problems else 0)

if __name__ == '__main__':
    main()
