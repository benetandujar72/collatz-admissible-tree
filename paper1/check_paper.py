"""check_paper.py — structural + citation audit for paper1/main.tex.

1. LaTeX environment/brace balance.
2. Every \lean{...} name cited in the paper must exist in the Lean corpus
   (as a theorem/def/abbrev/structure declaration or as a module file name).
"""
import re, io, glob, os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
tex = io.open(os.path.join(HERE, 'main.tex'), encoding='utf-8').read()

# 1. structural checks
beg = re.findall(r'\\begin\{(\w+)\}', tex)
end = re.findall(r'\\end\{(\w+)\}', tex)
cb, ce = Counter(beg), Counter(end)
bad = {k for k in cb | ce if cb[k] != ce[k]}
print("env balance:", "OK" if not bad else "MISMATCH %s" % bad)
nb, ne = tex.count('{'), tex.count('}')
print("brace balance:", "OK" if nb == ne else "MISMATCH {=%d }=%d" % (nb, ne))

# 2. lean-name audit
names = set()
for m in re.findall(r'\\lean\{([^}]*)\}', tex):
    m = m.replace('\\_', '_').replace('\\#', '#')
    for part in re.split(r'[,]', m):
        part = part.strip().rstrip('.')
        if not part or part.startswith('#'):
            continue
        # expand A/B shorthand: Cert_m1_Q8/Q10_S216_Barrier, collatz_no_cycle_below_359/16266
        if '/' in part:
            head, tail = part.split('/', 1)
            names.add(head)
            prefix = head.rsplit('_', 1)[0] if '_' in head else ''
            # try substituting the last token
            m2 = re.match(r'(.*_)([^_]+)$', head)
            if m2:
                names.add(m2.group(1) + tail.split('_')[0])
        else:
            names.add(part)

corpus = ""
for f in glob.glob(os.path.join(ROOT, 'CollatzLean4', 'CollatzLean4', '*.lean')):
    corpus += io.open(f, encoding='utf-8').read()
modules = {os.path.basename(f)[:-5]
           for f in glob.glob(os.path.join(ROOT, 'CollatzLean4', 'CollatzLean4', '*.lean'))}

missing = []
for n in sorted(names):
    base = n.replace('.lean', '')
    if base in modules:
        continue
    pat = re.compile(r'\b(theorem|def|abbrev|structure|class|inductive)\s+'
                     + re.escape(base) + r'\b')
    if pat.search(corpus):
        continue
    tail = base.split('.')[-1]
    if re.search(r'\b(theorem|def|abbrev)\s+' + re.escape(tail) + r'\b', corpus):
        continue
    missing.append(n)

print("lean names cited: %d; MISSING: %d" % (len(names), len(missing)))
for n in missing:
    print("  ??", n)
