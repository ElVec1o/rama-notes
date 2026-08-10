"""Cross-check every Lean declaration named in the papers against the Lean library.

Rule 5 requires a table mapping paper numbering to Lean declaration names. This builds it,
and in building it audits three things that are easy to get wrong and impossible to notice
by reading:

  DANGLING  a name cited in a paper that no longer exists in RamaLean. This is what happens
            when a theorem is renamed or a file is rewritten, and the paper keeps claiming
            something is machine-checked when the declaration is gone.
  ORPHAN    a Lean file that no paper mentions. Not an error, but it means work that is not
            being claimed, or claimed only in the research log.
  UNBUILT   a Lean file not reachable from RamaLean.lean, hence never compiled by
            `lake build`, hence carrying no guarantee at all despite looking formalized.

Names are matched leniently: the papers write `Foo.bar_baz` or just `bar_baz`, and Lean
declares `theorem bar_baz` inside `namespace Foo`, so a bare name matches if some namespace
qualifies it.
"""

import os
import re
import sys

PAPERS = ['paper2a_note/note.tex', 'paper2b_note/note.tex', 'paper2_note/note.tex', 'paper3_note/note.tex', 'paper4_note/note.tex',
          'methodology_note/note.tex', 'paper1_partition_self_divisibility.md']
LEANDIR = 'RamaLean'
ROOT = 'RamaLean.lean'

# \texttt{...} entries that are Lean identifiers rather than file paths or commands
TT = re.compile(r'\\texttt\{([^}]*)\}')
DECL = re.compile(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\'?!]*)', re.M)
NS = re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.\']*)', re.M)


def clean(s):
    """Undo LaTeX escaping inside \texttt."""
    return s.replace('\\_', '_').replace('\\-', '').replace('\\allowbreak', '').strip()


def lean_decls():
    """{bare name: [qualified names]} and {file: [bare names]}."""
    bare = {}
    perfile = {}
    for fn in sorted(os.listdir(LEANDIR)):
        if not fn.endswith('.lean'):
            continue
        path = os.path.join(LEANDIR, fn)
        src = open(path).read()
        nss = NS.findall(src)
        ns = nss[0] if nss else ''
        names = [m.group(2) for m in DECL.finditer(src)]
        perfile[fn] = names
        for nm in names:
            bare.setdefault(nm, []).append(f"{ns}.{nm}" if ns else nm)
    return bare, perfile


def cited():
    """{paper: set of candidate Lean names}."""
    out = {}
    for p in PAPERS:
        if not os.path.exists(p):
            continue
        src = open(p).read()
        names = set()
        for raw in TT.findall(src):
            c = clean(raw)
            if not c or '/' in c or ' ' in c:
                continue
            # keep identifier-shaped things, with or without a namespace prefix
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", c):
                names.add(c)
        out[p] = names
    return out


MATHLIB_PREFIX = ('Finset.', 'Matrix.', 'Nat.', 'Lean.', 'Real.', 'Complex.',
                  'Equiv.', 'Polynomial.', 'MeasureTheory.', 'SimpleGraph.')
TOOLING = {'RamaLean', 'lake', 'sorry', 'native_decide', 'propext', 'ring', 'det',
           # status labels, not declarations: the papers set them in \texttt because they
           # are literal labels in the Lean sources, and without this they read as dangling
           'VERIFIED', 'HEURISTIC', 'CONJECTURE', 'REFUTED', 'OPEN', 'Classical.choice',
           'Quot.sound',
           'decide', 'omega', 'simp', 'nlinarith', 'linarith', 'w', 'TODO',
           'eigenvalue_mem_ball', 'Classical.choice', 'Quot.sound'}


def is_benign(nm, perfile):
    """A cited name that is legitimately not a RamaLean declaration."""
    if nm.endswith('.lean') or nm.endswith('.py'):
        return True
    if nm in TOOLING or nm.startswith(MATHLIB_PREFIX):
        return True
    # a RamaLean module name rather than a declaration
    if nm + '.lean' in perfile:
        return True
    # a hypothesis name from a theorem statement: single lowercase token starting with h
    if re.fullmatch(r"h[a-zA-Z0-9_']*", nm):
        return True
    # an OEIS A-number
    if re.fullmatch(r"A\d{6}", nm):
        return True
    return False


def built_files():
    src = open(ROOT).read()
    return {m + '.lean' for m in re.findall(r'^import RamaLean\.([A-Za-z0-9_]+)', src, re.M)}


def main():
    bare, perfile = lean_decls()
    cites = cited()
    built = built_files()

    dangling = []
    used_files = set()
    table = []
    for p, names in cites.items():
        for nm in sorted(names):
            tail = nm.split('.')[-1]
            if tail in bare:
                quals = bare[tail]
                table.append((p, nm, ', '.join(quals)))
                for fn, ns in perfile.items():
                    if tail in ns:
                        used_files.add(fn)
            elif is_benign(nm, perfile):
                continue
            else:
                dangling.append((p, nm))

    # a file also counts as cited if a paper names its path
    papertext = "".join(open(q).read() for q in PAPERS if os.path.exists(q))
    for fn in perfile:
        if fn[:-5] in papertext:
            used_files.add(fn)
    allfiles = set(perfile)
    orphan = sorted(allfiles - used_files)
    unbuilt = sorted(allfiles - built)

    print(f"Lean files: {len(allfiles)}   declarations: {sum(len(v) for v in perfile.values())}")
    print(f"names cited in papers and resolved: {len(table)}")
    print()
    print("== DANGLING (cited in a paper, not found in RamaLean) ==")
    if dangling:
        for p, nm in dangling:
            print(f"  {p}: {nm}")
    else:
        print("  none")
    print()
    print("== UNBUILT (file not reachable from RamaLean.lean) ==")
    print("  " + (", ".join(unbuilt) if unbuilt else "none"))
    print()
    print("== ORPHAN (no paper cites any declaration from it) ==")
    print("  " + (", ".join(orphan) if orphan else "none"))
    print()
    print("== MAPPING TABLE ==")
    for p, nm, quals in sorted(table):
        print(f"  {os.path.dirname(p) or p:<18} {nm:<34} -> {quals}")
    return 1 if (dangling or unbuilt) else 0


if __name__ == '__main__':
    sys.exit(main())
