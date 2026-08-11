"""Full audit of the two papers under active correspondence: 2a (Hall) and 2b (Xu).

code/lean_map.py already checks that every Lean name a paper cites still EXISTS, and that no file
is unbuilt. That is necessary and not sufficient. A paper whose selling point is machine-checking
makes a stronger claim than "the identifier exists", and three things can be wrong while
lean_map.py reports clean:

  KIND      the cited name is a `def`, not a theorem. In this project the conjectures themselves
            are defs -- `D3`, `C1`, `MinDegTwoFails` -- so citing one is correct when the paper is
            stating a conjecture and wrong when it says "formalized" or "verified". The audit
            cannot decide intent, so it reports every def a paper cites and asks that each be
            deliberate.
  AXIOMS    the name depends on something beyond [propext, Classical.choice, Quot.sound].
            `native_decide` in particular produces a proof the kernel does not replay, which the
            repository's own README calls out; anything else is worse.
  SORRY     a file carrying `sorry` anywhere, since a cited theorem sitting next to one invites
            the reader to assume the whole file is checked.

This runs `#print axioms` on every cited name in one batch, and cross-reads the sources for the
declaration kind, so all three are answered together.

SCOPE. paper2a_note and paper2b_note only. Those are the two under correspondence with Chris Hall
and Zili Xu, and they are what a reader coming from either exchange will open.
"""

import os
import re
import sys
import glob
import subprocess
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__))
                 if '__file__' in globals() else 'code')   # jensen_sweep exec()s some of
                 # these, and __file__ is undefined there
import quickmode

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPERS = ['paper2a_note/note.tex', 'paper2b_note/note.tex']
LEANDIR = os.path.join(ROOT, 'RamaLean')

STD = {'propext', 'Classical.choice', 'Quot.sound'}
# \texttt{} entries that are prose, tooling or file paths rather than Lean identifiers
NOT_LEAN = re.compile(r'^(code/|RamaLean|lake|sorry|native_decide|propext|ring|nlinarith|'
                      r'linarith|simp|omega|decide|Mathlib|VERIFIED|HEURISTIC|CONJECTURE|'
                      r'REFUTED|OPEN)')


def declarations():
    """Every declaration in RamaLean: name -> (fully-qualified, kind, file)."""
    out = {}
    for path in sorted(glob.glob(os.path.join(LEANDIR, '*.lean'))):
        ns, src = [], open(path, encoding='utf-8').read()
        for line in src.split('\n'):
            m = re.match(r'namespace\s+([A-Za-z0-9_.]+)', line)
            if m:
                ns.append(m.group(1)); continue
            # `end X` must pop the namespace NAMED X, not merely the innermost: these files
            # nest `section`s inside namespaces, and popping blindly mis-qualifies every
            # declaration after the first `end`, which is what made fifteen names look missing.
            m = re.match(r'end\s+([A-Za-z0-9_.]+)', line)
            if m and m.group(1) in ns:
                while ns and ns[-1] != m.group(1):
                    ns.pop()
                if ns:
                    ns.pop()
                continue
            m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
                         r'(theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z0-9_\'!]+)',
                         line)
            if m:
                kind, nm = m.group(1), m.group(2)
                full = '.'.join(ns + [nm]) if ns else nm
                out[full] = (full, kind, os.path.basename(path))
                out.setdefault(nm, (full, kind, os.path.basename(path)))
    return out


def cited(paper):
    src = open(os.path.join(ROOT, paper), encoding='utf-8').read()
    names = set()
    for m in re.finditer(r'\\texttt\{([^}]*)\}', src):
        t = m.group(1).replace('\\_', '_').strip()
        if not t or NOT_LEAN.match(t) or '/' in t or ' ' in t or '.py' in t:
            continue
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.']*", t):
            names.add(t)
    return names


def axioms_of(fullnames):
    """One batch #print axioms; returns name -> set(axioms) or None if it failed."""
    body = 'import RamaLean\n' + '\n'.join(f'#print axioms {n}' for n in sorted(fullnames))
    tmp = os.path.join(ROOT, '_audit_axioms.lean')
    open(tmp, 'w').write(body)
    try:
        p = subprocess.run(['lake', 'env', 'lean', tmp], cwd=ROOT,
                           capture_output=True, text=True, timeout=3000)
    finally:
        os.remove(tmp)
    got = {}
    for line in (p.stdout or '').split('\n'):
        m = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        if m:
            got[m.group(1)] = {a.strip() for a in m.group(2).split(',') if a.strip()}
        m2 = re.match(r"'([^']+)' does not depend on any axioms", line)
        if m2:
            got[m2.group(1)] = set()
    return got


def build_root():
    """`lake build` the ROOT module before anything else.

    lean_map.py reads RamaLean.lean as text, so it cannot tell whether the root module has
    actually been compiled with the imports it lists. A file added to RamaLean.lean and built
    individually leaves the root's olean stale, and `import RamaLean` then does not expose it:
    three files verified the same day looked absent for exactly this reason. Building the root
    first is the only way to make the axiom pass mean what it appears to mean.
    """
    p = subprocess.run(['lake', 'build'], cwd=ROOT, capture_output=True, text=True, timeout=3600)
    ok = p.returncode == 0
    print(f"lake build (root): {'ok' if ok else 'FAILED'}")
    if not ok:
        tail = [l for l in (p.stdout + p.stderr).strip().split('\n') if l.strip()][-4:]
        for l in tail:
            print("   ", l[:110])
    return ok


def main():
    if not build_root():
        print("\nRoot build failed; the axiom pass below would be meaningless. Stopping.")
        return 1
    print()
    decls = declarations()
    sorry_files = set()
    for path in glob.glob(os.path.join(LEANDIR, '*.lean')):
        src = open(path, encoding='utf-8').read()
        for line in src.split('\n'):
            st = line.strip()
            if re.search(r'\bsorry\b', st) and not st.startswith('--') and '`' not in st:
                sorry_files.add(os.path.basename(path))
    print(f"Lean files carrying a bare `sorry`: {sorted(sorry_files) or 'none'}\n")

    per = {}
    allnames = set()
    for paper in PAPERS:
        names = {n for n in cited(paper) if n in decls}
        per[paper] = names
        allnames |= {decls[n][0] for n in names}
        print(f"{paper}: {len(names)} Lean declarations cited")

    print(f"\nResolving axioms for {len(allnames)} declarations (one batch)...")
    ax = axioms_of(allnames)
    print(f"  resolved: {len(ax)}\n")

    bad_ax, defs, unresolved = [], [], []
    for paper in PAPERS:
        for n in sorted(per[paper]):
            full, kind, f = decls[n]
            if kind in ('def', 'abbrev', 'structure'):
                defs.append((paper, n, kind, f))
            a = ax.get(full)
            if a is None:
                unresolved.append((paper, n, full, f))
            elif not a <= STD:
                bad_ax.append((paper, n, sorted(a - STD), f))

    print("=" * 78)
    print("KIND: declarations cited that are definitions, not theorems")
    print("(correct when the paper is stating a conjecture; wrong if it says 'formalized')")
    if defs:
        for (paper, n, kind, f) in defs:
            print(f"  {paper.split('_')[0]:<10} {n:<34} {kind:<9} {f}")
    else:
        print("  none")

    print("\n" + "=" * 78)
    print("AXIOMS: declarations resting on anything beyond the standard three")
    if bad_ax:
        for (paper, n, extra, f) in bad_ax:
            print(f"  {paper.split('_')[0]:<10} {n:<34} {extra}  {f}")
    else:
        print("  none: every cited declaration rests on [propext, Classical.choice, Quot.sound]")

    if unresolved:
        print("\n" + "=" * 78)
        print("UNRESOLVED: cited, present in source, but no axiom line came back")
        for (paper, n, full, f) in unresolved:
            print(f"  {paper.split('_')[0]:<10} {n:<34} -> {full}  {f}")

    print("\n" + "=" * 78)
    ok = not bad_ax and not sorry_files and not unresolved
    print(f"VERDICT: {'clean' if ok else 'ISSUES ABOVE'}")
    print(f"  {len(defs)} cited definition(s) -- check each is a conjecture being stated,")
    print("  not a result being claimed.")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
