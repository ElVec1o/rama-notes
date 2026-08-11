"""Run every script the papers cite, and report the ones that do not run.

WHY THIS EXISTS. Every numerical claim in the notes names the script that produced it, which is
the right discipline. But nothing ever ran those scripts again. code/hl_Wspec.py -- cited for the
vertex recursion and the W-spectrum claims -- had been broken for some time: hp.random_plane_family
returns a pair (Bs, res) and the script took the return as a single value, testing it against
None, which it never is because failure returns (None, inf). The tuple went downstream and Adj
crashed on it. The claim the paper attributes to that script was therefore unverifiable by anyone
who ran the repository, and it looked from outside exactly like a verified one.

That is a class of defect, not an instance. A citation to a script asserts two things -- that the
script produced the number, and that it still does -- and only the first was ever checked.

WHAT THIS CHECKS. Two things, because "it runs" is the weaker half of the problem. A script that
still runs but now prints different numbers is worse than one that crashes, since the paper's
figures are then silently wrong and nothing announces it.

  RUNS      the script exits without raising
  NUMBERS   its output still matches the recorded snapshot, so the figures the paper quotes are
            the figures the code still produces

Snapshots live in code/snapshots/<name>.txt and are written with --snapshot. Volatile lines --
elapsed times, budget notices, progress counters -- are stripped before comparison, since they
depend on the machine and not on the mathematics. Scripts that exceed the budget cannot be
snapshotted this way and are reported as RUNNING; that is a real gap and is stated rather than
papered over.

It also checks BIBLIOGRAPHIES, for the same reason. The split handed each paper the monolith's
37 references; 2a cited 16 of them and 2b cited 28, and six were cited by neither. A manual
\\begin{thebibliography} produces no warning for an uncited \\bibitem, so both papers were a
third dead weight with nothing in the toolchain to say so. Note the citation pattern must allow
the optional-argument form: a first version matched \\cite{...} but not \\cite[Conjecture 1]{RL},
and would have deleted a live reference.

  OK        exited zero and its output matches the snapshot (or none is recorded yet)
  DRIFT     exited zero but its output CHANGED against the snapshot: the paper may now quote
            figures the code no longer produces
  RUNNING   still going when the budget expired, expected for the search scripts, not a failure
  CRASH     non-zero exit, with the last traceback line reported
  MISSING   cited but not present in the repository

A CRASH or a MISSING is a defect in the paper, not merely in the code, because the paper cites it
as evidence.
"""

import os
import re
import sys
import glob
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SNAPS = os.path.join(ROOT, 'code', 'snapshots')
BUDGET = 45          # seconds per script; long searches are expected to exceed it

# Lines whose content depends on the machine rather than on the mathematics.
VOLATILE = re.compile(r'elapsed|budget|\bs of \b|^\s*\[|seconds|wall clock|ETA', re.I)


# An elapsed time embedded in an otherwise stable line ("93 configurations, 25s") made two
# scripts report drift for no reason but the machine's load. Dropping the whole line would lose
# the configuration count with it, so the duration alone is masked.
# No whitespace between the number and the unit: allowing it made the mask eat the path
# count in "paths=  3457  min|F|=...", turning a real number into <t>. Durations in this output
# are always written closed up, "25s" and "1.5ms".
DURATION = re.compile(r'(?<![\w.])\d+(?:\.\d+)?(?:s|sec|secs|ms|min)(?![\w.])')


def normalise(text):
    return '\n'.join(DURATION.sub('<t>', l.rstrip()) for l in text.split('\n')
                      if l.strip() and not VOLATILE.search(l))


def cited_scripts():
    """Every code/<name>.py named in any paper, with the papers naming it."""
    out = {}
    for tex in glob.glob(os.path.join(ROOT, '*_note', '*.tex')):
        s = open(tex, encoding='utf-8', errors='replace').read()
        for m in re.finditer(r'\\texttt\{code/([A-Za-z0-9_\\]+)\.py\}', s):
            name = m.group(1).replace('\\_', '_')
            out.setdefault(name, set()).add(os.path.basename(os.path.dirname(tex)))
    return {k: sorted(v) for k, v in sorted(out.items())}


def run(name, record=False):
    path = os.path.join(ROOT, 'code', name + '.py')
    if not os.path.exists(path):
        return 'MISSING', ''
    env = dict(os.environ)
    for v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
        env[v] = '2'
    try:
        # Run from the REPOSITORY ROOT, not from code/. The scripts use root-relative paths
        # (private/<name>_ckpt.txt for checkpoints, code/<other>.py when one reads another), so
        # running them from code/ makes every one of them fail on a path that is actually fine.
        # The first version of this checker did exactly that and reported twenty false crashes.
        # --quick is honoured by the long searches: it shrinks their budget so a
        # deterministic baseline can be taken. Scripts that do not know the flag ignore it,
        # argparse not being used anywhere here.
        # PYTHONHASHSEED is randomised per process, and several of these scripts build
        # adjacency as {v: set()} and iterate it, so their output depends on it: softedge2 gave
        # two distinct results over six runs unpinned and one over six pinned. Without this the
        # checker reports drift that is nothing but the hash seed, and worse, hides real drift
        # underneath it.
        env = dict(env, PYTHONHASHSEED='0')
        p = subprocess.run([sys.executable, path, '--quick'], cwd=ROOT,
                           capture_output=True, text=True, timeout=BUDGET, env=env)
    except subprocess.TimeoutExpired:
        return 'RUNNING', ''
    if p.returncode != 0:
        tail = [l for l in (p.stderr or '').strip().split('\n') if l.strip()]
        return 'CRASH', (tail[-1][:110] if tail else f'exit {p.returncode}')

    cur = normalise(p.stdout or '')
    # Several scripts checkpoint into private/ and RESUME. Snapshotting one of those captures a
    # nearly-complete run that tests almost nothing -- jensen_sweep recorded "gap points tested:
    # 3" and a worst ratio of inf, against the 1475 points the paper cites. Such a baseline
    # proves nothing, so it is refused rather than stored, and the script is reported as
    # RESUMED so the gap is visible instead of passing silently.
    if re.search(r'resuming after', cur, re.I):
        return 'RESUMED', 'checkpointed run; snapshot would capture a resumed state'
    snap = os.path.join(SNAPS, name + '.txt')
    if record:
        os.makedirs(SNAPS, exist_ok=True)
        open(snap, 'w').write(cur + '\n')
        return 'OK', 'snapshot written'
    if not os.path.exists(snap):
        return 'OK', 'no snapshot yet'
    want = open(snap).read().strip()
    if cur.strip() == want:
        return 'OK', ''
    a, b = want.split('\n'), cur.split('\n')
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else '<absent>'
        y = b[i] if i < len(b) else '<absent>'
        if x != y:
            return 'DRIFT', f'line {i+1}: was "{x.strip()[:44]}" now "{y.strip()[:44]}"'
    return 'DRIFT', 'lengths differ'


CITE = re.compile(r'\\cite[tp]?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}')


NUM = re.compile(r'(?<![\\A-Za-z0-9.])(\d+(?:\\,\d\d\d)*(?:\.\d+)?)(?![0-9])')
SCRIPT_TT = re.compile(r'\\texttt\{code/([A-Za-z0-9_\\]+)\.py\}')


def _nums(text):
    """Decimal numbers in a string, LaTeX thin-space separators removed.

    Exponent notation is stripped first. A sentence containing $10^{-15}$ otherwise
    contributes 10 and 15 as if they were quoted figures, which produced most of the
    false positives in the first run of this check.
    """
    text = re.sub(r'\d+\s*\^\s*\{[^}]*\}', ' ', text)
    text = re.sub(r'\d+\s*\^\s*-?\d+', ' ', text)
    out = []
    for t in NUM.findall(text):
        try:
            out.append((t, float(t.replace('\\,', ''))))
        except ValueError:
            pass
    return out


def quoted_numbers():
    """Figures a paper states beside a script citation, checked against that script's output.

    A snapshot proves a script still produces what it did. It does not prove the PAPER quotes it
    correctly, which is the other half and the one a reader depends on. Advisory: a sentence
    carrying a citation may also carry numbers from elsewhere, so an unmatched figure is a prompt
    to look rather than a proven error.
    """
    findings = []
    for tex in sorted(glob.glob(os.path.join(ROOT, '*_note', '*.tex'))):
        src = open(tex, encoding='utf-8', errors='replace').read()
        paper = os.path.basename(os.path.dirname(tex))
        for m in SCRIPT_TT.finditer(src):
            name = m.group(1).replace('\\_', '_')
            snap = os.path.join(SNAPS, name + '.txt')
            if not os.path.exists(snap):
                continue
            outnums = [v for _, v in _nums(open(snap).read())]
            lo = src.rfind('.', 0, max(0, m.start() - 400))
            hi = src.find('.', m.end())
            sentence = src[lo + 1: hi if hi > 0 else m.end() + 200]
            base = lo + 1
            # A sentence may cite several scripts -- "(code/a.py, code/b.py, code/c.py)" -- and
            # charging every figure to whichever name matched blamed D3fixdeg for the whole
            # five-engine table and sharp_close for universal_close's percentages. Bind each
            # figure to the citation NEAREST it instead, and skip the ones that belong to a
            # different script in the same sentence.
            cites = [(c.start() + base, c.group(1).replace('\\_', '_'))
                     for c in SCRIPT_TT.finditer(sentence)]
            for (txt, val) in _nums(sentence):
                if len(cites) > 1:
                    at = sentence.find(txt) + base
                    nearest = min(cites, key=lambda t: abs(t[0] - at))[1]
                    if nearest != name:
                        continue
                tol = 0.5 * 10 ** (-len(txt.split('.')[1])) if '.' in txt else 0.5
                if not any(abs(o - val) <= tol for o in outnums):
                    findings.append((paper, name, txt))
    return findings


def bibliography_report():
    r"""Uncited \bibitem entries, and \cite keys with no entry, per paper."""
    rows = []
    for tex in sorted(glob.glob(os.path.join(ROOT, '*_note', '*.tex'))):
        s = open(tex, encoding='utf-8', errors='replace').read()
        if '\\begin{thebibliography}' not in s:
            continue
        i = s.index('\\begin{thebibliography}')
        j = s.index('\\end{thebibliography}')
        defined = re.findall(r'\\bibitem\{([^}]+)\}', s[i:j])
        cited = set()
        for c in CITE.findall(s[:i]):
            cited |= {x.strip() for x in c.split(',')}
        name = os.path.basename(os.path.dirname(tex))
        rows.append((name, len(defined),
                     sorted(k for k in defined if k not in cited),
                     sorted(cited - set(defined))))
    return rows


def main():
    record = '--snapshot' in sys.argv
    scripts = cited_scripts()
    if record:
        print("RECORDING snapshots; nothing is checked on this pass.\n")
    print(f"Scripts cited by the papers: {len(scripts)}\n")
    print(f"{'script':>26}{'status':>10}   detail / cited by")
    bad = []
    counts = {}
    for name, papers in scripts.items():
        st, detail = run(name, record)
        counts[st] = counts.get(st, 0) + 1
        if st in ('CRASH', 'MISSING', 'DRIFT'):
            bad.append((name, st, detail, papers))
        note = detail if detail else ','.join(p.replace('_note', '') for p in papers)
        print(f"{name:>26}{st:>10}   {note}")

    print(f"\n  {counts}")
    if bad:
        print(f"\n  {len(bad)} CITED SCRIPT(S) FAILED. Each is a claim the papers assert:")
        for (name, st, detail, papers) in bad:
            print(f"    code/{name}.py  [{st}]  cited by {', '.join(papers)}")
            if detail:
                print(f"      {detail}")
        return 1
    print("\n" + "=" * 78)
    print("QUOTED NUMBERS (advisory): figures a paper states beside a script citation that do")
    print("not appear in that script's recorded output, allowing for rounding.")
    qn = quoted_numbers()
    if qn:
        seen = set()
        for (paper, name, txt) in qn:
            key = (paper, name, txt)
            if key in seen:
                continue
            seen.add(key)
            print(f"  {paper.replace('_note',''):<10} code/{name}.py  quotes {txt}")
        print(f"  {len(seen)} unmatched. Each is a prompt to check, not a proven error: a")
        print("  sentence carrying a citation may also carry numbers from elsewhere.")
    else:
        print("  none: every figure quoted beside a citation appears in that script's output.")

    print("\n" + "=" * 78)
    print("BIBLIOGRAPHIES")
    bibbad = False
    for (name, n, uncited, undefined) in bibliography_report():
        flag = ''
        if uncited or undefined:
            bibbad = True
            flag = f"   uncited={uncited or '-'}  undefined={undefined or '-'}"
        print(f"  {name:<18} {n:>3} entries{flag}")
    if bibbad:
        print("  An uncited bibitem produces no warning anywhere in the toolchain.")
        return 1

    ncited = len(scripts)
    nsnap = len(glob.glob(os.path.join(SNAPS, '*.txt')))
    covered = sum(1 for n in scripts if os.path.exists(os.path.join(SNAPS, n + '.txt')))
    print("\n" + "=" * 78)
    print("COVERAGE")
    print(f"  cited scripts: {ncited}   with a recorded baseline: {covered}"
          f"   without: {ncited - covered}")
    if ncited - covered:
        print(f"  Drift in those {ncited - covered} is UNDETECTED. They exceed the {BUDGET}s")
        print("  budget, so no baseline could be taken; that is a real gap, not a pass.")
    print(f"\n  Every cited script runs, and the {nsnap} with recorded snapshots still produce")
    print("  the same numbers. hl_Wspec.py violated the first property silently; a script that")
    print("  runs but has drifted would violate the second just as quietly.")
    if counts.get('RUNNING'):
        print(f"  {counts['RUNNING']} exceeded the budget and are unsnapshotted: a real gap.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
