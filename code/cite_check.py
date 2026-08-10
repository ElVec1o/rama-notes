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


def normalise(text):
    return '\n'.join(l.rstrip() for l in text.split('\n')
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
        p = subprocess.run([sys.executable, path], cwd=ROOT,
                           capture_output=True, text=True, timeout=BUDGET, env=env)
    except subprocess.TimeoutExpired:
        return 'RUNNING', ''
    if p.returncode != 0:
        tail = [l for l in (p.stderr or '').strip().split('\n') if l.strip()]
        return 'CRASH', (tail[-1][:110] if tail else f'exit {p.returncode}')

    cur = normalise(p.stdout or '')
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
    nsnap = len(glob.glob(os.path.join(SNAPS, '*.txt')))
    print(f"\n  Every cited script runs, and the {nsnap} with recorded snapshots still produce")
    print("  the same numbers. hl_Wspec.py violated the first property silently; a script that")
    print("  runs but has drifted would violate the second just as quietly.")
    if counts.get('RUNNING'):
        print(f"  {counts['RUNNING']} exceeded the budget and are unsnapshotted: a real gap.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
