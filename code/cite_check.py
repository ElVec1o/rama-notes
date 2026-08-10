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

WHAT THIS CHECKS, AND WHAT IT DELIBERATELY DOES NOT. It runs each cited script and classifies the
outcome. It does NOT check that the numbers still match the paper, which would need each script
to declare its own claims in a machine-readable way; that is a larger change and worth doing, but
a script that raises before printing anything is the failure actually observed, and it is cheap
to rule out.

  OK        exited zero within the budget
  RUNNING   still going when the budget expired, which is expected for the search scripts and is
            not a failure: it started, imported and got as far as computing
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
BUDGET = 45          # seconds per script; long searches are expected to exceed it


def cited_scripts():
    """Every code/<name>.py named in any paper, with the papers naming it."""
    out = {}
    for tex in glob.glob(os.path.join(ROOT, '*_note', '*.tex')):
        s = open(tex, encoding='utf-8', errors='replace').read()
        for m in re.finditer(r'\\texttt\{code/([A-Za-z0-9_\\]+)\.py\}', s):
            name = m.group(1).replace('\\_', '_')
            out.setdefault(name, set()).add(os.path.basename(os.path.dirname(tex)))
    return {k: sorted(v) for k, v in sorted(out.items())}


def run(name):
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
    if p.returncode == 0:
        return 'OK', ''
    tail = [l for l in (p.stderr or '').strip().split('\n') if l.strip()]
    return 'CRASH', (tail[-1][:110] if tail else f'exit {p.returncode}')


def main():
    scripts = cited_scripts()
    print(f"Scripts cited by the papers: {len(scripts)}\n")
    print(f"{'script':>26}{'status':>10}   detail / cited by")
    bad = []
    counts = {}
    for name, papers in scripts.items():
        st, detail = run(name)
        counts[st] = counts.get(st, 0) + 1
        if st in ('CRASH', 'MISSING'):
            bad.append((name, st, detail, papers))
        note = detail if detail else ','.join(p.replace('_note', '') for p in papers)
        print(f"{name:>26}{st:>10}   {note}")

    print(f"\n  {counts}")
    if bad:
        print(f"\n  {len(bad)} CITED SCRIPT(S) DO NOT RUN. Each is a claim the papers assert and")
        print("  no reader can reproduce:")
        for (name, st, detail, papers) in bad:
            print(f"    code/{name}.py  [{st}]  cited by {', '.join(papers)}")
            if detail:
                print(f"      {detail}")
        return 1
    print("\n  Every cited script runs. That is the property hl_Wspec.py violated silently.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
