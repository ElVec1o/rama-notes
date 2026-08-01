"""The cross-term decomposition C_r = sum_{|S|=r-2} [ Q_S - ||W_S||^2 ], and where the
two-term criterion 4a C_2 >= C_3 breaks.

Backs Theorems thm:C2 and thm:Cr of paper2_note/note.tex, and the table of partial sums.

The vertex recursion's remainder is X_e = sum_{r>=2} (-1)^{r-1} C_r x^{m-2r}, and
X_e <= 0 at x = 2 sqrt a is exactly

    sum_{r>=2} (-1)^r C_r (4a)^{2-r}  >=  0.                                    (*)

Reindexing C_r by S = T minus {k,l} and applying
<u ^ alpha, w ^ gamma> = <u,w><alpha,gamma> - <iota_w alpha, iota_u gamma>
together with f_k ^ omega'_k = 0 gives the decomposition in the title, in which Q_S is a
Gram-Hadamard (Schur) square and only W_S obstructs.  At r = 2 tightness kills W.

Usage:  bash run_hl_Cr.sh
Deterministic: seeds fixed.  Wall-clock budget enforced.
"""
import itertools
import math
import time

import numpy as np

import hl_planes as hp

BUDGET_S = 900.0
_T0 = time.monotonic()


def cols(Bc, S):
    return [Bc[j][:, c] for j in S for c in (0, 1)]


def gram(A1, A2):
    return float(np.linalg.det(np.column_stack(A1).T @ np.column_stack(A2)))


def C_direct(Bc, fs, q, r):
    """C_r straight from the definition; None if the budget runs out."""
    tot = 0.0
    for T in itertools.combinations(range(q), r):
        if time.monotonic() - _T0 > BUDGET_S:
            return None
        for k, l in itertools.permutations(T, 2):
            tot += gram([fs[k]] + cols(Bc, [j for j in T if j != k]),
                        [fs[l]] + cols(Bc, [j for j in T if j != l]))
    return tot


def C_fast(Bc, fs, q, r):
    """The same C_r, with one precomputed Gram matrix so the inner loop is index
    arithmetic and a small determinant.  Columns 0..q-1 hold the f_k, then columns
    q+2j, q+2j+1 hold the two columns of block j."""
    X = np.column_stack([fs[k] for k in range(q)]
                        + [Bc[j][:, c] for j in range(q) for c in (0, 1)])
    G = X.T @ X

    def idx(k, T):
        out = [k]
        for j in T:
            if j != k:
                out += [q + 2 * j, q + 2 * j + 1]
        return out

    tot, n = 0.0, 0
    for T in itertools.combinations(range(q), r):
        if (n & 1023) == 0 and time.monotonic() - _T0 > BUDGET_S:
            return None
        for k, l in itertools.permutations(T, 2):
            tot += np.linalg.det(G[np.ix_(idx(k, T), idx(l, T))])
            n += 1
    return tot


def Q_and_W(Bc, fs, q, S):
    """Q_S and ||W_S||^2 of Theorem thm:Cr."""
    rest = [k for k in range(q) if k not in S]
    cS = cols(Bc, S)
    Q = sum((fs[k] @ fs[l]) * gram([Bc[k][:, 0], Bc[k][:, 1]] + cS,
                                   [Bc[l][:, 0], Bc[l][:, 1]] + cS)
            for k in rest for l in rest)
    terms = []                       # iota_v (c_1^..^c_p) expanded over the columns
    for k in rest:
        cl = [Bc[k][:, 0], Bc[k][:, 1]] + cS
        for t in range(len(cl)):
            co = ((-1) ** t) * float(fs[k] @ cl[t])
            if co != 0.0:
                terms.append((co, [cl[x] for x in range(len(cl)) if x != t]))
    W2 = sum(c1 * c2 * gram(L1, L2) for c1, L1 in terms for c2, L2 in terms)
    return Q, W2


def lcf(n, pat):
    E = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
    for i in range(n):
        E.add(tuple(sorted((i, (i + pat[i % len(pat)]) % n))))
    return sorted(E)


def setup(Bs, m, e):
    e = e / np.linalg.norm(e)
    Q0 = hp.ortho_complement([e], m)
    return [Q0 @ B for B in Bs], [Q0 @ hp.f_vec(B, e) for B in Bs]


def main():
    rng = np.random.default_rng(29)

    print("=" * 88)
    print("PART 1.  C_r = sum_{|S|=r-2} [ Q_S - ||W_S||^2 ]")
    print("=" * 88)
    print(f"{'family':22} {'r':>2} {'C_r direct':>14} {'sum(Q_S-|W_S|^2)':>18} {'rel err':>10}")
    for nm, ed, m in (("K_6", hp.Kn_edges(6), 6), ("cube", hp.cube_edges(), 8),
                      ("Petersen", hp.petersen_edges(), 10)):
        Bs = hp.graph_blocks(ed, m)
        Bc, fs = setup(Bs, m, rng.normal(size=m))
        for r in (2, 3):
            if 2 * r > m:
                continue
            d = C_direct(Bc, fs, len(Bs), r)
            if d is None:
                continue
            tot = sum(Q - W for Q, W in
                      (Q_and_W(Bc, fs, len(Bs), list(S))
                       for S in itertools.combinations(range(len(Bs)), r - 2)))
            print(f"{nm:22} {r:2} {d:14.6g} {tot:18.6g} "
                  f"{abs(d - tot) / max(1.0, abs(d)):10.2e}")

    print()
    print("=" * 88)
    print("PART 2.  ||W_S||^2 against Q_S at level r = 3")
    print("=" * 88)
    print("For ODD r we need C_r = sum_S (Q_S - ||W_S||^2) SMALL, so we want ||W_S||^2")
    print("close to Q_S.  It is not: the ratio decays, so C_3 is essentially sum_S Q_S,")
    print("an undamped sum of Schur squares.")
    print(f"{'graph':22} {'m':>3} {'Q_0=C_2':>9} {'sum Q_n':>10} {'sum|W_n|^2':>11} "
          f"{'C_3':>9} {'|W|^2/Q':>8}")
    for nm, ed, m in (("cube", hp.cube_edges(), 8), ("Petersen", hp.petersen_edges(), 10),
                      ("Franklin", lcf(12, [5, -5]), 12), ("Heawood", lcf(14, [5, -5]), 14),
                      ("Mobius-Kantor", lcf(16, [5, -5]), 16)):
        if time.monotonic() - _T0 > BUDGET_S:
            print("  [budget]")
            break
        Bs = hp.graph_blocks(ed, m)
        Bc, fs = setup(Bs, m, np.random.default_rng(1000 + m).normal(size=m))
        q = len(Bs)
        Q0, _ = Q_and_W(Bc, fs, q, [])
        sQ = sW = 0.0
        for n in range(q):
            Q, W = Q_and_W(Bc, fs, q, [n])
            sQ += Q
            sW += W
        print(f"{nm:22} {m:3} {Q0:9.4g} {sQ:10.5g} {sW:11.5g} {sQ - sW:9.4g} {sW / sQ:8.4f}")

    print()
    print("=" * 88)
    print("PART 3.  the two-term criterion 4a C_2 >= C_3, and the partial sums of (*)")
    print("=" * 88)
    print(f"{'graph':24} {'m':>3} {'4aC2/C3':>9}   Sigma_2, Sigma_3, ...")
    for nm, ed, m, rmax in (("cube (8,cubic)", hp.cube_edges(), 8, 4),
                            ("Petersen", hp.petersen_edges(), 10, 5),
                            ("Franklin (12,cubic)", lcf(12, [5, -5]), 12, 6),
                            ("Heawood (14,cubic)", lcf(14, [5, -5]), 14, 6),
                            ("Mobius-Kantor (16)", lcf(16, [5, -5]), 16, 6),
                            ("Pappus (18,cubic)", lcf(18, [5, 7, -7, 7, -7, -5]), 18, 5),
                            ("Desargues (20)", lcf(20, [5, -5, 9, -9]), 20, 5),
                            ("Nauru (24)", lcf(24, [5, -9, 7, -7, 9, -5]), 24, 4)):
        if time.monotonic() - _T0 > BUDGET_S:
            print("  [wall-clock budget reached]")
            break
        Bs = hp.graph_blocks(ed, m)
        av = float(np.trace(hp.Adj(Bs)) / m)
        Bc, fs = setup(Bs, m, np.random.default_rng(1000 + m).normal(size=m))
        Cs = []
        for r in range(2, min(rmax, m // 2) + 1):
            v = C_fast(Bc, fs, len(Bs), r)
            if v is None:
                break
            Cs.append(v)
        if len(Cs) < 2:
            continue
        ratio = 4 * av * Cs[0] / Cs[1] if abs(Cs[1]) > 1e-9 else float('inf')
        acc, part = 0.0, []
        for i, c in enumerate(Cs):
            r = i + 2
            acc += ((-1) ** r) * c * (4 * av) ** (2 - r)
            part.append(acc)
        print(f"{nm:24} {m:3} {ratio:9.4g}   "
              + ", ".join(f"{p:8.4g}" for p in part))
        print(f"{'':24} {'':3} {'':9}   |terms|: "
              + ", ".join(f"{abs(c) * (4 * av) ** (2 - (i + 2)):8.4g}"
                          for i, c in enumerate(Cs)))
    print()
    print("The ratio crosses below 1 at m = 16, so C_3 <= 4a C_2 is false in general.")
    print("The terms peak at r = 3 and then decay geometrically, but the number needed")
    print("grows with m: three nearly suffice at m = 14, four at m = 16, and at m = 20")
    print("five have not settled.  So the criterion is not a bounded-length statement.")
    print(f"elapsed {time.monotonic() - _T0:.0f}s of {BUDGET_S:.0f}s")


if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------
#  The exact ratio R_e = F_A / F_{A^(e)} at the threshold, and the slack.
#  Backs the table in prop:rigid's paragraph.  Run as: python3 -c
#  "import hl_Cr; hl_Cr.ratio_table()"
# ---------------------------------------------------------------------------
def circ(n, S):
    return sorted({tuple(sorted((i, (i + s) % n))) for i in range(n) for s in S})


def ratio_table():
    """R_e/(x/2) and the slack -X_e/(F_{A^(e)} sqrt a), exactly, at x = 2 sqrt a."""
    print(f"{'graph':24} {'m':>3} {'q':>3} {'a':>4} {'slack':>9} {'R_e/(x/2)':>10}")
    rows = []
    for nm, ed, m in (("cube (a=3)", hp.cube_edges(), 8),
                      ("Petersen (a=3)", hp.petersen_edges(), 10),
                      ("Franklin (a=3)", lcf(12, [5, -5]), 12),
                      ("Heawood (a=3)", lcf(14, [5, -5]), 14),
                      ("C8(1,2)  (a=4)", circ(8, [1, 2]), 8),
                      ("C10(1,2) (a=4)", circ(10, [1, 2]), 10),
                      ("C12(1,2) (a=4)", circ(12, [1, 2]), 12),
                      ("C8(1,2,4) (a=5)", circ(8, [1, 2, 4]), 8),
                      ("C10(1,2,5)(a=5)", circ(10, [1, 2, 5]), 10)):
        Bs = hp.graph_blocks(ed, m)
        dg = np.diag(hp.Adj(Bs))
        if dg.min() != dg.max():
            continue
        a = float(dg[0])
        x = 2 * math.sqrt(a)
        e = np.random.default_rng(1000 + m).normal(size=m)
        e /= np.linalg.norm(e)
        d = hp.recursion(Bs, m, e)
        X = float(np.polyval(d['X'], x))
        FA = float(np.polyval(d['FA'], x))
        FAc = float(np.polyval(d['FAc'], x))
        r = (FA / FAc) / (x / 2)
        rows.append((a, r))
        print(f"{nm:24} {m:3} {len(Bs):3} {a:4.0f} "
              f"{-X / (FAc * math.sqrt(a)):9.5g} {r:10.5g}")
    print()
    for a in sorted({t[0] for t in rows}):
        v = [t[1] for t in rows if t[0] == a]
        print(f"  a={a:.0f}:  R_e/(x/2) = {min(v):.4f} .. {max(v):.4f}"
              f"   (spread {max(v) - min(v):.1e})")
