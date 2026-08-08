"""sr_perturb.py -- the decisive falsification engine for (SR-BAND).

We work directly in the coefficient space of the pgf.  A law satisfying (i) is
exactly a probability vector c indexed by the COMPOSITIONS s of p into q parts
of size <= b, and

    G(z)   = sum_s c_s z^s                       (homogeneous of degree p)
    f(y)   = sum_s c_s prod_k (y - a s_k)        (LINEAR in c)
    (ii)   sum_{s : s_k = j} c_s = C(b,j) a^{-j} (1-1/a)^{b-j}   for all k, j
                                                 (LINEAR in c)
    (iii)  G real stable                         (a closed condition, but with
                                                 NONEMPTY INTERIOR)

So the class in (SR-BAND) is  {c >= 0} cap {affine subspace} cap {stable}.
Projection families give points of it.  Two questions:

  Q1  Is the stable set FULL-DIMENSIONAL inside the affine subspace, i.e. can a
      projection family's pgf be perturbed in a generic direction of the null
      space of the marginal constraints and stay stable?   If YES, the class of
      (SR-BAND) is strictly larger than the matrix class and the target is a
      genuinely new statement.  If NO -- if every admissible perturbation
      leaves the stable set -- then (i)+(ii)+(iii) is rigid.

  Q2  Maximise lambda_max(f_c) over the class by projected gradient ascent with
      a stability barrier.  If it crosses  hi = (sqrt(a-1)+sqrt(b-1))^2  while
      the law is still stable, (SR-BAND) is FALSE.

Stability is tested by the line probe: G is real stable iff  t |-> G(u + t v)
has only real roots for every u in R^q and every v > 0.  Because G is
homogeneous of degree p, that univariate polynomial has degree <= p and is
recovered EXACTLY by interpolation through p+1 nodes, so the probe is cheap
and exact up to root-finding.
"""
import sys
import numpy as np
from math import comb
from itertools import combinations

sys.path.insert(0, '/Users/vico/Documents/elvec1o/RAMA-NOTEBOOK/code')
from sr_setup import (band, binom_pmf, law_from_family, graph_family,
                      rand_proj_family, icosahedral_rank2)               # noqa


# ------------------------------------------------------------- monomials
def compositions(p, q, b):
    out = []

    def rec(k, rest, cur):
        if k == q:
            if rest == 0:
                out.append(tuple(cur))
            return
        lo = max(0, rest - b * (q - k - 1))
        for v in range(lo, min(b, rest) + 1):
            cur.append(v)
            rec(k + 1, rest - v, cur)
            cur.pop()
    rec(0, p, [])
    return np.array(out, dtype=int)


def marg_constraints(E, q, a, b):
    """rows: for each k, j -> indicator(s_k = j); rhs = Bin(b,1/a)[j]."""
    M = len(E)
    tgt = binom_pmf(b, a)
    rows, rhs = [], []
    for k in range(q):
        for j in range(b + 1):
            rows.append((E[:, k] == j).astype(float))
            rhs.append(tgt[j])
    return np.array(rows), np.array(rhs)


def fcoef(E, a, q):
    """(M, q+1) matrix: row s = coefficients of prod_k (y - a s_k)."""
    out = np.zeros((len(E), q + 1))
    cache = {}
    for i, s in enumerate(E):
        key = tuple(sorted(s.tolist()))
        if key not in cache:
            poly = np.array([1.0])
            for v in key:
                poly = np.convolve(poly, [1.0, -a * float(v)])
            cache[key] = poly
        out[i] = cache[key]
    return out


# ---------------------------------------------------------- stability
class Stab:
    def __init__(self, E, p, seed=0, nsamp=200):
        self.E = E
        self.p = p
        self.q = E.shape[1]
        self.rng = np.random.default_rng(seed)
        self.nodes = np.cos(np.pi * (np.arange(p + 1) + 0.5) / (p + 1)) * 3.0
        self.lines = []
        for _ in range(nsamp):
            u = self.rng.normal(0, 1.0, size=self.q)
            v = self.rng.uniform(0.2, 2.0, size=self.q)
            self.lines.append((u, v))
        self._pre = np.array([self._prep(u, v) for (u, v) in self.lines])
        Vn = np.vander(self.nodes, self.p + 1, increasing=True)
        self._Vinv = np.linalg.pinv(Vn)

    def _prep(self, u, v):
        """(p+1, M) matrix of monomial values at z = u + t_i v."""
        Z = u[None, :] + self.nodes[:, None] * v[None, :]
        Vm = np.ones((len(self.nodes), len(self.E)))
        for k in range(self.q):
            Vm *= Z[:, k][:, None] ** self.E[:, k][None, :]
        return Vm

    def worst(self, c, ret_line=False):
        w, arg = 0.0, None
        Vinv = self._Vinv
        allvals = self._pre @ c               # (nsamp, p+1)
        for i in range(len(self._pre)):
            coef = Vinv @ allvals[i]          # ascending powers of t
            nz = np.nonzero(np.abs(coef) > 1e-12 * max(1e-30, np.abs(coef).max()))[0]
            if len(nz) < 2:
                continue
            cc = coef[:nz[-1] + 1]
            r = np.roots(cc[::-1])
            sc = max(1.0, float(np.abs(r).max()))
            m = float(np.abs(r.imag).max()) / sc
            if m > w:
                w, arg = m, self.lines[i]
        return (w, arg) if ret_line else w


def lam_max(c, F, lo_hint=None):
    f = F.T @ c
    r = np.roots(f)
    rr = r.real[np.abs(r.imag) < 1e-7 * max(1.0, np.abs(r).max())]
    rr = rr[np.abs(rr) > 1e-9]
    return (float(rr.max()) if len(rr) else -np.inf,
            float(rr.min()) if len(rr) else np.inf,
            float(np.abs(r.imag).max()))


# ------------------------------------------------------------------ main
def base_law(p, q, a, b, E, kind='random', seed=0):
    """coefficient vector of a projection family's pgf on the composition basis."""
    idx = {tuple(s): i for i, s in enumerate(E)}
    if kind == 'random':
        P, res = rand_proj_family(p, q, a, b, seed=seed)
    elif kind == 'icosa':
        P, p_, q_, a_, b_ = icosahedral_rank2()
        res = 0.0
    else:
        adj, p_, q_, a_, b_ = kind
        P, res = graph_family(adj, p, q, a, b), 0.0
    W, S = law_from_family(P, a, b)
    c = np.zeros(len(E))
    for wt, s in zip(W, S):
        c[idx[tuple(s.tolist())]] += wt
    return c, res, P


def study(p, q, a, b, seed=0, nsamp=160, ndir=25, verbose=True):
    lo, hi = band(a, b)
    E = compositions(p, q, b)
    M = len(E)
    A, rhs = marg_constraints(E, q, a, b)
    F = fcoef(E, a, q)
    c0, res, P = base_law(p, q, a, b, E, kind='random', seed=seed)
    st = Stab(E, p, seed=seed + 1, nsamp=nsamp)
    lm, lmn, im = lam_max(c0, F)
    print(f"({p},{q},{a},{b})  monomials M={M}  band=[{lo:.5f},{hi:.5f}]  "
          f"family residual {res:.1e}")
    print(f"    base family: |marg err| = {np.abs(A@c0-rhs).max():.2e}, "
          f"stability probe {st.worst(c0):.2e}, "
          f"lambda_max = {lm:.6f} (hi - lam = {hi-lm:+.6f}), "
          f"lambda_min = {lmn:.6f}")
    # null space of the marginal constraints
    U_, S_, Vt = np.linalg.svd(A, full_matrices=True)
    rk = int((S_ > 1e-9 * S_.max()).sum())
    N = Vt[rk:].T                     # M x (M - rk)
    print(f"    marginal constraints: {A.shape[0]} rows, rank {rk}; "
          f"null space dimension {N.shape[1]} (of M={M})")
    # Q1: how far can we move in a random null direction and stay stable / >=0?
    rng = np.random.default_rng(seed + 7)
    survivors = 0
    eps_list = []
    for _ in range(ndir):
        g = N @ rng.normal(size=N.shape[1])
        g /= np.linalg.norm(g)
        # largest eps keeping c >= 0
        neg = g < 0
        emax = np.min(-c0[neg] / g[neg]) if neg.any() else 1.0
        emax = min(emax, 10.0)
        e = emax
        ok = False
        for _ in range(28):
            c = c0 + e * g
            if c.min() >= -1e-14 and st.worst(c) < 1e-8:
                ok = True
                break
            e *= 0.5
        if ok:
            survivors += 1
            eps_list.append(e / max(emax, 1e-30))
    print(f"    Q1: {survivors}/{ndir} random null directions admit a STABLE "
          f"nonneg perturbation; median fraction of the nonneg-limit reached: "
          f"{np.median(eps_list) if eps_list else float('nan'):.3g}")
    return dict(E=E, A=A, rhs=rhs, F=F, c0=c0, N=N, st=st, lo=lo, hi=hi,
                P=P, M=M)


def ascend(d, p, q, a, b, iters=400, verbose=True, seed=0, upper=True):
    """projected gradient ascent on lambda_max (or descent on lambda_min)
    inside {c >= 0} cap {marginals} cap {stable}."""
    E, F, N, st, lo, hi = d['E'], d['F'], d['N'], d['st'], d['lo'], d['hi']
    c = d['c0'].copy()
    step = 0.05
    best = None
    for it in range(iters):
        f = F.T @ c
        r = np.roots(f)
        rr = np.sort(r.real[np.abs(r.imag) < 1e-7 * max(1.0, np.abs(r).max())])
        rr = rr[np.abs(rr) > 1e-9]
        if len(rr) == 0:
            break
        y = rr.max() if upper else rr.min()
        # d lambda / d c_s  =  - f_s(y) / f'(y)
        fs = F @ np.array([y ** (q - i) for i in range(q + 1)])
        fp = np.polyval(np.polyder(f), y)
        g = -fs / fp
        if not upper:
            g = -g
        g = N @ (N.T @ g)              # project onto the marginal null space
        # do not push negative coordinates further negative
        g[(c <= 1e-14) & (g < 0)] = 0.0
        nrm = np.linalg.norm(g)
        if nrm < 1e-14:
            break
        g /= nrm
        moved = False
        s = step
        for _ in range(30):
            cn = c + s * g
            if cn.min() >= -1e-13:
                cn = np.maximum(cn, 0.0)
                if st.worst(cn) < 1e-8:
                    fn = F.T @ cn
                    rn = np.roots(fn)
                    rrn = np.sort(rn.real[np.abs(rn.imag) < 1e-7 *
                                          max(1.0, np.abs(rn).max())])
                    rrn = rrn[np.abs(rrn) > 1e-9]
                    if len(rrn):
                        yn = rrn.max() if upper else rrn.min()
                        if (yn > y + 1e-12) if upper else (yn < y - 1e-12):
                            c, moved = cn, True
                            break
            s *= 0.5
        if not moved:
            step *= 0.5
            if step < 1e-9:
                break
        else:
            step = min(step * 1.3, 0.3)
        if verbose and it % 50 == 0:
            print(f"      it {it:4d}  lambda_{'max' if upper else 'min'} = "
                  f"{y:.6f}   (target {'hi' if upper else 'lo'} = "
                  f"{hi if upper else lo:.6f})   step {step:.2e}")
        best = (y, c.copy())
    return best


if __name__ == '__main__':
    np.set_printoptions(linewidth=150)
    print("=" * 78)
    print("CONTROL CASE (4,6,3,2): (i)+(ii) alone already force the band, so")
    print("the ascent MUST saturate at or below hi.")
    print("=" * 78)
    d = study(4, 6, 3, 2, seed=11, nsamp=140, ndir=20)
    r = ascend(d, 4, 6, 3, 2, iters=300, seed=11, upper=True)
    print(f"    ASCENT (upper): lambda_max -> {r[0]:.6f}   hi = {d['hi']:.6f}   "
          f"{'VIOLATION' if r[0] > d['hi']+1e-7 else 'inside'}")
    r2 = ascend(d, 4, 6, 3, 2, iters=300, seed=11, upper=False)
    print(f"    DESCENT (lower): lambda_min -> {r2[0]:.6f}   lo = {d['lo']:.6f}  "
          f"{'VIOLATION' if r2[0] < d['lo']-1e-7 else 'inside'}")
    print()

    print("=" * 78)
    print("THE TEST CASE (6,9,3,2): (i)+(ii) alone permit a root at ab = 6 >")
    print("hi = 5.82843.  Does STABILITY pull it back?")
    print("=" * 78)
    d = study(6, 9, 3, 2, seed=23, nsamp=140, ndir=20)
    r = ascend(d, 6, 9, 3, 2, iters=400, seed=23, upper=True)
    print(f"    ASCENT (upper): lambda_max -> {r[0]:.6f}   hi = {d['hi']:.6f}   "
          f"{'*** VIOLATION ***' if r[0] > d['hi']+1e-7 else 'inside'}")
    r2 = ascend(d, 6, 9, 3, 2, iters=400, seed=23, upper=False)
    print(f"    DESCENT (lower): lambda_min -> {r2[0]:.6f}   lo = {d['lo']:.6f}  "
          f"{'*** VIOLATION ***' if r2[0] < d['lo']-1e-7 else 'inside'}")
    np.save('/tmp/sr_c_69.npy', r[1])
