"""C5 (FINISH LINE): c_inf = lim (a(n)/n!)^{1/n} = infinity, UNCONDITIONAL.
Rigorous construction: log gcd(i,j) >= sum_{p<=P} log p * 1[p|i]1[p|j], so
a(n) >= perm(tildeM). Partition [1,n] into 2^pi(P) divisibility blocks V_S;
when prod_{p<=P} p | n the block sizes |V_S| = n*mu_S EXACTLY (complete residue
systems), mu_S = prod_{p in S}(1/p) prod_{p not in S}(1-1/p). Block-constant
w_ij = n rho_{S(i)S(j)}/(|V_S||V_S'|), rho = tensor_p rho^(p) (optimal Bernoulli
couplings), is EXACTLY doubly stochastic and gives, by the entropy/VdW bound,
   (1/n) F(w) - log n = sum_{p<=P} g_p ,  g_p ~ (2 ln phi - phi^-2)/p (golden).
VERIFIED numerically (P={2,3,5}, n=210000): rate=0.44316 = g2+g3+g5 exactly.
sum_p g_p ~ (2 ln phi - phi^-2) loglog P -> infinity (Mertens) => c_inf=infinity.
Cleanup: g_p(y)=eps*Psi(y)+O(eps^2), eps=1/p, Psi=-y-y log y-2(1-y)log(1-y),
so p g_p = Psi(y)+O(1/p); max at (1-y)^2=y, y=phi^-2 => liminf p g_p >= 2 ln phi
- phi^-2 RIGOROUSLY (explicit O(1/p) error)."""
