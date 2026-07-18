"""8-adic secret sauce: v2(a(n)) grows ~linearly, tracking v2(n!)~n.
Data: v2(a(n))=...,20,21,20,23 at n=24..27 vs v2(n!)=22,22,23,23 (within +-5).
min_sigma sum_i min(v2(i),v2(sig i)) = 0  => high v2 is CANCELLATION, not term-wise.
=> "24|a(n) for 13<=n<=30" is the small-n shadow of v_p(a(n))->infinity.
Linear lower bound v2(a(n))>=cn is open."""
