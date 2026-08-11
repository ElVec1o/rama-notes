# Clean Proof: Partition Self-Divisibility at Small Primes

## Statement

**Proposition.** Let p(n) denote the number of integer partitions of n.
Then:

  (i)   p(5)  ≡ 2 (mod 5)
  (ii)  p(7)  ≡ 1 (mod 7)
  (iii) p(11) ≡ 1 (mod 11)

Consequently, 7 and 11 belong to the set S = { n ≥ 2 : n | (p(n) − 1) },
while 5 does not.


## Preliminaries

We use two classical results.

**Euler's Pentagonal Number Theorem (1741).** For all n ≥ 1,

    p(n) = Σ_{k=1}^{∞} (-1)^{k+1} [ p(n − ω_k) + p(n − ω_{-k}) ]

where ω_k = k(3k−1)/2 are the generalized pentagonal numbers, and
p(m) = 0 for m < 0, p(0) = 1. The sum terminates when both ω_k > n and
ω_{-k} > n.

The first few generalized pentagonal numbers are:

    ω_1 = 1,  ω_{-1} = 2,  ω_2 = 5,  ω_{-2} = 7,  ω_3 = 12,  ω_{-3} = 15

**Partition values (direct computation or standard table).**

    p(0) = 1,  p(1) = 1,  p(2) = 2,  p(3) = 3,  p(4) = 5,
    p(5) = 7,  p(6) = 11, p(9) = 30, p(10) = 42


## Proof

### (i) p(5) ≡ 2 (mod 5)

Apply the pentagonal recurrence at n = 5. The generalized pentagonal
numbers ≤ 5 are ω_1 = 1, ω_{-1} = 2, ω_2 = 5. Next is ω_{-2} = 7 > 5,
so the recurrence terminates:

    p(5) = p(5 − 1) + p(5 − 2) − p(5 − 5)
         = p(4) + p(3) − p(0)
         = 5 + 3 − 1
         = 7

Now 7 = 1 · 5 + 2, so p(5) ≡ 2 (mod 5). In particular, 5 ∤ (p(5) − 1),
so 5 ∉ S. ∎


### (ii) p(7) ≡ 1 (mod 7)

Apply the pentagonal recurrence at n = 7. The generalized pentagonal
numbers ≤ 7 are ω_1 = 1, ω_{-1} = 2, ω_2 = 5, ω_{-2} = 7. Next is
ω_3 = 12 > 7, so:

    p(7) = p(7 − 1) + p(7 − 2) − p(7 − 5) − p(7 − 7)
         = p(6) + p(5) − p(2) − p(0)
         = 11 + 7 − 2 − 1
         = 15

Observe that the term p(5) = 7 vanishes modulo 7 (trivially: 7 ≡ 0 mod 7).
The remaining terms give:

    p(7) ≡ 11 + 0 − 2 − 1 ≡ 8 ≡ 1 (mod 7)

Hence 7 | (p(7) − 1), i.e., 7 ∈ S. ∎


### (iii) p(11) ≡ 1 (mod 11)

Apply the pentagonal recurrence at n = 11. The generalized pentagonal
numbers ≤ 11 are ω_1 = 1, ω_{-1} = 2, ω_2 = 5, ω_{-2} = 7. Next is
ω_3 = 12 > 11, so:

    p(11) = p(11 − 1) + p(11 − 2) − p(11 − 5) − p(11 − 7)
          = p(10) + p(9) − p(6) − p(4)
          = 42 + 30 − 11 − 5
          = 56

Observe that the term p(6) = 11 vanishes modulo 11 (trivially: 11 ≡ 0 mod 11).
The remaining terms give:

    p(11) ≡ 42 + 30 − 0 − 5  (mod 11)
           ≡ 9 + 8 − 0 − 5   (mod 11)      [reducing each: 42=3·11+9, 30=2·11+8, 5=5]
           ≡ 12               (mod 11)
           ≡ 1                (mod 11)

Hence 11 | (p(11) − 1), i.e., 11 ∈ S. ∎


## Remark

The vanishing terms — p(5) = 7 in part (ii) and p(6) = 11 in part (iii) —
are the n = 0 instances of Ramanujan's congruences p(7n + 5) ≡ 0 (mod 7)
and p(11n + 6) ≡ 0 (mod 11). However, at n = 0 these reduce to the
tautologies 7 ≡ 0 (mod 7) and 11 ≡ 0 (mod 11). The full strength of
Ramanujan's theorem is not invoked.

The reason the pentagonal recurrence at n = q involves a term p(β_q)
where β_q is Ramanujan's "magic residue" (β_5 = 4, β_7 = 5, β_11 = 6)
traces to the algebraic identity 24 · ω_k + 1 = (6k − 1)². Setting
q = |6k − 1| yields β_q = q − ω_k, so the pentagonal recurrence for
p(q) necessarily contains the term p(β_q). For the three Ramanujan primes
q = 5, 7, 11, we have the numerical coincidence p(β_q) = q, making this
term vanish modulo q.

For the next prime q = 13: β_13 = 6 and p(6) = 11 ≠ 13, so the
mechanism does not produce p(13) ≡ 1 (mod 13). Indeed, p(13) = 101 ≡ 10
(mod 13).
