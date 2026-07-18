#!/usr/bin/env python3
"""Verification of Paper 3, Theorem 3 (3|a(n) for n>=13) and its engine.
(A)  orbit lemma: >=3 columns equal mod 3  =>  3 | perm  (2000 random matrices)
(A') stronger integer form: 3 exactly-equal columns => 6 | perm
(C)  type-A numbers (all prime factors == 1 mod 3): 1,7,13,... 3rd is 13.
"""
from itertools import permutations
import random

def perm_brute(M):
    n=len(M); t=0
    for s in permutations(range(n)):
        p=1
        for i in range(n): p*=M[i][s[i]]
        t+=p
    return t

random.seed(1); bad=0
for _ in range(2000):
    n=random.randint(3,6)
    M=[[random.randint(0,8) for _ in range(n)] for _ in range(n)]
    cs=random.sample(range(n),3)
    for i in range(n):
        v=M[i][cs[0]]%3
        for c in cs[1:]: M[i][c]=v+3*random.randint(0,3)
    if perm_brute(M)%3!=0: bad+=1
print(f"(A) 3 cols equal mod 3 => 3|perm : {bad}/2000 violations")

bad2=0
for _ in range(2000):
    n=random.randint(3,6)
    M=[[random.randint(0,8) for _ in range(n)] for _ in range(n)]
    cs=random.sample(range(n),3)
    for i in range(n):
        for c in cs[1:]: M[i][c]=M[i][cs[0]]
    if perm_brute(M)%6!=0: bad2+=1
print(f"(A') 3 cols equal over Z => 6|perm : {bad2}/2000 violations")

def typeA(j):
    x=j
    for p in range(2,j+1):
        if x%p==0:
            if p%3!=1: return False
            while x%p==0: x//=p
    return True
tA=[j for j in range(1,60) if typeA(j)]
print(f"(C) type-A numbers <60: {tA}; 3rd = {tA[2]} => threshold n>={tA[2]}")
