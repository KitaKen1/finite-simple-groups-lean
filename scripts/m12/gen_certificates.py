#!/usr/bin/env python3
"""Certificate data generator for the SporadicM12 Lean project.

This script produces *candidate* certificate data (words, blocks, index lists).
Nothing here is trusted: every claim is re-verified by Lean `decide` proofs.

Generators (zero-based on {0,...,11}):
  a = (0 1 2 3 4 5 6 7 8 9 10)            -- 11-cycle, fixes 11
  b = (2 6 10 7)(3 9 4 5)                  -- fixes 0, 1, 8, 11
  c = (0 11)(1 10)(2 5)(3 7)(4 8)(6 9)     -- involution moving 11

In one-based notation these are the classical M12 generators
  (1..11), (3,7,11,8)(4,10,5,6), (1,12)(2,11)(3,6)(4,8)(5,9)(7,10).
"""

from collections import deque
from itertools import combinations
import sys

N = 12

def cycles_to_perm(cycles, n=N):
    p = list(range(n))
    for cyc in cycles:
        for i, x in enumerate(cyc):
            p[x] = cyc[(i + 1) % len(cyc)]
    return tuple(p)

def compose(g, h):
    """(g . h)(x) = g(h(x))"""
    return tuple(g[h[x]] for x in range(N))

def inverse(g):
    p = [0] * N
    for x in range(N):
        p[g[x]] = x
    return tuple(p)

IDENT = tuple(range(N))

a = cycles_to_perm([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]])
b = cycles_to_perm([[2, 6, 10, 7], [3, 9, 4, 5]])
c = cycles_to_perm([[0, 11], [1, 10], [2, 5], [3, 7], [4, 8], [6, 9]])

# letter -> (perm, lean name)
LETTERS = [
    ("a", a, "Gen.a"),
    ("A", inverse(a), "Gen.aInv"),
    ("b", b, "Gen.b"),
    ("B", inverse(b), "Gen.bInv"),
    ("c", c, "Gen.c"),
    ("C", inverse(c), "Gen.cInv"),
]

def word_to_lean(word):
    return "[" + ", ".join(LETTERS["aAbBcC".index(ch)][2] for ch in word) + "]"

def word_perm(word):
    """Word applied left-to-right (matches Lean Word.eval)."""
    p = IDENT
    for ch in word:
        g = LETTERS["aAbBcC".index(ch)][1]
        p = compose(g, p)
    return p

# ---------------------------------------------------------------- group BFS
print("BFS over the group ...", flush=True)
words = {IDENT: ""}
order_list = [IDENT]
dq = deque([IDENT])
while dq:
    p = dq.popleft()
    w = words[p]
    for ch, g, _ in LETTERS:
        q = compose(g, p)  # apply g after p => word w + ch
        if q not in words:
            words[q] = w + ch
            order_list.append(q)
            dq.append(q)

print(f"group order = {len(words)}")
assert len(words) == 95040, "generated group does not have order 95040!"

# sanity: words round-trip
for p, w in list(words.items())[:100]:
    assert word_perm(w) == p

# sanity: 5-point stabilizer trivial
stab5 = [p for p in order_list if all(p[i] == i for i in range(5))]
print(f"|stab(0,1,2,3,4)| = {len(stab5)}")
assert stab5 == [IDENT]

# parity check: all generators even (subgroup of A12)
def is_even(p):
    seen = [False] * N
    parity = 0
    for x in range(N):
        if not seen[x]:
            l = 0
            y = x
            while not seen[y]:
                seen[y] = True
                y = p[y]
                l += 1
            parity ^= (l - 1) & 1
    return parity == 0

assert is_even(a) and is_even(b) and is_even(c)
print("all generators even: ok")

# ------------------------------------------------- stabilizer-chain words
BASE = [0, 1, 2, 3, 4]

def find_level_words(k):
    """For each target x with x != BASE[j] for j<k and x != BASE[k],
    the first BFS element fixing BASE[0..k-1] pointwise and sending BASE[k] to x."""
    targets = {}
    needed = set(range(N)) - set(BASE[:k]) - {BASE[k]}
    for p in order_list:
        if all(p[BASE[j]] == BASE[j] for j in range(k)):
            x = p[BASE[k]]
            if x in needed and x not in targets:
                targets[x] = words[p]
                if len(targets) == len(needed):
                    break
    assert len(targets) == len(needed)
    return targets

level_words = []
for k in range(5):
    tw = find_level_words(k)
    level_words.append(tw)
    maxlen = max(len(w) for w in tw.values())
    print(f"level {k}: {len(tw)} targets, max word length {maxlen}")

with open(OUT := "output/stabilizer_words.txt", "w") as f:
    for k, tw in enumerate(level_words):
        f.write(f"-- level {k}: fixes {BASE[:k]}, moves {BASE[k]} to x\n")
        for x in sorted(tw):
            f.write(f"  | {x} => {word_to_lean(tw[x])}\n")
        f.write("\n")
print(f"wrote {OUT}")

# ------------------------------------------------------- Steiner S(5,6,12)
print("searching for the Steiner block orbit ...")
seed = None
for y in range(5, N):
    B0 = frozenset([0, 1, 2, 3, 4, y])
    seen = {B0}
    dq = deque([B0])
    while dq:
        B = dq.popleft()
        for _, g, _ in LETTERS[:6:2]:  # a, b, c suffice
            BB = frozenset(g[x] for x in B)
            if BB not in seen:
                seen.add(BB)
                dq.append(BB)
        if len(seen) > 132:
            break
    if len(seen) == 132:
        seed = B0
        blocks = sorted(sorted(B) for B in seen)
        print(f"seed block = {sorted(B0)} (y0 = {y}), orbit size 132")
        break
assert seed is not None, "no 132-block orbit found"
y0 = sorted(seed)[5]

# Steiner property sanity: every 5-subset of {0..11} is in exactly one block
from itertools import combinations as comb
count = {}
for B in blocks:
    for five in comb(B, 5):
        count[five] = count.get(five, 0) + 1
assert len(count) == 792 and all(v == 1 for v in count.values())
print("Steiner property S(5,6,12): ok")

block_index = {frozenset(B): i for i, B in enumerate(blocks)}

with open(OUT := "output/blocks.txt", "w") as f:
    for B in blocks:
        f.write("    ({" + ", ".join(map(str, B)) + "} : Block),\n")
print(f"wrote {OUT}")

# block-index permutation lists for each letter
with open(OUT := "output/block_index_lists.txt", "w") as f:
    for ch, g, lean in LETTERS:
        idxs = []
        for B in blocks:
            BB = frozenset(g[x] for x in B)
            idxs.append(block_index[BB])
        f.write(f"-- letter {ch} ({lean})\n")
        f.write("  [" + ", ".join(map(str, idxs)) + "]\n\n")
print(f"wrote {OUT}")

# seed lemma sanity: {0,1,2,3,4,x} is a block iff x == y0
for x in range(N):
    inb = frozenset([0, 1, 2, 3, 4, x]) in block_index
    assert inb == (x == y0)
print(f"seed lemma: {{0,1,2,3,4,x}} in blocks iff x = {y0}")

# ------------------------------------------------------- outside pairings
outside = sorted(set(range(N)) - set(BASE) - {y0})
print(f"outside points: {outside}")
out_idx = {p: i for i, p in enumerate(outside)}

taus = {}  # T (tuple of 4 base points) -> perm on 6 coords
for T in comb(BASE, 4):
    tau = [None] * 6
    for p in outside:
        five = frozenset(T) | {p}
        # unique block containing this 5-set
        found = [B for B in blocks if five <= set(B)]
        assert len(found) == 1
        q = (set(found[0]) - five).pop()
        assert q in out_idx and q != p
        tau[out_idx[p]] = out_idx[q]
    tau = tuple(tau)
    # involution without fixed points
    assert all(tau[tau[i]] == i and tau[i] != i for i in range(6))
    taus[T] = tau
    cycles = sorted({tuple(sorted((i, tau[i]))) for i in range(6)})
    print(f"  tau{''.join(map(str, T))} = {cycles}")

# common centralizer of all taus must be trivial; find sigma products.
def compose6(g, h):
    return tuple(g[h[x]] for x in range(6))

tau_list = sorted(taus.items())
# search products t1*t2*...*tk (lean mult, applied right-to-left) over tau words
# of length up to 4 such that the product has unique fixed point x.
from itertools import product as iproduct
sigma = {}
for length in range(2, 5):
    for combo in iproduct(range(len(tau_list)), repeat=length):
        p = IDENT6 = tuple(range(6))
        for i in combo:
            p = compose6(p, tau_list[i][1])  # left-assoc product
        fixed = [x for x in range(6) if p[x] == x]
        if len(fixed) == 1 and fixed[0] not in sigma:
            sigma[fixed[0]] = (combo, p)
    if len(sigma) == 6:
        break
assert len(sigma) == 6, f"only found sigmas for {sorted(sigma)}"

def tau_name(T):
    return "tau" + "".join(map(str, T))

with open(OUT := "output/pairings.txt", "w") as f:
    f.write(f"y0 = {y0}\noutside = {outside}\n\n")
    for T, tau in tau_list:
        cycles = sorted({tuple(sorted((i, tau[i]))) for i in range(6)})
        f.write(f"def {tau_name(T)} : OutsidePerm :=\n")
        parts = [f"List.formPerm ([{i}, {j}] : List Outside)" for i, j in cycles]
        f.write("  " + " *\n    ".join(parts) + "\n\n")
    for x in range(6):
        combo, p = sigma[x]
        names = [tau_name(tau_list[i][0]) for i in combo]
        f.write(f"-- unique fixed point {x}\n")
        f.write(f"def sigma{x} : OutsidePerm :=\n  " + " * ".join(names) + "\n\n")
print(f"wrote {OUT}")

# final-stabilizer sanity at the ambient level: any permutation of S12 fixing
# 0..4 and preserving the block set is the identity.  (7! = 5040 candidates)
from itertools import permutations as perms
blockset = set(map(frozenset, blocks))
rest = [x for x in range(N) if x >= 5]
cnt = 0
for img in perms(rest):
    p = list(range(N))
    for src, dst in zip(rest, img):
        p[src] = dst
    p = tuple(p)
    if all(frozenset(p[x] for x in B) in blockset for B in blocks):
        cnt += 1
        assert p == IDENT
assert cnt == 1
print("ambient final-stabilizer triviality: ok")
print("ALL CHECKS PASSED")
