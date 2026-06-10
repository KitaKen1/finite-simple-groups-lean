#!/usr/bin/env python3
"""Certificate data generator for the SporadicM22 Lean project.

Loads the verified group data from output/m22_data.json (built by
build_m22.py) and produces:

  * stabilizer-chain words for the base 0, 1, 2, p4, p5
    (orbit sizes 22, 21, 20, 16, 3);
  * block-index permutation lists for the two generators and inverses;
  * the unique block B0 through {0,1,2} and base point choices p4, p5;
  * a propagation certificate showing that a block-preserving permutation
    fixing the five base points is the identity;
  * Lean source fragments for all of the above.

Everything is re-verified by Lean `decide` later; this script is untrusted.
"""

import json
from collections import deque
from itertools import combinations

data = json.load(open("output/m22_data.json"))
A = tuple(data["gen_a"])
B = tuple(data["gen_b"])
blocks = [tuple(b) for b in data["blocks"]]
N = 22

def compose(g, h):
    return tuple(g[h[x]] for x in range(N))

def inverse(g):
    p = [0] * N
    for x in range(N):
        p[g[x]] = x
    return tuple(p)

IDENT = tuple(range(N))
LETTERS = [("a", A, "Gen.a"), ("A", inverse(A), "Gen.aInv"),
           ("b", B, "Gen.b"), ("B", inverse(B), "Gen.bInv")]

def word_to_lean(word):
    return "[" + ", ".join(LETTERS["aAbB".index(ch)][2] for ch in word) + "]"

# ---------------------------------------------------------------- group BFS
print("BFS over M22 ...", flush=True)
words = {IDENT: ""}
order_list = [IDENT]
dq = deque([IDENT])
while dq:
    p = dq.popleft()
    w = words[p]
    for ch, g, _ in LETTERS:
        q = compose(g, p)
        if q not in words:
            words[q] = w + ch
            order_list.append(q)
            dq.append(q)
assert len(words) == 443520
print("group order 443520: ok")

blockset = set(map(frozenset, blocks))
for _, g, _ in LETTERS:
    assert all(frozenset(g[x] for x in Bk) in blockset for Bk in blocks)
print("generators preserve blocks: ok")

# parity (M22 <= A22)
def is_even(p):
    seen = [False] * N
    par = 0
    for x in range(N):
        if not seen[x]:
            l, y = 0, x
            while not seen[y]:
                seen[y] = True
                y = p[y]
                l += 1
            par ^= (l - 1) & 1
    return par == 0
assert is_even(A) and is_even(B)
print("generators even: ok")

# ------------------------------------------------------------- base points
B0 = next(Bk for Bk in blocks if {0, 1, 2} <= set(Bk))
print("B0 =", B0)
p4 = min(x for x in range(N) if x not in B0)
p5 = min(x for x in B0 if x not in (0, 1, 2))
print("p4 =", p4, " p5 =", p5)
BASE = [0, 1, 2, p4, p5]

# verify the stabilizer chain orbit sizes by filtering the full group
def stab(elems, pt):
    return [g for g in elems if g[pt] == pt]

G0 = order_list
orbit0 = {g[0] for g in G0}
G1 = stab(G0, 0)
orbit1 = {g[1] for g in G1}
G2 = stab(G1, 1)
orbit2 = {g[2] for g in G2}
G3 = stab(G2, 2)
orbit3 = {g[p4] for g in G3}
G4 = stab(G3, p4)
orbit4 = {g[p5] for g in G4}
G5 = stab(G4, p5)
print("orbit sizes:", len(orbit0), len(orbit1), len(orbit2), len(orbit3), len(orbit4))
print("|G3| =", len(G3), " |G4| =", len(G4), " |G5| =", len(G5))
assert len(orbit0) == 22 and len(orbit1) == 21 and len(orbit2) == 20
assert orbit3 == set(range(N)) - set(B0) and len(orbit3) == 16
assert orbit4 == set(B0) - {0, 1, 2} and len(orbit4) == 3
assert G5 == [IDENT]
print("stabilizer chain 22*21*20*16*3, trivial tail: ok")

# ----------------------------------------------------- words for each level
def find_words(fixes, base_pt, targets):
    found = {}
    need = set(targets)
    for g in order_list:
        if all(g[f] == f for f in fixes):
            x = g[base_pt]
            if x in need and x not in found:
                found[x] = words[g]
                if len(found) == len(need):
                    break
    assert len(found) == len(need)
    return found

levels = []
levels.append(find_words([], 0, [x for x in range(N) if x != 0]))
levels.append(find_words([0], 1, [x for x in range(N) if x not in (0, 1)]))
levels.append(find_words([0, 1], 2, [x for x in range(N) if x not in (0, 1, 2)]))
levels.append(find_words([0, 1, 2], p4, sorted(set(range(N)) - set(B0) - {p4})))
levels.append(find_words([0, 1, 2, p4], p5, sorted(set(B0) - {0, 1, 2, p5})))

with open("output/stabilizer_words.txt", "w") as f:
    names = ["orbitZeroWord", "zeroStabWord", "zeroOneStabWord",
             "levelFourWord", "levelFiveWord"]
    for k, lv in enumerate(levels):
        maxlen = max(len(w) for w in lv.values())
        f.write(f"-- level {k} ({names[k]}), {len(lv)} targets, max word length {maxlen}\n")
        for x in sorted(lv):
            f.write(f"  | {x} => {word_to_lean(lv[x])}\n")
        f.write("\n")
        print(f"level {k}: {len(lv)} targets, max word length {maxlen}")
print("wrote output/stabilizer_words.txt")

# -------------------------------------------------------- block index lists
block_index = {frozenset(Bk): i for i, Bk in enumerate(blocks)}
with open("output/blocks_and_indices.txt", "w") as f:
    f.write("-- 77 blocks of S(3,6,22)\n")
    for Bk in blocks:
        f.write("    ({" + ", ".join(map(str, Bk)) + "} : Block),\n")
    f.write("\n")
    for ch, g, lean in LETTERS:
        idxs = [block_index[frozenset(g[x] for x in Bk)] for Bk in blocks]
        f.write(f"-- index list for {lean}\n")
        f.write("  [" + ", ".join(map(str, idxs)) + "]\n\n")
print("wrote output/blocks_and_indices.txt")

# ------------------------------------------------- propagation certificate
# rules:
#  - a block with >=3 pointwise-fixed points is setwise fixed ("known")
#  - if w lies in two known blocks B, B' with (B cap B') sub {w} cup fixed,
#    then w is pointwise fixed
fixed = set(BASE)
steps = []          # (w, blockIdx1, triple1, blockIdx2, triple2, other)
known_cache = {}    # blockIdx -> triple used

def known_blocks():
    res = {}
    for bi, Bk in enumerate(blocks):
        inter = sorted(set(Bk) & fixed)
        if len(inter) >= 3:
            res[bi] = inter[:3]
    return res

while len(fixed) < N:
    kb = known_blocks()
    progress = False
    for w in sorted(set(range(N)) - fixed):
        wbs = [bi for bi in kb if w in blocks[bi]]
        done = False
        for i in range(len(wbs)):
            for j in range(i + 1, len(wbs)):
                b1, b2 = wbs[i], wbs[j]
                inter = set(blocks[b1]) & set(blocks[b2])
                if inter - {w} <= fixed:
                    other = sorted(inter - {w})
                    assert len(other) <= 1
                    steps.append((w, b1, kb[b1], b2, kb[b2],
                                  other[0] if other else None))
                    fixed.add(w)
                    progress = done = True
                    break
            if done:
                break
        if done:
            continue
    if not progress:
        print("PROPAGATION STUCK at", sorted(fixed))
        break

assert len(fixed) == N, f"propagation incomplete: {sorted(fixed)}"
print(f"propagation: all 22 points fixed in {len(steps)} steps")

with open("output/propagation.txt", "w") as f:
    f.write(f"BASE = {BASE}\nB0 = {B0}\n\n")
    for (w, b1, t1, b2, t2, other) in steps:
        f.write(f"step: fix {w} via block#{b1} {blocks[b1]} (triple {t1}) "
                f"and block#{b2} {blocks[b2]} (triple {t2}), other={other}\n")
print("wrote output/propagation.txt")

# sanity at the ambient level: no nontrivial block-preserving permutation
# fixes the five base points (propagation already implies it, but re-check
# the logic on a few random block-preserving permutations)
import random
rng = random.Random(7)
for _ in range(5):
    g = rng.choice(order_list)
    if all(g[b] == b for b in BASE):
        assert g == IDENT
print("ALL CHECKS PASSED")
