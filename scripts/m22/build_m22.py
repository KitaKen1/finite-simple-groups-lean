#!/usr/bin/env python3
"""Construct M22 on 22 points from first principles, verifiably.

Plan:
  1. Build PG(2,4): 21 points, 21 lines over GF(4).
  2. Generate PSL(3,4) as permutations of the 21 points via SL(3,4)
     transvections.
  3. Blocks of S(3,6,22): {line + infinity} (21) plus one PSL-orbit of
     hyperovals (56).  Verify the Steiner property directly.
  4. Find an automorphism of the design moving infinity by backtracking.
  5. M22 := the order-443520 group generated; find a nice 2-element
     generating set.

Every important claim is checked directly in this script, and everything
that matters for Lean is re-verified by `decide` later.
"""

import random
from collections import deque
from itertools import combinations

# ---------------------------------------------------------------- GF(4)
# elements 0,1,2,3 ; 2 = w, 3 = w+1 ; addition = xor
MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]

def gf_mul(a, b):
    return MUL[a][b]

def gf_add(a, b):
    return a ^ b

# ---------------------------------------------------------------- PG(2,4)
def normalize(v):
    """Scale so the first nonzero coordinate is 1."""
    for c in v:
        if c != 0:
            inv = next(d for d in range(1, 4) if gf_mul(c, d) == 1)
            return tuple(gf_mul(inv, x) for x in v)
    return None

pts = sorted({normalize((x, y, z)) for x in range(4) for y in range(4)
              for z in range(4) if (x, y, z) != (0, 0, 0)})
assert len(pts) == 21
pt_idx = {p: i for i, p in enumerate(pts)}
INF = 21  # the extra point
N = 22

lines = []
for a in range(4):
    for b in range(4):
        for c in range(4):
            if (a, b, c) == (0, 0, 0):
                continue
            if normalize((a, b, c)) != (a, b, c):
                continue
            line = frozenset(pt_idx[p] for p in pts
                             if gf_add(gf_add(gf_mul(a, p[0]), gf_mul(b, p[1])),
                                       gf_mul(c, p[2])) == 0)
            assert len(line) == 5
            lines.append(line)
assert len(lines) == 21

# ---------------------------------------------------------------- SL(3,4)
def mat_mul(A, B):
    return tuple(tuple(
        gf_add(gf_add(gf_mul(A[i][0], B[0][j]), gf_mul(A[i][1], B[1][j])),
               gf_mul(A[i][2], B[2][j])) for j in range(3)) for i in range(3))

def mat_apply(A, p):
    v = tuple(gf_add(gf_add(gf_mul(A[i][0], p[0]), gf_mul(A[i][1], p[1])),
                     gf_mul(A[i][2], p[2])) for i in range(3))
    return normalize(v)

def transvection(i, j, lam):
    M = [[1 if r == c else 0 for c in range(3)] for r in range(3)]
    M[i][j] = lam
    return tuple(tuple(r) for r in M)

sl_gens = [transvection(i, j, lam)
           for (i, j) in [(0, 1), (1, 0), (1, 2), (2, 1)] for lam in (1, 2)]

def mat_to_perm22(M):
    p = [0] * N
    for i, pt in enumerate(pts):
        p[i] = pt_idx[mat_apply(M, pt)]
    p[INF] = INF
    return tuple(p)

def compose(g, h):
    return tuple(g[h[x]] for x in range(N))

def inverse(g):
    p = [0] * N
    for x in range(N):
        p[g[x]] = x
    return tuple(p)

IDENT = tuple(range(N))

psl_gens = [mat_to_perm22(M) for M in sl_gens]

def bfs_group(gens, cap=10**6):
    seen = {IDENT}
    dq = deque([IDENT])
    gg = []
    for g in gens:
        gg += [g, inverse(g)]
    while dq:
        p = dq.popleft()
        for g in gg:
            q = compose(g, p)
            if q not in seen:
                if len(seen) >= cap:
                    return None
                seen.add(q)
                dq.append(q)
    return seen

psl = bfs_group(psl_gens)
print("|PSL(3,4)| =", len(psl))
assert len(psl) == 20160

# ------------------------------------------------------------ hyperovals
# standard hyperoval: triangle + unit point + the two conic completions
H0 = frozenset(pt_idx[p] for p in
               [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (1, 2, 3), (1, 3, 2)])
assert len(H0) == 6
for tri in combinations(sorted(H0), 3):
    assert not any(set(tri) <= l for l in lines), "H0 has 3 collinear points"

# PSL-orbit of H0
orbit = {H0}
dq = deque([H0])
while dq:
    H = dq.popleft()
    for g in psl_gens:
        HH = frozenset(g[x] for x in H)
        if HH not in orbit:
            orbit.add(HH)
            dq.append(HH)
print("hyperoval orbit size =", len(orbit))
assert len(orbit) == 56

blocks = sorted(sorted(l | {INF}) for l in lines) + sorted(sorted(H) for H in orbit)
blocks = sorted(blocks)
assert len(blocks) == 77
blockset = set(map(frozenset, blocks))

# Steiner property S(3,6,22)
cnt = {}
for B in blocks:
    for tri in combinations(B, 3):
        cnt[tri] = cnt.get(tri, 0) + 1
assert len(cnt) == 1540 and all(v == 1 for v in cnt.values())
print("Steiner property S(3,6,22): ok")

# --------------------------------------------- automorphisms via backtracking
pt_blocks = [[] for _ in range(N)]
for bi, B in enumerate(blocks):
    for x in B:
        pt_blocks[x].append(bi)

pair_blocks = {}
for bi, B in enumerate(blocks):
    for x, y in combinations(B, 2):
        pair_blocks.setdefault(frozenset((x, y)), []).append(bi)

def find_automorphism(prescribed, rng):
    """Backtracking search for a design automorphism extending `prescribed`
    (a dict point -> image)."""
    img = dict(prescribed)
    used = set(img.values())

    def consistent(x):
        # every triple inside the domain must map to a block-triple iff source is
        dom = list(img)
        for y, z in combinations(dom, 2):
            if y == x or z == x:
                continue
            for t in combinations((x, y, z), 3):
                src_in = any(set(t) <= set(B) for B in blockset
                             if False) # placeholder
        return True

    # precompute triple-in-block lookup
    def triple_block(t):
        return frozenset(t) in triple_set

    dom_order = sorted(range(N), key=lambda x: (x not in img,))

    def extend():
        undef = [x for x in range(N) if x not in img]
        if not undef:
            # full assignment: accept only if it preserves the block set
            return all(frozenset(img[x] for x in B) in blockset for B in blocks)
        x = undef[0]
        cands = [v for v in range(N) if v not in used]
        rng.shuffle(cands)
        for v in cands:
            ok = True
            dom = [d for d in img]
            for y, z in combinations(dom, 2):
                src = frozenset((x, y, z))
                if len(src) < 3:
                    continue
                tgt = frozenset((v, img[y], img[z]))
                if (src in triple_set) != (tgt in triple_set):
                    ok = False
                    break
            if ok:
                # fully-assigned blocks must map to blocks
                for bi in pt_blocks[x]:
                    B = blocks[bi]
                    if all(p == x or p in img for p in B):
                        tgt = frozenset(v if p == x else img[p] for p in B)
                        if tgt not in blockset:
                            ok = False
                            break
            if ok:
                img[x] = v
                used.add(v)
                if extend():
                    return True
                del img[x]
                used.discard(v)
        return False

    if extend():
        return tuple(img[x] for x in range(N))
    return None

triple_set = set()
for B in blocks:
    for tri in combinations(B, 3):
        triple_set.add(frozenset(tri))

rng = random.Random(12345)
ext = find_automorphism({INF: 0}, rng)
assert ext is not None
assert all(frozenset(ext[x] for x in B) in blockset for B in blocks)
print("found design automorphism moving infinity:", ext[INF] == 0)

# --------------------------------------------------------------- the group
full = bfs_group(psl_gens + [ext])
print("|<PSL(3,4), ext>| =", len(full))

if len(full) == 887040:
    # M22:2 ; M22 is its derived subgroup; find an even-coset fix:
    # try ext * s for elements s until the generated group has order 443520
    elems = list(psl)[:200]
    target = None
    for s in elems:
        cand = compose(ext, s)
        grp = bfs_group(psl_gens + [cand], cap=500000)
        if grp is not None and len(grp) == 443520:
            target = cand
            break
    assert target is not None
    full = bfs_group(psl_gens + [target])
    ext = target

assert len(full) == 443520
print("|M22| = 443520: ok")

# every element preserves the blocks (sanity on generators only)
for g in psl_gens + [ext]:
    assert all(frozenset(g[x] for x in B) in blockset for B in blocks)
print("generators preserve the design: ok")

# ------------------------------------------------- find a 2-generator set
rng2 = random.Random(999)
full_list = list(full)
pair = None
for _ in range(200):
    x = rng2.choice(full_list)
    y = rng2.choice(full_list)
    grp = bfs_group([x, y], cap=443520)
    if grp is not None and len(grp) == 443520:
        pair = (x, y)
        break
print("2-generator pair found:", pair is not None)

import json
with open("output/m22_data.json", "w") as f:
    json.dump({
        "gen_a": list(pair[0]),
        "gen_b": list(pair[1]),
        "blocks": [list(B) for B in blocks],
    }, f)
print("wrote output/m22_data.json")
