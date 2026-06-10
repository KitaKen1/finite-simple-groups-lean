#!/usr/bin/env python3
"""Certificate data for the L34 (= PSL(3,4)) simplicity layer.

Produces scripts/output/l34_data.json with everything the Lean generator
needs. All claims are checked here and re-verified by Lean `decide`.
"""

import json
import random
from collections import deque
from itertools import combinations

# ----------------------------------------------------- PG(2,4) (as before)
MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]

def gf_mul(a, b):
    return MUL[a][b]

def normalize(v):
    for c in v:
        if c != 0:
            inv = next(d for d in range(1, 4) if gf_mul(c, d) == 1)
            return tuple(gf_mul(inv, x) for x in v)
    return None

pts = sorted({normalize((x, y, z)) for x in range(4) for y in range(4)
              for z in range(4) if (x, y, z) != (0, 0, 0)})
assert len(pts) == 21
pt_idx = {p: i for i, p in enumerate(pts)}
N = 21

def vadd(u, v):
    return tuple(a ^ b for a, b in zip(u, v))

def smul(c, u):
    return tuple(gf_mul(c, x) for x in u)

# ------------------------------------------------------------- elations
# elation with center <v> and functional phi (phi(v)=0): u -> u + phi(u) v
def functional(a, b, c):
    return lambda u: gf_mul(a, u[0]) ^ gf_mul(b, u[1]) ^ gf_mul(c, u[2])

elations = {}   # center index -> list of perm tuples (sorted canonically)
for x in range(N):
    v = pts[x]
    perms = set()
    for a in range(4):
        for b in range(4):
            for c in range(4):
                if (a, b, c) == (0, 0, 0):
                    continue
                phi = functional(a, b, c)
                if phi(v) != 0:
                    continue
                p = []
                for i, u in enumerate(pts):
                    img = normalize(vadd(u, smul(phi(u), v)))
                    p.append(pt_idx[img])
                p = tuple(p)
                assert p != tuple(range(N))
                perms.add(p)
    perms = sorted(perms)
    assert len(perms) == 15, (x, len(perms))
    for p in perms:
        # involution with exactly 5 fixed points (the axis)
        assert all(p[p[i]] == i for i in range(N))
        assert sum(1 for i in range(N) if p[i] == i) == 5
        assert p[x] == x
    elations[x] = perms

IDENT = tuple(range(N))

def compose(g, h):
    return tuple(g[h[i]] for i in range(N))

def bfs_group(gens, cap=30000):
    seen = {IDENT}
    dq = deque([IDENT])
    while dq:
        p = dq.popleft()
        for g in gens:
            q = compose(g, p)
            if q not in seen:
                if len(seen) >= cap:
                    return None
                seen.add(q)
                dq.append(q)
    return seen

# ------------------------------------------- choose 3 elation generators
rng = random.Random(2026)
all_elations = [(x, k) for x in range(N) for k in range(15)]
gens = None
for _ in range(200):
    picks = rng.sample(all_elations, 3)
    gs = [elations[x][k] for (x, k) in picks]
    grp = bfs_group(gs)
    if grp is not None and len(grp) == 20160:
        gens = picks
        break
assert gens is not None
e = [elations[x][k] for (x, k) in gens]
centers = [x for (x, k) in gens]
print("generators (center,k):", gens, "order 20160: ok")

# --------------------------------------------------- BFS with 3 letters
words = {IDENT: ""}
order_list = [IDENT]
dq = deque([IDENT])
LET = "123"
while dq:
    p = dq.popleft()
    w = words[p]
    for i, g in enumerate(e):
        q = compose(g, p)
        if q not in words:
            words[q] = w + LET[i]
            order_list.append(q)
            dq.append(q)
assert len(words) == 20160

def find_words(fixes, base_pt, targets):
    found, need = {}, set(targets)
    for g in order_list:
        if all(g[f] == f for f in fixes):
            x = g[base_pt]
            if x in need and x not in found:
                found[x] = words[g]
                if len(found) == len(need):
                    break
    assert len(found) == len(need)
    return found

orbit0 = find_words([], 0, [x for x in range(N) if x != 0])
stab0 = find_words([0], 1, [x for x in range(N) if x != 0 and x != 1])
maxlen = max(max(len(w) for w in orbit0.values()),
             max(len(w) for w in stab0.values()))
print("orbit/stab tables done, max word length", maxlen)

# 48 distinct elements fixing 0 and 1 (first in BFS order)
stab01_words = []
stab01_perms = []
for g in order_list:
    if g[0] == 0 and g[1] == 1:
        stab01_words.append(words[g])
        stab01_perms.append(g)
        if len(stab01_words) == 48:
            break
assert len(stab01_words) == 48
assert len(set(stab01_perms)) == 48
stab01_count = sum(1 for g in order_list if g[0] == 0 and g[1] == 1)
assert stab01_count == 48
print("stab01: exactly 48 elements; 48 word certificates collected")

# elation words at center 0
elation0_words = []
for k in range(15):
    g = elations[0][k]
    assert g in words
    elation0_words.append(words[g])
print("elation-at-0 words, max length",
      max(len(w) for w in elation0_words))

# ------------------------------------------------------- conj index tables
conj_tables = []
for i, g in enumerate(e):
    tbl = []
    for x in range(N):
        row = []
        gx = g[x]
        for k in range(15):
            q = compose(compose(g, elations[x][k]), g)  # g e g^{-1}, g inv
            assert q in elations[gx], "conjugate not an elation at gx"
            row.append(elations[gx].index(q))
        tbl.append(row)
    conj_tables.append(tbl)
print("conj tables ok")

# commutativity at 0
for k in range(15):
    for kk in range(15):
        assert compose(elations[0][k], elations[0][kk]) == \
               compose(elations[0][kk], elations[0][k])
print("elations at 0 commute pairwise")

# ------------------------------------------------- commutator identities
def inv(g):
    p = [0] * N
    for i in range(N):
        p[g[i]] = i
    return tuple(p)

comm_ids = []
for i, g in enumerate(e):
    found = None
    for (x1, k1) in all_elations:
        u = elations[x1][k1]
        for (x2, k2) in all_elations:
            v = elations[x2][k2]
            if compose(compose(u, v), compose(inv(u), inv(v))) == g:
                found = ((x1, k1), (x2, k2))
                break
        if found:
            break
    assert found is not None, f"generator {i} is not a commutator of elations"
    comm_ids.append(found)
    print(f"e{i+1} = [elation{found[0]}, elation{found[1]}]")

# ----------------------------------------------------------- M22-side data
data22 = json.load(open("output/m22_data.json"))
A22 = tuple(data22["gen_a"])
B22 = tuple(data22["gen_b"])
N22 = 22

def compose22(g, h):
    return tuple(g[h[i]] for i in range(N22))

def inv22(g):
    p = [0] * N22
    for i in range(N22):
        p[g[i]] = i
    return tuple(p)

I22 = tuple(range(N22))
LET22 = [("a", A22), ("A", inv22(A22)), ("b", B22), ("B", inv22(B22))]

print("BFS over M22 ...", flush=True)
words22 = {I22: ""}
order22 = [I22]
dq = deque([I22])
while dq:
    p = dq.popleft()
    w = words22[p]
    for ch, g in LET22:
        q = compose22(g, p)
        if q not in words22:
            words22[q] = w + ch
            order22.append(q)
            dq.append(q)
assert len(words22) == 443520

# embedded generators (fix 21)
emb = []
for g in e:
    p = list(g) + [21]
    emb.append(tuple(p))
emb_words = []
for p in emb:
    assert p in words22, "embedded elation not in M22!"
    emb_words.append(words22[p])
print("embedded generator words, lengths", [len(w) for w in emb_words])

def find_words22(fixes, base_pt, targets):
    found, need = {}, set(targets)
    for g in order22:
        if all(g[f] == f for f in fixes):
            x = g[base_pt]
            if x in need and x not in found:
                found[x] = words22[g]
                if len(found) == len(need):
                    break
    assert len(found) == len(need)
    return found

last_orbit = find_words22([], 21, [x for x in range(N22) if x != 21])
last_stab = find_words22([21], 0, [x for x in range(N22 - 1) if x != 0])
print("M22 last-point tables done, max lengths",
      max(len(w) for w in last_orbit.values()),
      max(len(w) for w in last_stab.values()))

# ---------------------------------------------------------------- emit
def perm_cycles(p, n):
    seen = [False] * n
    out = []
    for i in range(n):
        if not seen[i]:
            c = [i]
            seen[i] = True
            j = p[i]
            while j != i:
                c.append(j)
                seen[j] = True
                j = p[j]
            if len(c) > 1:
                out.append(c)
    return out

json.dump({
    "gens": gens,
    "gen_perms": [list(g) for g in e],
    "gen_cycles": [perm_cycles(g, N) for g in e],
    "centers": centers,
    "elations": {str(x): [perm_cycles(p, N) for p in elations[x]]
                 for x in range(N)},
    "conj_tables": conj_tables,
    "orbit0": orbit0,
    "stab0": stab0,
    "stab01_words": stab01_words,
    "elation0_words": elation0_words,
    "comm_ids": comm_ids,
    "emb_words": emb_words,
    "last_orbit": last_orbit,
    "last_stab": last_stab,
}, open("output/l34_data.json", "w"))
print("wrote output/l34_data.json")
print("ALL CHECKS PASSED")
