#!/usr/bin/env python3
"""Generate the data-heavy Lean source files for SporadicM22.

Outputs (in the repo root, overwriting):
  SporadicM22/Certificates/SteinerSystem.lean   (blocks + index certificates)
  SporadicM22/Certificates/StabilizerChain.lean (5 levels of orbit words)
  SporadicM22/Certificates/FinalStabilizer.lean (forced propagation, 2 branches)
  output/permutations.txt                       (generator cycle decompositions)

All generated claims are checked here first; Lean re-verifies them by decide.
"""

import json
from collections import deque

data = json.load(open("output/m22_data.json"))
A = tuple(data["gen_a"])
B = tuple(data["gen_b"])
blocks = [tuple(b) for b in data["blocks"]]
N = 22
blockset = set(map(frozenset, blocks))
block_index = {frozenset(b): i for i, b in enumerate(blocks)}

def compose(g, h): return tuple(g[h[x]] for x in range(N))
def inverse(g):
    p = [0]*N
    for x in range(N): p[g[x]] = x
    return tuple(p)
IDENT = tuple(range(N))
LETTERS = [("a", A, "Gen.a"), ("A", inverse(A), "Gen.aInv"),
           ("b", B, "Gen.b"), ("B", inverse(B), "Gen.bInv")]

def cycles(p):
    seen = [False]*N
    out = []
    for x in range(N):
        if not seen[x]:
            c = [x]; seen[x] = True; y = p[x]
            while y != x:
                c.append(y); seen[y] = True; y = p[y]
            if len(c) > 1: out.append(c)
    return out

with open("output/permutations.txt", "w") as f:
    for nm, g in [("m22a", A), ("m22b", B)]:
        cyc = cycles(g)
        parts = [f"List.formPerm ([{', '.join(map(str,c))}] : List (Fin 22))" for c in cyc]
        f.write(f"def {nm} : Perm22 :=\n  " + " *\n    ".join(parts) + "\n\n")
print("wrote output/permutations.txt")

# ------------------------------------------------------------------ words
print("BFS with words ...", flush=True)
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

B0 = next(b for b in blocks if {0,1,2} <= set(b))
p4 = min(x for x in range(N) if x not in B0)   # 5
p5 = min(x for x in B0 if x not in (0,1,2))    # 3
BASE = [0,1,2,p4,p5]
assert B0 == (0,1,2,3,4,21) and p4 == 5 and p5 == 3

def find_words(fixes, base_pt, targets):
    found, need = {}, set(targets)
    for g in order_list:
        if all(g[f] == f for f in fixes):
            x = g[base_pt]
            if x in need and x not in found:
                found[x] = words[g]
                if len(found) == len(need): break
    assert len(found) == len(need)
    return found

lv0 = find_words([], 0, [x for x in range(N) if x != 0])
lv1 = find_words([0], 1, [x for x in range(N) if x not in (0,1)])
lv2 = find_words([0,1], 2, [x for x in range(N) if x not in (0,1,2)])
lv3 = find_words([0,1,2], p4, sorted(set(range(N)) - set(B0) - {p4}))
lv4 = find_words([0,1,2,p4], p5, sorted(set(B0) - {0,1,2,p5}))

def word_lean(w):
    return "[" + ", ".join(LETTERS["aAbB".index(c)][2] for c in w) + "]"

def match_table(tbl):
    lines = []
    for x in sorted(tbl):
        lines.append(f"  | {x} => {word_lean(tbl[x])}")
    lines.append("  | _ => []")
    return "\n".join(lines)

# ------------------------------------------------------- forced propagation
def step_witnesses(seed):
    """Forced propagation with per-step witnesses.

    Returns (m, steps) where each step is
      (w, target, [(blockIdx, tgtIdx)], [(srcPoint, imgValue)])
    meaning: pi w is in both target blocks, differs from the listed images,
    and that pins it down to `target`."""
    m = dict(seed)
    steps = []
    kb = {}      # blockIdx -> (triple of source points, target block idx)

    def refresh_known():
        for bi, Bk in enumerate(blocks):
            if bi in kb: continue
            kn = [p for p in Bk if p in m]
            if len(kn) >= 3:
                imgs = [m[p] for p in kn[:3]]
                tgt = [j for j, B2 in enumerate(blocks) if set(imgs) <= set(B2)]
                assert len(tgt) == 1
                kb[bi] = (tuple(kn[:3]), tgt[0])

    changed = True
    while changed and len(m) < N:
        changed = False
        refresh_known()
        for w in sorted(set(range(N)) - set(m)):
            wbs = [bi for bi in kb if w in blocks[bi]]
            best = None
            # candidate set from one block: imgs of its known points excluded
            def block_cand(bi):
                tgt = set(blocks[kb[bi][1]])
                excl = [(p, m[p]) for p in blocks[bi] if p in m]
                return tgt - {e for _, e in excl}, excl
            for i in range(len(wbs)):
                c1, e1 = block_cand(wbs[i])
                if len(c1) == 1:
                    best = (c1.pop(), [wbs[i]], e1)
                    break
                for j in range(i+1, len(wbs)):
                    c2, e2 = block_cand(wbs[j])
                    inter = c1 & c2
                    if len(inter) == 1:
                        best = (inter.pop(), [wbs[i], wbs[j]], e1 + e2)
                        break
                if best: break
            if best:
                v, bis, excl = best
                m[w] = v
                steps.append((w, v, [(bi, kb[bi][1]) for bi in bis], excl))
                changed = True
                refresh_known()
    return m, steps, kb

seedA = {b: b for b in BASE}; seedA[4] = 4
mA, stepsA, kbA = step_witnesses(seedA)
assert len(mA) == N and all(mA[x] == x for x in range(N))
seedB = {b: b for b in BASE}; seedB[4] = 21
mB, stepsB, kbB = step_witnesses(seedB)
assert len(mB) == N
tau = tuple(mB[x] for x in range(N))
assert all(frozenset(tau[x] for x in b) in blockset for b in blocks)
print(f"branch A: {len(stepsA)} steps; branch B: {len(stepsB)} steps")

# ------------------------------------------------------------- Lean: Steiner
def fs(b):  # finset literal
    return "{" + ", ".join(map(str, b)) + "}"

block_lines = ",\n".join(f"    ({fs(b)} : Block)" for b in blocks)

idx_lists = {}
for ch, g, lean in LETTERS:
    idx_lists[ch] = [block_index[frozenset(g[x] for x in b)] for b in blocks]

def idx_lean(lst):
    out, line = [], "   "
    for v in lst:
        tok = f" {v},"
        if len(line) + len(tok) > 95:
            out.append(line); line = "   "
        line += tok
    out.append(line)
    s = "\n".join(out)
    return "[" + s.strip().rstrip(",") + "]"

steiner = f"""/-
Copyright (c) 2026 Kenta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta, Claude
-/
import SporadicM22.GeneratedSubgroup

/-!
# The Steiner system S(3,6,22) certificate workspace

The 77 blocks below are the candidate blocks of the large Witt design
`S(3,6,22)`. The data is not trusted: Lean checks the finite claims recorded
here, including the block-index certificates for both generators.
-/

namespace Sporadic
namespace M22Certificates
namespace SteinerSystem

/-- A block is a finite set of points in the degree-22 action. -/
abbrev Block : Type :=
  Finset (Fin 22)

/-- Candidate `S(3,6,22)` blocks, in zero-based notation. -/
def wittBlockList : List Block :=
  [
{block_lines}
  ]

/-- The candidate blocks as a `Finset`. -/
def wittBlocks : Finset Block :=
  wittBlockList.toFinset

set_option maxRecDepth 100000 in
/-- The candidate block list has no duplicate blocks. -/
theorem wittBlockList_nodup : wittBlockList.Nodup := by
  decide

set_option maxRecDepth 100000 in
/-- The candidate block list has length 77. -/
theorem wittBlockList_length : wittBlockList.length = 77 := by
  decide

/-- The block with certificate index `i`. -/
def wittBlockAt (i : Fin 77) : Block :=
  wittBlockList.get ⟨i.1, by rw [wittBlockList_length]; exact i.2⟩

/-- Every indexed candidate block belongs to `wittBlocks`. -/
theorem wittBlockAt_mem (i : Fin 77) : wittBlockAt i ∈ wittBlocks := by
  rw [wittBlocks]
  exact List.mem_toFinset.mpr (List.get_mem wittBlockList _)

/-- Membership in the listed blocks gives membership in the block finset. -/
theorem mem_wittBlocks_of_mem_wittBlockList {{B : Block}} (hB : B ∈ wittBlockList) :
    B ∈ wittBlocks := by
  rw [wittBlocks]
  exact List.mem_toFinset.mpr hB

/-- Membership in the block finset comes from membership in the listed blocks. -/
theorem mem_wittBlockList_of_mem_wittBlocks {{B : Block}} (hB : B ∈ wittBlocks) :
    B ∈ wittBlockList := by
  rw [wittBlocks] at hB
  exact List.mem_toFinset.mp hB

/-- Any member of `wittBlockList` is one of the indexed candidate blocks. -/
theorem exists_wittBlockAt_eq_get (i : Fin wittBlockList.length) :
    ∃ j : Fin 77, wittBlockList.get i = wittBlockAt j := by
  let j : Fin 77 := ⟨i.1, by simpa [wittBlockList_length] using i.2⟩
  refine ⟨j, ?_⟩
  unfold wittBlockAt
  congr

/-- Image of a block under a degree-22 permutation. -/
def blockMap (g : Perm22) (B : Block) : Block :=
  B.image g

@[simp]
theorem blockMap_one (B : Block) : blockMap (1 : Perm22) B = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_mul (g h : Perm22) (B : Block) :
    blockMap (g * h) B = blockMap g (blockMap h B) := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_inv_self (g : Perm22) (B : Block) :
    blockMap g⁻¹ (blockMap g B) = B := by
  ext x
  simp [blockMap]

/-- A permutation preserves the candidate block set. -/
def PreservesWittBlocks (g : Perm22) : Prop :=
  (∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks) ∧
    (∀ B ∈ wittBlockList, blockMap g⁻¹ B ∈ wittBlocks)

/-- A block-index permutation certificate for the action of `m22a`. -/
def m22aBlockIndexList : List (Fin 77) :=
  {idx_lean(idx_lists['a'])}

/-- A block-index permutation certificate for the action of `m22a⁻¹`. -/
def m22aInvBlockIndexList : List (Fin 77) :=
  {idx_lean(idx_lists['A'])}

/-- A block-index permutation certificate for the action of `m22b`. -/
def m22bBlockIndexList : List (Fin 77) :=
  {idx_lean(idx_lists['b'])}

/-- A block-index permutation certificate for the action of `m22b⁻¹`. -/
def m22bInvBlockIndexList : List (Fin 77) :=
  {idx_lean(idx_lists['B'])}

set_option maxRecDepth 10000 in
theorem m22aBlockIndexList_length : m22aBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22aInvBlockIndexList_length : m22aInvBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22bBlockIndexList_length : m22bBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22bInvBlockIndexList_length : m22bInvBlockIndexList.length = 77 := by
  decide

/-- The block-index map induced by `m22a`. -/
def m22aBlockIndex (i : Fin 77) : Fin 77 :=
  m22aBlockIndexList.get ⟨i.1, by rw [m22aBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22a⁻¹`. -/
def m22aInvBlockIndex (i : Fin 77) : Fin 77 :=
  m22aInvBlockIndexList.get ⟨i.1, by rw [m22aInvBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22b`. -/
def m22bBlockIndex (i : Fin 77) : Fin 77 :=
  m22bBlockIndexList.get ⟨i.1, by rw [m22bBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22b⁻¹`. -/
def m22bInvBlockIndex (i : Fin 77) : Fin 77 :=
  m22bInvBlockIndexList.get ⟨i.1, by rw [m22bInvBlockIndexList_length]; exact i.2⟩

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22a`. -/
theorem m22a_blockMapAt :
    ∀ i : Fin 77, blockMap m22a (wittBlockAt i) = wittBlockAt (m22aBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22a⁻¹`. -/
theorem m22aInv_blockMapAt :
    ∀ i : Fin 77, blockMap m22a⁻¹ (wittBlockAt i) =
      wittBlockAt (m22aInvBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22b`. -/
theorem m22b_blockMapAt :
    ∀ i : Fin 77, blockMap m22b (wittBlockAt i) = wittBlockAt (m22bBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22b⁻¹`. -/
theorem m22bInv_blockMapAt :
    ∀ i : Fin 77, blockMap m22b⁻¹ (wittBlockAt i) =
      wittBlockAt (m22bInvBlockIndex i) := by
  decide

/--
If a permutation has a verified block-index certificate, then it sends every
listed block to a listed block.
-/
theorem forall_mem_blockMap_mem_of_blockMapAt (g : Perm22) (index : Fin 77 → Fin 77)
    (h : ∀ i : Fin 77, blockMap g (wittBlockAt i) = wittBlockAt (index i)) :
    ∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks := by
  rw [List.forall_mem_iff_get]
  intro i
  obtain ⟨j, hget⟩ := exists_wittBlockAt_eq_get i
  rw [hget, h]
  exact wittBlockAt_mem (index j)

/--
A permutation preserves the candidate block set once both it and its inverse
have verified block-index certificates.
-/
theorem PreservesWittBlocks.of_blockMapAt (g : Perm22)
    (index invIndex : Fin 77 → Fin 77)
    (h : ∀ i : Fin 77, blockMap g (wittBlockAt i) = wittBlockAt (index i))
    (hinv : ∀ i : Fin 77, blockMap g⁻¹ (wittBlockAt i) = wittBlockAt (invIndex i)) :
    PreservesWittBlocks g :=
  ⟨forall_mem_blockMap_mem_of_blockMapAt g index h,
    forall_mem_blockMap_mem_of_blockMapAt g⁻¹ invIndex hinv⟩

theorem PreservesWittBlocks.one : PreservesWittBlocks (1 : Perm22) := by
  constructor <;> intro B hB
  · rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB
  · change blockMap (1 : Perm22) B ∈ wittBlocks
    rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB

theorem PreservesWittBlocks.mul {{g h : Perm22}}
    (hg : PreservesWittBlocks g) (hh : PreservesWittBlocks h) :
    PreservesWittBlocks (g * h) := by
  constructor
  · intro B hB
    rw [blockMap_mul]
    have hhB : blockMap h B ∈ wittBlocks := hh.1 B hB
    exact hg.1 (blockMap h B) (mem_wittBlockList_of_mem_wittBlocks hhB)
  · intro B hB
    rw [show (g * h)⁻¹ = h⁻¹ * g⁻¹ by simp, blockMap_mul]
    have hgB : blockMap g⁻¹ B ∈ wittBlocks := hg.2 B hB
    exact hh.2 (blockMap g⁻¹ B) (mem_wittBlockList_of_mem_wittBlocks hgB)

theorem PreservesWittBlocks.inv {{g : Perm22}}
    (hg : PreservesWittBlocks g) : PreservesWittBlocks g⁻¹ := by
  constructor
  · exact hg.2
  · exact hg.1

/-- The first generator preserves the candidate block set. -/
theorem m22a_preserves_wittBlocks : PreservesWittBlocks m22a :=
  PreservesWittBlocks.of_blockMapAt m22a m22aBlockIndex m22aInvBlockIndex
    m22a_blockMapAt m22aInv_blockMapAt

/-- The second generator preserves the candidate block set. -/
theorem m22b_preserves_wittBlocks : PreservesWittBlocks m22b :=
  PreservesWittBlocks.of_blockMapAt m22b m22bBlockIndex m22bInvBlockIndex
    m22b_blockMapAt m22bInv_blockMapAt

/-- Every element of the generated subgroup preserves the candidate block set. -/
theorem M22_preserves_wittBlocks (g : M22) : PreservesWittBlocks g.1 := by
  exact Subgroup.closure_induction
    (p := fun x hx => PreservesWittBlocks x)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact m22a_preserves_wittBlocks
      · exact m22b_preserves_wittBlocks)
    PreservesWittBlocks.one
    (fun x y _ _ hx hy => PreservesWittBlocks.mul hx hy)
    (fun x _ hx => PreservesWittBlocks.inv hx)
    g.2

/-- The block `B0` through the first three base points. -/
def blockB0 : Block :=
  ({fs(B0)} : Block)

set_option maxRecDepth 100000 in
/-- `B0` is the unique listed block through `0`, `1`, and `2`. -/
theorem unique_block_012 :
    ∀ C ∈ wittBlockList, (0 : Fin 22) ∈ C → (1 : Fin 22) ∈ C → (2 : Fin 22) ∈ C →
      C = blockB0 := by
  decide

/-- Membership of a point in the image block, given the point's image. -/
theorem mem_blockMap (g : Perm22) {{B : Block}} {{x : Fin 22}} (hx : x ∈ B)
    {{v : Fin 22}} (hv : g x = v) : v ∈ blockMap g B := by
  rw [← hv]
  exact Finset.mem_image_of_mem g hx

/-- Distinct points have distinct images. -/
theorem ne_of_value (g : Perm22) {{u w : Fin 22}} {{e : Fin 22}}
    (hu : g u = e) (hne : w ≠ u) : g w ≠ e := fun h =>
  hne (g.injective (h.trans hu.symm))

/--
A block with three known point images maps to the unique block through the
images.
-/
theorem blockMap_eq_of_three (g : Perm22)
    (hpres : ∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks)
    {{B B' : Block}} (hB : B ∈ wittBlockList)
    {{x y z : Fin 22}} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
    {{ix iy iz : Fin 22}} (hgx : g x = ix) (hgy : g y = iy) (hgz : g z = iz)
    (huniq : ∀ C ∈ wittBlockList, ix ∈ C → iy ∈ C → iz ∈ C → C = B') :
    blockMap g B = B' :=
  huniq _ (mem_wittBlockList_of_mem_wittBlocks (hpres B hB))
    (mem_blockMap g hx hgx) (mem_blockMap g hy hgy) (mem_blockMap g hz hgz)

/-- A member of a setwise-fixed block stays inside it. -/
theorem mem_of_blockMap_eq (g : Perm22) {{B B' : Block}}
    (hmap : blockMap g B = B') {{w : Fin 22}} (hw : w ∈ B) : g w ∈ B' := by
  rw [← hmap]
  exact Finset.mem_image_of_mem g hw

end SteinerSystem
end M22Certificates
end Sporadic
"""

with open("../SporadicM22/Certificates/SteinerSystem.lean", "w") as f:
    f.write(steiner)
print("wrote SteinerSystem.lean")

print("now run gen_lean_m22_part2.py for StabilizerChain and FinalStabilizer")
json.dump({
    "lv0": {str(k): v for k, v in lv0.items()},
    "lv1": {str(k): v for k, v in lv1.items()},
    "lv2": {str(k): v for k, v in lv2.items()},
    "lv3": {str(k): v for k, v in lv3.items()},
    "lv4": {str(k): v for k, v in lv4.items()},
    "stepsA": stepsA, "stepsB": stepsB,
    "kbA": {str(k): [list(v[0]), v[1]] for k, v in kbA.items()},
    "kbB": {str(k): [list(v[0]), v[1]] for k, v in kbB.items()},
    "tau": list(tau),
}, open("output/lean_gen_state.json", "w"))
print("saved generation state")
