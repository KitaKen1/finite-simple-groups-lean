#!/usr/bin/env python3
"""Generate StabilizerChain.lean and FinalStabilizer.lean for SporadicM22."""

import json

st = json.load(open("output/lean_gen_state.json"))
data = json.load(open("output/m22_data.json"))
blocks = [tuple(b) for b in data["blocks"]]
N = 22
LEAN = {"a": "Gen.a", "A": "Gen.aInv", "b": "Gen.b", "B": "Gen.bInv"}

def word_lean(w):
    if not w:
        return "[]"
    return "[" + ", ".join(LEAN[c] for c in w) + "]"

def match_table(tbl):
    lines = []
    for x in sorted(int(k) for k in tbl):
        lines.append(f"  | {x} => {word_lean(tbl[str(x)])}")
    lines.append("  | _ => []")
    return "\n".join(lines)

def fs(b):
    return "{" + ", ".join(map(str, b)) + "}"

# ------------------------------------------------------- StabilizerChain.lean
header = """/-
Copyright (c) 2026 Kenta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta, Claude
-/
import SporadicM22.Certificates.Words
import SporadicM22.Certificates.SteinerSystem

/-!
# Stabilizer-chain certificates

Verified data for the cardinality route with base `0, 1, 2, 5, 3`:

* orbit of `0` has size `22`;
* the stabilizer of `0` has orbit size `21`;
* the stabilizer of `0,1` has orbit size `20`;
* the stabilizer of `0,1,2` moves `5` through the 16 points outside the
  block `B0 = {0,1,2,3,4,21}` (which it preserves);
* the stabilizer of `0,1,2,5` moves `3` through the 3 points
  `{3,4,21} = B0 \\ {0,1,2}`;
* the stabilizer of `0,1,2,5,3` is trivial (`FinalStabilizer.lean`).

No external computation is trusted here until it is represented as data and
checked by Lean.
-/

namespace Sporadic
namespace M22Certificates
namespace StabilizerChain

open SteinerSystem

/-- The product of the target stabilizer-chain indices. -/
theorem target_index_product : 22 * 21 * 20 * 16 * 3 = 443520 := by
  norm_num
"""

word_defs = f"""
/-- First-step words: `orbitZeroWord x` sends `0` to `x`. -/
def orbitZeroWord (x : Fin 22) : Word :=
  match x.val with
{match_table(st["lv0"])}

/-- Second-step words: fix `0`, send `1` to `x`. -/
def zeroStabilizerWord (x : Fin 22) : Word :=
  match x.val with
{match_table(st["lv1"])}

/-- Third-step words: fix `0,1`, send `2` to `x`. -/
def zeroOneStabilizerWord (x : Fin 22) : Word :=
  match x.val with
{match_table(st["lv2"])}

/-- Fourth-step words: fix `0,1,2`, send `5` to `x` (for `x` outside `B0`). -/
def levelFourWord (x : Fin 22) : Word :=
  match x.val with
{match_table(st["lv3"])}

/-- Fifth-step words: fix `0,1,2,5`, send `3` to `x` (for `x` in `B0 \\ {{0,1,2}}`). -/
def levelFiveWord (x : Fin 22) : Word :=
  match x.val with
{match_table(st["lv4"])}
"""

decides = """
set_option maxRecDepth 400000 in
/-- The first-step certificate words send `0` to every point. -/
theorem orbitZeroWord_maps_zero_all :
    ∀ x : Fin 22, (Word.eval (orbitZeroWord x)) (0 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The second-step certificate words fix `0`. -/
theorem zeroStabilizerWord_fixes_zero_all :
    ∀ x : Fin 22, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The second-step certificate words send `1` to the requested point. -/
theorem zeroStabilizerWord_maps_one_all :
    ∀ x : Fin 22, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (1 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words fix `0`. -/
theorem zeroOneStabilizerWord_fixes_zero_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words fix `1`. -/
theorem zeroOneStabilizerWord_fixes_one_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words send `2` to the requested point. -/
theorem zeroOneStabilizerWord_maps_two_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `0`. -/
theorem levelFourWord_fixes_zero_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `1`. -/
theorem levelFourWord_fixes_one_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `2`. -/
theorem levelFourWord_fixes_two_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (2 : Fin 22) = 2 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words send `5` to the requested point. -/
theorem levelFourWord_maps_five_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (5 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `0`. -/
theorem levelFiveWord_fixes_zero_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `1`. -/
theorem levelFiveWord_fixes_one_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `2`. -/
theorem levelFiveWord_fixes_two_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (2 : Fin 22) = 2 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `5`. -/
theorem levelFiveWord_fixes_five_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (5 : Fin 22) = 5 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words send `3` to the requested point. -/
theorem levelFiveWord_maps_three_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (3 : Fin 22) = x := by
  decide

end StabilizerChain
end M22Certificates
end Sporadic
"""

with open("../SporadicM22/Certificates/StabilizerChain.lean", "w") as f:
    f.write(header + word_defs + decides)
print("wrote StabilizerChain.lean")

# ------------------------------------------------------ FinalStabilizer.lean
stepsA = st["stepsA"]
stepsB = st["stepsB"]
kbA = {int(k): (tuple(v[0]), v[1]) for k, v in st["kbA"].items()}
kbB = {int(k): (tuple(v[0]), v[1]) for k, v in st["kbB"].items()}
tau = st["tau"]
BASE_VALS = {0: 0, 1: 1, 2: 2, 5: 5, 3: 3}

def gen_branch(tag, steps, kb, seed4):
    """Emit decide lemmas + the branch theorem body."""
    values = dict(BASE_VALS)
    values[4] = seed4
    hv = {p: f"h{p}" for p in BASE_VALS}
    hv[4] = "h4"
    lemmas = []     # decide lemma texts
    body = []       # have-chain
    kb_emitted = {}
    at_emitted = {}

    def emit_at(idx):
        if idx in at_emitted:
            return at_emitted[idx]
        lname = f"at{tag}_{idx}"
        lemmas.append(
f"""set_option maxRecDepth 100000 in
private theorem {lname} :
    wittBlockAt ({idx} : Fin 77) = ({fs(blocks[idx])} : Block) := by
  decide""")
        at_emitted[idx] = lname
        return lname

    def emit_kb(bi):
        if bi in kb_emitted:
            return kb_emitted[bi]
        (triple, tgt) = kb[bi]
        Bsrc, Btgt = blocks[bi], blocks[tgt]
        imgs = [values[p] for p in triple]
        lname = f"uniq{tag}_{bi}"
        lemmas.append(
f"""set_option maxHeartbeats 1600000 in
-- The indexed uniqueness certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
private theorem {lname} :
    ∀ i : Fin 77, ({imgs[0]} : Fin 22) ∈ wittBlockAt i →
      ({imgs[1]} : Fin 22) ∈ wittBlockAt i → ({imgs[2]} : Fin 22) ∈ wittBlockAt i →
      i = ({tgt} : Fin 77) := by
  decide""")
        src_at = emit_at(bi)
        tgt_at = emit_at(tgt)
        hname = f"hKB{tag}_{bi}"
        args = " ".join(hv[p] for p in triple)
        body.append(
f"""  have {hname} : blockMap π ({fs(Bsrc)} : Block) = ({fs(Btgt)} : Block) :=
    blockMap_eq_of_three π hpres {src_at} (by decide) (by decide) (by decide)
      {args} {lname} {tgt_at}""")
        kb_emitted[bi] = hname
        return hname

    for si, (w, v, bis, excl) in enumerate(steps):
        mem_args = []
        for (bi, tgt) in bis:
            hname = emit_kb(bi)
            mem_args.append((hname, tgt))
        # decide lemma; prune exclusions to the candidate intersection
        needed = set(blocks[mem_args[0][1]])
        for (_, tgt) in mem_args[1:]:
            needed &= set(blocks[tgt])
        needed.discard(v)
        conds = []
        for k, (_, tgt) in enumerate(mem_args):
            conds.append(f"v ∈ ({fs(blocks[tgt])} : Block)")
        seen_e = set()
        excl_pairs = []
        for (u, e) in excl:
            if e in seen_e or u == w or e not in needed:
                continue
            seen_e.add(e)
            excl_pairs.append((u, e))
            conds.append(f"v ≠ {e}")
        assert {e for (_, e) in excl_pairs} == needed, (w, v, needed, excl_pairs)
        lname = f"step{tag}_{si}"
        cond_str = " → ".join(conds)
        lemmas.append(
f"""private theorem {lname} :
    ∀ v : Fin 22, {cond_str} → v = {v} := by
  decide""")
        # have chain
        mems = []
        for k, (hname, tgt) in enumerate(mem_args):
            mems.append(f"(mem_of_blockMap_eq π {hname} (by decide))")
        nes = []
        for (u, e) in excl_pairs:
            nes.append(f"(ne_of_value π {hv[u]} (by decide))")
        hvname = f"hv{tag}_{w}"
        body.append(
f"""  have {hvname} : π {w} = {v} :=
    {lname} _ {' '.join(mems + nes)}""")
        hv[w] = hvname
        values[w] = v
    return lemmas, body, hv, values

lemmasA, bodyA, hvA, valuesA = gen_branch("A", stepsA, kbA, 4)
lemmasB, bodyB, hvB, valuesB = gen_branch("B", stepsB, kbB, 21)
assert all(valuesA[x] == x for x in range(N))
assert [valuesB[x] for x in range(N)] == tau

finalA_cases = "\n".join(f"  · exact {hvA[x]}.trans (by decide)" for x in range(N))
finalB_cases = "\n".join(f"  · exact {hvB[x]}.trans (by decide)" for x in range(N))

tau_cycles = []
seen = [False]*N
for x in range(N):
    if not seen[x]:
        c = [x]; seen[x] = True; y = tau[x]
        while y != x:
            c.append(y); seen[y] = True; y = tau[y]
        if len(c) > 1:
            tau_cycles.append(c)
tau_def = " *\n    ".join(
    f"List.formPerm ([{', '.join(map(str, c))}] : List (Fin 22))" for c in tau_cycles)

final = f"""/-
Copyright (c) 2026 Kenta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta, Claude
-/
import SporadicM22.Certificates.SteinerSystem

/-!
# The final stabilizer certificate

This file proves that a degree-22 permutation that preserves the candidate
`S(3,6,22)` block set, is even, and fixes the five base points `0,1,2,3,5`
is the identity.

The full automorphism group of the design is `M22:2`; the pointwise
stabilizer of the base inside it has order two, generated by an odd
involution `tauOuter`. The proof therefore splits on `π 4`:

* if `π 4 = 4`, forced block propagation pins every point and `π = 1`;
* if `π 4 = 21`, forced propagation pins `π = tauOuter`, which is odd —
  contradicting evenness.

All propagation steps are Lean-checked `decide` certificates generated by
`scripts/gen_lean_m22_part2.py`.
-/

namespace Sporadic
namespace M22Certificates
namespace FinalStabilizer

open SteinerSystem

/-- The outer involution of `Aut(S(3,6,22)) = M22:2` fixing the base. -/
def tauOuter : Perm22 :=
  {tau_def}

set_option maxRecDepth 40000 in
/-- The outer involution is odd. -/
theorem tauOuter_sign : Equiv.Perm.sign tauOuter = -1 := by
  decide

set_option maxRecDepth 100000 in
/-- The block `B0` pins `π 4` to `4` or `21` once `0,1,2,3` are fixed. -/
private theorem pin_four :
    ∀ v : Fin 22, v ∈ blockB0 → v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 3 →
      v = 4 ∨ v = 21 := by
  decide

{chr(10).join(lemmasA)}

{chr(10).join(lemmasB)}

/-- Branch `π 4 = 4`: forced propagation yields the identity. -/
theorem eq_one_of_fix_four (π : Perm22)
    (hpres : ∀ B ∈ wittBlockList, blockMap π B ∈ wittBlocks)
    (h0 : π 0 = 0) (h1 : π 1 = 1) (h2 : π 2 = 2) (h3 : π 3 = 3)
    (h5 : π 5 = 5) (h4 : π 4 = 4) : π = 1 := by
{chr(10).join(bodyA)}
  apply Equiv.ext
  intro x
  fin_cases x
{finalA_cases}

/-- Branch `π 4 = 21`: forced propagation yields the outer involution. -/
theorem eq_tau_of_swap_four (π : Perm22)
    (hpres : ∀ B ∈ wittBlockList, blockMap π B ∈ wittBlocks)
    (h0 : π 0 = 0) (h1 : π 1 = 1) (h2 : π 2 = 2) (h3 : π 3 = 3)
    (h5 : π 5 = 5) (h4 : π 4 = 21) : π = tauOuter := by
{chr(10).join(bodyB)}
  apply Equiv.ext
  intro x
  fin_cases x
{finalB_cases}

/--
Any even degree-22 permutation that preserves the checked blocks and fixes
`0,1,2,3,5` is the identity. This is the ambient final-stabilizer certificate.
-/
theorem fixed_base_preserves_wittBlocks_eq_one (π : Perm22)
    (hg : PreservesWittBlocks π) (hsign : Equiv.Perm.sign π = 1)
    (h0 : π 0 = 0) (h1 : π 1 = 1) (h2 : π 2 = 2) (h3 : π 3 = 3)
    (h5 : π 5 = 5) : π = 1 := by
  have hpres := hg.1
  have hKB0 : blockMap π blockB0 = blockB0 :=
    blockMap_eq_of_three π hpres wittBlockAt_zero (by decide) (by decide)
      (by decide) h0 h1 h2 unique_block_012 wittBlockAt_zero
  have hmem4 : π 4 ∈ blockB0 := mem_of_blockMap_eq π hKB0 (by decide)
  have h4or : π 4 = 4 ∨ π 4 = 21 :=
    pin_four _ hmem4
      (ne_of_value π h0 (by decide)) (ne_of_value π h1 (by decide))
      (ne_of_value π h2 (by decide)) (ne_of_value π h3 (by decide))
  rcases h4or with h4 | h4
  · exact eq_one_of_fix_four π hpres h0 h1 h2 h3 h5 h4
  · exfalso
    have htau := eq_tau_of_swap_four π hpres h0 h1 h2 h3 h5 h4
    rw [htau, tauOuter_sign] at hsign
    exact absurd hsign (by decide)

end FinalStabilizer
end M22Certificates
end Sporadic
"""

with open("../SporadicM22/Certificates/FinalStabilizer.lean", "w") as f:
    f.write(final)
print("wrote FinalStabilizer.lean")
print(f"branch A: {len(lemmasA)} lemmas, branch B: {len(lemmasB)} lemmas")
