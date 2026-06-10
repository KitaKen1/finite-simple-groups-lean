/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.Certificates.StabilizerChain

/-!
# Orbit equalities for the stabilizer chain

This file turns the word certificates of `StabilizerChain.lean` into the five
orbit-size theorems used by the cardinality proof:

* `orbit_zero_ncard = 22`,
* `stabilizer_zero_orbit_one_ncard = 21`,
* `stabilizer_zero_one_orbit_two_ncard = 20`,
* `stab012_orbit_five_ncard = 16` (the complement of the block `B0`),
* `stab0125_orbit_three_ncard = 3` (the rest of the block `B0`).

The upper bounds at the last two levels use the verified block-preservation
certificates: an element fixing `0,1,2` maps the unique block through them to
itself.
-/

namespace Sporadic
namespace M22Certificates
namespace ChainOrbits

open StabilizerChain SteinerSystem

/-! ## Level 1: the orbit of `0` -/

theorem first_orbit_M22_witness (x : Fin 22) :
    ∃ g : M22, g.1 (0 : Fin 22) = x :=
  ⟨Word.toM22 (orbitZeroWord x), by simpa using orbitZeroWord_maps_zero_all x⟩

theorem orbit_zero_eq_univ : MulAction.orbit M22 (0 : Fin 22) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := first_orbit_M22_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem orbit_zero_ncard : (MulAction.orbit M22 (0 : Fin 22)).ncard = 22 := by
  rw [orbit_zero_eq_univ, Set.ncard_univ]
  simp

/-! ## Level 2: the stabilizer of `0` moving `1` -/

def zeroStabilizerElement (x : Fin 22) (hx : x ≠ 0) :
    MulAction.stabilizer M22 (0 : Fin 22) :=
  ⟨Word.toM22 (zeroStabilizerWord x), by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroStabilizerWord x)) (0 : Fin 22) = 0
    exact zeroStabilizerWord_fixes_zero_all x hx⟩

theorem second_orbit_stabilizer_witness (x : Fin 22) (hx : x ≠ 0) :
    ∃ g : MulAction.stabilizer M22 (0 : Fin 22), g.1.1 (1 : Fin 22) = x :=
  ⟨zeroStabilizerElement x hx, by
    change (Word.eval (zeroStabilizerWord x)) (1 : Fin 22) = x
    exact zeroStabilizerWord_maps_one_all x hx⟩

theorem stabilizer_zero_orbit_one_eq_nonzero :
    MulAction.orbit (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22) =
      {x : Fin 22 | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩ hx0
    have hfix : g.1.1 (0 : Fin 22) = 0 := by
      have hg0 := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
    have hmap : g.1.1 (1 : Fin 22) = 0 := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
    have h10 : (1 : Fin 22) = 0 := g.1.1.injective (by rw [hmap, hfix])
    exact (by decide : (1 : Fin 22) ≠ 0) h10
  · intro hx
    obtain ⟨g, hg⟩ := second_orbit_stabilizer_witness x hx
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stabilizer_zero_orbit_one_ncard :
    (MulAction.orbit (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22)).ncard = 21 := by
  rw [stabilizer_zero_orbit_one_eq_nonzero]
  have hset : ({x : Fin 22 | x ≠ 0} : Set (Fin 22)) = ({0} : Set (Fin 22))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/-! ## Level 3: the stabilizer of `0,1` moving `2` -/

def zeroOneStabilizerElement (x : Fin 22) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22) :=
  let g0 : MulAction.stabilizer M22 (0 : Fin 22) :=
    ⟨Word.toM22 (zeroOneStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 22) = 0
      exact zeroOneStabilizerWord_fixes_zero_all x hx0 hx1⟩
  ⟨g0, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 22) = 1
    exact zeroOneStabilizerWord_fixes_one_all x hx0 hx1⟩

theorem third_orbit_stabilizer_witness (x : Fin 22) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ g : MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22),
      g.1.1.1 (2 : Fin 22) = x :=
  ⟨zeroOneStabilizerElement x hx0 hx1, by
    change (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 22) = x
    exact zeroOneStabilizerWord_maps_two_all x hx0 hx1⟩

theorem stabilizer_zero_one_orbit_two_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
        (2 : Fin 22) =
      {x : Fin 22 | x ≠ 0 ∧ x ≠ 1} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1 (0 : Fin 22) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1 (2 : Fin 22) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h20 : (2 : Fin 22) = 0 := g.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (2 : Fin 22) ≠ 0) h20
    · intro hx1
      have hfix1 : g.1.1.1 (1 : Fin 22) = 1 := by
        have hg1 := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
      have hmap : g.1.1.1 (2 : Fin 22) = 1 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
      have h21 : (2 : Fin 22) = 1 := g.1.1.1.injective (by rw [hmap, hfix1])
      exact (by decide : (2 : Fin 22) ≠ 1) h21
  · rintro ⟨hx0, hx1⟩
    obtain ⟨g, hg⟩ := third_orbit_stabilizer_witness x hx0 hx1
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stabilizer_zero_one_orbit_two_ncard :
    (MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
        (2 : Fin 22)).ncard = 20 := by
  rw [stabilizer_zero_one_orbit_two_eq_remaining]
  have hset : ({x : Fin 22 | x ≠ 0 ∧ x ≠ 1} : Set (Fin 22)) =
      ({0, 1} : Set (Fin 22))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  norm_num

/-! ## Level 4: the stabilizer of `0,1,2` moving `5` outside the block `B0` -/

def levelFourElement (x : Fin 22) (hx : x ∈ blockB0ᶜ) :
    MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
      (2 : Fin 22) :=
  let g0 : MulAction.stabilizer M22 (0 : Fin 22) :=
    ⟨Word.toM22 (levelFourWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFourWord x)) (0 : Fin 22) = 0
      exact levelFourWord_fixes_zero_all x hx⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFourWord x)) (1 : Fin 22) = 1
      exact levelFourWord_fixes_one_all x hx⟩
  ⟨g1, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelFourWord x)) (2 : Fin 22) = 2
    exact levelFourWord_fixes_two_all x hx⟩

theorem fourth_orbit_stabilizer_witness (x : Fin 22) (hx : x ∈ blockB0ᶜ) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
        (2 : Fin 22),
      g.1.1.1.1 (5 : Fin 22) = x :=
  ⟨levelFourElement x hx, by
    change (Word.eval (levelFourWord x)) (5 : Fin 22) = x
    exact levelFourWord_maps_five_all x hx⟩

/-- An element fixing `0,1,2` preserves the block `B0` setwise. -/
theorem blockMap_B0_of_fixes (π : Perm22)
    (hpres : ∀ B ∈ wittBlockList, blockMap π B ∈ wittBlocks)
    (h0 : π 0 = 0) (h1 : π 1 = 1) (h2 : π 2 = 2) :
    blockMap π blockB0 = blockB0 :=
  blockMap_eq_of_three π hpres wittBlockAt_zero (by decide) (by decide) (by decide)
    h0 h1 h2 unique_block_012 wittBlockAt_zero

theorem stab012_orbit_five_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
          (2 : Fin 22))
        (5 : Fin 22) = ↑(blockB0ᶜ) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have hfix0 : g.1.1.1.1 (0 : Fin 22) = 0 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix1 : g.1.1.1.1 (1 : Fin 22) = 1 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix2 : g.1.1.1.1 (2 : Fin 22) = 2 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hmap : g.1.1.1.1 (5 : Fin 22) = x := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    have hB0 : blockMap g.1.1.1.1 blockB0 = blockB0 :=
      blockMap_B0_of_fixes g.1.1.1.1 (M22_preserves_wittBlocks g.1.1.1).1
        hfix0 hfix1 hfix2
    rw [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe]
    intro hxB0
    rw [← hB0] at hxB0
    obtain ⟨w, hwB0, hw⟩ := Finset.mem_image.mp hxB0
    have hw5 : w = 5 := g.1.1.1.1.injective (by rw [hw, hmap])
    rw [hw5] at hwB0
    exact (by decide : (5 : Fin 22) ∉ blockB0) hwB0
  · intro hx
    have hxc : x ∈ blockB0ᶜ := Finset.mem_coe.mp hx
    obtain ⟨g, hg⟩ := fourth_orbit_stabilizer_witness x hxc
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab012_orbit_five_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
          (2 : Fin 22))
        (5 : Fin 22)).ncard = 16 := by
  rw [stab012_orbit_five_eq, Set.ncard_coe_finset]
  decide

/-! ## Level 5: the stabilizer of `0,1,2,5` moving `3` inside the block `B0` -/

set_option maxHeartbeats 1600000 in
-- The membership pin certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- Inside `B0`, the points other than the fixed `0,1,2` are `3`, `4`, `21`. -/
theorem pin_three :
    ∀ v : Fin 22, v ∈ blockB0 → v ≠ 0 → v ≠ 1 → v ≠ 2 →
      v ∈ ({3, 4, 21} : Finset (Fin 22)) := by
  decide

theorem mem_targets_iff :
    ∀ x : Fin 22, x ∈ ({3, 4, 21} : Finset (Fin 22)) →
      (x = 3 ∨ x = 4 ∨ x = 21) := by
  decide

def levelFiveElement (x : Fin 22) (hx : x = 3 ∨ x = 4 ∨ x = 21) :
    MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
        (2 : Fin 22))
      (5 : Fin 22) :=
  let g0 : MulAction.stabilizer M22 (0 : Fin 22) :=
    ⟨Word.toM22 (levelFiveWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (0 : Fin 22) = 0
      exact levelFiveWord_fixes_zero_all x hx⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (1 : Fin 22) = 1
      exact levelFiveWord_fixes_one_all x hx⟩
  let g2 : MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
      (2 : Fin 22) :=
    ⟨g1, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (levelFiveWord x)) (2 : Fin 22) = 2
      exact levelFiveWord_fixes_two_all x hx⟩
  ⟨g2, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (levelFiveWord x)) (5 : Fin 22) = 5
    exact levelFiveWord_fixes_five_all x hx⟩

theorem fifth_orbit_stabilizer_witness (x : Fin 22) (hx : x = 3 ∨ x = 4 ∨ x = 21) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
          (2 : Fin 22))
        (5 : Fin 22),
      g.1.1.1.1.1 (3 : Fin 22) = x :=
  ⟨levelFiveElement x hx, by
    change (Word.eval (levelFiveWord x)) (3 : Fin 22) = x
    exact levelFiveWord_maps_three_all x hx⟩

theorem stab0125_orbit_three_eq :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
            (2 : Fin 22))
          (5 : Fin 22))
        (3 : Fin 22) = ↑({3, 4, 21} : Finset (Fin 22)) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have hfix0 : g.1.1.1.1.1 (0 : Fin 22) = 0 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix1 : g.1.1.1.1.1 (1 : Fin 22) = 1 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hfix2 : g.1.1.1.1.1 (2 : Fin 22) = 2 := by
      have h := (MulAction.mem_stabilizer_iff.mp g.1.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h
    have hmap : g.1.1.1.1.1 (3 : Fin 22) = x := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    have hB0 : blockMap g.1.1.1.1.1 blockB0 = blockB0 :=
      blockMap_B0_of_fixes g.1.1.1.1.1 (M22_preserves_wittBlocks g.1.1.1.1).1
        hfix0 hfix1 hfix2
    have hmem : x ∈ blockB0 := by
      rw [← hmap]
      exact mem_of_blockMap_eq g.1.1.1.1.1 hB0 (by decide)
    rw [Finset.mem_coe]
    refine pin_three x hmem ?_ ?_ ?_
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1 hfix0 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1 hfix1 (by decide)
    · rw [← hmap]
      exact ne_of_value g.1.1.1.1.1 hfix2 (by decide)
  · intro hx
    have hxor := mem_targets_iff x (Finset.mem_coe.mp hx)
    obtain ⟨g, hg⟩ := fifth_orbit_stabilizer_witness x hxor
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab0125_orbit_three_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M22 (0 : Fin 22)) (1 : Fin 22))
            (2 : Fin 22))
          (5 : Fin 22))
        (3 : Fin 22)).ncard = 3 := by
  rw [stab0125_orbit_three_eq, Set.ncard_coe_finset]
  decide

end ChainOrbits
end M22Certificates
end Sporadic
