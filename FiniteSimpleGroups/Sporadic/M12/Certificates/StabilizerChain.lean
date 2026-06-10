/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.Certificates.Words

/-!
# Stabilizer-chain certificates

This file contains verified data for the preferred cardinality route:

* orbit of `0` has size `12`;
* the stabilizer of `0` has orbit size `11` on the remaining points;
* the stabilizer of `0,1` has orbit size `10`;
* the stabilizer of `0,1,2` has orbit size `9`;
* the stabilizer of `0,1,2,3` has orbit size `8`;
* the stabilizer of `0,1,2,3,4` is trivial.

No external computation is trusted here until it is represented as data and
checked by Lean.
-/

namespace Sporadic
namespace M12Certificates
namespace StabilizerChain

/-- The product of the target stabilizer-chain indices. -/
theorem target_index_product : 12 * 11 * 10 * 9 * 8 = 95040 := by
  norm_num

/--
Certificate words for the first stabilizer-chain step.

`orbitZeroWord x` sends `0` to `x`. The identity word is used for `x = 0`.
-/
def orbitZeroWord (x : Fin 12) : Word :=
  match x.val with
  | 1 => [Gen.a]
  | 2 => [Gen.a, Gen.a]
  | 3 => [Gen.a, Gen.a, Gen.a]
  | 4 => [Gen.aInv, Gen.aInv, Gen.b]
  | 5 => [Gen.a, Gen.a, Gen.c]
  | 6 => [Gen.aInv, Gen.bInv]
  | 7 => [Gen.aInv, Gen.b]
  | 8 => [Gen.aInv, Gen.aInv, Gen.aInv]
  | 9 => [Gen.aInv, Gen.aInv]
  | 10 => [Gen.aInv]
  | 11 => [Gen.c]
  | _ => []

set_option maxRecDepth 20000 in
/-- The first-step certificate words send `0` to every point of `Fin 12`. -/
theorem orbitZeroWord_maps_zero_all :
    ∀ x : Fin 12, (Word.eval (orbitZeroWord x)) (0 : Fin 12) = x := by
  decide

theorem orbitZeroWord_maps_zero (x : Fin 12) :
    (Word.eval (orbitZeroWord x)) (0 : Fin 12) = x :=
  orbitZeroWord_maps_zero_all x

/-- Every point of `Fin 12` is reached from `0` by an explicit word. -/
theorem first_orbit_word_witness (x : Fin 12) :
    ∃ w : Word, (Word.eval w) (0 : Fin 12) = x :=
  ⟨orbitZeroWord x, orbitZeroWord_maps_zero x⟩

/-- Every point of `Fin 12` is reached from `0` by an element of `M12`. -/
theorem first_orbit_M12_witness (x : Fin 12) :
    ∃ g : M12, g.1 (0 : Fin 12) = x :=
  ⟨Word.toM12 (orbitZeroWord x), by simpa using orbitZeroWord_maps_zero x⟩

/-- The orbit of `0` under the generated group is all of `Fin 12`. -/
theorem orbit_zero_eq_univ : MulAction.orbit M12 (0 : Fin 12) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := first_orbit_M12_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The first orbit in the stabilizer-chain plan has size 12. -/
theorem orbit_zero_ncard : (MulAction.orbit M12 (0 : Fin 12)).ncard = 12 := by
  rw [orbit_zero_eq_univ, Set.ncard_univ]
  simp

/--
Certificate words for the second stabilizer-chain step.

For a nonzero target `x`, `zeroStabilizerWord x` fixes `0` and sends `1` to `x`.
The identity word is used at `x = 0` (irrelevant) and `x = 1`.
-/
def zeroStabilizerWord (x : Fin 12) : Word :=
  match x.val with
  | 2 => [Gen.a, Gen.bInv, Gen.aInv, Gen.bInv]
  | 3 => [Gen.c, Gen.b, Gen.c]
  | 4 => [Gen.a, Gen.b, Gen.aInv, Gen.bInv]
  | 5 => [Gen.a, Gen.b, Gen.aInv]
  | 6 => [Gen.a, Gen.bInv, Gen.aInv]
  | 7 => [Gen.c, Gen.aInv, Gen.bInv, Gen.c]
  | 8 => [Gen.c, Gen.aInv, Gen.b, Gen.c]
  | 9 => [Gen.c, Gen.bInv, Gen.c]
  | 10 => [Gen.a, Gen.b, Gen.c, Gen.a]
  | 11 => [Gen.aInv, Gen.c, Gen.aInv]
  | _ => []

set_option maxRecDepth 20000 in
/-- The second-step certificate words fix the first base point `0`. -/
theorem zeroStabilizerWord_fixes_zero_all :
    ∀ x : Fin 12, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (0 : Fin 12) = 0 := by
  decide

theorem zeroStabilizerWord_fixes_zero (x : Fin 12) (hx : x ≠ 0) :
    (Word.eval (zeroStabilizerWord x)) (0 : Fin 12) = 0 :=
  zeroStabilizerWord_fixes_zero_all x hx

set_option maxRecDepth 20000 in
/-- The second-step certificate words send `1` to the requested nonzero point. -/
theorem zeroStabilizerWord_maps_one_all :
    ∀ x : Fin 12, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (1 : Fin 12) = x := by
  decide

theorem zeroStabilizerWord_maps_one (x : Fin 12) (hx : x ≠ 0) :
    (Word.eval (zeroStabilizerWord x)) (1 : Fin 12) = x :=
  zeroStabilizerWord_maps_one_all x hx

/-- Interpret the second-step word as an element of the stabilizer of `0`. -/
def zeroStabilizerElement (x : Fin 12) (hx : x ≠ 0) :
    MulAction.stabilizer M12 (0 : Fin 12) :=
  ⟨Word.toM12 (zeroStabilizerWord x), by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroStabilizerWord x)) (0 : Fin 12) = 0
    exact zeroStabilizerWord_fixes_zero x hx⟩

/-- The second-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroStabilizerElement_apply (x y : Fin 12) (hx : x ≠ 0) :
    (zeroStabilizerElement x hx).1.1 y = (Word.eval (zeroStabilizerWord x)) y :=
  rfl

/--
Every nonzero point is reached from `1` by an element of the stabilizer of `0`.
-/
theorem second_orbit_stabilizer_witness (x : Fin 12) (hx : x ≠ 0) :
    ∃ g : MulAction.stabilizer M12 (0 : Fin 12), g.1.1 (1 : Fin 12) = x :=
  ⟨zeroStabilizerElement x hx, by
    rw [zeroStabilizerElement_apply]
    exact zeroStabilizerWord_maps_one x hx⟩

/-- The stabilizer of `0` moves `1` through exactly the nonzero points. -/
theorem stabilizer_zero_orbit_one_eq_nonzero :
    MulAction.orbit (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12) =
      {x : Fin 12 | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩ hx0
    have hfix : g.1.1 (0 : Fin 12) = 0 := by
      have hg0 := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
    have hmap : g.1.1 (1 : Fin 12) = 0 := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
    have h10 : (1 : Fin 12) = 0 := g.1.1.injective (by rw [hmap, hfix])
    exact (by decide : (1 : Fin 12) ≠ 0) h10
  · intro hx
    obtain ⟨g, hg⟩ := second_orbit_stabilizer_witness x hx
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The second orbit in the stabilizer-chain plan has size 11. -/
theorem stabilizer_zero_orbit_one_ncard :
    (MulAction.orbit (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12)).ncard = 11 := by
  rw [stabilizer_zero_orbit_one_eq_nonzero]
  have hset : ({x : Fin 12 | x ≠ 0} : Set (Fin 12)) = ({0} : Set (Fin 12))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/--
Certificate words for the third stabilizer-chain step.

For a target `x` different from `0` and `1`, `zeroOneStabilizerWord x` fixes
both `0` and `1`, and sends `2` to `x`.
-/
def zeroOneStabilizerWord (x : Fin 12) : Word :=
  match x.val with
  | 3 => [Gen.a, Gen.c, Gen.a, Gen.a, Gen.b, Gen.aInv]
  | 4 => [Gen.aInv, Gen.c, Gen.b, Gen.c, Gen.a]
  | 5 => [Gen.aInv, Gen.c, Gen.b, Gen.c, Gen.a, Gen.b]
  | 6 => [Gen.b]
  | 7 => [Gen.bInv]
  | 8 => [Gen.c, Gen.bInv, Gen.a, Gen.bInv, Gen.c]
  | 9 => [Gen.c, Gen.b, Gen.aInv, Gen.b, Gen.c]
  | 10 => [Gen.b, Gen.b]
  | 11 => [Gen.b, Gen.b, Gen.c, Gen.b, Gen.aInv, Gen.b, Gen.c]
  | _ => []

set_option maxRecDepth 40000 in
/-- The third-step certificate words fix `0`. -/
theorem zeroOneStabilizerWord_fixes_zero_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 12) = 0 := by
  decide

theorem zeroOneStabilizerWord_fixes_zero (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 12) = 0 :=
  zeroOneStabilizerWord_fixes_zero_all x hx0 hx1

set_option maxRecDepth 40000 in
/-- The third-step certificate words fix `1`. -/
theorem zeroOneStabilizerWord_fixes_one_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 12) = 1 := by
  decide

theorem zeroOneStabilizerWord_fixes_one (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 12) = 1 :=
  zeroOneStabilizerWord_fixes_one_all x hx0 hx1

set_option maxRecDepth 40000 in
/-- The third-step certificate words send `2` to the requested remaining point. -/
theorem zeroOneStabilizerWord_maps_two_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 12) = x := by
  decide

theorem zeroOneStabilizerWord_maps_two (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 12) = x :=
  zeroOneStabilizerWord_maps_two_all x hx0 hx1

/-- Interpret the third-step word as an element of the stabilizer of `0` and `1`. -/
def zeroOneStabilizerElement (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12) :=
  let g0 : MulAction.stabilizer M12 (0 : Fin 12) :=
    ⟨Word.toM12 (zeroOneStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 12) = 0
      exact zeroOneStabilizerWord_fixes_zero x hx0 hx1⟩
  ⟨g0, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 12) = 1
    exact zeroOneStabilizerWord_fixes_one x hx0 hx1⟩

/-- The third-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroOneStabilizerElement_apply
    (x y : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (zeroOneStabilizerElement x hx0 hx1).1.1.1 y =
      (Word.eval (zeroOneStabilizerWord x)) y :=
  rfl

/--
Every point different from `0` and `1` is reached from `2` by an element of the
stabilizer of `0` and `1`.
-/
theorem third_orbit_stabilizer_witness (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ g : MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12),
      g.1.1.1 (2 : Fin 12) = x :=
  ⟨zeroOneStabilizerElement x hx0 hx1, by
    rw [zeroOneStabilizerElement_apply]
    exact zeroOneStabilizerWord_maps_two x hx0 hx1⟩

/-- The stabilizer of `0` and `1` moves `2` through exactly the remaining points. -/
theorem stabilizer_zero_one_orbit_two_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
        (2 : Fin 12) =
      {x : Fin 12 | x ≠ 0 ∧ x ≠ 1} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1 (0 : Fin 12) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1 (2 : Fin 12) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h20 : (2 : Fin 12) = 0 := g.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (2 : Fin 12) ≠ 0) h20
    · intro hx1
      have hfix1 : g.1.1.1 (1 : Fin 12) = 1 := by
        have hg1 := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
      have hmap : g.1.1.1 (2 : Fin 12) = 1 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
      have h21 : (2 : Fin 12) = 1 := g.1.1.1.injective (by rw [hmap, hfix1])
      exact (by decide : (2 : Fin 12) ≠ 1) h21
  · rintro ⟨hx0, hx1⟩
    obtain ⟨g, hg⟩ := third_orbit_stabilizer_witness x hx0 hx1
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The third orbit in the stabilizer-chain plan has size 10. -/
theorem stabilizer_zero_one_orbit_two_ncard :
    (MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
        (2 : Fin 12)).ncard = 10 := by
  rw [stabilizer_zero_one_orbit_two_eq_remaining]
  have hset : ({x : Fin 12 | x ≠ 0 ∧ x ≠ 1} : Set (Fin 12)) =
      ({0, 1} : Set (Fin 12))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  norm_num

/--
Certificate words for the fourth stabilizer-chain step.

For a target `x` different from `0`, `1`, and `2`,
`zeroOneTwoStabilizerWord x` fixes `0`, `1`, and `2`, and sends `3` to `x`.
-/
def zeroOneTwoStabilizerWord (x : Fin 12) : Word :=
  match x.val with
  | 4 => [Gen.c, Gen.a, Gen.bInv, Gen.aInv, Gen.c, Gen.b, Gen.b]
  | 5 => [Gen.c, Gen.a, Gen.b, Gen.aInv, Gen.c, Gen.bInv]
  | 6 => [Gen.b, Gen.c, Gen.a, Gen.bInv, Gen.aInv, Gen.c]
  | 7 => [Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.c, Gen.aInv, Gen.bInv]
  | 8 => [Gen.b, Gen.a, Gen.c, Gen.a, Gen.a, Gen.b, Gen.aInv]
  | 9 => [Gen.c, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.c]
  | 10 => [Gen.aInv, Gen.c, Gen.b, Gen.b, Gen.c, Gen.a, Gen.bInv]
  | 11 => [Gen.bInv, Gen.aInv, Gen.b, Gen.c, Gen.aInv, Gen.aInv, Gen.c, Gen.a]
  | _ => []

set_option maxRecDepth 80000 in
/-- The fourth-step certificate words fix `0`. -/
theorem zeroOneTwoStabilizerWord_fixes_zero_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 12) = 0 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_zero
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 12) = 0 :=
  zeroOneTwoStabilizerWord_fixes_zero_all x hx0 hx1 hx2

set_option maxRecDepth 80000 in
/-- The fourth-step certificate words fix `1`. -/
theorem zeroOneTwoStabilizerWord_fixes_one_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 12) = 1 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_one
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 12) = 1 :=
  zeroOneTwoStabilizerWord_fixes_one_all x hx0 hx1 hx2

set_option maxRecDepth 80000 in
/-- The fourth-step certificate words fix `2`. -/
theorem zeroOneTwoStabilizerWord_fixes_two_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 12) = 2 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_two
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 12) = 2 :=
  zeroOneTwoStabilizerWord_fixes_two_all x hx0 hx1 hx2

set_option maxRecDepth 80000 in
/-- The fourth-step certificate words send `3` to the requested remaining point. -/
theorem zeroOneTwoStabilizerWord_maps_three_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (3 : Fin 12) = x := by
  decide

theorem zeroOneTwoStabilizerWord_maps_three
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (3 : Fin 12) = x :=
  zeroOneTwoStabilizerWord_maps_three_all x hx0 hx1 hx2

/-- Interpret the fourth-step word as an element of the stabilizer of `0`, `1`, and `2`. -/
def zeroOneTwoStabilizerElement
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
      (2 : Fin 12) :=
  let g0 : MulAction.stabilizer M12 (0 : Fin 12) :=
    ⟨Word.toM12 (zeroOneTwoStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 12) = 0
      exact zeroOneTwoStabilizerWord_fixes_zero x hx0 hx1 hx2⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 12) = 1
      exact zeroOneTwoStabilizerWord_fixes_one x hx0 hx1 hx2⟩
  ⟨g1, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 12) = 2
    exact zeroOneTwoStabilizerWord_fixes_two x hx0 hx1 hx2⟩

/-- The fourth-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroOneTwoStabilizerElement_apply
    (x y : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (zeroOneTwoStabilizerElement x hx0 hx1 hx2).1.1.1.1 y =
      (Word.eval (zeroOneTwoStabilizerWord x)) y :=
  rfl

/--
Every point different from `0`, `1`, and `2` is reached from `3` by an element
of the stabilizer of `0`, `1`, and `2`.
-/
theorem fourth_orbit_stabilizer_witness
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
        (2 : Fin 12),
      g.1.1.1.1 (3 : Fin 12) = x :=
  ⟨zeroOneTwoStabilizerElement x hx0 hx1 hx2, by
    rw [zeroOneTwoStabilizerElement_apply]
    exact zeroOneTwoStabilizerWord_maps_three x hx0 hx1 hx2⟩

/--
The stabilizer of `0`, `1`, and `2` moves `3` through exactly the remaining
nine points.
-/
theorem stabilizer_zero_one_two_orbit_three_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
          (2 : Fin 12))
        (3 : Fin 12) =
      {x : Fin 12 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1.1 (0 : Fin 12) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1.1 (3 : Fin 12) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h30 : (3 : Fin 12) = 0 := g.1.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (3 : Fin 12) ≠ 0) h30
    · constructor
      · intro hx1
        have hfix1 : g.1.1.1.1 (1 : Fin 12) = 1 := by
          have hg1 := (MulAction.mem_stabilizer_iff.mp g.1.2)
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
        have hmap : g.1.1.1.1 (3 : Fin 12) = 1 := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
        have h31 : (3 : Fin 12) = 1 := g.1.1.1.1.injective (by rw [hmap, hfix1])
        exact (by decide : (3 : Fin 12) ≠ 1) h31
      · intro hx2
        have hfix2 : g.1.1.1.1 (2 : Fin 12) = 2 := by
          have hg2 := (MulAction.mem_stabilizer_iff.mp g.2)
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg2
        have hmap : g.1.1.1.1 (3 : Fin 12) = 2 := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx2] using hg
        have h32 : (3 : Fin 12) = 2 := g.1.1.1.1.injective (by rw [hmap, hfix2])
        exact (by decide : (3 : Fin 12) ≠ 2) h32
  · rintro ⟨hx0, hx1, hx2⟩
    obtain ⟨g, hg⟩ := fourth_orbit_stabilizer_witness x hx0 hx1 hx2
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The fourth orbit in the stabilizer-chain plan has size 9. -/
theorem stabilizer_zero_one_two_orbit_three_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
          (2 : Fin 12))
        (3 : Fin 12)).ncard = 9 := by
  rw [stabilizer_zero_one_two_orbit_three_eq_remaining]
  have hset : ({x : Fin 12 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} : Set (Fin 12)) =
      ({0, 1, 2} : Set (Fin 12))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  have hcard : ({0, 1, 2} : Set (Fin 12)).ncard = 3 := by
    rw [show ({0, 1, 2} : Set (Fin 12)) = insert (0 : Fin 12) ({1, 2} : Set (Fin 12)) by
      ext x
      simp]
    rw [Set.ncard_insert_of_notMem]
    · rw [show ({1, 2} : Set (Fin 12)) = insert (1 : Fin 12) ({2} : Set (Fin 12)) by
        ext x
        simp]
      rw [Set.ncard_insert_of_notMem]
      · simp
      · simp
    · simp
  rw [hcard]
  norm_num

/--
Certificate words for the fifth stabilizer-chain step.

For a target `x` different from `0`, `1`, `2`, and `3`,
`zeroOneTwoThreeStabilizerWord x` fixes `0`, `1`, `2`, and `3`, and sends `4`
to `x`.
-/
def zeroOneTwoThreeStabilizerWord (x : Fin 12) : Word :=
  match x.val with
  | 5 => [Gen.aInv, Gen.c, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.b, Gen.c, Gen.a]
  | 6 => [Gen.a, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.bInv, Gen.c, Gen.aInv,
      Gen.aInv]
  | 7 => [Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.c, Gen.b, Gen.b,
      Gen.aInv]
  | 8 => [Gen.a, Gen.b, Gen.b, Gen.c, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv]
  | 9 => [Gen.b, Gen.a, Gen.c, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b,
      Gen.aInv]
  | 10 => [Gen.aInv, Gen.c, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.c, Gen.a]
  | 11 => [Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.a, Gen.c, Gen.aInv, Gen.bInv]
  | _ => []

set_option maxRecDepth 160000 in
/-- The fifth-step certificate words fix `0`. -/
theorem zeroOneTwoThreeStabilizerWord_fixes_zero_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 →
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) (0 : Fin 12) = 0 := by
  decide

theorem zeroOneTwoThreeStabilizerWord_fixes_zero
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (Word.eval (zeroOneTwoThreeStabilizerWord x)) (0 : Fin 12) = 0 :=
  zeroOneTwoThreeStabilizerWord_fixes_zero_all x hx0 hx1 hx2 hx3

set_option maxRecDepth 160000 in
/-- The fifth-step certificate words fix `1`. -/
theorem zeroOneTwoThreeStabilizerWord_fixes_one_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 →
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) (1 : Fin 12) = 1 := by
  decide

theorem zeroOneTwoThreeStabilizerWord_fixes_one
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (Word.eval (zeroOneTwoThreeStabilizerWord x)) (1 : Fin 12) = 1 :=
  zeroOneTwoThreeStabilizerWord_fixes_one_all x hx0 hx1 hx2 hx3

set_option maxRecDepth 160000 in
/-- The fifth-step certificate words fix `2`. -/
theorem zeroOneTwoThreeStabilizerWord_fixes_two_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 →
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) (2 : Fin 12) = 2 := by
  decide

theorem zeroOneTwoThreeStabilizerWord_fixes_two
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (Word.eval (zeroOneTwoThreeStabilizerWord x)) (2 : Fin 12) = 2 :=
  zeroOneTwoThreeStabilizerWord_fixes_two_all x hx0 hx1 hx2 hx3

set_option maxRecDepth 160000 in
/-- The fifth-step certificate words fix `3`. -/
theorem zeroOneTwoThreeStabilizerWord_fixes_three_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 →
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) (3 : Fin 12) = 3 := by
  decide

theorem zeroOneTwoThreeStabilizerWord_fixes_three
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (Word.eval (zeroOneTwoThreeStabilizerWord x)) (3 : Fin 12) = 3 :=
  zeroOneTwoThreeStabilizerWord_fixes_three_all x hx0 hx1 hx2 hx3

set_option maxRecDepth 160000 in
/-- The fifth-step certificate words send `4` to the requested remaining point. -/
theorem zeroOneTwoThreeStabilizerWord_maps_four_all :
    ∀ x : Fin 12, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 →
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) (4 : Fin 12) = x := by
  decide

theorem zeroOneTwoThreeStabilizerWord_maps_four
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (Word.eval (zeroOneTwoThreeStabilizerWord x)) (4 : Fin 12) = x :=
  zeroOneTwoThreeStabilizerWord_maps_four_all x hx0 hx1 hx2 hx3

/-- Interpret the fifth-step word as an element of the stabilizer of `0`, `1`, `2`, `3`. -/
def zeroOneTwoThreeStabilizerElement
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    MulAction.stabilizer
      (MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
        (2 : Fin 12))
      (3 : Fin 12) :=
  let g0 : MulAction.stabilizer M12 (0 : Fin 12) :=
    ⟨Word.toM12 (zeroOneTwoThreeStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoThreeStabilizerWord x)) (0 : Fin 12) = 0
      exact zeroOneTwoThreeStabilizerWord_fixes_zero x hx0 hx1 hx2 hx3⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoThreeStabilizerWord x)) (1 : Fin 12) = 1
      exact zeroOneTwoThreeStabilizerWord_fixes_one x hx0 hx1 hx2 hx3⟩
  let g2 : MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
      (2 : Fin 12) :=
    ⟨g1, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoThreeStabilizerWord x)) (2 : Fin 12) = 2
      exact zeroOneTwoThreeStabilizerWord_fixes_two x hx0 hx1 hx2 hx3⟩
  ⟨g2, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneTwoThreeStabilizerWord x)) (3 : Fin 12) = 3
    exact zeroOneTwoThreeStabilizerWord_fixes_three x hx0 hx1 hx2 hx3⟩

/-- The fifth-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroOneTwoThreeStabilizerElement_apply
    (x y : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    (zeroOneTwoThreeStabilizerElement x hx0 hx1 hx2 hx3).1.1.1.1.1 y =
      (Word.eval (zeroOneTwoThreeStabilizerWord x)) y :=
  rfl

/--
Every point different from `0`, `1`, `2`, and `3` is reached from `4` by an
element of the stabilizer of `0`, `1`, `2`, and `3`.
-/
theorem fifth_orbit_stabilizer_witness
    (x : Fin 12) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
          (2 : Fin 12))
        (3 : Fin 12),
      g.1.1.1.1.1 (4 : Fin 12) = x :=
  ⟨zeroOneTwoThreeStabilizerElement x hx0 hx1 hx2 hx3, by
    rw [zeroOneTwoThreeStabilizerElement_apply]
    exact zeroOneTwoThreeStabilizerWord_maps_four x hx0 hx1 hx2 hx3⟩

/--
The stabilizer of `0`, `1`, `2`, and `3` moves `4` through exactly the
remaining eight points.
-/
theorem stabilizer_zero_one_two_three_orbit_four_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
            (2 : Fin 12))
          (3 : Fin 12))
        (4 : Fin 12) =
      {x : Fin 12 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1.1.1 (0 : Fin 12) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1.1.1 (4 : Fin 12) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h40 : (4 : Fin 12) = 0 := g.1.1.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (4 : Fin 12) ≠ 0) h40
    · constructor
      · intro hx1
        have hfix1 : g.1.1.1.1.1 (1 : Fin 12) = 1 := by
          have hg1 := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
        have hmap : g.1.1.1.1.1 (4 : Fin 12) = 1 := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
        have h41 : (4 : Fin 12) = 1 := g.1.1.1.1.1.injective (by rw [hmap, hfix1])
        exact (by decide : (4 : Fin 12) ≠ 1) h41
      · constructor
        · intro hx2
          have hfix2 : g.1.1.1.1.1 (2 : Fin 12) = 2 := by
            have hg2 := (MulAction.mem_stabilizer_iff.mp g.1.2)
            simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg2
          have hmap : g.1.1.1.1.1 (4 : Fin 12) = 2 := by
            simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx2] using hg
          have h42 : (4 : Fin 12) = 2 := g.1.1.1.1.1.injective (by rw [hmap, hfix2])
          exact (by decide : (4 : Fin 12) ≠ 2) h42
        · intro hx3
          have hfix3 : g.1.1.1.1.1 (3 : Fin 12) = 3 := by
            have hg3 := (MulAction.mem_stabilizer_iff.mp g.2)
            simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg3
          have hmap : g.1.1.1.1.1 (4 : Fin 12) = 3 := by
            simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx3] using hg
          have h43 : (4 : Fin 12) = 3 := g.1.1.1.1.1.injective (by rw [hmap, hfix3])
          exact (by decide : (4 : Fin 12) ≠ 3) h43
  · rintro ⟨hx0, hx1, hx2, hx3⟩
    obtain ⟨g, hg⟩ := fifth_orbit_stabilizer_witness x hx0 hx1 hx2 hx3
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The fifth orbit in the stabilizer-chain plan has size 8. -/
theorem stabilizer_zero_one_two_three_orbit_four_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer
            (MulAction.stabilizer (MulAction.stabilizer M12 (0 : Fin 12)) (1 : Fin 12))
            (2 : Fin 12))
          (3 : Fin 12))
        (4 : Fin 12)).ncard = 8 := by
  rw [stabilizer_zero_one_two_three_orbit_four_eq_remaining]
  have hset : ({x : Fin 12 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3} : Set (Fin 12)) =
      ({0, 1, 2, 3} : Set (Fin 12))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  have hcard : ({0, 1, 2, 3} : Set (Fin 12)).ncard = 4 := by
    rw [show ({0, 1, 2, 3} : Set (Fin 12)) =
        insert (0 : Fin 12) ({1, 2, 3} : Set (Fin 12)) by
      ext x
      simp]
    rw [Set.ncard_insert_of_notMem]
    · rw [show ({1, 2, 3} : Set (Fin 12)) =
          insert (1 : Fin 12) ({2, 3} : Set (Fin 12)) by
        ext x
        simp]
      rw [Set.ncard_insert_of_notMem]
      · rw [show ({2, 3} : Set (Fin 12)) = insert (2 : Fin 12) ({3} : Set (Fin 12)) by
          ext x
          simp]
        rw [Set.ncard_insert_of_notMem]
        · simp
        · simp
      · simp
    · simp
  rw [hcard]
  norm_num

/-- The product of the five verified stabilizer-chain orbit sizes. -/
theorem five_index_product : 12 * 11 * 10 * 9 * 8 = 95040 := by
  norm_num

end StabilizerChain
end M12Certificates
end Sporadic
