/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Certificates.Words

/-!
# Stabilizer-chain certificates

This file will contain verified data for the preferred cardinality route:

* orbit of `0` has size `11`;
* the stabilizer of `0` has orbit size `10` on the remaining points;
* the stabilizer of `0,1` has orbit size `9`;
* the stabilizer of `0,1,2` has orbit size `8`;
* the stabilizer of `0,1,2,3` is trivial.

No external computation is trusted here until it is represented as data and
checked by Lean.
-/

namespace Sporadic
namespace Certificates
namespace StabilizerChain

/-- The product of the target stabilizer-chain indices. -/
theorem target_index_product : 11 * 10 * 9 * 8 = 7920 := by
  norm_num

/-- The word `a^n`, represented by `n` copies of the generator `a`. -/
def aPowerWord (n : Nat) : Word :=
  List.replicate n Gen.a

/--
The 11-cycle generator moves `0` to every point of `Fin 11`.
This is the first tiny verified orbit certificate.
-/
theorem aPowerWord_maps_zero_all :
    ∀ x : Fin 11, (Word.eval (aPowerWord x.val)) (0 : Fin 11) = x := by
  decide

theorem aPowerWord_maps_zero (x : Fin 11) :
    (Word.eval (aPowerWord x.val)) (0 : Fin 11) = x :=
  aPowerWord_maps_zero_all x

/-- Every point of `Fin 11` is reached from `0` by an explicit word in `a`. -/
theorem first_orbit_word_witness (x : Fin 11) :
    ∃ w : Word, (Word.eval w) (0 : Fin 11) = x :=
  ⟨aPowerWord x.val, aPowerWord_maps_zero x⟩

/-- Every point of `Fin 11` is reached from `0` by an element of `M11`. -/
theorem first_orbit_M11_witness (x : Fin 11) :
    ∃ g : M11, g.1 (0 : Fin 11) = x :=
  ⟨Word.toM11 (aPowerWord x.val), by simpa using aPowerWord_maps_zero x⟩

/-- The orbit of `0` under the generated group is all of `Fin 11`. -/
theorem orbit_zero_eq_univ : MulAction.orbit M11 (0 : Fin 11) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := first_orbit_M11_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The first orbit in the stabilizer-chain plan has size 11. -/
theorem orbit_zero_ncard : (MulAction.orbit M11 (0 : Fin 11)).ncard = 11 := by
  rw [orbit_zero_eq_univ, Set.ncard_univ]
  simp

/--
Certificate words for the second stabilizer-chain step.

For a nonzero target `x`, `zeroStabilizerWord x` fixes `0` and sends `1` to `x`.
The value at `0` is irrelevant; we use the identity word there to keep the
definition total.
-/
def zeroStabilizerWord (x : Fin 11) : Word :=
  match x.val with
  | 2 => [Gen.a, Gen.bInv, Gen.aInv, Gen.bInv]
  | 3 => [Gen.a, Gen.b, Gen.aInv, Gen.b]
  | 4 => [Gen.a, Gen.b, Gen.aInv, Gen.bInv]
  | 5 => [Gen.a, Gen.b, Gen.aInv]
  | 6 => [Gen.a, Gen.bInv, Gen.aInv]
  | 7 => [Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.b]
  | 8 => [Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a]
  | 9 => [Gen.a, Gen.b, Gen.b, Gen.aInv]
  | 10 => [Gen.a, Gen.bInv, Gen.aInv, Gen.b]
  | _ => []

set_option maxRecDepth 10000 in
/-- The second-step certificate words fix the first base point `0`. -/
theorem zeroStabilizerWord_fixes_zero_all :
    ∀ x : Fin 11, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (0 : Fin 11) = 0 := by
  decide

theorem zeroStabilizerWord_fixes_zero (x : Fin 11) (hx : x ≠ 0) :
    (Word.eval (zeroStabilizerWord x)) (0 : Fin 11) = 0 :=
  zeroStabilizerWord_fixes_zero_all x hx

set_option maxRecDepth 10000 in
/-- The second-step certificate words send `1` to the requested nonzero point. -/
theorem zeroStabilizerWord_maps_one_all :
    ∀ x : Fin 11, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (1 : Fin 11) = x := by
  decide

theorem zeroStabilizerWord_maps_one (x : Fin 11) (hx : x ≠ 0) :
    (Word.eval (zeroStabilizerWord x)) (1 : Fin 11) = x :=
  zeroStabilizerWord_maps_one_all x hx

/-- Interpret the second-step word as an element of the stabilizer of `0`. -/
def zeroStabilizerElement (x : Fin 11) (hx : x ≠ 0) :
    MulAction.stabilizer M11 (0 : Fin 11) :=
  ⟨Word.toM11 (zeroStabilizerWord x), by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroStabilizerWord x)) (0 : Fin 11) = 0
    exact zeroStabilizerWord_fixes_zero x hx⟩

/-- The second-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroStabilizerElement_apply (x y : Fin 11) (hx : x ≠ 0) :
    (zeroStabilizerElement x hx).1.1 y = (Word.eval (zeroStabilizerWord x)) y :=
  rfl

/--
Every nonzero point is reached from `1` by an element of the stabilizer of `0`.
-/
theorem second_orbit_stabilizer_witness (x : Fin 11) (hx : x ≠ 0) :
    ∃ g : MulAction.stabilizer M11 (0 : Fin 11), g.1.1 (1 : Fin 11) = x :=
  ⟨zeroStabilizerElement x hx, by
    rw [zeroStabilizerElement_apply]
    exact zeroStabilizerWord_maps_one x hx⟩

/-- The stabilizer of `0` moves `1` through exactly the nonzero points. -/
theorem stabilizer_zero_orbit_one_eq_nonzero :
    MulAction.orbit (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11) =
      {x : Fin 11 | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩ hx0
    have hfix : g.1.1 (0 : Fin 11) = 0 := by
      have hg0 := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
    have hmap : g.1.1 (1 : Fin 11) = 0 := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
    have h10 : (1 : Fin 11) = 0 := g.1.1.injective (by rw [hmap, hfix])
    exact (by decide : (1 : Fin 11) ≠ 0) h10
  · intro hx
    obtain ⟨g, hg⟩ := second_orbit_stabilizer_witness x hx
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The second orbit in the stabilizer-chain plan has size 10. -/
theorem stabilizer_zero_orbit_one_ncard :
    (MulAction.orbit (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11)).ncard = 10 := by
  rw [stabilizer_zero_orbit_one_eq_nonzero]
  have hset : ({x : Fin 11 | x ≠ 0} : Set (Fin 11)) = ({0} : Set (Fin 11))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/-- The product of the first two verified stabilizer-chain orbit sizes. -/
theorem first_two_index_product : 11 * 10 = 110 := by
  norm_num

/--
Certificate words for the third stabilizer-chain step.

For a target `x` different from `0` and `1`, `zeroOneStabilizerWord x` fixes
both `0` and `1`, and sends `2` to `x`.
-/
def zeroOneStabilizerWord (x : Fin 11) : Word :=
  match x.val with
  | 3 => [Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a]
  | 4 => [Gen.aInv, Gen.b, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.bInv, Gen.a]
  | 5 => [Gen.aInv, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a]
  | 6 => [Gen.b]
  | 7 => [Gen.bInv]
  | 8 => [Gen.bInv, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a]
  | 9 => [Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a]
  | 10 => [Gen.b, Gen.b]
  | _ => []

set_option maxRecDepth 20000 in
/-- The third-step certificate words fix `0`. -/
theorem zeroOneStabilizerWord_fixes_zero_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 11) = 0 := by
  decide

theorem zeroOneStabilizerWord_fixes_zero (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 11) = 0 :=
  zeroOneStabilizerWord_fixes_zero_all x hx0 hx1

set_option maxRecDepth 20000 in
/-- The third-step certificate words fix `1`. -/
theorem zeroOneStabilizerWord_fixes_one_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 11) = 1 := by
  decide

theorem zeroOneStabilizerWord_fixes_one (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 11) = 1 :=
  zeroOneStabilizerWord_fixes_one_all x hx0 hx1

set_option maxRecDepth 20000 in
/-- The third-step certificate words send `2` to the requested remaining point. -/
theorem zeroOneStabilizerWord_maps_two_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 11) = x := by
  decide

theorem zeroOneStabilizerWord_maps_two (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 11) = x :=
  zeroOneStabilizerWord_maps_two_all x hx0 hx1

/-- Interpret the third-step word as an element of the stabilizer of `0` and `1`. -/
def zeroOneStabilizerElement (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11) :=
  let g0 : MulAction.stabilizer M11 (0 : Fin 11) :=
    ⟨Word.toM11 (zeroOneStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 11) = 0
      exact zeroOneStabilizerWord_fixes_zero x hx0 hx1⟩
  ⟨g0, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 11) = 1
    exact zeroOneStabilizerWord_fixes_one x hx0 hx1⟩

/-- The third-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroOneStabilizerElement_apply
    (x y : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (zeroOneStabilizerElement x hx0 hx1).1.1.1 y =
      (Word.eval (zeroOneStabilizerWord x)) y :=
  rfl

/--
Every point different from `0` and `1` is reached from `2` by an element of the
stabilizer of `0` and `1`.
-/
theorem third_orbit_stabilizer_witness (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ g : MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11),
      g.1.1.1 (2 : Fin 11) = x :=
  ⟨zeroOneStabilizerElement x hx0 hx1, by
    rw [zeroOneStabilizerElement_apply]
    exact zeroOneStabilizerWord_maps_two x hx0 hx1⟩

/-- The stabilizer of `0` and `1` moves `2` through exactly the remaining points. -/
theorem stabilizer_zero_one_orbit_two_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
        (2 : Fin 11) =
      {x : Fin 11 | x ≠ 0 ∧ x ≠ 1} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1 (0 : Fin 11) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1 (2 : Fin 11) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h20 : (2 : Fin 11) = 0 := g.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (2 : Fin 11) ≠ 0) h20
    · intro hx1
      have hfix1 : g.1.1.1 (1 : Fin 11) = 1 := by
        have hg1 := (MulAction.mem_stabilizer_iff.mp g.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
      have hmap : g.1.1.1 (2 : Fin 11) = 1 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
      have h21 : (2 : Fin 11) = 1 := g.1.1.1.injective (by rw [hmap, hfix1])
      exact (by decide : (2 : Fin 11) ≠ 1) h21
  · rintro ⟨hx0, hx1⟩
    obtain ⟨g, hg⟩ := third_orbit_stabilizer_witness x hx0 hx1
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The third orbit in the stabilizer-chain plan has size 9. -/
theorem stabilizer_zero_one_orbit_two_ncard :
    (MulAction.orbit
        (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
        (2 : Fin 11)).ncard = 9 := by
  rw [stabilizer_zero_one_orbit_two_eq_remaining]
  have hset : ({x : Fin 11 | x ≠ 0 ∧ x ≠ 1} : Set (Fin 11)) =
      ({0, 1} : Set (Fin 11))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  norm_num

/-- The product of the first three verified stabilizer-chain orbit sizes. -/
theorem first_three_index_product : 11 * 10 * 9 = 990 := by
  norm_num

/--
Certificate words for the fourth stabilizer-chain step.

For a target `x` different from `0`, `1`, and `2`,
`zeroOneTwoStabilizerWord x` fixes `0`, `1`, and `2`, and sends `3` to `x`.
-/
def zeroOneTwoStabilizerWord (x : Fin 11) : Word :=
  match x.val with
  | 4 => [Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv,
      Gen.aInv, Gen.aInv]
  | 5 => [Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b,
      Gen.aInv]
  | 6 => [Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a,
      Gen.b]
  | 7 => [Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.bInv,
      Gen.a]
  | 8 => [Gen.a, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv]
  | 9 => [Gen.bInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv,
      Gen.aInv]
  | 10 => [Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv]
  | _ => []

set_option maxRecDepth 40000 in
/-- The fourth-step certificate words fix `0`. -/
theorem zeroOneTwoStabilizerWord_fixes_zero_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 11) = 0 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_zero
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 11) = 0 :=
  zeroOneTwoStabilizerWord_fixes_zero_all x hx0 hx1 hx2

set_option maxRecDepth 40000 in
/-- The fourth-step certificate words fix `1`. -/
theorem zeroOneTwoStabilizerWord_fixes_one_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 11) = 1 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_one
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 11) = 1 :=
  zeroOneTwoStabilizerWord_fixes_one_all x hx0 hx1 hx2

set_option maxRecDepth 40000 in
/-- The fourth-step certificate words fix `2`. -/
theorem zeroOneTwoStabilizerWord_fixes_two_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 11) = 2 := by
  decide

theorem zeroOneTwoStabilizerWord_fixes_two
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 11) = 2 :=
  zeroOneTwoStabilizerWord_fixes_two_all x hx0 hx1 hx2

set_option maxRecDepth 40000 in
/-- The fourth-step certificate words send `3` to the requested remaining point. -/
theorem zeroOneTwoStabilizerWord_maps_three_all :
    ∀ x : Fin 11, x ≠ 0 → x ≠ 1 → x ≠ 2 →
      (Word.eval (zeroOneTwoStabilizerWord x)) (3 : Fin 11) = x := by
  decide

theorem zeroOneTwoStabilizerWord_maps_three
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (Word.eval (zeroOneTwoStabilizerWord x)) (3 : Fin 11) = x :=
  zeroOneTwoStabilizerWord_maps_three_all x hx0 hx1 hx2

/-- Interpret the fourth-step word as an element of the stabilizer of `0`, `1`, and `2`. -/
def zeroOneTwoStabilizerElement
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    MulAction.stabilizer
      (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
      (2 : Fin 11) :=
  let g0 : MulAction.stabilizer M11 (0 : Fin 11) :=
    ⟨Word.toM11 (zeroOneTwoStabilizerWord x), by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoStabilizerWord x)) (0 : Fin 11) = 0
      exact zeroOneTwoStabilizerWord_fixes_zero x hx0 hx1 hx2⟩
  let g1 : MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11) :=
    ⟨g0, by
      rw [MulAction.mem_stabilizer_iff]
      change (Word.eval (zeroOneTwoStabilizerWord x)) (1 : Fin 11) = 1
      exact zeroOneTwoStabilizerWord_fixes_one x hx0 hx1 hx2⟩
  ⟨g1, by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroOneTwoStabilizerWord x)) (2 : Fin 11) = 2
    exact zeroOneTwoStabilizerWord_fixes_two x hx0 hx1 hx2⟩

/-- The fourth-step stabilizer element has the stored word as its underlying permutation. -/
theorem zeroOneTwoStabilizerElement_apply
    (x y : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    (zeroOneTwoStabilizerElement x hx0 hx1 hx2).1.1.1.1 y =
      (Word.eval (zeroOneTwoStabilizerWord x)) y :=
  rfl

/--
Every point different from `0`, `1`, and `2` is reached from `3` by an element
of the stabilizer of `0`, `1`, and `2`.
-/
theorem fourth_orbit_stabilizer_witness
    (x : Fin 11) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    ∃ g : MulAction.stabilizer
        (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
        (2 : Fin 11),
      g.1.1.1.1 (3 : Fin 11) = x :=
  ⟨zeroOneTwoStabilizerElement x hx0 hx1 hx2, by
    rw [zeroOneTwoStabilizerElement_apply]
    exact zeroOneTwoStabilizerWord_maps_three x hx0 hx1 hx2⟩

/--
The stabilizer of `0`, `1`, and `2` moves `3` through exactly the remaining
eight points.
-/
theorem stabilizer_zero_one_two_orbit_three_eq_remaining :
    MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
          (2 : Fin 11))
        (3 : Fin 11) =
      {x : Fin 11 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    constructor
    · intro hx0
      have hfix0 : g.1.1.1.1 (0 : Fin 11) = 0 := by
        have hg0 := (MulAction.mem_stabilizer_iff.mp g.1.1.2)
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
      have hmap : g.1.1.1.1 (3 : Fin 11) = 0 := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
      have h30 : (3 : Fin 11) = 0 := g.1.1.1.1.injective (by rw [hmap, hfix0])
      exact (by decide : (3 : Fin 11) ≠ 0) h30
    · constructor
      · intro hx1
        have hfix1 : g.1.1.1.1 (1 : Fin 11) = 1 := by
          have hg1 := (MulAction.mem_stabilizer_iff.mp g.1.2)
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg1
        have hmap : g.1.1.1.1 (3 : Fin 11) = 1 := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx1] using hg
        have h31 : (3 : Fin 11) = 1 := g.1.1.1.1.injective (by rw [hmap, hfix1])
        exact (by decide : (3 : Fin 11) ≠ 1) h31
      · intro hx2
        have hfix2 : g.1.1.1.1 (2 : Fin 11) = 2 := by
          have hg2 := (MulAction.mem_stabilizer_iff.mp g.2)
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg2
        have hmap : g.1.1.1.1 (3 : Fin 11) = 2 := by
          simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx2] using hg
        have h32 : (3 : Fin 11) = 2 := g.1.1.1.1.injective (by rw [hmap, hfix2])
        exact (by decide : (3 : Fin 11) ≠ 2) h32
  · rintro ⟨hx0, hx1, hx2⟩
    obtain ⟨g, hg⟩ := fourth_orbit_stabilizer_witness x hx0 hx1 hx2
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The fourth orbit in the stabilizer-chain plan has size 8. -/
theorem stabilizer_zero_one_two_orbit_three_ncard :
    (MulAction.orbit
        (MulAction.stabilizer
          (MulAction.stabilizer (MulAction.stabilizer M11 (0 : Fin 11)) (1 : Fin 11))
          (2 : Fin 11))
        (3 : Fin 11)).ncard = 8 := by
  rw [stabilizer_zero_one_two_orbit_three_eq_remaining]
  have hset : ({x : Fin 11 | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} : Set (Fin 11)) =
      ({0, 1, 2} : Set (Fin 11))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl]
  have hcard : ({0, 1, 2} : Set (Fin 11)).ncard = 3 := by
    rw [show ({0, 1, 2} : Set (Fin 11)) = insert (0 : Fin 11) ({1, 2} : Set (Fin 11)) by
      ext x
      simp]
    rw [Set.ncard_insert_of_notMem]
    · rw [show ({1, 2} : Set (Fin 11)) = insert (1 : Fin 11) ({2} : Set (Fin 11)) by
        ext x
        simp]
      rw [Set.ncard_insert_of_notMem]
      · simp
      · simp
    · simp
  rw [hcard]
  norm_num

/-- The product of the four verified stabilizer-chain orbit sizes. -/
theorem four_index_product : 11 * 10 * 9 * 8 = 7920 := by
  norm_num

end StabilizerChain
end Certificates
end Sporadic
