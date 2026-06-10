/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.L34.Transitivity

/-!
# Cardinality bookkeeping for L34

Orbit-stabilizer along the base `0, 1` gives
`|L34| = 21 * 20 * |Stab01| = 420 * |Stab01|`,
and the 48-word certificate gives `48 ≤ |Stab01|`.

The matching upper bound (`|L34| ≤ 20160`, hence `|Stab01| = 48` and
`|L34| = 20160`) comes from embedding `L34` into the point stabilizer of
`M22` and lives in `SporadicM22/PointStabilizer21.lean`.
-/

namespace Sporadic
namespace L34

/-- Stabilizer of the first base point in the 21-point action. -/
abbrev Stab0 : Type :=
  MulAction.stabilizer L34Subgroup (0 : Fin 21)

/-- Stabilizer of the first two base points. -/
abbrev Stab01 : Type :=
  MulAction.stabilizer Stab0 (1 : Fin 21)

/-! ## Level 1: the orbit of `0` is everything -/

theorem first_orbit_witness (x : Fin 21) :
    ∃ g : L34Subgroup, g.1 (0 : Fin 21) = x :=
  ⟨Word.toL34 (orbitZeroWord x), by simpa using orbitZeroWord_maps_zero_all x⟩

theorem orbit_zero_eq_univ :
    MulAction.orbit L34Subgroup (0 : Fin 21) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := first_orbit_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem orbit_zero_ncard :
    (MulAction.orbit L34Subgroup (0 : Fin 21)).ncard = 21 := by
  rw [orbit_zero_eq_univ, Set.ncard_univ]
  simp

/-! ## Level 2: the stabilizer of `0` moves `1` to every nonzero point -/

def zeroStabElement (x : Fin 21) (hx : x ≠ 0) : Stab0 :=
  ⟨Word.toL34 (zeroStabWord x), by
    rw [MulAction.mem_stabilizer_iff]
    change (Word.eval (zeroStabWord x)) (0 : Fin 21) = 0
    exact zeroStabWord_fixes_zero_all x hx⟩

theorem second_orbit_witness (x : Fin 21) (hx : x ≠ 0) :
    ∃ g : Stab0, g.1.1 (1 : Fin 21) = x :=
  ⟨zeroStabElement x hx, by
    change (Word.eval (zeroStabWord x)) (1 : Fin 21) = x
    exact zeroStabWord_maps_one_all x hx⟩

theorem stab0_orbit_one_eq_nonzero :
    MulAction.orbit Stab0 (1 : Fin 21) = {x : Fin 21 | x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨g, hg⟩ hx0
    have hfix : g.1.1 (0 : Fin 21) = 0 := by
      have hg0 := (MulAction.mem_stabilizer_iff.mp g.2)
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg0
    have hmap : g.1.1 (1 : Fin 21) = 0 := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hx0] using hg
    have h10 : (1 : Fin 21) = 0 := g.1.1.injective (by rw [hmap, hfix])
    exact (by decide : (1 : Fin 21) ≠ 0) h10
  · intro hx
    obtain ⟨g, hg⟩ := second_orbit_witness x hx
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem stab0_orbit_one_ncard :
    (MulAction.orbit Stab0 (1 : Fin 21)).ncard = 20 := by
  rw [stab0_orbit_one_eq_nonzero]
  have hset : ({x : Fin 21 | x ≠ 0} : Set (Fin 21)) = ({0} : Set (Fin 21))ᶜ := by
    ext x
    simp
  rw [hset, Set.ncard_compl, Set.ncard_singleton]
  simp

/-! ## The 420-fold formula -/

theorem card_L34_eq_first_orbit_mul_stabilizer :
    Nat.card L34Subgroup = 21 * Nat.card Stab0 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group L34Subgroup (0 : Fin 21)]
  rw [Set.fintypeCard_eq_ncard, orbit_zero_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0)]

theorem card_stab0_eq_second_orbit_mul_stabilizer :
    Nat.card Stab0 = 20 * Nat.card Stab01 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0 (1 : Fin 21)]
  rw [Set.fintypeCard_eq_ncard, stab0_orbit_one_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab01)]

theorem card_L34_eq_420_mul_stab01 :
    Nat.card L34Subgroup = 420 * Nat.card Stab01 := by
  rw [card_L34_eq_first_orbit_mul_stabilizer,
    card_stab0_eq_second_orbit_mul_stabilizer]
  ring

/-! ## Lower bound for the two-point stabilizer -/

/-- The list of 48 two-point stabilizer elements built from the words. -/
noncomputable def stab01List : List Stab01 :=
  stab01WordList.pmap
    (fun w hw =>
      (⟨⟨Word.toL34 w, by
          rw [MulAction.mem_stabilizer_iff]
          change (Word.eval w) (0 : Fin 21) = 0
          exact stab01WordList_fixes_zero w hw⟩, by
        rw [MulAction.mem_stabilizer_iff]
        change (Word.eval w) (1 : Fin 21) = 1
        exact stab01WordList_fixes_one w hw⟩ : Stab01))
    (fun _ h => h)

theorem stab01List_map_eval :
    stab01List.map (fun g : Stab01 => g.1.1.1) = stab01WordList.map Word.eval := by
  rw [stab01List, List.map_pmap]
  exact List.pmap_eq_map _

theorem stab01List_nodup : stab01List.Nodup := by
  have h := stab01WordList_evals_nodup
  rw [← stab01List_map_eval] at h
  exact h.of_map _

theorem stab01List_length : stab01List.length = 48 := by
  rw [stab01List, List.length_pmap]
  exact stab01WordList_length

/-- The two-point stabilizer has at least 48 elements. -/
theorem stab01_lower : 48 ≤ Nat.card Stab01 := by
  classical
  haveI : Fintype Stab01 := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  calc 48 = stab01List.length := stab01List_length.symm
    _ ≤ Fintype.card Stab01 := stab01List_nodup.length_le_card

end L34
end Sporadic
