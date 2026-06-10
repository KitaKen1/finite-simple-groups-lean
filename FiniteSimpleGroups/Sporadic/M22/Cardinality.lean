/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.GeneratedSubgroup
import FiniteSimpleGroups.Sporadic.M22.Certificates.ChainOrbits
import FiniteSimpleGroups.Sporadic.M22.Certificates.FinalStabilizer

/-!
# Cardinality proof workspace

The route is a verified stabilizer-chain certificate proving
`Nat.card Sporadic.M22 = 443520` along the base `0, 1, 2, 5, 3` with orbit
sizes `22, 21, 20, 16, 3` and a trivial final stabilizer.
-/

namespace Sporadic

namespace M22Cardinality

open M22Certificates M22Certificates.ChainOrbits M22Certificates.SteinerSystem
open M22Certificates.FinalStabilizer

/-- Stabilizer of the first base point in the 22-point action. -/
abbrev Stab0 : Type :=
  MulAction.stabilizer M22 (0 : Fin 22)

/-- Stabilizer of the first two base points. -/
abbrev Stab01 : Type :=
  MulAction.stabilizer Stab0 (1 : Fin 22)

/-- Stabilizer of the first three base points. -/
abbrev Stab012 : Type :=
  MulAction.stabilizer Stab01 (2 : Fin 22)

/-- Stabilizer of the first four base points `0,1,2,5`. -/
abbrev Stab0125 : Type :=
  MulAction.stabilizer Stab012 (5 : Fin 22)

/-- Stabilizer of all five base points `0,1,2,5,3`. -/
abbrev StabBase : Type :=
  MulAction.stabilizer Stab0125 (3 : Fin 22)

/-- The order expected from the verified orbit chain. -/
theorem target_order_arithmetic : 22 * 21 * 20 * 16 * 3 = 443520 := by
  norm_num

/-- The first orbit-stabilizer step: `|M22| = 22 * |Stab0|`. -/
theorem card_M22_eq_first_orbit_mul_stabilizer :
    Nat.card M22 = 22 * Nat.card Stab0 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M22 (0 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.orbit_zero_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0)]

/-- The second orbit-stabilizer step: `|Stab0| = 21 * |Stab01|`. -/
theorem card_stab0_eq_second_orbit_mul_stabilizer :
    Nat.card Stab0 = 21 * Nat.card Stab01 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0 (1 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stabilizer_zero_orbit_one_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab01)]

/-- The third orbit-stabilizer step: `|Stab01| = 20 * |Stab012|`. -/
theorem card_stab01_eq_third_orbit_mul_stabilizer :
    Nat.card Stab01 = 20 * Nat.card Stab012 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab01 (2 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stabilizer_zero_one_orbit_two_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab012)]

/-- The fourth orbit-stabilizer step: `|Stab012| = 16 * |Stab0125|`. -/
theorem card_stab012_eq_fourth_orbit_mul_stabilizer :
    Nat.card Stab012 = 16 * Nat.card Stab0125 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab012 (5 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab012_orbit_five_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0125)]

/-- The fifth orbit-stabilizer step: `|Stab0125| = 3 * |StabBase|`. -/
theorem card_stab0125_eq_fifth_orbit_mul_stabilizer :
    Nat.card Stab0125 = 3 * Nat.card StabBase := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0125 (3 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, ChainOrbits.stab0125_orbit_three_ncard]
  rw [← Nat.card_eq_fintype_card (α := StabBase)]

/--
The verified stabilizer-chain data reduces the cardinality theorem to the
final stabilizer certificate.
-/
theorem card_M22_eq_target_mul_final_stabilizer :
    Nat.card M22 = 443520 * Nat.card StabBase := by
  rw [card_M22_eq_first_orbit_mul_stabilizer,
    card_stab0_eq_second_orbit_mul_stabilizer,
    card_stab01_eq_third_orbit_mul_stabilizer,
    card_stab012_eq_fourth_orbit_mul_stabilizer,
    card_stab0125_eq_fifth_orbit_mul_stabilizer]
  ring

/-- Elements of the final stabilizer fix the base point `0`. -/
theorem stabBase_fixes_zero (g : StabBase) : g.1.1.1.1.1.1 0 = 0 := by
  have hmem : g.1.1.1.1.1 ∈ MulAction.stabilizer M22 (0 : Fin 22) := g.1.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (0 : Fin 22) = 0
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `1`. -/
theorem stabBase_fixes_one (g : StabBase) : g.1.1.1.1.1.1 1 = 1 := by
  have hmem : g.1.1.1.1 ∈ MulAction.stabilizer Stab0 (1 : Fin 22) := g.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (1 : Fin 22) = 1
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `2`. -/
theorem stabBase_fixes_two (g : StabBase) : g.1.1.1.1.1.1 2 = 2 := by
  have hmem : g.1.1.1 ∈ MulAction.stabilizer Stab01 (2 : Fin 22) := g.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (2 : Fin 22) = 2
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `5`. -/
theorem stabBase_fixes_five (g : StabBase) : g.1.1.1.1.1.1 5 = 5 := by
  have hmem : g.1.1 ∈ MulAction.stabilizer Stab012 (5 : Fin 22) := g.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (5 : Fin 22) = 5
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the base point `3`. -/
theorem stabBase_fixes_three (g : StabBase) : g.1.1.1.1.1.1 3 = 3 := by
  have hmem : g.1 ∈ MulAction.stabilizer Stab0125 (3 : Fin 22) := g.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (3 : Fin 22) = 3
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/--
The final five-point stabilizer is trivial, using the checked block
certificate and evenness.
-/
theorem final_stabilizer_eq_one (g : StabBase) : g = 1 := by
  have hperm : g.1.1.1.1.1.1 = (1 : Perm22) := by
    exact fixed_base_preserves_wittBlocks_eq_one g.1.1.1.1.1.1
      (M22_preserves_wittBlocks g.1.1.1.1.1)
      (M22_toPerm_sign g.1.1.1.1.1)
      (stabBase_fixes_zero g)
      (stabBase_fixes_one g)
      (stabBase_fixes_two g)
      (stabBase_fixes_three g)
      (stabBase_fixes_five g)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hperm

/-- The final stabilizer has order one. -/
theorem final_stabilizer_card_one : Nat.card StabBase = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => final_stabilizer_eq_one g⟩

/-- The verified stabilizer-chain certificate proves `|M22| = 443520`. -/
theorem card_M22 : Nat.card M22 = 443520 := by
  calc
    Nat.card M22 = 443520 * Nat.card StabBase :=
      card_M22_eq_target_mul_final_stabilizer
    _ = 443520 * 1 := by rw [final_stabilizer_card_one]
    _ = 443520 := by norm_num

end M22Cardinality

end Sporadic
