/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.GeneratedSubgroup
import FiniteSimpleGroups.Sporadic.M11.Certificates.StabilizerChain
import FiniteSimpleGroups.Sporadic.M11.Certificates.WittDesign

/-!
# Cardinality proof workspace

The intended first route is a verified stabilizer-chain certificate proving
`Nat.card Sporadic.M11 = 7920`. The final theorem name is reserved in
`FiniteSimpleGroups.Sporadic.M11.Statement` until the certificate has been implemented.
-/

namespace Sporadic

namespace M11Cardinality

open Certificates.WittDesign

/-- Stabilizer of the first base point in the 11-point action. -/
abbrev Stab0 : Type :=
  MulAction.stabilizer M11 (0 : Fin 11)

/-- Stabilizer of the first two base points in the 11-point action. -/
abbrev Stab01 : Type :=
  MulAction.stabilizer Stab0 (1 : Fin 11)

/-- Stabilizer of the first three base points in the 11-point action. -/
abbrev Stab012 : Type :=
  MulAction.stabilizer Stab01 (2 : Fin 11)

/-- Stabilizer of the first four base points in the 11-point action. -/
abbrev Stab0123 : Type :=
  MulAction.stabilizer Stab012 (3 : Fin 11)

/-- The order expected from sharp 4-transitivity on 11 points. -/
theorem target_order_arithmetic : 11 * 10 * 9 * 8 = 7920 := by
  norm_num

/-- The first orbit-stabilizer step: `|M11| = 11 * |Stab0|`. -/
theorem card_M11_eq_first_orbit_mul_stabilizer :
    Nat.card M11 = 11 * Nat.card Stab0 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M11 (0 : Fin 11)]
  rw [Set.fintypeCard_eq_ncard, Certificates.StabilizerChain.orbit_zero_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0)]

/-- The second orbit-stabilizer step: `|Stab0| = 10 * |Stab01|`. -/
theorem card_stab0_eq_second_orbit_mul_stabilizer :
    Nat.card Stab0 = 10 * Nat.card Stab01 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0 (1 : Fin 11)]
  rw [Set.fintypeCard_eq_ncard,
    Certificates.StabilizerChain.stabilizer_zero_orbit_one_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab01)]

/-- The third orbit-stabilizer step: `|Stab01| = 9 * |Stab012|`. -/
theorem card_stab01_eq_third_orbit_mul_stabilizer :
    Nat.card Stab01 = 9 * Nat.card Stab012 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab01 (2 : Fin 11)]
  rw [Set.fintypeCard_eq_ncard,
    Certificates.StabilizerChain.stabilizer_zero_one_orbit_two_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab012)]

/-- The fourth orbit-stabilizer step: `|Stab012| = 8 * |Stab0123|`. -/
theorem card_stab012_eq_fourth_orbit_mul_stabilizer :
    Nat.card Stab012 = 8 * Nat.card Stab0123 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab012 (3 : Fin 11)]
  rw [Set.fintypeCard_eq_ncard,
    Certificates.StabilizerChain.stabilizer_zero_one_two_orbit_three_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0123)]

/--
The verified stabilizer-chain data reduces the cardinality theorem to the final
stabilizer certificate.
-/
theorem card_M11_eq_target_mul_final_stabilizer :
    Nat.card M11 = 7920 * Nat.card Stab0123 := by
  rw [card_M11_eq_first_orbit_mul_stabilizer,
    card_stab0_eq_second_orbit_mul_stabilizer,
    card_stab01_eq_third_orbit_mul_stabilizer,
    card_stab012_eq_fourth_orbit_mul_stabilizer]
  ring

/--
Once the four-point stabilizer is proved trivial by certificate,
the target cardinality follows immediately.
-/
theorem card_M11_of_final_stabilizer_card_one (h : Nat.card Stab0123 = 1) :
    Nat.card M11 = 7920 := by
  calc
    Nat.card M11 = 7920 * Nat.card Stab0123 :=
      card_M11_eq_target_mul_final_stabilizer
    _ = 7920 * 1 := by rw [h]
    _ = 7920 := by norm_num

/-- Elements of the final stabilizer fix the first base point. -/
theorem stab0123_fixes_zero (g : Stab0123) : g.1.1.1.1.1 0 = 0 := by
  have hmem : g.1.1.1.1 ∈ MulAction.stabilizer M11 (0 : Fin 11) := g.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1 (0 : Fin 11) = 0
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the second base point. -/
theorem stab0123_fixes_one (g : Stab0123) : g.1.1.1.1.1 1 = 1 := by
  have hmem : g.1.1.1 ∈ MulAction.stabilizer Stab0 (1 : Fin 11) := g.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1 (1 : Fin 11) = 1
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the third base point. -/
theorem stab0123_fixes_two (g : Stab0123) : g.1.1.1.1.1 2 = 2 := by
  have hmem : g.1.1 ∈ MulAction.stabilizer Stab01 (2 : Fin 11) := g.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1 (2 : Fin 11) = 2
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the fourth base point. -/
theorem stab0123_fixes_three (g : Stab0123) : g.1.1.1.1.1 3 = 3 := by
  have hmem : g.1 ∈ MulAction.stabilizer Stab012 (3 : Fin 11) := g.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1 (3 : Fin 11) = 3
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/--
The final four-point stabilizer is trivial, using the checked Witt block
certificate in `FiniteSimpleGroups.Sporadic.M11.Certificates.WittDesign`.
-/
theorem final_stabilizer_eq_one (g : Stab0123) : g = 1 := by
  have hperm : g.1.1.1.1.1 = (1 : Perm11) := by
    exact fixed_four_preserves_wittBlocks_eq_one g.1.1.1.1.1
      (M11_preserves_wittBlocks g.1.1.1.1)
      (stab0123_fixes_zero g)
      (stab0123_fixes_one g)
      (stab0123_fixes_two g)
      (stab0123_fixes_three g)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hperm

/-- The final stabilizer has order one. -/
theorem final_stabilizer_card_one : Nat.card Stab0123 = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => final_stabilizer_eq_one g⟩

/-- The verified stabilizer-chain certificate proves `|M11| = 7920`. -/
theorem card_M11 : Nat.card M11 = 7920 :=
  card_M11_of_final_stabilizer_card_one final_stabilizer_card_one

end M11Cardinality

end Sporadic
