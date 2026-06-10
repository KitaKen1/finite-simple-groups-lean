/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.GeneratedSubgroup
import FiniteSimpleGroups.Sporadic.M12.Certificates.StabilizerChain
import FiniteSimpleGroups.Sporadic.M12.Certificates.WittDesign

/-!
# Cardinality proof workspace

The route is a verified stabilizer-chain certificate proving
`Nat.card Sporadic.M12 = 95040`, mirroring sharp 5-transitivity on 12 points.
-/

namespace Sporadic

namespace M12Cardinality

open M12Certificates.WittDesign

/-- Stabilizer of the first base point in the 12-point action. -/
abbrev Stab0 : Type :=
  MulAction.stabilizer M12 (0 : Fin 12)

/-- Stabilizer of the first two base points in the 12-point action. -/
abbrev Stab01 : Type :=
  MulAction.stabilizer Stab0 (1 : Fin 12)

/-- Stabilizer of the first three base points in the 12-point action. -/
abbrev Stab012 : Type :=
  MulAction.stabilizer Stab01 (2 : Fin 12)

/-- Stabilizer of the first four base points in the 12-point action. -/
abbrev Stab0123 : Type :=
  MulAction.stabilizer Stab012 (3 : Fin 12)

/-- Stabilizer of the first five base points in the 12-point action. -/
abbrev Stab01234 : Type :=
  MulAction.stabilizer Stab0123 (4 : Fin 12)

/-- The order expected from sharp 5-transitivity on 12 points. -/
theorem target_order_arithmetic : 12 * 11 * 10 * 9 * 8 = 95040 := by
  norm_num

/-- The first orbit-stabilizer step: `|M12| = 12 * |Stab0|`. -/
theorem card_M12_eq_first_orbit_mul_stabilizer :
    Nat.card M12 = 12 * Nat.card Stab0 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M12 (0 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard, M12Certificates.StabilizerChain.orbit_zero_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0)]

/-- The second orbit-stabilizer step: `|Stab0| = 11 * |Stab01|`. -/
theorem card_stab0_eq_second_orbit_mul_stabilizer :
    Nat.card Stab0 = 11 * Nat.card Stab01 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0 (1 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard,
    M12Certificates.StabilizerChain.stabilizer_zero_orbit_one_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab01)]

/-- The third orbit-stabilizer step: `|Stab01| = 10 * |Stab012|`. -/
theorem card_stab01_eq_third_orbit_mul_stabilizer :
    Nat.card Stab01 = 10 * Nat.card Stab012 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab01 (2 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard,
    M12Certificates.StabilizerChain.stabilizer_zero_one_orbit_two_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab012)]

/-- The fourth orbit-stabilizer step: `|Stab012| = 9 * |Stab0123|`. -/
theorem card_stab012_eq_fourth_orbit_mul_stabilizer :
    Nat.card Stab012 = 9 * Nat.card Stab0123 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab012 (3 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard,
    M12Certificates.StabilizerChain.stabilizer_zero_one_two_orbit_three_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab0123)]

/-- The fifth orbit-stabilizer step: `|Stab0123| = 8 * |Stab01234|`. -/
theorem card_stab0123_eq_fifth_orbit_mul_stabilizer :
    Nat.card Stab0123 = 8 * Nat.card Stab01234 := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group Stab0123 (4 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard,
    M12Certificates.StabilizerChain.stabilizer_zero_one_two_three_orbit_four_ncard]
  rw [← Nat.card_eq_fintype_card (α := Stab01234)]

/--
The verified stabilizer-chain data reduces the cardinality theorem to the final
stabilizer certificate.
-/
theorem card_M12_eq_target_mul_final_stabilizer :
    Nat.card M12 = 95040 * Nat.card Stab01234 := by
  rw [card_M12_eq_first_orbit_mul_stabilizer,
    card_stab0_eq_second_orbit_mul_stabilizer,
    card_stab01_eq_third_orbit_mul_stabilizer,
    card_stab012_eq_fourth_orbit_mul_stabilizer,
    card_stab0123_eq_fifth_orbit_mul_stabilizer]
  ring

/--
Once the five-point stabilizer is proved trivial by certificate,
the target cardinality follows immediately.
-/
theorem card_M12_of_final_stabilizer_card_one (h : Nat.card Stab01234 = 1) :
    Nat.card M12 = 95040 := by
  calc
    Nat.card M12 = 95040 * Nat.card Stab01234 :=
      card_M12_eq_target_mul_final_stabilizer
    _ = 95040 * 1 := by rw [h]
    _ = 95040 := by norm_num

/-- Elements of the final stabilizer fix the first base point. -/
theorem stab01234_fixes_zero (g : Stab01234) : g.1.1.1.1.1.1 0 = 0 := by
  have hmem : g.1.1.1.1.1 ∈ MulAction.stabilizer M12 (0 : Fin 12) := g.1.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (0 : Fin 12) = 0
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the second base point. -/
theorem stab01234_fixes_one (g : Stab01234) : g.1.1.1.1.1.1 1 = 1 := by
  have hmem : g.1.1.1.1 ∈ MulAction.stabilizer Stab0 (1 : Fin 12) := g.1.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (1 : Fin 12) = 1
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the third base point. -/
theorem stab01234_fixes_two (g : Stab01234) : g.1.1.1.1.1.1 2 = 2 := by
  have hmem : g.1.1.1 ∈ MulAction.stabilizer Stab01 (2 : Fin 12) := g.1.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (2 : Fin 12) = 2
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the fourth base point. -/
theorem stab01234_fixes_three (g : Stab01234) : g.1.1.1.1.1.1 3 = 3 := by
  have hmem : g.1.1 ∈ MulAction.stabilizer Stab012 (3 : Fin 12) := g.1.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (3 : Fin 12) = 3
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- Elements of the final stabilizer fix the fifth base point. -/
theorem stab01234_fixes_four (g : Stab01234) : g.1.1.1.1.1.1 4 = 4 := by
  have hmem : g.1 ∈ MulAction.stabilizer Stab0123 (4 : Fin 12) := g.2
  have hfix := MulAction.mem_stabilizer_iff.mp hmem
  change g.1.1.1.1.1.1 (4 : Fin 12) = 4
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/--
The final five-point stabilizer is trivial, using the checked Witt block
certificate in `SporadicM12.Certificates.WittDesign`.
-/
theorem final_stabilizer_eq_one (g : Stab01234) : g = 1 := by
  have hperm : g.1.1.1.1.1.1 = (1 : Perm12) := by
    exact fixed_five_preserves_wittBlocks_eq_one g.1.1.1.1.1.1
      (M12_preserves_wittBlocks g.1.1.1.1.1)
      (stab01234_fixes_zero g)
      (stab01234_fixes_one g)
      (stab01234_fixes_two g)
      (stab01234_fixes_three g)
      (stab01234_fixes_four g)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hperm

/-- The final stabilizer has order one. -/
theorem final_stabilizer_card_one : Nat.card Stab01234 = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_one_iff.mpr ⟨1, fun g => final_stabilizer_eq_one g⟩

/-- The verified stabilizer-chain certificate proves `|M12| = 95040`. -/
theorem card_M12 : Nat.card M12 = 95040 :=
  card_M12_of_final_stabilizer_card_one final_stabilizer_card_one

end M12Cardinality

end Sporadic
