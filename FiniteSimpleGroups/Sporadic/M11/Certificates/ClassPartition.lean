/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Mathlib.Data.Set.Card.Arithmetic
import FiniteSimpleGroups.Sporadic.M11.Certificates.TwoA

/-!
# Conjugacy-class partition workspace

This file packages the verified conjugacy-orbit rows into the form needed by
the final normal-subgroup argument. The only remaining class-partition work is
to prove that the same-order split rows `8A/8B` and `11A/11B` are not conjugate
inside `M11`.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

open scoped Function

/-- The class-table index of the 11A representative. -/
abbrev rep11AIndex : Fin 10 :=
  ⟨8, by decide⟩

/-- The conjugacy orbit attached to a class-table row. -/
def classOrbit (i : Fin 10) : Set M11 :=
  MulAction.orbit (ConjAct M11) (representativeM11 i)

/-- The 11A representative row is the generator `m11a`. -/
theorem representativeM11_rep11AIndex_eq_m11aM11 :
    representativeM11 rep11AIndex = m11aM11 := by
  apply Subtype.ext
  decide

/-- The identity representative row is the identity element. -/
theorem representativeM11_rep1AIndex_eq_one :
    representativeM11 ⟨0, by decide⟩ = 1 := by
  apply Subtype.ext
  decide

/-- Anything conjugate to the identity representative is the identity. -/
theorem eq_one_of_isConj_rep1A {x : M11}
    (hx : IsConj x (representativeM11 ⟨0, by decide⟩)) :
    x = 1 := by
  rcases isConj_iff.mp hx with ⟨g, hg⟩
  have hg1 : g * x * g⁻¹ = 1 := by
    rwa [representativeM11_rep1AIndex_eq_one] at hg
  have hgx : g * x = g := by
    rw [mul_inv_eq_iff_eq_mul] at hg1
    simpa using hg1
  exact mul_left_cancel hgx

/-- The identity row has a singleton conjugacy orbit. -/
theorem rep1AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 ⟨0, by decide⟩)) = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨?_, ?_⟩
  · constructor
    intro x y
    apply Subtype.ext
    have hxconj0 : IsConj x.1 (representativeM11 ⟨0, by decide⟩) :=
      ConjAct.mem_orbit_conjAct.mp x.2
    have hyconj0 : IsConj y.1 (representativeM11 ⟨0, by decide⟩) :=
      ConjAct.mem_orbit_conjAct.mp y.2
    have hxone : x.1 = 1 := eq_one_of_isConj_rep1A hxconj0
    have hyone : y.1 = 1 := eq_one_of_isConj_rep1A hyconj0
    rw [hxone, hyone]
  · refine ⟨⟨1, ?_⟩⟩
    rw [ConjAct.mem_orbit_conjAct, representativeM11_rep1AIndex_eq_one]

set_option maxHeartbeats 1000000 in
-- The ten cases unfold the concrete class-size table and the verified orbit certificates.
/-- The verified cardinality of the conjugacy orbit for every class-table row. -/
theorem classOrbit_ncard (i : Fin 10) :
    (classOrbit i).ncard = classSizeList.get ⟨i.1, by
      rw [classSizeList_length]
      exact i.2⟩ := by
  fin_cases i
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 ⟨0, by decide⟩)) = 1
    exact rep1AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep2AIndex)) = 165
    exact rep2AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep3AIndex)) = 440
    exact rep3AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep4AIndex)) = 990
    exact rep4AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep5AIndex)) = 1584
    exact rep5AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep6AIndex)) = 1320
    exact rep6AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep8AIndex)) = 990
    exact rep8AConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep8BIndex)) = 990
    exact rep8BConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep11AIndex)) = 720
    rw [representativeM11_rep11AIndex_eq_m11aM11]
    exact m11aConjOrbit_card
  · rw [← Nat.card_coe_set_eq]
    change Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep11BIndex)) = 720
    exact rep11BConjOrbit_card

/-- The `M11` element order of every representative matches the class-table row. -/
theorem representativeM11_orderOf_eq (i : Fin 10) :
    orderOf (representativeM11 i) = classElementOrder i := by
  change orderOf (⟨representativePerm i, Word.eval_mem_M11Subgroup (representativeWord i)⟩ :
    M11) = classElementOrder i
  rw [Subgroup.orderOf_mk]
  exact representativePerm_orderOf_eq i

/-- Conjugate group elements have the same order. -/
theorem orderOf_eq_of_isConj {x y : M11} (hxy : IsConj x y) :
    orderOf x = orderOf y := by
  rcases isConj_iff.mp hxy with ⟨g, hg⟩
  refine SemiconjBy.orderOf_eq g ?_
  rw [SemiconjBy]
  rwa [mul_inv_eq_iff_eq_mul] at hg

/-- Class-table rows with different element orders have disjoint conjugacy orbits. -/
theorem classOrbit_disjoint_of_order_ne {i j : Fin 10}
    (horder : classElementOrder i ≠ classElementOrder j) :
    Disjoint (classOrbit i) (classOrbit j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxi' : IsConj x (representativeM11 i) := by
    simpa [classOrbit] using (ConjAct.mem_orbit_conjAct.mp hxi)
  have hxj' : IsConj x (representativeM11 j) := by
    simpa [classOrbit] using (ConjAct.mem_orbit_conjAct.mp hxj)
  have hi := orderOf_eq_of_isConj hxi'
  have hj := orderOf_eq_of_isConj hxj'
  exact horder (by
    rw [← representativeM11_orderOf_eq i, ← representativeM11_orderOf_eq j]
    exact hi.symm.trans hj)

set_option linter.flexible false in
/--
If the ten displayed orbits are pairwise disjoint, their union has cardinality
`7920`.
-/
theorem classOrbit_iUnion_ncard_of_pairwise
    (hdisj : Pairwise (Disjoint on classOrbit)) :
    (⋃ i : Fin 10, classOrbit i).ncard = 7920 := by
  have hfin : ∀ i : Fin 10, (classOrbit i).Finite := fun _ => Set.toFinite _
  rw [Set.ncard_iUnion_of_finite hfin hdisj]
  rw [finsum_eq_sum_of_fintype]
  simp [classOrbit_ncard, classSizeList]
  decide

/--
If the ten displayed orbits are pairwise disjoint, then they cover all of
`M11`.
-/
theorem classOrbit_iUnion_eq_univ_of_pairwise
    (hdisj : Pairwise (Disjoint on classOrbit)) :
    (⋃ i : Fin 10, classOrbit i) = Set.univ := by
  by_contra hne
  have hlt : (⋃ i : Fin 10, classOrbit i).ncard < Nat.card M11 :=
    Set.ncard_lt_card hne
  rw [classOrbit_iUnion_ncard_of_pairwise hdisj, M11Cardinality.card_M11] at hlt
  omega

end ConjugacyClasses
end Certificates
end Sporadic
