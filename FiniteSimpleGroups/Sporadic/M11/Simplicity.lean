/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Cardinality
import FiniteSimpleGroups.Sporadic.M11.Certificates.ConjugacyClasses
import FiniteSimpleGroups.Sporadic.M11.Certificates.FourA
import FiniteSimpleGroups.Sporadic.M11.Certificates.ThreeA
import FiniteSimpleGroups.Sporadic.M11.Certificates.TwoA
import FiniteSimpleGroups.Sporadic.M11.Certificates.SplitClasses

/-!
# Simplicity proof workspace

The final theorem `Sporadic.simple_M11` is reserved in `FiniteSimpleGroups.Sporadic.M11.Statement`.
This file will hold the certificate-verified normal-subgroup argument.
-/

namespace Sporadic

namespace M11Simplicity

open Certificates.ConjugacyClasses
open scoped Function

/--
Placeholder namespace marker for the future conjugacy-class union argument.
This theorem is intentionally trivial; no mathematical target is hidden here.
-/
theorem workspace_ready : True :=
  trivial

/-- A normal subgroup is closed under conjugation by `M11`. -/
theorem normal_subgroup_closed_under_conj (N : Subgroup M11) [N.Normal]
    {x : M11} (hx : x ∈ N) (g : M11) :
    g * x * g⁻¹ ∈ N :=
  ‹N.Normal›.conj_mem x hx g

/-- If a normal subgroup contains an element, it contains its full conjugacy orbit. -/
theorem conj_orbit_subset_of_normal (N : Subgroup M11) [N.Normal]
    {x : M11} (hx : x ∈ N) :
    MulAction.orbit (ConjAct M11) x ⊆ N := by
  intro y hy
  rcases MulAction.mem_orbit_iff.mp hy with ⟨g, hg⟩
  rw [← hg, ConjAct.smul_def]
  exact normal_subgroup_closed_under_conj N hx (ConjAct.ofConjAct g)

/-- A normal subgroup containing `x` has cardinality at least the conjugacy orbit of `x`. -/
theorem card_orbit_le_of_mem_normal (N : Subgroup M11) [N.Normal]
    {x : M11} (hx : x ∈ N) :
    Nat.card (MulAction.orbit (ConjAct M11) x) ≤ Nat.card N := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective
    (fun y : MulAction.orbit (ConjAct M11) x =>
      (⟨y.1, conj_orbit_subset_of_normal N hx y.2⟩ : N))
    (by
      intro y z hyz
      apply Subtype.ext
      exact congrArg (fun n : N => (n : M11)) hyz)

/-- If a normal subgroup contains an 11A element, its order is at least `720`. -/
theorem card_ge_720_of_mem_11A (N : Subgroup M11) [N.Normal]
    (hx : m11aM11 ∈ N) :
    720 ≤ Nat.card N := by
  rw [← m11aConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 11B representative, its order is at least `720`. -/
theorem card_ge_720_of_mem_11B (N : Subgroup M11) [N.Normal]
    (hx : rep11BM11 ∈ N) :
    720 ≤ Nat.card N := by
  rw [← rep11BConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 5A representative, its order is at least `1584`. -/
theorem card_ge_1584_of_mem_5A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep5AIndex ∈ N) :
    1584 ≤ Nat.card N := by
  rw [← rep5AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 6A representative, its order is at least `1320`. -/
theorem card_ge_1320_of_mem_6A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep6AIndex ∈ N) :
    1320 ≤ Nat.card N := by
  rw [← rep6AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 4A representative, its order is at least `990`. -/
theorem card_ge_990_of_mem_4A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep4AIndex ∈ N) :
    990 ≤ Nat.card N := by
  rw [← rep4AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 3A representative, its order is at least `440`. -/
theorem card_ge_440_of_mem_3A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep3AIndex ∈ N) :
    440 ≤ Nat.card N := by
  rw [← rep3AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 2A representative, its order is at least `165`. -/
theorem card_ge_165_of_mem_2A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep2AIndex ∈ N) :
    165 ≤ Nat.card N := by
  rw [← rep2AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 8A representative, its order is at least `990`. -/
theorem card_ge_990_of_mem_8A (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep8AIndex ∈ N) :
    990 ≤ Nat.card N := by
  rw [← rep8AConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- If a normal subgroup contains the verified 8B representative, its order is at least `990`. -/
theorem card_ge_990_of_mem_8B (N : Subgroup M11) [N.Normal]
    (hx : representativeM11 rep8BIndex ∈ N) :
    990 ≤ Nat.card N := by
  rw [← rep8BConjOrbit_card]
  exact card_orbit_le_of_mem_normal N hx

/-- Every subgroup order divides the verified order `7920` of `M11`. -/
theorem subgroup_card_dvd_target (N : Subgroup M11) : Nat.card N ∣ 7920 := by
  have h := Subgroup.card_subgroup_dvd_card (α := M11) N
  rwa [M11Cardinality.card_M11] at h

/-!
## Final normal-subgroup count

The verified class partition turns every normal subgroup into a union of full
conjugacy-class rows. The finite arithmetic certificate below says that an
identity-containing union of those rows has divisor-cardinality only when its
size is `1` or `7920`.
-/

/-- Sum of the verified class sizes selected by a Boolean row selector. -/
def classSelectionSize (f : Fin 10 → Bool) : Nat :=
  ∑ i : Fin 10,
    if f i then classSizeList.get ⟨i.1, by
      rw [classSizeList_length]
      exact i.2⟩ else 0

/-- The class-table rows whose representatives lie in a subgroup. -/
noncomputable def subgroupClassSelection (N : Subgroup M11) (i : Fin 10) : Bool :=
  @ite Bool (representativeM11 i ∈ N) (Classical.propDecidable _) true false

/-- The selected conjugacy-class orbit attached to a subgroup and a row. -/
noncomputable def selectedClassSet (N : Subgroup M11) (i : Fin 10) : Set M11 :=
  @ite (Set M11) (representativeM11 i ∈ N) (Classical.propDecidable _) (classOrbit i) ∅

/-- The union of all conjugacy-class rows selected by a subgroup. -/
noncomputable def selectedClassUnion (N : Subgroup M11) : Set M11 :=
  ⋃ i : Fin 10, selectedClassSet N i

/-- Cardinality of one selected class row. -/
theorem selectedClassSet_ncard (N : Subgroup M11) (i : Fin 10) :
    (selectedClassSet N i).ncard =
      if subgroupClassSelection N i then classSizeList.get ⟨i.1, by
        rw [classSizeList_length]
        exact i.2⟩ else 0 := by
  classical
  by_cases hi : representativeM11 i ∈ N
  · simp [selectedClassSet, subgroupClassSelection, hi, classOrbit_ncard]
  · simp [selectedClassSet, subgroupClassSelection, hi]

/-- Cardinality of the union of the selected class rows. -/
theorem selectedClassUnion_ncard (N : Subgroup M11) :
    (selectedClassUnion N).ncard = classSelectionSize (subgroupClassSelection N) := by
  classical
  unfold selectedClassUnion classSelectionSize
  have hfin : ∀ i : Fin 10, (selectedClassSet N i).Finite := fun _ => Set.toFinite _
  have hdisj : Pairwise (Disjoint on selectedClassSet N) := by
    intro i j hij
    change Disjoint (selectedClassSet N i) (selectedClassSet N j)
    by_cases hi : representativeM11 i ∈ N
    · by_cases hj : representativeM11 j ∈ N
      · simpa [selectedClassSet, hi, hj] using classOrbit_pairwiseDisjoint hij
      · simp [selectedClassSet, hi, hj]
    · by_cases hj : representativeM11 j ∈ N
      · simp [selectedClassSet, hi, hj]
      · simp [selectedClassSet, hi, hj]
  rw [Set.ncard_iUnion_of_finite hfin hdisj]
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [selectedClassSet_ncard]

/-- A normal subgroup is exactly the union of the class rows selected by it. -/
theorem normal_subgroup_eq_selectedClassUnion (N : Subgroup M11) [N.Normal] :
    (N : Set M11) = selectedClassUnion N := by
  classical
  ext x
  constructor
  · intro hx
    have hxuniv : x ∈ ⋃ i : Fin 10, classOrbit i := by
      rw [classOrbit_iUnion_eq_univ]
      simp
    rcases Set.mem_iUnion.mp hxuniv with ⟨i, hxi⟩
    have hconj : IsConj x (representativeM11 i) := by
      simpa [classOrbit] using (ConjAct.mem_orbit_conjAct.mp hxi)
    have hrep : representativeM11 i ∈ N := by
      rcases isConj_iff.mp hconj with ⟨g, hg⟩
      rw [← hg]
      exact normal_subgroup_closed_under_conj N hx g
    exact Set.mem_iUnion.mpr ⟨i, by simp [selectedClassSet, hrep, hxi]⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    by_cases hrep : representativeM11 i ∈ N
    · have hxiOrbit : x ∈ classOrbit i := by
        simpa [selectedClassSet, hrep] using hxi
      exact conj_orbit_subset_of_normal N hrep hxiOrbit
    · simp [selectedClassSet, hrep] at hxi

/-- The carrier set of a subgroup has the same `ncard` as the subgroup type. -/
theorem subgroup_carrier_ncard (N : Subgroup M11) : (N : Set M11).ncard = Nat.card N := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card {x : M11 // x ∈ (N : Set M11)} = Nat.card N
  rfl

/-- A normal subgroup has the class-selection size of its selected rows. -/
theorem normal_subgroup_card_eq_classSelectionSize (N : Subgroup M11) [N.Normal] :
    Nat.card N = classSelectionSize (subgroupClassSelection N) := by
  rw [← subgroup_carrier_ncard N]
  rw [normal_subgroup_eq_selectedClassUnion N]
  exact selectedClassUnion_ncard N

set_option maxHeartbeats 2000000 in
-- The finite selector arithmetic enumerates all Boolean choices of ten class rows.
set_option maxRecDepth 20000 in
/--
Finite arithmetic certificate for selected class rows: if the identity row is
included and the selected size divides `7920`, then the selected size is either
`1` or `7920`.
-/
theorem classSelectionSize_dvd_target_iff : ∀ f : Fin 10 → Bool,
    f ⟨0, by decide⟩ = true →
      (classSelectionSize f ∣ 7920 ↔
        classSelectionSize f = 1 ∨ classSelectionSize f = 7920) := by
  decide

theorem classSelectionSize_eq_one_or_target_of_dvd (f : Fin 10 → Bool)
    (hf0 : f ⟨0, by decide⟩ = true)
    (hdvd : classSelectionSize f ∣ 7920) :
    classSelectionSize f = 1 ∨ classSelectionSize f = 7920 :=
  (classSelectionSize_dvd_target_iff f hf0).mp hdvd

/-- The identity class row is selected by every subgroup. -/
theorem subgroupClassSelection_zero (N : Subgroup M11) :
    subgroupClassSelection N (0 : Fin 10) = true := by
  have hmem : representativeM11 (0 : Fin 10) ∈ N := by
    change representativeM11 (⟨0, by decide⟩ : Fin 10) ∈ N
    rw [representativeM11_rep1AIndex_eq_one]
    exact N.one_mem
  simp [subgroupClassSelection, hmem]

/-- The order of a normal subgroup is either `1` or `7920`. -/
theorem normal_subgroup_card_eq_one_or_target (N : Subgroup M11) [N.Normal] :
    Nat.card N = 1 ∨ Nat.card N = 7920 := by
  have hcard := normal_subgroup_card_eq_classSelectionSize N
  have hdvd := subgroup_card_dvd_target N
  rw [hcard] at hdvd
  have hzero : subgroupClassSelection N ⟨0, by decide⟩ = true := by
    simpa using subgroupClassSelection_zero N
  have hsel := classSelectionSize_eq_one_or_target_of_dvd
    (subgroupClassSelection N) hzero hdvd
  rwa [← hcard] at hsel

/-- There is no proper nontrivial normal subgroup of `M11`. -/
theorem no_proper_nontrivial_normal_subgroup (N : Subgroup M11) [N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  rcases normal_subgroup_card_eq_one_or_target N with hcard | hcard
  · exact Or.inl (Subgroup.eq_bot_of_card_eq N hcard)
  · have hcardTop : Nat.card N = Nat.card M11 := by
      rw [M11Cardinality.card_M11]
      exact hcard
    exact Or.inr (Subgroup.eq_top_of_card_eq N hcardTop)

/-- The generated degree-11 Mathieu group candidate is nontrivial. -/
theorem nontrivial_M11 : Nontrivial M11 := by
  refine ⟨⟨m11aM11, 1, ?_⟩⟩
  intro h
  have hperm := congrArg (fun z : M11 => (z : Perm11)) h
  have hm11a_ne_one : m11a ≠ (1 : Perm11) := by
    decide
  exact hm11a_ne_one (by simpa [m11aM11] using hperm)

/-- The generated degree-11 Mathieu group candidate is simple. -/
theorem simple_M11 : IsSimpleGroup M11 := by
  haveI : Nontrivial M11 := nontrivial_M11
  apply IsSimpleGroup.mk
  intro N hN
  letI : N.Normal := hN
  exact no_proper_nontrivial_normal_subgroup N

end M11Simplicity

end Sporadic
