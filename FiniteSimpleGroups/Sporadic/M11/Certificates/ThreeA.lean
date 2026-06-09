/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Certificates.FourA

/-!
# 3A centralizer certificate

This file verifies the 3A row of the candidate conjugacy table. The proof uses
an explicit 18-element lower-bound certificate inside `M11` and an ambient
alternating-centralizer divisibility upper bound.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

/-- The class-table index of the 3A representative. -/
abbrev rep3AIndex : Fin 10 :=
  ⟨2, by decide⟩

/-- Eighteen words whose values are distinct elements of the 3A centralizer. -/
def rep3ACentralizerWordList : List Word :=
  [
    [],
    [Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv, Gen.bInv],
    [Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.a],
    [Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv],
    [Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a],
    [Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a],
    [Gen.b, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.b],
    [Gen.a, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b],
    [Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv],
    [Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.a, Gen.bInv, Gen.a],
    [Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.a],
    [Gen.b, Gen.a, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.b],
    [Gen.b, Gen.b, Gen.a, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a],
    [Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.b]
  ]

theorem rep3ACentralizerWordList_length : rep3ACentralizerWordList.length = 18 := by
  decide

/-- The finite set of the eighteen displayed 3A centralizer elements. -/
def rep3ACentralizerElementFinset : Finset M11 :=
  (rep3ACentralizerWordList.map Word.toM11).toFinset

set_option maxRecDepth 120000 in
/-- The displayed 3A centralizer elements are pairwise distinct. -/
theorem rep3ACentralizerElementFinset_card :
    rep3ACentralizerElementFinset.card = 18 := by
  decide

set_option maxRecDepth 120000 in
set_option linter.flexible false in
/-- Every displayed 3A centralizer element centralizes the 3A representative. -/
theorem rep3ACentralizerWordList_mem_centralizer :
    ∀ w ∈ rep3ACentralizerWordList,
      Word.toM11 w ∈ RepresentativeCentralizer rep3AIndex := by
  intro w hw
  simp [rep3ACentralizerWordList] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    decide

/-- The displayed 3A centralizer set is contained in the actual centralizer. -/
theorem rep3ACentralizerElementFinset_subset_centralizer
    {x : M11} (hx : x ∈ rep3ACentralizerElementFinset) :
    x ∈ RepresentativeCentralizer rep3AIndex := by
  rw [rep3ACentralizerElementFinset] at hx
  rw [List.mem_toFinset] at hx
  rw [List.mem_map] at hx
  rcases hx with ⟨w, hw, rfl⟩
  exact rep3ACentralizerWordList_mem_centralizer w hw

/-- Lower bound for the `M11` centralizer of the 3A representative. -/
theorem rep3A_centralizer_card_ge :
    18 ≤ Nat.card (RepresentativeCentralizer rep3AIndex) := by
  classical
  have hle :
      Fintype.card {x : M11 // x ∈ rep3ACentralizerElementFinset} ≤
        Fintype.card (RepresentativeCentralizer rep3AIndex) := by
    refine Fintype.card_le_of_injective
      (fun x : {x : M11 // x ∈ rep3ACentralizerElementFinset} =>
        (⟨x.1, rep3ACentralizerElementFinset_subset_centralizer x.2⟩ :
          RepresentativeCentralizer rep3AIndex)) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : RepresentativeCentralizer rep3AIndex => (z.1 : M11)) hxy
  rw [Fintype.card_coe, rep3ACentralizerElementFinset_card,
    ← Nat.card_eq_fintype_card] at hle
  exact hle

/-- An odd ambient centralizer element swapping the two fixed points of the 3A representative. -/
abbrev rep3AOddCentralizerWitness : Perm11 :=
  Equiv.swap (0 : Fin 11) (1 : Fin 11)

set_option maxRecDepth 100000 in
/-- The 3A odd witness centralizes the ambient 3A representative. -/
theorem rep3AOddCentralizerWitness_mem_ambient :
    rep3AOddCentralizerWitness ∈ RepresentativeAmbientCentralizer rep3AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

/-- The 3A centralizer witness is odd. -/
theorem rep3AOddCentralizerWitness_sign :
    Equiv.Perm.sign rep3AOddCentralizerWitness = -1 := by
  rw [rep3AOddCentralizerWitness, Equiv.Perm.sign_swap]
  decide

/-- The ambient alternating centralizer of the 3A representative has order `162`. -/
theorem rep3A_ambientAlternatingCentralizer_card :
    Nat.card (RepresentativeAmbientAlternatingCentralizer rep3AIndex) = 162 := by
  have hker_mul :
      Nat.card (representativeAmbientCentralizerSignHom rep3AIndex).ker * 2 = 324 := by
    have h :=
      (representativeAmbientCentralizerSignHom rep3AIndex).ker.card_mul_index
    rw [Subgroup.index_ker,
      representativeAmbientCentralizerSignHom_range_card_of_odd rep3AIndex
        ⟨rep3AOddCentralizerWitness, rep3AOddCentralizerWitness_mem_ambient⟩
        rep3AOddCentralizerWitness_sign] at h
    have hambient : Nat.card (RepresentativeAmbientCentralizer rep3AIndex) = 324 := by
      simpa [rep3AIndex, ambientCentralizerOrder, ambientCentralizerOrderList]
        using representativeAmbientCentralizer_card rep3AIndex
    rw [hambient] at h
    exact h
  have hker : Nat.card (representativeAmbientCentralizerSignHom rep3AIndex).ker = 162 := by
    omega
  have hmapcard :
      Nat.card ((representativeAmbientCentralizerSignHom rep3AIndex).ker.map
          (RepresentativeAmbientCentralizer rep3AIndex).subtype) =
        Nat.card (representativeAmbientCentralizerSignHom rep3AIndex).ker :=
    Subgroup.card_map_of_injective
      (RepresentativeAmbientCentralizer rep3AIndex).subtype_injective
  rw [← representativeAmbientCentralizerSignHom_ker_map_eq_inf, hmapcard, hker]

/-- The `M11` 3A centralizer order divides the ambient alternating centralizer order. -/
theorem rep3A_centralizer_card_dvd_ambient_alternating :
    Nat.card (RepresentativeCentralizer rep3AIndex) ∣ 162 := by
  have hmapcard :
      Nat.card ((RepresentativeCentralizer rep3AIndex).map M11Subgroup.subtype) =
        Nat.card (RepresentativeCentralizer rep3AIndex) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hdvd :=
    Subgroup.card_dvd_of_le
      (representativeCentralizer_map_le_ambient_alternating rep3AIndex)
  rw [hmapcard, rep3A_ambientAlternatingCentralizer_card] at hdvd
  exact hdvd

/-- The `M11` 3A centralizer order divides `18`. -/
theorem rep3A_centralizer_card_dvd_eighteen :
    Nat.card (RepresentativeCentralizer rep3AIndex) ∣ 18 := by
  have hdvdM11 : Nat.card (RepresentativeCentralizer rep3AIndex) ∣ 7920 := by
    have h := Subgroup.card_subgroup_dvd_card (RepresentativeCentralizer rep3AIndex)
    rwa [M11Cardinality.card_M11] at h
  have hdvdGcd :=
    Nat.dvd_gcd rep3A_centralizer_card_dvd_ambient_alternating hdvdM11
  simpa using hdvdGcd

/-- Upper bound for the `M11` centralizer of the 3A representative. -/
theorem rep3A_centralizer_card_le :
    Nat.card (RepresentativeCentralizer rep3AIndex) ≤ 18 := by
  exact Nat.le_of_dvd (by decide : 0 < 18) rep3A_centralizer_card_dvd_eighteen

/-- The `M11` centralizer of the 3A representative has order `18`. -/
theorem rep3A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep3AIndex) = 18 :=
  le_antisymm rep3A_centralizer_card_le rep3A_centralizer_card_ge

/-- If a conjugation centralizer has order 18, then the conjugacy orbit has size 440. -/
theorem conjOrbit_card_of_centralizer_card_eq_eighteen (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 18) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 440 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 18 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 440 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- The conjugacy orbit of the 3A representative has size `440`. -/
theorem rep3AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep3AIndex)) = 440 :=
  conjOrbit_card_of_centralizer_card_eq_eighteen
    (representativeM11 rep3AIndex) rep3A_centralizer_card

end ConjugacyClasses
end Certificates
end Sporadic
