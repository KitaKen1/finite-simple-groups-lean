/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Certificates.ThreeA

/-!
# 2A centralizer certificate

This file verifies the 2A row of the candidate conjugacy table. The upper bound
uses a compact structural argument: a 2A centralizer element is determined by
its induced permutation of the three fixed points and the image of one moved
point. The final-stabilizer Witt-design certificate then proves injectivity.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

/-- The class-table index of the 2A representative. -/
abbrev rep2AIndex : Fin 10 :=
  ⟨1, by decide⟩

/- Pointwise form of the centralizer equation for the 2A representative. -/
set_option maxRecDepth 100000 in
theorem rep2A_ambientCentralizer_apply_comm
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex)
    (x : Fin 11) :
    g (representativePerm rep2AIndex x) = representativePerm rep2AIndex (g x) := by
  have hcomm : g * representativePerm rep2AIndex = representativePerm rep2AIndex * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have happly := congrArg (fun h : Perm11 => h x) hcomm
  simpa using happly

/-- The three fixed points of the 2A representative. -/
def rep2AFixedPointFinset : Finset (Fin 11) :=
  {0, 1, 2}

/- The displayed fixed-point set is exactly the fixed set of the 2A representative. -/
set_option maxRecDepth 100000 in
theorem rep2A_fixedPoint_iff (x : Fin 11) :
    representativePerm rep2AIndex x = x ↔ x ∈ rep2AFixedPointFinset := by
  fin_cases x <;> decide

/- An ambient centralizer element maps the 2A fixed-point set to itself. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- The pointwise centralizer equation unfolds the concrete 2A representative.
theorem rep2A_ambientCentralizer_maps_fixedPointFinset
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex)
    {x : Fin 11} (hx : x ∈ rep2AFixedPointFinset) :
    g x ∈ rep2AFixedPointFinset := by
  rw [← rep2A_fixedPoint_iff] at hx ⊢
  calc
    representativePerm rep2AIndex (g x) = g (representativePerm rep2AIndex x) :=
      (rep2A_ambientCentralizer_apply_comm hg x).symm
    _ = g x := by rw [hx]

/- The 2A fixed-point coordinate uses the same six displayed fixed permutations as 4A. -/
abbrev rep2AFixedParam (g : Perm11) : Fin 6 :=
  rep4AFixedParam g

/- The recovered fixed-point parameter has the correct images on `0` and `1`. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep2AFixedParam_apply_zero_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex) :
    rep4AFixedPerm (rep2AFixedParam g) (0 : Fin 11) = g (0 : Fin 11) ∧
      rep4AFixedPerm (rep2AFixedParam g) (1 : Fin 11) = g (1 : Fin 11) := by
  have h0 : g (0 : Fin 11) ∈ rep2AFixedPointFinset :=
    rep2A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h1 : g (1 : Fin 11) ∈ rep2AFixedPointFinset :=
    rep2A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h01 : g (0 : Fin 11) ≠ g (1 : Fin 11) := by
    intro h
    exact (by decide : (0 : Fin 11) ≠ 1) (g.injective h)
  generalize h0g : g (0 : Fin 11) = y0
  generalize h1g : g (1 : Fin 11) = y1
  fin_cases y0 <;> fin_cases y1 <;>
    simp [rep2AFixedParam, rep4AFixedParam, rep4AFixedPerm, rep4AFixedPermList,
      rep2AFixedPointFinset, h0g, h1g] at h0 h1 h01 ⊢ <;> decide

/- The recovered fixed-point parameter has the correct image on `2`. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep2AFixedParam_apply_two
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex) :
    rep4AFixedPerm (rep2AFixedParam g) (2 : Fin 11) = g (2 : Fin 11) := by
  have h01 := rep2AFixedParam_apply_zero_one hg
  have h2 : g (2 : Fin 11) ∈ rep2AFixedPointFinset :=
    rep2A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h20 : g (2 : Fin 11) ≠ g (0 : Fin 11) := by
    intro h
    exact (by decide : (2 : Fin 11) ≠ 0) (g.injective h)
  have h21 : g (2 : Fin 11) ≠ g (1 : Fin 11) := by
    intro h
    exact (by decide : (2 : Fin 11) ≠ 1) (g.injective h)
  generalize hr : rep2AFixedParam g = r
  fin_cases r
  all_goals
    simp [rep2AFixedParam, rep4AFixedPerm, rep4AFixedPermList, hr] at h01 ⊢
    rcases h01 with ⟨h0, h1⟩
    rw [← h0] at h20
    rw [← h1] at h21
    generalize h2g : g (2 : Fin 11) = y2
    fin_cases y2
    all_goals
      simp [rep2AFixedPointFinset, h2g] at h2 h20 h21 ⊢
      try contradiction
      try simp
      try decide

/- The recovered fixed-point parameter agrees with `g` on the whole fixed-point set. -/
theorem rep2AFixedParam_apply_of_mem_fixedPoint
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex)
    {x : Fin 11} (hx : x ∈ rep2AFixedPointFinset) :
    rep4AFixedPerm (rep2AFixedParam g) x = g x := by
  rcases rep2AFixedParam_apply_zero_one hg with ⟨h0, h1⟩
  fin_cases x
  · exact h0
  · exact h1
  · exact rep2AFixedParam_apply_two hg
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide

/-- The moved points of the 2A representative. -/
def rep2AMovedPointFinset : Finset (Fin 11) :=
  {3, 4, 5, 6, 7, 8, 9, 10}

/- The moved-point set is exactly the complement of the fixed set for the 2A representative. -/
set_option maxRecDepth 100000 in
theorem rep2A_movedPoint_iff (x : Fin 11) :
    representativePerm rep2AIndex x ≠ x ↔ x ∈ rep2AMovedPointFinset := by
  fin_cases x <;> decide

/- An ambient centralizer element maps moved points to moved points. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- The complement-of-fixed-points calculation unfolds the same concrete 2A representative.
theorem rep2A_ambientCentralizer_maps_movedPointFinset
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep2AIndex)
    {x : Fin 11} (hx : x ∈ rep2AMovedPointFinset) :
    g x ∈ rep2AMovedPointFinset := by
  rw [← rep2A_movedPoint_iff] at hx ⊢
  intro hfix
  have hgpx : g (representativePerm rep2AIndex x) = g x := by
    calc
      g (representativePerm rep2AIndex x) = representativePerm rep2AIndex (g x) :=
        rep2A_ambientCentralizer_apply_comm hg x
      _ = g x := hfix
  exact hx (g.injective hgpx)

/- Coordinate decoder for the eight moved points. -/
def rep2AMovedCoord (x : Fin 11) : Fin 8 :=
  if x = 3 then 0
  else if x = 4 then 1
  else if x = 5 then 2
  else if x = 6 then 3
  else if x = 7 then 4
  else if x = 8 then 5
  else if x = 9 then 6
  else 7

/- The moved-point coordinate is injective on the displayed moved-point set. -/
set_option maxRecDepth 100000 in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem rep2AMovedCoord_eq_of_mem
    {x y : Fin 11} (hx : x ∈ rep2AMovedPointFinset) (hy : y ∈ rep2AMovedPointFinset)
    (hxy : rep2AMovedCoord x = rep2AMovedCoord y) :
    x = y := by
  fin_cases x <;> fin_cases y <;>
    simp [rep2AMovedPointFinset, rep2AMovedCoord] at hx hy hxy ⊢ <;>
    try contradiction <;> try decide

/- Coerce a centralizer element to the ambient centralizer. -/
theorem rep2A_centralizer_to_ambient
    (g : RepresentativeCentralizer rep2AIndex) :
    g.1.1 ∈ RepresentativeAmbientCentralizer rep2AIndex := by
  have hmap :
      g.1.1 ∈ (RepresentativeCentralizer rep2AIndex).map M11Subgroup.subtype :=
    ⟨g.1, g.2, rfl⟩
  exact representativeCentralizer_map_le_ambient rep2AIndex hmap

/- A 2A centralizer element is determined by its fixed-point coordinate and the image of `3`. -/
theorem rep2ACentralizer_param_injective :
    Function.Injective
      (fun g : RepresentativeCentralizer rep2AIndex =>
        (rep2AFixedParam g.1.1, rep2AMovedCoord (g.1.1 (3 : Fin 11)))) := by
  intro g h hgh
  have hgAmbient := rep2A_centralizer_to_ambient g
  have hhAmbient := rep2A_centralizer_to_ambient h
  have hparam :
      rep2AFixedParam g.1.1 = rep2AFixedParam h.1.1 :=
    congrArg Prod.fst hgh
  have hcoord :
      rep2AMovedCoord (g.1.1 (3 : Fin 11)) =
        rep2AMovedCoord (h.1.1 (3 : Fin 11)) :=
    congrArg Prod.snd hgh
  have h0 : g.1.1 (0 : Fin 11) = h.1.1 (0 : Fin 11) := by
    have hg0 := rep2AFixedParam_apply_of_mem_fixedPoint hgAmbient (by decide :
      (0 : Fin 11) ∈ rep2AFixedPointFinset)
    have hh0 := rep2AFixedParam_apply_of_mem_fixedPoint hhAmbient (by decide :
      (0 : Fin 11) ∈ rep2AFixedPointFinset)
    rw [← hg0, ← hh0, hparam]
  have h1 : g.1.1 (1 : Fin 11) = h.1.1 (1 : Fin 11) := by
    have hg1 := rep2AFixedParam_apply_of_mem_fixedPoint hgAmbient (by decide :
      (1 : Fin 11) ∈ rep2AFixedPointFinset)
    have hh1 := rep2AFixedParam_apply_of_mem_fixedPoint hhAmbient (by decide :
      (1 : Fin 11) ∈ rep2AFixedPointFinset)
    rw [← hg1, ← hh1, hparam]
  have h2 : g.1.1 (2 : Fin 11) = h.1.1 (2 : Fin 11) := by
    have hg2 := rep2AFixedParam_apply_of_mem_fixedPoint hgAmbient (by decide :
      (2 : Fin 11) ∈ rep2AFixedPointFinset)
    have hh2 := rep2AFixedParam_apply_of_mem_fixedPoint hhAmbient (by decide :
      (2 : Fin 11) ∈ rep2AFixedPointFinset)
    rw [← hg2, ← hh2, hparam]
  have hg3mem : g.1.1 (3 : Fin 11) ∈ rep2AMovedPointFinset :=
    rep2A_ambientCentralizer_maps_movedPointFinset hgAmbient (by decide)
  have hh3mem : h.1.1 (3 : Fin 11) ∈ rep2AMovedPointFinset :=
    rep2A_ambientCentralizer_maps_movedPointFinset hhAmbient (by decide)
  have h3 : g.1.1 (3 : Fin 11) = h.1.1 (3 : Fin 11) :=
    rep2AMovedCoord_eq_of_mem hg3mem hh3mem hcoord
  let q : M11 := h.1⁻¹ * g.1
  have hqPres : WittDesign.PreservesWittBlocks q.1 :=
    WittDesign.M11_preserves_wittBlocks q
  have hq0 : q.1 (0 : Fin 11) = 0 := by
    change (h.1.1)⁻¹ (g.1.1 (0 : Fin 11)) = 0
    rw [h0]
    simp
  have hq1 : q.1 (1 : Fin 11) = 1 := by
    change (h.1.1)⁻¹ (g.1.1 (1 : Fin 11)) = 1
    rw [h1]
    simp
  have hq2 : q.1 (2 : Fin 11) = 2 := by
    change (h.1.1)⁻¹ (g.1.1 (2 : Fin 11)) = 2
    rw [h2]
    simp
  have hq3 : q.1 (3 : Fin 11) = 3 := by
    change (h.1.1)⁻¹ (g.1.1 (3 : Fin 11)) = 3
    rw [h3]
    simp
  have hqOnePerm : q.1 = 1 :=
    WittDesign.fixed_four_preserves_wittBlocks_eq_one q.1 hqPres hq0 hq1 hq2 hq3
  have hqOne : q = 1 := by
    apply Subtype.ext
    exact hqOnePerm
  have hM11 : g.1 = h.1 := by
    have hm := congrArg (fun z : M11 => h.1 * z) hqOne
    simpa [q, mul_assoc] using hm
  apply Subtype.ext
  exact hM11

/-- Upper bound for the `M11` centralizer of the 2A representative. -/
theorem rep2A_centralizer_card_le :
    Nat.card (RepresentativeCentralizer rep2AIndex) ≤ 48 := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (RepresentativeCentralizer rep2AIndex)
        ≤ Fintype.card (Fin 6 × Fin 8) := by
          exact Fintype.card_le_of_injective
            (fun g : RepresentativeCentralizer rep2AIndex =>
              (rep2AFixedParam g.1.1, rep2AMovedCoord (g.1.1 (3 : Fin 11))))
            rep2ACentralizer_param_injective
    _ = 48 := by decide

/-- Forty-eight words whose values are distinct elements of the 2A centralizer. -/
def rep2ACentralizerWordList : List Word :=
  [
    [],
    [Gen.aInv, Gen.b, Gen.b],
    [Gen.b, Gen.b, Gen.a],
    [Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv],
    [Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.b, Gen.a],
    [Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv],
    [Gen.a, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv],
    [Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b],
    [Gen.a, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.aInv],
    [Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.a, Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.aInv],
    [Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv],
    [Gen.a, Gen.a, Gen.a, Gen.a, Gen.b, Gen.a, Gen.a, Gen.b, Gen.aInv],
    [Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.b],
    [Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a],
    [Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv],
    [Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.aInv, Gen.aInv],
    [Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv],
    [Gen.b, Gen.a, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.bInv, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.a],
    [Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv],
    [Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.aInv, Gen.aInv],
    [Gen.b, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv],
    [Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b],
    [Gen.bInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv],
    [Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.a, Gen.b],
    [Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.b],
    [Gen.a, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.a],
    [Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.bInv, Gen.a],
    [Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a],
    [Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv],
    [Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.b, Gen.a, Gen.a, Gen.a],
    [Gen.aInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.a],
    [Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv],
    [Gen.b, Gen.a, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a],
    [Gen.b, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a],
    [Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.b, Gen.a, Gen.a, Gen.b],
    [Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.a],
    [Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.a],
    [Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b],
    [Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.a]
  ]

theorem rep2ACentralizerWordList_length : rep2ACentralizerWordList.length = 48 := by
  decide

/-- The finite set of the forty-eight displayed 2A centralizer elements. -/
def rep2ACentralizerElementFinset : Finset M11 :=
  (rep2ACentralizerWordList.map Word.toM11).toFinset

set_option maxRecDepth 220000 in
set_option maxHeartbeats 2000000 in
-- This compares the 48 displayed permutations by finite computation.
/-- The displayed 2A centralizer elements are pairwise distinct. -/
theorem rep2ACentralizerElementFinset_card :
    rep2ACentralizerElementFinset.card = 48 := by
  decide

set_option maxRecDepth 220000 in
set_option linter.flexible false in
set_option maxHeartbeats 2000000 in
-- This checks all 48 displayed words against the concrete centralizer equation.
/-- Every displayed 2A centralizer element centralizes the 2A representative. -/
theorem rep2ACentralizerWordList_mem_centralizer :
    ∀ w ∈ rep2ACentralizerWordList,
      Word.toM11 w ∈ RepresentativeCentralizer rep2AIndex := by
  intro w hw
  simp [rep2ACentralizerWordList] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    decide

/-- The displayed 2A centralizer set is contained in the actual centralizer. -/
theorem rep2ACentralizerElementFinset_subset_centralizer
    {x : M11} (hx : x ∈ rep2ACentralizerElementFinset) :
    x ∈ RepresentativeCentralizer rep2AIndex := by
  rw [rep2ACentralizerElementFinset] at hx
  rw [List.mem_toFinset] at hx
  rw [List.mem_map] at hx
  rcases hx with ⟨w, hw, rfl⟩
  exact rep2ACentralizerWordList_mem_centralizer w hw

/-- Lower bound for the `M11` centralizer of the 2A representative. -/
theorem rep2A_centralizer_card_ge :
    48 ≤ Nat.card (RepresentativeCentralizer rep2AIndex) := by
  classical
  have hle :
      Fintype.card {x : M11 // x ∈ rep2ACentralizerElementFinset} ≤
        Fintype.card (RepresentativeCentralizer rep2AIndex) := by
    refine Fintype.card_le_of_injective
      (fun x : {x : M11 // x ∈ rep2ACentralizerElementFinset} =>
        (⟨x.1, rep2ACentralizerElementFinset_subset_centralizer x.2⟩ :
          RepresentativeCentralizer rep2AIndex)) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : RepresentativeCentralizer rep2AIndex => (z.1 : M11)) hxy
  rw [Fintype.card_coe, rep2ACentralizerElementFinset_card,
    ← Nat.card_eq_fintype_card] at hle
  exact hle

/-- The `M11` centralizer of the 2A representative has order `48`. -/
theorem rep2A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep2AIndex) = 48 :=
  le_antisymm rep2A_centralizer_card_le rep2A_centralizer_card_ge

/-- If a conjugation centralizer has order 48, then the conjugacy orbit has size 165. -/
theorem conjOrbit_card_of_centralizer_card_eq_fortyEight (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 48) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 165 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 48 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 165 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- The conjugacy orbit of the 2A representative has size `165`. -/
theorem rep2AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep2AIndex)) = 165 :=
  conjOrbit_card_of_centralizer_card_eq_fortyEight
    (representativeM11 rep2AIndex) rep2A_centralizer_card

end ConjugacyClasses
end Certificates
end Sporadic
