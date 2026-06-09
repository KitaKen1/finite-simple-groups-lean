/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Certificates.ConjugacyClasses

/-!
# 4A certificate refinements

This file keeps the next 4A upper-bound work away from the already-large
`ConjugacyClasses.lean` file. It imports the common conjugacy-class certificate
data and adds small, focused lemmas for the 4A row.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

set_option maxRecDepth 100000

/-- The 4A representative fixes `0`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_zero :
    representativePerm rep4AIndex (0 : Fin 11) = 0 := by
  decide

/-- The 4A representative fixes `1`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_one :
    representativePerm rep4AIndex (1 : Fin 11) = 1 := by
  decide

/-- The 4A representative fixes `2`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_two :
    representativePerm rep4AIndex (2 : Fin 11) = 2 := by
  decide

/-- The first displayed 4A cycle sends `3` to `4`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_three :
    representativePerm rep4AIndex (3 : Fin 11) = 4 := by
  decide

/-- The first displayed 4A cycle sends `4` to `9`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_four :
    representativePerm rep4AIndex (4 : Fin 11) = 9 := by
  decide

/-- The second displayed 4A cycle sends `5` to `8`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_five :
    representativePerm rep4AIndex (5 : Fin 11) = 8 := by
  decide

/-- The second displayed 4A cycle sends `6` to `10`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_six :
    representativePerm rep4AIndex (6 : Fin 11) = 10 := by
  decide

/-- The first displayed 4A cycle sends `7` to `3`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_seven :
    representativePerm rep4AIndex (7 : Fin 11) = 3 := by
  decide

/-- The second displayed 4A cycle sends `8` to `6`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_eight :
    representativePerm rep4AIndex (8 : Fin 11) = 6 := by
  decide

/-- The first displayed 4A cycle sends `9` to `7`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_nine :
    representativePerm rep4AIndex (9 : Fin 11) = 7 := by
  decide

/-- The second displayed 4A cycle sends `10` to `5`. -/
@[simp] theorem representativePerm_rep4AIndex_apply_ten :
    representativePerm rep4AIndex (10 : Fin 11) = 5 := by
  decide

/- Pointwise form of the centralizer equation for the 4A representative. -/
set_option maxRecDepth 100000 in
theorem rep4A_ambientCentralizer_apply_comm
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (x : Fin 11) :
    g (representativePerm rep4AIndex x) = representativePerm rep4AIndex (g x) := by
  have hcomm : g * representativePerm rep4AIndex = representativePerm rep4AIndex * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have happly := congrArg (fun h : Perm11 => h x) hcomm
  change g (representativePerm rep4AIndex x) = representativePerm rep4AIndex (g x)
  simpa using happly

/-- The three fixed points of the 4A representative. -/
def rep4AFixedPointFinset : Finset (Fin 11) :=
  {0, 1, 2}

/- The displayed fixed-point set is exactly the fixed set of the 4A representative. -/
set_option maxRecDepth 100000 in
theorem rep4A_fixedPoint_iff (x : Fin 11) :
    representativePerm rep4AIndex x = x ↔ x ∈ rep4AFixedPointFinset := by
  fin_cases x <;> decide

/-
An ambient permutation centralizing the 4A representative maps the 4A fixed
point set to itself.
-/
set_option maxRecDepth 100000 in
theorem rep4A_ambientCentralizer_maps_fixedPointFinset
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    {x : Fin 11} (hx : x ∈ rep4AFixedPointFinset) :
    g x ∈ rep4AFixedPointFinset := by
  rw [← rep4A_fixedPoint_iff] at hx ⊢
  have hcomm : g * representativePerm rep4AIndex = representativePerm rep4AIndex * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have happly := congrArg (fun h : Perm11 => h x) hcomm
  simpa [hx] using happly.symm

/- An ambient centralizer element sends the displayed fixed-point set onto itself. -/
theorem rep4AFixedPointFinset_image_eq_self
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4AFixedPointFinset.image g = rep4AFixedPointFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    intro x hx
    exact rep4A_ambientCentralizer_maps_fixedPointFinset hg hx
  · rw [Finset.card_image_of_injective _ g.injective]

/- The recovered fixed-point permutation parameter, determined by the images of `0` and `1`. -/
def rep4AFixedParam (g : Perm11) : Fin 6 :=
  if g (0 : Fin 11) = 0 then
    if g (1 : Fin 11) = 1 then 0 else 3
  else if g (0 : Fin 11) = 1 then
    if g (1 : Fin 11) = 0 then 1 else 4
  else
    if g (1 : Fin 11) = 1 then 2 else 5

/- The recovered fixed-point parameter has the correct images on `0` and `1`. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep4AFixedParam_apply_zero_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4AFixedPerm (rep4AFixedParam g) (0 : Fin 11) = g (0 : Fin 11) ∧
      rep4AFixedPerm (rep4AFixedParam g) (1 : Fin 11) = g (1 : Fin 11) := by
  have h0 : g (0 : Fin 11) ∈ rep4AFixedPointFinset :=
    rep4A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h1 : g (1 : Fin 11) ∈ rep4AFixedPointFinset :=
    rep4A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h01 : g (0 : Fin 11) ≠ g (1 : Fin 11) := by
    intro h
    exact (by decide : (0 : Fin 11) ≠ 1) (g.injective h)
  generalize h0g : g (0 : Fin 11) = y0
  generalize h1g : g (1 : Fin 11) = y1
  fin_cases y0 <;> fin_cases y1 <;>
    simp [rep4AFixedParam, rep4AFixedPerm, rep4AFixedPermList, rep4AFixedPointFinset,
      h0g, h1g] at h0 h1 h01 ⊢ <;> decide

/- The recovered fixed-point parameter also has the correct image on `2`. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep4AFixedParam_apply_two
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4AFixedPerm (rep4AFixedParam g) (2 : Fin 11) = g (2 : Fin 11) := by
  have h01 := rep4AFixedParam_apply_zero_one hg
  have h2 : g (2 : Fin 11) ∈ rep4AFixedPointFinset :=
    rep4A_ambientCentralizer_maps_fixedPointFinset hg (by decide)
  have h20 : g (2 : Fin 11) ≠ g (0 : Fin 11) := by
    intro h
    exact (by decide : (2 : Fin 11) ≠ 0) (g.injective h)
  have h21 : g (2 : Fin 11) ≠ g (1 : Fin 11) := by
    intro h
    exact (by decide : (2 : Fin 11) ≠ 1) (g.injective h)
  generalize hr : rep4AFixedParam g = r
  fin_cases r
  all_goals
    simp [rep4AFixedPerm, rep4AFixedPermList, hr] at h01 ⊢
    rcases h01 with ⟨h0, h1⟩
    rw [← h0] at h20
    rw [← h1] at h21
    generalize h2g : g (2 : Fin 11) = y2
    fin_cases y2
    all_goals
      simp [rep4AFixedPointFinset, h2g] at h2 h20 h21 ⊢
      try contradiction
      try simp
      try decide

/- The recovered fixed-point parameter agrees with `g` on the whole fixed-point set. -/
theorem rep4AFixedParam_apply_of_mem_fixedPoint
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    {x : Fin 11} (hx : x ∈ rep4AFixedPointFinset) :
    rep4AFixedPerm (rep4AFixedParam g) x = g x := by
  rcases rep4AFixedParam_apply_zero_one hg with ⟨h0, h1⟩
  fin_cases x
  · exact h0
  · exact h1
  · exact rep4AFixedParam_apply_two hg
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide

/-- The support of the first 4-cycle in the 4A representative. -/
def rep4ACycleAFinset : Finset (Fin 11) :=
  {3, 4, 9, 7}

/-- The support of the second 4-cycle in the 4A representative. -/
def rep4ACycleBFinset : Finset (Fin 11) :=
  {5, 8, 6, 10}

/- Coordinate decoder for the first displayed 4-cycle support. -/
def rep4ACycleACoord (x : Fin 11) : Fin 4 :=
  if x = 3 then 0 else if x = 4 then 1 else if x = 9 then 2 else 3

/- Coordinate decoder for the second displayed 4-cycle support. -/
def rep4ACycleBCoord (x : Fin 11) : Fin 4 :=
  if x = 5 then 0 else if x = 8 then 1 else if x = 6 then 2 else 3

/- The first 4-cycle decoder sends a support point back to the matching power. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep4ACycleACoord_apply_three_of_mem
    {x : Fin 11} (hx : x ∈ rep4ACycleAFinset) :
    (rep4ACycleA ^ (rep4ACycleACoord x).1) (3 : Fin 11) = x := by
  fin_cases x <;> simp [rep4ACycleAFinset, rep4ACycleACoord] at hx ⊢ <;> decide

/- The second 4-cycle decoder sends a support point back to the matching power. -/
set_option maxRecDepth 100000 in
set_option linter.flexible false in
theorem rep4ACycleBCoord_apply_five_of_mem
    {x : Fin 11} (hx : x ∈ rep4ACycleBFinset) :
    (rep4ACycleB ^ (rep4ACycleBCoord x).1) (5 : Fin 11) = x := by
  fin_cases x <;> simp [rep4ACycleBFinset, rep4ACycleBCoord] at hx ⊢ <;> decide

/-- The moved points of the 4A representative. -/
def rep4AMovedPointFinset : Finset (Fin 11) :=
  rep4ACycleAFinset ∪ rep4ACycleBFinset

/- The first 4-cycle support is invariant under the 4A representative. -/
set_option maxRecDepth 100000 in
theorem rep4A_perm_maps_cycleAFinset
    (x : Fin 11) :
    x ∈ rep4ACycleAFinset →
      representativePerm rep4AIndex x ∈ rep4ACycleAFinset := by
  fin_cases x <;> decide

/- The second 4-cycle support is invariant under the 4A representative. -/
set_option maxRecDepth 100000 in
theorem rep4A_perm_maps_cycleBFinset
    (x : Fin 11) :
    x ∈ rep4ACycleBFinset →
      representativePerm rep4AIndex x ∈ rep4ACycleBFinset := by
  fin_cases x <;> decide

/- The 4A representative preserves membership in the first 4-cycle support. -/
set_option maxRecDepth 100000 in
theorem rep4A_perm_mem_cycleAFinset_iff (x : Fin 11) :
    representativePerm rep4AIndex x ∈ rep4ACycleAFinset ↔
      x ∈ rep4ACycleAFinset := by
  fin_cases x <;> decide

/- The 4A representative preserves membership in the second 4-cycle support. -/
set_option maxRecDepth 100000 in
theorem rep4A_perm_mem_cycleBFinset_iff (x : Fin 11) :
    representativePerm rep4AIndex x ∈ rep4ACycleBFinset ↔
      x ∈ rep4ACycleBFinset := by
  fin_cases x <;> decide

/- The image of the second point of the first support has the same support side as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_four_mem_cycleAFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (4 : Fin 11) ∈ rep4ACycleAFinset ↔ g (3 : Fin 11) ∈ rep4ACycleAFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  rw [h4, rep4A_perm_mem_cycleAFinset_iff]

/- The image of the third point of the first support has the same support side as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_nine_mem_cycleAFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (9 : Fin 11) ∈ rep4ACycleAFinset ↔ g (3 : Fin 11) ∈ rep4ACycleAFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  have h9 : g (9 : Fin 11) = representativePerm rep4AIndex (g (4 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (4 : Fin 11)
  rw [h9, rep4A_perm_mem_cycleAFinset_iff, h4, rep4A_perm_mem_cycleAFinset_iff]

/- The image of the fourth point of the first support has the same support side as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_seven_mem_cycleAFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (7 : Fin 11) ∈ rep4ACycleAFinset ↔ g (3 : Fin 11) ∈ rep4ACycleAFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  have h9 : g (9 : Fin 11) = representativePerm rep4AIndex (g (4 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (4 : Fin 11)
  have h7 : g (7 : Fin 11) = representativePerm rep4AIndex (g (9 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (9 : Fin 11)
  rw [h7, rep4A_perm_mem_cycleAFinset_iff, h9, rep4A_perm_mem_cycleAFinset_iff,
    h4, rep4A_perm_mem_cycleAFinset_iff]

/- The image of the second point of the first support has the same B-side status as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_four_mem_cycleBFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (4 : Fin 11) ∈ rep4ACycleBFinset ↔ g (3 : Fin 11) ∈ rep4ACycleBFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  rw [h4, rep4A_perm_mem_cycleBFinset_iff]

/- The image of the third point of the first support has the same B-side status as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_nine_mem_cycleBFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (9 : Fin 11) ∈ rep4ACycleBFinset ↔ g (3 : Fin 11) ∈ rep4ACycleBFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  have h9 : g (9 : Fin 11) = representativePerm rep4AIndex (g (4 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (4 : Fin 11)
  rw [h9, rep4A_perm_mem_cycleBFinset_iff, h4, rep4A_perm_mem_cycleBFinset_iff]

/- The image of the fourth point of the first support has the same B-side status as the first. -/
set_option maxRecDepth 100000 in
theorem rep4A_cycleA_image_seven_mem_cycleBFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g (7 : Fin 11) ∈ rep4ACycleBFinset ↔ g (3 : Fin 11) ∈ rep4ACycleBFinset := by
  have h4 : g (4 : Fin 11) = representativePerm rep4AIndex (g (3 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)
  have h9 : g (9 : Fin 11) = representativePerm rep4AIndex (g (4 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (4 : Fin 11)
  have h7 : g (7 : Fin 11) = representativePerm rep4AIndex (g (9 : Fin 11)) := by
    simpa using rep4A_ambientCentralizer_apply_comm hg (9 : Fin 11)
  rw [h7, rep4A_perm_mem_cycleBFinset_iff, h9, rep4A_perm_mem_cycleBFinset_iff,
    h4, rep4A_perm_mem_cycleBFinset_iff]

/- Membership in the A-side is constant on the image of the first 4-cycle support. -/
theorem rep4A_cycleA_image_mem_cycleAFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (x : Fin 11) :
    x ∈ rep4ACycleAFinset →
      (g x ∈ rep4ACycleAFinset ↔ g (3 : Fin 11) ∈ rep4ACycleAFinset) := by
  intro hx
  fin_cases x
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exact Iff.rfl
  · exact rep4A_cycleA_image_four_mem_cycleAFinset_iff_base hg
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exact rep4A_cycleA_image_seven_mem_cycleAFinset_iff_base hg
  · exfalso; revert hx; decide
  · exact rep4A_cycleA_image_nine_mem_cycleAFinset_iff_base hg
  · exfalso; revert hx; decide

/- Membership in the B-side is constant on the image of the first 4-cycle support. -/
theorem rep4A_cycleA_image_mem_cycleBFinset_iff_base
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (x : Fin 11) :
    x ∈ rep4ACycleAFinset →
      (g x ∈ rep4ACycleBFinset ↔ g (3 : Fin 11) ∈ rep4ACycleBFinset) := by
  intro hx
  fin_cases x
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exact Iff.rfl
  · exact rep4A_cycleA_image_four_mem_cycleBFinset_iff_base hg
  · exfalso; revert hx; decide
  · exfalso; revert hx; decide
  · exact rep4A_cycleA_image_seven_mem_cycleBFinset_iff_base hg
  · exfalso; revert hx; decide
  · exact rep4A_cycleA_image_nine_mem_cycleBFinset_iff_base hg
  · exfalso; revert hx; decide

/- The moved-point set is exactly the complement of the fixed set for the 4A representative. -/
set_option maxRecDepth 100000 in
theorem rep4A_movedPoint_iff (x : Fin 11) :
    representativePerm rep4AIndex x ≠ x ↔ x ∈ rep4AMovedPointFinset := by
  fin_cases x <;> decide

/-
An ambient permutation centralizing the 4A representative maps moved points to
moved points.
-/
set_option maxRecDepth 100000 in
theorem rep4A_ambientCentralizer_maps_movedPointFinset
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    {x : Fin 11} (hx : x ∈ rep4AMovedPointFinset) :
    g x ∈ rep4AMovedPointFinset := by
  rw [← rep4A_movedPoint_iff] at hx ⊢
  intro hfix
  have hcomm : g * representativePerm rep4AIndex = representativePerm rep4AIndex * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have happly := congrArg (fun h : Perm11 => h x) hcomm
  have hgpx : g (representativePerm rep4AIndex x) = g x := by
    simpa [hfix] using happly
  exact hx (g.injective hgpx)

/- An ambient centralizer element sends the displayed moved-point set onto itself. -/
theorem rep4AMovedPointFinset_image_eq_self
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4AMovedPointFinset.image g = rep4AMovedPointFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    intro x hx
    exact rep4A_ambientCentralizer_maps_movedPointFinset hg hx
  · rw [Finset.card_image_of_injective _ g.injective]

/- A moved point is in one of the two displayed 4-cycle supports. -/
theorem rep4A_movedPoint_mem_cycleA_or_cycleB
    {x : Fin 11} (hx : x ∈ rep4AMovedPointFinset) :
    x ∈ rep4ACycleAFinset ∨ x ∈ rep4ACycleBFinset := by
  simpa [rep4AMovedPointFinset] using hx

/-
An ambient centralizer element sends the first 4-cycle support uniformly to one
of the two displayed 4-cycle supports.
-/
theorem rep4A_ambientCentralizer_maps_cycleAFinset_to_A_or_B
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    (∀ x : Fin 11, x ∈ rep4ACycleAFinset → g x ∈ rep4ACycleAFinset) ∨
      (∀ x : Fin 11, x ∈ rep4ACycleAFinset → g x ∈ rep4ACycleBFinset) := by
  have h3moved : g (3 : Fin 11) ∈ rep4AMovedPointFinset :=
    rep4A_ambientCentralizer_maps_movedPointFinset hg (by decide)
  rcases rep4A_movedPoint_mem_cycleA_or_cycleB h3moved with h3A | h3B
  · left
    intro x hx
    exact (rep4A_cycleA_image_mem_cycleAFinset_iff_base hg x hx).mpr h3A
  · right
    intro x hx
    exact (rep4A_cycleA_image_mem_cycleBFinset_iff_base hg x hx).mpr h3B

/- If the first support maps into the A-side, its image is exactly the A-support. -/
theorem rep4ACycleAFinset_image_eq_A_of_maps_to_A
    {g : Perm11}
    (hA : ∀ x : Fin 11, x ∈ rep4ACycleAFinset → g x ∈ rep4ACycleAFinset) :
    rep4ACycleAFinset.image g = rep4ACycleAFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    exact hA
  · rw [Finset.card_image_of_injective _ g.injective]

/- If the first support maps into the B-side, its image is exactly the B-support. -/
theorem rep4ACycleAFinset_image_eq_B_of_maps_to_B
    {g : Perm11}
    (hB : ∀ x : Fin 11, x ∈ rep4ACycleAFinset → g x ∈ rep4ACycleBFinset) :
    rep4ACycleAFinset.image g = rep4ACycleBFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    exact hB
  · rw [Finset.card_image_of_injective _ g.injective]
    decide

/- The image of the first 4-cycle support is exactly one of the two displayed supports. -/
theorem rep4A_ambientCentralizer_image_cycleAFinset_eq_A_or_B
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ACycleAFinset.image g = rep4ACycleAFinset ∨
      rep4ACycleAFinset.image g = rep4ACycleBFinset := by
  rcases rep4A_ambientCentralizer_maps_cycleAFinset_to_A_or_B hg with hA | hB
  · exact Or.inl (rep4ACycleAFinset_image_eq_A_of_maps_to_A hA)
  · exact Or.inr (rep4ACycleAFinset_image_eq_B_of_maps_to_B hB)

/- A point of the B-support is not in the A-support. -/
set_option maxRecDepth 100000 in
theorem rep4ACycleBFinset_not_mem_cycleAFinset
    (x : Fin 11) :
    x ∈ rep4ACycleBFinset → x ∉ rep4ACycleAFinset := by
  fin_cases x <;> decide

/- A point of the A-support is not in the B-support. -/
set_option maxRecDepth 100000 in
theorem rep4ACycleAFinset_not_mem_cycleBFinset
    (x : Fin 11) :
    x ∈ rep4ACycleAFinset → x ∉ rep4ACycleBFinset := by
  fin_cases x <;> decide

/-
If an ambient centralizer element sends the first support to itself, then it
sends the second support to itself.
-/
theorem rep4ACycleBFinset_image_eq_B_of_cycleAFinset_image_eq_A
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hA : rep4ACycleAFinset.image g = rep4ACycleAFinset) :
    rep4ACycleBFinset.image g = rep4ACycleBFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    intro x hxB
    have hxMoved : x ∈ rep4AMovedPointFinset := by
      simp [rep4AMovedPointFinset, hxB]
    have hgxMoved := rep4A_ambientCentralizer_maps_movedPointFinset hg hxMoved
    rcases rep4A_movedPoint_mem_cycleA_or_cycleB hgxMoved with hgxA | hgxB
    · have hgxImage : g x ∈ rep4ACycleAFinset.image g := by
        simpa [hA] using hgxA
      rw [Finset.mem_image] at hgxImage
      rcases hgxImage with ⟨y, hyA, hgy⟩
      have hyx : y = x := g.injective hgy
      subst y
      exact False.elim (rep4ACycleBFinset_not_mem_cycleAFinset x hxB hyA)
    · exact hgxB
  · rw [Finset.card_image_of_injective _ g.injective]

/-
If an ambient centralizer element sends the first support to the second support,
then it sends the second support to the first support.
-/
theorem rep4ACycleBFinset_image_eq_A_of_cycleAFinset_image_eq_B
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hA : rep4ACycleAFinset.image g = rep4ACycleBFinset) :
    rep4ACycleBFinset.image g = rep4ACycleAFinset := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.image_subset_iff]
    intro x hxB
    have hxMoved : x ∈ rep4AMovedPointFinset := by
      simp [rep4AMovedPointFinset, hxB]
    have hgxMoved := rep4A_ambientCentralizer_maps_movedPointFinset hg hxMoved
    rcases rep4A_movedPoint_mem_cycleA_or_cycleB hgxMoved with hgxA | hgxB
    · exact hgxA
    · have hgxImage : g x ∈ rep4ACycleAFinset.image g := by
        simpa [hA] using hgxB
      rw [Finset.mem_image] at hgxImage
      rcases hgxImage with ⟨y, hyA, hgy⟩
      have hyx : y = x := g.injective hgy
      subst y
      exact False.elim (rep4ACycleBFinset_not_mem_cycleAFinset x hxB hyA)
  · rw [Finset.card_image_of_injective _ g.injective]
    decide

/- An ambient 4A centralizer element either preserves or swaps the two 4-cycle supports. -/
theorem rep4A_ambientCentralizer_preserves_or_swaps_cycleFinsets
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    (rep4ACycleAFinset.image g = rep4ACycleAFinset ∧
        rep4ACycleBFinset.image g = rep4ACycleBFinset) ∨
      (rep4ACycleAFinset.image g = rep4ACycleBFinset ∧
        rep4ACycleBFinset.image g = rep4ACycleAFinset) := by
  rcases rep4A_ambientCentralizer_image_cycleAFinset_eq_A_or_B hg with hA | hB
  · exact Or.inl ⟨hA, rep4ACycleBFinset_image_eq_B_of_cycleAFinset_image_eq_A hg hA⟩
  · exact Or.inr ⟨hB, rep4ACycleBFinset_image_eq_A_of_cycleAFinset_image_eq_B hg hB⟩

/- The two displayed 4-cycle supports are distinct. -/
set_option maxRecDepth 100000 in
theorem rep4ACycleAFinset_ne_cycleBFinset :
    rep4ACycleAFinset ≠ rep4ACycleBFinset := by
  decide

/- The recovered swap parameter for the two displayed 4-cycle supports. -/
def rep4ASwapParam (g : Perm11) : Fin 2 :=
  if rep4ACycleAFinset.image g = rep4ACycleAFinset then 0 else 1

/- If the first support is preserved, the recovered swap parameter is zero. -/
theorem rep4ASwapParam_eq_zero_of_image_eq_A
    {g : Perm11} (hA : rep4ACycleAFinset.image g = rep4ACycleAFinset) :
    rep4ASwapParam g = 0 := by
  simp [rep4ASwapParam, hA]

/- If the first support maps to the second support, the recovered swap parameter is one. -/
theorem rep4ASwapParam_eq_one_of_image_eq_B
    {g : Perm11} (hB : rep4ACycleAFinset.image g = rep4ACycleBFinset) :
    rep4ASwapParam g = 1 := by
  have hne : rep4ACycleBFinset ≠ rep4ACycleAFinset := by
    intro h
    exact rep4ACycleAFinset_ne_cycleBFinset h.symm
  simp [rep4ASwapParam, hB, hne]

/- A zero recovered swap parameter forces separate preservation of the two supports. -/
theorem rep4A_ambientCentralizer_preserves_of_swapParam_zero
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hzero : rep4ASwapParam g = 0) :
    rep4ACycleAFinset.image g = rep4ACycleAFinset ∧
      rep4ACycleBFinset.image g = rep4ACycleBFinset := by
  unfold rep4ASwapParam at hzero
  by_cases hA : rep4ACycleAFinset.image g = rep4ACycleAFinset
  · exact ⟨hA, rep4ACycleBFinset_image_eq_B_of_cycleAFinset_image_eq_A hg hA⟩
  · simp [hA] at hzero

/- A one recovered swap parameter forces a swap of the two supports. -/
theorem rep4A_ambientCentralizer_swaps_of_swapParam_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hone : rep4ASwapParam g = 1) :
    rep4ACycleAFinset.image g = rep4ACycleBFinset ∧
      rep4ACycleBFinset.image g = rep4ACycleAFinset := by
  unfold rep4ASwapParam at hone
  by_cases hA : rep4ACycleAFinset.image g = rep4ACycleAFinset
  · simp [hA] at hone
  · rcases rep4A_ambientCentralizer_image_cycleAFinset_eq_A_or_B hg with hEqA | hEqB
    · exact False.elim (hA hEqA)
    · exact ⟨hEqB, rep4ACycleBFinset_image_eq_A_of_cycleAFinset_image_eq_B hg hEqB⟩

/- The preserve-or-swap theorem with the recovered `Fin 2` parameter attached. -/
theorem rep4A_ambientCentralizer_support_images_by_swapParam
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    (rep4ASwapParam g = 0 ∧
        rep4ACycleAFinset.image g = rep4ACycleAFinset ∧
        rep4ACycleBFinset.image g = rep4ACycleBFinset) ∨
      (rep4ASwapParam g = 1 ∧
        rep4ACycleAFinset.image g = rep4ACycleBFinset ∧
        rep4ACycleBFinset.image g = rep4ACycleAFinset) := by
  rcases rep4A_ambientCentralizer_preserves_or_swaps_cycleFinsets hg with hPreserve | hSwap
  · exact Or.inl ⟨rep4ASwapParam_eq_zero_of_image_eq_A hPreserve.1,
      hPreserve.1, hPreserve.2⟩
  · exact Or.inr ⟨rep4ASwapParam_eq_one_of_image_eq_B hSwap.1, hSwap.1, hSwap.2⟩

/- Recovered rotation coordinate for the image of the first 4-cycle base point. -/
def rep4ARotationParamI (g : Perm11) : Fin 4 :=
  if rep4ASwapParam g = 0 then
    rep4ACycleACoord (g (3 : Fin 11))
  else
    rep4ACycleBCoord (g (3 : Fin 11))

/- Recovered rotation coordinate for the image of the second 4-cycle base point. -/
def rep4ARotationParamJ (g : Perm11) : Fin 4 :=
  if rep4ASwapParam g = 0 then
    rep4ACycleBCoord (g (5 : Fin 11))
  else
    rep4ACycleACoord (g (5 : Fin 11))

/- If the two 4-cycle supports are preserved, the recovered `i` coordinate reproduces `g 3`. -/
theorem rep4ARotationParamI_apply_of_swapParam_zero
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hzero : rep4ASwapParam g = 0) :
    (rep4ACycleA ^ (rep4ARotationParamI g).1) (3 : Fin 11) = g (3 : Fin 11) := by
  have hPreserve := rep4A_ambientCentralizer_preserves_of_swapParam_zero hg hzero
  have hmemImage : g (3 : Fin 11) ∈ rep4ACycleAFinset.image g :=
    Finset.mem_image.mpr ⟨(3 : Fin 11), by decide, rfl⟩
  have hmemA : g (3 : Fin 11) ∈ rep4ACycleAFinset := by
    simpa [hPreserve.1] using hmemImage
  simpa [rep4ARotationParamI, hzero] using rep4ACycleACoord_apply_three_of_mem hmemA

/- If the two 4-cycle supports are swapped, the recovered `i` coordinate reproduces `g 3`. -/
theorem rep4ARotationParamI_apply_of_swapParam_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hone : rep4ASwapParam g = 1) :
    (rep4ACycleB ^ (rep4ARotationParamI g).1) (5 : Fin 11) = g (3 : Fin 11) := by
  have hSwap := rep4A_ambientCentralizer_swaps_of_swapParam_one hg hone
  have hmemImage : g (3 : Fin 11) ∈ rep4ACycleAFinset.image g :=
    Finset.mem_image.mpr ⟨(3 : Fin 11), by decide, rfl⟩
  have hmemB : g (3 : Fin 11) ∈ rep4ACycleBFinset := by
    simpa [hSwap.1] using hmemImage
  have hnot : ¬rep4ASwapParam g = 0 := by
    intro hzero
    exact (by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hzero)
  simpa [rep4ARotationParamI, hnot] using rep4ACycleBCoord_apply_five_of_mem hmemB

/- If the two 4-cycle supports are preserved, the recovered `j` coordinate reproduces `g 5`. -/
theorem rep4ARotationParamJ_apply_of_swapParam_zero
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hzero : rep4ASwapParam g = 0) :
    (rep4ACycleB ^ (rep4ARotationParamJ g).1) (5 : Fin 11) = g (5 : Fin 11) := by
  have hPreserve := rep4A_ambientCentralizer_preserves_of_swapParam_zero hg hzero
  have hmemImage : g (5 : Fin 11) ∈ rep4ACycleBFinset.image g :=
    Finset.mem_image.mpr ⟨(5 : Fin 11), by decide, rfl⟩
  have hmemB : g (5 : Fin 11) ∈ rep4ACycleBFinset := by
    simpa [hPreserve.2] using hmemImage
  simpa [rep4ARotationParamJ, hzero] using rep4ACycleBCoord_apply_five_of_mem hmemB

/- If the two 4-cycle supports are swapped, the recovered `j` coordinate reproduces `g 5`. -/
theorem rep4ARotationParamJ_apply_of_swapParam_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex)
    (hone : rep4ASwapParam g = 1) :
    (rep4ACycleA ^ (rep4ARotationParamJ g).1) (3 : Fin 11) = g (5 : Fin 11) := by
  have hSwap := rep4A_ambientCentralizer_swaps_of_swapParam_one hg hone
  have hmemImage : g (5 : Fin 11) ∈ rep4ACycleBFinset.image g :=
    Finset.mem_image.mpr ⟨(5 : Fin 11), by decide, rfl⟩
  have hmemA : g (5 : Fin 11) ∈ rep4ACycleAFinset := by
    simpa [hSwap.2] using hmemImage
  have hnot : ¬rep4ASwapParam g = 0 := by
    intro hzero
    exact (by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hzero)
  simpa [rep4ARotationParamJ, hnot] using rep4ACycleACoord_apply_three_of_mem hmemA

/- The displayed 4A candidate recovered from an ambient centralizer element. -/
def rep4ARecoveredRotation (g : Perm11) : Perm11 :=
  if rep4ASwapParam g = 0 then
    rep4ARotation
      (rep4AFixedParam g) (0 : Fin 2)
      (rep4ARotationParamI g) (rep4ARotationParamJ g)
  else
    rep4ARotation
      (rep4AFixedParam g) (1 : Fin 2)
      (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The displayed 192-parameter family for 4A as a finite set, without cardinality claims. -/
def rep4AAllRotationFinset : Finset Perm11 :=
  Finset.univ.image
    (fun p : ((Fin 6 × Fin 2) × Fin 4) × Fin 4 =>
      rep4ARotation p.1.1.1 p.1.1.2 p.1.2 p.2)

/- The recovered displayed candidate is a member of the 192-parameter family. -/
theorem rep4ARecoveredRotation_mem_allRotationFinset (g : Perm11) :
    rep4ARecoveredRotation g ∈ rep4AAllRotationFinset := by
  classical
  by_cases hzero : rep4ASwapParam g = 0
  · rw [rep4ARecoveredRotation, if_pos hzero, rep4AAllRotationFinset]
    exact Finset.mem_image.mpr
      ⟨⟨⟨⟨rep4AFixedParam g, (0 : Fin 2)⟩, rep4ARotationParamI g⟩,
          rep4ARotationParamJ g⟩, Finset.mem_univ _, rfl⟩
  · rw [rep4ARecoveredRotation, if_neg hzero, rep4AAllRotationFinset]
    exact Finset.mem_image.mpr
      ⟨⟨⟨⟨rep4AFixedParam g, (1 : Fin 2)⟩, rep4ARotationParamJ g⟩,
          rep4ARotationParamI g⟩, Finset.mem_univ _, rfl⟩

/- The displayed 4A rotation family has at most the expected 192 parameters. -/
set_option maxRecDepth 100000 in
theorem rep4AAllRotationFinset_card_le : rep4AAllRotationFinset.card ≤ 192 := by
  rw [rep4AAllRotationFinset]
  calc
    (Finset.univ.image
        (fun p : ((Fin 6 × Fin 2) × Fin 4) × Fin 4 =>
          rep4ARotation p.1.1.1 p.1.1.2 p.1.2 p.2)).card
        ≤ (Finset.univ : Finset (((Fin 6 × Fin 2) × Fin 4) × Fin 4)).card := by
          exact Finset.card_image_le
    _ = 192 := by decide

/- Without support swap, a displayed 4A rotation sends the A-base by its `i` coordinate. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_three_swap_zero
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotation r (0 : Fin 2) i j (3 : Fin 11) =
      (rep4ACycleA ^ i.1) (3 : Fin 11) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- Without support swap, a displayed 4A rotation sends the B-base by its `j` coordinate. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_five_swap_zero
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotation r (0 : Fin 2) i j (5 : Fin 11) =
      (rep4ACycleB ^ j.1) (5 : Fin 11) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- With support swap, a displayed 4A rotation sends the A-base into the B-cycle by `j`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_three_swap_one
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotation r (1 : Fin 2) i j (3 : Fin 11) =
      (rep4ACycleB ^ j.1) (5 : Fin 11) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- With support swap, a displayed 4A rotation sends the B-base into the A-cycle by `i`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_five_swap_one
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotation r (1 : Fin 2) i j (5 : Fin 11) =
      (rep4ACycleA ^ i.1) (3 : Fin 11) := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- The recovered displayed candidate agrees with an ambient centralizer element on the A-base. -/
theorem rep4ARecoveredRotation_apply_three
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (3 : Fin 11) = g (3 : Fin 11) := by
  rcases rep4A_ambientCentralizer_support_images_by_swapParam hg with hPreserve | hSwap
  · have hzero := hPreserve.1
    rw [rep4ARecoveredRotation, if_pos hzero, rep4ARotation_apply_three_swap_zero]
    exact rep4ARotationParamI_apply_of_swapParam_zero hg hzero
  · have hone := hSwap.1
    have hnot : ¬rep4ASwapParam g = 0 := by
      intro hzero
      exact (by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hzero)
    rw [rep4ARecoveredRotation, if_neg hnot, rep4ARotation_apply_three_swap_one]
    exact rep4ARotationParamI_apply_of_swapParam_one hg hone

/- The recovered displayed candidate agrees with an ambient centralizer element on the B-base. -/
theorem rep4ARecoveredRotation_apply_five
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (5 : Fin 11) = g (5 : Fin 11) := by
  rcases rep4A_ambientCentralizer_support_images_by_swapParam hg with hPreserve | hSwap
  · have hzero := hPreserve.1
    rw [rep4ARecoveredRotation, if_pos hzero, rep4ARotation_apply_five_swap_zero]
    exact rep4ARotationParamJ_apply_of_swapParam_zero hg hzero
  · have hone := hSwap.1
    have hnot : ¬rep4ASwapParam g = 0 := by
      intro hzero
      exact (by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hzero)
    rw [rep4ARecoveredRotation, if_neg hnot, rep4ARotation_apply_five_swap_one]
    exact rep4ARotationParamJ_apply_of_swapParam_one hg hone

/- A displayed 4A rotation commutes with the first A-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_four_eq_perm_apply_three
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (4 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (3 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation commutes with the second A-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_nine_eq_perm_apply_four
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (9 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (4 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation commutes with the third A-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_seven_eq_perm_apply_nine
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (7 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (9 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation commutes with the first B-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_eight_eq_perm_apply_five
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (8 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (5 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation commutes with the second B-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_six_eq_perm_apply_eight
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (6 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (8 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation commutes with the third B-cycle step. -/
set_option maxRecDepth 100000 in
theorem rep4ARotation_apply_ten_eq_perm_apply_six
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (10 : Fin 11) =
      representativePerm rep4AIndex (rep4ARotation r s i j (6 : Fin 11)) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 100000

/- The recovered candidate commutes with the first A-cycle step. -/
theorem rep4ARecoveredRotation_apply_four_eq_perm_apply_three (g : Perm11) :
    rep4ARecoveredRotation g (4 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (3 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_four_eq_perm_apply_three
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_four_eq_perm_apply_three
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate commutes with the second A-cycle step. -/
theorem rep4ARecoveredRotation_apply_nine_eq_perm_apply_four (g : Perm11) :
    rep4ARecoveredRotation g (9 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (4 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_nine_eq_perm_apply_four
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_nine_eq_perm_apply_four
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate commutes with the third A-cycle step. -/
theorem rep4ARecoveredRotation_apply_seven_eq_perm_apply_nine (g : Perm11) :
    rep4ARecoveredRotation g (7 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (9 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_seven_eq_perm_apply_nine
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_seven_eq_perm_apply_nine
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate commutes with the first B-cycle step. -/
theorem rep4ARecoveredRotation_apply_eight_eq_perm_apply_five (g : Perm11) :
    rep4ARecoveredRotation g (8 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (5 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_eight_eq_perm_apply_five
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_eight_eq_perm_apply_five
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate commutes with the second B-cycle step. -/
theorem rep4ARecoveredRotation_apply_six_eq_perm_apply_eight (g : Perm11) :
    rep4ARecoveredRotation g (6 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (8 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_six_eq_perm_apply_eight
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_six_eq_perm_apply_eight
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate commutes with the third B-cycle step. -/
theorem rep4ARecoveredRotation_apply_ten_eq_perm_apply_six (g : Perm11) :
    rep4ARecoveredRotation g (10 : Fin 11) =
      representativePerm rep4AIndex (rep4ARecoveredRotation g (6 : Fin 11)) := by
  by_cases hzero : rep4ASwapParam g = 0
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_ten_eq_perm_apply_six
        (rep4AFixedParam g) (0 : Fin 2)
        (rep4ARotationParamI g) (rep4ARotationParamJ g)
  · simpa [rep4ARecoveredRotation, hzero] using
      rep4ARotation_apply_ten_eq_perm_apply_six
        (rep4AFixedParam g) (1 : Fin 2)
        (rep4ARotationParamJ g) (rep4ARotationParamI g)

/- The recovered candidate agrees with an ambient centralizer element at `4`. -/
theorem rep4ARecoveredRotation_apply_four
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (4 : Fin 11) = g (4 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_four_eq_perm_apply_three,
    rep4ARecoveredRotation_apply_three hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (3 : Fin 11)).symm

/- The recovered candidate agrees with an ambient centralizer element at `9`. -/
theorem rep4ARecoveredRotation_apply_nine
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (9 : Fin 11) = g (9 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_nine_eq_perm_apply_four,
    rep4ARecoveredRotation_apply_four hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (4 : Fin 11)).symm

/- The recovered candidate agrees with an ambient centralizer element at `7`. -/
theorem rep4ARecoveredRotation_apply_seven
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (7 : Fin 11) = g (7 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_seven_eq_perm_apply_nine,
    rep4ARecoveredRotation_apply_nine hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (9 : Fin 11)).symm

/- The recovered candidate agrees with an ambient centralizer element at `8`. -/
theorem rep4ARecoveredRotation_apply_eight
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (8 : Fin 11) = g (8 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_eight_eq_perm_apply_five,
    rep4ARecoveredRotation_apply_five hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (5 : Fin 11)).symm

/- The recovered candidate agrees with an ambient centralizer element at `6`. -/
theorem rep4ARecoveredRotation_apply_six
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (6 : Fin 11) = g (6 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_six_eq_perm_apply_eight,
    rep4ARecoveredRotation_apply_eight hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (8 : Fin 11)).symm

/- The recovered candidate agrees with an ambient centralizer element at `10`. -/
theorem rep4ARecoveredRotation_apply_ten
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (10 : Fin 11) = g (10 : Fin 11) := by
  rw [rep4ARecoveredRotation_apply_ten_eq_perm_apply_six,
    rep4ARecoveredRotation_apply_six hg]
  simpa using (rep4A_ambientCentralizer_apply_comm hg (6 : Fin 11)).symm

/- A displayed 4A rotation restricts to the displayed fixed-point permutation at `0`. -/
theorem rep4ARotation_apply_zero
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (0 : Fin 11) = rep4AFixedPerm r (0 : Fin 11) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation restricts to the displayed fixed-point permutation at `1`. -/
theorem rep4ARotation_apply_one
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (1 : Fin 11) = rep4AFixedPerm r (1 : Fin 11) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- A displayed 4A rotation restricts to the displayed fixed-point permutation at `2`. -/
theorem rep4ARotation_apply_two
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ARotation r s i j (2 : Fin 11) = rep4AFixedPerm r (2 : Fin 11) := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- The recovered candidate agrees with an ambient centralizer element at `0`. -/
theorem rep4ARecoveredRotation_apply_zero
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (0 : Fin 11) = g (0 : Fin 11) := by
  by_cases hzero : rep4ASwapParam g = 0
  · rw [rep4ARecoveredRotation, if_pos hzero, rep4ARotation_apply_zero]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)
  · rw [rep4ARecoveredRotation, if_neg hzero, rep4ARotation_apply_zero]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)

/- The recovered candidate agrees with an ambient centralizer element at `1`. -/
theorem rep4ARecoveredRotation_apply_one
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (1 : Fin 11) = g (1 : Fin 11) := by
  by_cases hzero : rep4ASwapParam g = 0
  · rw [rep4ARecoveredRotation, if_pos hzero, rep4ARotation_apply_one]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)
  · rw [rep4ARecoveredRotation, if_neg hzero, rep4ARotation_apply_one]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)

/- The recovered candidate agrees with an ambient centralizer element at `2`. -/
theorem rep4ARecoveredRotation_apply_two
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g (2 : Fin 11) = g (2 : Fin 11) := by
  by_cases hzero : rep4ASwapParam g = 0
  · rw [rep4ARecoveredRotation, if_pos hzero, rep4ARotation_apply_two]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)
  · rw [rep4ARecoveredRotation, if_neg hzero, rep4ARotation_apply_two]
    exact rep4AFixedParam_apply_of_mem_fixedPoint hg (by decide)

/- The recovered displayed candidate is equal to the ambient centralizer element it recovers. -/
set_option maxHeartbeats 1000000 in
-- The proof performs extensional comparison over all eleven points with computed Fin coercions.
theorem rep4ARecoveredRotation_eq_of_ambientCentralizer
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    rep4ARecoveredRotation g = g := by
  ext x
  fin_cases x
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_zero hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_one hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_two hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_three hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_four hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_five hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_six hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_seven hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_eight hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_nine hg)
  · simpa using congrArg Fin.val (rep4ARecoveredRotation_apply_ten hg)

/- Every ambient 4A centralizer element lies in the displayed 192-candidate family. -/
theorem rep4A_ambientCentralizer_mem_allRotationFinset
    {g : Perm11} (hg : g ∈ RepresentativeAmbientCentralizer rep4AIndex) :
    g ∈ rep4AAllRotationFinset := by
  rw [← rep4ARecoveredRotation_eq_of_ambientCentralizer hg]
  exact rep4ARecoveredRotation_mem_allRotationFinset g

/- The ambient 4A centralizer is bounded by the displayed 192-candidate family. -/
theorem rep4A_ambientCentralizer_card_le_allRotationFinset :
    Nat.card (RepresentativeAmbientCentralizer rep4AIndex) ≤ rep4AAllRotationFinset.card := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hle :
      Fintype.card (RepresentativeAmbientCentralizer rep4AIndex) ≤
        Fintype.card {g : Perm11 // g ∈ rep4AAllRotationFinset} := by
    refine Fintype.card_le_of_injective
      (fun g : RepresentativeAmbientCentralizer rep4AIndex =>
        (⟨g.1, rep4A_ambientCentralizer_mem_allRotationFinset g.2⟩ :
          {g : Perm11 // g ∈ rep4AAllRotationFinset})) ?_
    intro g h hgh
    apply Subtype.ext
    exact congrArg
      (fun y : {g : Perm11 // g ∈ rep4AAllRotationFinset} => y.1) hgh
  rwa [Fintype.card_coe] at hle

/- The ambient 4A centralizer has at most `192` elements by the recovered parameter envelope. -/
theorem rep4A_ambientCentralizer_card_le_192 :
    Nat.card (RepresentativeAmbientCentralizer rep4AIndex) ≤ 192 :=
  le_trans rep4A_ambientCentralizer_card_le_allRotationFinset rep4AAllRotationFinset_card_le

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- The first small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r0_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (0 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (0 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r0_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (0 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (0 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r1_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (1 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (1 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r1_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (1 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (1 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r2_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (2 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (2 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r2_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (2 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (2 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r3_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (3 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (3 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r3_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (3 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (3 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r4_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (4 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (4 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r4_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (4 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (4 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r5_s0
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (5 : Fin 6) (0 : Fin 2) i j) = true ↔
      rep4APreservingParam (5 : Fin 6) (0 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 1000000 in
-- The proof unfolds a 16-candidate by 66-block finite preservation check.
/- A small Witt-block sieve slice for 4A candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff_r5_s1
    (i j : Fin 4) :
    wittBlockPreservationCheck
        (rep4ARotation (5 : Fin 6) (1 : Fin 2) i j) = true ↔
      rep4APreservingParam (5 : Fin 6) (1 : Fin 2) i j := by
  fin_cases i <;> fin_cases j <;> decide

/- The finite Witt-block sieve for all displayed 4A rotation candidates. -/
theorem rep4ARotation_wittBlockPreservationCheck_iff
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    wittBlockPreservationCheck (rep4ARotation r s i j) = true ↔
      rep4APreservingParam r s i j := by
  fin_cases r <;> fin_cases s
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r0_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r0_s1 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r1_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r1_s1 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r2_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r2_s1 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r3_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r3_s1 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r4_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r4_s1 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r5_s0 i j
  · exact rep4ARotation_wittBlockPreservationCheck_iff_r5_s1 i j

/- Among the displayed 4A rotations, exactly the eight certified parameters preserve Witt blocks. -/
theorem rep4ARotation_preserves_wittBlocks_iff
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    WittDesign.PreservesWittBlocks (rep4ARotation r s i j) ↔
      rep4APreservingParam r s i j := by
  rw [← wittBlockPreservationCheck_eq_true_iff]
  exact rep4ARotation_wittBlockPreservationCheck_iff r s i j

/- On the displayed 4A rotation candidates, the recovered parameter is the displayed one. -/
set_option maxRecDepth 100000 in
theorem rep4ASwapParam_rep4ARotation
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4ASwapParam (rep4ARotation r s i j) = s := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/- Without support swap, the recovered `i` coordinate is the displayed `i`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotationParamI_rep4ARotation_swap_zero
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotationParamI (rep4ARotation r (0 : Fin 2) i j) = i := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- With support swap, the recovered `i` coordinate reads the displayed `j`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotationParamI_rep4ARotation_swap_one
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotationParamI (rep4ARotation r (1 : Fin 2) i j) = j := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- Without support swap, the recovered `j` coordinate is the displayed `j`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotationParamJ_rep4ARotation_swap_zero
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotationParamJ (rep4ARotation r (0 : Fin 2) i j) = j := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/- With support swap, the recovered `j` coordinate reads the displayed `i`. -/
set_option maxRecDepth 100000 in
theorem rep4ARotationParamJ_rep4ARotation_swap_one
    (r : Fin 6) (i j : Fin 4) :
    rep4ARotationParamJ (rep4ARotation r (1 : Fin 2) i j) = i := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide

/-
If a 4A ambient-centralizer parameter tuple satisfies the structured
preserving-parameter predicate, then the corresponding displayed rotation is
one of the eight preserving candidates.
-/
set_option maxRecDepth 100000 in
theorem rep4ARotation_mem_preservingRotationFinset_of_preservingParam
    (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    rep4APreservingParam r s i j →
      rep4ARotation r s i j ∈ rep4APreservingRotationFinset := by
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> decide

/-
The ambient image of the `M11` centralizer of the 4A representative lies in
the eight displayed Witt-preserving candidates.
-/
theorem rep4ACentralizer_map_mem_preservingRotationFinset
    {x : Perm11}
    (hx : x ∈ (RepresentativeCentralizer rep4AIndex).map M11Subgroup.subtype) :
    x ∈ rep4APreservingRotationFinset := by
  classical
  have hxAmbient : x ∈ RepresentativeAmbientCentralizer rep4AIndex :=
    representativeCentralizer_map_le_ambient rep4AIndex hx
  have hxAll := rep4A_ambientCentralizer_mem_allRotationFinset hxAmbient
  rw [rep4AAllRotationFinset, Finset.mem_image] at hxAll
  rcases hxAll with ⟨p, -, hp⟩
  rcases p with ⟨⟨⟨r, s⟩, i⟩, j⟩
  have hxPres : WittDesign.PreservesWittBlocks x := by
    rcases hx with ⟨y, -, rfl⟩
    exact WittDesign.M11_preserves_wittBlocks y
  have hparam : rep4APreservingParam r s i j := by
    apply (rep4ARotation_preserves_wittBlocks_iff r s i j).mp
    simpa [hp] using hxPres
  rw [← hp]
  exact rep4ARotation_mem_preservingRotationFinset_of_preservingParam r s i j hparam

/- The ambient image of the `M11` 4A centralizer has at most eight elements. -/
theorem rep4ACentralizer_map_card_le_preservingRotationFinset :
    Nat.card ((RepresentativeCentralizer rep4AIndex).map M11Subgroup.subtype) ≤
      rep4APreservingRotationFinset.card := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hle :
      Fintype.card ((RepresentativeCentralizer rep4AIndex).map M11Subgroup.subtype) ≤
        Fintype.card {x : Perm11 // x ∈ rep4APreservingRotationFinset} := by
    refine Fintype.card_le_of_injective
      (fun x : (RepresentativeCentralizer rep4AIndex).map M11Subgroup.subtype =>
        (⟨x.1, rep4ACentralizer_map_mem_preservingRotationFinset x.2⟩ :
          {x : Perm11 // x ∈ rep4APreservingRotationFinset})) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : {x : Perm11 // x ∈ rep4APreservingRotationFinset} => z.1) hxy
  rwa [Fintype.card_coe] at hle

/- Upper bound for the `M11` centralizer of the 4A representative. -/
theorem rep4A_centralizer_card_le :
    Nat.card (RepresentativeCentralizer rep4AIndex) ≤ 8 := by
  have hmapcard :
      Nat.card ((RepresentativeCentralizer rep4AIndex).map M11Subgroup.subtype) =
        Nat.card (RepresentativeCentralizer rep4AIndex) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := rep4ACentralizer_map_card_le_preservingRotationFinset
  rw [hmapcard, rep4APreservingRotationFinset_card] at hle
  exact hle

/- The `M11` centralizer of the 4A representative has order `8`. -/
theorem rep4A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep4AIndex) = 8 :=
  le_antisymm rep4A_centralizer_card_le rep4A_centralizer_card_ge

/- The conjugacy orbit of the 4A representative has size `990`. -/
theorem rep4AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep4AIndex)) = 990 :=
  conjOrbit_card_of_centralizer_card_eq_eight
    (representativeM11 rep4AIndex) rep4A_centralizer_card

end ConjugacyClasses
end Certificates
end Sporadic
