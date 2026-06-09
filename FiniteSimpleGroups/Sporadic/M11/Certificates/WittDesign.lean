/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.GeneratedSubgroup

/-!
# Witt design certificate workspace

This file starts a small certificate route for the final stabilizer step.
The 66 blocks below are candidate blocks for the small Witt design `S(4,5,11)`.
The data is not trusted: Lean checks the finite claims recorded here.
-/

namespace Sporadic
namespace Certificates
namespace WittDesign

/-- A block is a finite set of points in the degree-11 action. -/
abbrev Block : Type :=
  Finset (Fin 11)

/-- Candidate small Witt design blocks, in zero-based notation. -/
def wittBlockList : List Block :=
  [
    ({0, 1, 2, 3, 9} : Block),
    ({0, 1, 2, 4, 7} : Block),
    ({0, 1, 2, 5, 6} : Block),
    ({0, 1, 2, 8, 10} : Block),
    ({0, 1, 3, 4, 8} : Block),
    ({0, 1, 3, 5, 7} : Block),
    ({0, 1, 3, 6, 10} : Block),
    ({0, 1, 4, 5, 10} : Block),
    ({0, 1, 4, 6, 9} : Block),
    ({0, 1, 5, 8, 9} : Block),
    ({0, 1, 6, 7, 8} : Block),
    ({0, 1, 7, 9, 10} : Block),
    ({0, 2, 3, 4, 5} : Block),
    ({0, 2, 3, 6, 8} : Block),
    ({0, 2, 3, 7, 10} : Block),
    ({0, 2, 4, 6, 10} : Block),
    ({0, 2, 4, 8, 9} : Block),
    ({0, 2, 5, 7, 8} : Block),
    ({0, 2, 5, 9, 10} : Block),
    ({0, 2, 6, 7, 9} : Block),
    ({0, 3, 4, 6, 7} : Block),
    ({0, 3, 4, 9, 10} : Block),
    ({0, 3, 5, 6, 9} : Block),
    ({0, 3, 5, 8, 10} : Block),
    ({0, 3, 7, 8, 9} : Block),
    ({0, 4, 5, 6, 8} : Block),
    ({0, 4, 5, 7, 9} : Block),
    ({0, 4, 7, 8, 10} : Block),
    ({0, 5, 6, 7, 10} : Block),
    ({0, 6, 8, 9, 10} : Block),
    ({1, 2, 3, 4, 10} : Block),
    ({1, 2, 3, 5, 8} : Block),
    ({1, 2, 3, 6, 7} : Block),
    ({1, 2, 4, 5, 9} : Block),
    ({1, 2, 4, 6, 8} : Block),
    ({1, 2, 5, 7, 10} : Block),
    ({1, 2, 6, 9, 10} : Block),
    ({1, 2, 7, 8, 9} : Block),
    ({1, 3, 4, 5, 6} : Block),
    ({1, 3, 4, 7, 9} : Block),
    ({1, 3, 5, 9, 10} : Block),
    ({1, 3, 6, 8, 9} : Block),
    ({1, 3, 7, 8, 10} : Block),
    ({1, 4, 5, 7, 8} : Block),
    ({1, 4, 6, 7, 10} : Block),
    ({1, 4, 8, 9, 10} : Block),
    ({1, 5, 6, 7, 9} : Block),
    ({1, 5, 6, 8, 10} : Block),
    ({2, 3, 4, 6, 9} : Block),
    ({2, 3, 4, 7, 8} : Block),
    ({2, 3, 5, 6, 10} : Block),
    ({2, 3, 5, 7, 9} : Block),
    ({2, 3, 8, 9, 10} : Block),
    ({2, 4, 5, 6, 7} : Block),
    ({2, 4, 5, 8, 10} : Block),
    ({2, 4, 7, 9, 10} : Block),
    ({2, 5, 6, 8, 9} : Block),
    ({2, 6, 7, 8, 10} : Block),
    ({3, 4, 5, 7, 10} : Block),
    ({3, 4, 5, 8, 9} : Block),
    ({3, 4, 6, 8, 10} : Block),
    ({3, 5, 6, 7, 8} : Block),
    ({3, 6, 7, 9, 10} : Block),
    ({4, 5, 6, 9, 10} : Block),
    ({4, 6, 7, 8, 9} : Block),
    ({5, 7, 8, 9, 10} : Block)
  ]

/-- The candidate small Witt design blocks as a `Finset`. -/
def wittBlocks : Finset Block :=
  wittBlockList.toFinset

set_option maxRecDepth 20000 in
/-- The candidate block list has no duplicate blocks. -/
theorem wittBlockList_nodup : wittBlockList.Nodup := by
  decide

set_option maxRecDepth 20000 in
/-- The candidate block list has length 66. -/
theorem wittBlockList_length : wittBlockList.length = 66 := by
  decide

set_option maxRecDepth 20000 in
/-- The candidate block list has the expected 66 blocks. -/
theorem wittBlocks_card : wittBlocks.card = 66 := by
  rw [wittBlocks, List.toFinset_card_of_nodup wittBlockList_nodup]
  decide

/-- The block with certificate index `i`. -/
def wittBlockAt (i : Fin 66) : Block :=
  wittBlockList.get ⟨i.1, by rw [wittBlockList_length]; exact i.2⟩

/-- Every indexed candidate block belongs to `wittBlocks`. -/
theorem wittBlockAt_mem (i : Fin 66) : wittBlockAt i ∈ wittBlocks := by
  rw [wittBlocks]
  exact List.mem_toFinset.mpr (List.get_mem wittBlockList _)

/-- Membership in the listed blocks gives membership in the block finset. -/
theorem mem_wittBlocks_of_mem_wittBlockList {B : Block} (hB : B ∈ wittBlockList) :
    B ∈ wittBlocks := by
  rw [wittBlocks]
  exact List.mem_toFinset.mpr hB

/-- Membership in the block finset comes from membership in the listed blocks. -/
theorem mem_wittBlockList_of_mem_wittBlocks {B : Block} (hB : B ∈ wittBlocks) :
    B ∈ wittBlockList := by
  rw [wittBlocks] at hB
  exact List.mem_toFinset.mp hB

/-- Any member of `wittBlockList` is one of the indexed candidate blocks. -/
theorem exists_wittBlockAt_eq_get (i : Fin wittBlockList.length) :
    ∃ j : Fin 66, wittBlockList.get i = wittBlockAt j := by
  let j : Fin 66 := ⟨i.1, by simpa [wittBlockList_length] using i.2⟩
  refine ⟨j, ?_⟩
  unfold wittBlockAt
  congr

/-- Image of a block under a degree-11 permutation. -/
def blockMap (g : Perm11) (B : Block) : Block :=
  B.image g

@[simp]
theorem blockMap_one (B : Block) : blockMap (1 : Perm11) B = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_mul (g h : Perm11) (B : Block) :
    blockMap (g * h) B = blockMap g (blockMap h B) := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_inv_self (g : Perm11) (B : Block) :
    blockMap g⁻¹ (blockMap g B) = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_self_inv (g : Perm11) (B : Block) :
    blockMap g (blockMap g⁻¹ B) = B := by
  ext x
  simp [blockMap]

/-- A permutation preserves the candidate Witt block set. -/
def PreservesWittBlocks (g : Perm11) : Prop :=
  (∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks) ∧
    (∀ B ∈ wittBlockList, blockMap g⁻¹ B ∈ wittBlocks)

/-- A block-index permutation certificate for the action of `m11a`. -/
def m11aBlockIndexList : List (Fin 66) :=
  [30, 31, 32, 0, 33, 34, 1, 2, 35, 36, 37, 3, 38, 39, 4, 5, 40, 41, 6, 42, 43,
    7, 44, 8, 45, 46, 47, 9, 10, 11, 12, 48, 49, 50, 51, 13, 14, 52, 53, 54,
    15, 55, 16, 56, 17, 18, 57, 19, 58, 59, 20, 60, 21, 61, 22, 23, 62, 24,
    25, 63, 26, 64, 27, 28, 65, 29]

/-- A block-index permutation certificate for the action of `m11a⁻¹`. -/
def m11aInvBlockIndexList : List (Fin 66) :=
  [3, 6, 7, 11, 14, 15, 18, 21, 23, 27, 28, 29, 30, 35, 36, 40, 42, 44, 45, 47,
    50, 52, 54, 55, 57, 58, 60, 62, 63, 65, 0, 1, 2, 4, 5, 8, 9, 10, 12, 13,
    16, 17, 19, 20, 22, 24, 25, 26, 31, 32, 33, 34, 37, 38, 39, 41, 43, 46,
    48, 49, 51, 53, 56, 59, 61, 64]

/-- A block-index permutation certificate for the action of `m11b`. -/
def m11bBlockIndexList : List (Fin 66) :=
  [8, 2, 6, 10, 9, 0, 11, 5, 7, 4, 3, 1, 22, 29, 19, 28, 25, 13, 20, 15, 18,
    26, 21, 24, 16, 23, 12, 17, 14, 27, 46, 41, 36, 38, 47, 32, 44, 34, 40,
    33, 39, 45, 37, 31, 35, 43, 30, 42, 63, 56, 62, 48, 64, 50, 61, 53, 60,
    57, 51, 59, 65, 52, 55, 58, 54, 49]

/-- A block-index permutation certificate for the action of `m11b⁻¹`. -/
def m11bInvBlockIndexList : List (Fin 66) :=
  [5, 11, 1, 10, 9, 7, 2, 8, 0, 4, 3, 6, 26, 17, 28, 19, 24, 27, 20, 14, 18,
    22, 12, 25, 23, 16, 21, 29, 15, 13, 46, 43, 35, 39, 37, 44, 32, 42, 33,
    40, 38, 31, 47, 45, 36, 41, 30, 34, 51, 65, 53, 58, 61, 55, 64, 62, 49,
    57, 63, 59, 56, 54, 50, 48, 52, 60]

theorem m11aBlockIndexList_length : m11aBlockIndexList.length = 66 := by
  decide

theorem m11aInvBlockIndexList_length : m11aInvBlockIndexList.length = 66 := by
  decide

theorem m11bBlockIndexList_length : m11bBlockIndexList.length = 66 := by
  decide

theorem m11bInvBlockIndexList_length : m11bInvBlockIndexList.length = 66 := by
  decide

/-- The block-index map induced by `m11a`. -/
def m11aBlockIndex (i : Fin 66) : Fin 66 :=
  m11aBlockIndexList.get ⟨i.1, by rw [m11aBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m11a⁻¹`. -/
def m11aInvBlockIndex (i : Fin 66) : Fin 66 :=
  m11aInvBlockIndexList.get ⟨i.1, by rw [m11aInvBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m11b`. -/
def m11bBlockIndex (i : Fin 66) : Fin 66 :=
  m11bBlockIndexList.get ⟨i.1, by rw [m11bBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m11b⁻¹`. -/
def m11bInvBlockIndex (i : Fin 66) : Fin 66 :=
  m11bInvBlockIndexList.get ⟨i.1, by rw [m11bInvBlockIndexList_length]; exact i.2⟩

set_option maxHeartbeats 800000 in
-- The indexed 66-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 80000 in
/-- Lean verifies the block-index certificate for `m11a`. -/
theorem m11a_blockMapAt :
    ∀ i : Fin 66, blockMap m11a (wittBlockAt i) = wittBlockAt (m11aBlockIndex i) := by
  decide

set_option maxHeartbeats 800000 in
-- The indexed 66-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 80000 in
/-- Lean verifies the block-index certificate for `m11a⁻¹`. -/
theorem m11aInv_blockMapAt :
    ∀ i : Fin 66, blockMap m11a⁻¹ (wittBlockAt i) =
      wittBlockAt (m11aInvBlockIndex i) := by
  decide

set_option maxHeartbeats 800000 in
-- The indexed 66-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 80000 in
/-- Lean verifies the block-index certificate for `m11b`. -/
theorem m11b_blockMapAt :
    ∀ i : Fin 66, blockMap m11b (wittBlockAt i) = wittBlockAt (m11bBlockIndex i) := by
  decide

set_option maxHeartbeats 800000 in
-- The indexed 66-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 80000 in
/-- Lean verifies the block-index certificate for `m11b⁻¹`. -/
theorem m11bInv_blockMapAt :
    ∀ i : Fin 66, blockMap m11b⁻¹ (wittBlockAt i) =
      wittBlockAt (m11bInvBlockIndex i) := by
  decide

/--
If a permutation has a verified block-index certificate, then it sends every
listed Witt block to a listed Witt block.
-/
theorem forall_mem_blockMap_mem_of_blockMapAt (g : Perm11) (index : Fin 66 → Fin 66)
    (h : ∀ i : Fin 66, blockMap g (wittBlockAt i) = wittBlockAt (index i)) :
    ∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks := by
  rw [List.forall_mem_iff_get]
  intro i
  obtain ⟨j, hget⟩ := exists_wittBlockAt_eq_get i
  rw [hget, h]
  exact wittBlockAt_mem (index j)

/--
A permutation preserves the candidate Witt block set once both it and its inverse
have verified block-index certificates.
-/
theorem PreservesWittBlocks.of_blockMapAt (g : Perm11)
    (index invIndex : Fin 66 → Fin 66)
    (h : ∀ i : Fin 66, blockMap g (wittBlockAt i) = wittBlockAt (index i))
    (hinv : ∀ i : Fin 66, blockMap g⁻¹ (wittBlockAt i) = wittBlockAt (invIndex i)) :
    PreservesWittBlocks g :=
  ⟨forall_mem_blockMap_mem_of_blockMapAt g index h,
    forall_mem_blockMap_mem_of_blockMapAt g⁻¹ invIndex hinv⟩

theorem PreservesWittBlocks.one : PreservesWittBlocks (1 : Perm11) := by
  constructor <;> intro B hB
  · rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB
  · change blockMap (1 : Perm11) B ∈ wittBlocks
    rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB

theorem PreservesWittBlocks.mul {g h : Perm11}
    (hg : PreservesWittBlocks g) (hh : PreservesWittBlocks h) :
    PreservesWittBlocks (g * h) := by
  constructor
  · intro B hB
    rw [blockMap_mul]
    have hhB : blockMap h B ∈ wittBlocks := hh.1 B hB
    exact hg.1 (blockMap h B) (mem_wittBlockList_of_mem_wittBlocks hhB)
  · intro B hB
    rw [show (g * h)⁻¹ = h⁻¹ * g⁻¹ by simp, blockMap_mul]
    have hgB : blockMap g⁻¹ B ∈ wittBlocks := hg.2 B hB
    exact hh.2 (blockMap g⁻¹ B) (mem_wittBlockList_of_mem_wittBlocks hgB)

theorem PreservesWittBlocks.inv {g : Perm11}
    (hg : PreservesWittBlocks g) : PreservesWittBlocks g⁻¹ := by
  constructor
  · exact hg.2
  · exact hg.1

/-- The 11-cycle generator preserves the candidate Witt block set. -/
theorem m11a_preserves_wittBlocks : PreservesWittBlocks m11a :=
  PreservesWittBlocks.of_blockMapAt m11a m11aBlockIndex m11aInvBlockIndex
    m11a_blockMapAt m11aInv_blockMapAt

/-- The second generator preserves the candidate Witt block set. -/
theorem m11b_preserves_wittBlocks : PreservesWittBlocks m11b :=
  PreservesWittBlocks.of_blockMapAt m11b m11bBlockIndex m11bInvBlockIndex
    m11b_blockMapAt m11bInv_blockMapAt

/-- Every element of the generated subgroup preserves the candidate block set. -/
theorem M11_preserves_wittBlocks (g : M11) : PreservesWittBlocks g.1 := by
  exact Subgroup.closure_induction
    (p := fun x hx => PreservesWittBlocks x)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact m11a_preserves_wittBlocks
      · exact m11b_preserves_wittBlocks)
    PreservesWittBlocks.one
    (fun x y _ _ hx hy => PreservesWittBlocks.mul hx hy)
    (fun x _ hx => PreservesWittBlocks.inv hx)
    g.2

/-- The six points outside the fixed block `{0,1,2,3,9}`, compressed to `Fin 6`. -/
abbrev Outside : Type :=
  Fin 6

/-- Permutations of the six outside points. -/
abbrev OutsidePerm : Type :=
  Equiv.Perm Outside

/-- The pairing on outside points induced by the triple `{0,1,2}`. -/
def tau012 : OutsidePerm :=
  List.formPerm ([0, 3] : List Outside) *
    List.formPerm ([1, 2] : List Outside) *
    List.formPerm ([4, 5] : List Outside)

/-- The pairing on outside points induced by the triple `{0,1,3}`. -/
def tau013 : OutsidePerm :=
  List.formPerm ([0, 4] : List Outside) *
    List.formPerm ([1, 3] : List Outside) *
    List.formPerm ([2, 5] : List Outside)

/-- The pairing on outside points induced by the triple `{0,2,3}`. -/
def tau023 : OutsidePerm :=
  List.formPerm ([0, 1] : List Outside) *
    List.formPerm ([2, 4] : List Outside) *
    List.formPerm ([3, 5] : List Outside)

/-- The pairing on outside points induced by the triple `{1,2,3}`. -/
def tau123 : OutsidePerm :=
  List.formPerm ([0, 5] : List Outside) *
    List.formPerm ([1, 4] : List Outside) *
    List.formPerm ([2, 3] : List Outside)

/-- A product of pairings whose unique fixed point is `0`. -/
def sigma0 : OutsidePerm :=
  tau013 * tau023 * tau123 * tau012

/-- A product of pairings whose unique fixed point is `1`. -/
def sigma1 : OutsidePerm :=
  tau023 * tau123 * tau013 * tau012

/-- A product of pairings whose unique fixed point is `2`. -/
def sigma2 : OutsidePerm :=
  tau013 * tau123 * tau023 * tau012

/-- A product of pairings whose unique fixed point is `3`. -/
def sigma3 : OutsidePerm :=
  tau123 * tau023 * tau013 * tau012

/-- A product of pairings whose unique fixed point is `4`. -/
def sigma4 : OutsidePerm :=
  tau123 * tau013 * tau023 * tau012

/-- A product of pairings whose unique fixed point is `5`. -/
def sigma5 : OutsidePerm :=
  tau023 * tau013 * tau123 * tau012

set_option maxRecDepth 20000 in
/-- The product `sigma0` has exactly one fixed point. -/
theorem sigma0_fixed_iff : ∀ x : Outside, sigma0 x = x ↔ x = 0 := by
  decide

set_option maxRecDepth 20000 in
/-- The product `sigma1` has exactly one fixed point. -/
theorem sigma1_fixed_iff : ∀ x : Outside, sigma1 x = x ↔ x = 1 := by
  decide

set_option maxRecDepth 20000 in
/-- The product `sigma2` has exactly one fixed point. -/
theorem sigma2_fixed_iff : ∀ x : Outside, sigma2 x = x ↔ x = 2 := by
  decide

set_option maxRecDepth 20000 in
/-- The product `sigma3` has exactly one fixed point. -/
theorem sigma3_fixed_iff : ∀ x : Outside, sigma3 x = x ↔ x = 3 := by
  decide

set_option maxRecDepth 20000 in
/-- The product `sigma4` has exactly one fixed point. -/
theorem sigma4_fixed_iff : ∀ x : Outside, sigma4 x = x ↔ x = 4 := by
  decide

set_option maxRecDepth 20000 in
/-- The product `sigma5` has exactly one fixed point. -/
theorem sigma5_fixed_iff : ∀ x : Outside, sigma5 x = x ↔ x = 5 := by
  decide

/-- A function on the outside points commutes with an outside permutation. -/
def CommutesWithOutside (f : Outside → Outside) (τ : OutsidePerm) : Prop :=
  ∀ x, f (τ x) = τ (f x)

/-- Commutation with two outside permutations implies commutation with their product. -/
theorem CommutesWithOutside.mul {f : Outside → Outside} {σ τ : OutsidePerm}
    (hσ : CommutesWithOutside f σ) (hτ : CommutesWithOutside f τ) :
    CommutesWithOutside f (σ * τ) := by
  intro x
  simp only [CommutesWithOutside, Equiv.Perm.mul_apply] at *
  rw [hσ (τ x), hτ x]

/--
The four pairings on the six outside points have trivial common centralizer.
This is the finite core of the final four-point stabilizer argument.
-/
theorem outside_commuting_pairings_eq_id (f : Outside → Outside)
    (h012 : CommutesWithOutside f tau012)
    (h013 : CommutesWithOutside f tau013)
    (h023 : CommutesWithOutside f tau023)
    (h123 : CommutesWithOutside f tau123) :
    ∀ x, f x = x := by
  intro x
  fin_cases x
  · have hcomm : CommutesWithOutside f sigma0 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h013 h023) h123) h012
    have hfixed : sigma0 (f 0) = f 0 := by
      have h := hcomm 0
      have h0 : sigma0 0 = 0 := by decide
      simpa [h0] using h.symm
    exact (sigma0_fixed_iff (f 0)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma1 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h023 h123) h013) h012
    have hfixed : sigma1 (f 1) = f 1 := by
      have h := hcomm 1
      have h1 : sigma1 1 = 1 := by decide
      simpa [h1] using h.symm
    exact (sigma1_fixed_iff (f 1)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma2 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h013 h123) h023) h012
    have hfixed : sigma2 (f 2) = f 2 := by
      have h := hcomm 2
      have h2 : sigma2 2 = 2 := by decide
      simpa [h2] using h.symm
    exact (sigma2_fixed_iff (f 2)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma3 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h123 h023) h013) h012
    have hfixed : sigma3 (f 3) = f 3 := by
      have h := hcomm 3
      have h3 : sigma3 3 = 3 := by decide
      simpa [h3] using h.symm
    exact (sigma3_fixed_iff (f 3)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma4 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h123 h013) h023) h012
    have hfixed : sigma4 (f 4) = f 4 := by
      have h := hcomm 4
      have h4 : sigma4 4 = 4 := by decide
      simpa [h4] using h.symm
    exact (sigma4_fixed_iff (f 4)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma5 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h023 h013) h123) h012
    have hfixed : sigma5 (f 5) = f 5 := by
      have h := hcomm 5
      have h5 : sigma5 5 = 5 := by decide
      simpa [h5] using h.symm
    exact (sigma5_fixed_iff (f 5)).mp hfixed

/-- The outside coordinates as points of the degree-11 action. -/
def outsidePointList : List (Fin 11) :=
  [4, 5, 6, 7, 8, 10]

theorem outsidePointList_length : outsidePointList.length = 6 := by
  decide

/-- The embedding of the six outside coordinates back into `Fin 11`. -/
def outsidePoint (i : Outside) : Fin 11 :=
  outsidePointList.get ⟨i.1, by rw [outsidePointList_length]; exact i.2⟩

/-- Predicate for the six points outside `{0,1,2,3,9}`. -/
def IsOutsidePoint (x : Fin 11) : Prop :=
  x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 10

/-- The coordinate of a degree-11 point, used only when it is an outside point. -/
def outsideIndex (x : Fin 11) : Outside :=
  if x = 4 then 0 else
  if x = 5 then 1 else
  if x = 6 then 2 else
  if x = 7 then 3 else
  if x = 8 then 4 else 5

/-- The induced map on outside coordinates. -/
def outsideMap (g : Perm11) : Outside → Outside :=
  fun i => outsideIndex (g (outsidePoint i))

set_option maxRecDepth 20000 in
/-- Among candidate blocks, `{0,1,2,3,x}` occurs exactly for `x = 9`. -/
theorem seed_block_mem_iff : ∀ x : Fin 11,
    ({0, 1, 2, 3, x} : Block) ∈ wittBlocks ↔ x = 9 := by
  decide

set_option maxRecDepth 20000 in
/-- Every outside coordinate names an outside point. -/
theorem outsidePoint_isOutside : ∀ i : Outside, IsOutsidePoint (outsidePoint i) := by
  intro i
  unfold IsOutsidePoint outsidePoint outsidePointList
  fin_cases i <;> decide

set_option maxRecDepth 20000 in
/-- Being outside is equivalent to not being one of the five fixed-block points. -/
theorem isOutsidePoint_iff : ∀ x : Fin 11,
    IsOutsidePoint x ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 9 := by
  intro x
  unfold IsOutsidePoint
  fin_cases x <;> decide

set_option maxRecDepth 20000 in
/-- `outsideIndex` is a left inverse to `outsidePoint`. -/
theorem outsideIndex_left_inverse : ∀ i : Outside, outsideIndex (outsidePoint i) = i := by
  decide

set_option maxRecDepth 20000 in
/-- `outsidePoint` is a right inverse to `outsideIndex` on outside points. -/
theorem outsidePoint_right_inverse : ∀ x : Fin 11,
    IsOutsidePoint x → outsidePoint (outsideIndex x) = x := by
  intro x
  unfold IsOutsidePoint outsidePoint outsidePointList outsideIndex
  fin_cases x <;> decide

set_option maxRecDepth 20000 in
/-- The blocks over the triple `{0,1,2}` encode the pairing `tau012`. -/
theorem triple012_pair_mem_iff : ∀ i j : Outside,
    ({0, 1, 2, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau012 i := by
  decide

set_option maxRecDepth 20000 in
/-- The blocks over the triple `{0,1,3}` encode the pairing `tau013`. -/
theorem triple013_pair_mem_iff : ∀ i j : Outside,
    ({0, 1, 3, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau013 i := by
  decide

set_option maxRecDepth 20000 in
/-- The blocks over the triple `{0,2,3}` encode the pairing `tau023`. -/
theorem triple023_pair_mem_iff : ∀ i j : Outside,
    ({0, 2, 3, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau023 i := by
  decide

set_option maxRecDepth 20000 in
/-- The blocks over the triple `{1,2,3}` encode the pairing `tau123`. -/
theorem triple123_pair_mem_iff : ∀ i j : Outside,
    ({1, 2, 3, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau123 i := by
  decide

/-- A block-set preserving permutation that fixes `0,1,2,3` also fixes `9`. -/
theorem fixed_four_preserves_wittBlocks_fixes_nine (g : Perm11)
    (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) :
    g 9 = 9 := by
  have hB : ({0, 1, 2, 3, g 9} : Block) ∈ wittBlocks := by
    have hB0 := hg.1 ({0, 1, 2, 3, 9} : Block) (by decide)
    simpa [blockMap, h0, h1, h2, h3] using hB0
  exact (seed_block_mem_iff (g 9)).mp hB

/-- A permutation fixing `{0,1,2,3,9}` sends outside points to outside points. -/
theorem perm_maps_outsidePoint (g : Perm11)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) (i : Outside) :
    IsOutsidePoint (g (outsidePoint i)) := by
  rw [isOutsidePoint_iff]
  constructor
  · intro h
    have : g (outsidePoint i) = g 0 := by simpa [h0] using h
    have hi : outsidePoint i = 0 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.1 hi
  constructor
  · intro h
    have : g (outsidePoint i) = g 1 := by simpa [h1] using h
    have hi : outsidePoint i = 1 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.1 hi
  constructor
  · intro h
    have : g (outsidePoint i) = g 2 := by simpa [h2] using h
    have hi : outsidePoint i = 2 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.2.1 hi
  constructor
  · intro h
    have : g (outsidePoint i) = g 3 := by simpa [h3] using h
    have hi : outsidePoint i = 3 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.2.2.1 hi
  · intro h
    have : g (outsidePoint i) = g 9 := by simpa [h9] using h
    have hi : outsidePoint i = 9 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.2.2.2 hi

/-- The coordinate map agrees with the original permutation on outside points. -/
theorem outsideMap_apply (g : Perm11)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) (i : Outside) :
    outsidePoint (outsideMap g i) = g (outsidePoint i) := by
  unfold outsideMap
  exact outsidePoint_right_inverse (g (outsidePoint i))
    (perm_maps_outsidePoint g h0 h1 h2 h3 h9 i)

/-- Convert membership in the checked block finset back to membership in the block list. -/
theorem pair_block_mem_list_of_mem_blocks {B : Block} (hB : B ∈ wittBlocks) :
    B ∈ wittBlockList := by
  rw [wittBlocks] at hB
  exact List.mem_toFinset.mp hB

/-- A block-preserving fixed-four permutation commutes with `tau012` on outside points. -/
theorem outsideMap_commutes_tau012 (g : Perm11) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) :
    CommutesWithOutside (outsideMap g) tau012 := by
  intro i
  have hMemW :
      ({0, 1, 2, outsidePoint i, outsidePoint (tau012 i)} : Block) ∈ wittBlocks :=
    (triple012_pair_mem_iff i (tau012 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h9 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h9 (tau012 i)
  have hMapped :
      ({0, 1, 2, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau012 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h1, h2, ← hi, ← hit] using hImage
  exact (triple012_pair_mem_iff (outsideMap g i) (outsideMap g (tau012 i))).mp hMapped

/-- A block-preserving fixed-four permutation commutes with `tau013` on outside points. -/
theorem outsideMap_commutes_tau013 (g : Perm11) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) :
    CommutesWithOutside (outsideMap g) tau013 := by
  intro i
  have hMemW :
      ({0, 1, 3, outsidePoint i, outsidePoint (tau013 i)} : Block) ∈ wittBlocks :=
    (triple013_pair_mem_iff i (tau013 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h9 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h9 (tau013 i)
  have hMapped :
      ({0, 1, 3, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau013 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h1, h3, ← hi, ← hit] using hImage
  exact (triple013_pair_mem_iff (outsideMap g i) (outsideMap g (tau013 i))).mp hMapped

/-- A block-preserving fixed-four permutation commutes with `tau023` on outside points. -/
theorem outsideMap_commutes_tau023 (g : Perm11) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) :
    CommutesWithOutside (outsideMap g) tau023 := by
  intro i
  have hMemW :
      ({0, 2, 3, outsidePoint i, outsidePoint (tau023 i)} : Block) ∈ wittBlocks :=
    (triple023_pair_mem_iff i (tau023 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h9 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h9 (tau023 i)
  have hMapped :
      ({0, 2, 3, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau023 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h2, h3, ← hi, ← hit] using hImage
  exact (triple023_pair_mem_iff (outsideMap g i) (outsideMap g (tau023 i))).mp hMapped

/-- A block-preserving fixed-four permutation commutes with `tau123` on outside points. -/
theorem outsideMap_commutes_tau123 (g : Perm11) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h9 : g 9 = 9) :
    CommutesWithOutside (outsideMap g) tau123 := by
  intro i
  have hMemW :
      ({1, 2, 3, outsidePoint i, outsidePoint (tau123 i)} : Block) ∈ wittBlocks :=
    (triple123_pair_mem_iff i (tau123 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h9 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h9 (tau123 i)
  have hMapped :
      ({1, 2, 3, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau123 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h1, h2, h3, ← hi, ← hit] using hImage
  exact (triple123_pair_mem_iff (outsideMap g i) (outsideMap g (tau123 i))).mp hMapped

/--
Any degree-11 permutation that preserves the checked Witt blocks and fixes
`0,1,2,3` is the identity. This is the ambient final-stabilizer certificate.
-/
theorem fixed_four_preserves_wittBlocks_eq_one (g : Perm11)
    (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) :
    g = 1 := by
  have h9 := fixed_four_preserves_wittBlocks_fixes_nine g hg h0 h1 h2 h3
  have houtside := outside_commuting_pairings_eq_id (outsideMap g)
    (outsideMap_commutes_tau012 g hg h0 h1 h2 h3 h9)
    (outsideMap_commutes_tau013 g hg h0 h1 h2 h3 h9)
    (outsideMap_commutes_tau023 g hg h0 h1 h2 h3 h9)
    (outsideMap_commutes_tau123 g hg h0 h1 h2 h3 h9)
  apply Equiv.ext
  intro x
  fin_cases x
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · have hmap := houtside (0 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (0 : Outside)
    have hp : outsidePoint (0 : Outside) = 4 := by decide
    calc
      g 4 = g (outsidePoint (0 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 0) := happly.symm
      _ = outsidePoint (0 : Outside) := by rw [hmap]
      _ = 4 := hp
  · have hmap := houtside (1 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (1 : Outside)
    have hp : outsidePoint (1 : Outside) = 5 := by decide
    calc
      g 5 = g (outsidePoint (1 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 1) := happly.symm
      _ = outsidePoint (1 : Outside) := by rw [hmap]
      _ = 5 := hp
  · have hmap := houtside (2 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (2 : Outside)
    have hp : outsidePoint (2 : Outside) = 6 := by decide
    calc
      g 6 = g (outsidePoint (2 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 2) := happly.symm
      _ = outsidePoint (2 : Outside) := by rw [hmap]
      _ = 6 := hp
  · have hmap := houtside (3 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (3 : Outside)
    have hp : outsidePoint (3 : Outside) = 7 := by decide
    calc
      g 7 = g (outsidePoint (3 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 3) := happly.symm
      _ = outsidePoint (3 : Outside) := by rw [hmap]
      _ = 7 := hp
  · have hmap := houtside (4 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (4 : Outside)
    have hp : outsidePoint (4 : Outside) = 8 := by decide
    calc
      g 8 = g (outsidePoint (4 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 4) := happly.symm
      _ = outsidePoint (4 : Outside) := by rw [hmap]
      _ = 8 := hp
  · simpa using h9
  · have hmap := houtside (5 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h9 (5 : Outside)
    have hp : outsidePoint (5 : Outside) = 10 := by decide
    calc
      g 10 = g (outsidePoint (5 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 5) := happly.symm
      _ = outsidePoint (5 : Outside) := by rw [hmap]
      _ = 10 := hp

end WittDesign
end Certificates
end Sporadic
