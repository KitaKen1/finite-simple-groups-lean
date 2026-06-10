/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.GeneratedSubgroup

/-!
# The Steiner system S(3,6,22) certificate workspace

The 77 blocks below are the candidate blocks of the large Witt design
`S(3,6,22)`. The data is not trusted: Lean checks the finite claims recorded
here, including the block-index certificates for both generators.
-/

namespace Sporadic
namespace M22Certificates
namespace SteinerSystem

/-- A block is a finite set of points in the degree-22 action. -/
abbrev Block : Type :=
  Finset (Fin 22)

/-- Candidate `S(3,6,22)` blocks, in zero-based notation. -/
def wittBlockList : List Block :=
  [
    ({0, 1, 2, 3, 4, 21} : Block),
    ({0, 1, 5, 10, 16, 19} : Block),
    ({0, 1, 6, 9, 15, 20} : Block),
    ({0, 1, 7, 12, 14, 17} : Block),
    ({0, 1, 8, 11, 13, 18} : Block),
    ({0, 2, 5, 9, 14, 18} : Block),
    ({0, 2, 6, 10, 13, 17} : Block),
    ({0, 2, 7, 11, 16, 20} : Block),
    ({0, 2, 8, 12, 15, 19} : Block),
    ({0, 3, 5, 12, 13, 20} : Block),
    ({0, 3, 6, 11, 14, 19} : Block),
    ({0, 3, 7, 10, 15, 18} : Block),
    ({0, 3, 8, 9, 16, 17} : Block),
    ({0, 4, 5, 11, 15, 17} : Block),
    ({0, 4, 6, 12, 16, 18} : Block),
    ({0, 4, 7, 9, 13, 19} : Block),
    ({0, 4, 8, 10, 14, 20} : Block),
    ({0, 5, 6, 7, 8, 21} : Block),
    ({0, 9, 10, 11, 12, 21} : Block),
    ({0, 13, 14, 15, 16, 21} : Block),
    ({0, 17, 18, 19, 20, 21} : Block),
    ({1, 2, 5, 6, 11, 12} : Block),
    ({1, 2, 7, 8, 9, 10} : Block),
    ({1, 2, 13, 14, 19, 20} : Block),
    ({1, 2, 15, 16, 17, 18} : Block),
    ({1, 3, 5, 8, 14, 15} : Block),
    ({1, 3, 6, 7, 13, 16} : Block),
    ({1, 3, 9, 12, 18, 19} : Block),
    ({1, 3, 10, 11, 17, 20} : Block),
    ({1, 4, 5, 7, 18, 20} : Block),
    ({1, 4, 6, 8, 17, 19} : Block),
    ({1, 4, 9, 11, 14, 16} : Block),
    ({1, 4, 10, 12, 13, 15} : Block),
    ({1, 5, 9, 13, 17, 21} : Block),
    ({1, 6, 10, 14, 18, 21} : Block),
    ({1, 7, 11, 15, 19, 21} : Block),
    ({1, 8, 12, 16, 20, 21} : Block),
    ({2, 3, 5, 7, 17, 19} : Block),
    ({2, 3, 6, 8, 18, 20} : Block),
    ({2, 3, 9, 11, 13, 15} : Block),
    ({2, 3, 10, 12, 14, 16} : Block),
    ({2, 4, 5, 8, 13, 16} : Block),
    ({2, 4, 6, 7, 14, 15} : Block),
    ({2, 4, 9, 12, 17, 20} : Block),
    ({2, 4, 10, 11, 18, 19} : Block),
    ({2, 5, 10, 15, 20, 21} : Block),
    ({2, 6, 9, 16, 19, 21} : Block),
    ({2, 7, 12, 13, 18, 21} : Block),
    ({2, 8, 11, 14, 17, 21} : Block),
    ({3, 4, 5, 6, 9, 10} : Block),
    ({3, 4, 7, 8, 11, 12} : Block),
    ({3, 4, 13, 14, 17, 18} : Block),
    ({3, 4, 15, 16, 19, 20} : Block),
    ({3, 5, 11, 16, 18, 21} : Block),
    ({3, 6, 12, 15, 17, 21} : Block),
    ({3, 7, 9, 14, 20, 21} : Block),
    ({3, 8, 10, 13, 19, 21} : Block),
    ({4, 5, 12, 14, 19, 21} : Block),
    ({4, 6, 11, 13, 20, 21} : Block),
    ({4, 7, 10, 16, 17, 21} : Block),
    ({4, 8, 9, 15, 18, 21} : Block),
    ({5, 6, 13, 15, 18, 19} : Block),
    ({5, 6, 14, 16, 17, 20} : Block),
    ({5, 7, 9, 12, 15, 16} : Block),
    ({5, 7, 10, 11, 13, 14} : Block),
    ({5, 8, 9, 11, 19, 20} : Block),
    ({5, 8, 10, 12, 17, 18} : Block),
    ({6, 7, 9, 11, 17, 18} : Block),
    ({6, 7, 10, 12, 19, 20} : Block),
    ({6, 8, 9, 12, 13, 14} : Block),
    ({6, 8, 10, 11, 15, 16} : Block),
    ({7, 8, 13, 15, 17, 20} : Block),
    ({7, 8, 14, 16, 18, 19} : Block),
    ({9, 10, 13, 16, 18, 20} : Block),
    ({9, 10, 14, 15, 17, 19} : Block),
    ({11, 12, 13, 16, 17, 19} : Block),
    ({11, 12, 14, 15, 18, 20} : Block)
  ]

/-- The candidate blocks as a `Finset`. -/
def wittBlocks : Finset Block :=
  wittBlockList.toFinset

set_option maxRecDepth 100000 in
/-- The candidate block list has no duplicate blocks. -/
theorem wittBlockList_nodup : wittBlockList.Nodup := by
  decide

set_option maxRecDepth 100000 in
/-- The candidate block list has length 77. -/
theorem wittBlockList_length : wittBlockList.length = 77 := by
  decide

/-- The block with certificate index `i`. -/
def wittBlockAt (i : Fin 77) : Block :=
  wittBlockList.get ⟨i.1, by rw [wittBlockList_length]; exact i.2⟩

/-- Every indexed candidate block belongs to `wittBlocks`. -/
theorem wittBlockAt_mem (i : Fin 77) : wittBlockAt i ∈ wittBlocks := by
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
    ∃ j : Fin 77, wittBlockList.get i = wittBlockAt j := by
  let j : Fin 77 := ⟨i.1, by simpa [wittBlockList_length] using i.2⟩
  refine ⟨j, ?_⟩
  unfold wittBlockAt
  congr

/-- Image of a block under a degree-22 permutation. -/
def blockMap (g : Perm22) (B : Block) : Block :=
  B.image g

@[simp]
theorem blockMap_one (B : Block) : blockMap (1 : Perm22) B = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_mul (g h : Perm22) (B : Block) :
    blockMap (g * h) B = blockMap g (blockMap h B) := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_inv_self (g : Perm22) (B : Block) :
    blockMap g⁻¹ (blockMap g B) = B := by
  ext x
  simp [blockMap]

/-- A permutation preserves the candidate block set. -/
def PreservesWittBlocks (g : Perm22) : Prop :=
  (∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks) ∧
    (∀ B ∈ wittBlockList, blockMap g⁻¹ B ∈ wittBlocks)

/-- A block-index permutation certificate for the action of `m22a`. -/
def m22aBlockIndexList : List (Fin 77) :=
  [64, 76, 10, 48, 31, 35, 67, 50, 7, 39, 58, 4, 75, 13, 21, 65, 53, 70, 44, 18, 28, 42, 72,
    55, 3, 19, 69, 23, 51, 25, 62, 57, 5, 74, 34, 16, 40, 71, 26, 15, 47, 63, 17, 37, 29, 11,
    68, 22, 59, 61, 41, 33, 9, 32, 6, 56, 73, 45, 49, 66, 1, 2, 54, 8, 60, 52, 24, 30, 38, 46,
    14, 12, 36, 27, 20, 43, 0]

/-- A block-index permutation certificate for the action of `m22a⁻¹`. -/
def m22aInvBlockIndexList : List (Fin 77) :=
  [76, 60, 61, 24, 11, 32, 54, 8, 63, 52, 2, 45, 71, 13, 70, 39, 35, 42, 19, 25, 74, 14, 47,
    27, 66, 29, 38, 73, 20, 44, 67, 4, 53, 51, 34, 5, 72, 43, 68, 9, 36, 50, 21, 75, 18, 57,
    69, 40, 3, 58, 7, 28, 65, 16, 62, 23, 55, 31, 10, 48, 64, 49, 30, 41, 0, 15, 59, 6, 46, 26,
    17, 37, 22, 56, 33, 12, 1]

/-- A block-index permutation certificate for the action of `m22b`. -/
def m22bBlockIndexList : List (Fin 77) :=
  [3, 20, 13, 6, 12, 48, 74, 62, 51, 33, 24, 30, 28, 59, 71, 67, 37, 54, 75, 43, 66, 19, 10,
    5, 16, 0, 2, 4, 1, 17, 11, 7, 15, 18, 8, 14, 9, 34, 25, 31, 23, 55, 42, 64, 72, 57, 76, 69,
    40, 35, 26, 22, 29, 36, 32, 21, 27, 47, 63, 68, 50, 60, 45, 58, 46, 53, 56, 70, 61, 39, 52,
    49, 38, 65, 44, 73, 41]

/-- A block-index permutation certificate for the action of `m22b⁻¹`. -/
def m22bInvBlockIndexList : List (Fin 77) :=
  [25, 28, 26, 0, 27, 23, 3, 31, 34, 36, 22, 30, 4, 2, 35, 32, 24, 29, 33, 21, 1, 55, 51, 40,
    10, 38, 50, 56, 12, 52, 11, 39, 54, 9, 37, 49, 53, 16, 72, 69, 48, 76, 42, 19, 74, 62, 64,
    57, 5, 71, 60, 8, 70, 65, 17, 41, 66, 45, 63, 13, 61, 68, 7, 58, 43, 73, 20, 15, 59, 47,
    67, 14, 44, 75, 6, 18, 46]

set_option maxRecDepth 10000 in
theorem m22aBlockIndexList_length : m22aBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22aInvBlockIndexList_length : m22aInvBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22bBlockIndexList_length : m22bBlockIndexList.length = 77 := by
  decide

set_option maxRecDepth 10000 in
theorem m22bInvBlockIndexList_length : m22bInvBlockIndexList.length = 77 := by
  decide

/-- The block-index map induced by `m22a`. -/
def m22aBlockIndex (i : Fin 77) : Fin 77 :=
  m22aBlockIndexList.get ⟨i.1, by rw [m22aBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22a⁻¹`. -/
def m22aInvBlockIndex (i : Fin 77) : Fin 77 :=
  m22aInvBlockIndexList.get ⟨i.1, by rw [m22aInvBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22b`. -/
def m22bBlockIndex (i : Fin 77) : Fin 77 :=
  m22bBlockIndexList.get ⟨i.1, by rw [m22bBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m22b⁻¹`. -/
def m22bInvBlockIndex (i : Fin 77) : Fin 77 :=
  m22bInvBlockIndexList.get ⟨i.1, by rw [m22bInvBlockIndexList_length]; exact i.2⟩

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22a`. -/
theorem m22a_blockMapAt :
    ∀ i : Fin 77, blockMap m22a (wittBlockAt i) = wittBlockAt (m22aBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22a⁻¹`. -/
theorem m22aInv_blockMapAt :
    ∀ i : Fin 77, blockMap m22a⁻¹ (wittBlockAt i) =
      wittBlockAt (m22aInvBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22b`. -/
theorem m22b_blockMapAt :
    ∀ i : Fin 77, blockMap m22b (wittBlockAt i) = wittBlockAt (m22bBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 77-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m22b⁻¹`. -/
theorem m22bInv_blockMapAt :
    ∀ i : Fin 77, blockMap m22b⁻¹ (wittBlockAt i) =
      wittBlockAt (m22bInvBlockIndex i) := by
  decide

/--
If a permutation has a verified block-index certificate, then it sends every
listed block to a listed block.
-/
theorem forall_mem_blockMap_mem_of_blockMapAt (g : Perm22) (index : Fin 77 → Fin 77)
    (h : ∀ i : Fin 77, blockMap g (wittBlockAt i) = wittBlockAt (index i)) :
    ∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks := by
  rw [List.forall_mem_iff_get]
  intro i
  obtain ⟨j, hget⟩ := exists_wittBlockAt_eq_get i
  rw [hget, h]
  exact wittBlockAt_mem (index j)

/--
A permutation preserves the candidate block set once both it and its inverse
have verified block-index certificates.
-/
theorem PreservesWittBlocks.of_blockMapAt (g : Perm22)
    (index invIndex : Fin 77 → Fin 77)
    (h : ∀ i : Fin 77, blockMap g (wittBlockAt i) = wittBlockAt (index i))
    (hinv : ∀ i : Fin 77, blockMap g⁻¹ (wittBlockAt i) = wittBlockAt (invIndex i)) :
    PreservesWittBlocks g :=
  ⟨forall_mem_blockMap_mem_of_blockMapAt g index h,
    forall_mem_blockMap_mem_of_blockMapAt g⁻¹ invIndex hinv⟩

theorem PreservesWittBlocks.one : PreservesWittBlocks (1 : Perm22) := by
  constructor <;> intro B hB
  · rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB
  · change blockMap (1 : Perm22) B ∈ wittBlocks
    rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB

theorem PreservesWittBlocks.mul {g h : Perm22}
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

theorem PreservesWittBlocks.inv {g : Perm22}
    (hg : PreservesWittBlocks g) : PreservesWittBlocks g⁻¹ := by
  constructor
  · exact hg.2
  · exact hg.1

/-- The first generator preserves the candidate block set. -/
theorem m22a_preserves_wittBlocks : PreservesWittBlocks m22a :=
  PreservesWittBlocks.of_blockMapAt m22a m22aBlockIndex m22aInvBlockIndex
    m22a_blockMapAt m22aInv_blockMapAt

/-- The second generator preserves the candidate block set. -/
theorem m22b_preserves_wittBlocks : PreservesWittBlocks m22b :=
  PreservesWittBlocks.of_blockMapAt m22b m22bBlockIndex m22bInvBlockIndex
    m22b_blockMapAt m22bInv_blockMapAt

/-- Every element of the generated subgroup preserves the candidate block set. -/
theorem M22_preserves_wittBlocks (g : M22) : PreservesWittBlocks g.1 := by
  exact Subgroup.closure_induction
    (p := fun x hx => PreservesWittBlocks x)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact m22a_preserves_wittBlocks
      · exact m22b_preserves_wittBlocks)
    PreservesWittBlocks.one
    (fun x y _ _ hx hy => PreservesWittBlocks.mul hx hy)
    (fun x _ hx => PreservesWittBlocks.inv hx)
    g.2

/-- The block `B0` through the first three base points. -/
def blockB0 : Block :=
  ({0, 1, 2, 3, 4, 21} : Block)

set_option maxRecDepth 100000 in
/-- The block at index `0` is `B0`. -/
theorem wittBlockAt_zero : wittBlockAt (0 : Fin 77) = blockB0 := by
  decide

set_option maxHeartbeats 1600000 in
-- The indexed 77-block uniqueness certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- `B0` is the unique listed block through `0`, `1`, and `2`, by index. -/
theorem unique_block_012 :
    ∀ i : Fin 77, (0 : Fin 22) ∈ wittBlockAt i → (1 : Fin 22) ∈ wittBlockAt i →
      (2 : Fin 22) ∈ wittBlockAt i → i = 0 := by
  decide

/-- Every listed block is an indexed block. -/
theorem mem_wittBlockList_exists_at {B : Block} (hB : B ∈ wittBlockList) :
    ∃ i : Fin 77, B = wittBlockAt i := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hB
  obtain ⟨j, hj⟩ := exists_wittBlockAt_eq_get n
  exact ⟨j, by rw [← hn, hj]⟩

/-- Membership of a point in the image block, given the point's image. -/
theorem mem_blockMap (g : Perm22) {B : Block} {x : Fin 22} (hx : x ∈ B)
    {v : Fin 22} (hv : g x = v) : v ∈ blockMap g B := by
  rw [← hv]
  exact Finset.mem_image_of_mem g hx

/-- Distinct points have distinct images. -/
theorem ne_of_value (g : Perm22) {u w : Fin 22} {e : Fin 22}
    (hu : g u = e) (hne : w ≠ u) : g w ≠ e := fun h =>
  hne (g.injective (h.trans hu.symm))

/--
A block with three known point images maps to the unique indexed block
through the images.
-/
theorem blockMap_eq_of_three (g : Perm22)
    (hpres : ∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks)
    {B B' : Block} {i₀ : Fin 77} (hBat : wittBlockAt i₀ = B)
    {x y z : Fin 22} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
    {ix iy iz : Fin 22} (hgx : g x = ix) (hgy : g y = iy) (hgz : g z = iz)
    {t : Fin 77}
    (huniq : ∀ i : Fin 77, ix ∈ wittBlockAt i → iy ∈ wittBlockAt i →
      iz ∈ wittBlockAt i → i = t)
    (hat : wittBlockAt t = B') :
    blockMap g B = B' := by
  have hBmem : B ∈ wittBlockList :=
    mem_wittBlockList_of_mem_wittBlocks (hBat ▸ wittBlockAt_mem i₀)
  obtain ⟨i, hi⟩ := mem_wittBlockList_exists_at
    (mem_wittBlockList_of_mem_wittBlocks (hpres B hBmem))
  have h1 : ix ∈ wittBlockAt i := by
    rw [← hi]
    exact mem_blockMap g hx hgx
  have h2 : iy ∈ wittBlockAt i := by
    rw [← hi]
    exact mem_blockMap g hy hgy
  have h3 : iz ∈ wittBlockAt i := by
    rw [← hi]
    exact mem_blockMap g hz hgz
  rw [hi, huniq i h1 h2 h3, hat]

/-- A member of a setwise-fixed block stays inside it. -/
theorem mem_of_blockMap_eq (g : Perm22) {B B' : Block}
    (hmap : blockMap g B = B') {w : Fin 22} (hw : w ∈ B) : g w ∈ B' := by
  rw [← hmap]
  exact Finset.mem_image_of_mem g hw

end SteinerSystem
end M22Certificates
end Sporadic
