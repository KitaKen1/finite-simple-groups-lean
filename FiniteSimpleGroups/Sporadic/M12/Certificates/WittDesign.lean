/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.GeneratedSubgroup

/-!
# Witt design certificate workspace

This file contains the certificate route for the final stabilizer step.
The 132 blocks below are candidate blocks for the large Witt design `S(5,6,12)`.
The data is not trusted: Lean checks the finite claims recorded here.

The final theorem `fixed_five_preserves_wittBlocks_eq_one` shows that any
degree-12 permutation preserving the candidate block set and fixing the five
base points `0,1,2,3,4` is the identity.
-/

namespace Sporadic
namespace M12Certificates
namespace WittDesign

/-- A block is a finite set of points in the degree-12 action. -/
abbrev Block : Type :=
  Finset (Fin 12)

/-- Candidate large Witt design blocks, in zero-based notation. -/
def wittBlockList : List Block :=
  [
    ({0, 1, 2, 3, 4, 6} : Block),
    ({0, 1, 2, 3, 5, 10} : Block),
    ({0, 1, 2, 3, 7, 8} : Block),
    ({0, 1, 2, 3, 9, 11} : Block),
    ({0, 1, 2, 4, 5, 8} : Block),
    ({0, 1, 2, 4, 7, 11} : Block),
    ({0, 1, 2, 4, 9, 10} : Block),
    ({0, 1, 2, 5, 6, 11} : Block),
    ({0, 1, 2, 5, 7, 9} : Block),
    ({0, 1, 2, 6, 7, 10} : Block),
    ({0, 1, 2, 6, 8, 9} : Block),
    ({0, 1, 2, 8, 10, 11} : Block),
    ({0, 1, 3, 4, 5, 9} : Block),
    ({0, 1, 3, 4, 7, 10} : Block),
    ({0, 1, 3, 4, 8, 11} : Block),
    ({0, 1, 3, 5, 6, 8} : Block),
    ({0, 1, 3, 5, 7, 11} : Block),
    ({0, 1, 3, 6, 7, 9} : Block),
    ({0, 1, 3, 6, 10, 11} : Block),
    ({0, 1, 3, 8, 9, 10} : Block),
    ({0, 1, 4, 5, 6, 7} : Block),
    ({0, 1, 4, 5, 10, 11} : Block),
    ({0, 1, 4, 6, 8, 10} : Block),
    ({0, 1, 4, 6, 9, 11} : Block),
    ({0, 1, 4, 7, 8, 9} : Block),
    ({0, 1, 5, 6, 9, 10} : Block),
    ({0, 1, 5, 7, 8, 10} : Block),
    ({0, 1, 5, 8, 9, 11} : Block),
    ({0, 1, 6, 7, 8, 11} : Block),
    ({0, 1, 7, 9, 10, 11} : Block),
    ({0, 2, 3, 4, 5, 11} : Block),
    ({0, 2, 3, 4, 7, 9} : Block),
    ({0, 2, 3, 4, 8, 10} : Block),
    ({0, 2, 3, 5, 6, 7} : Block),
    ({0, 2, 3, 5, 8, 9} : Block),
    ({0, 2, 3, 6, 8, 11} : Block),
    ({0, 2, 3, 6, 9, 10} : Block),
    ({0, 2, 3, 7, 10, 11} : Block),
    ({0, 2, 4, 5, 6, 9} : Block),
    ({0, 2, 4, 5, 7, 10} : Block),
    ({0, 2, 4, 6, 7, 8} : Block),
    ({0, 2, 4, 6, 10, 11} : Block),
    ({0, 2, 4, 8, 9, 11} : Block),
    ({0, 2, 5, 6, 8, 10} : Block),
    ({0, 2, 5, 7, 8, 11} : Block),
    ({0, 2, 5, 9, 10, 11} : Block),
    ({0, 2, 6, 7, 9, 11} : Block),
    ({0, 2, 7, 8, 9, 10} : Block),
    ({0, 3, 4, 5, 6, 10} : Block),
    ({0, 3, 4, 5, 7, 8} : Block),
    ({0, 3, 4, 6, 7, 11} : Block),
    ({0, 3, 4, 6, 8, 9} : Block),
    ({0, 3, 4, 9, 10, 11} : Block),
    ({0, 3, 5, 6, 9, 11} : Block),
    ({0, 3, 5, 7, 9, 10} : Block),
    ({0, 3, 5, 8, 10, 11} : Block),
    ({0, 3, 6, 7, 8, 10} : Block),
    ({0, 3, 7, 8, 9, 11} : Block),
    ({0, 4, 5, 6, 8, 11} : Block),
    ({0, 4, 5, 7, 9, 11} : Block),
    ({0, 4, 5, 8, 9, 10} : Block),
    ({0, 4, 6, 7, 9, 10} : Block),
    ({0, 4, 7, 8, 10, 11} : Block),
    ({0, 5, 6, 7, 8, 9} : Block),
    ({0, 5, 6, 7, 10, 11} : Block),
    ({0, 6, 8, 9, 10, 11} : Block),
    ({1, 2, 3, 4, 5, 7} : Block),
    ({1, 2, 3, 4, 8, 9} : Block),
    ({1, 2, 3, 4, 10, 11} : Block),
    ({1, 2, 3, 5, 6, 9} : Block),
    ({1, 2, 3, 5, 8, 11} : Block),
    ({1, 2, 3, 6, 7, 11} : Block),
    ({1, 2, 3, 6, 8, 10} : Block),
    ({1, 2, 3, 7, 9, 10} : Block),
    ({1, 2, 4, 5, 6, 10} : Block),
    ({1, 2, 4, 5, 9, 11} : Block),
    ({1, 2, 4, 6, 7, 9} : Block),
    ({1, 2, 4, 6, 8, 11} : Block),
    ({1, 2, 4, 7, 8, 10} : Block),
    ({1, 2, 5, 6, 7, 8} : Block),
    ({1, 2, 5, 7, 10, 11} : Block),
    ({1, 2, 5, 8, 9, 10} : Block),
    ({1, 2, 6, 9, 10, 11} : Block),
    ({1, 2, 7, 8, 9, 11} : Block),
    ({1, 3, 4, 5, 6, 11} : Block),
    ({1, 3, 4, 5, 8, 10} : Block),
    ({1, 3, 4, 6, 7, 8} : Block),
    ({1, 3, 4, 6, 9, 10} : Block),
    ({1, 3, 4, 7, 9, 11} : Block),
    ({1, 3, 5, 6, 7, 10} : Block),
    ({1, 3, 5, 7, 8, 9} : Block),
    ({1, 3, 5, 9, 10, 11} : Block),
    ({1, 3, 6, 8, 9, 11} : Block),
    ({1, 3, 7, 8, 10, 11} : Block),
    ({1, 4, 5, 6, 8, 9} : Block),
    ({1, 4, 5, 7, 8, 11} : Block),
    ({1, 4, 5, 7, 9, 10} : Block),
    ({1, 4, 6, 7, 10, 11} : Block),
    ({1, 4, 8, 9, 10, 11} : Block),
    ({1, 5, 6, 7, 9, 11} : Block),
    ({1, 5, 6, 8, 10, 11} : Block),
    ({1, 6, 7, 8, 9, 10} : Block),
    ({2, 3, 4, 5, 6, 8} : Block),
    ({2, 3, 4, 5, 9, 10} : Block),
    ({2, 3, 4, 6, 7, 10} : Block),
    ({2, 3, 4, 6, 9, 11} : Block),
    ({2, 3, 4, 7, 8, 11} : Block),
    ({2, 3, 5, 6, 10, 11} : Block),
    ({2, 3, 5, 7, 8, 10} : Block),
    ({2, 3, 5, 7, 9, 11} : Block),
    ({2, 3, 6, 7, 8, 9} : Block),
    ({2, 3, 8, 9, 10, 11} : Block),
    ({2, 4, 5, 6, 7, 11} : Block),
    ({2, 4, 5, 7, 8, 9} : Block),
    ({2, 4, 5, 8, 10, 11} : Block),
    ({2, 4, 6, 8, 9, 10} : Block),
    ({2, 4, 7, 9, 10, 11} : Block),
    ({2, 5, 6, 7, 9, 10} : Block),
    ({2, 5, 6, 8, 9, 11} : Block),
    ({2, 6, 7, 8, 10, 11} : Block),
    ({3, 4, 5, 6, 7, 9} : Block),
    ({3, 4, 5, 7, 10, 11} : Block),
    ({3, 4, 5, 8, 9, 11} : Block),
    ({3, 4, 6, 8, 10, 11} : Block),
    ({3, 4, 7, 8, 9, 10} : Block),
    ({3, 5, 6, 7, 8, 11} : Block),
    ({3, 5, 6, 8, 9, 10} : Block),
    ({3, 6, 7, 9, 10, 11} : Block),
    ({4, 5, 6, 7, 8, 10} : Block),
    ({4, 5, 6, 9, 10, 11} : Block),
    ({4, 6, 7, 8, 9, 11} : Block),
    ({5, 7, 8, 9, 10, 11} : Block)
  ]

/-- The candidate large Witt design blocks as a `Finset`. -/
def wittBlocks : Finset Block :=
  wittBlockList.toFinset

set_option maxRecDepth 100000 in
/-- The candidate block list has no duplicate blocks. -/
theorem wittBlockList_nodup : wittBlockList.Nodup := by
  decide

set_option maxRecDepth 100000 in
/-- The candidate block list has length 132. -/
theorem wittBlockList_length : wittBlockList.length = 132 := by
  decide

set_option maxRecDepth 100000 in
/-- The candidate block list has the expected 132 blocks. -/
theorem wittBlocks_card : wittBlocks.card = 132 := by
  rw [wittBlocks, List.toFinset_card_of_nodup wittBlockList_nodup]
  decide

/-- The block with certificate index `i`. -/
def wittBlockAt (i : Fin 132) : Block :=
  wittBlockList.get ⟨i.1, by rw [wittBlockList_length]; exact i.2⟩

/-- Every indexed candidate block belongs to `wittBlocks`. -/
theorem wittBlockAt_mem (i : Fin 132) : wittBlockAt i ∈ wittBlocks := by
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
    ∃ j : Fin 132, wittBlockList.get i = wittBlockAt j := by
  let j : Fin 132 := ⟨i.1, by simpa [wittBlockList_length] using i.2⟩
  refine ⟨j, ?_⟩
  unfold wittBlockAt
  congr

/-- Image of a block under a degree-12 permutation. -/
def blockMap (g : Perm12) (B : Block) : Block :=
  B.image g

@[simp]
theorem blockMap_one (B : Block) : blockMap (1 : Perm12) B = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_mul (g h : Perm12) (B : Block) :
    blockMap (g * h) B = blockMap g (blockMap h B) := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_inv_self (g : Perm12) (B : Block) :
    blockMap g⁻¹ (blockMap g B) = B := by
  ext x
  simp [blockMap]

@[simp]
theorem blockMap_self_inv (g : Perm12) (B : Block) :
    blockMap g (blockMap g⁻¹ B) = B := by
  ext x
  simp [blockMap]

/-- A permutation preserves the candidate Witt block set. -/
def PreservesWittBlocks (g : Perm12) : Prop :=
  (∀ B ∈ wittBlockList, blockMap g B ∈ wittBlocks) ∧
    (∀ B ∈ wittBlockList, blockMap g⁻¹ B ∈ wittBlocks)

/-- A block-index permutation certificate for the action of `m12a`. -/
def m12aBlockIndexList : List (Fin 132) :=
  [66, 0, 67, 68, 69, 70, 1, 71, 72, 2, 73, 3, 74, 4, 75, 76, 77, 78, 5, 6, 79,
    7, 8, 80, 81, 9, 10, 82, 83, 11, 84, 85, 12, 86, 87, 88, 13, 14, 89, 15,
    90, 16, 91, 17, 92, 18, 93, 19, 20, 94, 95, 96, 21, 97, 22, 23, 24, 98,
    99, 100, 25, 26, 27, 101, 28, 29, 102, 103, 30, 104, 105, 106, 31, 32, 33,
    107, 108, 109, 34, 110, 35, 36, 37, 111, 112, 38, 113, 39, 114, 40, 115,
    41, 116, 42, 117, 118, 43, 44, 45, 119, 46, 47, 120, 48, 49, 121, 122, 50,
    51, 123, 124, 52, 125, 126, 53, 54, 55, 56, 127, 57, 128, 58, 129, 59, 60,
    130, 61, 62, 63, 64, 131, 65]

/-- A block-index permutation certificate for the action of `m12a⁻¹`. -/
def m12aInvBlockIndexList : List (Fin 132) :=
  [1, 6, 9, 11, 13, 18, 19, 21, 22, 25, 26, 29, 32, 36, 37, 39, 41, 43, 45, 47,
    48, 52, 54, 55, 56, 60, 61, 62, 64, 65, 68, 72, 73, 74, 78, 80, 81, 82,
    85, 87, 89, 91, 93, 96, 97, 98, 100, 101, 103, 104, 107, 108, 111, 114,
    115, 116, 117, 119, 121, 123, 124, 126, 127, 128, 129, 131, 0, 2, 3, 4, 5,
    7, 8, 10, 12, 14, 15, 16, 17, 20, 23, 24, 27, 28, 30, 31, 33, 34, 35, 38,
    40, 42, 44, 46, 49, 50, 51, 53, 57, 58, 59, 63, 66, 67, 69, 70, 71, 75,
    76, 77, 79, 83, 84, 86, 88, 90, 92, 94, 95, 99, 102, 105, 106, 109, 110,
    112, 113, 118, 120, 122, 125, 130]

/-- A block-index permutation certificate for the action of `m12b`. -/
def m12bBlockIndexList : List (Fin 132) :=
  [25, 17, 10, 23, 15, 7, 20, 18, 0, 9, 22, 28, 12, 8, 27, 19, 3, 6, 29, 24, 1,
    16, 26, 21, 4, 13, 2, 14, 11, 5, 53, 38, 63, 36, 51, 65, 61, 46, 48, 33,
    43, 64, 58, 56, 35, 50, 41, 40, 54, 34, 45, 60, 59, 52, 31, 57, 47, 42,
    55, 30, 49, 39, 44, 32, 37, 62, 69, 94, 99, 87, 92, 82, 101, 76, 89, 84,
    74, 100, 79, 72, 71, 86, 97, 77, 91, 90, 81, 96, 75, 73, 67, 88, 98, 83,
    85, 70, 66, 80, 95, 68, 93, 78, 126, 120, 117, 129, 118, 127, 110, 105,
    115, 130, 107, 102, 125, 128, 112, 104, 123, 119, 103, 109, 122, 131, 113,
    111, 124, 116, 108, 121, 114, 106]

/-- A block-index permutation certificate for the action of `m12b⁻¹`. -/
def m12bInvBlockIndexList : List (Fin 132) :=
  [8, 20, 26, 16, 24, 29, 17, 5, 13, 9, 2, 28, 12, 25, 27, 4, 21, 1, 7, 15, 6,
    23, 10, 3, 19, 0, 22, 14, 11, 18, 59, 54, 63, 39, 49, 44, 33, 64, 31, 61,
    47, 46, 57, 40, 62, 50, 37, 56, 38, 60, 45, 34, 53, 30, 48, 58, 43, 55,
    42, 52, 51, 36, 65, 32, 41, 35, 96, 90, 99, 66, 95, 80, 79, 89, 76, 88,
    73, 83, 101, 78, 97, 86, 71, 93, 75, 94, 81, 69, 91, 74, 85, 84, 70, 100,
    67, 98, 87, 82, 92, 68, 77, 72, 113, 120, 117, 109, 131, 112, 128, 121,
    108, 125, 116, 124, 130, 110, 127, 104, 106, 119, 103, 129, 122, 118, 126,
    114, 102, 107, 115, 105, 111, 123]

/-- A block-index permutation certificate for the action of `m12c`. -/
def m12cBlockIndexList : List (Fin 132) :=
  [131, 80, 121, 64, 114, 55, 100, 45, 107, 91, 129, 21, 119, 93, 62, 116, 37,
    127, 29, 97, 111, 11, 98, 65, 123, 82, 68, 41, 52, 18, 44, 125, 95, 109,
    112, 59, 99, 16, 118, 70, 122, 27, 58, 75, 30, 7, 53, 84, 83, 106, 57,
    130, 28, 46, 71, 5, 88, 50, 42, 35, 77, 92, 14, 105, 3, 23, 108, 128, 26,
    117, 39, 54, 96, 89, 81, 43, 126, 60, 85, 103, 1, 74, 25, 48, 47, 78, 124,
    101, 56, 73, 104, 9, 61, 13, 115, 32, 72, 19, 22, 36, 6, 87, 113, 79, 90,
    63, 49, 8, 66, 33, 120, 20, 34, 102, 4, 94, 15, 69, 38, 12, 110, 2, 40,
    24, 86, 31, 76, 17, 67, 10, 51, 0]

/-- A block-index permutation certificate for the action of `m12c⁻¹`.
Since `m12c` is an involution, this list equals `m12cBlockIndexList`. -/
def m12cInvBlockIndexList : List (Fin 132) :=
  m12cBlockIndexList

set_option maxRecDepth 10000 in
theorem m12aBlockIndexList_length : m12aBlockIndexList.length = 132 := by
  decide

set_option maxRecDepth 10000 in
theorem m12aInvBlockIndexList_length : m12aInvBlockIndexList.length = 132 := by
  decide

set_option maxRecDepth 10000 in
theorem m12bBlockIndexList_length : m12bBlockIndexList.length = 132 := by
  decide

set_option maxRecDepth 10000 in
theorem m12bInvBlockIndexList_length : m12bInvBlockIndexList.length = 132 := by
  decide

set_option maxRecDepth 10000 in
theorem m12cBlockIndexList_length : m12cBlockIndexList.length = 132 := by
  decide

set_option maxRecDepth 10000 in
theorem m12cInvBlockIndexList_length : m12cInvBlockIndexList.length = 132 := by
  decide

/-- The block-index map induced by `m12a`. -/
def m12aBlockIndex (i : Fin 132) : Fin 132 :=
  m12aBlockIndexList.get ⟨i.1, by rw [m12aBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m12a⁻¹`. -/
def m12aInvBlockIndex (i : Fin 132) : Fin 132 :=
  m12aInvBlockIndexList.get ⟨i.1, by rw [m12aInvBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m12b`. -/
def m12bBlockIndex (i : Fin 132) : Fin 132 :=
  m12bBlockIndexList.get ⟨i.1, by rw [m12bBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m12b⁻¹`. -/
def m12bInvBlockIndex (i : Fin 132) : Fin 132 :=
  m12bInvBlockIndexList.get ⟨i.1, by rw [m12bInvBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m12c`. -/
def m12cBlockIndex (i : Fin 132) : Fin 132 :=
  m12cBlockIndexList.get ⟨i.1, by rw [m12cBlockIndexList_length]; exact i.2⟩

/-- The block-index map induced by `m12c⁻¹`. -/
def m12cInvBlockIndex (i : Fin 132) : Fin 132 :=
  m12cInvBlockIndexList.get ⟨i.1, by rw [m12cInvBlockIndexList_length]; exact i.2⟩

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12a`. -/
theorem m12a_blockMapAt :
    ∀ i : Fin 132, blockMap m12a (wittBlockAt i) = wittBlockAt (m12aBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12a⁻¹`. -/
theorem m12aInv_blockMapAt :
    ∀ i : Fin 132, blockMap m12a⁻¹ (wittBlockAt i) =
      wittBlockAt (m12aInvBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12b`. -/
theorem m12b_blockMapAt :
    ∀ i : Fin 132, blockMap m12b (wittBlockAt i) = wittBlockAt (m12bBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12b⁻¹`. -/
theorem m12bInv_blockMapAt :
    ∀ i : Fin 132, blockMap m12b⁻¹ (wittBlockAt i) =
      wittBlockAt (m12bInvBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12c`. -/
theorem m12c_blockMapAt :
    ∀ i : Fin 132, blockMap m12c (wittBlockAt i) = wittBlockAt (m12cBlockIndex i) := by
  decide

set_option maxHeartbeats 3200000 in
-- The indexed 132-block equality certificate is intentionally checked by computation.
set_option maxRecDepth 200000 in
/-- Lean verifies the block-index certificate for `m12c⁻¹`. -/
theorem m12cInv_blockMapAt :
    ∀ i : Fin 132, blockMap m12c⁻¹ (wittBlockAt i) =
      wittBlockAt (m12cInvBlockIndex i) := by
  decide

/--
If a permutation has a verified block-index certificate, then it sends every
listed Witt block to a listed Witt block.
-/
theorem forall_mem_blockMap_mem_of_blockMapAt (g : Perm12) (index : Fin 132 → Fin 132)
    (h : ∀ i : Fin 132, blockMap g (wittBlockAt i) = wittBlockAt (index i)) :
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
theorem PreservesWittBlocks.of_blockMapAt (g : Perm12)
    (index invIndex : Fin 132 → Fin 132)
    (h : ∀ i : Fin 132, blockMap g (wittBlockAt i) = wittBlockAt (index i))
    (hinv : ∀ i : Fin 132, blockMap g⁻¹ (wittBlockAt i) = wittBlockAt (invIndex i)) :
    PreservesWittBlocks g :=
  ⟨forall_mem_blockMap_mem_of_blockMapAt g index h,
    forall_mem_blockMap_mem_of_blockMapAt g⁻¹ invIndex hinv⟩

theorem PreservesWittBlocks.one : PreservesWittBlocks (1 : Perm12) := by
  constructor <;> intro B hB
  · rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB
  · change blockMap (1 : Perm12) B ∈ wittBlocks
    rw [blockMap_one]
    exact mem_wittBlocks_of_mem_wittBlockList hB

theorem PreservesWittBlocks.mul {g h : Perm12}
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

theorem PreservesWittBlocks.inv {g : Perm12}
    (hg : PreservesWittBlocks g) : PreservesWittBlocks g⁻¹ := by
  constructor
  · exact hg.2
  · exact hg.1

/-- The 11-cycle generator preserves the candidate Witt block set. -/
theorem m12a_preserves_wittBlocks : PreservesWittBlocks m12a :=
  PreservesWittBlocks.of_blockMapAt m12a m12aBlockIndex m12aInvBlockIndex
    m12a_blockMapAt m12aInv_blockMapAt

/-- The second generator preserves the candidate Witt block set. -/
theorem m12b_preserves_wittBlocks : PreservesWittBlocks m12b :=
  PreservesWittBlocks.of_blockMapAt m12b m12bBlockIndex m12bInvBlockIndex
    m12b_blockMapAt m12bInv_blockMapAt

/-- The third generator preserves the candidate Witt block set. -/
theorem m12c_preserves_wittBlocks : PreservesWittBlocks m12c :=
  PreservesWittBlocks.of_blockMapAt m12c m12cBlockIndex m12cInvBlockIndex
    m12c_blockMapAt m12cInv_blockMapAt

/-- Every element of the generated subgroup preserves the candidate block set. -/
theorem M12_preserves_wittBlocks (g : M12) : PreservesWittBlocks g.1 := by
  exact Subgroup.closure_induction
    (p := fun x hx => PreservesWittBlocks x)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact m12a_preserves_wittBlocks
      · exact m12b_preserves_wittBlocks
      · exact m12c_preserves_wittBlocks)
    PreservesWittBlocks.one
    (fun x y _ _ hx hy => PreservesWittBlocks.mul hx hy)
    (fun x _ hx => PreservesWittBlocks.inv hx)
    g.2

/-- The six points outside the fixed block `{0,1,2,3,4,6}`, compressed to `Fin 6`. -/
abbrev Outside : Type :=
  Fin 6

/-- Permutations of the six outside points. -/
abbrev OutsidePerm : Type :=
  Equiv.Perm Outside

/-- The pairing on outside points induced by the quadruple `{0,1,2,3}`. -/
def tau0123 : OutsidePerm :=
  List.formPerm ([0, 4] : List Outside) *
    List.formPerm ([1, 2] : List Outside) *
    List.formPerm ([3, 5] : List Outside)

/-- The pairing on outside points induced by the quadruple `{0,1,2,4}`. -/
def tau0124 : OutsidePerm :=
  List.formPerm ([0, 2] : List Outside) *
    List.formPerm ([1, 5] : List Outside) *
    List.formPerm ([3, 4] : List Outside)

/-- The pairing on outside points induced by the quadruple `{0,1,3,4}`. -/
def tau0134 : OutsidePerm :=
  List.formPerm ([0, 3] : List Outside) *
    List.formPerm ([1, 4] : List Outside) *
    List.formPerm ([2, 5] : List Outside)

/-- The pairing on outside points induced by the quadruple `{0,2,3,4}`. -/
def tau0234 : OutsidePerm :=
  List.formPerm ([0, 5] : List Outside) *
    List.formPerm ([1, 3] : List Outside) *
    List.formPerm ([2, 4] : List Outside)

/-- The pairing on outside points induced by the quadruple `{1,2,3,4}`. -/
def tau1234 : OutsidePerm :=
  List.formPerm ([0, 1] : List Outside) *
    List.formPerm ([2, 3] : List Outside) *
    List.formPerm ([4, 5] : List Outside)

/-- A product of pairings whose unique fixed point is `0`. -/
def sigma0 : OutsidePerm :=
  tau0123 * tau0124 * tau0234 * tau1234

/-- A product of pairings whose unique fixed point is `1`. -/
def sigma1 : OutsidePerm :=
  tau0123 * tau0124 * tau0134 * tau0234

/-- A product of pairings whose unique fixed point is `2`. -/
def sigma2 : OutsidePerm :=
  tau0123 * tau0124 * tau1234 * tau0234

/-- A product of pairings whose unique fixed point is `3`. -/
def sigma3 : OutsidePerm :=
  tau0123 * tau0124 * tau1234 * tau0134

/-- A product of pairings whose unique fixed point is `4`. -/
def sigma4 : OutsidePerm :=
  tau0123 * tau0124 * tau0134 * tau1234

/-- A product of pairings whose unique fixed point is `5`. -/
def sigma5 : OutsidePerm :=
  tau0123 * tau0124 * tau0234 * tau0134

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
The five pairings on the six outside points have trivial common centralizer.
This is the finite core of the final five-point stabilizer argument.
-/
theorem outside_commuting_pairings_eq_id (f : Outside → Outside)
    (h0123 : CommutesWithOutside f tau0123)
    (h0124 : CommutesWithOutside f tau0124)
    (h0134 : CommutesWithOutside f tau0134)
    (h0234 : CommutesWithOutside f tau0234)
    (h1234 : CommutesWithOutside f tau1234) :
    ∀ x, f x = x := by
  intro x
  fin_cases x
  · have hcomm : CommutesWithOutside f sigma0 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h0234) h1234
    have hfixed : sigma0 (f 0) = f 0 := by
      have h := hcomm 0
      have h0 : sigma0 0 = 0 := by decide
      simpa [h0] using h.symm
    exact (sigma0_fixed_iff (f 0)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma1 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h0134) h0234
    have hfixed : sigma1 (f 1) = f 1 := by
      have h := hcomm 1
      have h1 : sigma1 1 = 1 := by decide
      simpa [h1] using h.symm
    exact (sigma1_fixed_iff (f 1)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma2 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h1234) h0234
    have hfixed : sigma2 (f 2) = f 2 := by
      have h := hcomm 2
      have h2 : sigma2 2 = 2 := by decide
      simpa [h2] using h.symm
    exact (sigma2_fixed_iff (f 2)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma3 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h1234) h0134
    have hfixed : sigma3 (f 3) = f 3 := by
      have h := hcomm 3
      have h3 : sigma3 3 = 3 := by decide
      simpa [h3] using h.symm
    exact (sigma3_fixed_iff (f 3)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma4 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h0134) h1234
    have hfixed : sigma4 (f 4) = f 4 := by
      have h := hcomm 4
      have h4 : sigma4 4 = 4 := by decide
      simpa [h4] using h.symm
    exact (sigma4_fixed_iff (f 4)).mp hfixed
  · have hcomm : CommutesWithOutside f sigma5 :=
      CommutesWithOutside.mul
        (CommutesWithOutside.mul
          (CommutesWithOutside.mul h0123 h0124) h0234) h0134
    have hfixed : sigma5 (f 5) = f 5 := by
      have h := hcomm 5
      have h5 : sigma5 5 = 5 := by decide
      simpa [h5] using h.symm
    exact (sigma5_fixed_iff (f 5)).mp hfixed

/-- The outside coordinates as points of the degree-12 action. -/
def outsidePointList : List (Fin 12) :=
  [5, 7, 8, 9, 10, 11]

theorem outsidePointList_length : outsidePointList.length = 6 := by
  decide

/-- The embedding of the six outside coordinates back into `Fin 12`. -/
def outsidePoint (i : Outside) : Fin 12 :=
  outsidePointList.get ⟨i.1, by rw [outsidePointList_length]; exact i.2⟩

/-- Predicate for the six points outside `{0,1,2,3,4,6}`. -/
def IsOutsidePoint (x : Fin 12) : Prop :=
  x = 5 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11

/-- The coordinate of a degree-12 point, used only when it is an outside point. -/
def outsideIndex (x : Fin 12) : Outside :=
  if x = 5 then 0 else
  if x = 7 then 1 else
  if x = 8 then 2 else
  if x = 9 then 3 else
  if x = 10 then 4 else 5

/-- The induced map on outside coordinates. -/
def outsideMap (g : Perm12) : Outside → Outside :=
  fun i => outsideIndex (g (outsidePoint i))

set_option maxRecDepth 100000 in
/-- Among candidate blocks, `{0,1,2,3,4,x}` occurs exactly for `x = 6`. -/
theorem seed_block_mem_iff : ∀ x : Fin 12,
    ({0, 1, 2, 3, 4, x} : Block) ∈ wittBlocks ↔ x = 6 := by
  decide

set_option maxRecDepth 20000 in
/-- Every outside coordinate names an outside point. -/
theorem outsidePoint_isOutside : ∀ i : Outside, IsOutsidePoint (outsidePoint i) := by
  intro i
  unfold IsOutsidePoint outsidePoint outsidePointList
  fin_cases i <;> decide

set_option maxRecDepth 20000 in
/-- Being outside is equivalent to not being one of the six fixed-block points. -/
theorem isOutsidePoint_iff : ∀ x : Fin 12,
    IsOutsidePoint x ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 4 ∧ x ≠ 6 := by
  intro x
  unfold IsOutsidePoint
  fin_cases x <;> decide

set_option maxRecDepth 20000 in
/-- `outsideIndex` is a left inverse to `outsidePoint`. -/
theorem outsideIndex_left_inverse : ∀ i : Outside, outsideIndex (outsidePoint i) = i := by
  decide

set_option maxRecDepth 20000 in
/-- `outsidePoint` is a right inverse to `outsideIndex` on outside points. -/
theorem outsidePoint_right_inverse : ∀ x : Fin 12,
    IsOutsidePoint x → outsidePoint (outsideIndex x) = x := by
  intro x
  unfold IsOutsidePoint outsidePoint outsidePointList outsideIndex
  fin_cases x <;> decide

set_option maxHeartbeats 1600000 in
-- The 36-pair block-membership certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- The blocks over the quadruple `{0,1,2,3}` encode the pairing `tau0123`. -/
theorem quad0123_pair_mem_iff : ∀ i j : Outside,
    ({0, 1, 2, 3, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau0123 i := by
  decide

set_option maxHeartbeats 1600000 in
-- The 36-pair block-membership certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- The blocks over the quadruple `{0,1,2,4}` encode the pairing `tau0124`. -/
theorem quad0124_pair_mem_iff : ∀ i j : Outside,
    ({0, 1, 2, 4, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau0124 i := by
  decide

set_option maxHeartbeats 1600000 in
-- The 36-pair block-membership certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- The blocks over the quadruple `{0,1,3,4}` encode the pairing `tau0134`. -/
theorem quad0134_pair_mem_iff : ∀ i j : Outside,
    ({0, 1, 3, 4, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau0134 i := by
  decide

set_option maxHeartbeats 1600000 in
-- The 36-pair block-membership certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- The blocks over the quadruple `{0,2,3,4}` encode the pairing `tau0234`. -/
theorem quad0234_pair_mem_iff : ∀ i j : Outside,
    ({0, 2, 3, 4, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau0234 i := by
  decide

set_option maxHeartbeats 1600000 in
-- The 36-pair block-membership certificate is intentionally checked by computation.
set_option maxRecDepth 100000 in
/-- The blocks over the quadruple `{1,2,3,4}` encode the pairing `tau1234`. -/
theorem quad1234_pair_mem_iff : ∀ i j : Outside,
    ({1, 2, 3, 4, outsidePoint i, outsidePoint j} : Block) ∈ wittBlocks ↔
      j = tau1234 i := by
  decide

/-- A block-set preserving permutation that fixes `0,1,2,3,4` also fixes `6`. -/
theorem fixed_five_preserves_wittBlocks_fixes_six (g : Perm12)
    (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) (h4 : g 4 = 4) :
    g 6 = 6 := by
  have hB : ({0, 1, 2, 3, 4, g 6} : Block) ∈ wittBlocks := by
    have hB0 := hg.1 ({0, 1, 2, 3, 4, 6} : Block) (by decide)
    simpa [blockMap, h0, h1, h2, h3, h4] using hB0
  exact (seed_block_mem_iff (g 6)).mp hB

/-- A permutation fixing `{0,1,2,3,4,6}` sends outside points to outside points. -/
theorem perm_maps_outsidePoint (g : Perm12)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) (i : Outside) :
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
  constructor
  · intro h
    have : g (outsidePoint i) = g 4 := by simpa [h4] using h
    have hi : outsidePoint i = 4 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.2.2.2.1 hi
  · intro h
    have : g (outsidePoint i) = g 6 := by simpa [h6] using h
    have hi : outsidePoint i = 6 := g.injective this
    have hout := outsidePoint_isOutside i
    rw [isOutsidePoint_iff] at hout
    exact hout.2.2.2.2.2 hi

/-- The coordinate map agrees with the original permutation on outside points. -/
theorem outsideMap_apply (g : Perm12)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) (i : Outside) :
    outsidePoint (outsideMap g i) = g (outsidePoint i) := by
  unfold outsideMap
  exact outsidePoint_right_inverse (g (outsidePoint i))
    (perm_maps_outsidePoint g h0 h1 h2 h3 h4 h6 i)

/-- Convert membership in the checked block finset back to membership in the block list. -/
theorem pair_block_mem_list_of_mem_blocks {B : Block} (hB : B ∈ wittBlocks) :
    B ∈ wittBlockList := by
  rw [wittBlocks] at hB
  exact List.mem_toFinset.mp hB

/-- A block-preserving fixed-five permutation commutes with `tau0123` on outside points. -/
theorem outsideMap_commutes_tau0123 (g : Perm12) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) :
    CommutesWithOutside (outsideMap g) tau0123 := by
  intro i
  have hMemW :
      ({0, 1, 2, 3, outsidePoint i, outsidePoint (tau0123 i)} : Block) ∈ wittBlocks :=
    (quad0123_pair_mem_iff i (tau0123 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h4 h6 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h4 h6 (tau0123 i)
  have hMapped :
      ({0, 1, 2, 3, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau0123 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h1, h2, h3, ← hi, ← hit] using hImage
  exact (quad0123_pair_mem_iff (outsideMap g i) (outsideMap g (tau0123 i))).mp hMapped

/-- A block-preserving fixed-five permutation commutes with `tau0124` on outside points. -/
theorem outsideMap_commutes_tau0124 (g : Perm12) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) :
    CommutesWithOutside (outsideMap g) tau0124 := by
  intro i
  have hMemW :
      ({0, 1, 2, 4, outsidePoint i, outsidePoint (tau0124 i)} : Block) ∈ wittBlocks :=
    (quad0124_pair_mem_iff i (tau0124 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h4 h6 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h4 h6 (tau0124 i)
  have hMapped :
      ({0, 1, 2, 4, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau0124 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h1, h2, h4, ← hi, ← hit] using hImage
  exact (quad0124_pair_mem_iff (outsideMap g i) (outsideMap g (tau0124 i))).mp hMapped

/-- A block-preserving fixed-five permutation commutes with `tau0134` on outside points. -/
theorem outsideMap_commutes_tau0134 (g : Perm12) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) :
    CommutesWithOutside (outsideMap g) tau0134 := by
  intro i
  have hMemW :
      ({0, 1, 3, 4, outsidePoint i, outsidePoint (tau0134 i)} : Block) ∈ wittBlocks :=
    (quad0134_pair_mem_iff i (tau0134 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h4 h6 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h4 h6 (tau0134 i)
  have hMapped :
      ({0, 1, 3, 4, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau0134 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h1, h3, h4, ← hi, ← hit] using hImage
  exact (quad0134_pair_mem_iff (outsideMap g i) (outsideMap g (tau0134 i))).mp hMapped

/-- A block-preserving fixed-five permutation commutes with `tau0234` on outside points. -/
theorem outsideMap_commutes_tau0234 (g : Perm12) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) :
    CommutesWithOutside (outsideMap g) tau0234 := by
  intro i
  have hMemW :
      ({0, 2, 3, 4, outsidePoint i, outsidePoint (tau0234 i)} : Block) ∈ wittBlocks :=
    (quad0234_pair_mem_iff i (tau0234 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h4 h6 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h4 h6 (tau0234 i)
  have hMapped :
      ({0, 2, 3, 4, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau0234 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h0, h2, h3, h4, ← hi, ← hit] using hImage
  exact (quad0234_pair_mem_iff (outsideMap g i) (outsideMap g (tau0234 i))).mp hMapped

/-- A block-preserving fixed-five permutation commutes with `tau1234` on outside points. -/
theorem outsideMap_commutes_tau1234 (g : Perm12) (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2)
    (h3 : g 3 = 3) (h4 : g 4 = 4) (h6 : g 6 = 6) :
    CommutesWithOutside (outsideMap g) tau1234 := by
  intro i
  have hMemW :
      ({1, 2, 3, 4, outsidePoint i, outsidePoint (tau1234 i)} : Block) ∈ wittBlocks :=
    (quad1234_pair_mem_iff i (tau1234 i)).mpr rfl
  have hImage := hg.1 _ (pair_block_mem_list_of_mem_blocks hMemW)
  have hi := outsideMap_apply g h0 h1 h2 h3 h4 h6 i
  have hit := outsideMap_apply g h0 h1 h2 h3 h4 h6 (tau1234 i)
  have hMapped :
      ({1, 2, 3, 4, outsidePoint (outsideMap g i),
        outsidePoint (outsideMap g (tau1234 i))} : Block) ∈ wittBlocks := by
    simpa [blockMap, h1, h2, h3, h4, ← hi, ← hit] using hImage
  exact (quad1234_pair_mem_iff (outsideMap g i) (outsideMap g (tau1234 i))).mp hMapped

/--
Any degree-12 permutation that preserves the checked Witt blocks and fixes
`0,1,2,3,4` is the identity. This is the ambient final-stabilizer certificate.
-/
theorem fixed_five_preserves_wittBlocks_eq_one (g : Perm12)
    (hg : PreservesWittBlocks g)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) (h4 : g 4 = 4) :
    g = 1 := by
  have h6 := fixed_five_preserves_wittBlocks_fixes_six g hg h0 h1 h2 h3 h4
  have houtside := outside_commuting_pairings_eq_id (outsideMap g)
    (outsideMap_commutes_tau0123 g hg h0 h1 h2 h3 h4 h6)
    (outsideMap_commutes_tau0124 g hg h0 h1 h2 h3 h4 h6)
    (outsideMap_commutes_tau0134 g hg h0 h1 h2 h3 h4 h6)
    (outsideMap_commutes_tau0234 g hg h0 h1 h2 h3 h4 h6)
    (outsideMap_commutes_tau1234 g hg h0 h1 h2 h3 h4 h6)
  apply Equiv.ext
  intro x
  fin_cases x
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · have hmap := houtside (0 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (0 : Outside)
    have hp : outsidePoint (0 : Outside) = 5 := by decide
    calc
      g 5 = g (outsidePoint (0 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 0) := happly.symm
      _ = outsidePoint (0 : Outside) := by rw [hmap]
      _ = 5 := hp
  · simpa using h6
  · have hmap := houtside (1 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (1 : Outside)
    have hp : outsidePoint (1 : Outside) = 7 := by decide
    calc
      g 7 = g (outsidePoint (1 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 1) := happly.symm
      _ = outsidePoint (1 : Outside) := by rw [hmap]
      _ = 7 := hp
  · have hmap := houtside (2 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (2 : Outside)
    have hp : outsidePoint (2 : Outside) = 8 := by decide
    calc
      g 8 = g (outsidePoint (2 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 2) := happly.symm
      _ = outsidePoint (2 : Outside) := by rw [hmap]
      _ = 8 := hp
  · have hmap := houtside (3 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (3 : Outside)
    have hp : outsidePoint (3 : Outside) = 9 := by decide
    calc
      g 9 = g (outsidePoint (3 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 3) := happly.symm
      _ = outsidePoint (3 : Outside) := by rw [hmap]
      _ = 9 := hp
  · have hmap := houtside (4 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (4 : Outside)
    have hp : outsidePoint (4 : Outside) = 10 := by decide
    calc
      g 10 = g (outsidePoint (4 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 4) := happly.symm
      _ = outsidePoint (4 : Outside) := by rw [hmap]
      _ = 10 := hp
  · have hmap := houtside (5 : Outside)
    have happly := outsideMap_apply g h0 h1 h2 h3 h4 h6 (5 : Outside)
    have hp : outsidePoint (5 : Outside) = 11 := by decide
    calc
      g 11 = g (outsidePoint (5 : Outside)) := by rw [hp]
      _ = outsidePoint (outsideMap g 5) := happly.symm
      _ = outsidePoint (5 : Outside) := by rw [hmap]
      _ = 11 := hp

end WittDesign
end M12Certificates
end Sporadic
