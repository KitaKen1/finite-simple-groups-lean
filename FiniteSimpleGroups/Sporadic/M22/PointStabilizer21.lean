/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.L34.Simplicity
import FiniteSimpleGroups.Sporadic.M22.Cardinality
import FiniteSimpleGroups.Sporadic.M22.Certificates.LastPoint
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The stabilizer of the last point is the embedded PSL(3,4)

This file identifies the stabilizer of the point `21` in `M22` with the
embedded copy of `L34` and concludes that the point stabilizer is a simple
group of order `20160`.

The cardinality identification closes both open counts at once:
`|L34| = 420·|Stab01|` with `48 ≤ |Stab01|` (Layer 1), while the embedding
into the stabilizer (of order `443520 / 22 = 20160`) gives
`420·|Stab01| ≤ 20160`, forcing `|Stab01| = 48` and `|L34| = 20160`.
-/

namespace Sporadic
namespace M22PointStabilizer

open M22Certificates M22Certificates.LastPoint
open L34 (L34Subgroup l34e1 l34e2 l34e3 simple_L34)

/-- The stabilizer of the last point `21` in the 22-point action. -/
def StabLast : Subgroup M22 :=
  MulAction.stabilizer M22 (21 : Fin 22)

/-! ## The stabilizer has order 20160 -/

theorem orbit_last_witness (x : Fin 22) :
    ∃ g : M22, g.1 (21 : Fin 22) = x :=
  ⟨Word.toM22 (lastOrbitWord x), by simpa using lastOrbitWord_maps_all x⟩

theorem orbit_last_eq_univ : MulAction.orbit M22 (21 : Fin 22) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := orbit_last_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

theorem orbit_last_ncard : (MulAction.orbit M22 (21 : Fin 22)).ncard = 22 := by
  rw [orbit_last_eq_univ, Set.ncard_univ]
  simp

theorem card_M22_eq_22_mul_stabLast :
    Nat.card M22 = 22 * Nat.card StabLast := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M22 (21 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, orbit_last_ncard]
  rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer M22 (21 : Fin 22))]
  rfl

theorem card_stabLast : Nat.card StabLast = 20160 := by
  have h := card_M22_eq_22_mul_stabLast
  rw [M22Cardinality.card_M22] at h
  omega

/-! ## The embedding of the 21-point world -/

/-- `Fin 21` as the subtype of points of `Fin 22` below `21`. -/
def finTwentyOneEquiv : Fin 21 ≃ {x : Fin 22 // x.val < 21} where
  toFun i := ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The embedding of degree-21 permutations into degree-22 permutations,
fixing the last point. -/
def embedPerm : L34.Perm21 →* Perm22 :=
  Equiv.Perm.extendDomainHom finTwentyOneEquiv

theorem embedPerm_injective : Function.Injective embedPerm :=
  Equiv.Perm.extendDomainHom_injective finTwentyOneEquiv

/-- The embedded generators, as explicit degree-22 permutations. -/
def m22l1 : Perm22 := Word.eval embWord1

def m22l2 : Perm22 := Word.eval embWord2

def m22l3 : Perm22 := Word.eval embWord3

theorem m22l1_mem : m22l1 ∈ M22Subgroup := Word.eval_mem_M22Subgroup _

theorem m22l2_mem : m22l2 ∈ M22Subgroup := Word.eval_mem_M22Subgroup _

theorem m22l3_mem : m22l3 ∈ M22Subgroup := Word.eval_mem_M22Subgroup _

set_option maxRecDepth 400000 in
/-- The first embedded generator agrees with the word certificate. -/
theorem embedPerm_l34e1 : embedPerm l34e1 = m22l1 := by
  apply Equiv.ext
  decide

set_option maxRecDepth 400000 in
/-- The second embedded generator agrees with the word certificate. -/
theorem embedPerm_l34e2 : embedPerm l34e2 = m22l2 := by
  apply Equiv.ext
  decide

set_option maxRecDepth 400000 in
/-- The third embedded generator agrees with the word certificate. -/
theorem embedPerm_l34e3 : embedPerm l34e3 = m22l3 := by
  apply Equiv.ext
  decide

set_option maxRecDepth 40000 in
theorem m22l1_fixes_last : m22l1 (21 : Fin 22) = 21 := by
  decide

set_option maxRecDepth 40000 in
theorem m22l2_fixes_last : m22l2 (21 : Fin 22) = 21 := by
  decide

set_option maxRecDepth 40000 in
theorem m22l3_fixes_last : m22l3 (21 : Fin 22) = 21 := by
  decide

/-- The embedded copy of `L34` inside the degree-22 permutations. -/
def EmbeddedL34 : Subgroup Perm22 :=
  L34Subgroup.map embedPerm

theorem embeddedL34_eq_closure :
    EmbeddedL34 = Subgroup.closure ({m22l1, m22l2, m22l3} : Set Perm22) := by
  rw [EmbeddedL34, L34.L34Subgroup, MonoidHom.map_closure]
  congr 1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    embedPerm_l34e1, embedPerm_l34e2, embedPerm_l34e3]

/-- The embedded copy is isomorphic to `L34`. -/
noncomputable def embeddedL34Equiv : L34Subgroup ≃* EmbeddedL34 :=
  L34Subgroup.equivMapOfInjective embedPerm embedPerm_injective

theorem card_embeddedL34 : Nat.card EmbeddedL34 = Nat.card L34Subgroup := by
  rw [← Nat.card_congr embeddedL34Equiv.toEquiv]

theorem embeddedL34_le_M22Subgroup : EmbeddedL34 ≤ M22Subgroup := by
  rw [embeddedL34_eq_closure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact m22l1_mem
  · exact m22l2_mem
  · exact m22l3_mem

theorem fixes_last_of_mem_embeddedL34 {g : Perm22} (hg : g ∈ EmbeddedL34) :
    g 21 = 21 := by
  rw [embeddedL34_eq_closure] at hg
  exact Subgroup.closure_induction
    (p := fun x _ => x (21 : Fin 22) = 21)
    (fun x hx => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact m22l1_fixes_last
      · exact m22l2_fixes_last
      · exact m22l3_fixes_last)
    (by simp)
    (fun x y _ _ hx hy => by
      change (x * y) (21 : Fin 22) = 21
      rw [Equiv.Perm.mul_apply, hy, hx])
    (fun x _ hx => by
      change x⁻¹ (21 : Fin 22) = 21
      exact Equiv.Perm.inv_eq_iff_eq.mpr hx.symm)
    hg

/-- The embedded `L34`, viewed as a subgroup of `M22`. -/
def EmbeddedL34InM22 : Subgroup M22 :=
  EmbeddedL34.subgroupOf M22Subgroup

noncomputable def embeddedInM22Equiv : EmbeddedL34InM22 ≃* EmbeddedL34 :=
  Subgroup.subgroupOfEquivOfLe embeddedL34_le_M22Subgroup

theorem embeddedInM22_le_stabLast : EmbeddedL34InM22 ≤ StabLast := by
  intro g hg
  have hfix : g.1 (21 : Fin 22) = 21 :=
    fixes_last_of_mem_embeddedL34 (Subgroup.mem_subgroupOf.mp hg)
  rw [StabLast, MulAction.mem_stabilizer_iff]
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-! ## Closing the cardinality -/

theorem card_L34_le : Nat.card L34Subgroup ≤ 20160 := by
  calc Nat.card L34Subgroup
      = Nat.card EmbeddedL34 := (card_embeddedL34).symm
    _ = Nat.card EmbeddedL34InM22 := by
        rw [Nat.card_congr embeddedInM22Equiv.toEquiv]
    _ ≤ Nat.card StabLast := Subgroup.card_le_of_le embeddedInM22_le_stabLast
    _ = 20160 := card_stabLast

/-- The two-point stabilizer of `L34` has exactly 48 elements. -/
theorem card_L34_stab01 : Nat.card L34.Stab01 = 48 := by
  have hle := card_L34_le
  rw [L34.card_L34_eq_420_mul_stab01] at hle
  have hge := L34.stab01_lower
  omega

/-- The concrete `PSL(3,4)` has order `20160`. -/
theorem card_L34 : Nat.card L34Subgroup = 20160 := by
  rw [L34.card_L34_eq_420_mul_stab01, card_L34_stab01]

/-- The embedded `L34` is exactly the stabilizer of the last point. -/
theorem embeddedInM22_eq_stabLast : EmbeddedL34InM22 = StabLast := by
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le
  · exact embeddedInM22_le_stabLast
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rw [SetLike.coe_sort_coe, SetLike.coe_sort_coe]
    rw [card_stabLast, Nat.card_congr embeddedInM22Equiv.toEquiv,
      card_embeddedL34, card_L34]
  · exact Set.toFinite _

/-- The stabilizer of the last point is isomorphic to `L34`. -/
noncomputable def stabLastEquivL34 : StabLast ≃* L34Subgroup :=
  ((MulEquiv.subgroupCongr embeddedInM22_eq_stabLast).symm.trans
    embeddedInM22Equiv).trans embeddedL34Equiv.symm

/-- The stabilizer of the last point is a simple group. -/
theorem isSimpleGroup_stabLast : IsSimpleGroup StabLast := by
  haveI := simple_L34
  exact stabLastEquivL34.isSimpleGroup

end M22PointStabilizer
end Sporadic
