/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.PointStabilizer21

/-!
# Simplicity of M22

The classical normal-subgroup argument, as for `M12`:

Let `N` be a nontrivial normal subgroup of `M22` and `S` the stabilizer of
the point `21` (the embedded `PSL(3,4)`, simple by `L34.simple_L34`).

1. Two-transitivity word certificates make `N` transitive on the 22 points.
2. Orbit-stabilizer: `|N| = 22 * |N ∩ S|`.
3. `N ∩ S ⊴ S` and `S` is simple, so `N ∩ S = ⊥` or `S ≤ N`.
4. If `S ≤ N`: `|N| = 22 * 20160 = 443520 = |M22|`, so `N = ⊤`.
5. If `N ∩ S = ⊥`: `|N| = 22`, all nontrivial elements of `N` are conjugate
   by stabilizer elements, hence share one order; but Cauchy gives elements
   of order `2` and of order `11` in a group of order `22` — contradiction.
-/

namespace Sporadic
namespace M22Simplicity

open M22Certificates
open M22Certificates.StabilizerChain
open M22Certificates.LastPoint
open M22PointStabilizer

/-! ## Permutation helpers -/

theorem perm_apply_inv_self (f : Perm22) (x : Fin 22) : f (f⁻¹ x) = x :=
  Equiv.Perm.eq_inv_iff_eq.mp rfl

theorem perm_inv_apply_self (f : Perm22) (x : Fin 22) : f⁻¹ (f x) = x :=
  Equiv.Perm.inv_eq_iff_eq.mpr rfl

/-! ## Two-transitivity certificates -/

theorem pair_witness_from_base (x y : Fin 22) (hxy : x ≠ y) :
    ∃ g : M22, g.1 0 = x ∧ g.1 1 = y := by
  classical
  set A := Word.toM22 (orbitZeroWord x) with hA
  have hA0 : A.1 (0 : Fin 22) = x := by
    simpa [hA] using orbitZeroWord_maps_zero_all x
  set z := A.1⁻¹ y with hzdef
  have hz0 : z ≠ 0 := by
    intro h
    apply hxy
    have : y = A.1 (0 : Fin 22) := by
      rw [← h, hzdef, perm_apply_inv_self]
    rw [this, hA0]
  set B := Word.toM22 (zeroStabilizerWord z) with hB
  have hBfix : B.1 (0 : Fin 22) = 0 := by
    simpa [hB] using zeroStabilizerWord_fixes_zero_all z hz0
  have hBone : B.1 (1 : Fin 22) = z := by
    simpa [hB] using zeroStabilizerWord_maps_one_all z hz0
  refine ⟨A * B, ?_, ?_⟩
  · change (A.1 * B.1) 0 = x
    rw [Equiv.Perm.mul_apply, hBfix, hA0]
  · change (A.1 * B.1) 1 = y
    rw [Equiv.Perm.mul_apply, hBone, hzdef, perm_apply_inv_self]

theorem pair_witness (p q u v : Fin 22) (hpq : p ≠ q) (huv : u ≠ v) :
    ∃ g : M22, g.1 p = u ∧ g.1 q = v := by
  obtain ⟨g1, h1p, h1q⟩ := pair_witness_from_base p q hpq
  obtain ⟨g2, h2u, h2v⟩ := pair_witness_from_base u v huv
  have hinvp : g1.1⁻¹ p = 0 := by
    rw [← h1p, perm_inv_apply_self]
  have hinvq : g1.1⁻¹ q = 1 := by
    rw [← h1q, perm_inv_apply_self]
  refine ⟨g2 * g1⁻¹, ?_, ?_⟩
  · change (g2.1 * g1.1⁻¹) p = u
    rw [Equiv.Perm.mul_apply, hinvp, h2u]
  · change (g2.1 * g1.1⁻¹) q = v
    rw [Equiv.Perm.mul_apply, hinvq, h2v]

/-- The stabilizer of `21` moves any non-`21` point to any non-`21` point. -/
theorem stab_pair_witness (p q : Fin 22) (hp : p ≠ 21) (hq : q ≠ 21) :
    ∃ s : M22, s.1 21 = 21 ∧ s.1 p = q := by
  set Wp := Word.toM22 (lastStabWord p) with hWp
  set Wq := Word.toM22 (lastStabWord q) with hWq
  have hWp0 : Wp.1 (0 : Fin 22) = p := by
    simpa [hWp] using lastStabWord_maps_all p hp
  have hWp21 : Wp.1 (21 : Fin 22) = 21 := by
    simpa [hWp] using lastStabWord_fixes_all p hp
  have hWq0 : Wq.1 (0 : Fin 22) = q := by
    simpa [hWq] using lastStabWord_maps_all q hq
  have hWq21 : Wq.1 (21 : Fin 22) = 21 := by
    simpa [hWq] using lastStabWord_fixes_all q hq
  have hWpInv21 : Wp.1⁻¹ (21 : Fin 22) = 21 := by
    conv_lhs => rw [← hWp21]
    exact perm_inv_apply_self _ _
  have hWpInvp : Wp.1⁻¹ p = 0 := by
    rw [← hWp0, perm_inv_apply_self]
  refine ⟨Wq * Wp⁻¹, ?_, ?_⟩
  · change (Wq.1 * Wp.1⁻¹) 21 = 21
    rw [Equiv.Perm.mul_apply, hWpInv21, hWq21]
  · change (Wq.1 * Wp.1⁻¹) p = q
    rw [Equiv.Perm.mul_apply, hWpInvp, hWq0]

/-! ## Transitivity of nontrivial normal subgroups -/

theorem exists_moved_of_ne_bot (N : Subgroup M22) (hbot : N ≠ ⊥) :
    ∃ n ∈ N, ∃ p : Fin 22, n.1 p ≠ p := by
  by_contra h
  push Not at h
  apply hbot
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Equiv.ext
  intro p
  simpa using h n hn p

theorem normal_orbit_witness (N : Subgroup M22) (hN : N.Normal)
    {n : M22} (hnN : n ∈ N) {p : Fin 22} (hp : n.1 p ≠ p) (u v : Fin 22) :
    ∃ m ∈ N, m.1 u = v := by
  by_cases huv : u = v
  · exact ⟨1, N.one_mem, by simp [huv]⟩
  · obtain ⟨g, hgp, hgq⟩ := pair_witness p (n.1 p) u v (Ne.symm hp) huv
    refine ⟨g * n * g⁻¹, hN.conj_mem n hnN g, ?_⟩
    have hinv : g.1⁻¹ u = p := by
      rw [← hgp, perm_inv_apply_self]
    change (g.1 * n.1 * g.1⁻¹) u = v
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hgq]

theorem normal_orbit_last_eq_univ (N : Subgroup M22) (hN : N.Normal)
    {n : M22} (hnN : n ∈ N) {p : Fin 22} (hp : n.1 p ≠ p) :
    MulAction.orbit N (21 : Fin 22) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨m, hmN, hmx⟩ := normal_orbit_witness N hN hnN hp 21 x
    exact ⟨⟨m, hmN⟩, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hmx⟩

/-! ## Orbit-stabilizer for the normal subgroup -/

theorem card_normal_eq_22_mul_stab (N : Subgroup M22)
    (horbit : MulAction.orbit N (21 : Fin 22) = Set.univ) :
    Nat.card N = 22 * Nat.card (MulAction.stabilizer N (21 : Fin 22)) := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group N (21 : Fin 22)]
  rw [Set.fintypeCard_eq_ncard, horbit, Set.ncard_univ]
  rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer N (21 : Fin 22))]
  simp

/-- The stabilizer of `21` inside `N` matches `N` viewed inside `StabLast`. -/
def stabInNEquiv (N : Subgroup M22) :
    MulAction.stabilizer N (21 : Fin 22) ≃* (N.subgroupOf StabLast) where
  toFun g :=
    ⟨⟨g.1.1, by
      rw [StabLast, MulAction.mem_stabilizer_iff]
      have hg := MulAction.mem_stabilizer_iff.mp g.2
      simpa [Subgroup.smul_def] using hg⟩,
    Subgroup.mem_subgroupOf.mpr g.1.2⟩
  invFun g :=
    ⟨⟨g.1.1, Subgroup.mem_subgroupOf.mp g.2⟩, by
      rw [MulAction.mem_stabilizer_iff]
      have hg := MulAction.mem_stabilizer_iff.mp g.1.2
      simpa [Subgroup.smul_def] using hg⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_stabInN_eq (N : Subgroup M22) :
    Nat.card (MulAction.stabilizer N (21 : Fin 22)) =
      Nat.card (N.subgroupOf StabLast) :=
  Nat.card_congr (stabInNEquiv N).toEquiv

/-! ## The regular case is impossible -/

theorem eq_one_of_fixes_last (N : Subgroup M22)
    (hb : N.subgroupOf StabLast = ⊥)
    {m : M22} (hmN : m ∈ N) (hfix : m.1 21 = 21) : m = 1 := by
  have hmS : m ∈ StabLast := by
    rw [StabLast, MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix
  have hmem : (⟨m, hmS⟩ : StabLast) ∈ N.subgroupOf StabLast :=
    Subgroup.mem_subgroupOf.mpr hmN
  rw [hb, Subgroup.mem_bot] at hmem
  exact Subtype.ext_iff.mp hmem

theorem conj_witness (N : Subgroup M22) (hN : N.Normal)
    (hb : N.subgroupOf StabLast = ⊥)
    {n1 n2 : M22} (h1N : n1 ∈ N) (h2N : n2 ∈ N) (h1 : n1 ≠ 1) (h2 : n2 ≠ 1) :
    ∃ s : M22, s * n1 * s⁻¹ = n2 := by
  have hp1 : n1.1 (21 : Fin 22) ≠ 21 := fun h =>
    h1 (eq_one_of_fixes_last N hb h1N h)
  have hp2 : n2.1 (21 : Fin 22) ≠ 21 := fun h =>
    h2 (eq_one_of_fixes_last N hb h2N h)
  obtain ⟨s, hs21, hsp⟩ := stab_pair_witness (n1.1 21) (n2.1 21) hp1 hp2
  refine ⟨s, ?_⟩
  have hsinv : s.1⁻¹ (21 : Fin 22) = 21 := by
    conv_lhs => rw [← hs21]
    exact perm_inv_apply_self _ _
  have hm21 : (s * n1 * s⁻¹).1 (21 : Fin 22) = n2.1 21 := by
    change (s.1 * n1.1 * s.1⁻¹) 21 = n2.1 21
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsinv, hsp]
  have hfix : (n2⁻¹ * (s * n1 * s⁻¹)).1 (21 : Fin 22) = 21 := by
    change (n2.1⁻¹ * (s * n1 * s⁻¹).1) 21 = 21
    rw [Equiv.Perm.mul_apply, hm21, perm_inv_apply_self]
  have hmem : n2⁻¹ * (s * n1 * s⁻¹) ∈ N :=
    N.mul_mem (N.inv_mem h2N) (hN.conj_mem n1 h1N s)
  have hone := eq_one_of_fixes_last N hb hmem hfix
  exact (inv_mul_eq_one.mp hone).symm

theorem orderOf_conj_eq (s x : M22) : orderOf (s * x * s⁻¹) = orderOf x := by
  have h : s * x * s⁻¹ = (MulAut.conj s) x := rfl
  rw [h]
  exact orderOf_injective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective x

theorem regular_case_absurd (N : Subgroup M22) (hN : N.Normal)
    (hb : N.subgroupOf StabLast = ⊥) (hcard : Nat.card N = 22) : False := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hF : Fintype.card N = 22 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨x2, hx2⟩ := exists_prime_orderOf_dvd_card (G := N) 2 (by rw [hF]; norm_num)
  obtain ⟨x11, hx11⟩ :=
    exists_prime_orderOf_dvd_card (G := N) 11 (by rw [hF]; norm_num)
  have h2 : orderOf (x2.1 : M22) = 2 := by
    have h := orderOf_injective N.subtype N.subtype_injective x2
    rw [hx2] at h
    exact h
  have h11 : orderOf (x11.1 : M22) = 11 := by
    have h := orderOf_injective N.subtype N.subtype_injective x11
    rw [hx11] at h
    exact h
  have hx2ne : (x2.1 : M22) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    norm_num at h2
  have hx11ne : (x11.1 : M22) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h11
    norm_num at h11
  obtain ⟨s, hs⟩ := conj_witness N hN hb x2.2 x11.2 hx2ne hx11ne
  have := orderOf_conj_eq s x2.1
  rw [hs, h2, h11] at this
  norm_num at this

/-! ## Main theorem -/

theorem normal_eq_bot_or_eq_top (N : Subgroup M22) (hN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨n, hnN, p, hp⟩ := exists_moved_of_ne_bot N hbot
  have horbit := normal_orbit_last_eq_univ N hN hnN hp
  have hcardN := card_normal_eq_22_mul_stab N horbit
  rw [card_stabInN_eq] at hcardN
  haveI : IsSimpleGroup StabLast := isSimpleGroup_stabLast
  have hnormal : (N.subgroupOf StabLast).Normal := hN.subgroupOf StabLast
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply regular_case_absurd N hN hb
    rw [hcardN, hb, Subgroup.card_bot]
  · have hcardS : Nat.card (N.subgroupOf StabLast) = 20160 := by
      rw [ht, Subgroup.card_top]
      exact card_stabLast
    have hcard : Nat.card N = Nat.card M22 := by
      rw [hcardN, hcardS, M22Cardinality.card_M22]
    exact Subgroup.eq_top_of_card_eq N hcard

set_option maxRecDepth 20000 in
theorem m22a_ne_one : m22a ≠ 1 := by
  intro h
  have h0 : m22a (0 : Fin 22) = 0 := by
    rw [h]
    rfl
  exact absurd h0 (by decide)

theorem nontrivial_M22 : Nontrivial M22 := by
  refine ⟨⟨⟨m22a, m22a_mem_M22Subgroup⟩, 1, ?_⟩⟩
  intro h
  exact m22a_ne_one (by simpa using congrArg Subtype.val h)

/-- The Mathieu group `M22` is simple. -/
theorem simple_M22 : IsSimpleGroup M22 :=
  { toNontrivial := nontrivial_M22
    eq_bot_or_eq_top_of_normal := normal_eq_bot_or_eq_top }

end M22Simplicity
end Sporadic
