/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.PointStabilizer

/-!
# Simplicity of M12

This file proves `IsSimpleGroup M12` by the classical normal-subgroup
argument, leveraging the simplicity of the point stabilizer (the embedded
`M11`, transported from the `M11` project):

Let `N` be a nontrivial normal subgroup of `M12`.

1. Two-transitivity word certificates show that `N` is transitive on the 12
   points: a conjugate of an element moving `p` can move any `u` to any `v`.
2. Orbit-stabilizer for `N` gives `|N| = 12 * |N ∩ S|`, where `S` is the
   stabilizer of the point `11`.
3. `N ∩ S` is normal in `S ≅ M11`, which is simple. Hence `N ∩ S = ⊥` or
   `S ≤ N`.
4. If `S ≤ N`, then `|N| = 12 * 7920 = 95040 = |M12|`, so `N = ⊤`.
5. If `N ∩ S = ⊥`, then `|N| = 12` and every nontrivial element of `N` moves
   the point `11`. Conjugation by stabilizer elements is transitive on the
   nontrivial elements of `N`, so they all share the same order. But Cauchy's
   theorem gives elements of order `2` and of order `3` in a group of order
   `12` — a contradiction.
-/

namespace Sporadic
namespace M12Simplicity

open M12Certificates
open M12Certificates.StabilizerChain
open M12PointStabilizer

/-! ## Two-transitivity certificates -/

/-- A permutation applied to its inverse's value. -/
theorem perm_apply_inv_self (f : Perm12) (x : Fin 12) : f (f⁻¹ x) = x :=
  Equiv.Perm.eq_inv_iff_eq.mp rfl

/-- A permutation's inverse applied to its value. -/
theorem perm_inv_apply_self (f : Perm12) (x : Fin 12) : f⁻¹ (f x) = x :=
  Equiv.Perm.inv_eq_iff_eq.mpr rfl

/-- A word certificate moving the base pair `(0, 1)` to any pair `(x, y)`. -/
theorem pair_witness_from_base (x y : Fin 12) (hxy : x ≠ y) :
    ∃ g : M12, g.1 0 = x ∧ g.1 1 = y := by
  classical
  set A := Word.toM12 (orbitZeroWord x) with hA
  have hA0 : A.1 (0 : Fin 12) = x := by
    simpa [hA] using orbitZeroWord_maps_zero x
  set z := A.1⁻¹ y with hzdef
  have hz0 : z ≠ 0 := by
    intro h
    apply hxy
    have : y = A.1 (0 : Fin 12) := by
      rw [← h, hzdef, perm_apply_inv_self]
    rw [this, hA0]
  set B := Word.toM12 (zeroStabilizerWord z) with hB
  have hBfix : B.1 (0 : Fin 12) = 0 := by
    simpa [hB] using zeroStabilizerWord_fixes_zero z hz0
  have hBone : B.1 (1 : Fin 12) = z := by
    simpa [hB] using zeroStabilizerWord_maps_one z hz0
  refine ⟨A * B, ?_, ?_⟩
  · change (A.1 * B.1) 0 = x
    rw [Equiv.Perm.mul_apply, hBfix, hA0]
  · change (A.1 * B.1) 1 = y
    rw [Equiv.Perm.mul_apply, hBone, hzdef, perm_apply_inv_self]

/-- `M12` is two-transitive: any pair goes to any pair. -/
theorem pair_witness (p q u v : Fin 12) (hpq : p ≠ q) (huv : u ≠ v) :
    ∃ g : M12, g.1 p = u ∧ g.1 q = v := by
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

/-- The word `a^n`, fixing `11` and moving `0` around the 11-cycle. -/
def aPowerWord (n : Nat) : Word :=
  List.replicate n Gen.a

set_option maxRecDepth 20000 in
/-- The `a`-power words reach every point except `11` from `0`. -/
theorem aPowerWord_maps_zero_all :
    ∀ x : Fin 12, x ≠ 11 → (Word.eval (aPowerWord x.val)) (0 : Fin 12) = x := by
  decide

set_option maxRecDepth 20000 in
/-- The `a`-power words fix the point `11`. -/
theorem aPowerWord_fixes_eleven_all :
    ∀ x : Fin 12, (Word.eval (aPowerWord x.val)) (11 : Fin 12) = 11 := by
  decide

/-- The stabilizer of `11` moves any non-`11` point to any non-`11` point. -/
theorem stab_pair_witness (p q : Fin 12) (hp : p ≠ 11) (hq : q ≠ 11) :
    ∃ s : M12, s.1 11 = 11 ∧ s.1 p = q := by
  set Wp := Word.toM12 (aPowerWord p.val) with hWp
  set Wq := Word.toM12 (aPowerWord q.val) with hWq
  have hWp0 : Wp.1 (0 : Fin 12) = p := by
    simpa [hWp] using aPowerWord_maps_zero_all p hp
  have hWp11 : Wp.1 (11 : Fin 12) = 11 := by
    simpa [hWp] using aPowerWord_fixes_eleven_all p
  have hWq0 : Wq.1 (0 : Fin 12) = q := by
    simpa [hWq] using aPowerWord_maps_zero_all q hq
  have hWq11 : Wq.1 (11 : Fin 12) = 11 := by
    simpa [hWq] using aPowerWord_fixes_eleven_all q
  have hWpInv11 : Wp.1⁻¹ (11 : Fin 12) = 11 := by
    conv_lhs => rw [← hWp11]
    exact perm_inv_apply_self _ _
  have hWpInvp : Wp.1⁻¹ p = 0 := by
    rw [← hWp0, perm_inv_apply_self]
  refine ⟨Wq * Wp⁻¹, ?_, ?_⟩
  · change (Wq.1 * Wp.1⁻¹) 11 = 11
    rw [Equiv.Perm.mul_apply, hWpInv11, hWq11]
  · change (Wq.1 * Wp.1⁻¹) p = q
    rw [Equiv.Perm.mul_apply, hWpInvp, hWq0]

/-! ## Transitivity of nontrivial normal subgroups -/

/-- A nontrivial subgroup contains an element moving some point. -/
theorem exists_moved_of_ne_bot (N : Subgroup M12) (hbot : N ≠ ⊥) :
    ∃ n ∈ N, ∃ p : Fin 12, n.1 p ≠ p := by
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

/-- A normal subgroup with a moved point moves any point to any point. -/
theorem normal_orbit_witness (N : Subgroup M12) (hN : N.Normal)
    {n : M12} (hnN : n ∈ N) {p : Fin 12} (hp : n.1 p ≠ p) (u v : Fin 12) :
    ∃ m ∈ N, m.1 u = v := by
  by_cases huv : u = v
  · exact ⟨1, N.one_mem, by simp [huv]⟩
  · obtain ⟨g, hgp, hgq⟩ := pair_witness p (n.1 p) u v (Ne.symm hp) huv
    refine ⟨g * n * g⁻¹, hN.conj_mem n hnN g, ?_⟩
    have hinv : g.1⁻¹ u = p := by
      rw [← hgp, perm_inv_apply_self]
    change (g.1 * n.1 * g.1⁻¹) u = v
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hgq]

/-- The orbit of `11` under a nontrivial normal subgroup is everything. -/
theorem normal_orbit_eleven_eq_univ (N : Subgroup M12) (hN : N.Normal)
    {n : M12} (hnN : n ∈ N) {p : Fin 12} (hp : n.1 p ≠ p) :
    MulAction.orbit N (11 : Fin 12) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨m, hmN, hmx⟩ := normal_orbit_witness N hN hnN hp 11 x
    exact ⟨⟨m, hmN⟩, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hmx⟩

/-! ## Orbit-stabilizer for the normal subgroup -/

/-- Orbit-stabilizer: a transitive subgroup has order `12 * |stabilizer|`. -/
theorem card_normal_eq_twelve_mul_stab (N : Subgroup M12)
    (horbit : MulAction.orbit N (11 : Fin 12) = Set.univ) :
    Nat.card N = 12 * Nat.card (MulAction.stabilizer N (11 : Fin 12)) := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group N (11 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard, horbit, Set.ncard_univ]
  rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer N (11 : Fin 12))]
  simp

/-- The stabilizer of `11` inside `N` matches `N` viewed inside `StabEleven`. -/
def stabInNEquiv (N : Subgroup M12) :
    MulAction.stabilizer N (11 : Fin 12) ≃* (N.subgroupOf StabEleven) where
  toFun g :=
    ⟨⟨g.1.1, by
      rw [StabEleven, MulAction.mem_stabilizer_iff]
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

/-- The two stabilizer descriptions have the same cardinality. -/
theorem card_stabInN_eq (N : Subgroup M12) :
    Nat.card (MulAction.stabilizer N (11 : Fin 12)) =
      Nat.card (N.subgroupOf StabEleven) :=
  Nat.card_congr (stabInNEquiv N).toEquiv

/-! ## The regular case is impossible -/

/-- If `N ∩ S = ⊥`, an element of `N` fixing `11` is the identity. -/
theorem eq_one_of_fixes_eleven (N : Subgroup M12)
    (hb : N.subgroupOf StabEleven = ⊥)
    {m : M12} (hmN : m ∈ N) (hfix : m.1 11 = 11) : m = 1 := by
  have hmS : m ∈ StabEleven := by
    rw [StabEleven, MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix
  have hmem : (⟨m, hmS⟩ : StabEleven) ∈ N.subgroupOf StabEleven :=
    Subgroup.mem_subgroupOf.mpr hmN
  rw [hb, Subgroup.mem_bot] at hmem
  exact Subtype.ext_iff.mp hmem

/-- If `N ∩ S = ⊥`, nontrivial elements of `N` are conjugate by stabilizer
elements. -/
theorem conj_witness (N : Subgroup M12) (hN : N.Normal)
    (hb : N.subgroupOf StabEleven = ⊥)
    {n1 n2 : M12} (h1N : n1 ∈ N) (h2N : n2 ∈ N) (h1 : n1 ≠ 1) (h2 : n2 ≠ 1) :
    ∃ s : M12, s * n1 * s⁻¹ = n2 := by
  have hp1 : n1.1 (11 : Fin 12) ≠ 11 := fun h =>
    h1 (eq_one_of_fixes_eleven N hb h1N h)
  have hp2 : n2.1 (11 : Fin 12) ≠ 11 := fun h =>
    h2 (eq_one_of_fixes_eleven N hb h2N h)
  obtain ⟨s, hs11, hsp⟩ := stab_pair_witness (n1.1 11) (n2.1 11) hp1 hp2
  refine ⟨s, ?_⟩
  have hsinv : s.1⁻¹ (11 : Fin 12) = 11 := by
    conv_lhs => rw [← hs11]
    exact perm_inv_apply_self _ _
  have hm11 : (s * n1 * s⁻¹).1 (11 : Fin 12) = n2.1 11 := by
    change (s.1 * n1.1 * s.1⁻¹) 11 = n2.1 11
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsinv, hsp]
  have hfix : (n2⁻¹ * (s * n1 * s⁻¹)).1 (11 : Fin 12) = 11 := by
    change (n2.1⁻¹ * (s * n1 * s⁻¹).1) 11 = 11
    rw [Equiv.Perm.mul_apply, hm11, perm_inv_apply_self]
  have hmem : n2⁻¹ * (s * n1 * s⁻¹) ∈ N :=
    N.mul_mem (N.inv_mem h2N) (hN.conj_mem n1 h1N s)
  have hone := eq_one_of_fixes_eleven N hb hmem hfix
  exact (inv_mul_eq_one.mp hone).symm

/-- Conjugation preserves element orders. -/
theorem orderOf_conj_eq (s x : M12) : orderOf (s * x * s⁻¹) = orderOf x := by
  have h : s * x * s⁻¹ = (MulAut.conj s) x := rfl
  rw [h]
  exact orderOf_injective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective x

/-- A normal subgroup of order 12 with all nontrivial elements conjugate is
impossible: Cauchy gives elements of order 2 and 3. -/
theorem regular_case_absurd (N : Subgroup M12) (hN : N.Normal)
    (hb : N.subgroupOf StabEleven = ⊥) (hcard : Nat.card N = 12) : False := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  have hF : Fintype.card N = 12 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨x2, hx2⟩ := exists_prime_orderOf_dvd_card (G := N) 2 (by rw [hF]; norm_num)
  obtain ⟨x3, hx3⟩ := exists_prime_orderOf_dvd_card (G := N) 3 (by rw [hF]; norm_num)
  have h2 : orderOf (x2.1 : M12) = 2 := by
    have h := orderOf_injective N.subtype N.subtype_injective x2
    rw [hx2] at h
    exact h
  have h3 : orderOf (x3.1 : M12) = 3 := by
    have h := orderOf_injective N.subtype N.subtype_injective x3
    rw [hx3] at h
    exact h
  have hx2ne : (x2.1 : M12) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    norm_num at h2
  have hx3ne : (x3.1 : M12) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h3
    norm_num at h3
  obtain ⟨s, hs⟩ := conj_witness N hN hb x2.2 x3.2 hx2ne hx3ne
  have := orderOf_conj_eq s x2.1
  rw [hs, h2, h3] at this
  norm_num at this

/-! ## Main theorem -/

/-- Every normal subgroup of `M12` is trivial or everything. -/
theorem normal_eq_bot_or_eq_top (N : Subgroup M12) (hN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨n, hnN, p, hp⟩ := exists_moved_of_ne_bot N hbot
  have horbit := normal_orbit_eleven_eq_univ N hN hnN hp
  have hcardN := card_normal_eq_twelve_mul_stab N horbit
  rw [card_stabInN_eq] at hcardN
  haveI : IsSimpleGroup StabEleven := isSimpleGroup_stabEleven
  have hnormal : (N.subgroupOf StabEleven).Normal := hN.subgroupOf StabEleven
  rcases hnormal.eq_bot_or_eq_top with hb | ht
  · exfalso
    apply regular_case_absurd N hN hb
    rw [hcardN, hb, Subgroup.card_bot]
  · have hcardS : Nat.card (N.subgroupOf StabEleven) = 7920 := by
      rw [ht, Subgroup.card_top]
      exact card_stabEleven
    have hcard : Nat.card N = Nat.card M12 := by
      rw [hcardN, hcardS, M12Cardinality.card_M12]
    exact Subgroup.eq_top_of_card_eq N hcard

/-- `M12` is nontrivial: the first generator is not the identity. -/
theorem nontrivial_M12 : Nontrivial M12 := by
  refine ⟨⟨⟨m12a, m12a_mem_M12Subgroup⟩, 1, ?_⟩⟩
  intro h
  have hperm : m12a = (1 : Perm12) := by
    simpa using congrArg Subtype.val h
  have h0 : m12a (0 : Fin 12) = 0 := by
    rw [hperm]
    rfl
  exact absurd h0 (by decide)

/-- The Mathieu group `M12` is simple. -/
theorem simple_M12 : IsSimpleGroup M12 :=
  { toNontrivial := nontrivial_M12
    eq_bot_or_eq_top_of_normal := normal_eq_bot_or_eq_top }

end M12Simplicity
end Sporadic
