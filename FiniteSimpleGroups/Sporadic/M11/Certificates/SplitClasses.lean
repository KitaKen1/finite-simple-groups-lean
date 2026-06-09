/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import FiniteSimpleGroups.Sporadic.M11.Certificates.ClassPartition

/-!
# Split conjugacy-class certificates

This file proves the first non-conjugacy certificate for same-order rows in the
class table. The `11A/11B` split is certified by parity: an explicit ambient
conjugator from the 11A representative to the 11B representative is odd, while
the centralizer of the 11-cycle `m11a` is contained in the ambient alternating
group.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

open scoped Function

set_option maxRecDepth 100000 in
/-- The 11A representative is the explicit generator `m11a` as an ambient permutation. -/
theorem representativePerm_rep11AIndex_eq_m11a :
    representativePerm rep11AIndex = m11a := by
  decide

/-- The 11B representative, coerced from `M11`, is the stored ambient representative. -/
theorem rep11BM11_val : (rep11BM11 : Perm11) = rep11BPerm :=
  rfl

/-- A class representative coerced from `M11` has the stored ambient permutation value. -/
theorem representativeM11_val (i : Fin 10) :
    (representativeM11 i : Perm11) = representativePerm i :=
  rfl

/-- The 11A representative, coerced from `M11`, is the stored ambient generator. -/
theorem representativeM11_rep11AIndex_val :
    (representativeM11 rep11AIndex : Perm11) = m11a := by
  exact representativePerm_rep11AIndex_eq_m11a

/--
An explicit odd ambient conjugator carrying the 11A representative `m11a` to the
11B representative. In cycle notation this is `(4 5 9 10 6 8)` on zero-based
points, fixing the other five points.
-/
abbrev rep11ABOddConjugator : Perm11 :=
  List.formPerm ([4, 5, 9, 10, 6, 8] : List (Fin 11))

set_option maxRecDepth 100000 in
/-- The displayed odd ambient conjugator sends the 11A representative to 11B. -/
theorem rep11ABOddConjugator_conj :
    rep11ABOddConjugator * m11a * rep11ABOddConjugator⁻¹ = rep11BPerm := by
  decide

set_option maxRecDepth 100000 in
/-- The displayed ambient conjugator is odd. -/
theorem rep11ABOddConjugator_sign :
    Equiv.Perm.sign rep11ABOddConjugator = -1 := by
  decide

set_option maxRecDepth 100000 in
/-- The generator `m11a` is an 11-cycle, expressed via its cycle type. -/
theorem m11a_cycleType : m11a.cycleType = {11} := by
  decide

set_option maxRecDepth 100000 in
/-- The ambient centralizer of `m11a` is contained in the ambient alternating group. -/
theorem m11a_centralizer_le_alternating :
    Subgroup.centralizer ({m11a} : Set Perm11) ≤ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.centralizer_le_alternating_iff]
  rw [m11a_cycleType]
  constructor
  · intro c hc
    have hc11 : c = 11 := by
      simpa using hc
    subst c
    exact ⟨5, rfl⟩
  · constructor
    · decide
    · intro i
      by_cases hi : i = 11
      · subst i
        simp
      · simp [hi]

set_option maxHeartbeats 2000000 in
-- The proof combines a finite parity certificate with a short group calculation.
set_option maxRecDepth 100000 in
/-- The two order-11 rows `11A` and `11B` are not conjugate inside `M11`. -/
theorem rep11A_rep11B_not_isConj :
    ¬ IsConj (representativeM11 rep11AIndex) rep11BM11 := by
  intro h
  rcases isConj_iff.mp h with ⟨g, hg⟩
  have hperm0 := congrArg (fun z : M11 => (z : Perm11)) hg
  have hperm : g.1 * m11a * g.1⁻¹ = rep11BPerm := by
    simpa [representativeM11_rep11AIndex_val, rep11BM11_val] using hperm0
  have hcback : rep11ABOddConjugator⁻¹ * rep11BPerm * rep11ABOddConjugator = m11a := by
    rw [← rep11ABOddConjugator_conj]
    simp [mul_assoc]
  have hzconj :
      (rep11ABOddConjugator⁻¹ * g.1) * m11a *
          (rep11ABOddConjugator⁻¹ * g.1)⁻¹ = m11a := by
    calc
      (rep11ABOddConjugator⁻¹ * g.1) * m11a * (rep11ABOddConjugator⁻¹ * g.1)⁻¹
          = rep11ABOddConjugator⁻¹ * (g.1 * m11a * g.1⁻¹) *
              rep11ABOddConjugator := by
            simp [mul_assoc]
      _ = rep11ABOddConjugator⁻¹ * rep11BPerm * rep11ABOddConjugator := by
            rw [hperm]
      _ = m11a := hcback
  have hzcent :
      rep11ABOddConjugator⁻¹ * g.1 ∈ Subgroup.centralizer ({m11a} : Set Perm11) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzmul :=
      congrArg (fun z : Perm11 => z * (rep11ABOddConjugator⁻¹ * g.1)) hzconj
    simpa [mul_assoc] using hzmul
  have hzAlt : rep11ABOddConjugator⁻¹ * g.1 ∈ alternatingGroup (Fin 11) :=
    m11a_centralizer_le_alternating hzcent
  have hzsign1 : Equiv.Perm.sign (rep11ABOddConjugator⁻¹ * g.1) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp hzAlt
  have hgAlt : g.1 ∈ alternatingGroup (Fin 11) :=
    M11_toPerm_mem_alternatingGroup g
  have hgsign : Equiv.Perm.sign g.1 = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp hgAlt
  have hzsignNeg : Equiv.Perm.sign (rep11ABOddConjugator⁻¹ * g.1) = -1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, rep11ABOddConjugator_sign, hgsign]
    norm_num
  rw [hzsign1] at hzsignNeg
  norm_num at hzsignNeg

/-!
## The 8A/8B split

The two order-8 representatives are conjugate in the ambient alternating group,
so parity is not enough. We enumerate the 16 ambient conjugators and check that
none preserves the small Witt block system. Since every `M11` element preserves
that block system, no `M11` conjugator can exist.
-/

/-- The 8-cycle part of the 8B representative. -/
abbrev rep8BLongCycle : Perm11 :=
  List.formPerm ([3, 7, 5, 8, 9, 4, 6, 10] : List (Fin 11))

/-- The transposition support shared by the 8A and 8B representatives. -/
abbrev rep8Swap12 : Perm11 :=
  Equiv.swap (1 : Fin 11) (2 : Fin 11)

/-- A base ambient conjugator from 8A to 8B. -/
abbrev rep8ABBaseConjugator : Perm11 :=
  Equiv.swap (4 : Fin 11) (7 : Fin 11) *
    Equiv.swap (8 : Fin 11) (10 : Fin 11)

/--
The 16 ambient conjugators from the 8A representative to the 8B representative.
The parameter `k` rotates the 8-cycle image, and `s` chooses the orientation of
the 2-cycle support.
-/
def rep8ABConjugator (k : Fin 8) (s : Fin 2) : Perm11 :=
  rep8BLongCycle ^ k.1 * rep8Swap12 ^ s.1 * rep8ABBaseConjugator

set_option maxRecDepth 100000 in
/-- Each displayed 8A-to-8B candidate is an ambient conjugator. -/
theorem rep8ABConjugator_conj (k : Fin 8) (s : Fin 2) :
    rep8ABConjugator k s * representativePerm rep8AIndex *
        (rep8ABConjugator k s)⁻¹ = representativePerm rep8BIndex := by
  fin_cases k <;> fin_cases s <;> decide

set_option maxHeartbeats 2000000 in
-- This finite sieve checks 16 candidates against the 66 listed Witt blocks.
set_option maxRecDepth 100000 in
/-- No displayed 8A-to-8B ambient conjugator preserves the Witt blocks. -/
theorem rep8ABConjugator_wittBlockPreservationCheck_false (k : Fin 8) (s : Fin 2) :
    wittBlockPreservationCheck (rep8ABConjugator k s) = false := by
  fin_cases k <;> fin_cases s <;> decide

set_option maxRecDepth 100000 in
/-- Each displayed 8A-to-8B ambient conjugator fixes the unique fixed point `0`. -/
theorem rep8ABConjugator_apply_zero (k : Fin 8) (s : Fin 2) :
    rep8ABConjugator k s (0 : Fin 11) = 0 := by
  fin_cases k <;> fin_cases s <;> decide

set_option maxHeartbeats 2000000 in
-- The proof propagates the images of `1` and `3` around the 2-cycle and 8-cycle.
set_option maxRecDepth 100000 in
/--
An ambient 8A-to-8B conjugator is determined by the image of `1` and the image
of `3`.
-/
theorem rep8ABConjugator_eq_of_conj_of_images (g : Perm11)
    (hconj : g * representativePerm rep8AIndex * g⁻¹ = representativePerm rep8BIndex)
    (k : Fin 8) (s : Fin 2)
    (h1 : g (1 : Fin 11) = rep8ABConjugator k s (1 : Fin 11))
    (h3 : g (3 : Fin 11) = rep8ABConjugator k s (3 : Fin 11)) :
    g = rep8ABConjugator k s := by
  have hstep : ∀ x : Fin 11,
      g (representativePerm rep8AIndex x) = representativePerm rep8BIndex (g x) := by
    intro x
    have happly := congrArg (fun p : Perm11 => p (g x)) hconj
    simpa using happly
  have h0 : g (0 : Fin 11) = rep8ABConjugator k s (0 : Fin 11) := by
    have hg0 : g (0 : Fin 11) = 0 := by
      have hfix := hstep (0 : Fin 11)
      change g (0 : Fin 11) = representativePerm rep8BIndex (g (0 : Fin 11)) at hfix
      generalize h0v : g (0 : Fin 11) = y at hfix ⊢
      fin_cases y <;> first | rfl | (exfalso; revert hfix; decide)
    rw [rep8ABConjugator_apply_zero]
    exact hg0
  have h2 : g (2 : Fin 11) = rep8ABConjugator k s (2 : Fin 11) := by
    have h := hstep (1 : Fin 11)
    rw [h1] at h
    change g (representativePerm rep8AIndex (1 : Fin 11)) =
      rep8ABConjugator k s (2 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h4 : g (4 : Fin 11) = rep8ABConjugator k s (4 : Fin 11) := by
    have h := hstep (3 : Fin 11)
    rw [h3] at h
    change g (representativePerm rep8AIndex (3 : Fin 11)) =
      rep8ABConjugator k s (4 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h5 : g (5 : Fin 11) = rep8ABConjugator k s (5 : Fin 11) := by
    have h := hstep (4 : Fin 11)
    rw [h4] at h
    change g (representativePerm rep8AIndex (4 : Fin 11)) =
      rep8ABConjugator k s (5 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h10 : g (10 : Fin 11) = rep8ABConjugator k s (10 : Fin 11) := by
    have h := hstep (5 : Fin 11)
    rw [h5] at h
    change g (representativePerm rep8AIndex (5 : Fin 11)) =
      rep8ABConjugator k s (10 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h9 : g (9 : Fin 11) = rep8ABConjugator k s (9 : Fin 11) := by
    have h := hstep (10 : Fin 11)
    rw [h10] at h
    change g (representativePerm rep8AIndex (10 : Fin 11)) =
      rep8ABConjugator k s (9 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h7 : g (7 : Fin 11) = rep8ABConjugator k s (7 : Fin 11) := by
    have h := hstep (9 : Fin 11)
    rw [h9] at h
    change g (representativePerm rep8AIndex (9 : Fin 11)) =
      rep8ABConjugator k s (7 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h6 : g (6 : Fin 11) = rep8ABConjugator k s (6 : Fin 11) := by
    have h := hstep (7 : Fin 11)
    rw [h7] at h
    change g (representativePerm rep8AIndex (7 : Fin 11)) =
      rep8ABConjugator k s (6 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  have h8 : g (8 : Fin 11) = rep8ABConjugator k s (8 : Fin 11) := by
    have h := hstep (6 : Fin 11)
    rw [h6] at h
    change g (representativePerm rep8AIndex (6 : Fin 11)) =
      rep8ABConjugator k s (8 : Fin 11)
    rw [h]
    fin_cases k <;> fin_cases s <;> decide
  apply Equiv.ext
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

set_option maxHeartbeats 1000000 in
-- The fixed point of the 8B representative is unique.
set_option maxRecDepth 100000 in
/-- An ambient 8A-to-8B conjugator sends the fixed point `0` to `0`. -/
theorem rep8_conj_maps_zero (g : Perm11)
    (hconj : g * representativePerm rep8AIndex * g⁻¹ = representativePerm rep8BIndex) :
    g (0 : Fin 11) = 0 := by
  have hstep : ∀ x : Fin 11,
      g (representativePerm rep8AIndex x) = representativePerm rep8BIndex (g x) := by
    intro x
    have happly := congrArg (fun p : Perm11 => p (g x)) hconj
    simpa using happly
  have hfix := hstep (0 : Fin 11)
  change g (0 : Fin 11) = representativePerm rep8BIndex (g (0 : Fin 11)) at hfix
  generalize h0v : g (0 : Fin 11) = y at hfix ⊢
  fin_cases y <;> first | rfl | (exfalso; revert hfix; decide)

set_option maxHeartbeats 1000000 in
-- The image of the 2-cycle support is the 2-cycle support.
set_option maxRecDepth 100000 in
/-- An ambient 8A-to-8B conjugator sends `1` into the 2-cycle support `{1,2}`. -/
theorem rep8_conj_maps_one_or_two (g : Perm11)
    (hconj : g * representativePerm rep8AIndex * g⁻¹ = representativePerm rep8BIndex) :
    g (1 : Fin 11) = 1 ∨ g (1 : Fin 11) = 2 := by
  have hstep : ∀ x : Fin 11,
      g (representativePerm rep8AIndex x) = representativePerm rep8BIndex (g x) := by
    intro x
    have happly := congrArg (fun p : Perm11 => p (g x)) hconj
    simpa using happly
  have h12 := hstep (1 : Fin 11)
  have h21 := hstep (2 : Fin 11)
  change g (2 : Fin 11) = representativePerm rep8BIndex (g (1 : Fin 11)) at h12
  change g (1 : Fin 11) = representativePerm rep8BIndex (g (2 : Fin 11)) at h21
  have hsq : representativePerm rep8BIndex (representativePerm rep8BIndex (g (1 : Fin 11))) =
      g (1 : Fin 11) := by
    rw [h12] at h21
    exact h21.symm
  have hnotfix : representativePerm rep8BIndex (g (1 : Fin 11)) ≠ g (1 : Fin 11) := by
    intro hfix
    have hg2g1 : g (2 : Fin 11) = g (1 : Fin 11) := by
      rw [hfix] at h12
      exact h12
    have hbad : (2 : Fin 11) = 1 := g.injective hg2g1
    exact (by decide : (2 : Fin 11) ≠ 1) hbad
  generalize hy : g (1 : Fin 11) = y at hsq hnotfix ⊢
  fin_cases y
  · exfalso; apply hnotfix; decide
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide
  · exfalso; revert hsq; decide

set_option maxHeartbeats 4000000 in
-- The finite split into 16 possible images of `1` and `3` is the exhaustiveness certificate.
set_option maxRecDepth 100000 in
/-- Every ambient 8A-to-8B conjugator is one of the 16 displayed candidates. -/
theorem rep8ABConjugator_exists_of_conj (g : Perm11)
    (hconj : g * representativePerm rep8AIndex * g⁻¹ = representativePerm rep8BIndex) :
    ∃ k : Fin 8, ∃ s : Fin 2, g = rep8ABConjugator k s := by
  have hstep : ∀ x : Fin 11,
      g (representativePerm rep8AIndex x) = representativePerm rep8BIndex (g x) := by
    intro x
    have happly := congrArg (fun p : Perm11 => p (g x)) hconj
    simpa using happly
  have h0 := rep8_conj_maps_zero g hconj
  rcases rep8_conj_maps_one_or_two g hconj with h1 | h1
  · have h2 : g (2 : Fin 11) = 2 := by
      have h12 := hstep (1 : Fin 11)
      change g (2 : Fin 11) = representativePerm rep8BIndex (g (1 : Fin 11)) at h12
      rw [h1] at h12
      rw [h12]
      decide
    generalize h3v : g (3 : Fin 11) = y at ⊢
    fin_cases y
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 0) (g.injective (by rw [h3v, h0]; decide))
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 1) (g.injective (by rw [h3v, h1]; decide))
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 2) (g.injective (by rw [h3v, h2]; decide))
    · refine ⟨0, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨5, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨2, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨6, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨1, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨3, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨4, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨7, 0, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
  · have h2 : g (2 : Fin 11) = 1 := by
      have h12 := hstep (1 : Fin 11)
      change g (2 : Fin 11) = representativePerm rep8BIndex (g (1 : Fin 11)) at h12
      rw [h1] at h12
      rw [h12]
      decide
    generalize h3v : g (3 : Fin 11) = y at ⊢
    fin_cases y
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 0) (g.injective (by rw [h3v, h0]; decide))
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 2) (g.injective (by rw [h3v, h2]; decide))
    · exfalso
      exact (by decide : (3 : Fin 11) ≠ 1) (g.injective (by rw [h3v, h1]; decide))
    · refine ⟨0, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨5, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨2, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨6, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨1, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨3, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨4, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide
    · refine ⟨7, 1, ?_⟩
      apply rep8ABConjugator_eq_of_conj_of_images g hconj
      · rw [h1]; decide
      · rw [h3v]; decide

set_option maxHeartbeats 2000000 in
-- The contradiction is: an `M11` conjugator preserves Witt blocks, but all ambient candidates fail.
set_option maxRecDepth 100000 in
/-- The two order-8 rows `8A` and `8B` are not conjugate inside `M11`. -/
theorem rep8A_rep8B_not_isConj :
    ¬ IsConj (representativeM11 rep8AIndex) (representativeM11 rep8BIndex) := by
  intro h
  rcases isConj_iff.mp h with ⟨g, hg⟩
  have hperm0 := congrArg (fun z : M11 => (z : Perm11)) hg
  have hperm : g.1 * representativePerm rep8AIndex * g.1⁻¹ = representativePerm rep8BIndex := by
    simpa [representativeM11_val] using hperm0
  rcases rep8ABConjugator_exists_of_conj g.1 hperm with ⟨k, s, hgks⟩
  have hpres : WittDesign.PreservesWittBlocks (rep8ABConjugator k s) := by
    rw [← hgks]
    exact WittDesign.M11_preserves_wittBlocks g
  have htrue := (wittBlockPreservationCheck_eq_true_iff (rep8ABConjugator k s)).mpr hpres
  rw [rep8ABConjugator_wittBlockPreservationCheck_false k s] at htrue
  contradiction

/-- Non-conjugate representatives have disjoint conjugacy orbits. -/
theorem classOrbit_disjoint_of_not_isConj {i j : Fin 10}
    (hnot : ¬ IsConj (representativeM11 i) (representativeM11 j)) :
    Disjoint (classOrbit i) (classOrbit j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxi' : IsConj x (representativeM11 i) := by
    simpa [classOrbit] using (ConjAct.mem_orbit_conjAct.mp hxi)
  have hxj' : IsConj x (representativeM11 j) := by
    simpa [classOrbit] using (ConjAct.mem_orbit_conjAct.mp hxj)
  exact hnot (hxi'.symm.trans hxj')

/-- The `11A` and `11B` conjugacy orbits are disjoint. -/
theorem rep11A_rep11B_classOrbit_disjoint :
    Disjoint (classOrbit rep11AIndex) (classOrbit rep11BIndex) :=
  classOrbit_disjoint_of_not_isConj rep11A_rep11B_not_isConj

/-- The `8A` and `8B` conjugacy orbits are disjoint. -/
theorem rep8A_rep8B_classOrbit_disjoint :
    Disjoint (classOrbit rep8AIndex) (classOrbit rep8BIndex) :=
  classOrbit_disjoint_of_not_isConj rep8A_rep8B_not_isConj

set_option maxHeartbeats 1000000 in
-- Same-order distinct rows are exactly the two verified split pairs.
set_option maxRecDepth 100000 in
/-- The only distinct class-table rows with equal element order are the split pairs. -/
theorem same_order_distinct_index_cases {i j : Fin 10} (hij : i ≠ j)
    (horder : classElementOrder i = classElementOrder j) :
    (i = rep8AIndex ∧ j = rep8BIndex) ∨
      (i = rep8BIndex ∧ j = rep8AIndex) ∨
      (i = rep11AIndex ∧ j = rep11BIndex) ∨
      (i = rep11BIndex ∧ j = rep11AIndex) := by
  fin_cases i <;> fin_cases j <;>
    simp [classElementOrder, classElementOrderList, rep8AIndex, rep8BIndex,
      rep11AIndex, rep11BIndex] at horder hij ⊢

/-- The ten verified conjugacy-class orbits are pairwise disjoint. -/
theorem classOrbit_pairwiseDisjoint : Pairwise (Disjoint on classOrbit) := by
  intro i j hij
  by_cases horder : classElementOrder i = classElementOrder j
  · rcases same_order_distinct_index_cases hij horder with h | h | h | h
    · rcases h with ⟨rfl, rfl⟩
      exact rep8A_rep8B_classOrbit_disjoint
    · rcases h with ⟨rfl, rfl⟩
      exact rep8A_rep8B_classOrbit_disjoint.symm
    · rcases h with ⟨rfl, rfl⟩
      exact rep11A_rep11B_classOrbit_disjoint
    · rcases h with ⟨rfl, rfl⟩
      exact rep11A_rep11B_classOrbit_disjoint.symm
  · exact classOrbit_disjoint_of_order_ne horder

/-- The ten verified conjugacy-class orbits have total size `7920`. -/
theorem classOrbit_iUnion_ncard :
    (⋃ i : Fin 10, classOrbit i).ncard = 7920 :=
  classOrbit_iUnion_ncard_of_pairwise classOrbit_pairwiseDisjoint

/-- The ten verified conjugacy-class orbits cover all of `M11`. -/
theorem classOrbit_iUnion_eq_univ :
    (⋃ i : Fin 10, classOrbit i) = Set.univ :=
  classOrbit_iUnion_eq_univ_of_pairwise classOrbit_pairwiseDisjoint

end ConjugacyClasses
end Certificates
end Sporadic
