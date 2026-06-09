/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Mathlib.GroupTheory.Perm.Centralizer
import FiniteSimpleGroups.Sporadic.M11.Cardinality
import FiniteSimpleGroups.Sporadic.M11.Certificates.Words

/-!
# Conjugacy-class certificates

This file will eventually store representatives, class-size certificates, and
Lean-side verification lemmas for the simplicity proof.
-/

namespace Sporadic
namespace Certificates
namespace ConjugacyClasses

/--
The identity class contributes size `1`. This tiny arithmetic lemma is only a
sanity marker for the certificate workspace.
-/
theorem identity_class_size : (1 : Nat) ∣ 7920 := by
  norm_num

/-!
## Candidate class-size arithmetic

The data below is a certificate input, not a proof that the listed classes have
these sizes in the generated subgroup. The next stage must verify the actual
conjugacy classes in Lean. This file already checks the finite arithmetic that
will be used after those class certificates are connected.
-/

/-- Candidate M11 conjugacy class labels in ATLAS order. -/
def classLabelList : List String :=
  ["1A", "2A", "3A", "4A", "5A", "6A", "8A", "8B", "11A", "11B"]

/-- Candidate centralizer orders for the class labels above. -/
def centralizerOrderList : List Nat :=
  [7920, 48, 18, 8, 5, 6, 8, 8, 11, 11]

/--
Ambient symmetric-group centralizer orders for the same representatives. These
are usually larger than the centralizers inside `M11`; they are useful as a
Lean-checked upper bound before the sharper `M11` certificates are added.
-/
def ambientCentralizerOrderList : List Nat :=
  [39916800, 2304, 324, 192, 50, 36, 16, 16, 11, 11]

/-- Candidate element orders for the class labels above. -/
def classElementOrderList : List Nat :=
  [1, 2, 3, 4, 5, 6, 8, 8, 11, 11]

/-- Candidate conjugacy class sizes, computed as `7920 / centralizer_order`. -/
def classSizeList : List Nat :=
  [1, 165, 440, 990, 1584, 1320, 990, 990, 720, 720]

theorem classLabelList_length : classLabelList.length = 10 := by
  decide

theorem centralizerOrderList_length : centralizerOrderList.length = 10 := by
  decide

theorem ambientCentralizerOrderList_length : ambientCentralizerOrderList.length = 10 := by
  decide

theorem classElementOrderList_length : classElementOrderList.length = 10 := by
  decide

theorem classSizeList_length : classSizeList.length = 10 := by
  decide

set_option maxRecDepth 20000 in
/-- The candidate class sizes add up to the already verified group order. -/
theorem classSizeList_sum : classSizeList.sum = 7920 := by
  decide

set_option maxRecDepth 20000 in
/-- Each listed class size times its listed centralizer order is `7920`. -/
theorem classSize_mul_centralizerOrder :
    List.zipWith (· * ·) classSizeList centralizerOrderList =
      List.replicate 10 7920 := by
  decide

/-- Candidate sizes of the nonidentity conjugacy classes. -/
def nonidentityClassSizeList : List Nat :=
  [165, 440, 990, 1584, 1320, 990, 990, 720, 720]

theorem nonidentityClassSizeList_length : nonidentityClassSizeList.length = 9 := by
  decide

/-- The size attached to one nonidentity candidate class. -/
def nonidentityClassSize (i : Fin 9) : Nat :=
  nonidentityClassSizeList.get
    ⟨i.1, by rw [nonidentityClassSizeList_length]; exact i.2⟩

/--
Boolean bit test for a nonidentity class-size subset. The bit `i` records
whether the `i`th nonidentity class is included in a normal-subgroup candidate.
-/
def hasClassBit (m i : Nat) : Bool :=
  (m / 2 ^ i) % 2 == 1

/-- Add a class size exactly when the corresponding bit is set. -/
def addIfBit (m i size : Nat) : Nat :=
  if hasClassBit m i then size else 0

/-- Candidate normal-subgroup order encoded by a 9-bit mask. -/
def classUnionSizeOfMaskNat (m : Nat) : Nat :=
  1 + addIfBit m 0 165 + addIfBit m 1 440 + addIfBit m 2 990 +
    addIfBit m 3 1584 + addIfBit m 4 1320 + addIfBit m 5 990 +
    addIfBit m 6 990 + addIfBit m 7 720 + addIfBit m 8 720

/-- Candidate normal-subgroup order encoded by one of the `2^9` masks. -/
def classUnionSizeOfMask (m : Fin 512) : Nat :=
  classUnionSizeOfMaskNat m.1

set_option maxRecDepth 20000 in
/--
Subset-sum certificate for the simplicity route: if an identity-containing
union of the candidate nonidentity class sizes has order dividing `7920`, then
its size is either `1` or `7920`.
-/
theorem classUnionSizeOfMask_dvd_target_iff : ∀ m : Fin 512,
    classUnionSizeOfMask m ∣ 7920 ↔
      classUnionSizeOfMask m = 1 ∨ classUnionSizeOfMask m = 7920 := by
  decide

theorem classUnionSizeOfMask_eq_one_or_target_of_dvd (m : Fin 512)
    (h : classUnionSizeOfMask m ∣ 7920) :
    classUnionSizeOfMask m = 1 ∨ classUnionSizeOfMask m = 7920 :=
  (classUnionSizeOfMask_dvd_target_iff m).mp h

/-!
## Candidate representatives

These representatives are stored as words in the current generators. Thus Lean
does not need to trust an external assertion that they belong to `M11`: every
word evaluates to an element of the generated subgroup by
`Sporadic.Certificates.Word.toM11`.
-/

/-- Candidate representative words for the 10 class labels above. -/
def representativeWordList : List Word :=
  [[],
    [Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.b],
    [Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a],
    [Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.a, Gen.a, Gen.b],
    [Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.b],
    [Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.b],
    [Gen.b, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a],
    [Gen.b, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv],
    [Gen.a],
    [Gen.a, Gen.a, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.b]
  ]

theorem representativeWordList_length : representativeWordList.length = 10 := by
  decide

/-- The representative word for a class-table row. -/
def representativeWord (i : Fin 10) : Word :=
  representativeWordList.get
    ⟨i.1, by rw [representativeWordList_length]; exact i.2⟩

/-- Candidate class representative as an ambient degree-11 permutation. -/
def representativePerm (i : Fin 10) : Perm11 :=
  Word.eval (representativeWord i)

/-- Candidate class representative as an element of the generated group `M11`. -/
def representativeM11 (i : Fin 10) : M11 :=
  Word.toM11 (representativeWord i)

/-- Candidate class representatives as ambient permutations. -/
def representativePermList : List Perm11 :=
  representativeWordList.map Word.eval

theorem representativePermList_length : representativePermList.length = 10 := by
  decide

/-- The candidate element order for a class-table row. -/
def classElementOrder (i : Fin 10) : Nat :=
  classElementOrderList.get
    ⟨i.1, by rw [classElementOrderList_length]; exact i.2⟩

/-- The ambient symmetric-group centralizer order for a class-table row. -/
def ambientCentralizerOrder (i : Fin 10) : Nat :=
  ambientCentralizerOrderList.get
    ⟨i.1, by rw [ambientCentralizerOrderList_length]; exact i.2⟩

set_option maxRecDepth 80000 in
/--
Each candidate representative has order dividing the listed candidate order.
The later exact-order certificate will refine this by ruling out smaller powers.
-/
theorem representativePerm_pow_order_eq_one : ∀ i : Fin 10,
    representativePerm i ^ classElementOrder i = 1 := by
  decide

set_option maxRecDepth 100000 in
/--
Each candidate representative has exactly the listed candidate order. This uses
the standard `orderOf_eq_of_pow_and_pow_div_prime` API: after proving the listed
power is one, Lean only checks the proper prime-divisor powers.
-/
theorem representativePerm_orderOf_eq : ∀ i : Fin 10,
    orderOf (representativePerm i) = classElementOrder i := by
  intro i
  apply orderOf_eq_of_pow_and_pow_div_prime
  · fin_cases i <;> decide
  · exact representativePerm_pow_order_eq_one i
  · intro p hp hd
    fin_cases i
    · exfalso
      exact hp.not_dvd_one (by simpa [classElementOrder, classElementOrderList] using hd)
    · have hp_eq : p = 2 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (by simpa [classElementOrder, classElementOrderList] using hd)
      subst p
      decide
    · have hp_eq : p = 3 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (by simpa [classElementOrder, classElementOrderList] using hd)
      subst p
      decide
    · have hp_eq : p = 2 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (m := 2) (n := 2)
            (by simpa [classElementOrder, classElementOrderList] using hd))
      subst p
      decide
    · have hp_eq : p = 5 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
          (by simpa [classElementOrder, classElementOrderList] using hd)
      subst p
      decide
    · have hp_eq : p = 2 ∨ p = 3 := by
        have h : p ∣ 2 * 3 := by
          simpa [classElementOrder, classElementOrderList] using hd
        rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
      rcases hp_eq with rfl | rfl <;> decide
    · have hp_eq : p = 2 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (m := 2) (n := 3)
            (by simpa [classElementOrder, classElementOrderList] using hd))
      subst p
      decide
    · have hp_eq : p = 2 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (m := 2) (n := 3)
            (by simpa [classElementOrder, classElementOrderList] using hd))
      subst p
      decide
    · have hp_eq : p = 11 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_eleven).mp
          (by simpa [classElementOrder, classElementOrderList] using hd)
      subst p
      decide
    · have hp_eq : p = 11 := by
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_eleven).mp
          (by simpa [classElementOrder, classElementOrderList] using hd)
      subst p
      decide

set_option maxRecDepth 80000 in
/-- The 10 candidate representative permutations are pairwise distinct. -/
theorem representativePermList_nodup : representativePermList.Nodup := by
  decide

/-!
## Generic representative centralizer bounds

The exact `M11` centralizer sizes still need class-specific certificates. The
lemmas below give a uniform verified lower bound from the cyclic subgroup
generated by each representative, and a uniform upper bound from the ambient
symmetric-group centralizer.
-/

/-- The centralizer in `M11` of a candidate representative. -/
abbrev RepresentativeCentralizer (i : Fin 10) : Subgroup M11 :=
  Subgroup.centralizer ({representativeM11 i} : Set M11)

/-- The ambient symmetric-group centralizer of a candidate representative. -/
abbrev RepresentativeAmbientCentralizer (i : Fin 10) : Subgroup Perm11 :=
  Subgroup.centralizer ({representativePerm i} : Set Perm11)

set_option maxRecDepth 100000 in
/-- The cyclic subgroup generated by a representative has the listed element order. -/
theorem representativeM11_zpowers_card (i : Fin 10) :
    Nat.card (Subgroup.zpowers (representativeM11 i)) = classElementOrder i := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_zpowers]
  change orderOf (⟨representativePerm i, Word.eval_mem_M11Subgroup (representativeWord i)⟩ :
    M11) = classElementOrder i
  rw [Subgroup.orderOf_mk]
  exact representativePerm_orderOf_eq i

set_option maxRecDepth 100000 in
/-- The ambient cyclic subgroup generated by a representative has the listed element order. -/
theorem representativePerm_zpowers_card (i : Fin 10) :
    Nat.card (Subgroup.zpowers (representativePerm i)) = classElementOrder i := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_zpowers]
  exact representativePerm_orderOf_eq i

/-- The cyclic subgroup generated by a representative centralizes it. -/
theorem representativeM11_zpowers_le_centralizer (i : Fin 10) :
    Subgroup.zpowers (representativeM11 i) ≤ RepresentativeCentralizer i := by
  intro x hx
  change x ∈ Subgroup.centralizer ({representativeM11 i} : Set M11)
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_zpowers_iff] at hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  exact (Commute.zpow_self (a := representativeM11 i) (n := n)).eq

/-- Lower bound on an `M11` representative centralizer from its cyclic subgroup. -/
theorem representativeCentralizer_card_ge_order (i : Fin 10) :
    classElementOrder i ≤ Nat.card (RepresentativeCentralizer i) := by
  have hle := Subgroup.card_le_of_le (representativeM11_zpowers_le_centralizer i)
  rw [representativeM11_zpowers_card] at hle
  exact hle

set_option maxRecDepth 100000 in
/-- Lean-checked ambient symmetric-group centralizer orders for all representatives. -/
theorem representativeAmbientCentralizer_card (i : Fin 10) :
    Nat.card (RepresentativeAmbientCentralizer i) = ambientCentralizerOrder i := by
  fin_cases i <;> rw [Equiv.Perm.nat_card_centralizer] <;> norm_num <;> decide

/-- The `M11` centralizer of a representative maps into its ambient centralizer. -/
theorem representativeCentralizer_map_le_ambient (i : Fin 10) :
    (RepresentativeCentralizer i).map M11Subgroup.subtype ≤
      RepresentativeAmbientCentralizer i := by
  have hle : (RepresentativeCentralizer i).map M11Subgroup.subtype ≤
      Subgroup.centralizer (M11Subgroup.subtype '' ({representativeM11 i} : Set M11)) := by
    exact Subgroup.map_centralizer_le_centralizer_image ({representativeM11 i} : Set M11)
      M11Subgroup.subtype
  have himage : M11Subgroup.subtype '' ({representativeM11 i} : Set M11) =
      ({representativePerm i} : Set Perm11) := by
    ext x
    simp [representativeM11, representativePerm]
  change (RepresentativeCentralizer i).map M11Subgroup.subtype ≤
    Subgroup.centralizer ({representativePerm i} : Set Perm11)
  rw [himage] at hle
  exact hle

/-- Upper bound on an `M11` representative centralizer from the ambient centralizer. -/
theorem representativeCentralizer_card_le_ambient (i : Fin 10) :
    Nat.card (RepresentativeCentralizer i) ≤ ambientCentralizerOrder i := by
  have hmapcard : Nat.card ((RepresentativeCentralizer i).map M11Subgroup.subtype) =
      Nat.card (RepresentativeCentralizer i) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le (representativeCentralizer_map_le_ambient i)
  rw [hmapcard, representativeAmbientCentralizer_card] at hle
  exact hle

/-- Combined lower and upper bound for every representative centralizer. -/
theorem representativeCentralizer_card_bounds (i : Fin 10) :
    classElementOrder i ≤ Nat.card (RepresentativeCentralizer i) ∧
      Nat.card (RepresentativeCentralizer i) ≤ ambientCentralizerOrder i :=
  ⟨representativeCentralizer_card_ge_order i, representativeCentralizer_card_le_ambient i⟩

/-!
## Alternating-group refinement for representative centralizers

Since the generated `M11` lies in the ambient alternating group, an `M11`
centralizer maps not just into the ambient centralizer, but into its intersection
with the alternating group. For the 8A and 8B rows this is enough to sharpen the
ambient upper bound from `16` to `8`.
-/

/-- The ambient centralizer intersected with the ambient alternating group. -/
abbrev RepresentativeAmbientAlternatingCentralizer (i : Fin 10) : Subgroup Perm11 :=
  RepresentativeAmbientCentralizer i ⊓ alternatingGroup (Fin 11)

/-- The sign homomorphism restricted to an ambient representative centralizer. -/
def representativeAmbientCentralizerSignHom (i : Fin 10) :
    RepresentativeAmbientCentralizer i →* ℤˣ :=
  (Equiv.Perm.sign : Perm11 →* ℤˣ).comp (RepresentativeAmbientCentralizer i).subtype

/--
The kernel of the restricted sign homomorphism maps to the intersection of the
ambient centralizer with the alternating group.
-/
theorem representativeAmbientCentralizerSignHom_ker_map_eq_inf (i : Fin 10) :
    (representativeAmbientCentralizerSignHom i).ker.map
        (RepresentativeAmbientCentralizer i).subtype =
      RepresentativeAmbientAlternatingCentralizer i := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y.2, by
      change Equiv.Perm.sign ((RepresentativeAmbientCentralizer i).subtype y) = 1
      exact MonoidHom.mem_ker.mp hy⟩
  · intro hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    change (representativeAmbientCentralizerSignHom i) ⟨x, hx.1⟩ = 1
    exact Equiv.Perm.mem_alternatingGroup.mp hx.2

/-- The range of the restricted sign homomorphism is all of `ℤˣ` if it contains an odd element. -/
theorem representativeAmbientCentralizerSignHom_range_eq_top_of_odd (i : Fin 10)
    (c : RepresentativeAmbientCentralizer i) (hc : Equiv.Perm.sign c.1 = -1) :
    (representativeAmbientCentralizerSignHom i).range = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro u
  rcases Int.units_eq_one_or u with hu | hu
  · subst u
    exact ⟨1, by simp [representativeAmbientCentralizerSignHom]⟩
  · subst u
    exact ⟨c, by simpa [representativeAmbientCentralizerSignHom] using hc⟩

/-- The restricted sign range has cardinality two if it contains an odd element. -/
theorem representativeAmbientCentralizerSignHom_range_card_of_odd (i : Fin 10)
    (c : RepresentativeAmbientCentralizer i) (hc : Equiv.Perm.sign c.1 = -1) :
    Nat.card (representativeAmbientCentralizerSignHom i).range = 2 := by
  rw [representativeAmbientCentralizerSignHom_range_eq_top_of_odd i c hc]
  exact (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv).trans
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units_int])

/--
If an ambient representative centralizer has order `16` and contains an odd
element, then its alternating part has order `8`.
-/
theorem representativeAmbientAlternatingCentralizer_card_eq_eight_of_ambient_card_eq_sixteen
    (i : Fin 10) (hambient : Nat.card (RepresentativeAmbientCentralizer i) = 16)
    (c : RepresentativeAmbientCentralizer i) (hc : Equiv.Perm.sign c.1 = -1) :
    Nat.card (RepresentativeAmbientAlternatingCentralizer i) = 8 := by
  have hker_mul :
      Nat.card (representativeAmbientCentralizerSignHom i).ker * 2 = 16 := by
    have h :=
      (representativeAmbientCentralizerSignHom i).ker.card_mul_index
    rw [Subgroup.index_ker,
      representativeAmbientCentralizerSignHom_range_card_of_odd i c hc,
      hambient] at h
    exact h
  have hker : Nat.card (representativeAmbientCentralizerSignHom i).ker = 8 := by
    omega
  have hmapcard :
      Nat.card ((representativeAmbientCentralizerSignHom i).ker.map
          (RepresentativeAmbientCentralizer i).subtype) =
        Nat.card (representativeAmbientCentralizerSignHom i).ker :=
    Subgroup.card_map_of_injective (RepresentativeAmbientCentralizer i).subtype_injective
  rw [← representativeAmbientCentralizerSignHom_ker_map_eq_inf, hmapcard, hker]

/-- The `M11` centralizer of a representative maps into the ambient alternating centralizer. -/
theorem representativeCentralizer_map_le_ambient_alternating (i : Fin 10) :
    (RepresentativeCentralizer i).map M11Subgroup.subtype ≤
      RepresentativeAmbientAlternatingCentralizer i := by
  intro x hx
  exact ⟨representativeCentralizer_map_le_ambient i hx, by
    rcases hx with ⟨y, -, rfl⟩
    exact M11_toPerm_mem_alternatingGroup y⟩

/-- Upper bound from the ambient alternating centralizer. -/
theorem representativeCentralizer_card_le_ambient_alternating (i : Fin 10) :
    Nat.card (RepresentativeCentralizer i) ≤
      Nat.card (RepresentativeAmbientAlternatingCentralizer i) := by
  have hmapcard : Nat.card ((RepresentativeCentralizer i).map M11Subgroup.subtype) =
      Nat.card (RepresentativeCentralizer i) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le (representativeCentralizer_map_le_ambient_alternating i)
  rw [hmapcard] at hle
  exact hle

/-- The class-table index of the 8A representative. -/
abbrev rep8AIndex : Fin 10 :=
  ⟨6, by decide⟩

/-- The class-table index of the 8B representative. -/
abbrev rep8BIndex : Fin 10 :=
  ⟨7, by decide⟩

/-- The transposition on the 2-cycle shared by the 8A and 8B representatives. -/
abbrev rep8OddCentralizerWitness : Perm11 :=
  Equiv.swap (1 : Fin 11) (2 : Fin 11)

set_option maxRecDepth 100000 in
/-- The 8A odd witness centralizes the ambient 8A representative. -/
theorem rep8OddCentralizerWitness_mem_rep8A_ambient :
    rep8OddCentralizerWitness ∈ RepresentativeAmbientCentralizer rep8AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

set_option maxRecDepth 100000 in
/-- The 8B odd witness centralizes the ambient 8B representative. -/
theorem rep8OddCentralizerWitness_mem_rep8B_ambient :
    rep8OddCentralizerWitness ∈ RepresentativeAmbientCentralizer rep8BIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

/-- The 8A/8B centralizer witness is odd. -/
theorem rep8OddCentralizerWitness_sign :
    Equiv.Perm.sign rep8OddCentralizerWitness = -1 := by
  rw [rep8OddCentralizerWitness, Equiv.Perm.sign_swap]
  decide

/-- The ambient alternating centralizer of the 8A representative has order `8`. -/
theorem rep8A_ambientAlternatingCentralizer_card :
    Nat.card (RepresentativeAmbientAlternatingCentralizer rep8AIndex) = 8 := by
  refine representativeAmbientAlternatingCentralizer_card_eq_eight_of_ambient_card_eq_sixteen
    rep8AIndex ?_ ⟨rep8OddCentralizerWitness, rep8OddCentralizerWitness_mem_rep8A_ambient⟩ ?_
  · simpa [rep8AIndex, ambientCentralizerOrder, ambientCentralizerOrderList]
      using representativeAmbientCentralizer_card rep8AIndex
  · exact rep8OddCentralizerWitness_sign

/-- The ambient alternating centralizer of the 8B representative has order `8`. -/
theorem rep8B_ambientAlternatingCentralizer_card :
    Nat.card (RepresentativeAmbientAlternatingCentralizer rep8BIndex) = 8 := by
  refine representativeAmbientAlternatingCentralizer_card_eq_eight_of_ambient_card_eq_sixteen
    rep8BIndex ?_ ⟨rep8OddCentralizerWitness, rep8OddCentralizerWitness_mem_rep8B_ambient⟩ ?_
  · simpa [rep8BIndex, ambientCentralizerOrder, ambientCentralizerOrderList]
      using representativeAmbientCentralizer_card rep8BIndex
  · exact rep8OddCentralizerWitness_sign

/-- The `M11` centralizer of the 8A representative has order `8`. -/
theorem rep8A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep8AIndex) = 8 := by
  have hle := representativeCentralizer_card_le_ambient_alternating rep8AIndex
  rw [rep8A_ambientAlternatingCentralizer_card] at hle
  have hge : 8 ≤ Nat.card (RepresentativeCentralizer rep8AIndex) := by
    simpa [rep8AIndex, classElementOrder, classElementOrderList]
      using representativeCentralizer_card_ge_order rep8AIndex
  exact le_antisymm hle hge

/-- The `M11` centralizer of the 8B representative has order `8`. -/
theorem rep8B_centralizer_card :
    Nat.card (RepresentativeCentralizer rep8BIndex) = 8 := by
  have hle := representativeCentralizer_card_le_ambient_alternating rep8BIndex
  rw [rep8B_ambientAlternatingCentralizer_card] at hle
  have hge : 8 ≤ Nat.card (RepresentativeCentralizer rep8BIndex) := by
    simpa [rep8BIndex, classElementOrder, classElementOrderList]
      using representativeCentralizer_card_ge_order rep8BIndex
  exact le_antisymm hle hge

/-!
## A Witt-block sieve for the 5A representative

The ambient centralizer of the 5A representative has order 50. Intersecting
with the alternating group leaves a 25-element rotation part. The next exact
centralizer proof needs to show that only the diagonal 5 rotations preserve the
Witt design, because every element of `M11` preserves the Witt blocks.
-/

/-- The class-table index of the 5A representative. -/
abbrev rep5AIndex : Fin 10 :=
  ⟨4, by decide⟩

/-- One 5-cycle factor of the 5A representative. -/
abbrev rep5ACycleA : Perm11 :=
  List.formPerm ([1, 2, 3, 7, 6] : List (Fin 11))

/-- The other 5-cycle factor of the 5A representative. -/
abbrev rep5ACycleB : Perm11 :=
  List.formPerm ([4, 8, 5, 9, 10] : List (Fin 11))

set_option maxRecDepth 100000 in
/-- The 5A representative is the product of the two displayed 5-cycles. -/
theorem rep5A_cycle_factorization :
    representativePerm rep5AIndex = rep5ACycleA * rep5ACycleB := by
  decide

/-- The 25 rotation candidates in the alternating ambient centralizer of 5A. -/
def rep5ARotation (i j : Fin 5) : Perm11 :=
  rep5ACycleA ^ i.1 * rep5ACycleB ^ j.1

set_option maxRecDepth 100000 in
/-- Each displayed 5A rotation candidate centralizes the ambient 5A representative. -/
theorem rep5ARotation_mem_ambientCentralizer (i j : Fin 5) :
    rep5ARotation i j ∈ RepresentativeAmbientCentralizer rep5AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 100000 in
/-- Each displayed 5A rotation candidate is even. -/
theorem rep5ARotation_mem_alternatingGroup (i j : Fin 5) :
    rep5ARotation i j ∈ alternatingGroup (Fin 11) := by
  change Equiv.Perm.sign (rep5ARotation i j) = 1
  fin_cases i <;> fin_cases j <;> decide

/-- Boolean forward block-preservation check over the 66 listed Witt blocks. -/
def wittBlockForwardCheck (g : Perm11) : Bool :=
  WittDesign.wittBlockList.all
    (fun B => decide (WittDesign.blockMap g B ∈ WittDesign.wittBlocks))

/-- Boolean two-sided block-preservation check over the 66 listed Witt blocks. -/
def wittBlockPreservationCheck (g : Perm11) : Bool :=
  wittBlockForwardCheck g && wittBlockForwardCheck g⁻¹

/-- The Boolean Witt-block check is equivalent to the Prop-level preservation statement. -/
theorem wittBlockPreservationCheck_eq_true_iff (g : Perm11) :
    wittBlockPreservationCheck g = true ↔ WittDesign.PreservesWittBlocks g := by
  simp [wittBlockPreservationCheck, wittBlockForwardCheck, WittDesign.PreservesWittBlocks,
    List.all_eq_true]

set_option maxRecDepth 200000

/-
The finite Boolean sieve: among the 25 even ambient rotation candidates for 5A,
exactly the 5 diagonal ones preserve the listed Witt blocks.
The proof is a bounded evaluation of 25 candidates against the 66-block list.
-/
set_option maxHeartbeats 2000000 in
-- The proof unfolds the full 25-by-66 block-preservation check.
theorem rep5ARotation_wittBlockPreservationCheck_iff (i j : Fin 5) :
    wittBlockPreservationCheck (rep5ARotation i j) = true ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

/-
Among the 25 even ambient rotation candidates for 5A, exactly the 5 diagonal
ones preserve the small Witt design. This is the finite Lean-side sieve that
will later give the sharp 5A centralizer upper bound once the ambient
centralizer is parameterized by these rotations.
-/
theorem rep5ARotation_preserves_wittBlocks_iff (i j : Fin 5) :
    WittDesign.PreservesWittBlocks (rep5ARotation i j) ↔ i = j := by
  rw [← wittBlockPreservationCheck_eq_true_iff]
  exact rep5ARotation_wittBlockPreservationCheck_iff i j

/-- An odd ambient centralizer element that swaps the two 5-cycles of the 5A representative. -/
abbrev rep5AOddCentralizerWitness : Perm11 :=
  Equiv.swap (1 : Fin 11) (4 : Fin 11) *
    Equiv.swap (2 : Fin 11) (8 : Fin 11) *
    Equiv.swap (3 : Fin 11) (5 : Fin 11) *
    Equiv.swap (7 : Fin 11) (9 : Fin 11) *
    Equiv.swap (6 : Fin 11) (10 : Fin 11)

set_option maxRecDepth 100000 in
/-- The 5A odd witness centralizes the ambient 5A representative. -/
theorem rep5AOddCentralizerWitness_mem_ambient :
    rep5AOddCentralizerWitness ∈ RepresentativeAmbientCentralizer rep5AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

set_option maxRecDepth 100000 in
/-- The 5A centralizer witness is odd. -/
theorem rep5AOddCentralizerWitness_sign :
    Equiv.Perm.sign rep5AOddCentralizerWitness = -1 := by
  decide

/-- The ambient alternating centralizer of the 5A representative has order `25`. -/
theorem rep5A_ambientAlternatingCentralizer_card :
    Nat.card (RepresentativeAmbientAlternatingCentralizer rep5AIndex) = 25 := by
  have hker_mul :
      Nat.card (representativeAmbientCentralizerSignHom rep5AIndex).ker * 2 = 50 := by
    have h :=
      (representativeAmbientCentralizerSignHom rep5AIndex).ker.card_mul_index
    rw [Subgroup.index_ker,
      representativeAmbientCentralizerSignHom_range_card_of_odd rep5AIndex
        ⟨rep5AOddCentralizerWitness, rep5AOddCentralizerWitness_mem_ambient⟩
        rep5AOddCentralizerWitness_sign] at h
    have hambient : Nat.card (RepresentativeAmbientCentralizer rep5AIndex) = 50 := by
      simpa [rep5AIndex, ambientCentralizerOrder, ambientCentralizerOrderList]
        using representativeAmbientCentralizer_card rep5AIndex
    rw [hambient] at h
    exact h
  have hker : Nat.card (representativeAmbientCentralizerSignHom rep5AIndex).ker = 25 := by
    omega
  have hmapcard :
      Nat.card ((representativeAmbientCentralizerSignHom rep5AIndex).ker.map
          (RepresentativeAmbientCentralizer rep5AIndex).subtype) =
        Nat.card (representativeAmbientCentralizerSignHom rep5AIndex).ker :=
    Subgroup.card_map_of_injective
      (RepresentativeAmbientCentralizer rep5AIndex).subtype_injective
  rw [← representativeAmbientCentralizerSignHom_ker_map_eq_inf, hmapcard, hker]

/-- The 25 displayed 5A rotations as a finite set. -/
def rep5ARotationFinset : Finset Perm11 :=
  Finset.univ.image (fun p : Fin 5 × Fin 5 => rep5ARotation p.1 p.2)

set_option maxRecDepth 200000 in
/-- The parameterization of the 25 displayed 5A rotations is injective. -/
theorem rep5ARotation_injective :
    Function.Injective (fun p : Fin 5 × Fin 5 => rep5ARotation p.1 p.2) := by
  intro p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

/-- The displayed 5A rotation set has cardinality `25`. -/
theorem rep5ARotationFinset_card : rep5ARotationFinset.card = 25 := by
  rw [rep5ARotationFinset, Finset.card_image_of_injective _ rep5ARotation_injective]
  decide

/-- The ambient alternating centralizer of 5A, as a finite set of ambient permutations. -/
noncomputable def rep5AAmbientAlternatingCentralizerFinset : Finset Perm11 := by
  classical
  exact Finset.univ.filter
    (fun g : Perm11 => g ∈ RepresentativeAmbientAlternatingCentralizer rep5AIndex)

/-- The displayed 5A rotations lie in the ambient alternating centralizer. -/
theorem rep5ARotationFinset_subset_ambientAlternating :
    rep5ARotationFinset ⊆ rep5AAmbientAlternatingCentralizerFinset := by
  classical
  intro g hg
  rw [rep5ARotationFinset, Finset.mem_image] at hg
  rcases hg with ⟨p, -, rfl⟩
  rw [rep5AAmbientAlternatingCentralizerFinset]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    exact ⟨rep5ARotation_mem_ambientCentralizer p.1 p.2,
      rep5ARotation_mem_alternatingGroup p.1 p.2⟩⟩

/-- The finite-set form of the 5A ambient alternating centralizer has cardinality `25`. -/
theorem rep5AAmbientAlternatingCentralizerFinset_card :
    rep5AAmbientAlternatingCentralizerFinset.card = 25 := by
  classical
  change (Finset.univ.filter
    (fun g : Perm11 => g ∈ RepresentativeAmbientAlternatingCentralizer rep5AIndex)).card = 25
  rw [← Fintype.card_subtype
    (fun g : Perm11 => g ∈ RepresentativeAmbientAlternatingCentralizer rep5AIndex)]
  rw [← Nat.card_eq_fintype_card]
  exact rep5A_ambientAlternatingCentralizer_card

/-- The 25 displayed rotations are exactly the ambient alternating centralizer of 5A. -/
theorem rep5ARotationFinset_eq_ambientAlternating :
    rep5ARotationFinset = rep5AAmbientAlternatingCentralizerFinset := by
  apply Finset.eq_of_subset_of_card_le rep5ARotationFinset_subset_ambientAlternating
  rw [rep5ARotationFinset_card, rep5AAmbientAlternatingCentralizerFinset_card]

/-- Every 5A ambient alternating centralizer element is one of the displayed rotations. -/
theorem rep5A_ambientAlternatingCentralizer_mem_rotationFinset
    (g : Perm11) (hg : g ∈ RepresentativeAmbientAlternatingCentralizer rep5AIndex) :
    g ∈ rep5ARotationFinset := by
  classical
  rw [rep5ARotationFinset_eq_ambientAlternating]
  rw [rep5AAmbientAlternatingCentralizerFinset]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩

set_option maxRecDepth 100000 in
/-- A diagonal 5A rotation is the corresponding power of the 5A representative. -/
theorem rep5ARotation_diag_eq_rep5A_pow (i : Fin 5) :
    rep5ARotation i i = representativePerm rep5AIndex ^ i.1 := by
  fin_cases i <;> decide

/--
The image of the `M11` centralizer of the 5A representative lies in the cyclic
ambient subgroup generated by that representative.
-/
theorem rep5ACentralizer_map_le_zpowers :
    (RepresentativeCentralizer rep5AIndex).map M11Subgroup.subtype ≤
      Subgroup.zpowers (representativePerm rep5AIndex) := by
  classical
  intro x hx
  have hxAlt :
      x ∈ RepresentativeAmbientAlternatingCentralizer rep5AIndex :=
    representativeCentralizer_map_le_ambient_alternating rep5AIndex hx
  have hxRot := rep5A_ambientAlternatingCentralizer_mem_rotationFinset x hxAlt
  rw [rep5ARotationFinset, Finset.mem_image] at hxRot
  rcases hxRot with ⟨p, -, hp⟩
  rcases p with ⟨i, j⟩
  have hxPres : WittDesign.PreservesWittBlocks x := by
    rcases hx with ⟨y, -, rfl⟩
    exact WittDesign.M11_preserves_wittBlocks y
  have hij : i = j := by
    apply (rep5ARotation_preserves_wittBlocks_iff i j).mp
    simpa [hp] using hxPres
  subst j
  rw [← hp, rep5ARotation_diag_eq_rep5A_pow]
  exact Subgroup.npow_mem_zpowers (representativePerm rep5AIndex) i.1

/-- Upper bound for the `M11` centralizer of the 5A representative. -/
theorem rep5A_centralizer_card_le :
    Nat.card (RepresentativeCentralizer rep5AIndex) ≤ 5 := by
  have hmapcard :
      Nat.card ((RepresentativeCentralizer rep5AIndex).map M11Subgroup.subtype) =
        Nat.card (RepresentativeCentralizer rep5AIndex) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le rep5ACentralizer_map_le_zpowers
  rw [hmapcard, representativePerm_zpowers_card] at hle
  simpa [rep5AIndex, classElementOrder, classElementOrderList] using hle

/-- The `M11` centralizer of the 5A representative has order `5`. -/
theorem rep5A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep5AIndex) = 5 := by
  have hge : 5 ≤ Nat.card (RepresentativeCentralizer rep5AIndex) := by
    simpa [rep5AIndex, classElementOrder, classElementOrderList]
      using representativeCentralizer_card_ge_order rep5AIndex
  exact le_antisymm rep5A_centralizer_card_le hge

/-!
## A Witt-block sieve for the 6A representative

The 6A representative has cycle shape `2 * 6 * 3` in the ambient symmetric
group, so its ambient centralizer has order `36`. The displayed rotations below
parameterize that full ambient centralizer. A finite Witt-block check then
shows that exactly the six diagonal rotations preserve the candidate Witt
design. Since every `M11` element preserves the Witt blocks, the `M11`
centralizer is forced into the cyclic subgroup generated by the representative.
-/

/-- The class-table index of the 6A representative. -/
abbrev rep6AIndex : Fin 10 :=
  ⟨5, by decide⟩

/-- The 2-cycle factor of the 6A representative. -/
abbrev rep6ACycle2 : Perm11 :=
  List.formPerm ([0, 1] : List (Fin 11))

/-- The 6-cycle factor of the 6A representative. -/
abbrev rep6ACycle6 : Perm11 :=
  List.formPerm ([2, 3, 5, 4, 6, 8] : List (Fin 11))

/-- The 3-cycle factor of the 6A representative. -/
abbrev rep6ACycle3 : Perm11 :=
  List.formPerm ([7, 10, 9] : List (Fin 11))

set_option maxRecDepth 100000 in
/-- The 6A representative is the product of the displayed 2-, 6-, and 3-cycles. -/
theorem rep6A_cycle_factorization :
    representativePerm rep6AIndex = rep6ACycle2 * rep6ACycle6 * rep6ACycle3 := by
  decide

/-- The 36 rotation candidates in the ambient centralizer of 6A. -/
def rep6ARotation (i : Fin 2) (j : Fin 6) (k : Fin 3) : Perm11 :=
  rep6ACycle2 ^ i.1 * rep6ACycle6 ^ j.1 * rep6ACycle3 ^ k.1

set_option maxRecDepth 150000 in
/-- Each displayed 6A rotation candidate centralizes the ambient 6A representative. -/
theorem rep6ARotation_mem_ambientCentralizer (i : Fin 2) (j : Fin 6) (k : Fin 3) :
    rep6ARotation i j k ∈ RepresentativeAmbientCentralizer rep6AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The parity coordinate forced by a diagonal 6A power. -/
def rep6AParity (j : Fin 6) : Fin 2 :=
  ⟨j.1 % 2, Nat.mod_lt _ (by decide)⟩

/-- The 3-cycle coordinate forced by a diagonal 6A power. -/
def rep6AThird (j : Fin 6) : Fin 3 :=
  ⟨j.1 % 3, Nat.mod_lt _ (by decide)⟩

/-
The finite Boolean sieve: among the 36 ambient rotation candidates for 6A,
exactly the six diagonal rotations preserve the listed Witt blocks.
-/
set_option maxHeartbeats 3000000 in
-- The proof unfolds the full 36-by-66 block-preservation check.
theorem rep6ARotation_wittBlockPreservationCheck_iff
    (i : Fin 2) (j : Fin 6) (k : Fin 3) :
    wittBlockPreservationCheck (rep6ARotation i j k) = true ↔
      i = rep6AParity j ∧ k = rep6AThird j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/--
Among the 36 ambient rotations for 6A, exactly the six diagonal rotations
preserve the small Witt design.
-/
theorem rep6ARotation_preserves_wittBlocks_iff
    (i : Fin 2) (j : Fin 6) (k : Fin 3) :
    WittDesign.PreservesWittBlocks (rep6ARotation i j k) ↔
      i = rep6AParity j ∧ k = rep6AThird j := by
  rw [← wittBlockPreservationCheck_eq_true_iff]
  exact rep6ARotation_wittBlockPreservationCheck_iff i j k

/-- The 36 displayed 6A rotations as a finite set. -/
def rep6ARotationFinset : Finset Perm11 :=
  Finset.univ.image (fun p : (Fin 2 × Fin 6) × Fin 3 => rep6ARotation p.1.1 p.1.2 p.2)

set_option maxRecDepth 250000 in
/-- The parameterization of the 36 displayed 6A rotations is injective. -/
theorem rep6ARotation_injective :
    Function.Injective
      (fun p : (Fin 2 × Fin 6) × Fin 3 => rep6ARotation p.1.1 p.1.2 p.2) := by
  intro p q
  rcases p with ⟨⟨i, j⟩, k⟩
  rcases q with ⟨⟨i', j'⟩, k'⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases i' <;> fin_cases j' <;> fin_cases k' <;> decide

/-- The displayed 6A rotation set has cardinality `36`. -/
theorem rep6ARotationFinset_card : rep6ARotationFinset.card = 36 := by
  rw [rep6ARotationFinset, Finset.card_image_of_injective _ rep6ARotation_injective]
  decide

/-- The ambient centralizer of 6A, as a finite set of ambient permutations. -/
noncomputable def rep6AAmbientCentralizerFinset : Finset Perm11 := by
  classical
  exact Finset.univ.filter
    (fun g : Perm11 => g ∈ RepresentativeAmbientCentralizer rep6AIndex)

/-- The displayed 6A rotations lie in the ambient centralizer. -/
theorem rep6ARotationFinset_subset_ambient :
    rep6ARotationFinset ⊆ rep6AAmbientCentralizerFinset := by
  classical
  intro g hg
  rw [rep6ARotationFinset, Finset.mem_image] at hg
  rcases hg with ⟨p, -, rfl⟩
  rw [rep6AAmbientCentralizerFinset]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rep6ARotation_mem_ambientCentralizer
    p.1.1 p.1.2 p.2⟩

/-- The finite-set form of the 6A ambient centralizer has cardinality `36`. -/
theorem rep6AAmbientCentralizerFinset_card :
    rep6AAmbientCentralizerFinset.card = 36 := by
  classical
  change (Finset.univ.filter
    (fun g : Perm11 => g ∈ RepresentativeAmbientCentralizer rep6AIndex)).card = 36
  rw [← Fintype.card_subtype
    (fun g : Perm11 => g ∈ RepresentativeAmbientCentralizer rep6AIndex)]
  rw [← Nat.card_eq_fintype_card]
  simpa [rep6AIndex, ambientCentralizerOrder, ambientCentralizerOrderList]
    using representativeAmbientCentralizer_card rep6AIndex

/-- The 36 displayed rotations are exactly the ambient centralizer of 6A. -/
theorem rep6ARotationFinset_eq_ambient :
    rep6ARotationFinset = rep6AAmbientCentralizerFinset := by
  apply Finset.eq_of_subset_of_card_le rep6ARotationFinset_subset_ambient
  rw [rep6ARotationFinset_card, rep6AAmbientCentralizerFinset_card]

/-- Every 6A ambient centralizer element is one of the displayed rotations. -/
theorem rep6A_ambientCentralizer_mem_rotationFinset
    (g : Perm11) (hg : g ∈ RepresentativeAmbientCentralizer rep6AIndex) :
    g ∈ rep6ARotationFinset := by
  classical
  rw [rep6ARotationFinset_eq_ambient]
  rw [rep6AAmbientCentralizerFinset]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩

set_option maxRecDepth 100000 in
/-- A diagonal 6A rotation is the corresponding power of the 6A representative. -/
theorem rep6ARotation_diag_eq_rep6A_pow (j : Fin 6) :
    rep6ARotation (rep6AParity j) j (rep6AThird j) =
      representativePerm rep6AIndex ^ j.1 := by
  fin_cases j <;> decide

/--
The image of the `M11` centralizer of the 6A representative lies in the cyclic
ambient subgroup generated by that representative.
-/
theorem rep6ACentralizer_map_le_zpowers :
    (RepresentativeCentralizer rep6AIndex).map M11Subgroup.subtype ≤
      Subgroup.zpowers (representativePerm rep6AIndex) := by
  classical
  intro x hx
  have hxAmbient : x ∈ RepresentativeAmbientCentralizer rep6AIndex :=
    representativeCentralizer_map_le_ambient rep6AIndex hx
  have hxRot := rep6A_ambientCentralizer_mem_rotationFinset x hxAmbient
  rw [rep6ARotationFinset, Finset.mem_image] at hxRot
  rcases hxRot with ⟨p, -, hp⟩
  rcases p with ⟨⟨i, j⟩, k⟩
  have hxPres : WittDesign.PreservesWittBlocks x := by
    rcases hx with ⟨y, -, rfl⟩
    exact WittDesign.M11_preserves_wittBlocks y
  have hdiag : i = rep6AParity j ∧ k = rep6AThird j := by
    apply (rep6ARotation_preserves_wittBlocks_iff i j k).mp
    simpa [hp] using hxPres
  rcases hdiag with ⟨hi, hk⟩
  subst i
  subst k
  rw [← hp, rep6ARotation_diag_eq_rep6A_pow]
  exact Subgroup.npow_mem_zpowers (representativePerm rep6AIndex) j.1

/-- Upper bound for the `M11` centralizer of the 6A representative. -/
theorem rep6A_centralizer_card_le :
    Nat.card (RepresentativeCentralizer rep6AIndex) ≤ 6 := by
  have hmapcard :
      Nat.card ((RepresentativeCentralizer rep6AIndex).map M11Subgroup.subtype) =
        Nat.card (RepresentativeCentralizer rep6AIndex) :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le rep6ACentralizer_map_le_zpowers
  rw [hmapcard, representativePerm_zpowers_card] at hle
  simpa [rep6AIndex, classElementOrder, classElementOrderList] using hle

/-- The `M11` centralizer of the 6A representative has order `6`. -/
theorem rep6A_centralizer_card :
    Nat.card (RepresentativeCentralizer rep6AIndex) = 6 := by
  have hge : 6 ≤ Nat.card (RepresentativeCentralizer rep6AIndex) := by
    simpa [rep6AIndex, classElementOrder, classElementOrderList]
      using representativeCentralizer_card_ge_order rep6AIndex
  exact le_antisymm rep6A_centralizer_card_le hge

/-!
## A Witt-block sieve for the 4A representative

The 4A representative has cycle shape `1^3 * 4^2`. Its ambient centralizer has
order `192`: arbitrary permutations of the three fixed points, rotations of the
two 4-cycles, and an optional swap of the two 4-cycles.

The first verified step below is a lower-bound certificate: a word in the
generators gives an order-eight element of `M11` centralizing the 4A
representative. The full ambient-parameter sieve is left as the next proof
engineering target, because a direct 192-candidate `decide` proof is too heavy.
-/

/-- The class-table index of the 4A representative. -/
abbrev rep4AIndex : Fin 10 :=
  ⟨3, by decide⟩

/-- The six permutations of the fixed-point set `{0, 1, 2}`, extended by identity. -/
def rep4AFixedPermList : List Perm11 :=
  [
    1,
    Equiv.swap (0 : Fin 11) (1 : Fin 11),
    Equiv.swap (0 : Fin 11) (2 : Fin 11),
    Equiv.swap (1 : Fin 11) (2 : Fin 11),
    List.formPerm ([0, 1, 2] : List (Fin 11)),
    List.formPerm ([0, 2, 1] : List (Fin 11))
  ]

theorem rep4AFixedPermList_length : rep4AFixedPermList.length = 6 := by
  decide

/-- One of the six fixed-point permutations for the 4A ambient centralizer. -/
def rep4AFixedPerm (r : Fin 6) : Perm11 :=
  rep4AFixedPermList.get ⟨r.1, by rw [rep4AFixedPermList_length]; exact r.2⟩

/-- One 4-cycle factor of the 4A representative. -/
abbrev rep4ACycleA : Perm11 :=
  List.formPerm ([3, 4, 9, 7] : List (Fin 11))

/-- The other 4-cycle factor of the 4A representative. -/
abbrev rep4ACycleB : Perm11 :=
  List.formPerm ([5, 8, 6, 10] : List (Fin 11))

/-- The ambient permutation swapping the two 4-cycle supports of the 4A representative. -/
abbrev rep4ACycleSwap : Perm11 :=
  Equiv.swap (3 : Fin 11) (5 : Fin 11) *
    Equiv.swap (4 : Fin 11) (8 : Fin 11) *
    Equiv.swap (9 : Fin 11) (6 : Fin 11) *
    Equiv.swap (7 : Fin 11) (10 : Fin 11)

set_option maxRecDepth 100000 in
/-- The 4A representative is the product of the two displayed 4-cycles. -/
theorem rep4A_cycle_factorization :
    representativePerm rep4AIndex = rep4ACycleA * rep4ACycleB := by
  decide

/-- The 192 rotation and fixed-point permutation candidates in the ambient centralizer of 4A. -/
def rep4ARotation (r : Fin 6) (s : Fin 2) (i j : Fin 4) : Perm11 :=
  rep4AFixedPerm r * rep4ACycleA ^ i.1 * rep4ACycleB ^ j.1 * rep4ACycleSwap ^ s.1

/-- The successor coordinate on the 4-cycle rotations. -/
def rep4ANext (i : Fin 4) : Fin 4 :=
  ⟨(i.1 + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- Boolean form of the 4A preserving-parameter predicate. -/
def rep4APreservingParamCheck (r : Fin 6) (s : Fin 2) (i j : Fin 4) : Bool :=
  ((r.1 == 0) && (s.1 == 0) && (i.1 == j.1)) ||
    ((r.1 == 2) && (s.1 == 1) && (j.1 == (rep4ANext i).1))

/-- The parameter predicate for the eight 4A ambient candidates expected to preserve Witt blocks. -/
def rep4APreservingParam (r : Fin 6) (s : Fin 2) (i j : Fin 4) : Prop :=
  rep4APreservingParamCheck r s i j = true

instance rep4APreservingParam_decidable (r : Fin 6) (s : Fin 2) (i j : Fin 4) :
    Decidable (rep4APreservingParam r s i j) :=
  inferInstanceAs (Decidable (rep4APreservingParamCheck r s i j = true))

/-- The finite parameter set for the eight expected 4A preserving candidates. -/
def rep4APreservingParamFinset : Finset (((Fin 6 × Fin 2) × Fin 4) × Fin 4) :=
  Finset.univ.filter
    (fun p => rep4APreservingParam p.1.1.1 p.1.1.2 p.1.2 p.2)

/- The 4A preserving-parameter certificate has cardinality `8`. -/
theorem rep4APreservingParamFinset_card : rep4APreservingParamFinset.card = 8 := by
  decide

/-- The eight displayed 4A ambient candidates that preserve the Witt blocks. -/
def rep4APreservingRotationFinset : Finset Perm11 :=
  {
    rep4ARotation (0 : Fin 6) (0 : Fin 2) (0 : Fin 4) (0 : Fin 4),
    rep4ARotation (0 : Fin 6) (0 : Fin 2) (1 : Fin 4) (1 : Fin 4),
    rep4ARotation (0 : Fin 6) (0 : Fin 2) (2 : Fin 4) (2 : Fin 4),
    rep4ARotation (0 : Fin 6) (0 : Fin 2) (3 : Fin 4) (3 : Fin 4),
    rep4ARotation (2 : Fin 6) (1 : Fin 2) (0 : Fin 4) (1 : Fin 4),
    rep4ARotation (2 : Fin 6) (1 : Fin 2) (1 : Fin 4) (2 : Fin 4),
    rep4ARotation (2 : Fin 6) (1 : Fin 2) (2 : Fin 4) (3 : Fin 4),
    rep4ARotation (2 : Fin 6) (1 : Fin 2) (3 : Fin 4) (0 : Fin 4)
  }

set_option maxRecDepth 200000

/- The displayed 4A preserving-candidate set has cardinality `8`. -/
set_option maxHeartbeats 1000000 in
-- The proof compares the eight displayed preserving candidates.
theorem rep4APreservingRotationFinset_card : rep4APreservingRotationFinset.card = 8 := by
  decide

/-- A word for an order-eight element of `M11` centralizing the 4A representative. -/
def rep4AExtraWord : Word :=
  [Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv]

/-- The order-eight 4A centralizer element as an ambient permutation. -/
abbrev rep4AExtraPerm : Perm11 :=
  Word.eval rep4AExtraWord

/-- The order-eight 4A centralizer element as an element of `M11`. -/
abbrev rep4AExtraM11 : M11 :=
  Word.toM11 rep4AExtraWord

/-- The eight ambient powers of the extra 4A centralizer word. -/
def rep4AExtraPowerFinset : Finset Perm11 :=
  Finset.univ.image (fun n : Fin 8 => rep4AExtraPerm ^ n.1)

set_option maxRecDepth 100000 in
/-- The extra 4A centralizer word has order `8` in the ambient permutation group. -/
theorem rep4AExtra_orderOf : orderOf rep4AExtraM11 = 8 := by
  change orderOf (⟨rep4AExtraPerm, Word.eval_mem_M11Subgroup rep4AExtraWord⟩ : M11) = 8
  rw [Subgroup.orderOf_mk]
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide
  · decide
  · intro p hp hd
    have hp_eq : p = 2 := by
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (m := 2) (n := 3) (by simpa using hd))
    subst p
    decide

set_option maxRecDepth 100000 in
/-- The extra 4A centralizer word centralizes the 4A representative. -/
theorem rep4AExtra_mem_centralizer :
    rep4AExtraM11 ∈ RepresentativeCentralizer rep4AIndex := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide

/-- The cyclic subgroup generated by the extra 4A centralizer word has order `8`. -/
theorem rep4AExtra_zpowers_card :
    Nat.card (Subgroup.zpowers rep4AExtraM11) = 8 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_zpowers]
  exact rep4AExtra_orderOf

/-- The cyclic subgroup generated by the extra word lies in the 4A centralizer. -/
theorem rep4AExtra_zpowers_le_centralizer :
    Subgroup.zpowers rep4AExtraM11 ≤ RepresentativeCentralizer rep4AIndex := by
  intro x hx
  change x ∈ Subgroup.centralizer ({representativeM11 rep4AIndex} : Set M11)
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_zpowers_iff] at hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  have hcomm : Commute rep4AExtraM11 (representativeM11 rep4AIndex) :=
    Subgroup.mem_centralizer_singleton_iff.mp rep4AExtra_mem_centralizer
  exact (hcomm.zpow_left n).eq

/-- Lower bound for the `M11` centralizer of the 4A representative. -/
theorem rep4A_centralizer_card_ge : 8 ≤ Nat.card (RepresentativeCentralizer rep4AIndex) := by
  have hle := Subgroup.card_le_of_le rep4AExtra_zpowers_le_centralizer
  rw [rep4AExtra_zpowers_card] at hle
  exact hle

/-!
## Centralizer check for the 11A representative

The first nontrivial class-size certificate we can verify without a large orbit
enumeration is the centralizer of the generator `m11a`. In the ambient symmetric
group, `m11a` is an 11-cycle, so its centralizer has order 11. The centralizer
inside `M11` contains the cyclic subgroup generated by `m11a`, also of order 11,
and maps into the ambient centralizer. Thus the `M11` centralizer has order 11.
-/

/-- The generator `m11a` as an element of the generated group. -/
abbrev m11aM11 : M11 :=
  ⟨m11a, m11a_mem_M11Subgroup⟩

/-- The centralizer in `M11` of the 11-cycle generator. -/
abbrev M11aCentralizer : Subgroup M11 :=
  Subgroup.centralizer ({m11aM11} : Set M11)

set_option maxRecDepth 100000 in
/-- The ambient permutation `m11a` has order 11. -/
theorem m11a_orderOf : orderOf m11a = 11 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide
  · decide

set_option maxRecDepth 100000 in
/-- The cyclic subgroup generated by `m11a` inside `M11` has order 11. -/
theorem m11a_zpowers_card : Nat.card (Subgroup.zpowers m11aM11) = 11 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_zpowers]
  change orderOf (⟨m11a, m11a_mem_M11Subgroup⟩ : M11) = 11
  rw [Subgroup.orderOf_mk]
  exact m11a_orderOf

/-- The cyclic subgroup generated by `m11a` centralizes `m11a`. -/
theorem m11a_zpowers_le_centralizer :
    Subgroup.zpowers m11aM11 ≤ M11aCentralizer := by
  intro x hx
  change x ∈ Subgroup.centralizer ({m11aM11} : Set M11)
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_zpowers_iff] at hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  exact (Commute.zpow_self (a := m11aM11) (n := n)).eq

set_option maxRecDepth 100000 in
/-- The ambient symmetric-group centralizer of the 11-cycle `m11a` has order 11. -/
theorem ambient_m11a_centralizer_card :
    Nat.card (Subgroup.centralizer ({m11a} : Set Perm11)) = 11 := by
  rw [Equiv.Perm.nat_card_centralizer]
  norm_num
  decide

/-- The `M11` centralizer of `m11a` maps into the ambient centralizer. -/
theorem M11aCentralizer_map_le_ambient :
    M11aCentralizer.map M11Subgroup.subtype ≤
      Subgroup.centralizer ({m11a} : Set Perm11) := by
  have hle : M11aCentralizer.map M11Subgroup.subtype ≤
      Subgroup.centralizer (M11Subgroup.subtype '' ({m11aM11} : Set M11)) := by
    exact Subgroup.map_centralizer_le_centralizer_image ({m11aM11} : Set M11)
      M11Subgroup.subtype
  have himage : M11Subgroup.subtype '' ({m11aM11} : Set M11) = ({m11a} : Set Perm11) := by
    ext x
    simp
  change M11aCentralizer.map M11Subgroup.subtype ≤
    Subgroup.centralizer ({m11a} : Set Perm11)
  rw [himage] at hle
  exact hle

/-- Upper bound for the `M11` centralizer of `m11a`, from the ambient centralizer. -/
theorem M11aCentralizer_card_le : Nat.card M11aCentralizer ≤ 11 := by
  have hmapcard : Nat.card (M11aCentralizer.map M11Subgroup.subtype) =
      Nat.card M11aCentralizer :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le M11aCentralizer_map_le_ambient
  rw [hmapcard, ambient_m11a_centralizer_card] at hle
  exact hle

/-- Lower bound for the `M11` centralizer of `m11a`, from its cyclic subgroup. -/
theorem M11aCentralizer_card_ge : 11 ≤ Nat.card M11aCentralizer := by
  have hle := Subgroup.card_le_of_le m11a_zpowers_le_centralizer
  rw [m11a_zpowers_card] at hle
  exact hle

/-- The `M11` centralizer of the 11A representative has the listed order 11. -/
theorem M11aCentralizer_card : Nat.card M11aCentralizer = 11 :=
  le_antisymm M11aCentralizer_card_le M11aCentralizer_card_ge

/-!
The centralizer computation also gives the conjugacy orbit size for the 11A
representative by orbit-stabilizer.
-/

/--
The stabilizer of `m11aM11` under conjugation is equivalent to the centralizer
of `m11aM11`.
-/
noncomputable def m11aConjActStabilizerEquivCentralizer :
    MulAction.stabilizer (ConjAct M11) m11aM11 ≃ M11aCentralizer where
  toFun s := ⟨ConjAct.ofConjAct s.1, by
    change ConjAct.ofConjAct s.1 ∈ Subgroup.centralizer ({m11aM11} : Set M11)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs : s.1 • m11aM11 = m11aM11 := s.2
    rw [ConjAct.smul_def] at hs
    have hs' : ConjAct.ofConjAct s.1 * m11aM11 * (ConjAct.ofConjAct s.1)⁻¹ =
        m11aM11 := hs
    rw [mul_inv_eq_iff_eq_mul] at hs'
    exact hs'⟩
  invFun c := ⟨ConjAct.toConjAct c.1, by
    change ConjAct.toConjAct c.1 • m11aM11 = m11aM11
    rw [ConjAct.toConjAct_smul]
    have hc : c.1 * m11aM11 = m11aM11 * c.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [mul_inv_eq_iff_eq_mul]
    exact hc⟩
  left_inv s := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- The conjugation stabilizer of the 11A representative has order 11. -/
theorem m11aConjActStabilizer_card :
    Fintype.card (MulAction.stabilizer (ConjAct M11) m11aM11) = 11 := by
  classical
  exact (Fintype.card_congr m11aConjActStabilizerEquivCentralizer).trans (by
    rw [← Nat.card_eq_fintype_card, M11aCentralizer_card])

/-- The conjugacy orbit of the 11A representative has size 720. -/
theorem m11aConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) m11aM11) = 720 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) m11aM11
  rw [m11aConjActStabilizer_card] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) m11aM11) = 720 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-!
## Centralizer and orbit check for the 11B representative

The same centralizer/orbit-stabilizer route also verifies the second class-table
row of order 11.
-/

/-- Generic equivalence between a conjugation stabilizer and a centralizer. -/
noncomputable def conjActStabilizerEquivCentralizer (g : M11) :
    MulAction.stabilizer (ConjAct M11) g ≃ Subgroup.centralizer ({g} : Set M11) where
  toFun s := ⟨ConjAct.ofConjAct s.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs : s.1 • g = g := s.2
    rw [ConjAct.smul_def] at hs
    have hs' : ConjAct.ofConjAct s.1 * g * (ConjAct.ofConjAct s.1)⁻¹ = g := hs
    rw [mul_inv_eq_iff_eq_mul] at hs'
    exact hs'⟩
  invFun c := ⟨ConjAct.toConjAct c.1, by
    change ConjAct.toConjAct c.1 • g = g
    rw [ConjAct.toConjAct_smul]
    have hc : c.1 * g = g * c.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [mul_inv_eq_iff_eq_mul]
    exact hc⟩
  left_inv s := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- Cardinality form of `conjActStabilizerEquivCentralizer`. -/
theorem conjActStabilizer_card_eq_centralizer_card (g : M11) :
    Fintype.card (MulAction.stabilizer (ConjAct M11) g) =
      Nat.card (Subgroup.centralizer ({g} : Set M11)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr (conjActStabilizerEquivCentralizer g)

/-- If a conjugation centralizer has order 11, then the conjugacy orbit has size 720. -/
theorem conjOrbit_card_of_centralizer_card_eq_eleven (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 11) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 720 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 11 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 720 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- If a conjugation centralizer has order 8, then the conjugacy orbit has size 990. -/
theorem conjOrbit_card_of_centralizer_card_eq_eight (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 8) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 990 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 8 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 990 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- If a conjugation centralizer has order 5, then the conjugacy orbit has size 1584. -/
theorem conjOrbit_card_of_centralizer_card_eq_five (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 5) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 1584 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 5 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 1584 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- If a conjugation centralizer has order 6, then the conjugacy orbit has size 1320. -/
theorem conjOrbit_card_of_centralizer_card_eq_six (g : M11)
    (hcentralizer : Nat.card (Subgroup.centralizer ({g} : Set M11)) = 6) :
    Nat.card (MulAction.orbit (ConjAct M11) g) = 1320 := by
  classical
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct M11) g
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct M11) g) = 6 := by
    rw [conjActStabilizer_card_eq_centralizer_card, hcentralizer]
  rw [hstab] at h
  have hG : Fintype.card (ConjAct M11) = 7920 := by
    rw [ConjAct.card]
    rw [← Nat.card_eq_fintype_card]
    exact M11Cardinality.card_M11
  rw [hG] at h
  have horbit : Fintype.card (MulAction.orbit (ConjAct M11) g) = 1320 := by
    omega
  rw [Nat.card_eq_fintype_card]
  exact horbit

/-- The conjugacy orbit of the 5A representative has size `1584`. -/
theorem rep5AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep5AIndex)) = 1584 :=
  conjOrbit_card_of_centralizer_card_eq_five
    (representativeM11 rep5AIndex) rep5A_centralizer_card

/-- The conjugacy orbit of the 6A representative has size `1320`. -/
theorem rep6AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep6AIndex)) = 1320 :=
  conjOrbit_card_of_centralizer_card_eq_six
    (representativeM11 rep6AIndex) rep6A_centralizer_card

/-- The conjugacy orbit of the 8A representative has size `990`. -/
theorem rep8AConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep8AIndex)) = 990 :=
  conjOrbit_card_of_centralizer_card_eq_eight
    (representativeM11 rep8AIndex) rep8A_centralizer_card

/-- The conjugacy orbit of the 8B representative has size `990`. -/
theorem rep8BConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) (representativeM11 rep8BIndex)) = 990 :=
  conjOrbit_card_of_centralizer_card_eq_eight
    (representativeM11 rep8BIndex) rep8B_centralizer_card

/-- The class-table index of the 11B representative. -/
abbrev rep11BIndex : Fin 10 :=
  ⟨9, by decide⟩

/-- Candidate 11B representative as an ambient permutation. -/
abbrev rep11BPerm : Perm11 :=
  representativePerm rep11BIndex

/-- Candidate 11B representative as an element of `M11`. -/
abbrev rep11BM11 : M11 :=
  representativeM11 rep11BIndex

/-- The centralizer in `M11` of the 11B representative. -/
abbrev M11Rep11BCentralizer : Subgroup M11 :=
  Subgroup.centralizer ({rep11BM11} : Set M11)

/-- The 11B ambient representative has order 11. -/
theorem rep11B_orderOf : orderOf rep11BPerm = 11 := by
  simpa [rep11BPerm, rep11BIndex, classElementOrder, classElementOrderList]
    using representativePerm_orderOf_eq rep11BIndex

/-- The cyclic subgroup generated by the 11B representative has order 11. -/
theorem rep11B_zpowers_card : Nat.card (Subgroup.zpowers rep11BM11) = 11 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_zpowers]
  change orderOf (⟨rep11BPerm, Word.eval_mem_M11Subgroup (representativeWord rep11BIndex)⟩ :
    M11) = 11
  rw [Subgroup.orderOf_mk]
  exact rep11B_orderOf

/-- The cyclic subgroup generated by the 11B representative centralizes it. -/
theorem rep11B_zpowers_le_centralizer :
    Subgroup.zpowers rep11BM11 ≤ M11Rep11BCentralizer := by
  intro x hx
  change x ∈ Subgroup.centralizer ({rep11BM11} : Set M11)
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_zpowers_iff] at hx
  rcases hx with ⟨n, hn⟩
  rw [← hn]
  exact (Commute.zpow_self (a := rep11BM11) (n := n)).eq

set_option maxRecDepth 100000 in
/-- The ambient symmetric-group centralizer of the 11B representative has order 11. -/
theorem ambient_rep11B_centralizer_card :
    Nat.card (Subgroup.centralizer ({rep11BPerm} : Set Perm11)) = 11 := by
  rw [Equiv.Perm.nat_card_centralizer]
  norm_num
  decide

/-- The `M11` centralizer of the 11B representative maps into the ambient centralizer. -/
theorem M11Rep11BCentralizer_map_le_ambient :
    M11Rep11BCentralizer.map M11Subgroup.subtype ≤
      Subgroup.centralizer ({rep11BPerm} : Set Perm11) := by
  have hle : M11Rep11BCentralizer.map M11Subgroup.subtype ≤
      Subgroup.centralizer (M11Subgroup.subtype '' ({rep11BM11} : Set M11)) := by
    exact Subgroup.map_centralizer_le_centralizer_image ({rep11BM11} : Set M11)
      M11Subgroup.subtype
  have himage : M11Subgroup.subtype '' ({rep11BM11} : Set M11) =
      ({rep11BPerm} : Set Perm11) := by
    ext x
    simp [rep11BM11, rep11BPerm, representativeM11, representativePerm]
  change M11Rep11BCentralizer.map M11Subgroup.subtype ≤
    Subgroup.centralizer ({rep11BPerm} : Set Perm11)
  rw [himage] at hle
  exact hle

/-- Upper bound for the `M11` centralizer of the 11B representative. -/
theorem M11Rep11BCentralizer_card_le : Nat.card M11Rep11BCentralizer ≤ 11 := by
  have hmapcard : Nat.card (M11Rep11BCentralizer.map M11Subgroup.subtype) =
      Nat.card M11Rep11BCentralizer :=
    Subgroup.card_map_of_injective M11Subgroup.subtype_injective
  have hle := Subgroup.card_le_of_le M11Rep11BCentralizer_map_le_ambient
  rw [hmapcard, ambient_rep11B_centralizer_card] at hle
  exact hle

/-- Lower bound for the `M11` centralizer of the 11B representative. -/
theorem M11Rep11BCentralizer_card_ge : 11 ≤ Nat.card M11Rep11BCentralizer := by
  have hle := Subgroup.card_le_of_le rep11B_zpowers_le_centralizer
  rw [rep11B_zpowers_card] at hle
  exact hle

/-- The `M11` centralizer of the 11B representative has the listed order 11. -/
theorem M11Rep11BCentralizer_card : Nat.card M11Rep11BCentralizer = 11 :=
  le_antisymm M11Rep11BCentralizer_card_le M11Rep11BCentralizer_card_ge

/-- The conjugation stabilizer of the 11B representative has order 11. -/
theorem rep11BConjActStabilizer_card :
    Fintype.card (MulAction.stabilizer (ConjAct M11) rep11BM11) = 11 := by
  rw [conjActStabilizer_card_eq_centralizer_card, M11Rep11BCentralizer_card]

/-- The conjugacy orbit of the 11B representative has size 720. -/
theorem rep11BConjOrbit_card :
    Nat.card (MulAction.orbit (ConjAct M11) rep11BM11) = 720 :=
  conjOrbit_card_of_centralizer_card_eq_eleven rep11BM11 M11Rep11BCentralizer_card

end ConjugacyClasses
end Certificates
end Sporadic
