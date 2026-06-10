/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.M11Embedding
import FiniteSimpleGroups.Sporadic.M12.Cardinality

/-!
# The stabilizer of the twelfth point

This file identifies the stabilizer of the point `11` in `M12` with the
embedded copy of `M11`, and concludes that the point stabilizer is a simple
group of order `7920`.

The identification uses:

* a word certificate showing that the orbit of `11` is all of `Fin 12`, hence
  `|Stab(11)| = 95040 / 12 = 7920` by orbit-stabilizer;
* the inclusion of the embedded `M11` (which fixes `11`) into the stabilizer;
* the cardinality `7920` of the embedded `M11`, transported from the `M11`
  project, forcing the inclusion to be an equality.
-/

namespace Sporadic
namespace M12PointStabilizer

open M12Certificates
open M11Embedding

/-- The stabilizer of the twelfth point `11` in the 12-point action. -/
def StabEleven : Subgroup M12 :=
  MulAction.stabilizer M12 (11 : Fin 12)

/--
Word certificate sending `11` to `x`: first apply `c` (which sends `11`
to `0`), then the first-step orbit word.
-/
def elevenOrbitWord (x : Fin 12) : Word :=
  Gen.c :: StabilizerChain.orbitZeroWord x

set_option maxRecDepth 20000 in
/-- The certificate words send `11` to every point of `Fin 12`. -/
theorem elevenOrbitWord_maps_eleven_all :
    ∀ x : Fin 12, (Word.eval (elevenOrbitWord x)) (11 : Fin 12) = x := by
  decide

/-- Every point of `Fin 12` is reached from `11` by an element of `M12`. -/
theorem orbit_eleven_M12_witness (x : Fin 12) :
    ∃ g : M12, g.1 (11 : Fin 12) = x :=
  ⟨Word.toM12 (elevenOrbitWord x), by simpa using elevenOrbitWord_maps_eleven_all x⟩

/-- The orbit of `11` under `M12` is all of `Fin 12`. -/
theorem orbit_eleven_eq_univ : MulAction.orbit M12 (11 : Fin 12) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨g, hg⟩ := orbit_eleven_M12_witness x
    exact ⟨g, by simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg⟩

/-- The orbit of `11` has size 12. -/
theorem orbit_eleven_ncard : (MulAction.orbit M12 (11 : Fin 12)).ncard = 12 := by
  rw [orbit_eleven_eq_univ, Set.ncard_univ]
  simp

/-- Orbit-stabilizer for the twelfth point. -/
theorem card_M12_eq_twelve_mul_stabEleven :
    Nat.card M12 = 12 * Nat.card StabEleven := by
  classical
  rw [Nat.card_eq_fintype_card,
    ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group M12 (11 : Fin 12)]
  rw [Set.fintypeCard_eq_ncard, orbit_eleven_ncard]
  rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer M12 (11 : Fin 12))]
  rfl

/-- The stabilizer of the twelfth point has order `7920`. -/
theorem card_stabEleven : Nat.card StabEleven = 7920 := by
  have h := card_M12_eq_twelve_mul_stabEleven
  rw [M12Cardinality.card_M12] at h
  omega

/-- The embedded `M11`, viewed as a subgroup of `M12`. -/
def EmbeddedM11InM12 : Subgroup M12 :=
  EmbeddedM11.subgroupOf M12Subgroup

/-- The embedded `M11` inside `M12` is isomorphic to the ambient embedded copy. -/
noncomputable def embeddedInM12Equiv : EmbeddedM11InM12 ≃* EmbeddedM11 :=
  Subgroup.subgroupOfEquivOfLe embeddedM11_le_M12Subgroup

/-- The embedded `M11` inside `M12` has order `7920`. -/
theorem card_embeddedInM12 : Nat.card EmbeddedM11InM12 = 7920 := by
  rw [Nat.card_congr embeddedInM12Equiv.toEquiv]
  exact card_embeddedM11

/-- The embedded `M11` inside `M12` is contained in the stabilizer of `11`. -/
theorem embeddedInM12_le_stabEleven : EmbeddedM11InM12 ≤ StabEleven := by
  intro g hg
  have hfix : g.1 (11 : Fin 12) = 11 :=
    fixes_eleven_of_mem_embeddedM11 (Subgroup.mem_subgroupOf.mp hg)
  rw [StabEleven, MulAction.mem_stabilizer_iff]
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hfix

/-- The embedded `M11` inside `M12` is exactly the stabilizer of `11`. -/
theorem embeddedInM12_eq_stabEleven : EmbeddedM11InM12 = StabEleven := by
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le
  · exact embeddedInM12_le_stabEleven
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rw [SetLike.coe_sort_coe, SetLike.coe_sort_coe]
    rw [card_stabEleven, card_embeddedInM12]
  · exact Set.toFinite _

/-- The stabilizer of `11` is isomorphic to the `M11` project's group. -/
noncomputable def stabElevenEquivM11 : StabEleven ≃* M11 :=
  ((MulEquiv.subgroupCongr embeddedInM12_eq_stabEleven).symm.trans
    embeddedInM12Equiv).trans embeddedM11Equiv.symm

/-- The stabilizer of `11` is a simple group, transported from `simple_M11`. -/
theorem isSimpleGroup_stabEleven : IsSimpleGroup StabEleven := by
  haveI := simple_M11
  exact stabElevenEquivM11.isSimpleGroup

end M12PointStabilizer
end Sporadic
