/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import FiniteSimpleGroups.Sporadic.M12.Basic

/-!
# Explicit degree-12 permutations

The three generators below are the classical degree-12 permutation generators
recorded in `docs/provenance.md`: the two `M11` generators (fixing the new
twelfth point) together with an involution moving it. They are input data for
certificates, not trusted mathematical facts.
-/

namespace Sporadic

open Equiv Equiv.Perm

/-- The 11-cycle `(1,2,3,4,5,6,7,8,9,10,11)` in zero-based `Fin 12` notation.
It fixes the twelfth point `11`. -/
def m12a : Perm12 :=
  List.formPerm ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 12))

/--
The permutation `(3,7,11,8)(4,10,5,6)` in one-based notation, written as
`(2,6,10,7)(3,9,4,5)` on `Fin 12`. It also fixes the twelfth point `11`.
-/
def m12b : Perm12 :=
  List.formPerm ([2, 6, 10, 7] : List (Fin 12)) *
    List.formPerm ([3, 9, 4, 5] : List (Fin 12))

/--
The involution `(1,12)(2,11)(3,6)(4,8)(5,9)(7,10)` in one-based notation,
written as `(0,11)(1,10)(2,5)(3,7)(4,8)(6,9)` on `Fin 12`. This is the
classical element extending `M11` to `M12`.
-/
def m12c : Perm12 :=
  List.formPerm ([0, 11] : List (Fin 12)) *
    List.formPerm ([1, 10] : List (Fin 12)) *
    List.formPerm ([2, 5] : List (Fin 12)) *
    List.formPerm ([3, 7] : List (Fin 12)) *
    List.formPerm ([4, 8] : List (Fin 12)) *
    List.formPerm ([6, 9] : List (Fin 12))

/-- Milestone sanity check: `m12a` is an equivalence, hence a permutation. -/
theorem m12a_bijective : Function.Bijective m12a :=
  m12a.bijective

/-- Milestone sanity check: `m12b` is an equivalence, hence a permutation. -/
theorem m12b_bijective : Function.Bijective m12b :=
  m12b.bijective

/-- Milestone sanity check: `m12c` is an equivalence, hence a permutation. -/
theorem m12c_bijective : Function.Bijective m12c :=
  m12c.bijective

end Sporadic
