/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import FiniteSimpleGroups.Sporadic.M11.Basic

/-!
# Explicit degree-11 permutations

The two generators below are the standard degree-11 permutation generators
recorded in `docs/provenance.md`. They are input data for certificates, not
trusted mathematical facts.
-/

namespace Sporadic

open Equiv Equiv.Perm

/-- The 11-cycle `(1,2,3,4,5,6,7,8,9,10,11)` in zero-based `Fin 11` notation. -/
def m11a : Perm11 :=
  List.formPerm ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 11))

/--
The permutation `(3,7,11,8)(4,10,5,6)` in one-based notation, written as
`(2,6,10,7)(3,9,4,5)` on `Fin 11`.
-/
def m11b : Perm11 :=
  List.formPerm ([2, 6, 10, 7] : List (Fin 11)) *
    List.formPerm ([3, 9, 4, 5] : List (Fin 11))

/-- Milestone 1 sanity check: `m11a` is an equivalence, hence a permutation. -/
theorem m11a_bijective : Function.Bijective m11a :=
  m11a.bijective

/-- Milestone 1 sanity check: `m11b` is an equivalence, hence a permutation. -/
theorem m11b_bijective : Function.Bijective m11b :=
  m11b.bijective

end Sporadic
