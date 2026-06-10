/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import FiniteSimpleGroups.Sporadic.M22.Basic

/-!
# Explicit degree-22 permutations

The two generators below were produced by `scripts/build_m22.py`, which
constructs `M22` from first principles (PG(2,4), PSL(3,4), and the Steiner
system `S(3,6,22)`) and then extracts a verified 2-element generating set.
They are input data for certificates, not trusted mathematical facts: Lean
re-verifies the order and block certificates.
-/

namespace Sporadic

open Equiv Equiv.Perm

/-- The first generator: a product of four 5-cycles (order 5). -/
def m22a : Perm22 :=
  List.formPerm ([0, 11, 4, 5, 15] : List (Fin 22)) *
    List.formPerm ([1, 14, 21, 10, 18] : List (Fin 22)) *
    List.formPerm ([2, 7, 8, 16, 12] : List (Fin 22)) *
    List.formPerm ([3, 13, 9, 19, 20] : List (Fin 22))

/-- The second generator: a product of two 8-cycles, a 4-cycle, and a
2-cycle (order 8). -/
def m22b : Perm22 :=
  List.formPerm ([0, 17, 10, 19, 18, 8, 3, 1] : List (Fin 22)) *
    List.formPerm ([2, 14] : List (Fin 22)) *
    List.formPerm ([4, 7, 6, 15] : List (Fin 22)) *
    List.formPerm ([5, 21, 12, 13, 9, 11, 16, 20] : List (Fin 22))

/-- Milestone sanity check: `m22a` is an equivalence, hence a permutation. -/
theorem m22a_bijective : Function.Bijective m22a :=
  m22a.bijective

/-- Milestone sanity check: `m22b` is an equivalence, hence a permutation. -/
theorem m22b_bijective : Function.Bijective m22b :=
  m22b.bijective

end Sporadic
