/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Basic namespace for the M22 experiment

This project formalizes the third experimental sporadic group target:
Mathieu's group `M22`, represented as a subgroup of `Equiv.Perm (Fin 22)`.

The public API is intended to live in the namespace `Sporadic`.
-/

namespace Sporadic

/-- The ambient permutation group for the degree-22 representation. -/
abbrev Perm22 : Type := Equiv.Perm (Fin 22)

end Sporadic
