/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Basic namespace for the M12 experiment

This project formalizes the second experimental sporadic group target:
Mathieu's group `M12`, represented as a subgroup of `Equiv.Perm (Fin 12)`.

The public API is intended to live in the namespace `Sporadic`.
-/

namespace Sporadic

/-- The ambient permutation group for the degree-12 representation. -/
abbrev Perm12 : Type := Equiv.Perm (Fin 12)

end Sporadic
