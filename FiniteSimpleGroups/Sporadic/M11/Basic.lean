/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Basic namespace for the M11 experiment

This project formalizes the first experimental sporadic group target:
Mathieu's group `M11`, represented as a subgroup of `Equiv.Perm (Fin 11)`.

The public API is intended to live in the namespace `Sporadic`.
-/

namespace Sporadic

/-- The ambient permutation group for the degree-11 representation. -/
abbrev Perm11 : Type := Equiv.Perm (Fin 11)

end Sporadic
