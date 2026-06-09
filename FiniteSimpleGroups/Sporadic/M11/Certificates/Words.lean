/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.GeneratedSubgroup

/-!
# Words in the M11 generators

This file defines the small, auditable word language that future certificates
will use. A certificate may contain words over `a`, `a⁻¹`, `b`, and `b⁻¹`;
Lean evaluates those words in `Equiv.Perm (Fin 11)` and proves that their values
belong to the generated subgroup.
-/

namespace Sporadic
namespace Certificates

/-- Generator alphabet for the current two-generator presentation experiment. -/
inductive Gen where
  | a
  | aInv
  | b
  | bInv
  deriving DecidableEq, Repr

/-- A certificate word over the generator alphabet. -/
abbrev Word : Type :=
  List Gen

namespace Gen

/-- Interpret a generator letter as a degree-11 permutation. -/
def toPerm : Gen → Perm11
  | a => m11a
  | aInv => m11a⁻¹
  | b => m11b
  | bInv => m11b⁻¹

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_M11Subgroup (g : Gen) : g.toPerm ∈ M11Subgroup := by
  cases g <;> simp [toPerm, m11a_mem_M11Subgroup, m11b_mem_M11Subgroup]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm11
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm11) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `M11Subgroup`. -/
theorem eval_mem_M11Subgroup : ∀ w : Word, eval w ∈ M11Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact M11Subgroup.mul_mem (eval_mem_M11Subgroup rest) (Gen.toPerm_mem_M11Subgroup g)

/-- Interpret a word as an element of the generated group `M11`. -/
def toM11 (w : Word) : M11 :=
  ⟨eval w, eval_mem_M11Subgroup w⟩

@[simp]
theorem toM11_toPerm (w : Word) : (toM11 w).1 = eval w :=
  rfl

end Word

end Certificates
end Sporadic
