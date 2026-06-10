/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.GeneratedSubgroup

/-!
# Words in the M22 generators

This file defines the small, auditable word language that certificates use.
A certificate may contain words over `a`, `a⁻¹`, `b`, and `b⁻¹`;
Lean evaluates those words in `Equiv.Perm (Fin 22)` and proves that their
values belong to the generated subgroup.
-/

namespace Sporadic
namespace M22Certificates

/-- Generator alphabet for the two-generator presentation. -/
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

/-- Interpret a generator letter as a degree-22 permutation. -/
def toPerm : Gen → Perm22
  | a => m22a
  | aInv => m22a⁻¹
  | b => m22b
  | bInv => m22b⁻¹

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_M22Subgroup (g : Gen) : g.toPerm ∈ M22Subgroup := by
  cases g <;>
    simp [toPerm, m22a_mem_M22Subgroup, m22b_mem_M22Subgroup]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm22
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm22) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `M22Subgroup`. -/
theorem eval_mem_M22Subgroup : ∀ w : Word, eval w ∈ M22Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact M22Subgroup.mul_mem (eval_mem_M22Subgroup rest) (Gen.toPerm_mem_M22Subgroup g)

/-- Interpret a word as an element of the generated group `M22`. -/
def toM22 (w : Word) : M22 :=
  ⟨eval w, eval_mem_M22Subgroup w⟩

@[simp]
theorem toM22_toPerm (w : Word) : (toM22 w).1 = eval w :=
  rfl

end Word

end M22Certificates
end Sporadic
