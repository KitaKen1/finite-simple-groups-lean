/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.GeneratedSubgroup

/-!
# Words in the M12 generators

This file defines the small, auditable word language that certificates use.
A certificate may contain words over `a`, `a⁻¹`, `b`, `b⁻¹`, `c`, and `c⁻¹`;
Lean evaluates those words in `Equiv.Perm (Fin 12)` and proves that their values
belong to the generated subgroup.
-/

namespace Sporadic
namespace M12Certificates

/-- Generator alphabet for the current three-generator presentation experiment. -/
inductive Gen where
  | a
  | aInv
  | b
  | bInv
  | c
  | cInv
  deriving DecidableEq, Repr

/-- A certificate word over the generator alphabet. -/
abbrev Word : Type :=
  List Gen

namespace Gen

/-- Interpret a generator letter as a degree-12 permutation. -/
def toPerm : Gen → Perm12
  | a => m12a
  | aInv => m12a⁻¹
  | b => m12b
  | bInv => m12b⁻¹
  | c => m12c
  | cInv => m12c⁻¹

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_M12Subgroup (g : Gen) : g.toPerm ∈ M12Subgroup := by
  cases g <;>
    simp [toPerm, m12a_mem_M12Subgroup, m12b_mem_M12Subgroup, m12c_mem_M12Subgroup]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm12
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm12) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `M12Subgroup`. -/
theorem eval_mem_M12Subgroup : ∀ w : Word, eval w ∈ M12Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact M12Subgroup.mul_mem (eval_mem_M12Subgroup rest) (Gen.toPerm_mem_M12Subgroup g)

/-- Interpret a word as an element of the generated group `M12`. -/
def toM12 (w : Word) : M12 :=
  ⟨eval w, eval_mem_M12Subgroup w⟩

@[simp]
theorem toM12_toPerm (w : Word) : (toM12 w).1 = eval w :=
  rfl

end Word

end M12Certificates
end Sporadic
