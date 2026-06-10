/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.L34.Basic

/-!
# Words in the L34 generators

A three-letter alphabet: the generators are involutions, so no inverse
letters are needed.
-/

namespace Sporadic
namespace L34

/-- Generator alphabet (all three generators are involutions). -/
inductive Gen where
  | e1
  | e2
  | e3
  deriving DecidableEq, Repr

/-- A certificate word over the generator alphabet. -/
abbrev Word : Type :=
  List Gen

namespace Gen

/-- Interpret a generator letter as a degree-21 permutation. -/
def toPerm : Gen → Perm21
  | e1 => l34e1
  | e2 => l34e2
  | e3 => l34e3

/-- Each generator letter evaluates to an element of the generated subgroup. -/
theorem toPerm_mem_L34Subgroup (g : Gen) : g.toPerm ∈ L34Subgroup := by
  cases g <;> simp [toPerm, l34e1_mem, l34e2_mem, l34e3_mem]

end Gen

namespace Word

/-- Evaluate a certificate word as a permutation. -/
def eval : Word → Perm21
  | [] => 1
  | g :: rest => eval rest * g.toPerm

@[simp]
theorem eval_nil : eval [] = (1 : Perm21) :=
  rfl

@[simp]
theorem eval_cons (g : Gen) (rest : Word) :
    eval (g :: rest) = eval rest * g.toPerm :=
  rfl

/-- A word always evaluates to an element of `L34Subgroup`. -/
theorem eval_mem_L34Subgroup : ∀ w : Word, eval w ∈ L34Subgroup
  | [] => by simp [eval]
  | g :: rest => by
      exact L34Subgroup.mul_mem (eval_mem_L34Subgroup rest)
        (Gen.toPerm_mem_L34Subgroup g)

/-- Interpret a word as an element of the generated group. -/
def toL34 (w : Word) : L34Subgroup :=
  ⟨eval w, eval_mem_L34Subgroup w⟩

@[simp]
theorem toL34_toPerm (w : Word) : (toL34 w).1 = eval w :=
  rfl

end Word

end L34
end Sporadic
