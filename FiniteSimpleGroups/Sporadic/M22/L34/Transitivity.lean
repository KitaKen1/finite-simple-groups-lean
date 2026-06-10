/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.L34.Words

/-!
# Transitivity certificates for L34

Word tables for the 21-point action: the orbit of `0`, the orbit of `1`
under the stabilizer of `0`, and 48 distinct elements of the two-point
stabilizer (used for the cardinality lower bound).
-/

namespace Sporadic
namespace L34

/-- Words sending `0` to `x`. -/
def orbitZeroWord (x : Fin 21) : Word :=
  match x.val with
  | 1 => [Gen.e1, Gen.e3, Gen.e2, Gen.e3]
  | 2 => [Gen.e1, Gen.e3, Gen.e2, Gen.e1]
  | 3 => [Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1]
  | 4 => [Gen.e1, Gen.e3, Gen.e1]
  | 5 => [Gen.e3, Gen.e2, Gen.e3]
  | 6 => [Gen.e1, Gen.e3]
  | 7 => [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1]
  | 8 => [Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3]
  | 9 => [Gen.e1, Gen.e3, Gen.e1, Gen.e2]
  | 10 => [Gen.e1, Gen.e3, Gen.e2]
  | 11 => [Gen.e3, Gen.e1]
  | 12 => [Gen.e3, Gen.e2]
  | 13 => [Gen.e3]
  | 14 => [Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2]
  | 15 => [Gen.e3, Gen.e2, Gen.e3, Gen.e1]
  | 16 => [Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3]
  | 17 => [Gen.e3, Gen.e1, Gen.e3]
  | 18 => [Gen.e1]
  | 19 => [Gen.e1, Gen.e3, Gen.e1, Gen.e3]
  | 20 => [Gen.e2]
  | _ => []

/-- Words fixing `0` and sending `1` to `x` (for `x ≠ 0`). -/
def zeroStabWord (x : Fin 21) : Word :=
  match x.val with
  | 2 => [Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1]
  | 3 => [Gen.e1, Gen.e2, Gen.e1]
  | 4 => [Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3]
  | 5 => [Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3]
  | 6 => [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2]
  | 7 => [Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2]
  | 8 => [Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1]
  | 9 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3]
  | 10 => [Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3]
  | 11 => [Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3]
  | 12 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2]
  | 13 => [Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2]
  | 14 => [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3]
  | 15 => [Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3]
  | 16 => [Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1]
  | 17 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2]
  | 18 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2]
  | 19 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2]
  | 20 => [Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2]
  | _ => []

set_option maxRecDepth 400000 in
/-- The first-table words send `0` to every point. -/
theorem orbitZeroWord_maps_zero_all :
    ∀ x : Fin 21, (Word.eval (orbitZeroWord x)) (0 : Fin 21) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The second-table words fix `0`. -/
theorem zeroStabWord_fixes_zero_all :
    ∀ x : Fin 21, x ≠ 0 → (Word.eval (zeroStabWord x)) (0 : Fin 21) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The second-table words send `1` to the requested nonzero point. -/
theorem zeroStabWord_maps_one_all :
    ∀ x : Fin 21, x ≠ 0 → (Word.eval (zeroStabWord x)) (1 : Fin 21) = x := by
  decide

/-- 48 candidate words for distinct elements fixing `0` and `1`. -/
def stab01WordList : List Word :=
  [
    [],
    [Gen.e2, Gen.e3, Gen.e2],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2],
    [Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3],
    [Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1],
    [Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2],
    [Gen.e1, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e2, Gen.e1],
    [Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3],
    [Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e1, Gen.e2, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e2, Gen.e1, Gen.e3, Gen.e1, Gen.e3, Gen.e2]
  ]

set_option maxRecDepth 400000 in
/-- Every listed word fixes `0`. -/
theorem stab01WordList_fixes_zero :
    ∀ w ∈ stab01WordList, (Word.eval w) (0 : Fin 21) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- Every listed word fixes `1`. -/
theorem stab01WordList_fixes_one :
    ∀ w ∈ stab01WordList, (Word.eval w) (1 : Fin 21) = 1 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 3200000 in
-- The pairwise-distinctness certificate is intentionally checked by computation.
/-- The 48 listed words evaluate to pairwise distinct permutations. -/
theorem stab01WordList_evals_nodup :
    (stab01WordList.map Word.eval).Nodup := by
  decide

theorem stab01WordList_length : stab01WordList.length = 48 := by
  decide

end L34
end Sporadic
