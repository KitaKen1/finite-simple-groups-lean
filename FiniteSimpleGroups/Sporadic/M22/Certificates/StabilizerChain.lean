/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.Certificates.Words
import FiniteSimpleGroups.Sporadic.M22.Certificates.SteinerSystem

/-!
# Stabilizer-chain certificates

Verified data for the cardinality route with base `0, 1, 2, 5, 3`:

* orbit of `0` has size `22`;
* the stabilizer of `0` has orbit size `21`;
* the stabilizer of `0,1` has orbit size `20`;
* the stabilizer of `0,1,2` moves `5` through the 16 points outside the
  block `B0 = {0,1,2,3,4,21}` (which it preserves);
* the stabilizer of `0,1,2,5` moves `3` through the 3 points
  `{3,4,21} = B0 \ {0,1,2}`;
* the stabilizer of `0,1,2,5,3` is trivial (`FinalStabilizer.lean`).

No external computation is trusted here until it is represented as data and
checked by Lean.
-/

namespace Sporadic
namespace M22Certificates
namespace StabilizerChain

open SteinerSystem

/-- The product of the target stabilizer-chain indices. -/
theorem target_index_product : 22 * 21 * 20 * 16 * 3 = 443520 := by
  norm_num

/-- First-step words: `orbitZeroWord x` sends `0` to `x`. -/
def orbitZeroWord (x : Fin 22) : Word :=
  match x.val with
  | 1 => [Gen.bInv]
  | 2 => [Gen.bInv, Gen.a, Gen.b]
  | 3 => [Gen.bInv, Gen.bInv]
  | 4 => [Gen.a, Gen.a]
  | 5 => [Gen.aInv, Gen.aInv]
  | 6 => [Gen.aInv, Gen.bInv]
  | 7 => [Gen.a, Gen.a, Gen.b]
  | 8 => [Gen.a, Gen.b, Gen.aInv]
  | 9 => [Gen.a, Gen.bInv]
  | 10 => [Gen.b, Gen.b]
  | 11 => [Gen.a]
  | 12 => [Gen.a, Gen.b, Gen.a]
  | 13 => [Gen.a, Gen.bInv, Gen.aInv]
  | 14 => [Gen.bInv, Gen.a]
  | 15 => [Gen.aInv]
  | 16 => [Gen.a, Gen.b]
  | 17 => [Gen.b]
  | 18 => [Gen.bInv, Gen.aInv]
  | 19 => [Gen.a, Gen.bInv, Gen.a]
  | 20 => [Gen.a, Gen.b, Gen.b]
  | 21 => [Gen.aInv, Gen.aInv, Gen.b]
  | _ => []

/-- Second-step words: fix `0`, send `1` to `x`. -/
def zeroStabilizerWord (x : Fin 22) : Word :=
  match x.val with
  | 2 => [Gen.aInv, Gen.b, Gen.aInv, Gen.aInv]
  | 3 => [Gen.bInv, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.aInv]
  | 4 => [Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a]
  | 5 => [Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b, Gen.b]
  | 6 => [Gen.b, Gen.aInv, Gen.bInv]
  | 7 => [Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv]
  | 8 => [Gen.a, Gen.b, Gen.b, Gen.b, Gen.a, Gen.a]
  | 9 => [Gen.b, Gen.a, Gen.bInv]
  | 10 => [Gen.b, Gen.b, Gen.a, Gen.a, Gen.b]
  | 11 => [Gen.a, Gen.b, Gen.aInv, Gen.b, Gen.b, Gen.b]
  | 12 => [Gen.a, Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.b]
  | 13 => [Gen.a, Gen.b, Gen.b, Gen.a, Gen.b, Gen.b]
  | 14 => [Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.a]
  | 15 => [Gen.a, Gen.a, Gen.bInv, Gen.a]
  | 16 => [Gen.a, Gen.bInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv]
  | 17 => [Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.bInv]
  | 18 => [Gen.aInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.bInv, Gen.aInv]
  | 19 => [Gen.a, Gen.a, Gen.b, Gen.b, Gen.b, Gen.a]
  | 20 => [Gen.b, Gen.aInv, Gen.aInv, Gen.bInv]
  | 21 => [Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv]
  | _ => []

/-- Third-step words: fix `0,1`, send `2` to `x`. -/
def zeroOneStabilizerWord (x : Fin 22) : Word :=
  match x.val with
  | 3 => [Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.b, Gen.b]
  | 4 => [Gen.a, Gen.a, Gen.bInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a]
  | 5 => [Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a]
  | 6 => [Gen.aInv, Gen.bInv, Gen.bInv, Gen.a, Gen.b, Gen.b, Gen.b]
  | 7 => [Gen.bInv, Gen.bInv, Gen.a, Gen.bInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b]
  | 8 => [Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.b, Gen.a, Gen.b, Gen.b, Gen.a, Gen.a]
  | 9 => [Gen.a, Gen.b, Gen.b, Gen.a, Gen.bInv, Gen.bInv, Gen.a, Gen.b]
  | 10 => [Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a]
  | 11 => [Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.bInv]
  | 12 => [Gen.a, Gen.bInv, Gen.bInv, Gen.a, Gen.a, Gen.bInv, Gen.bInv, Gen.bInv]
  | 13 => [Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.b]
  | 14 => [Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.aInv, Gen.aInv]
  | 15 => [Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.bInv, Gen.aInv]
  | 16 => [Gen.b, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.bInv, Gen.a]
  | 17 => [Gen.bInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.a]
  | 18 => [Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.b, Gen.b]
  | 19 => [Gen.bInv, Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.aInv]
  | 20 => [Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv]
  | 21 => [Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.bInv, Gen.a, Gen.bInv]
  | _ => []

/-- Fourth-step words: fix `0,1,2`, send `5` to `x` (for `x` outside `B0`). -/
def levelFourWord (x : Fin 22) : Word :=
  match x.val with
  | 6 => [Gen.aInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.aInv]
  | 7 => [Gen.aInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b, Gen.a, Gen.a, Gen.b]
  | 8 => [Gen.bInv, Gen.a, Gen.bInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.bInv]
  | 9 => [Gen.aInv, Gen.bInv, Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv]
  | 10 => [Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.b]
  | 11 => [Gen.a, Gen.a, Gen.b, Gen.b, Gen.a, Gen.a, Gen.b, Gen.a]
  | 12 => [Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.b, Gen.b, Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv]
  | 13 => [Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.b, Gen.a, Gen.b, Gen.a, Gen.a]
  | 14 => [Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.bInv, Gen.bInv]
  | 15 => [Gen.b, Gen.a, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.a, Gen.bInv, Gen.aInv, Gen.b]
  | 16 => [Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.b, Gen.b, Gen.a, Gen.bInv, Gen.bInv, Gen.a, Gen.b, Gen.aInv]
  | 17 => [Gen.b, Gen.aInv, Gen.b, Gen.aInv, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.b]
  | 18 => [Gen.a, Gen.a, Gen.b, Gen.b, Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv]
  | 19 => [Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.aInv, Gen.b, Gen.b, Gen.b, Gen.b, Gen.a, Gen.b]
  | 20 => [Gen.b, Gen.b, Gen.a, Gen.b, Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.aInv]
  | _ => []

/-- Fifth-step words: fix `0,1,2,5`, send `3` to `x` (for `x` in `B0 \ {0,1,2}`). -/
def levelFiveWord (x : Fin 22) : Word :=
  match x.val with
  | 4 => [Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.aInv, Gen.b, Gen.b, Gen.a, Gen.a]
  | 21 => [Gen.aInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b]
  | _ => []

set_option maxRecDepth 400000 in
/-- The first-step certificate words send `0` to every point. -/
theorem orbitZeroWord_maps_zero_all :
    ∀ x : Fin 22, (Word.eval (orbitZeroWord x)) (0 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The second-step certificate words fix `0`. -/
theorem zeroStabilizerWord_fixes_zero_all :
    ∀ x : Fin 22, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The second-step certificate words send `1` to the requested point. -/
theorem zeroStabilizerWord_maps_one_all :
    ∀ x : Fin 22, x ≠ 0 → (Word.eval (zeroStabilizerWord x)) (1 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words fix `0`. -/
theorem zeroOneStabilizerWord_fixes_zero_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words fix `1`. -/
theorem zeroOneStabilizerWord_fixes_one_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The third-step certificate words send `2` to the requested point. -/
theorem zeroOneStabilizerWord_maps_two_all :
    ∀ x : Fin 22, x ≠ 0 → x ≠ 1 →
      (Word.eval (zeroOneStabilizerWord x)) (2 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `0`. -/
theorem levelFourWord_fixes_zero_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `1`. -/
theorem levelFourWord_fixes_one_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words fix `2`. -/
theorem levelFourWord_fixes_two_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (2 : Fin 22) = 2 := by
  decide

set_option maxRecDepth 400000 in
/-- The fourth-step certificate words send `5` to the requested point. -/
theorem levelFourWord_maps_five_all :
    ∀ x : Fin 22, x ∈ blockB0ᶜ →
      (Word.eval (levelFourWord x)) (5 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `0`. -/
theorem levelFiveWord_fixes_zero_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (0 : Fin 22) = 0 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `1`. -/
theorem levelFiveWord_fixes_one_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (1 : Fin 22) = 1 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `2`. -/
theorem levelFiveWord_fixes_two_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (2 : Fin 22) = 2 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words fix `5`. -/
theorem levelFiveWord_fixes_five_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (5 : Fin 22) = 5 := by
  decide

set_option maxRecDepth 400000 in
/-- The fifth-step certificate words send `3` to the requested point. -/
theorem levelFiveWord_maps_three_all :
    ∀ x : Fin 22, x = 3 ∨ x = 4 ∨ x = 21 →
      (Word.eval (levelFiveWord x)) (3 : Fin 22) = x := by
  decide

end StabilizerChain
end M22Certificates
end Sporadic
