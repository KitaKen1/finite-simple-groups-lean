/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.Certificates.Words

/-!
# Word certificates around the last point `21`

Tables used by the simplicity proof:

* `lastOrbitWord x` sends `21` to `x` (orbit-stabilizer for the stabilizer
  of `21`);
* `lastStabWord x` fixes `21` and sends `0` to `x` (transitivity of the
  point stabilizer on the remaining 21 points);
* `embWordI` evaluates to the embedded `L34` generators (membership of the
  embedded `PSL(3,4)` in `M22`).
-/

namespace Sporadic
namespace M22Certificates
namespace LastPoint

/-- Words sending `21` to `x`. -/
def lastOrbitWord (x : Fin 22) : Word :=
  match x.val with
  | 0 => [Gen.a, Gen.bInv, Gen.bInv]
  | 1 => [Gen.aInv, Gen.aInv]
  | 2 => [Gen.aInv, Gen.b]
  | 3 => [Gen.aInv, Gen.aInv, Gen.bInv]
  | 4 => [Gen.bInv, Gen.aInv]
  | 5 => [Gen.bInv]
  | 6 => [Gen.bInv, Gen.a, Gen.bInv]
  | 7 => [Gen.aInv, Gen.b, Gen.a]
  | 8 => [Gen.a, Gen.a, Gen.b]
  | 9 => [Gen.a, Gen.b, Gen.aInv]
  | 10 => [Gen.a]
  | 11 => [Gen.b, Gen.aInv, Gen.bInv]
  | 12 => [Gen.b]
  | 13 => [Gen.b, Gen.b]
  | 14 => [Gen.aInv]
  | 15 => [Gen.bInv, Gen.a]
  | 16 => [Gen.b, Gen.aInv]
  | 17 => [Gen.a, Gen.bInv]
  | 18 => [Gen.a, Gen.a]
  | 19 => [Gen.a, Gen.b]
  | 20 => [Gen.bInv, Gen.bInv]
  | _ => []

/-- Words fixing `21` and sending `0` to `x` (for `x ≠ 21`). -/
def lastStabWord (x : Fin 22) : Word :=
  match x.val with
  | 1 => [Gen.aInv, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.b]
  | 2 => [Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.bInv, Gen.a, Gen.bInv]
  | 3 => [Gen.aInv, Gen.aInv, Gen.b, Gen.b, Gen.b, Gen.aInv]
  | 4 => [Gen.a, Gen.bInv, Gen.a, Gen.a, Gen.b, Gen.aInv]
  | 5 => [Gen.a, Gen.bInv, Gen.bInv, Gen.aInv, Gen.aInv, Gen.b]
  | 6 => [Gen.a, Gen.a, Gen.bInv, Gen.bInv, Gen.aInv]
  | 7 => [Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv]
  | 8 => [Gen.aInv, Gen.b, Gen.b, Gen.a]
  | 9 => [Gen.aInv, Gen.b, Gen.aInv, Gen.bInv]
  | 10 => [Gen.a, Gen.bInv, Gen.a, Gen.b, Gen.aInv]
  | 11 => [Gen.b, Gen.a, Gen.bInv, Gen.a]
  | 12 => [Gen.b, Gen.b, Gen.b, Gen.aInv, Gen.bInv, Gen.bInv]
  | 13 => [Gen.a, Gen.bInv, Gen.aInv, Gen.b, Gen.aInv]
  | 14 => [Gen.b, Gen.b, Gen.aInv, Gen.aInv, Gen.b, Gen.b]
  | 15 => [Gen.a, Gen.b, Gen.aInv, Gen.aInv, Gen.bInv, Gen.bInv]
  | 16 => [Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.a, Gen.b]
  | 17 => [Gen.a, Gen.b, Gen.a, Gen.bInv, Gen.a, Gen.bInv]
  | 18 => [Gen.b, Gen.a, Gen.b, Gen.a]
  | 19 => [Gen.b, Gen.a, Gen.bInv, Gen.bInv, Gen.aInv, Gen.bInv]
  | 20 => [Gen.b, Gen.b, Gen.a, Gen.a, Gen.bInv, Gen.aInv]
  | _ => []

set_option maxRecDepth 400000 in
/-- The orbit words send `21` to every point. -/
theorem lastOrbitWord_maps_all :
    ∀ x : Fin 22, (Word.eval (lastOrbitWord x)) (21 : Fin 22) = x := by
  decide

set_option maxRecDepth 400000 in
/-- The stabilizer words fix `21`. -/
theorem lastStabWord_fixes_all :
    ∀ x : Fin 22, x ≠ 21 → (Word.eval (lastStabWord x)) (21 : Fin 22) = 21 := by
  decide

set_option maxRecDepth 400000 in
/-- The stabilizer words send `0` to the requested point. -/
theorem lastStabWord_maps_all :
    ∀ x : Fin 22, x ≠ 21 → (Word.eval (lastStabWord x)) (0 : Fin 22) = x := by
  decide

/-- A word certificate for the embedded generator 1. -/
def embWord1 : Word :=
  [Gen.a, Gen.bInv, Gen.aInv, Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.aInv, Gen.bInv]

/-- A word certificate for the embedded generator 2. -/
def embWord2 : Word :=
  [Gen.a, Gen.bInv, Gen.bInv, Gen.aInv, Gen.b, Gen.b, Gen.b, Gen.b, Gen.a, Gen.b, Gen.b, Gen.aInv]

/-- A word certificate for the embedded generator 3. -/
def embWord3 : Word :=
  [Gen.a, Gen.b, Gen.aInv, Gen.bInv, Gen.aInv, Gen.bInv, Gen.bInv, Gen.a, Gen.b, Gen.b, Gen.a, Gen.a, Gen.b, Gen.aInv]

end LastPoint
end M22Certificates
end Sporadic
