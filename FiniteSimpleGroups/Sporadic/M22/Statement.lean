/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M22.Simplicity

/-!
# Target statements

The statements are the milestone targets for the experiment.

* `card_M22` is proved by the stabilizer-chain and `S(3,6,22)` block
  certificates.
* `simple_M22` is proved by the point-stabilizer route: the stabilizer of
  the last point is the embedded `PSL(3,4)` (simple by the certificate-driven
  Iwasawa argument in `SporadicM22/L34/`), and the classical normal-subgroup
  argument excludes a regular normal subgroup of order `22` via Cauchy's
  theorem (orders `2` and `11` cannot coincide).
-/

namespace Sporadic

theorem card_M22 : Nat.card M22 = 443520 := by
  exact M22Cardinality.card_M22

theorem simple_M22 : IsSimpleGroup M22 := by
  exact M22Simplicity.simple_M22

end Sporadic
