/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M12.Simplicity

/-!
# Target statements

The statements are the milestone targets for the experiment.

* `card_M12` is proved by the stabilizer-chain and Witt design certificates.
* `simple_M12` is proved by the point-stabilizer route: the stabilizer of the
  twelfth point is the embedded `M11` (simple, by the `M11` project), and the
  classical normal-subgroup argument excludes a regular normal subgroup of
  order `12` via Cauchy's theorem.
-/

namespace Sporadic

theorem card_M12 : Nat.card M12 = 95040 := by
  exact M12Cardinality.card_M12

theorem simple_M12 : IsSimpleGroup M12 := by
  exact M12Simplicity.simple_M12

end Sporadic
