/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import FiniteSimpleGroups.Sporadic.M11.Simplicity

/-!
# Target statements

The statements are the milestone targets for the experiment.
-/

namespace Sporadic

theorem card_M11 : Nat.card M11 = 7920 := by
  exact M11Cardinality.card_M11

theorem simple_M11 : IsSimpleGroup M11 := by
  exact M11Simplicity.simple_M11

end Sporadic
