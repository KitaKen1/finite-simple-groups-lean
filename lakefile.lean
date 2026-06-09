/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from OpenAI Codex and ChatGPT.
-/
import Lake
open Lake DSL

package "FiniteSimpleGroups" where
  version := v!"0.1.0"
  keywords := #["math", "group-theory", "finite-simple-groups"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`linter.style.header, false⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.30.0"

@[default_target]
lean_lib «FiniteSimpleGroups» where
  -- The top-level library imports the groups currently formalized in this repo.
