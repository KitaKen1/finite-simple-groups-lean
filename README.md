# FiniteSimpleGroups

This repository is a Lean/mathlib project for formalizing concrete finite
simple groups and the certificates needed to verify them inside Lean.

## Status

Among the standard finite simple group families, this repository currently
contains a Lean proof only for the sporadic Mathieu group `M11`.

| Family | Groups | Lean status |
| --- | --- | --- |
| Cyclic groups of prime order | `C_p` | basic results exist in mathlib; not mirrored here |
| Alternating groups | `A_n`, `5 <= n` | basic results exist in mathlib; not mirrored here |
| Groups of Lie type | `PSL`, Suzuki, etc. | not included yet |
| Sporadic groups | `M11` | `Sporadic.card_M11`, `Sporadic.simple_M11` |

```lean
#check Sporadic.M11
#check Sporadic.card_M11
#check Sporadic.simple_M11
```

## Build

```bash
lake build
```

Minimal public API and axiom-dependency check:

```lean
import FiniteSimpleGroups.Sporadic.M11

#check Sporadic.M11
#check Sporadic.card_M11
#check Sporadic.simple_M11

#print axioms Sporadic.card_M11
#print axioms Sporadic.simple_M11
```

## Layout

The repository layout is intentionally minimal.

```text
FiniteSimpleGroups.lean
FiniteSimpleGroups/Sporadic/M11.lean
FiniteSimpleGroups/Sporadic/M11/
FiniteSimpleGroupsLean4Web/M11Lean4Web.lean
lakefile.lean
lake-manifest.json
lean-toolchain
```

`FiniteSimpleGroups/Sporadic/M11/README.md` records the generators,
certificate policy, and external-data provenance for the `M11` proof.

## Lean4Web

`FiniteSimpleGroupsLean4Web/M11Lean4Web.lean` is a standalone single-file
version of the M11 proof. Copy it into Lean4Web to check the theorem statements
and `#print axioms` output there.

## AI Usage Disclosure
The solution and code were developed with assistance from Codex 5.5 using xhigh reasoning and ChatGPT 5.5 Pro.
