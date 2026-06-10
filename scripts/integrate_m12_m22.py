#!/usr/bin/env python3
"""Integrate the M12exp and M22exp projects into FiniteSimpleGroups.

* copies SporadicM12/SporadicM22 sources into
  FiniteSimpleGroups/Sporadic/{M12,M22}/ with import rewrites;
* writes the umbrella files Sporadic/M12.lean and Sporadic/M22.lean;
* updates the root FiniteSimpleGroups.lean;
* generates the standalone Lean4Web files M12Lean4Web.lean (which includes
  the full M11 proof it depends on) and M22Lean4Web.lean (self-contained);
* copies the certificate-generation scripts for provenance.

Run from the forGithub repo root.
"""

import os
import re
import shutil

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASE = os.path.dirname(ROOT)
M12EXP = os.path.join(BASE, "M12exp")
M22EXP = os.path.join(BASE, "M22exp")

EXP_HEADER = """/-
Copyright (c) 2026 Kenta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta, Claude
-/"""

HOUSE_HEADER = """/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: Developed with assistance from Claude Code (Fable 5, 1M context,
high reasoning).
-/"""

def rewrite_imports(text, mapping):
    for old, new in mapping.items():
        text = text.replace(f"import {old}", f"import {new}")
    return text.replace(EXP_HEADER, HOUSE_HEADER)

def copy_tree(src_root, src_lib, dst_rel, mapping):
    copied = []
    for dirpath, _, files in os.walk(os.path.join(src_root, src_lib)):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            src = os.path.join(dirpath, f)
            rel = os.path.relpath(src, os.path.join(src_root, src_lib))
            dst = os.path.join(ROOT, dst_rel, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            text = open(src).read()
            text = rewrite_imports(text, mapping)
            open(dst, "w").write(text)
            copied.append(rel)
    # umbrella file
    src = os.path.join(src_root, src_lib + ".lean")
    text = rewrite_imports(open(src).read(), mapping)
    open(os.path.join(ROOT, dst_rel + ".lean"), "w").write(text)
    return copied

MAP12 = {
    "SporadicM12.": "FiniteSimpleGroups.Sporadic.M12.",
    "SporadicM11.": "FiniteSimpleGroups.Sporadic.M11.",
}
MAP22 = {
    "SporadicM22.": "FiniteSimpleGroups.Sporadic.M22.",
}

c12 = copy_tree(M12EXP, "SporadicM12", "FiniteSimpleGroups/Sporadic/M12", MAP12)
print(f"copied {len(c12)} M12 files")
c22 = copy_tree(M22EXP, "SporadicM22", "FiniteSimpleGroups/Sporadic/M22", MAP22)
print(f"copied {len(c22)} M22 files")

# ------------------------------------------------------------- root module
open(os.path.join(ROOT, "FiniteSimpleGroups.lean"), "w").write("""/-
Copyright (c) 2026 Kenta.
Authors: Kenta
AI usage: M11 with OpenAI Codex (GPT-5.5, xhigh reasoning)
and ChatGPT 5.5 Pro; M12, M22, and PSL(3,4) with
Claude Code (Fable 5, 1M context, high reasoning).
-/
import FiniteSimpleGroups.Sporadic.M11
import FiniteSimpleGroups.Sporadic.M12
import FiniteSimpleGroups.Sporadic.M22

/-!
# Finite simple groups

This library collects Lean/mathlib formalizations of concrete finite simple
groups.  The completed entries are Mathieu's sporadic groups `M11`, `M12`,
and `M22` (each with its order and simplicity), together with the
certificate-driven copy of `PSL(3,4)` used as the point stabilizer of `M22`.
-/
""")
print("wrote FiniteSimpleGroups.lean")

# --------------------------------------------------------------- Lean4Web
def strip_for_concat(path):
    """Remove the leading copyright block and all import lines."""
    lines = open(path).read().split("\n")
    out = []
    i = 0
    if lines and lines[0].startswith("/-") and not lines[0].startswith("/-!"):
        while i < len(lines) and not lines[i].rstrip().endswith("-/"):
            i += 1
        i += 1
    for j in range(i, len(lines)):
        if lines[j].startswith("import "):
            continue
        out.append(lines[j])
    body = "\n".join(out).strip("\n")
    return body

def mathlib_imports(paths):
    imps = []
    for p in paths:
        for line in open(p).read().split("\n"):
            if line.startswith("import Mathlib") and line not in imps:
                imps.append(line)
    return imps

def file_marker(rel):
    bar = "-" * 70
    return f"/-\n{bar}\nSource: {rel}\n{bar}\n-/"

# ---- M12Lean4Web: M11 single-file body + M12 modules
m11web = open(os.path.join(ROOT, "FiniteSimpleGroupsLean4Web/M11Lean4Web.lean")).read()
m11_lines = m11web.split("\n")
last_import = max(i for i, l in enumerate(m11_lines) if l.startswith("import "))
m11_imports = [l for l in m11_lines if l.startswith("import ")]
m11_body = "\n".join(m11_lines[last_import + 1:]).strip("\n")

M12_ORDER = [
    "Basic.lean", "Permutations.lean", "GeneratedSubgroup.lean",
    "Certificates/Words.lean", "Certificates/StabilizerChain.lean",
    "Certificates/WittDesign.lean", "Cardinality.lean",
    "M11Embedding.lean", "PointStabilizer.lean", "Simplicity.lean",
    "Statement.lean",
]
m12_paths = [os.path.join(ROOT, "FiniteSimpleGroups/Sporadic/M12", f)
             for f in M12_ORDER]
extra12 = [l for l in mathlib_imports(m12_paths) if l not in m11_imports]

m12_parts = []
for f, p in zip(M12_ORDER, m12_paths):
    m12_parts.append(file_marker(f"FiniteSimpleGroups/Sporadic/M12/{f}"))
    m12_parts.append(strip_for_concat(p))

m12web = f"""/-
Lean4Web complete single-file version of the FiniteSimpleGroups M12 proof.

Paste this whole file into a Lean4Web environment with mathlib.
It contains the full M11 proof (which M12 depends on), the M12
construction, |M12| = 95040, and IsSimpleGroup M12.

AI usage: the embedded M11 proof was developed with assistance from
OpenAI Codex (GPT-5.5, xhigh reasoning) and ChatGPT 5.5 Pro;
the M12 layer with Claude Code (Fable 5, 1M context, high reasoning).

The final `#print axioms` commands should not show `sorryAx`.
Standard mathlib/classical axioms such as `propext`, `Classical.choice`,
and `Quot.sound` may appear.
-/

{chr(10).join(m11_imports + extra12)}

{m11_body}

{chr(10).join(m12_parts)}

#print axioms Sporadic.card_M12
#print axioms Sporadic.simple_M12
"""
open(os.path.join(ROOT, "FiniteSimpleGroupsLean4Web/M12Lean4Web.lean"), "w").write(m12web)
print("wrote M12Lean4Web.lean", len(m12web.split(chr(10))), "lines")

# ---- M22Lean4Web: self-contained
M22_ORDER = [
    "Basic.lean", "Permutations.lean", "GeneratedSubgroup.lean",
    "Certificates/Words.lean", "Certificates/SteinerSystem.lean",
    "Certificates/StabilizerChain.lean", "Certificates/ChainOrbits.lean",
    "Certificates/FinalStabilizer.lean", "Certificates/LastPoint.lean",
    "Cardinality.lean",
    "L34/Basic.lean", "L34/Words.lean", "L34/Transitivity.lean",
    "L34/Elations.lean", "L34/Cardinality.lean", "L34/Simplicity.lean",
    "PointStabilizer21.lean", "Simplicity.lean", "Statement.lean",
]
m22_paths = [os.path.join(ROOT, "FiniteSimpleGroups/Sporadic/M22", f)
             for f in M22_ORDER]
imps22 = mathlib_imports(m22_paths)

m22_parts = []
for f, p in zip(M22_ORDER, m22_paths):
    m22_parts.append(file_marker(f"FiniteSimpleGroups/Sporadic/M22/{f}"))
    m22_parts.append(strip_for_concat(p))

m22web = f"""/-
Lean4Web complete single-file version of the FiniteSimpleGroups M22 proof.

Paste this whole file into a Lean4Web environment with mathlib.
It contains the M22 construction, |M22| = 443520, the certificate-driven
simplicity proof of its point stabilizer PSL(3,4), and IsSimpleGroup M22.

AI usage: Developed with assistance from Claude Code (Fable 5, 1M context, high reasoning).

The final `#print axioms` commands should not show `sorryAx`.
Standard mathlib/classical axioms such as `propext`, `Classical.choice`,
and `Quot.sound` may appear.
-/

{chr(10).join(imps22)}

{chr(10).join(m22_parts)}

#print axioms Sporadic.card_M22
#print axioms Sporadic.simple_M22
"""
open(os.path.join(ROOT, "FiniteSimpleGroupsLean4Web/M22Lean4Web.lean"), "w").write(m22web)
print("wrote M22Lean4Web.lean", len(m22web.split(chr(10))), "lines")

# --------------------------------------------------------------- scripts
for name, exp in [("m12", M12EXP), ("m22", M22EXP)]:
    dst = os.path.join(ROOT, "scripts", name)
    os.makedirs(dst, exist_ok=True)
    src = os.path.join(exp, "scripts")
    for f in sorted(os.listdir(src)):
        if f.endswith(".py"):
            shutil.copy(os.path.join(src, f), os.path.join(dst, f))
            print("script:", name, f)
print("done")
