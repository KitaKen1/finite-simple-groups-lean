# FiniteSimpleGroupsLean4Web

Standalone Lean4Web files for this repository.

* `M11Lean4Web.lean`: complete single-file version of the `M11` formalization.
* `M12Lean4Web.lean`: complete single-file version of the `M12`
  formalization, including the full `M11` proof it depends on.
* `M22Lean4Web.lean`: complete single-file version of the `M22`
  formalization, including the `PSL(3,4)` simplicity layer.

These files are outside the Lake library root, so they are not built by
`lake build`.  They are meant to be copied into Lean4Web.  The `M12` and
`M22` files are large; the Lean4Web server may exceed its time limits on the
heaviest certificates — the authoritative check is the Lake build of the
structured library.
