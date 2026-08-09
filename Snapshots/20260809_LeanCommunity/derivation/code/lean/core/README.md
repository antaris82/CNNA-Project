# CNNA core package

This package exports the `CNNA` library and is intentionally independent of
mathlib. Its `lake-manifest.json` contains zero dependencies. Core source files
may import only Lean core modules and other `CNNA` modules; imports from
`Mathlib`, `CNNAProofs`, or any proof package are forbidden.

Toolchain: `leanprover/lean4:v4.31.0`.
