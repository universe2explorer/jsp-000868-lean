# JSP-000868 — Lean 4 formalization

**Problem** ([JSP-000868](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000868)):
"If a polynomial's unit-modulus sublevel set is connected, must it lie in a disk of
radius two?"

**Answer (published):** Yes — for monic (nonconstant) complex polynomials
(Erdős–Herzog–Piranian 1958; Pólya 1959; Pommerenke's Jensen-argument proof).

**Formal theorem** (`JSP000868.lean`): for monic `f : ℂ[X]` of positive degree, if
`{z | ‖f.eval z‖ ≤ 1}` is connected, then it is contained in a closed disk of radius 2
(in fact centered at the root centroid). See
`../hidden_files/statement-correspondence.md` for the clause-by-clause correspondence
with the original problem, including why the monic and nonconstant normalizations are
required (both are forced: without them the loose catalog sentence is false).

## Layout
- `JSP000868/JensenWeight.lean` — the one-dimensional weighted Jensen estimate:
  real-rooted `∏ |y − xᵢ| ≤ 1` on `[A,B]` implies `B − mean(xᵢ) ≤ 2`.
- `JSP000868/Main.lean` — projection of the connected lemniscate onto a unit
  direction, reduction to the 1D estimate, radius-2 bound around the root centroid.
- `JSP000868.lean` — root module re-exporting the target theorem `JSP000868.jsp000868`.

## Reproduction
Toolchain and dependency pins: `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`.
Build: `lake exe cache get && lake build`. Audit: `lake env lean Audit.lean`
(`#print axioms` for each target theorem).

## Status
Work in progress. No `sorry`/`admit` is permitted in the final version.
