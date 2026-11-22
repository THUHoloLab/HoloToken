# Bandwidth ceiling of perfectly absorbing exceptional points — Lean 4 formalization

[![Lean EP absorber](https://github.com/THUHoloLab/HoloToken/actions/workflows/lean-ep-absorber.yml/badge.svg)](https://github.com/THUHoloLab/HoloToken/actions/workflows/lean-ep-absorber.yml)

Machine-checked results from the Letter *Sharp Bandwidth Ceiling of Perfectly Absorbing
Exceptional Points* (Department of Precision Instrument, Tsinghua University).
At equal intrinsic loss L, the 90% absorption band of a perfectly absorbing exceptional point (EP)
of any order is at most 2√(2/3) L ≈ 1.633 L, 29.9% of the Bode–Fano ceiling 4πL/ln 10,
while two modes with split zeros already reach 2.720 L.

All 15 theorems below compile with Lean 4 and Mathlib, contain no `sorry`, and depend only on
Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`
(checked in CI by `scripts/check_axioms.lean`).

## What is formalized

| Lean file | Theorem | Statement |
|---|---|---|
| `EPAbsorber/N2.lean` | `EP.P2_factor`, `EP.P2_trace` | the second-order EP P(ω) = ω² + 2iLω − 2L² has poles ±L − iL and intrinsic loss L |
| | `EP.P2_normSq`, `EP.r2_normSq` | \|r(ω)\|² = ω⁴/(ω⁴ + 4L⁴) |
| | `EP.band_N2` | its 90% band is exactly [−√(2/3) L, √(2/3) L], i.e. B = 2√(2/3) L |
| | `EP.width_N2_bounds` | 1.6329 < 2√(2/3) < 1.6330 |
| | `EP.reach_lt` | X_N = 2L/(N sinh(asinh 3/N)) < 2L/asinh 3 for every N |
| `EPAbsorber/Envelope.lean` | `EP.envelope_prod`, `EP.envelope_jensen` | the envelope inequality, Eq. (5), for the canonical EP |
| | `EP.reach` | inside the 90% band, \|ω\| ≤ X_N (one-sided reach, Eq. (6)) |
| `EPAbsorber/Ratio.lean` | `EP.Ratio.ratio_bounds` | 0.2985 < 2√(2/3)/(4π/ln 10) < 0.2995 (the 29.9%) |
| `EPAbsorber/DimerBound.lean` | `EP.DimerBound.rD_normSq`, `EP.DimerBound.dimer_bound` | dimer (L = 1): no connected 90% band containing the CPA zero exceeds (4/3)√(1+√10) |
| `EPAbsorber/DimerAttained.lean` | `EP.DimerAttained.dimer_attained`, `EP.DimerAttained.dimer_value_bounds` | the bound is attained at g = (1+√10)/3; 2.720 < (4/3)√(1+√10) < 2.7203 |

## What is not yet formalized

These are proved on paper in the Supplemental Material of the Letter and appear as open
(blue or white) nodes in the blueprint:

1. reduction of every full-order EP to the canonical form, Eq. (4) (rank-one reduction, Schur form, Darlington synthesis);
2. the Bode–Fano ceiling B ≤ 4πL/ln 10;
3. the sharp supremum sup B_EP = 2√(2/3) L for every order N ≥ 2 (Schwarz chain, entropy dual, interval-arithmetic certificate).

The Lean results therefore establish the attainment at N = 2, the 29.9% ratio, the dimer value and
the edge-by-edge bound for canonical EPs; the bound for every order rests on the paper proof.

## Blueprint

The blueprint shows every statement with its dependency graph; formalized statements are linked to
their Lean names, and results still proved only on paper are marked as open.

- Web: https://thuhololab.github.io/HoloToken/ep-absorber/blueprint/
- Dependency graph: https://thuhololab.github.io/HoloToken/ep-absorber/blueprint/dep_graph_document.html
- PDF: https://thuhololab.github.io/HoloToken/ep-absorber/blueprint.pdf

Sources are in `blueprint/src`; the built site is in `docs/ep-absorber` at the repository root.
To rebuild: `pip install leanblueprint`, then in `blueprint/src` run `plastex -c plastex.cfg web.tex`
(web) or `latexmk -pdf print.tex` with `blueprint.sty` from the `leanblueprint` package on `TEXINPUTS` (PDF).

## Reproduce

Requires [elan](https://github.com/leanprover/elan). Versions are pinned by `lean-toolchain`
(Lean 4.37.0-rc1) and `lake-manifest.json` (Mathlib).

```bash
git clone https://github.com/THUHoloLab/HoloToken.git
cd HoloToken/lean/EPAbsorber
lake exe cache get
lake build
lake env lean scripts/check_axioms.lean
```

## Scope of the model

The theorems are statements about the coupled-mode model of the Letter: N resonant modes with
frequency-independent couplings, a passive rational scattering matrix with lossless background,
intrinsic loss L = tr Γᵢ, and the 90% band defined by |r(ω)|² ≤ 1/10 (σ²_min(S) ≤ 0.1 for several ports)
on the connected interval containing a CPA frequency. Dimer results are stated at L = 1; B/L is scale-free.
