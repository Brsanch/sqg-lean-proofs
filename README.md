# SQG Identity — Lean 4 Formalization (Work in Progress)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)

Concept DOI (always-latest): [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) · v0.3.0: [10.5281/zenodo.19584185](https://doi.org/10.5281/zenodo.19584185) · v0.2.0: [10.5281/zenodo.19583417](https://doi.org/10.5281/zenodo.19583417) · v0.1.0: [10.5281/zenodo.19583257](https://doi.org/10.5281/zenodo.19583257)

Lean 4 + mathlib formalization of Fourier-space identities for the
Surface Quasi-Geostrophic (SQG) equation, working towards a machine-checked
regularity proof. Currently covers the shear-vorticity identity
(Theorem 1 of paper D14) and supporting Riesz/Sobolev infrastructure.

## What's proven

**Theorems 1 and 2 of D14** are fully machine-verified (zero `sorry`):

- Shear-vorticity identity `Ŝ_nt − ω̂/2 = |k|·sin²(α−β)·θ̂` in polar
  and Cartesian forms, with half-angle, aligned, and perpendicular corollaries
- Selection-rule bound `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` with equality-case
  characterization
- ℓ² integrated form via `SqgFourierData` bundle, Parseval bridge to
  `L²(𝕋ᵈ)`, and Ḣ¹ seminorm restatement

**Riesz-transform and Sobolev infrastructure** on `𝕋ᵈ` (also zero `sorry`):

- Riesz symbol `m_j(n) = −i·n_j/‖n‖`, pointwise bound, Pythagorean
  identity, complex identity `Σ_j R_j² = −Id`
- SQG velocity isometry `‖u₁‖² + ‖u₂‖² = ‖θ‖²`
- Leray–Helmholtz projector: definition, trace, self-adjoint, idempotent,
  kills longitudinal, preserves transverse
- Fractional-derivative symbol, Ḣˢ seminorm, Laplacian and inverse-Laplacian
  symbols, Biot-Savart factorisation
- L² contractivity of bounded multipliers, Riesz L² contractivity
- Ḣˢ-level bounds: strain/velocity-gradient ≤ Ḣˢ⁺¹(θ), velocity ≤ Ḣˢ(θ)
- Sobolev interpolation (mode-level), Bernstein frequency estimates
- Hessian symbol, tangential-Hessian vanishing, third-order symbols
- Strain-rotation decomposition, vorticity symbol = −|k|
- SQG strain norm bound, divergence-free, explicit strain formulas
- **Tight mode-level identities** (no inequality):
  - `|S₀₀|² + |S₀₁|² = ‖n‖²/4` (strain eigenvalue tight)
  - `Σ ‖S_ij‖² = ‖n‖²/2` (strain Frobenius tight)
  - `Σ ‖∂̂_i u_j‖² = ‖n‖²` (gradient Frobenius tight)
  - `‖ω̂‖ = ‖n‖` (vorticity norm)
  - `‖∂u‖²_F = ‖S‖²_F + ‖ω‖²/2` (strain-vorticity partition)
- Mode-level Ḣˢ tight identities for strain, gradient, vorticity
- Riesz Ḣˢ contractivity, derivative Ḣˢ mode bound
- Vorticity L² = θ Ḣ¹ (Parseval integrated form)
- **α-Fractional heat semigroup** (unifies heat + Poisson + fractional SQG):
  - `fracHeatSymbol α t n = exp(-t·‖n‖^{2α})` for `0 < α`
  - Specializations: α=1 → heat, α=1/2 → Poisson
  - `fracHeatSymbol_rpow_eq`: time-rescaling identity
  - General smoothing: `‖n‖^k·fracHeat ≤ (k/(2α))^{k/(2α)}·exp(-k/(2α))/t^{k/(2α)}`
  - Mode + integrated L² and Ḣᵏ bounds
  - Mode + integrated L² / Ḣˢ contractivity
  - **α-fracHeat-smoothed SQG suite** (mode + integrated):
    - Vorticity: `‖fracHeat·ω̂·c‖² ≤ (1/α)^{1/α}·exp(-1/α)/t^{1/α}·‖c‖²`
    - Gradient: same bound per component
    - Strain: same bound per component
    - Velocity Ḣˢ: `‖fracHeat·u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}` (no gain)
- **Heat semigroup & parabolic smoothing**:
  - `heatSymbol`, positivity, boundedness, additivity, Ḣˢ contractivity
  - `x · exp(-x) ≤ exp(-1)` (tangent-line inequality)
  - `‖n‖² · exp(-t‖n‖²) ≤ exp(-1)/t` (k=1 gradient smoothing)
  - `‖n‖⁴ · exp(-t‖n‖²) ≤ 4·exp(-2)/t²` (k=2 Hessian smoothing)
  - General `k : ℕ`: `‖n‖^{2k} · exp(-t‖n‖²) ≤ k^k·exp(-k)/t^k`
    (max of `y^k·exp(-y)` at `y = k`)
  - General real `k > 0`: same bound using `Real.rpow`
  - Mode-level and integrated Ḣᵏ parabolic smoothing for all real k > 0
  - L² and Ḣˢ contractivity of heat (integrated form)
  - Heat-smoothed SQG quantities (mode-level and integrated):
    - Vorticity: `‖heat·ω̂·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Gradient: `‖heat·∂̂u·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Strain (generic): `‖heat·Ŝ·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Strain (tight): `‖heat·Ŝ_ij·c‖² ≤ exp(-1)/(4t) · ‖c‖²` (4× sharper)
    - Ḣˢ-level bounds for all: vorticity/gradient/strain Ḣˢ ≤ θ Ḣˢ⁺¹
    - Tight Ḣˢ for S₀₀/S₀₁: `‖e^{tΔ}S_ij‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}/4`
    - Velocity: `‖e^{tΔ}u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}` (both heat and Riesz contract)

## What's proven conditionally (Theorem 3 skeleton, §10)

The regularity result (Theorem 3) is **not unconditionally formalized**,
but `RieszTorus.lean` §10 now carries a *conditional* Theorem 3:
a machine-checked derivation that takes three analytic hypotheses
as input and concludes

    ∀ s ≥ 0, ∃ M, ∀ t ≥ 0, ‖θ(t)‖²_{Ḣˢ} ≤ M

— uniform bounds in every Sobolev space. Two of the three hypotheses
now carry real mathematical content (uniform Ḣ¹ bound; Ḣ¹→Ḣˢ
bootstrap); the third remains a structural placeholder.

See `sqg_regularity_conditional` in `RieszTorus.lean`. The hypothesis
structures (`MaterialMaxPrinciple`, `BKMCriterion`,
`FracSobolevCalculus`) explicitly pin down *which* analytic facts the
argument is borrowing from outside the algebraic layer.

A structured form `SqgSolution.regularity_conditional` (§10.1) wraps
the theorem around an `SqgSolution` record, which bundles the
time-evolution `θ`, a smooth-initial-data predicate (`θ 0` has finite
Ḣˢ seminorm for some `s > 2`), and a placeholder `solvesSqgEvolution`
field for the SQG PDE itself. The `smoothInitialData` field uses
`Summable` on the Ḣˢ-weighted Fourier series — the honest well-posedness
condition, not a vacuous `≤ M` bound.

**§10.2 Trivial-case discharges:**
`MaterialMaxPrinciple.of_identically_zero` and
`BKMCriterion.of_identically_zero` prove both refined hypotheses
unconditionally for the stationary zero solution `θ ≡ 0`. These are
supported by a new utility lemma `hsSeminormSq_of_zero` (the Ḣˢ
seminorm of `0` vanishes). Not mathematically deep, but they
demonstrate the hypotheses can be discharged to real proofs in at
least one case, not merely axiomatized.

**§10.3 Well-posedness + smooth-data form:**
`SqgWellPosedness` (hypothesis structure) asserts existence of a
matching `SqgSolution` for any smooth initial datum — the standard
SQG local well-posedness statement in Ḣˢ for `s > 2`. The
user-facing theorem `sqg_regularity_for_smooth_data` combines
well-posedness, the three analytic hypotheses (applied uniformly to
every solution), and smooth initial data `θ₀` to conclude: there
exists a solution with `θ 0 = θ₀` having uniform Sobolev bounds at
every order. This is the "input: smooth data → output: smooth
evolution" form of Theorem 3.

**`FracSobolevCalculus.ofMathlib`:** of the three analytic
hypotheses, `FracSobolevCalculus` has been refined to real
mode-level content (`hsMonotone`) and can be discharged
unconditionally — its proof is a direct re-export of existing
lemmas in this file. So in practice, only `MaterialMaxPrinciple`
and `BKMCriterion` need axiomatic treatment.

## What's not proven (yet)

Closing Theorem 3 unconditionally would require infrastructure that
doesn't exist in mathlib yet:

- **Material-derivative transport / maximum principle** — needed to
  prove `MaterialMaxPrinciple.hOnePropagation`. Mathlib has basic flow
  API but no ODE existence-uniqueness or DiPerna–Lions-level theory.
- **BKM blow-up criterion + Sobolev bootstrap** — needed to prove
  `BKMCriterion.hsPropagation`. Not in mathlib.
- **Fractional Sobolev operator calculus** —
  `FracSobolevCalculus.fracLaplacianIsSelfAdjointFourierMultiplier`.
  Our torus-level symbols are in-file, but the general operator theory
  is missing upstream.

This repo is the Fourier-algebraic foundation plus a conditional
Theorem 3 skeleton — the analytic heavy lifting (discharging the three
hypotheses) remains to be done.

## The identity

For a Fourier mode with wavevector `k = |k|(cos α, sin α)` and front normal
`n̂ = (cos β, sin β)`:

    Ŝ_nt - ω̂/2 = |k| · sin²(α - β) · θ̂

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build is slow (~5–10 min on cold cache). Incremental builds are fast.

## Files

- `SqgIdentity/Basic.lean` — Theorems 1 and 2: polar and Cartesian forms,
  ℓ² lift, `SqgFourierData` bundle, Parseval bridge to `L²(𝕋ᵈ)`
- `SqgIdentity/RieszTorus.lean` — Riesz-transform symbols on `𝕋ᵈ`,
  Leray–Helmholtz projector, Sobolev scale, Laplacian/inverse-Laplacian,
  Biot-Savart, D14 Theorem 1 at Fourier-symbol level
- `SqgIdentity.lean` — root module (imports both)
- `lakefile.toml` — project config (mathlib dependency pinned to v4.29.0)
- `lean-toolchain` — Lean 4.29.0

## Credit

Mathematical theorem and Lean formalization: Bryan Sanchez.
