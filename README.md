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

## What's not proven (yet)

The regularity result (Theorem 3) is **not formalized**. Closing it in
Lean would require infrastructure that doesn't exist in mathlib yet:

- Material-derivative transport / maximum principle (mathlib has basic
  flow API but no ODE existence-uniqueness or DiPerna–Lions)
- BKM blow-up criterion (not in mathlib)
- Fractional Sobolev spaces on ℝⁿ as operators (our torus-level symbols
  are in-file, but the general theory is missing upstream)

This repo is the Fourier-algebraic foundation — the analytic heavy
lifting remains to be done.

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
