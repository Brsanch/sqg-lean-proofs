# SQG Shear-Vorticity Identity — Lean 4 Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)

Concept DOI (always-latest): [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) · v0.3.0: [10.5281/zenodo.19584185](https://doi.org/10.5281/zenodo.19584185) · v0.2.0: [10.5281/zenodo.19583417](https://doi.org/10.5281/zenodo.19583417) · v0.1.0: [10.5281/zenodo.19583257](https://doi.org/10.5281/zenodo.19583257)

First formalization target: **Theorem 1** from paper D14 (shear-vorticity
identity in Fourier space for the Surface Quasi-Geostrophic equation).

## Status (2026-04-14) — ALL PROVEN ✅

| Item | Status |
|---|---|
| Lean 4.29.0 + mathlib v4.29.0 project set up | ✅ Builds |
| `one_sub_cos_two_mul`: `1 - cos(2x) = 2 sin²(x)` | ✅ Proven |
| `half_times_one_sub_cos`: `(\|k\|/2)·(1 - cos(2φ)) = \|k\|·sin²(φ)` | ✅ Proven |
| **Theorem 1**: `sqg_shear_vorticity_identity` | ✅ **Proven** (zero `sorry`) |
| Corollary — half-angle form: `sqg_shear_vorticity_identity_halfangle` | ✅ Proven |
| Corollary — aligned case (β = α → 0): `sqg_shear_aligned` | ✅ Proven |
| Corollary — perpendicular case (β = α − π/2 → \|k\|·θ̂): `sqg_shear_perpendicular` | ✅ Proven |
| **Theorem 2 (bound form)**: `sqg_selection_rule_bound` — `‖Ŝ_nt − ω̂/2‖ ≤ \|k\|·‖θ̂‖` | ✅ Proven |
| Exact magnitude: `sqg_shear_vorticity_norm` — `‖Ŝ_nt − ω̂/2‖ = \|k\|·sin²(α−β)·‖θ̂‖` | ✅ Proven |
| **Theorem 2 (equality case)**: `sqg_selection_rule_saturated_iff` — bound saturated iff `sin²(α−β) = 1 ∨ θ̂ = 0` | ✅ Proven |
| **Theorem 1, Cartesian form**: `sqg_shear_vorticity_identity_cartesian` — `Ŝ_nt − ω̂/2 = (k₂n₁ − k₁n₂)² / \|k\| · θ̂` | ✅ Proven |
| Cartesian aligned (`k × n̂ = 0` → LHS = 0): `sqg_shear_aligned_cartesian` | ✅ Proven |
| Cartesian perpendicular (`k · n̂ = 0` → LHS = \|k\|·θ̂): `sqg_shear_perpendicular_cartesian` | ✅ Proven |
| **Theorem 2 (Cartesian bound)**: `sqg_selection_rule_bound_cartesian` — `‖Ŝ_nt − ω̂/2‖ ≤ \|k\|·‖θ̂‖` | ✅ Proven |
| **Theorem 2 (Cartesian equality)**: `sqg_selection_rule_saturated_iff_cartesian` — bound saturated iff `k·n̂ = 0 ∨ θ̂ = 0` | ✅ Proven |
| ℓ² lift lemma: `pointwise_bound_to_ell2` — pointwise `‖x‖ ≤ r·‖y‖` + summability of `r²·‖y‖²` ⟹ summability of `‖x‖²` + integrated bound | ✅ Proven |
| **Theorem 2 (ℓ² form)**: `sqg_selection_rule_ell2` — `Σᵢ ‖ŵᵢ‖² ≤ Σᵢ \|kᵢ\|²·‖θ̂ᵢ‖²` | ✅ Proven |
| `SqgFourierData` bundle + `w i` definition (explicit RHS of the identity) | ✅ Defined |
| `SqgFourierData.w_norm_le` — pointwise selection-rule bound per mode | ✅ Proven |
| `SqgFourierData.ell2_bound` — integrated ℓ² bound on an SQG Fourier-mode family | ✅ Proven |

## The theorem

For a Fourier mode with wavevector `k = |k|(cos α, sin α)` and front normal
`n̂ = (cos β, sin β)`:

    Ŝ_nt - ω̂/2 = |k| · sin²(α - β) · θ̂

Paper proof (D14 §2.2): direct computation after substituting the SQG
velocity `û = (-i k₂/|k|, i k₁/|k|)·θ̂`, plus the half-angle identity
`1 - cos(2x) = 2 sin²(x)`.

The half-angle identity is machine-verified (`one_sub_cos_two_mul`), and
the full algebraic reduction from `Ŝ_nt - ω̂/2` to `|k|·sin²(α-β)·θ̂` is
now closed — see `sqg_shear_vorticity_identity` (zero `sorry`).

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build is slow (~5–10 min on cold cache). Incremental builds are fast.

## Files

- `SqgIdentity/Basic.lean` — main file with statements and proofs
- `lakefile.toml` — project config (mathlib dependency pinned to v4.29.0)
- `lean-toolchain` — Lean 4.29.0

## Proof strategy for `sqg_shear_vorticity_identity`

1. `rw [Real.sin_sub]` — expand sin²(α−β) so RHS is polynomial in sin/cos.
2. `simp only []` — unfold all let bindings.
3. `push_cast` — push ℝ→ℂ coercions inward.
4. `field_simp [hne]` — clear the /|k| denominators in û₁, û₂.
5. `simp only [I_sq, neg_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]` — simplify I²=−1, unify notation.
6. `ring_nf` — normalize the polynomial.
7. `linear_combination -(θ·(cos²α+sin²α))·hβ` — close using sin²β+cos²β=1.

The key insight: after steps 1–6 the goal factors as
  θ·(cos²α+sin²α)·(sin²β+cos²β−1)·(−1) = 0,
which vanishes exactly when sin²β+cos²β=1.

## Scope

**In-file content (closed).** Theorems 1 and 2 of D14 are fully
machine-verified in both polar and Cartesian form, with exact-magnitude
and equality-case refinements, and an ℓ² integrated form packaged over
an arbitrary `SqgFourierData ι`. Zero `sorry`. 18 theorems, 1 definition,
1 structure.

**Theorem 3 (regularity) — blocked on missing mathlib infrastructure.**
The D14 regularity argument closes via §9 propositions built on content
that does not yet exist in mathlib; each is a multi-month formalization
project in its own right:

1. **2D Fourier series on `𝕋²` with Parseval.** Mathlib has 1D Fourier
   series on the circle (`Mathlib.Analysis.Fourier.FourierSeries`) but
   no two-dimensional version. Would need either a tensor-product
   construction over `ℤ²` or a direct port of the 1D `HilbertBasis.fourier`
   argument to `Fin 2 → Circle`.
2. **Fractional Laplacian `(-Δ)^{1/2}` and Riesz transforms.** The SQG
   velocity `u = (-∂₂, ∂₁)(-Δ)^{-1/2} θ` is a Riesz transform acting on
   `θ`. Mathlib has no Riesz-transform library and no `(-Δ)^s`
   construction for `s ∉ ℕ` on either the torus or `ℝⁿ`.
3. **Material-derivative transport and maximum principle.** The proof
   uses `Dθ/Dt = 0` (passive transport along the velocity field) plus
   `‖θ(t)‖_{L^∞} = ‖θ₀‖_{L^∞}`. Formalizing this requires Flow theory
   for a non-Lipschitz velocity field, which mathlib currently only
   supports for time-independent vector fields with pointwise Lipschitz
   hypotheses.
4. **BKM / Constantin–Majda–Tabak blow-up criterion.** The final step
   converts the ℓ² bound into global regularity via a criterion
   equivalent to `∫₀^T ‖∇θ‖_{L^∞}·‖n · (∇θ)^⊥ / ‖∇θ‖‖_{L^∞} dt < ∞`.
   Neither the criterion nor the supporting `Ḣ^s` fractional Sobolev
   embeddings are in mathlib.

Closing Theorem 3 in Lean would require landing (1)–(4) upstream first.
The in-file ℓ² bound (`SqgFourierData.ell2_bound`) is exactly the
algebraic input consumed by §9; the rest is analysis infrastructure,
not SQG-specific reasoning.

## Credit

Mathematical theorem: Bryan Sanchez (D14 paper).
Lean formalization: Bryan Sanchez + Claude Code (AI assistant).
