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
| **Parseval bridge**: `sqg_L2_torus_bound` — `∫ ‖w‖² ≤ ∑ₙ r(n)²·‖θ̂(n)‖²` on `L²(𝕋ᵈ)` via `AddCircleMulti.hasSum_sq_mFourierCoeff` | ✅ Proven |
| `latticeNorm` + `latticeNorm_sq` + `latticeNorm_eq_zero_iff` + `latticeNorm_pos` + `sq_le_latticeNorm_sq` | ✅ Proven |
| `rieszSymbol j n := -i·nⱼ/‖n‖` (Fourier multiplier symbol on `𝕋ᵈ`) | ✅ Defined |
| `norm_rieszSymbol` — `‖m_j(n)‖ = \|n_j\|/‖n‖` for `n ≠ 0` | ✅ Proven |
| **Riesz pointwise bound**: `rieszSymbol_norm_le_one` — `‖m_j(n)‖ ≤ 1` | ✅ Proven |
| **Riesz Pythagorean identity**: `rieszSymbol_sum_sq` — `Σⱼ ‖m_j(n)‖² = 1` for `n ≠ 0` | ✅ Proven |
| **Complex Riesz identity**: `rieszSymbol_sum_sq_complex` — `Σⱼ (m_j(n))² = -1` (operator form `Σⱼ R_j² = -Id`) | ✅ Proven |
| **SQG velocity symbol isometry**: `sqg_velocity_symbol_isometry` — `‖m₂·z‖² + ‖-m₁·z‖² = ‖z‖²` on `𝕋²` | ✅ Proven |
| **L² contractive multipliers**: `L2_contractive_of_bounded_symbol` — `‖m‖∞ ≤ 1` + Parseval ⟹ `‖g‖_{L²} ≤ ‖f‖_{L²}` | ✅ Proven |
| `L2_isometry_of_unit_symbol` — unit-modulus pointwise ⟹ `‖g‖_{L²} = ‖f‖_{L²}` | ✅ Proven |
| **Riesz L² contractivity**: `riesz_L2_contractive` — `‖R_j f‖_{L²(𝕋ᵈ)} ≤ ‖f‖_{L²(𝕋ᵈ)}` | ✅ Proven |
| **SQG velocity L² isometry**: `sqg_velocity_L2_isometry` — `‖u₁‖²_{L²} + ‖u₂‖²_{L²} = ‖θ‖²_{L²}` for zero-mean θ on 𝕋² | ✅ Proven |
| `fracDerivSymbol s n := ‖n‖^s` off zero — Fourier symbol of `(-Δ)^{s/2}` | ✅ Defined |
| Parseval multiplier: `hasSum_sq_multiplier` + `L2_norm_sq_eq_multiplier_tsum` — `∫‖g‖² = Σₙ ‖m(n)‖²·‖f̂(n)‖²` | ✅ Proven |
| Multiplier composition: `mFourierCoeff_multiplier_comp` — `ĝ = m₁·f̂`, `ĥ = m₂·ĝ` ⟹ `ĥ = (m₂·m₁)·f̂` | ✅ Proven |
| `hsSeminormSq s f := Σₙ ‖n‖^{2s}·‖f̂(n)‖²` — homogeneous Ḣˢ seminorm squared | ✅ Defined |
| `hsSeminormSq_eq_L2_of_multiplier` — `(-Δ)^{s/2}` identification: `‖g‖²_{L²} = ‖f‖²_{Ḣˢ}` when `ĝ = σ_s·f̂` | ✅ Proven |
| **SQG selection rule, Ḣ¹ form**: `sqg_selection_rule_Hs1` — `‖ŵ(n)‖ ≤ ‖n‖·‖θ̂(n)‖` + summability ⟹ `‖w‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}` | ✅ Proven |

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

- `SqgIdentity/Basic.lean` — main file: Theorems 1 and 2, ℓ² lift, `SqgFourierData` bundle, Parseval bridge to `L²(𝕋ᵈ)`
- `SqgIdentity/RieszTorus.lean` — Riesz-transform symbols on `𝕋ᵈ`: pointwise bound, Pythagorean identities (real & complex), SQG velocity isometry, fractional-derivative symbol, Ḣˢ seminorm, Ḣ¹ form of the selection rule
- `SqgIdentity.lean` — root module (imports both)
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
and equality-case refinements, an ℓ² integrated form packaged over an
arbitrary `SqgFourierData ι`, and a Parseval bridge to `L²(𝕋ᵈ)`.
Zero `sorry`.

**The L²(𝕋ᵈ) form is concrete, not abstract.** `sqg_L2_torus_bound`
gives `∫ ‖w‖² ≤ ∑ₙ r(n)²·‖θ̂(n)‖²` for any pair of L² functions on the
torus whose Fourier coefficients satisfy the pointwise selection-rule
bound. Specialising `r(n) = ‖n‖` makes the RHS `‖∇θ‖²_{L²(𝕋ᵈ)}`
(another Parseval application), so this is exactly
`‖S_nt − ω/2‖_{L²} ≤ ‖∇θ‖_{L²}`, the integrated form of Theorem 2
consumed by §9. `sqg_selection_rule_Hs1` restates this directly in
terms of the Ḣ¹ seminorm via the fractional-derivative symbol.

**Theorem 3 (regularity) — status on mathlib infrastructure** *(audited
2026-04-14 by reading `.lake/packages/mathlib/` directly, not from
memory)*:

1. ~~**2D Fourier series on `𝕋ᵈ` with Parseval.**~~ **Available.**
   `Mathlib.Analysis.Fourier.AddCircleMulti` provides
   `UnitAddTorus d := d → UnitAddCircle`, the Hilbert basis
   `mFourierBasis`, and both Parseval identities
   (`hasSum_prod_mFourierCoeff`, `hasSum_sq_mFourierCoeff`). Used in
   `sqg_L2_torus_bound`.
2. **Fractional Laplacian `(-Δ)^s` and Riesz transforms.** Not in
   mathlib as general Calderón–Zygmund singular integrals, but we have
   built an in-file **torus Riesz library** in
   `SqgIdentity/RieszTorus.lean` that bypasses singular-integral theory
   via Fourier multipliers:
   * Symbol level: `m_j(n) = -i·nⱼ/‖n‖`, pointwise `‖m_j(n)‖ ≤ 1`,
     norm Pythagorean `Σⱼ ‖m_j(n)‖² = 1`, complex-valued counterpart
     `Σⱼ (m_j(n))² = -1` (⇔ `Σⱼ R_j² = -Id`), SQG velocity symbol
     isometry `‖m₂·z‖² + ‖-m₁·z‖² = ‖z‖²` on `𝕋²`.
   * Operator level: generic L²-contractivity
     `‖m‖∞ ≤ 1 ⟹ ‖g‖_{L²} ≤ ‖f‖_{L²}`, the Riesz corollary
     `‖R_j f‖_{L²(𝕋ᵈ)} ≤ ‖f‖_{L²(𝕋ᵈ)}`, and the SQG energy-conservation
     identity `‖u₁‖²_{L²} + ‖u₂‖²_{L²} = ‖θ‖²_{L²}` for zero-mean θ on 𝕋².
   * Sobolev scale: `fracDerivSymbol s n = ‖n‖ˢ` (off zero), homogeneous
     Ḣˢ seminorm squared `hsSeminormSq s f`, Fourier-multiplier
     identification `‖(-Δ)^{s/2} f‖²_{L²} = ‖f‖²_{Ḣˢ}`, and the Ḣ¹
     form of the SQG selection rule.

   Driven entirely by `AddCircleMulti.hasSum_sq_mFourierCoeff` — no
   singular-integral machinery invoked. Still missing upstream:
   `(-Δ)^s` for non-integer `s` on `ℝⁿ` as an operator (the torus-level
   *symbol* is covered here).
3. **Material-derivative transport and maximum principle.**
   `Mathlib.Dynamics.Flow` (292 lines) is basic monoid-action API only
   — no Cauchy–Lipschitz / ODE existence-uniqueness, no DiPerna–Lions
   for non-Lipschitz fields.
4. **BKM / Constantin–Majda–Tabak blow-up criterion.** Still missing.
   No BKM hits in mathlib. `SobolevInequality.lean` covers
   Gagliardo–Nirenberg at integer order but no fractional `Ḣ^s` on ℝⁿ.

Closing Theorem 3 would still require landing (2, ℝⁿ-level)–(4)
upstream. The Parseval step (previously listed as blocker #1) turned
out to already be in mathlib, and is now used in-file; the torus Riesz
symbol and Ḣˢ scaffolding for (2) are also in-file.

## Credit

Mathematical theorem and Lean formalization: Bryan Sanchez.
