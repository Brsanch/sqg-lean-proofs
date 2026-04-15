# SQG Shear-Vorticity Identity — Lean 4 Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583257.svg)](https://doi.org/10.5281/zenodo.19583257)

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

## Next steps

1. Arbitrary-Cartesian form — restate Theorem 1 and the selection rule for `k = (k₁, k₂)` with `|k| = √(k₁² + k₂²)`, removing the polar-coordinate parameterization. Mostly bookkeeping.
2. Summability form — lift the per-mode inequality to `ℓ²`/`Hˢ` Sobolev spaces via Parseval, yielding the integrated bound needed for Theorem 3. Requires `tsum` machinery.
3. Theorem 3 (regularity) — after §9's propositions are formalized individually. Requires Sobolev embeddings, material-derivative infrastructure, and a maximum principle that are not yet in mathlib's fluid-dynamics-adjacent content.

## Credit

Mathematical theorem: Bryan Sanchez (D14 paper).
Lean formalization: Bryan Sanchez + Claude Code (AI assistant).
