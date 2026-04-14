# SQG Shear-Vorticity Identity — Lean 4 Formalization

First formalization target: **Theorem 1** from paper D14 (shear-vorticity
identity in Fourier space for the Surface Quasi-Geostrophic equation).

## Status (2026-04-14)

| Item | Status |
|---|---|
| Lean 4.29.0 + mathlib v4.29.0 project set up | ✅ Builds |
| Sanity check: `(1 : ℂ) + 1 = 2` | ✅ Proven |
| `one_sub_cos_two_mul`: `1 - cos(2x) = 2 sin²(x)` | ✅ Proven |
| `half_times_one_sub_cos`: `(\|k\|/2)·(1 - cos(2φ)) = \|k\|·sin²(φ)` | ✅ Proven |
| `sqg_shear_vorticity_identity` (main theorem) | ⚠️ Statement typechecks, proof body is `sorry` |

## The theorem

For a Fourier mode with wavevector `k = |k|(cos α, sin α)` and front normal
`n̂ = (cos β, sin β)`:

    Ŝ_nt - ω̂/2 = |k| · sin²(α - β) · θ̂

Paper proof (D14 §2.2): direct computation after substituting the SQG
velocity `û = (-i k₂/|k|, i k₁/|k|)·θ̂`, plus the half-angle identity
`1 - cos(2x) = 2 sin²(x)`.

The half-angle identity is now machine-verified (`one_sub_cos_two_mul`).
The algebraic reduction from `Ŝ_nt - ω̂/2` to `(|k|/2)(1 - cos(2(α-β)))·θ̂`
is mechanical; closing it is the remaining work.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd lean_proofs/sqg_identity
lake build
```

First build is slow (~5–10 min on cold cache). Incremental builds are fast.

## Files

- `SqgIdentity/Basic.lean` — main file with statements and proofs
- `lakefile.toml` — project config (mathlib dependency pinned to v4.29.0)
- `lean-toolchain` — Lean 4.29.0

## Next steps

1. Close the `sorry` in `sqg_shear_vorticity_identity` by substituting the
   `let` bindings, simplifying with `ring_nf`, and applying
   `half_times_one_sub_cos`.
2. Move on to Theorem 2 (selection rule) — the next piece of the proof.
3. Eventually: Theorem 3 (regularity) — after §9's propositions are
   formalized individually.

## Credit

Mathematical theorem: Bryan Sanchez (D14 paper).
Lean formalization: Bryan Sanchez + Claude Code (AI assistant).
