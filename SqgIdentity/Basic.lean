-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).
-- Machine-verified formalization of D14 Theorem 1.
-- Mathematical theorem by Bryan Sanchez; Lean formalization by Bryan Sanchez + Claude Code.

/-
Formalization target: Theorem 1 (Shear-Vorticity Identity) from paper D14.

Paper statement (Fourier space):
  F[S_nt - ω/2](k) = |k| · sin²(φ_k) · θ̂(k)

We formalize the pointwise per-wavevector algebraic content. After expanding
the SQG velocity û = (-i k₂/|k|, i k₁/|k|) · θ̂ and computing S_ij and ω,
the identity reduces to:

  Ŝ_nt - ω̂/2 = (|k|/2) · (1 - cos(2(α-β))) · θ̂ = |k| · sin²(α-β) · θ̂

This is (1) linear algebra in ℂ, and (2) a half-angle trig identity.
-/

import Mathlib

open Complex

namespace SqgIdentity

/-- The half-angle identity that closes Theorem 1: `1 - cos(2x) = 2 sin²(x)`.
    This is the mathematical content once the SQG algebra is unwound. -/
theorem one_sub_cos_two_mul (x : ℝ) :
    1 - Real.cos (2 * x) = 2 * (Real.sin x)^2 := by
  have h1 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 :=
    Real.cos_two_mul' x
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  linarith

/-- Equivalent form: `(|k|/2)·(1 - cos(2φ)) = |k|·sin²(φ)`.
    This is the "reduced" form of Theorem 1 — both sides of the identity
    after the SQG linear algebra is complete. -/
theorem half_times_one_sub_cos (absk φ : ℝ) :
    (absk / 2) * (1 - Real.cos (2 * φ)) = absk * (Real.sin φ)^2 := by
  rw [one_sub_cos_two_mul]
  ring

/-- Shear-vorticity identity for SQG in Fourier space (pointwise form).

For a Fourier mode k = |k|(cos α, sin α) and front normal n̂ = (cos β, sin β)
with tangent t̂ = (-sin β, cos β), the SQG velocity amplitudes are
  û₁ = -i k₂ θ̂ / |k|,    û₂ = i k₁ θ̂ / |k|
The strain tensor amplitudes are Ŝ_ij = (i/2)(k_i û_j + k_j û_i), and the
vorticity amplitude is ω̂ = i(k₁ û₂ - k₂ û₁).

Then:   Ŝ_nt - ω̂/2 = |k| · sin²(α - β) · θ̂

where Ŝ_nt = n̂_i Ŝ_ij t̂_j is the shear in the (n̂, t̂) frame.

STATUS: statement typechecks; proof body is `sorry`. The algebraic reduction
to `half_times_one_sub_cos` is mechanical but lengthy in raw Lean tactics.
-/
theorem sqg_shear_vorticity_identity
    (absk α β : ℝ) (θ : ℂ) (habsk : 0 < absk) :
    let k1 : ℂ := (absk * Real.cos α : ℝ)
    let k2 : ℂ := (absk * Real.sin α : ℝ)
    let n1 : ℂ := (Real.cos β : ℝ)
    let n2 : ℂ := (Real.sin β : ℝ)
    let t1 : ℂ := (-Real.sin β : ℝ)
    let t2 : ℂ := (Real.cos β : ℝ)
    let u1 : ℂ := -I * k2 * θ / (absk : ℂ)
    let u2 : ℂ := I * k1 * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * (k1 * u1 + k1 * u1)
    let S12 : ℂ := (I / 2) * (k1 * u2 + k2 * u1)
    let S22 : ℂ := (I / 2) * (k2 * u2 + k2 * u2)
    let ω : ℂ := I * (k1 * u2 - k2 * u1)
    let S_nt : ℂ := n1 * t1 * S11 + n1 * t2 * S12 + n2 * t1 * S12 + n2 * t2 * S22
    S_nt - ω / 2 = (absk : ℂ) * ((Real.sin (α - β))^2 : ℝ) * θ := by
  have hne : (absk : ℂ) ≠ 0 := by exact_mod_cast habsk.ne'
  -- After clearing /absk denominators and simplifying I² = -1, both sides reduce
  -- to a polynomial in ↑sinα, ↑cosα, ↑sinβ, ↑cosβ, ↑absk, θ.
  -- The only non-ring constraint needed is sin²β + cos²β = 1.
  have hβ : (Real.sin β : ℂ) ^ 2 + (Real.cos β : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq β
  -- Expand sin²(α - β) on the RHS so both sides are polynomial in sin/cos.
  rw [show ((Real.sin (α - β)) ^ 2 : ℝ) =
      (Real.sin α * Real.cos β - Real.cos α * Real.sin β) ^ 2 from by
    rw [Real.sin_sub]]
  -- Unfold all let bindings.
  simp only []
  -- Push ℝ→ℂ coercions inward.
  push_cast
  -- Clear the /absk denominators in u1, u2.
  field_simp [hne]
  -- Simplify I² = -1, and unify notation:
  -- push_cast may have introduced Complex.cos/sin; rewrite back to ↑(Real.cos/sin).
  simp only [I_sq, neg_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  -- Normalize the polynomial.
  ring_nf
  -- After normalization the goal factors as
  --   θ · (↑cosα² + ↑sinα²) · (1 − ↑cosβ² − ↑sinβ²) · (1 − ↑absk/2) = 0.
  -- Both the "(1 − ↑cosβ² − ↑sinβ²)" and the ↑absk·(↑sinβ²+↑cosβ²−1)/2 terms
  -- vanish by sin²β + cos²β = 1.  Coefficient from hand calculation:
  linear_combination -(θ * ((Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2)) * hβ

end SqgIdentity
