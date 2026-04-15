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

STATUS: fully proven (zero `sorry`). The algebraic reduction uses the
standard Lean tactics `push_cast`, `field_simp`, `ring_nf`, and
`linear_combination` with the Pythagorean identity as the sole closing
hypothesis.
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

/-! ## Corollaries of Theorem 1

These are the physical content of the shear-vorticity identity:
(1) half-angle form,
(2) vanishing when the wavevector is aligned with the front normal,
(3) maximum value when the wavevector is perpendicular to the front normal.
-/

/-- Half-angle restatement of Theorem 1:
    `Ŝ_nt - ω̂/2 = (|k|/2)·(1 - cos(2(α-β)))·θ̂`.
    Equivalent to the `sin²` form via `one_sub_cos_two_mul`; useful when
    the per-mode statement needs to be integrated against Fourier weights. -/
theorem sqg_shear_vorticity_identity_halfangle
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
    S_nt - ω / 2 = ((absk : ℂ) / 2) * ((1 - Real.cos (2 * (α - β))) : ℝ) * θ := by
  have h := sqg_shear_vorticity_identity absk α β θ habsk
  -- Complex-valued half-angle identity.
  have hc : ∀ z : ℂ, 1 - Complex.cos (2 * z) = 2 * (Complex.sin z)^2 := fun z => by
    have h1 := Complex.cos_two_mul z
    have h2 := Complex.sin_sq_add_cos_sq z
    linear_combination -h1 - 2 * h2
  simp only [] at h ⊢
  rw [h]
  push_cast
  rw [hc ((α : ℂ) - (β : ℂ))]
  ring

/-- **Aligned case**: when the wavevector is parallel to the front normal
    (β = α), `sin²(α - β) = 0` and the shear-vorticity combination vanishes.
    Physically: along-front modes neither strain nor spin the front. -/
theorem sqg_shear_aligned
    (absk α : ℝ) (θ : ℂ) (habsk : 0 < absk) :
    let k1 : ℂ := (absk * Real.cos α : ℝ)
    let k2 : ℂ := (absk * Real.sin α : ℝ)
    let n1 : ℂ := (Real.cos α : ℝ)
    let n2 : ℂ := (Real.sin α : ℝ)
    let t1 : ℂ := (-Real.sin α : ℝ)
    let t2 : ℂ := (Real.cos α : ℝ)
    let u1 : ℂ := -I * k2 * θ / (absk : ℂ)
    let u2 : ℂ := I * k1 * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * (k1 * u1 + k1 * u1)
    let S12 : ℂ := (I / 2) * (k1 * u2 + k2 * u1)
    let S22 : ℂ := (I / 2) * (k2 * u2 + k2 * u2)
    let ω : ℂ := I * (k1 * u2 - k2 * u1)
    let S_nt : ℂ := n1 * t1 * S11 + n1 * t2 * S12 + n2 * t1 * S12 + n2 * t2 * S22
    S_nt - ω / 2 = 0 := by
  have h := sqg_shear_vorticity_identity absk α α θ habsk
  simp only [sub_self, Real.sin_zero] at h
  simp only [] at h ⊢
  rw [h]
  push_cast
  ring

/-- **Perpendicular case**: when the wavevector is perpendicular to the
    front normal (β = α - π/2, so `sin(α - β) = 1`), the shear-vorticity
    combination attains its maximum: `Ŝ_nt - ω̂/2 = |k| · θ̂`.
    Physically: cross-front modes contribute the full `|k|·θ̂` to front
    sharpening — this is the "worst case" for regularity analysis. -/
theorem sqg_shear_perpendicular
    (absk α : ℝ) (θ : ℂ) (habsk : 0 < absk) :
    let β := α - Real.pi / 2
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
    S_nt - ω / 2 = (absk : ℂ) * θ := by
  have h := sqg_shear_vorticity_identity absk α (α - Real.pi / 2) θ habsk
  have hsin : Real.sin (α - (α - Real.pi / 2)) = 1 := by
    rw [show α - (α - Real.pi / 2) = Real.pi / 2 from by ring]
    exact Real.sin_pi_div_two
  rw [hsin] at h
  simp only [one_pow, Complex.ofReal_one, mul_one] at h
  simp only [] at h ⊢
  rw [h]

/-- **Theorem 2 — Selection rule (bound form)**:
    over every choice of front-normal angle β, the shear-vorticity
    combination obeys
        `‖Ŝ_nt - ω̂/2‖ ≤ |k| · ‖θ̂‖`.
    This bound is saturated at `β = α ± π/2` (see `sqg_shear_perpendicular`)
    and vanishes at `β = α` (see `sqg_shear_aligned`).

    In the regularity analysis of D14, this controls the worst-case
    per-mode contribution to strain growth. -/
theorem sqg_selection_rule_bound
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
    ‖S_nt - ω / 2‖ ≤ absk * ‖θ‖ := by
  have h := sqg_shear_vorticity_identity absk α β θ habsk
  simp only [] at h ⊢
  rw [h]
  -- Combine the real factors absk and sin²(α-β) into one real cast.
  rw [show ((absk : ℂ) * ((Real.sin (α - β))^2 : ℝ) * θ) =
      ((absk * (Real.sin (α - β))^2 : ℝ) : ℂ) * θ from by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ absk * (Real.sin (α - β))^2)]
  have hsin2 : (Real.sin (α - β))^2 ≤ 1 := by
    have hpy := Real.sin_sq_add_cos_sq (α - β)
    nlinarith [sq_nonneg (Real.cos (α - β))]
  have hθ : 0 ≤ ‖θ‖ := norm_nonneg θ
  -- absk * sin²(α-β) * ‖θ‖ ≤ absk * 1 * ‖θ‖ = absk * ‖θ‖.
  calc absk * (Real.sin (α - β))^2 * ‖θ‖
      ≤ absk * 1 * ‖θ‖ := by
        apply mul_le_mul_of_nonneg_right _ hθ
        exact mul_le_mul_of_nonneg_left hsin2 habsk.le
    _ = absk * ‖θ‖ := by ring

/-- **Exact magnitude** of the shear-vorticity excess:
    `‖Ŝ_nt − ω̂/2‖ = |k| · sin²(α−β) · ‖θ̂‖`.
    Refines `sqg_selection_rule_bound` by computing the norm exactly
    rather than just bounding it. -/
theorem sqg_shear_vorticity_norm
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
    ‖S_nt - ω / 2‖ = absk * (Real.sin (α - β))^2 * ‖θ‖ := by
  have h := sqg_shear_vorticity_identity absk α β θ habsk
  simp only [] at h ⊢
  rw [h]
  rw [show ((absk : ℂ) * ((Real.sin (α - β))^2 : ℝ) * θ) =
      ((absk * (Real.sin (α - β))^2 : ℝ) : ℂ) * θ from by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ absk * (Real.sin (α - β))^2)]

/-- **Theorem 2, equality case**: the selection-rule bound
    `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` is saturated if and only if either
    `sin²(α−β) = 1` (i.e., `α − β ≡ π/2 mod π`, the wavevector is
    perpendicular to the front normal) or `θ̂ = 0` (trivial case).
    This characterizes exactly which Fourier modes and orientations
    realize the worst-case strain growth. -/
theorem sqg_selection_rule_saturated_iff
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
    ‖S_nt - ω / 2‖ = absk * ‖θ‖ ↔ (Real.sin (α - β))^2 = 1 ∨ θ = 0 := by
  have hN := sqg_shear_vorticity_norm absk α β θ habsk
  simp only [] at hN ⊢
  rw [hN]
  constructor
  · intro heq
    by_cases hθ : θ = 0
    · right; exact hθ
    · left
      have hθ_ne : ‖θ‖ ≠ 0 := fun h => hθ (norm_eq_zero.mp h)
      -- From absk * sin² * ‖θ‖ = absk * ‖θ‖, conclude sin² = 1.
      have hfactored :
          absk * ((Real.sin (α - β))^2 - 1) * ‖θ‖ = 0 := by linarith
      rcases mul_eq_zero.mp hfactored with hab | hθ0
      · rcases mul_eq_zero.mp hab with habk0 | hsq0
        · exact absurd habk0 habsk.ne'
        · linarith
      · exact absurd hθ0 hθ_ne
  · rintro (h1 | h2)
    · rw [h1]; ring
    · rw [h2, norm_zero]; ring

/-! ## Cartesian form

The polar-parameterized theorems above use `k = |k|(cos α, sin α)` and
`n̂ = (cos β, sin β)`. Downstream applications typically have the
wavevector in Cartesian form `k = (k₁, k₂)`. The following theorem
restates Theorem 1 without the polar parameterization, using the
2D cross product `k × n̂ = k₂ n₁ − k₁ n₂` (which equals `|k| sin(α−β)`
in the polar parameterization).
-/

/-- **Theorem 1, Cartesian form**:
    For an arbitrary Cartesian wavevector `k = (k₁, k₂) ≠ (0, 0)` and
    unit front normal `n̂ = (n₁, n₂)` with `n₁² + n₂² = 1`,
    the shear-vorticity identity reads

        Ŝ_nt − ω̂/2 = (k₂ n₁ − k₁ n₂)² / |k| · θ̂

    where `(k₂ n₁ − k₁ n₂)` is the 2D cross product `k × n̂`, satisfying
    `|k × n̂| = |k| · |sin(angle between k and n̂)|`. The polar theorem
    `sqg_shear_vorticity_identity` is the special case
    `k = |k|(cos α, sin α)`, `n̂ = (cos β, sin β)`.
-/
theorem sqg_shear_vorticity_identity_cartesian
    (k1 k2 n1 n2 absk : ℝ) (θ : ℂ)
    (hk : absk^2 = k1^2 + k2^2) (habsk : 0 < absk)
    (hn : n1^2 + n2^2 = 1) :
    let u1 : ℂ := -I * (k2 : ℂ) * θ / (absk : ℂ)
    let u2 : ℂ := I * (k1 : ℂ) * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * ((k1 : ℂ) * u1 + (k1 : ℂ) * u1)
    let S12 : ℂ := (I / 2) * ((k1 : ℂ) * u2 + (k2 : ℂ) * u1)
    let S22 : ℂ := (I / 2) * ((k2 : ℂ) * u2 + (k2 : ℂ) * u2)
    let ω : ℂ := I * ((k1 : ℂ) * u2 - (k2 : ℂ) * u1)
    let S_nt : ℂ := (n1 : ℂ) * (-(n2 : ℂ)) * S11 + (n1 : ℂ) * (n1 : ℂ) * S12
                    + (n2 : ℂ) * (-(n2 : ℂ)) * S12 + (n2 : ℂ) * (n1 : ℂ) * S22
    S_nt - ω / 2 = ((k2 * n1 - k1 * n2)^2 : ℝ) / (absk : ℂ) * θ := by
  have hne : (absk : ℂ) ≠ 0 := by exact_mod_cast habsk.ne'
  have hkℂ : (absk : ℂ)^2 = (k1 : ℂ)^2 + (k2 : ℂ)^2 := by exact_mod_cast hk
  have hnℂ : (n1 : ℂ)^2 + (n2 : ℂ)^2 = 1 := by exact_mod_cast hn
  simp only []
  push_cast
  field_simp [hne]
  simp only [I_sq, neg_mul]
  ring_nf
  linear_combination (-θ * ((k1 : ℂ)^2 + (k2 : ℂ)^2)) * hnℂ

/-! ## Cartesian-form corollaries

Mirrors the polar corollaries (aligned / perpendicular / bound /
saturation iff) in the Cartesian parameterization. The substitutions:
  polar `sin(α−β) = 0`  ↔  Cartesian `k × n̂ = 0`  (i.e., `k₂n₁ − k₁n₂ = 0`)
  polar `sin²(α−β) = 1` ↔  Cartesian `k · n̂ = 0`  (i.e., `k₁n₁ + k₂n₂ = 0`)
The key identity `(k·n̂)² + (k×n̂)² = |k|²·|n̂|²` (which equals `|k|²`
when `|n̂| = 1`) converts between them.
-/

/-- **Cartesian aligned**: if `k × n̂ = 0` (k parallel to n̂) then the
    shear-vorticity combination vanishes: `Ŝ_nt − ω̂/2 = 0`. -/
theorem sqg_shear_aligned_cartesian
    (k1 k2 n1 n2 absk : ℝ) (θ : ℂ)
    (hk : absk^2 = k1^2 + k2^2) (habsk : 0 < absk)
    (hn : n1^2 + n2^2 = 1)
    (hcross : k2 * n1 - k1 * n2 = 0) :
    let u1 : ℂ := -I * (k2 : ℂ) * θ / (absk : ℂ)
    let u2 : ℂ := I * (k1 : ℂ) * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * ((k1 : ℂ) * u1 + (k1 : ℂ) * u1)
    let S12 : ℂ := (I / 2) * ((k1 : ℂ) * u2 + (k2 : ℂ) * u1)
    let S22 : ℂ := (I / 2) * ((k2 : ℂ) * u2 + (k2 : ℂ) * u2)
    let ω : ℂ := I * ((k1 : ℂ) * u2 - (k2 : ℂ) * u1)
    let S_nt : ℂ := (n1 : ℂ) * (-(n2 : ℂ)) * S11 + (n1 : ℂ) * (n1 : ℂ) * S12
                    + (n2 : ℂ) * (-(n2 : ℂ)) * S12 + (n2 : ℂ) * (n1 : ℂ) * S22
    S_nt - ω / 2 = 0 := by
  have h := sqg_shear_vorticity_identity_cartesian k1 k2 n1 n2 absk θ hk habsk hn
  have hsq : (k2 * n1 - k1 * n2)^2 = 0 := by rw [hcross]; ring
  simp only [] at h ⊢
  rw [h, hsq]
  push_cast
  simp

/-- **Cartesian perpendicular**: if `k · n̂ = 0` (k perpendicular to n̂)
    then `Ŝ_nt − ω̂/2 = |k| · θ̂`. -/
theorem sqg_shear_perpendicular_cartesian
    (k1 k2 n1 n2 absk : ℝ) (θ : ℂ)
    (hk : absk^2 = k1^2 + k2^2) (habsk : 0 < absk)
    (hn : n1^2 + n2^2 = 1)
    (hdot : k1 * n1 + k2 * n2 = 0) :
    let u1 : ℂ := -I * (k2 : ℂ) * θ / (absk : ℂ)
    let u2 : ℂ := I * (k1 : ℂ) * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * ((k1 : ℂ) * u1 + (k1 : ℂ) * u1)
    let S12 : ℂ := (I / 2) * ((k1 : ℂ) * u2 + (k2 : ℂ) * u1)
    let S22 : ℂ := (I / 2) * ((k2 : ℂ) * u2 + (k2 : ℂ) * u2)
    let ω : ℂ := I * ((k1 : ℂ) * u2 - (k2 : ℂ) * u1)
    let S_nt : ℂ := (n1 : ℂ) * (-(n2 : ℂ)) * S11 + (n1 : ℂ) * (n1 : ℂ) * S12
                    + (n2 : ℂ) * (-(n2 : ℂ)) * S12 + (n2 : ℂ) * (n1 : ℂ) * S22
    S_nt - ω / 2 = (absk : ℂ) * θ := by
  have h := sqg_shear_vorticity_identity_cartesian k1 k2 n1 n2 absk θ hk habsk hn
  -- (k×n̂)² = |k|² when k·n̂ = 0 and |n̂| = 1:
  have hsq : (k2 * n1 - k1 * n2)^2 = absk^2 := by
    have hid : (k1*n1 + k2*n2)^2 + (k2*n1 - k1*n2)^2 = (k1^2+k2^2)*(n1^2+n2^2) := by ring
    nlinarith [hdot, hn, hk, hid]
  simp only [] at h ⊢
  rw [h, hsq]
  have hne : (absk : ℂ) ≠ 0 := by exact_mod_cast habsk.ne'
  push_cast
  field_simp

/-- **Theorem 2 — Selection rule bound (Cartesian form)**:
    `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` for arbitrary Cartesian wavevector
    `k = (k₁, k₂) ≠ 0` and unit front normal `n̂`. -/
theorem sqg_selection_rule_bound_cartesian
    (k1 k2 n1 n2 absk : ℝ) (θ : ℂ)
    (hk : absk^2 = k1^2 + k2^2) (habsk : 0 < absk)
    (hn : n1^2 + n2^2 = 1) :
    let u1 : ℂ := -I * (k2 : ℂ) * θ / (absk : ℂ)
    let u2 : ℂ := I * (k1 : ℂ) * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * ((k1 : ℂ) * u1 + (k1 : ℂ) * u1)
    let S12 : ℂ := (I / 2) * ((k1 : ℂ) * u2 + (k2 : ℂ) * u1)
    let S22 : ℂ := (I / 2) * ((k2 : ℂ) * u2 + (k2 : ℂ) * u2)
    let ω : ℂ := I * ((k1 : ℂ) * u2 - (k2 : ℂ) * u1)
    let S_nt : ℂ := (n1 : ℂ) * (-(n2 : ℂ)) * S11 + (n1 : ℂ) * (n1 : ℂ) * S12
                    + (n2 : ℂ) * (-(n2 : ℂ)) * S12 + (n2 : ℂ) * (n1 : ℂ) * S22
    ‖S_nt - ω / 2‖ ≤ absk * ‖θ‖ := by
  have h := sqg_shear_vorticity_identity_cartesian k1 k2 n1 n2 absk θ hk habsk hn
  have hsq : (k2 * n1 - k1 * n2)^2 ≤ absk^2 := by
    have hid : (k1*n1 + k2*n2)^2 + (k2*n1 - k1*n2)^2 = (k1^2+k2^2)*(n1^2+n2^2) := by ring
    nlinarith [sq_nonneg (k1*n1 + k2*n2), hn, hk, hid]
  simp only [] at h ⊢
  rw [h, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (k2*n1 - k1*n2)),
      abs_of_pos habsk]
  -- Goal: (k2*n1 - k1*n2)^2 / absk * ‖θ‖ ≤ absk * ‖θ‖
  have hbound : (k2 * n1 - k1 * n2)^2 / absk ≤ absk := by
    rw [div_le_iff₀ habsk]
    nlinarith [hsq]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg θ)

/-- **Theorem 2, equality case (Cartesian form)**: the selection-rule
    bound is saturated iff `k · n̂ = 0` (wavevector perpendicular to
    front normal) or `θ̂ = 0` (trivial). -/
theorem sqg_selection_rule_saturated_iff_cartesian
    (k1 k2 n1 n2 absk : ℝ) (θ : ℂ)
    (hk : absk^2 = k1^2 + k2^2) (habsk : 0 < absk)
    (hn : n1^2 + n2^2 = 1) :
    let u1 : ℂ := -I * (k2 : ℂ) * θ / (absk : ℂ)
    let u2 : ℂ := I * (k1 : ℂ) * θ / (absk : ℂ)
    let S11 : ℂ := (I / 2) * ((k1 : ℂ) * u1 + (k1 : ℂ) * u1)
    let S12 : ℂ := (I / 2) * ((k1 : ℂ) * u2 + (k2 : ℂ) * u1)
    let S22 : ℂ := (I / 2) * ((k2 : ℂ) * u2 + (k2 : ℂ) * u2)
    let ω : ℂ := I * ((k1 : ℂ) * u2 - (k2 : ℂ) * u1)
    let S_nt : ℂ := (n1 : ℂ) * (-(n2 : ℂ)) * S11 + (n1 : ℂ) * (n1 : ℂ) * S12
                    + (n2 : ℂ) * (-(n2 : ℂ)) * S12 + (n2 : ℂ) * (n1 : ℂ) * S22
    ‖S_nt - ω / 2‖ = absk * ‖θ‖ ↔ k1 * n1 + k2 * n2 = 0 ∨ θ = 0 := by
  have h := sqg_shear_vorticity_identity_cartesian k1 k2 n1 n2 absk θ hk habsk hn
  have hid : (k1*n1 + k2*n2)^2 + (k2*n1 - k1*n2)^2 = (k1^2+k2^2)*(n1^2+n2^2) := by ring
  simp only [] at h ⊢
  rw [h, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (k2*n1 - k1*n2)),
      abs_of_pos habsk]
  constructor
  · intro heq
    by_cases hθ : θ = 0
    · right; exact hθ
    · left
      have hθ_ne : ‖θ‖ ≠ 0 := fun h => hθ (norm_eq_zero.mp h)
      have hA : (k2*n1 - k1*n2)^2 / absk = absk :=
        mul_right_cancel₀ hθ_ne heq
      have hB : (k2*n1 - k1*n2)^2 = absk^2 := by
        have h1 : (k2*n1 - k1*n2)^2 = absk * absk := (div_eq_iff habsk.ne').mp hA
        nlinarith [h1]
      have hC : (k1*n1 + k2*n2)^2 = 0 := by nlinarith [hid, hB, hk, hn]
      exact sq_eq_zero_iff.mp hC
  · rintro (hdot | hθ0)
    · have hC : (k1*n1 + k2*n2)^2 = 0 := by rw [hdot]; ring
      have hB : (k2*n1 - k1*n2)^2 = absk^2 := by nlinarith [hid, hC, hk, hn]
      rw [hB]
      have : absk^2 / absk = absk := by
        rw [sq, mul_div_assoc, div_self habsk.ne', mul_one]
      rw [this]
    · rw [hθ0, norm_zero]; ring

/-! ## ℓ² summability lift

The pointwise selection-rule bound
    `‖Ŝ_nt(k) − ω̂(k)/2‖ ≤ |k|·‖θ̂(k)‖`
holds at each Fourier mode (polar: `sqg_selection_rule_bound`, Cartesian:
`sqg_selection_rule_bound_cartesian`). Squaring and summing over modes
yields the integrated ℓ² bound
    `Σ_k ‖Ŝ_nt(k) − ω̂(k)/2‖² ≤ Σ_k |k|²·‖θ̂(k)‖²`
which, by Parseval, is the statement
    `‖S_nt − ω/2‖_{L²} ≤ ‖∇θ‖_{L²}`
needed for Theorem 3's regularity analysis.

The content below is the general squaring-and-summing step, with the
concrete Fourier-basis packaging deferred to a future file.
-/

/-- **ℓ² lift of a pointwise norm bound**: given a pointwise inequality
    `‖x i‖ ≤ r i · ‖y i‖` with `r i ≥ 0`, and summability of the weighted
    squared family `(r i)² · ‖y i‖²`, the squared family `‖x i‖²` is
    summable and satisfies the integrated bound.

    Applied to `x i = Ŝ_nt(kᵢ) − ω̂(kᵢ)/2`, `r i = |kᵢ|`, `y i = θ̂(kᵢ)`,
    together with `sqg_selection_rule_bound_cartesian`, this yields
    Theorem 2 in ℓ² form. -/
theorem pointwise_bound_to_ell2 {ι : Type*}
    (x y : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hpointwise : ∀ i, ‖x i‖ ≤ r i * ‖y i‖)
    (hsum : Summable (fun i => (r i)^2 * ‖y i‖^2)) :
    Summable (fun i => ‖x i‖^2) ∧
    (∑' i, ‖x i‖^2) ≤ ∑' i, (r i)^2 * ‖y i‖^2 := by
  have hsq : ∀ i, ‖x i‖^2 ≤ (r i)^2 * ‖y i‖^2 := by
    intro i
    have hxnn : 0 ≤ ‖x i‖ := norm_nonneg _
    have hpoint := hpointwise i
    calc ‖x i‖^2
        = ‖x i‖ * ‖x i‖ := by ring
      _ ≤ (r i * ‖y i‖) * (r i * ‖y i‖) := by
          exact mul_self_le_mul_self hxnn hpoint
      _ = (r i)^2 * ‖y i‖^2 := by ring
  have hnn : ∀ i, 0 ≤ ‖x i‖^2 := fun i => sq_nonneg _
  have hsumm : Summable (fun i => ‖x i‖^2) :=
    hsum.of_nonneg_of_le hnn hsq
  exact ⟨hsumm, hsumm.tsum_le_tsum hsq hsum⟩

/-- **Theorem 2 (ℓ² form)**: Concrete specialization — given a family of
    SQG Fourier modes indexed by `ι`, where at each index `i` the
    pointwise selection-rule bound is given, and the weighted amplitudes
    `|kᵢ|²·‖θ̂ᵢ‖²` are summable, the shear-vorticity excess is ℓ²
    summable with
        `Σᵢ ‖ŵᵢ‖² ≤ Σᵢ |kᵢ|²·‖θ̂ᵢ‖²`
    where `ŵᵢ` denotes `Ŝ_nt(kᵢ) − ω̂(kᵢ)/2`.

    (The hypothesis `hpointwise` is what
    `sqg_selection_rule_bound_cartesian` supplies per-mode; this lemma
    does the ℓ² packaging.) -/
theorem sqg_selection_rule_ell2 {ι : Type*}
    (w : ι → ℂ) (θ : ι → ℂ) (absk : ι → ℝ)
    (habsk_nn : ∀ i, 0 ≤ absk i)
    (hpointwise : ∀ i, ‖w i‖ ≤ absk i * ‖θ i‖)
    (hsum : Summable (fun i => (absk i)^2 * ‖θ i‖^2)) :
    Summable (fun i => ‖w i‖^2) ∧
    (∑' i, ‖w i‖^2) ≤ ∑' i, (absk i)^2 * ‖θ i‖^2 :=
  pointwise_bound_to_ell2 w θ absk habsk_nn hpointwise hsum

end SqgIdentity
