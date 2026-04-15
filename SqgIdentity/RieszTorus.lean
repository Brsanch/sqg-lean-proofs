-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).
-- Torus Riesz-transform library (Fourier-multiplier approach).

import Mathlib
import SqgIdentity.Basic

/-!
# Riesz transforms on the unit torus `𝕋ᵈ` via Fourier multipliers

This file develops the part of the Riesz-transform library needed for the
integrated form of D14 Theorem 2 on the torus, bypassing general
Calderón–Zygmund singular-integral theory. The key observation is that on
the torus the Riesz transform `R_j` has a bounded Fourier multiplier
symbol

    m_j(n) = -i · n_j / ‖n‖    (for n ≠ 0),

so its L²-theory falls out of Parseval.

## Main contents

* `latticeNorm n := sqrt(Σ nⱼ²)` with basic positivity and support lemmas.
* `rieszSymbol j n = -i nⱼ/‖n‖` (off zero), with `‖m_j(n)‖ ≤ 1` and the
  Pythagorean identity `Σⱼ ‖m_j(n)‖² = 1` for `n ≠ 0`.
* `sqg_velocity_symbol_isometry` — on `𝕋²`, for any `z ∈ ℂ`,
  `‖m₂·z‖² + ‖(-m₁)·z‖² = ‖z‖²` when `n ≠ 0`.
* `L2_contractive_of_bounded_symbol` — `‖m‖∞ ≤ 1` + Parseval implies
  L² contractivity for any Fourier multiplier.
* `riesz_L2_contractive` — `‖R_j f‖_{L²(𝕋ᵈ)} ≤ ‖f‖_{L²(𝕋ᵈ)}`.
* `sqg_velocity_L2_isometry` — `‖u₁‖²_{L²} + ‖u₂‖²_{L²} = ‖θ‖²_{L²}`
  for the SQG velocity of a zero-mean scalar `θ` on `𝕋²`.
* `fracDerivSymbol s n = ‖n‖^s` (off zero) — symbol of `(-Δ)^{s/2}`.
* `hsSeminormSq s f = Σ ‖n‖^{2s}·‖f̂(n)‖²` — the homogeneous Ḣˢ seminorm
  squared on `L²(𝕋ᵈ)`, identified with `‖(-Δ)^{s/2} f‖²_{L²}` via
  the Fourier multiplier.
* `sqg_selection_rule_Hs1` — Ḣ¹ form of Theorem 2 on the torus.

All statements are driven by `hasSum_sq_mFourierCoeff` (Parseval); no
singular-integral machinery is invoked.
-/

namespace SqgIdentity

open Complex Finset MeasureTheory

/-! ### The lattice norm `‖n‖ = √(Σⱼ nⱼ²)` -/

/-- The Euclidean norm on the integer lattice, extended by real arithmetic
(so its square is `Σⱼ (nⱼ)²`). -/
noncomputable def latticeNorm {d : Type*} [Fintype d] (n : d → ℤ) : ℝ :=
  Real.sqrt (∑ j, (n j : ℝ) ^ 2)

lemma latticeNorm_nonneg {d : Type*} [Fintype d] (n : d → ℤ) :
    0 ≤ latticeNorm n :=
  Real.sqrt_nonneg _

lemma latticeNorm_sq {d : Type*} [Fintype d] (n : d → ℤ) :
    (latticeNorm n) ^ 2 = ∑ j, (n j : ℝ) ^ 2 := by
  unfold latticeNorm
  have h : 0 ≤ ∑ j, (n j : ℝ) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.sq_sqrt h]

/-- The lattice norm vanishes exactly at `n = 0`. -/
lemma latticeNorm_eq_zero_iff {d : Type*} [Fintype d] (n : d → ℤ) :
    latticeNorm n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hsq : ∑ j, (n j : ℝ) ^ 2 = 0 := by
      have := congrArg (· ^ 2) h
      simpa [latticeNorm_sq] using this
    have hall : ∀ j ∈ (Finset.univ : Finset d), (n j : ℝ) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsq
    funext j
    have hj : (n j : ℝ) ^ 2 = 0 := hall j (Finset.mem_univ j)
    have : (n j : ℝ) = 0 := by
      have := sq_eq_zero_iff.mp hj
      exact this
    exact_mod_cast this
  · rintro rfl
    unfold latticeNorm
    simp

/-- For `n ≠ 0`, the lattice norm is strictly positive. -/
lemma latticeNorm_pos {d : Type*} [Fintype d] {n : d → ℤ} (hn : n ≠ 0) :
    0 < latticeNorm n :=
  lt_of_le_of_ne (latticeNorm_nonneg n)
    (fun h => hn ((latticeNorm_eq_zero_iff n).mp h.symm))

/-- Componentwise bound: `(n_j)² ≤ Σ (n_i)² = ‖n‖²`. -/
lemma sq_le_latticeNorm_sq {d : Type*} [Fintype d] (n : d → ℤ) (j : d) :
    (n j : ℝ) ^ 2 ≤ (latticeNorm n) ^ 2 := by
  rw [latticeNorm_sq]
  exact Finset.single_le_sum (f := fun i : d => ((n i : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-! ### The Riesz symbol `m_j(n) = -i nⱼ/‖n‖` -/

/-- The Riesz transform symbol on `𝕋ᵈ`:

    m_j(n) = -i · n_j / ‖n‖    for n ≠ 0,    m_j(0) = 0. -/
noncomputable def rieszSymbol {d : Type*} [Fintype d]
    (j : d) (n : d → ℤ) : ℂ :=
  if n = 0 then 0 else -I * ((n j : ℝ) : ℂ) / ((latticeNorm n : ℝ) : ℂ)

@[simp]
lemma rieszSymbol_zero {d : Type*} [Fintype d] (j : d) :
    rieszSymbol j (0 : d → ℤ) = 0 := by
  simp [rieszSymbol]

/-- Norm of the Riesz symbol: for `n ≠ 0`, `|m_j(n)| = |n_j| / ‖n‖`. -/
lemma norm_rieszSymbol {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) (j : d) :
    ‖rieszSymbol j n‖ = |(n j : ℝ)| / latticeNorm n := by
  have hpos : 0 < latticeNorm n := latticeNorm_pos hn
  unfold rieszSymbol
  rw [if_neg hn]
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul]
  congr 1
  · rw [Complex.norm_real, Real.norm_eq_abs]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- **Pointwise bound**: every Riesz symbol satisfies `|m_j(n)| ≤ 1`.
Combined with Parseval, this gives L²-contractivity of `R_j`. -/
theorem rieszSymbol_norm_le_one {d : Type*} [Fintype d]
    (j : d) (n : d → ℤ) : ‖rieszSymbol j n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [rieszSymbol, hn]
  · have hpos : 0 < latticeNorm n := latticeNorm_pos hn
    rw [norm_rieszSymbol hn, div_le_iff₀ hpos, one_mul]
    rw [← Real.sqrt_sq_eq_abs]
    have hle : ((n j : ℝ)) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i : d => ((n i : ℝ)) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    calc Real.sqrt ((n j : ℝ) ^ 2)
        ≤ Real.sqrt (∑ i, (n i : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = latticeNorm n := rfl

/-- **Pythagorean sum identity**: `Σⱼ |m_j(n)|² = 1` for `n ≠ 0`.
This is the identity that makes the Riesz-vector `R = (R_1, …, R_d)` a
partial isometry on mean-zero L² functions. -/
theorem rieszSymbol_sum_sq {d : Type*} [Fintype d] {n : d → ℤ} (hn : n ≠ 0) :
    ∑ j, ‖rieszSymbol j n‖ ^ 2 = 1 := by
  have hpos : 0 < latticeNorm n := latticeNorm_pos hn
  have hne : (latticeNorm n) ^ 2 ≠ 0 := ne_of_gt (pow_pos hpos 2)
  have hterm : ∀ j, ‖rieszSymbol j n‖ ^ 2 = (n j : ℝ) ^ 2 / (latticeNorm n) ^ 2 := by
    intro j
    rw [norm_rieszSymbol hn, div_pow, sq_abs]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← latticeNorm_sq]
  exact div_self hne

/-- Compact form of the Riesz symbol off zero, useful for algebraic
rewrites (no `if` branch in sight). -/
lemma rieszSymbol_of_ne_zero {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) (j : d) :
    rieszSymbol j n = -I * ((n j : ℝ) : ℂ) / ((latticeNorm n : ℝ) : ℂ) := by
  simp [rieszSymbol, hn]

/-- **Complex-valued Riesz identity**: `Σⱼ (m_j(n))² = -1` for `n ≠ 0`.

This is the Fourier-multiplier form of the operator identity
`Σⱼ R_j² = -Id` on zero-mean functions, i.e., `-Δ = -Σⱼ ∂_j²` expressed
via the factorisation `∂_j = (-Δ)^{1/2}·R_j`. Note the sign vs. the
norm Pythagorean identity: `|m_j|² = (-n_j²)/‖n‖² · (-1)` absorbs the
`-I² = 1` into absolute value, but the raw complex square keeps it. -/
theorem rieszSymbol_sum_sq_complex {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) :
    ∑ j, (rieszSymbol j n) ^ 2 = -1 := by
  have hpos : 0 < latticeNorm n := latticeNorm_pos hn
  have hne : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hne2 : ((latticeNorm n : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  -- Key: each squared term, times ‖n‖², equals -n_j²
  have hterm : ∀ j, (rieszSymbol j n) ^ 2 * ((latticeNorm n : ℝ) : ℂ) ^ 2
             = -(((n j : ℝ) : ℂ) ^ 2) := by
    intro j
    rw [rieszSymbol_of_ne_zero hn]
    field_simp
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((n j : ℝ) : ℂ) ^ 2 * hI
  -- Sum the per-j equalities and divide by ‖n‖²
  have hsum_real : ∑ j, ((n j : ℝ) : ℂ) ^ 2 = ((latticeNorm n : ℝ) : ℂ) ^ 2 := by
    have h1 : (∑ j, ((n j : ℝ) : ℂ) ^ 2)
            = ((∑ j, ((n j : ℝ)) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, ← latticeNorm_sq]
    push_cast; rfl
  have hmul : (∑ j, (rieszSymbol j n) ^ 2) * ((latticeNorm n : ℝ) : ℂ) ^ 2
           = (-1) * ((latticeNorm n : ℝ) : ℂ) ^ 2 := by
    rw [Finset.sum_mul]
    calc ∑ j, (rieszSymbol j n) ^ 2 * ((latticeNorm n : ℝ) : ℂ) ^ 2
        = ∑ j, -(((n j : ℝ) : ℂ) ^ 2) := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = -(∑ j, ((n j : ℝ) : ℂ) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = -(((latticeNorm n : ℝ) : ℂ) ^ 2) := by rw [hsum_real]
      _ = (-1) * ((latticeNorm n : ℝ) : ℂ) ^ 2 := by ring
  exact mul_right_cancel₀ hne2 hmul

/-! ### SQG velocity divergence-free at the symbol level -/

/-- **SQG velocity is divergence-free at the symbol level.** On `𝕋²`,
for any `z ∈ ℂ` and any lattice point `n ∈ ℤ²`,

    n₁ · (m₂(n)·z) + n₂ · (-m₁(n)·z) = 0,

i.e. `k · û(k) = 0` when `û = (m₂·θ̂, -m₁·θ̂)`. -/
theorem sqg_velocity_divergence_free_symbol
    (n : Fin 2 → ℤ) (z : ℂ) :
    ((n 0 : ℝ) : ℂ) * (rieszSymbol 1 n * z)
      + ((n 1 : ℝ) : ℂ) * ((-rieszSymbol 0 n) * z) = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 0 < latticeNorm n := latticeNorm_pos hn
    have hne : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    rw [rieszSymbol_of_ne_zero hn (j := 1), rieszSymbol_of_ne_zero hn (j := 0)]
    field_simp
    ring

/-! ### SQG velocity symbol isometry on `𝕋²` -/

/-- **SQG velocity symbol isometry on `𝕋²`.** For any `z ∈ ℂ` and any
non-zero lattice point `n ∈ ℤ²`,

    ‖m₂(n)·z‖² + ‖(-m₁(n))·z‖² = ‖z‖²,

which is the per-mode statement that `(u₁, u₂) = (m₂·θ̂, -m₁·θ̂)`
conserves energy. -/
theorem sqg_velocity_symbol_isometry {n : Fin 2 → ℤ} (hn : n ≠ 0) (z : ℂ) :
    ‖rieszSymbol 1 n * z‖ ^ 2 + ‖(- rieszSymbol 0 n) * z‖ ^ 2 = ‖z‖ ^ 2 := by
  have hsum : ‖rieszSymbol 1 n‖ ^ 2 + ‖rieszSymbol 0 n‖ ^ 2 = 1 := by
    have := rieszSymbol_sum_sq (n := n) hn
    -- Σⱼ ‖m_j‖² sums j over Fin 2 = {0, 1}
    simpa [Fin.sum_univ_two, add_comm] using this
  have h1 : ‖rieszSymbol 1 n * z‖ ^ 2 = ‖rieszSymbol 1 n‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  have h2 : ‖(- rieszSymbol 0 n) * z‖ ^ 2 = ‖rieszSymbol 0 n‖ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_neg, mul_pow]
  rw [h1, h2, ← add_mul, hsum, one_mul]

/-! ### Fractional-derivative symbol `σ_s(n) = ‖n‖ˢ` -/

/-- The Fourier multiplier symbol of `(-Δ)^{s/2}` on `𝕋ᵈ`, defined as
`‖n‖^s` off zero and `0` at `n = 0` (the zero-mean convention that makes
it a genuine seminorm). -/
noncomputable def fracDerivSymbol {d : Type*} [Fintype d]
    (s : ℝ) (n : d → ℤ) : ℝ :=
  if n = 0 then 0 else (latticeNorm n) ^ s

@[simp]
lemma fracDerivSymbol_zero {d : Type*} [Fintype d] (s : ℝ) :
    fracDerivSymbol s (0 : d → ℤ) = 0 := by
  simp [fracDerivSymbol]

lemma fracDerivSymbol_of_ne_zero {d : Type*} [Fintype d] (s : ℝ)
    {n : d → ℤ} (hn : n ≠ 0) :
    fracDerivSymbol s n = (latticeNorm n) ^ s := by
  simp [fracDerivSymbol, hn]

lemma fracDerivSymbol_nonneg {d : Type*} [Fintype d] (s : ℝ) (n : d → ℤ) :
    0 ≤ fracDerivSymbol s n := by
  by_cases hn : n = 0
  · simp [fracDerivSymbol, hn]
  · rw [fracDerivSymbol_of_ne_zero s hn]
    exact Real.rpow_nonneg (latticeNorm_nonneg n) s

lemma fracDerivSymbol_pos {d : Type*} [Fintype d] (s : ℝ)
    {n : d → ℤ} (hn : n ≠ 0) :
    0 < fracDerivSymbol s n := by
  rw [fracDerivSymbol_of_ne_zero s hn]
  exact Real.rpow_pos_of_pos (latticeNorm_pos hn) s

/-- At `s = 1`, `fracDerivSymbol` is just `‖n‖` off zero. -/
lemma fracDerivSymbol_one_eq {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) :
    fracDerivSymbol 1 n = latticeNorm n := by
  rw [fracDerivSymbol_of_ne_zero 1 hn, Real.rpow_one]

/-- At `s = 2`, `fracDerivSymbol` is `‖n‖²` off zero. -/
lemma fracDerivSymbol_two_eq {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) :
    fracDerivSymbol 2 n = (latticeNorm n) ^ 2 := by
  rw [fracDerivSymbol_of_ne_zero 2 hn]
  have h : (latticeNorm n) ^ (2 : ℝ) = (latticeNorm n) ^ (2 : ℕ) :=
    Real.rpow_natCast (latticeNorm n) 2
  simpa using h

/-! ### Symbol-level identity `∂_j = (-Δ)^{1/2} · R_j` -/

/-- **Symbol factorisation** `∂_j = (-Δ)^{1/2} · R_j`. Off the zero
mode, `m_j(n) · ‖n‖ = -i · n_j`, i.e. the Riesz multiplier times the
`(-Δ)^{1/2}` multiplier recovers the symbol of the partial derivative
`∂_j` (with the usual `-i` convention). -/
lemma rieszSymbol_mul_fracDeriv_one {d : Type*} [Fintype d] (j : d)
    {n : d → ℤ} (hn : n ≠ 0) :
    rieszSymbol j n * ((fracDerivSymbol 1 n : ℝ) : ℂ)
      = -I * ((n j : ℝ) : ℂ) := by
  have hpos : 0 < latticeNorm n := latticeNorm_pos hn
  have hne : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  rw [rieszSymbol_of_ne_zero hn, fracDerivSymbol_one_eq hn]
  field_simp

/-! ### Derivative symbol `∂_j ↔ i·n_j` and the Ḣ¹ identification -/

/-- The Fourier multiplier symbol of `∂_j` on `𝕋ᵈ`, i.e. `i · n_j`
(the usual convention `f̂(n) = ∫ f·e^{-2πi n·x} dx` is hidden in the
torus library; here we track the symbol modulo the `2π` convention). -/
noncomputable def derivSymbol {d : Type*} [Fintype d]
    (j : d) (n : d → ℤ) : ℂ := I * ((n j : ℝ) : ℂ)

@[simp]
lemma derivSymbol_zero {d : Type*} [Fintype d] (j : d) :
    derivSymbol j (0 : d → ℤ) = 0 := by
  simp [derivSymbol]

lemma norm_derivSymbol {d : Type*} [Fintype d] (j : d) (n : d → ℤ) :
    ‖derivSymbol j n‖ = |(n j : ℝ)| := by
  unfold derivSymbol
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_derivSymbol_sq {d : Type*} [Fintype d] (j : d) (n : d → ℤ) :
    ‖derivSymbol j n‖ ^ 2 = (n j : ℝ) ^ 2 := by
  rw [norm_derivSymbol, sq_abs]

/-- **Pythagorean identity for the derivative symbol.** The sum over
coordinate directions of `‖i·n_j‖²` recovers `‖n‖²`. -/
lemma sum_norm_derivSymbol_sq {d : Type*} [Fintype d] (n : d → ℤ) :
    ∑ j, ‖derivSymbol j n‖ ^ 2 = (latticeNorm n) ^ 2 := by
  rw [latticeNorm_sq]
  exact Finset.sum_congr rfl (fun j _ => norm_derivSymbol_sq j n)

/-- **Symbol-level factorisation** `∂_j = (-Δ)^{1/2} · R_j`. For every
lattice point `n` (including `n = 0`), the Riesz multiplier `m_j(n)`
times the `(-Δ)^{1/2}` multiplier `‖n‖` equals the derivative symbol
`-i · n_j = -derivSymbol j n`. -/
lemma rieszSymbol_mul_fracDeriv_one_eq_neg_derivSymbol
    {d : Type*} [Fintype d] (j : d) (n : d → ℤ) :
    rieszSymbol j n * ((fracDerivSymbol 1 n : ℝ) : ℂ)
      = -derivSymbol j n := by
  by_cases hn : n = 0
  · simp [hn, derivSymbol]
  · rw [rieszSymbol_mul_fracDeriv_one j hn]
    unfold derivSymbol
    ring

/-! ### Measure-theoretic setup for torus L² integrals -/

-- Replicate the file-local instance from `Mathlib.Analysis.Fourier.AddCircleMulti`
-- so `Lp ℂ 2 (volume : Measure (UnitAddTorus d))` is well-defined here.
noncomputable local instance rieszTorusMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance rieszTorusHaar :
    MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance rieszTorusProb :
    MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open UnitAddTorus

/-! ### Generic L²-contractivity of bounded Fourier multipliers -/

/-- **L²-contractivity for bounded Fourier multipliers.** If two L²
functions `f, g` on `𝕋ᵈ` satisfy `ĝ(n) = m(n)·f̂(n)` with a pointwise
bounded multiplier `‖m(n)‖ ≤ 1`, then `‖g‖_{L²} ≤ ‖f‖_{L²}`. -/
theorem L2_contractive_of_bounded_symbol
    {d : Type*} [Fintype d]
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (_hm : ∀ n, ‖m n‖ ≤ 1)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n) :
    (∫ t, ‖g t‖ ^ 2) ≤ ∫ t, ‖f t‖ ^ 2 := by
  have hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2) := hasSum_sq_mFourierCoeff f
  have hg_parseval : HasSum (fun n ↦ ‖mFourierCoeff g n‖ ^ 2)
      (∫ t, ‖g t‖ ^ 2) := hasSum_sq_mFourierCoeff g
  -- Pointwise: ‖ĝ(n)‖² = ‖m(n)‖² · ‖f̂(n)‖² ≤ ‖f̂(n)‖²
  have hpt : ∀ n, ‖mFourierCoeff g n‖ ^ 2 ≤ ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    rw [hcoeff n, norm_mul, mul_pow]
    have h1 : ‖m n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖m n‖ := norm_nonneg _
      nlinarith [_hm n, h0]
    calc ‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2
        ≤ 1 * ‖mFourierCoeff f n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  -- Sum comparison
  have hsummable : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) := hf_parseval.summable
  have hle : ∑' n, ‖mFourierCoeff g n‖ ^ 2 ≤ ∑' n, ‖mFourierCoeff f n‖ ^ 2 :=
    Summable.tsum_le_tsum hpt (hg_parseval.summable) hsummable
  calc (∫ t, ‖g t‖ ^ 2)
      = ∑' n, ‖mFourierCoeff g n‖ ^ 2 := hg_parseval.tsum_eq.symm
    _ ≤ ∑' n, ‖mFourierCoeff f n‖ ^ 2 := hle
    _ = ∫ t, ‖f t‖ ^ 2 := hf_parseval.tsum_eq

/-- **L²-isometry for unit-modulus Fourier multipliers.** If `‖m(n)‖ = 1`
pointwise and `ĝ = m·f̂`, then `‖g‖_{L²} = ‖f‖_{L²}`. -/
theorem L2_isometry_of_unit_symbol
    {d : Type*} [Fintype d]
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hm : ∀ n, ‖m n‖ = 1)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n) :
    (∫ t, ‖g t‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  have hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2) := hasSum_sq_mFourierCoeff f
  have hg_parseval : HasSum (fun n ↦ ‖mFourierCoeff g n‖ ^ 2)
      (∫ t, ‖g t‖ ^ 2) := hasSum_sq_mFourierCoeff g
  have hpt : ∀ n, ‖mFourierCoeff g n‖ ^ 2 = ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    rw [hcoeff n, norm_mul, mul_pow, hm n, one_pow, one_mul]
  have heq : (fun n ↦ ‖mFourierCoeff g n‖ ^ 2)
           = (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) := funext hpt
  rw [heq] at hg_parseval
  exact hg_parseval.unique hf_parseval

/-! ### L²-contractivity of the Riesz transform on `𝕋ᵈ` -/

/-- **L²-contractivity of the Riesz transform.** If `R_j f` is an L²
function on `𝕋ᵈ` whose Fourier coefficients are given by the Riesz
multiplier, then `‖R_j f‖²_{L²} ≤ ‖f‖²_{L²}`. -/
theorem riesz_L2_contractive
    {d : Type*} [Fintype d] (j : d)
    (f Rj_f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ n, mFourierCoeff Rj_f n = rieszSymbol j n * mFourierCoeff f n) :
    (∫ t, ‖Rj_f t‖ ^ 2) ≤ ∫ t, ‖f t‖ ^ 2 :=
  L2_contractive_of_bounded_symbol f Rj_f (rieszSymbol j)
    (rieszSymbol_norm_le_one j) hcoeff

/-! ### SQG velocity L²-isometry on `𝕋²` -/

/-- **SQG velocity L²-isometry on `𝕋²`.**

If `θ ∈ L²(𝕋²)` has zero mean (`θ̂(0) = 0`), and `u₁, u₂ ∈ L²(𝕋²)` are the
components of the SQG velocity defined by their Fourier coefficients

    û₁(n) = m₂(n)·θ̂(n)      (= -i·n₂/‖n‖·θ̂(n))
    û₂(n) = -m₁(n)·θ̂(n)     (= i·n₁/‖n‖·θ̂(n))

then `‖u₁‖²_{L²} + ‖u₂‖²_{L²} = ‖θ‖²_{L²}`. Vectorially this is the SQG
energy-conservation identity `‖u‖_{L²(𝕋²)} = ‖θ‖_{L²(𝕋²)}`. -/
theorem sqg_velocity_L2_isometry
    (θ u₁ u₂ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ_mean : mFourierCoeff θ 0 = 0)
    (hu₁ : ∀ n, mFourierCoeff u₁ n = rieszSymbol 1 n * mFourierCoeff θ n)
    (hu₂ : ∀ n, mFourierCoeff u₂ n = -rieszSymbol 0 n * mFourierCoeff θ n) :
    (∫ t, ‖u₁ t‖ ^ 2) + (∫ t, ‖u₂ t‖ ^ 2) = ∫ t, ‖θ t‖ ^ 2 := by
  have hθ_parseval : HasSum (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)
      (∫ t, ‖θ t‖ ^ 2) := hasSum_sq_mFourierCoeff θ
  have hu₁_parseval : HasSum (fun n ↦ ‖mFourierCoeff u₁ n‖ ^ 2)
      (∫ t, ‖u₁ t‖ ^ 2) := hasSum_sq_mFourierCoeff u₁
  have hu₂_parseval : HasSum (fun n ↦ ‖mFourierCoeff u₂ n‖ ^ 2)
      (∫ t, ‖u₂ t‖ ^ 2) := hasSum_sq_mFourierCoeff u₂
  -- Per-mode: ‖û₁(n)‖² + ‖û₂(n)‖² = ‖θ̂(n)‖².
  have hpt : ∀ n, ‖mFourierCoeff u₁ n‖ ^ 2 + ‖mFourierCoeff u₂ n‖ ^ 2
                = ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · -- At `n = 0` every term is 0 since θ̂(0) = 0.
      rw [hu₁ n, hu₂ n, hn, hθ_mean]
      simp
    · -- Off zero, this is the symbol isometry.
      rw [hu₁ n, hu₂ n]
      exact sqg_velocity_symbol_isometry hn (mFourierCoeff θ n)
  have hsum_add := hu₁_parseval.add hu₂_parseval
  have heq : (fun n ↦ ‖mFourierCoeff u₁ n‖ ^ 2 + ‖mFourierCoeff u₂ n‖ ^ 2)
           = (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2) :=
    funext hpt
  rw [heq] at hsum_add
  exact hsum_add.unique hθ_parseval

/-! ### Parseval energy identities for Fourier multipliers -/

/-- **Parseval-side multiplier identity.** If `ĝ = m·f̂` on the Fourier
side, then `∫ ‖g‖² = Σₙ ‖m(n)‖² · ‖f̂(n)‖²`. -/
theorem hasSum_sq_multiplier
    {d : Type*} [Fintype d]
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n) :
    HasSum (fun n ↦ ‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2) (∫ t, ‖g t‖ ^ 2) := by
  have hg_parseval : HasSum (fun n ↦ ‖mFourierCoeff g n‖ ^ 2)
      (∫ t, ‖g t‖ ^ 2) := hasSum_sq_mFourierCoeff g
  have heq : (fun n ↦ ‖mFourierCoeff g n‖ ^ 2)
           = (fun n ↦ ‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by
    funext n
    rw [hcoeff n, norm_mul, mul_pow]
  rw [heq] at hg_parseval
  exact hg_parseval

/-- Integrated form of the multiplier Parseval identity. -/
theorem L2_norm_sq_eq_multiplier_tsum
    {d : Type*} [Fintype d]
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n) :
    (∫ t, ‖g t‖ ^ 2) = ∑' n, ‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
  (hasSum_sq_multiplier f g m hcoeff).tsum_eq.symm

/-! ### Multiplier composition and Ḣˢ seminorm -/

/-- **Composition of Fourier multipliers.** If `ĝ = m₁·f̂` and `ĥ = m₂·ĝ`
on the Fourier side, then `ĥ = (m₂·m₁)·f̂`. -/
theorem mFourierCoeff_multiplier_comp
    {d : Type*} [Fintype d]
    (f g h : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m₁ m₂ : (d → ℤ) → ℂ)
    (hg : ∀ n, mFourierCoeff g n = m₁ n * mFourierCoeff f n)
    (hh : ∀ n, mFourierCoeff h n = m₂ n * mFourierCoeff g n) :
    ∀ n, mFourierCoeff h n = (m₂ n * m₁ n) * mFourierCoeff f n := by
  intro n
  rw [hh n, hg n, ← mul_assoc]

/-- **Ḣˢ seminorm squared** on `L²(𝕋ᵈ)` via the Fourier multiplier
`σ_s(n) = ‖n‖ˢ`. The zero mode `n = 0` contributes `0`, so this is a
true seminorm (vanishing on constants). -/
noncomputable def hsSeminormSq
    {d : Type*} [Fintype d] (s : ℝ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : ℝ :=
  ∑' n, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2

/-- Fourier-multiplier identification of `(-Δ)^{s/2}`: if `ĝ = σ_s·f̂`
then `∫ ‖g‖² = ‖f‖²_{Ḣˢ}`. -/
theorem hsSeminormSq_eq_L2_of_multiplier
    {d : Type*} [Fintype d] (s : ℝ)
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ n, mFourierCoeff g n
        = ((fracDerivSymbol s n : ℝ) : ℂ) * mFourierCoeff f n) :
    (∫ t, ‖g t‖ ^ 2) = hsSeminormSq s f := by
  unfold hsSeminormSq
  have hsum := hasSum_sq_multiplier f g
      (fun n ↦ ((fracDerivSymbol s n : ℝ) : ℂ)) hcoeff
  have hnorm : ∀ n : (d → ℤ),
      ‖((fracDerivSymbol s n : ℝ) : ℂ)‖ = fracDerivSymbol s n := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fracDerivSymbol_nonneg s n)]
  have heq : (fun n ↦ ‖((fracDerivSymbol s n : ℝ) : ℂ)‖ ^ 2
                   * ‖mFourierCoeff f n‖ ^ 2)
           = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by
    funext n; rw [hnorm n]
  rw [heq] at hsum
  exact hsum.tsum_eq.symm

/-! ### Gradient L²-norm equals the Ḣ¹ seminorm -/

/-- **Plancherel for the gradient.** If `θ ∈ L²(𝕋ᵈ)` and functions
`dθ j ∈ L²(𝕋ᵈ)` represent its partial derivatives with Fourier
coefficients `(dθ j).̂(n) = (i·n_j)·θ̂(n)` (i.e. they are the images of `θ`
under the Fourier multiplier `derivSymbol j`), then the sum of their
L²-norms squared equals the Ḣ¹-seminorm squared of `θ`:

    Σⱼ ∫ ‖dθ j‖² = Σₙ ‖n‖² · ‖θ̂(n)‖² = hsSeminormSq 1 θ. -/
theorem gradient_L2_eq_hsSeminormSq_one
    {d : Type*} [Fintype d]
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (dθ : d → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ j n, mFourierCoeff (dθ j) n = derivSymbol j n * mFourierCoeff θ n) :
    ∑ j, (∫ t, ‖(dθ j) t‖ ^ 2) = hsSeminormSq 1 θ := by
  -- Per-component Parseval identity using the derivative multiplier.
  have hper : ∀ j, HasSum
      (fun n ↦ ‖derivSymbol j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
      (∫ t, ‖(dθ j) t‖ ^ 2) := by
    intro j
    exact hasSum_sq_multiplier θ (dθ j) (derivSymbol j) (hcoeff j)
  -- Sum the finitely many per-component HasSums into one HasSum.
  have hsum :
      HasSum (fun n ↦ ∑ j, ‖derivSymbol j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
        (∑ j, (∫ t, ‖(dθ j) t‖ ^ 2)) := hasSum_sum (fun j _ => hper j)
  -- Collapse the inner sum via `sum_norm_derivSymbol_sq`.
  have hfun : (fun n ↦ ∑ j, ‖derivSymbol j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
            = (fun n ↦ (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
    funext n
    rw [← Finset.sum_mul, sum_norm_derivSymbol_sq]
  rw [hfun] at hsum
  -- Identify `‖n‖² = (fracDerivSymbol 1 n)²` so the tsum matches `hsSeminormSq 1`.
  have hfrac : (fun n : (d → ℤ) ↦ (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
             = (fun n ↦ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
    funext n
    by_cases hn : n = 0
    · simp [hn, latticeNorm, fracDerivSymbol]
    · rw [fracDerivSymbol_one_eq hn]
  rw [hfrac] at hsum
  unfold hsSeminormSq
  exact hsum.tsum_eq.symm

/-! ### SQG selection rule in Ḣ¹ form -/

/-- **SQG selection rule, Ḣ¹ form.** If `‖ŵ(n)‖ ≤ ‖n‖·‖θ̂(n)‖` pointwise
and the RHS is summable, then `‖w‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}`. Equivalently,
`‖S_nt - ω/2‖_{L²(𝕋²)} ≤ ‖∇θ‖_{L²(𝕋²)}` after identifying the gradient
norm via Parseval. -/
theorem sqg_selection_rule_Hs1
    {d : Type*} [Fintype d]
    (θ w : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hbound : ∀ n, ‖mFourierCoeff w n‖ ≤ (fracDerivSymbol 1 n) * ‖mFourierCoeff θ n‖)
    (hsum : Summable (fun n ↦ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    (∫ t, ‖w t‖ ^ 2) ≤ hsSeminormSq 1 θ := by
  unfold hsSeminormSq
  exact sqg_L2_torus_bound θ w (fun n ↦ fracDerivSymbol 1 n)
    (fun n ↦ fracDerivSymbol_nonneg 1 n) hbound hsum

end SqgIdentity
