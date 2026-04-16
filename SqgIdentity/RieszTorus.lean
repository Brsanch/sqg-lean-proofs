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

/-- **Integer-lattice lower bound.** Every nonzero integer lattice point
has Euclidean norm at least `1`, because the sum of squares of integers
not all zero is at least `1`. -/
lemma latticeNorm_ge_one_of_ne_zero {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) : 1 ≤ latticeNorm n := by
  -- Pick `j` with `n j ≠ 0`, then `(n j : ℝ)² ≥ 1` from integrality,
  -- and `Σ_i (n_i : ℝ)² ≥ (n j : ℝ)² ≥ 1`.
  have hexj : ∃ j, n j ≠ 0 := by
    by_contra habs
    exact hn (funext fun j => not_not.mp (fun hnot => habs ⟨j, hnot⟩))
  obtain ⟨j, hj⟩ := hexj
  have hsq_ge_one : (1 : ℝ) ≤ (n j : ℝ) ^ 2 := by
    have hnz : (n j : ℝ) ≠ 0 := by exact_mod_cast hj
    have habs : (1 : ℝ) ≤ |(n j : ℝ)| := by
      have hZ : (1 : ℤ) ≤ |n j| := Int.one_le_abs hj
      have : ((1 : ℤ) : ℝ) ≤ ((|n j| : ℤ) : ℝ) := by exact_mod_cast hZ
      simpa [Int.cast_abs] using this
    have h0 : 0 ≤ |(n j : ℝ)| := abs_nonneg _
    nlinarith [habs, h0, sq_abs (n j : ℝ)]
  have hle : (1 : ℝ) ≤ (latticeNorm n) ^ 2 := by
    calc (1 : ℝ) ≤ (n j : ℝ) ^ 2 := hsq_ge_one
      _ ≤ (latticeNorm n) ^ 2 := sq_le_latticeNorm_sq n j
  have hLpos : 0 ≤ latticeNorm n := latticeNorm_nonneg n
  nlinarith [hle, hLpos, sq_nonneg (latticeNorm n - 1), sq_nonneg (latticeNorm n + 1)]

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

/-! ### Riesz-transform total-energy identity on `𝕋ᵈ` -/

/-- **Sum-of-Riesz L²-isometry on `𝕋ᵈ`.** If `f ∈ L²(𝕋ᵈ)` has zero mean
and `(R_j f) ∈ L²(𝕋ᵈ)` are functions whose Fourier coefficients are
given by the Riesz multiplier, then

    Σⱼ ‖R_j f‖²_{L²(𝕋ᵈ)} = ‖f‖²_{L²(𝕋ᵈ)}.

This is the `d`-dimensional generalisation of `sqg_velocity_L2_isometry`
and expresses the fact that the vector Riesz transform `(R₁, …, R_d)`
is an L²-isometry on zero-mean data. -/
theorem riesz_sum_L2_isometry
    {d : Type*} [Fintype d]
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (Rj_f : d → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hf_mean : mFourierCoeff f 0 = 0)
    (hcoeff : ∀ j n, mFourierCoeff (Rj_f j) n
                     = rieszSymbol j n * mFourierCoeff f n) :
    ∑ j, (∫ t, ‖(Rj_f j) t‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  have hper : ∀ j, HasSum
      (fun n ↦ ‖rieszSymbol j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
      (∫ t, ‖(Rj_f j) t‖ ^ 2) := by
    intro j
    exact hasSum_sq_multiplier f (Rj_f j) (rieszSymbol j) (hcoeff j)
  have hsum :
      HasSum (fun n ↦ ∑ j, ‖rieszSymbol j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
        (∑ j, (∫ t, ‖(Rj_f j) t‖ ^ 2)) := hasSum_sum (fun j _ => hper j)
  have hfun : (fun n : (d → ℤ) ↦
                  ∑ j, ‖rieszSymbol j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
            = (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) := by
    funext n
    rw [← Finset.sum_mul]
    by_cases hn : n = 0
    · simp [hn, hf_mean]
    · rw [rieszSymbol_sum_sq hn, one_mul]
  rw [hfun] at hsum
  have hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2) := hasSum_sq_mFourierCoeff f
  exact hsum.unique hf_parseval

/-! ### Double-Riesz Fourier identity `Σⱼ R_j² = -I` -/

/-- **Double-Riesz Fourier identity.** At the Fourier-coefficient level,
if each `g_j ∈ L²(𝕋ᵈ)` is built from `f ∈ L²(𝕋ᵈ)` by the double Riesz
symbol `ĝ_j(n) = (m_j(n))²·f̂(n)` and `f` has zero mean, then

    `Σⱼ ĝ_j(n) = -f̂(n)` for every `n`.

This is the Fourier-side statement of the classical L² identity
`Σⱼ R_j² = -I` on zero-mean fields. At `n = 0` the zero-mean hypothesis
collapses both sides to zero; off zero the result follows from
`rieszSymbol_sum_sq_complex` (`Σⱼ (m_j(n))² = -1`). -/
theorem riesz_double_sum_symbol
    {d : Type*} [Fintype d]
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (g : d → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ j n, mFourierCoeff (g j) n
                      = (rieszSymbol j n) ^ 2 * mFourierCoeff f n)
    (hf_mean : mFourierCoeff f 0 = 0) :
    ∀ n, (∑ j, mFourierCoeff (g j) n) = -mFourierCoeff f n := by
  intro n
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset d)) => hcoeff j n),
      ← Finset.sum_mul]
  by_cases hn : n = 0
  · rw [hn, hf_mean]; simp
  · rw [rieszSymbol_sum_sq_complex hn]; ring

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

/-! ### Gradient Ḣˢ-norm equals the Ḣ^{s+1} seminorm -/

/-- **Index shift for `fracDerivSymbol`.** For every `n` and every `s`,

    `(σ_{s+1}(n))² = (σ_s(n))² · ‖n‖²`.

At `n = 0` both sides vanish; off zero this is `Real.rpow_add_one`. -/
lemma fracDerivSymbol_add_one_sq {d : Type*} [Fintype d]
    (s : ℝ) (n : d → ℤ) :
    (fracDerivSymbol (s + 1) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
  · have hpos : 0 < latticeNorm n := latticeNorm_pos hn
    rw [fracDerivSymbol_of_ne_zero _ hn, fracDerivSymbol_of_ne_zero _ hn,
        Real.rpow_add_one (ne_of_gt hpos) s]
    ring

/-- **Plancherel for the gradient in Ḣˢ.** If `θ ∈ L²(𝕋ᵈ)` and functions
`dθ j ∈ L²(𝕋ᵈ)` represent its partial derivatives at the symbol level,
then summing their Ḣˢ-seminorms-squared recovers the Ḣ^{s+1}-seminorm
of `θ`:

    `Σⱼ ‖∂ⱼθ‖²_{Ḣˢ} = ‖θ‖²_{Ḣ^{s+1}}`.

At `s = 0` this specialises to `gradient_L2_eq_hsSeminormSq_one`. -/
theorem gradient_Hs_eq_hsSeminormSq_add_one
    {d : Type*} [Fintype d] (s : ℝ)
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (dθ : d → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ j n, mFourierCoeff (dθ j) n = derivSymbol j n * mFourierCoeff θ n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    ∑ j, hsSeminormSq s (dθ j) = hsSeminormSq (s + 1) θ := by
  -- Per-component pointwise identity: σ_s(n)² · ‖d̂θ_j(n)‖²
  -- = σ_s(n)² · |derivSymbol j n|² · ‖θ̂(n)‖²  (absorb the derivative symbol).
  have hmode : ∀ j n,
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2
      = (fracDerivSymbol s n) ^ 2
          * ((n j : ℝ) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
    intro j n
    rw [hcoeff j n, norm_mul, mul_pow, norm_derivSymbol_sq]
  -- Per-component Ḣˢ summability follows from the Ḣ^{s+1} summability on θ
  -- because |n_j|² ≤ ‖n‖² and σ_{s+1}(n)² = σ_s(n)² · ‖n‖² (the index shift).
  have hsumj : ∀ j, Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2) := by
    intro j
    refine hsumm.of_nonneg_of_le
      (fun n => by rw [hmode j n];
                   exact mul_nonneg (sq_nonneg _)
                     (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun n => ?_)
    rw [hmode j n, fracDerivSymbol_add_one_sq s n]
    have hθsq : 0 ≤ ‖mFourierCoeff θ n‖ ^ 2 := sq_nonneg _
    have hσs : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
    have hnj : (n j : ℝ) ^ 2 ≤ (latticeNorm n) ^ 2 :=
      sq_le_latticeNorm_sq n j
    calc (fracDerivSymbol s n) ^ 2 * ((n j : ℝ) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
        = ((fracDerivSymbol s n) ^ 2 * (n j : ℝ) ^ 2)
            * ‖mFourierCoeff θ n‖ ^ 2 := by ring
      _ ≤ ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2)
            * ‖mFourierCoeff θ n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnj hσs) hθsq
  -- Per-component HasSum against hsSeminormSq s (dθ j).
  have hper : ∀ j, HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2)
      (hsSeminormSq s (dθ j)) := by
    intro j; unfold hsSeminormSq; exact (hsumj j).hasSum
  -- Combine the finite family of per-component HasSums.
  have hsum_all : HasSum
      (fun n ↦ ∑ j,
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2)
      (∑ j, hsSeminormSq s (dθ j)) := hasSum_sum (fun j _ => hper j)
  -- Pointwise Pythagoras: Σⱼ σ_s² · ‖d̂θ_j‖² = σ_s² · ‖n‖² · ‖θ̂‖² = σ_{s+1}² · ‖θ̂‖².
  have hpt : ∀ n,
        (∑ j, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2)
      = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    have hrewrite : (∑ j,
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2)
        = (fracDerivSymbol s n) ^ 2
            * ((∑ j, (n j : ℝ) ^ 2) * ‖mFourierCoeff θ n‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun j _ => hmode j n),
          ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hrewrite, ← latticeNorm_sq, fracDerivSymbol_add_one_sq]
    ring
  -- Substitute pointwise identity into the combined HasSum and match RHS.
  have heq : (fun n ↦ ∑ j,
                  (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (dθ j) n‖ ^ 2)
           = (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2
                        * ‖mFourierCoeff θ n‖ ^ 2) := funext hpt
  rw [heq] at hsum_all
  have hrhs : HasSum
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
      (hsSeminormSq (s + 1) θ) := by
    unfold hsSeminormSq; exact hsumm.hasSum
  exact hsum_all.unique hrhs

/-! ### Ḣˢ-contractivity of a single Riesz transform -/

/-- **Ḣˢ-contractivity of the Riesz transform.** If `R_j f` has the
Riesz-multiplier Fourier coefficients of `f` and the Ḣˢ series of `f`
is summable, then `‖R_j f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣˢ}`. -/
theorem riesz_Hs_contractive
    {d : Type*} [Fintype d] (s : ℝ) (j : d)
    (f Rj_f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ n, mFourierCoeff Rj_f n = rieszSymbol j n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s Rj_f ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  -- Per-mode: ‖(R_j f)̂(n)‖² = ‖m_j(n)‖² · ‖f̂(n)‖² ≤ ‖f̂(n)‖².
  have hmode : ∀ n, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff Rj_f n‖ ^ 2
                  ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    rw [hcoeff n, norm_mul, mul_pow]
    have hm1 : ‖rieszSymbol j n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖rieszSymbol j n‖ := norm_nonneg _
      nlinarith [rieszSymbol_norm_le_one j n, h0]
    have hrest : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (fracDerivSymbol s n) ^ 2
            * (‖rieszSymbol j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
        = ‖rieszSymbol j n‖ ^ 2
            * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by ring
      _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hrest
      _ = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  -- Summability of the R_j f side from pointwise bound.
  have hsumm_Rj : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff Rj_f n‖ ^ 2) := by
    refine hsumm.of_nonneg_of_le (fun n => ?_) hmode
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact Summable.tsum_le_tsum hmode hsumm_Rj hsumm

/-! ### Generic unitary vector-multiplier Ḣˢ-isometry -/

/-- **Unitary vector-multiplier Ḣˢ-isometry.** Abstract kernel of
`riesz_sum_Hs_isometry` and `sqg_velocity_Hs_isometry`: if `u_j ∈ L²(𝕋ᵈ)`
are built from `f ∈ L²(𝕋ᵈ)` by a family of Fourier multipliers `m_j`
that is pointwise unitary in `j` off the zero mode,

    `Σⱼ ‖m_j(n)‖² = 1` for `n ≠ 0`,

each `m_j` is bounded (`‖m_j(n)‖ ≤ 1`), and `f̂(0) = 0`, then under
Ḣˢ-summability of `f`,

    `Σⱼ ‖u_j‖²_{Ḣˢ} = ‖f‖²_{Ḣˢ}`.

The proof bundles per-component HasSums against `hsSeminormSq` and
closes the combined HasSum via `hasSum.unique`, pulling the unitarity
identity through the pointwise product `σ_s(n)² · (Σⱼ ‖m_j(n)‖²) · ‖f̂(n)‖²`. -/
theorem unitary_vec_mul_Hs_isometry
    {d ι : Type*} [Fintype d] [Fintype ι] (s : ℝ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (u : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : ι → (d → ℤ) → ℂ)
    (hcoeff : ∀ j n, mFourierCoeff (u j) n = m j n * mFourierCoeff f n)
    (hbound : ∀ j n, ‖m j n‖ ≤ 1)
    (hunit : ∀ {n : d → ℤ}, n ≠ 0 → ∑ j, ‖m j n‖ ^ 2 = 1)
    (hf_mean : mFourierCoeff f 0 = 0)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    ∑ j, hsSeminormSq s (u j) = hsSeminormSq s f := by
  -- Per-component Ḣˢ summability from the ‖m_j(n)‖ ≤ 1 bound.
  have hsumj : ∀ j, Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2) := by
    intro j
    refine hsumm.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fun n => ?_)
    rw [hcoeff j n, norm_mul, mul_pow]
    have hm1 : ‖m j n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖m j n‖ := norm_nonneg _
      nlinarith [hbound j n, h0]
    have hrest : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (fracDerivSymbol s n) ^ 2
            * (‖m j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
        = ‖m j n‖ ^ 2
            * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by ring
      _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hrest
      _ = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  -- Per-component HasSum against hsSeminormSq s (u j).
  have hper : ∀ j, HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2)
      (hsSeminormSq s (u j)) := by
    intro j; unfold hsSeminormSq; exact (hsumj j).hasSum
  -- Combine finitely many per-component HasSums.
  have hsum_all : HasSum
      (fun n ↦ ∑ j,
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2)
      (∑ j, hsSeminormSq s (u j)) := hasSum_sum (fun j _ => hper j)
  -- Pointwise identity: Σⱼ σ²·‖m_j·f̂‖² = σ²·‖f̂‖², by unitarity (off 0) or trivially (at 0).
  have hpt : ∀ n,
        (∑ j, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2)
      = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    have hmode : ∀ j,
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2
        = ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
            * ‖m j n‖ ^ 2 := by
      intro j; rw [hcoeff j n, norm_mul, mul_pow]; ring
    rw [Finset.sum_congr rfl (fun j _ => hmode j), ← Finset.mul_sum]
    by_cases hn : n = 0
    · simp [hn, hf_mean]
    · rw [hunit hn, mul_one]
  -- Substitute and conclude via HasSum.unique.
  have heq : (fun n ↦ ∑ j,
                  (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (u j) n‖ ^ 2)
           = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
    funext hpt
  rw [heq] at hsum_all
  have hrhs : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
      (hsSeminormSq s f) := by
    unfold hsSeminormSq; exact hsumm.hasSum
  exact hsum_all.unique hrhs

/-! ### Ḣˢ-isometry of the vector Riesz transform -/

/-- **Vector Riesz transform is an Ḣˢ-isometry.** If `(R_j f) ∈ L²(𝕋ᵈ)`
have the Riesz-multiplier Fourier coefficients of `f` and the Ḣˢ series
of `f` is summable, then the sum of the Ḣˢ-seminorms-squared of the
components equals that of `f`:

    Σⱼ ‖R_j f‖²_{Ḣˢ} = ‖f‖²_{Ḣˢ}. -/
theorem riesz_sum_Hs_isometry
    {d : Type*} [Fintype d] (s : ℝ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (Rj_f : d → Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hcoeff : ∀ j n, mFourierCoeff (Rj_f j) n
                     = rieszSymbol j n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    ∑ j, hsSeminormSq s (Rj_f j) = hsSeminormSq s f := by
  -- Per-component summability from the single-Riesz bound.
  have hsumj : ∀ j, Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2) := by
    intro j
    refine hsumm.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun n => ?_)
    rw [hcoeff j n, norm_mul, mul_pow]
    have hm1 : ‖rieszSymbol j n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖rieszSymbol j n‖ := norm_nonneg _
      nlinarith [rieszSymbol_norm_le_one j n, h0]
    have hrest : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (fracDerivSymbol s n) ^ 2
            * (‖rieszSymbol j n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
        = ‖rieszSymbol j n‖ ^ 2
            * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by ring
      _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hrest
      _ = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  -- Per-component HasSum bundle.
  have hper : ∀ j, HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2)
      (hsSeminormSq s (Rj_f j)) := by
    intro j
    unfold hsSeminormSq
    exact (hsumj j).hasSum
  -- Finite sum of per-component HasSums.
  have hsum_all : HasSum
      (fun n ↦ ∑ j,
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2)
      (∑ j, hsSeminormSq s (Rj_f j)) := hasSum_sum (fun j _ => hper j)
  -- Pointwise Pythagorean identity: Σⱼ σ²·‖m_j·f̂‖² = σ²·‖f̂‖².
  have hpt : ∀ n,
      (∑ j, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2)
        = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    have hmode : ∀ j, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2
               = ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
                   * ‖rieszSymbol j n‖ ^ 2 := by
      intro j
      rw [hcoeff j n, norm_mul, mul_pow]; ring
    rw [Finset.sum_congr rfl (fun j _ => hmode j), ← Finset.mul_sum]
    by_cases hn : n = 0
    · simp [hn]
    · rw [rieszSymbol_sum_sq hn, mul_one]
  -- Substitute the pointwise identity into the combined HasSum.
  have heq : (fun n ↦ ∑ j,
                  (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (Rj_f j) n‖ ^ 2)
           = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
    funext hpt
  rw [heq] at hsum_all
  -- RHS as a HasSum and uniqueness.
  have hrhs : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
      (hsSeminormSq s f) := by
    unfold hsSeminormSq; exact hsumm.hasSum
  exact hsum_all.unique hrhs

/-! ### SQG velocity Ḣˢ-isometry on `𝕋²` -/

/-- **SQG velocity is an Ḣˢ-isometry on `𝕋²`.** If `θ : L²(𝕋²)` has zero
mean and `u₁, u₂ : L²(𝕋²)` are the components of the SQG velocity at the
Fourier-symbol level,

    `û₁(n) = rieszSymbol 1 n · θ̂(n)`,
    `û₂(n) = -rieszSymbol 0 n · θ̂(n)`,

and the Ḣˢ series of `θ` is summable, then

    `‖u₁‖²_{Ḣˢ} + ‖u₂‖²_{Ḣˢ} = ‖θ‖²_{Ḣˢ}`.

This is the Ḣˢ upgrade of `sqg_velocity_L2_isometry` and expresses that
SQG energy is conserved at every regularity level, because the velocity
is obtained from `θ` by a unitary symbol. -/
theorem sqg_velocity_Hs_isometry
    (s : ℝ)
    (θ u₁ u₂ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ_mean : mFourierCoeff θ 0 = 0)
    (hu₁ : ∀ n, mFourierCoeff u₁ n = rieszSymbol 1 n * mFourierCoeff θ n)
    (hu₂ : ∀ n, mFourierCoeff u₂ n = -rieszSymbol 0 n * mFourierCoeff θ n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u₁ + hsSeminormSq s u₂ = hsSeminormSq s θ := by
  -- Bounded-multiplier Ḣˢ summability helper.
  have hbound_summ : ∀ (m : (Fin 2 → ℤ) → ℂ) (hB : ∀ n, ‖m n‖ ≤ 1)
      (g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
      (hg : ∀ n, mFourierCoeff g n = m n * mFourierCoeff θ n),
      Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff g n‖ ^ 2) := by
    intro m hB g hg
    refine hsumm.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fun n => ?_)
    rw [hg n, norm_mul, mul_pow]
    have hm1 : ‖m n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖m n‖ := norm_nonneg _
      nlinarith [hB n, h0]
    have hrest : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (fracDerivSymbol s n) ^ 2
            * (‖m n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
        = ‖m n‖ ^ 2
            * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by ring
      _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hrest
      _ = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := one_mul _
  -- Per-component summability from the symbol bound ‖rieszSymbol‖ ≤ 1.
  have hsumm₁ : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₁ n‖ ^ 2) :=
    hbound_summ (rieszSymbol 1) (rieszSymbol_norm_le_one 1) u₁ hu₁
  have hsumm₂ : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₂ n‖ ^ 2) := by
    refine hbound_summ (fun n ↦ -rieszSymbol 0 n) ?_ u₂ hu₂
    intro n; rw [norm_neg]; exact rieszSymbol_norm_le_one 0 n
  -- Per-component and reference HasSums against hsSeminormSq.
  have hu₁_hasSum : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₁ n‖ ^ 2)
      (hsSeminormSq s u₁) := by
    unfold hsSeminormSq; exact hsumm₁.hasSum
  have hu₂_hasSum : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₂ n‖ ^ 2)
      (hsSeminormSq s u₂) := by
    unfold hsSeminormSq; exact hsumm₂.hasSum
  have hθ_hasSum : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
      (hsSeminormSq s θ) := by
    unfold hsSeminormSq; exact hsumm.hasSum
  -- Pointwise Pythagorean identity per mode.
  have hpt : ∀ n,
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₁ n‖ ^ 2
      + (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₂ n‖ ^ 2
      = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · -- At n = 0, θ̂(0) = 0 forces all three terms to 0.
      rw [hu₁ n, hu₂ n, hn, hθ_mean]
      simp
    · -- Off zero, multiply the symbol isometry by σ_s(n)².
      have hiso := sqg_velocity_symbol_isometry hn (mFourierCoeff θ n)
      rw [hu₁ n, hu₂ n]
      linear_combination (fracDerivSymbol s n) ^ 2 * hiso
  -- Combine the two per-component HasSums.
  have hsum_add := hu₁_hasSum.add hu₂_hasSum
  have heq : (fun n ↦
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₁ n‖ ^ 2
      + (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u₂ n‖ ^ 2)
           = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
    funext hpt
  rw [heq] at hsum_add
  exact hsum_add.unique hθ_hasSum

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

/-! ### Multiplicative splitting of the `fracDerivSymbol` -/

/-- **Additive-in-exponent splitting of the fractional derivative symbol.**
For every `n` and every `s, t`,

    `(σ_{s+t}(n))² = (σ_s(n))² · (σ_t(n))²`.

At `n = 0` both sides vanish; off zero this is `Real.rpow_add`. -/
lemma fracDerivSymbol_add_sq {d : Type*} [Fintype d]
    (s t : ℝ) (n : d → ℤ) :
    (fracDerivSymbol (s + t) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol t n) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
  · have hpos : 0 < latticeNorm n := latticeNorm_pos hn
    rw [fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn,
        Real.rpow_add hpos s t]
    ring

/-- **Multiplicative additivity of `fracDerivSymbol` (unsquared).**
For every `n` and every `s, t`,

    `σ_{s+t}(n) = σ_s(n) · σ_t(n)`.

At `n = 0` both sides are `0`; off zero this is `Real.rpow_add`. -/
lemma fracDerivSymbol_mul {d : Type*} [Fintype d]
    (s t : ℝ) (n : d → ℤ) :
    fracDerivSymbol (s + t) n = fracDerivSymbol s n * fracDerivSymbol t n := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
  · have hpos : 0 < latticeNorm n := latticeNorm_pos hn
    rw [fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn,
        Real.rpow_add hpos s t]

/-! ### Monotonicity of `fracDerivSymbol` and `hsSeminormSq` in `s` -/

/-- **Monotonicity of `fracDerivSymbol` in the exponent.** On the integer
lattice, for every `n`, if `s ≤ t` then `σ_s(n) ≤ σ_t(n)`. At `n = 0`
both sides are `0`; off zero `‖n‖ ≥ 1` (integer-lattice fact) makes
`‖n‖^s ≤ ‖n‖^t`. -/
lemma fracDerivSymbol_mono_of_le {d : Type*} [Fintype d]
    {s t : ℝ} (hst : s ≤ t) (n : d → ℤ) :
    fracDerivSymbol s n ≤ fracDerivSymbol t n := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
  · rw [fracDerivSymbol_of_ne_zero _ hn, fracDerivSymbol_of_ne_zero _ hn]
    exact Real.rpow_le_rpow_of_exponent_le
      (latticeNorm_ge_one_of_ne_zero hn) hst

/-- **Squared monotonicity of `fracDerivSymbol`.** Convenience form of
`fracDerivSymbol_mono_of_le`, kept in the squared shape used inside
`hsSeminormSq`. -/
lemma fracDerivSymbol_sq_mono_of_le {d : Type*} [Fintype d]
    {s t : ℝ} (hst : s ≤ t) (n : d → ℤ) :
    (fracDerivSymbol s n) ^ 2 ≤ (fracDerivSymbol t n) ^ 2 := by
  have h := fracDerivSymbol_mono_of_le hst n
  have h0 : 0 ≤ fracDerivSymbol s n := fracDerivSymbol_nonneg s n
  nlinarith [h, h0]

/-- **Monotonicity of the Ḣˢ seminorm in `s`.** On the torus, the
Ḣˢ-seminorm is monotone in `s`: if `s ≤ t` and the Ḣᵗ tail of `f` is
summable, then

    `‖f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣᵗ}`.

Monotonicity comes from `‖n‖ ≥ 1` off zero, which gives
`σ_s(n)² ≤ σ_t(n)²` at every nonzero lattice point. -/
theorem hsSeminormSq_mono_of_le
    {d : Type*} [Fintype d]
    {s t : ℝ} (hst : s ≤ t)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hsumm_t : Summable
        (fun n ↦ (fracDerivSymbol t n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s f ≤ hsSeminormSq t f := by
  unfold hsSeminormSq
  -- Per-mode: σ_s(n)² · ‖f̂(n)‖² ≤ σ_t(n)² · ‖f̂(n)‖² since σ_s² ≤ σ_t² and ‖f̂‖² ≥ 0.
  have hmode : ∀ n, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2
                  ≤ (fracDerivSymbol t n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
    fun n => mul_le_mul_of_nonneg_right
      (fracDerivSymbol_sq_mono_of_le hst n) (sq_nonneg _)
  have hsumm_s : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by
    refine hsumm_t.of_nonneg_of_le (fun n => ?_) hmode
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact Summable.tsum_le_tsum hmode hsumm_s hsumm_t

/-- **Nonnegativity of the Ḣˢ squared seminorm.**
Each summand `σ_s(n)² · ‖f̂(n)‖²` is nonneg, so the tsum is nonneg
(or 0 when not summable, by `tsum_eq_zero_of_not_summable`). -/
theorem hsSeminormSq_nonneg {d : Type*} [Fintype d] (s : ℝ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    0 ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  exact tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-! ### Riesz product symbol -/

/-- **Product of Riesz symbols.** For `n ≠ 0`,

    `R̂_j(n) · R̂_k(n) = - (n_j · n_k) / ‖n‖²`.

This is the Fourier symbol of the composition `R_j ∘ R_k`; summing over
`j = k` recovers `riesz_double_sum_symbol` (= −1). The off-diagonal
entries are the building blocks of the **Leray projector**
`P̂_{jk} = δ_{jk} - n̂_j n̂_k = δ_{jk} + R̂_j R̂_k`. -/
theorem riesz_product_symbol {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) (j k : d) :
    rieszSymbol j n * rieszSymbol k n
      = -(↑(n j : ℤ) * ↑(n k : ℤ)) / (↑(latticeNorm n) ^ 2 : ℂ) := by
  rw [rieszSymbol_of_ne_zero hn j, rieszSymbol_of_ne_zero hn k]
  have hL : (↑(latticeNorm n) : ℂ) ≠ 0 := by
    have := latticeNorm_pos hn
    exact_mod_cast this.ne'
  field_simp
  rw [show (I : ℂ) ^ 2 = -1 from Complex.I_sq]
  push_cast
  ring

/-! ### Leray–Helmholtz projector symbol -/

/-- **Leray–Helmholtz projector symbol.** On the integer lattice
`ℤᵈ \ {0}`, define

    `P̂_{jk}(n) = δ_{jk} + R̂_j(n)·R̂_k(n)
              = δ_{jk} - n_j·n_k / ‖n‖²`.

`P̂` projects Fourier modes onto the divergence-free subspace; it is the
Fourier-side representation of the Leray projector `P = Id + R⊗R`. -/
noncomputable def leraySymbol {d : Type*} [Fintype d] [DecidableEq d]
    (j k : d) (n : d → ℤ) : ℂ :=
  if j = k then 1 + rieszSymbol j n * rieszSymbol k n
  else rieszSymbol j n * rieszSymbol k n

/-- **Leray symbol for `n = 0`.** Every entry is `δ_{jk}` at the
zero frequency (since all Riesz symbols vanish there). -/
lemma leraySymbol_zero {d : Type*} [Fintype d] [DecidableEq d]
    (j k : d) : leraySymbol j k (0 : d → ℤ) = if j = k then 1 else 0 := by
  simp [leraySymbol, rieszSymbol_zero]

/-- **Trace of the Leray symbol.** For `n ≠ 0`,

    `Σⱼ P̂_{jj}(n) = d − 1`.

This counts the number of independent divergence-free polarisations
of a Fourier mode on `𝕋ᵈ`: every nonzero `n` has `d − 1` transverse
directions. The proof uses `rieszSymbol_sum_sq_complex` (Σ R̂_j² = −1). -/
theorem leray_trace {d : Type*} [Fintype d] [DecidableEq d]
    {n : d → ℤ} (hn : n ≠ 0) :
    ∑ j : d, leraySymbol j j n = (Fintype.card d : ℂ) - 1 := by
  simp only [leraySymbol, if_true]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Σ R̂_j · R̂_j = Σ R̂_j² = -1
  have hRR : ∑ j : d, rieszSymbol j n * rieszSymbol j n
           = ∑ j : d, (rieszSymbol j n) ^ 2 := by
    congr 1; ext j; ring
  rw [hRR, rieszSymbol_sum_sq_complex hn]
  simp [Finset.card_univ]
  ring

/-- **Riesz–frequency dot product.** For `n ≠ 0`,

    `Σ_k  R̂_k(n) · n_k = −i · ‖n‖`.

This is the Fourier-side expression of `div(R f) = (-Δ)^{1/2} f`.
Each `R̂_k(n) = -i n_k/‖n‖`, so the sum reduces to
`(-i/‖n‖) Σ_k n_k² = -i · ‖n‖`. -/
theorem riesz_dot_freq {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) :
    ∑ k, rieszSymbol k n * (↑(n k : ℤ) : ℂ)
      = -Complex.I * (↑(latticeNorm n) : ℂ) := by
  have hL : (↑(latticeNorm n) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  -- Multiply both sides by ‖n‖ to clear denominators
  have hmul : (∑ k, rieszSymbol k n * (↑(n k : ℤ) : ℂ)) * (↑(latticeNorm n) : ℂ)
            = (-Complex.I * (↑(latticeNorm n) : ℂ)) * (↑(latticeNorm n) : ℂ) := by
    rw [Finset.sum_mul]
    -- Per-term: R̂_k · n_k · ‖n‖ = -I · n_k²
    have hterm : ∀ k, rieszSymbol k n * (↑(n k : ℤ) : ℂ) * (↑(latticeNorm n) : ℂ)
                    = -Complex.I * ((↑(n k : ℤ) : ℂ) ^ 2) := by
      intro k
      rw [rieszSymbol_of_ne_zero hn k]
      field_simp
      push_cast; ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    -- Σ_k (-I · n_k²) = -I · Σ_k n_k² = -I · ‖n‖²
    rw [← Finset.mul_sum]
    have hsum : ∑ k, ((↑(n k : ℤ) : ℂ) ^ 2) = (↑(latticeNorm n) : ℂ) ^ 2 := by
      have hreal : (∑ k, (n k : ℝ) ^ 2) = latticeNorm n ^ 2 :=
        (latticeNorm_sq n).symm
      exact_mod_cast congrArg (↑· : ℝ → ℂ) hreal
    rw [hsum]; ring
  exact mul_right_cancel₀ hL hmul

/-- **Leray projector annihilates longitudinal modes.** For `n ≠ 0`,

    `Σ_k  P̂_{jk}(n) · n_k = 0`.

This is the defining property of the Helmholtz/Leray projector: it
kills the gradient (irrotational) component of any vector field.
Follows from `riesz_dot_freq` (Σ R̂_k n_k = −i‖n‖) and the Riesz
symbol normalisation. -/
theorem leray_kills_longitudinal {d : Type*} [Fintype d] [DecidableEq d]
    {n : d → ℤ} (hn : n ≠ 0) (j : d) :
    ∑ k, leraySymbol j k n * (↑(n k : ℤ) : ℂ) = 0 := by
  -- Rewrite leraySymbol to δ_{jk} + R̂_j R̂_k and distribute.
  have hexpand : ∀ k, leraySymbol j k n * (↑(n k : ℤ) : ℂ)
      = (if j = k then (↑(n k : ℤ) : ℂ) else 0)
        + rieszSymbol j n * (rieszSymbol k n * (↑(n k : ℤ) : ℂ)) := by
    intro k
    unfold leraySymbol
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
  rw [Finset.sum_add_distrib]
  -- First sum: Σ_k δ_{jk} · n_k = n_j
  have hδ : ∑ k, (if j = k then (↑(n k : ℤ) : ℂ) else 0) = (↑(n j : ℤ) : ℂ) := by
    exact (Finset.sum_ite_eq Finset.univ j _).trans (if_pos (Finset.mem_univ j))
  rw [hδ]
  -- Second sum: R̂_j · Σ_k R̂_k · n_k = R̂_j · (-I · ‖n‖)
  rw [← Finset.mul_sum, riesz_dot_freq hn]
  -- Now: n_j + R̂_j · (-I · ‖n‖) = 0
  rw [rieszSymbol_of_ne_zero hn j]
  have hL : (↑(latticeNorm n) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp
  rw [show (Complex.I : ℂ) ^ 2 = -1 from Complex.I_sq]
  push_cast; ring

/-- **Self-adjointness of the Leray symbol.** `P̂_{jk}(n) = P̂_{kj}(n)`,
since `R̂_j · R̂_k = R̂_k · R̂_j` (complex multiplication commutes). -/
theorem leray_self_adjoint {d : Type*} [Fintype d] [DecidableEq d]
    (j k : d) (n : d → ℤ) :
    leraySymbol j k n = leraySymbol k j n := by
  unfold leraySymbol
  by_cases hjk : j = k
  · rw [hjk]
  · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring

/-- **Idempotency of the Leray projector.** For `n ≠ 0`,

    `Σ_l  P̂_{jl}(n) · P̂_{lk}(n) = P̂_{jk}(n)`.

Proof: expand `P̂ = δ + R̂⊗R̂` to get four sums. The cross terms each give
`R̂_j R̂_k` and the quadruple-product sum gives `R̂_j · (Σ R̂_l²) · R̂_k = -R̂_j R̂_k`.
The three contributions `R̂_j R̂_k + R̂_j R̂_k + (-R̂_j R̂_k) = R̂_j R̂_k`
combine with the `δ_{jk}` term to reproduce `P̂_{jk}`. -/
theorem leray_idempotent {d : Type*} [Fintype d] [DecidableEq d]
    {n : d → ℤ} (hn : n ≠ 0) (j k : d) :
    ∑ l, leraySymbol j l n * leraySymbol l k n = leraySymbol j k n := by
  -- Expand leraySymbol into δ + R̂⊗R̂ form
  have hexpand : ∀ a b, leraySymbol a b n
      = (if a = b then 1 else 0) + rieszSymbol a n * rieszSymbol b n := by
    intro a b; unfold leraySymbol; split_ifs <;> ring
  simp_rw [hexpand]
  -- Distribute the product: (δ_jl + R̂_j R̂_l)(δ_lk + R̂_l R̂_k)
  -- = δ_jl δ_lk + δ_jl R̂_l R̂_k + R̂_j R̂_l δ_lk + R̂_j R̂_l R̂_l R̂_k
  have hdist : ∀ l,
      ((if j = l then (1 : ℂ) else 0) + rieszSymbol j n * rieszSymbol l n)
    * ((if l = k then (1 : ℂ) else 0) + rieszSymbol l n * rieszSymbol k n)
    = (if j = l then 1 else 0) * (if l = k then 1 else 0)
    + (if j = l then 1 else 0) * (rieszSymbol l n * rieszSymbol k n)
    + rieszSymbol j n * rieszSymbol l n * (if l = k then 1 else 0)
    + rieszSymbol j n * (rieszSymbol l n ^ 2) * rieszSymbol k n := by
    intro l; ring
  simp_rw [hdist]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Term 1: Σ_l δ_{jl} δ_{lk} = δ_{jk}
  have h1 : ∑ l, (if j = l then (1 : ℂ) else 0) * (if l = k then 1 else 0)
           = if j = k then 1 else 0 := by
    have : (fun l => (if j = l then (1 : ℂ) else 0) * (if l = k then 1 else 0))
         = (fun l => if j = l then (if l = k then 1 else 0) else 0) := by
      ext l; split_ifs <;> simp
    rw [this, (Finset.sum_ite_eq Finset.univ j _).trans (if_pos (Finset.mem_univ j))]
  -- Term 2: Σ_l δ_{jl} (R̂_l R̂_k) = R̂_j R̂_k
  have h2 : ∑ l, (if j = l then (1 : ℂ) else 0) * (rieszSymbol l n * rieszSymbol k n)
           = rieszSymbol j n * rieszSymbol k n := by
    have : (fun l => (if j = l then (1 : ℂ) else 0) * (rieszSymbol l n * rieszSymbol k n))
         = (fun l => if j = l then rieszSymbol l n * rieszSymbol k n else 0) := by
      ext l; split_ifs <;> simp
    rw [this, (Finset.sum_ite_eq Finset.univ j _).trans (if_pos (Finset.mem_univ j))]
  -- Term 3: Σ_l R̂_j R̂_l δ_{lk} = R̂_j R̂_k
  have h3 : ∑ l, rieszSymbol j n * rieszSymbol l n * (if l = k then (1 : ℂ) else 0)
           = rieszSymbol j n * rieszSymbol k n := by
    have : (fun l => rieszSymbol j n * rieszSymbol l n * (if l = k then (1 : ℂ) else 0))
         = (fun l => if l = k then rieszSymbol j n * rieszSymbol l n else 0) := by
      ext l; split_ifs <;> ring
    rw [this, (Finset.sum_ite_eq' Finset.univ k _).trans (if_pos (Finset.mem_univ k))]
  -- Term 4: Σ_l R̂_j R̂_l² R̂_k = R̂_j (Σ_l R̂_l²) R̂_k = -R̂_j R̂_k
  have h4 : ∑ l, rieszSymbol j n * (rieszSymbol l n ^ 2) * rieszSymbol k n
           = -(rieszSymbol j n * rieszSymbol k n) := by
    rw [show (fun l => rieszSymbol j n * (rieszSymbol l n ^ 2) * rieszSymbol k n)
          = (fun l => rieszSymbol j n * rieszSymbol k n * (rieszSymbol l n ^ 2)) from by
        ext l; ring]
    rw [← Finset.mul_sum, rieszSymbol_sum_sq_complex hn]; ring
  rw [h1, h2, h3, h4]; ring

/-! ### SQG vorticity–potential relation -/

/-- **SQG vorticity symbol.** For the SQG velocity
`û₀ = R̂₁·θ̂, û₁ = -R̂₀·θ̂` on `𝕋²`, the 2D scalar vorticity
`ω = ∂₀u₁ − ∂₁u₀` has Fourier symbol

    `ω̂/θ̂ = −‖n‖`

at every `n ≠ 0`. This is the Fourier-level statement of the SQG
constitutive relation `ω = −(-Δ)^{1/2}θ` (with the sign matching
the velocity convention `u = (R₁θ, -R₀θ)`).

The proof factors through `riesz_dot_freq`
(`Σ R̂_k · n_k = -i‖n‖`). -/
theorem sqg_vorticity_symbol {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    derivSymbol 0 n * (-rieszSymbol 0 n)
      - derivSymbol 1 n * rieszSymbol 1 n
    = -(↑(latticeNorm n) : ℂ) := by
  -- Rewrite: the expression equals -(Σ_j derivSymbol j · rieszSymbol j)
  have hstep : derivSymbol 0 n * (-rieszSymbol 0 n)
                 - derivSymbol 1 n * rieszSymbol 1 n
             = -(∑ j : Fin 2, derivSymbol j n * rieszSymbol j n) := by
    simp [Fin.sum_univ_two]; ring
  rw [hstep]
  -- Each derivSymbol j n = I · (n j : ℂ), so factor out I
  have hfactor : ∑ j : Fin 2, derivSymbol j n * rieszSymbol j n
               = Complex.I * ∑ j : Fin 2, rieszSymbol j n * (↑(n j : ℤ) : ℂ) := by
    simp only [derivSymbol, Fin.sum_univ_two]
    push_cast; ring
  rw [hfactor, riesz_dot_freq hn]
  rw [show -(Complex.I * (-Complex.I * (↑(latticeNorm n) : ℂ)))
        = -(-(Complex.I * Complex.I * (↑(latticeNorm n) : ℂ))) from by ring]
  rw [neg_neg, Complex.I_mul_I, neg_one_mul]

/-! ### Parseval multiplier identity in Ḣˢ form -/

/-- **Ḣˢ-level Parseval for Fourier multipliers.** If `ĝ(n) = m(n)·f̂(n)`
and the Ḣˢ tail of `f` weighted by `‖m(n)‖²` is summable, then

    `HasSum (fun n ↦ σ_s(n)² · ‖m(n)‖² · ‖f̂(n)‖²) ‖g‖²_{Ḣˢ}`.

Lifts `hasSum_sq_multiplier` from the L² integral to the Ḣˢ seminorm. -/
theorem hasSum_sq_multiplier_Hs
    {d : Type*} [Fintype d] (s : ℝ)
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2
                   * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2))) :
    HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2
                 * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2))
      (hsSeminormSq s g) := by
  -- Rewrite the summand to the `g`-shape and apply Ḣˢ HasSum via the
  -- definition of `hsSeminormSq`.
  have hfun : (fun n ↦ (fracDerivSymbol s n) ^ 2
                         * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2))
            = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff g n‖ ^ 2) := by
    funext n
    rw [hcoeff n, norm_mul, mul_pow]
  rw [hfun]
  unfold hsSeminormSq
  rw [hfun] at hsumm
  exact hsumm.hasSum

/-- **Integrated Ḣˢ multiplier Parseval.** Closed-form of the Ḣˢ seminorm
of `g = m·f` as the weighted tsum of `f`-Fourier coefficients. -/
theorem hsSeminormSq_eq_multiplier_tsum
    {d : Type*} [Fintype d] (s : ℝ)
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2
                   * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2))) :
    hsSeminormSq s g
      = ∑' n, (fracDerivSymbol s n) ^ 2
                  * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
  (hasSum_sq_multiplier_Hs s f g m hcoeff hsumm).tsum_eq.symm

/-! ### Ḣˢ-isometry for unit-modulus multipliers -/

/-- **Ḣˢ-isometry for unit-modulus Fourier multipliers.** If `‖m(n)‖ = 1`
pointwise, `ĝ = m·f̂`, and `f` is Ḣˢ-summable, then

    `‖g‖²_{Ḣˢ} = ‖f‖²_{Ḣˢ}`.

Lifts `L2_isometry_of_unit_symbol` to every regularity level. -/
theorem Hs_isometry_of_unit_symbol
    {d : Type*} [Fintype d] (s : ℝ)
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hm : ∀ n, ‖m n‖ = 1)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s g = hsSeminormSq s f := by
  -- Pointwise the multiplied summand equals the θ summand, since ‖m(n)‖² = 1.
  have hptfun : (fun n ↦ (fracDerivSymbol s n) ^ 2
                           * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2))
              = (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by
    funext n; rw [hm n]; ring
  have hsumm' : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2
                 * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) := by
    rw [hptfun]; exact hsumm
  have hg_hasSum :=
    hasSum_sq_multiplier_Hs s f g m hcoeff hsumm'
  rw [hptfun] at hg_hasSum
  have hf_hasSum : HasSum
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
      (hsSeminormSq s f) := by
    unfold hsSeminormSq; exact hsumm.hasSum
  exact hg_hasSum.unique hf_hasSum

/-! ### SQG selection rule in Ḣˢ form -/

/-- **Ḣˢ-contractivity of bounded Fourier multipliers.** If two L²
functions `f, g` on `𝕋ᵈ` satisfy `ĝ(n) = m(n)·f̂(n)` with `‖m(n)‖ ≤ 1`
and `f` has Ḣˢ-summable Fourier coefficients, then `‖g‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣˢ}`.
This generalises `riesz_Hs_contractive` beyond the Riesz multiplier. -/
theorem Hs_contractive_of_bounded_symbol
    {d : Type*} [Fintype d] (s : ℝ)
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (m : (d → ℤ) → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1)
    (hcoeff : ∀ n, mFourierCoeff g n = m n * mFourierCoeff f n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s g ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  -- Per-mode: ‖ĝ(n)‖² = ‖m(n)‖² · ‖f̂(n)‖² ≤ ‖f̂(n)‖², multiplied by σ_s(n)² ≥ 0.
  have hmode : ∀ n, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff g n‖ ^ 2
                  ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := by
    intro n
    rw [hcoeff n, norm_mul, mul_pow]
    have hm1 : ‖m n‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖m n‖ := norm_nonneg _
      nlinarith [hm n, h0]
    have hrest : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (fracDerivSymbol s n) ^ 2
            * (‖m n‖ ^ 2 * ‖mFourierCoeff f n‖ ^ 2)
        = ‖m n‖ ^ 2
            * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by ring
      _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hrest
      _ = (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  have hsumm_g : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff g n‖ ^ 2) := by
    refine hsumm.of_nonneg_of_le (fun n => ?_) hmode
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact Summable.tsum_le_tsum hmode hsumm_g hsumm

/-- **SQG selection rule, Ḣˢ form.** If `‖ŵ(n)‖ ≤ σ_k(n)·‖θ̂(n)‖` pointwise
(the selection-rule shape with any regularity exponent `k`) and the
weighted tail is Ḣˢ-summable in the scaled form below, then

    `‖w‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+k}}`.

At `s = 0, k = 1` this recovers `sqg_selection_rule_Hs1`. -/
theorem sqg_selection_rule_Hs
    {d : Type*} [Fintype d] (s k : ℝ)
    (θ w : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hbound : ∀ n,
        ‖mFourierCoeff w n‖ ≤ (fracDerivSymbol k n) * ‖mFourierCoeff θ n‖)
    (hsum : Summable
        (fun n ↦ (fracDerivSymbol (s + k) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s w ≤ hsSeminormSq (s + k) θ := by
  -- Pointwise in the Ḣˢ weight: σ_s(n)² · ‖ŵ(n)‖²
  -- ≤ σ_s(n)² · σ_k(n)² · ‖θ̂(n)‖² = σ_{s+k}(n)² · ‖θ̂(n)‖².
  have hmode : ∀ n,
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff w n‖ ^ 2
      ≤ (fracDerivSymbol (s + k) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    have hσs : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
    have h_w_nn : 0 ≤ ‖mFourierCoeff w n‖ := norm_nonneg _
    have hσk_nn : 0 ≤ (fracDerivSymbol k n) := fracDerivSymbol_nonneg k n
    have h_rhs_nn :
        0 ≤ (fracDerivSymbol k n) * ‖mFourierCoeff θ n‖ :=
      mul_nonneg hσk_nn (norm_nonneg _)
    have hsq_w : ‖mFourierCoeff w n‖ ^ 2
                ≤ ((fracDerivSymbol k n) * ‖mFourierCoeff θ n‖) ^ 2 := by
      have := hbound n
      nlinarith [this, h_w_nn, h_rhs_nn]
    calc (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff w n‖ ^ 2
        ≤ (fracDerivSymbol s n) ^ 2
            * ((fracDerivSymbol k n) * ‖mFourierCoeff θ n‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_w hσs
      _ = ((fracDerivSymbol s n) ^ 2 * (fracDerivSymbol k n) ^ 2)
            * ‖mFourierCoeff θ n‖ ^ 2 := by ring
      _ = (fracDerivSymbol (s + k) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
          rw [← fracDerivSymbol_add_sq]
  -- Summability of the `w` Ḣˢ series from the pointwise bound.
  have hsumm_w : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff w n‖ ^ 2) := by
    refine hsum.of_nonneg_of_le (fun n => ?_) hmode
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- Both sides as tsums under hsSeminormSq.
  unfold hsSeminormSq
  exact Summable.tsum_le_tsum hmode hsumm_w hsum

end SqgIdentity
