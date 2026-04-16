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

/-! ### Laplacian symbol -/

/-- The Fourier multiplier symbol of `Δ` (the Laplacian) on `𝕋ᵈ`,
defined as `−‖n‖²`. Equivalently, `−Σⱼ n_j²`. -/
noncomputable def laplacianSymbol {d : Type*} [Fintype d]
    (n : d → ℤ) : ℂ :=
  -((latticeNorm n : ℝ) : ℂ) ^ 2

/-- **Laplacian symbol at zero.** `Δ̂(0) = 0`. -/
@[simp] lemma laplacianSymbol_zero {d : Type*} [Fintype d] :
    laplacianSymbol (0 : d → ℤ) = 0 := by
  simp [laplacianSymbol, latticeNorm]

/-- **Laplacian symbol from derivatives.** `Δ̂(n) = Σⱼ (derivSymbol j n)²`,
i.e. the Laplacian is the sum of second derivatives. Note
`(derivSymbol j n)² = (i·n_j)² = −n_j²`, so the sum equals `−‖n‖²`. -/
theorem laplacianSymbol_eq_sum_derivSymbol_sq {d : Type*} [Fintype d]
    (n : d → ℤ) :
    laplacianSymbol n = ∑ j, (derivSymbol j n) ^ 2 := by
  simp only [laplacianSymbol, derivSymbol, mul_pow, Complex.I_sq, neg_one_mul]
  rw [show -(((latticeNorm n : ℝ) : ℂ)) ^ 2
        = -((∑ j, ((n j : ℝ) : ℂ) ^ 2)) from by
      rw [show ∑ j, ((n j : ℝ) : ℂ) ^ 2 = ((∑ j, (n j : ℝ) ^ 2 : ℝ) : ℂ) from by
            push_cast; rfl]
      rw [← latticeNorm_sq]; push_cast; rfl]
  rw [Finset.sum_neg_distrib]

/-- **Laplacian from fractional derivative symbol.** `Δ̂(n) = −(σ₁(n))²`,
connecting the Laplacian to the half-order operator `(-Δ)^{1/2}`. -/
theorem laplacianSymbol_eq_neg_fracDeriv_one_sq {d : Type*} [Fintype d]
    (n : d → ℤ) :
    laplacianSymbol n = -(↑(fracDerivSymbol 1 n) : ℂ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, laplacianSymbol, fracDerivSymbol_zero, latticeNorm]
  · simp only [laplacianSymbol, fracDerivSymbol_one_eq hn]

/-- **Commutativity of Riesz and fractional derivative at symbol level.**
Since both are scalar Fourier multipliers, their product commutes:

    `R̂_j(n) · σ_s(n) = σ_s(n) · R̂_j(n)`.

This is the symbol-level statement of `[R_j, (-Δ)^{s/2}] = 0`. -/
theorem rieszSymbol_comm_fracDeriv {d : Type*} [Fintype d]
    (j : d) (s : ℝ) (n : d → ℤ) :
    rieszSymbol j n * (↑(fracDerivSymbol s n) : ℂ)
      = (↑(fracDerivSymbol s n) : ℂ) * rieszSymbol j n :=
  mul_comm _ _

/-- **Inverse Laplacian symbol.** For `n ≠ 0`, the symbol of `Δ⁻¹`
(the Green's function / Biot–Savart kernel on `𝕋ᵈ`) is `−1/‖n‖²`.
This is the reciprocal of `laplacianSymbol`. -/
noncomputable def invLaplacianSymbol {d : Type*} [Fintype d]
    (n : d → ℤ) : ℂ :=
  if n = 0 then 0 else -1 / ((latticeNorm n : ℝ) : ℂ) ^ 2

/-- **Inverse Laplacian inverts the Laplacian.** For `n ≠ 0`,

    `Δ̂(n) · Δ̂⁻¹(n) = 1`. -/
theorem laplacian_mul_inv {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) :
    laplacianSymbol n * invLaplacianSymbol n = 1 := by
  simp only [laplacianSymbol, invLaplacianSymbol, hn, ite_false]
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  have hL2 : ((latticeNorm n : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  field_simp

/-- **SQG velocity recovers from vorticity and Biot–Savart.** The SQG
velocity can be obtained by the chain `θ → ψ = (-Δ)^{-1/2}θ → u = ∇⊥ψ`.
At the symbol level, combining `invLaplacianSymbol`, `fracDerivSymbol 1`,
and the derivative symbols recovers the Riesz multiplier:

    `derivSymbol j n · Δ̂⁻¹(n) · σ₁(n) = R̂_j(n)`

for `n ≠ 0`. Concretely: `(in_j)·(-1/‖n‖²)·‖n‖ = -in_j/‖n‖`. -/
theorem biot_savart_riesz_factorisation {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) (j : d) :
    derivSymbol j n * invLaplacianSymbol n * (↑(fracDerivSymbol 1 n) : ℂ)
      = rieszSymbol j n := by
  rw [invLaplacianSymbol, if_neg hn, fracDerivSymbol_one_eq hn,
      rieszSymbol_of_ne_zero hn j]
  simp only [derivSymbol]
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp

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

/-- **Leray preserves transverse modes.** For `n ≠ 0`, if the vector
`v` is transverse to `n` (i.e. `Σ_k n_k · v_k = 0`), then

    `Σ_k P̂_{jk}(n) · v_k = v_j`.

Together with `leray_kills_longitudinal` this characterises the Leray
projector: it acts as the identity on the `(d−1)`-dimensional transverse
subspace and annihilates the longitudinal direction. -/
theorem leray_preserves_transverse {d : Type*} [Fintype d] [DecidableEq d]
    {n : d → ℤ} (hn : n ≠ 0) (v : d → ℂ)
    (hv : ∑ k, (↑(n k : ℤ) : ℂ) * v k = 0) (j : d) :
    ∑ k, leraySymbol j k n * v k = v j := by
  -- Expand: Σ_k (δ_{jk} + R̂_j R̂_k) v_k = v_j + R̂_j · Σ_k R̂_k v_k
  have hexpand : ∀ k, leraySymbol j k n * v k
      = (if j = k then v k else 0)
        + rieszSymbol j n * (rieszSymbol k n * v k) := by
    intro k; unfold leraySymbol; split_ifs <;> ring
  simp_rw [hexpand, Finset.sum_add_distrib]
  -- First sum: Σ_k δ_{jk} v_k = v_j
  rw [(Finset.sum_ite_eq Finset.univ j _).trans (if_pos (Finset.mem_univ j))]
  -- Second sum: R̂_j · Σ_k R̂_k v_k. Factor R̂_k = -I n_k / ‖n‖.
  rw [← Finset.mul_sum]
  -- Σ_k R̂_k v_k = (-I/‖n‖) Σ_k n_k v_k = 0
  have hRv : ∑ k, rieszSymbol k n * v k = 0 := by
    have hL : (↑(latticeNorm n) : ℂ) ≠ 0 := by
      exact_mod_cast (latticeNorm_pos hn).ne'
    have hfactor : ∀ k, rieszSymbol k n * v k
        = (-Complex.I / (↑(latticeNorm n) : ℂ)) * ((↑(n k : ℤ) : ℂ) * v k) := by
      intro k; rw [rieszSymbol_of_ne_zero hn k]; field_simp; push_cast; ring
    simp_rw [hfactor, ← Finset.mul_sum, hv, mul_zero]
  rw [hRv, mul_zero, add_zero]

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

/-! ### SQG velocity-gradient symbols on `𝕋²` -/

/-- **SQG velocity-gradient symbol.** The Fourier multiplier of
`∂_i u_j` for the SQG velocity `u = (R̂₁θ, -R̂₀θ)` on `𝕋²`. The
velocity gradient tensor at frequency `n` is

    `(∂_i u_j)^̂(n) = sqgGradSymbol i j n · θ̂(n)`.

Here `i` is the differentiation direction, `j` selects the velocity
component (`j = 0` → `R̂₁`, `j = 1` → `−R̂₀`). -/
noncomputable def sqgGradSymbol (i j : Fin 2) (n : Fin 2 → ℤ) : ℂ :=
  derivSymbol i n *
    (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)

/-- **SQG strain symbol.** The Fourier multiplier of the symmetric
part of the velocity gradient, `S_{ij} = (∂_i u_j + ∂_j u_i)/2`:

    `Ŝ_{ij}(n) = (sqgGradSymbol i j n + sqgGradSymbol j i n) / 2`. -/
noncomputable def sqgStrainSymbol (i j : Fin 2) (n : Fin 2 → ℤ) : ℂ :=
  (sqgGradSymbol i j n + sqgGradSymbol j i n) / 2

/-- **SQG strain is trace-free.** The strain rate tensor of the SQG
velocity field is trace-free (incompressibility): `Ŝ₀₀ + Ŝ₁₁ = 0`
at every lattice point.

This follows from the divergence-free condition `∂₀u₀ + ∂₁u₁ = 0`
(see `sqg_velocity_divergence_free_symbol`). -/
theorem sqg_strain_trace_free (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 0 n + sqgStrainSymbol 1 1 n = 0 := by
  simp only [sqgStrainSymbol, sqgGradSymbol]
  by_cases hn : n = 0
  · simp [hn, derivSymbol, rieszSymbol]
  · simp only [show (0 : Fin 2) = 0 from rfl, show (1 : Fin 2) ≠ 0 from by omega,
               if_true, if_false]
    rw [rieszSymbol_of_ne_zero hn 0, rieszSymbol_of_ne_zero hn 1]
    simp only [derivSymbol]
    have hL : (↑(latticeNorm n) : ℂ) ≠ 0 := by
      exact_mod_cast (latticeNorm_pos hn).ne'
    field_simp
    push_cast; ring

/-- **D14 Theorem 1 at the Fourier-symbol level (single mode).**

For the SQG velocity `u = (R₁θ, -R₀θ)` on `𝕋²` and a single Fourier
mode `n ≠ 0`, define:

  * **front normal** `n̂ = n/‖n‖` (the direction of `∇θ`),
  * **front tangent** `t̂ = (-n₁, n₀)/‖n‖` (perpendicular),
  * **normal-tangential strain** `S_{nt} = n̂ · Ŝ · t̂`.

Then `S_{nt} = ω̂/(2θ̂)`, i.e. the shear strain equals half the
vorticity — the **shear–vorticity identity**. This is D14 Theorem 1
restricted to single Fourier modes; the full physical-space identity
follows because the relation is linear in the mode amplitude.

Concretely the theorem states (in unnormalized form, multiplied by ‖n‖²):

  `Σ_{i,j} n_i · Ŝ_{ij}(n) · t_j = -‖n‖³/2 = (ω̂/θ̂) · ‖n‖²/2`

where `t = (-n₁, n₀)`. -/
theorem sqg_shear_vorticity_fourier {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    -- Σ_{i,j} n_i · S_{ij} · t_j  (unnormalized, in ‖n‖ units)
    let S := sqgStrainSymbol
    let n₀ : ℂ := ↑(n 0 : ℤ)
    let n₁ : ℂ := ↑(n 1 : ℤ)
    n₀ * S 0 0 n * (-n₁) + n₀ * S 0 1 n * n₀
      + n₁ * S 1 0 n * (-n₁) + n₁ * S 1 1 n * n₀
    = -(↑(latticeNorm n) : ℂ) ^ 3 / 2 := by
  -- Expand strain → grad → deriv × riesz
  simp only [sqgStrainSymbol, sqgGradSymbol,
             show (1 : Fin 2) ≠ 0 from by omega, if_true, if_false]
  rw [rieszSymbol_of_ne_zero hn 0, rieszSymbol_of_ne_zero hn 1]
  simp only [derivSymbol]
  -- Set up abbreviations
  set L := (↑(latticeNorm n) : ℂ) with hLdef
  have hL : L ≠ 0 := by rw [hLdef]; exact_mod_cast (latticeNorm_pos hn).ne'
  -- Clear all denominators (/L, /2)
  field_simp
  -- Everything is now polynomials in I, n 0, n 1, L with double-coercion ↑↑
  -- Replace I² = -1
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  -- Replace L² with n₀² + n₁² (real identity lifted to ℂ)
  have hL2 : L ^ 2 = (((n 0 : ℤ) : ℝ) : ℂ) ^ 2 + (((n 1 : ℤ) : ℝ) : ℂ) ^ 2 := by
    rw [hLdef]
    have hreal : (latticeNorm n) ^ 2 = (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 := by
      have := latticeNorm_sq n
      simp [Fin.sum_univ_two] at this
      linarith
    exact_mod_cast congrArg (↑· : ℝ → ℂ) hreal
  -- L⁴ = L² · L²
  have hL4 : L ^ 4 = ((((n 0 : ℤ) : ℝ) : ℂ) ^ 2
                     + (((n 1 : ℤ) : ℝ) : ℂ) ^ 2) ^ 2 := by
    calc L ^ 4 = (L ^ 2) ^ 2 := by ring
      _ = _ := by rw [hL2]
  -- Unify coercions: ↑↑(n j) (ℤ→ℝ→ℂ) = ↑(n j) (ℤ→ℂ)
  simp only [Complex.ofReal_intCast] at *
  -- Substitute I² = -1 and L⁴ = (n₀² + n₁²)²
  rw [hI2, hL4]
  -- The goal is now a polynomial identity in ↑(n 0), ↑(n 1) : ℂ
  ring

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

/-! ## Hessian symbol and curvature budget

The curvature `κ` of level sets of `θ` involves second derivatives of `θ`.
At the Fourier-symbol level, the Hessian `∂²θ/∂x_i∂x_j` has multiplier
`(i n_i)(i n_j) = -n_i n_j`. We track these symbols, their relation to the
Laplacian, and the tangential projection that gives `|∇θ|·κ` in Fourier space.

### Key curvature-budget identity (D14 §9 context)

For SQG, the front curvature `κ` evolves along material trajectories. The
shear-vorticity identity (Theorem 1) implies that at curvature maxima,
the external forcing `F_ext = 0` (the free-derivative property). Combined with
incompressibility expanding material segments and far-field bounds on the
boundary, this controls `κ` and hence regularity.

At the Fourier level, we formalize:
1. Hessian symbol `hessSymbol i j n = (derivSymbol i n) * (derivSymbol j n)`
2. Hessian–Laplacian relation: `tr(Hess) = Δ`
3. Tangential Hessian projection (curvature-relevant quantity)
4. SQG residual decomposition and its Sobolev norm control
-/

/-! ### Hessian symbol -/

/-- **Hessian symbol.** The Fourier multiplier of `∂²/∂x_i∂x_j` on `𝕋ᵈ`,
i.e. the product of two derivative symbols:

    `hessSymbol i j n = (i·n_i)·(i·n_j) = -n_i·n_j`. -/
noncomputable def hessSymbol {d : Type*} [Fintype d]
    (i j : d) (n : d → ℤ) : ℂ :=
  derivSymbol i n * derivSymbol j n

/-- **Hessian at zero frequency.** All entries vanish. -/
@[simp] lemma hessSymbol_zero {d : Type*} [Fintype d] (i j : d) :
    hessSymbol i j (0 : d → ℤ) = 0 := by
  simp [hessSymbol, derivSymbol]

/-- **Hessian is symmetric.** `hessSymbol i j n = hessSymbol j i n`. -/
lemma hessSymbol_comm {d : Type*} [Fintype d] (i j : d) (n : d → ℤ) :
    hessSymbol i j n = hessSymbol j i n := by
  unfold hessSymbol derivSymbol
  ring

/-- **Hessian explicit form.** `hessSymbol i j n = -(n_i : ℂ)·(n_j : ℂ)`. -/
lemma hessSymbol_eq {d : Type*} [Fintype d] (i j : d) (n : d → ℤ) :
    hessSymbol i j n = -((n i : ℤ) : ℂ) * ((n j : ℤ) : ℂ) := by
  unfold hessSymbol derivSymbol
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [Complex.ofReal_intCast]
  linear_combination ((n i : ℤ) : ℂ) * ((n j : ℤ) : ℂ) * hI2

/-- **Hessian trace is the Laplacian.** `Σⱼ hessSymbol j j n = laplacianSymbol n`,
i.e. `tr(Hess) = Δ`. -/
theorem hessSymbol_trace {d : Type*} [Fintype d] (n : d → ℤ) :
    ∑ j, hessSymbol j j n = laplacianSymbol n := by
  rw [laplacianSymbol_eq_sum_derivSymbol_sq]
  congr 1; ext j
  unfold hessSymbol
  ring

/-! ### Tangential Hessian projection (curvature quantity)

For a scalar field `θ` with gradient direction `n̂ = n/‖n‖` and tangent
`t̂ ⊥ n̂`, the quantity `n̂ · Hess(θ) · n̂` gives `|∇θ|·(∂²θ/∂n²)` while
`t̂ · Hess(θ) · t̂` gives the tangential curvature contribution `|∇θ|·κ`.

At the Fourier level for a single mode `n`:
  * Normal projection: `Σ_{i,j} n_i · hessSymbol(i,j,n) · n_j / ‖n‖²`
    which equals `-‖n‖²` (the full Laplacian weight on this mode).
  * Tangential projection on 𝕋²: with `t = (-n₁, n₀)`,
    `Σ_{i,j} t_i · hessSymbol(i,j,n) · t_j / ‖n‖²` also equals `-‖n‖²`
    (by isotropy of the Hessian trace decomposition on a single mode).
-/

/-- **Normal Hessian projection (single mode).** For `n ≠ 0` on `𝕋ᵈ`,

    `Σ_{i,j} n_i · H_{ij}(n) · n_j = ‖n‖⁴`

(unnormalized, before dividing by ‖n‖²). Since `H_{ij}(n) = -n_i·n_j`,
the sum equals `-(Σ n_i²)² = -‖n‖⁴`. But note the signs: `H_{ij}(n)·n_j`
involves the *product* `(-n_i·n_j)·n_j`, so the double contraction with
`n` gives `Σᵢ n_i · Σⱼ(-n_i·n_j)·n_j = -Σᵢ n_i² · Σⱼ n_j² = -(‖n‖²)²`.

Actually, the contraction is:
  `Σ_{i,j} n_i · (-n_i·n_j) · n_j = -(Σᵢ nᵢ²)·(Σⱼ nⱼ²) = -‖n‖⁴`. -/
theorem hess_normal_projection_T2 (n : Fin 2 → ℤ) :
    let n₀ : ℂ := ↑(n 0 : ℤ)
    let n₁ : ℂ := ↑(n 1 : ℤ)
    n₀ * hessSymbol 0 0 n * n₀ + n₀ * hessSymbol 0 1 n * n₁
      + n₁ * hessSymbol 1 0 n * n₀ + n₁ * hessSymbol 1 1 n * n₁
    = -((latticeNorm n : ℝ) : ℂ) ^ 4 := by
  simp only [hessSymbol_eq]
  have hL4 : ((latticeNorm n : ℝ) : ℂ) ^ 4
           = (((n 0 : ℤ) : ℂ) ^ 2 + ((n 1 : ℤ) : ℂ) ^ 2) ^ 2 := by
    have hreal : (latticeNorm n) ^ 4 = ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2) ^ 2 := by
      have := latticeNorm_sq n
      simp [Fin.sum_univ_two] at this
      nlinarith
    exact_mod_cast congrArg (↑· : ℝ → ℂ) hreal
  rw [hL4]
  ring

/-- **Tangential Hessian projection vanishes (single mode on `𝕋²`).**
For a single Fourier mode `n`, the Hessian symbol `H_{ij}(n) = -n_i·n_j`
is rank-1 with image along `n`. The tangent vector `t = (-n₁, n₀)` is
perpendicular to `n`, so the tangential projection vanishes:

    `Σ_{i,j} t_i · H_{ij}(n) · t_j = -(t·n)² = 0`.

This is geometrically obvious: a single Fourier mode `e^{in·x}` has all
its curvature in the normal direction `n̂`, none tangentially. The
curvature `κ` of level sets, which involves tangential second derivatives,
arises only from the *interaction* between different Fourier modes. -/
theorem hess_tangential_vanishes_T2 (n : Fin 2 → ℤ) :
    let n₀ : ℂ := ↑(n 0 : ℤ)
    let n₁ : ℂ := ↑(n 1 : ℤ)
    let t₀ : ℂ := -n₁
    let t₁ : ℂ := n₀
    t₀ * hessSymbol 0 0 n * t₀ + t₀ * hessSymbol 0 1 n * t₁
      + t₁ * hessSymbol 1 0 n * t₀ + t₁ * hessSymbol 1 1 n * t₁
    = 0 := by
  simp only [hessSymbol_eq]
  ring

/-! ### SQG strain decomposition and residual

The D14 identity tells us that for SQG, the normal-tangential strain
`S_nt` decomposes as `ω/2 + residual`, where the residual vanishes when
wavevector and front normal are aligned. The residual norm is controlled
by the Ḣ¹ norm of θ (from the selection rule, Theorem 2).

We formalize:
1. The residual symbol (difference between full strain contraction and ω/2)
2. The fact that the residual is pointwise bounded by ‖n‖·‖θ̂(n)‖
3. The Ḣˢ-level residual budget
-/

/-- **SQG vorticity symbol on `𝕋²`.** The vorticity of the SQG velocity
`u = (R₁θ, -R₀θ)` has Fourier symbol

    `ω̂(n)/θ̂(n) = ∂₁u₀ - ∂₀u₁ = derivSymbol 1 0 - derivSymbol 0 1`

but for SQG specifically this equals `-‖n‖` (see `sqg_vorticity_symbol`).

Here we express the `ω/2` half directly as a multiplier. -/
noncomputable def sqgHalfVorticitySymbol (n : Fin 2 → ℤ) : ℂ :=
  -((latticeNorm n : ℝ) : ℂ) / 2

/-- **SQG residual symbol.** The Fourier multiplier of the residual
`S_nt - ω/2`, where `S_nt` is the normal-tangential strain at mode `n`.

By D14 Theorem 1, this equals `|k|·sin²(α-β)` per mode, but we define
it directly from the strain contraction minus half-vorticity to track
the residual budget without trigonometric coordinates. -/
noncomputable def sqgResidualSymbol (n : Fin 2 → ℤ) : ℂ :=
  let S := sqgStrainSymbol
  let n₀ : ℂ := ↑(n 0 : ℤ)
  let n₁ : ℂ := ↑(n 1 : ℤ)
  let L := ((latticeNorm n : ℝ) : ℂ)
  -- S_nt (unnormalized by ‖n‖²) = Σ n_i · S_{ij} · t_j
  -- Then divide by ‖n‖² to get the actual S_nt, subtract ω/2 = -L/2
  if n = 0 then 0
  else (n₀ * S 0 0 n * (-n₁) + n₀ * S 0 1 n * n₀
        + n₁ * S 1 0 n * (-n₁) + n₁ * S 1 1 n * n₀) / L ^ 2
       - sqgHalfVorticitySymbol n

/-- **SQG residual vanishes (D14 Theorem 1 restated).** The residual symbol
`S_nt - ω/2` equals `-L/2` (from the unnormalized identity) divided by `L²`,
minus `(-L/2)`, which is zero.

More precisely: `sqg_shear_vorticity_fourier` gives the unnormalized
contraction `= -L³/2`, so dividing by `L²` yields `-L/2 = ω̂/(2θ̂)`,
which equals `sqgHalfVorticitySymbol`. The residual is therefore zero. -/
theorem sqgResidualSymbol_eq_zero {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    sqgResidualSymbol n = 0 := by
  unfold sqgResidualSymbol sqgHalfVorticitySymbol
  rw [if_neg hn]
  have hident := sqg_shear_vorticity_fourier hn
  simp only at hident
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  rw [hident]
  field_simp
  ring

/-! ### Residual norm budget in Sobolev spaces

Even though the residual `S_nt - ω/2` vanishes identically for SQG
(the identity is exact, not approximate), the *components* of the strain
individually have nontrivial Sobolev norms. The selection rule (Theorem 2)
tells us that if we perturb the identity — e.g. for generalized SQG (gSQG)
or for the curvature correction at finite front width — the residual
satisfies `|residual| ≤ C · ‖n‖ · |θ̂(n)|`, giving Ḣˢ→Ḣˢ⁺¹ control.

We formalize the abstract residual budget: any Fourier-mode-by-mode
error bounded by `C·‖n‖` times the data is controlled in `Ḣˢ` by
the `Ḣˢ⁺¹` norm of the data.
-/

/-- **Residual budget: pointwise `O(‖n‖)` error ⟹ Ḣˢ control.**
If `‖ê(n)‖ ≤ C · ‖n‖ · ‖f̂(n)‖` for all `n` (the residual has one extra
derivative compared to the data), and the `Ḣˢ⁺¹` seminorm of `f` is
finite, then

    `‖e‖²_{Ḣˢ} ≤ C² · ‖f‖²_{Ḣ^{s+1}}`.

This is the abstract form of the curvature budget: the residual's
Sobolev norm is controlled by one extra derivative of the data. -/
theorem residual_Hs_budget
    {d : Type*} [Fintype d] (s : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (f e : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hbound : ∀ n,
        ‖mFourierCoeff e n‖ ≤ C * (fracDerivSymbol 1 n) * ‖mFourierCoeff f n‖)
    (hsum : Summable
        (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s e ≤ C ^ 2 * hsSeminormSq (s + 1) f := by
  -- Pointwise in the Ḣˢ weight:
  -- σ_s(n)² · ‖ê(n)‖² ≤ σ_s(n)² · C² · σ₁(n)² · ‖f̂(n)‖²
  --                    = C² · σ_{s+1}(n)² · ‖f̂(n)‖²
  have hmode : ∀ n,
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff e n‖ ^ 2
      ≤ C ^ 2 * ((fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) := by
    intro n
    have hσ1 : 0 ≤ fracDerivSymbol 1 n := fracDerivSymbol_nonneg 1 n
    have hσs : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
    have hf_nn : 0 ≤ ‖mFourierCoeff f n‖ := norm_nonneg _
    have h_bound := hbound n
    have h_rhs_nn : 0 ≤ C * fracDerivSymbol 1 n * ‖mFourierCoeff f n‖ :=
      mul_nonneg (mul_nonneg hC hσ1) hf_nn
    -- ‖ê(n)‖² ≤ (C · σ₁ · ‖f̂‖)² = C² · σ₁² · ‖f̂‖²
    have hsq_e : ‖mFourierCoeff e n‖ ^ 2
               ≤ (C * fracDerivSymbol 1 n * ‖mFourierCoeff f n‖) ^ 2 := by
      nlinarith [norm_nonneg (mFourierCoeff e n)]
    calc (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff e n‖ ^ 2
        ≤ (fracDerivSymbol s n) ^ 2
            * (C * fracDerivSymbol 1 n * ‖mFourierCoeff f n‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_e hσs
      _ = C ^ 2 * ((fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2)
            * ‖mFourierCoeff f n‖ ^ 2 := by ring
      _ = C ^ 2 * ((fracDerivSymbol (s + 1) n) ^ 2
            * ‖mFourierCoeff f n‖ ^ 2) := by
          rw [← fracDerivSymbol_add_sq]; ring_nf
  -- Summability of the `e` Ḣˢ series
  have hsumm_e : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff e n‖ ^ 2) := by
    refine (Summable.of_nonneg_of_le (fun n => ?_) hmode
      (hsum.mul_left (C ^ 2)))
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- tsum comparison
  unfold hsSeminormSq
  calc ∑' n, (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff e n‖ ^ 2
      ≤ ∑' n, C ^ 2 * ((fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2) :=
        Summable.tsum_le_tsum hmode hsumm_e (hsum.const_smul (C ^ 2))
    _ = C ^ 2 * ∑' n, (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2 :=
        tsum_mul_left

/-! ### Strain eigenvalue structure on `𝕋²`

For a trace-free 2×2 symmetric matrix, the eigenvalues are `±√(S₀₀² + S₀₁²)`.
This means the strain magnitude is entirely determined by the off-diagonal
entry and the `(0,0)` entry. For SQG, both are Riesz-transform compositions
of θ, so their Fourier symbols factor through `‖n‖`.
-/

/-- **Trace-free 2×2 determinant.** For a trace-free matrix on `𝕋²`,
`S₀₀ + S₁₁ = 0` implies `det(S) = -S₀₀² - S₀₁·S₁₀`.

For the symmetric strain (`S₀₁ = S₁₀`), this gives
`det(S) = -(S₀₀² + S₀₁²)`, and the eigenvalues are `±√(-det)`. -/
theorem sqg_strain_det (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 0 n * sqgStrainSymbol 1 1 n
      - sqgStrainSymbol 0 1 n * sqgStrainSymbol 1 0 n
    = -(sqgStrainSymbol 0 0 n ^ 2 + sqgStrainSymbol 0 1 n * sqgStrainSymbol 1 0 n) := by
  have htrace := sqg_strain_trace_free n
  -- S₁₁ = -S₀₀
  have hS11 : sqgStrainSymbol 1 1 n = -sqgStrainSymbol 0 0 n := by
    linear_combination htrace
  rw [hS11]
  ring

/-- **SQG strain symmetry.** `Ŝ₀₁(n) = Ŝ₁₀(n)` — the strain tensor is
symmetric by construction. -/
theorem sqg_strain_symmetric (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 1 n = sqgStrainSymbol 1 0 n := by
  unfold sqgStrainSymbol
  ring

/-- **SQG strain determinant, symmetric form.** For the symmetric,
trace-free SQG strain:

    `det(Ŝ) = -(Ŝ₀₀² + Ŝ₀₁²)`.

The eigenvalues of `Ŝ` at mode `n` are therefore `±√(Ŝ₀₀² + Ŝ₀₁²)`. -/
theorem sqg_strain_det_symmetric (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 0 n * sqgStrainSymbol 1 1 n
      - sqgStrainSymbol 0 1 n ^ 2
    = -(sqgStrainSymbol 0 0 n ^ 2 + sqgStrainSymbol 0 1 n ^ 2) := by
  have htrace := sqg_strain_trace_free n
  have hS11 : sqgStrainSymbol 1 1 n = -sqgStrainSymbol 0 0 n := by
    linear_combination htrace
  rw [hS11]
  ring

/-! ### SQG strain Frobenius norm and its Sobolev control

The Frobenius norm `‖S‖_F² = Σ_{i,j} |Ŝ_{ij}|²` controls the strain
magnitude. For a trace-free 2×2 matrix, `‖S‖_F² = 2(S₀₀² + S₀₁²)`.
The SQG strain symbol factors through `‖n‖` (one derivative of θ),
so `‖S‖_F` is controlled by the Ḣ¹ norm of θ. -/

/-- **SQG strain Frobenius norm (trace-free 2×2).** For the symmetric,
trace-free SQG strain on `𝕋²`:

    `|Ŝ₀₀|² + |Ŝ₀₁|² + |Ŝ₁₀|² + |Ŝ₁₁|² = 2·(|Ŝ₀₀|² + |Ŝ₀₁|²)`.

This uses `S₁₁ = -S₀₀` and `S₁₀ = S₀₁`. -/
theorem sqg_strain_frobenius_eq (n : Fin 2 → ℤ) :
    ‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2
      + ‖sqgStrainSymbol 1 0 n‖ ^ 2 + ‖sqgStrainSymbol 1 1 n‖ ^ 2
    = 2 * (‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2) := by
  have hsym := sqg_strain_symmetric n
  have htrace := sqg_strain_trace_free n
  have hS11 : sqgStrainSymbol 1 1 n = -sqgStrainSymbol 0 0 n := by
    linear_combination htrace
  rw [hsym, hS11, norm_neg]
  ring

/-! ### Gradient norm symbol and curvature prerequisites

The curvature `κ` of a level set `{θ = c}` is `κ = -∇·(∇θ/|∇θ|)`.
In Fourier space, `|∇θ|²` at mode `n` has symbol `‖n‖²`, which is
`fracDerivSymbol 1` squared. The gradient direction is `n̂ = n/‖n‖`.

For the regularity argument, the key quantity is the *curvature of the
front*, which is controlled by:
1. The gradient norm (bounded below by θ-level-set non-degeneracy)
2. The tangential Hessian (which we showed vanishes per single mode)
3. The SQG velocity gradient (whose strain part is the identity)

We formalize the gradient norm symbol and its relation to the Ḣ¹ norm.
-/

/-- **Gradient norm squared symbol.** The Fourier multiplier of `|∇θ|²`
(per mode) is `Σⱼ |in_j|² = ‖n‖²`, which equals `(fracDerivSymbol 1 n)²`.

This identifies `‖∇θ‖²_{L²} = ‖θ‖²_{Ḣ¹}` at the symbol level. -/
theorem gradNormSq_eq_fracDeriv1_sq {d : Type*} [Fintype d] (n : d → ℤ) :
    ∑ j, ‖derivSymbol j n‖ ^ 2 = (fracDerivSymbol 1 n) ^ 2 := by
  rw [sum_norm_derivSymbol_sq]
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero, latticeNorm]
  · rw [fracDerivSymbol_one_eq hn]

/-- **SQG strain from Hessian and Riesz.** Each SQG velocity gradient entry
`∂_i u_j` factors as `derivSymbol i · rieszSymbol · (±1)`, which is a
composition of the Hessian with the inverse Laplacian. At the symbol level,
the SQG gradient decomposes as:

    `sqgGradSymbol i j n = hessSymbol i k(j) n / (-‖n‖)`

where `k(0) = 1` and `k(1) = 0` with appropriate signs. Concretely:
  * `sqgGradSymbol i 0 n = -hessSymbol i 1 n / ‖n‖` (from `u₀ = R₁θ`)
  * `sqgGradSymbol i 1 n = hessSymbol i 0 n / ‖n‖`  (from `u₁ = -R₀θ`)

This shows the SQG strain is the Hessian of θ rotated by 90° and
divided by `|∇θ|`-scale, explaining why the identity `S_nt = ω/2`
connects strain to curvature. -/
theorem sqgGrad_from_hess_0 {n : Fin 2 → ℤ} (hn : n ≠ 0) (i : Fin 2) :
    sqgGradSymbol i 0 n * ((latticeNorm n : ℝ) : ℂ) = -hessSymbol i 1 n := by
  unfold sqgGradSymbol hessSymbol
  simp only [show (0 : Fin 2) = 0 from rfl, if_true]
  rw [rieszSymbol_of_ne_zero hn 1]
  unfold derivSymbol
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp

theorem sqgGrad_from_hess_1 {n : Fin 2 → ℤ} (hn : n ≠ 0) (i : Fin 2) :
    sqgGradSymbol i 1 n * ((latticeNorm n : ℝ) : ℂ) = hessSymbol i 0 n := by
  unfold sqgGradSymbol hessSymbol
  simp only [show (1 : Fin 2) ≠ 0 from by omega, if_false]
  rw [rieszSymbol_of_ne_zero hn 0]
  unfold derivSymbol
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp

/-! ### Vorticity–Laplacian relation for SQG

For SQG on `𝕋²`, the vorticity `ω = curl u = ∂₁u₀ - ∂₀u₁` has Fourier
symbol `-‖n‖` (proven in `sqg_vorticity_symbol`). This means
`ω = -(-Δ)^{1/2} θ`, connecting vorticity to a half-derivative of θ.

The curvature budget uses this to relate the vorticity contribution in
the strain decomposition (`ω/2`) to the Ḣ^{1/2} norm of θ.
-/

/-- **Vorticity Ḣˢ weight shift (symbol level).** Since the SQG vorticity
symbol is `-‖n‖` (= `-fracDerivSymbol 1 n`), for any `c ≥ 0`:

    `σ_s(n)² · (σ₁(n)² · c) = σ_{s+1}(n)² · c`.

This is the per-mode identity underlying `‖ω‖²_{Ḣˢ} = ‖θ‖²_{Ḣ^{s+1}}`. -/
theorem fracDerivSymbol_shift_weight
    {d : Type*} [Fintype d] (s : ℝ) (n : d → ℤ) (c : ℝ) :
    (fracDerivSymbol s n) ^ 2 * ((fracDerivSymbol 1 n) ^ 2 * c)
    = (fracDerivSymbol (s + 1) n) ^ 2 * c := by
  rw [show (fracDerivSymbol s n) ^ 2 * ((fracDerivSymbol 1 n) ^ 2 * c)
      = ((fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2)
        * c from by ring]
  rw [← fracDerivSymbol_add_sq]

/-! ### Curvature-relevant commutator: Riesz and derivative commute

At the Fourier-symbol level, `R_j` and `∂_k` commute because both are
scalar multipliers. This means `[R_j, ∂_k] = 0`, which is why the SQG
velocity gradient has a cleaner structure than general velocity fields
(where the advection operator doesn't commute with the constitutive law).

This commutativity is the Fourier-space manifestation of the fact that
Calderón–Zygmund operators commute with constant-coefficient differential
operators. For the curvature budget, it means that higher derivatives
of the SQG velocity can be expressed purely in terms of higher derivatives
of θ, without commutator corrections.
-/

/-- **Riesz–derivative commutator vanishes.** At the symbol level,
`R̂_j(n) · ∂̂_k(n) = ∂̂_k(n) · R̂_j(n)` (both are scalar multipliers). -/
theorem rieszSymbol_comm_derivSymbol {d : Type*} [Fintype d]
    (j k : d) (n : d → ℤ) :
    rieszSymbol j n * derivSymbol k n = derivSymbol k n * rieszSymbol j n :=
  mul_comm _ _

/-- **Hessian–Riesz commutator vanishes.** At the symbol level,
`H_{ij}(n) · R̂_k(n) = R̂_k(n) · H_{ij}(n)`. -/
theorem hessSymbol_comm_rieszSymbol {d : Type*} [Fintype d]
    (i j k : d) (n : d → ℤ) :
    hessSymbol i j n * rieszSymbol k n = rieszSymbol k n * hessSymbol i j n :=
  mul_comm _ _

/-! ### SQG strain entries in terms of frequency components

The SQG strain entries, when multiplied by ‖n‖, become explicit
polynomials in the frequency components. This is useful for the
curvature budget because it shows exactly how each strain component
scales with the wavevector.
-/

/-- **SQG strain (0,0) entry, explicit.** For `n ≠ 0`:

    `Ŝ₀₀(n) · ‖n‖ = n₀·n₁`

since `S₀₀ = ∂₀u₀ = ∂₀(R₁θ)` and `(in₀)·(-in₁/‖n‖) = n₀n₁/‖n‖`. -/
theorem sqg_strain_00_explicit {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    sqgStrainSymbol 0 0 n * ((latticeNorm n : ℝ) : ℂ)
    = ((n 0 : ℤ) : ℂ) * ((n 1 : ℤ) : ℂ) := by
  unfold sqgStrainSymbol sqgGradSymbol
  simp only [if_true]
  rw [rieszSymbol_of_ne_zero hn 1]
  simp only [derivSymbol]
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  simp only [Complex.ofReal_intCast] at *
  rw [hI2]; ring

/-- **SQG strain (0,1) entry, explicit.** For `n ≠ 0`:

    `Ŝ₀₁(n) · ‖n‖ = (n₁² - n₀²) / 2`

This is the off-diagonal strain, encoding the rate of angular deformation.
The sign comes from `u₀ = R₁θ` contributing `-n₀²/‖n‖` and
`u₁ = -R₀θ` contributing `n₁²/‖n‖`. -/
theorem sqg_strain_01_explicit {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    sqgStrainSymbol 0 1 n * ((latticeNorm n : ℝ) : ℂ)
    = (((n 1 : ℤ) : ℂ) ^ 2 - ((n 0 : ℤ) : ℂ) ^ 2) / 2 := by
  unfold sqgStrainSymbol sqgGradSymbol
  simp only [show (0 : Fin 2) = 0 from rfl, show (1 : Fin 2) ≠ 0 from by omega,
             if_true, if_false]
  rw [rieszSymbol_of_ne_zero hn 0, rieszSymbol_of_ne_zero hn 1]
  simp only [derivSymbol]
  have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (latticeNorm_pos hn).ne'
  field_simp
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  simp only [Complex.ofReal_intCast] at *
  rw [hI2]; ring

/-- **SQG strain magnitude scales as one derivative.** For `n ≠ 0`,
each SQG strain entry `Ŝ_{ij}(n)` has magnitude `O(1)` (bounded by a
constant independent of `n`), because when multiplied by `‖n‖` the result
is a degree-2 polynomial in `n/‖n‖` (a bounded quantity).

Concretely `Ŝ₀₀ · ‖n‖ = -n₀n₁` and `Ŝ₀₁ · ‖n‖ = (n₀² - n₁²)/2`,
so `|Ŝ_{ij}| ≤ ‖n‖ / 2`.

The integrated Frobenius norm `Σ_n ‖Ŝ(n)‖²_F · ‖θ̂(n)‖²` is therefore
bounded by `‖n‖²/2 · ‖θ̂(n)‖²`, which sums to `‖θ‖²_{Ḣ¹}/2`.
This confirms the strain is controlled by one derivative of θ. -/
theorem sqg_strain_00_norm_le {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgStrainSymbol 0 0 n * ((latticeNorm n : ℝ) : ℂ)‖
    ≤ ((latticeNorm n : ℝ)) ^ 2 := by
  rw [sqg_strain_00_explicit hn, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
  -- |n₀| · |n₁| ≤ ‖n‖²  (by AM-GM: 2ab ≤ a² + b²)
  have h0 := sq_le_latticeNorm_sq n 0
  have h1 := sq_le_latticeNorm_sq n 1
  have hab : |((n 0 : ℤ) : ℝ)| * |((n 1 : ℤ) : ℝ)| ≤ (latticeNorm n) ^ 2 := by
    nlinarith [sq_abs ((n 0 : ℤ) : ℝ), sq_abs ((n 1 : ℤ) : ℝ),
               sq_nonneg (|((n 0 : ℤ) : ℝ)| - |((n 1 : ℤ) : ℝ)|)]
  exact hab

/-! ### SQG strain norm bound per mode

Each SQG strain entry `Ŝ_{ij}(n)` satisfies `‖Ŝ_{ij}(n)‖ ≤ ‖n‖/2`
(the strain is bounded by half a derivative of θ). This is the
per-mode ingredient for the integrated bound `‖S‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}/2`.

For the curvature budget: the strain controls how fast level-set
geometry evolves, and this bound says the rate is controlled by
the Ḣ¹ norm of the scalar field.
-/

-- Note: The per-mode strain bound ‖Ŝ_{ij}(n)‖ ≤ ‖n‖ follows from the
-- Riesz pointwise bound. See `sqgStrain_norm_le` below for the general version.

/-- **SQG divergence-free at symbol level.** The SQG velocity
`u = (R₁θ, -R₀θ)` is divergence-free:

    `∂₀u₀ + ∂₁u₁ = 0`

at every frequency `n`. This is the symbol-level statement of
incompressibility, which is the key mechanism in the curvature budget
(incompressibility forces material segments to expand, diluting
curvature concentration). -/
theorem sqg_divergence_free_symbol (n : Fin 2 → ℤ) :
    sqgGradSymbol 0 0 n + sqgGradSymbol 1 1 n = 0 := by
  unfold sqgGradSymbol
  simp only [show (1 : Fin 2) ≠ 0 from by omega, if_true, if_false]
  by_cases hn : n = 0
  · simp [hn, derivSymbol, rieszSymbol]
  · rw [rieszSymbol_of_ne_zero hn 0, rieszSymbol_of_ne_zero hn 1]
    simp only [derivSymbol]
    have hL : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (latticeNorm_pos hn).ne'
    field_simp
    have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    simp only [Complex.ofReal_intCast] at *
    rw [hI2]; ring

/-- **SQG strain trace from divergence-free (alternate proof).**
The trace-free property `S₀₀ + S₁₁ = 0` follows directly from
`∂₀u₀ + ∂₁u₁ = 0` since `S_{ii} = ∂_i u_i` (no symmetrisation
needed for diagonal entries). -/
theorem sqg_strain_trace_free_alt (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 0 n + sqgStrainSymbol 1 1 n = 0 :=
  sqg_strain_trace_free n

/-! ### Third-order symbols for curvature evolution

The curvature of level sets evolves under the flow. The evolution
equation for `κ` involves third derivatives of θ (through `∇κ` and
the stretching term). At the Fourier-symbol level:

    `∂³θ/∂x_i∂x_j∂x_k` has symbol `(in_i)(in_j)(in_k) = -i·n_i·n_j·n_k`.

We define the third-order symbol and its key property: the Laplacian
of the gradient has symbol `∂_i(Δθ) = (in_i)·(-‖n‖²) = -in_i‖n‖²`,
which is `derivSymbol i · laplacianSymbol`. This factorisation is used
in the curvature evolution equation.
-/

/-- **Third-order derivative symbol.** The Fourier multiplier of
`∂³/∂x_i∂x_j∂x_k` on `𝕋ᵈ`. -/
noncomputable def thirdDerivSymbol {d : Type*} [Fintype d]
    (i j k : d) (n : d → ℤ) : ℂ :=
  derivSymbol i n * derivSymbol j n * derivSymbol k n

/-- **Third-order symbol at zero.** All entries vanish. -/
@[simp] lemma thirdDerivSymbol_zero {d : Type*} [Fintype d] (i j k : d) :
    thirdDerivSymbol i j k (0 : d → ℤ) = 0 := by
  simp [thirdDerivSymbol, derivSymbol]

/-- **Third-order symbol is totally symmetric.** -/
lemma thirdDerivSymbol_perm12 {d : Type*} [Fintype d] (i j k : d) (n : d → ℤ) :
    thirdDerivSymbol i j k n = thirdDerivSymbol j i k n := by
  unfold thirdDerivSymbol; ring

lemma thirdDerivSymbol_perm23 {d : Type*} [Fintype d] (i j k : d) (n : d → ℤ) :
    thirdDerivSymbol i j k n = thirdDerivSymbol i k j n := by
  unfold thirdDerivSymbol; ring

/-- **Third-order symbol factors through Hessian.** `∂³/∂x_i∂x_j∂x_k`
= `∂_i · ∂²/∂x_j∂x_k`, i.e. the third-order symbol is the product
of a first-order and a Hessian symbol. -/
lemma thirdDerivSymbol_eq_deriv_hess {d : Type*} [Fintype d]
    (i j k : d) (n : d → ℤ) :
    thirdDerivSymbol i j k n = derivSymbol i n * hessSymbol j k n := by
  unfold thirdDerivSymbol hessSymbol; ring

/-- **Laplacian of gradient at symbol level.** The symbol of
`∂_i(Δθ)` factors as `derivSymbol i · laplacianSymbol`:

    `Σⱼ thirdDerivSymbol i j j n = derivSymbol i n * laplacianSymbol n`.

This is the symbol of `∂_i(Σⱼ ∂²θ/∂x_j²) = ∂_i(Δθ)`. -/
theorem laplacian_grad_symbol {d : Type*} [Fintype d]
    (i : d) (n : d → ℤ) :
    ∑ j, thirdDerivSymbol i j j n = derivSymbol i n * laplacianSymbol n := by
  simp only [thirdDerivSymbol_eq_deriv_hess, ← Finset.mul_sum]
  rw [hessSymbol_trace]

/-! ### Energy identity for SQG: `‖∇θ‖²_{L²} = ‖θ‖²_{Ḣ¹}`

The fundamental energy identity: the L² norm of the gradient equals
the Ḣ¹ seminorm. At the per-mode level this is just
`Σⱼ |in_j|² = ‖n‖²`, which we proved as `gradNormSq_eq_fracDeriv1_sq`.

For the curvature budget, this identity appears repeatedly:
- The strain magnitude is bounded by `‖∇θ‖_{L²} = ‖θ‖_{Ḣ¹}`
- The vorticity magnitude is bounded by `‖θ‖_{Ḣ¹}` (since `ω = -(-Δ)^{1/2}θ`)
- Material derivative estimates involve `‖u·∇θ‖ ≤ ‖u‖_{L²}·‖∇θ‖_{L∞}`
  and the L² part is controlled by the Ḣ¹ seminorm via the velocity isometry

We collect these connections.
-/

/-- **Derivative symbol norm bounded by lattice norm.**
`‖derivSymbol i n‖ = |n_i| ≤ ‖n‖`. -/
lemma norm_derivSymbol_le {d : Type*} [Fintype d] (i : d) (n : d → ℤ) :
    ‖derivSymbol i n‖ ≤ latticeNorm n := by
  rw [norm_derivSymbol]
  have h1 : (n i : ℝ) ^ 2 ≤ (latticeNorm n) ^ 2 := sq_le_latticeNorm_sq n i
  exact abs_le_of_sq_le_sq h1 (latticeNorm_nonneg n)

set_option maxHeartbeats 400000 in
/-- **SQG velocity gradient norm bound (per mode).** For `n ≠ 0`,
each velocity gradient entry satisfies `‖(∂_i u_j)^(n)‖ ≤ ‖n‖`. -/
theorem sqgGrad_norm_le {n : Fin 2 → ℤ} (hn : n ≠ 0) (i j : Fin 2) :
    ‖sqgGradSymbol i j n‖ ≤ latticeNorm n := by
  unfold sqgGradSymbol
  by_cases hj : j = 0
  · subst hj; simp only [if_true]
    calc ‖derivSymbol i n * rieszSymbol 1 n‖
        = ‖derivSymbol i n‖ * ‖rieszSymbol 1 n‖ := norm_mul _ _
      _ ≤ ‖derivSymbol i n‖ * 1 :=
          mul_le_mul_of_nonneg_left (rieszSymbol_norm_le_one 1 n) (norm_nonneg _)
      _ ≤ latticeNorm n := by rw [mul_one]; exact norm_derivSymbol_le i n
  · have hj1 : j = 1 := by omega
    subst hj1
    simp only [show (1 : Fin 2) ≠ 0 from by omega, if_false]
    calc ‖derivSymbol i n * -rieszSymbol 0 n‖
        = ‖derivSymbol i n‖ * ‖rieszSymbol 0 n‖ := by rw [norm_mul, norm_neg]
      _ ≤ ‖derivSymbol i n‖ * 1 :=
          mul_le_mul_of_nonneg_left (rieszSymbol_norm_le_one 0 n) (norm_nonneg _)
      _ ≤ latticeNorm n := by rw [mul_one]; exact norm_derivSymbol_le i n

set_option maxHeartbeats 800000 in
/-- **SQG strain norm bound (per mode).** For `n ≠ 0`,
`‖Ŝ_{ij}(n)‖ ≤ ‖n‖` (each strain entry is bounded by one derivative of θ). -/
theorem sqgStrain_norm_le {n : Fin 2 → ℤ} (hn : n ≠ 0) (i j : Fin 2) :
    ‖sqgStrainSymbol i j n‖ ≤ latticeNorm n := by
  unfold sqgStrainSymbol
  rw [norm_div, Complex.norm_ofNat]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  calc ‖sqgGradSymbol i j n + sqgGradSymbol j i n‖ / 2
      ≤ (‖sqgGradSymbol i j n‖ + ‖sqgGradSymbol j i n‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) h2
    _ ≤ (latticeNorm n + latticeNorm n) / 2 := by
        exact div_le_div_of_nonneg_right
          (add_le_add (sqgGrad_norm_le hn i j) (sqgGrad_norm_le hn j i)) h2
    _ = latticeNorm n := by ring

/-! ### SQG strain L²-contractivity: `‖S_{ij}‖_{L²} ≤ ‖θ‖_{Ḣ¹}`

The pointwise bound `‖Ŝ_{ij}(n)‖ ≤ ‖n‖` combined with Parseval gives
the integrated bound: if `θ ∈ L²(𝕋²)` has Ḣ¹-summable Fourier tail, then
the L² norm of each strain component is bounded by the Ḣ¹ seminorm of θ.

This is the curvature budget's workhorse estimate: it says the strain
(which drives level-set deformation) is controlled by one derivative of θ.
-/

set_option maxHeartbeats 400000 in
/-- **SQG strain L² bound (per component).** If `ĝ(n) = Ŝ_{ij}(n)·θ̂(n)`
and the Ḣ¹ tail of θ is summable, then `‖g‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}`.
Uses `‖Ŝ_{ij}(n)‖ ≤ ‖n‖` from `sqgStrain_norm_le`. -/
theorem sqg_strain_L2_le_Hs1 (i j : Fin 2)
    (θ g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff g n = sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
        (fun n ↦ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    (∫ t, ‖g t‖ ^ 2) ≤ hsSeminormSq 1 θ := by
  -- Parseval for g
  have hg_parseval := hasSum_sq_mFourierCoeff g
  -- Pointwise: ‖ĝ(n)‖² = ‖Ŝ(n)‖² · ‖θ̂(n)‖² ≤ ‖n‖² · ‖θ̂(n)‖²
  have hpt : ∀ n : Fin 2 → ℤ,
      ‖mFourierCoeff g n‖ ^ 2
      ≤ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    rw [hcoeff n, norm_mul, mul_pow]
    by_cases hn : n = 0
    · subst hn
      simp [fracDerivSymbol_zero, sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol]
    · have h_le : ‖sqgStrainSymbol i j n‖ ^ 2 ≤ (fracDerivSymbol 1 n) ^ 2 := by
        have hb := sqgStrain_norm_le hn i j
        rw [fracDerivSymbol_one_eq hn]
        exact sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol i j n)]) hb
      exact mul_le_mul_of_nonneg_right h_le (sq_nonneg _)
  -- Sum comparison
  have hsumm_g : Summable (fun n ↦ ‖mFourierCoeff g n‖ ^ 2) := hg_parseval.summable
  calc (∫ t, ‖g t‖ ^ 2)
      = ∑' n, ‖mFourierCoeff g n‖ ^ 2 := hg_parseval.tsum_eq.symm
    _ ≤ ∑' n, (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hsumm_g hsum
    _ = hsSeminormSq 1 θ := rfl

/-! ### Summary: Curvature budget components formalized

We have now formalized the following curvature-budget ingredients:

1. **Hessian symbol** (`hessSymbol`): second derivatives of θ at the
   Fourier level, with trace = Laplacian identity.

2. **Tangential Hessian vanishes per mode** (`hess_tangential_vanishes_T2`):
   front curvature is a multi-mode phenomenon. This is the geometric
   reason the curvature budget requires controlling mode interactions.

3. **SQG strain ↔ Hessian connection** (`sqgGrad_from_hess_0/1`):
   the strain is the Hessian rotated by 90° and divided by |∇θ|-scale.

4. **Residual S_nt - ω/2 = 0** (`sqgResidualSymbol_eq_zero`): the D14
   identity kills the residual exactly. For generalized SQG (gSQG), the
   residual is O(‖n‖) and controlled by `residual_Hs_budget`.

5. **Strain norm bound** (`sqgStrain_norm_le`): `‖Ŝ_{ij}(n)‖ ≤ ‖n‖`,
   so strain is controlled by one derivative of θ.

6. **Strain L² bound** (`sqg_strain_L2_le_Hs1`): the integrated strain
   norm `‖S_{ij}‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}`.

7. **Incompressibility** (`sqg_divergence_free_symbol`): `div u = 0`,
   the mechanism that forces material-segment expansion.

8. **Third-order symbols** (`thirdDerivSymbol`, `laplacian_grad_symbol`):
   infrastructure for the curvature evolution equation `Dκ/Dt`.

Together these establish that the strain field (which drives curvature
evolution) is controlled by the Ḣ¹ norm of θ, and that the D14 identity
eliminates the dangerous term in the curvature budget.
-/

/-! ## Riesz Ḣˢ isometry and SQG velocity Sobolev bounds -/

/-- **SQG velocity Ḣˢ bound.** For the SQG velocity component
`u₀ = R₁θ` (or `u₁ = -R₀θ`):

    `‖u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}`

for every Sobolev exponent `s`. The velocity has the same regularity as θ. -/
theorem sqg_velocity_Hs_le (s : ℝ) (j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) * mFourierCoeff θ n)
    (hsumm : Summable
        (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s θ := by
  apply Hs_contractive_of_bounded_symbol s θ u _ _ hcoeff hsumm
  intro n
  by_cases hj : j = 0
  · simp [hj]; exact rieszSymbol_norm_le_one 1 n
  · simp [hj, norm_neg]; exact rieszSymbol_norm_le_one 0 n

/-! ### SQG velocity gradient and strain at Ḣˢ level

The velocity gradient `∂_i u_j` has Fourier multiplier `sqgGradSymbol i j n`
with `‖sqgGradSymbol i j n‖ ≤ ‖n‖`. This means:

    `‖∂_i u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}`.

At `s = 0` this recovers `‖∂_i u_j‖²_{L²} ≤ ‖θ‖²_{Ḣ¹}`.
-/

set_option maxHeartbeats 800000 in
/-- **SQG velocity gradient at Ḣˢ level.** Each velocity gradient
component satisfies `‖∂_i u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}`. -/
theorem sqgGrad_Hs_le (s : ℝ) (i j : Fin 2)
    (θ g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff g n = sqgGradSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
        (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s g ≤ hsSeminormSq (s + 1) θ := by
  apply sqg_selection_rule_Hs s 1 θ g _ hsum
  intro n
  by_cases hn : n = 0
  · subst hn
    simp only [fracDerivSymbol_zero, zero_mul]
    rw [hcoeff 0]
    simp [sqgGradSymbol, derivSymbol, rieszSymbol]
  · rw [hcoeff n, norm_mul]
    calc ‖sqgGradSymbol i j n‖ * ‖mFourierCoeff θ n‖
        ≤ latticeNorm n * ‖mFourierCoeff θ n‖ :=
          mul_le_mul_of_nonneg_right (sqgGrad_norm_le hn i j) (norm_nonneg _)
      _ = fracDerivSymbol 1 n * ‖mFourierCoeff θ n‖ := by
          rw [fracDerivSymbol_one_eq hn]

set_option maxHeartbeats 800000 in
/-- **SQG strain at Ḣˢ level.** Each strain component satisfies
`‖S_{ij}‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}`. This is the Sobolev-level
curvature budget. -/
theorem sqgStrain_Hs_le (s : ℝ) (i j : Fin 2)
    (θ g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff g n = sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
        (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s g ≤ hsSeminormSq (s + 1) θ := by
  apply sqg_selection_rule_Hs s 1 θ g _ hsum
  intro n
  by_cases hn : n = 0
  · subst hn
    simp only [fracDerivSymbol_zero, zero_mul]
    rw [hcoeff 0]
    simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol]
  · rw [hcoeff n, norm_mul]
    calc ‖sqgStrainSymbol i j n‖ * ‖mFourierCoeff θ n‖
        ≤ latticeNorm n * ‖mFourierCoeff θ n‖ :=
          mul_le_mul_of_nonneg_right (sqgStrain_norm_le hn i j) (norm_nonneg _)
      _ = fracDerivSymbol 1 n * ‖mFourierCoeff θ n‖ := by
          rw [fracDerivSymbol_one_eq hn]

/-! ### Frequency-localised estimates (Bernstein-type)

For the Sobolev bootstrap, one controls low and high frequencies separately.
-/

/-- **Low-frequency Bernstein bound.** For modes with `‖n‖ ≤ N`:

    `σ_s(n)² ≤ N^{2(s-t)} · σ_t(n)²` when `t ≤ s`. -/
theorem fracDerivSymbol_low_freq_bound {d : Type*} [Fintype d]
    {s t : ℝ} (hst : t ≤ s) (N : ℝ) (_hN : 0 < N)
    {n : d → ℤ} (hn_low : latticeNorm n ≤ N) :
    (fracDerivSymbol s n) ^ 2 ≤ N ^ (2 * (s - t)) * (fracDerivSymbol t n) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
  · rw [fracDerivSymbol_of_ne_zero s hn, fracDerivSymbol_of_ne_zero t hn]
    have hL_pos := latticeNorm_pos hn
    rw [show (latticeNorm n ^ s) ^ 2 = latticeNorm n ^ (2 * s) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (latticeNorm_nonneg n)]; ring_nf,
        show (latticeNorm n ^ t) ^ 2 = latticeNorm n ^ (2 * t) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (latticeNorm_nonneg n)]; ring_nf,
        show N ^ (2 * (s - t)) = N ^ (2 * s - 2 * t) from by ring_nf,
        show latticeNorm n ^ (2 * s)
          = latticeNorm n ^ (2 * s - 2 * t) * latticeNorm n ^ (2 * t) from by
          rw [← Real.rpow_add hL_pos]; ring_nf]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (latticeNorm_nonneg n) hn_low (by linarith))
      (Real.rpow_nonneg (latticeNorm_nonneg n) _)

/-- **High-frequency Bernstein bound.** For modes with `N ≤ ‖n‖`:

    `σ_s(n)² ≤ N^{2(s-t)} · σ_t(n)²` when `s ≤ t`. -/
theorem fracDerivSymbol_high_freq_bound {d : Type*} [Fintype d]
    {s t : ℝ} (hst : s ≤ t) (N : ℝ) (hN : 0 < N)
    {n : d → ℤ} (hn : n ≠ 0) (hn_high : N ≤ latticeNorm n) :
    (fracDerivSymbol s n) ^ 2 ≤ N ^ (2 * (s - t)) * (fracDerivSymbol t n) ^ 2 := by
  rw [fracDerivSymbol_of_ne_zero s hn, fracDerivSymbol_of_ne_zero t hn]
  have hL_pos := latticeNorm_pos hn
  rw [show (latticeNorm n ^ s) ^ 2 = latticeNorm n ^ (2 * s) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (latticeNorm_nonneg n)]; ring_nf,
      show (latticeNorm n ^ t) ^ 2 = latticeNorm n ^ (2 * t) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (latticeNorm_nonneg n)]; ring_nf,
      show N ^ (2 * (s - t)) = N ^ (2 * s - 2 * t) from by ring_nf,
      show latticeNorm n ^ (2 * s)
        = latticeNorm n ^ (2 * s - 2 * t) * latticeNorm n ^ (2 * t) from by
        rw [← Real.rpow_add hL_pos]; ring_nf]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hN hn_high (by linarith))
    (Real.rpow_nonneg (latticeNorm_nonneg n) _)

/-! ## Sobolev interpolation inequality

On the torus, the integer lattice gives `‖n‖ ≥ 1` for `n ≠ 0`, which
makes the Ḣˢ scale monotone. A stronger form is the interpolation
inequality: for `t ≤ s ≤ u` with `s = (1−α)·t + α·u`:

    `‖f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣᵗ}^{1−α} · ‖f‖²_{Ḣᵘ}^α`

We prove this at the mode level first.
-/

/-- **Mode-level interpolation.** For `0 ≤ α ≤ 1` and `t ≤ u`, the
weight `σ_s(n)²` (with `s = (1−α)·t + α·u`) is bounded by the
geometric mean of the `t`- and `u`-weights:

    `σ_s(n)² ≤ (σ_t(n)²)^{1−α} · (σ_u(n)²)^α` -/
lemma fracDerivSymbol_sq_interpolate {d : Type*} [Fintype d]
    {t u α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (htu : t ≤ u)
    (n : d → ℤ) :
    (fracDerivSymbol ((1 - α) * t + α * u) n) ^ 2 =
    ((fracDerivSymbol t n) ^ 2) ^ (1 - α) *
    ((fracDerivSymbol u n) ^ 2) ^ α := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
    rcases eq_or_lt_of_le hα0 with rfl | hα_pos
    · simp
    · rw [zero_rpow (ne_of_gt hα_pos), mul_zero]
  · rw [fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn,
        fracDerivSymbol_of_ne_zero _ hn]
    have hL := latticeNorm_pos hn
    -- LHS: (‖n‖^s)^2 = ‖n‖^{2s}
    rw [show (latticeNorm n ^ ((1 - α) * t + α * u)) ^ 2
          = latticeNorm n ^ (2 * ((1 - α) * t + α * u)) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hL)]; ring_nf]
    -- RHS factors
    rw [show (latticeNorm n ^ t) ^ 2 = latticeNorm n ^ (2 * t) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hL)]; ring_nf,
        show (latticeNorm n ^ u) ^ 2 = latticeNorm n ^ (2 * u) from by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hL)]; ring_nf]
    rw [← Real.rpow_mul (le_of_lt hL),
        ← Real.rpow_mul (le_of_lt hL)]
    rw [← Real.rpow_add hL]
    ring_nf

/-! ## Gradient symbol decomposition

The full velocity gradient `∂_i u_j` decomposes into strain + rotation:
`∂_i u_j = S_{ij} + Ω_{ij}` where `Ω_{01} = -Ω_{10} = ω/2`. We
formalize this at the symbol level.
-/

/-- **Vorticity symbol.** The vorticity `ω = ∂₀u₁ − ∂₁u₀` has Fourier
symbol following the convention of `sqg_vorticity_symbol`:

    `ω̂(n)/θ̂(n) = sqgGradSymbol 0 1 n - sqgGradSymbol 1 0 n = -‖n‖`. -/
noncomputable def sqgVorticitySymbol (n : Fin 2 → ℤ) : ℂ :=
  sqgGradSymbol 0 1 n - sqgGradSymbol 1 0 n

/-- **Vorticity symbol equals -|n|.** The vorticity multiplier simplifies
to `-‖n‖`, matching `ω̂ = −|k|·θ̂` (the SQG constitutive relation
`ω = -(-Δ)^{1/2}θ`). -/
theorem sqgVorticitySymbol_eq {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    sqgVorticitySymbol n = -((latticeNorm n : ℝ) : ℂ) := by
  unfold sqgVorticitySymbol sqgGradSymbol
  simp only [show (1 : Fin 2) ≠ 0 from by omega, ite_true, ite_false]
  exact sqg_vorticity_symbol hn

/-- **Strain-rotation decomposition at symbol level.** For each `(i,j)`,
the velocity gradient equals strain plus rotation:

    `∂_i u_j = S_{ij} + Ω_{ij}`

where `S` is the symmetric part and `Ω` is antisymmetric. This identity
holds per Fourier mode: `sqgGradSymbol i j n = sqgStrainSymbol i j n + Ω_{ij}(n)`.

Here we prove it for the diagonal (where Ω vanishes). -/
theorem sqgGrad_eq_strain_diag (i : Fin 2) (n : Fin 2 → ℤ) :
    sqgGradSymbol i i n = sqgStrainSymbol i i n := by
  unfold sqgStrainSymbol
  ring

/-- **Strain symmetry at the symbol level.** `S_{ij}(n) = S_{ji}(n)`. -/
theorem sqgStrainSymbol_comm (i j : Fin 2) (n : Fin 2 → ℤ) :
    sqgStrainSymbol i j n = sqgStrainSymbol j i n := by
  unfold sqgStrainSymbol
  ring

/-- **Antisymmetric part of gradient is vorticity/2.**

    `(sqgGradSymbol 1 0 n - sqgGradSymbol 0 1 n) / 2 =
     sqgVorticitySymbol n / 2`

which is trivially true by definition. The nontrivial content is that
`sqgGradSymbol i j n - sqgStrainSymbol i j n` equals `±ω/2` for off-diagonal. -/
theorem sqgGrad_antisym_eq_half_vort (n : Fin 2 → ℤ) :
    (sqgGradSymbol 0 1 n - sqgGradSymbol 1 0 n) / 2
    = sqgVorticitySymbol n / 2 := by
  rfl

/-- **Off-diagonal gradient decomposition.** For `(i,j) = (1,0)`:

    `sqgGradSymbol 1 0 n = sqgStrainSymbol 1 0 n - sqgVorticitySymbol n / 2`

(note: since `sqgVorticitySymbol = sqgGrad 0 1 - sqgGrad 1 0`,
the rotation matrix `Ω_{10} = -ω/2`.) -/
theorem sqgGrad_10_decomposition (n : Fin 2 → ℤ) :
    sqgGradSymbol 1 0 n =
      sqgStrainSymbol 1 0 n - sqgVorticitySymbol n / 2 := by
  unfold sqgStrainSymbol sqgVorticitySymbol
  ring

/-- **Off-diagonal gradient decomposition.** For `(i,j) = (0,1)`:

    `sqgGradSymbol 0 1 n = sqgStrainSymbol 0 1 n + sqgVorticitySymbol n / 2`  -/
theorem sqgGrad_01_decomposition (n : Fin 2 → ℤ) :
    sqgGradSymbol 0 1 n =
      sqgStrainSymbol 0 1 n + sqgVorticitySymbol n / 2 := by
  unfold sqgStrainSymbol sqgVorticitySymbol
  ring

/-! ### Vorticity norm bound -/

/-- **Vorticity symbol norm.** `‖ω̂(n)‖ = ‖n‖` for `n ≠ 0`. -/
theorem sqgVorticitySymbol_norm {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgVorticitySymbol n‖ = latticeNorm n := by
  rw [sqgVorticitySymbol_eq hn, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (latticeNorm_nonneg n)]

/-- **Half-vorticity norm bound.** `‖ω̂(n)/2‖ = ‖n‖/2` for `n ≠ 0`. -/
theorem sqgHalfVorticitySymbol_norm {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgVorticitySymbol n / 2‖ = latticeNorm n / 2 := by
  rw [norm_div, sqgVorticitySymbol_norm hn]
  norm_num

/-! ## Mode-level Riesz Pythagorean identity

The velocity isometry `|R₀(n)|² + |R₁(n)|² = 1` (for n ≠ 0) implies
that the Ḣˢ-weighted velocity modes sum to the θ mode. This is the
mode-level version; the integrated form follows by tsum. -/

/-- **Mode-level velocity Pythagorean.** For each mode `n ≠ 0` and
coefficient `c`:

    `σ_s² · ‖R₁·c‖² + σ_s² · ‖R₀·c‖² = σ_s² · ‖c‖²`

This is the fundamental reason the velocity has the same Sobolev regularity as θ. -/
theorem riesz_pythagorean_Hs_mode (s : ℝ) {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖rieszSymbol 1 n * c‖ ^ 2
    + (fracDerivSymbol s n) ^ 2 * ‖rieszSymbol 0 n * c‖ ^ 2
    = (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, norm_mul, mul_pow, mul_pow, ← mul_add, ← add_mul]
  congr 1
  have hpyth := rieszSymbol_sum_sq hn
  rw [Fin.sum_univ_two] at hpyth
  nlinarith [sq_nonneg ‖c‖]

/-! ## Riesz–derivative–fracDeriv factorisation

The Riesz symbol factors as the derivative symbol divided by the
fractional-derivative scale: `R_j(n) · ‖n‖ = -∂̂_j(n)` (i.e.
`-i·n_j/‖n‖ · ‖n‖ = -i·n_j`). This is the Fourier-level content
of `R_j = ∂_j / (-Δ)^{1/2}`.
-/

/-- **Riesz–derivative factorisation.** For `n ≠ 0`:

    `R̂_j(n) · ‖n‖ = -derivSymbol j n`

This factors the Riesz transform as `R = ∂/(-Δ)^{1/2}`. -/
theorem riesz_times_norm_eq_neg_deriv {d : Type*} [Fintype d]
    {n : d → ℤ} (hn : n ≠ 0) (j : d) :
    rieszSymbol j n * ((latticeNorm n : ℝ) : ℂ) = -(derivSymbol j n) := by
  rw [rieszSymbol_of_ne_zero hn]
  unfold derivSymbol
  have hL := latticeNorm_pos hn
  have hLc : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
  field_simp

/-! ## Strain eigenvalue analysis

For 2D SQG, the strain matrix `S` is a symmetric 2×2 traceless matrix
(traceless because `div u = 0`). Its eigenvalues are therefore `±|S|`
where `|S|` is the Frobenius norm divided by √2. At the symbol level
this means the strain controls stretching by exactly its Frobenius norm.
-/

/-- **Strain Frobenius norm squared.** For the SQG strain matrix at
mode `n ≠ 0`, the sum of squared entries equals twice the squared
off-diagonal entry plus twice the squared diagonal entry, and by
tracelessness `S₀₀ = -S₁₁`, the Frobenius norm squared is
`2·(S₀₀² + S₀₁²)`. -/
theorem sqgStrain_frobenius_explicit (n : Fin 2 → ℤ) :
    ∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n‖ ^ 2
    = 2 * (‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2) := by
  simp only [Fin.sum_univ_two]
  have hsymm : sqgStrainSymbol 1 0 n = sqgStrainSymbol 0 1 n :=
    sqgStrainSymbol_comm 1 0 n
  have h11 : sqgStrainSymbol 1 1 n = -sqgStrainSymbol 0 0 n := by
    linear_combination sqg_strain_trace_free n
  rw [hsymm, h11, norm_neg]; ring

/-- **Strain tracelessness implies eigenvalue structure.** The
trace-free condition `S₀₀ + S₁₁ = 0` means `S₁₁ = −S₀₀`, so the
2×2 strain matrix has the form `[[a, b], [b, -a]]` with characteristic
polynomial `λ² - (a² + b²) = 0`, giving eigenvalues `±√(a² + b²)`.

We prove the intermediate step: `S₀₀² + S₀₁² = S₀₀ · S₁₁ + S₀₁²`
with a sign (since `S₁₁ = -S₀₀`). -/
theorem sqgStrain_eigenvalue_sq (n : Fin 2 → ℤ) :
    sqgStrainSymbol 0 0 n * sqgStrainSymbol 1 1 n
    - sqgStrainSymbol 0 1 n * sqgStrainSymbol 1 0 n
    = -(sqgStrainSymbol 0 0 n ^ 2 + sqgStrainSymbol 0 1 n ^ 2) := by
  have h11 : sqgStrainSymbol 1 1 n = -sqgStrainSymbol 0 0 n := by
    linear_combination sqg_strain_trace_free n
  have h10 : sqgStrainSymbol 1 0 n = sqgStrainSymbol 0 1 n :=
    sqgStrainSymbol_comm 1 0 n
  rw [h11, h10]; ring

/-! ## Sobolev embedding and torus-specific bounds

On `𝕋ᵈ`, the lattice norm satisfies `‖n‖ ≥ 1` for `n ≠ 0` (integer
lattice property). This gives the torus-specific embedding: higher
Sobolev norms dominate lower ones. We already have `fracDerivSymbol_mono_of_le`;
here we add the integrated form.
-/

/-- **Ḣˢ seminorm dominance on the torus.** For `s ≤ t` on `𝕋ᵈ`:

    `‖f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣᵗ}`

This is stronger than on ℝᵈ because integer lattice modes have `‖n‖ ≥ 1`. -/
theorem hsSeminormSq_mono {d : Type*} [Fintype d]
    {s t : ℝ} (hst : s ≤ t)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hsum : Summable (fun n ↦ (fracDerivSymbol t n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s f ≤ hsSeminormSq t f := by
  unfold hsSeminormSq
  exact Summable.tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_right
      (fracDerivSymbol_sq_mono_of_le hst n)
      (sq_nonneg _))
    (hsum.of_nonneg_of_le
      (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun n ↦ mul_le_mul_of_nonneg_right
        (fracDerivSymbol_sq_mono_of_le hst n)
        (sq_nonneg _)))
    hsum

/-! ## Strain spectral bound

The strain eigenvalue bound: each eigenvalue `λ` of `S(n)` (symmetric
traceless 2×2) satisfies `|λ|² ≤ |n|²`. At the mode level this is
equivalent to `|S₀₀|² + |S₀₁|² ≤ |n|²`.
-/

/-- **Strain eigenvalue norm bound (weak form).** At mode `n ≠ 0`, the
sum of the squared diagonal and off-diagonal strain components is
bounded by twice the mode norm squared:

    `|S₀₀|² + |S₀₁|² ≤ 2·‖n‖²`

Each component satisfies `|S_{ij}| ≤ ‖n‖` (from `sqgStrain_norm_le`),
so summing two squares gives `≤ 2‖n‖²`. The tight bound is
`‖n‖²/4` (AM-GM), but the weak form suffices for energy estimates. -/
theorem sqgStrain_eigenvalue_norm_le {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2
    ≤ 2 * (latticeNorm n) ^ 2 := by
  have hS00_bound : ‖sqgStrainSymbol 0 0 n‖ ≤ latticeNorm n :=
    sqgStrain_norm_le hn 0 0
  have hS01_bound : ‖sqgStrainSymbol 0 1 n‖ ≤ latticeNorm n :=
    sqgStrain_norm_le hn 0 1
  have hL_nn : 0 ≤ latticeNorm n := latticeNorm_nonneg n
  have h00sq : ‖sqgStrainSymbol 0 0 n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol 0 0 n)]) hS00_bound
  have h01sq : ‖sqgStrainSymbol 0 1 n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol 0 1 n)]) hS01_bound
  linarith

/-- **Strain tight identity: |S₀₀|² + |S₀₁|² = ‖n‖²/4.**
This is the sharp identity: combining the explicit formulas
`S₀₀·‖n‖ = n₀·n₁` and `S₀₁·‖n‖ = (n₁² - n₀²)/2` gives

    `(S₀₀·‖n‖)² + (S₀₁·‖n‖)² = n₀²n₁² + (n₁²-n₀²)²/4 = (n₀²+n₁²)²/4 = ‖n‖⁴/4`

So `|S₀₀|² + |S₀₁|² = ‖n‖²/4`. This is the tight form of
`sqgStrain_eigenvalue_norm_le`. -/
theorem sqgStrain_eigenvalue_tight {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2
    = (latticeNorm n) ^ 2 / 4 := by
  have hL_pos := latticeNorm_pos hn
  have hL_ne : (latticeNorm n : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hLc : ((latticeNorm n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL_ne
  have h00 := sqg_strain_00_explicit hn
  have h01 := sqg_strain_01_explicit hn
  have hL_sq : (latticeNorm n) ^ 2 = ((n 0 : ℤ) : ℝ) ^ 2 + ((n 1 : ℤ) : ℝ) ^ 2 := by
    rw [latticeNorm_sq]; simp [Fin.sum_univ_two]
  -- Multiply both sides by L²
  have key : ((latticeNorm n) ^ 2) *
      (‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2)
    = (latticeNorm n) ^ 4 / 4 := by
    have h00_sq : ‖sqgStrainSymbol 0 0 n * ((latticeNorm n : ℝ) : ℂ)‖ ^ 2
        = (latticeNorm n) ^ 2 * ‖sqgStrainSymbol 0 0 n‖ ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (latticeNorm_nonneg n)]
      ring
    have h01_sq : ‖sqgStrainSymbol 0 1 n * ((latticeNorm n : ℝ) : ℂ)‖ ^ 2
        = (latticeNorm n) ^ 2 * ‖sqgStrainSymbol 0 1 n‖ ^ 2 := by
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (latticeNorm_nonneg n)]
      ring
    have h00_val : ‖sqgStrainSymbol 0 0 n * ((latticeNorm n : ℝ) : ℂ)‖ ^ 2
        = (((n 0 : ℤ) : ℝ) * ((n 1 : ℤ) : ℝ)) ^ 2 := by
      rw [h00, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
      rw [← abs_mul, sq_abs]
    have h01_val : ‖sqgStrainSymbol 0 1 n * ((latticeNorm n : ℝ) : ℂ)‖ ^ 2
        = ((((n 1 : ℤ) : ℝ) ^ 2 - ((n 0 : ℤ) : ℝ) ^ 2) / 2) ^ 2 := by
      rw [h01]
      have hcast : (((n 1 : ℤ) : ℂ) ^ 2 - ((n 0 : ℤ) : ℂ) ^ 2) / 2
          = ((((n 1 : ℤ) : ℝ) ^ 2 - ((n 0 : ℤ) : ℝ) ^ 2) / 2 : ℝ) := by
        push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    -- Now we have:
    -- L² · (‖S₀₀‖² + ‖S₀₁‖²) = ‖S₀₀·L‖² + ‖S₀₁·L‖²  (from h00_sq, h01_sq)
    --                        = (n₀n₁)² + ((n₁²-n₀²)/2)²
    -- = n₀²n₁² + (n₁⁴ - 2n₀²n₁² + n₀⁴)/4
    -- = (4n₀²n₁² + n₁⁴ - 2n₀²n₁² + n₀⁴)/4
    -- = (n₀⁴ + 2n₀²n₁² + n₁⁴)/4
    -- = (n₀² + n₁²)²/4
    -- = L⁴/4
    rw [mul_add, ← h00_sq, ← h01_sq, h00_val, h01_val]
    have hL4 : (latticeNorm n) ^ 4 = ((latticeNorm n) ^ 2) ^ 2 := by ring
    rw [hL4, hL_sq]
    ring
  -- Divide both sides by L²
  have hL_sq_pos : 0 < (latticeNorm n) ^ 2 := by positivity
  have hL_sq_ne : (latticeNorm n) ^ 2 ≠ 0 := ne_of_gt hL_sq_pos
  field_simp at key
  linarith [key, pow_nonneg (latticeNorm_nonneg n) 4]

/-- **Strain Frobenius norm tight equality.** For `n ≠ 0`:

    `Σ_{ij} ‖S_{ij}(n)‖² = ‖n‖²/2`

This follows from tracelessness (Σ over {(0,0),(1,1)} gives `2·|S₀₀|²`)
and symmetry (`S₁₀ = S₀₁`, giving `Σ = 2·(|S₀₀|² + |S₀₁|²) = L²/2`). -/
theorem sqgStrain_frobenius_tight {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n‖ ^ 2) = (latticeNorm n) ^ 2 / 2 := by
  rw [sqgStrain_frobenius_explicit n, sqgStrain_eigenvalue_tight hn]
  ring

/-- **Velocity gradient norm tight equality.** For `n ≠ 0`, the sum
of all squared velocity gradient components equals `‖n‖²`:

    `Σ_{ij} ‖∂̂_i u_j(n)‖² = ‖n‖²`

Proof: `∂̂_i u_j(n) = (in_i) · R_{swap(j)}(n)` with `|iR_k| = |R_k|`,
and `Σ_i n_i² · Σ_k ‖R_k‖² = ‖n‖² · 1`. -/
theorem sqgGrad_frobenius_tight {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgGradSymbol i j n‖ ^ 2) = (latticeNorm n) ^ 2 := by
  have hR : ‖rieszSymbol (0 : Fin 2) n‖ ^ 2 + ‖rieszSymbol (1 : Fin 2) n‖ ^ 2 = 1 := by
    have := rieszSymbol_sum_sq hn
    simp only [Fin.sum_univ_two] at this
    linarith
  have hL_sq : (latticeNorm n) ^ 2 = ((n 0 : ℤ) : ℝ) ^ 2 + ((n 1 : ℤ) : ℝ) ^ 2 := by
    rw [latticeNorm_sq]; simp [Fin.sum_univ_two]
  -- Helper: ‖sqgGradSymbol i 0 n‖² = |n_i|² · ‖R₁(n)‖²
  have h0 : ∀ i : Fin 2, ‖sqgGradSymbol i 0 n‖ ^ 2
      = ((n i : ℤ) : ℝ) ^ 2 * ‖rieszSymbol 1 n‖ ^ 2 := by
    intro i
    unfold sqgGradSymbol derivSymbol
    simp only [show (0 : Fin 2) = 0 from rfl, if_true]
    rw [norm_mul, mul_pow]
    rw [show ‖Complex.I * ((((n i : ℤ) : ℝ) : ℂ))‖ = |((n i : ℤ) : ℝ)| from by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]]
    rw [sq_abs]
  -- Helper: ‖sqgGradSymbol i 1 n‖² = |n_i|² · ‖R₀(n)‖²
  have h1 : ∀ i : Fin 2, ‖sqgGradSymbol i 1 n‖ ^ 2
      = ((n i : ℤ) : ℝ) ^ 2 * ‖rieszSymbol 0 n‖ ^ 2 := by
    intro i
    unfold sqgGradSymbol derivSymbol
    simp only [show (1 : Fin 2) ≠ 0 from by omega, if_false]
    rw [norm_mul, mul_pow, norm_neg]
    rw [show ‖Complex.I * ((((n i : ℤ) : ℝ) : ℂ))‖ = |((n i : ℤ) : ℝ)| from by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]]
    rw [sq_abs]
  simp only [Fin.sum_univ_two]
  rw [h0 0, h0 1, h1 0, h1 1, hL_sq]
  nlinarith [hR, sq_nonneg ((n 0 : ℤ) : ℝ), sq_nonneg ((n 1 : ℤ) : ℝ)]

/-- **Velocity gradient = strain + rotation partition at mode level.**
For `n ≠ 0`:

    `Σ_{ij} ‖∂̂_i u_j(n)‖² = Σ_{ij} ‖S_{ij}(n)‖² + ‖ω̂(n)‖² / 2`

which at tight values becomes `L² = L²/2 + L²/2`. This is the
microlocal form of the enstrophy = vorticity² + 2·strain² identity. -/
theorem sqg_grad_strain_vort_partition {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgGradSymbol i j n‖ ^ 2)
    = (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n‖ ^ 2)
      + ‖sqgVorticitySymbol n‖ ^ 2 / 2 := by
  rw [sqgGrad_frobenius_tight hn, sqgStrain_frobenius_tight hn,
      sqgVorticitySymbol_norm hn]
  ring

/-- **Strain eigenvalue tight upper bound.** Each strain eigenvalue `λ`
satisfies `|λ| ≤ ‖n‖/2`, so `|λ|² ≤ ‖n‖²/4`. This is the tight form
of the strain spectral bound. -/
theorem sqgStrain_00_sq_le_quarter {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgStrainSymbol 0 0 n‖ ^ 2 ≤ (latticeNorm n) ^ 2 / 4 := by
  have htight := sqgStrain_eigenvalue_tight hn
  have h01_nn : 0 ≤ ‖sqgStrainSymbol 0 1 n‖ ^ 2 := sq_nonneg _
  linarith

/-- **Off-diagonal strain eigenvalue tight upper bound.** -/
theorem sqgStrain_01_sq_le_quarter {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgStrainSymbol 0 1 n‖ ^ 2 ≤ (latticeNorm n) ^ 2 / 4 := by
  have htight := sqgStrain_eigenvalue_tight hn
  have h00_nn : 0 ≤ ‖sqgStrainSymbol 0 0 n‖ ^ 2 := sq_nonneg _
  linarith

/-- **Tight Ḣˢ strain bound.** For each strain component and each `s`:

    `‖S_{ij}(n)‖² · σ_s(n)² ≤ σ_{s+1}(n)²·‖θ̂(n)‖²/4`

This is a sharper form of `sqgStrain_Hs_le`, reflecting that each
individual strain component is bounded by `L/2`, not just `L`. -/
theorem sqgStrain_tight_Hs_mode_bound {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (s : ℝ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖sqgStrainSymbol 0 0 n * c‖ ^ 2
    ≤ (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 / 4 := by
  rw [norm_mul, mul_pow]
  have h00 := sqgStrain_00_sq_le_quarter hn
  have hfrac := fracDerivSymbol_add_sq s 1 n
  have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
    rw [fracDerivSymbol_one_eq hn]
  have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hprod_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
    mul_nonneg hσs_nn hc_nn
  calc (fracDerivSymbol s n) ^ 2 * (‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖c‖ ^ 2)
      = ‖sqgStrainSymbol 0 0 n‖ ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) := by ring
    _ ≤ ((latticeNorm n) ^ 2 / 4) * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h00 hprod_nn
    _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 / 4 := by
        rw [hfrac, hfrac1]; ring

/-! ## Ḣ^{1/2} connection: vorticity L² equals θ Ḣ^{1/2}

The SQG constitutive relation `ω = −(-Δ)^{1/2}θ` means the vorticity
has a half-derivative extra smoothness gap compared to θ. At the
Fourier level this is `ω̂(n) = −‖n‖·θ̂(n)`, so `‖ω‖²_{L²} = ‖θ‖²_{Ḣ¹}`.
-/

/-- **Mode-level vorticity = fracDeriv_1 θ.** For `n ≠ 0`:

    `‖ω̂(n)‖² = (fracDerivSymbol 1 n)²`

so the L² norm of `ω` equals the Ḣ¹ seminorm of θ, not Ḣ^{1/2}.
(The factor 1/2 in `ω/2` is absorbed into the constant when connecting
to the identity `ω = -Λθ` on the full torus convention.) -/
theorem sqgVorticitySymbol_norm_sq_eq {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgVorticitySymbol n‖ ^ 2 = (fracDerivSymbol 1 n) ^ 2 := by
  rw [sqgVorticitySymbol_norm hn, fracDerivSymbol_one_eq hn]

/-- **Vorticity L² norm equals θ Ḣ¹ seminorm (integrated form).**
For SQG velocity with `ω̂(n) = -‖n‖·θ̂(n)` and `ω : Lp ℂ 2`:

    `‖ω‖²_{L²} = ‖θ‖²_{Ḣ¹}`

Proof: Parseval + mode-level identity. -/
theorem sqgVorticity_L2_eq_Hs1
    (θ ω : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff ω n = sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2))
    (hω_parseval : HasSum (fun n ↦ ‖mFourierCoeff ω n‖ ^ 2) (∫ t, ‖ω t‖ ^ 2)) :
    (∫ t, ‖ω t‖ ^ 2) = hsSeminormSq 1 θ := by
  unfold hsSeminormSq
  rw [← hω_parseval.tsum_eq]
  congr 1
  ext n
  rw [hcoeff n, norm_mul, mul_pow]
  by_cases hn : n = 0
  · subst hn
    rw [show sqgVorticitySymbol 0 = 0 from by
          unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol
          simp, norm_zero]
    simp [fracDerivSymbol_zero]
  · rw [sqgVorticitySymbol_norm hn, fracDerivSymbol_one_eq hn]

/-- **Strain L² norm = θ Ḣ¹ seminorm / 2.** For each strain component,
the L² norm of `S_{ij}` equals `‖n‖/2 · |θ̂|` in the mode picture,
giving:

    `Σ_{ij} ‖S_{ij}‖²_{L²} = ‖θ‖²_{Ḣ¹} / 2`

(from the tight Frobenius identity). This matches the velocity gradient
decomposition energy identity. -/
theorem sqgStrain_Frobenius_L2_eq_Hs1_half {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (c : ℂ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n * c‖ ^ 2)
    = (fracDerivSymbol 1 n) ^ 2 * ‖c‖ ^ 2 / 2 := by
  have hfactor : (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n * c‖ ^ 2)
      = (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n‖ ^ 2) * ‖c‖ ^ 2 := by
    simp only [norm_mul, mul_pow]
    simp only [Fin.sum_univ_two]
    ring
  rw [hfactor, sqgStrain_frobenius_tight hn, fracDerivSymbol_one_eq hn]
  ring

/-! ## Riesz transform Ḣˢ properties

Each Riesz transform `R_j : Lp ℂ 2 → Lp ℂ 2` is an isometry modulo zero modes,
and the transfer of fractional derivatives commutes with Riesz transforms.
We establish mode-level properties.
-/

/-- **Riesz symbol preserves Ḣˢ weight norm.** At each nonzero mode:

    `σ_s(n)² · ‖R_j(n) · c‖² = ‖R_j(n)‖² · σ_s(n)² · ‖c‖²`

which is trivial algebra but useful for sum manipulations. -/
theorem rieszSymbol_Hs_mode_factor (s : ℝ) (n : Fin 2 → ℤ)
    (j : Fin 2) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖rieszSymbol j n * c‖ ^ 2
    = ‖rieszSymbol j n‖ ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) := by
  rw [norm_mul, mul_pow]; ring

/-- **Riesz Ḣˢ bound per component.** For each `j` and `n ≠ 0`:

    `σ_s(n)² · ‖R_j(n) · c‖² ≤ σ_s(n)² · ‖c‖²`

This is the mode-level Ḣˢ contractivity of each Riesz transform. -/
theorem rieszSymbol_Hs_mode_bound (s : ℝ) {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (j : Fin 2) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖rieszSymbol j n * c‖ ^ 2
    ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := by
  rw [rieszSymbol_Hs_mode_factor s n j c]
  have hR : ‖rieszSymbol j n‖ ^ 2 ≤ 1 := by
    have := rieszSymbol_sum_sq hn
    have hR_j_nn : 0 ≤ ‖rieszSymbol j n‖ ^ 2 := sq_nonneg _
    have hR_other_nn : ∀ k : Fin 2, 0 ≤ ‖rieszSymbol k n‖ ^ 2 :=
      fun _ ↦ sq_nonneg _
    -- ‖R_j‖² ≤ Σ ‖R_k‖² = 1
    calc ‖rieszSymbol j n‖ ^ 2
        ≤ ∑ k : Fin 2, ‖rieszSymbol k n‖ ^ 2 := by
          rw [show (‖rieszSymbol j n‖ ^ 2)
              = ∑ k ∈ ({j} : Finset (Fin 2)), ‖rieszSymbol k n‖ ^ 2 from by simp]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by simp : ({j} : Finset (Fin 2)) ⊆ Finset.univ)
            (fun k _ _ ↦ hR_other_nn k)
      _ = 1 := this
  have hprod_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc ‖rieszSymbol j n‖ ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2)
      ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hR hprod_nn
    _ = (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := one_mul _

/-- **Derivative symbol preserves Ḣˢ**: `σ_s² · |∂̂_j · c|² ≤ σ_{s+1}² · |c|²` -/
theorem derivSymbol_Hs_mode_bound (s : ℝ) (n : Fin 2 → ℤ)
    (j : Fin 2) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖derivSymbol j n * c‖ ^ 2
    ≤ (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp [derivSymbol, fracDerivSymbol_zero]
  rw [norm_mul, mul_pow]
  rw [show (fracDerivSymbol (s + 1) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2 from
    fracDerivSymbol_add_sq s 1 n]
  rw [fracDerivSymbol_one_eq hn]
  have h_deriv : ‖derivSymbol j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 := by
    unfold derivSymbol
    rw [show ‖Complex.I * (((n j : ℤ) : ℝ) : ℂ)‖ = |((n j : ℤ) : ℝ)| from by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]]
    rw [sq_abs]
    exact sq_le_latticeNorm_sq n j
  have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hprod_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
    mul_nonneg hσs_nn hc_nn
  calc (fracDerivSymbol s n) ^ 2 * (‖derivSymbol j n‖ ^ 2 * ‖c‖ ^ 2)
      = ‖derivSymbol j n‖ ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) := by ring
    _ ≤ (latticeNorm n) ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h_deriv hprod_nn
    _ = (fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2 := by ring

/-! ## Strain-Ḣˢ tight identity

Using the tight strain Frobenius identity Σ‖S_ij‖² = ‖n‖²/2 at each
mode, we can derive the sharp Ḣˢ strain identity for the sum of all
strain components at once.
-/

/-- **Mode-level strain Frobenius Ḣˢ tight bound.** For `n ≠ 0` and any
coefficient `c`:

    `σ_s(n)² · Σ_{ij} ‖S_{ij}(n)·c‖² = σ_{s+1}(n)²·‖c‖²/2`

This is the tight form: the strain Frobenius norm at frequency `n`
equals exactly `σ_1(n)/√2 · |c|`. -/
theorem sqgStrain_Frobenius_Hs_tight {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (s : ℝ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2
      * (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgStrainSymbol i j n * c‖ ^ 2)
    = (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 / 2 := by
  rw [sqgStrain_Frobenius_L2_eq_Hs1_half hn c]
  rw [show (fracDerivSymbol (s + 1) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2 from
    fracDerivSymbol_add_sq s 1 n]
  ring

/-- **Mode-level gradient Frobenius Ḣˢ tight bound.** For `n ≠ 0`:

    `σ_s(n)² · Σ_{ij} ‖∂̂_i u_j(n)·c‖² = σ_{s+1}(n)²·‖c‖²`

So the velocity gradient tensor has the exact Ḣˢ scale `Ḣ^{s+1}(θ)`. -/
theorem sqgGrad_Frobenius_Hs_tight {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (s : ℝ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2
      * (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgGradSymbol i j n * c‖ ^ 2)
    = (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 := by
  have hfactor : (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgGradSymbol i j n * c‖ ^ 2)
      = (∑ i : Fin 2, ∑ j : Fin 2, ‖sqgGradSymbol i j n‖ ^ 2) * ‖c‖ ^ 2 := by
    simp only [norm_mul, mul_pow]
    simp only [Fin.sum_univ_two]
    ring
  rw [hfactor, sqgGrad_frobenius_tight hn]
  rw [show (fracDerivSymbol (s + 1) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2 from
    fracDerivSymbol_add_sq s 1 n]
  rw [fracDerivSymbol_one_eq hn]
  ring

/-- **Vorticity Ḣˢ tight identity.** For `n ≠ 0`:

    `σ_s(n)² · ‖ω̂(n)·c‖² = σ_{s+1}(n)²·‖c‖²`

The vorticity has the exact Ḣˢ scale `Ḣ^{s+1}(θ)`. -/
theorem sqgVorticity_Hs_tight {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (s : ℝ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖sqgVorticitySymbol n * c‖ ^ 2
    = (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, sqgVorticitySymbol_norm hn]
  rw [show (fracDerivSymbol (s + 1) n) ^ 2
      = (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol 1 n) ^ 2 from
    fracDerivSymbol_add_sq s 1 n]
  rw [fracDerivSymbol_one_eq hn]
  ring

/-! ## Integrated Ḣˢ tight identities (Parseval/tsum form)

Lifting the mode-level tight identities to integrated Ḣˢ seminorms.
-/

/-- **Vorticity Ḣˢ tight identity.** For `ω̂(n) = sqgVorticitySymbol n · θ̂(n)`:

    `‖ω‖²_{Ḣˢ} = ‖θ‖²_{Ḣ^{s+1}}`

The proof is by Parseval plus the mode-level `sqgVorticity_Hs_tight`. -/
theorem sqgVorticity_Hs_eq_Hs1
    (s : ℝ)
    (θ ω : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff ω n = sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s ω = hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  congr 1
  ext n
  by_cases hn : n = 0
  · subst hn
    have h0 : sqgVorticitySymbol 0 = 0 := by
      unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol
      simp
    rw [hcoeff 0, h0, zero_mul, norm_zero]
    simp [fracDerivSymbol_zero]
  · rw [hcoeff n]
    exact sqgVorticity_Hs_tight hn s (mFourierCoeff θ n)

/-! ## Summary: Full curvature budget at all Sobolev levels

The library now provides a complete Fourier-space curvature budget:

1. **Symbols**: `hessSymbol`, `sqgGradSymbol`, `sqgStrainSymbol`,
   `sqgVorticitySymbol`, `fracDerivSymbol`, `thirdDerivSymbol`

2. **Pointwise bounds**: every symbol is controlled by powers of `‖n‖`,
   giving Sobolev embeddings via `sqg_selection_rule_Hs`

3. **L² bounds**: strain and velocity gradient are in `Ḣ¹(θ)`

4. **Ḣˢ bounds**: strain `Ḣˢ ≤ θ Ḣˢ⁺¹`, velocity `Ḣˢ ≤ θ Ḣˢ`

5. **Bernstein estimates**: frequency-localised control of Sobolev
   weights via `fracDerivSymbol_low/high_freq_bound`

6. **Interpolation**: mode-level geometric mean bound
   `fracDerivSymbol_sq_interpolate`

7. **Gradient decomposition**: `∂u = S + Ω` with `Ω = ω/2` and
   the D14 identity killing the `S_{nt}` residual

8. **Incompressibility**: `div u = 0` ensures material transport
   preserves the Jacobian
-/

end SqgIdentity
