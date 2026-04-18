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
  exact h

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
  · simp only [show (1 : Fin 2) ≠ 0 from by omega,
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
  simp only [if_true]
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
  simp only [show (1 : Fin 2) ≠ 0 from by omega,
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
theorem sqgGrad_norm_le {n : Fin 2 → ℤ} (_hn : n ≠ 0) (i j : Fin 2) :
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
    {t u α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (_htu : t ≤ u)
    (n : d → ℤ) :
    (fracDerivSymbol ((1 - α) * t + α * u) n) ^ 2 =
    ((fracDerivSymbol t n) ^ 2) ^ (1 - α) *
    ((fracDerivSymbol u n) ^ 2) ^ α := by
  by_cases hn : n = 0
  · simp [hn, fracDerivSymbol_zero]
    rcases eq_or_lt_of_le hα0 with rfl | hα_pos
    · simp
    · exact Or.inr (Real.zero_rpow hα_pos.ne')
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

    `sqgGradSymbol 0 1 n = sqgStrainSymbol 0 1 n + sqgVorticitySymbol n / 2` -/
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
    simp only [if_true]
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
    (_hsum : Summable
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
    (_hsum : Summable (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
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

/-- **Strain 0,0 component Ḣˢ tight bound (integrated).** The (0,0)
component of the strain matrix satisfies:

    `‖S₀₀‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}} / 4`

This is 4× sharper than `sqgStrain_Hs_le` (which gives ≤ ‖θ‖²_{Ḣ^{s+1}}).
The factor 1/4 comes from the tight eigenvalue bound `|S₀₀|² ≤ ‖n‖²/4`. -/
theorem sqgStrain_00_Hs_le_quarter
    (s : ℝ)
    (θ S : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff S n = sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s S ≤ hsSeminormSq (s + 1) θ / 4 := by
  unfold hsSeminormSq
  rw [show (∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2) / 4
      = ∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 from by
    rw [← tsum_div_const]]
  apply Summable.tsum_le_tsum (f := fun n ↦
    fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S) n‖ ^ 2)
  · intro n
    by_cases hn : n = 0
    · subst hn
      rw [hcoeff 0]
      simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
        fracDerivSymbol_zero]
    · rw [hcoeff n]
      have := sqgStrain_tight_Hs_mode_bound hn s (mFourierCoeff θ n)
      convert this using 1
  · apply (hsum.div_const 4).of_nonneg_of_le
    · intro n
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      by_cases hn : n = 0
      · subst hn
        rw [hcoeff 0]
        simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
          fracDerivSymbol_zero]
      · rw [hcoeff n]
        have := sqgStrain_tight_Hs_mode_bound hn s (mFourierCoeff θ n)
        convert this using 1
  · exact hsum.div_const 4

/-- **Strain 0,1 component tight Ḣˢ mode bound.** -/
theorem sqgStrain_01_tight_Hs_mode_bound {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (s : ℝ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖sqgStrainSymbol 0 1 n * c‖ ^ 2
    ≤ (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 / 4 := by
  rw [norm_mul, mul_pow]
  have h01 := sqgStrain_01_sq_le_quarter hn
  have hfrac := fracDerivSymbol_add_sq s 1 n
  have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
    rw [fracDerivSymbol_one_eq hn]
  have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hprod_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
    mul_nonneg hσs_nn hc_nn
  calc (fracDerivSymbol s n) ^ 2 * (‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖c‖ ^ 2)
      = ‖sqgStrainSymbol 0 1 n‖ ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) := by ring
    _ ≤ ((latticeNorm n) ^ 2 / 4) * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h01 hprod_nn
    _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖c‖ ^ 2 / 4 := by
        rw [hfrac, hfrac1]; ring

/-- **Strain 0,1 component Ḣˢ tight bound (integrated).** -/
theorem sqgStrain_01_Hs_le_quarter
    (s : ℝ)
    (θ S : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff S n = sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s S ≤ hsSeminormSq (s + 1) θ / 4 := by
  unfold hsSeminormSq
  rw [show (∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2) / 4
      = ∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 from by
    rw [← tsum_div_const]]
  apply Summable.tsum_le_tsum (f := fun n ↦
    fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S) n‖ ^ 2)
  · intro n
    by_cases hn : n = 0
    · subst hn
      rw [hcoeff 0]
      simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
        fracDerivSymbol_zero]
    · rw [hcoeff n]
      exact sqgStrain_01_tight_Hs_mode_bound hn s (mFourierCoeff θ n)
  · apply (hsum.div_const 4).of_nonneg_of_le
    · intro n
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      by_cases hn : n = 0
      · subst hn
        rw [hcoeff 0]
        simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
          fracDerivSymbol_zero]
      · rw [hcoeff n]
        exact sqgStrain_01_tight_Hs_mode_bound hn s (mFourierCoeff θ n)
  · exact hsum.div_const 4

/-! ## Heat semigroup symbol

The heat equation `∂_t u = Δ u` has semigroup `e^{tΔ}` with Fourier
multiplier `e^{-t·‖n‖²}`. This is always in (0, 1], and represents
parabolic smoothing.

The fractional heat `e^{-t(-Δ)^α}` (for SQG's diffusion-free setting,
with α = 0 here) has symbol `e^{-t·‖n‖^{2α}}`.
-/

/-- **Heat semigroup symbol.** For `t ≥ 0`:

    `ê_tΔ(n) = exp(-t·‖n‖²)`. -/
noncomputable def heatSymbol {d : Type*} [Fintype d]
    (t : ℝ) (n : d → ℤ) : ℝ :=
  Real.exp (-t * (latticeNorm n) ^ 2)

/-- **Heat semigroup symbol at n = 0 is 1.** -/
@[simp] lemma heatSymbol_zero_mode {d : Type*} [Fintype d] (t : ℝ) :
    heatSymbol t (0 : d → ℤ) = 1 := by
  unfold heatSymbol
  simp [latticeNorm]

/-- **Heat semigroup symbol is positive.** -/
lemma heatSymbol_pos {d : Type*} [Fintype d] (t : ℝ) (n : d → ℤ) :
    0 < heatSymbol t n := Real.exp_pos _

/-- **Heat semigroup symbol is nonneg.** -/
lemma heatSymbol_nonneg {d : Type*} [Fintype d] (t : ℝ) (n : d → ℤ) :
    0 ≤ heatSymbol t n := le_of_lt (heatSymbol_pos t n)

/-- **Heat semigroup at t=0 is identity.** -/
@[simp] lemma heatSymbol_zero_time {d : Type*} [Fintype d] (n : d → ℤ) :
    heatSymbol 0 n = 1 := by
  unfold heatSymbol
  simp

/-- **Heat semigroup is bounded by 1 for t ≥ 0.** -/
lemma heatSymbol_le_one {d : Type*} [Fintype d] {t : ℝ} (ht : 0 ≤ t)
    (n : d → ℤ) :
    heatSymbol t n ≤ 1 := by
  unfold heatSymbol
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  apply Real.exp_le_exp.mpr
  have hL_sq_nn : 0 ≤ (latticeNorm n) ^ 2 := sq_nonneg _
  nlinarith

/-- **Heat semigroup is strictly below 1 at nonzero modes for t > 0.** -/
lemma heatSymbol_lt_one {d : Type*} [Fintype d] {t : ℝ} (ht : 0 < t)
    {n : d → ℤ} (hn : n ≠ 0) :
    heatSymbol t n < 1 := by
  unfold heatSymbol
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  apply Real.exp_lt_exp.mpr
  have hL_pos : 0 < latticeNorm n := latticeNorm_pos hn
  have hL_sq_pos : 0 < (latticeNorm n) ^ 2 := by positivity
  nlinarith

/-- **Heat semigroup: additive in time (homomorphism).** -/
lemma heatSymbol_add {d : Type*} [Fintype d] (t₁ t₂ : ℝ) (n : d → ℤ) :
    heatSymbol (t₁ + t₂) n = heatSymbol t₁ n * heatSymbol t₂ n := by
  unfold heatSymbol
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Heat semigroup Ḣˢ mode contractivity.** For `t ≥ 0`:

    `σ_s(n)² · ‖(e^{tΔ})̂(n) · c‖² ≤ σ_s(n)² · ‖c‖²`

Parabolic smoothing is a contraction at every Sobolev level. -/
theorem heatSymbol_Hs_mode_bound {t : ℝ} (ht : 0 ≤ t) (s : ℝ)
    {n : (Fin 2) → ℤ} (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg _ _)]
  have hh_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hh_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
  have hh_sq_le : (heatSymbol t n) ^ 2 ≤ 1 := pow_le_one₀ hh_nn hh_le
  have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hprod_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
    mul_nonneg hσs_nn hc_nn
  calc (fracDerivSymbol s n) ^ 2 * ((heatSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = (heatSymbol t n) ^ 2 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) := by ring
    _ ≤ 1 * ((fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hh_sq_le hprod_nn
    _ = (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := one_mul _

/-! ## Parabolic smoothing at the k=1 level

Classical parabolic smoothing: `‖n‖² · exp(-t·‖n‖²) ≤ 1/(et)`.
This is the gradient-level smoothing provided by the heat semigroup.

The key is the tangent-line inequality: `x · exp(-x) ≤ exp(-1)`
(classical; max at `x = 1`).
-/

/-- **Tangent-line inequality at `x = 1`.** `x · exp(-x) ≤ exp(-1)`
for all real `x`.

At `x = 1` this is equality. Both `x · exp(-x)` and `exp(-1)` tangent
each other at `x = 1` and the convex-below-concave argument gives
`≤`. Equivalently: `ex ≤ exp(x)`, which is the tangent line inequality
for `exp` at `x = 1`. -/
theorem mul_exp_neg_le_exp_neg_one (x : ℝ) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  by_cases hx : 0 ≤ x
  · -- x ≥ 0: use x ≤ exp(x-1) (tangent line at x=1)
    have h1 : x ≤ Real.exp (x - 1) := by
      have := Real.add_one_le_exp (x - 1)
      linarith
    have hexp_neg_pos : 0 < Real.exp (-x) := Real.exp_pos _
    calc x * Real.exp (-x)
        ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right h1 hexp_neg_pos.le
      _ = Real.exp ((x - 1) + (-x)) := (Real.exp_add _ _).symm
      _ = Real.exp (-1) := by
          congr 1; ring
  · -- x < 0: x · exp(-x) < 0 ≤ exp(-1)
    push Not at hx
    have hexp_neg_pos : 0 < Real.exp (-x) := Real.exp_pos _
    have hneg : x * Real.exp (-x) < 0 := mul_neg_of_neg_of_pos hx hexp_neg_pos
    have hpos : 0 < Real.exp (-1) := Real.exp_pos _
    linarith

/-- **Parabolic smoothing bound at gradient level.** For `t > 0`:

    `‖n‖² · exp(-t·‖n‖²) ≤ exp(-1) / t`

This is the mode-level statement of the heat-semigroup smoothing estimate
`‖∇(e^{tΔ}f)‖_L² ≤ C/√t · ‖f‖_L²` at frequency `n`. -/
theorem latticeNorm_sq_mul_heat_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ 2 * heatSymbol t n ≤ Real.exp (-1) / t := by
  unfold heatSymbol
  -- Goal: L² · exp(-t·L²) ≤ exp(-1)/t
  -- Let y = t·L². Then L² = y/t and exp(-t·L²) = exp(-y).
  -- So LHS = (y/t) · exp(-y) = y·exp(-y) / t ≤ exp(-1)/t.
  set y : ℝ := t * (latticeNorm n) ^ 2 with hy_def
  have hy_nn : 0 ≤ y := mul_nonneg ht.le (sq_nonneg _)
  have hexp_rw : Real.exp (-t * (latticeNorm n) ^ 2) = Real.exp (-y) := by
    congr 1; rw [hy_def]; ring
  rw [hexp_rw]
  -- Now: L² · exp(-y) ≤ exp(-1)/t, with y = t·L²
  have hL_sq_eq : (latticeNorm n) ^ 2 = y / t := by
    rw [hy_def]; field_simp
  rw [hL_sq_eq, div_mul_eq_mul_div]
  -- Goal: y * exp(-y) / t ≤ exp(-1) / t
  have h_num : y * Real.exp (-y) ≤ Real.exp (-1) := mul_exp_neg_le_exp_neg_one y
  gcongr

/-- **Parabolic smoothing: fracDerivSymbol 1 form.** For `t > 0`:

    `σ_1(n)² · heatSymbol(t, n) ≤ exp(-1) / t`. -/
theorem fracDerivSymbol_1_sq_mul_heat_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol 1 n) ^ 2 * heatSymbol t n ≤ Real.exp (-1) / t := by
  by_cases hn : n = 0
  · subst hn
    have : (fracDerivSymbol 1 (0 : Fin 2 → ℤ)) = 0 := fracDerivSymbol_zero 1
    rw [this]
    simp
    exact div_nonneg (Real.exp_pos _).le ht.le
  · rw [fracDerivSymbol_one_eq hn]
    exact latticeNorm_sq_mul_heat_le ht n

/-- **Parabolic smoothing in `Ḣ¹` form.** For `t > 0`, the heat-smoothed
function has gradient bounded by `1/(et)` times its L² norm at each mode:

    `σ_1(n)² · ‖(heatSymbol t n) · c‖² ≤ (exp(-1) / t) · ‖c‖²`

This is the mode-level form of the classical `‖∇(e^{tΔ}f)‖_{L²} ≤
(et)^{-1/2} · ‖f‖_{L²}` estimate (squared). -/
theorem heatSymbol_grad_smoothing_mode {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol 1 n) ^ 2 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (heatSymbol_nonneg t n)]
  have hmain := fracDerivSymbol_1_sq_mul_heat_le ht n
  -- Need: σ_1² · heat² · ‖c‖² ≤ (e^{-1}/t) · ‖c‖²
  -- Have:  σ_1² · heat   ≤ e^{-1}/t
  -- So σ_1² · heat² = (σ_1² · heat) · heat ≤ (e^{-1}/t) · heat ≤ (e^{-1}/t) · 1
  have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
  have hσ_nn : 0 ≤ (fracDerivSymbol 1 n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ Real.exp (-1) / t :=
    div_nonneg (Real.exp_pos _).le ht.le
  calc (fracDerivSymbol 1 n) ^ 2 * ((heatSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol 1 n) ^ 2 * heatSymbol t n)
        * (heatSymbol t n * ‖c‖ ^ 2) := by ring
    _ ≤ (Real.exp (-1) / t) * (heatSymbol t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hheat_nn hc_nn)
    _ ≤ (Real.exp (-1) / t) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hheat_le_one hc_nn
    _ = (Real.exp (-1) / t) * ‖c‖ ^ 2 := by ring

/-! ## Parabolic smoothing at Hessian level (k=2)

Bootstrap from the k=1 case: apply the k=1 bound at time `t/2`,
square both sides, and use `exp(a) · exp(a) = exp(2a)` to get the
`k=2` bound `‖n‖^4 · exp(-t‖n‖²) ≤ 4·exp(-2)/t²`.
-/

/-- **Parabolic smoothing at Hessian level.** For `t > 0`:

    `‖n‖^4 · exp(-t·‖n‖²) ≤ 4·exp(-2)/t²`

The max of `y² · exp(-y)` is `4/e²` at `y = 2`. -/
theorem latticeNorm_4_mul_heat_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ 4 * heatSymbol t n
      ≤ 4 * Real.exp (-2) / t ^ 2 := by
  -- Use k=1 bound at time t/2: L² · exp(-(t/2)L²) ≤ exp(-1)/(t/2) = 2·exp(-1)/t
  have ht_half : 0 < t / 2 := half_pos ht
  have h := latticeNorm_sq_mul_heat_le ht_half n
  -- h: L² · heatSymbol (t/2) n ≤ exp(-1) / (t/2)
  -- i.e., L² · exp(-(t/2)·L²) ≤ 2·exp(-1)/t
  have hL_sq_nn : 0 ≤ (latticeNorm n) ^ 2 := sq_nonneg _
  have hheat_nn : 0 ≤ heatSymbol (t/2) n := heatSymbol_nonneg _ _
  have hprod_nn : 0 ≤ (latticeNorm n) ^ 2 * heatSymbol (t/2) n :=
    mul_nonneg hL_sq_nn hheat_nn
  have hrhs_nn : 0 ≤ Real.exp (-1) / (t / 2) :=
    div_nonneg (Real.exp_pos _).le ht_half.le
  -- Square both sides of h:
  -- (L² · heat(t/2))² ≤ (exp(-1)/(t/2))²
  -- LHS = L^4 · heat(t/2)² = L^4 · heat(t)  (since heat(t/2)² = heat(t))
  -- RHS = (exp(-1))² / (t/2)² = exp(-2) / (t²/4) = 4·exp(-2)/t²
  have hsq : ((latticeNorm n) ^ 2 * heatSymbol (t/2) n) ^ 2
          ≤ (Real.exp (-1) / (t / 2)) ^ 2 := by
    exact sq_le_sq' (by linarith [hprod_nn, hrhs_nn]) h
  -- Simplify LHS: (L² · heat(t/2))² = L^4 · heat(t/2)² = L^4 · heat(t)
  have h_lhs_eq : ((latticeNorm n) ^ 2 * heatSymbol (t/2) n) ^ 2
      = (latticeNorm n) ^ 4 * heatSymbol t n := by
    rw [mul_pow]
    congr 1
    · ring
    · -- heatSymbol (t/2) n ^ 2 = heatSymbol t n
      unfold heatSymbol
      rw [sq, ← Real.exp_add]
      congr 1; ring
  -- Simplify RHS: (exp(-1)/(t/2))² = 4·exp(-2)/t²
  have h_rhs_eq : (Real.exp (-1) / (t / 2)) ^ 2 = 4 * Real.exp (-2) / t ^ 2 := by
    rw [div_pow]
    have hexp_sq : (Real.exp (-1)) ^ 2 = Real.exp (-2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hexp_sq]
    have ht_ne : t ≠ 0 := ht.ne'
    field_simp
    ring
  rw [h_lhs_eq] at hsq
  rw [h_rhs_eq] at hsq
  exact hsq

/-- **Parabolic smoothing: fracDerivSymbol 2 form.** For `t > 0`:

    `σ_2(n)² · heat(t, n) ≤ 4·exp(-2)/t²`. -/
theorem fracDerivSymbol_2_sq_mul_heat_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol 2 n) ^ 2 * heatSymbol t n
      ≤ 4 * Real.exp (-2) / t ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : (fracDerivSymbol 2 (0 : Fin 2 → ℤ)) = 0 := fracDerivSymbol_zero 2
    rw [this]
    simp
    positivity
  · -- σ_2(n)² = L^4
    have h_σ2_sq : (fracDerivSymbol 2 n) ^ 2 = (latticeNorm n) ^ 4 := by
      rw [fracDerivSymbol_of_ne_zero 2 hn]
      have hL_nn : 0 ≤ latticeNorm n := latticeNorm_nonneg n
      rw [show ((latticeNorm n) ^ (2 : ℝ)) ^ 2
          = latticeNorm n ^ (2 * 2 : ℝ) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_nn]; norm_num]
      rw [show ((2 : ℝ) * 2) = (4 : ℕ) from by norm_num]
      rw [Real.rpow_natCast]
    rw [h_σ2_sq]
    exact latticeNorm_4_mul_heat_le ht n

/-- **Parabolic smoothing in `Ḣ²` form.** For `t > 0`, the heat-smoothed
function has Hessian bounded by `4·exp(-2)/t²` times its L² norm at each mode:

    `σ_2(n)² · ‖(heatSymbol t n) · c‖² ≤ (4·exp(-2) / t²) · ‖c‖²`

This is the mode-level form of the classical `‖Δ(e^{tΔ}f)‖_{L²} ≤
(2/(et)) · ‖f‖_{L²}` estimate (squared). -/
theorem heatSymbol_hess_smoothing_mode {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol 2 n) ^ 2 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (4 * Real.exp (-2) / t ^ 2) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (heatSymbol_nonneg t n)]
  have hmain := fracDerivSymbol_2_sq_mul_heat_le ht n
  have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
  have hσ_nn : 0 ≤ (fracDerivSymbol 2 n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ 4 * Real.exp (-2) / t ^ 2 := by positivity
  calc (fracDerivSymbol 2 n) ^ 2 * ((heatSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol 2 n) ^ 2 * heatSymbol t n)
        * (heatSymbol t n * ‖c‖ ^ 2) := by ring
    _ ≤ (4 * Real.exp (-2) / t ^ 2) * (heatSymbol t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hheat_nn hc_nn)
    _ ≤ (4 * Real.exp (-2) / t ^ 2) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hheat_le_one hc_nn
    _ = (4 * Real.exp (-2) / t ^ 2) * ‖c‖ ^ 2 := by ring

/-! ## Parabolic smoothing: applications to SQG velocity/vorticity

Combining the heat-semigroup smoothing with SQG velocity/vorticity
structure: the heat-smoothed SQG velocity gradient is controlled in
terms of `L²(θ)` at a rate `1/(et)`.
-/

/-- **SQG vorticity parabolic smoothing.** Heat-smoothed SQG vorticity
satisfies `‖ω̂(n) · heat(t,n) · c‖² ≤ exp(-1)/t · ‖c‖²` for each mode
`n ≠ 0`.

Proof: `‖ω̂·heat·c‖² = L²·heat²·‖c‖²`. Using `heat ≤ 1` gives
`heat² ≤ heat`, so `L²·heat²·‖c‖² ≤ L²·heat·‖c‖² ≤ exp(-1)/t·‖c‖²`. -/
theorem sqgVorticity_heat_smoothing_mode {t : ℝ} (ht : 0 < t)
    {n : Fin 2 → ℤ} (hn : n ≠ 0) (c : ℂ) :
    ‖sqgVorticitySymbol n * ((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
  -- ‖ω̂ · heat · c‖² = L² · heat² · ‖c‖²
  have hnorm : ‖sqgVorticitySymbol n * ((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
      = (latticeNorm n) ^ 2 * (heatSymbol t n) ^ 2 * ‖c‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow, sqgVorticitySymbol_norm hn,
      Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg t n)]
  rw [hnorm]
  -- Goal: L² · heat² · ‖c‖² ≤ exp(-1)/t · ‖c‖²
  -- Use heat² ≤ heat · 1 = heat (since heat ≤ 1)
  have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
  have hL_sq_nn : 0 ≤ (latticeNorm n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hmain : (latticeNorm n) ^ 2 * heatSymbol t n ≤ Real.exp (-1) / t :=
    latticeNorm_sq_mul_heat_le ht n
  calc (latticeNorm n) ^ 2 * (heatSymbol t n) ^ 2 * ‖c‖ ^ 2
      = ((latticeNorm n) ^ 2 * heatSymbol t n) * heatSymbol t n * ‖c‖ ^ 2 := by
        rw [sq]; ring
    _ ≤ (Real.exp (-1) / t) * heatSymbol t n * ‖c‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hc_nn
        exact mul_le_mul_of_nonneg_right hmain hheat_nn
    _ ≤ (Real.exp (-1) / t) * 1 * ‖c‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hc_nn
        apply mul_le_mul_of_nonneg_left hheat_le_one
        exact div_nonneg (Real.exp_pos _).le ht.le
    _ = (Real.exp (-1) / t) * ‖c‖ ^ 2 := by ring

/-! ## General parabolic smoothing at arbitrary k ∈ ℕ

Bootstrap from `k=1` at time `t/k`, then raise to the k-th power.
The key identity is `heat(t) = (heat(t/k))^k`, which lets us rewrite:

    L^{2k} · heat(t) = (L² · heat(t/k))^k ≤ (k·exp(-1)/t)^k = k^k·exp(-k)/t^k

giving the general smoothing bound.
-/

/-- **Heat semigroup and powers of time.** For `k ≥ 1`:

    `heatSymbol t n = (heatSymbol (t/k) n)^k`. -/
theorem heatSymbol_pow_eq {t : ℝ} (n : Fin 2 → ℤ) {k : ℕ} (hk : k ≠ 0) :
    heatSymbol t n = (heatSymbol (t / k) n) ^ k := by
  unfold heatSymbol
  rw [← Real.exp_nat_mul]
  congr 1
  have hk_real : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

/-- **General parabolic smoothing at integer k.** For `k ≥ 1`, `t > 0`:

    `‖n‖^{2k} · exp(-t‖n‖²) ≤ k^k · exp(-k) / t^k`

The max of `y^k · exp(-y)` for `y ≥ 0` is achieved at `y = k`, with
value `(k/e)^k = k^k · exp(-k)`. -/
theorem latticeNorm_pow_mul_heat_le {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ (2 * k) * heatSymbol t n
    ≤ (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k := by
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have ht_k : 0 < t / k := div_pos ht hk_pos
  have hbase := latticeNorm_sq_mul_heat_le ht_k n
  -- hbase: L² · heat(t/k) ≤ exp(-1) / (t/k)
  have hbase_nn : 0 ≤ (latticeNorm n) ^ 2 * heatSymbol (t/k) n :=
    mul_nonneg (sq_nonneg _) (heatSymbol_nonneg _ _)
  have hbound_nn : 0 ≤ Real.exp (-1) / (t / k) :=
    div_nonneg (Real.exp_pos _).le ht_k.le
  -- Raise both sides to k-th power
  have hpow : ((latticeNorm n) ^ 2 * heatSymbol (t/k) n) ^ k
            ≤ (Real.exp (-1) / (t / k)) ^ k := by
    gcongr
  -- Rewrite LHS as L^{2k} · heat(t)
  have hLHS_eq : ((latticeNorm n) ^ 2 * heatSymbol (t/k) n) ^ k
      = (latticeNorm n) ^ (2 * k) * heatSymbol t n := by
    rw [mul_pow, ← pow_mul, ← heatSymbol_pow_eq n hk]
  -- Rewrite RHS: (exp(-1)/(t/k))^k = (k·exp(-1)/t)^k = k^k · exp(-k) / t^k
  have hRHS_eq : (Real.exp (-1) / (t / k)) ^ k
      = (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k := by
    have ht_ne : t ≠ 0 := ht.ne'
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    have hrew : Real.exp (-1) / (t / k) = (k : ℝ) * Real.exp (-1) / t := by
      field_simp
    rw [hrew, div_pow, mul_pow]
    have hexp : (Real.exp (-1)) ^ k = Real.exp (-(k : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
  rw [hLHS_eq] at hpow
  rw [hRHS_eq] at hpow
  exact hpow

/-- **General parabolic smoothing at fracDerivSymbol level.** For `k ≥ 1`:

    `σ_k(n)² · heat(t, n) ≤ k^k · exp(-k) / t^k`

where `σ_k(n)²` denotes the squared `k`-th fractional derivative symbol
(which equals `‖n‖^{2k}` for `n ≠ 0`). -/
theorem fracDerivSymbol_nat_sq_mul_heat_le {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol (k : ℝ) n) ^ 2 * heatSymbol t n
    ≤ (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k := by
  by_cases hn : n = 0
  · subst hn
    rw [fracDerivSymbol_zero]
    simp
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  · have h_σk_sq : (fracDerivSymbol (k : ℝ) n) ^ 2 = (latticeNorm n) ^ (2 * k) := by
      rw [fracDerivSymbol_of_ne_zero _ hn]
      have hL_nn : 0 ≤ latticeNorm n := latticeNorm_nonneg n
      rw [show ((latticeNorm n) ^ ((k : ℝ))) ^ 2
          = latticeNorm n ^ ((2 * k : ℕ) : ℝ) from by
        rw [← Real.rpow_natCast ((latticeNorm n) ^ (k : ℝ)) 2,
          ← Real.rpow_mul hL_nn]
        congr 1; push_cast; ring]
      rw [Real.rpow_natCast]
    rw [h_σk_sq]
    exact latticeNorm_pow_mul_heat_le hk ht n

/-- **Mode-level Ḣᵏ parabolic smoothing at general k.** For `k ≥ 1`:

    `σ_k(n)² · ‖heat(t,n) · c‖² ≤ (k^k · exp(-k) / t^k) · ‖c‖²`

This is the mode-level form of the classical
`‖(-Δ)^{k/2} (e^{tΔ}f)‖_{L²} ≤ (k/(et))^{k/2} · ‖f‖_{L²}` estimate. -/
theorem heatSymbol_Hk_smoothing_mode {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol (k : ℝ) n) ^ 2 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (heatSymbol_nonneg t n)]
  have hmain := fracDerivSymbol_nat_sq_mul_heat_le hk ht n
  have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
  have hσ_nn : 0 ≤ (fracDerivSymbol (k : ℝ) n) ^ 2 := sq_nonneg _
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have htk_pos : 0 < t ^ k := pow_pos ht k
    positivity
  calc (fracDerivSymbol (k : ℝ) n) ^ 2 * ((heatSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol (k : ℝ) n) ^ 2 * heatSymbol t n)
        * (heatSymbol t n * ‖c‖ ^ 2) := by ring
    _ ≤ ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) * (heatSymbol t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hheat_nn hc_nn)
    _ ≤ ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hheat_le_one hc_nn
    _ = ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) * ‖c‖ ^ 2 := by ring

/-- **Heat operator strictly smooths at each natural Sobolev level.**
For `k ≥ 1`, applying the heat semigroup for time `t > 0` gives a
bound at `Ḣᵏ` level proportional to `1/t^k`. -/
theorem heatSymbol_increases_regularity {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol (k : ℝ) n) ^ 2 * heatSymbol t n ≤
      (k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k :=
  fracDerivSymbol_nat_sq_mul_heat_le hk ht n

/-! ## Integrated parabolic smoothing (Lp form)

Lifting the mode-level parabolic smoothing bounds to integrated
Ḣᵏ seminorms via Parseval.
-/

/-- **Integrated parabolic smoothing at Ḣᵏ level.** For `k ≥ 1`, `t > 0`,
and heat-smoothed function `u` with Fourier coefficients
`û(n) = heatSymbol(t, n) · f̂(n)`:

    `‖u‖²_{Ḣᵏ} ≤ (k^k · exp(-k) / t^k) · ‖f‖²_{L²}`

This is the classical `‖(-Δ)^{k/2}(e^{tΔ}f)‖²_{L²} ≤ (k/(et))^k · ‖f‖²_{L²}`
parabolic smoothing estimate. -/
theorem heatSymbol_Hk_smoothing_integrated {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq (k : ℝ) u ≤
      ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff f n‖ ^ 2) := by
  unfold hsSeminormSq
  rw [show ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑f) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k) * ‖mFourierCoeff (↑↑f) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦
    fracDerivSymbol (k : ℝ) n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heatSymbol_Hk_smoothing_mode hk ht n (mFourierCoeff f n)
  · apply (hsum.mul_left ((k : ℝ) ^ k * Real.exp (-(k : ℝ)) / t ^ k)).of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      rw [hcoeff n]
      exact heatSymbol_Hk_smoothing_mode hk ht n (mFourierCoeff f n)
  · exact hsum.mul_left _

/-- **Integrated parabolic smoothing at gradient level.** Specialization
of `heatSymbol_Hk_smoothing_integrated` at `k = 1`:

    `‖u‖²_{Ḣ¹} ≤ (exp(-1) / t) · ‖f‖²_{L²}` -/
theorem heatSymbol_grad_smoothing_integrated {t : ℝ} (ht : 0 < t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq 1 u ≤
      (Real.exp (-1) / t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff f n‖ ^ 2) := by
  have h := heatSymbol_Hk_smoothing_integrated (k := 1) (by omega) ht f u hcoeff hsum
  simp only [Nat.cast_one, pow_one] at h
  convert h using 1
  ring

/-- **Integrated parabolic smoothing at Hessian level.** Specialization
at `k = 2`:

    `‖u‖²_{Ḣ²} ≤ (4·exp(-2) / t²) · ‖f‖²_{L²}` -/
theorem heatSymbol_hess_smoothing_integrated {t : ℝ} (ht : 0 < t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq 2 u ≤
      (4 * Real.exp (-2) / t ^ 2) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff f n‖ ^ 2) := by
  have h := heatSymbol_Hk_smoothing_integrated (k := 2) (by omega) ht f u hcoeff hsum
  simp only [Nat.cast_ofNat] at h
  convert h using 2
  norm_num

/-! ## Parabolic smoothing at real exponent k > 0

Extends natural-number parabolic smoothing to arbitrary real k > 0
using `Real.rpow`. The bootstrap is identical: apply k=1 at `t/k`,
then raise both sides to the real k-th power via `Real.rpow_le_rpow`.
-/

/-- **Heat semigroup rpow identity.** For `k > 0`, `t : ℝ`:

    `heatSymbol t n = (heatSymbol (t/k) n) ^ k`

where `^` is `Real.rpow`. -/
theorem heatSymbol_rpow_eq {t : ℝ} (n : Fin 2 → ℤ) {k : ℝ} (hk : 0 < k) :
    heatSymbol t n = (heatSymbol (t / k) n) ^ k := by
  unfold heatSymbol
  -- Goal: exp(-t·L²) = (exp(-(t/k)·L²))^k
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  -- Now: exp(-t·L²) = exp(k · (-(t/k)·L²))
  congr 1
  have hk_ne : k ≠ 0 := hk.ne'
  field_simp

/-- **Exponential rpow identity.** `exp(-1)^k = exp(-k)`. -/
lemma exp_neg_one_rpow (k : ℝ) : (Real.exp (-1)) ^ k = Real.exp (-k) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1; ring

/-- **`latticeNorm` squared as rpow.** For `n : Fin 2 → ℤ`:

    `(latticeNorm n)^2 = (latticeNorm n)^(2 : ℝ)` (rpow form). -/
lemma latticeNorm_sq_eq_rpow (n : Fin 2 → ℤ) :
    ((latticeNorm n) ^ 2 : ℝ) = (latticeNorm n) ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- **General real-k parabolic smoothing.** For `k > 0`, `t > 0`:

    `‖n‖^{2k} · exp(-t·‖n‖²) ≤ k^k · exp(-k) / t^k`

where all exponents are `Real.rpow`. -/
theorem latticeNorm_rpow_mul_heat_le {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ (2 * k) * heatSymbol t n
    ≤ k ^ k * Real.exp (-k) / t ^ k := by
  have hL_nn : 0 ≤ latticeNorm n := latticeNorm_nonneg n
  have ht_k : 0 < t / k := div_pos ht hk
  have hbase := latticeNorm_sq_mul_heat_le ht_k n
  have hbase_nn : 0 ≤ (latticeNorm n) ^ 2 * heatSymbol (t/k) n :=
    mul_nonneg (sq_nonneg _) (heatSymbol_nonneg _ _)
  -- Raise both sides to the k-th real power
  have hpow : ((latticeNorm n) ^ 2 * heatSymbol (t/k) n) ^ k
            ≤ (Real.exp (-1) / (t / k)) ^ k :=
    Real.rpow_le_rpow hbase_nn hbase hk.le
  -- Simplify LHS: (L² · heat(t/k))^k = L^{2k} · heat(t)
  have hLHS_eq : ((latticeNorm n) ^ 2 * heatSymbol (t/k) n) ^ k
      = (latticeNorm n) ^ (2 * k) * heatSymbol t n := by
    rw [Real.mul_rpow (sq_nonneg _) (heatSymbol_nonneg _ _)]
    congr 1
    · -- (L²)^k = L^{2k}
      rw [latticeNorm_sq_eq_rpow, ← Real.rpow_mul hL_nn]
    · -- heat(t/k)^k = heat(t)
      rw [← heatSymbol_rpow_eq n hk]
  -- Simplify RHS: (exp(-1)/(t/k))^k = k·exp(-1)/t)^k = k^k · exp(-k) / t^k
  have hRHS_eq : (Real.exp (-1) / (t / k)) ^ k
      = k ^ k * Real.exp (-k) / t ^ k := by
    have ht_ne : t ≠ 0 := ht.ne'
    have hk_ne : k ≠ 0 := hk.ne'
    have hrew : Real.exp (-1) / (t / k) = k * Real.exp (-1) / t := by
      field_simp
    rw [hrew]
    rw [Real.div_rpow (by positivity : 0 ≤ k * Real.exp (-1)) ht.le]
    rw [Real.mul_rpow hk.le (Real.exp_pos _).le]
    rw [exp_neg_one_rpow]
  rw [hLHS_eq] at hpow
  rw [hRHS_eq] at hpow
  exact hpow

/-- **Real-k parabolic smoothing at fracDerivSymbol level.** For `k > 0`, `t > 0`:

    `σ_k(n)² · heat(t, n) ≤ k^k · exp(-k) / t^k`

using `rpow` for `σ_k` and the power `t^k`. -/
theorem fracDerivSymbol_sq_mul_heat_le_rpow {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol k n) ^ 2 * heatSymbol t n
    ≤ k ^ k * Real.exp (-k) / t ^ k := by
  by_cases hn : n = 0
  · subst hn
    rw [fracDerivSymbol_zero]
    simp
    positivity
  · -- σ_k(n)² = L^{2k}: use (L^k)^2 = L^k · L^k = L^(k+k) = L^(2k)
    have hL_pos : 0 < latticeNorm n := latticeNorm_pos hn
    have h_σk_sq : (fracDerivSymbol k n) ^ 2 = (latticeNorm n) ^ (2 * k) := by
      rw [fracDerivSymbol_of_ne_zero k hn, sq,
        ← Real.rpow_add hL_pos]
      congr 1; ring
    rw [h_σk_sq]
    exact latticeNorm_rpow_mul_heat_le hk ht n

/-- **Mode-level Ḣᵏ parabolic smoothing at real k > 0.** For any `k > 0, t > 0`:

    `σ_k(n)² · ‖heat(t,n) · c‖² ≤ (k^k · exp(-k) / t^k) · ‖c‖²` -/
theorem heatSymbol_Hk_smoothing_mode_rpow {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol k n) ^ 2 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (k ^ k * Real.exp (-k) / t ^ k) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (heatSymbol_nonneg t n)]
  have hmain := fracDerivSymbol_sq_mul_heat_le_rpow hk ht n
  have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
  have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ k ^ k * Real.exp (-k) / t ^ k := by
    have htk_pos : 0 < t ^ k := Real.rpow_pos_of_pos ht k
    have hkk_pos : 0 < k ^ k := Real.rpow_pos_of_pos hk k
    positivity
  calc (fracDerivSymbol k n) ^ 2 * ((heatSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol k n) ^ 2 * heatSymbol t n)
        * (heatSymbol t n * ‖c‖ ^ 2) := by ring
    _ ≤ (k ^ k * Real.exp (-k) / t ^ k) * (heatSymbol t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hheat_nn hc_nn)
    _ ≤ (k ^ k * Real.exp (-k) / t ^ k) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hheat_le_one hc_nn
    _ = (k ^ k * Real.exp (-k) / t ^ k) * ‖c‖ ^ 2 := by ring

/-- **Integrated Ḣᵏ parabolic smoothing at real k > 0.** For `k > 0, t > 0`,
heat-smoothed `u` with `û(n) = heat(t,n) · f̂(n)`:

    `‖u‖²_{Ḣᵏ} ≤ (k^k · exp(-k) / t^k) · ‖f‖²_{L²}` -/
theorem heatSymbol_Hk_smoothing_integrated_rpow {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq k u ≤
      (k ^ k * Real.exp (-k) / t ^ k) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff f n‖ ^ 2) := by
  unfold hsSeminormSq
  rw [show (k ^ k * Real.exp (-k) / t ^ k) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑f) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        (k ^ k * Real.exp (-k) / t ^ k) * ‖mFourierCoeff (↑↑f) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦
    fracDerivSymbol k n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heatSymbol_Hk_smoothing_mode_rpow hk ht n (mFourierCoeff f n)
  · apply (hsum.mul_left (k ^ k * Real.exp (-k) / t ^ k)).of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      rw [hcoeff n]
      exact heatSymbol_Hk_smoothing_mode_rpow hk ht n (mFourierCoeff f n)
  · exact hsum.mul_left _

/-! ## Heat semigroup contractivity at every Sobolev level

The heat semigroup is a contraction on `L²`, `Ḣˢ`, and more generally
at every Sobolev level. These are proven by lifting the mode-level
`heatSymbol_Hs_mode_bound` via Parseval/tsum.
-/

/-- **Heat L² contractivity (integrated).** For `t ≥ 0`, heat-smoothed
function satisfies `‖e^{tΔ}f‖²_{L²} ≤ ‖f‖²_{L²}`. -/
theorem heatSymbol_L2_contractivity {t : ℝ} (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) (∫ x, ‖f x‖ ^ 2))
    (hu_parseval : HasSum (fun n ↦ ‖mFourierCoeff u n‖ ^ 2) (∫ x, ‖u x‖ ^ 2))
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    (∫ x, ‖u x‖ ^ 2) ≤ (∫ x, ‖f x‖ ^ 2) := by
  rw [← hu_parseval.tsum_eq, ← hf_parseval.tsum_eq]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hheat_le_one : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
      pow_le_one₀ hheat_nn hheat_le_one
    have hc_nn : 0 ≤ ‖mFourierCoeff f n‖ ^ 2 := sq_nonneg _
    calc (heatSymbol t n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2
        ≤ 1 * ‖mFourierCoeff f n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hheat_sq_le hc_nn
      _ = ‖mFourierCoeff f n‖ ^ 2 := one_mul _
  · exact hu_parseval.summable
  · exact hsum

/-- **Heat Ḣˢ contractivity (integrated).** For `t ≥ 0`:

    `‖e^{tΔ}f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣˢ}` -/
theorem heatSymbol_Hs_contractivity {s : ℝ} {t : ℝ} (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  apply Summable.tsum_le_tsum
    (f := fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heatSymbol_Hs_mode_bound ht s (mFourierCoeff f n)
  · apply hsum.of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      rw [hcoeff n]
      exact heatSymbol_Hs_mode_bound ht s (mFourierCoeff f n)
  · exact hsum

/-! ## α-Fractional heat semigroup

The fractional heat semigroup `e^{-t(-Δ)^α}` for `0 < α` has Fourier
multiplier `exp(-t·‖n‖^{2α})`. Unifies:
- Heat (α = 1): `exp(-t·‖n‖²)`  [`heatSymbol`]
- Poisson (α = 1/2): `exp(-t·‖n‖)`  [`poissonSymbol`]

Relevant for fractional SQG / surface quasi-geostrophic-like equations
with dissipation `(-Δ)^α` where `0 < α ≤ 1`.
-/

/-- **α-Fractional heat semigroup symbol.** For `α > 0, t : ℝ`:

    `H_{α,t}(n) = exp(-t · ‖n‖^{2α})`

where `‖n‖^{2α}` uses `Real.rpow`. -/
noncomputable def fracHeatSymbol (α t : ℝ) (n : Fin 2 → ℤ) : ℝ :=
  Real.exp (-t * (latticeNorm n) ^ (2 * α))

/-- **α-Fractional heat at zero mode is `exp(0) = 1` if `α > 0`.** -/
@[simp] lemma fracHeatSymbol_zero_mode {α t : ℝ} (hα : 0 < α) :
    fracHeatSymbol α t (0 : Fin 2 → ℤ) = 1 := by
  unfold fracHeatSymbol
  simp [latticeNorm, Real.zero_rpow (by linarith : (2 * α) ≠ 0)]

/-- **Fractional heat is positive.** -/
lemma fracHeatSymbol_pos (α t : ℝ) (n : Fin 2 → ℤ) :
    0 < fracHeatSymbol α t n := Real.exp_pos _

/-- **Fractional heat is nonneg.** -/
lemma fracHeatSymbol_nonneg (α t : ℝ) (n : Fin 2 → ℤ) :
    0 ≤ fracHeatSymbol α t n := (fracHeatSymbol_pos α t n).le

/-- **Fractional heat at t=0 is 1.** -/
@[simp] lemma fracHeatSymbol_zero_time (α : ℝ) (n : Fin 2 → ℤ) :
    fracHeatSymbol α 0 n = 1 := by
  unfold fracHeatSymbol
  simp

/-- **Fractional heat ≤ 1 for t ≥ 0 and α > 0.** -/
lemma fracHeatSymbol_le_one {α t : ℝ} (_hα : 0 < α) (ht : 0 ≤ t) (n : Fin 2 → ℤ) :
    fracHeatSymbol α t n ≤ 1 := by
  unfold fracHeatSymbol
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  apply Real.exp_le_exp.mpr
  have hL_pow_nn : 0 ≤ (latticeNorm n : ℝ) ^ (2 * α) :=
    Real.rpow_nonneg (latticeNorm_nonneg n) (2 * α)
  nlinarith

/-- **Fractional heat: additive in time (homomorphism).** -/
lemma fracHeatSymbol_add (α t₁ t₂ : ℝ) (n : Fin 2 → ℤ) :
    fracHeatSymbol α (t₁ + t₂) n
    = fracHeatSymbol α t₁ n * fracHeatSymbol α t₂ n := by
  unfold fracHeatSymbol
  rw [← Real.exp_add]
  congr 1; ring

/-- **Heat is α=1 case of fracHeat.** -/
theorem fracHeatSymbol_one_eq_heat (t : ℝ) (n : Fin 2 → ℤ) :
    fracHeatSymbol 1 t n = heatSymbol t n := by
  unfold fracHeatSymbol heatSymbol
  congr 1
  have hL_nn : 0 ≤ (latticeNorm n : ℝ) := latticeNorm_nonneg n
  rw [show ((latticeNorm n : ℝ) : ℝ) ^ (2 * (1 : ℝ)) = (latticeNorm n) ^ 2 from by
    rw [show (2 * 1 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]]

/-- **Fractional heat base smoothing bound.** For `0 < α`, `t > 0`:

    `‖n‖^{2α} · exp(-t·‖n‖^{2α}) ≤ exp(-1)/t`

Obtained by letting `y = t·‖n‖^{2α}` and using `y·exp(-y) ≤ exp(-1)`. -/
theorem latticeNorm_rpow_mul_fracHeat_le {α : ℝ} (_hα : 0 < α) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ (2 * α) * fracHeatSymbol α t n ≤ Real.exp (-1) / t := by
  unfold fracHeatSymbol
  set y : ℝ := t * (latticeNorm n) ^ (2 * α) with hy_def
  have hL_pow_nn : 0 ≤ (latticeNorm n : ℝ) ^ (2 * α) :=
    Real.rpow_nonneg (latticeNorm_nonneg n) (2 * α)
  have hy_nn : 0 ≤ y := mul_nonneg ht.le hL_pow_nn
  have hexp_rw : Real.exp (-t * (latticeNorm n) ^ (2 * α)) = Real.exp (-y) := by
    congr 1; rw [hy_def]; ring
  rw [hexp_rw]
  have hLeq : ((latticeNorm n : ℝ) ^ (2 * α)) = y / t := by
    rw [hy_def]; field_simp
  rw [hLeq, div_mul_eq_mul_div]
  have h_num : y * Real.exp (-y) ≤ Real.exp (-1) := mul_exp_neg_le_exp_neg_one y
  gcongr

/-- **Fractional heat rpow identity.** For `k > 0`:

    `fracHeatSymbol α t n = (fracHeatSymbol α (t/k) n)^k`. -/
theorem fracHeatSymbol_rpow_eq {α : ℝ} {t : ℝ} (n : Fin 2 → ℤ) {k : ℝ} (hk : 0 < k) :
    fracHeatSymbol α t n = (fracHeatSymbol α (t / k) n) ^ k := by
  unfold fracHeatSymbol
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  have hk_ne : k ≠ 0 := hk.ne'
  field_simp

/-- **General α-fractional heat smoothing.** For `0 < α`, `t > 0`, `k > 0`:

    `‖n‖^k · exp(-t·‖n‖^{2α}) ≤ (k/(2α))^{k/(2α)} · exp(-k/(2α)) / t^{k/(2α)}`

Unifies:
- Heat (α = 1): `‖n‖^k·exp(-t‖n‖²) ≤ (k/2)^{k/2} · exp(-k/2) / t^{k/2}`
- Poisson (α = 1/2): `‖n‖^k·exp(-t‖n‖) ≤ k^k · exp(-k) / t^k` -/
theorem latticeNorm_rpow_mul_fracHeat_le_general
    {α k : ℝ} (hα : 0 < α) (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ k * fracHeatSymbol α t n
    ≤ (k / (2 * α)) ^ (k / (2 * α)) * Real.exp (-(k / (2 * α))) / t ^ (k / (2 * α)) := by
  have hL_nn : 0 ≤ latticeNorm n := latticeNorm_nonneg n
  set m : ℝ := k / (2 * α) with hm_def
  have hm_pos : 0 < m := by rw [hm_def]; positivity
  have ht_m : 0 < t / m := div_pos ht hm_pos
  -- Base: L^{2α} · fracHeat α (t/m) n ≤ exp(-1) / (t/m)
  have hbase := latticeNorm_rpow_mul_fracHeat_le hα ht_m n
  have hbase_nn : 0 ≤ (latticeNorm n) ^ (2 * α) * fracHeatSymbol α (t/m) n :=
    mul_nonneg (Real.rpow_nonneg hL_nn _) (fracHeatSymbol_nonneg _ _ _)
  -- Raise to m-th real power
  have hpow : ((latticeNorm n) ^ (2 * α) * fracHeatSymbol α (t/m) n) ^ m
            ≤ (Real.exp (-1) / (t / m)) ^ m :=
    Real.rpow_le_rpow hbase_nn hbase hm_pos.le
  -- LHS: (L^{2α} · frac(t/m))^m = L^{2αm} · frac(t)
  have hLHS_eq : ((latticeNorm n) ^ (2 * α) * fracHeatSymbol α (t/m) n) ^ m
      = (latticeNorm n) ^ k * fracHeatSymbol α t n := by
    rw [Real.mul_rpow (Real.rpow_nonneg hL_nn _) (fracHeatSymbol_nonneg _ _ _)]
    congr 1
    · -- (L^{2α})^m = L^{2αm} = L^k
      rw [← Real.rpow_mul hL_nn]
      congr 1
      rw [hm_def]; field_simp
    · -- frac(t/m)^m = frac(t)
      rw [← fracHeatSymbol_rpow_eq n hm_pos]
  -- RHS: (exp(-1)/(t/m))^m = m^m · exp(-m) / t^m
  have hRHS_eq : (Real.exp (-1) / (t / m)) ^ m = m ^ m * Real.exp (-m) / t ^ m := by
    have ht_ne : t ≠ 0 := ht.ne'
    have hm_ne : m ≠ 0 := hm_pos.ne'
    have hrew : Real.exp (-1) / (t / m) = m * Real.exp (-1) / t := by
      field_simp
    rw [hrew, Real.div_rpow (by positivity : 0 ≤ m * Real.exp (-1)) ht.le,
      Real.mul_rpow hm_pos.le (Real.exp_pos _).le, exp_neg_one_rpow]
  rw [hLHS_eq] at hpow
  rw [hRHS_eq] at hpow
  convert hpow using 1

/-- **General α-fractional heat bound via fracDerivSymbol.** For `k > 0`:

    `σ_k(n)² · fracHeat(α, t, n) ≤ (k/α)^{k/α} · exp(-k/α) / t^{k/α}`

Using `σ_k² = ‖n‖^{2k}` and the general bound with parameter `2k`. -/
theorem fracDerivSymbol_sq_mul_fracHeat_le
    {α k : ℝ} (hα : 0 < α) (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (fracDerivSymbol k n) ^ 2 * fracHeatSymbol α t n
    ≤ (k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α) := by
  by_cases hn : n = 0
  · subst hn
    rw [fracDerivSymbol_zero]
    simp
    have : 0 < k / α := div_pos hk hα
    positivity
  · have hL_pos : 0 < latticeNorm n := latticeNorm_pos hn
    have h_σk_sq : (fracDerivSymbol k n) ^ 2 = (latticeNorm n) ^ (2 * k) := by
      rw [fracDerivSymbol_of_ne_zero k hn, sq, ← Real.rpow_add hL_pos]
      congr 1; ring
    rw [h_σk_sq]
    -- Apply general bound with k' = 2k, so k'/(2α) = k/α
    have h2k_pos : 0 < 2 * k := by linarith
    have := latticeNorm_rpow_mul_fracHeat_le_general hα h2k_pos ht n
    -- This gives: L^{2k} · frac ≤ (2k/(2α))^{2k/(2α)} · exp(-2k/(2α)) / t^{2k/(2α)}
    -- = (k/α)^{k/α} · exp(-k/α) / t^{k/α}
    have hsimp : 2 * k / (2 * α) = k / α := by field_simp
    rw [hsimp] at this
    exact this

/-- **α-Fractional heat Ḣᵏ mode smoothing.** For `α > 0, k > 0, t > 0`:

    `σ_k(n)² · ‖fracHeat(α,t,n) · c‖² ≤ ((k/α)^{k/α} · exp(-k/α) / t^{k/α}) · ‖c‖²` -/
theorem fracHeatSymbol_Hk_mode_bound
    {α k : ℝ} (hα : 0 < α) (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol k n) ^ 2 * ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α)) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
  have hmain := fracDerivSymbol_sq_mul_fracHeat_le hα hk ht n
  have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
  have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ (k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α) := by
    have hkα : 0 < k / α := div_pos hk hα
    have htk : 0 < t ^ (k / α) := Real.rpow_pos_of_pos ht _
    have hkk : 0 < (k / α) ^ (k / α) := Real.rpow_pos_of_pos hkα _
    positivity
  calc (fracDerivSymbol k n) ^ 2 * ((fracHeatSymbol α t n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol k n) ^ 2 * fracHeatSymbol α t n)
        * (fracHeatSymbol α t n * ‖c‖ ^ 2) := by ring
    _ ≤ ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α))
        * (fracHeatSymbol α t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hf_nn hc_nn)
    _ ≤ ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α)) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hf_le hc_nn
    _ = ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α)) * ‖c‖ ^ 2 := by ring

/-- **α-Fractional heat L² contractivity (mode-level).** -/
theorem fracHeatSymbol_L2_mode_contract {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
  have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
  have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht n
  have hf_sq_le : (fracHeatSymbol α t n) ^ 2 ≤ 1 := pow_le_one₀ hf_nn hf_le
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  calc (fracHeatSymbol α t n) ^ 2 * ‖c‖ ^ 2
      ≤ 1 * ‖c‖ ^ 2 := mul_le_mul_of_nonneg_right hf_sq_le hc_nn
    _ = ‖c‖ ^ 2 := one_mul _

/-- **α-Fractional heat Ḣˢ mode contractivity.** -/
theorem fracHeatSymbol_Hs_mode_bound {α s t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 * ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
  mul_le_mul_of_nonneg_left (fracHeatSymbol_L2_mode_contract hα ht n c) (sq_nonneg _)

/-- **α-Fractional heat Ḣᵏ integrated smoothing.** For `0 < α, k > 0, t > 0`:

    `‖e^{-t(-Δ)^α} f‖²_{Ḣᵏ} ≤ (k/α)^{k/α}·exp(-k/α)/t^{k/α} · ‖f‖²_{L²}` -/
theorem fracHeatSymbol_Hk_smoothing_integrated
    {α k : ℝ} (hα : 0 < α) (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((fracHeatSymbol α t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq k u ≤
      ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α)) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff f n‖ ^ 2) := by
  unfold hsSeminormSq
  rw [show ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α)) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑f) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        ((k / α) ^ (k / α) * Real.exp (-(k / α)) / t ^ (k / α))
          * ‖mFourierCoeff (↑↑f) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦
    fracDerivSymbol k n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact fracHeatSymbol_Hk_mode_bound hα hk ht n (mFourierCoeff f n)
  · apply (hsum.mul_left _).of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      rw [hcoeff n]
      exact fracHeatSymbol_Hk_mode_bound hα hk ht n (mFourierCoeff f n)
  · exact hsum.mul_left _

/-- **α-Fractional heat L² contractivity (integrated).** For `α > 0, t ≥ 0`:

    `‖e^{-t(-Δ)^α} f‖²_{L²} ≤ ‖f‖²_{L²}` -/
theorem fracHeatSymbol_L2_contractivity
    {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((fracHeatSymbol α t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) (∫ x, ‖f x‖ ^ 2))
    (hu_parseval : HasSum (fun n ↦ ‖mFourierCoeff u n‖ ^ 2) (∫ x, ‖u x‖ ^ 2))
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    (∫ x, ‖u x‖ ^ 2) ≤ (∫ x, ‖f x‖ ^ 2) := by
  rw [← hu_parseval.tsum_eq, ← hf_parseval.tsum_eq]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact fracHeatSymbol_L2_mode_contract hα ht n (mFourierCoeff f n)
  · exact hu_parseval.summable
  · exact hsum

/-- **α-Fractional heat Ḣˢ contractivity (integrated).** -/
theorem fracHeatSymbol_Hs_contractivity
    {α s t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((fracHeatSymbol α t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s f := by
  unfold hsSeminormSq
  apply Summable.tsum_le_tsum
    (f := fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact fracHeatSymbol_Hs_mode_bound hα ht n (mFourierCoeff f n)
  · apply hsum.of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      rw [hcoeff n]
      exact fracHeatSymbol_Hs_mode_bound hα ht n (mFourierCoeff f n)
  · exact hsum

/-! ## α-Fractional heat-smoothed SQG quantities

Unified framework: applies α-fractional heat to SQG vorticity, gradient,
and strain. Specializes to heat (α=1) and Poisson (α=1/2) versions.
-/

/-- **α-fracHeat-smoothed SQG vorticity L² mode bound.** For `n ≠ 0, t > 0`:

    `‖fracHeat(α,t,n) · ω̂(n) · c‖² ≤ (1/(2α))^{1/(2α)}·exp(-1/(2α))/t^{1/(2α)} · ‖c‖²`

Specializes:
- α = 1: `‖heat · ω̂ · c‖² ≤ (1/2)^{1/2}·exp(-1/2)/t^{1/2} · ‖c‖²`
  Wait: for heat, we have 4·exp(-1)/t. The factor differs. Let me restate.

Actually for α = 1: this theorem gives the SMALLER LHS `ω̂·heat`, bounded
by `(k/(2α))^{k/(2α)}·exp(-k/(2α))/t^{k/(2α)}` with k=1: `(1/2)^{1/2}·e^{-1/2}/√t`.

This is a different bound scaling than the heat version which scales as 1/t. -/
theorem fracHeat_smoothed_vorticity_L2_mode
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    {n : Fin 2 → ℤ} (hn : n ≠ 0) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * sqgVorticitySymbol n * c‖ ^ 2
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
  -- ‖fracHeat·ω̂·c‖² = fracHeat² · ‖ω̂‖² · ‖c‖² = fracHeat² · L² · ‖c‖²
  -- Use: fracHeat² · L² ≤ fracHeat · L² (since fracHeat ≤ 1)
  --      fracHeat · L² = fracHeat · σ_1² ≤ (1/α)^{1/α}·exp(-1/α)/t^{1/α}
  rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n),
    sqgVorticitySymbol_norm hn]
  -- Goal: fracHeat² · L² · ‖c‖² ≤ ...
  have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
  have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
  have hmain : (fracDerivSymbol 1 n) ^ 2 * fracHeatSymbol α t n
      ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) :=
    fracDerivSymbol_sq_mul_fracHeat_le hα one_pos ht n
  have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
    rw [fracDerivSymbol_one_eq hn]
  rw [hfrac1] at hmain
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) := by
    have h1α : 0 < 1 / α := div_pos one_pos hα
    have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
    have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
    positivity
  calc (fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2
      = fracHeatSymbol α t n * ((latticeNorm n) ^ 2 * fracHeatSymbol α t n) * ‖c‖ ^ 2 := by
        rw [sq]; ring
    _ ≤ fracHeatSymbol α t n *
        ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hc_nn
        exact mul_le_mul_of_nonneg_left hmain hf_nn
    _ ≤ 1 *
        ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hc_nn
        exact mul_le_mul_of_nonneg_right hf_le hfactor_nn
    _ = ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by ring

/-- **α-fracHeat-smoothed SQG gradient L² mode bound.** For `t > 0, α > 0`:

    `‖fracHeat(α,t,n) · ∂̂_i u_j(n) · c‖² ≤ (1/α)^{1/α}·exp(-1/α)/t^{1/α} · ‖c‖²` -/
theorem fracHeat_smoothed_sqgGrad_L2_mode
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (n : Fin 2 → ℤ) (i j : Fin 2) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * sqgGradSymbol i j n * c‖ ^ 2
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have hg0 : sqgGradSymbol i j 0 = 0 := by
      unfold sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [hg0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have h1α : 0 < 1 / α := div_pos one_pos hα
    have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
    have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
    have hgrad := sqgGrad_norm_le hn i j
    have hgrad_sq_le : ‖sqgGradSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (sqgGradSymbol i j n)]) hgrad
    have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
    have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
    have hmain : (fracDerivSymbol 1 n) ^ 2 * fracHeatSymbol α t n
        ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) :=
      fracDerivSymbol_sq_mul_fracHeat_le hα one_pos ht n
    have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
      rw [fracDerivSymbol_one_eq hn]
    rw [hfrac1] at hmain
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hfactor_nn : 0 ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) := by
      have h1α : 0 < 1 / α := div_pos one_pos hα
      have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
      have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
      positivity
    calc (fracHeatSymbol α t n) ^ 2 * ‖sqgGradSymbol i j n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg _)
      _ = fracHeatSymbol α t n * ((latticeNorm n) ^ 2 * fracHeatSymbol α t n) * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ fracHeatSymbol α t n *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hmain hf_nn
      _ ≤ 1 *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_right hf_le hfactor_nn
      _ = ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by ring

/-- **α-fracHeat-smoothed SQG strain L² mode bound.** Same structure as gradient. -/
theorem fracHeat_smoothed_sqgStrain_L2_mode
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (n : Fin 2 → ℤ) (i j : Fin 2) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * sqgStrainSymbol i j n * c‖ ^ 2
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have hs0 : sqgStrainSymbol i j 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [hs0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have h1α : 0 < 1 / α := div_pos one_pos hα
    have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
    have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
    have hstrain := sqgStrain_norm_le hn i j
    have hstrain_sq_le : ‖sqgStrainSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol i j n)]) hstrain
    have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
    have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
    have hmain : (fracDerivSymbol 1 n) ^ 2 * fracHeatSymbol α t n
        ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) :=
      fracDerivSymbol_sq_mul_fracHeat_le hα one_pos ht n
    have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
      rw [fracDerivSymbol_one_eq hn]
    rw [hfrac1] at hmain
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hfactor_nn : 0 ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) := by
      have h1α : 0 < 1 / α := div_pos one_pos hα
      have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
      have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
      positivity
    calc (fracHeatSymbol α t n) ^ 2 * ‖sqgStrainSymbol i j n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hstrain_sq_le (sq_nonneg _)
      _ = fracHeatSymbol α t n * ((latticeNorm n) ^ 2 * fracHeatSymbol α t n) * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ fracHeatSymbol α t n *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hmain hf_nn
      _ ≤ 1 *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_right hf_le hfactor_nn
      _ = ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) * ‖c‖ ^ 2 := by ring

/-- **α-fracHeat-smoothed SQG velocity Ḣˢ mode bound.** For `α > 0, t ≥ 0`:

    `σ_s² · ‖fracHeat(α,t,n) · R · c‖² ≤ σ_s² · ‖c‖²`

No Sobolev gain: both Riesz and fracHeat are contractive. -/
theorem fracHeat_smoothed_sqg_velocity_mode
    (s : ℝ) {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (n : Fin 2 → ℤ) (j : Fin 2) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 *
      ‖((fracHeatSymbol α t n : ℝ) : ℂ) *
       (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) * c‖ ^ 2
    ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := by
  rw [show ((fracHeatSymbol α t n : ℝ) : ℂ) *
      (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) * c
      = (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
        (((fracHeatSymbol α t n : ℝ) : ℂ) * c) from by ring]
  by_cases hn : n = 0
  · subst hn
    by_cases hj : j = 0
    · simp [hj, rieszSymbol_zero, fracDerivSymbol_zero]
    · simp [hj, rieszSymbol_zero, fracDerivSymbol_zero]
  · have hR_le : ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2 ≤ 1 := by
      have hpyth := rieszSymbol_sum_sq hn
      simp only [Fin.sum_univ_two] at hpyth
      by_cases hj : j = 0
      · simp [hj]; nlinarith [sq_nonneg ‖rieszSymbol 0 n‖]
      · simp [hj, norm_neg]; nlinarith [sq_nonneg ‖rieszSymbol 1 n‖]
    have hf_contract := fracHeatSymbol_L2_mode_contract hα ht n c
    have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
    have hfc_nn : 0 ≤ ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2 := sq_nonneg _
    calc (fracDerivSymbol s n) ^ 2 *
          ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
            (((fracHeatSymbol α t n : ℝ) : ℂ) * c)‖ ^ 2
        = (fracDerivSymbol s n) ^ 2 *
          (‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2 *
           ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2) := by
          rw [norm_mul, mul_pow]
      _ ≤ (fracDerivSymbol s n) ^ 2 *
          (1 * ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hR_le hfc_nn) hσs_nn
      _ = (fracDerivSymbol s n) ^ 2 *
          ‖((fracHeatSymbol α t n : ℝ) : ℂ) * c‖ ^ 2 := by ring
      _ ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hf_contract hσs_nn

/-! ## α-fracHeat-smoothed SQG integrated Lp bounds -/

/-- **α-fracHeat-smoothed SQG vorticity L² integrated.** For `t > 0, α > 0`:

    `‖fracHeat(α,·)·ω‖²_{L²} ≤ (1/α)^{1/α}·exp(-1/α)/t^{1/α} · ‖θ‖²_{L²}` -/
theorem fracHeat_smoothed_vorticity_L2_integrated
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
      (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α))
          * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  have hmode : ∀ n : Fin 2 → ℤ,
      ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α))
        * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hω0 : sqgVorticitySymbol 0 = 0 := by
        unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hω0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
      have h1α : 0 < 1 / α := div_pos one_pos hα
      have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
      have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
      exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact fracHeat_smoothed_vorticity_L2_mode hα ht hn (mFourierCoeff θ n)
  apply Summable.tsum_le_tsum hmode
  · exact (hsum.mul_left _).of_nonneg_of_le (fun n ↦ sq_nonneg _) hmode
  · exact hsum.mul_left _

/-- **α-fracHeat-smoothed SQG gradient L² integrated.** -/
theorem fracHeat_smoothed_sqgGrad_L2_integrated
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgGradSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
      (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α))
          * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact fracHeat_smoothed_sqgGrad_L2_mode hα ht n i j (mFourierCoeff θ n)
  · apply (hsum.mul_left _).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact fracHeat_smoothed_sqgGrad_L2_mode hα ht n i j (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **α-fracHeat-smoothed SQG strain L² integrated.** -/
theorem fracHeat_smoothed_sqgStrain_L2_integrated
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
      (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α))
          * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact fracHeat_smoothed_sqgStrain_L2_mode hα ht n i j (mFourierCoeff θ n)
  · apply (hsum.mul_left _).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact fracHeat_smoothed_sqgStrain_L2_mode hα ht n i j (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **α-fracHeat-smoothed SQG velocity Ḣˢ integrated.** For `α > 0, t ≥ 0`:

    `‖fracHeat(α,·) u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}`

No gain in Sobolev level since both Riesz and fracHeat contract. -/
theorem fracHeat_smoothed_sqg_velocity_Hs_integrated
    (s : ℝ) {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) *
        (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
        mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    exact fracHeat_smoothed_sqg_velocity_mode s hα ht n j (mFourierCoeff θ n)
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **α-fracHeat-smoothed SQG vorticity Ḣˢ integrated (contractive).**
For `α > 0, t ≥ 0`:

    `‖fracHeat(α,·) ω‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}`

Uses fracHeat ≤ 1 and `‖ω̂(n)‖ = ‖n‖ = σ_1(n)` to get level shift by 1. -/
theorem fracHeat_smoothed_vorticity_Hs_integrated (s : ℝ) {α t : ℝ}
    (hα : 0 < α) (ht : 0 ≤ t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hω0 : sqgVorticitySymbol 0 = 0 := by
        unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hω0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n),
        sqgVorticitySymbol_norm hn]
      have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
      have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht n
      have hf_sq_le : (fracHeatSymbol α t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hf_nn hf_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          = (fracHeatSymbol α t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hf_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **α-fracHeat-smoothed SQG gradient Ḣˢ integrated (contractive).** -/
theorem fracHeat_smoothed_sqgGrad_Hs_integrated (s : ℝ) {α t : ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgGradSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hg0 : sqgGradSymbol i j 0 = 0 := by
        unfold sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hg0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
      have hgrad := sqgGrad_norm_le hn i j
      have hgrad_sq_le : ‖sqgGradSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (sqgGradSymbol i j n)]) hgrad
      have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
      have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht n
      have hf_sq_le : (fracHeatSymbol α t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hf_nn hf_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((fracHeatSymbol α t n) ^ 2 * ‖sqgGradSymbol i j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg _)
        _ = (fracHeatSymbol α t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hf_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **α-fracHeat-smoothed SQG strain Ḣˢ integrated (contractive).** -/
theorem fracHeat_smoothed_sqgStrain_Hs_integrated (s : ℝ) {α t : ℝ}
    (hα : 0 < α) (ht : 0 ≤ t) (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((fracHeatSymbol α t n : ℝ) : ℂ) * sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hs0 : sqgStrainSymbol i j 0 = 0 := by
        unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hs0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
      have hstrain := sqgStrain_norm_le hn i j
      have hstrain_sq_le : ‖sqgStrainSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol i j n)]) hstrain
      have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
      have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht n
      have hf_sq_le : (fracHeatSymbol α t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hf_nn hf_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((fracHeatSymbol α t n) ^ 2 * ‖sqgStrainSymbol i j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((fracHeatSymbol α t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hstrain_sq_le (sq_nonneg _)
        _ = (fracHeatSymbol α t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hf_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **α-fracHeat-smoothed S₀₀ L² mode tight bound.** For `α > 0, t > 0, n ≠ 0`:

    `‖fracHeat(α,t,n) · S₀₀(n) · c‖² ≤ (1/α)^{1/α}·exp(-1/α)/(4·t^{1/α}) · ‖c‖²`

4× sharper than the generic strain bound via tight `|S₀₀(n)|² ≤ ‖n‖²/4`. -/
theorem fracHeat_smoothed_sqgStrain_00_L2_mode_tight
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * c‖ ^ 2
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / (4 * t ^ (1 / α))) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have hs0 : sqgStrainSymbol 0 0 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [hs0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have h1α : 0 < 1 / α := div_pos one_pos hα
    have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
    have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
    have hstrain := sqgStrain_00_sq_le_quarter hn
    have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
    have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
    have hmain : (fracDerivSymbol 1 n) ^ 2 * fracHeatSymbol α t n
        ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) :=
      fracDerivSymbol_sq_mul_fracHeat_le hα one_pos ht n
    have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
      rw [fracDerivSymbol_one_eq hn]
    rw [hfrac1] at hmain
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hfactor_nn : 0 ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) := by
      have h1α : 0 < 1 / α := div_pos one_pos hα
      have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
      have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
      positivity
    calc (fracHeatSymbol α t n) ^ 2 * ‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (fracHeatSymbol α t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hstrain (sq_nonneg _)
      _ = fracHeatSymbol α t n *
          ((latticeNorm n) ^ 2 * fracHeatSymbol α t n) / 4 * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ fracHeatSymbol α t n *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_left hmain hf_nn
      _ ≤ 1 *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_right hf_le hfactor_nn
      _ = (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / (4 * t ^ (1 / α)) * ‖c‖ ^ 2 := by
          rw [one_mul]; field_simp

/-- **α-fracHeat-smoothed S₀₁ L² mode tight bound.** Same structure. -/
theorem fracHeat_smoothed_sqgStrain_01_L2_mode_tight
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((fracHeatSymbol α t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * c‖ ^ 2
    ≤ ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / (4 * t ^ (1 / α))) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have hs0 : sqgStrainSymbol 0 1 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [hs0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have h1α : 0 < 1 / α := div_pos one_pos hα
    have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
    have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (fracHeatSymbol_nonneg α t n)]
    have hstrain := sqgStrain_01_sq_le_quarter hn
    have hf_nn : 0 ≤ fracHeatSymbol α t n := fracHeatSymbol_nonneg α t n
    have hf_le : fracHeatSymbol α t n ≤ 1 := fracHeatSymbol_le_one hα ht.le n
    have hmain : (fracDerivSymbol 1 n) ^ 2 * fracHeatSymbol α t n
        ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) :=
      fracDerivSymbol_sq_mul_fracHeat_le hα one_pos ht n
    have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
      rw [fracDerivSymbol_one_eq hn]
    rw [hfrac1] at hmain
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hfactor_nn : 0 ≤ (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α) := by
      have h1α : 0 < 1 / α := div_pos one_pos hα
      have htα : 0 < t ^ (1 / α) := Real.rpow_pos_of_pos ht _
      have h1kk : 0 < (1 / α) ^ (1 / α) := Real.rpow_pos_of_pos h1α _
      positivity
    calc (fracHeatSymbol α t n) ^ 2 * ‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (fracHeatSymbol α t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul_of_nonneg_left hstrain (sq_nonneg _)
      _ = fracHeatSymbol α t n *
          ((latticeNorm n) ^ 2 * fracHeatSymbol α t n) / 4 * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ fracHeatSymbol α t n *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_left hmain hf_nn
      _ ≤ 1 *
          ((1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / t ^ (1 / α)) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_right hf_le hfactor_nn
      _ = (1 / α) ^ (1 / α) * Real.exp (-(1 / α)) / (4 * t ^ (1 / α)) * ‖c‖ ^ 2 := by
          rw [one_mul]; field_simp

/-! ## Applications: heat-smoothed SQG quantities

Combining the heat smoothing bounds with SQG vorticity/strain structure.
-/

/-- **Heat-smoothed SQG vorticity Ḣˢ bound.** The SQG vorticity after
heat smoothing, evaluated at `n ≠ 0`, satisfies

    `‖heat(t,n) · ω̂(n) · c‖² ≤ exp(-1)/t · ‖c‖²`

using vorticity identity `‖ω̂(n)‖ = ‖n‖` and the k=1 parabolic smoothing.
This gives an L² bound on heat-smoothed vorticity independent of n's
frequency. -/
theorem heat_smoothed_vorticity_L2_mode {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * c‖ ^ 2
    ≤ Real.exp (-1) / t * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : sqgVorticitySymbol 0 = 0 := by
      unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol
      simp
    rw [this, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have : 0 ≤ Real.exp (-1) / t * ‖c‖ ^ 2 := by
      apply mul_nonneg
      · exact div_nonneg (Real.exp_pos _).le ht.le
      · exact sq_nonneg _
    linarith
  · -- Use the sqgVorticity_heat_smoothing_mode we already have
    rw [show ((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * c
        = sqgVorticitySymbol n * ((heatSymbol t n : ℝ) : ℂ) * c from by ring]
    exact sqgVorticity_heat_smoothing_mode ht hn c

/-- **Heat-smoothed SQG velocity Ḣˢ ≤ θ Ḣˢ.** For the SQG velocity
`u = R_⊥ θ` and its heat-smoothed version `e^{tΔ} u`, combining Riesz
Ḣˢ contractivity with heat Ḣˢ contractivity gives:

    `‖e^{tΔ} u‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}`

at every Sobolev level. Mode-level statement. -/
theorem heat_smoothed_sqg_velocity_mode (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (n : Fin 2 → ℤ) (j : Fin 2) (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 *
      ‖((heatSymbol t n : ℝ) : ℂ) *
       (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) * c‖ ^ 2
    ≤ (fracDerivSymbol s n) ^ 2 * ‖c‖ ^ 2 := by
  -- Combine Riesz contractivity with heat contractivity at mode level
  have hheat := heatSymbol_Hs_mode_bound ht s (c := c)
    (n := n)
  -- Step 1: ‖heat · riesz · c‖² ≤ ‖riesz · c‖² (heat contraction)
  -- Step 2: σ_s² · ‖riesz · c‖² ≤ σ_s² · ‖c‖² (Riesz Ḣˢ)
  have hcomb_expr : ((heatSymbol t n : ℝ) : ℂ) *
      (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) * c
      = (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
        (((heatSymbol t n : ℝ) : ℂ) * c) := by ring
  rw [hcomb_expr]
  -- Now: σ_s² · ‖R · (heat · c)‖² ≤ σ_s² · ‖c‖²
  -- Use: σ_s² · ‖R · (heat · c)‖² ≤ σ_s² · ‖heat · c‖² (Riesz contractive)
  --      σ_s² · ‖heat · c‖² ≤ σ_s² · ‖c‖² (heat contractive)
  by_cases hn : n = 0
  · subst hn
    by_cases hj : j = 0
    · simp [hj, rieszSymbol_zero, fracDerivSymbol_zero]
    · simp [hj, rieszSymbol_zero, fracDerivSymbol_zero]
  · have hR_le : ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2 ≤ 1 := by
      have hpyth := rieszSymbol_sum_sq hn
      simp only [Fin.sum_univ_two] at hpyth
      by_cases hj : j = 0
      · simp [hj]; nlinarith [sq_nonneg ‖rieszSymbol 0 n‖]
      · simp [hj, norm_neg]; nlinarith [sq_nonneg ‖rieszSymbol 1 n‖]
    have hR_Hs_bound : (fracDerivSymbol s n) ^ 2 *
        ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
          (((heatSymbol t n : ℝ) : ℂ) * c)‖ ^ 2
        ≤ (fracDerivSymbol s n) ^ 2 *
          ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
      have hhc_nn : 0 ≤ ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2 := sq_nonneg _
      calc (fracDerivSymbol s n) ^ 2 *
            (‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2
              * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            (1 * ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hR_le hhc_nn)
              hσs_nn
        _ = (fracDerivSymbol s n) ^ 2 *
            ‖((heatSymbol t n : ℝ) : ℂ) * c‖ ^ 2 := by ring
    exact le_trans hR_Hs_bound hheat

/-- **Heat-smoothed SQG velocity gradient L² bound.** Each gradient
component after heat smoothing:

    `‖heat(t,n) · ∂̂_i u_j(n) · c‖² ≤ exp(-1)/t · ‖c‖²`

Proof: `‖∂̂_i u_j(n)‖ ≤ ‖n‖`, so `‖heat·∂u·c‖² = heat²·‖∂u‖²·‖c‖² ≤
heat·(L²·heat)·‖c‖² ≤ heat·exp(-1)/t·‖c‖² ≤ exp(-1)/t·‖c‖²`. -/
theorem heat_smoothed_sqgGrad_L2_mode {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (i j : Fin 2) (c : ℂ) :
    ‖((heatSymbol t n : ℝ) : ℂ) * sqgGradSymbol i j n * c‖ ^ 2
    ≤ Real.exp (-1) / t * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : sqgGradSymbol i j 0 = 0 := by
      unfold sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [this, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have : 0 ≤ Real.exp (-1) / t * ‖c‖ ^ 2 :=
      mul_nonneg (div_nonneg (Real.exp_pos _).le ht.le) (sq_nonneg _)
    linarith
  · -- ‖heat·∂u·c‖² = heat²·‖∂u‖²·‖c‖²
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hgrad := sqgGrad_norm_le hn i j
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hgrad_sq_le : ‖sqgGradSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (sqgGradSymbol i j n)]) hgrad
    have hL_sq_heat := latticeNorm_sq_mul_heat_le ht n
    -- Goal: heat² · ‖∂u‖² · ‖c‖² ≤ exp(-1)/t · ‖c‖²
    calc (heatSymbol t n) ^ 2 * ‖sqgGradSymbol i j n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (heatSymbol t n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg _)
      _ = heatSymbol t n * ((latticeNorm n) ^ 2 * heatSymbol t n) * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ heatSymbol t n * (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hL_sq_heat hheat_nn
      _ ≤ 1 * (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_right hheat_le
          exact div_nonneg (Real.exp_pos _).le ht.le
      _ = Real.exp (-1) / t * ‖c‖ ^ 2 := by ring

/-- **Heat-smoothed SQG strain L² bound.** Analogous to the velocity
gradient bound. -/
theorem heat_smoothed_sqgStrain_L2_mode {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (i j : Fin 2) (c : ℂ) :
    ‖((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol i j n * c‖ ^ 2
    ≤ Real.exp (-1) / t * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : sqgStrainSymbol i j 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [this, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have : 0 ≤ Real.exp (-1) / t * ‖c‖ ^ 2 :=
      mul_nonneg (div_nonneg (Real.exp_pos _).le ht.le) (sq_nonneg _)
    linarith
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hstrain := sqgStrain_norm_le hn i j
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hstrain_sq_le : ‖sqgStrainSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol i j n)]) hstrain
    have hL_sq_heat := latticeNorm_sq_mul_heat_le ht n
    calc (heatSymbol t n) ^ 2 * ‖sqgStrainSymbol i j n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (heatSymbol t n) ^ 2 * (latticeNorm n) ^ 2 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hstrain_sq_le (sq_nonneg _)
      _ = heatSymbol t n * ((latticeNorm n) ^ 2 * heatSymbol t n) * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ heatSymbol t n * (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hL_sq_heat hheat_nn
      _ ≤ 1 * (Real.exp (-1) / t) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_right hheat_le
          exact div_nonneg (Real.exp_pos _).le ht.le
      _ = Real.exp (-1) / t * ‖c‖ ^ 2 := by ring

/-- **Heat-smoothed strain (0,0) — tight bound.** Using tight
`|S₀₀(n)|² ≤ ‖n‖²/4`:

    `‖heat(t,n)·S₀₀(n)·c‖² ≤ exp(-1)/(4t) · ‖c‖²`

This is 4× sharper than `heat_smoothed_sqgStrain_L2_mode`. -/
theorem heat_smoothed_sqgStrain_00_L2_mode_tight {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * c‖ ^ 2
    ≤ Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : sqgStrainSymbol 0 0 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [this, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have : 0 ≤ Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
      apply mul_nonneg
      · apply div_nonneg (Real.exp_pos _).le; linarith
      · exact sq_nonneg _
    linarith
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hstrain_tight := sqgStrain_00_sq_le_quarter hn
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hL_sq_heat := latticeNorm_sq_mul_heat_le ht n
    calc (heatSymbol t n) ^ 2 * ‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (heatSymbol t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hstrain_tight (sq_nonneg _)
      _ = heatSymbol t n * ((latticeNorm n) ^ 2 * heatSymbol t n) / 4 * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ heatSymbol t n * (Real.exp (-1) / t) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_left hL_sq_heat hheat_nn
      _ ≤ 1 * (Real.exp (-1) / t) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          apply mul_le_mul_of_nonneg_right hheat_le
          exact div_nonneg (Real.exp_pos _).le ht.le
      _ = Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
          rw [one_mul]; field_simp

/-- **Heat-smoothed strain (0,1) — tight bound.** -/
theorem heat_smoothed_sqgStrain_01_L2_mode_tight {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * c‖ ^ 2
    ≤ Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    have : sqgStrainSymbol 0 1 0 = 0 := by
      unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
    rw [this, mul_zero, zero_mul, norm_zero, sq, mul_zero]
    have : 0 ≤ Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
      apply mul_nonneg
      · apply div_nonneg (Real.exp_pos _).le; linarith
      · exact sq_nonneg _
    linarith
  · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hstrain_tight := sqgStrain_01_sq_le_quarter hn
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht.le n
    have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hL_sq_heat := latticeNorm_sq_mul_heat_le ht n
    calc (heatSymbol t n) ^ 2 * ‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖c‖ ^ 2
        ≤ (heatSymbol t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply mul_le_mul_of_nonneg_left hstrain_tight (sq_nonneg _)
      _ = heatSymbol t n * ((latticeNorm n) ^ 2 * heatSymbol t n) / 4 * ‖c‖ ^ 2 := by
          rw [sq]; ring
      _ ≤ heatSymbol t n * (Real.exp (-1) / t) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          exact mul_le_mul_of_nonneg_left hL_sq_heat hheat_nn
      _ ≤ 1 * (Real.exp (-1) / t) / 4 * ‖c‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
          apply mul_le_mul_of_nonneg_right hheat_le
          exact div_nonneg (Real.exp_pos _).le ht.le
      _ = Real.exp (-1) / (4 * t) * ‖c‖ ^ 2 := by
          rw [one_mul]; field_simp

/-! ## Negative-order fractional derivative (Λ^{-s})

The multiplier `Λ^{-s}(n) = ‖n‖^{-s}` for `n ≠ 0`, zero at `n = 0`.
This is the inverse of `Λ^s = (-Δ)^{s/2}` on mean-zero functions.
Useful for Biot-Savart-like integrations and Sobolev embeddings.

We already have `fracDerivSymbol` which is `‖n‖^s` for any real `s`.
For `s > 0` this is the positive-order; for `s < 0` it's the negative-order.
-/

/-- **Fractional Laplacian inverse symbol.** For `n ≠ 0`:

    `Λ^{-s}(n) = ‖n‖^{-s} = 1/σ_s(n)`

and `0` at `n = 0`. This is `fracDerivSymbol (-s) n`. -/
lemma fracDerivSymbol_neg_inv {s : ℝ} {n : Fin 2 → ℤ} (hn : n ≠ 0) (_hs : 0 < s) :
    fracDerivSymbol (-s) n * fracDerivSymbol s n = 1 := by
  rw [fracDerivSymbol_of_ne_zero _ hn, fracDerivSymbol_of_ne_zero _ hn]
  have hL_pos := latticeNorm_pos hn
  rw [← Real.rpow_add hL_pos]
  simp [Real.rpow_zero]

/-- **Λ^{-s} · Λ^s = 1 at each nonzero mode (squared form).** -/
lemma fracDerivSymbol_sq_neg_inv {s : ℝ} {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    (fracDerivSymbol (-s) n) ^ 2 * (fracDerivSymbol s n) ^ 2 = 1 := by
  rw [fracDerivSymbol_of_ne_zero _ hn, fracDerivSymbol_of_ne_zero _ hn]
  have hL_pos := latticeNorm_pos hn
  have hL_nn := latticeNorm_nonneg n
  rw [show ((latticeNorm n) ^ (-s)) ^ 2 * ((latticeNorm n) ^ s) ^ 2
      = ((latticeNorm n) ^ (-s) * (latticeNorm n) ^ s) ^ 2 from by ring]
  rw [← Real.rpow_add hL_pos, show (-s + s : ℝ) = 0 from by ring, Real.rpow_zero]
  ring

/-- **Negative-order gain.** Applying `Λ^{-s}` to `c` gives a Ḣˢ bound
by the `L²` norm of `c` at each mode `n ≠ 0`:

    `σ_s(n)² · ‖Λ^{-s}(n) · c‖² = ‖c‖²`

i.e., the composition `Λ^s ∘ Λ^{-s}` is the identity. -/
theorem fracDerivSymbol_neg_Hs_equals_L2 {s : ℝ} {n : Fin 2 → ℤ} (hn : n ≠ 0)
    (c : ℂ) :
    (fracDerivSymbol s n) ^ 2 *
      ‖((fracDerivSymbol (-s) n : ℝ) : ℂ) * c‖ ^ 2
    = ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (fracDerivSymbol_nonneg _ _)]
  rw [show (fracDerivSymbol s n) ^ 2 *
      ((fracDerivSymbol (-s) n) ^ 2 * ‖c‖ ^ 2)
      = ((fracDerivSymbol s n) ^ 2 * (fracDerivSymbol (-s) n) ^ 2) * ‖c‖ ^ 2 from by ring]
  rw [show (fracDerivSymbol s n) ^ 2 * (fracDerivSymbol (-s) n) ^ 2
      = (fracDerivSymbol (-s) n) ^ 2 * (fracDerivSymbol s n) ^ 2 from by ring]
  rw [fracDerivSymbol_sq_neg_inv hn, one_mul]

/-- **Ḣˢ-to-L² mapping via Λ^{-s}.** For `s > 0`, the operator
`Λ^{-s}` maps `L²` functions into `Ḣˢ` (and vice versa). Mode-level
bound that the multiplier `Λ^{-s}` satisfies:

    `‖Λ^{-s}(n)‖ ≤ 1`  for all `n ≠ 0`.

(i.e., `Λ^{-s}` is `L²`-contractive on integer lattice with `s ≥ 0`.) -/
theorem fracDerivSymbol_neg_bound_on_lattice {s : ℝ} (hs : 0 ≤ s)
    {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    fracDerivSymbol (-s) n ≤ 1 := by
  rw [fracDerivSymbol_of_ne_zero _ hn]
  have hL : 1 ≤ latticeNorm n := latticeNorm_ge_one_of_ne_zero hn
  have hL_pos : 0 < latticeNorm n := latticeNorm_pos hn
  rw [show (latticeNorm n) ^ (-s) = 1 / (latticeNorm n) ^ s from by
    rw [Real.rpow_neg (le_of_lt hL_pos)]; field_simp]
  rw [div_le_one (Real.rpow_pos_of_pos hL_pos s)]
  calc (1 : ℝ) = (1 : ℝ) ^ s := by rw [Real.one_rpow]
    _ ≤ (latticeNorm n) ^ s := Real.rpow_le_rpow (by norm_num) hL hs

/-! ## Poisson semigroup (α=1/2 fractional heat)

The Poisson semigroup `e^{-t·Λ}` (where `Λ = (-Δ)^{1/2}`) has Fourier
multiplier `exp(-t·‖n‖)`. This corresponds to `α=1/2` in the fractional
heat family. Useful for critical SQG analysis.
-/

/-- **Poisson semigroup symbol.** For `t ≥ 0`:

    `P_t(n) = exp(-t·‖n‖)`. -/
noncomputable def poissonSymbol {d : Type*} [Fintype d]
    (t : ℝ) (n : d → ℤ) : ℝ :=
  Real.exp (-t * latticeNorm n)

@[simp] lemma poissonSymbol_zero_mode {d : Type*} [Fintype d] (t : ℝ) :
    poissonSymbol t (0 : d → ℤ) = 1 := by
  unfold poissonSymbol
  simp [latticeNorm]

lemma poissonSymbol_pos {d : Type*} [Fintype d] (t : ℝ) (n : d → ℤ) :
    0 < poissonSymbol t n := Real.exp_pos _

lemma poissonSymbol_nonneg {d : Type*} [Fintype d] (t : ℝ) (n : d → ℤ) :
    0 ≤ poissonSymbol t n := (poissonSymbol_pos t n).le

@[simp] lemma poissonSymbol_zero_time {d : Type*} [Fintype d] (n : d → ℤ) :
    poissonSymbol 0 n = 1 := by
  unfold poissonSymbol
  simp

/-- **Poisson ≤ 1 for t ≥ 0.** -/
lemma poissonSymbol_le_one {d : Type*} [Fintype d] {t : ℝ} (ht : 0 ≤ t)
    (n : d → ℤ) : poissonSymbol t n ≤ 1 := by
  unfold poissonSymbol
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  apply Real.exp_le_exp.mpr
  have := latticeNorm_nonneg n
  nlinarith

/-- **Poisson semigroup: additive in time.** -/
lemma poissonSymbol_add {d : Type*} [Fintype d] (t₁ t₂ : ℝ) (n : d → ℤ) :
    poissonSymbol (t₁ + t₂) n = poissonSymbol t₁ n * poissonSymbol t₂ n := by
  unfold poissonSymbol
  rw [← Real.exp_add]
  congr 1; ring

/-- **Poisson is α=1/2 case of fracHeat.** -/
theorem fracHeatSymbol_half_eq_poisson (t : ℝ) (n : Fin 2 → ℤ) :
    fracHeatSymbol (1/2) t n = poissonSymbol t n := by
  unfold fracHeatSymbol poissonSymbol
  congr 1
  have hL_nn : 0 ≤ (latticeNorm n : ℝ) := latticeNorm_nonneg n
  rw [show ((latticeNorm n : ℝ) : ℝ) ^ (2 * (1/2 : ℝ)) = latticeNorm n from by
    rw [show (2 * (1/2) : ℝ) = (1 : ℝ) from by norm_num, Real.rpow_one]]

/-- **Poisson smoothing at gradient level.** For `t > 0`:

    `‖n‖ · exp(-t·‖n‖) ≤ exp(-1) / t`

Proof: set `y = t·‖n‖`, use the tangent-line inequality
`x · exp(-x) ≤ exp(-1)` with `x = y`. -/
theorem latticeNorm_mul_poisson_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n : ℝ) * poissonSymbol t n ≤ Real.exp (-1) / t := by
  have h := latticeNorm_rpow_mul_fracHeat_le (α := 1/2) (by norm_num : (0:ℝ) < 1/2) ht n
  rw [fracHeatSymbol_half_eq_poisson,
    show (2 * (1/2:ℝ)) = 1 from by norm_num, Real.rpow_one] at h
  exact h

/-- **Poisson smoothing for `σ_1(n) = ‖n‖`.** -/
theorem fracDerivSymbol_1_mul_poisson_le {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    fracDerivSymbol 1 n * poissonSymbol t n ≤ Real.exp (-1) / t := by
  by_cases hn : n = 0
  · subst hn
    rw [fracDerivSymbol_zero]
    simp
    positivity
  · rw [fracDerivSymbol_one_eq hn]
    exact latticeNorm_mul_poisson_le ht n

/-- **Poisson L²-contractivity (mode-level).** For `t ≥ 0`:

    `‖P_t(n) · c‖² ≤ ‖c‖²`. -/
theorem poissonSymbol_L2_mode_contract {t : ℝ} (ht : 0 ≤ t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    ‖((poissonSymbol t n : ℝ) : ℂ) * c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  rw [← fracHeatSymbol_half_eq_poisson]
  exact fracHeatSymbol_L2_mode_contract (by norm_num : (0:ℝ) < 1/2) ht n c

/-- **Poisson semigroup rpow identity.** For `k > 0`, `t : ℝ`:

    `poissonSymbol t n = (poissonSymbol (t/k) n)^k`. -/
theorem poissonSymbol_rpow_eq {t : ℝ} (n : Fin 2 → ℤ) {k : ℝ} (hk : 0 < k) :
    poissonSymbol t n = (poissonSymbol (t / k) n) ^ k := by
  unfold poissonSymbol
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  have hk_ne : k ≠ 0 := hk.ne'
  field_simp

/-- **General Poisson smoothing at real k > 0.** For `k > 0`, `t > 0`:

    `‖n‖^k · exp(-t·‖n‖) ≤ k^k · exp(-k) / t^k`

using `rpow`. -/
theorem latticeNorm_rpow_mul_poisson_le {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    (latticeNorm n) ^ k * poissonSymbol t n
    ≤ k ^ k * Real.exp (-k) / t ^ k := by
  have h := latticeNorm_rpow_mul_fracHeat_le_general
    (by norm_num : (0:ℝ) < 1/2) hk ht n
  rw [fracHeatSymbol_half_eq_poisson,
    show (k / (2 * (1/2:ℝ))) = k from by field_simp] at h
  exact h

/-- **Poisson smoothing at fracDerivSymbol level.** For `k > 0`, `t > 0`:

    `σ_k(n) · poisson(t, n) ≤ k^k · exp(-k) / t^k` -/
theorem fracDerivSymbol_mul_poisson_le_rpow {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) :
    fracDerivSymbol k n * poissonSymbol t n
    ≤ k ^ k * Real.exp (-k) / t ^ k := by
  by_cases hn : n = 0
  · subst hn
    rw [fracDerivSymbol_zero]
    simp
    have : 0 < k ^ k * Real.exp (-k) / t ^ k := by
      have hk_pos : 0 < k ^ k := Real.rpow_pos_of_pos hk k
      have ht_pos : 0 < t ^ k := Real.rpow_pos_of_pos ht k
      positivity
    linarith
  · rw [fracDerivSymbol_of_ne_zero k hn]
    exact latticeNorm_rpow_mul_poisson_le hk ht n

/-- **Poisson Ḣᵏ mode bound at real k > 0.** Using `‖n‖^k·poisson(t,n) ≤
k^k·exp(-k)/t^k` and `poisson ≤ 1`:

    `σ_k(n) · ‖poisson(t,n) · c‖² ≤ (k^k · exp(-k) / t^k)^? · ‖c‖²`

Wait, this bound has a different structure than heat because Poisson
scales with σ_k (not σ_{2k}). Let me state the correct bound:

    `σ_k(n)² · ‖poisson(t,n) · c‖² ≤ σ_k(n) · (k^k·exp(-k)/t^k) · ‖c‖²`

which uses `σ_k · poisson² ≤ σ_k · poisson ≤ k^k·exp(-k)/t^k`. So:

    `σ_k(n)² · ‖poisson(t,n) · c‖² ≤ σ_k(n) · (k^k·exp(-k)/t^k) · ‖c‖²`

At each individual mode. -/
theorem poissonSymbol_Hk_mode_bound {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (n : Fin 2 → ℤ) (c : ℂ) :
    fracDerivSymbol k n * ‖((poissonSymbol t n : ℝ) : ℂ) * c‖ ^ 2
    ≤ (k ^ k * Real.exp (-k) / t ^ k) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (poissonSymbol_nonneg t n)]
  have hmain := fracDerivSymbol_mul_poisson_le_rpow hk ht n
  have hp_nn : 0 ≤ poissonSymbol t n := poissonSymbol_nonneg t n
  have hp_le : poissonSymbol t n ≤ 1 := poissonSymbol_le_one ht.le n
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hfactor_nn : 0 ≤ k ^ k * Real.exp (-k) / t ^ k := by
    have hk_pos : 0 < k ^ k := Real.rpow_pos_of_pos hk k
    have ht_pos : 0 < t ^ k := Real.rpow_pos_of_pos ht k
    positivity
  calc fracDerivSymbol k n * ((poissonSymbol t n) ^ 2 * ‖c‖ ^ 2)
      = (fracDerivSymbol k n * poissonSymbol t n)
        * (poissonSymbol t n * ‖c‖ ^ 2) := by rw [sq]; ring
    _ ≤ (k ^ k * Real.exp (-k) / t ^ k) * (poissonSymbol t n * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmain (mul_nonneg hp_nn hc_nn)
    _ ≤ (k ^ k * Real.exp (-k) / t ^ k) * (1 * ‖c‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hfactor_nn
        exact mul_le_mul_of_nonneg_right hp_le hc_nn
    _ = (k ^ k * Real.exp (-k) / t ^ k) * ‖c‖ ^ 2 := by ring

/-! ## Integrated tight Ḣˢ strain identity

Lifts the mode-level tight bound `|S₀₀(n)|² + |S₀₁(n)|² = ‖n‖²/4`
to integrated Ḣˢ seminorms.
-/

/-- **Tight Ḣˢ strain identity (integrated sum of S₀₀ + S₀₁).**
For SQG with strain components `S₀₀, S₀₁` related to `θ` by Fourier
multipliers `sqgStrainSymbol 0 0, sqgStrainSymbol 0 1`:

    `‖S₀₀‖²_{Ḣˢ} + ‖S₀₁‖²_{Ḣˢ} = ‖θ‖²_{Ḣ^{s+1}} / 4`

This is an exact equality at every Sobolev level `s`. Uses the mode-level
tight identity `|S₀₀(n)|² + |S₀₁(n)|² = ‖n‖²/4`. -/
theorem sqgStrain_00_01_Hs_sum_eq
    (s : ℝ)
    (θ S00 S01 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff0 : ∀ n, mFourierCoeff S00 n = sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hcoeff1 : ∀ n, mFourierCoeff S01 n = sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s S00 + hsSeminormSq s S01 = hsSeminormSq (s + 1) θ / 4 := by
  unfold hsSeminormSq
  -- Establish summabilities first
  have hsum0 : Summable (fun n ↦ fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S00) n‖ ^ 2) := by
    apply hsum.of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      by_cases hn : n = 0
      · subst hn
        rw [hcoeff0 0]
        simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
          fracDerivSymbol_zero]
      · rw [hcoeff0 n, norm_mul, mul_pow]
        have h00 := sqgStrain_00_sq_le_quarter hn
        have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
        have hc_nn : 0 ≤ ‖mFourierCoeff θ n‖ ^ 2 := sq_nonneg _
        have hfrac := fracDerivSymbol_add_sq s 1 n
        have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
          rw [fracDerivSymbol_one_eq hn]
        calc (fracDerivSymbol s n) ^ 2 *
              (‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
            = ‖sqgStrainSymbol 0 0 n‖ ^ 2 *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by ring
          _ ≤ ((latticeNorm n) ^ 2 / 4) *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h00 (mul_nonneg hσs_nn hc_nn)
          _ ≤ (latticeNorm n) ^ 2 *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hσs_nn hc_nn)
              have : 0 ≤ (latticeNorm n) ^ 2 := sq_nonneg _; linarith
          _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
              rw [hfrac, hfrac1]; ring
  have hsum1 : Summable (fun n ↦ fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S01) n‖ ^ 2) := by
    apply hsum.of_nonneg_of_le
    · intro n; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      by_cases hn : n = 0
      · subst hn
        rw [hcoeff1 0]
        simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
          fracDerivSymbol_zero]
      · rw [hcoeff1 n, norm_mul, mul_pow]
        have h01 := sqgStrain_01_sq_le_quarter hn
        have hσs_nn : 0 ≤ (fracDerivSymbol s n) ^ 2 := sq_nonneg _
        have hc_nn : 0 ≤ ‖mFourierCoeff θ n‖ ^ 2 := sq_nonneg _
        have hfrac := fracDerivSymbol_add_sq s 1 n
        have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
          rw [fracDerivSymbol_one_eq hn]
        calc (fracDerivSymbol s n) ^ 2 *
              (‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
            = ‖sqgStrainSymbol 0 1 n‖ ^ 2 *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by ring
          _ ≤ ((latticeNorm n) ^ 2 / 4) *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h01 (mul_nonneg hσs_nn hc_nn)
          _ ≤ (latticeNorm n) ^ 2 *
              ((fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hσs_nn hc_nn)
              have : 0 ≤ (latticeNorm n) ^ 2 := sq_nonneg _; linarith
          _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
              rw [hfrac, hfrac1]; ring
  -- Establish the pointwise identity
  have hpt : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S00) n‖ ^ 2
        + fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S01) n‖ ^ 2
      = fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 := by
    intro n
    rw [hcoeff0 n, hcoeff1 n]
    by_cases hn : n = 0
    · subst hn
      simp [sqgStrainSymbol, sqgGradSymbol, derivSymbol, rieszSymbol,
        fracDerivSymbol_zero]
    · rw [norm_mul, norm_mul, mul_pow, mul_pow]
      have htight := sqgStrain_eigenvalue_tight hn
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      rw [show fracDerivSymbol s n ^ 2 *
          (‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
          + fracDerivSymbol s n ^ 2 *
          (‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
          = fracDerivSymbol s n ^ 2 *
            ((‖sqgStrainSymbol 0 0 n‖ ^ 2 + ‖sqgStrainSymbol 0 1 n‖ ^ 2) *
             ‖mFourierCoeff (↑↑θ) n‖ ^ 2) from by ring]
      rw [htight, hfrac, hfrac1]; ring
  -- Now the sum identity follows by tsum_add and tsum_div_const
  have hsum_add : Summable (fun n ↦
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S00) n‖ ^ 2
      + fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S01) n‖ ^ 2) :=
    hsum0.add hsum1
  have step1 : (∑' (n : Fin 2 → ℤ), fracDerivSymbol s n ^ 2 *
      ‖mFourierCoeff (↑↑S00) n‖ ^ 2) +
      (∑' (n : Fin 2 → ℤ), fracDerivSymbol s n ^ 2 *
        ‖mFourierCoeff (↑↑S01) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
          (fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S00) n‖ ^ 2
            + fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑S01) n‖ ^ 2) :=
    (hsum0.tsum_add hsum1).symm
  rw [step1]
  rw [show (∑' (n : Fin 2 → ℤ), fracDerivSymbol (s + 1) n ^ 2 *
            ‖mFourierCoeff (↑↑θ) n‖ ^ 2) / 4
      = ∑' (n : Fin 2 → ℤ), fracDerivSymbol (s + 1) n ^ 2 *
            ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 from by rw [tsum_div_const]]
  exact tsum_congr hpt

/-- **L² strain tight identity (from Ḣ⁰ specialization).**

    `‖S₀₀‖²_{Ḣ⁰} + ‖S₀₁‖²_{Ḣ⁰} = ‖θ‖²_{Ḣ¹} / 4`

At mean-zero functions, Ḣ⁰ = L² so this is the L²-level strain tight
identity. -/
theorem sqgStrain_00_01_L2_tight_eq
    (θ S00 S01 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff0 : ∀ n, mFourierCoeff S00 n = sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hcoeff1 : ∀ n, mFourierCoeff S01 n = sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq 0 S00 + hsSeminormSq 0 S01 = hsSeminormSq 1 θ / 4 := by
  have h := sqgStrain_00_01_Hs_sum_eq 0 θ S00 S01 hcoeff0 hcoeff1
    (by simpa using hsum)
  simpa using h

/-! ## Poisson semigroup: integrated contractivity -/

/-- **Poisson L² contractivity (integrated).** For `t ≥ 0`:

    `‖P_t f‖²_{L²} ≤ ‖f‖²_{L²}`

where `P_t f` has Fourier coefficients `poissonSymbol(t,n) · f̂(n)`. -/
theorem poissonSymbol_L2_contractivity {t : ℝ} (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((poissonSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hf_parseval : HasSum (fun n ↦ ‖mFourierCoeff f n‖ ^ 2) (∫ x, ‖f x‖ ^ 2))
    (hu_parseval : HasSum (fun n ↦ ‖mFourierCoeff u n‖ ^ 2) (∫ x, ‖u x‖ ^ 2))
    (hsum : Summable (fun n ↦ ‖mFourierCoeff f n‖ ^ 2)) :
    (∫ x, ‖u x‖ ^ 2) ≤ (∫ x, ‖f x‖ ^ 2) := by
  apply fracHeatSymbol_L2_contractivity (by norm_num : (0:ℝ) < 1/2) ht f u _
    hf_parseval hu_parseval hsum
  intro n; rw [hcoeff n, ← fracHeatSymbol_half_eq_poisson]

/-- **Poisson Ḣˢ contractivity (integrated).** For `t ≥ 0`, any `s`:

    `‖P_t f‖²_{Ḣˢ} ≤ ‖f‖²_{Ḣˢ}` -/
theorem poissonSymbol_Hs_contractivity {s : ℝ} {t : ℝ} (ht : 0 ≤ t)
    (f u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n = ((poissonSymbol t n : ℝ) : ℂ) * mFourierCoeff f n)
    (hsum : Summable (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff f n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s f := by
  apply fracHeatSymbol_Hs_contractivity (by norm_num : (0:ℝ) < 1/2) ht f u _ hsum
  intro n; rw [hcoeff n, ← fracHeatSymbol_half_eq_poisson]

/-- **Heat-smoothed SQG vorticity integrated L² bound.** For `t > 0`:

    `‖e^{tΔ} ω‖²_{L²} ≤ exp(-1)/t · ‖θ‖²_{L²}`

where `ω` is the SQG vorticity (so `ω̂ = sqgVorticitySymbol · θ̂`).
The heat smoothing at `t > 0` converts the Ḣ¹-level vorticity into an
L²-level quantity with parabolic decay `exp(-1)/t`. -/
theorem heat_smoothed_vorticity_L2_integrated {t : ℝ} (ht : 0 < t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-1) / t * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-1) / t *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-1) / t * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  -- Establish the mode-level bound first
  have hmode : ∀ n : Fin 2 → ℤ,
      ‖((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n‖ ^ 2
      ≤ Real.exp (-1) / t * ‖mFourierCoeff θ n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hω0 : sqgVorticitySymbol 0 = 0 := by
        unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hω0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le ht.le) (sq_nonneg _)
    · rw [show ((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n
          = sqgVorticitySymbol n * ((heatSymbol t n : ℝ) : ℂ) * mFourierCoeff θ n from by ring]
      exact sqgVorticity_heat_smoothing_mode ht hn (mFourierCoeff θ n)
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n; rw [hcoeff n]; exact hmode n
  · apply (hsum.mul_left (Real.exp (-1) / t)).of_nonneg_of_le
    · intro n; positivity
    · intro n; rw [hcoeff n]; exact hmode n
  · exact hsum.mul_left _

/-- **Heat-smoothed SQG gradient integrated L² bound.** For `t > 0`:

    `‖e^{tΔ} ∂_i u_j‖²_{L²} ≤ exp(-1)/t · ‖θ‖²_{L²}` -/
theorem heat_smoothed_sqgGrad_L2_integrated {t : ℝ} (ht : 0 < t)
    (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgGradSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-1) / t * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-1) / t *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-1) / t * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heat_smoothed_sqgGrad_L2_mode ht n i j (mFourierCoeff θ n)
  · apply (hsum.mul_left (Real.exp (-1) / t)).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact heat_smoothed_sqgGrad_L2_mode ht n i j (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **Heat-smoothed SQG strain integrated L² bound.** For `t > 0`:

    `‖e^{tΔ} S_{ij}‖²_{L²} ≤ exp(-1)/t · ‖θ‖²_{L²}` -/
theorem heat_smoothed_sqgStrain_L2_integrated {t : ℝ} (ht : 0 < t)
    (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-1) / t * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-1) / t *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-1) / t * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heat_smoothed_sqgStrain_L2_mode ht n i j (mFourierCoeff θ n)
  · apply (hsum.mul_left (Real.exp (-1) / t)).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact heat_smoothed_sqgStrain_L2_mode ht n i j (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **Heat-smoothed SQG strain tight integrated L² bound (4× sharper).**

    `‖e^{tΔ} S₀₀‖²_{L²} ≤ exp(-1)/(4t) · ‖θ‖²_{L²}` -/
theorem heat_smoothed_sqgStrain_00_L2_integrated_tight {t : ℝ} (ht : 0 < t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-1) / (4 * t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-1) / (4 * t) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-1) / (4 * t) * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heat_smoothed_sqgStrain_00_L2_mode_tight ht n (mFourierCoeff θ n)
  · apply (hsum.mul_left (Real.exp (-1) / (4 * t))).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact heat_smoothed_sqgStrain_00_L2_mode_tight ht n (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **Heat-smoothed S₀₁ tight integrated L² bound.** -/
theorem heat_smoothed_sqgStrain_01_L2_integrated_tight {t : ℝ} (ht : 0 < t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-1) / (4 * t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-1) / (4 * t) *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-1) / (4 * t) * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  apply Summable.tsum_le_tsum (f := fun n ↦ ‖mFourierCoeff u n‖ ^ 2)
  · intro n
    rw [hcoeff n]
    exact heat_smoothed_sqgStrain_01_L2_mode_tight ht n (mFourierCoeff θ n)
  · apply (hsum.mul_left (Real.exp (-1) / (4 * t))).of_nonneg_of_le
    · intro n; exact sq_nonneg _
    · intro n
      rw [hcoeff n]
      exact heat_smoothed_sqgStrain_01_L2_mode_tight ht n (mFourierCoeff θ n)
  · exact hsum.mul_left _

/-- **Heat-smoothed SQG vorticity Ḣˢ integrated bound.** For `t ≥ 0`:

    `‖e^{tΔ} ω‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}`

where `u` has Fourier coefficients `heat(t,n) · sqgVorticitySymbol(n) · θ̂(n)`.
Combines heat Ḣˢ-contractivity with vorticity Ḣˢ-Ḣˢ⁺¹ bound. -/
theorem heat_smoothed_vorticity_Hs_integrated (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  -- Extract the mode-level bound once
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hω0 : sqgVorticitySymbol 0 = 0 := by
        unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hω0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (heatSymbol_nonneg t n),
        sqgVorticitySymbol_norm hn]
      have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
      have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
      have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hheat_nn hheat_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          = (heatSymbol t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hheat_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **Heat-smoothed SQG gradient Ḣˢ integrated bound.** For `t ≥ 0`:

    `‖e^{tΔ} ∂_i u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}` -/
theorem heat_smoothed_sqgGrad_Hs_integrated (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgGradSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hg0 : sqgGradSymbol i j 0 = 0 := by
        unfold sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hg0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (heatSymbol_nonneg t n)]
      have hgrad := sqgGrad_norm_le hn i j
      have hgrad_sq_le : ‖sqgGradSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (sqgGradSymbol i j n)]) hgrad
      have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
      have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
      have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hheat_nn hheat_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ‖sqgGradSymbol i j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg _)
        _ = (heatSymbol t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hheat_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **Heat-smoothed SQG strain Ḣˢ integrated bound.** For `t ≥ 0`:

    `‖e^{tΔ} S_{ij}‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}` -/
theorem heat_smoothed_sqgStrain_Hs_integrated (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (i j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol i j n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hs0 : sqgStrainSymbol i j 0 = 0 := by
        unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hs0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (heatSymbol_nonneg t n)]
      have hstrain := sqgStrain_norm_le hn i j
      have hstrain_sq_le : ‖sqgStrainSymbol i j n‖ ^ 2 ≤ (latticeNorm n) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (sqgStrainSymbol i j n)]) hstrain
      have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
      have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
      have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hheat_nn hheat_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ‖sqgStrainSymbol i j n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hstrain_sq_le (sq_nonneg _)
        _ = (heatSymbol t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hheat_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **Heat-smoothed SQG velocity Ḣˢ integrated bound.** For `t ≥ 0`:

    `‖e^{tΔ} u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}`

where velocity `u_j = (R₁θ, -R₀θ)` and heat acts diagonally.
No gain in Sobolev level — both Riesz and heat are contractive. -/
theorem heat_smoothed_sqg_velocity_Hs_integrated (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (j : Fin 2)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) *
        (if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n) *
        mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq s θ := by
  unfold hsSeminormSq
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    -- ‖heat·R·c‖² ≤ ‖c‖²  using heat ≤ 1 and |R| ≤ 1
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (heatSymbol_nonneg t n)]
    have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
    have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
    have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
      pow_le_one₀ hheat_nn hheat_le
    have hR_le : ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2 ≤ 1 := by
      by_cases hn : n = 0
      · subst hn
        by_cases hj : j = 0
        · simp [hj]
        · simp [hj]
      · have hpyth := rieszSymbol_sum_sq hn
        simp only [Fin.sum_univ_two] at hpyth
        by_cases hj : j = 0
        · simp [hj]; nlinarith [sq_nonneg ‖rieszSymbol 0 n‖]
        · simp [hj, norm_neg]; nlinarith [sq_nonneg ‖rieszSymbol 1 n‖]
    have hc_nn : 0 ≤ ‖mFourierCoeff θ n‖ ^ 2 := sq_nonneg _
    calc (heatSymbol t n) ^ 2 *
          ‖(if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n)‖ ^ 2 *
          ‖mFourierCoeff θ n‖ ^ 2
        ≤ 1 * 1 * ‖mFourierCoeff θ n‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc_nn
          exact mul_le_mul hheat_sq_le hR_le (sq_nonneg _) (by linarith)
      _ = ‖mFourierCoeff θ n‖ ^ 2 := by ring
  apply Summable.tsum_le_tsum hmode
  · exact hsum.of_nonneg_of_le (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum

/-- **Heat-smoothed S₀₀ Ḣˢ integrated TIGHT bound (4× sharper).**

    `‖e^{tΔ} S₀₀‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}} / 4` -/
theorem heat_smoothed_sqgStrain_00_Hs_integrated_tight (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ / 4 := by
  unfold hsSeminormSq
  rw [show (∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2) / 4
      = ∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 from by
    rw [← tsum_div_const]]
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hs0 : sqgStrainSymbol 0 0 0 = 0 := by
        unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hs0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      positivity
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (heatSymbol_nonneg t n)]
      have hstrain := sqgStrain_00_sq_le_quarter hn
      have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
      have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
      have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hheat_nn hheat_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ‖sqgStrainSymbol 0 0 n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hstrain (sq_nonneg _)
        _ = (heatSymbol t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) / 4 := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) / 4 := by
            apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
            apply mul_le_mul_of_nonneg_right hheat_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 / 4 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact (hsum.div_const 4).of_nonneg_of_le
      (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum.div_const 4

/-- **Heat-smoothed S₀₁ Ḣˢ integrated TIGHT bound.**

    `‖e^{tΔ} S₀₁‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}} / 4` -/
theorem heat_smoothed_sqgStrain_01_Hs_integrated_tight (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s u ≤ hsSeminormSq (s + 1) θ / 4 := by
  unfold hsSeminormSq
  rw [show (∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2) / 4
      = ∑' (n : Fin 2 → ℤ),
        fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 from by
    rw [← tsum_div_const]]
  have hmode : ∀ n : Fin 2 → ℤ,
      fracDerivSymbol s n ^ 2 * ‖mFourierCoeff (↑↑u) n‖ ^ 2
      ≤ fracDerivSymbol (s + 1) n ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 / 4 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hs0 : sqgStrainSymbol 0 1 0 = 0 := by
        unfold sqgStrainSymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hs0, mul_zero, zero_mul, norm_zero]
      have h0sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0sq, mul_zero]
      positivity
    · rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (heatSymbol_nonneg t n)]
      have hstrain := sqgStrain_01_sq_le_quarter hn
      have hheat_nn : 0 ≤ heatSymbol t n := heatSymbol_nonneg t n
      have hheat_le : heatSymbol t n ≤ 1 := heatSymbol_le_one ht n
      have hheat_sq_le : (heatSymbol t n) ^ 2 ≤ 1 :=
        pow_le_one₀ hheat_nn hheat_le
      have hfrac := fracDerivSymbol_add_sq s 1 n
      have hfrac1 : (fracDerivSymbol 1 n) ^ 2 = (latticeNorm n) ^ 2 := by
        rw [fracDerivSymbol_one_eq hn]
      calc (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ‖sqgStrainSymbol 0 1 n‖ ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)
          ≤ (fracDerivSymbol s n) ^ 2 *
            ((heatSymbol t n) ^ 2 * ((latticeNorm n) ^ 2 / 4) * ‖mFourierCoeff θ n‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hstrain (sq_nonneg _)
        _ = (heatSymbol t n) ^ 2 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) / 4 := by
            ring
        _ ≤ 1 *
            ((fracDerivSymbol s n) ^ 2 * (latticeNorm n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2) / 4 := by
            apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 4)
            apply mul_le_mul_of_nonneg_right hheat_sq_le (by positivity)
        _ = (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2 / 4 := by
            rw [hfrac, hfrac1]; ring
  apply Summable.tsum_le_tsum hmode
  · exact (hsum.div_const 4).of_nonneg_of_le
      (fun n ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmode
  · exact hsum.div_const 4

/-- **Tight heat-smoothed strain Ḣˢ sum bound.** Summing the two tight
strain Ḣˢ bounds:

    `‖e^{tΔ}S₀₀‖²_{Ḣˢ} + ‖e^{tΔ}S₀₁‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}} / 2`

The factor 1/2 reflects the strain-Frobenius tight identity
`Σ‖S_ij‖² = ‖n‖²/2` (and the heat contraction keeps the bound). -/
theorem heat_smoothed_sqgStrain_Hs_sum_le (s : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (θ S00 S01 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff0 : ∀ n, mFourierCoeff S00 n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hcoeff1 : ∀ n, mFourierCoeff S01 n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable
      (fun n ↦ (fracDerivSymbol (s + 1) n) ^ 2 * ‖mFourierCoeff θ n‖ ^ 2)) :
    hsSeminormSq s S00 + hsSeminormSq s S01 ≤ hsSeminormSq (s + 1) θ / 2 := by
  have h00 := heat_smoothed_sqgStrain_00_Hs_integrated_tight s ht θ S00 hcoeff0 hsum
  have h01 := heat_smoothed_sqgStrain_01_Hs_integrated_tight s ht θ S01 hcoeff1 hsum
  linarith

/-- **Poisson-smoothed SQG vorticity L² mode bound.** For `n ≠ 0`, `t > 0`:

    `‖P_t·ω̂·c‖² ≤ exp(-2)/t² · ‖c‖²`

The Poisson smoothing is sharper than heat at vorticity level because
Poisson gains 1 derivative per t (heat gains 2). So `P_t · L ≤ e^{-1}/t`
squared gives `P_t²·L² ≤ e^{-2}/t²`. -/
theorem poisson_smoothed_vorticity_L2_mode {t : ℝ} (ht : 0 < t)
    {n : Fin 2 → ℤ} (hn : n ≠ 0) (c : ℂ) :
    ‖((poissonSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * c‖ ^ 2
    ≤ Real.exp (-2) / t ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (poissonSymbol_nonneg t n),
    sqgVorticitySymbol_norm hn]
  -- Goal: p² · L² · ‖c‖² ≤ exp(-2)/t² · ‖c‖²
  -- Use: (p · L)² ≤ (exp(-1)/t)² = exp(-2)/t²
  have hmain := latticeNorm_mul_poisson_le ht n
  -- hmain: L · p ≤ exp(-1)/t
  have hp_nn : 0 ≤ poissonSymbol t n := poissonSymbol_nonneg t n
  have hL_nn : 0 ≤ (latticeNorm n : ℝ) := latticeNorm_nonneg n
  have hLp_nn : 0 ≤ (latticeNorm n : ℝ) * poissonSymbol t n :=
    mul_nonneg hL_nn hp_nn
  have hexp_nn : 0 ≤ Real.exp (-1) / t :=
    div_nonneg (Real.exp_pos _).le ht.le
  have hmain' : (latticeNorm n * poissonSymbol t n) ^ 2 ≤ (Real.exp (-1) / t) ^ 2 :=
    sq_le_sq' (by linarith) hmain
  have hsq_eq : (Real.exp (-1) / t) ^ 2 = Real.exp (-2) / t ^ 2 := by
    rw [div_pow]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1; ring
  rw [hsq_eq] at hmain'
  have hc_nn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  calc (poissonSymbol t n) ^ 2 * (latticeNorm n : ℝ) ^ 2 * ‖c‖ ^ 2
      = (latticeNorm n * poissonSymbol t n) ^ 2 * ‖c‖ ^ 2 := by ring
    _ ≤ Real.exp (-2) / t ^ 2 * ‖c‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmain' hc_nn

/-- **Poisson-smoothed SQG vorticity L² integrated bound.** For `t > 0`:

    `‖P_t ω‖²_{L²} ≤ exp(-2)/t² · ‖θ‖²_{L²}` -/
theorem poisson_smoothed_vorticity_L2_integrated {t : ℝ} (ht : 0 < t)
    (θ u : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff : ∀ n, mFourierCoeff u n =
      ((poissonSymbol t n : ℝ) : ℂ) * sqgVorticitySymbol n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff u n‖ ^ 2)
    ≤ Real.exp (-2) / t ^ 2 * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  rw [show Real.exp (-2) / t ^ 2 *
        (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = ∑' (n : Fin 2 → ℤ),
        Real.exp (-2) / t ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 from
    (tsum_mul_left).symm]
  have hmode : ∀ n : Fin 2 → ℤ,
      ‖mFourierCoeff (↑↑u) n‖ ^ 2 ≤
      Real.exp (-2) / t ^ 2 * ‖mFourierCoeff (↑↑θ) n‖ ^ 2 := by
    intro n
    rw [hcoeff n]
    by_cases hn : n = 0
    · subst hn
      have hω0 : sqgVorticitySymbol 0 = 0 := by
        unfold sqgVorticitySymbol sqgGradSymbol derivSymbol rieszSymbol; simp
      rw [hω0, mul_zero, zero_mul, norm_zero, sq, mul_zero]
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonneg _)) (sq_nonneg _)
    · exact poisson_smoothed_vorticity_L2_mode ht hn (mFourierCoeff θ n)
  apply Summable.tsum_le_tsum hmode
  · exact (hsum.mul_left (Real.exp (-2) / t ^ 2)).of_nonneg_of_le
      (fun n ↦ sq_nonneg _) hmode
  · exact hsum.mul_left _

/-- **Tight heat-smoothed strain L² sum bound.**

    `‖e^{tΔ}S₀₀‖²_{L²} + ‖e^{tΔ}S₀₁‖²_{L²} ≤ exp(-1)/(2t) · ‖θ‖²_{L²}` -/
theorem heat_smoothed_sqgStrain_L2_sum_le {t : ℝ} (ht : 0 < t)
    (θ S00 S01 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hcoeff0 : ∀ n, mFourierCoeff S00 n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 0 n * mFourierCoeff θ n)
    (hcoeff1 : ∀ n, mFourierCoeff S01 n =
      ((heatSymbol t n : ℝ) : ℂ) * sqgStrainSymbol 0 1 n * mFourierCoeff θ n)
    (hsum : Summable (fun n ↦ ‖mFourierCoeff θ n‖ ^ 2)) :
    (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff S00 n‖ ^ 2)
    + (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff S01 n‖ ^ 2)
    ≤ Real.exp (-1) / (2 * t) *
      (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff θ n‖ ^ 2) := by
  have h00 := heat_smoothed_sqgStrain_00_L2_integrated_tight ht θ S00 hcoeff0 hsum
  have h01 := heat_smoothed_sqgStrain_01_L2_integrated_tight ht θ S01 hcoeff1 hsum
  have ht' : (0 : ℝ) < 4 * t := by linarith
  have h_sum_quarter :
      Real.exp (-1) / (4 * t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      + Real.exp (-1) / (4 * t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2)
      = Real.exp (-1) / (2 * t) * (∑' (n : Fin 2 → ℤ), ‖mFourierCoeff (↑↑θ) n‖ ^ 2) := by
    field_simp
    ring
  linarith [h00, h01, h_sum_quarter]

/-! ## Summary: Full curvature budget at all Sobolev levels

The library now provides a complete Fourier-space curvature budget:

**Symbol infrastructure**
- `hessSymbol`, `sqgGradSymbol`, `sqgStrainSymbol`, `sqgVorticitySymbol`
- `fracDerivSymbol` (positive and negative order via `rpow`)
- `thirdDerivSymbol`, `laplacianSymbol`, `invLaplacianSymbol`
- `heatSymbol`, `poissonSymbol`

**D14 identity and residual**
- `sqg_shear_vorticity_fourier`: `⟨n, S·n⟩ = -L³/2 · θ̂`
- `sqgResidualSymbol_eq_zero`: residual `S_nt - ω/2` is zero
- `residual_Hs_budget`: gSQG residual control at Ḣˢ level

**Tight identities (equalities, not bounds)**
- `|S₀₀|² + |S₀₁|² = ‖n‖²/4` (strain eigenvalue)
- `Σ ‖S_ij‖² = ‖n‖²/2` (strain Frobenius)
- `Σ ‖∂̂_i u_j‖² = ‖n‖²` (gradient Frobenius)
- `‖ω̂‖ = ‖n‖` (vorticity norm)
- `Σ ‖∂u‖² = Σ ‖S‖² + ‖ω‖²/2` (strain-vorticity partition)

**Ḣˢ-level bounds (integrated and mode-level)**
- Velocity: `‖u‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}` (Riesz isometry)
- Strain/gradient: `‖S_ij‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ⁺¹}` (generic) or `/4` (tight)
- Vorticity: `‖ω‖²_{Ḣˢ} = ‖θ‖²_{Ḣˢ⁺¹}` (tight equality)
- Interpolation: mode-level geometric mean bound
- Bernstein-type low/high frequency bounds

**Heat semigroup (all integer and real k > 0)**
- `heatSymbol t n = exp(-t·‖n‖²)`, positivity, boundedness, additivity
- Tangent-line: `x·exp(-x) ≤ exp(-1)`
- k-th parabolic smoothing (ℕ and ℝ): `‖n‖^{2k}·heat(t,n) ≤ k^k·exp(-k)/t^k`
- Ḣᵏ mode and integrated forms for k ≥ 0
- L² and Ḣˢ contractivity (integrated)
- Heat-smoothed SQG: vorticity, velocity, gradient, strain L² bounds
- Tight strain heat-smoothed: 4× sharper via `|S_ij|² ≤ ‖n‖²/4`

**Poisson semigroup (α=1/2 fractional heat)**
- `poissonSymbol t n = exp(-t·‖n‖)`, positivity, boundedness, additivity
- k-th Poisson smoothing (ℕ and ℝ): `‖n‖^k·poisson ≤ k^k·exp(-k)/t^k`
- Mode-level Ḣᵏ Poisson smoothing

**Λ^{-s} (negative-order fractional derivative)**
- `fracDerivSymbol (-s)` is inverse of `fracDerivSymbol s` on each nonzero mode
- Bounded by 1 on integer lattice for `s ≥ 0`

**Structural**
- Incompressibility: `div u = 0`
- `∂u = S + Ω` decomposition with `Ω = ω/2`
- Strain-rotation, Hessian-strain, Biot-Savart-like factorisations
-/

/-! ## §10 Roadmap to conditional Theorem 3 (SQG regularity)

This section states **Theorem 3 conditionally**. The goal is to pin
down *exactly* which analytic facts are load-bearing for the D14
regularity argument, by making them explicit hypotheses in the Lean
statement.

The current repository proves the Fourier-algebraic spine (Theorems 1
and 2 of D14) unconditionally. It does **not** prove Theorem 3. The
three analytic hypotheses below are the pieces the paper argument
borrows from outside the algebraic layer; they are stated here as
abstract propositions and will be replaced by concrete theorems as
the infrastructure for them appears (in mathlib or in this repo).

Current status of each hypothesis:

* `MaterialMaxPrinciple` — placeholder. Needs: DiPerna–Lions-level
  flow theory for a divergence-free velocity with `θ ∈ L²`, plus the
  "free-derivative" property of the D14 identity at κ-maxima.
* `BKMCriterion` — placeholder. Needs: the SQG analogue of the
  Beale–Kato–Majda criterion: `∫₀^T ‖∇θ‖_{L^∞} dt < ∞` ⇒ smooth on
  `[0, T]`.
* `FracSobolevCalculus` — placeholder. Needs: fractional powers of
  `(-Δ)` on `L²(𝕋²)` as self-adjoint operators commuting with the
  Fourier transform. The torus-mode symbols are already in this file;
  the operator-level theory is what is missing.

Each hypothesis is currently a `True`-valued `Prop` — a placeholder
that will be refined as the corresponding infrastructure is formalized.
The point of the current skeleton is to fix the *shape* of the
conditional theorem so every future PR aligns against it. No `sorry`
is used; the placeholders are honest stubs rather than hidden gaps.

When each placeholder is replaced by a concrete proposition and the
skeleton proof body consumes it, `sqg_regularity_conditional` will
carry real mathematical content. When each hypothesis is replaced by
a proved theorem, the result becomes unconditional.
-/

/-- **Material max-principle hypothesis.**

Packages the analytic output of the D14 §9 bounded-κ argument:
if the material max-principle for front curvature holds (the
"free-derivative" property at κ-maxima, incompressibility-driven
material-segment expansion, and far-field control combine to bound
κ globally), then the Ḣ¹ seminorm of `θ(t)` stays bounded for all
time by the initial data.

The `hOnePropagation` field is the real mathematical content: it
asserts the existence of a uniform-in-time Ḣ¹ bound. The three
`True`-valued fields are structural placeholders tracking the three
steps of the §9 argument, to be refined one at a time as the
material-derivative infrastructure is formalized. -/
structure MaterialMaxPrinciple
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- Uniform-in-time Ḣ¹ bound — the consolidated output of the §9
  argument, consumed by `BKMCriterion.hsPropagation`. -/
  hOnePropagation :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 1 (θ t) ≤ M
  /-- Ḣ¹ summability at every forward time. Makes the Ḣ¹ bound in
  `hOnePropagation` non-vacuous: without summability, `hsSeminormSq 1`
  is `0` by the `tsum` convention, and the bound `≤ M` would be
  trivially satisfied for any `M ≥ 0`. Required for interpolation-based
  downstream bounds (see §10.6). -/
  hOneSummability :
    ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : Fin 2 → ℤ =>
        (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff (θ t) n‖ ^ 2)
  /-- `F_ext = 0` at any curvature maximum of a level set of `θ(·, t)`
  (placeholder; contributes to the proof of `hOnePropagation`). -/
  freeDerivativeAtKappaMax : True
  /-- Incompressibility expands the material segment bounding the front
  (placeholder; contributes to the proof of `hOnePropagation`). -/
  materialSegmentExpansion : True
  /-- Far-field bounds on the level-set geometry control the boundary
  term (placeholder; contributes to the proof of `hOnePropagation`). -/
  farFieldBoundary : True

/-- **BKM-type blow-up criterion (Sobolev-scale form).**

A Fourier/Sobolev form of the SQG analogue of the Beale–Kato–Majda
criterion: a uniform-in-time Ḣ¹ bound propagates to a uniform-in-time
Ḣˢ bound for every `s ≥ 0`. This is the composite statement that
classical SQG BKM + fractional Sobolev bootstrap gives.

The `hsPropagation` field is the real mathematical content. The
placeholder field tracks the original time-integrated ∇θ form that
the sharper literature criterion uses. -/
structure BKMCriterion
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- Uniform Ḣ¹ bound propagates to uniform Ḣˢ bound for every
  `s ≥ 0`. This is the BKM + bootstrap package consumed by
  `sqg_regularity_conditional`. -/
  hsPropagation :
    (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 1 (θ t) ≤ M) →
      ∀ s : ℝ, 0 ≤ s →
        ∃ M' : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M'
  /-- Finite `L¹_t L∞_x` gradient integral implies smoothness on
  `[0, T]` (placeholder; the sharper form literature uses). -/
  boundedGradIntegralImpliesSmooth : True

/-- **Fractional Sobolev operator calculus.**

The fractional derivative symbols `fracDerivSymbol s n = ‖n‖^s` are
Fourier multipliers. This structure packages their mode-level content
into a form the regularity argument can consume.

`hsMonotone` is the real mathematical content — the mode-level
Ḣˢ-monotonicity lemma (a direct re-export of `hsSeminormSq_mono`).

`fracLaplacianIsSelfAdjointFourierMultiplier` remains a placeholder
for the upgrade to self-adjoint operators on `L²(𝕋²)` commuting with
the Fourier transform — the operator calculus needed to run the energy
argument that proves `MaterialMaxPrinciple.hOnePropagation` and feeds
`BKMCriterion.hsPropagation` at full rigor. -/
structure FracSobolevCalculus
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- Ḣˢ-monotonicity (mode level): for `s ≤ t`, `‖·‖_{Ḣˢ} ≤ ‖·‖_{Ḣᵗ}`
  provided the Ḣᵗ data is summable. -/
  hsMonotone :
    ∀ (s t : ℝ), s ≤ t → ∀ (τ : ℝ),
      Summable (fun n : Fin 2 → ℤ =>
        (fracDerivSymbol t n) ^ 2 * ‖mFourierCoeff (θ τ) n‖ ^ 2) →
      hsSeminormSq s (θ τ) ≤ hsSeminormSq t (θ τ)
  /-- `(-Δ)^s` is a self-adjoint operator commuting with `𝓕`. Placeholder. -/
  fracLaplacianIsSelfAdjointFourierMultiplier : True

/-- **`FracSobolevCalculus` is unconditionally satisfied.**

The `hsMonotone` field is directly provided by `hsSeminormSq_mono`, and
the remaining placeholder field is `True`. So every time-evolution `θ`
admits a `FracSobolevCalculus` proof — this hypothesis was chosen
specifically to be mode-level content already in the repo.

This theorem lets callers supply `FracSobolevCalculus.ofMathlib θ` as
the `hFSC` argument to `sqg_regularity_conditional`, discharging one
of the three hypotheses unconditionally. -/
theorem FracSobolevCalculus.ofMathlib
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    FracSobolevCalculus θ where
  hsMonotone := fun _s _t hst τ hsum => hsSeminormSq_mono hst (θ τ) hsum
  fracLaplacianIsSelfAdjointFourierMultiplier := trivial

/-- **Conditional Theorem 3 — SQG global regularity (Sobolev form).**

Given the three analytic hypotheses below — `MaterialMaxPrinciple`
and `BKMCriterion` now carry real mathematical content;
`FracSobolevCalculus` remains a structural placeholder that both
refined hypotheses depend on internally — the solution `θ` to SQG
stays bounded in every Sobolev space `Ḣˢ` uniformly in time.

The conclusion `∀ s ≥ 0, ∃ M, ∀ t ≥ 0, hsSeminormSq s (θ t) ≤ M` is
the Sobolev-scale form of global regularity: all fractional derivatives
of `θ` remain in `L²` for all time, with a uniform bound.

**Proof sketch (informal, to be formalized):**
1. `sqg_shear_vorticity_identity` (Basic.lean) gives the mode-level
   identity `Ŝ_nt − ω̂/2 = |k|·sin²(α−β)·θ̂`.
2. `MaterialMaxPrinciple.{freeDerivativeAtKappaMax,
   materialSegmentExpansion, farFieldBoundary}` combine to prove
   `hOnePropagation` (uniform Ḣ¹ bound).
3. `BKMCriterion.hsPropagation` bootstraps the Ḣ¹ bound to every Ḣˢ.
4. `FracSobolevCalculus` licenses the operator calculus used at
   both (2) and (3).

The current proof body consumes `hOnePropagation` and `hsPropagation`
directly. The two remaining placeholders (`freeDerivativeAtKappaMax`
et al., `fracLaplacianIsSelfAdjointFourierMultiplier`) stay as
structural markers of the unproved internal content. -/
theorem sqg_regularity_conditional
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hMMP : MaterialMaxPrinciple θ)
    (hBKM : BKMCriterion θ)
    (_hFSC : FracSobolevCalculus θ) :
    ∀ s : ℝ, 0 ≤ s →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M :=
  hBKM.hsPropagation hMMP.hOnePropagation

/-! ### §10.1 Material derivative scaffolding

This subsection is the foundation for the SQG PDE at the level we can
state without a full material-derivative operator. Two tiers:

1. **Fourier-level velocity multiplier** (`sqgVelocitySymbol`) — pure
   algebraic content, fully proved.
2. **`SqgEvolutionAxioms` structure** — bundles expected consequences
   of the PDE as predicates on `θ`. The `l2Conservation` field is a
   real statement any SQG solution satisfies; the other two fields are
   placeholders pending material-derivative infrastructure
   (DiPerna–Lions / Ambrosio-level flow theory, not in mathlib).

`SqgEvolutionAxioms` is consumed by `SqgSolution.solvesSqgEvolution`
in §10.2, upgrading that field from `True` to real propositional
content.
-/

/-- **SQG velocity Fourier multiplier.** For `θ` with Fourier
coefficients `θ̂`, the SQG velocity `u = (R₁θ, -R₀θ)` has components
with Fourier multipliers:

  * `sqgVelocitySymbol 0 n = rieszSymbol 1 n` (i.e. `m₁(n)` — the
    `R₁` multiplier, recovering `u₀ = R₁θ`),
  * `sqgVelocitySymbol 1 n = -rieszSymbol 0 n` (i.e. `-m₀(n)` —
    recovering `u₁ = -R₀θ`).

This is the mode-level analogue of the velocity operator; defining the
actual velocity field `u : ℝ → Lp ℂ 2 (...)` as a composite of
time-dependent Riesz transforms requires `FracSobolevCalculus` at
operator level. -/
noncomputable def sqgVelocitySymbol (j : Fin 2) (n : Fin 2 → ℤ) : ℂ :=
  if j = 0 then rieszSymbol 1 n else -rieszSymbol 0 n

/-- **SQG velocity multiplier is bounded by 1 pointwise.** Riesz
contractivity per-mode per-component. -/
theorem sqgVelocitySymbol_norm_le_one (j : Fin 2) (n : Fin 2 → ℤ) :
    ‖sqgVelocitySymbol j n‖ ≤ 1 := by
  unfold sqgVelocitySymbol
  split_ifs
  · exact rieszSymbol_norm_le_one 1 n
  · rw [norm_neg]; exact rieszSymbol_norm_le_one 0 n

/-- **SQG velocity multiplier has unit squared-sum at nonzero modes.**
`‖u₀(n)‖² + ‖u₁(n)‖² = 1` for `n ≠ 0` — the per-mode kinetic-energy
identity that sources the global L²-isometry `‖u‖² = ‖θ‖²`. -/
theorem sqgVelocitySymbol_sum_sq {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    ‖sqgVelocitySymbol 0 n‖ ^ 2 + ‖sqgVelocitySymbol 1 n‖ ^ 2 = 1 := by
  unfold sqgVelocitySymbol
  simp only [Fin.isValue, if_true]
  have h := rieszSymbol_sum_sq (n := n) hn
  simpa [Fin.sum_univ_two, add_comm] using h

/-- **SQG velocity multiplier vanishes at the zero mode.** The constant
component of the velocity is zero (u has zero mean, inherited from θ's
zero-mean assumption in Riesz transforms). -/
theorem sqgVelocitySymbol_zero (j : Fin 2) :
    sqgVelocitySymbol j (0 : Fin 2 → ℤ) = 0 := by
  unfold sqgVelocitySymbol
  split_ifs
  · exact rieszSymbol_zero 1
  · rw [rieszSymbol_zero 0, neg_zero]

/-- **SQG velocity multiplier is divergence-free.** Per-mode statement:
`n · u(n) = 0` for any `n ∈ ℤ²`. This is the symbol-level form of
`div u = 0`. Restates `sqg_velocity_divergence_free_symbol` using the
bundled `sqgVelocitySymbol`. -/
theorem sqgVelocitySymbol_divergence_free (n : Fin 2 → ℤ) (z : ℂ) :
    ((n 0 : ℝ) : ℂ) * (sqgVelocitySymbol 0 n * z)
      + ((n 1 : ℝ) : ℂ) * (sqgVelocitySymbol 1 n * z) = 0 := by
  unfold sqgVelocitySymbol
  simp only [Fin.isValue, if_true]
  exact sqg_velocity_divergence_free_symbol n z

/-- **"Is-SQG-velocity-component" predicate.** A purely specificational
predicate asserting that the `L²` function `u_j` is the `j`-th
component of the SQG velocity of `θ`. Matches every Fourier mode.

This replaces a direct `sqgVelocity_fromFourier` operator definition,
which would require `HilbertBasis.repr` machinery to construct `u_j`
from its Fourier coefficients. The predicate form sidesteps the
construction while still letting us state what a "correct" velocity
component is, so existence can be axiomatized separately or discharged
case-by-case when needed. -/
def IsSqgVelocityComponent
    (θ u_j : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (j : Fin 2) : Prop :=
  ∀ n : Fin 2 → ℤ,
    mFourierCoeff u_j n = sqgVelocitySymbol j n * mFourierCoeff θ n

/-- **Fourier coefficients of the zero Lp function vanish.**

For every dimension `d` and every mode `n : Fin d → ℤ`,
`mFourierCoeff (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n = 0`.

Proof: Parseval gives `∑' m, ‖mFourierCoeff 0 m‖² = ∫ ‖0‖² = 0`,
so each term of a summable non-negative series with zero total is
individually zero.

Extracted from the previously-inline proof in
`IsSqgVelocityComponent.of_zero` so that downstream constructors
(notably `IsSqgWeakSolutionTimeTest.zero` in §10.16 and
`sqgNonlinearFlux_zero_theta`) can reuse it without re-deriving the
Parseval argument. -/
theorem mFourierCoeff_zero
    {d : ℕ}
    (n : Fin d → ℤ) :
    mFourierCoeff
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n = 0 := by
  have hP := hasSum_sq_mFourierCoeff
    (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))))
  have hi : (∫ t,
        ‖((0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) : _ → ℂ) t‖ ^ 2)
        = 0 := by simp
  rw [hi] at hP
  have hle :
      ‖mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n‖ ^ 2
        ≤ ∑' m, ‖mFourierCoeff
            (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) m‖ ^ 2 :=
    hP.summable.le_tsum n (fun _ _ => sq_nonneg _)
  rw [hP.tsum_eq] at hle
  have h_sq :
      ‖mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n‖ ^ 2 = 0 :=
    le_antisymm hle (sq_nonneg _)
  have h_norm :
      ‖mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n‖ = 0 := by
    have hmul :
        ‖mFourierCoeff
            (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n‖
          * ‖mFourierCoeff
              (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n‖
            = 0 := by
      nlinarith [h_sq,
        norm_nonneg (mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))) n)]
    exact mul_self_eq_zero.mp hmul
  exact norm_eq_zero.mp h_norm

/-- **The zero function is an SQG-velocity-component of the zero scalar.**
If `θ = 0`, then `u_j = 0` satisfies every Fourier-mode condition
trivially (both sides are zero). A minimal existence example.

Proof now a three-liner after factoring `mFourierCoeff_zero` into
a public lemma (the 30+-line inline Parseval argument has moved
there). -/
theorem IsSqgVelocityComponent.of_zero (j : Fin 2) :
    IsSqgVelocityComponent (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
      (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) j := by
  intro n
  rw [mFourierCoeff_zero]
  simp

/-- **SQG evolution axioms.** Encodes "`θ` solves SQG" at the level we
can state without a full material-derivative operator.

Three fields, all with real mathematical content (no `True`
placeholders remain):

* `l2Conservation`: `L²` norm is constant in time — a direct
  consequence of `∫ θ · div(uθ) dx = 0` plus `div u = 0`.
* `meanConservation`: the spatial mean `∫ θ dx` (equivalently the
  zeroth Fourier coefficient) is preserved along the flow — the
  zero-mode reading of `∂ₜθ + div(uθ) = 0`.
* `velocityIsRieszTransform`: for each axis `j`, an `L²`-valued
  time-indexed velocity component exists which realizes the SQG
  relation `u_j(t) = (±R_{1-j}) θ(t)` mode-by-mode via
  `IsSqgVelocityComponent`.

The three fields together are sufficient to define `SqgSolution` with
real PDE content, to run the §10.5 `L²` bound argument, and to feed
the §10.8 s=2 bootstrap discharge of `BKMCriterionS2` once the energy
estimate is formalized. The full weak form of `∂ₜθ + u·∇θ = 0`
paired against smooth test functions is a strictly stronger refinement
that would consume a distributional / material-derivative
infrastructure not yet built here.

Used as the `solvesSqgEvolution` field of `SqgSolution` in §10.2. -/
structure SqgEvolutionAxioms
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- `L²` norm squared is conserved along the flow: consequence of
  incompressibility plus `∫ θ (u·∇θ) = 0`. -/
  l2Conservation :
    ∀ t : ℝ, 0 ≤ t → hsSeminormSq 0 (θ t) = hsSeminormSq 0 (θ 0)
  /-- Spatial-mean conservation (zero-mode form of `∂ₜθ + div(uθ) = 0`):
  the zeroth Fourier coefficient is preserved for all forward time.
  Equivalent to `∫ θ(t) dx = ∫ θ(0) dx` on `𝕋²`. -/
  meanConservation :
    ∀ t : ℝ, 0 ≤ t →
      mFourierCoeff (θ t) (0 : Fin 2 → ℤ)
        = mFourierCoeff (θ 0) (0 : Fin 2 → ℤ)
  /-- For each axis `j`, a time-indexed `L²` velocity component
  `u_j : ℝ → Lp ℂ 2` exists satisfying the SQG velocity relation
  `u_j(t) = (sgnj · R_{1-j}) θ(t)` mode-by-mode (as encoded by
  `IsSqgVelocityComponent`). -/
  velocityIsRieszTransform :
    ∀ j : Fin 2,
      ∃ u_j : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
        ∀ t : ℝ, IsSqgVelocityComponent (θ t) (u_j t) j

/-- **SQG evolution axioms hold for the identically-zero solution.**
A minimal sanity check: `θ ≡ 0` trivially satisfies the real content
(`l2Conservation`) since both sides of the equation are `0`. -/
theorem SqgEvolutionAxioms.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    SqgEvolutionAxioms θ where
  l2Conservation := fun t _ => by rw [hθ t, hθ 0]
  meanConservation := fun t _ => by rw [hθ t, hθ 0]
  velocityIsRieszTransform := fun j =>
    ⟨fun _ => 0, fun t => by
      rw [hθ t]
      exact IsSqgVelocityComponent.of_zero j⟩

/-! ### §10.2 `SqgSolution` wrapper

The Sobolev-bound conclusion of `sqg_regularity_conditional` is stated
about a bare time-indexed family `θ : ℝ → L²(𝕋²)`. For compositional
proofs it is cleaner to package a solution with its defining data.

`SqgSolution` bundles three things:

1. The time-evolution family `θ`.
2. The `smoothInitialData` predicate: `θ 0` has finite Ḣˢ seminorm for
   some `s > 2` (the standard well-posedness regularity class for
   SQG — one order above the scaling-critical level `s = 1`).
3. The `solvesSqgEvolution` predicate: a `SqgEvolutionAxioms θ` proof.
   Real content (`l2Conservation`) plus two placeholders for the
   full PDE statement.

`SqgSolution.regularity_conditional` then restates
`sqg_regularity_conditional` in the structured form.
-/

/-- **SQG solution.** Bundles a time-evolution `θ`, a smooth-initial-data
predicate, and an `SqgEvolutionAxioms θ` proof. -/
structure SqgSolution where
  /-- The time-evolution of the active scalar on `𝕋²`. -/
  θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))
  /-- Initial data has finite Ḣˢ seminorm at some subcritical
  regularity `s > 2` — the standard SQG well-posedness class. -/
  smoothInitialData :
    ∃ s : ℝ, 2 < s ∧
      Summable (fun n : Fin 2 → ℤ =>
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (θ 0) n‖ ^ 2)
  /-- `θ` satisfies the SQG evolution axioms — real content for
  `l2Conservation`, placeholders for the full PDE. -/
  solvesSqgEvolution : SqgEvolutionAxioms θ

namespace SqgSolution

variable (S : SqgSolution)

/-- **Sobolev bounds conclusion.** Uniform Ḣˢ bounds at every order,
for all forward time — the conclusion of conditional Theorem 3 stated
on an `SqgSolution`. -/
def SobolevBounds : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (S.θ t) ≤ M

/-- **Conditional Theorem 3 (structured form).**

Any `SqgSolution` satisfying the three analytic hypotheses
— `MaterialMaxPrinciple`, `BKMCriterion`, `FracSobolevCalculus` — has
uniform Sobolev bounds at every order.

Proof is direct delegation to `sqg_regularity_conditional`. The
`smoothInitialData` and `solvesSqgEvolution` fields of `S` are not
yet consumed by the proof, because the three analytic hypotheses
currently supply (via `hOnePropagation` and `hsPropagation`) the
content those fields will eventually establish from first principles. -/
theorem regularity_conditional
    (hMMP : MaterialMaxPrinciple S.θ)
    (hBKM : BKMCriterion S.θ)
    (hFSC : FracSobolevCalculus S.θ) :
    S.SobolevBounds :=
  sqg_regularity_conditional S.θ hMMP hBKM hFSC

end SqgSolution

/-! ### §10.3 Trivial-case discharges

The stationary zero solution `θ ≡ 0` is trivially regular: every
Sobolev norm vanishes at every time. We prove this discharges both
refined hypotheses (`MaterialMaxPrinciple.hOnePropagation` and
`BKMCriterion.hsPropagation`) unconditionally in that case.

These aren't mathematically deep, but they demonstrate the structural
point: the hypotheses *can* be discharged to real proofs, not just
axiomatized. Future PRs strengthen from "discharges in the trivial
case" to "discharges under increasingly general hypotheses." -/

/-- **Ḣˢ seminorm of the zero function is zero.** -/
theorem hsSeminormSq_of_zero {d : Type*} [Fintype d] (s : ℝ) :
    hsSeminormSq s (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) = 0 := by
  -- Each mode's coefficient is zero, so each summand is zero.
  unfold hsSeminormSq
  -- Parseval: ∑' ‖mFourierCoeff 0 n‖² = ∫ ‖(0 : Lp) t‖² = 0
  have hParseval := hasSum_sq_mFourierCoeff
    (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
  have h_int : (∫ t, ‖((0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : _ → ℂ) t‖ ^ 2)
        = 0 := by simp
  rw [h_int] at hParseval
  -- From HasSum (‖·̂‖²) 0 with non-neg summands, each is zero
  have h_each : ∀ n : d → ℤ,
      ‖mFourierCoeff (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) n‖ ^ 2 = 0 := by
    intro n
    have hnn : ∀ m, 0 ≤ ‖mFourierCoeff
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) m‖ ^ 2 := fun _ => sq_nonneg _
    have hle : ‖mFourierCoeff
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) n‖ ^ 2
          ≤ ∑' m, ‖mFourierCoeff
            (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) m‖ ^ 2 :=
      hParseval.summable.le_tsum n (fun m _ => hnn m)
    rw [hParseval.tsum_eq] at hle
    exact le_antisymm hle (sq_nonneg _)
  -- Now each weighted term is zero, so the tsum is zero.
  have h_term_zero : ∀ n : d → ℤ,
      (fracDerivSymbol s n) ^ 2
        * ‖mFourierCoeff (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) n‖ ^ 2 = 0 := by
    intro n
    rw [h_each n, mul_zero]
  calc (∑' n : d → ℤ, (fracDerivSymbol s n) ^ 2
          * ‖mFourierCoeff (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) n‖ ^ 2)
      = ∑' _ : d → ℤ, (0 : ℝ) := tsum_congr h_term_zero
    _ = 0 := tsum_zero

/-- **MaterialMaxPrinciple holds for the identically-zero evolution.** -/
theorem MaterialMaxPrinciple.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    MaterialMaxPrinciple θ where
  hOnePropagation := ⟨0, fun t _ => by
    rw [hθ t, hsSeminormSq_of_zero]⟩
  hOneSummability := fun t _ => by
    -- For θ t = 0, each mode coefficient is 0, so each term is 0.
    -- Summable of constant 0 sequence is trivial.
    have h_each : ∀ n : Fin 2 → ℤ,
        (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff (θ t) n‖ ^ 2 = 0 := by
      intro n
      rw [hθ t]
      -- mFourierCoeff (0 : Lp) n = 0 by IsSqgVelocityComponent.of_zero's helper argument
      have hP := hasSum_sq_mFourierCoeff
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
      have hi : (∫ t, ‖((0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : _ → ℂ) t‖ ^ 2)
            = 0 := by simp
      rw [hi] at hP
      have hle : ‖mFourierCoeff
            (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) n‖ ^ 2
            ≤ ∑' m, ‖mFourierCoeff
              (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) m‖ ^ 2 :=
        hP.summable.le_tsum n (fun _ _ => sq_nonneg _)
      rw [hP.tsum_eq] at hle
      have h_sq : ‖mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) n‖ ^ 2 = 0 :=
        le_antisymm hle (sq_nonneg _)
      rw [h_sq, mul_zero]
    have : (fun n : Fin 2 → ℤ =>
          (fracDerivSymbol 1 n) ^ 2 * ‖mFourierCoeff (θ t) n‖ ^ 2)
          = fun _ => 0 := by
      ext n; exact h_each n
    rw [this]
    exact summable_zero
  freeDerivativeAtKappaMax := trivial
  materialSegmentExpansion := trivial
  farFieldBoundary := trivial

/-- **BKMCriterion holds for the identically-zero evolution.** -/
theorem BKMCriterion.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    BKMCriterion θ where
  hsPropagation := fun _ s _ => ⟨0, fun t _ => by
    rw [hθ t, hsSeminormSq_of_zero]⟩
  boundedGradIntegralImpliesSmooth := trivial

/-! ### §10.4 Well-posedness hypothesis + packaged regularity

`SqgWellPosedness` axiomatizes the local-in-time well-posedness of
SQG: any smooth initial data gives rise to *some* `SqgSolution`
matching it at `t = 0`. This is the standard existence theorem for
Ḣˢ data with `s > 2`, and is the last missing link between "regularity
of a given solution" and "regularity for given smooth data."

`sqg_regularity_for_smooth_data` combines well-posedness with the
three analytic hypotheses (assumed to hold for every solution) and
concludes: every smooth initial datum evolves into a solution with
uniform Sobolev bounds at every order. -/

/-- **Well-posedness hypothesis for SQG (placeholder).**

The standard local-in-time existence statement: smooth initial data
yields *some* `SqgSolution` with matching initial condition. The
missing analytic content is Ḣˢ well-posedness of SQG for `s > 2`
(Constantin–Majda–Tabak et al.). -/
structure SqgWellPosedness : Prop where
  /-- Existence of a solution matching prescribed smooth initial data. -/
  existsSolution :
    ∀ θ₀ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
      (∃ s : ℝ, 2 < s ∧
        Summable (fun n : Fin 2 → ℤ =>
          (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ₀ n‖ ^ 2)) →
      ∃ S : SqgSolution, S.θ 0 = θ₀

/-- **Conditional Theorem 3 for smooth initial data.**

Combines well-posedness with the three analytic hypotheses (required
to hold for every solution) and concludes: every smooth initial datum
`θ₀` evolves into a solution with uniform Sobolev bounds at every order.

This is the "user-facing" form of Theorem 3: it takes initial data,
not a pre-baked solution. -/
theorem sqg_regularity_for_smooth_data
    (hWP : SqgWellPosedness)
    (hMMPAll : ∀ S : SqgSolution, MaterialMaxPrinciple S.θ)
    (hBKMAll : ∀ S : SqgSolution, BKMCriterion S.θ)
    (hFSCAll : ∀ S : SqgSolution, FracSobolevCalculus S.θ)
    (θ₀ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hsmooth : ∃ s : ℝ, 2 < s ∧
      Summable (fun n : Fin 2 → ℤ =>
        (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff θ₀ n‖ ^ 2)) :
    ∃ S : SqgSolution, S.θ 0 = θ₀ ∧ S.SobolevBounds := by
  obtain ⟨S, hS0⟩ := hWP.existsSolution θ₀ hsmooth
  exact ⟨S, hS0, S.regularity_conditional (hMMPAll S) (hBKMAll S) (hFSCAll S)⟩

/-! ### §10.5 L² conservation ⟹ uniform L² bound (s=0 degenerate subcase)

A concrete payoff of §10.1's `SqgEvolutionAxioms` integration: we can
discharge the "s=0 degenerate subcase" of `MaterialMaxPrinciple.hOnePropagation`
directly. Given only `l2Conservation`, the `L²` norm is bounded for
all time by its initial value.

This is **not** enough to discharge `hOnePropagation` itself (which is
about `s=1`, i.e. `Ḣ¹`) — L² conservation doesn't control gradients.
But it does demonstrate that once the SQG PDE content is real (as
`SqgEvolutionAxioms.l2Conservation`, `meanConservation`, and
`velocityIsRieszTransform` now are, via `SqgSolution`), a genuine
chain of reasoning produces genuine regularity output. This is the
pattern the full `hOnePropagation` discharge will follow once the
integer-order energy estimate formalized in §10.8 is carried out in
detail: PDE property → conserved quantity → uniform bound.
-/

/-- **Uniform L² bound from L² conservation.** The "s=0 degenerate
subcase" of `MaterialMaxPrinciple.hOnePropagation`.

This is a real theorem — takes the `l2Conservation` field of
`SqgEvolutionAxioms` and produces a uniform-in-time `hsSeminormSq 0`
bound with `M = hsSeminormSq 0 (θ 0)`.

It does not discharge `hOnePropagation` (which needs `Ḣ¹`, not `Ḣ⁰`),
but it demonstrates the pattern: once PDE content is real, genuine
regularity output follows. -/
theorem uniform_l2Bound_of_l2Conservation
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hE : SqgEvolutionAxioms θ) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 0 (θ t) ≤ M :=
  ⟨hsSeminormSq 0 (θ 0), fun t ht => le_of_eq (hE.l2Conservation t ht)⟩

/-- **Uniform L² bound for any `SqgSolution`.** Specializes
`uniform_l2Bound_of_l2Conservation` to the structured form. -/
theorem SqgSolution.uniform_l2Bound (S : SqgSolution) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 0 (S.θ t) ≤ M :=
  uniform_l2Bound_of_l2Conservation S.θ S.solvesSqgEvolution

/-! ### §10.6 Interpolation reduction of BKM scope

`BKMCriterion.hsPropagation` currently axiomatizes the bootstrap
`uniform Ḣ¹ → uniform Ḣˢ` for every `s ≥ 0`. But **interpolation
handles `s ∈ [0, 1]` for free**: on the integer lattice, `‖n‖ ≥ 1` at
every nonzero mode, so `‖n‖^{2s} ≤ ‖n‖²` for `s ≤ 1`, giving
`hsSeminormSq s θ ≤ hsSeminormSq 1 θ` directly (this is
`hsSeminormSq_mono_of_le`).

So we can replace the "all `s ≥ 0`" bootstrap by one that only covers
`s > 1`, without weakening Theorem 3. This subsection:

* Introduces `BKMCriterionHighFreq`, the refined hypothesis covering
  only `s > 1`.
* Shows the original `BKMCriterion` implies it, so every previous
  discharge auto-promotes.
* Gives a trivial-case discharge for the weaker form.
* Proves `sqg_regularity_via_interpolation`: the combined theorem,
  which uses interpolation for the `s ∈ [0, 1]` branch and the
  `BKMCriterionHighFreq` hypothesis for `s > 1`.

Net effect: BKM's axiomatic footprint is reduced by the full
`s ∈ [0, 1]` range — a factor-of-2 shrink in the Sobolev scale BKM
is responsible for.
-/

/-- **Refined BKM criterion (high-frequency only).** The bootstrap
from uniform Ḣ¹ bound to uniform Ḣˢ bound for `s > 1` — the range
where interpolation no longer suffices.

This is strictly weaker than `BKMCriterion.hsPropagation`
(`BKMCriterion.toHighFreq` below), and is all that the combined
regularity theorem actually needs once `SqgEvolutionAxioms` supplies
the L² bound and interpolation handles `s ∈ [0, 1]`. -/
structure BKMCriterionHighFreq
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- Uniform Ḣ¹ bound propagates to uniform Ḣˢ bound for every `s > 1`. -/
  hsPropagationHighFreq :
    (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 1 (θ t) ≤ M) →
      ∀ s : ℝ, 1 < s →
        ∃ M' : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M'

/-- **Original `BKMCriterion` implies the refined high-frequency form.**
Every existing discharge of `BKMCriterion` automatically gives the
weaker `BKMCriterionHighFreq`. -/
theorem BKMCriterion.toHighFreq
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hBKM : BKMCriterion θ) : BKMCriterionHighFreq θ where
  hsPropagationHighFreq :=
    fun h₁ s _ => hBKM.hsPropagation h₁ s (by linarith)

/-- **Refined BKM holds for the identically-zero evolution.** Direct
discharge via `BKMCriterion.of_identically_zero + toHighFreq`. -/
theorem BKMCriterionHighFreq.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) : BKMCriterionHighFreq θ :=
  (BKMCriterion.of_identically_zero θ hθ).toHighFreq

/-- **Interpolation reduction: Theorem 3 from weakened BKM.**

Discharges the full Sobolev-scale regularity conclusion using the
reduced axiomatic footprint:

* `MaterialMaxPrinciple` → uniform Ḣ¹ bound + Ḣ¹ summability
* `SqgEvolutionAxioms.l2Conservation` → uniform L² bound
* `BKMCriterionHighFreq` → Ḣ¹ → Ḣˢ bootstrap for `s > 1` only

For `s ∈ [0, 1]`, interpolation delivers the bound from MMP directly
(no BKM needed; summability comes from `hMMP.hOneSummability`). For
`s > 1`, the refined BKM supplies it.

This makes the axiomatic content of Theorem 3 more precise: BKM is
only needed for `s > 1`, not the full `s ≥ 0` range. -/
theorem sqg_regularity_via_interpolation
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hMMP : MaterialMaxPrinciple θ)
    (hBKM : BKMCriterionHighFreq θ)
    (_hE : SqgEvolutionAxioms θ) :
    ∀ s : ℝ, 0 ≤ s →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M := by
  intro s hs
  -- Get the Ḣ¹ bound once; we'll reuse it.
  obtain ⟨M₁, hM₁⟩ := hMMP.hOnePropagation
  by_cases hs1 : s ≤ 1
  · -- s ∈ [0, 1]: interpolation via hsSeminormSq_mono_of_le, summability from MMP
    refine ⟨M₁, fun t ht => ?_⟩
    calc hsSeminormSq s (θ t)
        ≤ hsSeminormSq 1 (θ t) :=
          hsSeminormSq_mono_of_le hs1 (θ t) (hMMP.hOneSummability t ht)
      _ ≤ M₁ := hM₁ t ht
  · -- s > 1: invoke BKMCriterionHighFreq
    push Not at hs1
    exact hBKM.hsPropagationHighFreq ⟨M₁, hM₁⟩ s hs1

/-- **Structured-form interpolation reduction.** Specializes
`sqg_regularity_via_interpolation` to an `SqgSolution`, consuming
`S.solvesSqgEvolution` for the L² bound automatically. -/
theorem SqgSolution.regularity_via_interpolation (S : SqgSolution)
    (hMMP : MaterialMaxPrinciple S.θ)
    (hBKM : BKMCriterionHighFreq S.θ) :
    S.SobolevBounds :=
  sqg_regularity_via_interpolation S.θ hMMP hBKM S.solvesSqgEvolution

/-! ### §10.7 MMP alone covers the intermediate Sobolev range

Consequence of the internalized `hOneSummability` in
`MaterialMaxPrinciple`: the intermediate range `s ∈ [0, 1]` is fully
discharged by MMP without any BKM hypothesis. This is the cleanest
statement of the interpolation reduction — it says MMP's "uniform
Ḣ¹ bound + summability" is a self-contained piece of content
sufficient for a substantial fragment of Theorem 3 on its own.
-/

/-- **MMP alone ⟹ uniform Ḣˢ bound for `s ∈ [0, 1]`.**

No BKM, no well-posedness, no L² conservation — just MMP's Ḣ¹ bound
and summability internalized into the structure. The uniform bound
at any `s ∈ [0, 1]` is achieved with `M = M₁` from `hOnePropagation`
(the same constant across the whole intermediate range).

This is a real (non-trivial, non-circular) theorem showing that
MMP is a self-contained piece of the Theorem 3 puzzle — it handles
a 50% sub-range of Sobolev indices entirely. -/
theorem MaterialMaxPrinciple.uniform_hs_intermediate
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hMMP : MaterialMaxPrinciple θ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M := by
  intro s _ hs1
  obtain ⟨M₁, hM₁⟩ := hMMP.hOnePropagation
  exact ⟨M₁, fun t ht => le_trans
    (hsSeminormSq_mono_of_le hs1 (θ t) (hMMP.hOneSummability t ht))
    (hM₁ t ht)⟩

/-- **`SqgSolution` form of the intermediate-range theorem.** -/
theorem SqgSolution.uniform_hs_intermediate (S : SqgSolution)
    (hMMP : MaterialMaxPrinciple S.θ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (S.θ t) ≤ M :=
  hMMP.uniform_hs_intermediate

/-! ### §10.8 s=2 bootstrap: integer-order BKM refinement

The `BKMCriterionHighFreq` axiom of §10.6 covers the Ḣˢ bootstrap for
every `s > 1`, which on `𝕋²` involves fractional-calculus
machinery (Kato–Ponce-type product and commutator estimates) that is
not yet available in this development's dependency chain.

**The integer case `s = 2` avoids fractional calculus entirely.** The
Fourier multiplier `|n|²` is polynomial, and at `s = 2` the BKM
energy estimate uses only the classical commutator

  `[Δ, u·∇] = 2 ∇u · ∇² + (Δu) · ∇`,

which is a *differential* operator — its bounds are pointwise,
handled by the real-valued calculus already in Mathlib, with no
Littlewood–Paley decomposition required.

This subsection introduces `BKMCriterionS2`, a strict weakening of
`BKMCriterionHighFreq` that only covers `s ∈ (1, 2]`. Combined with
the §10.6 / §10.7 interpolation from `MaterialMaxPrinciple` on
`s ∈ [0, 1]`, it delivers **a conditional Theorem 3 on the full
Sobolev range `[0, 2]` from an axiomatic footprint that targets only
integer-order regularity**.

Significance: `BKMCriterionS2` is the most restricted BKM-type
hypothesis against which the conditional Theorem 3 can still cover
a non-trivial Sobolev range above the critical index `s = 1`. A
future discharge via a genuine Ḣ² energy estimate — integer-order,
no fractional calculus — would make Theorem 3 unconditional on
`s ∈ [0, 2]`. The `s > 2` tail remains an explicit open axiom.

Provided here:

* `BKMCriterionS2`: refined hypothesis covering `s ∈ (1, 2]`.
* `BKMCriterionHighFreq.toS2`: the HighFreq axiom (and therefore the
  original `BKMCriterion`) implies the S2 form. Every previous
  discharge auto-promotes.
* `BKMCriterionS2.of_identically_zero`: trivial-case discharge.
* `sqg_regularity_via_s2_bootstrap`: combined theorem for
  `s ∈ [0, 2]`.
* `SqgSolution.regularity_via_s2_bootstrap`: structured form.
-/

/-- **S2 BKM criterion.** Uniform Ḣ¹ bound propagates to uniform Ḣˢ
bound for every `s ∈ (1, 2]` — the integer-order range where the BKM
bootstrap uses only classical (differential) commutators, no
fractional Sobolev calculus.

This is strictly weaker than `BKMCriterionHighFreq`
(`BKMCriterionHighFreq.toS2` below). Exactly what the combined
conditional Theorem 3 on `s ∈ [0, 2]` requires. -/
structure BKMCriterionS2
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- Uniform Ḣ¹ bound propagates to uniform Ḣˢ bound for every
  `s ∈ (1, 2]`. Integer-order: no fractional calculus required. -/
  hsPropagationS2 :
    (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq 1 (θ t) ≤ M) →
      ∀ s : ℝ, 1 < s → s ≤ 2 →
        ∃ M' : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M'

/-- **High-frequency BKM implies S2 BKM.** Every existing discharge of
`BKMCriterionHighFreq` auto-promotes to `BKMCriterionS2` — the
restriction `s ≤ 2` is harmless. -/
theorem BKMCriterionHighFreq.toS2
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hBKM : BKMCriterionHighFreq θ) : BKMCriterionS2 θ where
  hsPropagationS2 := fun h₁ s hs1 _ => hBKM.hsPropagationHighFreq h₁ s hs1

/-- **Original BKM criterion implies S2 BKM.** Chain through
`BKMCriterion.toHighFreq` and `BKMCriterionHighFreq.toS2`. -/
theorem BKMCriterion.toS2
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hBKM : BKMCriterion θ) : BKMCriterionS2 θ :=
  hBKM.toHighFreq.toS2

/-- **S2 BKM holds for the identically-zero evolution.** Discharge
via `BKMCriterion.of_identically_zero + toS2`. -/
theorem BKMCriterionS2.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) : BKMCriterionS2 θ :=
  (BKMCriterion.of_identically_zero θ hθ).toS2

/-- **s=2 bootstrap reduction: Theorem 3 on `s ∈ [0, 2]`.**

Discharges the conditional regularity conclusion on the range `[0, 2]`
from a strictly weaker axiomatic footprint than
`sqg_regularity_via_interpolation`:

* `MaterialMaxPrinciple` → uniform Ḣ¹ bound + Ḣ¹ summability
* `BKMCriterionS2` → Ḣ¹ → Ḣˢ bootstrap for `s ∈ (1, 2]` only —
  the integer-order subrange

For `s ∈ [0, 1]`, MMP summability + monotonicity delivers the bound
directly (same argument as §10.6 / §10.7). For `s ∈ (1, 2]`,
`BKMCriterionS2` supplies it.

**The top of the range, `s > 2`, is not covered.** That is the
explicit remaining open axiom. This is the honest partial-win: the
conditional Theorem 3 now holds over `[0, 2]` from an axiomatic
footprint that targets only integer-order Sobolev regularity. -/
theorem sqg_regularity_via_s2_bootstrap
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hMMP : MaterialMaxPrinciple θ)
    (hBKM : BKMCriterionS2 θ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (θ t) ≤ M := by
  intro s _ hs2
  obtain ⟨M₁, hM₁⟩ := hMMP.hOnePropagation
  by_cases hs1 : s ≤ 1
  · -- s ∈ [0, 1]: interpolation via hsSeminormSq_mono_of_le, summability from MMP
    refine ⟨M₁, fun t ht => ?_⟩
    calc hsSeminormSq s (θ t)
        ≤ hsSeminormSq 1 (θ t) :=
          hsSeminormSq_mono_of_le hs1 (θ t) (hMMP.hOneSummability t ht)
      _ ≤ M₁ := hM₁ t ht
  · -- s ∈ (1, 2]: invoke BKMCriterionS2
    push Not at hs1
    exact hBKM.hsPropagationS2 ⟨M₁, hM₁⟩ s hs1 hs2

/-- **Structured-form s=2 bootstrap reduction.** Specializes
`sqg_regularity_via_s2_bootstrap` to an `SqgSolution`, covering the
integer-order range `[0, 2]` of `S.SobolevBounds`. -/
theorem SqgSolution.regularity_via_s2_bootstrap (S : SqgSolution)
    (hMMP : MaterialMaxPrinciple S.θ)
    (hBKM : BKMCriterionS2 S.θ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → hsSeminormSq s (S.θ t) ≤ M :=
  sqg_regularity_via_s2_bootstrap S.θ hMMP hBKM

/-! ### §10.9 Fourier convolution scaffolding

Statement of the SQG evolution at full per-mode Fourier resolution —
i.e., the Duhamel identity

  `θ̂(m, t) − θ̂(m, 0) = − ∫₀ᵗ (u·∇θ)̂(m, τ) dτ`

— expresses the nonlinear flux `(u·∇θ)̂(m)` as a **convolution of
Fourier coefficient sequences**:

  `(u_j ∂_j θ)̂(m) = ∑ ℓ, û_j(m − ℓ) · (i·ℓ_j) · θ̂(ℓ)`.

This section introduces `fourierConvolution` as an abstract operator
on coefficient sequences `ι → ℂ` over any additive commutative group
`ι`, together with the **pointwise convolution bound**
`convolution_bounded_by_product` — the single analytic lemma that
powers the Bochner integrability step when the per-mode flux is later
integrated in time to state the Duhamel identity.

Lemmas provided:

* `fourierConvolution` — the raw bilinear convolution on `ι → ℂ`.
* `fourierConvolution_zero_left` / `_zero_right` — convolution with
  zero is zero (used by the zero-solution discharges).
* `tsum_sq_norm_shift_left` — shift invariance of the ℓ² norm:
  `∑ ℓ, ‖g(m − ℓ)‖² = ∑ ℓ, ‖g(ℓ)‖²`.
* `summable_sq_norm_shift_left` — its summability companion.
* `convolution_bounded_by_product` — the Young + triangle uniform
  bound `‖(f * g)(m)‖ ≤ (‖f‖²_ℓ² + ‖g‖²_ℓ²)/2`.
* `SqgFourierData.fourierConvolution` — thin bundle-level wrapper
  that exposes the operation on two `SqgFourierData` bundles.

The Young-form bound is weaker than full Cauchy–Schwarz
(`√(‖f‖²)·√(‖g‖²)`) but equivalent up to a constant, and sufficient
for the uniform-in-time boundedness that Bochner integrability of the
per-mode flux requires. -/

/-- **Fourier convolution of two coefficient sequences on an additive
commutative group.** Defined by

  `(f * g)(m) := ∑' ℓ, f(ℓ) · g(m − ℓ)`

(with the usual `tsum` convention: returns `0` if the sum diverges).

On the integer lattice `Fin d → ℤ`, this is the Fourier-side of
pointwise multiplication: if `f = f̂ᵤ` and `g = ĝᵥ` are Fourier
coefficient sequences of `L²(𝕋^d)` functions `u`, `v`, then
`fourierConvolution f g` equals the Fourier coefficient sequence of
the pointwise product `u · v` (modulo the usual `2π` normalization
factor absorbed into `mFourierCoeff`). -/
noncomputable def fourierConvolution {ι : Type*} [AddCommGroup ι]
    (f g : ι → ℂ) (m : ι) : ℂ :=
  ∑' ℓ : ι, f ℓ * g (m - ℓ)

/-- **Convolution with the zero sequence on the left is zero.** -/
theorem fourierConvolution_zero_left {ι : Type*} [AddCommGroup ι]
    (g : ι → ℂ) (m : ι) :
    fourierConvolution (fun _ => (0 : ℂ)) g m = 0 := by
  unfold fourierConvolution
  simp

/-- **Convolution with the zero sequence on the right is zero.** -/
theorem fourierConvolution_zero_right {ι : Type*} [AddCommGroup ι]
    (f : ι → ℂ) (m : ι) :
    fourierConvolution f (fun _ => (0 : ℂ)) m = 0 := by
  unfold fourierConvolution
  simp

/-- **Reindexing involution `ℓ ↦ m − ℓ`.** An `Equiv ι ι` whose
inverse is itself; used to transfer summability and `tsum` identities
across the shift. -/
noncomputable def subLeftEquiv {ι : Type*} [AddCommGroup ι]
    (m : ι) : ι ≃ ι where
  toFun ℓ := m - ℓ
  invFun ℓ := m - ℓ
  left_inv ℓ := sub_sub_self m ℓ
  right_inv ℓ := sub_sub_self m ℓ

/-- **Shift invariance of the ℓ² norm (tsum form).**
`∑' ℓ, ‖g(m − ℓ)‖² = ∑' ℓ, ‖g(ℓ)‖²`. -/
theorem tsum_sq_norm_shift_left {ι : Type*} [AddCommGroup ι]
    (g : ι → ℂ) (m : ι) :
    (∑' ℓ : ι, ‖g (m - ℓ)‖ ^ 2) = ∑' ℓ : ι, ‖g ℓ‖ ^ 2 :=
  (subLeftEquiv m).tsum_eq (fun ℓ => ‖g ℓ‖ ^ 2)

/-- **Shift invariance of ℓ² summability.** If `∑' ℓ, ‖g(ℓ)‖²` is
summable, so is `∑' ℓ, ‖g(m − ℓ)‖²`. -/
theorem summable_sq_norm_shift_left {ι : Type*} [AddCommGroup ι]
    (g : ι → ℂ) (m : ι)
    (hg : Summable (fun ℓ => ‖g ℓ‖ ^ 2)) :
    Summable (fun ℓ => ‖g (m - ℓ)‖ ^ 2) :=
  (subLeftEquiv m).summable_iff.mpr hg

/-- **Pointwise convolution bound (Young + triangle form).**

For ℓ²-summable `f`, `g : ι → ℂ`, the convolution at every mode `m`
satisfies the **uniform-in-`m`** bound

  `‖(f * g)(m)‖ ≤ (‖f‖²_ℓ² + ‖g‖²_ℓ²) / 2`.

Proof: Young's inequality `2ab ≤ a² + b²` at every `ℓ` gives
termwise `‖f(ℓ)‖·‖g(m − ℓ)‖ ≤ (‖f(ℓ)‖² + ‖g(m − ℓ)‖²)/2`. Summing,
combined with shift invariance `∑ ℓ, ‖g(m − ℓ)‖² = ∑ ℓ, ‖g(ℓ)‖²` and
the triangle inequality for `tsum`, yields the stated bound.

Weaker than the Cauchy–Schwarz form `√(‖f‖²) · √(‖g‖²)` but
equivalent up to a constant factor. It is the form the §11 Bochner
step will consume: once the ℓ² norms of the per-mode sequences are
uniformly bounded in time, the per-mode flux is uniformly bounded,
hence Bochner-integrable on any finite time interval. -/
theorem convolution_bounded_by_product
    {ι : Type*} [AddCommGroup ι]
    (f g : ι → ℂ)
    (hf : Summable (fun ℓ => ‖f ℓ‖ ^ 2))
    (hg : Summable (fun ℓ => ‖g ℓ‖ ^ 2))
    (m : ι) :
    ‖fourierConvolution f g m‖
      ≤ ((∑' ℓ, ‖f ℓ‖ ^ 2) + (∑' ℓ, ‖g ℓ‖ ^ 2)) / 2 := by
  -- Shift invariance of the ℓ² norm of `g`.
  have hg_shift_sum : Summable (fun ℓ => ‖g (m - ℓ)‖ ^ 2) :=
    summable_sq_norm_shift_left g m hg
  have hg_shift_eq : (∑' ℓ, ‖g (m - ℓ)‖ ^ 2) = ∑' ℓ, ‖g ℓ‖ ^ 2 :=
    tsum_sq_norm_shift_left g m
  -- Young termwise: `‖f(ℓ)‖·‖g(m − ℓ)‖ ≤ (‖f(ℓ)‖² + ‖g(m − ℓ)‖²)/2`.
  have hyoung : ∀ ℓ, ‖f ℓ‖ * ‖g (m - ℓ)‖
      ≤ (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) / 2 := by
    intro ℓ
    have h := two_mul_le_add_sq ‖f ℓ‖ ‖g (m - ℓ)‖
    linarith
  -- Summability of the upper-bound sequence.
  have hbound_sum : Summable (fun ℓ => (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) / 2) := by
    have hadd : Summable (fun ℓ => ‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) :=
      hf.add hg_shift_sum
    simpa [div_eq_mul_inv] using hadd.mul_right ((1 : ℝ) / 2)
  -- Summability of the product sequence via domination by the Young bound.
  have hprod_nn : ∀ ℓ, 0 ≤ ‖f ℓ‖ * ‖g (m - ℓ)‖ := fun _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod_sum : Summable (fun ℓ => ‖f ℓ‖ * ‖g (m - ℓ)‖) :=
    Summable.of_nonneg_of_le hprod_nn hyoung hbound_sum
  -- Triangle inequality for `tsum` (via `norm_mul` on each term).
  have hnorm_eq : (fun ℓ => ‖f ℓ * g (m - ℓ)‖)
      = (fun ℓ => ‖f ℓ‖ * ‖g (m - ℓ)‖) := by
    funext ℓ; exact norm_mul _ _
  have htri_sum : Summable (fun ℓ => ‖f ℓ * g (m - ℓ)‖) := by
    rw [hnorm_eq]; exact hprod_sum
  have htriangle : ‖fourierConvolution f g m‖
      ≤ ∑' ℓ, ‖f ℓ * g (m - ℓ)‖ := by
    unfold fourierConvolution
    exact norm_tsum_le_tsum_norm htri_sum
  -- tsum comparison (HasSum-form, avoids depending on `tsum_le_tsum`'s exact name)
  have hprod_le_bound :
      (∑' ℓ, ‖f ℓ‖ * ‖g (m - ℓ)‖) ≤ ∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) / 2 :=
    hasSum_le hyoung hprod_sum.hasSum hbound_sum.hasSum
  -- `∑' (a + b) = ∑' a + ∑' b` via `HasSum.add`.
  have hadd_eq :
      (∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2))
        = (∑' ℓ, ‖f ℓ‖ ^ 2) + (∑' ℓ, ‖g (m - ℓ)‖ ^ 2) :=
    (hf.hasSum.add hg_shift_sum.hasSum).tsum_eq
  -- Pull out the `/2` factor via `tsum_mul_right` on `* (1/2)`.
  have hdiv_eq :
      (∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) / 2)
        = (∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2)) / 2 := by
    simp [div_eq_mul_inv, tsum_mul_right]
  -- Assemble the final chain.
  calc ‖fourierConvolution f g m‖
      ≤ ∑' ℓ, ‖f ℓ * g (m - ℓ)‖ := htriangle
    _ = ∑' ℓ, ‖f ℓ‖ * ‖g (m - ℓ)‖ := by rw [hnorm_eq]
    _ ≤ ∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2) / 2 := hprod_le_bound
    _ = (∑' ℓ, (‖f ℓ‖ ^ 2 + ‖g (m - ℓ)‖ ^ 2)) / 2 := hdiv_eq
    _ = ((∑' ℓ, ‖f ℓ‖ ^ 2) + (∑' ℓ, ‖g (m - ℓ)‖ ^ 2)) / 2 := by rw [hadd_eq]
    _ = ((∑' ℓ, ‖f ℓ‖ ^ 2) + (∑' ℓ, ‖g ℓ‖ ^ 2)) / 2 := by rw [hg_shift_eq]

namespace SqgFourierData

/-- **Bundle-level convolution wrapper.** Forwards the raw
`fourierConvolution` on the `θ` fields of two `SqgFourierData`
bundles. Convenience for statements that already carry a
`SqgFourierData` structure — reuses all of the `w`, `w_norm_le`,
`ell2_bound` machinery from the Fourier-mode packaging section. -/
noncomputable def fourierConvolution {ι : Type*} [AddCommGroup ι]
    (D₁ D₂ : SqgFourierData ι) : ι → ℂ :=
  _root_.SqgIdentity.fourierConvolution D₁.θ D₂.θ

/-- **Bundle-level convolution bound.** Immediate consequence of
`convolution_bounded_by_product`: if both bundles' `θ`-sequences are
ℓ²-summable, the bundle convolution is pointwise bounded by
`(‖D₁.θ‖²_ℓ² + ‖D₂.θ‖²_ℓ²)/2`. -/
theorem fourierConvolution_bounded_by_product
    {ι : Type*} [AddCommGroup ι]
    (D₁ D₂ : SqgFourierData ι)
    (h₁ : Summable (fun ℓ => ‖D₁.θ ℓ‖ ^ 2))
    (h₂ : Summable (fun ℓ => ‖D₂.θ ℓ‖ ^ 2))
    (m : ι) :
    ‖D₁.fourierConvolution D₂ m‖
      ≤ ((∑' ℓ, ‖D₁.θ ℓ‖ ^ 2) + (∑' ℓ, ‖D₂.θ ℓ‖ ^ 2)) / 2 :=
  convolution_bounded_by_product D₁.θ D₂.θ h₁ h₂ m

end SqgFourierData

/-! ### §10.10 Mode-Lipschitz upgrade to `SqgEvolutionAxioms`

The `meanConservation` field introduced in §10.8 is the `m = 0`
consequence of the SQG evolution: the spatial mean is exactly
preserved. At `m ≠ 0` the Fourier coefficient is *not* conserved —
it evolves via the per-mode flux `(u·∇θ)̂(m, τ)`, which by
`convolution_bounded_by_product` is uniformly bounded in `τ`
(provided `u` and `θ` are ℓ²-summable uniformly in time). The
consequence is a **mode-level Lipschitz-in-time bound**:

  `‖θ̂(m, t₂) − θ̂(m, t₁)‖ ≤ (t₂ − t₁) · C_m`

for some `C_m ≥ 0` that depends on the mode.

This is the differential form of the Duhamel identity — strictly
stronger than `meanConservation` (which is the `C_0 = 0` case at
mode 0) and strictly weaker than the full integral Duhamel (which
would also specify `C_m` as an explicit convolution quantity and
state the identity as an equality with a Bochner integral).

At this level the structure carries enough content to feed the §10.8
s=2 bootstrap once the Bochner integration infrastructure is in
place: the Lipschitz constants `C_m` are exactly the `‖·‖∞` bounds
on the time-integrand of the per-mode Duhamel identity.

This subsection:

* Introduces `ModeLipschitz θ` — a Prop predicate capturing the
  mode-by-mode Lipschitz-in-time bound.
* Shows `ModeLipschitz.of_identically_zero`: the zero solution
  satisfies it trivially with `C_m = 0`.
* States `SqgEvolutionAxioms_strong` — a strengthened version of
  `SqgEvolutionAxioms` that additionally requires `ModeLipschitz`.
  The original `SqgEvolutionAxioms` is kept for backward
  compatibility; `SqgEvolutionAxioms_strong.toWeak` forgets the
  extra content.
* Provides the zero-solution discharge
  `SqgEvolutionAxioms_strong.of_identically_zero`.
-/

/-- **Mode-Lipschitz-in-time property.** Every Fourier coefficient
of `θ(t)` is Lipschitz-in-time, with a mode-specific constant.

This is the differential form of the per-mode Duhamel identity:
the full identity says `θ̂(m, t) − θ̂(m, s) = −∫ₛᵗ F(m, τ) dτ` where
`F` is the convolution flux; bounding `F` uniformly in `τ` (by
`convolution_bounded_by_product`) yields the stated Lipschitz
bound with `C m = sup_τ ‖F(m, τ)‖`. -/
def ModeLipschitz
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop :=
  ∀ m : Fin 2 → ℤ,
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        ‖mFourierCoeff (θ t) m - mFourierCoeff (θ s) m‖
          ≤ (t - s) * C

/-- **Mode-Lipschitz holds trivially for the identically-zero
evolution.** Every Fourier coefficient difference is zero, and any
non-negative constant (take `C = 0`) satisfies the bound. -/
theorem ModeLipschitz.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    ModeLipschitz θ := by
  intro m
  refine ⟨0, le_refl 0, fun s t _ _ => ?_⟩
  rw [hθ t, hθ s, sub_self]
  simp

/-- **Strengthened `SqgEvolutionAxioms`.** Bundles the original axioms
with the mode-Lipschitz predicate — the §10.10 keystone content
established in this section. -/
structure SqgEvolutionAxioms_strong
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop where
  /-- All of the original `SqgEvolutionAxioms` content. -/
  weak : SqgEvolutionAxioms θ
  /-- Per-mode Lipschitz-in-time bound — the §10.10 upgrade. -/
  modeLipschitz : ModeLipschitz θ

namespace SqgEvolutionAxioms_strong

/-- **Forgetful projection.** A strong evolution axiom-set implies
the original one. -/
theorem toWeak {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (h : SqgEvolutionAxioms_strong θ) : SqgEvolutionAxioms θ :=
  h.weak

/-- **Zero-solution discharge for the strengthened structure.** -/
theorem of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    SqgEvolutionAxioms_strong θ where
  weak := SqgEvolutionAxioms.of_identically_zero θ hθ
  modeLipschitz := ModeLipschitz.of_identically_zero θ hθ

end SqgEvolutionAxioms_strong

/-! ### §10.11 SQG-specific Bochner wiring: `DuhamelFlux ⇒ ModeLipschitz`

§10.9 gives the pointwise convolution bound
`convolution_bounded_by_product`. §10.10 states the Lipschitz-in-time
target `ModeLipschitz`. This subsection wires them together via the
Bochner-integral chain

  `‖∫_s^t F(m, τ) dτ‖ ≤ ∫_s^t ‖F(m, τ)‖ dτ ≤ (t − s) · sup_τ ‖F(m, τ)‖`.

Concretely: the `DuhamelFlux` predicate bundles

  (i)  A per-mode flux function `F : (Fin 2 → ℤ) → ℝ → ℂ`.
  (ii) A uniform-in-`τ` bound `sup_τ ‖F(m, τ)‖ ≤ K m` (this is the
       precise shape that `convolution_bounded_by_product` delivers).
  (iii) The per-mode Duhamel integral identity
       `θ̂(m, t) − θ̂(m, s) = − ∫_s^t F(m, τ) dτ`.

`DuhamelFlux.modeLipschitz` then discharges `ModeLipschitz` via a
one-shot application of `MeasureTheory.norm_setIntegral_le_of_norm_le_const`
combined with `Real.volume_Icc` for the interval-length identity.

**This is the SQG-specific wiring** the §10.9 / §10.10 scaffolding
was built for: given a real SQG solution supplying `DuhamelFlux`
(with flux witnessed by a sum of `fourierConvolution`s and the bound
witnessed by `convolution_bounded_by_product` on the velocity/gradient
coefficient sequences), `SqgEvolutionAxioms_strong` follows
immediately. No intermediate integrability argument is needed — the
mathlib lemma packages it inside. -/

/-- **Duhamel-flux representation of an SQG-type evolution.**

Witnesses a per-mode Fourier-side Duhamel identity for `θ`:

  `θ̂(m, t) − θ̂(m, s) = −∫_s^t F(m, τ) dτ`  for  `0 ≤ s ≤ t`,

together with a uniform-in-`τ` bound `‖F(m, τ)‖ ≤ K m` on each mode's
flux — the precise shape that `convolution_bounded_by_product`
delivers when `F(m, τ)` is realized as a sum of
`fourierConvolution`s of ℓ²-summable sequences. -/
def DuhamelFlux
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop :=
  ∃ F : (Fin 2 → ℤ) → ℝ → ℂ,
    (∀ m, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 ≤ τ → ‖F m τ‖ ≤ K) ∧
    (∀ m (s t : ℝ), 0 ≤ s → s ≤ t →
      mFourierCoeff (θ t) m - mFourierCoeff (θ s) m
        = -∫ τ in Set.Icc s t, F m τ)

/-- **Zero-solution discharge of `DuhamelFlux`.** Take the identically-
zero flux; both sides of the Duhamel identity vanish. -/
theorem DuhamelFlux.of_identically_zero
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hθ : ∀ t, θ t = 0) :
    DuhamelFlux θ := by
  refine ⟨fun _ _ => (0 : ℂ), ?_, ?_⟩
  · intro m
    refine ⟨0, le_refl 0, fun τ _ => ?_⟩
    simp
  · intro m s t hs hst
    -- LHS: mFourierCoeff (θ t) m - mFourierCoeff (θ s) m = 0 since θ ≡ 0.
    -- RHS: -∫ τ in Icc s t, 0 = 0.
    rw [hθ t, hθ s, sub_self]
    simp

/-- **SQG-specific Bochner wiring: `DuhamelFlux ⇒ ModeLipschitz`.**

The single analytic fact between the §10.9/§10.10 scaffolding and a
real-solution discharge of `SqgEvolutionAxioms_strong`. Given a
Duhamel-flux witness with per-mode bound `K_m`, every Fourier
coefficient is Lipschitz-in-time with constant `K_m`:

  `‖θ̂(m, t) − θ̂(m, s)‖ ≤ (t − s) · K_m`.

Proof is a one-shot application of
`MeasureTheory.norm_setIntegral_le_of_norm_le_const` on `Set.Icc s t`
under the `volume` measure, combined with `Real.volume_Icc` to
evaluate `volume.real (Icc s t) = t − s` for `s ≤ t`. -/
theorem DuhamelFlux.modeLipschitz
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (h : DuhamelFlux θ) : ModeLipschitz θ := by
  intro m
  obtain ⟨F, hbound, hduhamel⟩ := h
  obtain ⟨K, hK_nn, hK⟩ := hbound m
  refine ⟨K, hK_nn, fun s t hs hst => ?_⟩
  -- Rewrite via Duhamel, drop the leading minus sign.
  rw [hduhamel m s t hs hst, norm_neg]
  -- `Icc s t` has finite `volume`.
  have hvol_lt_top : (volume : Measure ℝ) (Set.Icc s t) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  -- Per-point bound on the flux over `Icc s t`. For τ ∈ Icc s t,
  -- hs : 0 ≤ s and hτ.1 : s ≤ τ give 0 ≤ τ, so the weakened K-bound applies.
  have hbound_on : ∀ τ ∈ Set.Icc s t, ‖F m τ‖ ≤ K :=
    fun τ hτ => hK τ (le_trans hs hτ.1)
  -- Apply the mathlib Bochner lemma.
  have hbochner :
      ‖∫ τ in Set.Icc s t, F m τ‖
        ≤ K * ((volume : Measure ℝ).real (Set.Icc s t)) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol_lt_top hbound_on
  -- Evaluate the interval length.
  have hvol_real : ((volume : Measure ℝ).real (Set.Icc s t)) = t - s := by
    simp [MeasureTheory.measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ t - s by linarith)]
  -- Combine.
  calc ‖∫ τ in Set.Icc s t, F m τ‖
      ≤ K * ((volume : Measure ℝ).real (Set.Icc s t)) := hbochner
    _ = K * (t - s) := by rw [hvol_real]
    _ = (t - s) * K := by ring

/-- **Structured-form: `DuhamelFlux` promotes `SqgEvolutionAxioms`
to `SqgEvolutionAxioms_strong`.** The single remaining step
between "real SQG solution with Duhamel representation" and the
§10.10 keystone structure. -/
theorem SqgEvolutionAxioms.strengthen_of_duhamel
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hE : SqgEvolutionAxioms θ)
    (hD : DuhamelFlux θ) :
    SqgEvolutionAxioms_strong θ where
  weak := hE
  modeLipschitz := hD.modeLipschitz

/-! ### §10.12 Concrete SQG nonlinear flux + PDE-identity promotion

Duhamel keystone: realize the per-mode nonlinear flux `(u · ∇θ)̂(m)`
as a **concrete Lean expression** — a sum over the two velocity
components of `fourierConvolution`s between the velocity Fourier
coefficients and the gradient Fourier coefficients. Bound it via
`convolution_bounded_by_product` on each component. Discharge
`SqgEvolutionAxioms_strong` from a **PDE-level integral identity**
against this specific flux, under two natural ℓ² control
hypotheses (uniform ℓ² bound on velocity coefficients and on
gradient coefficients in time).

After §10.12, the remaining open content of conditional Theorem 3 on
`s ∈ [0, 2]` collapses to:

* `MaterialMaxPrinciple.hOnePropagation` — the D14 §9 geometric
  argument (unchanged).
* `BKMCriterionS2.hsPropagationS2` — integer-order Ḣ² bootstrap
  (unchanged).
* **A single weak-form PDE identity** at the Fourier level, stated
  cleanly as `θ̂(m, t) − θ̂(m, s) = − ∫_s^t (sqgNonlinearFlux)(m, τ) dτ`.
  This is the PDE existence / regularity content; the flux and its
  bound are no longer part of the open axiomatic footprint.

Provided here:

* `sqgNonlinearFlux θ u m` — the concrete flux definition.
* `sqgNonlinearFlux_bounded` — the per-mode pointwise bound derived
  from `convolution_bounded_by_product` on each component.
* `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity` — the PDE-to-
  `SqgEvolutionAxioms_strong` promotion theorem.
-/

/-- **Concrete SQG nonlinear flux at a fixed mode.** The Fourier-side
realization of `(u · ∇θ)̂(m)` as a sum of convolutions:

  `sqgNonlinearFlux θ u m = ∑ⱼ (û_j * (i · ·_j · θ̂))(m)`

where `derivSymbol j ℓ = i · ℓ_j` is the Fourier multiplier of
`∂_j` (from the Riesz library) and `fourierConvolution` is the
§10.9 coefficient-sequence convolution. -/
noncomputable def sqgNonlinearFlux
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (u : Fin 2 → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (m : Fin 2 → ℤ) : ℂ :=
  ∑ j : Fin 2, fourierConvolution
    (fun ℓ => mFourierCoeff (u j) ℓ)
    (fun ℓ => derivSymbol j ℓ * mFourierCoeff θ ℓ) m

/-- **Per-mode bound on `sqgNonlinearFlux`.**

Given ℓ²-summability of (i) the velocity Fourier coefficients of each
`u j` and (ii) the gradient Fourier coefficients `derivSymbol j · θ̂`,
the nonlinear flux at every mode satisfies a Young-type bound inherited
from `convolution_bounded_by_product` on each component, summed over
the two velocity directions via the triangle inequality. -/
theorem sqgNonlinearFlux_bounded
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (u : Fin 2 → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hu_sum : ∀ j, Summable (fun ℓ : Fin 2 → ℤ => ‖mFourierCoeff (u j) ℓ‖ ^ 2))
    (hgrad_sum : ∀ j, Summable
      (fun ℓ : Fin 2 → ℤ => ‖derivSymbol j ℓ * mFourierCoeff θ ℓ‖ ^ 2))
    (m : Fin 2 → ℤ) :
    ‖sqgNonlinearFlux θ u m‖
      ≤ ∑ j : Fin 2,
          ((∑' ℓ, ‖mFourierCoeff (u j) ℓ‖ ^ 2)
            + (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff θ ℓ‖ ^ 2)) / 2 := by
  unfold sqgNonlinearFlux
  calc
    ‖∑ j : Fin 2, fourierConvolution (fun ℓ => mFourierCoeff (u j) ℓ)
        (fun ℓ => derivSymbol j ℓ * mFourierCoeff θ ℓ) m‖
      ≤ ∑ j : Fin 2, ‖fourierConvolution (fun ℓ => mFourierCoeff (u j) ℓ)
          (fun ℓ => derivSymbol j ℓ * mFourierCoeff θ ℓ) m‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin 2,
          ((∑' ℓ, ‖mFourierCoeff (u j) ℓ‖ ^ 2)
            + (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff θ ℓ‖ ^ 2)) / 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact convolution_bounded_by_product _ _ (hu_sum j) (hgrad_sum j) m

/-- **PDE-identity promotion to `SqgEvolutionAxioms_strong`.**

The §10.12 keystone. Given:

* `SqgEvolutionAxioms θ` (from the existing scaffold),
* a concrete velocity field `u : Fin 2 → ℝ → Lp` witnessing the
  Riesz-transform relation for `θ` at every time,
* uniform ℓ²-summability and uniform-in-`τ` tsum bounds on the
  velocity and gradient Fourier coefficients (supplied by the caller
  — a one-line consequence of Parseval + Riesz L²-isometry + MMP's
  Ḣ¹ summability, but deferred here),
* **the PDE integral identity** at the Fourier level against
  `sqgNonlinearFlux`,

this theorem concludes `SqgEvolutionAxioms_strong θ` — the §10.10
keystone structure.

**Only PDE-specific input:** the integral identity `hDuhamel`. The
flux is a concrete Lean expression (`sqgNonlinearFlux`), the bound is
derived (`sqgNonlinearFlux_bounded`), and the Bochner wiring is
already in §10.11 (`DuhamelFlux.modeLipschitz`). -/
theorem SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hE : SqgEvolutionAxioms θ)
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (_hu_velocity : ∀ (j : Fin 2) (τ : ℝ), IsSqgVelocityComponent (θ τ) (u j τ) j)
    (Mu : ℝ) (hMu : 0 ≤ Mu)
    (hu_sum : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      Summable (fun ℓ : Fin 2 → ℤ => ‖mFourierCoeff (u j τ) ℓ‖ ^ 2))
    (hu_bdd : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      (∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2) ≤ Mu)
    (Mg : ℝ) (hMg : 0 ≤ Mg)
    (hgrad_sum : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      Summable (fun ℓ : Fin 2 → ℤ => ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2))
    (hgrad_bdd : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2) ≤ Mg)
    (hDuhamel : ∀ (m : Fin 2 → ℤ) (s t : ℝ), 0 ≤ s → s ≤ t →
      mFourierCoeff (θ t) m - mFourierCoeff (θ s) m
        = -∫ τ in Set.Icc s t, sqgNonlinearFlux (θ τ) (fun j => u j τ) m) :
    SqgEvolutionAxioms_strong θ := by
  -- Build the `DuhamelFlux` witness with flux = sqgNonlinearFlux and K = Mu + Mg.
  have hDF : DuhamelFlux θ := by
    refine ⟨fun m τ => sqgNonlinearFlux (θ τ) (fun j => u j τ) m, ?_, ?_⟩
    · -- Uniform per-mode bound (applies at τ ≥ 0).
      intro m
      refine ⟨Mu + Mg, by linarith, fun τ hτ => ?_⟩
      have hFlux :=
        sqgNonlinearFlux_bounded (θ τ) (fun j => u j τ)
          (fun j => hu_sum j τ hτ) (fun j => hgrad_sum j τ hτ) m
      -- Each summand is at most (Mu + Mg)/2; `Fin 2` has two terms.
      have hterm : ∀ j : Fin 2,
          ((∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2)
            + (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2)) / 2
          ≤ (Mu + Mg) / 2 := by
        intro j
        have h1 := hu_bdd j τ hτ
        have h2 := hgrad_bdd j τ hτ
        linarith
      have hsum_le :
          ∑ j : Fin 2,
              ((∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2)
                + (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2)) / 2
            ≤ Mu + Mg := by
        calc
          ∑ j : Fin 2,
              ((∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2)
                + (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2)) / 2
            ≤ ∑ _j : Fin 2, (Mu + Mg) / 2 :=
                Finset.sum_le_sum (fun j _ => hterm j)
          _ = (Mu + Mg) / 2 + (Mu + Mg) / 2 := Fin.sum_univ_two _
          _ = Mu + Mg := by ring
      linarith
    · -- Duhamel identity.
      intro m s t hs hst
      exact hDuhamel m s t hs hst
  exact hE.strengthen_of_duhamel hDF

/-! ### §10.13 ℓ²-control helpers for `sqgNonlinearFlux_bounded`

§10.12's `of_sqgDuhamelIdentity` takes four ℓ²-control hypotheses.
Three of the four are one-line consequences of data the repo already
provides:

* Velocity Fourier summability at fixed `τ`: automatic from
  `hasSum_sq_mFourierCoeff` applied to `u j τ : Lp`.
* Gradient Fourier summability: ℓ² domination by the
  `(fracDerivSymbol 1)`-weighted series, whose summability comes
  from `MaterialMaxPrinciple.hOneSummability`.
* Velocity Fourier ℓ² tsum bound: per-mode `‖sqgVelocitySymbol‖ ≤ 1`
  combined with `IsSqgVelocityComponent` gives
  `‖u_j‖²_ℓ² ≤ ‖θ‖²_ℓ²` directly.

This subsection formalizes those three lines as named helpers.
Callers of `of_sqgDuhamelIdentity` can use them to derive the four
control hypotheses from `SqgEvolutionAxioms` + `MaterialMaxPrinciple`
+ the `IsSqgVelocityComponent` witness alone (plus one external
`∫ |θ|²` bound — the one piece that requires combining
`l2Conservation` with `meanConservation`, deferred). -/

/-- **Single-coordinate derivative symbol bound.** At every lattice
point, `‖derivSymbol j n‖² ≤ (fracDerivSymbol 1 n)²`. At `n ≠ 0` this
is `|n_j|² ≤ ‖n‖²`; at `n = 0` both sides vanish. -/
lemma norm_derivSymbol_sq_le_fracDerivSymbol_one_sq
    (j : Fin 2) (n : Fin 2 → ℤ) :
    ‖derivSymbol j n‖ ^ 2 ≤ (fracDerivSymbol 1 n) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    simp [derivSymbol]
  · rw [norm_derivSymbol_sq, fracDerivSymbol_one_eq hn]
    exact sq_le_latticeNorm_sq n j

/-- **Gradient Fourier summability from Ḣ¹ summability.** -/
lemma gradient_fourier_summable_of_hOneSummability
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (j : Fin 2)
    (hθ_sum : Summable
      (fun ℓ : Fin 2 → ℤ => (fracDerivSymbol 1 ℓ) ^ 2 * ‖mFourierCoeff θ ℓ‖ ^ 2)) :
    Summable
      (fun ℓ : Fin 2 → ℤ => ‖derivSymbol j ℓ * mFourierCoeff θ ℓ‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ hθ_sum
  intro ℓ
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (norm_derivSymbol_sq_le_fracDerivSymbol_one_sq j ℓ) (sq_nonneg _)

/-- **Gradient Fourier ℓ² tsum bound by Ḣ¹ seminorm.** -/
lemma gradient_fourier_tsum_le_hsSeminormSq_one
    (θ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (j : Fin 2)
    (hθ_sum : Summable
      (fun ℓ : Fin 2 → ℤ => (fracDerivSymbol 1 ℓ) ^ 2 * ‖mFourierCoeff θ ℓ‖ ^ 2)) :
    (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff θ ℓ‖ ^ 2) ≤ hsSeminormSq 1 θ := by
  unfold hsSeminormSq
  refine hasSum_le ?_
    (gradient_fourier_summable_of_hOneSummability θ j hθ_sum).hasSum
    hθ_sum.hasSum
  intro ℓ
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (norm_derivSymbol_sq_le_fracDerivSymbol_one_sq j ℓ) (sq_nonneg _)

/-- **Velocity Fourier summability** — automatic from Parseval on
`u_j : Lp`. -/
lemma velocity_fourier_summable
    (u_j : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Summable (fun ℓ : Fin 2 → ℤ => ‖mFourierCoeff u_j ℓ‖ ^ 2) :=
  (hasSum_sq_mFourierCoeff u_j).summable

/-- **Velocity Fourier ℓ² tsum bound from `IsSqgVelocityComponent`.**
Per-mode `‖sqgVelocitySymbol‖ ≤ 1` gives `‖u_j‖²_ℓ² ≤ ‖θ‖²_ℓ²`. -/
lemma velocity_fourier_tsum_le_of_IsSqgVelocityComponent
    (θ u_j : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (j : Fin 2)
    (hvel : IsSqgVelocityComponent θ u_j j) :
    (∑' ℓ, ‖mFourierCoeff u_j ℓ‖ ^ 2)
      ≤ ∑' ℓ, ‖mFourierCoeff θ ℓ‖ ^ 2 := by
  refine hasSum_le ?_
    (hasSum_sq_mFourierCoeff u_j).summable.hasSum
    (hasSum_sq_mFourierCoeff θ).summable.hasSum
  intro ℓ
  rw [hvel ℓ, norm_mul, mul_pow]
  have h1 : ‖sqgVelocitySymbol j ℓ‖ ^ 2 ≤ 1 := by
    have h := sqgVelocitySymbol_norm_le_one j ℓ
    have hnn := norm_nonneg (sqgVelocitySymbol j ℓ)
    nlinarith
  calc ‖sqgVelocitySymbol j ℓ‖ ^ 2 * ‖mFourierCoeff θ ℓ‖ ^ 2
      ≤ 1 * ‖mFourierCoeff θ ℓ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = ‖mFourierCoeff θ ℓ‖ ^ 2 := one_mul _

/-! ### §10.14 Full L² conservation + MMP-keyed promotion

The last external hypothesis in §10.12's `of_sqgDuhamelIdentity` is
`Mu` — a uniform ℓ² tsum bound on the velocity Fourier coefficients.
Combining `l2Conservation` (which controls the non-zero modes) with
`meanConservation` (which controls the zero mode) gives **full L²
conservation** of `θ`; by Parseval this translates to conservation
of `∑' n, ‖θ̂(τ) n‖²`, closing the loop.

This subsection ships:

* `l2_integral_eq_fourier_zero_sq_plus_hsSeminormSq_zero` — the
  Parseval "split-at-zero-mode" identity, writing the full ℓ² tsum
  as the zero-mode contribution plus `hsSeminormSq 0`.
* `theta_fourier_tsum_conserved` — given `SqgEvolutionAxioms θ`,
  `∑' n, ‖θ̂(τ) n‖² = ∑' n, ‖θ̂(0) n‖²` for every forward time.
* `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP` — the
  fully-internalized promotion theorem. Consumes **only**
  `SqgEvolutionAxioms + MaterialMaxPrinciple + velocity witness +
  the PDE integral identity**.

**The headline reading of the repo after §10.14:**

> "Give me a solution satisfying `SqgEvolutionAxioms` (which already
> requires mean + L² conservation + Riesz-transform velocity),
> `MaterialMaxPrinciple` (uniform Ḣ¹ bound), and the integral form
> of the SQG PDE against `sqgNonlinearFlux` — and I will hand you
> uniform Ḣˢ bounds for every `s ∈ [0, 2]`."
-/

/-- **Parseval split at the zero mode.** For any `f : L²(𝕋²)`,

  `∫ ‖f‖² = ‖f̂(0)‖² + hsSeminormSq 0 f`.

Since `fracDerivSymbol 0` vanishes at `n = 0` and equals `1` at every
other mode, `hsSeminormSq 0 f` sums the squared Fourier coefficients
over `n ≠ 0`, leaving the zero-mode contribution separated. -/
lemma l2_integral_eq_fourier_zero_sq_plus_hsSeminormSq_zero
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    (∫ t, ‖f t‖ ^ 2) = ‖mFourierCoeff f (0 : Fin 2 → ℤ)‖ ^ 2 + hsSeminormSq 0 f := by
  classical
  have hP : HasSum
      (fun n : Fin 2 → ℤ => ‖mFourierCoeff f n‖ ^ 2) (∫ t, ‖f t‖ ^ 2) :=
    hasSum_sq_mFourierCoeff f
  have hsum := hP.summable
  have h1 :
      (∑' n : Fin 2 → ℤ, ‖mFourierCoeff f n‖ ^ 2)
        = ‖mFourierCoeff f (0 : Fin 2 → ℤ)‖ ^ 2
          + ∑' n : Fin 2 → ℤ, ite (n = 0) 0 (‖mFourierCoeff f n‖ ^ 2) :=
    hsum.tsum_eq_add_tsum_ite 0
  rw [hP.tsum_eq] at h1
  rw [h1]
  congr 1
  -- Show the residual tsum equals `hsSeminormSq 0 f`.
  unfold hsSeminormSq
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst hn; simp [fracDerivSymbol_zero]
  · rw [if_neg hn, fracDerivSymbol_of_ne_zero 0 hn, Real.rpow_zero]
    ring

/-- **Full Fourier ℓ² tsum conservation for SQG solutions.**

Given `SqgEvolutionAxioms θ`, for every forward time `τ ≥ 0`,

  `∑' n, ‖θ̂(τ) n‖² = ∑' n, ‖θ̂(0) n‖²`.

Proof: Parseval's "split at the zero mode" identity writes both sides
as `‖θ̂(·) 0‖² + hsSeminormSq 0 (θ ·)`. The first term is conserved
by `meanConservation`; the second by `l2Conservation`. -/
lemma theta_fourier_tsum_conserved
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hE : SqgEvolutionAxioms θ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∑' n, ‖mFourierCoeff (θ τ) n‖ ^ 2)
      = ∑' n, ‖mFourierCoeff (θ 0) n‖ ^ 2 := by
  rw [(hasSum_sq_mFourierCoeff (θ τ)).tsum_eq,
      (hasSum_sq_mFourierCoeff (θ 0)).tsum_eq,
      l2_integral_eq_fourier_zero_sq_plus_hsSeminormSq_zero (θ τ),
      l2_integral_eq_fourier_zero_sq_plus_hsSeminormSq_zero (θ 0),
      hE.meanConservation τ hτ, hE.l2Conservation τ hτ]

/-- **MMP-keyed promotion to `SqgEvolutionAxioms_strong`.** The clean
form the §10.9–§10.13 machinery was built for.

Consumes:
* `SqgEvolutionAxioms θ`
* `MaterialMaxPrinciple θ`
* velocity field `u` + `IsSqgVelocityComponent` witness
* the PDE integral identity at the Fourier level against
  `sqgNonlinearFlux`

Concludes `SqgEvolutionAxioms_strong θ`. All four ℓ² control
hypotheses of `of_sqgDuhamelIdentity` are discharged internally:

* Velocity summability: `velocity_fourier_summable` (Parseval on
  `u j τ : Lp`).
* Velocity tsum bound: `velocity_fourier_tsum_le_of_IsSqgVelocityComponent`
  combined with `theta_fourier_tsum_conserved` gives a constant
  `Mu := ∑' n, ‖θ̂(0) n‖²`.
* Gradient summability: `gradient_fourier_summable_of_hOneSummability`
  against `MMP.hOneSummability`.
* Gradient tsum bound: `gradient_fourier_tsum_le_hsSeminormSq_one`
  combined with `MMP.hOnePropagation` gives `Mg := M₁`. -/
theorem SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hE : SqgEvolutionAxioms θ)
    (hMMP : MaterialMaxPrinciple θ)
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hu_velocity : ∀ (j : Fin 2) (τ : ℝ), IsSqgVelocityComponent (θ τ) (u j τ) j)
    (hDuhamel : ∀ (m : Fin 2 → ℤ) (s t : ℝ), 0 ≤ s → s ≤ t →
      mFourierCoeff (θ t) m - mFourierCoeff (θ s) m
        = -∫ τ in Set.Icc s t, sqgNonlinearFlux (θ τ) (fun j => u j τ) m) :
    SqgEvolutionAxioms_strong θ := by
  -- Velocity tsum bound Mu := ∑' n, ‖θ̂(0) n‖², constant across forward time
  -- by `theta_fourier_tsum_conserved`.
  set Mu : ℝ := ∑' n : Fin 2 → ℤ, ‖mFourierCoeff (θ 0) n‖ ^ 2 with hMu_def
  have hMu_nn : 0 ≤ Mu := tsum_nonneg (fun _ => sq_nonneg _)
  have hu_sum : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      Summable (fun ℓ : Fin 2 → ℤ => ‖mFourierCoeff (u j τ) ℓ‖ ^ 2) :=
    fun j τ _ => velocity_fourier_summable (u j τ)
  have hu_bdd : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      (∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2) ≤ Mu := by
    intro j τ hτ
    calc (∑' ℓ, ‖mFourierCoeff (u j τ) ℓ‖ ^ 2)
        ≤ ∑' ℓ, ‖mFourierCoeff (θ τ) ℓ‖ ^ 2 :=
          velocity_fourier_tsum_le_of_IsSqgVelocityComponent
            (θ τ) (u j τ) j (hu_velocity j τ)
      _ = Mu := theta_fourier_tsum_conserved hE hτ
  -- Gradient tsum bound Mg := M₁ from MMP.hOnePropagation.
  obtain ⟨M₁, hM₁⟩ := hMMP.hOnePropagation
  set Mg : ℝ := M₁ with hMg_def
  have hMg_nn : 0 ≤ Mg := by
    have hbd := hM₁ 0 (le_refl 0)
    have hnn : 0 ≤ hsSeminormSq 1 (θ 0) := hsSeminormSq_nonneg 1 (θ 0)
    linarith
  have hgrad_sum : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      Summable (fun ℓ : Fin 2 → ℤ =>
        ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2) :=
    fun j τ hτ =>
      gradient_fourier_summable_of_hOneSummability (θ τ) j
        (hMMP.hOneSummability τ hτ)
  have hgrad_bdd : ∀ (j : Fin 2) (τ : ℝ), 0 ≤ τ →
      (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2) ≤ Mg := by
    intro j τ hτ
    calc (∑' ℓ, ‖derivSymbol j ℓ * mFourierCoeff (θ τ) ℓ‖ ^ 2)
        ≤ hsSeminormSq 1 (θ τ) :=
          gradient_fourier_tsum_le_hsSeminormSq_one (θ τ) j
            (hMMP.hOneSummability τ hτ)
      _ ≤ Mg := hM₁ τ hτ
  -- Chain through of_sqgDuhamelIdentity.
  exact SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity
    hE u hu_velocity Mu hMu_nn hu_sum hu_bdd Mg hMg_nn
    hgrad_sum hgrad_bdd hDuhamel

/-! ### §10.15 Weak-solution predicate `IsSqgWeakSolution`

§10.14's `of_sqgDuhamelIdentity_via_MMP` takes `hDuhamel`, the mode-wise
integral identity, as a raw ∀-proposition. This section wraps that
hypothesis in a named predicate `IsSqgWeakSolution θ u` so that callers
can pass "θ is a weak SQG solution driven by velocity `u`" as a single
structural witness.

**Connection to the classical test-function weak form.** The standard
distributional weak form of `∂_t θ + u · ∇θ = 0` on `𝕋² × [0, T]` reads:
for every smooth test function `φ : 𝕋² × ℝ → ℝ` with compact time
support in `(0, T)`,

  `∫₀^T ⟨θ(τ), ∂_τ φ(·, τ)⟩_{L²(𝕋²)} dτ`
  `  + ∫₀^T ⟨θ(τ) · u(τ), ∇_x φ(·, τ)⟩_{L²(𝕋²)} dτ = 0`.

Specialising to separated test functions `φ(x, τ) = ψ(τ) · e_m(x)`
where `e_m` is the Fourier character of mode `m` and `ψ` is a smooth
bump on `[s, t]`, Parseval gives

  `∫₀^T ψ'(τ) · θ̂(m, τ) dτ`
  `  + ∫₀^T ψ(τ) · ((u · ∇θ)̂(m, τ)) dτ = 0`.

Taking `ψ → 𝟙_{[s, t]}` (bump-to-indicator limit) and recognising
`(u · ∇θ)̂(m, τ) = sqgNonlinearFlux (θ τ) (u τ) m` produces the
mode-wise Duhamel identity carried below. The forward direction
"distributional weak form → mode-wise identity" therefore hinges on:

* density of separated Fourier characters in the test-function space
  on `𝕋² × [0, T]`,
* the bump-to-indicator limit for `ψ`, valid because
  `sqgNonlinearFlux (θ τ) (u τ) m` is uniformly bounded in `τ` by
  `sqgNonlinearFlux_bounded` (§10.12) and so the integrand on
  `[s, t]` is Bochner-integrable,
* identification `(u · ∇θ)̂(m) = ∑ⱼ (û_j ⋆ (i·ℓ_j · θ̂))(m)`, which
  is the very definition of `sqgNonlinearFlux`.

None of those three steps needs the DNS solution's regularity beyond
what `SqgEvolutionAxioms + MaterialMaxPrinciple` already give; they
are genuine Fourier-analysis facts on `𝕋²`. Formalising them in
mathlib is the multi-step tactical goal whose first layer this
section names.

**Why wrap at all.** The predicate's sole field is the Duhamel
identity itself, so `.duhamel` is a trivial projection. But:

1. Downstream consumers (`of_IsSqgWeakSolution_via_MMP`) take one
   structural witness instead of a five-argument ∀-proposition.
2. When the test-function weak form is later formalised, this is
   exactly the predicate that will receive a second constructor
   `IsSqgWeakSolution.of_testFormWeakSolution`.
3. Documentation of the intended semantics (the docstring above)
   attaches to the named predicate rather than to a raw hypothesis
   repeated verbatim at every call site. -/

/-- **SQG weak-solution predicate (Fourier-mode form).**

`IsSqgWeakSolution θ u` says that `θ` is a weak solution of the SQG
equation `∂_t θ + u · ∇θ = 0` driven by velocity field `u`, expressed
at the Fourier-mode level: for every mode `m` and every forward time
interval `[s, t]`,

  `θ̂(m, t) − θ̂(m, s) = − ∫_s^t sqgNonlinearFlux(θ τ)(u τ)(m) dτ`.

This is the direct consumer of `of_sqgDuhamelIdentity_via_MMP`. See
the section-level comment above for the classical distributional
weak form it specialises and the Fourier-analysis steps that would
link them. -/
structure IsSqgWeakSolution
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    : Prop where
  /-- Mode-wise Duhamel identity for the SQG PDE. -/
  duhamel : ∀ (m : Fin 2 → ℤ) (s t : ℝ), 0 ≤ s → s ≤ t →
    mFourierCoeff (θ t) m - mFourierCoeff (θ s) m
      = -∫ τ in Set.Icc s t, sqgNonlinearFlux (θ τ) (fun j => u j τ) m

/-- **MMP-keyed promotion from `IsSqgWeakSolution`.** The one-line
wrapper over `of_sqgDuhamelIdentity_via_MMP` that consumes the
structural weak-solution witness. This is the entry point the repo's
final conditional Theorem 3 layer is meant to sit on: any analytic
construction that delivers `IsSqgWeakSolution` plus `MMP` plus the
velocity-component witness closes the full `[0, 2]` bootstrap. -/
theorem SqgEvolutionAxioms_strong.of_IsSqgWeakSolution_via_MMP
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hE : SqgEvolutionAxioms θ)
    (hMMP : MaterialMaxPrinciple θ)
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (hu_velocity : ∀ (j : Fin 2) (τ : ℝ), IsSqgVelocityComponent (θ τ) (u j τ) j)
    (hweak : IsSqgWeakSolution θ u) :
    SqgEvolutionAxioms_strong θ :=
  SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP
    hE hMMP u hu_velocity hweak.duhamel

/-! ### §10.16 Test-function weak-form predicate `IsSqgWeakSolutionTimeTest`

§10.15's `IsSqgWeakSolution θ u` carries the mode-wise Duhamel identity
as a named structural witness for
`of_IsSqgWeakSolution_via_MMP`. This section opens the next tactical
layer: a **test-function weak-form predicate**, stated at a
granularity fine enough to couple with time integration but coarse
enough to avoid a full distributional-calculus apparatus on `𝕋² × ℝ`.

**Simplification of scope.** The classical distributional weak form
of `∂_t θ + u · ∇θ = 0` pairs against smooth test functions
`φ : 𝕋² × ℝ → ℂ` with compact time support and reads:

  `∫₀^T ⟨θ(τ), ∂_τφ(·, τ) + u(τ) · ∇_x φ(·, τ)⟩_{L²(𝕋²)} dτ = 0`.

Two independent analytical steps separate this from the mode-wise
Duhamel identity carried by `IsSqgWeakSolution`:

(A) **Spatial Fourier-character specialization** — pair against
    separated test functions `φ(x, τ) = ψ(τ) · e_m(x)` and identify
    `⟨θ(τ), e_m · u(τ) · ∇_x e_m'⟩` with
    `sqgNonlinearFlux (θ τ) (u τ) m` via Parseval + the convolution-of-
    Fourier-coefficients structure already proved in §10.9/§10.12.

(B) **Bump-to-indicator limit in time** — take a smooth bump
    `ψ_n → 𝟙_{[s, t]}` and use dominated convergence (legitimate
    because `sqgNonlinearFlux_bounded` gives a uniform flux bound) to
    recover
    `θ̂(m, t) − θ̂(m, s) = − ∫_s^t sqgNonlinearFlux(θ τ)(u τ)(m) dτ`.

§10.16 **pre-executes step (A)** by formulating the test-function
weak form directly at the Fourier-mode level — one time test function
`ψ : ℝ → ℂ` per mode. What remains for `IsSqgWeakSolution` is step
(B) alone: a clean bump-to-indicator limit argument using the bounded
flux.

The advantage is modularity: step (A) becomes a property *of the
predicate's formulation*, not a theorem that needs proof; step (B)
stands alone as the next formalization target and lives entirely in
time integration, not space-time Bochner. -/

/-- **Time test functions.** A `C¹` function `ψ : ℝ → ℂ` with compact
support. We use `C¹` rather than `C^∞` because §10's bump-to-indicator
argument needs only one derivative: pair against the derivative of a
mollified indicator, dominated by the bounded flux. -/
def IsSqgTimeTestFunction (ψ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ

/-- **Mode-wise time-weak form of SQG.**

For every time test function `ψ` and every Fourier mode `m`,

  `∫ τ, (deriv ψ τ) · θ̂(m, τ) dτ`
  `  = ∫ τ, ψ τ · sqgNonlinearFlux(θ τ)(u τ)(m) dτ`.

The SQG Fourier-mode ODE is `∂_τ θ̂(m, τ) = −sqgNonlinearFlux(θ τ)(u τ)(m)`.
Pairing both sides with `ψ` and integrating by parts in time (boundary
terms vanish since `ψ` is compactly supported) gives

  `∫ τ, (∂_τ ψ)(τ) · θ̂(m, τ) dτ = ∫ τ, ψ(τ) · (u · ∇θ)̂(m, τ) dτ`

with `(u · ∇θ)̂(m, τ)` identified with
`sqgNonlinearFlux(θ τ)(u τ)(m)` by the convolution structure of
§10.9/§10.12. This is step (A) of the reduction in the §10.16 header.

Strictly stronger than `IsSqgWeakSolution`: any of the Duhamel-
identity witnesses that were in §10.15's scope must in particular
satisfy this pairing (multiply the Duhamel identity on both sides by
`deriv ψ τ`, integrate, and use the compact support of `ψ` to
integrate by parts). Strictly weaker than a full space-time
distributional weak form: we have already projected onto Fourier
characters in space. -/
def IsSqgWeakSolutionTimeTest
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    : Prop :=
  ∀ (ψ : ℝ → ℂ), IsSqgTimeTestFunction ψ →
  ∀ (m : Fin 2 → ℤ),
    (∫ τ, (deriv ψ τ) * mFourierCoeff (θ τ) m)
      = ∫ τ, ψ τ * sqgNonlinearFlux (θ τ) (fun j => u j τ) m

/-- **Nonlinear flux of the zero scalar field vanishes.**

`sqgNonlinearFlux 0 u m = 0` for every velocity field `u` and mode
`m`. Each component convolution's right factor is
`fun ℓ => derivSymbol j ℓ * mFourierCoeff 0 ℓ`, which is pointwise
zero by `mFourierCoeff_zero`. The convolution with the zero sequence
on the right is then zero by `fourierConvolution_zero_right`. -/
theorem sqgNonlinearFlux_zero_theta
    (u : Fin 2 → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (m : Fin 2 → ℤ) :
    sqgNonlinearFlux
        (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) u m = 0 := by
  unfold sqgNonlinearFlux
  apply Finset.sum_eq_zero
  intro j _
  have h :
      (fun ℓ => derivSymbol j ℓ * mFourierCoeff
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) ℓ)
        = fun _ => (0 : ℂ) := by
    funext ℓ
    rw [mFourierCoeff_zero]
    ring
  rw [h]
  exact fourierConvolution_zero_right _ m

/-- **The zero scalar field is a trivial time-weak solution.**

Both integrands vanish pointwise:
* `mFourierCoeff (fun _ => 0) τ m = mFourierCoeff (0 : Lp) m = 0`
  by `mFourierCoeff_zero`.
* `sqgNonlinearFlux (fun _ => 0) τ u m = sqgNonlinearFlux 0 (u τ) m = 0`
  by `sqgNonlinearFlux_zero_theta`.

So each integral is zero and the weak-form identity reads `0 = 0`.
This is the §10.16 counterpart of `IsSqgVelocityComponent.of_zero`. -/
theorem IsSqgWeakSolutionTimeTest.zero
    (u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    IsSqgWeakSolutionTimeTest
      (fun _ => (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))) u := by
  intro ψ _ m
  have h1 : (fun τ : ℝ => deriv ψ τ
      * mFourierCoeff ((fun _ : ℝ =>
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))) τ) m)
        = fun _ => (0 : ℂ) := by
    funext τ
    rw [mFourierCoeff_zero]
    ring
  have h2 : (fun τ : ℝ => ψ τ
      * sqgNonlinearFlux ((fun _ : ℝ =>
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))) τ)
            (fun j => u j τ) m)
        = fun _ => (0 : ℂ) := by
    funext τ
    rw [sqgNonlinearFlux_zero_theta]
    ring
  rw [h1, h2]

/-! ### §10.17 Fourier-coefficient time regularity

The bump-to-indicator bridge (step (B) of §10.16) from
`IsSqgWeakSolutionTimeTest` to `IsSqgWeakSolution` needs a time-
regularity witness: on mollified indicators `ψ_n → 𝟙_{[s, t]}`, the
left-hand pairing `∫ (deriv ψ_n)·θ̂(m)` tends to a boundary evaluation
`θ̂(m, t) − θ̂(m, s)`, and that limit is pointwise only if
`τ ↦ θ̂(m, τ)` is continuous at `s` and `t`.

This section names the minimal continuity predicate needed.
`SqgEvolutionAxioms` alone does NOT supply it: mean + L²
conservation + Riesz-transform velocity are constants of the motion,
not pointwise regularity. A real SQG solution constructed from
smooth initial data and the material-derivative flow delivers
Fourier-coefficient continuity as a property of the construction;
this predicate abstracts that property so the bridge can consume it
without reference to any specific construction.

Contents:
* `SqgFourierContinuous θ` — every mode coefficient `τ ↦ θ̂(m, τ)`
  is continuous in `τ`.
* `SqgFourierContinuous.zero` — the zero scalar field satisfies it
  trivially (every coefficient is the zero constant).
* `SqgFourierContinuous.const` — any constant-in-time field does
  too (every coefficient is a real constant). -/

/-- **Fourier-coefficient continuity in time.**

For every Fourier mode `m`, the map `τ ↦ mFourierCoeff (θ τ) m` is
continuous. This is strictly weaker than requiring `τ ↦ θ τ` to be
continuous in `Lp ℂ 2` (which by boundedness of `mFourierCoeff`
would imply Fourier-coefficient continuity uniformly across modes),
but is exactly what the bump-to-indicator limit needs for a fixed
mode at fixed endpoints `(s, t)`. -/
def SqgFourierContinuous
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop :=
  ∀ m : Fin 2 → ℤ, Continuous (fun τ => mFourierCoeff (θ τ) m)

/-- **Zero scalar field is Fourier-continuous.** Every coefficient
is the zero constant (by `mFourierCoeff_zero`), hence continuous. -/
theorem SqgFourierContinuous.zero :
    SqgFourierContinuous
      (fun _ => (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))) := by
  intro m
  have h : (fun τ : ℝ => mFourierCoeff ((fun _ : ℝ =>
          (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))) τ) m)
        = fun _ => (0 : ℂ) := by
    funext τ
    exact mFourierCoeff_zero m
  rw [h]
  exact continuous_const

/-- **Constant-in-time scalar field is Fourier-continuous.** Every
coefficient `mFourierCoeff θ₀ m` is a time-independent complex
number. -/
theorem SqgFourierContinuous.const
    (θ₀ : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    SqgFourierContinuous (fun _ => θ₀) := by
  intro _
  exact continuous_const

/-! ### §10.18 Mollifier construction for the bump-to-indicator bridge

Phase 2.2 of the bridge: name the concrete mollifier family that
Phase 2.3's limit argument will instantiate.

**Primitive.** Mathlib's `ContDiffBump` delivers, for any center `c`
in a finite-dimensional inner-product space and any `0 < rIn < rOut`,
a `C^∞` function ℝ-valued on that space with the properties:
* equals `1` on `closedBall c rIn`,
* supported in `closedBall c rOut`,
* values in `[0, 1]` everywhere.

On ℝ, `closedBall c r = [c − r, c + r]`. Picking
`c := (s + t) / 2`, `rIn := (t − s) / 2`, `rOut := (t − s) / 2 + ε`
yields a bump that is `1` on exactly `[s, t]` and supported in
`[s − ε, t + ε]` — exactly the Friedrichs-mollifier shape.

`HasContDiffBump ℝ` is automatic via
`hasContDiffBump_of_innerProductSpace`. `FiniteDimensional ℝ ℝ` is
automatic (ℝ as a module over itself is 1-dimensional), so
`ContDiffBump.hasCompactSupport` applies. -/

/-- **Mollifier-data bump for `[s, t]` widened by `ε` on each side.**

Centered at the midpoint with inner radius half the interval width
and outer radius half the interval width plus `ε`. The hypotheses
`s < t` and `0 < ε` make `0 < rIn < rOut`. -/
noncomputable def sqgMollifierBump (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) :
    ContDiffBump ((s + t) / 2 : ℝ) where
  rIn := (t - s) / 2
  rOut := (t - s) / 2 + ε
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- **Complex-valued mollifier function.**

The underlying bump `sqgMollifierBump ε s t hst hε : ℝ → ℝ`
composed with the `Complex.ofReal` coercion so it fits the
`IsSqgTimeTestFunction` signature `ℝ → ℂ`. -/
noncomputable def sqgMollifier (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) :
    ℝ → ℂ :=
  fun τ => ((sqgMollifierBump ε s t hst hε) τ : ℂ)

/-- **Mollifier is `C¹` (in fact `C^∞`, but `C¹` is what we need).**
Composition of `Complex.ofRealCLM` (infinitely smooth linear map)
with the bump (`C^∞` by `ContDiffBump.contDiff`). We target
`ContDiff ℝ 1` directly because:
* `ContDiffBump.contDiff` provides `ContDiff ℝ (↑n) f` for
  `n : ℕ∞`, whose max value `∞` lifts to `(∞ : WithTop ℕ∞)` — it
  cannot reach `(⊤ : WithTop ℕ∞)` (the analytic level).
* `IsSqgTimeTestFunction` only needs `C¹`. -/
theorem sqgMollifier_contDiff (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) :
    ContDiff ℝ 1 (sqgMollifier ε s t hst hε) := by
  unfold sqgMollifier
  exact Complex.ofRealCLM.contDiff.comp
    (sqgMollifierBump ε s t hst hε).contDiff

/-- **Mollifier has compact support.** The underlying bump has
compact support (`ContDiffBump.hasCompactSupport`, using
`FiniteDimensional ℝ ℝ`), and composition with `Complex.ofReal`
preserves that because `Complex.ofReal 0 = 0`. -/
theorem sqgMollifier_hasCompactSupport
    (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) :
    HasCompactSupport (sqgMollifier ε s t hst hε) := by
  unfold sqgMollifier
  exact (sqgMollifierBump ε s t hst hε).hasCompactSupport.comp_left
    Complex.ofReal_zero

/-- **Mollifier is a time test function.**

Bundles `sqgMollifier_contDiff` (at level `1`) with
`sqgMollifier_hasCompactSupport` to match `IsSqgTimeTestFunction`. -/
theorem sqgMollifier_isSqgTimeTestFunction
    (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) :
    IsSqgTimeTestFunction (sqgMollifier ε s t hst hε) :=
  ⟨sqgMollifier_contDiff ε s t hst hε,
   sqgMollifier_hasCompactSupport ε s t hst hε⟩

/-- **Mollifier equals `1` on `[s, t]`.** On the core interval the
inner bump evaluates to `1` (by `ContDiffBump.one_of_mem_closedBall`,
since `[s, t] = closedBall ((s + t) / 2) ((t − s) / 2)`), and
`Complex.ofReal` maps `1` to `1`. -/
theorem sqgMollifier_eq_one_of_mem_Icc
    (ε s t : ℝ) (hst : s < t) (hε : 0 < ε)
    (τ : ℝ) (hτ : τ ∈ Set.Icc s t) :
    sqgMollifier ε s t hst hε τ = 1 := by
  obtain ⟨h1, h2⟩ := hτ
  have hbump : (sqgMollifierBump ε s t hst hε) τ = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change τ ∈ Metric.closedBall ((s + t) / 2) ((t - s) / 2)
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  unfold sqgMollifier
  rw [hbump]
  norm_cast

/-! ### §10.19 Mollifier-specialized weak-form identity (Phase 2.3.a)

Instantiating `IsSqgWeakSolutionTimeTest` at the mollifier gives an
algebraic starting point for the bump-to-indicator limit: the full
weak-form identity `∫(deriv ψ_ε)·θ̂ + ∫ψ_ε·F = 0` is the sum of two
integrals; rearranged it says

  `∫(deriv ψ_ε)·θ̂(m) = −∫ψ_ε·F(m)`.

That rearrangement is what the final limit argument will take in
both directions — the LHS tends to `θ̂(m, s) − θ̂(m, t)` (by
`SqgFourierContinuous θ`), the RHS tends to `−∫_s^t F(m)` (by
dominated convergence against `sqgNonlinearFlux_bounded`).

This section delivers only the rearrangement. The two limits are
Phase 2.3.b and 2.3.c. -/

/-- **Weak-form identity specialised at the mollifier.**

For every `s < t`, `ε > 0`, and mode `m`, if `θ` weakly solves SQG
at the mode level (`IsSqgWeakSolutionTimeTest θ u`) then

  `∫ τ, (deriv (sqgMollifier ε s t hst hε) τ) · mFourierCoeff (θ τ) m`
  `  = ∫ τ, (sqgMollifier ε s t hst hε τ) · sqgNonlinearFlux (θ τ) (u τ) m`.

Proof: apply the predicate to the mollifier (a valid time test
function by `sqgMollifier_isSqgTimeTestFunction`). -/
theorem IsSqgWeakSolutionTimeTest.mollifier_identity
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    {u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hweak : IsSqgWeakSolutionTimeTest θ u)
    (ε s t : ℝ) (hst : s < t) (hε : 0 < ε) (m : Fin 2 → ℤ) :
    (∫ τ, (deriv (sqgMollifier ε s t hst hε) τ) * mFourierCoeff (θ τ) m)
      = ∫ τ, (sqgMollifier ε s t hst hε τ)
          * sqgNonlinearFlux (θ τ) (fun j => u j τ) m :=
  hweak (sqgMollifier ε s t hst hε)
    (sqgMollifier_isSqgTimeTestFunction ε s t hst hε) m

/-! ### §10.20 Concrete mollifier and bump-to-indicator limit

The abstract `sqgMollifier` of §10.18 (built from `ContDiffBump` via
`Classical.choice`) is adequate for the mollifier_identity, but its
abstract API prevents deriving derivative sign information on the
collars — a key ingredient for Phase 2.3.b (LHS collar limit).

This section constructs `sqgConcreteMollifier` directly from
`Real.smoothTransition`, with an explicit product formula:

  `sqgConcreteMollifier ε s t τ`
  `  = smoothTransition((τ − s + ε)/ε) · smoothTransition((t − τ + ε)/ε)`

Since `Real.smoothTransition` is monotone and C^∞, the concrete
mollifier inherits these properties.  Its collar behavior is exact:

* **Left collar** `[s − ε, s]`: second factor = 1 (argument ≥ 1 when
  τ ≤ s < t), so the mollifier is the monotone rising function
  `smoothTransition((τ − s + ε)/ε)`, going from 0 at τ = s − ε to
  1 at τ = s.
* **Flat region** `[s, t]`: both arguments are ≥ 1, so both factors = 1.
* **Right collar** `[t, t + ε]`: first factor = 1 (argument ≥ 1 when
  s < t ≤ τ), so the mollifier is the antitone falling function
  `smoothTransition((t − τ + ε)/ε)`, going from 1 at τ = t to 0 at
  τ = t + ε.
* **Outside** `[s − ε, t + ε]`: one factor has argument ≤ 0, so = 0.

Crucially, `sqgConcreteMollifier ε s t τ = 1` for **every** τ ∈ (s, t)
and every ε > 0 (not just eventually).  This makes the Phase 2.3.c
proof (RHS DCT limit) especially clean: the integrand already equals
`G τ` on `(s, t)` for all positive ε. -/

/-- **Concrete mollifier** for the bump-to-indicator bridge, built
directly from `Real.smoothTransition` to expose its monotonicity.

  `sqgConcreteMollifier ε s t τ`
  `  = smoothTransition((τ − s + ε)/ε) · smoothTransition((t − τ + ε)/ε)`.

When `ε = 0`, division by ε gives `(·)/0 = 0` in Lean's real-number
convention, so both factors collapse to `smoothTransition 0 = 0`; the
function is identically 0 (not a bump).  All positivity hypotheses
`hε : 0 < ε` are therefore reserved for the property lemmas, not the
definition. -/
noncomputable def sqgConcreteMollifier (ε s t : ℝ) : ℝ → ℝ :=
  fun τ => Real.smoothTransition ((τ - s + ε) / ε) *
           Real.smoothTransition ((t - τ + ε) / ε)

/-- `sqgConcreteMollifier` is non-negative everywhere: product of two
non-negative `smoothTransition` values. -/
theorem sqgConcreteMollifier_nonneg (ε s t τ : ℝ) :
    0 ≤ sqgConcreteMollifier ε s t τ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- `sqgConcreteMollifier` is at most 1 everywhere: product of two
values each ≤ 1, and the product of non-negatives ≤ 1 that multiply
to ≤ 1. Since `0 ≤ a ≤ 1` and `0 ≤ b ≤ 1`, we have `a * b ≤ 1 * 1 = 1`. -/
theorem sqgConcreteMollifier_le_one (ε s t τ : ℝ) :
    sqgConcreteMollifier ε s t τ ≤ 1 := by
  unfold sqgConcreteMollifier
  exact mul_le_one₀ (Real.smoothTransition.le_one _)
         (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

/-- For `τ ∈ (s, t)` (open interval), both `smoothTransition` arguments
are strictly greater than 1, so both factors equal 1 and the concrete
mollifier equals 1.  In contrast to the abstract bump approach, this
holds for **every** `ε > 0`, not just eventually. -/
theorem sqgConcreteMollifier_eq_one_of_mem_Ioo {s t τ : ℝ} (hτ : τ ∈ Set.Ioo s t)
    {ε : ℝ} (hε : 0 < ε) : sqgConcreteMollifier ε s t τ = 1 := by
  unfold sqgConcreteMollifier
  have hτs : s < τ := hτ.1
  have hτt : τ < t := hτ.2
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hε]; linarith
  · rw [le_div_iff₀ hε]; linarith

/-- Same as `sqgConcreteMollifier_eq_one_of_mem_Ioo` for the closed interval `Icc`.
Both factors are 1 on `[s, t]`. -/
theorem sqgConcreteMollifier_eq_one_of_mem_Icc {s t τ : ℝ} (hτ : τ ∈ Set.Icc s t)
    {ε : ℝ} (hε : 0 < ε) : sqgConcreteMollifier ε s t τ = 1 := by
  unfold sqgConcreteMollifier
  have hτs : s ≤ τ := hτ.1
  have hτt : τ ≤ t := hτ.2
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hε]; linarith
  · rw [le_div_iff₀ hε]; linarith

/-- Left factor only: when `τ ≤ t`, the second `smoothTransition` factor
equals 1 (its argument `(t − τ + ε)/ε ≥ 1` iff `t − τ ≥ 0`). -/
theorem sqgConcreteMollifier_eq_left_factor {s t τ : ℝ} (hτt : τ ≤ t) {ε : ℝ}
    (hε : 0 < ε) :
    sqgConcreteMollifier ε s t τ =
      Real.smoothTransition ((τ - s + ε) / ε) := by
  unfold sqgConcreteMollifier
  have h2 : Real.smoothTransition ((t - τ + ε) / ε) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  rw [h2, mul_one]

/-- The concrete mollifier vanishes for `τ ≤ s − ε`: the left factor's
argument is `(τ − s + ε)/ε ≤ 0` when `τ ≤ s − ε`. -/
theorem sqgConcreteMollifier_zero_of_le_left {s t τ ε : ℝ} (hε : 0 < ε)
    (hτ : τ ≤ s - ε) : sqgConcreteMollifier ε s t τ = 0 := by
  unfold sqgConcreteMollifier
  have harg : (τ - s + ε) / ε ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hε.le; linarith
  rw [Real.smoothTransition.zero_of_nonpos harg, zero_mul]

/-- The concrete mollifier vanishes for `τ ≥ t + ε`: the right factor's
argument is `(t − τ + ε)/ε ≤ 0` when `τ ≥ t + ε`. -/
theorem sqgConcreteMollifier_zero_of_ge_right {s t τ ε : ℝ} (hε : 0 < ε)
    (hτ : t + ε ≤ τ) : sqgConcreteMollifier ε s t τ = 0 := by
  unfold sqgConcreteMollifier
  have harg : (t - τ + ε) / ε ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hε.le; linarith
  rw [Real.smoothTransition.zero_of_nonpos harg, mul_zero]

/-- The concrete mollifier is `ContDiff ℝ 1`: it is a product of two
`C^∞` compositions of `Real.smoothTransition` with affine functions. -/
theorem sqgConcreteMollifier_contDiff (ε s t : ℝ) :
    ContDiff ℝ 1 (sqgConcreteMollifier ε s t) := by
  unfold sqgConcreteMollifier
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).add contDiff_const).div_const ε)
  · exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.sub contDiff_id).add contDiff_const).div_const ε)

/-- The concrete mollifier has compact support: it vanishes outside the
closed interval `[s − ε, t + ε]`, hence `tsupport ⊆ [s − ε, t + ε]`. -/
theorem sqgConcreteMollifier_hasCompactSupport {ε s t : ℝ} (hε : 0 < ε) :
    HasCompactSupport (sqgConcreteMollifier ε s t) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (s - ε) (t + ε))
    isCompact_Icc
  intro τ hτ
  simp only [Function.mem_support] at hτ
  simp only [Set.mem_Icc]
  by_contra h
  simp only [not_and_or, not_le] at h
  rcases h with h | h
  · exact hτ (sqgConcreteMollifier_zero_of_le_left hε h.le)
  · exact hτ (sqgConcreteMollifier_zero_of_ge_right hε h.le)

/-- The complex-valued concrete mollifier `(sqgConcreteMollifier ε s t · : ℝ → ℂ)`
(coerced via `↑`) is a valid time test function: `C¹` and compactly supported. -/
theorem sqgConcreteMollifier_isSqgTimeTestFunction {ε s t : ℝ} (hε : 0 < ε) :
    IsSqgTimeTestFunction (fun τ => (sqgConcreteMollifier ε s t τ : ℂ)) := by
  constructor
  · exact ofRealCLM.contDiff.comp (sqgConcreteMollifier_contDiff ε s t)
  · show HasCompactSupport (Complex.ofReal ∘ sqgConcreteMollifier ε s t)
    exact (sqgConcreteMollifier_hasCompactSupport hε).comp_left Complex.ofReal_zero

/-! #### Phase 2.3.c — RHS mollifier integral converges to interval integral

As `ε → 0⁺`, `∫ (sqgConcreteMollifier ε s t τ : ℂ) * G τ dτ → ∫_{[s,t]} G τ dτ`.

Proof: Dominated Convergence Theorem.

**Bound.** For `ε ≤ 1`, the mollifier is supported in `[s − 1, t + 1]`
(compact), and `‖mollifier · G‖ ≤ 1 · K = K` since the mollifier is in
`[0, 1]` and `‖G τ‖ ≤ K` by hypothesis.  The dominating function
`K · 𝟙_{[s − 1, t + 1]}` is integrable.

**Pointwise.** For a.e. τ:
* τ ∈ (s, t): both smoothTransition arguments are > 1 for ALL ε > 0, so
  mollifier = 1 for all ε > 0 → integrand = G τ a.e. ✓
* τ < s: argument `(τ − s + ε)/ε → −∞` as ε → 0⁺ → smoothTransition → 0
  (in fact = 0 for ε < s − τ) → integrand = 0 ✓
* τ > t: symmetric → integrand = 0 ✓

Limit identification: `∫ 𝟙_{[s,t]} G = ∫_{[s,t]} G` by
`MeasureTheory.integral_indicator`. -/

/-- **Phase 2.3.c**: The RHS mollifier integral tends to the interval
integral as `ε → 0⁺`.

Hypotheses:
* `hK_nn`: the flux bound `K` is non-negative.
* `hG_bound`: `‖G τ‖ ≤ K` for all τ (uniform bound).
* `hG_meas`: `G` is measurable (needed for DCT and the set integral).
* `hst`: `s < t`. -/
theorem sqgConcreteMollifier_rhs_tendsto {s t : ℝ} (hst : s < t)
    {G : ℝ → ℂ} {K : ℝ} (hK_nn : 0 ≤ K)
    (hG_bound : ∀ τ, ‖G τ‖ ≤ K)
    (hG_meas : AEStronglyMeasurable G volume) :
    Filter.Tendsto
      (fun ε => ∫ τ, (sqgConcreteMollifier ε s t τ : ℂ) * G τ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ τ in Set.Icc s t, G τ)) := by
  -- Rewrite the target as ∫ 𝟙_{[s,t]} G (for the DCT limit identification)
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  -- Apply DCT for filters (nhdsWithin 0 Ioi 0 is countably generated as a sub-nhds of ℝ)
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun τ => K * (Set.Icc (s - 1) (t + 1)).indicator (fun _ => (1 : ℝ)) τ)
  · -- Measurability: for each ε, the integrand is measurable
    apply Filter.Eventually.of_forall
    intro ε
    apply AEStronglyMeasurable.mul _ hG_meas
    exact (Complex.continuous_ofReal.comp
      ((sqgConcreteMollifier_contDiff ε s t).continuous)).aestronglyMeasurable
  · -- Domination: for ε ∈ (0, 1], the integrand is bounded by K · 𝟙_{[s-1,t+1]}
    apply Filter.eventually_of_mem (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
    intro ε ⟨hε_pos, hε_le⟩
    apply Filter.Eventually.of_forall
    intro τ
    simp only [Set.indicator, Set.mem_Icc]
    split_ifs with hmem
    · -- τ ∈ [s-1, t+1]
      rw [mul_one]
      calc ‖(sqgConcreteMollifier ε s t τ : ℂ) * G τ‖
          = ‖(sqgConcreteMollifier ε s t τ : ℂ)‖ * ‖G τ‖ := norm_mul _ _
        _ ≤ 1 * K := by
            apply mul_le_mul _ (hG_bound τ) (norm_nonneg _) zero_le_one
            rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (sqgConcreteMollifier_nonneg ε s t τ)]
            exact sqgConcreteMollifier_le_one ε s t τ
        _ = K := one_mul K
    · -- τ ∉ [s-1, t+1], so mollifier = 0 (support ⊆ [s-ε, t+ε] ⊆ [s-1, t+1] for ε ≤ 1)
      rw [mul_zero]
      -- mollifier is 0 outside [s-1, t+1] when ε ≤ 1
      have hmoll : sqgConcreteMollifier ε s t τ = 0 := by
        simp only [not_and_or, not_le] at hmem
        rcases hmem with h | h
        · exact sqgConcreteMollifier_zero_of_le_left hε_pos (by linarith)
        · exact sqgConcreteMollifier_zero_of_ge_right hε_pos (by linarith)
      simp [hmoll]
  · -- Integrability of the dominating function K · 𝟙_{[s-1, t+1]}
    apply Integrable.const_mul _ K
    apply IntegrableOn.integrable_indicator _ measurableSet_Icc
    exact integrableOn_const
        (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (hC := enorm_ne_top)
  · -- Pointwise a.e. convergence
    apply Filter.Eventually.of_forall
    intro τ
    by_cases hτ : τ ∈ Set.Icc s t
    · -- τ ∈ [s, t]: indicator = G τ; mollifier = 1 for all ε > 0
      rw [Set.indicator_of_mem hτ]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      apply Filter.eventually_of_mem self_mem_nhdsWithin
      intro ε hε
      show G τ = (sqgConcreteMollifier ε s t τ : ℂ) * G τ
      rw [sqgConcreteMollifier_eq_one_of_mem_Icc hτ (Set.mem_Ioi.mp hε)]
      push_cast; ring
    · -- τ ∉ [s, t]: indicator = 0; mollifier eventually zero near 0⁺
      rw [Set.indicator_of_notMem hτ]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      -- Show (fun _ => (0:ℂ)) =ᶠ[nhdsWithin 0 (Ioi 0)] (fun ε => (sqgConcreteMollifier ε s t τ : ℂ) * G τ)
      simp only [Set.mem_Icc, not_and_or, not_le] at hτ
      rcases hτ with hτs | hτt
      · -- τ < s: mollifier = 0 for all ε ∈ (0, s − τ)
        apply Filter.eventually_of_mem (Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < s - τ))
        intro ε ⟨hε_pos, hε_le⟩
        show (0 : ℂ) = (sqgConcreteMollifier ε s t τ : ℂ) * G τ
        rw [sqgConcreteMollifier_zero_of_le_left hε_pos (by linarith)]
        push_cast; ring
      · -- τ > t: mollifier = 0 for all ε ∈ (0, τ − t)
        apply Filter.eventually_of_mem (Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < τ - t))
        intro ε ⟨hε_pos, hε_le⟩
        show (0 : ℂ) = (sqgConcreteMollifier ε s t τ : ℂ) * G τ
        rw [sqgConcreteMollifier_zero_of_ge_right hε_pos (by linarith)]
        push_cast; ring

/-! ### §10.21 Phase 2.3.d — Bridge from time-test weak form to Duhamel

Combines Phase 2.3.a (`IsSqgWeakSolutionTimeTest.mollifier_identity`,
§10.19) with Phase 2.3.c (`sqgConcreteMollifier_rhs_tendsto`, §10.20)
and an abstract Phase 2.3.b predicate to prove the bridge theorem
`IsSqgWeakSolution.of_IsSqgWeakSolutionTimeTest`.

**Phase 2.3.b — open item.** `IsSqgCollarLhsCondition θ` asserts that
for each mode `m` and interval `[s, t]` with `0 ≤ s ≤ t`, the LHS
mollifier integral
`∫ τ, deriv(ψ_ε τ) · θ̂(m, τ) dτ` → `θ̂(m, s) − θ̂(m, t)` as `ε → 0⁺`,
where `ψ_ε τ = sqgConcreteMollifier ε s t τ` coerced to `ℂ`.

The proof of `IsSqgCollarLhsCondition θ` from `SqgFourierContinuous θ`
proceeds by FTC on each collar:

* **Left collar** `[s − ε, s]`: `∫_{s−ε}^s deriv(ψ_ε) = ψ_ε(s) − ψ_ε(s − ε) = 1`
  by `intervalIntegral.integral_eq_sub_of_hasDerivAt` applied to the
  C¹ function `sqgConcreteMollifier`; non-negativity of the derivative
  on this collar (`Monotone.deriv_nonneg`, since the left factor is
  monotone rising) then gives `‖collar integral − θ̂(s)‖ ≤ osc_{[s−ε,s]}(θ̂) → 0`.
* **Right collar** symmetric.

This FTC + continuity argument will be fully formalised in §10.22 once
`HasDerivAt` boilerplate for `sqgConcreteMollifier` is in place. -/

/-- **Phase 2.3.b predicate**: for every mode `m` and interval `[s, t]`
(with `0 ≤ s ≤ t`), the LHS mollifier integral
`∫ τ, deriv(ψ_ε τ) · θ̂(m, τ) dτ` tends to `θ̂(m, s) − θ̂(m, t)` as
`ε → 0⁺`, where `ψ_ε` is `sqgConcreteMollifier ε s t` coerced to `ℂ`.

This is the Phase 2.3.b component of the bump-to-indicator bridge.
Once proved from `SqgFourierContinuous θ` (§10.22), it can be dropped
as a hypothesis of `IsSqgWeakSolution.of_IsSqgWeakSolutionTimeTest`. -/
def IsSqgCollarLhsCondition
    (θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) : Prop :=
  ∀ (m : Fin 2 → ℤ) (s t : ℝ), 0 ≤ s → s ≤ t →
    Filter.Tendsto
      (fun ε => ∫ τ,
        deriv (fun τ => (sqgConcreteMollifier ε s t τ : ℂ)) τ
          * mFourierCoeff (θ τ) m)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (mFourierCoeff (θ s) m - mFourierCoeff (θ t) m))

/-- **Phase 2.3.d — Bridge theorem**: `IsSqgWeakSolutionTimeTest θ u`
together with the collar-limit condition `IsSqgCollarLhsCondition θ`
and uniform flux bounds implies `IsSqgWeakSolution θ u`.

**Proof sketch.**
1. For every `ε > 0`, Phase 2.3.a gives
   `∫ deriv(ψ_ε)·θ̂(m) = ∫ ψ_ε·G(m)`.
2. Phase 2.3.b (`h_collar`): the LHS → `θ̂(m, s) − θ̂(m, t)`.
3. Phase 2.3.c (`sqgConcreteMollifier_rhs_tendsto`): the RHS →
   `∫_{[s,t]} G(m)`.
4. Uniqueness of limits (`tendsto_nhds_unique`): `θ̂(m, s) − θ̂(m, t) =
   ∫_{[s,t]} G(m)`, hence `θ̂(m, t) − θ̂(m, s) = −∫_{[s,t]} G(m)`. -/
theorem IsSqgWeakSolution.of_IsSqgWeakSolutionTimeTest
    {θ : ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    {u : Fin 2 → ℝ → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))}
    (hweak : IsSqgWeakSolutionTimeTest θ u)
    (h_collar : IsSqgCollarLhsCondition θ)
    {K : ℝ} (hK_nn : 0 ≤ K)
    (hG_bound : ∀ (m : Fin 2 → ℤ) (τ : ℝ),
        ‖sqgNonlinearFlux (θ τ) (fun j => u j τ) m‖ ≤ K)
    (hG_meas : ∀ (m : Fin 2 → ℤ),
        AEStronglyMeasurable
          (fun τ => sqgNonlinearFlux (θ τ) (fun j => u j τ) m)
          volume) :
    IsSqgWeakSolution θ u := by
  constructor
  intro m s t hs hst
  -- s = t: both sides vanish
  rcases eq_or_lt_of_le hst with rfl | hst_lt
  · simp [sub_self]
  -- Main case: s < t
  -- Phase 2.3.a: weak-form identity at the concrete mollifier for every ε > 0
  have eq_eps : ∀ ε > 0,
      ∫ τ, deriv (fun τ => (sqgConcreteMollifier ε s t τ : ℂ)) τ
               * mFourierCoeff (θ τ) m =
      ∫ τ, (sqgConcreteMollifier ε s t τ : ℂ)
               * sqgNonlinearFlux (θ τ) (fun j => u j τ) m :=
    fun ε hε => hweak (fun τ => (sqgConcreteMollifier ε s t τ : ℂ))
                      (sqgConcreteMollifier_isSqgTimeTestFunction hε) m
  -- Phase 2.3.b: LHS → θ̂(s) − θ̂(t)
  have lhs_lim := h_collar m s t hs hst_lt.le
  -- Phase 2.3.c: RHS → ∫_{[s,t]} G
  have rhs_lim := sqgConcreteMollifier_rhs_tendsto hst_lt hK_nn
      (hG_bound m) (hG_meas m)
  -- Rewrite rhs_lim using eq_eps: the LHS also tends to ∫_{[s,t]} G
  have lhs_lim' : Filter.Tendsto
      (fun ε => ∫ τ, deriv (fun τ => (sqgConcreteMollifier ε s t τ : ℂ)) τ
                       * mFourierCoeff (θ τ) m)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ τ in Set.Icc s t,
               sqgNonlinearFlux (θ τ) (fun j => u j τ) m)) :=
    rhs_lim.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
                     (fun ε hε => (eq_eps ε (Set.mem_Ioi.mp hε)).symm))
  -- Uniqueness of limits (nhdsWithin 0 (Ioi 0) is NeBot on ℝ)
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := inferInstance
  have heq : mFourierCoeff (θ s) m - mFourierCoeff (θ t) m =
      ∫ τ in Set.Icc s t, sqgNonlinearFlux (θ τ) (fun j => u j τ) m :=
    tendsto_nhds_unique lhs_lim lhs_lim'
  -- θ̂(t) − θ̂(s) = −∫_{[s,t]} G
  linear_combination -heq

/-! ### §10.22 Phase 2.3.b — collar FTC: `SqgFourierContinuous → IsSqgCollarLhsCondition`

This section executes the proof roadmap documented in §10.21. The mollifier
`ψ_ε = sqgConcreteMollifier ε s t` is piecewise constant (= 0 outside
`[s − ε, t + ε]`, = 1 on `[s, t]`), so its derivative is supported on the two
**collars** `[s − ε, s]` and `[t, t + ε]`. On the left collar the mollifier
reduces to `Real.smoothTransition ((τ − s + ε)/ε)` (right factor = 1); on the
right collar it reduces to `Real.smoothTransition ((t − τ + ε)/ε)` (left
factor = 1). Each factor is monotone in the scaled variable, so:

* **Tier 1 — monotonicity.** `sqgConcreteMollifier` is `MonotoneOn` the left
  collar and `AntitoneOn` the right collar. This is the substrate all sign
  statements below rest on.
* **Tier 2 — derivative sign / vanishing.** On `Ioo s t` the function is
  locally constant ⇒ `deriv = 0`. Outside `[s − ε, t + ε]` the same holds.
  On the interior of each collar the local monotone representative makes
  `deriv` non-negative (left) or non-positive (right).

Tiers 3–6 (FTC mass identities, integral split, collar squeeze, final
assembly) are the subsequent commits in this plan. -/

/-- **Right-factor collapse.** Symmetric companion to
`sqgConcreteMollifier_eq_left_factor`: when `s ≤ τ`, the left factor
`smoothTransition ((τ − s + ε)/ε)` equals 1 (its argument is `≥ 1`), so the
mollifier reduces to the right factor. Needed for the right-collar monotone
representation in Tier 1. -/
theorem sqgConcreteMollifier_eq_right_factor {s t τ : ℝ} (hτs : s ≤ τ) {ε : ℝ}
    (hε : 0 < ε) :
    sqgConcreteMollifier ε s t τ =
      Real.smoothTransition ((t - τ + ε) / ε) := by
  unfold sqgConcreteMollifier
  have h1 : Real.smoothTransition ((τ - s + ε) / ε) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hε]; linarith)
  rw [h1, one_mul]

/-! #### Tier 1 — monotonicity on the two collars -/

/-- **Tier 1a — MonotoneOn left collar.** On `[s − ε, s]`, the mollifier
equals `Real.smoothTransition ((τ − s + ε)/ε)` (right factor is 1 because
`τ ≤ s ≤ t`). Precomposition of a monotone function with an affine
increasing map is monotone. -/
theorem sqgConcreteMollifier_monotoneOn_left_collar {s t ε : ℝ}
    (hε : 0 < ε) (hst : s ≤ t) :
    MonotoneOn (sqgConcreteMollifier ε s t) (Set.Icc (s - ε) s) := by
  intro a ha b hb hab
  have ha_t : a ≤ t := ha.2.trans hst
  have hb_t : b ≤ t := hb.2.trans hst
  rw [sqgConcreteMollifier_eq_left_factor ha_t hε,
      sqgConcreteMollifier_eq_left_factor hb_t hε]
  apply Real.smoothTransition.monotone
  exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)

/-- **Tier 1b — AntitoneOn right collar.** On `[t, t + ε]`, the mollifier
equals `Real.smoothTransition ((t − τ + ε)/ε)` (left factor is 1 because
`s ≤ t ≤ τ`). The argument `(t − τ + ε)/ε` is *decreasing* in `τ`, so after
composition with the monotone `smoothTransition` the mollifier is antitone. -/
theorem sqgConcreteMollifier_antitoneOn_right_collar {s t ε : ℝ}
    (hε : 0 < ε) (hst : s ≤ t) :
    AntitoneOn (sqgConcreteMollifier ε s t) (Set.Icc t (t + ε)) := by
  intro a ha b hb hab
  have ha_s : s ≤ a := hst.trans ha.1
  have hb_s : s ≤ b := hst.trans hb.1
  rw [sqgConcreteMollifier_eq_right_factor ha_s hε,
      sqgConcreteMollifier_eq_right_factor hb_s hε]
  apply Real.smoothTransition.monotone
  exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)

/-! #### Tier 2 — derivative sign and vanishing zones -/

/-- **Tier 2a — derivative vanishes on the mid-interval `Ioo s t`.** On the
open interval `(s, t)` the mollifier is constantly 1, hence locally constant
in a neighborhood of any `τ ∈ Ioo s t`, so `deriv = 0` by
`Filter.EventuallyEq.deriv_eq`. -/
theorem sqgConcreteMollifier_deriv_zero_of_mem_Ioo {s t τ ε : ℝ}
    (hτ : τ ∈ Set.Ioo s t) (hε : 0 < ε) :
    deriv (sqgConcreteMollifier ε s t) τ = 0 := by
  have h : (sqgConcreteMollifier ε s t) =ᶠ[nhds τ] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact sqgConcreteMollifier_eq_one_of_mem_Ioo hx hε
  rw [h.deriv_eq]; exact deriv_const τ 1

/-- **Tier 2b — derivative vanishes strictly below `s − ε`.** Below the
support's left edge the mollifier is identically 0, so `deriv = 0`. -/
theorem sqgConcreteMollifier_deriv_zero_of_lt_left {s t τ ε : ℝ}
    (hτ : τ < s - ε) (hε : 0 < ε) :
    deriv (sqgConcreteMollifier ε s t) τ = 0 := by
  have h : (sqgConcreteMollifier ε s t) =ᶠ[nhds τ] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hτ] with x hx
    exact sqgConcreteMollifier_zero_of_le_left hε hx.le
  rw [h.deriv_eq]; exact deriv_const τ 0

/-- **Tier 2c — derivative vanishes strictly above `t + ε`.** Symmetric to
Tier 2b. -/
theorem sqgConcreteMollifier_deriv_zero_of_gt_right {s t τ ε : ℝ}
    (hτ : t + ε < τ) (hε : 0 < ε) :
    deriv (sqgConcreteMollifier ε s t) τ = 0 := by
  have h : (sqgConcreteMollifier ε s t) =ᶠ[nhds τ] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hτ] with x hx
    exact sqgConcreteMollifier_zero_of_ge_right hε hx.le
  rw [h.deriv_eq]; exact deriv_const τ 0

/-- **Tier 2d — derivative is non-negative on the interior of the left
collar.** In a neighborhood of `τ ∈ Ioo (s − ε) s` (specifically, any nbhd
contained in `Iic t`), the mollifier equals the monotone representative
`x ↦ smoothTransition ((x − s + ε)/ε)`. By `Filter.EventuallyEq.deriv_eq`
the derivative at `τ` matches, and the representative's derivative is
non-negative by `Monotone.deriv_nonneg`. -/
theorem sqgConcreteMollifier_deriv_nonneg_of_mem_left_collar
    {s t τ ε : ℝ} (hτ : τ ∈ Set.Ioo (s - ε) s) (hε : 0 < ε) (hst : s ≤ t) :
    0 ≤ deriv (sqgConcreteMollifier ε s t) τ := by
  set f : ℝ → ℝ := fun x => Real.smoothTransition ((x - s + ε) / ε) with hf_def
  have h_nhds : (sqgConcreteMollifier ε s t) =ᶠ[nhds τ] f := by
    filter_upwards [Iic_mem_nhds (lt_of_lt_of_le hτ.2 hst)] with x hx
    exact sqgConcreteMollifier_eq_left_factor hx hε
  rw [h_nhds.deriv_eq]
  have hf_mono : Monotone f := fun a b hab => by
    apply Real.smoothTransition.monotone
    exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
  exact hf_mono.deriv_nonneg

/-- **Tier 2e — derivative is non-positive on the interior of the right
collar.** Symmetric to Tier 2d: local representative is
`x ↦ smoothTransition ((t − x + ε)/ε)`, which is antitone, so
`deriv ≤ 0` by `Antitone.deriv_nonpos`. -/
theorem sqgConcreteMollifier_deriv_nonpos_of_mem_right_collar
    {s t τ ε : ℝ} (hτ : τ ∈ Set.Ioo t (t + ε)) (hε : 0 < ε) (hst : s ≤ t) :
    deriv (sqgConcreteMollifier ε s t) τ ≤ 0 := by
  set f : ℝ → ℝ := fun x => Real.smoothTransition ((t - x + ε) / ε) with hf_def
  have h_nhds : (sqgConcreteMollifier ε s t) =ᶠ[nhds τ] f := by
    filter_upwards [Ioi_mem_nhds (lt_of_le_of_lt hst hτ.1)] with x hx
    exact sqgConcreteMollifier_eq_right_factor hx.le hε
  rw [h_nhds.deriv_eq]
  have hf_anti : Antitone f := fun a b hab => by
    apply Real.smoothTransition.monotone
    exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
  exact hf_anti.deriv_nonpos

/-! #### Tier 3 — FTC mass identities on each collar -/

/-- **Plumbing — pointwise `HasDerivAt` from `ContDiff 1`.** Needed to feed
`intervalIntegral.integral_eq_sub_of_hasDerivAt` on every collar. -/
theorem sqgConcreteMollifier_hasDerivAt (ε s t x : ℝ) :
    HasDerivAt (sqgConcreteMollifier ε s t)
      (deriv (sqgConcreteMollifier ε s t) x) x :=
  ((sqgConcreteMollifier_contDiff ε s t).differentiable one_ne_zero)
    .differentiableAt.hasDerivAt

/-- **Plumbing — derivative is globally interval-integrable.** `sqgConcreteMollifier`
is `C¹`, so `deriv` is continuous and hence interval-integrable on any `[a, b]`. -/
theorem sqgConcreteMollifier_deriv_intervalIntegrable (ε s t a b : ℝ) :
    IntervalIntegrable (deriv (sqgConcreteMollifier ε s t)) volume a b :=
  ((sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one).intervalIntegrable a b

/-- **Tier 3a — Left-collar FTC mass identity.**
`∫_{s−ε}^{s} deriv ψ_ε = ψ_ε(s) − ψ_ε(s − ε) = 1 − 0 = 1`. -/
theorem sqgConcreteMollifier_integral_deriv_left_collar {ε s t : ℝ}
    (hε : 0 < ε) (hst : s ≤ t) :
    ∫ τ in (s - ε)..s, deriv (sqgConcreteMollifier ε s t) τ = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => sqgConcreteMollifier_hasDerivAt ε s t x)
        (sqgConcreteMollifier_deriv_intervalIntegrable ε s t _ _),
      sqgConcreteMollifier_eq_one_of_mem_Icc ⟨le_refl s, hst⟩ hε,
      sqgConcreteMollifier_zero_of_le_left hε (le_refl _)]
  ring

/-- **Tier 3b — Right-collar FTC mass identity.**
`∫_{t}^{t+ε} deriv ψ_ε = ψ_ε(t + ε) − ψ_ε(t) = 0 − 1 = −1`. -/
theorem sqgConcreteMollifier_integral_deriv_right_collar {ε s t : ℝ}
    (hε : 0 < ε) (hst : s ≤ t) :
    ∫ τ in t..(t + ε), deriv (sqgConcreteMollifier ε s t) τ = -1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => sqgConcreteMollifier_hasDerivAt ε s t x)
        (sqgConcreteMollifier_deriv_intervalIntegrable ε s t _ _),
      sqgConcreteMollifier_zero_of_ge_right hε (le_refl _),
      sqgConcreteMollifier_eq_one_of_mem_Icc ⟨hst, le_refl t⟩ hε]
  ring

/-! #### Tier 4 — split the full real integral into two collar interval integrals -/

/-- **Tier 4 plumbing — complex derivative via real derivative coercion.**
`deriv (τ ↦ ↑(ψ_ε τ)) = ↑(deriv ψ_ε τ)` because coercion `ℝ → ℂ` is `ℝ`-linear
and `ψ_ε` is real-differentiable at every point. -/
theorem sqgConcreteMollifier_deriv_complex (ε s t x : ℝ) :
    deriv (fun τ => (sqgConcreteMollifier ε s t τ : ℂ)) x =
      ((deriv (sqgConcreteMollifier ε s t) x : ℝ) : ℂ) :=
  ((sqgConcreteMollifier_hasDerivAt ε s t x).ofReal_comp).deriv

/-- **Tier 4 plumbing — `deriv ψ_ε` is zero at the left edge of the left
collar, `τ = s − ε`.** The derivative is continuous (by `ContDiff 1`) and
identically zero on the open half-line `(−∞, s − ε)`; uniqueness of the
one-sided limit from the left then pins down the boundary value. -/
theorem sqgConcreteMollifier_deriv_zero_at_s_minus_ε {s t ε : ℝ} (hε : 0 < ε) :
    deriv (sqgConcreteMollifier ε s t) (s - ε) = 0 := by
  have hcont : Continuous (deriv (sqgConcreteMollifier ε s t)) :=
    (sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one
  have h_left_lim : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
      (𝓝[<] (s - ε)) (𝓝 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [sqgConcreteMollifier_deriv_zero_of_lt_left hx hε]
  have h_full_tendsto : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
      (𝓝[<] (s - ε)) (𝓝 (deriv (sqgConcreteMollifier ε s t) (s - ε))) :=
    hcont.continuousAt.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h_full_tendsto h_left_lim

/-- **Tier 4 plumbing — `deriv ψ_ε` is zero at the right edge, `τ = t + ε`.**
Symmetric to `_deriv_zero_at_s_minus_ε`. -/
theorem sqgConcreteMollifier_deriv_zero_at_t_plus_ε {s t ε : ℝ} (hε : 0 < ε) :
    deriv (sqgConcreteMollifier ε s t) (t + ε) = 0 := by
  have hcont : Continuous (deriv (sqgConcreteMollifier ε s t)) :=
    (sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one
  have h_right_lim : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
      (𝓝[>] (t + ε)) (𝓝 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [sqgConcreteMollifier_deriv_zero_of_gt_right hx hε]
  have h_full_tendsto : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
      (𝓝[>] (t + ε)) (𝓝 (deriv (sqgConcreteMollifier ε s t) (t + ε))) :=
    hcont.continuousAt.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h_full_tendsto h_right_lim

/-- **Tier 4 plumbing — `deriv ψ_ε` vanishes on the closed mid-interval
`[s, t]`.** On `Ioo s t` it is zero by Tier 2a; at the endpoints `s` and
`t` (with `s < t`) the one-sided limit of the continuous `deriv` equals zero
by approaching from the inside, pinning the value down. When `s = t` we use
the boundary-edge vanishing at `s = t` directly, approached from outside the
collars on the other side. -/
theorem sqgConcreteMollifier_deriv_zero_on_mid_Icc {s t τ ε : ℝ} (hε : 0 < ε)
    (hst : s ≤ t) (hτ : τ ∈ Set.Icc s t) :
    deriv (sqgConcreteMollifier ε s t) τ = 0 := by
  rcases eq_or_lt_of_le hst with rfl | hst_lt
  · -- s = t case; τ = s = t. Squeeze: deriv ≥ 0 from the left-collar side,
    -- deriv ≤ 0 from the right-collar side, continuity forces = 0.
    have hτ_eq : τ = t := le_antisymm hτ.2 hτ.1
    subst hτ_eq
    have hcont : Continuous (deriv (sqgConcreteMollifier ε t t)) :=
      (sqgConcreteMollifier_contDiff ε t t).continuous_deriv_one
    have hlb : 0 ≤ deriv (sqgConcreteMollifier ε t t) t := by
      have h_t : Filter.Tendsto (deriv (sqgConcreteMollifier ε t t))
          (𝓝[<] t) (𝓝 (deriv (sqgConcreteMollifier ε t t) t)) :=
        hcont.continuousAt.mono_left nhdsWithin_le_nhds
      apply ge_of_tendsto h_t
      filter_upwards [Ioo_mem_nhdsLT (show t - ε < t by linarith)] with x hx
      exact sqgConcreteMollifier_deriv_nonneg_of_mem_left_collar hx hε le_rfl
    have hub : deriv (sqgConcreteMollifier ε t t) t ≤ 0 := by
      have h_t : Filter.Tendsto (deriv (sqgConcreteMollifier ε t t))
          (𝓝[>] t) (𝓝 (deriv (sqgConcreteMollifier ε t t) t)) :=
        hcont.continuousAt.mono_left nhdsWithin_le_nhds
      apply le_of_tendsto h_t
      filter_upwards [Ioo_mem_nhdsGT (show t < t + ε by linarith)] with x hx
      exact sqgConcreteMollifier_deriv_nonpos_of_mem_right_collar hx hε le_rfl
    linarith
  · rcases eq_or_lt_of_le hτ.1 with heq_s | hτ_gt_s
    · subst heq_s
      -- τ = s: deriv from right is 0 (deriv = 0 on Ioo s t)
      have hcont : Continuous (deriv (sqgConcreteMollifier ε s t)) :=
        (sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one
      have h_right_lim : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
          (𝓝[>] s) (𝓝 0) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        filter_upwards [Ioo_mem_nhdsGT hst_lt] with x hx
        rw [sqgConcreteMollifier_deriv_zero_of_mem_Ioo hx hε]
      have h_full_tendsto : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
          (𝓝[>] s) (𝓝 (deriv (sqgConcreteMollifier ε s t) s)) :=
        hcont.continuousAt.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique h_full_tendsto h_right_lim
    · rcases eq_or_lt_of_le hτ.2 with heq_t | hτ_lt_t
      · subst heq_t
        -- τ = t: deriv from left is 0
        have hcont : Continuous (deriv (sqgConcreteMollifier ε s t)) :=
          (sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one
        have h_left_lim : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
            (𝓝[<] τ) (𝓝 0) := by
          apply Filter.Tendsto.congr' _ tendsto_const_nhds
          filter_upwards [Ioo_mem_nhdsLT hτ_gt_s] with x hx
          rw [sqgConcreteMollifier_deriv_zero_of_mem_Ioo hx hε]
        have h_full_tendsto : Filter.Tendsto (deriv (sqgConcreteMollifier ε s t))
            (𝓝[<] τ) (𝓝 (deriv (sqgConcreteMollifier ε s t) τ)) :=
          hcont.continuousAt.mono_left nhdsWithin_le_nhds
        exact tendsto_nhds_unique h_full_tendsto h_left_lim
      · exact sqgConcreteMollifier_deriv_zero_of_mem_Ioo ⟨hτ_gt_s, hτ_lt_t⟩ hε

/-- **Tier 4 — derivative (complex-valued) vanishes outside the two open
collars (extended to include their separating boundaries).** -/
theorem sqgConcreteMollifier_deriv_complex_zero_off_collars
    {ε s t τ : ℝ} (hε : 0 < ε) (hst : s ≤ t)
    (hτ : τ ≤ s - ε ∨ τ ∈ Set.Icc s t ∨ t + ε ≤ τ) :
    deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ = 0 := by
  rw [sqgConcreteMollifier_deriv_complex]
  rcases hτ with h | h | h
  · rcases eq_or_lt_of_le h with rfl | h
    · rw [sqgConcreteMollifier_deriv_zero_at_s_minus_ε hε]; simp
    · rw [sqgConcreteMollifier_deriv_zero_of_lt_left h hε]; simp
  · rw [sqgConcreteMollifier_deriv_zero_on_mid_Icc hε hst h]; simp
  · rcases eq_or_lt_of_le h with rfl | h
    · rw [sqgConcreteMollifier_deriv_zero_at_t_plus_ε hε]; simp
    · rw [sqgConcreteMollifier_deriv_zero_of_gt_right h hε]; simp

/-- **Tier 4 plumbing — interval integrability of the product integrand.** -/
theorem sqgConcreteMollifier_product_intervalIntegrable
    (ε s t : ℝ) {F : ℝ → ℂ} (hF : Continuous F) (a b : ℝ) :
    IntervalIntegrable
      (fun τ => deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ)
      volume a b := by
  apply Continuous.intervalIntegrable
  apply Continuous.mul _ hF
  have : (fun τ => deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ) =
         (fun τ => ((deriv (sqgConcreteMollifier ε s t) τ : ℝ) : ℂ)) := by
    funext τ; exact sqgConcreteMollifier_deriv_complex ε s t τ
  rw [this]
  exact Complex.continuous_ofReal.comp
    ((sqgConcreteMollifier_contDiff ε s t).continuous_deriv_one)

/-- **Tier 4 — the full real integral equals the buffered interval integral.** -/
theorem sqgConcreteMollifier_integral_eq_buffered
    {ε s t : ℝ} (hε : 0 < ε) (hst : s ≤ t) (F : ℝ → ℂ) :
    ∫ τ, deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ
      = ∫ τ in (s - ε - 1)..(t + ε + 1),
          deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro τ hτ
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    apply hτ
    have hτ_le : τ ≤ s - ε := by linarith
    rw [sqgConcreteMollifier_deriv_complex_zero_off_collars hε hst (Or.inl hτ_le)]
    ring
  · by_contra h
    push_neg at h
    apply hτ
    have hτ_ge : t + ε ≤ τ := by linarith
    rw [sqgConcreteMollifier_deriv_complex_zero_off_collars hε hst
          (Or.inr (Or.inr hτ_ge))]
    ring

/-- **Tier 4 — full real integral decomposed as a sum over the two collars.** -/
theorem sqgConcreteMollifier_integral_collar_split
    {ε s t : ℝ} (hε : 0 < ε) (hst : s ≤ t) {F : ℝ → ℂ} (hF : Continuous F) :
    ∫ τ, deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ
      = (∫ τ in (s - ε)..s,
          deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ)
      + (∫ τ in t..(t + ε),
          deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ) := by
  set G : ℝ → ℂ := fun τ =>
    deriv (fun x => (sqgConcreteMollifier ε s t x : ℂ)) τ * F τ with hG_def
  have hII : ∀ a b : ℝ, IntervalIntegrable G volume a b :=
    fun a b => sqgConcreteMollifier_product_intervalIntegrable ε s t hF a b
  rw [sqgConcreteMollifier_integral_eq_buffered hε hst F]
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hII (s - ε - 1) (s - ε)) (hII (s - ε) _),
      ← intervalIntegral.integral_add_adjacent_intervals (hII (s - ε) s) (hII s _),
      ← intervalIntegral.integral_add_adjacent_intervals (hII s t) (hII t _),
      ← intervalIntegral.integral_add_adjacent_intervals (hII t (t + ε)) (hII (t + ε) _)]
  have h_outer_left : ∫ τ in (s - ε - 1)..(s - ε), G τ = 0 := by
    rw [show (∫ τ in (s - ε - 1)..(s - ε), G τ)
          = ∫ τ in (s - ε - 1)..(s - ε), (0 : ℂ) from ?_,
        intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith : s - ε - 1 ≤ s - ε)] at hτ
    rw [hG_def, sqgConcreteMollifier_deriv_complex_zero_off_collars hε hst
          (Or.inl hτ.2)]
    ring
  have h_mid : ∫ τ in s..t, G τ = 0 := by
    rw [show (∫ τ in s..t, G τ) = ∫ τ in s..t, (0 : ℂ) from ?_,
        intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le hst] at hτ
    rw [hG_def, sqgConcreteMollifier_deriv_complex_zero_off_collars hε hst
          (Or.inr (Or.inl hτ))]
    ring
  have h_outer_right : ∫ τ in (t + ε)..(t + ε + 1), G τ = 0 := by
    rw [show (∫ τ in (t + ε)..(t + ε + 1), G τ)
          = ∫ τ in (t + ε)..(t + ε + 1), (0 : ℂ) from ?_,
        intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith : t + ε ≤ t + ε + 1)] at hτ
    rw [hG_def, sqgConcreteMollifier_deriv_complex_zero_off_collars hε hst
          (Or.inr (Or.inr hτ.1))]
    ring
  rw [h_outer_left, h_outer_right, h_mid, zero_add, add_zero]

end SqgIdentity
