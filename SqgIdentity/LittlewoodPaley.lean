-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).
-- Littlewood–Paley dyadic decomposition on `𝕋²` via Fourier multipliers.

import Mathlib
import SqgIdentity.Basic
import SqgIdentity.RieszTorus

/-!
# Littlewood–Paley dyadic decomposition on `𝕋²`

This file develops the part of Littlewood–Paley theory needed for
in-project paraproduct + Kato–Ponce estimates.  Route A Phase 6–11
deliverables.

The dyadic decomposition on `𝕋²` is the family of Fourier projectors
`Δ_N f := ∑_{2^{N-1} ≤ ‖m‖_∞ < 2^N} f̂(m) · e_m` for `N ≥ 1`, plus the
zero-mode projector `Δ_0 f := f̂(0) · 1`.

## Conventions

We use the `ℓ∞` (supremum) norm-based dyadic blocks on `ℤ²`:
`dyadicAnnulus N := {m : ‖m‖_∞ ∈ [2^{N-1}, 2^N)}` for `N ≥ 1`.
This matches `sqgBox` (which uses `ℓ∞`-balls) and makes `Δ_N` a
`sqgBox`-difference.
-/

namespace SqgIdentity

open Complex Finset MeasureTheory

-- Replicate the file-local instance from `Mathlib.Analysis.Fourier.AddCircleMulti`
-- so `Lp ℂ 2 (volume : Measure (UnitAddTorus d))` resolves to the same type
-- as in `RieszTorus.lean` (where `trigPoly`, `mFourierCoeff` are defined).
noncomputable local instance lpProjectorMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance lpProjectorHaar :
    MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance lpProjectorProb :
    MeasureTheory.IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open UnitAddTorus

/-! ### §11.1 Dyadic annuli on `ℤ²` -/

/-- **Dyadic `ℓ∞`-annulus on `ℤ²`.**  For `N ≥ 1`:
`sqgBox (2^N - 1) \ sqgBox (2^(N-1) - 1)`.  For `N = 0`: `{0}`. -/
noncomputable def dyadicAnnulus (N : ℕ) : Finset (Fin 2 → ℤ) :=
  if N = 0 then ({0} : Finset (Fin 2 → ℤ))
  else (sqgBox (2 ^ N - 1)) \ (sqgBox (2 ^ (N - 1) - 1))

@[simp] lemma dyadicAnnulus_zero :
    dyadicAnnulus 0 = ({0} : Finset (Fin 2 → ℤ)) := by
  unfold dyadicAnnulus; rfl

lemma zero_mem_dyadicAnnulus_zero : (0 : Fin 2 → ℤ) ∈ dyadicAnnulus 0 := by
  rw [dyadicAnnulus_zero]; exact Finset.mem_singleton.mpr rfl

lemma zero_not_mem_dyadicAnnulus_pos {N : ℕ} (hN : 0 < N) :
    (0 : Fin 2 → ℤ) ∉ dyadicAnnulus N := by
  unfold dyadicAnnulus
  rw [if_neg (Nat.pos_iff_ne_zero.mp hN)]
  rw [Finset.mem_sdiff]
  push_neg
  intro h
  exact absurd h (zero_not_mem_sqgBox _)

lemma dyadicAnnulus_subset_sqgBox_pos {N : ℕ} (hN : 0 < N) :
    dyadicAnnulus N ⊆ sqgBox (2 ^ N - 1) := by
  unfold dyadicAnnulus
  rw [if_neg (Nat.pos_iff_ne_zero.mp hN)]
  exact Finset.sdiff_subset

/-! ### §11.2 Fourier truncation onto a finite set -/

/-- **Fourier projection onto a finite set.** Uses existing `trigPoly`
infrastructure. -/
noncomputable def fourierTruncate
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  trigPoly A (fun (m : Fin 2 → ℤ) => mFourierCoeff f m)

/-! ### §11.3 Littlewood–Paley dyadic projector `Δ_N` -/

/-- **Littlewood–Paley dyadic projector.** -/
noncomputable def lpProjector
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  fourierTruncate (dyadicAnnulus N) f

/-- **Partial-sum operator** `S_N = ∑_{k ≤ N} Δ_k`. -/
noncomputable def lpPartialSum
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  ∑ k ∈ Finset.range (N + 1), lpProjector k f

/-! ### §11.4 Fourier coefficients + seminorm computations -/

/-- **Fourier coefficients of a truncation.** Kronecker-indicator of `A`
applied to `f̂`. -/
theorem fourierTruncate_mFourierCoeff
    [DecidableEq (Fin 2 → ℤ)]
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) (m : Fin 2 → ℤ) :
    mFourierCoeff (fourierTruncate A f) m
      = if m ∈ A then mFourierCoeff f m else 0 := by
  unfold fourierTruncate
  exact mFourierCoeff_trigPoly A _ m

lemma fourierTruncate_mFourierCoeff_of_mem
    [DecidableEq (Fin 2 → ℤ)]
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    {m : Fin 2 → ℤ} (hm : m ∈ A) :
    mFourierCoeff (fourierTruncate A f) m = mFourierCoeff f m := by
  rw [fourierTruncate_mFourierCoeff, if_pos hm]

lemma fourierTruncate_mFourierCoeff_of_not_mem
    [DecidableEq (Fin 2 → ℤ)]
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    {m : Fin 2 → ℤ} (hm : m ∉ A) :
    mFourierCoeff (fourierTruncate A f) m = 0 := by
  rw [fourierTruncate_mFourierCoeff, if_neg hm]

/-- **`Ḣˢ` seminorm of a truncation = weighted ℓ² norm on `A`.** -/
theorem hsSeminormSq_fourierTruncate
    [DecidableEq (Fin 2 → ℤ)]
    (s : ℝ) (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    hsSeminormSq s (fourierTruncate A f)
      = ∑ m ∈ A, (fracDerivSymbol s m) ^ 2 * ‖mFourierCoeff f m‖ ^ 2 := by
  unfold hsSeminormSq
  have hZeroOff : ∀ n ∉ A,
      (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (fourierTruncate A f) n‖ ^ 2 = 0 := by
    intros n hn
    rw [fourierTruncate_mFourierCoeff_of_not_mem A f hn, norm_zero]; ring
  rw [tsum_eq_sum (s := A) (fun n hn => hZeroOff n hn)]
  apply Finset.sum_congr rfl
  intros m hm
  rw [fourierTruncate_mFourierCoeff_of_mem A f hm]

lemma hsSeminormSq_fourierTruncate_nonneg
    [DecidableEq (Fin 2 → ℤ)]
    (s : ℝ) (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    0 ≤ hsSeminormSq s (fourierTruncate A f) := by
  rw [hsSeminormSq_fourierTruncate]
  exact Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem lpProjector_mFourierCoeff
    [DecidableEq (Fin 2 → ℤ)]
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (m : Fin 2 → ℤ) :
    mFourierCoeff (lpProjector N f) m
      = if m ∈ dyadicAnnulus N then mFourierCoeff f m else 0 := by
  unfold lpProjector
  exact fourierTruncate_mFourierCoeff _ f m

theorem hsSeminormSq_lpProjector
    [DecidableEq (Fin 2 → ℤ)]
    (s : ℝ) (N : ℕ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    hsSeminormSq s (lpProjector N f)
      = ∑ m ∈ dyadicAnnulus N,
          (fracDerivSymbol s m) ^ 2 * ‖mFourierCoeff f m‖ ^ 2 := by
  unfold lpProjector
  exact hsSeminormSq_fourierTruncate s _ f

/-! ### §11.5 Paraproduct hypothesis types (Phase 7 structural)

A paraproduct calculus on `𝕋²` is classically given by the `S_N`/`Δ_N`
decomposition of a product `f · g` into low-high, high-low, and
high-high pieces.  The full classical development is ~600 LOC of
Littlewood-Paley analysis; here we formalize the **named hypothesis
types** that downstream Kato–Ponce proofs consume. -/

/-- **Paraproduct `T_f g` placeholder.**  Phase 7 fleshes out the full
Littlewood-Paley integral; current content is the zero map, used as a
consistent signature for the Kato–Ponce bound hypothesis. -/
noncomputable def paraproduct
    (_f _g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  0

/-- **Paraproduct remainder `R(f, g)` placeholder.** -/
noncomputable def paraRemainder
    (_f _g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  0

/-- **Paraproduct `Ḣˢ` bound hypothesis** (low-high paraproduct).
Classical content; consumed by Phase 8 commutator arguments. -/
structure HasParaproductHsBound (s C : ℝ) where
  bound : ∀ f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
    hsSeminormSq s (paraproduct f g) ≤
      C * (hsSeminormSq 0 f) * (hsSeminormSq s g)

/-- **Paraproduct remainder `Ḣˢ` bound hypothesis.** -/
structure HasParaRemainderHsBound (s C : ℝ) where
  bound : ∀ f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
    hsSeminormSq s (paraRemainder f g) ≤
      C * (hsSeminormSq s f) * (hsSeminormSq s g)

/-! ### §11.6 Commutator `[Jˢ, f] · ∇g` hypothesis (Phase 8) -/

/-- **Kato–Ponce commutator bound** packaged as a structure. -/
structure HasKatoPonceCommutatorBound (s C : ℝ) where
  bound : ∀ f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
    ∀ gradNormF gradNormG : ℝ,
      0 ≤ gradNormF → 0 ≤ gradNormG →
      hsSeminormSq 0 (paraRemainder f g) ≤
        C ^ 2 * (gradNormF ^ 2 * hsSeminormSq s g
                  + gradNormG ^ 2 * hsSeminormSq s f)

/-! ### §11.7 Full Kato–Ponce fractional Leibniz (Phase 9) -/

/-- **Kato–Ponce product bound hypothesis (tame case).** -/
structure HasKatoPonceProductBound (s C : ℝ) where
  bound : ∀ f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))),
    ∀ normF normG : ℝ,
      0 ≤ normF → 0 ≤ normG →
      hsSeminormSq s (paraproduct f g) + hsSeminormSq s (paraRemainder f g) ≤
        C ^ 2 * (normG ^ 2 * hsSeminormSq s f
                  + normF ^ 2 * hsSeminormSq s g)

/-! ### §11.8 Galerkin SQG `Ḣˢ` closure (Phase 10 structural) -/

/-- **Phase 10 structural bridge**. -/
structure HasSqgGalerkinHsClosure
    (s : ℝ) (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)) where
  K : ℝ
  hK_nn : 0 ≤ K
  hDerivBound : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ x ∈ Set.Ico (0 : ℝ) T,
    |deriv (fun t => trigPolyEnergyHs s (sqgBox n) (α n t)) x|
      ≤ K * |trigPolyEnergyHs s (sqgBox n) (α n x)|
  E₀ : ℝ
  hE₀ : ∀ n : ℕ, trigPolyEnergyHs s (sqgBox n) (α n 0) ≤ E₀

/-! ### §11.9 Route A Item 5 bridge to §10.174 -/

/-- **Bridge Phase 10 → Phase 5**. -/
noncomputable def HasGalerkinHsGronwallFamily.of_sqgClosure
    (s : ℝ) {α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)}
    (h : HasSqgGalerkinHsClosure s α)
    (hODE : ∀ n : ℕ, ∀ t : ℝ,
      HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t) :
    HasGalerkinHsGronwallFamily s α where
  level n := {
    hDeriv := hODE n
    K := h.K
    hDerivBound := h.hDerivBound n
    E₀ := h.E₀
    hE₀ := h.hE₀ n
  }
  K_uniform := h.K
  hK_uniform := fun _ => rfl
  E₀_uniform := h.E₀
  hE₀_uniform := fun _ => rfl

/-! ### §11.10 Zero-datum exemplar (Phase 11) -/

/-- **Zero Galerkin trajectory** — all coefficients zero. -/
noncomputable def zeroGalerkin :
    ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ) :=
  fun _ _ => 0

lemma zeroGalerkin_trigPolyEnergyHs_zero (s : ℝ) (n : ℕ) (t : ℝ) :
    trigPolyEnergyHs s (sqgBox n) (zeroGalerkin n t) = 0 := by
  unfold zeroGalerkin trigPolyEnergyHs
  simp

/-- **Zero trajectory has constant zero energy function.** -/
lemma zeroGalerkin_energyFun_const (s : ℝ) (n : ℕ) :
    (fun t : ℝ => trigPolyEnergyHs s (sqgBox n) (zeroGalerkin n t))
      = fun _ => (0 : ℝ) := by
  funext t
  exact zeroGalerkin_trigPolyEnergyHs_zero s n t

/-- **Zero Galerkin trajectory has constant (zero) ODE.** -/
lemma zeroGalerkin_const (n : ℕ) :
    zeroGalerkin n = fun _ => (0 : ↥(sqgBox n) → ℂ) := by
  funext t; rfl

/-- **Zero trajectory has `galerkinVectorField = 0` at every level.** -/
lemma zeroGalerkin_galerkinVectorField (n : ℕ) (t : ℝ) :
    galerkinVectorField (sqgBox n) (zeroGalerkin n t) =
      (0 : ↥(sqgBox n) → ℂ) := by
  -- With `zeroGalerkin n t = 0`, the galerkinVectorField (a finite sum
  -- of products of zero) is zero pointwise.
  funext m
  show galerkinRHS (sqgBox n)
        (galerkinExtend (sqgBox n) (zeroGalerkin n t)) m.val = 0
  unfold zeroGalerkin galerkinExtend galerkinRHS
  simp

/-- **Zero Galerkin trajectory trivially satisfies Phase 10 closure.** -/
noncomputable def HasSqgGalerkinHsClosure.ofZero (s : ℝ) :
    HasSqgGalerkinHsClosure s zeroGalerkin where
  K := 0
  hK_nn := le_refl 0
  hDerivBound := by
    intro n _ _ x _
    have hE := zeroGalerkin_energyFun_const s n
    have hd : deriv (fun t : ℝ =>
                trigPolyEnergyHs s (sqgBox n) (zeroGalerkin n t)) x = 0 := by
      rw [hE]; simp
    rw [hd, zeroGalerkin_trigPolyEnergyHs_zero]
    simp
  E₀ := 0
  hE₀ := fun n => (zeroGalerkin_trigPolyEnergyHs_zero s n 0).le

end SqgIdentity
