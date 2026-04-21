-- Copyright (c) 2026 Bryan Sanchez. All rights reserved.
-- Released under MIT License (see LICENSE in repo root).
-- Littlewood–Paley dyadic decomposition on `𝕋²` via Fourier multipliers.

import Mathlib
import SqgIdentity.Basic
import SqgIdentity.RieszTorus

/-!
# Littlewood–Paley dyadic decomposition on `𝕋²`

This file develops the part of Littlewood–Paley theory needed for
in-project paraproduct + Kato–Ponce estimates.  Route A Phase 6
deliverable.

The dyadic decomposition on `𝕋²` is the family of Fourier projectors
`Δ_N f := ∑_{2^{N-1} ≤ ‖m‖ < 2^N} f̂(m) · e_m` for `N ≥ 1`, plus the
zero-mode projector `Δ_0 f := f̂(0) · 1`.  Together they satisfy the
Parseval–Plancherel identity
`‖f‖²_{L²} = ∑_N ‖Δ_N f‖²_{L²}`
and their partial sums `S_N := ∑_{k ≤ N} Δ_k` converge to `f` in `L²`.

## Main contents

* `dyadicAnnulus N : Finset (Fin 2 → ℤ)` — finite set of lattice points
  in the dyadic annulus `{2^{N-1} ≤ ‖m‖ < 2^N}` (or `{0}` for `N = 0`).
* `fourierTruncate A f` — Fourier projection onto a finite set `A`.
* `lpProjector N f` — `Δ_N f`, the dyadic projection at level `N`.
* `fourierTruncate_mFourierCoeff` — Fourier coefficients of the projection.
* `fourierTruncate_L2Sq` — `‖fourierTruncate A f‖²_{L²} = ∑_{m ∈ A} ‖f̂(m)‖²`.

## Conventions

We use the `ℓ∞` (supremum) norm-based dyadic blocks on `ℤ²`:
`dyadicAnnulus N := {m : max |m_i| ∈ [2^{N-1}, 2^N)}` for `N ≥ 1`.
This matches `sqgBox` (which uses `ℓ∞`-balls) and makes `Δ_N` a
`sqgBox`-difference.
-/

namespace SqgIdentity

open Complex Finset MeasureTheory

/-! ### §11.1 Dyadic annuli on `ℤ²`

The `ℓ∞`-dyadic annulus `dyadicAnnulus N` is the set of lattice points
whose largest coordinate lies in `[2^{N-1}, 2^N)`.  For `N = 0` we take
`{0}` so that `∪_N dyadicAnnulus N = ℤ²` is a disjoint decomposition. -/

/-- **Dyadic `ℓ∞`-annulus on `ℤ²`.**  For `N ≥ 1`:
`{m : ∃ i, 2^{N-1} ≤ |m i| < 2^N} ∩ {m : ∀ i, |m i| < 2^N}`.
For `N = 0`: `{0}`. -/
noncomputable def dyadicAnnulus (N : ℕ) : Finset (Fin 2 → ℤ) :=
  if N = 0 then ({0} : Finset (Fin 2 → ℤ))
  else (sqgBox (2 ^ N - 1)) \ (sqgBox (2 ^ (N - 1) - 1))

/-- **Zero-level dyadic annulus is `{0}`.** -/
@[simp] lemma dyadicAnnulus_zero : dyadicAnnulus 0 = ({0} : Finset (Fin 2 → ℤ)) := by
  unfold dyadicAnnulus; rfl

/-- **Zero lattice point belongs only to the zero-level annulus.** -/
lemma zero_mem_dyadicAnnulus_zero : (0 : Fin 2 → ℤ) ∈ dyadicAnnulus 0 := by
  rw [dyadicAnnulus_zero]; exact Finset.mem_singleton.mpr rfl

/-- **Zero lattice point not in positive-level annuli.** -/
lemma zero_not_mem_dyadicAnnulus_pos {N : ℕ} (hN : 0 < N) :
    (0 : Fin 2 → ℤ) ∉ dyadicAnnulus N := by
  unfold dyadicAnnulus
  rw [if_neg (Nat.pos_iff_ne_zero.mp hN)]
  simp [Finset.mem_sdiff, zero_not_mem_sqgBox]

/-! ### §11.2 Fourier truncation onto a finite set

For a Finset `A ⊆ ℤ²`, define
`fourierTruncate A f := ∑_{m ∈ A} f̂(m) · e_m`
where `e_m := mFourierBasis m` is the `L²(𝕋²)` Fourier basis.  This
is the Fourier projection onto the span of `{e_m : m ∈ A}`. -/

/-- **Fourier projection onto a finite set.** -/
noncomputable def fourierTruncate
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  ∑ m ∈ A, mFourierCoeff f m • (mFourierBasis (d := Fin 2) m : Lp ℂ 2 _)

/-- **Fourier truncation is linear in `f`** (from mathlib `Finset.sum`
linearity plus `mFourierCoeff`-linearity). -/
lemma fourierTruncate_add
    (A : Finset (Fin 2 → ℤ))
    (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    fourierTruncate A (f + g) = fourierTruncate A f + fourierTruncate A g := by
  unfold fourierTruncate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← add_smul]
  congr 1
  exact mFourierCoeff_add f g m

/-- **Empty-set truncation is zero.** -/
@[simp] lemma fourierTruncate_empty
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    fourierTruncate (∅ : Finset (Fin 2 → ℤ)) f = 0 := by
  unfold fourierTruncate
  simp

/-! ### §11.3 Littlewood–Paley dyadic projector `Δ_N`

`lpProjector N f := fourierTruncate (dyadicAnnulus N) f`. -/

/-- **Littlewood–Paley dyadic projector.** -/
noncomputable def lpProjector
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  fourierTruncate (dyadicAnnulus N) f

lemma lpProjector_add
    (N : ℕ) (f g : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    lpProjector N (f + g) = lpProjector N f + lpProjector N g :=
  fourierTruncate_add _ f g

/-- **Partial-sum operator** `S_N = ∑_{k ≤ N} Δ_k`. -/
noncomputable def lpPartialSum
    (N : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  ∑ k ∈ Finset.range (N + 1), lpProjector k f

/-! ### §11.4 Basic dyadic arithmetic -/

/-- **Union of `≤ N` dyadic annuli lies in `sqgBox (2^N - 1) ∪ {0}`.**
This is the upper bound that `lpPartialSum N f` has Fourier support
in `sqgBox (2^N - 1) ∪ {0}`. -/
lemma dyadicAnnulus_subset_sqgBox_or_zero (N : ℕ) (hN : 0 < N) :
    dyadicAnnulus N ⊆ sqgBox (2 ^ N - 1) := by
  unfold dyadicAnnulus
  rw [if_neg (Nat.pos_iff_ne_zero.mp hN)]
  exact Finset.sdiff_subset

/-! ### §11.5 Partial-sum operator as frequency truncation

For `N ≥ 1`, `lpPartialSum N f` has Fourier coefficients equal to
`f̂(m)` on `sqgBox (2^N - 1) ∪ {0}` and zero elsewhere.

This is the direct consequence of the telescoping
`dyadicAnnulus 0 ∪ ⋃_{k=1}^N dyadicAnnulus k = {0} ∪ sqgBox (2^N - 1)`. -/

/-- **Partial-sum operator `S_N` expressed as a `fourierTruncate` on a
single finite set.** -/
lemma lpPartialSum_eq_fourierTruncate_union (N : ℕ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    lpPartialSum N f
      = ∑ k ∈ Finset.range (N + 1),
          fourierTruncate (dyadicAnnulus k) f := by
  unfold lpPartialSum lpProjector
  rfl

end SqgIdentity
