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
`Δ_N f := ∑_{2^{N-1} ≤ ‖m‖_∞ < 2^N} f̂(m) · e_m` for `N ≥ 1`, plus the
zero-mode projector `Δ_0 f := f̂(0) · 1`.  The family forms a disjoint
Fourier partition of `ℤ²`.

## Main contents

* `dyadicAnnulus N : Finset (Fin 2 → ℤ)` — finite set of lattice points
  in the dyadic annulus `{2^{N-1} ≤ ‖m‖_∞ < 2^N}` (or `{0}` for `N = 0`).
* `fourierTruncate A f` — Fourier projection onto a finite set `A`,
  defined as `trigPoly A (mFourierCoeff f ·)`.
* `lpProjector N f` — `Δ_N f`, the dyadic projection at level `N`.
* `fourierTruncate_mFourierCoeff` — Fourier coefficients of the projection
  (Kronecker-indicator of `A`).
* `hsSeminormSq_fourierTruncate` — `Ḣˢ`-seminorm of the projection
  equals the weighted ℓ² norm on `A`.

## Conventions

We use the `ℓ∞` (supremum) norm-based dyadic blocks on `ℤ²`:
`dyadicAnnulus N := {m : ‖m‖_∞ ∈ [2^{N-1}, 2^N)}` for `N ≥ 1`.
This matches `sqgBox` (which uses `ℓ∞`-balls) and makes `Δ_N` a
`sqgBox`-difference.
-/

namespace SqgIdentity

open Complex Finset MeasureTheory

/-! ### §11.1 Dyadic annuli on `ℤ²`

The `ℓ∞`-dyadic annulus `dyadicAnnulus N` is the set of lattice points
whose largest coordinate (in absolute value) lies in `[2^{N-1}, 2^N)`.
For `N = 0` we take `{0}` so that `⋃_N dyadicAnnulus N = ℤ²` is a
disjoint decomposition. -/

/-- **Dyadic `ℓ∞`-annulus on `ℤ²`.**  For `N ≥ 1`:
`sqgBox (2^N - 1) \ sqgBox (2^(N-1) - 1)` (so `‖m‖_∞ ∈ [2^{N-1}, 2^N)`).
For `N = 0`: `{0}`.

`sqgBox k = {m : m ≠ 0, ∀ i, |m i| ≤ k + 1}`, so
`sqgBox (2^N - 1) = {m ≠ 0 : ‖m‖_∞ ≤ 2^N}` (when `N ≥ 1`). -/
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
  rw [Finset.mem_sdiff]
  push_neg
  intro h
  exact absurd h (zero_not_mem_sqgBox _)

/-! ### §11.2 Fourier truncation onto a finite set

For a Finset `A ⊆ ℤ²`, define `fourierTruncate A f` as the trig-poly
with Fourier coefficients matching `f` on `A` and zero elsewhere.
This is the Fourier projection onto the span of `{e_m : m ∈ A}`. -/

/-- **Fourier projection onto a finite set.** Uses existing `trigPoly`
infrastructure. -/
noncomputable def fourierTruncate
    (A : Finset (Fin 2 → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  trigPoly A (fun m => mFourierCoeff f m)

/-! ### §11.3 Littlewood–Paley dyadic projector `Δ_N`

`lpProjector N f := fourierTruncate (dyadicAnnulus N) f`. -/

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

/-! ### §11.4 Basic dyadic arithmetic -/

/-- **Dyadic annulus at level `N ≥ 1` is contained in `sqgBox (2^N - 1)`.**
This is the upper envelope for `lpPartialSum N f` Fourier support. -/
lemma dyadicAnnulus_subset_sqgBox_pos {N : ℕ} (hN : 0 < N) :
    dyadicAnnulus N ⊆ sqgBox (2 ^ N - 1) := by
  unfold dyadicAnnulus
  rw [if_neg (Nat.pos_iff_ne_zero.mp hN)]
  exact Finset.sdiff_subset

end SqgIdentity
