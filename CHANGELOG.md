# Changelog

All releases are archived on Zenodo; the concept DOI
[10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) resolves
to the latest version.

## v0.4.9 — 2026-04-19

Energy inequality derived directly from Galerkin dynamics; unconditional
`BKMCriterionS2` on the finite-Fourier-support, real-coefficient,
uniform-ℓ∞-coefficient class. 14,105 lines, zero `sorry`, zero new axioms.

- §10.79 combined advection + commutator factorization (ring-closed via
  §10.62 split).
- §10.80 pair-`Finset` reindexing `(m, ℓ) ↔ (m−ℓ, ℓ)` via
  `Finset.sum_nbij'`.
- §10.81 per-pair algebraic identity bridging the energy summand at
  `(p.1+p.2, p.2)` to `advectionSummand + commutatorSummand` with Riesz
  velocity.
- §10.82 real inner product on `ℂ` as `Re(star z · w)` via `Complex.inner`.
- §10.83 pair-sum form of the energy derivative (8-step proof composing
  §10.69 + §10.48 + §10.79–§10.82).
- §10.84 advection cancellation in the energy derivative via §10.74.
- §10.85 per-mode and per-pair L² bounds from Ḣ² energy.
- §10.86 energy inequality `|d/dt E| ≤ 24·D⁵·M·|S|² · E` under
  finite-support + real-coefficient + uniform-ℓ∞ hypotheses.
- §10.87 top-level capstone
  `BKMCriterionS2.of_galerkin_dynamics_with_L_inf_bound`.

Archive: [10.5281/zenodo.19654673](https://doi.org/10.5281/zenodo.19654673).

## v0.4.8 — 2026-04-19

Kato–Ponce + advection-cancellation derivation of `BKMCriterionS2` from a
supplied energy inequality. Parallel to the trivial-M route of §10.57.

- §10.61–§10.63 foundations: `comSymb k ℓ := ‖k+ℓ‖⁴ − ‖k‖⁴`; triangle +
  Cauchy–Schwarz on the integer lattice; Kato–Ponce symbol bound
  `|comSymb k ℓ| ≤ 6·(‖k‖+‖ℓ‖)³·‖ℓ‖` and bounded-support
  specialisation `≤ 48·D³·‖ℓ‖`.
- §10.64–§10.67 Gronwall infrastructure: scalar Gronwall wrapping mathlib;
  Ḣ²→ℓ∞ coefficient extraction;  `GalerkinEnergyGronwall` predicate;
  `BKMCriterionS2.of_galerkinEnergyGronwall`.
- §10.68–§10.69 finite-sum energy bridge `trigPolyEnergyHs2` and
  `HasDerivAt` formula for the Galerkin-trajectory composition.
- §10.70–§10.72 `pairIdx S`, `advectionSwap` involution,
  `IsFourierDivFree`, `IsRealFourier` with Riesz instances.
- §10.73–§10.74 **advection cancellation theorem**
  `advectionSum_re_eq_zero` via `Finset.sum_nbij'` reindex and kernel
  identity `F(τp) + star(F p) = 0`.
- §10.75 `commutatorSummand` pointwise bound
  `≤ 6·D⁵·(Σⱼ‖u_j ℓ‖)·‖c k‖·‖c (k+ℓ)‖` on bounded support.
- §10.76–§10.78 capstone
  `BKMCriterionS2.of_galerkin_energy_inequality` from
  `|d/dt E| ≤ K·E`.

Archive: [10.5281/zenodo.19653165](https://doi.org/10.5281/zenodo.19653165).

## v0.4.5 – v0.4.7 — 2026-04-19

Radial-shell, collinear and axis-aligned stationary families; Galerkin ODE
scaffold; unconditional discharge of both Theorem 3 analytic axioms on the
finite-support, uniform-coefficient class.

- §10.32 pair-sum cross div-free lemma (`|ℓ| = |k|` ⇒ pair-sum = 0).
- §10.33–§10.34 `IsRadialShell`, `shellMode`, `shellVelocity`, flux = 0 via
  `Finset.sum_involution`; `SqgEvolutionAxioms_strong.shellMode_const`.
- §10.35 regularity capstone `sqg_regularity_shellMode_const`.
- §10.36–§10.48 Galerkin ODE scaffold (`galerkinRHS`,
  `galerkinVectorField`, continuity, `ContDiff ℝ ∞`, local Lipschitz via
  `ContDiffAt.exists_lipschitzOnWith`, Picard–Lindelöf wrapper,
  real-symmetric support predicates, `galerkinToLp`,
  `galerkinRHS_eq_neg_sqgNonlinearFlux` bridging ODE and PDE).
- §10.40, §10.43, §10.49–§10.52 collinear and axis-aligned stationary
  classes unified under `IsStationaryShape`; user-facing
  `sqg_regularity_via_stationaryShape`; auto-Picard
  `galerkin_local_exists`.
- §10.56 **`MaterialMaxPrinciple.of_finite_support_uniform`** — MMP
  discharged unconditionally.
- §10.57 **`BKMCriterionS2.of_finite_support_uniform`** — BKM discharged
  unconditionally on the same class.
- §10.58 capstones `sqg_regularity_of_finite_support_uniform` and
  `SqgEvolutionAxioms_strong.of_finite_support_weak_solution`.

## v0.4.3 – v0.4.4 — 2026-04-18

First non-zero concrete discharge of the conditional Theorem 3 chain; first
multi-mode stationary SQG witness.

- §10.22 `SqgFourierContinuous.toCollarLhsCondition` — full LHS collar FTC
  closing Phase 2.3.b of the bump-to-indicator bridge.
- §10.23 `sqg_regularity_const` — for any `θ₀` with Ḣ¹ summability, the
  constant-in-time evolution paired with zero velocity satisfies uniform
  Ḣˢ bounds on `[0, 2]`, unconditionally.
- §10.24–§10.27 `sqg_regularity_scaled` (first time-varying discharge with
  `θ(τ) = c(τ) · θ₀`, `‖c(τ)‖ ≤ 1`); general trigonometric-polynomial
  initial data; first single-mode stationary witness.
- §10.28–§10.31 odd-symmetry helpers; antipodal-pair construction with
  Riesz-transform velocity; `antipodal_inner_sum_zero`;
  `SqgEvolutionAxioms_strong.antipodalMode_const` — first multi-mode
  discharge via `of_IsSqgWeakSolution_via_MMP`.

## v0.4.2 — 2026-04-18

Duhamel keystone closed end-to-end. Only remaining SQG-specific open
content is the weak-form PDE integral identity.

- §10.12 concrete `sqgNonlinearFlux` as a sum of `fourierConvolution`s;
  uniform bound `sqgNonlinearFlux_bounded`;
  `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity`.
- §10.13 ℓ²-control helpers (velocity + gradient summability, tsum bounds
  from Parseval, MMP, and `IsSqgVelocityComponent`).
- §10.14 `theta_fourier_tsum_conserved` — full Fourier-tsum L²
  conservation via Parseval split at the zero mode;
  `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP`, fully
  internalized.

Archive: [10.5281/zenodo.19637844](https://doi.org/10.5281/zenodo.19637844).

## v0.4.0 – v0.4.1 — 2026-04-17

Last `True` placeholders eliminated from `SqgEvolutionAxioms`; s=2 integer
BKM bootstrap; Fourier convolution scaffolding and Bochner wiring.

- §10.8 `BKMCriterionS2`; `sqg_regularity_via_s2_bootstrap` giving
  uniform Ḣˢ bounds for every `s ∈ [0, 2]` from MMP + `BKMCriterionS2`.
- §10.9 `fourierConvolution` and `convolution_bounded_by_product`
  (uniform Young + triangle `‖(f * g)(m)‖ ≤ (‖f‖²_{ℓ²} + ‖g‖²_{ℓ²})/2`).
- §10.10 `ModeLipschitz` predicate; `SqgEvolutionAxioms_strong`.
- §10.11 `DuhamelFlux`; `DuhamelFlux.modeLipschitz` via
  `MeasureTheory.norm_setIntegral_le_of_norm_le_const`;
  `SqgEvolutionAxioms.strengthen_of_duhamel`.

Archives:
- v0.4.0: [10.5281/zenodo.19637609](https://doi.org/10.5281/zenodo.19637609)
- v0.4.1: [10.5281/zenodo.19637612](https://doi.org/10.5281/zenodo.19637612)

## v0.3.0 — earlier

Conditional Theorem 3 roadmap with axiomatic hypotheses.
`FracSobolevCalculus` discharged unconditionally. BKM scope reduced to
`s > 1` via interpolation; MMP alone handles `s ∈ [0, 1]`.

- §10 `sqg_regularity_conditional`, `SqgSolution.regularity_conditional`.
- §10.2 trivial-case discharges for the zero solution.
- §10.3 `SqgWellPosedness`; `sqg_regularity_for_smooth_data`.
- §10.5 `uniform_l2Bound_of_l2Conservation`.
- §10.6 `BKMCriterionHighFreq`; `sqg_regularity_via_interpolation`.
- §10.7 MMP internalises Ḣ¹ summability;
  `MaterialMaxPrinciple.uniform_hs_intermediate`.

Archive: [10.5281/zenodo.19584185](https://doi.org/10.5281/zenodo.19584185).

## v0.2.0 — earlier

Supporting Riesz / Sobolev infrastructure on `𝕋ᵈ`: Leray–Helmholtz
projector, fractional derivative symbol, Ḣˢ seminorm, tight mode-level
identities for strain, gradient, vorticity, α-fractional heat semigroup,
classical heat semigroup with parabolic smoothing, heat- and
fractional-heat-smoothed SQG suites at mode and integrated level.

Archive: [10.5281/zenodo.19583417](https://doi.org/10.5281/zenodo.19583417).

## v0.1.0 — earlier

Initial release: Theorem 1 in polar and Cartesian forms; Theorem 2 at
the Fourier-symbol level.

Archive: [10.5281/zenodo.19583257](https://doi.org/10.5281/zenodo.19583257).
