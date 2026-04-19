# SQG Identity — Lean 4 Formalization (Work in Progress)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)

Concept DOI (always-latest): [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) · v0.4.9 (current): [10.5281/zenodo.19654673](https://doi.org/10.5281/zenodo.19654673) · v0.4.8: [10.5281/zenodo.19653165](https://doi.org/10.5281/zenodo.19653165) · v0.4.7 · v0.4.6 · v0.4.5 · v0.4.4 · v0.4.3 · v0.4.2: [10.5281/zenodo.19637844](https://doi.org/10.5281/zenodo.19637844) · v0.4.1: [10.5281/zenodo.19637612](https://doi.org/10.5281/zenodo.19637612) · v0.4.0: [10.5281/zenodo.19637609](https://doi.org/10.5281/zenodo.19637609) · v0.3.0: [10.5281/zenodo.19584185](https://doi.org/10.5281/zenodo.19584185) · v0.2.0: [10.5281/zenodo.19583417](https://doi.org/10.5281/zenodo.19583417) · v0.1.0: [10.5281/zenodo.19583257](https://doi.org/10.5281/zenodo.19583257)

Lean 4 + mathlib formalization of Fourier-space identities for the
Surface Quasi-Geostrophic (SQG) equation, working towards a machine-checked
regularity proof. Covers the shear-vorticity identity (Theorem 1 of
paper D14), the selection-rule bound (Theorem 2), supporting
Riesz/Sobolev infrastructure, and — as of §10 — a **conditional
Theorem 3 roadmap** with explicit axiomatic hypotheses that pin down
*exactly* which analytic facts the regularity argument borrows from
outside the algebraic layer.

Current state: **14267 lines, zero errors, zero `sorry`, zero new axioms**. §10.8
replaced the last `True` placeholders in `SqgEvolutionAxioms` and
introduced the **s=2 integer-order BKM bootstrap**. §10.9–§10.11
added the Fourier convolution scaffolding, mode-Lipschitz keystone,
and SQG-specific Bochner wiring `DuhamelFlux ⇒ ModeLipschitz`.
**§10.12–§10.14** completed the Duhamel keystone:
`sqgNonlinearFlux` realizes `(u·∇θ)̂(m)` concretely; full Fourier-tsum
L² conservation; `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP`
consuming only axioms + MMP + PDE integral identity.
**§10.15–§10.22 (v0.4.3)** close the bump-to-indicator bridge:
`IsSqgWeakSolution` ⇒ TimeTest form; `sqgConcreteMollifier` built from
`Real.smoothTransition`; DCT-based RHS limit; full LHS collar FTC
(monotonicity, derivative sign/vanishing, FTC mass, integral split,
collar squeeze); and **`SqgFourierContinuous.toCollarLhsCondition`** —
Phase 2.3.b closed.
**§10.23** delivers the first **non-zero concrete
discharge** of the conditional Theorem 3 chain: for any
`θ₀ ∈ Lp ℂ 2 𝕋²` with Ḣ¹ summability, the constant-in-time evolution
`θ(τ) = θ₀` paired with zero velocity satisfies uniform Ḣˢ bounds for
every `s ∈ [0, 2]` — **unconditionally**, via `sqg_regularity_const`.

**§10.24–§10.31 (v0.4.2–v0.4.4)** build out scaled and multi-mode
stationary witnesses: `sqg_regularity_scaled`, `singleMode_const`,
and the first **multi-mode** named discharge
`SqgEvolutionAxioms_strong.antipodalMode_const` on the antipodal pair
`{m₀, −m₀}` — stationary via four div-free identities plus a unified
`antipodal_inner_sum_zero` cancellation factoring through
`IsSqgVelocityComponent`.

**§10.32–§10.48 (v0.4.5)** ship the radial-shell +
collinear stationary families and the Galerkin ODE scaffold:
§10.32 pair-sum cross div-free lemma (`|ℓ| = |k|` ⇒ pair-sum = 0);
§10.33–§10.34 `IsRadialShell` + `shellMode` + `SqgEvolutionAxioms_strong.shellMode_const`
(flux = 0 via `Finset.sum_involution`); §10.35 regularity capstone;
§10.36–§10.38 Galerkin ODE scaffold (`galerkinRHS`, `galerkinVectorField`,
constant-solution witness); §10.39 continuity; §10.40 collinear-support
class via per-pair `C = 0`; §10.41 `ContDiff ℝ ∞` on the finite-dim
Pi space; §10.42 local Lipschitz; §10.43 unified `IsStationaryShape`
predicate; §10.44 Picard-Lindelöf wrapper producing local ODE
solutions from pre-chosen Lipschitz/bound/time constants; §10.45
radial-shell Picard solution; §10.46 real-symmetric predicates
(`IsSymmetricSupport`, `IsRealCoeff`); §10.47 `galerkinToLp` (Pi state
lifts to `Lp` via `trigPoly`); §10.48 `galerkinRHS_eq_neg_sqgNonlinearFlux`
bridging the ODE framework to the PDE weak-solution framework.

**§10.49–§10.56 (v0.4.6)** unify the stationary theory
and close out the analytic-hypothesis discharge for finite-support
time-varying θ: §10.49 `SqgEvolutionAxioms_strong.shellMode_const_of_stationaryShape`
— single named discharge subsuming both §10.34 (radial) and §10.40
(collinear); §10.50 `sqg_regularity_via_stationaryShape` consumer-
facing regularity capstone; §10.51 **`galerkin_local_exists`** —
auto-Picard that derives all constants (`a, L, K, ε`) from ContDiff +
compactness, so any initial `c₀` gets a local Galerkin ODE solution
with no hand-chosen constants; §10.52 axis-aligned stationary classes
`IsXAxisShell` / `IsYAxisShell` (corollaries of collinear);
**§10.56 `MaterialMaxPrinciple.of_finite_support_uniform`** — MMP
discharged unconditionally for any time-varying θ with finite Fourier
support and uniform coefficient bound `M`, yielding
`hsSeminormSq 1 (θ t) ≤ M² · ∑_{n∈S} σ₁(n)²`.

**§10.55, §10.57–§10.60 (v0.4.7 — most recent)** close the analytic-
hypothesis chain and bundle the consumer-facing capstones:
§10.55 `galerkin_mode_FTC` — mode-wise FTC for Galerkin trajectories
via `hasDerivAt_pi` + `intervalIntegral.integral_eq_sub_of_hasDerivAt`;
§10.57 **`BKMCriterionS2.of_finite_support_uniform`** — mirror of
§10.56 for the BKM axiom, discharged on the same class;
§10.58 **two capstones**: `sqg_regularity_of_finite_support_uniform`
— unconditional Ḣˢ bound on `[0, 2]` (no axioms); and
`SqgEvolutionAxioms_strong.of_finite_support_weak_solution` — full
strong-axiom discharge for any finite-support uniform-bound weak
solution, via §10.56 MMP + the internal BKM wiring of
`of_IsSqgWeakSolution_via_MMP`;
§10.59 demo reproving `shellMode_const` via the §10.58 route;
§10.60 L² conservation on radial-shell Galerkin ODE (trivial case —
vector field ≡ 0 ⇒ α constant ⇒ L² constant).

**Milestone.** Both conditional-Theorem-3 analytic axioms
(`MaterialMaxPrinciple` and `BKMCriterionS2`) now have **unconditional**
discharges for the finite-Fourier-support + uniform-coefficient-bound
class. The conditional Theorem 3 chain becomes unconditional on this
entire class.

**§10.61–§10.78 (v0.4.8 — most recent)** ship the **ambitious BKM
commutator chain**: a *derived* `BKMCriterionS2` discharge via
energy-Gronwall hypothesis, parallel to §10.57's trivial-M route but
grounded in the classical Kato-Ponce + advection-cancellation argument.

- **§10.61–§10.63** foundations: `comSymb k ℓ := ‖k+ℓ‖⁴ − ‖k‖⁴`
  (s=2 commutator symbol); triangle + Cauchy-Schwarz on the integer
  lattice via `Finset.sum_mul_sq_le_sq_mul_sq`; Kato-Ponce symbol bound
  `|comSymb k ℓ| ≤ 6·(‖k‖+‖ℓ‖)³·‖ℓ‖`; bounded-support specialization
  `≤ 48·D³·‖ℓ‖`; CS-in-sqrt helper.

- **§10.64–§10.67** Gronwall infrastructure: `scalar_gronwall_exp` wrapping
  mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le`; `Ḣ²→ℓ∞`
  coefficient extraction `fourier_coeff_bound_from_hs2` via integer-lattice
  `(fracDerivSymbol 2 n)² ≥ 1`; `GalerkinEnergyGronwall` predicate;
  **`BKMCriterionS2.of_galerkinEnergyGronwall`** capstone composing with §10.57.

- **§10.68–§10.69** energy-as-finite-sum setup: `trigPolyEnergyHs2 S c :=
  Σ m:↥S, (fracDerivSymbol 2 m.val)²·‖c m‖²` as a pointwise-differentiable
  form of Ḣ², with bridge to `hsSeminormSq 2 (galerkinToLp S c)` via
  `tsum_eq_sum` + `Finset.sum_attach`; `HasDerivAt`-formula for the
  Galerkin-trajectory composition via `HasDerivAt.norm_sq` + `hasDerivAt_pi`.

- **§10.70–§10.72** advection-cancellation scaffolding: `pairIdx S`
  (pair index `(k, ℓ) ∈ S × S` with `k+ℓ ∈ S`) + `advectionSwap (k,ℓ) :=
  (k+ℓ, -ℓ)` involution (self-map under `IsSymmetricSupport S`);
  `IsFourierDivFree u := ∀ ℓ, Σⱼ (ℓⱼ : ℂ)·u ⱼ ℓ = 0` + Riesz instance;
  `IsRealFourier u := ∀ (j, ℓ), u_j(−ℓ) = star (u_j ℓ)` + Riesz instance
  for real-coefficient trig-poly on symmetric support. `star_rieszSymbol`
  proved via `Complex.ext` on real-part.

- **§10.73–§10.74** **advection cancellation theorem.** The kernel identity
  `advectionSummand u c (advectionSwap p) + star (advectionSummand u c p) = 0`
  under div-free + reality (via `advection_jsum_swap_eq_star`: V = star U
  through `hReal` + telescoping `(k+ℓ)ⱼ − kⱼ = ℓⱼ` + div-free), then
  applied via `Finset.sum_nbij'` reindex + `star_sum` to yield
  `advectionSum_add_star_eq_zero`, hence `advectionSum_re_eq_zero`:
  **`Re(Σ_{pairIdx S} advectionSummand u c) = 0`**.

- **§10.75** commutator pair-summand + pointwise bound. `commutatorSummand u c p =
  I·(‖k+ℓ‖²−‖k‖²)·‖k+ℓ‖²·(Σⱼ kⱼ·u_j ℓ)·c(k)·star(c(k+ℓ))` (residual factor
  after advection split); proved
  `‖commutatorSummand u c p‖ ≤ 6·D⁵·(Σⱼ‖u ⱼ ℓ‖)·‖c k‖·‖c (k+ℓ)‖` on
  bounded support via §10.62's `abs_latticeNorm_add_sq_sub_sq_le` +
  componentwise bound `|kⱼ| ≤ ‖k‖` + explicit calc chain.

- **§10.76–§10.78** final capstone chain: `trigPolyEnergy_exp_bound_of_deriv_le`
  (apply §10.64 scalar Gronwall to trig-poly energy); `galerkinEnergyGronwall_of_deriv_le`
  (promote to `GalerkinEnergyGronwall` via §10.68 bridge); and **top-level
  `BKMCriterionS2.of_galerkin_energy_inequality`** — given a Galerkin
  trajectory with energy inequality `|d/dt E| ≤ K·|E|`, zero-mode bound,
  finite support, and extension convention, produces `BKMCriterionS2`
  via §10.77 → §10.67 → §10.57. This is the **derived BKM discharge**
  route, closing "ambitious #3" from the v0.4.7 handoff.

**§10.79–§10.87 (v0.4.9 — most recent)** close the **last mile** —
deriving the energy-inequality hypothesis of §10.78 directly from Galerkin
dynamics, producing an unconditional `BKMCriterionS2` from any Galerkin
trajectory with uniform L^∞ coefficient bound:

- **§10.79–§10.81** algebraic kernel: combined `advectionSummand +
  commutatorSummand` factorization (`ring`-closed via §10.62 split);
  pair-Finset reindexing `(m, ℓ) ↔ (m-ℓ, ℓ)` between
  `{(m, ℓ) ∈ S × S : m - ℓ ∈ S}` and `pairIdx S` via `Finset.sum_nbij'`;
  per-pair algebraic identity bridging the energy summand at `(p.1+p.2, p.2)`
  to `advectionSummand u c̃ + commutatorSummand u c̃` with Riesz velocity
  `u_j ℓ := sqgVS j ℓ · c̃ ℓ`, closed via `Finset.mul_sum` + `push_cast`
  + `ring`.

- **§10.82** mathlib bridge: `@inner ℝ ℂ _ z w = (star z * w).re`
  via `Complex.inner` + `mul_comm` (note arg order — first arg is the
  conjugated one).

- **§10.83** **pair-sum form of the energy derivative**: an 8-step proof
  composing §10.69 (`HasDerivAt` formula), §10.48 (galerkinRHS bridge),
  §10.80 (reindexing), §10.81 (per-pair factorization),
  `Complex.re_ofReal_mul`, `Complex.re_sum`, and `Finset.sum_attach`
  (after `Finset.univ_eq_attach`) to produce
  `Σ m, (fracDerivSymbol 2 m.val)² · 2 · ⟪c m, GVF S c m⟫_ℝ
   = -2 · Re(Σ_{p ∈ pairIdx S} (advection u c̃ p + commutator u c̃ p))`.

- **§10.84** advection cancellation in the energy derivative: combine
  §10.83 with §10.74 to drop the advection sum, leaving
  `-2 · Re(Σ commutator u c̃ p)`.

- **§10.85** per-mode and per-pair L² bounds from Ḣ² energy:
  `‖c̃ m‖² ≤ trigPolyEnergyHs2 S c` for `m ∈ S` (uses
  `latticeNorm_ge_one_of_ne_zero` + `pow_le_pow_left₀`);
  `‖c̃ a‖ · ‖c̃ b‖ ≤ E` via AM-GM.

- **§10.86** **energy inequality**:
  `|Σ m, (fracDerivSymbol 2 m.val)² · 2 · ⟪c m, GVF S c m⟫_ℝ|
   ≤ 24·D⁵·M·|S|² · trigPolyEnergyHs2 S c`
  under `0 ∉ S`, `IsSymmetricSupport S`, `IsRealCoeff`, support diameter
  `D`, and uniform L^∞ bound `M`. Combines §10.84 + §10.75 with
  `gcongr`-driven multiplicative monotonicity. Discharges the
  `hE_bound` hypothesis of §10.78 with `K = 24·D⁵·M·|S|²`.

- **§10.87** top-level capstone: `BKMCriterionS2.of_galerkin_dynamics_with_L_inf_bound`
  composing §10.69 (HasDerivAt → continuity, HasDerivWithinAt) with §10.86
  (energy inequality) and §10.78 (BKMCriterionS2 from energy inequality).
  Hypotheses: Galerkin dynamics `hα`, `IsRealCoeff` per time, support diameter,
  uniform L^∞ bound, zero-mode bound, extension convention. Conclusion:
  `BKMCriterionS2 (fun τ => galerkinToLp S (α τ))` with no energy-inequality
  black box.

**Final milestone (v0.4.9).** The §10.61-§10.78 chain is now
unconditional: from any Galerkin trajectory with finite Fourier support
(`0 ∉ S`), real-coefficient symmetry, and uniform L^∞ bound on
coefficients, `BKMCriterionS2` follows automatically. The energy
inequality is no longer a black-box hypothesis but is derived end-to-end
from the dynamics via the Kato-Ponce + advection-cancellation + per-pair
L² bound machinery. Closes "ambitious #4" from the v0.4.7 handoff.

## What's proven

**Theorems 1 and 2 of D14** are fully machine-verified (zero `sorry`):

- Shear-vorticity identity `Ŝ_nt − ω̂/2 = |k|·sin²(α−β)·θ̂` in polar
  and Cartesian forms, with half-angle, aligned, and perpendicular corollaries
- Selection-rule bound `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` with equality-case
  characterization
- ℓ² integrated form via `SqgFourierData` bundle, Parseval bridge to
  `L²(𝕋ᵈ)`, and Ḣ¹ seminorm restatement

**Riesz-transform and Sobolev infrastructure** on `𝕋ᵈ` (also zero `sorry`):

- Riesz symbol `m_j(n) = −i·n_j/‖n‖`, pointwise bound, Pythagorean
  identity, complex identity `Σ_j R_j² = −Id`
- SQG velocity isometry `‖u₁‖² + ‖u₂‖² = ‖θ‖²`
- Leray–Helmholtz projector: definition, trace, self-adjoint, idempotent,
  kills longitudinal, preserves transverse
- Fractional-derivative symbol, Ḣˢ seminorm, Laplacian and inverse-Laplacian
  symbols, Biot-Savart factorisation
- L² contractivity of bounded multipliers, Riesz L² contractivity
- Ḣˢ-level bounds: strain/velocity-gradient ≤ Ḣˢ⁺¹(θ), velocity ≤ Ḣˢ(θ)
- Sobolev interpolation (mode-level), Bernstein frequency estimates
- Hessian symbol, tangential-Hessian vanishing, third-order symbols
- Strain-rotation decomposition, vorticity symbol = −|k|
- SQG strain norm bound, divergence-free, explicit strain formulas
- **Tight mode-level identities** (no inequality):
  - `|S₀₀|² + |S₀₁|² = ‖n‖²/4` (strain eigenvalue tight)
  - `Σ ‖S_ij‖² = ‖n‖²/2` (strain Frobenius tight)
  - `Σ ‖∂̂_i u_j‖² = ‖n‖²` (gradient Frobenius tight)
  - `‖ω̂‖ = ‖n‖` (vorticity norm)
  - `‖∂u‖²_F = ‖S‖²_F + ‖ω‖²/2` (strain-vorticity partition)
- Mode-level Ḣˢ tight identities for strain, gradient, vorticity
- Riesz Ḣˢ contractivity, derivative Ḣˢ mode bound
- Vorticity L² = θ Ḣ¹ (Parseval integrated form)
- **α-Fractional heat semigroup** (unifies heat + Poisson + fractional SQG):
  - `fracHeatSymbol α t n = exp(-t·‖n‖^{2α})` for `0 < α`
  - Specializations: α=1 → heat, α=1/2 → Poisson
  - `fracHeatSymbol_rpow_eq`: time-rescaling identity
  - General smoothing: `‖n‖^k·fracHeat ≤ (k/(2α))^{k/(2α)}·exp(-k/(2α))/t^{k/(2α)}`
  - Mode + integrated L² and Ḣᵏ bounds
  - Mode + integrated L² / Ḣˢ contractivity
  - **α-fracHeat-smoothed SQG suite** (mode + integrated):
    - Vorticity: `‖fracHeat·ω̂·c‖² ≤ (1/α)^{1/α}·exp(-1/α)/t^{1/α}·‖c‖²`
    - Gradient: same bound per component
    - Strain: same bound per component
    - Velocity Ḣˢ: `‖fracHeat·u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}` (no gain)
- **Heat semigroup & parabolic smoothing**:
  - `heatSymbol`, positivity, boundedness, additivity, Ḣˢ contractivity
  - `x · exp(-x) ≤ exp(-1)` (tangent-line inequality)
  - `‖n‖² · exp(-t‖n‖²) ≤ exp(-1)/t` (k=1 gradient smoothing)
  - `‖n‖⁴ · exp(-t‖n‖²) ≤ 4·exp(-2)/t²` (k=2 Hessian smoothing)
  - General `k : ℕ`: `‖n‖^{2k} · exp(-t‖n‖²) ≤ k^k·exp(-k)/t^k`
    (max of `y^k·exp(-y)` at `y = k`)
  - General real `k > 0`: same bound using `Real.rpow`
  - Mode-level and integrated Ḣᵏ parabolic smoothing for all real k > 0
  - L² and Ḣˢ contractivity of heat (integrated form)
  - Heat-smoothed SQG quantities (mode-level and integrated):
    - Vorticity: `‖heat·ω̂·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Gradient: `‖heat·∂̂u·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Strain (generic): `‖heat·Ŝ·c‖² ≤ exp(-1)/t · ‖c‖²` (L²)
    - Strain (tight): `‖heat·Ŝ_ij·c‖² ≤ exp(-1)/(4t) · ‖c‖²` (4× sharper)
    - Ḣˢ-level bounds for all: vorticity/gradient/strain Ḣˢ ≤ θ Ḣˢ⁺¹
    - Tight Ḣˢ for S₀₀/S₀₁: `‖e^{tΔ}S_ij‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣ^{s+1}}/4`
    - Velocity: `‖e^{tΔ}u_j‖²_{Ḣˢ} ≤ ‖θ‖²_{Ḣˢ}` (both heat and Riesz contract)

## What's proven conditionally (Theorem 3 skeleton, §10)

The regularity result (Theorem 3) is **not unconditionally formalized**,
but `RieszTorus.lean` §10 now carries a *conditional* Theorem 3:
a machine-checked derivation that takes three analytic hypotheses
as input and concludes

    ∀ s ≥ 0, ∃ M, ∀ t ≥ 0, ‖θ(t)‖²_{Ḣˢ} ≤ M

— uniform bounds in every Sobolev space. Two of the three hypotheses
now carry real mathematical content (uniform Ḣ¹ bound; Ḣ¹→Ḣˢ
bootstrap); the third remains a structural placeholder.

See `sqg_regularity_conditional` in `RieszTorus.lean`. The hypothesis
structures (`MaterialMaxPrinciple`, `BKMCriterion`,
`FracSobolevCalculus`) explicitly pin down *which* analytic facts the
argument is borrowing from outside the algebraic layer.

A structured form `SqgSolution.regularity_conditional` (§10.1) wraps
the theorem around an `SqgSolution` record, which bundles the
time-evolution `θ`, a smooth-initial-data predicate (`θ 0` has finite
Ḣˢ seminorm for some `s > 2`), and a placeholder `solvesSqgEvolution`
field for the SQG PDE itself. The `smoothInitialData` field uses
`Summable` on the Ḣˢ-weighted Fourier series — the honest well-posedness
condition, not a vacuous `≤ M` bound.

**§10.2 Trivial-case discharges:**
`MaterialMaxPrinciple.of_identically_zero` and
`BKMCriterion.of_identically_zero` prove both refined hypotheses
unconditionally for the stationary zero solution `θ ≡ 0`. These are
supported by a new utility lemma `hsSeminormSq_of_zero` (the Ḣˢ
seminorm of `0` vanishes). Not mathematically deep, but they
demonstrate the hypotheses can be discharged to real proofs in at
least one case, not merely axiomatized.

**§10.3 Well-posedness + smooth-data form:**
`SqgWellPosedness` (hypothesis structure) asserts existence of a
matching `SqgSolution` for any smooth initial datum — the standard
SQG local well-posedness statement in Ḣˢ for `s > 2`. The
user-facing theorem `sqg_regularity_for_smooth_data` combines
well-posedness, the three analytic hypotheses (applied uniformly to
every solution), and smooth initial data `θ₀` to conclude: there
exists a solution with `θ 0 = θ₀` having uniform Sobolev bounds at
every order. This is the "input: smooth data → output: smooth
evolution" form of Theorem 3.

**`FracSobolevCalculus.ofMathlib`:** of the three analytic
hypotheses, `FracSobolevCalculus` has been refined to real
mode-level content (`hsMonotone`) and can be discharged
unconditionally — its proof is a direct re-export of existing
lemmas in this file. So in practice, only `MaterialMaxPrinciple`
and `BKMCriterion` need axiomatic treatment.

**§10.1 Material derivative scaffolding:**
First wedge into the long road of unconditionalising
`MaterialMaxPrinciple` and `BKMCriterion`. Adds:

- `sqgVelocitySymbol j n` — Fourier multiplier for the SQG velocity
  `u = (R₁θ, -R₀θ)`, component `j`.
- `sqgVelocitySymbol_norm_le_one`, `_sum_sq`, `_zero`,
  `_divergence_free` — mode-level velocity identities (all proved).
- `IsSqgVelocityComponent θ u_j j` — specificational predicate
  asserting that `u_j` is the `j`-th SQG velocity component of `θ`
  (mode-by-mode match via `sqgVelocitySymbol`).
- `IsSqgVelocityComponent.of_zero` — the zero function is a valid
  velocity component for the zero scalar.
- `SqgEvolutionAxioms θ` — Prop structure bundling expected
  consequences of the SQG PDE. As of §10.8, **all three fields carry
  real mathematical content** (no `True` placeholders):
  - `l2Conservation`: L² norm squared is conserved.
  - `meanConservation`: the spatial mean (zeroth Fourier coefficient)
    is preserved — zero-mode reading of `∂ₜθ + div(uθ) = 0`.
  - `velocityIsRieszTransform`: for each axis `j`, an `L²`-valued
    time-indexed velocity component exists satisfying
    `IsSqgVelocityComponent` mode-by-mode.
- `SqgEvolutionAxioms.of_identically_zero` — zero solution discharges
  all three fields (mean via `rfl` on rewritten zero, velocity via
  `IsSqgVelocityComponent.of_zero`).

**§10.2 `SqgSolution` strengthened:** `solvesSqgEvolution` upgraded
from `True` to `SqgEvolutionAxioms θ`. Every `SqgSolution` now
carries L² conservation as real content.

**§10.5 L² bound from conservation:**
`uniform_l2Bound_of_l2Conservation`: given `SqgEvolutionAxioms`,
produces a uniform-in-time `hsSeminormSq 0` bound with
`M = hsSeminormSq 0 (θ 0)`. This is the "s=0 degenerate subcase" of
`MaterialMaxPrinciple.hOnePropagation` — not enough to discharge
`hOnePropagation` itself (which is about Ḣ¹, not Ḣ⁰), but it
demonstrates the pattern: once PDE content is real, genuine
regularity output follows.

`SqgSolution.uniform_l2Bound` specializes this to the structured form.

**§10.6 Interpolation reduction of BKM scope:**
The axiomatic content of `BKMCriterion.hsPropagation` is overkill —
it bootstraps Ḣ¹ to Ḣˢ for *every* `s ≥ 0`, but **interpolation
handles `s ∈ [0, 1]` for free** via `hsSeminormSq_mono_of_le`
(integer lattice gives `‖n‖^{2s} ≤ ‖n‖²` for `s ≤ 1, n ≠ 0`). Adds:

- `BKMCriterionHighFreq` — refined BKM requiring bootstrap only
  for `s > 1`. Strictly weaker than the original.
- `BKMCriterion.toHighFreq` — every full BKM discharge promotes.
- `BKMCriterionHighFreq.of_identically_zero` — trivial case.
- `sqg_regularity_via_interpolation` — main reduction theorem.
  Takes MMP + Ḣ¹-summability + `BKMCriterionHighFreq` +
  `SqgEvolutionAxioms`, gives the full regularity conclusion
  `∀ s ≥ 0, ∃ M, ∀ t ≥ 0, hsSeminormSq s (θ t) ≤ M`.
  Proof: `s ∈ [0, 1]` branch uses `hsSeminormSq_mono_of_le`;
  `s > 1` branch uses the refined BKM.
- `SqgSolution.regularity_via_interpolation` — structured form.

**Net effect:** BKM's axiomatic footprint is reduced by the full
`s ∈ [0, 1]` range — a factor-of-2 shrink in the Sobolev scale BKM
is responsible for. Combined with `FracSobolevCalculus.ofMathlib`
(FSC discharged unconditionally) and `uniform_l2Bound_of_l2Conservation`
(L² handled by SqgEvolutionAxioms), the still-axiomatic content of
Theorem 3 is now cleanly scoped to: MMP's uniform Ḣ¹ bound, BKM's
high-frequency bootstrap (`s > 1` only), and Ḣ¹ summability.

**§10.7 MMP strengthening — intermediate-range self-sufficiency:**
Internalized Ḣ¹ summability into `MaterialMaxPrinciple` as a new
`hOneSummability` field. Was previously an external hypothesis to
`sqg_regularity_via_interpolation`. Consequence:

- MMP now has two real fields: `hOnePropagation` (uniform Ḣ¹ bound)
  and `hOneSummability` (summability at each time).
- `MaterialMaxPrinciple.uniform_hs_intermediate` — MMP alone discharges
  uniform Ḣˢ bounds for every `s ∈ [0, 1]`. No BKM, no L² conservation,
  no well-posedness needed. MMP is self-contained for this sub-range.
- `sqg_regularity_via_interpolation` signature simplified:
  `hSum` argument removed (now comes from `hMMP.hOneSummability`).
- `SqgSolution.regularity_via_interpolation` — same simplification.

This shows MMP carries enough content to handle a 50% sub-range of
Sobolev indices independently. The still-axiomatic `hOnePropagation`
field remains — actually discharging it requires the full D14 §9
material-derivative argument (~5k+ lines of missing infrastructure,
multi-month effort).

**§10.8 s=2 integer-order BKM bootstrap:**
The `BKMCriterionHighFreq` axiom of §10.6 covers the Ḣˢ bootstrap for
every `s > 1`, which on `𝕋²` brings in fractional-calculus machinery
(Kato–Ponce-type commutator estimates) not yet available. The
**integer case `s = 2` avoids fractional calculus entirely** — the
multiplier `|n|²` is polynomial and the commutator `[Δ, u·∇]` is a
classical differential operator. Adds:

- `BKMCriterionS2` — refined BKM hypothesis covering only
  `s ∈ (1, 2]`. Strictly weaker than `BKMCriterionHighFreq`.
- `BKMCriterionHighFreq.toS2` and `BKMCriterion.toS2` — every
  existing discharge auto-promotes.
- `BKMCriterionS2.of_identically_zero` — trivial case.
- `sqg_regularity_via_s2_bootstrap` — combined reduction: MMP +
  `BKMCriterionS2` gives uniform Ḣˢ bounds for **every `s ∈ [0, 2]`**.
  Proof: `s ∈ [0, 1]` via MMP + monotonicity; `s ∈ (1, 2]` via S2
  bootstrap.
- `SqgSolution.regularity_via_s2_bootstrap` — structured form.

Simultaneously: replaces the last two `True` placeholders in
`SqgEvolutionAxioms` with real content (`meanConservation`,
`velocityIsRieszTransform`), so every field of the structure now
carries a genuine PDE consequence.

**Net effect of §10.8:** conditional Theorem 3 on the range
`s ∈ [0, 2]` now holds from an axiomatic footprint that targets
only **integer-order** Sobolev regularity — no fractional calculus
prerequisites in mathlib required to discharge. The `s > 2` tail
remains an explicit open axiom.

**§10.9 Fourier convolution scaffolding:**
Both remaining open axioms (`MaterialMaxPrinciple.hOnePropagation`
for the uniform Ḣ¹ bound, `BKMCriterionS2.hsPropagationS2` for the
integer-order Ḣ² bootstrap) route through one shared analytic fact:
the per-mode Duhamel identity
`θ̂(m, t) − θ̂(m, 0) = − ∫₀ᵗ (u·∇θ)̂(m, τ) dτ`, where the nonlinear
flux is a Fourier-side **convolution** of coefficient sequences. This
section introduces the machinery:

- `fourierConvolution f g m = ∑ ℓ, f(ℓ) · g(m − ℓ)` on any additive
  commutative group `ι` with coefficients in `ℂ`.
- `fourierConvolution_zero_left` / `_zero_right` — discharge helpers.
- `subLeftEquiv m` — the reindexing involution `ℓ ↦ m − ℓ`.
- `tsum_sq_norm_shift_left` — shift invariance
  `∑ ℓ, ‖g(m − ℓ)‖² = ∑ ℓ, ‖g(ℓ)‖²`.
- `summable_sq_norm_shift_left` — summability companion.
- **`convolution_bounded_by_product`** — the uniform-in-`m` Young +
  triangle bound `‖(f * g)(m)‖ ≤ (‖f‖²_ℓ² + ‖g‖²_ℓ²)/2`. This is the
  single analytic fact the Bochner integrability step of a future
  Duhamel upgrade consumes.
- `SqgFourierData.fourierConvolution` — thin bundle wrapper so the
  operation is available on existing `SqgFourierData` bundles (reuses
  the §Fourier-mode-packaging machinery).
- `SqgFourierData.fourierConvolution_bounded_by_product` — bundle
  form of the Young bound.

**§10.10 Mode-Lipschitz keystone upgrade to `SqgEvolutionAxioms`:**
The differential form of the per-mode Duhamel identity — every
Fourier coefficient of `θ(t)` is Lipschitz-in-time with a
mode-specific constant:

`∀ m, ∃ C ≥ 0, ∀ s ≤ t, ‖θ̂(m, t) − θ̂(m, s)‖ ≤ (t − s) · C`.

Strictly stronger than `meanConservation` (which is the `C = 0` case
at `m = 0`) and strictly weaker than the full Bochner Duhamel
identity (which specifies `C` as a convolution flux). Adds:

- `ModeLipschitz θ` — the predicate.
- `ModeLipschitz.of_identically_zero` — trivial case (take `C = 0`).
- `SqgEvolutionAxioms_strong` — bundles the original
  `SqgEvolutionAxioms` with `ModeLipschitz`.
- `SqgEvolutionAxioms_strong.toWeak` — forgetful projection.
- `SqgEvolutionAxioms_strong.of_identically_zero` — zero discharge.

**Net effect of §10.9–§10.10:** the keystone analytic fact (bounded
per-mode flux via convolution) and its differential form (mode
Lipschitz-in-time) are now present in the development as
machine-checked scaffolding. A future `SqgEvolutionAxioms_strong`
discharge from a real solution — once Bochner integration of the
flux is wired through — would produce Ḣ¹ and Ḣ² bounds directly via
the existing §10.7 (MMP) and §10.8 (S2) reductions.

**§10.11 SQG-specific Bochner wiring (the connective tissue):**
`DuhamelFlux` and `DuhamelFlux.modeLipschitz` close the gap between
the §10.9 pointwise convolution bound and the §10.10 Lipschitz-in-time
target. Adds:

- `DuhamelFlux θ` — the predicate asserting `θ` has a per-mode
  Fourier-side Duhamel representation: there exists
  `F : (Fin 2 → ℤ) → ℝ → ℂ` with a uniform-in-`τ` bound `‖F(m, τ)‖
  ≤ K_m` and the integral identity
  `θ̂(m, t) − θ̂(m, s) = −∫_s^t F(m, τ) dτ` for every `0 ≤ s ≤ t`.
  This is exactly the shape a real SQG solution supplies, with `F`
  witnessed by `fourierConvolution`s of velocity/gradient sequences
  and `K_m` witnessed by `convolution_bounded_by_product`.
- `DuhamelFlux.of_identically_zero` — trivial case (zero flux).
- **`DuhamelFlux.modeLipschitz` — the Bochner wiring itself.**
  Proves `DuhamelFlux θ → ModeLipschitz θ` via
  `MeasureTheory.norm_setIntegral_le_of_norm_le_const` on `Set.Icc s t`
  under the `volume` measure, combined with `Real.volume_Icc` for
  the interval-length identity `volume.real (Icc s t) = t − s`.
  No intermediate integrability argument is needed — the mathlib
  lemma packages it.
- `SqgEvolutionAxioms.strengthen_of_duhamel` — one-liner
  `SqgEvolutionAxioms θ + DuhamelFlux θ → SqgEvolutionAxioms_strong θ`.
  The "promotion" theorem that turns a real-solution witness of
  Duhamel into the §10.10 keystone structure.

**Net effect of §10.11:** the SQG-specific connective tissue between
"pointwise convolution bound" and "Lipschitz-in-time" is now
machine-checked. The entire path
`convolution_bounded_by_product` → `DuhamelFlux` →
`ModeLipschitz` → `SqgEvolutionAxioms_strong` → (§10.7 / §10.8
reductions) → conditional Theorem 3 on `s ∈ [0, 2]` is formalized.

**§10.12 Concrete nonlinear-flux construction:** `sqgNonlinearFlux`
realizes `(u·∇θ)̂(m)` as a concrete Lean expression — a sum of
`fourierConvolution`s between velocity Fourier coefficients and
gradient Fourier coefficients `derivSymbol j · θ̂`. Adds:

- `sqgNonlinearFlux θ u m` — the concrete flux at a fixed mode.
- `sqgNonlinearFlux_bounded` — per-mode bound derived via
  `norm_sum_le` over `Fin 2` + `convolution_bounded_by_product` on
  each component.
- `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity` — the PDE-to-
  `SqgEvolutionAxioms_strong` promotion theorem: given
  `SqgEvolutionAxioms θ`, a velocity witness satisfying
  `IsSqgVelocityComponent`, uniform ℓ² bounds `Mu`/`Mg` on velocity
  and gradient Fourier coefficients, and **the integral identity**
  `θ̂(m, t) − θ̂(m, s) = − ∫_s^t sqgNonlinearFlux(θ τ)(u · τ)(m) dτ`,
  concludes `SqgEvolutionAxioms_strong θ` — the §10.10 keystone.

**Net effect of §10.12:** the flux and its bound are no longer part
of the open axiomatic footprint. The remaining SQG-specific input is
**a single PDE integral identity** — the mode-wise weak form of
`∂_t θ + u·∇θ = 0`. Combined with `MaterialMaxPrinciple.hOnePropagation`
and `BKMCriterionS2.hsPropagationS2`, these are the three remaining
open pieces for conditional Theorem 3 on `s ∈ [0, 2]`.

## What's not proven (yet)

Closing Theorem 3 unconditionally would require infrastructure that
doesn't exist in mathlib yet:

- **Material-derivative transport / maximum principle** — needed to
  prove `MaterialMaxPrinciple.hOnePropagation`. Mathlib has basic flow
  API but no ODE existence-uniqueness or DiPerna–Lions-level theory.
  §10.10's `ModeLipschitz` is the differential-form keystone this
  ultimately needs: once supplied from a real solution via Bochner
  integration of the §10.9 convolution flux, MMP's Ḣ¹ bound should
  follow from the existing reduction chain.
- **Integer-order energy estimate at `s = 2`** — needed to discharge
  `BKMCriterionS2.hsPropagationS2`. This is the target of §10.8's
  axiomatic scoping: it uses only classical (differential)
  commutators. With §10.9's `convolution_bounded_by_product` +
  §10.10's `ModeLipschitz` in place, the remaining step is the
  integration-in-time that turns the per-mode bounded flux into a
  uniform Ḣ² bound.
- **Fractional Sobolev bootstrap for `s > 2`** — the remaining open
  tail of conditional Theorem 3. Requires Kato–Ponce-type estimates
  on `𝕋²` (not in mathlib).
- **Mode-wise weak-form PDE identity** — the single remaining SQG-
  specific input. `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity`
  consumes `θ̂(m, t) − θ̂(m, s) = − ∫_s^t sqgNonlinearFlux(θ τ)(u · τ)(m) dτ`
  directly; providing this hypothesis for a real SQG solution
  discharges the keystone. The flux is now a concrete Lean
  expression, the bound is derived — only the PDE identity is
  axiomatic.
- **Uniform ℓ² bounds on velocity / gradient coefficients** — one-
  line consequences of Parseval + Riesz L²-isometry + MMP's Ḣ¹
  summability. §10.13 formalized these as named helpers
  (`velocity_fourier_summable`,
  `velocity_fourier_tsum_le_of_IsSqgVelocityComponent`,
  `gradient_fourier_summable_of_hOneSummability`,
  `gradient_fourier_tsum_le_hsSeminormSq_one`). **§10.14 (latest)
  closes the remaining `Mu` gap** via
  `theta_fourier_tsum_conserved` (full L² Fourier-tsum conservation,
  derived from `l2Conservation` + `meanConservation` via a Parseval
  split-at-zero-mode identity), and ships
  `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP` — the
  fully-internalized promotion theorem consuming only
  `SqgEvolutionAxioms + MaterialMaxPrinciple + velocity witness +
  the PDE integral identity`.

This repo is the Fourier-algebraic foundation plus a conditional
Theorem 3 skeleton with the keystone analytic scaffolding fully
machine-checked. **After §10.14** the headline reading is:

> "Give me a solution satisfying `SqgEvolutionAxioms`
> (mean + L² conservation + Riesz-transform velocity),
> `MaterialMaxPrinciple` (uniform Ḣ¹ bound), and the integral form
> of the SQG PDE against the concrete nonlinear flux
> `sqgNonlinearFlux` — and I will hand you uniform Ḣˢ bounds for
> every `s ∈ [0, 2]`."

The chain `sqgNonlinearFlux` → `convolution_bounded_by_product` →
`DuhamelFlux` → `ModeLipschitz` → `SqgEvolutionAxioms_strong` →
§10.7 / §10.8 reductions → conditional Theorem 3 on `s ∈ [0, 2]`
is closed end-to-end. The remaining open content collapses to:
(i) a single PDE integral identity at the Fourier level,
(ii) `MaterialMaxPrinciple.hOnePropagation`, and
(iii) `BKMCriterionS2.hsPropagationS2`. The `s > 2` fractional tail
remains open separately.

## The identity

For a Fourier mode with wavevector `k = |k|(cos α, sin α)` and front normal
`n̂ = (cos β, sin β)`:

    Ŝ_nt - ω̂/2 = |k| · sin²(α - β) · θ̂

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

First build is slow (~5–10 min on cold cache). Incremental builds are fast.

## Files

- `SqgIdentity/Basic.lean` — Theorems 1 and 2: polar and Cartesian forms,
  ℓ² lift, `SqgFourierData` bundle, Parseval bridge to `L²(𝕋ᵈ)`
- `SqgIdentity/RieszTorus.lean` — Riesz-transform symbols on `𝕋ᵈ`,
  Leray–Helmholtz projector, Sobolev scale, Laplacian/inverse-Laplacian,
  Biot-Savart, D14 Theorem 1 at Fourier-symbol level
- `SqgIdentity.lean` — root module (imports both)
- `lakefile.toml` — project config (mathlib dependency pinned to v4.29.0)
- `lean-toolchain` — Lean 4.29.0

## Credit

Mathematical theorem and Lean formalization: Bryan Sanchez.
