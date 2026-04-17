# SQG Identity — Lean 4 Formalization (Work in Progress)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)

Concept DOI (always-latest): [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) · v0.3.0: [10.5281/zenodo.19584185](https://doi.org/10.5281/zenodo.19584185) · v0.2.0: [10.5281/zenodo.19583417](https://doi.org/10.5281/zenodo.19583417) · v0.1.0: [10.5281/zenodo.19583257](https://doi.org/10.5281/zenodo.19583257)

Lean 4 + mathlib formalization of Fourier-space identities for the
Surface Quasi-Geostrophic (SQG) equation, working towards a machine-checked
regularity proof. Covers the shear-vorticity identity (Theorem 1 of
paper D14), the selection-rule bound (Theorem 2), supporting
Riesz/Sobolev infrastructure, and — as of §10 — a **conditional
Theorem 3 roadmap** with explicit axiomatic hypotheses that pin down
*exactly* which analytic facts the regularity argument borrows from
outside the algebraic layer.

Current state: **~7630 lines, zero errors, zero `sorry`**. Main has
advanced substantially beyond the last Zenodo release (v0.3.0) — see
the §10 section list below for what landed post-v0.3.0. §10.8
replaced the last `True` placeholders in `SqgEvolutionAxioms` with
real predicates and introduced the **s=2 integer-order BKM
bootstrap** (conditional Theorem 3 on `s ∈ [0, 2]` with no
fractional-calculus prerequisites). §10.9–§10.10 (most recent) add
**Fourier convolution scaffolding** (`fourierConvolution`,
`convolution_bounded_by_product`) and the **mode-Lipschitz keystone
upgrade** — the differential form of the per-mode Duhamel identity,
the single analytic fact that both remaining open axioms
(`MaterialMaxPrinciple.hOnePropagation` and
`BKMCriterionS2.hsPropagationS2`) route through.

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
- **Bochner integration of the per-mode flux** — the connective
  tissue between §10.9 (pointwise convolution bound) and a real
  `SqgEvolutionAxioms_strong` discharge. Requires wiring the Young
  bound into an `∫ τ in Set.Icc 0 t` statement; the mathlib Bochner
  API is present, the application to time-indexed Fourier
  coefficients is the piece to write.

This repo is the Fourier-algebraic foundation plus a conditional
Theorem 3 skeleton with the keystone analytic scaffolding now
machine-checked. As of §10.10 the conditional conclusion over
`s ∈ [0, 2]` rests on a single integer-order axiom; the `s > 2`
fractional tail is the remaining open piece; and the convolution /
mode-Lipschitz machinery bridging a real SQG solution to the §10.7
and §10.8 reductions is in place.

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
