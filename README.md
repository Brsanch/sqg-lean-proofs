# SQG Identity — Lean 4 Formalization

[![CI](https://github.com/SolomonB14D3/sqg-lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/SolomonB14D3/sqg-lean-proofs/actions/workflows/lean_action_ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENSE)

A Lean 4 + mathlib formalization of Fourier-space identities for the inviscid
Surface Quasi-Geostrophic (SQG) equation on the 2-torus, together with a
conditional regularity roadmap.

Two algebraic theorems are fully machine-verified. A third (global regularity)
is supplied as a conditional result: a named, closed set of analytic
hypotheses, each of which is either discharged unconditionally in this
repository or scoped to a precise open problem.

The mathematical content is developed in the accompanying paper:

- **[`paper/sqg-identity.pdf`](./paper/sqg-identity.pdf)** — *The
  shear-vorticity identity and spectral concentration in SQG front dynamics.*
  ([markdown source](./paper/sqg-identity.md))

The formalization comprises over 20,000 lines of Lean 4 source, with
**zero `sorry` and no axioms beyond mathlib**.

## What is proven unconditionally

### Theorem 1 (Shear-Vorticity Identity)

For the SQG velocity field `u = ∇⊥(−Δ)^{−1/2} θ` on `𝕋²`, the Fourier
multiplier of `S_{nt} − ½ ω` is `|k|·sin²(φ_k)`:

```
F[S_nt − ½ω](k) = |k| · sin²(α − β) · θ̂(k)
```

where `k = |k|(cos α, sin α)` and the front normal is `n̂ = (cos β, sin β)`.
In particular, `S_nt − ½ω ≡ 0` for any one-dimensional front.

Lean statement: `sqg_shear_vorticity_identity` in
[`SqgIdentity/Basic.lean`](./SqgIdentity/Basic.lean).

### Theorem 2 (Selection-Rule Bound)

Pointwise mode-level bound with equality characterization, integrated form
via Parseval on `L²(𝕋ᵈ)` and restated as an `Ḣ¹`-seminorm inequality.
Lives in `SqgIdentity/Basic.lean` (mode-level) and
[`SqgIdentity/RieszTorus.lean`](./SqgIdentity/RieszTorus.lean) (integrated).

### Supporting infrastructure

`RieszTorus.lean` develops a self-contained Fourier-multiplier account of the
torus Riesz transforms, Leray–Helmholtz projector, fractional Sobolev scale,
Biot–Savart factorisation, tight mode-level strain/vorticity identities, the
α-fractional heat semigroup and its smoothing bounds, and a parallel suite
for the classical heat semigroup. All bounds are established without
general Calderón–Zygmund singular-integral theory: they follow from Parseval
plus explicit Fourier-symbol inequalities.

## What is proven conditionally (Theorem 3 roadmap)

`RieszTorus.lean` §10 formalizes a conditional form of the regularity
theorem: given a named set of analytic hypotheses, uniform `Ḣˢ` bounds
follow. The hypotheses are explicit Lean structures, so the argument's
axiomatic footprint is inspectable.

| Hypothesis | Scope | Status in this repository |
|---|---|---|
| `FracSobolevCalculus` | Mode-wise Ḣˢ monotonicity | Discharged unconditionally (`ofMathlib`) |
| `MaterialMaxPrinciple` | Uniform Ḣ¹ bound | Discharged on the finite-support, uniform-ℓ∞-coefficient class (§10.56) |
| `BKMCriterionS2` | Ḣˢ bootstrap for `s ∈ (1, 2]` | Discharged on the same class (§10.57) and derived from Galerkin dynamics via a Kato–Ponce + advection-cancellation + Gronwall chain (§10.87) |
| `SqgEvolutionAxioms` | Mean + L² conservation + Riesz-transform velocity | Real content, discharged for the zero solution and for every finite-support weak solution (§10.58) |

**Capstones.** On the finite-Fourier-support, real-coefficient, uniform-ℓ∞
class, regularity is unconditional:

- `sqg_regularity_of_finite_support_uniform` — uniform `Ḣˢ` bound on
  `[0, T]` for every `s ∈ [0, 2]` with zero axioms.
- `BKMCriterionS2.of_galerkin_dynamics_with_L_inf_bound` — BKM
  criterion produced directly from Galerkin dynamics and an
  L^∞ coefficient bound; the energy inequality is derived, not assumed.
- **`galerkin_time_global_unconditional_realSym` (§10.116).** Time-global
  existence of a Galerkin trajectory on every symmetric Fourier support
  `S`, from any real-symmetric initial coefficient vector `c₀` satisfying
  `∑_{m ∈ S} ‖c₀(m)‖² ≤ (R/2)²`. Delivers, at every `t ≥ 0`:
  `HasDerivWithinAt` of the ODE on `Ici 0`, ℓ²-sum conservation,
  propagation of real-symmetry, and the pi-norm bound `‖α t‖_∞ ≤ R/2`.
  No open hypotheses: the program discharges `hInv` (universal
  ball-invariance), `hRealSymPropagates`, and every auxiliary L^∞ slack
  bound internally, via a chain of local Picard-Lindelöf steps whose
  ball-containment guarantee is extracted from
  `ODE.FunSpace.compProj_mem_closedBall` and whose ℓ²-sum invariant
  is preserved exactly by §10.110.
- **`exists_sqgSolution_of_galerkin_realSym` (§10.117).** Packages the
  §10.116 time-global Galerkin trajectory as an honest `SqgSolution`
  on `L²(𝕋²)`. For every symmetric support `S ⊆ ℤ²` with `0 ∉ S`,
  every `R > 0`, and every real-symmetric `c₀ : ↥S → ℂ` with
  `∑ ‖c₀(m)‖² ≤ (R/2)²`, there exists an `SqgSolution` whose
  time-zero slice is `galerkinToLp S c₀`. The underlying trajectory
  is `t ↦ galerkinToLp S (α t)` with `α` the §10.116 capstone;
  `SqgEvolutionAxioms` is discharged directly from the ℓ²-sum
  invariant (§10.117.B) and `smoothInitialData` from
  `hsSeminormSq_summable_of_finite_support` at `s := 3`.
- **Sₙ ↗ truncation infrastructure (§10.118–§10.123).** The nested
  symmetric Fourier boxes `sqgBox n`, the Fourier-coefficient
  restriction `fourierRestrict n θ`, and the uniform estimates that
  any weak-`L²` compactness argument needs. Starts from arbitrary
  `L²(𝕋²)` initial data with real-symmetric Fourier coefficients,
  builds the Galerkin family on `sqgBox n` from §10.116 at every
  level with a radius uniform in `n` (via Parseval), and establishes:
  uniform L² bound
  `hsSeminormSq 0 (galerkinToLp (sqgBox n) (αₙ t)) ≤ ∫ ‖θ‖²`, and
  per-mode pointwise bound
  `‖galerkinExtend (sqgBox n) (αₙ t) m‖² ≤ ∫ ‖θ‖²`.
- **Conditional Galerkin-limit → `SqgSolution` chain (§10.125–§10.130).**
  Hypothesis-keyed closure of the passage-to-the-limit half.
  `IsGalerkinLimitData θ b` packages the invariants any classical
  extraction yields (zero-mode, initial-data match, ℓ²-summability,
  ℓ²-sum conservation, real-symmetry); `GalerkinLimitTrajectory θ b`
  packages the synthesized `L²` trajectory with a Fourier-coefficient
  match. `SqgEvolutionAxioms.of_galerkinLimit` derives
  `SqgEvolutionAxioms` and `exists_sqgSolution_of_galerkinLimit`
  completes the chain to `SqgSolution` given a `smoothInitialData`
  summability on the limit. Exercised unconditionally on the zero
  datum via `exists_sqgSolution_ofZero`.
- **Concrete finite-support closure (§10.131–§10.132).** Instantiates
  the packaged hypotheses directly from §10.116's time-global
  Galerkin trajectory, giving
  `exists_sqgSolution_via_galerkinLimit_of_finite_support` — a
  parallel construction of the §10.117 `SqgSolution` now routed
  through §10.125–§10.130. Demonstrates the conditional chain is
  instantiable on non-zero inputs.
- **`SqgEvolutionAxioms_strong` via Ici-0 Duhamel port (§10.133–§10.134).**
  Upgrades the §10.117 / §10.132 `SqgSolution` to the Duhamel-level
  strong axioms. Uses
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` to port
  the §10.91 → §10.92 → §10.94 chain to consume the
  `HasDerivWithinAt ... (Ici 0)` shape delivered by §10.116.
  Headline: `exists_sqgSolution_strong_of_galerkin_realSym`.
- **Time-test → Duhamel bridge (§10.135–§10.136).** Structural
  closure of the step-(B) gap from §10.16:
  `IsSqgWeakSolution.of_timeTest_of_bumpSeq` lifts
  `IsSqgWeakSolutionTimeTest` to `IsSqgWeakSolution` given a
  `HasBumpToIndicatorSequence` witness. Proof is a one-line
  `tendsto_nhds_unique` on the two pointwise-equal sequences of
  integrals.
  `SqgEvolutionAxioms_strong.of_timeTest_via_MMP` composes with
  §10.14's MMP-keyed promotion.
- **Route B conditional chain for the generic-`L²` limit (§10.137–§10.146).**
  Structural closure of item 1 (originally "generic-L² Galerkin →
  full-SQG extraction"). Packages a classical Aubin–Lions extraction
  + `H⁻²` time-derivative bound + `l2Conservation` of the limit into
  a single conditional existence theorem
  `exists_sqgSolution_via_RouteB` for the `SqgSolution`. Exercised
  unconditionally on the zero datum by
  `exists_sqgSolution_via_RouteB_zero` (§10.146) via
  `HasAubinLionsExtraction.ofZero`. Per-mode Fourier convergence
  under strong-`L²` (§10.141 `tendsto_mFourierCoeff_of_tendsto_L2Sq`)
  is the bridge from the `Lp` side to the Fourier-coefficient side
  used throughout.

## What is *not* proven

- Unconditional discharge of `MaterialMaxPrinciple.hOnePropagation` and
  `BKMCriterionS2.hsPropagationS2` outside the finite-support class.
- The fractional Sobolev bootstrap for `s > 2` (requires Kato–Ponce-type
  estimates on `𝕋²` that are not yet in mathlib).
- Construction of the `HasAubinLionsExtraction` witness
  (§10.139) for non-zero `L²` data from the uniform `L²` bound
  (§10.122) + an `H⁻²` time-derivative bound. Classical Aubin–Lions
  compactness; requires mathlib-scale weak-compactness / Fréchet–
  Kolmogorov infrastructure not yet in tree.
- The `l2Conservation` hypothesis fed to §10.144
  (`SqgEvolutionAxioms.of_aubinLions`) for non-zero data. Classical
  `Lp`-norm continuity under strong-`L²` convergence; requires
  `MeasureTheory.L2` inner-product bridge lemmas composed with
  §10.97's Galerkin `ℓ²`-conservation and §10.119's Parseval-on-
  truncation identity.
- A concrete `HasBumpToIndicatorSequence` witness (§10.135)
  constructed from mathlib's `ContDiffBump` infrastructure, to close
  item 6 analytically rather than only structurally.

## Canonical open-items tracker

See [`OPEN.md`](./OPEN.md) in the repo root for the authoritative
list of what remains, linked to tagged releases that closed each
item.

## Building

The project uses Lake and pins mathlib to v4.29.0.

```bash
# elan installs Lean 4 and Lake
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# Fetch pre-built mathlib olean cache, then build
lake exe cache get
lake build
```

A cold build with cache takes roughly five to ten minutes; incremental
builds are fast. Continuous integration runs the same command on every push.

## Layout

```
SqgIdentity.lean             -- root module
SqgIdentity/
  Basic.lean                 -- Theorems 1 and 2: polar + Cartesian forms,
                                ℓ² lift, SqgFourierData bundle, Parseval bridge
  RieszTorus.lean            -- Riesz-transform symbols on 𝕋ᵈ, Leray–Helmholtz,
                                fractional Sobolev scale, fractional + classical
                                heat semigroup suites, §10 Theorem 3 roadmap
paper/
  sqg-identity.md            -- paper source (markdown)
  sqg-identity.pdf           -- paper PDF
lakefile.toml                -- project config
lean-toolchain               -- Lean version
CHANGELOG.md                 -- release-by-release formalization history
```

## Citing

See [`CITATION.cff`](./CITATION.cff) for the canonical citation. The
concept DOI [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256)
always resolves to the latest archived release.

## License

MIT — see [`LICENSE`](./LICENSE).
