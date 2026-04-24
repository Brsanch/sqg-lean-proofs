# SQG Identity — Lean 4 Formalization

[![CI](https://github.com/Brsanch/sqg-lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Brsanch/sqg-lean-proofs/actions/workflows/lean_action_ci.yml)
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

The formalization comprises over 25,850 lines of Lean 4 source in the
`RieszTorus` module and 2,490 lines in the `FourierBridge` module
(over 29,000 lines project-wide, wiring in the
[sqg-lean-proofs-fourier](https://github.com/Brsanch/sqg-lean-proofs-fourier)
companion package for classical Littlewood–Paley / Bony paraproduct /
quantitative uniform-in-N Kato–Ponce commutator content), with
**zero `sorry` and no axioms beyond mathlib**.

**Scope of Theorem 2 (SQG regularity, conditional).** Following paper
§9.6.3, Theorem 2 is stated as conditional on two explicit hypotheses,
(H-strain) and (H-bdry), labeled and documented inline in the Lean
source as `HasStrainLowerBound` and `HasBoundaryCurvatureBound`
(`SqgIdentity/RieszTorus.lean` §14). Paper §9.8 provides the
alternative single-hypothesis thermostat reformulation (H-α), labeled
`HasThermostatBound` in Lean. Neither hypothesis is derived from the
SQG dynamics alone in this repository — the §9 analytical argument
that `(H-strain)+(H-bdry) ⇒ uniform Ḣ¹ bound` is classical content
the paper develops and is taken as an auxiliary input in the
`MaterialMaxPrinciple.of_HstrainHbdry` / `.of_thermostat`
constructors. Everything downstream — BKM, interpolation, full-range
Theorem 2, Path A Ḣˢ bootstrap, Path B Galerkin chain — is machine
verified conditional on this analytical input.

**Mathlib-adjacent infrastructure discharged in this repository** (each
full proof, no axioms added):
- §13 lattice Sobolev per-mode Ḣˢ sup bound (`RieszTorus.lean`).
- §B.15 inverse Fourier transform `lpOfFourierCoeff` on `𝕋²` via
  `mFourierBasis` (`RieszTorus.lean`).
- §B.16–§B.19 Rellich–Kondrachov compact embedding `H¹(𝕋²) ⊂⊂ L²` in
  Fourier form: `countable_diagonal_bounded_sequences` +
  `fourier_rellich_kondrachov` (`FourierBridge.lean`), enabling
  Aubin–Lions extraction on the Galerkin sequence.

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

### Per-mode selection-rule bound (universal CZ form)

Pointwise mode-level bound `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` with equality
characterization, integrated via Parseval on `L²(𝕋ᵈ)` and restated as an
`Ḣ¹`-seminorm inequality. Lives in `SqgIdentity/Basic.lean` (mode-level,
`sqg_selection_rule_bound`) and
[`SqgIdentity/RieszTorus.lean`](./SqgIdentity/RieszTorus.lean) (integrated
via `sqg_selection_rule_Hs1`).

This is the universal Calderón–Zygmund bound. The accompanying paper's
Proposition 6.1 — the *pointwise parity-improved* bound
`|nSn_near(x*)| ≤ C·κ²·δ²·G` at the gradient maximum — is a **refinement
of** this Lean-verified bound using gradient-maximum parity cancellation;
its proof in `paper/sqg-identity.md` §6.1 operates at formal Taylor-expansion
+ parity-sector-cancellation level, is tighter than Córdoba's O(κA) form,
and is **not itself machine-verified**. Lean verifies the universal CZ
precursor that the paper's parity argument refines.

### Supporting infrastructure

`RieszTorus.lean` develops a self-contained Fourier-multiplier account of the
torus Riesz transforms, Leray–Helmholtz projector, fractional Sobolev scale,
Biot–Savart factorisation, tight mode-level strain/vorticity identities, the
α-fractional heat semigroup and its smoothing bounds, and a parallel suite
for the classical heat semigroup. All bounds are established without
general Calderón–Zygmund singular-integral theory: they follow from Parseval
plus explicit Fourier-symbol inequalities.

## What is proven conditionally (Theorem 2 roadmap)

`RieszTorus.lean` §10 formalizes a conditional form of the regularity
theorem: given a named set of analytic hypotheses, uniform `Ḣˢ` bounds
follow. The hypotheses are explicit Lean structures, so the argument's
axiomatic footprint is inspectable.

| Hypothesis | Scope | Status in this repository |
|---|---|---|
| `FracSobolevCalculus` | Mode-wise Ḣˢ monotonicity | Discharged unconditionally (`ofMathlib`) |
| `MaterialMaxPrinciple` | Uniform Ḣ¹ bound | Discharged on the finite-support, uniform-ℓ∞-coefficient class (§10.56); lifted to every strong-`L²` Galerkin limit with uniform `Ḣ¹` bound via §10.167 |
| `BKMCriterionS2` | Ḣˢ bootstrap for `s ∈ (1, 2]` | Discharged on the same class (§10.57) and derived from Galerkin dynamics via a Kato–Ponce + advection-cancellation + Gronwall chain (§10.87); lifted to every strong-`L²` Galerkin limit with uniform `Ḣˢ` bound via §10.168 |
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
- **`l2Conservation` internally discharged (§10.147, v0.4.38).**
  The `hL2` hypothesis fed to §10.144 is produced unconditionally
  from the other Route B data: strong-`L²` convergence of the
  Galerkin restrictions + §10.97 per-level energy conservation +
  §10.142 zero-mode preservation. The hypothesis-free capstone
  `exists_sqgSolution_via_RouteB_from_galerkin_energy` (§10.148)
  produces an `SqgSolution` from `HasAubinLionsExtraction` alone,
  without the `hL2` input.
- **Structural chain for `HasAubinLionsExtraction` existence (§10.149–§10.153).**
  Factors the remaining item 1 analytical gap into three
  precisely-typed Lean construction targets, replacing the
  earlier "mathlib-scale weak-compactness infrastructure" blocker
  with named theorem signatures. Predicates:
  `HasModeLipschitzFamily` (§10.149) → `HasPerModeLimit`
  (§10.150) → `HasFourierSynthesis` (§10.151) →
  `HasAubinLionsExtraction` (§10.139) via the one-line bridge
  `HasAubinLionsExtraction.ofPerModeLimit` (§10.151).
  `HasModeLipschitzFamily.ofSqgGalerkinBounds` (§10.152)
  discharges the sup-over-time mode bound concretely from §10.123
  and takes the per-mode Lipschitz constant `L m` as input; the
  per-mode `H⁻²`-energy primitive `galerkinRHS_mode_bound_of_HsNeg2Bound_ne_zero`
  (§10.153.A) and the mean-value-theorem Lipschitz bound
  `galerkinExtend_mode_lipschitz_of_ODE_bound` (§10.153.B) supply
  the analytic inputs needed to close `L m` in a future session.
  Capstone `exists_sqgSolution_via_RouteB_from_perModeLimit_synthesis`
  (§10.156) produces an `SqgSolution` from the per-mode limit +
  Fourier synthesis data directly.
- **Item 1 three-target structural closure (v0.4.39).** All three
  remaining Item 1 analytical targets from v0.4.38 now have in-tree
  Lean constructors, reducing their content to named, precisely-
  typed classical-analysis hypotheses.
    - **§10.153.C `sqgGalerkin_modeLipschitz_from_UniformH2`** —
      Target #3 monolithic closure.  Composes §10.153.A + §10.153.B
      across `m = 0` / `m ≠ 0` and `s ≤ t` / `t ≤ s` splits into an
      existential `(L, hL_nn, hL_holds)` triple consumable by §10.152.
      Closed after a 6-retry diagnostic iteration that broke a
      `DecidableEq (Fin 2 → ℤ)` synthesis loop via
      `attribute [local irreducible] GalerkinRHSHsNegSqBound` plus
      dropping the `Uniform` wrapper from the signature.
    - **§10.154 coefficient-injectivity bridge + `HasFourierSynthesis.ofPerModeLimit`**
      — Target #2 structural constructor.  `Lp_eq_of_mFourierCoeff_eq`
      (§10.154.A) establishes that two `Lp ℂ 2` elements with matching
      Fourier coefficients are equal (via `mFourierBasis.repr.injective`).
      `HasFourierSynthesis.ofPerModeLimit` (§10.154.B) assembles
      `HasFourierSynthesis per θ` from a synthesis witness + initial
      coefficient match + strong-`L²` convergence.
    - **§10.155 `HasPerModeLimit.ofModeLipschitzFamily`** — Target #1
      structural reduction.  Takes a classical Arzelà–Ascoli + Cantor
      diagonal extraction witness and produces `HasPerModeLimit α`
      from `HasModeLipschitzFamily α`, via the
      `modeCoeff_eq_galerkinExtend` bridge lemma (§10.155.A).
- **Concrete Fourier synthesis operator (v0.4.39, §10.157–§10.158).**
  Not just a structural reduction: an in-tree construction from
  ℓ²-summable coefficient sequences to `Lp ℂ 2` elements.
    - **§10.157 `fourierSynthesisLp`** — lifts `b ∈ ℓ²(ℤ²)` to the
      corresponding `L²(𝕋²)` element via mathlib's
      `mFourierBasis.repr.symm`.  `mFourierCoeff_fourierSynthesisLp`
      proves the Fourier coefficients of the synthesis recover `b`.
    - **§10.158.A/B `θLimOfLp` + `mFourierCoeff_θLimOfLp`** — concrete
      `θ_lim : ℝ → Lp ℂ 2` operator for `HasFourierSynthesis` via
      pointwise Fourier synthesis of an `lp`-valued per-mode limit.
- **MMP off the finite-Fourier-support class (post-v0.4.39, §10.167).**
  Extends §10.56 from the finite-support + uniform-ℓ∞ class to every
  strong-`L²` Galerkin limit with a uniform `Ḣ¹` bound, via lower-
  semicontinuity of `hsSeminormSq` under strong-`L²` convergence.
    - **§10.167.A `hsSeminormSq_le_of_L2_limit_uniform_bound`** — pure
      Fourier-side LSC lemma. Strong-`L²` convergence + per-`n` weighted
      summability + uniform `Ḣˢ` bound ⇒ weighted family on the limit
      is summable and the bound transfers. Proof via per-mode Fourier
      convergence (§10.141) + `tendsto_finset_sum` +
      `summable_of_sum_le` / `Real.tsum_le_of_sum_le` from mathlib.
    - **§10.167.B `MaterialMaxPrinciple.of_L2_limit_uniform_H1`** —
      MMP for `θ` realized as pointwise-in-`t` strong-`L²` limit of a
      sequence with uniform `Ḣ¹` bound.
    - **§10.167.C `MaterialMaxPrinciple.of_aubinLions_uniform_H1`** —
      specialization to `HasAubinLionsExtraction`, consuming the
      §10.139 extraction witness + a uniform `Ḣ¹` bound on the Galerkin
      states `galerkinToLp (sqgBox n) (α n t)`. Produces MMP for
      `ext.θ_lim` with no additional analytic axiom.
- **BKM off the finite-Fourier-support class (post-v0.4.39, §10.168).**
  Parallel to §10.167 for `BKMCriterionS2`.  Same LSC mechanism at
  every `s ∈ (1, 2]`, so the BKM structure's internal `Ḣ¹` hypothesis
  is vacuous.
    - **§10.168.A `BKMCriterionS2.of_L2_limit_uniform_Hs`** — BKM from
      an `L²`-limit sequence with per-`s` uniform `Ḣˢ` bound on the
      sequence.
    - **§10.168.B `BKMCriterionS2.of_aubinLions_uniform_Hs`** —
      specialization to `HasAubinLionsExtraction`.  Together with
      §10.167, both `MaterialMaxPrinciple` and `BKMCriterionS2` lift
      off the finite-support class from uniform `Ḣˢ` control on the
      Galerkin approximation alone.
- **Theorem 2 on the Aubin–Lions limit (post-v0.4.39, §10.169).**
  Capstone composition of §10.167.C + §10.168.B +
  `sqg_regularity_via_s2_bootstrap`.  Delivers the conditional
  Theorem 2 conclusion `∀ s ∈ [0, 2], ∃ M', ∀ t ≥ 0,
  hsSeminormSq s (ext.θ_lim t) ≤ M'` from exactly the uniform-in-
  `n`-and-`t` `Ḣˢ` bounds on the Galerkin approximation at `s = 1`
  and `s ∈ (1, 2]`.  No finite-support restriction on `θ_lim`; no
  axiom beyond mathlib.  This is the maximally-closed form of
  Theorem 2 reachable from the current infrastructure.
  **§10.170** exercises the composition unconditionally on the zero
  Aubin–Lions extraction (`HasAubinLionsExtraction.ofZero`), giving
  `sqg_regularity_of_aubinLions_ofZero`.
  **§10.171 `sqg_solution_and_regularity_via_RouteB_uniform_Hs`** —
  end-to-end capstone combining §10.148 (`SqgSolution` producer)
  with §10.169 (Theorem 2 on the limit).  From an Aubin–Lions
  extraction + per-level energy conservation + velocity witness +
  smooth initial data + uniform `Ḣˢ` bounds, produces both a genuine
  `SqgSolution` on `𝕋²` and the full Theorem 2 regularity conclusion
  on `s ∈ [0, 2]` for that solution.
- **Item 1 `hH2` structural closure (post-v0.4.39, §10.172).**
  The final Item 1 analytic input — the uniform `H⁻²` bound on
  `galerkinRHS` — is **discharged structurally** without passing
  through any Sobolev product bilinear estimate.  §10.172.A–F
  use the divergence-free structure `σ(ℓ) · ℓ = 0` on the SQG
  velocity symbol + Young's inequality on the finite Fourier
  convolution to produce the pointwise bound
  `‖galerkinRHS S c m‖ ≤ latticeNorm m · ∑_{n ∈ ↥S} ‖c n‖²`.
  Combined with §10.97's `L²` conservation, this yields a per-mode
  Lipschitz constant `L(m) = ‖θ₀‖²_{L²} · latticeNorm m` uniform in
  the Galerkin level `n`.  The capstone
  `HasPerModeLimit.ofSqgGalerkin_l2_conservation` (§10.172.F) then
  produces a `HasPerModeLimit α` **unconditionally** from Galerkin
  `L²` conservation + ODE hypotheses, completing the Item 1 chain
  down to the `HasFourierSynthesis` step.  Crucially: the standard
  Aubin-Lions uniform `H⁻²` bound via `L² × L² → H⁻¹` bilinear
  **fails** on `𝕋²` due to the log-divergence of `∑_{m≠0} |m|⁻²`
  in 2D; §10.172 sidesteps this entirely by never passing through
  a Sobolev product estimate.
- **Full-range Theorem 2 via `BKMCriterionHighFreq`
  (post-v0.4.39, §10.173–§10.175).**  Lifts the `s ≤ 2` restriction
  of §10.168/§10.169/§10.171 to the full Sobolev scale `s ≥ 0`.
  §10.167.A's LSC lemma is generic in `s`, so the high-frequency
  generalization is structural:
    - **§10.173.A/B `BKMCriterionHighFreq.of_L2_limit_uniform_Hs_all_s`
      / `.of_aubinLions_uniform_Hs_all_s`** — generic-`s` BKM from
      uniform `Ḣˢ` bounds at every `s > 1`.
    - **§10.174 `sqg_regularity_of_aubinLions_via_interpolation`** —
      full-range Theorem 2.  Composes §10.167.C + §10.173.B +
      `sqg_regularity_via_interpolation`.  Delivers uniform `Ḣˢ`
      bounds on every `s ≥ 0` given uniform Galerkin `Ḣˢ` bounds at
      `s = 1` and every `s > 1` plus `SqgEvolutionAxioms`.
    - **§10.175 `sqg_solution_and_regularity_via_RouteB_interpolation`**
      — end-to-end full-range capstone.  Parallel to §10.171 but
      covers every `s ≥ 0`.  Resolves `OPEN.md` Item 5's
      infrastructure gap: the structural chain is now uniform across
      the full Sobolev scale.

## What is *not* proven

- The classical Kato–Ponce fractional Leibniz estimate on `𝕋²` that
  would **discharge** the high-`s` Galerkin `Ḣˢ` bound hypothesis
  consumed by §10.174 / §10.175.  Both
  `MaterialMaxPrinciple.hOnePropagation` and
  `BKMCriterionHighFreq.hsPropagationHighFreq` now lift off the
  finite-support class (via §10.167 and §10.173) given uniform `Ḣˢ`
  bounds on the Galerkin approximation, supplied by the caller.

### Planned work: Route A (in-project Littlewood–Paley)

**Status: structural skeleton delivered and CI-green.** All 12 phases
of Route A have structural content in `RieszTorus.lean` (§10.177–§10.182
and §11.1–§11.16, inline because the local `rieszTorusMeasureSpace`
instance doesn't export across files).

- **Phases 1 + 3** (§10.177–§10.181, ~220 LOC): Parametric-`s`
  Galerkin `Ḣˢ` energy identity + Grönwall bound.
- **Phases 2 + 5** (§10.182, ~120 LOC): `HasGalerkinHsGronwallFamily`
  hypothesis package + uniform-across-levels bound extraction
  (`bound_on_Icc`, `uniform_bound_on_Icc`, `global_uniform_bound`).
- **Phase 6** (§11.1–§11.4, ~140 LOC): Littlewood–Paley primitives
  (`dyadicAnnulus N`, `fourierTruncate`, `lpProjector`, `lpPartialSum`,
  Fourier-coefficient + `Ḣˢ`-seminorm computations).
- **Phases 7–9** (§11.5–§11.7, ~50 LOC): Paraproduct, remainder,
  commutator, full Kato–Ponce hypothesis types (structural placeholders
  with zero paraproduct/remainder stubs).
- **Phase 10** (§11.8–§11.9, ~40 LOC): `HasSqgGalerkinHsClosure`
  structural bridge + `HasGalerkinHsGronwallFamily.of_sqgClosure`
  Phase 10 → Phase 5 bridge.
- **Phase 11** (§11.10, §11.13, ~60 LOC): Zero-datum exemplar for the
  Galerkin trajectory + `HasSqgGalerkinHsClosure.ofZero`.
- **§11.11** (~55 LOC): Trivial Kato–Ponce witnesses on the zero
  paraproduct stubs (`HasKatoPonceProductBound.ofZeroStubs`, etc.) —
  demonstrates hypothesis types are instantiable at `C = 0`.
- **§11.12** (~20 LOC): Phase 10 capstone
  `HasSqgGalerkinHsClosure.uniform_bound` — single-scalar uniform `Ḣˢ`
  bound on `[0, T]` feeding §10.174's `hBoundS` directly.
- **§11.14–§11.16** (~50 LOC): Auxiliary lemmas for the paraproduct
  chain: `lpProjector_vanishes_off_annulus`, `fourierTruncate_zero`,
  `lpProjector_zero`, `hsSeminormSq_lpProjector_zero`,
  `hsSeminormSq_fourierTruncate_zero`.
- **§11.17–§11.24** (~900 LOC): Concrete finite-Fourier-support
  product theory.  `sumSet`, `modeConvolution`, `trigPolyProduct`
  with closed-form Fourier coefficients (§11.17); Parseval +
  Cauchy–Schwarz pointwise bounds (§11.18); Peetre lattice
  inequality + seminorm on a trig polynomial (§11.19); concrete
  tame support-dependent Kato–Ponce bound (§11.20);
  `HasTrigPolyKatoPonceBound` structure (§11.21); Young's
  ℓ¹×ℓ² → ℓ² on `modeConvolution` (§11.22); ℓ¹ → `Ḣˢ`
  Cauchy–Schwarz bridge (§11.23); uniform-in-support L² product
  bound (§11.24).
- **§11.25** (~400 LOC): Banach-algebra `Ḣˢ` product bound.
  §11.25.A–D + C₂ (Peetre-weighted Young blocks + sqrt-Peetre);
  §11.25.E full `‖fg‖²_{Ḣˢ} ≤ 2^{2s}·(C_s(A)+C_s(B))·‖f‖²·‖g‖²`
  support-dependent assembly; §11.25.F support-INDEPENDENT form
  parametric on `HasLatticeZetaBound s C`; §11.25.G
  `HasTrigPolyBanachAlgebraBound` structure + `.of_latticeZeta`
  constructor; §11.25.H₁/H₂ zero-coefficient exemplars; §11.25.I
  `HasLatticeZetaBound.mono`.
- **§11.26** (~340 LOC): **Concrete `HasLatticeZetaBound s
  (latticeZetaConst s)` for every `s > 1`, unconditional.**
  §11.26.A 1D p-series prep; §11.26.B/B₂ coord → lattice norm;
  §11.26.C/C₁/C₂/C₃ annular shells on `ℤ²`; §11.26.D `|shell k| ≤ 8k + 4`;
  §11.26.E `∑_{m ∈ shell k} ‖m‖^{-2s} ≤ (8k+4)·k^{-2s}`;
  §11.26.F₁/F₂ `latticeZetaConst s := 8·ζ(2s-1) + 4·ζ(2s)`;
  §11.26.G `shellOf m := max(|m 0|.toNat, |m 1|.toNat)` +
  positivity, membership, and pairwise-disjointness of shells;
  §11.26.H shell-partition of any finite `A ⊆ ℤ²\{0}` + disjoint
  `Finset.sum_biUnion` + `Real.rpow_add` exponent split + finite-
  to-tsum bridge via `Summable.sum_le_tsum`.  Composed with §11.25.F/G,
  this gives a **concrete support-independent Banach-algebra `Ḣˢ`
  product bound with explicit constant** `2^{2s}·(2·latticeZetaConst s)`.

- **§11.27–§11.33** (~180 LOC): unconditional consequences of §11.26.H
  composed with the existing abstract theorems.  §11.27 is the concrete
  Banach-algebra `Ḣˢ` product bound (zero open hypotheses) for every
  `s > 1`.  §11.28 self-product form; §11.29 monotone constant form;
  §11.30 `ℓ¹ → Ḣˢ` Cauchy–Schwarz (Fourier-side form of Sobolev
  `Ḣˢ ⊂ L∞`); §11.31/§11.32 uniform `L² × Ḣˢ → L²` bounds in both
  factor directions; §11.33 Ḣᵗ interpolation for `t ≤ s`.
- **§11.34–§11.38 Path A closure of Item 5** (~120 LOC):
  `HasSqgGalerkinAllSBound α` hypothesis type packaging uniform
  Galerkin `Ḣ¹` + `Ḣˢ` bounds at every `s > 1`; `.ofZero` witness;
  `sqg_regularity_of_allSBound` capstone composing with §10.174's
  full-range interpolation; end-to-end `SqgSolution` variant;
  zero-datum unconditional full-range Theorem 2.

**Item 5 Path A closure** is at the same standard as Items 3/4:
hypothesis-keyed with zero-data exemplars; all classical PDE content
is labeled and isolated behind named hypotheses.

### Path B: structural bridge to classical Fourier analysis

The classical Fourier-analysis content that feeds the Galerkin
`Ḣˢ`-bound chain — Littlewood–Paley dyadic decomposition, Bony
paraproducts, a quantitative uniform-in-`N` Kato–Ponce commutator
bound of shape
`‖[Jˢ, u·∇]g‖_{L²} ≤ C·(‖∇u‖_{L∞}·‖g‖_{Ḣˢ} + ‖u‖_{Ḣˢ}·‖∇g‖_{L∞})`,
and the Sobolev embedding `Ḣˢ ⊂ L∞` for `s > d/2 = 1` — is in-tree
in the companion package
[`sqg-lean-proofs-fourier`](https://github.com/Brsanch/sqg-lean-proofs-fourier).
That package is intended for reuse by future NS / Euler / MHD
formalizations.  The SQG-specific plumbing (energy identity, velocity
Riesz-preservation, exponential Grönwall closure,
`HasSqgGalerkinAllSBound.ofGalerkin_nonZero_fullyConcrete`) is
in-tree in `SqgIdentity/FourierBridge.lean`.

**What Path B does *not* do.**  The end-to-end Path B chain is
verified conditional on the paper's (H-strain) + (H-bdry) hypotheses
(paper §9.6.3), or equivalently on the thermostat reformulation
(H-α) (paper §9.8). These hypotheses are named at the Lean level in
`SqgIdentity/RieszTorus.lean` §14 as `HasStrainLowerBound`,
`HasBoundaryCurvatureBound`, and `HasThermostatBound`, with the
`MaterialMaxPrinciple.of_HstrainHbdry` and
`MaterialMaxPrinciple.of_thermostat` constructors taking them as
labeled inputs.  Deriving any of these three hypotheses from the SQG
dynamics alone remains the open research problem the paper documents
as conditional Theorem 2; this repository does not claim to close it.

### Other open items (see `OPEN.md`)

- Item 1 classical analytical inputs consumed by v0.4.39 structural
  constructors (Arzelà–Ascoli + Cantor diagonal, strong-`L²`
  convergence, per-mode ODE / continuity / `H⁻²` discharges).
- Concrete `HasBumpToIndicatorSequence` witness (§10.135) from
  mathlib's `ContDiffBump` infrastructure.

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
  Basic.lean                 -- Theorem 1 + per-mode selection-rule bound
                                (universal CZ form; paper Prop 6.1 precursor):
                                polar + Cartesian forms, ℓ² lift,
                                SqgFourierData bundle, Parseval bridge
  RieszTorus.lean            -- Riesz-transform symbols on 𝕋ᵈ, Leray–Helmholtz,
                                fractional Sobolev scale, fractional + classical
                                heat semigroup suites, §10 Theorem 2 roadmap
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
