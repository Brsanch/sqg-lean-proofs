# Open items — sqg-lean-proofs

Canonical list of everything remaining before the project is closed.
Each item is linked to the tagged release that will close it.

## SQG mathematics

### 1. Generic-`L²` Galerkin → full-SQG extraction (Route B; v0.4.39)
**Status:** All three named Lean targets from v0.4.38 have constructors
in-tree.  `l2Conservation` is internally discharged (§10.147, v0.4.38).
Route B capstone `exists_sqgSolution_via_RouteB_from_galerkin_energy`
(§10.148) produces an `SqgSolution` without the `hL2` hypothesis.

**v0.4.39 closed constructors:**

- **§10.153.C `sqgGalerkin_modeLipschitz_from_UniformH2`** — Target #3
  monolithic composition of §10.153.A + §10.153.B, in existential form
  consumable by §10.152.  Closed after 6-retry diagnostic workflow
  (DecidableEq synthesis loop, broken by local irreducibility on
  `GalerkinRHSHsNegSqBound` + direct per-`(n, τ)` hypothesis form).
- **§10.154.A/B `Lp_eq_of_mFourierCoeff_eq` +
  `HasFourierSynthesis.ofPerModeLimit`** — Target #2 coefficient-
  injectivity bridge + structural constructor.  Reduces
  `HasFourierSynthesis` construction to a synthesis witness + initial
  coefficient match + strong-L² convergence.
- **§10.155.A/B `HasModeLipschitzFamily.modeCoeff_eq_galerkinExtend` +
  `HasPerModeLimit.ofModeLipschitzFamily`** — Target #1 structural
  reduction.  Reduces `HasPerModeLimit` construction to a classical
  Arzelà–Ascoli + Cantor diagonal extraction witness.
- **§10.157 `fourierSynthesisLp`** — concrete Fourier synthesis
  operator via `mFourierBasis.repr.symm`.
- **§10.158.A/B `θLimOfLp` + `mFourierCoeff_θLimOfLp`** — concrete
  `θ_lim` operator for `HasFourierSynthesis` from an `lp`-valued
  per-mode limit function.

**Remaining Item 1 analytical work:**

1. **Strong-`L²` convergence** of the extracted Galerkin sequence to
   `θLimOfLp` (the `h_L2` input of §10.154.B).  Parseval on the
   difference + Fatou + DCT on `ℓ²(ℤ²)`.
2. **Classical Arzelà–Ascoli + Cantor diagonal extraction** (the
   `hExtract` input of §10.155.B).  Mathlib has
   `BoundedContinuousFunction.arzelaAscoli` + `Denumerable
   (Fin 2 → ℤ)`; ~300-line assembly.
3. **`hDeriv` / `hCont` / `hH2` discharges** for §10.153.C from
   §10.116's Galerkin ODE + §10.138's `H⁻²` bound via per-mode
   derivative projection.
4. **`Memℓp 2 ↔ Summable (‖·‖²)` bridge** — elementary mathlib lookup
   for the correct lemma name (§10.158.C guess was wrong; deferred).

Route B infrastructure now delivers `SQG Galerkin data →
HasModeLipschitzFamily → HasPerModeLimit → HasFourierSynthesis →
HasAubinLionsExtraction → SqgSolution`, plus the concrete
Fourier-synthesis operator.  Only genuine mathlib-scale classical
analysis remains.

### ~~2. `SqgEvolutionAxioms_strong` upgrade for §10.117 / §10.132~~ ✓ Closed in v0.4.33
Delivered by §10.133–§10.134: Ici-0 port of the §10.91 → §10.92 →
§10.94 Duhamel chain via `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`.
Headline: `exists_sqgSolution_strong_of_galerkin_realSym`.

### 3. `MaterialMaxPrinciple.hOnePropagation` off the finite-Fourier-support class
Extend §10.56's MMP discharge to solutions with infinite Fourier
support. Route via the §10.135 limit + lower-semicontinuity of the
Ḣ¹ seminorm. Target release: **v0.4.38**.

### 4. `BKMCriterionS2.hsPropagationS2` off the finite-Fourier-support class
Parallel to item 3 for the BKM criterion. Extends §10.57. Target
release: **v0.4.39**.

### 5. Ḣˢ bootstrap for `s > 2`
Blocked upstream on a mathlib Kato–Ponce fractional Leibniz estimate
on `𝕋ᵈ`. Two phases:
- **5.A** Contribute Kato–Ponce estimates to mathlib.
- **5.B** Once 5.A merges, extend `sqg_regularity_via_s2_bootstrap`
  to `s > 2`.
Target release: **v0.5.0**.

### ~~6. Mode-wise weak-form PDE identity against `sqgNonlinearFlux`~~ ✓ Closed in v0.4.34 (structural)
Structural bridge delivered by §10.135–§10.136:
`IsSqgWeakSolution.of_timeTest_of_bumpSeq` lifts
`IsSqgWeakSolutionTimeTest` to `IsSqgWeakSolution` given a
`HasBumpToIndicatorSequence` witness at every `(m, s, t)`, and
`SqgEvolutionAxioms_strong.of_timeTest_via_MMP` composes with §10.14.
Concrete construction of `HasBumpToIndicatorSequence` from mathlib's
`ContDiffBump` infrastructure is separately available but not
required by the chain.

## Infrastructure

*(Item 9 resolved — see "Previously-listed items now resolved" below.)*

## Previously-listed items now resolved

The following items on prior "what's left" lists are **already
closed** in current code:

- ~~2. `SqgEvolutionAxioms_strong` upgrade~~ — closed in v0.4.33
  via §10.133–§10.134 (Ici-0 port of Duhamel chain; headline
  `exists_sqgSolution_strong_of_galerkin_realSym`).
- ~~Derive `hFluxBound` from uniform L∞~~ — closed by §10.93
  `sqgNonlinearFlux_galerkin_bounded_of_L_inf` +
  §10.94 `SqgEvolutionAxioms_strong.of_galerkin_dynamics_with_L_inf_bound_on_support`.
- ~~Derive `SqgEvolutionAxioms.l2Conservation` from `Re⟨α, galerkinVF⟩ = 0`~~ —
  closed by §10.96 `galerkinRHS_inner_sum_re_eq_zero` +
  §10.97 `galerkinEnergyH0_const` +
  `galerkinToLp_hsSeminormSq_zero_const`, consumed by §10.98.
- ~~`push_neg` deprecation~~ — closed in v0.4.32.
- ~~CI Node 20 deprecation~~ — mitigated in v0.4.32 via
  `FORCE_JAVASCRIPT_ACTIONS_TO_NODE24` + `actions/checkout@v6`.
- ~~9. Zenodo webhook~~ — root cause was *not* the webhook itself
  (HTTP handshake was fine, returning 202 OK on every fire).  Two
  compounding issues:
  (a) GitHub sync started creating an **orphan concept** `19646556`
      at v0.4.3 instead of continuing canonical concept `19583256`;
      every later release minted a new record in the orphan chain.
  (b) `.zenodo.json`'s hardcoded `"version"` field overrode the git
      tag name in Zenodo's record metadata, producing 14 records all
      labeled `v0.4.9` (and one `v0.4.37`) under the orphan concept.
  **Fix (2026-04-21):** canonical concept `19583256` extended forward
  to v0.4.39 via the REST API (new record `19674045`, DOI
  `10.5281/zenodo.19674045`, commit `16a00e5` stripped the stale
  `"version"` field).  Concept DOI badge in README now resolves to
  v0.4.39.  The 24 orphan records under `19646556` are published and
  therefore undeletable by the owner — a separate email to
  `info@zenodo.org` is needed to purge or relink them; this is admin
  hygiene, not a blocker.  Zenodo's GitHub integration already points
  at the current `Brsanch/sqg-lean-proofs` repo (not the old
  `SolomonB14D3/sqg-lean-proofs` slug), so once the user re-enables
  sync, future tags will archive correctly into the canonical chain.

## Protocol

- One item per tagged release where practical. No compound changes.
- **No local `lake env lean` on `RieszTorus.lean`.** CI is the compile.
- Each release updates this file (strikes through closed items,
  moves resolved items to the "now resolved" section).
- "What's left" answers come from this file, not from regenerated
  context.
