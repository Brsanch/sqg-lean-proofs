# Open items — sqg-lean-proofs

Canonical list of everything remaining before the project is closed.
Each item is linked to the tagged release that will close it.

## SQG mathematics

### 1. Generic-`L²` Galerkin → full-SQG extraction (Route B; chain extended v0.4.38)
**Status:** Chain extended through §10.147–§10.152. `l2Conservation`
(hypothesis #2 below) is now **internally discharged** from strong-`L²`
convergence + §10.97 per-level energy conservation + §10.142 zero-mode
preservation.  Route B capstone
`exists_sqgSolution_via_RouteB_from_galerkin_energy` (§10.148)
produces an `SqgSolution` without the `hL2` hypothesis.

Additional structural reduction (§10.149–§10.152) factors
`HasAubinLionsExtraction` existence into three precisely-typed Lean
construction targets:

1. **`HasPerModeLimit.ofModeLipschitzFamily`** — classical
   Arzelà–Ascoli (mode-wise on `[0, T]`) + Cantor diagonal across
   `ℤ² \ {0}`.  Mathlib has `BoundedContinuousFunction.arzelaAscoli`
   and `Denumerable (Fin 2 → ℤ)`; assembly is ~300-line Lean work.
2. **`HasFourierSynthesis.ofPerModeLimit`** — Parseval + Fatou +
   dominated convergence on `ℓ²(ℤ²)` producing the Lp-valued limit
   and strong-`L²` convergence.  Moderate, ~100–200 lines.
3. **Finish `§10.152`** — derive per-mode Lipschitz `L m` from
   §10.138's `H⁻²` bound + §10.116's Galerkin ODE via FTC.  Currently
   taken as a hypothesis input to `HasModeLipschitzFamily.ofSqgGalerkinBounds`.
   Tractable, ~50–100 lines.

Route B infrastructure (v0.4.38) now provides the complete chain
`SQG Galerkin data → HasModeLipschitzFamily → HasPerModeLimit →
HasFourierSynthesis → HasAubinLionsExtraction → SqgSolution`, each
arrow a named Lean theorem.  The three remaining targets above are the
ONLY analytical gaps — no more "mathlib-scale Bochner infrastructure"
vagueness; every gap is a specific named-theorem signature.

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

### 9. Zenodo webhook
Broken since v0.4.3. 24 releases have landed without Zenodo archives
(v0.4.15 through v0.4.38). Fix: re-authorize the webhook at
`github.com/SolomonB14D3/sqg-lean-proofs/settings/integrations`, then
confirm a fresh DOI mints on the next tag.

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

## Protocol

- One item per tagged release where practical. No compound changes.
- **No local `lake env lean` on `RieszTorus.lean`.** CI is the compile.
- Each release updates this file (strikes through closed items,
  moves resolved items to the "now resolved" section).
- "What's left" answers come from this file, not from regenerated
  context.
