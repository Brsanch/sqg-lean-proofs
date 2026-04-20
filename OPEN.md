# Open items — sqg-lean-proofs

Canonical list of everything remaining before the project is closed.
Each item is linked to the execution plan at
`.claude/plans/plan-it-out-don-t-mossy-kahan.md` on the executor's
side, and to the tagged release that will close it on this side.

## SQG mathematics

### 1. Generic-L² Galerkin → full-SQG extraction
Construct `IsGalerkinLimitData θ b` + `GalerkinLimitTrajectory θ b`
from §10.118–§10.123's uniform estimates for `L²(𝕋²)` initial data
that is *not* a finite trigonometric polynomial. Requires per-mode
time-modulus of continuity, diagonal subsequence extraction, and
Fourier synthesis. Target release: **v0.4.37**.

### 2. `SqgEvolutionAxioms_strong` upgrade for §10.117 / §10.132
The existing Galerkin-derived `SqgSolution` satisfies only the
weak-form `SqgEvolutionAxioms`. Upgrade to the Duhamel-level
`SqgEvolutionAxioms_strong` via a backward-Picard extension of §10.116
to full ℝ, feeding §10.94. Target release: **v0.4.35**.

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

### 6. Mode-wise weak-form PDE identity against `sqgNonlinearFlux`
State and prove the per-mode Duhamel identity for genuine SQG weak
solutions. Feeds `SqgEvolutionAxioms_strong.of_sqgDuhamelIdentity_via_MMP`
to extend the strong form beyond the finite-support Galerkin class.
Target release: **v0.4.36**.

## Infrastructure

### 9. Zenodo webhook
Broken since v0.4.3. 17 releases have landed without Zenodo
archives (v0.4.15 through v0.4.31). Fix: re-authorize the webhook
at `github.com/SolomonB14D3/sqg-lean-proofs/settings/integrations`,
then confirm a fresh DOI mints on the next tag.

## Previously-listed items now resolved

The following items on prior "what's left" lists are **already
closed** in current code, though memory / README captions may still
mention them:

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
