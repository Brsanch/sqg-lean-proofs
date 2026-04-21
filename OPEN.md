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
- **§10.156 Item 1 structural capstone** — consumes `per` + `syn`
  witnesses + the wiring §10.139–§10.152 packaged and produces the
  full `SqgSolution` extraction.

**Post-tag additions (on `main`, not in the v0.4.39 tag):**

- **§10.158.C/D `lpOfSummableSqNorm` + `lpOfSummableSqNorm_coeff`** —
  **closes the `Memℓp 2 ↔ Summable (‖·‖²)` bridge** internally via
  mathlib's `memℓp_gen_iff`.  (Prior "§10.158.C guess was wrong"
  remark is obsolete — the second attempt on `memℓp_gen_iff` lands.)
- **§10.159 `HasFourierSynthesis.ofSummable`** — top-level Target #2
  constructor that composes §10.154.B + §10.157 + §10.158 into a
  single API taking `per`, an `Lp` witness, an initial coefficient
  match, an ℓ²-summability datum, and a strong-`L²` convergence
  datum.  The caller never supplies an `Lp`-valued witness directly.
- **§10.160 `integral_norm_sq_sub_eq_tsum_sq_mFourierCoeff_sub`** —
  Parseval on a difference (`∫ ‖f - g‖² = ∑' m, ‖f̂ m - ĝ m‖²` on the
  2-torus).  Green on CI as of commit `5428199` (`Pi.sub_apply` fix).
- **§10.161 `integral_norm_sq_galerkin_sub_θLim_eq_tsum`** — L²-to-ℓ²
  bridge: specializes §10.160 to `f = galerkinToLp` and `g =
  θLimOfSummable`, composing the Fourier-coefficient identities for
  both sides.  Green via §10.160's fix.
- **§10.162 `tendsto_integral_norm_sq_galerkin_sub_θLim_of_tsum`**
  (commit `48420b8`) — `Tendsto.congr` wrapper on §10.161.  Converts
  `h_L2` (L²-integral Tendsto, the hypothesis of §10.159.C) into a
  pure ℓ²-tsum Tendsto on per-mode coefficient differences.  Zero
  `Lp`-coercion bookkeeping remains downstream.
- **§10.163 `tsum_sq_sub_tendsto_zero_of_tight`** (commit `80ed516`)
  — pure-ℓ² Vitali convergence.  Per-mode pointwise convergence
  `f k i → g i` plus uniform ℓ²-tail tightness on squared differences
  + summability of each `‖f k · - g‖²` gives `∑' i, ‖f k i - g i‖² → 0`.
  Free of SQG-specifics.
- **§10.164 `HasFourierSynthesis.ofTight`** (commit `7703930`) —
  tight-family capstone.  Given `HasPerModeLimit` + `hSum` + summability
  of coefficient differences + uniform ℓ²-tail tightness on differences,
  constructs `HasFourierSynthesis per θ` with zero `Lp`-coercion exposure
  to the caller.  Composes §10.162 + §10.163 +
  `HasPerModeLimit.tendsto_modeCoeff`.
- **§10.165.A/B/C/D + `sqgGalerkin_hExtract_witness`** (commits
  `e9e51a8`, `4d8010e`, `c6a0407`, `e2fab41`, `0d99c72`) — full
  Arzelà–Ascoli + Cantor diagonal construction: BW on bounded
  complex sequences (§10.165.A), Cantor diagonal across a countable
  family of bounded ℂ-sequences (§10.165.B), application to
  `(Fin 2 → ℤ) × ℚ`-indexed rational-time data (§10.165.C),
  Lipschitz-driven extension to every real `t ≥ 0` via CauchySeq +
  rational approximation (§10.165.D).  Final composition
  `sqgGalerkin_hExtract_witness` produces the `hExtract` witness
  demanded by §10.155.B unconditionally from `HasModeLipschitzFamily`.
- **§10.153.C `m`-restriction** (commit `4e02eef`) — restricts
  `hDeriv` / `hCont` hypotheses to `m ∈ sqgBox n` and handles
  leakage modes internally (`galerkinExtend = 0` there, so the
  Lipschitz bound is trivially satisfied).  Resolves the scoping
  issue that previously blocked Item 1 input #3.
- **§10.166.A/B** (commit `e6b0015`) — discharges of §10.153.C's
  restricted `hDeriv` / `hCont` from the whole-trajectory derivative
  of §10.116 via `hasDerivWithinAt_pi` / `continuousOn_pi` and the
  `rfl` identity `galerkinVectorField ⟨m, hm⟩ = galerkinRHS
  (galerkinExtend _) m` (line 13737).

**Item 1 analytical work — ALL THREE INPUTS DISCHARGED STRUCTURALLY:**

1. ~~**Strong-`L²` convergence**~~ — ✓ **closed down to elementary
   tightness** via §10.164.
2. ~~**Classical Arzelà–Ascoli + Cantor diagonal extraction**~~ —
   ✓ **closed unconditionally** via §10.165 (the `hExtract` witness
   for §10.155.B follows from `HasModeLipschitzFamily` alone).
3. ~~**`hDeriv` / `hCont` discharges for §10.153.C**~~ — ✓ **closed**
   via §10.166.A/B (Item 1 input #3; consumes the whole-trajectory
   derivative from §10.116).  `hH2` (uniform `H⁻²` bound) is the
   remaining SQG-specific analytic input; it will be discharged from
   the §10.116 uniform `L∞` coefficient bound + §10.138 once the
   mathlib Kato–Ponce infrastructure allows.

Route B infrastructure now delivers `SQG Galerkin data →
HasModeLipschitzFamily → HasPerModeLimit → HasFourierSynthesis →
HasAubinLionsExtraction → SqgSolution`, plus concrete Fourier
synthesis (§10.157) and the `ofSummable` top-level constructor
(§10.159).  Only genuine mathlib-scale classical analysis remains.

### ~~2. `SqgEvolutionAxioms_strong` upgrade for §10.117 / §10.132~~ ✓ Closed in v0.4.33
Delivered by §10.133–§10.134: Ici-0 port of the §10.91 → §10.92 →
§10.94 Duhamel chain via `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`.
Headline: `exists_sqgSolution_strong_of_galerkin_realSym`.

### ~~3. `MaterialMaxPrinciple.hOnePropagation` off the finite-Fourier-support class~~ ✓ Closed post-v0.4.39 (structural)
Closed by §10.167 (commit `bc420d5`).  Route implemented as the
lower-semicontinuity of `hsSeminormSq` under strong-`L²` convergence:

- **§10.167.A** `hsSeminormSq_le_of_L2_limit_uniform_bound` — pure
  Fourier-side LSC lemma.  Strong-`L²` convergence `fₙ → g` + uniform
  `Ḣˢ` bound on the sequence + per-`n` weighted summability ⇒
  weighted `Ḣˢ` family on `g` is summable and `hsSeminormSq s g ≤ M`.
  Proof: per-mode Fourier convergence (§10.141) + finite-sum
  continuity (`tendsto_finset_sum`) + `summable_of_sum_le` /
  `Real.tsum_le_of_sum_le` from mathlib.
- **§10.167.B** `MaterialMaxPrinciple.of_L2_limit_uniform_H1` — MMP
  for any `θ` realised as a pointwise-in-`t` strong-`L²` limit of a
  sequence with uniform `Ḣ¹` bound and per-state summability.
- **§10.167.C** `MaterialMaxPrinciple.of_aubinLions_uniform_H1` —
  specialisation to `HasAubinLionsExtraction`.  Consumes the §10.139
  extraction witness plus a uniform `Ḣ¹` bound on the Galerkin states
  `galerkinToLp (sqgBox n) (α n t)`; produces MMP for `ext.θ_lim`.

With these, MMP off the finite-support class follows from a single
uniform `Ḣ¹` bound on the Galerkin approximation, with no additional
analytic axiom.  The uniform `Ḣ¹` bound is the classical regularity
input supplied by Galerkin energy theory.

### ~~4. `BKMCriterionS2.hsPropagationS2` off the finite-Fourier-support class~~ ✓ Closed post-v0.4.39 (structural)
Closed by §10.168 (commit `10ea042`).  Parallel to Item 3 via the
same `hsSeminormSq_le_of_L2_limit_uniform_bound` LSC lemma at
every `s ∈ (1, 2]`:

- **§10.168.A** `BKMCriterionS2.of_L2_limit_uniform_Hs` — BKM from an
  `L²`-limit sequence with uniform-in-`n`-and-`t` `Ḣˢ` bound at each
  `s ∈ (1, 2]`.  The `Ḣ¹` hypothesis inside `hsPropagationS2` is
  unused: §10.167.A applied at each `s` discharges the `Ḣˢ` bound on
  the limit directly.
- **§10.168.B** `BKMCriterionS2.of_aubinLions_uniform_Hs` —
  specialisation to `HasAubinLionsExtraction`.  Consumes the §10.139
  extraction witness plus a uniform `Ḣˢ` bound on the Galerkin states
  at every `s ∈ (1, 2]`; produces `BKMCriterionS2 (ext.θ_lim)`.
- **`hsSeminormSq_summable_galerkinToLp`** — parametric-`s` companion
  to §10.167's `hsSeminormSq_one_summable_galerkinToLp`.

Together with §10.167, both `MaterialMaxPrinciple` and
`BKMCriterionS2` lift off the finite-support class with no additional
analytic axiom, so long as the caller supplies uniform `Ḣˢ` bounds on
the Galerkin approximation for `s ∈ [1, 2]`.

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
  therefore undeletable by the owner; they are accepted as clutter
  and not worth further action.  Zenodo's GitHub integration already
  points at the current `Brsanch/sqg-lean-proofs` repo (not the old
  `SolomonB14D3/sqg-lean-proofs` slug), so once the user re-enables
  sync, future tags will archive correctly into the canonical chain.

## Protocol

- One item per tagged release where practical. No compound changes.
- **No local `lake env lean` on `RieszTorus.lean`.** CI is the compile.
- Each release updates this file (strikes through closed items,
  moves resolved items to the "now resolved" section).
- "What's left" answers come from this file, not from regenerated
  context.
