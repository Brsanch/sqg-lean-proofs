# Open items — sqg-lean-proofs

Canonical list of everything remaining before the project is closed.
Each item is linked to the tagged release that will close it.

## SQG mathematics

### ~~1. Generic-`L²` Galerkin → full-SQG extraction (Route B; v0.4.39)~~ ✓ Closed post-v0.4.39 (§10.172)
**Status:** All three named Lean targets from v0.4.38 have constructors
in-tree.  `l2Conservation` is internally discharged (§10.147, v0.4.38).
Route B capstone `exists_sqgSolution_via_RouteB_from_galerkin_energy`
(§10.148) produces an `SqgSolution` without the `hL2` hypothesis.
Item 1's remaining `hH2` analytic input is discharged **structurally**
by §10.172 via the divergence-free pointwise galerkinRHS bound
(bypasses the need for any uniform `H⁻²` seminorm estimate).

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

**Item 1 analytical work — ALL FOUR INPUTS DISCHARGED STRUCTURALLY:**

1. ~~**Strong-`L²` convergence**~~ — ✓ **closed down to elementary
   tightness** via §10.164.
2. ~~**Classical Arzelà–Ascoli + Cantor diagonal extraction**~~ —
   ✓ **closed unconditionally** via §10.165 (the `hExtract` witness
   for §10.155.B follows from `HasModeLipschitzFamily` alone).
3. ~~**`hDeriv` / `hCont` discharges for §10.153.C**~~ — ✓ **closed**
   via §10.166.A/B (Item 1 input #3; consumes the whole-trajectory
   derivative from §10.116).
4. ~~**`hH2` uniform `H⁻²` bound on `galerkinRHS`**~~ — ✓ **closed
   structurally via §10.172 without needing any uniform `H⁻²`
   estimate**.  §10.172.A (Cauchy–Schwarz in `Fin 2`), §10.172.B
   (`galerkinKKernel` norm bound via divergence-free
   `σ(ℓ) · ℓ = 0`), §10.172.C (pointwise
   `‖galerkinRHS S c m‖ ≤ latticeNorm m · ∑_n ‖c n‖²`), §10.172.D
   (per-mode Lipschitz from `L²` conservation via §10.153.B MVT),
   §10.172.E (`HasModeLipschitzFamily.ofSqgGalerkin_l2_conservation`),
   §10.172.F (`HasPerModeLimit.ofSqgGalerkin_l2_conservation` Item 1
   capstone).  The standard uniform `H⁻²` bound via a Sobolev product
   bilinear estimate **fails** on `𝕋²` (the `L² × L² → H⁻¹`
   bilinear is log-divergent in 2D); the pointwise path circumvents
   this by using the divergence-free structure directly on the
   Fourier convolution, producing a per-mode Lipschitz constant
   `L(m) = ‖θ₀‖²_{L²} · latticeNorm m` uniform in `n`.

Route B infrastructure now delivers `SQG Galerkin data →
HasModeLipschitzFamily (§10.172.E) → HasPerModeLimit (§10.172.F) →
HasFourierSynthesis → HasAubinLionsExtraction → SqgSolution`, plus
concrete Fourier synthesis (§10.157) and the `ofSummable` top-level
constructor (§10.159).  The Item 1 chain is **fully structurally
closed** down to `HasPerModeLimit`.  The remaining
`HasFourierSynthesis` construction (tightness argument on `ℓ²(ℤ²)`)
is handled by §10.164 `ofTight`.

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

### Theorem 3 capstone on the Aubin–Lions limit (§10.169 – §10.171)
Composes §10.167 + §10.168 into a single theorem delivering the
conditional Theorem 3 conclusion on the `L²`-limit class, and
packages it with the §10.148 `SqgSolution` producer into an end-to-
end capstone:

- **§10.169 `sqg_regularity_of_aubinLions_uniform_Hs`** — for every
  `s ∈ [0, 2]`, a uniform `Ḣˢ` bound on `ext.θ_lim t` follows from
  uniform `Ḣˢ` bounds on the Galerkin states at `s = 1` and
  `s ∈ (1, 2]`.  No finite-support restriction on `θ_lim`; no axiom
  beyond mathlib.
- **§10.170 `sqg_regularity_of_aubinLions_ofZero`** —
  unconditional zero-datum instance of §10.169 on
  `HasAubinLionsExtraction.ofZero`.  Exercises the full composition
  end-to-end.
- **§10.171 `sqg_solution_and_regularity_via_RouteB_uniform_Hs`** —
  the end-to-end headline.  From a `HasAubinLionsExtraction`
  witness, per-level Galerkin energy conservation, a velocity
  witness, smooth initial data, and the uniform `Ḣˢ` bounds,
  delivers both a genuine `SqgSolution` **and** the Theorem 3
  regularity conclusion `∀ s ∈ [0, 2], ∃ M', ∀ t ≥ 0,
  hsSeminormSq s (sol.θ t) ≤ M'` on its `θ`-field.  This is the
  maximally-closed form of Theorem 3 reachable from the current
  infrastructure.

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
**Infrastructure extension now in-tree (post-v0.4.39):** §10.173.A/B
and §10.174 provide the structural extension path via
`BKMCriterionHighFreq` (the generic-`s` variant covering `s > 1`,
replacing the `s ≤ 2`-restricted `BKMCriterionS2`).  §10.174
`sqg_regularity_of_aubinLions_via_interpolation` delivers Theorem 3
on the full range `s ≥ 0` given uniform `Ḣˢ` Galerkin bounds at every
`s > 1`.  §10.175
`sqg_solution_and_regularity_via_RouteB_interpolation` is the
end-to-end full-range capstone.

**Still outstanding:** the actual classical Kato–Ponce fractional
Leibniz estimate on `𝕋²` that would **discharge** the high-`s`
Galerkin `Ḣˢ` bound hypothesis.  Two phases remain:
- **5.A** Contribute Kato–Ponce estimates to mathlib, OR supply an
  in-tree local version specialised to the torus Fourier multiplier
  setting.
- **5.B** Once 5.A delivers, discharge the §10.174 `hBoundS` hypothesis
  unconditionally for smooth initial data (local-in-time) and for
  the conditional-on-BKM-integral (global-in-time) setting.
Target release: **v0.5.0**.

**Route A execution (post-commit `d8346b0`, in progress):** Structural
skeleton for the Kato–Ponce chain delivered across §10.177–§10.182
and §11.1–§11.10 (all inline in `RieszTorus.lean`):

- §10.177–§10.181: Parametric-`s` Galerkin `Ḣˢ` energy identity,
  Grönwall bound (Phase 1 + Phase 3 + Phase 5 structural).
- §10.182: `HasGalerkinHsGronwallFamily` hypothesis package
  (Phase 2 + Phase 5).
- §11.1–§11.4: Dyadic annuli, `fourierTruncate`, `lpProjector`,
  `lpPartialSum`, Fourier-coefficient / seminorm computations
  (Phase 6).
- §11.5–§11.7: Paraproduct + remainder + commutator + full
  Kato–Ponce hypothesis types (Phase 7 + 8 + 9 structural).
- §11.8: `HasSqgGalerkinHsClosure` — Phase 10 structural bridge.
- §11.9: `HasGalerkinHsGronwallFamily.of_sqgClosure` — Phase 10 → 5.
- §11.10: Zero-datum exemplar (Phase 11).

**Route A execution — Item 5.A concrete content (post-commit `a7e9376`,
2026-04-21 late afternoon):** First concrete classical content toward
Item 5.A delivered across §11.17–§11.21:

- §11.17: `sumSet`, `modeConvolution`, `trigPolyProduct` + closed-form
  Fourier-coefficient formula.  Foundation for pointwise multiplication
  on finite-Fourier-support data via the Fourier convolution formula
  `(fg)̂(n) = ∑_{a+b=n} f̂(a)·ĝ(b)`.  Avoids the general `Lp`-not-a-ring
  issue by working directly with trig-poly representations.
- §11.18: Parseval identity `hsSeminormSq_trigPolyProduct` reducing the
  tsum `Ḣˢ` seminorm to a finite sum over `sumSet A B`, plus Cauchy–
  Schwarz pointwise bound on `|modeConvolution|²` via
  `Finset.sum_mul_sq_le_sq_mul_sq`.
- §11.19: Peetre lattice inequality `‖a+b‖^s ≤ 2^{s-1}·(‖a‖^s + ‖b‖^s)`
  for `s ≥ 1` via `NNReal.rpow_add_le_mul_rpow_add_rpow` +
  `latticeNorm_add_le` triangle, plus the `(σ_s(·))²` specialization.
  §11.19.D `hsSeminormSq_trigPoly` — direct finite-sum formula for
  seminorm on a trig polynomial.
- §11.20: **Concrete tame Kato–Ponce bound** on `trigPolyProduct`
  (support-dependent):
  `‖fg‖²_{Ḣˢ} ≤ (A ×ˢ B).card · 2^{2s-1} · (E_s^{cf}·N^{cg} + N^{cf}·E_s^{cg})`
  where `E_s = ∑ σ_s² ‖c‖²` and `N = ∑ ‖c‖²`.  First concrete trig-poly
  Kato–Ponce in-tree.  The `(A ×ˢ B).card` factor is the coarse
  Cauchy–Schwarz constant; a uniform (in support) bound requires Young
  `ℓ¹ × ℓ² → ℓ²` plus `∑_{m ∈ ℤ²} ‖m‖^{-2s}` summability for `s > d/2 = 1`,
  deferred.
- §11.21: **`HasTrigPolyKatoPonceBound`** hypothesis structure bounding
  `hsSeminormSq s (trigPolyProduct A B cf cg)` in Leibniz-split form.
  `HasTrigPolyKatoPonceBound.of_peetre` delivers a concrete instance
  at `C = 2^{2s-1}` for any `s ≥ 1` via §11.20.C.
- §11.22: **Young's `ℓ¹ × ℓ² → ℓ²`** on `modeConvolution`.
  Finite-lattice convolution bound:
  `∑_{n ∈ sumSet A B} ‖modeConv(n)‖² ≤ (∑_a ‖cf a‖)² · (∑_b ‖cg b‖²)`.
  Support-INDEPENDENT (no `(A ×ˢ B).card` factor on the RHS).
  Proof: triangle bound (§11.22.A) + weighted Cauchy–Schwarz via
  `Finset.sum_mul_sq_le_sq_mul_sq` with `F = χ · √‖cf‖`,
  `G = χ · √‖cf‖ · ‖cg‖` (§11.22.B) + first-factor bound
  `∑_{(a,b), a+b=n} ‖cf a‖ ≤ ∑_a ‖cf a‖` via `sum_eq_single` pinning
  `b = n - a` (§11.22.C) + sum reorder (§11.22.D) + product-sum
  factorization (§11.22.E).
- §11.23: **Cauchy–Schwarz bridge `ℓ¹ → Ḣˢ`** for `0 ∉ A`, `s > 0`:
  `(∑_a ‖cf a‖)² ≤ (∑_a ‖a‖^{-2s}) · hsSeminormSq s (trigPoly A cf)`.
  Proof: `Finset.sum_mul_sq_le_sq_mul_sq` with
  `F a = ‖a‖^{-s}`, `G a = ‖a‖^s · ‖cf a‖`; `F · G = ‖cf a‖` via
  `Real.rpow_add` on `-s + s = 0`; `F² = ‖a‖^{-2s}` and
  `G² = (σ_s a)² · ‖cf a‖²`.  Key input: `latticeNorm_pos` for
  `a ≠ 0` (from `0 ∉ A`).
- §11.24: **Uniform-in-support `L²` product bound.**  Combines §11.22
  and §11.23 into the finite-lattice uniform bound for `s > 0`,
  `0 ∉ A`:
  `∑_n ‖modeConv(n)‖² ≤ (∑_a ‖a‖^{-2s}) · hsSeminormSq s (trigPoly A cf) · (∑_b ‖cg b‖²)`.
  The lattice-weight factor `∑_{a ∈ A} ‖a‖^{-2s}` is bounded by the
  global zeta `∑_{a ∈ ℤ² \ {0}} ‖a‖^{-2s}` which is finite for
  `s > d/2 = 1`.  For the SQG Galerkin at `A = sqgBox n`, this is
  uniform in `n`.
- §11.25.A–D + C₂: **Building blocks for the Banach-algebra `Ḣˢ`
  product bound.**
  - §11.25.A₁–A₂ `sumSet_symm`, `modeConvolution_symm`: commutativity
    of the Minkowski sum and the mode convolution in their two factors.
  - §11.25.B `hsSeminormSq_zero_trigPolyProduct_le_young_symm`:
    symmetric Young bound `∑_n ‖modeConv(n)‖² ≤ (∑_a ‖cf a‖²) · (∑_b ‖cg b‖)²`
    via §11.22 applied to swapped factors (ℓ² × ℓ¹ direction).
  - §11.25.C `young_peetre_weighted_left`: Peetre-weighted Young on
    `T_1'(n) = ∑_{a+b=n} σ_s(a)·‖cf a‖·‖cg b‖`:
    `∑_n T_1'(n)² ≤ hsSeminormSq s (trigPoly A cf) · (∑_b ‖cg b‖)²`
    via complex embedding into §11.25.B.
  - §11.25.C₂ `fracDerivSymbol_add_le_sqrt`: linear-form (sqrt) Peetre
    inequality: `σ_s(a+b) ≤ √(2^{2s-1}) · (σ_s a + σ_s b)` for `s ≥ 1`.
    From squared Peetre §11.19.C + subadditivity + Real.sqrt_le_sqrt.
  - §11.25.D `young_peetre_weighted_right`: dual of §11.25.C, applying
    §11.22 (ℓ¹ × ℓ² direction) to `T_2'(n)`:
    `∑_n T_2'(n)² ≤ (∑_a ‖cf a‖)² · hsSeminormSq s (trigPoly B cg)`.

**Still outstanding for unconditional Item 5 closure:** §11.25.E
Banach-algebra `Ḣˢ` product bound — assembled by combining §11.25.C
(weighted Young left) + §11.25.D (weighted Young right) + §11.25.C₂
(sqrt-Peetre) + §11.23 (CS bridge) via pointwise bound
`(σ_s n)² · ‖modeConv‖² ≤ 2^{2s} · (T_1'² + T_2'²)`.  Target:
  `‖fg‖²_{Ḣˢ} ≤ 2^{2s} · (C_s(A) + C_s(B)) · ‖f‖²_{Ḣˢ} · ‖g‖²_{Ḣˢ}`
for `0 ∉ A`, `0 ∉ B`, `s ≥ 1`; ~150 LOC.  Then: global lattice
zeta summability `∑_{a ∈ ℤ² \ {0}} ‖a‖^{-2s} < ∞` for `s > 1`
(standard); wiring into `HasSqgGalerkinHsClosure` Phase 10 bridge
via the SQG-specific velocity bound on `∇θ_n · u_n` and the §10.174
`hBoundS` discharge.  Classical remainder ~250–400 LOC.

With §11.17–§11.25.A–D + C₂, all the Young + Cauchy–Schwarz +
sqrt-Peetre building blocks are in-tree.  Assembly into §11.25.E
Banach-algebra form is the natural next step.  The structural
chain from Kato-Ponce to uniform `Ḣˢ` Galerkin bound (feeding
§10.174's `hBoundS`) is in-tree.

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

- ~~1. Generic-`L²` Galerkin → SqgSolution extraction — `hH2` analytic
  input~~ — closed post-v0.4.39 by §10.172 via divergence-free
  pointwise `galerkinRHS` bound instead of any `H⁻²` seminorm
  estimate.  The standard uniform `H⁻²` bound fails on `𝕋²` due
  to the log-divergence of `∑_{m≠0} |m|⁻²` in 2D; the pointwise
  path bypasses this.  Per-mode Lipschitz constant
  `L(m) = ‖θ₀‖²_{L²} · latticeNorm m` uniform in `n`.  Chain:
  `HasModeLipschitzFamily.ofSqgGalerkin_l2_conservation` (§10.172.E)
  → `HasPerModeLimit.ofSqgGalerkin_l2_conservation` (§10.172.F).
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

## Next-session plan — Route A (Littlewood–Paley in-project)

Decided 2026-04-21 late evening.  All remaining analytic content
(Items 2, 3, 5) written **in-project** in `SqgIdentity/` as mathlib-
shaped primitives.  No upstream review cycle; mathlib contribution
is a separate later activity.

### LOC mapping (~4810 lines total, ~12-15 agent-hours)

| Phase | Target | LOC | Deliverable |
|---|---|---|---|
| 1 | Galerkin `Ḣ¹` energy identity + commutator (Item 2) | ~800 | `d/dt ‖θ_n‖²_{Ḣ¹}` + int-by-parts on finite-support |
| 2 | MMP → `‖∇u_n‖_{L∞}` bound + Grönwall (Item 2) | ~450 | Uniform `Ḣ¹` bound on Galerkin |
| 3 | Parametric-`s` energy identity (Item 3) | ~300 | Same structure as Phase 1, `s ∈ (1, 2]` |
| 4 | Hölder + Sobolev `L^p` on `𝕋²` | ~400 | Prereq for Phase 5 |
| 5 | BKM integral hypothesis + Grönwall (Item 3) | ~350 | Uniform `Ḣˢ` bound on Galerkin, `s ∈ (1, 2]` |
| 6 | Littlewood–Paley on `𝕋²`: dyadic projectors `Δ_N` | ~700 | New file `SqgIdentity/LittlewoodPaley.lean` |
| 7 | Paraproduct `T_f g`, remainder `R(f,g)` | ~600 | Continue LP file |
| 8 | Commutator `[Jˢ, f]·∇g` estimate | ~500 | Core of Kato–Ponce |
| 9 | Full Kato–Ponce `‖Jˢ(fg)‖_{L^p}` (Item 5) | ~400 | Consumable by downstream |
| 10 | SQG flux application + `s > 2` bootstrap | ~200 | Extends §10.174 to unconditional |
| 11 | Structural hypothesis wrappers, zero-datum, docs | ~300 | `HasBKMIntegral`, zero-datum, CHANGELOG |
| 12 | CI iteration overhead (~20%) | ~800 | Expected from §10.172 pattern |

### Dependency graph

```
Phase 1 (Ḣ¹ identity) ──────────────┐
                                    ├─→ Phase 2 (Item 2 closure)
Phase 3 (param-s identity) ─────────┤
                                    ├─→ Phase 5 (Item 3 closure, s≤2)
Phase 4 (L^p on 𝕋²) ────────────────┘
                                         │
Phase 6 (Δ_N projectors) ───────────┐    │
Phase 7 (paraproducts) ─────────────┤    │
                                    ├─→ Phase 9 (Kato–Ponce)
Phase 8 (commutator) ───────────────┘         │
                                              ├─→ Phase 10 (Item 5 closure, s>2)
                                         ← Phases 4, 5 (L^p + BKM)
```

### Order of attack

1. **Phase 6** first (Littlewood–Paley primitives) — unblocks both
   the commutator chain and future SQG work.  Write in
   `SqgIdentity/LittlewoodPaley.lean`.
2. Phases 7, 8, 9 build on Phase 6.
3. **Phase 1** in parallel — the Galerkin `Ḣ¹` identity is
   independent of Littlewood–Paley (just chain rule under finite sum).
4. Phases 2, 3 follow Phase 1.
5. Phase 4 (`L^p` on `𝕋²`) needed before Phase 5.  Check mathlib
   — much may already exist via `MeasureTheory.Lp`.
6. Phases 5, 10 are the closing capstones for Items 3 and 5.
7. Phase 11 wraps structural hypothesis types + documentation.

### Mathlib gaps to expect

- `Lᵖ(𝕋²)`: mathlib has `Lp` generically but torus-specific
  interpolation and Sobolev embedding lemmas may need local versions.
- Littlewood-Paley: not in mathlib yet; write from scratch using
  `mFourierBasis` + dyadic cutoffs.
- Fractional Leibniz: exactly what we're adding.

### Session entry points for future agent

- **Start a session with**: "continue Route A, start Phase 6 (Littlewood-Paley primitives)".
- **Or**: "continue Route A, Item 2 first (Galerkin Ḣ¹ energy identity)".
- Read `memory/plan_route_A_item_5.md` for the full dependency map.

## Protocol

- One item per tagged release where practical. No compound changes.
- **No local `lake env lean` on `RieszTorus.lean`.** CI is the compile.
- Each release updates this file (strikes through closed items,
  moves resolved items to the "now resolved" section).
- "What's left" answers come from this file, not from regenerated
  context.
