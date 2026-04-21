# Changelog

All releases are archived on Zenodo; the concept DOI
[10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) resolves
to the latest version.

## Unreleased (post-v0.4.39, on `main`) — 2026-04-21

**Route A execution — in progress.**  Structural skeleton for all
12 phases delivered across §10.177–§10.182 (RieszTorus.lean) and
§11.1–§11.10 (new file `SqgIdentity/LittlewoodPaley.lean`).  All
structural hypothesis types are in place; the classical
Littlewood–Paley analytical content (paraproduct definitions,
commutator estimates, full Kato–Ponce) remains for a follow-up
session.

- **§10.177–§10.181** — Parametric-`s` Galerkin `Ḣˢ` energy identity
  (Phase 1 at `s = 1`, Phase 3 at `s > 1`).
  - `trigPolyEnergyHs s S c = ∑ (fracDerivSymbol s m)² · ‖c m‖²`.
  - `trigPolyEnergyHs_hasDerivAt` — derivative identity.
  - `trigPolyEnergyHs_gronwall_bound` — Phase 5 Grönwall closure.
- **§10.182** — `HasGalerkinHsGronwallFamily` hypothesis package
  (Phase 2 + Phase 5 structural).
  - `bound_on_Icc`, `uniform_bound_on_Icc`, `global_uniform_bound`.
- **New file `LittlewoodPaley.lean`**:
  - **§11.1** `dyadicAnnulus N` — `ℓ∞`-dyadic blocks on `ℤ²` as
    `sqgBox`-differences.
  - **§11.2** `fourierTruncate A f` — Fourier projection onto a
    Finset via `trigPoly`.
  - **§11.3** `lpProjector N`, `lpPartialSum N` — Littlewood–Paley
    projector `Δ_N` and its partial sum `S_N` (Phase 6).
  - **§11.4** `fourierTruncate_mFourierCoeff`,
    `hsSeminormSq_fourierTruncate` — Kronecker-indicator + `Ḣˢ`
    seminorm of the truncation.
  - **§11.5** `HasParaproductHsBound`, `HasParaRemainderHsBound` —
    paraproduct hypothesis types (Phase 7 structural).
  - **§11.6** `HasKatoPonceCommutatorBound` — commutator hypothesis
    (Phase 8 structural).
  - **§11.7** `HasKatoPonceProductBound` — full Kato–Ponce hypothesis
    (Phase 9 structural).
  - **§11.8** `HasSqgGalerkinHsClosure` — Phase 10 structural bridge
    from Kato–Ponce + velocity bound to the log-derivative inequality.
  - **§11.9** `HasGalerkinHsGronwallFamily.of_sqgClosure` — Phase 10
    → Phase 5 bridge.
  - **§11.10** `zeroGalerkin` + zero-datum exemplar — exercises the
    full Phase 2→5→10 chain on the zero trajectory, parallel to
    §10.170 / §10.176.

**Route A chain structure.**  With the structural chain in place,
closing `OPEN.md` Item 5 reduces to discharging
`HasKatoPonceProductBound s C` for the high-`s` Galerkin analysis.
The rest of the chain is `.of_sqgClosure` + `.global_uniform_bound`
feeding §10.174's `hBoundS` hypothesis.

**Route A Item 5.A — concrete classical content begun.**  First
concrete trig-poly Kato–Ponce delivered across §11.17–§11.21
(inline in `RieszTorus.lean`):

- **§11.17** `sumSet`, `modeConvolution`, `trigPolyProduct` — finite-
  Fourier-support pointwise product via the Fourier convolution
  formula `(fg)̂(n) = ∑_{a+b=n} f̂(a)·ĝ(b)`.  Closed-form
  Fourier-coefficient formula (`mFourierCoeff_trigPolyProduct`) +
  zero-factor lemmas.  Avoids `Lp`-not-a-ring by working on trig-poly
  representations directly.
- **§11.18** `hsSeminormSq_trigPolyProduct` (Parseval identity
  reducing the tsum `Ḣˢ` seminorm to a finite sum over `sumSet A B`)
  + `modeConvolution_normSq_le_card_mul_sum` (pointwise Cauchy–
  Schwarz bound on `|modeConvolution|²` via
  `Finset.sum_mul_sq_le_sq_mul_sq`).
- **§11.19** Peetre lattice inequality:
  - `latticeNorm_add_rpow_le` — `‖a+b‖^s ≤ 2^{s-1}·(‖a‖^s + ‖b‖^s)`
    for `s ≥ 1` via `NNReal.rpow_add_le_mul_rpow_add_rpow` +
    `latticeNorm_add_le`.
  - `fracDerivSymbol_sq_eq_latticeNorm_rpow` — uniform expansion
    `(σ_s x)² = ‖x‖^{2s}` handling `x = 0` via `Real.zero_rpow`.
  - `fracDerivSymbol_sq_add_le` — Peetre on the `fracDerivSymbol`
    squared.
  - `hsSeminormSq_trigPoly` — direct finite-sum formula for `Ḣˢ`
    seminorm on a trig polynomial.
- **§11.20** `hsSeminormSq_trigPolyProduct_le_kato_ponce` —
  **concrete tame Kato–Ponce bound** (support-dependent):
  `‖fg‖²_{Ḣˢ} ≤ (A ×ˢ B).card · 2^{2s-1} · (E_s^{cf}·N^{cg} + N^{cf}·E_s^{cg})`
  where `E_s = ∑_a σ_s² ‖c_a‖²` and `N = ∑_a ‖c_a‖²`.  Proof
  combines §11.18.C (Cauchy–Schwarz on `modeConv`) with §11.19.C
  (Peetre on `σ_s(a+b)²`), sum reorder across `sumSet A B × (A ×ˢ B)`
  (§11.20.A), and product-sum factorization via `Finset.sum_product`
  + `Finset.mul_sum`/`Finset.sum_mul`.
- **§11.21** `HasTrigPolyKatoPonceBound` — hypothesis structure
  bounding `hsSeminormSq s (trigPolyProduct A B cf cg)` in Leibniz
  split form, parallel to `HasKatoPonceProductBound` but keyed on
  `trigPolyProduct` rather than the paraproduct stubs.
  `HasTrigPolyKatoPonceBound.of_peetre` delivers a concrete instance
  at `C = 2^{2s-1}` from §11.20.C.
- **§11.22** `hsSeminormSq_zero_trigPolyProduct_le_young` — finite-
  lattice Young's `ℓ¹ × ℓ² → ℓ²` on `modeConvolution`:
  `∑_n ‖modeConv(n)‖² ≤ (∑_a ‖cf a‖)² · (∑_b ‖cg b‖²)`.
  Support-INDEPENDENT on the RHS (no `(A ×ˢ B).card` factor).
  Sub-lemmas:
  - `modeConvolution_norm_le_sum_abs` — triangle bound (§11.22.A).
  - `sum_pair_indicator_sq_le_cs` — weighted Cauchy–Schwarz on the
    indicator sum with `F = χ · √‖cf‖`, `G = χ · √‖cf‖ · ‖cg‖` via
    `Finset.sum_mul_sq_le_sq_mul_sq` (§11.22.B).
  - `sum_pair_indicator_first_le_ℓ1` — first-factor bound
    `∑_{(a,b), a+b=n} ‖cf a‖ ≤ ∑_a ‖cf a‖` via `Finset.sum_product`
    + `Finset.sum_eq_single (n - a)` pinning `b = n - a`, with
    `add_sub_cancel_right` + `add_comm` for the vector-additive-group
    algebra (§11.22.C).
  - `sum_sumSet_pair_cfcg_reorder` — specialization of §11.20.A
    sum-reorder for Young (§11.22.D).
  - Final assembly via `Finset.sum_product` + `Finset.mul_sum` +
    `Finset.sum_mul` to factor `∑ p, ‖cf p.1‖·‖cg p.2‖²` as
    `(∑ a, ‖cf a‖)·(∑ b, ‖cg b‖²)` (§11.22.E).
- **§11.23** `sum_norm_sq_le_latticeWeight_mul_hsSeminormSq` — CS
  bridge `ℓ¹ → weighted ℓ²` for `0 ∉ A`, `s > 0`:
  `(∑_a ‖cf a‖)² ≤ (∑_a ‖a‖^{-2s}) · hsSeminormSq s (trigPoly A cf)`.
  Proof: `Finset.sum_mul_sq_le_sq_mul_sq` with `F a = ‖a‖^{-s}`,
  `G a = ‖a‖^s · ‖cf a‖`, computing the factors via `Real.rpow_add`
  for `F · G = ‖cf a‖` (exponent `-s + s = 0` + `Real.rpow_zero`),
  `Real.rpow_mul` for `F² = ‖a‖^{-2s}`, and `mul_pow` +
  `fracDerivSymbol_of_ne_zero` for `G² = (σ_s a)² · ‖cf a‖²`.
  Key input: `latticeNorm_pos` for `a ≠ 0` (from `0 ∉ A`).
- **§11.24** `l2_trigPolyProduct_le_uniform` — uniform-in-support
  `L²` product bound combining §11.22 + §11.23:
  `∑_n ‖modeConv(n)‖² ≤ C_s(A) · hsSeminormSq s (trigPoly A cf) · (∑_b ‖cg b‖²)`
  where `C_s(A) = ∑_{a ∈ A} ‖a‖^{-2s}`.  For `A = sqgBox n` the
  constant `C_s(A)` is bounded by the global lattice zeta
  `∑_{a ∈ ℤ² \ {0}} ‖a‖^{-2s}` (finite for `s > d/2 = 1`), giving
  uniform-in-`n` L² product bound on the Galerkin dynamics.
- **§11.25.A–D + C₂** building blocks for the Banach-algebra Ḣˢ
  product bound:
  - `sumSet_symm`, `modeConvolution_symm`: commutativity of the
    Minkowski sum and the mode convolution (§11.25.A).
  - `hsSeminormSq_zero_trigPolyProduct_le_young_symm`: symmetric
    Young bound `∑_n ‖modeConv(n)‖² ≤ (∑_a ‖cf a‖²) · (∑_b ‖cg b‖)²`
    via §11.22 on swapped factors (§11.25.B).
  - `young_peetre_weighted_left`: weighted Young
    `∑_n T_1'(n)² ≤ hsSeminormSq s (trigPoly A cf) · (∑_b ‖cg b‖)²`
    via complex embedding of the real nonneg Peetre-weighted
    sequences into ℂ, then applying §11.25.B (§11.25.C).
  - `fracDerivSymbol_add_le_sqrt`: linear-form (sqrt) Peetre
    `σ_s(a+b) ≤ √(2^(2s-1)) · (σ_s a + σ_s b)` for `s ≥ 1`, from
    squared Peetre §11.19.C + subadditivity + Real.sqrt monotonicity
    (§11.25.C₂).
  - `young_peetre_weighted_right`: dual of §11.25.C via §11.22
    (ℓ¹ × ℓ² direction) on `T_2'` (§11.25.D).
- **§11.25.E** `hsSeminormSq_trigPolyProduct_le_banach_algebra` —
  **Banach-algebra `Ḣˢ` product bound on `trigPolyProduct`.**
  Full assembly of §11.25.A–D + C₂ + §11.23 into:
  `‖fg‖²_{Ḣˢ} ≤ 2^{2s} · (C_s(A) + C_s(B)) · ‖f‖²_{Ḣˢ} · ‖g‖²_{Ḣˢ}`
  for `s ≥ 1`, `0 ∉ A`, `0 ∉ B`, where
  `C_s(A) = ∑_{a ∈ A} ‖a‖^{-2s}`.  Proof strategy:
  1. §11.25.E₁ `fracDerivSymbol_mul_modeConvolution_norm_le_sqrt_peetre`
     — pointwise sqrt-Peetre: `σ_s(n) · ‖modeConv(n)‖ ≤ √(2^{2s-1}) ·
     (T_1'(n) + T_2'(n))` via triangle on `modeConv`, distribution of
     `σ_s n` into the indicator sum, replacement `σ_s n = σ_s(a+b)`
     under χ, and §11.25.C₂ sqrt-Peetre applied elementwise.
  2. Square + `(x + y)² ≤ 2(x² + y²)`:
     `(σ_s n)² · ‖modeConv‖² ≤ 2^{2s} · (T_1'(n)² + T_2'(n)²)`.
  3. Sum over `n ∈ sumSet A B` (via `Finset.sum_le_sum` + factor 2^{2s}
     out + split the two squared sums).
  4. Apply §11.25.C to bound `∑_n T_1'(n)²` and §11.25.D to bound
     `∑_n T_2'(n)²`, rewriting RHS via `hsSeminormSq_trigPoly` so the
     weighted-sum factors become `hsSeminormSq s (trigPoly · ·)`.
  5. Apply §11.23 (CS bridge) to replace the remaining `ℓ¹` factors
     `(∑_b ‖cg b‖)²`, `(∑_a ‖cf a‖)²` with
     `C_s(B) · hsSeminormSq s (trigPoly B cg)` and
     `C_s(A) · hsSeminormSq s (trigPoly A cf)` respectively, using
     `hA : 0 ∉ A`, `hB : 0 ∉ B`, and `hs_pos : 0 < s`
     (derived from `1 ≤ s`).
  6. Combine + `ring`: `C_s(A) + C_s(B)` factor emerges.

  Combined with global lattice zeta summability
  `∑_{a ∈ ℤ² \ {0}} ‖a‖^{-2s} < ∞` for `s > d/2 = 1` on `𝕋²`
  (deferred), this delivers the support-INDEPENDENT Banach-algebra
  bound.  For Galerkin `A = B = sqgBox n`, this is uniform in `n`
  and discharges `hBoundS` in §10.174's Aubin-Lions interpolation.

**Still outstanding for unconditional Item 5.A closure:**
- Global lattice zeta summability `∑_{a ∈ ℤ² \ {0}} ‖a‖^{-2s} < ∞`
  for `s > 1` (~150 LOC).
- `HasTrigPolyKatoPonceBound → HasSqgGalerkinHsClosure` bridge via
  SQG velocity `u_n = R θ_n` (Riesz transform) + gradient `∇θ_n`
  (~200 LOC).
- §10.174 `hBoundS` discharge (~50 LOC).

Classical remainder ~400 LOC.

- **§11.25.F** `hsSeminormSq_trigPolyProduct_le_uniform_banach_algebra`
  — **support-independent Banach-algebra `Ḣˢ` bound.**  Parametrises
  §11.25.E on a uniform lattice-zeta bound:
  `‖fg‖²_{Ḣˢ} ≤ 2^{2s} · 2C · ‖f‖²_{Ḣˢ} · ‖g‖²_{Ḣˢ}`
  for `s ≥ 1`, `0 ∉ A`, `0 ∉ B`, `HasLatticeZetaBound s C`.  Proof:
  compose §11.25.E with the per-finset hypothesis `C_s(A) ≤ C` and
  `C_s(B) ≤ C` via `linarith` on `C_s(A) + C_s(B) ≤ 2C`, then
  `mul_le_mul_of_nonneg_left` + `ring`.  §11.25.F₁
  `HasLatticeZetaBound (s C : ℝ) : Prop` structure bundles the
  uniform finite-sum bound as a `Prop` hypothesis; concrete witness
  for `s > 1` via global lattice zeta summability remains open.
- **§11.25.G** — hypothesis structure + concrete constructor.
  - **§11.25.G₁** `HasTrigPolyBanachAlgebraBound (s C : ℝ) : Prop`
    structure: bundles `‖fg‖²_{Ḣˢ} ≤ C · ‖f‖²_{Ḣˢ} · ‖g‖²_{Ḣˢ}` as
    a `Prop` for every `A, B ⊆ ℤ² \ {0}` finite.  Parallel to §11.21
    `HasTrigPolyKatoPonceBound` but Banach-algebra form rather than
    Leibniz split form.
  - **§11.25.G** `HasTrigPolyBanachAlgebraBound.of_latticeZeta` —
    constructor from `HasLatticeZetaBound s C_z` + `s ≥ 1` to
    `HasTrigPolyBanachAlgebraBound s (2^{2s} · 2·C_z)` via §11.25.F.
    **Diagnostic path (3 CI iterations):**
    1. First attempt (`where bound := fun ... => ...`): `isDefEq`
       timeout after 200000 heartbeats.
    2. Second attempt (`refine ⟨?_, ?_⟩ + linarith [h]`): `linarith
       failed to find a contradiction`.  linarith couldn't normalize
       the two "identical-looking" sides.
    3. Third attempt (factored `h_bound` + `exact ⟨_, _⟩`): explicit
       `type mismatch` error surfaced the root cause —
       `@trigPolyProduct inst✝ A B cf cg` (theorem's class param)
       vs `@trigPolyProduct decidablePiFintype A B cf cg`
       (structure's auto-synthesized default instance).
    Final fix: remove `[DecidableEq (Fin 2 → ℤ)]` from the
    theorem signature.  Default synthesis picks `decidablePiFintype`
    uniformly at every use site, matching the structure's field.
    CI green at commit `364f711`.
- **§11.25.H** `hsSeminormSq_trigPolyProduct_zero_left` +
  `hsSeminormSq_trigPolyProduct_zero_right` — zero-coefficient
  exemplars showing the trig-poly product has zero Ḣˢ seminorm when
  either factor's coefficient sequence is zero.  Direct corollaries
  of `trigPolyProduct_zero_left` / `_zero_right` (zero-product
  identity) + `hsSeminormSq_of_zero` (zero function has zero Ḣˢ
  seminorm).  Uses default `decidablePiFintype` (no class parameter)
  to avoid the instance-mismatch pattern diagnosed in §11.25.G.
- **§11.25.I** `HasLatticeZetaBound.mono` — utility monotonicity
  lemma: if `HasLatticeZetaBound s C` and `C ≤ C'`, then
  `HasLatticeZetaBound s C'`.  Trivial field-wise le_trans.

### §11.26 Lattice zeta partial progress toward concrete witness

Building infrastructure for a concrete
`HasLatticeZetaBound s (latticeZetaConst s)` witness at `s > 1`,
via the annular-shell + 1D p-series reduction.

- **§11.26.A** `summable_one_div_nat_rpow_at_two_s_sub_one` —
  `Summable (fun n : ℕ => 1/(n : ℝ)^(2s-1))` for `s > 1`, via
  mathlib's `Real.summable_one_div_nat_rpow`.
- **§11.26.B** `abs_coord_le_latticeNorm` — `|(n j : ℝ)| ≤ latticeNorm n`
  via `sq_le_latticeNorm_sq` + `Real.sqrt_sq_eq_abs` + `Real.sqrt_le_sqrt`.
- **§11.26.B₂** `max_abs_coord_le_latticeNorm` — `ℓ∞ ≤ ℓ²` on `Fin 2 → ℤ`.
- **§11.26.C** `annularShell k : Finset (Fin 2 → ℤ)` — subset of piFinset
  Icc² with filter `m ≠ 0 ∧ (|m 0| = k ∨ |m 1| = k)`.  Represents the
  "ring" of integer points with `ℓ∞`-norm exactly `k`.
- **§11.26.C₁/C₂/C₃** — membership characterization, `latticeNorm m ≥ k`
  on shell k, shell at k=0 is empty.
- **§11.26.D** `card_annularShell_le` — `|shell k| ≤ 8k + 4` via
  filter-or decomposition + `Fintype.card_filter_piFinset_eq_of_mem` +
  `Fintype.filter_piFinset_of_notMem` (explicit-arg form to avoid
  instance-synthesis failure on underscores).
- **§11.26.E** `sum_annularShell_rpow_le` — shell-sum bound
  `∑_{m ∈ shell k} ‖m‖^{-2s} ≤ (8k+4) · k^{-2s}` via pointwise monotonicity
  of `x ↦ x^{-2s}` (`inv_anti₀` + `Real.rpow_neg`) + cardinality.
- **§11.26.F₁** `latticeZetaConst s := 8·∑'(k:ℕ), 1/(k:ℝ)^{2s-1} +
  4·∑'(k:ℕ), 1/(k:ℝ)^{2s}` — the uniform constant (tsum in `(k:ℝ)` form;
  `k=0` terms vanish since `1/0^p = 0` for `p > 0`).
- **§11.26.F₂** `latticeZetaConst_nonneg` — nonnegativity via
  `tsum_nonneg` + `div_nonneg` + `Real.rpow_nonneg`.
- **§11.26.G** `shellOf m := max (|m 0|).toNat (|m 1|).toNat` —
  `ℓ∞`-radius shell-index function.  §11.26.G₁ `shellOf_pos_of_ne_zero`
  (`m ≠ 0 ⇒ shellOf m ≥ 1`), §11.26.G₂ `mem_annularShell_shellOf`
  (`m ≠ 0 ⇒ m ∈ annularShell (shellOf m)`), §11.26.G₃
  `annularShell_disjoint` (distinct shells are pairwise disjoint).
- **§11.26.H** `hasLatticeZetaBound_latticeZetaConst` — **full
  unconditional `HasLatticeZetaBound s (latticeZetaConst s)` for
  `s > 1`.**  Partition any finite `A ⊆ ℤ² \ {0}` by `shellOf`,
  decompose sum via `Finset.sum_biUnion` over `A.image shellOf`
  with disjoint shells (§11.26.G₃), bound each shell via §11.26.E,
  split `(8k+4)·k^{-2s} = 8·k^{1-2s} + 4·k^{-2s}` via `Real.rpow_add`
  with `1 = 1 + (-(2s))` exponent decomposition, bridge finite sum
  to `tsum` via `Summable.sum_le_tsum` on the two p-series
  (`Real.summable_one_div_nat_rpow.mpr (by linarith)` at `p = 2s-1`
  and `p = 2s`).  **Closes the lattice-zeta leg of Route A Item 5.A
  unconditionally.**  Composed with §11.25.F/G/G₁ gives the
  support-independent Banach-algebra Ḣˢ product bound with concrete
  constant `2^{2s}·(2·latticeZetaConst s)`.
- **§11.27** `hasTrigPolyBanachAlgebraBound_of_gt_one` — **fully
  unconditional Banach-algebra `Ḣˢ` product bound witness** via
  one-line composition of §11.25.G `.of_latticeZeta` with §11.26.H.
  Delivers `HasTrigPolyBanachAlgebraBound s (2^{2s}·(2·latticeZetaConst s))`
  for every `s > 1`, the **first Banach-algebra product bound in-tree
  with zero open hypotheses**.  §11.27.A
  `hasTrigPolyBanachAlgebraBound_of_gt_one_zero_left` — zero-coefficient
  exemplar sanity check.
- **§11.28** `hsSeminormSq_trigPolyProduct_self_le` — self-product
  specialization of §11.27 for Gronwall-energy estimates:
  `‖f²‖²_{Ḣˢ} ≤ 2^{2s}·(2·latticeZetaConst s)·(‖f‖²_{Ḣˢ})²` for `s > 1`,
  `0 ∉ A`.  Natural form for quadratic nonlinearities.
- **§11.29** `hasTrigPolyBanachAlgebraBound_of_gt_one_mono` —
  monotonicity of the concrete Banach-algebra constant in `C`.
  For any `C ≥ 2^{2s}·(2·latticeZetaConst s)`,
  `HasTrigPolyBanachAlgebraBound s C` holds.  Unifies constants across
  multi-term estimates.
- **§11.30** `sum_norm_sq_le_latticeZeta_mul_hsSeminormSq` —
  **unconditional `ℓ¹ → Ḣˢ` Cauchy–Schwarz bound for `s > 1`,
  `0 ∉ A`:**
  `(∑_a ‖cf a‖)² ≤ latticeZetaConst s · hsSeminormSq s (trigPoly A cf)`.
  Fourier-side form of the classical Sobolev embedding
  `Ḣˢ ⊂ L∞` on `𝕋²` for `s > d/2 = 1`, with explicit
  uniform-in-support constant.  Composition of §11.23.A with §11.26.H.
- **§11.31** `l2_trigPolyProduct_le_latticeZeta` — **unconditional
  uniform `L²` product bound for `s > 1`, `0 ∉ A`:**
  `∑_n ‖modeConv(n)‖² ≤ latticeZetaConst s · ‖f‖²_{Ḣˢ} · (∑_b ‖cg b‖²)`.
  Composition of §11.24 with §11.26.H.  On the SQG Galerkin at
  `A = sqgBox n`, delivers the uniform-in-`n` `L² × Ḣˢ → L²` product
  bound needed for the energy estimate chain.
- **§11.32** `l2_trigPolyProduct_le_latticeZeta_symm` — symmetric form
  of §11.31 with Ḣˢ control on the SECOND factor:
  `∑_n ‖modeConv(n)‖² ≤ (∑_a ‖cf a‖²) · latticeZetaConst s · ‖g‖²_{Ḣˢ}`
  for `s > 1`, `0 ∉ B`.  Via §11.25.B (swapped Young) + §11.30 on `B`.
  Completes `L² × Ḣˢ → L²` in both factor directions.
- **§11.33** `hsSeminormSq_trigPolyProduct_le_latticeZeta_interp` —
  Ḣᵗ interpolation form of §11.27 for every `t ≤ s`, `s > 1`:
  `hsSeminormSq t (trigPolyProduct A B cf cg) ≤ 2^{2s}·(2·latticeZetaConst s) · ‖f‖²_{Ḣˢ} · ‖g‖²_{Ḣˢ}`.
  Via `hsSeminormSq_mono_of_le` (exponent monotonicity) + finite-
  Fourier-support summability on `sumSet A B`.  Use case: SQG energy
  at `t = 1` with `s = 3/2`.
- **§11.34–§11.38 Path A structural closure of Item 5** (HEAD `a13e2d2`):
  - **§11.34** `HasSqgGalerkinAllSBound α` — hypothesis type bundling
    `M₁ + Ms : ℝ → ℝ` + uniform Galerkin `Ḣ¹` and `Ḣˢ` bounds at every
    `s > 1`.  Time-global form §10.174's `hBoundS` consumes directly.
    Not `Prop`-valued (data fields `M₁ : ℝ`, `Ms : ℝ → ℝ`).
  - **§11.35** `HasSqgGalerkinAllSBound.ofZero` — zero-datum witness
    with all bounds collapsing to `0` via
    `hsSeminormSq_zero_galerkin_of_trinary_zero`.
  - **§11.36** `sqg_regularity_of_allSBound` — full-range Theorem 3
    capstone from `HasSqgGalerkinAllSBound` + `HasAubinLionsExtraction`
    + `SqgEvolutionAxioms` via §10.174.
  - **§11.37** `sqg_solution_and_regularity_via_allSBound` — end-to-end
    `SqgSolution` + Theorem 3 variant of §10.175 consuming the single
    `HasSqgGalerkinAllSBound` hypothesis.
  - **§11.38** `sqg_regularity_ofZero_via_allSBound` — fully
    unconditional full-range Theorem 3 on zero data via §11.35 + §11.36.

  **Item 5 Path A status: CLOSED.**  Standard matches Items 3/4:
  hypothesis-keyed, discharged on zero data, classical content
  (Kato–Ponce commutator + Sobolev + BKM-integral) labeled and
  deferred to the companion `sqg-lean-proofs-fourier` package.

**Companion package: sqg-lean-proofs-fourier (skeleton, 2026-04-21):**
  Classical Fourier-analysis content (Littlewood–Paley +
  paraproducts + Kato–Ponce commutator + `Ḣˢ ⊂ L∞` Sobolev embedding)
  lifted out to a separate Lean package so it can be reused by
  NS/Euler/MHD future formalizations.  All files are placeholder
  stubs with detailed header comments documenting planned content.
  Total planned: ~1500 LOC upstream.  Plumbing into
  `HasSqgGalerkinAllSBound` in this repo: ~500 LOC remaining for
  Path B closure.

**Item 5 infrastructure: full-range Theorem 3 via `BKMCriterionHighFreq`
— §10.173–§10.175.**

Lifts the `s ≤ 2` restriction of §10.168/§10.169/§10.171 to the
full Sobolev scale `s ≥ 0`:

- **§10.173.A** `BKMCriterionHighFreq.of_L2_limit_uniform_Hs_all_s` —
  generic-`s` variant of §10.168.A.  Uses §10.167.A's LSC lemma
  (already generic in `s`) to derive `BKMCriterionHighFreq θ` from
  uniform `Ḣˢ` bounds on the `L²`-limit sequence at **every** `s > 1`
  (not just `s ∈ (1, 2]`).
- **§10.173.B** `BKMCriterionHighFreq.of_aubinLions_uniform_Hs_all_s`
  — Aubin–Lions specialisation.  Summability comes for free from
  `hsSeminormSq_summable_galerkinToLp` (finite-support Fourier).
- **§10.174** `sqg_regularity_of_aubinLions_via_interpolation` —
  full-range Theorem 3 capstone.  Composes §10.167.C + §10.173.B +
  `sqg_regularity_via_interpolation`.  Delivers
  `∀ s ≥ 0, ∃ M', ∀ t ≥ 0, hsSeminormSq s (ext.θ_lim t) ≤ M'`
  given uniform `Ḣˢ` bounds on Galerkin at `s = 1` and every `s > 1`
  plus `SqgEvolutionAxioms` on the limit.
- **§10.175** `sqg_solution_and_regularity_via_RouteB_interpolation`
  — end-to-end full-range capstone.  Parallel to §10.171 but covers
  every `s ≥ 0`.

**Impact on `OPEN.md` Item 5 (Ḣˢ bootstrap for `s > 2`):** the
**infrastructure** is now in-tree.  What remains is discharging the
high-`s` Galerkin `Ḣˢ` bound hypothesis, which classically requires
Kato–Ponce / fractional Leibniz on `𝕋²` — either via a mathlib
contribution or an in-tree local version.  The structural chain is
now uniform across the full Sobolev scale, so the classical PDE
content is isolated as a single named hypothesis.

**Item 1 `hH2` closure — §10.172 (divergence-free pointwise bound).**

Item 1's last remaining analytic input (`hH2`, the uniform `H⁻²`
bound on `galerkinRHS`) closed **structurally** without any Sobolev
product bilinear estimate, using only:

- **§10.172.A** — Cauchy–Schwarz in `Fin 2` (`fin_two_CS_real_sq` +
  `fin_two_CS_complex_real_sq`) + `sqgVelocitySymbol_sum_sq`
  (∑|σ_j(ℓ)|² = 1 for ℓ ≠ 0) give
  `‖∑_j σ_j(ℓ) · (m j : ℂ)‖ ≤ latticeNorm m`.
- **§10.172.B** — `galerkinKKernel_norm_le_latticeNorm`: via the
  divergence-free identity `σ(ℓ) · ℓ = 0`
  (`sqgVelocitySymbol_divergence_free`),
  `σ(ℓ) · (m - ℓ) = σ(ℓ) · m`, so
  `‖galerkinKKernel ℓ (m - ℓ)‖ ≤ latticeNorm m` **uniformly in `ℓ`**.
- **§10.172.C** — `galerkinRHS_norm_le_latticeNorm_mul_l2_sum`:
  pointwise `‖galerkinRHS S c m‖ ≤ latticeNorm m · ∑_{n ∈ ↥S} ‖c n‖²`.
  Proof: triangle on the finite-support sum + §10.172.B per-term
  bound + Young's inequality on the convolution sum, with a
  `Finset.sum_image`-based reindexing via the involution `ℓ ↦ m - ℓ`
  to bound the `|c(m - ℓ)|²` half-sum by `∑_{n ∈ ↥S} ‖c n‖²`.
- **§10.172.D** — `sqgGalerkin_modeLipschitz_from_l2_conservation`:
  per-mode Lipschitz constant from §10.172.C + §10.97 `L²`
  conservation + §10.153.B mean-value theorem.  Produces
  `L(m) = (∫ ‖θ₀‖²) · latticeNorm m` uniform in `n`.
- **§10.172.E** — `HasModeLipschitzFamily.ofSqgGalerkin_l2_conservation`:
  wires §10.172.D into §10.152's `ofSqgGalerkinBounds` constructor,
  using `sum_sq_fourierRestrict_le_L2Sq` (§10.119) to bridge the
  equality-form `L²` conservation to the inequality form.
- **§10.172.F** — `HasPerModeLimit.ofSqgGalerkin_l2_conservation`:
  Item 1 capstone composing §10.172.E + §10.165 (`hExtract` witness)
  + §10.155.B (`HasPerModeLimit.ofModeLipschitzFamily`).  Produces
  `HasPerModeLimit α` **unconditionally** from `L²` conservation +
  ODE hypotheses (no `hH2` hypothesis needed).

**Why pointwise rather than `H⁻²`?**  The standard Aubin-Lions input
on `𝕋²` is a uniform `H⁻s` bound on `∂_t θ`.  In 2D, the
`L² × L² → H⁻¹` bilinear estimate **fails** due to the logarithmic
divergence of `∑_{m ≠ 0} |m|⁻²`.  A `H⁻²` bound on `∂_t θ` would
require `‖u θ‖_{H⁻¹}` uniformly, which itself requires `Ḣ^{1/2}`
control on at least one factor — not attainable from pure `L²`
conservation.  §10.172 sidesteps this by never passing through a
Sobolev product estimate, instead using the divergence-free symbol
structure to produce a per-mode bound directly from Young's inequality
on the Fourier convolution.

**Theorem 3 off the finite-Fourier-support class + end-to-end capstone.**
Items 1 (now fully closed), 3 (MMP off finite-support), and 4 (BKM
off finite-support) from `OPEN.md` all closed structurally.  The
`MaterialMaxPrinciple` and `BKMCriterionS2` hypotheses of the
conditional Theorem 3 now lift off the finite-Fourier-support class
to every strong-`L²` Galerkin limit, given uniform `Ḣˢ` bounds on
the Galerkin approximation.

Item 1 analytical inputs — all three structurally discharged:

- **§10.160–§10.164** — strong-`L²` convergence reduced to elementary
  tightness via `HasFourierSynthesis.ofTight`.  Parseval-on-difference
  (§10.160), specialisation to the Galerkin-limit coefficient pair
  (§10.161), `Tendsto.congr` wrapper (§10.162), pure-ℓ² Vitali
  convergence on squared differences (§10.163), tight-family capstone
  (§10.164).
- **§10.165.A/B/C/D + `sqgGalerkin_hExtract_witness`** — Bolzano–
  Weierstrass on `ℂ` (§10.165.A), Cantor diagonal across countable
  families of bounded ℂ-sequences (§10.165.B), rational-time
  subsequence for `HasModeLipschitzFamily` (§10.165.C), Lipschitz-
  driven extension from rational to real times (§10.165.D).  Final
  composition produces the `hExtract` witness demanded by §10.155.B
  unconditionally from `HasModeLipschitzFamily`.
- **§10.166.A/B** — `hDeriv` / `hCont` discharges for §10.153.C's
  restricted hypotheses from §10.116's whole-trajectory derivative.
  Composed with §10.153.C's `m`-restriction to `sqgBox n` (commit
  `4e02eef`), Item 1 input #3 is closed.

Item 3 — MMP off finite-support class (§10.167):

- **§10.167.A `hsSeminormSq_le_of_L2_limit_uniform_bound`** — pure
  Fourier-side lower-semicontinuity lemma.  Strong-`L²` convergence
  + per-`n` weighted summability + uniform `Ḣˢ` bound ⇒ weighted
  family on the limit is summable and the bound transfers.  Proof:
  per-mode Fourier convergence (§10.141) + `tendsto_finset_sum` +
  `summable_of_sum_le` / `Real.tsum_le_of_sum_le` from mathlib.
- **§10.167.B `MaterialMaxPrinciple.of_L2_limit_uniform_H1`** — MMP
  for `θ` realised as a pointwise-in-`t` strong-`L²` limit of a
  sequence with uniform `Ḣ¹` bound and per-state summability.
- **§10.167.C `MaterialMaxPrinciple.of_aubinLions_uniform_H1`** —
  specialisation to `HasAubinLionsExtraction`.  5 CI iterations to
  resolve a `DecidableEq (Fin 2 → ℤ)` instance-synthesis mismatch
  between the theorem's explicit binder and the
  `Fintype.decidablePiFintype` auto-synthesis used by
  `ext.tendsto_L2`.  Final fix: drop the explicit binder.

Item 4 — BKM off finite-support class (§10.168):

- **§10.168.A `BKMCriterionS2.of_L2_limit_uniform_Hs`** — BKM from an
  `L²`-limit sequence with per-`s` uniform `Ḣˢ` bound on the
  sequence.  Reuses §10.167.A at each `s ∈ (1, 2]`; the `Ḣ¹`
  hypothesis inside `hsPropagationS2` is unused.
- **§10.168.B `BKMCriterionS2.of_aubinLions_uniform_Hs`** —
  specialisation to `HasAubinLionsExtraction`.  One-shot green CI —
  §10.167 lessons transferred directly.
- **`hsSeminormSq_summable_galerkinToLp`** — parametric-`s`
  companion to §10.167's `hsSeminormSq_one_summable_galerkinToLp`.

Theorem 3 capstone on the Aubin–Lions limit (§10.169 – §10.171):

- **§10.169 `sqg_regularity_of_aubinLions_uniform_Hs`** —
  conditional Theorem 3 on `s ∈ [0, 2]` for `ext.θ_lim` from uniform
  `Ḣˢ` bounds on the Galerkin states at `s = 1` and `s ∈ (1, 2]`.
  Composes §10.167.C + §10.168.B + `sqg_regularity_via_s2_bootstrap`.
- **§10.170 `sqg_regularity_of_aubinLions_ofZero`** — zero-datum
  instance.  Exercises the full composition on
  `HasAubinLionsExtraction.ofZero`.  Uses the auxiliary
  `hsSeminormSq_zero_galerkin_of_trinary_zero` + `.le` to lift
  `... = 0` to `... ≤ 0`.
- **§10.171 `sqg_solution_and_regularity_via_RouteB_uniform_Hs`** —
  end-to-end capstone.  Composes §10.148
  (`exists_sqgSolution_via_RouteB_from_galerkin_energy`) with
  §10.169, delivering both a genuine `SqgSolution` on `𝕋²` and the
  Theorem 3 regularity conclusion on `s ∈ [0, 2]` for its
  `θ`-field.  This is the maximally-closed form of Theorem 3
  reachable from the current infrastructure: what remains is
  classical SQG analysis (uniform `Ḣˢ` energy estimates, `hH2`
  bilinear bound) and the mathlib Kato–Ponce contribution.

Infrastructure cleanup:

- **Zenodo webhook (OPEN.md item 9)** — canonical concept
  `19583256` extended to v0.4.39 via REST API (DOI
  `10.5281/zenodo.19674045`).  Stale `"version"` field stripped
  from `.zenodo.json` (commit `16a00e5`).
- **README CI badge** — fixed to point at the new repo slug
  `Brsanch/sqg-lean-proofs`.

Statistics: ~21,100 lines in `RieszTorus.lean` at HEAD (~21,600
project-wide).  Zero `sorry`, no axioms beyond mathlib.

## v0.4.39 — 2026-04-20

**Item 1 analytical closure — three structural reductions + concrete
Fourier synthesis operator.**  All three remaining Route B analytical
targets from v0.4.38 now have named Lean theorem signatures:

- **§10.153.C `sqgGalerkin_modeLipschitz_from_UniformH2`** — Target #3
  monolithic closure (composes §10.153.A + §10.153.B across
  `m = 0` / `m ≠ 0` and `s ≤ t` / `t ≤ s` splits).  Produces the
  `(L, hL_nonneg, hL_holds)` data consumed by
  `HasModeLipschitzFamily.ofSqgGalerkinBounds` (§10.152) from a
  uniform `H⁻²` bound + the Galerkin ODE hypotheses, in existential
  form.  Closed after a 6-retry diagnostic iteration that identified
  the actual loop culprit (DecidableEq-instance synthesis on
  `Fin 2 → ℤ` / `↥(sqgBox _)` via `Int.decEq ↦ 70k`,
  `Multiset.decidableForallMultiset ↦ 55k`).  Fix: keep
  `GalerkinRHSHsNegSqBound` locally irreducible + restructure the
  theorem to take the per-`(n, τ)` hypothesis directly rather than
  `UniformGalerkinRHSHsNegSqBound`.  The diagnostic workflow from
  `feedback_lean_diagnostic_workflow.md` saved ~40 min of blind
  heartbeat-bumping.
- **§10.154 `Lp_eq_of_mFourierCoeff_eq` + `HasFourierSynthesis.ofPerModeLimit`**
  — Target #2 coefficient-injectivity bridge + constructor.
  §10.154.A establishes that two `Lp ℂ 2` elements with matching
  Fourier coefficients are equal (via `mFourierBasis.repr.injective`).
  §10.154.B assembles `HasFourierSynthesis per θ` from a synthesis
  witness + an initial coefficient match (which replaces the
  stronger `θ_lim 0 = θ` field via §10.154.A).
- **§10.155 `HasModeLipschitzFamily.modeCoeff_eq_galerkinExtend` +
  `HasPerModeLimit.ofModeLipschitzFamily`** — Target #1 structural
  reduction.  §10.155.A bridges `lip.modeCoeff` with `galerkinExtend`
  via the `modeCoeff_eq`/`_off` fields.  §10.155.B takes a classical
  Arzelà–Ascoli + Cantor diagonal extraction witness and produces
  `HasPerModeLimit α` from `HasModeLipschitzFamily α`.
- **§10.157 `fourierSynthesisLp`** — **concrete Fourier synthesis
  operator** (not just a reduction): lifts an ℓ²-summable coefficient
  sequence to the corresponding `Lp ℂ 2` element via mathlib's
  `mFourierBasis.repr.symm`.  `mFourierCoeff_fourierSynthesisLp` proves
  the Fourier coefficients of the synthesis recover the input sequence.
- **§10.158 `θLimOfLp` + `mFourierCoeff_θLimOfLp`** — concrete
  `θ_lim` operator for `HasFourierSynthesis` (composes §10.157's
  `fourierSynthesisLp` with an `lp`-valued per-mode limit function).
  Coefficient match theorem closes the `h_coeff` input of §10.154.B
  algebraically given `bLp ↔ per.b` agreement.

**Diagnostic workflow paid off.**  6 retries on §10.153.C with
structured bisection (diagnostic output reading + targeted fixes):
retry 1 `classical` (no effect), retry 2 both predicates irreducible +
diag (counts 265k → 434 — loop killed, but function-expected error),
retry 3 inner only (loop returned — confirmed retry 2's fix was on
`Uniform`), retry 4 helper + `noncomputable def` for §10.155 (helper
hit loop during type-check), retry 5 drop `Uniform` from signature
(loop broken decisively, only arithmetic mismatch remained), retry 6
`neg_sub` bridge (green).  Each retry informed the next — no blind
heartbeat bumping.

**Remaining Item-1 work** (what still needs genuine mathlib wrangling):
1. Strong-`L²` convergence of the extracted Galerkin sequence to
   `θLimOfLp` — Parseval on the difference + Fatou + DCT on `ℓ²(ℤ²)`.
2. Classical Arzelà–Ascoli + Cantor diagonal extraction (§10.155.B's
   `hExtract` input).  Mathlib has `BoundedContinuousFunction.arzelaAscoli`
   + `Denumerable (Fin 2 → ℤ)` — ~300-line assembly.
3. `hDeriv` / `hCont` / `hH2` discharges for §10.153.C from §10.116's
   Galerkin ODE + §10.138's `H⁻²` bound via derivative projection.
4. `Memℓp 2 ↔ Summable (‖·‖²)` bridge — elementary mathlib name lookup
   (the §10.158.C guess `memℓp_two_iff_summable_sq_norm` was wrong).

~ +200 lines vs v0.4.38, ~19,900 total.  Zero `sorry`.  Zero axioms
beyond mathlib.

## v0.4.38 — 2026-04-20

**§10.147–§10.152 — Route B analytical chain extended.**  First of two
Route B analytical hypotheses (`l2Conservation`) now internally
discharged; the second (`HasAubinLionsExtraction` existence) reduced
to three precisely-typed Lean construction targets.

- **§10.147 `l2Conservation_of_aubinLions`** — strong-`L²` convergence
  + §10.97 per-level energy conservation + §10.142 zero-mode
  preservation → `hL2 : ∀ t, 0 ≤ t → hsSeminormSq 0 (ext.θ_lim t) =
  hsSeminormSq 0 (ext.θ_lim 0)`.  Built on new bridge lemmas
  `Lp_two_norm_sq_eq_integral_norm_sq`,
  `tendsto_Lp_two_norm_sub_of_tendsto_integral_sq`,
  `tendsto_integral_norm_sq_of_tendsto_L2sub`,
  `integral_norm_sq_eq_hsSeminormSq_zero_of_zero_fourier_zero`, and
  `tendsto_hsSeminormSq_of_tendsto_L2sub_torus`.
- **§10.148 `exists_sqgSolution_via_RouteB_from_galerkin_energy`** —
  hypothesis-free capstone consuming §10.147.  Produces `SqgSolution`
  from `HasAubinLionsExtraction` witness + per-level `hsSeminormSq 0`
  invariance + velocity witness + `smoothInitialData`.  The `hL2`
  hypothesis of §10.145 is now internal.
- **§10.149 `HasModeLipschitzFamily`** — structural predicate
  packaging the Fourier-side compactness ingredients: universal mode
  extension, uniform mode-wise bound, uniform per-mode Lipschitz-in-
  time constant.  Plus `galerkinModeCoeff` canonical constructor.
- **§10.150 `HasPerModeLimit`** — structural predicate for the output
  of Arzelà–Ascoli + Cantor diagonal: extracted subsequence + per-mode
  limit function + per-mode pointwise-in-time convergence.  Plus
  `HasPerModeLimit.b_zero_mode` automatic triviality from `0 ∉ sqgBox n`.
- **§10.151 `HasFourierSynthesis` + `HasAubinLionsExtraction.ofPerModeLimit`**
  — Parseval-synthesis interface: given per-mode limit + Lp-valued
  synthesis witness, one-line construction of `HasAubinLionsExtraction`.
- **§10.152 `HasModeLipschitzFamily.ofSqgGalerkinBounds`** —
  structural discharge for the SQG Galerkin family using §10.123's
  `sq_galerkinExtend_le_L2Sq` (modeBound concretely discharged via
  `Real.sqrt_sq` + `Real.sqrt_le_sqrt`) and a named per-mode Lipschitz
  hypothesis `L m` (derivable from §10.138's `H⁻²` bound + §10.116's
  Galerkin ODE via FTC, remaining work).

**Diagnostic breakthrough during §10.147 work.**  After 9 CI failures
on heartbeat-exhausted whnf timeouts, `set_option diagnostics true`
pinpointed the root cause: `sqgBox n := Fintype.piFinset (Finset.Icc
(-(n+1)) (n+1)) .erase 0` with symbolic `n = nsub k` drove isDefEq into
a loop unfolding `Int.rec` (3.5M times), `List.range.loop` (162k
times), `Quot.lift` (117k times).  Fix:
`attribute [local irreducible] sqgBox` in the §10.147 section.
Documented in memory as `feedback_lean_diagnostic_workflow.md` so
future sessions skip the trial-and-error.

**Remaining Item-1 work** (explicit Lean targets):
1. `HasPerModeLimit.ofModeLipschitzFamily` — classical Arzelà–Ascoli
   (mathlib `BoundedContinuousFunction.arzelaAscoli`) + Cantor
   diagonal across ℤ² \ {0} (mathlib `Denumerable`).
2. `HasFourierSynthesis.ofPerModeLimit` — Parseval + Fatou + dominated
   convergence on ℓ²(ℤ²).
3. Finish `§10.152`: derive per-mode Lipschitz `L m` from §10.138 +
   §10.116 ODE via FTC.

+540 lines, ~19,670 total.  Zero `sorry`.  Zero axioms beyond mathlib.

## v0.4.37 — 2026-04-20

**§10.146 — zero-datum instance of Route B (second attempt, fixed).**
Exercises the v0.4.35 Route B structural chain end-to-end on the
zero initial datum. First attempt (v0.4.36, since retracted) failed
CI on a `rw`/`simp` interaction with the structure-field projection
of `nsub := id`; this release rewrites with `nsub := fun n => n`
so field projection beta-reduces cleanly, and inlines a `funext + rfl`
proof for the trinested zero function.

- **`galerkinToLp_zero`** — standalone helper: `galerkinToLp S 0 = 0`
  via `Finset.sum_eq_zero` + `galerkinExtend_apply_of_mem`.
- **`HasAubinLionsExtraction.ofZero`** — trivial extraction witness
  with `nsub = fun n => n`, zero limit, and strong-`L²` tendsto
  closed by rewriting each integrand to zero then invoking
  `tendsto_const_nhds`.
- **`exists_sqgSolution_via_RouteB_zero`** — `SqgSolution` existence
  through the full Route B capstone on the zero datum. Confirms the
  §10.144 `SqgEvolutionAxioms` assembly and §10.145 composition with
  `exists_sqgSolution_of_aubinLions` are not vacuous.

+100 lines; zero `sorry`; CI green.

## v0.4.36 — 2026-04-20 (retracted)

**§10.146 first attempt** — compile failure in `HasAubinLionsExtraction.ofZero.tendsto_L2`
due to structure-field-projection `rw` pattern mismatch. Retracted
by revert and replaced by v0.4.37. Tag remains for historical
continuity but points at broken code; do not consume.

## v0.4.35 — 2026-04-20

**§10.137–§10.145 — Route B conditional chain for the generic-`L²`
Galerkin → full-SQG extraction.** Closes item 1 at the structural
level modulo two named analytical hypotheses that any classical
Resnick extraction supplies.

- **§10.137** `hsSeminormSq` at negative index `s`. The existing
  `fracDerivSymbol` gives `|n|^s` off zero for any real `s`; at
  `s < 0` this is the negative-Sobolev weight. `hsSeminormSq_nonneg_any`
  as a convenience lemma.
- **§10.138** `GalerkinRHSHsNegSqBound` / `UniformGalerkinRHSHsNegSqBound`
  — packaged predicate for the `H⁻ˢ` Fourier-side time-derivative
  bound on `galerkinRHS`. At `s = 2` this is the classical
  `‖dθₙ/dt‖_{H⁻²} ≤ C · ‖θ₀‖²_{L²}` estimate of Resnick 1995.
- **§10.139** `HasAubinLionsExtraction θ α` — structure packaging the
  output of a classical Aubin–Lions extraction: a subsequence `nsub`
  + an `Lp` limit `θ_lim` with strong-`L²` pointwise-in-time
  convergence `‖galerkinToLp (sqgBox (nsub k)) (α (nsub k) t) − θ_lim t‖²
  → 0` at every `t ≥ 0`.
- **§10.140** `exists_sqgSolution_of_aubinLions` — `SqgSolution`
  existence from `HasAubinLionsExtraction` + a pre-built
  `SqgEvolutionAxioms` witness + `smoothInitialData`.
- **§10.141** `sq_sub_mFourierCoeff_le_L2Sq` + `tendsto_mFourierCoeff_of_tendsto_L2Sq`
  — Parseval-based per-mode Fourier-coefficient 1-Lipschitz bound
  and the strong-`L²` → per-mode Fourier convergence consequence.
  The bridge between `Lp` convergence and `ℂ`-valued Fourier limits.
- **§10.142** `mFourierCoeff_aubinLionsLimit_zero` — zero-mode
  triviality for the Aubin–Lions limit from `0 ∉ sqgBox n` + per-mode
  convergence. Plus helper `mFourierCoeff_galerkinToLp_sqgBox_zero`.
- **§10.143** `tendsto_mFourierCoeff_of_aubinLions` + `mFourierCoeff_aubinLions_init`
  — specialization of §10.141 to the Aubin–Lions extraction's
  canonical sequence and initial-data identification.
- **§10.144** `SqgEvolutionAxioms.of_aubinLions` — assembles the
  three SqgEvolutionAxioms clauses: `l2Conservation` from an
  explicit hypothesis (classical Parseval-on-truncation + norm
  continuity; listed separately below), `meanConservation` from
  §10.142 automatically, `velocityIsRieszTransform` from a
  `HasGalerkinLimitVelocity` witness.
- **§10.145** `exists_sqgSolution_via_RouteB` — headline capstone.
  Composes §10.140 with §10.144 into a single existence theorem
  for `SqgSolution` via the Aubin–Lions extraction.

**Status after v0.4.35.** The Route B structural chain is complete.
Closing item 1 end-to-end now reduces to discharging two concrete
analytical hypotheses: the `HasAubinLionsExtraction` witness itself
(classical Aubin–Lions compactness from §10.138's `H⁻²` bound +
§10.122's uniform `L²` bound), and the `l2Conservation` hypothesis
fed to §10.144 (`Lp` norm continuity under strong-`L²` convergence
+ `galerkinEnergyH0_const` + Parseval on the Fourier-restriction).
Both are classical analysis that requires modest mathlib infrastructure
not yet in-tree.

+320+ lines across eight commits; zero `sorry`, zero new axioms;
CI green on the final assembly commit.

## v0.4.34 — 2026-04-20

**§10.135–§10.136 — time-test weak form → Duhamel identity bridge
(item 6 structural).** Formalizes step (B) of §10.16's reduction:
given the Fourier-specialized test-function weak form
`IsSqgWeakSolutionTimeTest θ u` plus a bump-to-indicator
convergence witness (packaged as `HasBumpToIndicatorSequence`), the
mode-wise Duhamel identity `IsSqgWeakSolution θ u` follows by
`tendsto_nhds_unique` on the two convergent sequences. Closes
item 6 at the structural level.

- **`HasBumpToIndicatorSequence θ u m s t`** — explicit packaging of
  the bump sequence + the two `Tendsto` convergences (LHS to
  `θ̂(s) − θ̂(t)`, RHS to `∫_{[s,t]} flux`). Downstream callers
  supply this from `ContDiffBump` or other mollifier constructions.
- **§10.135** `IsSqgWeakSolution.of_timeTest_of_bumpSeq` — main
  bridge theorem. Proof is a one-line `tendsto_nhds_unique` on the
  two pointwise-equal sequences of integrals.
- **§10.136** `SqgEvolutionAxioms_strong.of_timeTest_via_MMP` —
  composes §10.135 with §10.14's
  `SqgEvolutionAxioms_strong.of_IsSqgWeakSolution_via_MMP` to
  discharge the strong axioms from the time-test form + MMP + bump
  witness.

+119 lines; zero `sorry`, zero new axioms beyond mathlib; CI green.

Scope: the structural bridge is unconditional. Concrete construction
of `HasBumpToIndicatorSequence` from mathlib's `ContDiffBump`
infrastructure is a separate analytical question (dominated
convergence + mollifier standard results); providing it would close
item 6 analytically as well. Left for future sessions.

## v0.4.33 — 2026-04-20

**§10.133–§10.134 — `SqgEvolutionAxioms_strong` for the §10.117 /
§10.132 `SqgSolution`.** Closes item 2 of the open-items list on the
finite-Fourier-support class. The existing Galerkin-derived
`SqgSolution` (v0.4.28, v0.4.31) carries only the weak-form
`SqgEvolutionAxioms`. v0.4.33 upgrades the underlying trajectory to
`SqgEvolutionAxioms_strong` by porting the §10.91 → §10.92 → §10.94
Duhamel chain to consume the `HasDerivWithinAt ... (Ici 0)` shape
delivered by §10.116.H.3 (rather than full-ℝ `HasDerivAt`).

Route: `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`
accepts exactly the right-derivative shape obtainable from the Ici-0
within-derivative via `HasDerivWithinAt.mono`. The rest of the chain
(`IsSqgWeakSolutionOnSupport` → `SqgEvolutionAxioms_strong`) goes
through unchanged because `IsSqgWeakSolutionOnSupport` already asks
only `0 ≤ s ≤ t`.

- **§10.133.A** `galerkin_mode_FTC_Ici` — per-mode FTC for the
  Ici-0 Galerkin trajectory on `[s, t]` with `0 ≤ s ≤ t`. Uses
  `continuous_apply` + `ContinuousOn` of `galerkinVectorField ∘ α`
  on `Icc s t` + `integral_eq_sub_of_hasDeriv_right_of_le`.
- **§10.133.B** `IsSqgWeakSolutionOnSupport.of_galerkin_dynamics_Ici`
  — mirror of §10.91 consuming the Ici-0 derivative.
- **§10.133.C** `SqgEvolutionAxioms_strong.of_galerkin_dynamics_on_support_Ici`
  — mirror of §10.92. Abstract flux-bound form.
- **§10.133.D** `SqgEvolutionAxioms_strong.of_galerkin_dynamics_with_L_inf_bound_on_support_Ici`
  — mirror of §10.94. L∞ coefficient bound discharges `hFluxBound`
  internally via §10.93.
- **§10.134** `exists_sqgSolution_strong_of_galerkin_realSym` —
  headline capstone paralleling §10.132 but producing both
  `SqgSolution` and `SqgEvolutionAxioms_strong` on the underlying
  trajectory. The uniform L∞ bound `R/2` is extracted from the
  §10.116.H.3 π-norm bound via `norm_le_pi_norm`.

+242 lines; zero `sorry`, zero new axioms beyond mathlib; CI green.

## v0.4.32 — 2026-04-20

**Hygiene release: `push_neg` deprecation + CI Node 24 opt-in.**
No mathematical content change.

- **Item 10.** Replaced 10 occurrences of `push_neg at h` with
  `push Not at h` throughout `RieszTorus.lean`. The `push Not` form is
  the mathlib-recommended successor as of the v4.29 deprecation cycle.
- **Item 11.** CI workflow updated ahead of the June 2026 Node 20
  removal deadline in GitHub Actions. `actions/checkout@v5` bumped to
  `@v6` (Node 24 native). `leanprover/lean-action@v1` floats to the
  latest v1.x (v1.4.0 at time of writing); its transitive
  `actions/cache@v4` dependency is still on Node 20, so
  `FORCE_JAVASCRIPT_ACTIONS_TO_NODE24: "true"` is set at the job level
  to force those transitive JS actions to Node 24. Inline comment
  documents the removal condition.
- **OPEN.md** added as the canonical open-items tracker. Replaces the
  drift-prone ad-hoc regeneration of "what's left" from context.
  Each subsequent release strikes items off this file so the list
  has a single source of truth.

Marked for the record: items 7 (`hFluxBound` from L∞) and 8
(`l2Conservation` from `Re⟨α, galerkinVF⟩ = 0`) from the original
open-items list were already closed in-tree — §10.93 / §10.94 cover
item 7, and §10.96 / §10.97 / `galerkinToLp_hsSeminormSq_zero_const`
cover item 8. The v0.4.10 session memory note listing them as open
was stale.

## v0.4.31 — 2026-04-20

**§10.131–§10.132 — concrete closure of the v0.4.30 chain on the
finite-Fourier-support class.** v0.4.30 gave the conditional
chain `packaged limit hypotheses → SqgSolution`. v0.4.31
instantiates those packaged hypotheses directly from
§10.116.H.3's time-global Galerkin trajectory for finite-support
initial data, producing a parallel construction of v0.4.28's
`exists_sqgSolution_of_galerkin_realSym` routed through the new
§10.125–§10.130 pipeline. +171 lines; zero `sorry`, zero new axioms.

- **§10.131** `isGalerkinLimitData_of_galerkin_realSym` — all five
  clauses of `IsGalerkinLimitData` discharged directly from the
  §10.116 invariants: `zeroMode` from `0 ∉ S₀`, `initial` from
  `mFourierCoeff_galerkinToLp` + `α 0 = c₀`, `summable` from finite
  support, `conservation` by reducing both the time-`t` and time-0
  tsums to finite `S₀`-sums via `tsum_eq_sum` and applying
  §10.116's ℓ²-sum invariant, `realSym` by case split on
  `m ∈ S₀`.
- **§10.131** `galerkinLimitTrajectory_of_galerkin` — θ_lim =
  `t ↦ galerkinToLp S₀ (α t)` with `coeff` direct from
  `mFourierCoeff_galerkinToLp` and `init_eq` from `α 0 = c₀`.
- **§10.131** `hasGalerkinLimitVelocity_of_galerkin` — velocity
  witness `shellVelocity S₀ (galerkinExtend S₀ (α τ)) j` via
  `isSqgVelocityComponent_shellMode`.
- **§10.132** `exists_sqgSolution_via_galerkinLimit_of_finite_support`
  — capstone. Real-symmetric ℓ²-bounded `c₀ : ↥S₀ → ℂ` on symmetric
  zero-excluding `S₀` ↦ `SqgSolution` through
  §10.116 → §10.131 → §10.129. Parallels v0.4.28's `exists_sqgSolution_of_galerkin_realSym`.

### Full chain status after v0.4.31

The three layers are now mutually consistent and joined:

* v0.4.28 `exists_sqgSolution_of_galerkin_realSym` — direct
  §10.117 packaging for finite-support data.
* v0.4.29 §10.118–§10.123 — Sₙ ↗ uniform estimates for generic `L²`
  data.
* v0.4.30 §10.125–§10.130 — conditional packaged-limit →
  `SqgSolution` chain.
* v0.4.31 §10.131–§10.132 — concrete instantiation of v0.4.30's
  hypotheses from v0.4.28's data. Demonstrates the v0.4.30 chain is
  actually instantiable on non-zero inputs.

The remaining mathematical gap is unchanged: constructing
`IsGalerkinLimitData` + `GalerkinLimitTrajectory` from v0.4.29's
estimates for generic (non-finite-support) `L²` data. That step is
the classical Resnick extraction (per-mode equicontinuity from
`Ḣ¹`-bounds or `H⁻²` test-function duality, diagonal subsequence,
Fourier synthesis), which requires mathlib weak-compactness
infrastructure not yet wired in.

## v0.4.30 — 2026-04-20

**§10.125–§10.130 — conditional Galerkin-limit → `SqgSolution` chain.**
Formalizes the passage-to-the-limit half of the Sₙ ↗ weak-`L²`
argument in a hypothesis-keyed form: whenever a classical extraction
produces the predicate data `IsGalerkinLimitData θ b`, a synthesized
`L²` trajectory `GalerkinLimitTrajectory θ b`, and a Riesz velocity
witness, a full `SqgSolution` falls out algebraically. The only open
ingredient after v0.4.30 is the construction of those packaged
hypotheses from v0.4.29's uniform estimates, i.e. the per-mode
equicontinuity + diagonal extraction + Fourier synthesis step
(classical Resnick theory).

- **§10.125** `IsGalerkinLimitData θ b` — predicate bundling: zero
  mode at every forward time, initial-data Fourier match,
  uniform-in-`t` ℓ²-summability, `∑' m, ‖b m t‖²` conservation, and
  real-symmetry of `b`. `IsGalerkinLimitData.ofZero` instantiates
  the degenerate zero datum.
- **§10.126** `galerkinLimitHasFourierCoeff b θ_t` predicate +
  `hsSeminormSq_zero_of_fourierCoeff_eq` identifying
  `hsSeminormSq 0 (θ_t) = ∑' m, ‖b m‖²` when `b 0 = 0`.
- **§10.127** `GalerkinLimitTrajectory θ b` structure bundling the
  synthesized `Lp`-trajectory with its Fourier-coefficient match and
  initial-time slice. `GalerkinLimitTrajectory.ofZero` instance.
- **§10.128** `SqgEvolutionAxioms.of_galerkinLimit` — derives
  `SqgEvolutionAxioms` from the three packaged hypotheses. All three
  clauses transfer structurally: L² conservation via §10.126, mean
  conservation via §10.125's `zeroMode`, velocity via the
  `HasGalerkinLimitVelocity` witness.
- **§10.129** `exists_sqgSolution_of_galerkinLimit` — `SqgSolution`
  capstone from the packaged limit + `smoothInitialData` summability.
- **§10.130** `exists_sqgSolution_ofZero` — unconditional zero-datum
  `SqgSolution` existence, exercising the full §10.125–§10.129 chain
  without any weak-compactness machinery.

### Remaining open (full chain status)

v0.4.29's uniform-estimate layer (§10.118–§10.123) + v0.4.30's
conditional limit chain (§10.125–§10.130) sandwich a single
remaining mathematical obstruction: constructing
`IsGalerkinLimitData` + `GalerkinLimitTrajectory` from the
§10.121 per-level Galerkin family for non-zero `L²` data. That
step needs either a per-mode Ḣ¹-type bound on the Galerkin
trajectory (or on the symbol-weighted ℓ² mass) to close
equicontinuity, or an `H⁻²` test-function duality bypass. The
mathematical theory (Resnick 1995) resolves it at the PDE level;
the Lean formalization would require mathlib-weight measure-
theoretic weak-compactness infrastructure that is non-trivial to
wire up.

## v0.4.29 — 2026-04-20

**§10.118–§10.123 — Sₙ ↗ weak-* limit infrastructure from generic
`L²(𝕋²)` initial data.** The v0.4.28 release discharged the
"Galerkin → full-SQG limit" README item via direct packaging (a
lifted Galerkin trajectory is already an L²(𝕋²) element). v0.4.29
addresses the stronger reading: **start from an arbitrary
`L²(𝕋²)` initial datum (not just a finite trig polynomial) and build
the Sₙ ↗ truncation apparatus with uniform estimates.** Nearly
+300 lines across six sections. Zero `sorry`, zero new axioms.

- **§10.118** `sqgBox n` — canonical nested symmetric Fourier box on
  ℤ² (integer `ℓ∞`-ball of radius `n + 1` minus origin). Proves
  `zero_not_mem`, `IsSymmetricSupport`, `sqgBox_mono`,
  `mem_sqgBox_iff` (coordinate characterization), and exhaustion
  `exists_mem_sqgBox` (every nonzero `m` eventually enters).
- **§10.119** `fourierRestrict n θ : ↥(sqgBox n) → ℂ` — restriction
  of the Fourier coefficients of any `L²` element to `sqgBox n`.
  Key identity `galerkinExtend_fourierRestrict_apply` and uniform
  ℓ² bound `sum_sq_fourierRestrict_le_L2Sq`: the finite ℓ²-sum of
  restricted coefficients is bounded by `∫ ‖θ‖²` via Parseval
  (`hasSum_sq_mFourierCoeff`) + `Summable.sum_le_tsum`. **Bound
  uniform in `n`.**
- **§10.120** `IsFourierRealSym θ` — predicate asserting that `θ`'s
  Fourier coefficients satisfy `θ̂(-m) = star θ̂(m)` (i.e. `θ`
  corresponds to a real-valued function on 𝕋²). Pass-through theorem
  `galerkinExtend_fourierRestrict_realSym` supplies the `hRealC₀`
  hypothesis of §10.116 for the restricted vector.
- **§10.121** `exists_galerkin_trajectory_of_L2` — per-level
  time-global Galerkin trajectory on `sqgBox n` starting from
  `fourierRestrict n θ`. Applies §10.116 with a **uniform-in-`n`**
  radius `R` chosen so that `(R/2)² ≥ ∫ ‖θ‖²`; the restricted data
  automatically fits inside the ball thanks to §10.119's Parseval
  bound. Delivers the full 5-way conjunction of §10.116.H.3 for
  every `n`.
- **§10.122** `hsSeminormSq_galerkinToLp_le_L2Sq` — uniform L² bound:
  `hsSeminormSq 0 (galerkinToLp (sqgBox n) (αₙ t)) ≤ ∫ ‖θ‖²` for
  every `n ∈ ℕ` and `t ≥ 0`. Derived from §10.117.A + the
  ℓ²-sum conservation of §10.116 + §10.119's Parseval bound.
- **§10.123** `sq_galerkinExtend_le_L2Sq` — per-mode pointwise bound:
  `‖galerkinExtend (sqgBox n) (αₙ t) m‖² ≤ ∫ ‖θ‖²` for every fixed
  mode `m`, `n ∈ ℕ`, `t ≥ 0`. Uses `Finset.single_le_sum` on the
  ℓ²-sum conservation invariant; trivially zero for `m ∉ sqgBox n`.
  This is the per-mode L∞ control that feeds any diagonal-subsequence
  argument for a weak-* limit.
- **§10.124** — program status note. What §10.118–§10.123 supplies:
  all the uniform-in-`n` estimates classically consumed by a
  weak-* L²(𝕋²) compactness argument. What remains: a
  diagonal-subsequence Arzelà–Ascoli extraction giving per-mode
  time-uniform convergence on compacts, then Fourier synthesis of
  the limit into an `L²` trajectory, then passage of
  `SqgEvolutionAxioms` through the limit. That chain needs a
  per-mode time-modulus of continuity derived from a uniform
  `‖galerkinVectorField (sqgBox n) (αₙ t) m‖` bound (via Cauchy–Schwarz
  on the bilinear `galerkinRHS` against the ℓ² bound), plus
  subsequence-extraction machinery from mathlib's weak-topology
  infrastructure. **The prerequisite estimates are now in place.**

### Scope disclosure

This release does not close the full Galerkin-to-weak-L²-limit chain;
it builds the uniform-estimate layer (§10.118–§10.123) that any
formal extraction of the limit must consume. The remaining passage-
to-the-limit argument (Arzelà–Ascoli → diagonal subsequence →
Fourier synthesis → axiom transfer) is substantial formal work that
is genuinely open.

### Open items after v0.4.29

1. Per-mode time-modulus of continuity for `αₙ(·, m)` from a uniform
   `galerkinVectorField` bound.
2. Diagonal subsequence extraction across modes (Arzelà–Ascoli on
   each mode + Cantor diagonal).
3. Fourier synthesis of the per-mode limit into an `L²(𝕋²)` trajectory.
4. Transfer of `SqgEvolutionAxioms` (`l2Conservation`,
   `meanConservation`, `velocityIsRieszTransform`) through the limit.
5. `SqgEvolutionAxioms_strong` upgrade of the §10.117 finite-support
   `SqgSolution` (see v0.4.28 notes).
6. `MaterialMaxPrinciple.hOnePropagation` /
   `BKMCriterionS2.hsPropagationS2` outside the finite-support class.
7. Ḣˢ bootstrap for `s > 2` (blocked on mathlib Kato–Ponce on 𝕋²).
8. Mode-wise weak-form PDE identity against `sqgNonlinearFlux`.

## v0.4.28 — 2026-04-20

**§10.117 — Galerkin → full-SQG limit on `L²(𝕋²)`.** Packages the
time-global Galerkin trajectory of §10.116 as an honest `SqgSolution`
on the L²(𝕋²) torus. Discharges the README "Galerkin → full-SQG limit"
open item. ~115 lines on top of v0.4.27 (18,114 → 17,520 shipped
line of source; headline capstone at §10.117.C).

- **§10.117.A `hsSeminormSq_zero_galerkinToLp`** — standalone
  identification `hsSeminormSq 0 (galerkinToLp S c) = ∑_{m ∈ S} ‖c m‖²`
  for any support `S` with `0 ∉ S`. Pulls the `hExp` step out of
  §10.97's internal computation so it can be consumed without an
  ODE-dynamics hypothesis. Independent of time, pure Fourier-side.

- **§10.117.B `SqgEvolutionAxioms.of_galerkin_realSym_Ici`** —
  parallel to §10.98's `SqgEvolutionAxioms.of_galerkin_dynamics`, but
  consumes only the ℓ²-sum conservation invariant (no `HasDerivAt`,
  no `hRealC`). Matches the output shape of §10.116's time-global
  capstone directly. Velocity witness identical to §10.98:
  `u_j τ := shellVelocity S (galerkinExtend S (α τ)) j` through
  `isSqgVelocityComponent_shellMode`. `meanConservation` is the
  `0 ∉ S` triviality.

- **§10.117.C `exists_sqgSolution_of_galerkin_realSym`** — headline
  existence theorem: for any symmetric support `S ⊆ ℤ²` with
  `0 ∉ S`, any radius `R > 0`, and any real-symmetric `c₀ : ↥S → ℂ`
  with `∑ ‖c₀ m‖² ≤ (R/2)²`, there exists an `SqgSolution` whose
  time-zero slice is `galerkinToLp S c₀`. Composes
  §10.116 (time-global Galerkin) with §10.117.B
  (`SqgEvolutionAxioms`) and discharges `smoothInitialData` with
  `s := 3` via `hsSeminormSq_summable_of_finite_support` (the finite
  Fourier support makes the Ḣ³ Parseval sum trivially summable).

The lifted trajectory is `t ↦ galerkinToLp S (α t)` where `α` is the
§10.116.H.3 capstone. `SqgSolution` consumes the weak-form
`SqgEvolutionAxioms` (not `_strong`), which is what §10.117.B
produces directly. The `_strong` / Duhamel-level promotion through
§10.94 would require `HasDerivAt` on all of `ℝ`, one notch stronger
than the `HasDerivWithinAt ... (Ici 0)` delivered by §10.116; that
upgrade is not pursued here (separately open).

### Open items after v0.4.28

- `SqgEvolutionAxioms_strong` for the Galerkin trajectory on `Ici 0`
  (needs either an ℝ-wide HasDerivAt extension or an Ici-0 variant
  of §10.94).
- `MaterialMaxPrinciple.hOnePropagation` /
  `BKMCriterionS2.hsPropagationS2` outside the finite-support class.
- Ḣˢ bootstrap for `s > 2` (Kato–Ponce-type estimates on `𝕋²`).
- Mode-wise weak-form PDE identity against `sqgNonlinearFlux` for
  real SQG weak solutions.

## v0.4.27 — 2026-04-20

**§10.116 complete.** Unconditional time-global Galerkin existence
on the real-symmetric ℓ²-bounded class. Extends v0.4.26 by ~420
lines (§10.116.G + §10.116.H).

- **§10.116.G `galerkin_realSym_existence_on_horizon`** — arbitrary
  finite horizon: for any `T ≥ 0`, a real-symmetric Galerkin
  trajectory on `[0, T]` with full invariants. Direct corollary of
  §10.116.F with `n := ⌈T/ε⌉`.

- **§10.116.H.1 `galerkin_realSym_chain_sequence`** — mirror of
  §10.105 with real-symmetry and ℓ²-sum invariants in the subtype
  carried through `Nat.rec`. The invariant
  `Inv c := (∑ ‖c m‖² = ∑ ‖c₀ m‖²) ∧ real-sym c` is closed under
  `stepFn c hinv ε` by §10.110 (ℓ²-conservation) + `hStep`'s
  real-symmetry preservation. Pi-norm bound for `hStep`'s
  precondition follows via `piNorm_le_of_sum_sq_le_sq`.

- **§10.116.H.2 `galerkin_realSym_global_on_Ici`** — mirror of
  §10.107 with the Nat-floor piecewise glue
  `α t := β ⌊t/ε⌋₊ (t - ⌊t/ε⌋₊·ε)`. Same three-case structure
  (strict interior / junction / origin) for `HasDerivWithinAt` on
  `Ici 0`. Adds ℓ²-sum conservation, real-symmetry, and pi-norm
  bound conclusions at every `t ≥ 0`.

- **§10.116.H.3 `galerkin_time_global_unconditional_realSym`** — the
  headline capstone. Plugs §10.116.D (`galerkin_realSym_forward_step`)
  into §10.116.H.2. Fully unconditional on the real-symmetric class
  with `∑ ‖c₀ m‖² ≤ (R/2)²`:

    * no `hInv` (universal ball-invariance) hypothesis
    * no `hRealSymPropagates` hypothesis
    * no L∞ slack bound hypothesis

  Delivers the full 5-way conjunction at every `t ≥ 0`: `α 0 = c₀`,
  `HasDerivWithinAt α (galerkinVectorField S (α t)) (Ici 0) t`,
  `∑ ‖α t m‖² = ∑ ‖c₀ m‖²`, real-symmetry of `α t`, and
  `‖α t‖_π ≤ R/2`.

### §10.116 program summary

Total §10.116 contribution: **~950 lines** (A through H) — larger
than initially scoped (~300), reflecting the genuine mathematical
content: Picard ball-containment extraction, within-Icc real-symmetry
propagation, real-symmetric forward step + chain sequence + Nat-floor
globalization + ℓ²-invariant-tracking subtype construction.

The only remaining open hypotheses for time-global existence on the
class of trajectories with finite Fourier support + real-coefficient
symmetry + uniform L∞ bound (the "Galerkin real-symmetric class"
of §10.100-§10.103 and §10.115 CHANGELOG notes) are now fully
discharged by this chain.

18,114 lines, zero `sorry`, zero new axioms.

## v0.4.26 — 2026-04-20

Real-symmetric chain n-step with ℓ²-sum invariant. Extends v0.4.25 by
~200 lines.

- **§10.116.F `galerkin_realSym_chain_n_step`** — mirror of §10.104
  with two additional invariants tracked through the induction:
  (a) real-symmetry at every `τ ∈ [0, n·ε]`, and (b) ℓ²-sum equality
  `∑ ‖α τ m‖² = ∑ ‖c₀ m‖²` (preserved exactly by §10.110). No `hInv`
  hypothesis needed: the pi-norm bound `‖α τ‖_π ≤ R/2` is derived
  pointwise from the ℓ²-sum invariant plus the initial
  `∑ ‖c₀ m‖² ≤ (R/2)²`, via `piNorm_le_of_sum_sq_le_sq`.

- **Refactor §10.110 `galerkinEnergyH0_const_on_Icc`** — weakens
  `hRealC` hypothesis from `∀ τ, 0 ≤ τ → ∀ n ∈ S, …` to the
  morally stronger `∀ τ ∈ Icc 0 ε, ∀ n ∈ S, …`. Internal proof only
  uses the hypothesis at `x ∈ Ico 0 ε`, so the interface change is
  free. §10.111 `galerkin_supNorm_bound_on_Icc` and §10.116.E adapt
  via `fun τ hτ => hRealC τ hτ.1` at the callsite; external shape is
  unchanged.

- **`piNorm_le_of_sum_sq_le_sq`** — reusable helper: for any
  `c : ι → E` and `B ≥ 0`, `∑ ‖c i‖² ≤ B² ⇒ ‖c‖_π ≤ B`. Used by
  §10.116.F at the base and induction-step junctions.

17,693 lines, zero `sorry`, zero new axioms.

## v0.4.25 — 2026-04-20

Real-symmetric forward step + ℓ²→pi chain invariant. Extends v0.4.24
by ~270 lines (§10.116.B through §10.116.E).

- **§10.116.B `hRealC_of_initial_and_bound_on_Icc`** — port of §10.114
  from `Ici 0` to `Icc 0 ε`. Same strategy: `ODE_solution_unique_of_mem_Icc_right`
  on `Icc 0 ε` with the `starSwap`-image solution. Conversion from
  the Icc-form `HasDerivWithinAt` to the `Ici t` right-sided form
  (required by the mathlib uniqueness lemma) uses
  `hasDerivWithinAt_inter` with `Iio ε` as the open witness (mirror
  of §10.110's pattern).

- **§10.116.C `galerkin_forward_step_with_ball`** — parallel to §10.103
  but delivers the `α t ∈ closedBall c₀ (R/2)` containment from
  §10.116.A. Picard setup identical to §10.102, but with
  `galerkin_local_exists_with_ball_containment` in place of
  `galerkin_local_exists_given_bounds`.

- **§10.116.D `galerkin_realSym_forward_step`** — combines §10.116.B
  and §10.116.C. For real-symmetric `c₀` in the `R/2`-ball, produces
  `α` on `[0, ε]` with `α(τ)` real-symmetric at every `τ ∈ [0, ε]`.
  L∞ bound `M := R` feeding §10.116.B follows from the ball-containment
  `‖α τ - c₀‖ ≤ R/2` + triangle inequality with `‖c₀‖ ≤ R/2`, so
  `‖α τ‖ ≤ R`. No circularity: `R` is a slack bound, the tight `R/2`
  bound is recovered by ℓ² conservation.

- **§10.116.E `galerkin_piNorm_le_ℓ2_on_Icc`** — sharper replacement
  for §10.111: pointwise `‖α t‖_π ≤ √(∑ ‖α 0 m‖²)` for a
  real-symmetric Galerkin trajectory on `[0, ε]`. Via §10.110's
  ℓ² conservation plus the elementary `‖c m‖² ≤ ∑ ‖c m'‖²`.
  This is the invariant that propagates across chain steps: if
  `c_k := α_{k-1}(ε)` then `∑ ‖c_k m‖² = ∑ ‖c_{k-1} m‖²` exactly,
  so the chain cannot drift in ℓ² norm.

The §10.116 program now has all building blocks in place. What
remains (§10.116.F-G, future session):

1. A `galerkin_realSym_chain_n_step` mirroring §10.104 but using
   §10.116.D at each step and §10.116.E to carry the ℓ² invariant.
2. `galerkin_realSym_chain_sequence` + `galerkin_realSym_global`
   mirroring §10.105-§10.108, producing time-global `α` on
   `Ici 0` without a `hInv` hypothesis — discharged internally from
   the per-step real-symmetry and ℓ² conservation.
3. Final unconditional capstone on the real-symmetric
   ℓ²-ball-constrained class.

Estimated ~250-300 lines remain for full closure.

17,492 lines, zero `sorry`, zero new axioms.

## v0.4.24 — 2026-04-20

Picard-Lindelöf wrapper with ball-containment. Extends v0.4.23 by ~50 lines.

- **§10.116.A `galerkin_local_exists_with_ball_containment`** — variant
  of `galerkin_local_exists_given_bounds` that additionally returns
  `α t ∈ closedBall c₀ a` for all `t : ℝ`. Replays mathlib's
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` proof
  in the Galerkin setting to expose `ODE.FunSpace.compProj_mem_closedBall`,
  which the standard mathlib wrapper proves internally but hides in
  the existential form.

This is the foundation for the §10.116 program (universal `hInv`
discharge on the real-symmetric class). The remaining steps involve:

1. Within-`Icc` variant of `hRealC_of_initial_and_bound_on_Ici`
   (§10.114) — needed to propagate real-symmetry over a single
   `galerkin_forward_step` interval `[0, ε]` rather than `Ici 0`.
2. `galerkin_realSym_forward_step` wiring §10.116.A + the within-Icc
   §10.114 variant + `galerkin_hInv_discharged` to produce a single
   real-symmetric Picard step.
3. Refactoring `galerkin_chain_sequence` (§10.105) to track
   real-symmetry through `Classical.choose`, producing a time-global
   `α` whose per-step `hInv` is discharged internally.
4. The final unconditional capstone combining 1–3 with §10.115.

The mathematical obstacle noted when scoping the program — that
pi-norm `‖c‖ ≤ R/(2·√|S|)` is not preserved by ℓ² conservation —
is resolved by working with ℓ²-norm as the chain invariant: ℓ²-norm
is preserved exactly by `galerkinEnergyH0_const_on_Icc`, so
`‖c_k‖_2 ≤ R/2` holds at every `k`, and
`‖α t‖_π ≤ ‖α t‖_2 = ‖c_k‖_2 ≤ R/2` gives the pi-norm bound on the
next step (tighter than §10.111's bound).

17,222 lines, zero `sorry`, zero new axioms.

## v0.4.23 — 2026-04-20

Time-global capstone with real-symmetric initial data. Extends v0.4.22
by ~58 lines.

- **§10.115 `galerkin_time_global_real_symmetric_initial`** — wires
  §10.114 into §10.113 to discharge the `hRealSymPropagates`
  hypothesis internally. Takes only real-symmetry of the initial
  coefficient vector `c₀` (one Finset-indexed `∀ n ∈ S` statement)
  plus the universal ball-invariance `hInv` (the one remaining open
  hypothesis). Produces the full four-way conjunction: `α(0) = c₀`,
  `‖α t‖ ≤ R/2` for `t ≥ 0`, `HasDerivWithinAt α (vf α(t)) (Ici 0) t`
  for `t ≥ 0`, and the sharp `‖α t‖ ≤ √|S|·‖c₀‖` ℓ²-derived bound.

  Proof strategy: re-derive the L∞ bound `‖α τ‖ ≤ R/2` at each
  `τ ≥ 0` directly from `hInv` (invoked on `[0, τ + 1]`), feed it as
  the `M := R/2` constant to `hRealC_of_initial_and_bound_on_Ici`,
  and thread real-symmetry at `τ = 0` through `α 0 = c₀`. Breaks
  the apparent circularity between §10.112 (needs real-symmetry)
  and §10.114 (needs L∞ bound) — the bound comes from `hInv`, not
  from §10.112.

- **Refactor §10.110-§10.113 + `galerkin_hInv_discharged`** to accept
  the weaker hypothesis `hRealC : ∀ τ, 0 ≤ τ → ∀ n ∈ S, …` in place
  of `∀ τ : ℝ, ∀ n ∈ S, …`. The proof of
  `galerkinEnergyH0_const_on_Icc` only applies the real-symmetry
  hypothesis at `τ ∈ [0, ε)`, so this weakening is free. Required
  so that §10.115 can feed §10.114's conclusion (which carries
  `0 ≤ τ` as a precondition) through §10.113 and §10.112 verbatim.

17,172 lines, zero `sorry`, zero new axioms.

## v0.4.22 — 2026-04-20

Within-interval real-symmetry propagation. Extends v0.4.21 by ~111 lines.

- **§10.114 `starSwap_hasDerivWithinAt`** — within-interval analog of
  the existing `starSwap_hasDerivAt`. Shows `β := starSwap ∘ α`
  satisfies the Galerkin ODE as a `HasDerivWithinAt` statement
  whenever `α` does. Proof is identical in shape: `hasDerivWithinAt_pi`
  + per-coord `HasDerivWithinAt.star`.
- **§10.114 `hRealC_of_initial_and_bound_on_Ici`** — ports §10.100's
  `hRealC_of_initial_and_bound` from the global
  `∀ t, HasDerivAt α (vf α(t)) t` hypothesis to the within-interval
  `∀ t ≥ 0, HasDerivWithinAt α (vf α(t)) (Ici 0) t`. Proof strategy
  substitutes `ODE_solution_unique_univ` with
  `ODE_solution_unique_of_mem_Icc_right` on `Icc 0 T` for each
  `T > 0` (invoked with `T := τ + 1` at the call site), with
  Lipschitz on `closedBall 0 M` via `ContDiffOn.exists_lipschitzOnWith`
  (same pattern as §10.102).

Combined with §10.113, this is the last technical piece needed to
fully discharge `hRealSymPropagates` internally for real-symmetric
initial data, provided the caller supplies an L∞ coefficient bound
(the natural choice is `M := √|S|·‖c₀‖ + 1` from §10.112, breaking
any apparent circularity in the combined capstone).

17,114 lines, zero `sorry`, zero new axioms.

## v0.4.21 — 2026-04-20

Unified time-global capstone. Extends v0.4.20 by ~45 lines.

- **§10.113 `galerkin_time_global_real_symmetric`** — a single
  existence statement combining §10.108 + §10.112, delivering a
  four-way conjunction:
  1. `α 0 = c₀` (initial data),
  2. `‖α t‖ ≤ R/2` for `t ≥ 0` (from §10.108, via `hInv`),
  3. `HasDerivWithinAt α (galerkinVectorField S (α t)) (Ici 0) t`
     at every `t ≥ 0`,
  4. `‖α t‖ ≤ √|S|·‖c₀‖` (from §10.112, via `hRealSymPropagates`).

  Two hypotheses still exposed:
  - `hInv` — §10.108's universal ball-invariance.
  - `hRealSymPropagates` — real-symmetry along the constructed `α`.

  Full unconditionalization requires a within-interval
  `HasDerivWithinAt`-flavoured adaptation of §10.100's
  `hRealC_of_initial_and_bound` (currently stated for `HasDerivAt`
  on all of `ℝ`). Estimated ~150 additional lines.

This closes the v0.4.14-v0.4.21 time-global existence program as a
conditional result (real-symmetric class, finite Fourier support).
17,003 lines, zero `sorry`, zero new axioms.

CI pitfalls caught (v0.4.21): `galerkin_global_existence_from_invariance`
takes `S` as an explicit argument (not inferred) — implicit `R` vs
explicit `S` had confused the argument-binding in my invocation.

## v0.4.20 — 2026-04-20

Unified global sup-norm bound. Extends v0.4.19 by ~35 lines.

- **§10.112 `galerkin_supNorm_le_sqrt_card_on_Ici`** — time-global
  counterpart of §10.111's `galerkin_supNorm_bound_on_Icc`. For any
  `α : ℝ → ↥S → ℂ` satisfying the Galerkin ODE on `Ici 0` with
  real-symmetric data, the sup norm is bounded uniformly in time
  by `√|S| · ‖α 0‖` for **all** `t ≥ 0` (not just on a finite
  interval `[0, ε]`).

  Proof is a one-liner: apply §10.111 with `ε := t + 1` and restrict
  the `HasDerivWithinAt` hypothesis from `Ici 0` to the subset
  `Icc 0 (t + 1)` via `.mono`.

Together §10.108 + §10.112 give **unconditional uniform
boundedness**: any real-symmetric trajectory produced by the
conditional construction in §10.108 satisfies the uniform-in-time
sup bound `‖α t‖ ≤ √|S| · ‖α 0‖`, for all `t ≥ 0`.

16,958 lines, zero `sorry`, zero new axioms.

## v0.4.19 — 2026-04-20

Within-interval `L²`-sum conservation + unconditional ball-invariance
discharge for §10.108's `hInv`. Extends v0.4.18 by ~166 lines.

- **§10.110 `galerkinEnergyH0_const_on_Icc`** — ports §10.97's L²
  conservation from `∀ t, HasDerivAt α (vf α(t)) t` on all of `ℝ` to
  the within-interval `∀ t ∈ [0, ε], HasDerivWithinAt α (vf α(t))
  (Icc 0 ε) t`. Building blocks:
  - `galerkinEnergyH0_hasDerivWithinAt` — `HasDerivWithinAt.fun_sum`
    + per-coord `.norm_sq` + `hasDerivWithinAt_pi`.
  - `galerkinEnergyH0_hasDerivWithinAt_zero` — reapply §10.96's
    inner-sum-real-part-zero identity (copied from §10.97).
  - Apply `constant_of_has_deriv_right_zero` after converting
    `HasDerivWithinAt (Icc 0 ε) x → HasDerivWithinAt (Ici x) x`
    via `.mono` onto `Ico x ε` + `hasDerivWithinAt_inter` with
    the open neighborhood `Iio ε`.
- **§10.111 `galerkin_supNorm_bound_on_Icc`** — direct application
  of §10.109 with §10.110's conservation, giving
  `‖α t‖ ≤ √|S| · ‖α 0‖` at every `t ∈ [0, ε]`.
- **§10.111 `galerkin_hInv_discharged`** — convenience wrapper
  in the exact shape consumed by §10.108's `hInv`: given
  `0 < S.card` and `‖c‖ ≤ R / (2·√|S|)`, delivers `‖α t‖ ≤ R/2`.
  The `√|S|` appears as a hypothesis rescaling (intrinsic to the
  sup-norm ↔ `ℓ²` comparison, not a proof artifact).

This completes the unconditional discharge of §10.108's `hInv` for
real-symmetric Galerkin solutions on finite Fourier support.
Together with the rest of §10.101-§10.111, time-global existence
is now unconditionally provable on this class — modulo the
`R/(2·√|S|)` rescaling in the initial-data hypothesis.

16,923 lines, zero `sorry`, zero new axioms.

## v0.4.18 — 2026-04-20

Pure norm bound bridging `ℓ²`-sum conservation (§10.97) and the
Pi sup-norm on `↥S → ℂ` that §10.108's ball-invariance hypothesis
references. Extends v0.4.17 by ~64 lines.

- **§10.109 three lemmas**:
  - `pi_sum_sq_le_card_mul_sup_sq` — `∑_m ‖c m‖² ≤ |S|·‖c‖²` on any
    finite-index Pi with seminormed codomain.
  - `pi_term_sq_le_sum_sq` — `‖c m‖² ≤ ∑_m' ‖c m'‖²` (single term
    bounded by sum of squares).
  - `galerkin_supNorm_le_sqrt_card_of_sum_sq_const` — if
    `∑_m ‖α t m‖² = ∑_m ‖α 0 m‖²` for all `t`, then
    `‖α t‖ ≤ √|S|·‖α 0‖`. Used to convert §10.97's sum-conservation
    into a sup-norm bound with a `√|S|` factor.

The `√|S|` factor is intrinsic to the Pi sup-norm ↔ `ℓ²` relation;
it means §10.108's `hInv` cannot be discharged to preserve the
`R/2` sup-ball exactly — rather, the discharged bound is
`‖α t‖ ≤ R/2` given `‖c₀‖ ≤ R/(2·√|S|)`. Capstone wrapper TBD.

Remaining toward unconditional time-global existence:
- §10.110: within-interval L²-sum conservation (`HasDerivWithinAt`
  version of §10.97's `galerkinEnergyH0_const`). Needs
  `HasDerivWithinAt.fun_sum` + `.norm_sq` (both present in mathlib)
  and `constant_of_has_deriv_right_zero` for the interval constancy.
  Estimated ~150-200 lines.
- §10.111 (or revised §10.108): wire §10.109 + §10.110 to discharge
  `hInv` unconditionally, with the `R/(2·√|S|)` hypothesis reshape.

16,757 lines, zero `sorry`, zero new axioms.

CI pitfalls caught (v0.4.18): a stray space before the closing
norm bar — `‖c m' ‖` — breaks the parser (the `‖` parser expects
the previous token to abut). Keep norms tight: `‖c m'‖`.

## v0.4.17 — 2026-04-20

Time-global existence steps 7-8 of 8 — program complete (conditional on
ball-invariance). Extends v0.4.16 by ~250 lines.

- **§10.107 `galerkin_global_hasDerivWithinAt_conditional`** —
  strengthens §10.106 with the derivative claim on `Set.Ici 0`. The
  piecewise `α t = β ⌊t/ε⌋₊ (t − ⌊t/ε⌋₊ · ε)` is shown to have
  `HasDerivWithinAt α (galerkinVectorField S (α t)) (Ici 0) t` at each
  `t ≥ 0`. Three cases:
  - **Strict step interior** `k·ε < t < (k+1)·ε`: use
    `hasDerivWithinAt_inter` with the open neighborhood
    `Ioo (k·ε) ((k+1)·ε)` and `.mono` onto
    `Icc (k·ε) ((k+1)·ε)`.
  - **Junction** `t = k·ε ≥ 1`: combine the previous step's
    `HasDerivWithinAt` on `Icc ((k−1)·ε) (k·ε)` (values agree via
    `β n ε = η(n+1) = β(n+1) 0`) with the current step's on
    `Icc (k·ε) ((k+1)·ε)` by `.union` + `Set.Icc_union_Icc_eq_Icc`,
    then extend to `Ici 0` via `hasDerivWithinAt_inter` with
    `Ioo ((k−1)·ε) ((k+1)·ε)`.
  - **Origin** `t = 0`: one-sided, `hasDerivWithinAt_inter` with
    `Iio ε` reduces to `Ico 0 ε ⊆ Icc 0 ε`.

  Translated β-derivative on step interval via `HasDerivWithinAt.scomp`
  with `(· − k·ε)` (scalar derivative `1`).
- **§10.108 `galerkin_global_existence_from_invariance`** — final
  capstone that hides the intermediate `hStep` hypothesis. Takes
  `R > 0`, `‖c₀‖ ≤ R/2`, and an `ε`-parameterized ball-invariance
  hypothesis; invokes `galerkin_forward_step` (§10.103) internally to
  discharge the step existence, then applies §10.107.

The only remaining premise for unconditional time-global existence is
discharging the ball-invariance `hInv` from L² conservation (§10.97),
which is independent of this chain and deferred.

16,693 lines, zero `sorry`, zero new axioms.

CI pitfalls caught (v0.4.17): `subst hk'_def` with `hk'_def : k = k' + 1`
fails when `k` is a `set`-variable — use a fresh local `kp := k - 1`
plus an explicit `Nat.succ_pred_eq_of_pos` and cast via
`congrArg (Nat.cast (R := ℝ))`. `ne_of_gt ht_pos : t ≠ 0` consumes
a hypothesis of the shape `t = 0`, not `0 = t` — drop the `.symm`
when reaching contradictions.

## v0.4.16 — 2026-04-20

Time-global existence steps 5-6 of 8: chain sequence `(η, β)` and
global function definition with pointwise norm bound. Extends v0.4.15
by ~123 lines.

- **§10.105 `galerkin_chain_sequence`** — via `Nat.rec` +
  `Classical.choose` on `hStep`, produce two sequences:
  `η : ℕ → ↥S → ℂ` (endpoint values with `η 0 = c₀`, `‖η n‖ ≤ R/2`)
  and `β : ℕ → ℝ → ↥S → ℂ` (step solutions with `β n 0 = η n`,
  `β n ε = η (n+1)`, `HasDerivWithinAt` on `[0, ε]`, and norm
  `≤ R/2` throughout). `chainEndpt` is built as a `ℕ`-indexed
  family in `{c // ‖c‖ ≤ R/2}`, with the bound at `n+1` discharged
  by `hInv` applied at step `n`.
- **§10.106 `galerkin_global_alpha_exists`** — define the global
  function `α : ℝ → ↥S → ℂ` piecewise:
  `α t = β ⌊t/ε⌋₊ (t − ⌊t/ε⌋₊ · ε)`. Establishes `α 0 = c₀`
  (using `Nat.floor_eq_zero` at `t=0`) and `‖α t‖ ≤ R/2` for all
  `t ≥ 0` (using `le_div_iff₀` + `div_lt_iff₀` on the Nat.floor
  bracketing `⌊t/ε⌋₊ · ε ≤ t < (⌊t/ε⌋₊ + 1) · ε`, then applying
  `hβB`).

Remaining for full time-global existence (deferred):
§10.107 global `HasDerivAt`/`HasDerivWithinAt` assembly (junction
handling at each `k·ε`, strict interior via `HasDerivWithinAt.hasDerivAt`
+ translation), §10.108 final capstone combining all pieces.

16,441 lines, zero `sorry`, zero new axioms.

CI pitfalls caught (v0.4.16): `_` placeholders in `stepSpec _ _`
cannot be inferred (chainEndpt value is ambiguous) — must pass
explicit `chainEndpt n`; `div_le_iff₀` orients as `a/c ≤ b`, so
`↑k ≤ t/ε` requires `le_div_iff₀` instead.

## v0.4.15 — 2026-04-20

Time-global existence step 4 of 8: Nat-indexed chain of local Picard
solutions. Ships §10.104, extending v0.4.14 by ~160 lines.

- **§10.104 `galerkin_chain_n_step`** — Under a ball-invariance
  hypothesis (`hInv`), iterate `galerkin_forward_step` by
  `ℕ`-induction: for each `n : ℕ`, produce `α : ℝ → ↥S → ℂ` with
  `α 0 = c₀`, `HasDerivWithinAt` on `[0, n·ε]`, and norm bounded by
  `R/2` throughout. Inductive step concatenates via
  `if t ≤ n·ε then α_n t else β (t − n·ε)`, glues the derivative at
  the step boundary via `HasDerivWithinAt.union` +
  `Set.Icc_union_Icc_eq_Icc`, and extends through interior points
  using `hasDerivWithinAt_inter` with one-sided open neighborhoods.
  Translated β-derivative on `[n·ε, (n+1)·ε]` obtained via
  `HasDerivWithinAt.scomp` with `(· − n·ε)`.

Remaining for full time-global existence (deferred):
§10.105 piecewise gluing into a single `α : ℝ → ↥S → ℂ`
(requires ODE uniqueness or direct Nat.rec construction),
§10.106 global HasDerivAt assembly, §10.107 L² conservation →
forward-invariance, §10.108 final capstone.

16,317 lines, zero `sorry`, zero new axioms.

CI pitfalls caught (v0.4.15): `set` auto-rewrites hypothesis display,
making subsequent `rw [show ... from rfl]` fail; `subst ht_eq` with
`ht_eq : t = Tn` substitutes `t` with `Tn` (not the reverse) — all
references to `t` in the substituted branch must be renamed.

## v0.4.14 — 2026-04-20

Time-global existence scaffolding: quadratic growth bound + uniform-ε
Picard + forward-step utility. Steps 1-3 of the global existence program.
~16,130 lines, zero `sorry`, zero new axioms.

- **§10.101 `galerkinVectorField_quadratic_bound`** — `‖galerkinVectorField S c‖ ≤ C·‖c‖²`
  where `C = ∑_{(ℓ,k) ∈ S × S} ‖galerkinKKernel ℓ k‖`. Bilinear/polynomial
  growth of the Galerkin vector field, via per-mode bound +
  reindex `ℓ ↦ (ℓ, m-ℓ)` into the full `S × S` product.
- **§10.102 `galerkin_uniform_ε_picard`** — Given radius `R > 0`, extract
  Lipschitz constant on `closedBall 0 R` (via `ContDiffOn.exists_lipschitzOnWith`
  + §10.101 growth bound), pick `ε = (R/2)/(L+1)` where `L = C·R²`, and
  apply mathlib Picard-Lindelöf on `closedBall c₀ (R/2) ⊆ closedBall 0 R`
  for any `c₀` with `‖c₀‖ ≤ R/2`.
- **§10.103 `galerkin_forward_step`** — one-sided variant on `[0, ε]`
  (forward iteration building block).

Remaining for full time-global existence (deferred to next session):
Nat-indexed chain construction, piecewise gluing, HasDerivAt
assembly on ℝ, L² conservation → forward-invariance of the ball,
final capstone. Estimated ~550-750 lines.

CI pitfalls caught: mathlib renames `pow_le_pow_left → pow_le_pow_left₀`,
`div_le_iff → div_le_iff₀`. Fresh `div_le_iff₀` rewrite still brittle
(instance mismatch between `Real.partialOrder.toLE` and `Real.instLE`);
use `field_simp` + `linarith` instead.

Archive: [TBD — Zenodo DOI pending].

## v0.4.13 — 2026-04-20

Real-symmetry ODE propagation: closes `hRealC` in the Phase-3 capstone
from per-τ to τ=0-only. 15,219 lines (`RieszTorus`) + 709 (`Basic`),
zero `sorry`, zero new axioms.

**§10.100** consumes the universal `galerkinRHS_starSwap_identity` from
v0.4.12 plus mathlib's `ODE_solution_unique_univ` to propagate
real-coefficient symmetry from the initial time to all times under the
Galerkin ODE. The variant capstone
`SqgEvolutionAxioms_strong.of_galerkin_dynamics_with_L_inf_bound_from_initial_realC`
takes `hRealC` at `τ=0` only, plus a uniform L∞ bound on all `τ : ℝ`
(strengthened from `τ ≥ 0` in v0.4.11's capstone so the starSwapped
trajectory stays in the same Lipschitz ball globally in time).

- **`negSubtype`** / **`starSwap`** / **`starSwap_starSwap`**: subtype
  plumbing for the order-2 involution `c ↦ fun n ↦ star (c (-n))` on
  `↥S → ℂ`, with `norm_starSwap_apply` giving sup-norm invariance.
- **`galerkinExtend_starSwap`**: the zero-extension of `starSwap hS c` is
  `fun m ↦ star (galerkinExtend S c (-m))` at the full lattice level
  (case split on `m ∈ S`; off-support uses `star_zero` + `hSym`).
- **`galerkinVectorField_starSwap`**: `galerkinVectorField` commutes
  with `starSwap`. Direct corollary of the universal
  `galerkinRHS_starSwap_identity` (§10.99) after pushing `starSwap` into
  `galerkinExtend` via the lemma above.
- **`starSwap_hasDerivAt`**: if `α` solves the Galerkin ODE, so does
  `β := fun τ ↦ starSwap hS (α τ)`. Via `hasDerivAt_pi` per coordinate +
  `HasDerivAt.star` (complex conjugation is ℝ-linear continuous).
- **`hRealC_of_initial_and_bound`**: the propagation theorem. Sets
  `β := starSwap ∘ α`; shows both `α τ, β τ ∈ closedBall 0 M` via
  `pi_norm_le_iff_of_nonneg`; extracts `K`-Lipschitz on that ball via
  `ContDiffOn.exists_lipschitzOnWith` (compact + convex + C¹); applies
  `ODE_solution_unique_univ` with the hRealC₀ initial equality to force
  `α = β`; unpacks to `hRealC` at every τ.
- **Capstone** `…_from_initial_realC`: wraps the propagation and feeds
  v0.4.11's §10.98 capstone.

+228 lines. One-shot CI green.

Archive: [TBD — Zenodo DOI pending].

## v0.4.12 — 2026-04-19

Real-coefficient symmetry algebraic preservation (building blocks for
ODE propagation). 15,700 lines (14,991 `RieszTorus` + 709 `Basic`), zero
`sorry`, zero new axioms.

Three new lemmas establishing the algebraic ingredients for propagating
real-coefficient symmetry from initial to all times under the Galerkin
ODE. The full ODE-uniqueness propagation (closing `hRealC` to a τ=0-only
hypothesis in §10.98) is deferred to a subsequent session; this release
ships the algebraic identities that will feed that argument.

- **§10.99 `galerkinRHS_neg_eq_star_of_realSymmetric`**: under
  `IsSymmetricSupport S` and `hRealC` on `c`,
  `galerkinRHS S c (-n) = star (galerkinRHS S c n)`. Proof via
  `Finset.sum_nbij'` reindex `ℓ ↔ -ℓ` + K-kernel self-star (via
  `star_derivSymbol` + `star_sqgVelocitySymbol`) + K-kernel
  double-negation-invariance.
- **Subtype lift `galerkinVectorField_neg_eq_star_of_realSymmetric`**:
  §10.99 at the `↥S → ℂ` vector-field level via definitional
  `galerkinVectorField S c ⟨m, h⟩ = galerkinRHS S (ext c) m`.
- **§10.99 extension `galerkinRHS_starSwap_identity`**: universal (no
  `hRealC` required) — for any `d : (Fin 2 → ℤ) → ℂ`,
  `galerkinRHS S (fun m => star (d (-m))) n = star (galerkinRHS S d (-n))`
  under `IsSymmetricSupport S` alone. Same reindex + algebraic structure
  as §10.99, but no reality hypothesis. This is the precise identity
  that the ODE-uniqueness propagation will consume — it says the
  Galerkin vector field commutes with the "starSwap" operator
  `c ↦ fun m => star (c (-m))` as functions, regardless of whether `c`
  itself has real symmetry.

CI pitfalls caught: `Finset.sum_nbij'` takes **non-dependent** `i : ι → κ`
(not `∀ a ∈ s, β`); `fun ℓ _ => -ℓ` confuses the elaborator. Pattern
`fun ℓ : τ => -ℓ` works. Beta-reduction via `dsimp only` needed before
rewriting arguments hidden behind lambda redexes.

Archive: [TBD — Zenodo DOI pending].

## v0.4.11 — 2026-04-19

Phase-3 self-contained Galerkin → `SqgEvolutionAxioms_strong` capstone.
15,553 lines (14,844 `RieszTorus` + 709 `Basic`), zero `sorry`, zero new
axioms.

Closes the remaining `hE : SqgEvolutionAxioms θ` hypothesis of v0.4.10's
§10.94 by deriving it internally from Galerkin dynamics + symmetric
support + zero-excluded + real-coefficient symmetry. Final capstone
`SqgEvolutionAxioms_strong.of_galerkin_dynamics_with_L_inf_bound` takes
only the Galerkin ODE, structural conditions on `S`, real-coefficient
symmetry, and the uniform `L^∞` coefficient bound — no auxiliary
hypotheses.

- §10.95 `advectionSummandH0` + Ḣ⁰ advection cancellation paralleling
  §10.73-§10.74 (weights stripped; `Complex.I` prefix retained for the
  `star I = -I` cancellation).
- §10.96 `galerkinRHS_inner_sum_eq_neg_advectionSumH0` + real-part
  vanishing: composes §10.48's flux decomposition with §10.80's
  pair-Finset reindex. Perfect alignment of conventions — no extra
  swap reindex needed.
- §10.97 L² conservation via `HasDerivAt.norm_sq` + `HasDerivAt.fun_sum`
  + §10.96's `Re = 0`, then `is_const_of_deriv_eq_zero`. Ports to
  `hsSeminormSq 0 (galerkinToLp ...)` under `0 ∉ S`.
- §10.98 `SqgEvolutionAxioms.of_galerkin_dynamics` bundles L² + zero-mode
  triviality + Riesz velocity into the axiom witness; composes with
  §10.94 Phase-2 capstone for the final self-contained result.

One-shot CI green (no iterations across 4 chunk pushes); 338 new lines
vs. the ~400-500 line pessimistic estimate.

Archive: [TBD — Zenodo DOI pending].

## v0.4.10 — 2026-04-19

Galerkin dynamics → `SqgEvolutionAxioms_strong` chain closed via rescoped
`IsSqgWeakSolutionOnSupport`. 15,049 lines (14,340 `RieszTorus` + 709
`Basic`), zero `sorry`, zero new axioms.

Closes the last "analytic-input → strong-axioms" mile for the finite-
Fourier-support Galerkin class. §10.48's universal-over-`m` statement
cannot feed `IsSqgWeakSolution` off-support (the Galerkin nonlinearity
leaks into modes outside `S` unless `S` is a radial/stationary shell,
where dynamics are trivial by §10.60). The fix is to rescope the Duhamel
hypothesis to `m ∈ S` and observe that `ModeLipschitz`'s per-mode chain
is trivial off-support under `hSupport`.

- §10.89 `IsSqgWeakSolutionOnSupport` predicate (Duhamel only at `m ∈ S`)
  and `IsSqgWeakSolution.toOnSupport` forgetful bridge. Direct construction
  `ModeLipschitz.of_finite_support_weak_on_support`: Bochner on-support
  (reusing §10.11's pattern), trivial off-support via `hSupport`.
- §10.90 `SqgEvolutionAxioms_strong.of_finite_support_weak_on_support`
  capstone mirroring §10.58 but consuming the rescoped Duhamel hypothesis.
- §10.91 `IsSqgWeakSolutionOnSupport.of_galerkin_dynamics`: composes §10.55
  `galerkin_mode_FTC` with §10.48 `galerkinRHS_eq_neg_sqgNonlinearFlux`,
  bridges `intervalIntegral` (Ioc) to `Set.Icc` via mathlib's
  `integral_Icc_eq_integral_Ioc` (Lebesgue `volume` is `NoAtoms`).
- §10.92 `SqgEvolutionAxioms_strong.of_galerkin_dynamics_on_support`
  end-to-end capstone: any Galerkin trajectory with base
  `SqgEvolutionAxioms` + per-mode flux bound yields the strong axioms.
  `hSupport` is automatic from `galerkinExtend_apply_of_not_mem`.

Archive: [TBD — Zenodo DOI pending].

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
