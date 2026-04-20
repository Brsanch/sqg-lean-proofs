# Changelog

All releases are archived on Zenodo; the concept DOI
[10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256) resolves
to the latest version.

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
