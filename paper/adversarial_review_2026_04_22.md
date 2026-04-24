# Adversarial referee report — `sqg-identity.md` (2026-04-22)

Self-review of `paper/sqg-identity.md` (1,093 lines, HEAD 5c13201) conducted as a hostile referee. No external input. Findings sorted by severity: **A** = must fix before submission, **B** = should fix, **C** = minor / editorial.

**Status (2026-04-24 update):** A1–A4 addressed in commit c302039. A1 table corrected with direct recomputation from cached features; A2 §9.8.3 values replaced with direct N=512 measurements and 4/3 conversion factor removed; A3 Prop 9.11 rewritten to make the spectral-to-pointwise bridge (B-spec) an explicit second hypothesis, "sharpest reduction" downgraded to "reformulation", Corollary 9.11.1 reframed as equivalence (not reduction); A4 Lemma 6.2 proof extended to derive the κ²δ² bound via the gradient-maximum parity conditions, with Remark 6.2.1 flagging the essential role of Proposition 9.1.

**B-class follow-up (2026-04-24):** B1 abstract scaling replaced with bounded-in-[0.17, 0.97] framing and −0.15 ± 0.05 clean-sharpening exponent; B2 addressed implicitly by A3's §9.8.1 rewrite that distinguishes spectral V from Lemma 6.5's material V and defines S_source as a residual; B3 factor-of-4 remark rephrased as a double factor-of-2 (tensor algebra + variance squaring), dropping the misleading line-element/wavevector duality story; B4 §8 equations (25)–(32) renumbered (8.1)–(8.8), §5.4 eq (13) → (5.4.a), no duplicated eq tags remain; B5 Lemma 9.13 Step 1 rewritten to make its positivity-on-segment claim explicitly conditional on (H-strain) rather than claiming a non-existent lower bound from Lemma 6.1; B6 §8.3 Test D relabeled "algebraic cross-check on static test fields" with explicit caveat that it is not a dynamical verification and does not rule out a shared solver-dependent error with Test C; B7 §9.8.5 LASSO flagged as in-sample fit on auto-correlated features, "refined (H-α*)" removed, kept only as a heuristic push–pull observation.

**C-class follow-up (2026-04-24):** C4 duplicate references (old [9]=[1], [10]=[4]) consolidated; refs [11]–[14] renumbered to [9]–[12] with body citations updated; C5 appendix Δt aligned to solver (`min(5e-4, 1.5/N)`) with binding-branch note, §5.1 Δt stale "3.9×10⁻³" replaced by "5×10⁻⁴ at N=512"; C6 added remark under Conjecture 9.4 spelling out that Conjecture 9.4 and (H-α) are logically distinct sufficient conditions, that the proof chain of §9.6.3 and §9.8 does not invoke Conjecture 9.4, and that (H-α)+(B-spec) ⇒ Conjecture 9.4 indirectly via Prop 9.11 but not conversely. C1 (scope statement), C2 (§8.6 implementation note), C3 (§7.4 prior-work comparison) were already good — no edits.

**Lean impact:** none. `MaterialMaxPrinciple.of_thermostat` in `RieszTorus.lean:25834` already takes `HasThermostatBound` plus separate `hOnePropagation` + `hOneSummability` spectral inputs, matching the new (B-spec) framing. Lean's `sqg_selection_rule_bound` is the universal per-mode CZ bound; the physical-space κ²δ² refinement sits behind `farFieldBoundary : True.intro` placeholders that abstract the paper-level parity argument.

---

## A. Must-fix

### A1. §9.8.5 table disagrees with cached data

Paper Table at line 1017–1021:

| N | ᾱ (paper) | α_max (paper) | frac(α>1) (paper) |
|---|---|---|---|
| 128 | 1.23 | 10.46 | 19.2% |
| 256 | 0.83 | 1.04 | 2.1% |
| 384 | **0.78** | 0.92 | 0.00% |

Recomputed directly from `results/sqg_thermostat_decomp/features_N{128,256,384,512}_multimode.npz` using the same definition α = 1 + (dV/dt)/(4|nSn|V), mask G>4, damping-weighted ᾱ:

| N | ᾱ (recomputed) | α_max | frac(α>1) |
|---|---|---|---|
| 128 | **0.914** | 10.46 | 19.1% |
| 256 | 0.833 | 1.04 | 2.1% |
| 384 | **0.809** | 0.92 | 0.0% |
| 512 | 0.803 | 1.04 | **2.0%** |

Three problems:

1. **N=128 ᾱ is wrong by 25%.** Paper reports 1.23; actual value is 0.914. The pointwise α_max and frac>1 match, but the time-weighted average does not. Either the paper computed an un-weighted mean (which would give something else again) or the number is a transcription error. Either way, a referee will re-run the script and notice.
2. **N=512 is omitted despite being the paper's flagship resolution.** All of §5, §9.3, §9.4, and §9.8.3 are built on N=512. Dropping N=512 from the convergence table looks selective — particularly because at N=512 the frac(α>1) is 2%, contradicting the paper's narrative of "cleaner with resolution." The correct story is probably "α_max stabilizes around 1.04, ᾱ plateaus around 0.80" — which is still consistent with (H-α), but different from what is written.
3. **The claim "no excursion above 1" at N=384 does not generalize.** The paper writes "α_max appears to stabilize around 0.9 as N grows" (line 1023). The cached data shows α_max actually climbs back above 1 at N=512. The monotone-stabilization claim is unsupported.

**Fix:** redo the table with all four N values and rewrite the narrative as "α_max stabilizes around 1.0–1.05, ᾱ plateaus around 0.80." This is still an argument in favor of (H-α) — the pointwise α approaches but does not cross 1 in any systematic way — but it has to be honest about α_max ≈ 1.

### A2. §9.8.3 table lacks reproducibility

Line 999: *"(Values reconstructed from the rate decomposition of sqg_heartbeat_2026_04_13.md in the companion NoetherSolve repository; conversion factor α_heartbeat = α·(4/3) between the two normalizations.)"*

Three problems:

- The source file is in a different (private, research) repository that will not be visible to a reviewer.
- A "conversion factor of 4/3 between two normalizations" without a derivation will look like ad-hoc rescaling. Write out why the heartbeat paper used 3|nSn|V in the denominator and why the paper uses 4|nSn|V, or redo the measurement with the paper's definition.
- The table shows α declining from 0.92 at G≈10 to 0.52 at G≈42 ("trend toward α → 1/2 at large G", line 1001). This is the *strongest* claim in the whole paper — strong enough that α_⋆=0.5 would get us into the "easy" sub-critical regime (line 978). But the N-scan table (A1 above, recomputed) shows ᾱ **plateauing at 0.80**, not trending to 1/2. The two tables appear to tell incompatible stories. A referee will flag this.

**Fix:** either (a) re-measure §9.8.3 with the same protocol as §9.8.5 so the tables use comparable definitions, and revise the "trend toward 1/2" claim, or (b) drop §9.8.3 and rely on §9.8.5 alone. Option (b) is safer.

### A3. Prop 9.11 reuses eq (33), which §9.5.2 already conceded does not close

Prop 9.11 proof (line 976): *"The localized CZ bound of §9.5.1 (equation (33)) gives |nSn_near(x(t))| ≤ C_near·ψ(t)·G(t)."*

This is precisely the (PC) hypothesis that Remark 6.7.1 labeled "not derivable in the form stated" (line 435), and that §9.5.2's "gap status (explicit)" box (line 800) concedes the Sobolev route cannot discharge. §9.6 was introduced as the route that bypasses it.

The proof of Prop 9.11 brings it back. If the referee is reading linearly, §9.8's "sharpest reduction" appears to build on exactly the bound that §9.5.2 admitted does not close.

Two candidate resolutions:

1. Prop 9.11 actually only needs the *spectral* version: the windowed angular variance V contracts, hence the Fourier content of nSn_near is concentrated on angles with small sin²(2φ_k), hence ‖nSn_near‖ is bounded. Spell this out as a multiplier bound on the windowed symbol, not as an appeal to eq (33). The L¹ estimate ∑|m(k)||θ̂_W| is controlled by an angular-H² norm, not by ψG directly.
2. Alternatively, accept that (H-α) implies the same PC-like bound, which means (H-α) is at least as strong as the §9.6.3 conditional pair; then the title "sharpest reduction" needs a softer label like "equivalent reformulation" and the paper has to say so explicitly.

**Fix:** rewrite the proof of Prop 9.11 to derive the |nSn_near| control from ψ→0 through a multiplier/Sobolev calculation, without citing (33).

### A4. Theorem 2 statement vs Lemma 6.2 proof

Theorem 2 (line 228) states |nSn_near(x*)| ≤ C κ² δ² ‖∇θ‖_∞ = C κ² A²/G.

Lemma 6.2's proof (line 302) derives |f_near| ≤ C κ A R (i.e., O(κA), *G-independent*), and then remarks parenthetically (line 304): *"More refined: the angular structure of K_f provides an additional κδ suppression, giving O(κ²δA) = O(κ²A²/G), but the O(κA) bound suffices."*

So the proved bound is O(κA), not O(κ²A²/G). Theorem 2 states the sharper bound without deriving it. In the proof chain, the sharper bound is what's actually used — Step 4 of Theorem 3 (line 910) writes `|nSn_near(x*)| ≤ C κ²(x*) A²/G ≤ C κ̄² A²/G → 0`. Without the sharper bound, this step fails, and the whole "bounded curvature suffices" mechanism collapses.

**Fix:** prove the sharper κ²δ² bound in Lemma 6.2. This is not hard — it's exactly the near-field parity cancellation with the two axes (n, t), which the proof sketches but only carries through to the κ¹ level. The extra factor needs the odd-odd sector parity + the gradient-maximum condition θ_nn = θ_nt = 0 at x*.

---

## B. Should-fix

### B1. Abstract picks a favorable scaling protocol

Line 7: *"numerical simulations at N=512 verify ... the scaling bound |nSn(x*)| ∼ G^{-0.17} across four decades of gradient intensity."*

§9.5 (line 684) documents that the same solver on the same IC gives α = +0.42 (sign-flipped) under a different measurement protocol. §9.5 resolves it: restrict to the sharpening interval and both protocols give α ≈ −0.15 ± 0.05. But the abstract cites only the favorable number without caveat or the reconciliation range.

**Fix:** abstract should say α = −0.15 ± 0.05 in the sharpening phase (both protocols agree there), or drop the scaling exponent entirely since §6.4 and §9.4 show it's not used in the proof — the paper only needs |nSn(x*)| bounded, not power-law.

### B2. Material ↔ spectral variance conflation at (9.8.a)

Lemma 6.5 proves the material angular variance of advected wavevectors contracts as dV/dt = 4(nSn)V. §9.8.1 (line 946) writes the same ODE for V := ⟨sin²(2φ_k)⟩ weighted by |θ̂_W|², which is a spectral quantity at a fixed point. These are not trivially the same object.

The paper acknowledges this as the Eulerian-vs-Lagrangian issue elsewhere (§9.5.1 — "the local spectral concentration works locally but fails globally"), but §9.8 slides between the two without flagging it. If the referee is being charitable, the argument is: "there is *some* V (the spectral one) such that S_source := dV/dt + 4|nSn|V is a well-defined functional, (H-α) asserts α < 1, and that closes the chain." That framing is logically clean. But the reader currently has to reconstruct it against the apparent identification with Lemma 6.5.

**Fix:** add a sentence at the start of §9.8.1 making clear that V in this section is the *spectral* variance (weighted by |θ̂_W|²), that (9.8.a) is not derived from Lemma 6.5 but is the *definition* of S_source, and that (H-α) is therefore a separate hypothesis on a measurable functional — not a consequence of the material-frame Lemma 6.5.

### B3. Lemma 6.5 — factor of 2 vs factor of 4

Line 419: *"the material gradient equation rotates wavevectors at rate 2|nSn| (not |nSn|) ... the factor of 2 in angular rate becomes a factor of 4 in the variance."*

But line 391 gives dV/dt = 4(nSn)V, and line 407 dV/dt = 4(∫ nSn dτ)V. The linearized ODE at line 401 gives d(Δφ)/dt = 2(nSn)Δφ, squared yields variance rate 4(nSn), so the factor of 4 in (26) is correct. Good.

However, line 419's phrasing ("a line element rotates at rate σ but a wavevector rotates at rate 2σ") is a non-sequitur: the geometric reason is that dφ/dt picks up a factor 2 from the strain tensor's diagonalization, not from line-element vs. wavevector duality. This will confuse the reader. **Fix wording.**

### B4. Equation-number collisions

Eq (25), (26), (27) appear twice (§6.6 lines 379, 383, 391 for wavevector dynamics; §8.1 lines 531, 535, 539 for tanh-front perturbation). Readers tracking cross-references will get lost. **Fix:** renumber §8 to (32)–(37) or use a different scheme like (8.1), (8.2).

Also: eq (45) is used in §9.5.1 (line 737) for Prop 9.5 commutator decomposition and again at (53) later — less critical but worth scanning.

### B5. Step 1 of Lemma 9.13 — missing uniformity

Line 822: *"|nSn(x*)| ≥ |nSn_far| − |nSn_near| ≥ cA − Cκ²δ²G"*

The lower bound `|nSn_far| ≥ cA` is never established in the paper. Lemma 6.1 gives an *upper* bound |nSn_far| ≤ CA. A sign-definite lower bound is a separate statement (the paper has it numerically in §9.3 as "|nSn(x*)| ∈ [0.17, 0.97]" but that's a measurement, not a proof). Without the lower bound, the arclength estimate of Step 1 collapses.

**Fix:** either (a) add an explicit lower-bound hypothesis that the far-field strain at x* is bounded below (this might just be (H-strain) itself, in which case flag the circularity), or (b) rephrase Step 1 as conditional on the same lower bound hypothesis used later.

### B6. §8 "four independent verifications" — third path is mislabeled

Table at line 567:
- Path A: analytic. OK.
- Path B: constructed. OK.
- Path C: "SQG solver". OK.
- Path D: "clean-room solver ... using different conventions at every layer ... no dealiasing".

Path D *without dealiasing* is not a verification of the formula on a well-resolved SQG solution — it's a verification that the *algebraic* rearrangement of Fourier multipliers commutes with different FFT libraries. The independent-solver claim oversells. **Fix:** relabel Path D as "algebraic cross-check against an independent FFT implementation on static test fields," not a dynamical verification.

### B7. §9.8.5 push–pull LASSO table

Line 1029–1037 reports standardized LASSO coefficients from "130 snapshots, three initial conditions." Six features, but no report of (i) feature correlations, (ii) LASSO regularization choice, (iii) cross-validation R² vs training R². With only 130 samples and 6 features including cumulative/state variables that are auto-correlated, a training R²=0.918 can fit noise.

**Fix:** add a one-sentence caveat that the R² is in-sample, that the coefficients are interpretive rather than testable, and drop the hopeful-looking "sharper form (H-α*)" at line 1042 until out-of-sample data supports it. Or move the whole LASSO to an appendix.

---

## C. Minor / editorial

### C1. Scope statement (line 33) is good — keep
The "what this paper is / what it isn't" framing is exactly right and heads off the first referee complaint.

### C2. §8.6 implementation note is an excellent catch — keep
The 14% artifact from `np.interp` is the kind of honest mid-paper reproducibility detail that reviewers appreciate.

### C3. §7.4 comparison to prior work — thorough
The Constantin-Majda-Tabak, Córdoba, He-Kiselev, Kiselev-Ryzhik-Yao-Zlatoš, Jeong-Kim, Misiołek-Vu-Yoneda comparison block is good. Minor: line 513's "informal expectation" that He-Kiselev examples violate (H-strain) is honestly hedged — keep the hedge.

### C4. References 9 = 1 and 10 = 4
The reference list duplicates CMT (1 and 9) and Córdoba (4 and 10). Consolidate.

### C5. Appendix "Δt = min(5·10⁻⁴, 2/N)"
Line 1087. At N=512 this gives 2/512 ≈ 3.9e-3. §5.1 mentions Δt = 3.9e-3. OK. But recomputation experiments used Δt = min(5e-4, 1.5/N) (different constant 1.5). Either the paper's constant is wrong or the experiments used a different solver than documented in the appendix. **Fix:** verify `noethersolve/sqg_solver.py` against the appendix and update whichever is outdated.

### C6. "conjecture 9.4" vs "Proposition 9.11"
§9.5 has Conjecture 9.4 stating the local strain energy is bounded. This is weaker than what §9.8 uses (which is (H-α)). The logical relationship between Conjecture 9.4 and (H-α) is not discussed. Either state it (probably (H-α) ⇒ Conjecture 9.4) or drop Conjecture 9.4 to avoid dilution.

---

## Overall verdict

The paper is not wrong. It is careful, the identity (Theorem 1) is solid and machine-verified, Theorem 2 is a real contribution (modulo fixing A4), and the conditional Theorem 3 is honestly labeled conditional. The thermostat reformulation is a genuinely new framing.

But a hostile referee lands on A1 (N=128 table error) within 10 minutes of reading, and A3 (Prop 9.11 reusing the §9.5.2-conceded bound) within an hour. Both are fixable without changing the substance of the result. A2 (§9.8.3 conversion factor + incompatible-looking numerics) is the single biggest credibility risk.

Recommend: fix A1–A4 before any submission. B1–B7 before second round. C's are cleanup.

The paper is closer to submittable than the user probably thinks, but the specific data-provenance issues in A1 and A2 will get it desk-rejected fast at any analysis journal. Fix those first.
