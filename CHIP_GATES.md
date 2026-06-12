# Chip gates — sqg-lean-proofs (load before ANY new Lean work in this repo)

Ported 2026-06-12 from `jacobian-lean-challenge/tools/chip-prompt-preamble.md`
(the 7 anti-paraphrase gates, added there 2026-05-23 after that repo ballooned
~130k → 183k+ LOC via paraphrase chips), adapted to this repo's own failure:
the 2026-05-29 audit found the "conditional Theorem 3" chain **circular** —
vacuous `True`-equivalent hypothesis structures, `True`-valued placeholder
fields in the geometric core, and a real antecedent (`hOnePropagation`,
uniform `Ḣ¹`) ≈ the conclusion. Full account: `OPEN.md` banner +
`docs/findings/sqg_material_max_principle_falsified_2026_05_29.md` in the
NoetherSolve repo. This repo grew 8,155 → ~29k LOC producing that chain.

Before writing ANY new code, the chip must pass ALL gates below. If it fails
any, REJECT and report `✗ REJECTED` with the failing gate.

## Gate V — vacuity lint (mechanical; this repo's incident class)

Run, from the NoetherSolve repo:

```
python3 "/Volumes/4TB SD/ClaudeCode/noethersolve/scripts/lean_vacuity_lint.py" \
  "/Volumes/4TB SD/ClaudeCode/sqg-lean-proofs" --no-color --max-findings 27
```

Rules (each is a mechanical signature from the 2026-05-29 audit): `True`-typed
fields/binders; `Prop := True` defs; `True.intro` proof terms; structures that
cannot constrain their subject (`(_θ : ...)`); structures none of whose fields
mention their parameters (`∃ α⋆ < 1` ≡ `True` pattern); theorems with
underscore-unused named hypotheses (the `MaterialMaxPrinciple.of_thermostat`
relabeling pattern).

**Baseline = 27 findings (audited 2026-06-12).** Six are the deliberately
retained, banner-annotated §14 circular-chain declarations
(`HasStrainLowerBound`, `HasBoundaryCurvatureBound`, `HasThermostatBound`,
`MaterialMaxPrinciple.of_HstrainHbdry` ×2, `.of_thermostat`); the rest are
unused-hypothesis findings, including three that deserve suspicion on any
future touch: `sqg_uniformHs_conditional` (ignores `_hFSC`),
`sqg_regularity_via_interpolation` (ignores `_hE`),
`sqg_regularity_via_stationaryShape` (ignores `_hS`) — a "regularity via X"
theorem that does not use X is the relabeling pattern by construction.

**The count must never increase.** New code adds zero findings; if a finding
is deliberate, waive it inline with `-- vacuity-ok: <reason>` (greppable) and
say so in the chip report. Reducing the baseline (refining a `True` field to
the real statement, dropping a decorative hypothesis) is real work; lower the
`--max-findings` number in this file in the same commit.

What the linter CANNOT catch (still on the human/review path): circularity
(hypothesis ≈ conclusion — `hOnePropagation` was this), misformalization, and
encoding mismatches. "Lint-clean" ≠ "content is real".

## Gates 1–7 (anti-paraphrase, adapted)

1. **Paraphrase gate.** Shipping `T_new (h₁ ... hₖ)` from `T_old (h₁ ... hₙ)`,
   `k < n`, by naming the dropped hypotheses into a NEW structure/class/Prop
   is a paraphrase, not progress — each name is a deferred sorry with a
   different docstring. REJECT unless the chip also discharges a named
   hypothesis by classical proof on arbitrary data (not on finite-support /
   single-mode / `Subsingleton` instances).

2. **Parallel-route gate.** A new route to an already-reachable conclusion is
   net negative (maintenance surface, zero new closure). The repo's own
   history: Routes A/B/C to the withdrawn chain all funneled through the same
   unproven Lemma 6.5. REJECT unless the new route closes something the
   existing one does not, documented precisely.

3. **Named-hypothesis gate.** A new `class`/`structure`/`def Prop` whose
   discharge is "left as future work" or instantiated only on finite-support /
   single-mode data is a renamed sorry. REJECT unless the same session
   discharges it on arbitrary data.

4. **Per-instance gate.** Concrete single-mode / shell-mode / stationary-shape
   witnesses are smoke tests, +50–150 LOC each, and do not move the frontier.
   At most ONE per session, only if a same-session theorem consumes it.

5. **Minimum substantive content.** The chip report's `proven:` field must be
   a substantive classical statement in plain math — NOT "bridges hypothesis A
   to hypothesis B", "packages X into structure Y", or "reduces N inputs to
   N−1". REJECT the latter.

6. **mathlib-first gate.** Before new infrastructure, grep
   `.lake/packages/mathlib/` for the closest lemma. If it is within ~50 LOC of
   glue, use it; otherwise keep new infrastructure < 300 LOC and name the gap.

7. **Frontier gate (repo-specific).** Per `OPEN.md` there are **no open
   regularity items**: the regularity chain is withdrawn, and what stands is
   Theorem 1 (the identity) + the §8 curvature correction. Any chip claiming
   regularity progress must first state, in its dispatch, which line of the
   `OPEN.md` banner it overturns and with what classical (non-Lean) argument —
   otherwise REJECT. The genuine obstruction on record is log-criticality
   (`‖S‖_∞ ≲ G log G`); see the leap queue
   (`noethersolve/docs/LEAP_QUEUE.md`).

## Discipline rules (panic-safe build; non-negotiable)

- Per-file iteration: `LEAN_NUM_THREADS=1 lake env lean SqgIdentity/FILE.lean`.
- Merge gate for any new top-level declaration: full
  `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build`
  (single-file checks miss cross-file duplicate names).
- NEVER: unthrottled `lake build`, `lake exe cache get`, `du`/`find` on
  `.lake`.
- No `sorry`, no `axiom`, no `ω` as a binder name.
- "Zero sorry, zero axioms" is NOT the bar — this repo had both while hiding a
  circular chain. The bar is Gate V + Gates 1–7 + the OPEN.md banner staying
  truthful.
