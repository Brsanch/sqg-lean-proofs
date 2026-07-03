# Open items — sqg-lean-proofs

> **Before any new Lean work: read `CHIP_GATES.md` (repo root)** — vacuity
> lint gate (mechanical, baseline-ratcheted) + the 7 anti-paraphrase gates.

## ⚠️ Status banner (2026-05-29, source aligned 2026-05-30) — conditional chain is circular; regularity NOT closed

An audit on 2026-05-29 found that "closed at the formalization-of-the-
conditional-chain level" overstates what exists:

- The conditioning hypotheses `HasStrainLowerBound` (H-strain),
  `HasBoundaryCurvatureBound` (H-bdry), `HasThermostatBound` (H-α) are
  **logically vacuous** structures — content `∃ c ≥ 0` / `∃ α < 1` ≡ `True`
  (`RieszTorus.lean` §14). They condition on nothing.
- The geometric core of `MaterialMaxPrinciple` was **`True`-valued placeholder
  fields** (`freeDerivativeAtKappaMax`, `materialSegmentExpansion`,
  `farFieldBoundary`), since **removed** (2026-05-30).
- The only real antecedent is a uniform-in-time `Ḣ¹` (enstrophy) bound
  (`hOnePropagation`), which ≈ the conclusion. The chain is therefore
  **circular** ("uniform enstrophy ⟹ regularity"), the same failure mode
  as the NS Seregin-closure route.
- The classical §9 material-maximum-principle argument these structures are
  meant to encode is **falsified by the project's own numerics**: the
  "free derivative" step needs `f = −cκA` but `corr(f,−κ)=0.44`, giving
  `κ_max ~ G` (unbounded); and the depletion mechanism is provably one
  order short (parity kills `nSn(x*)` through 3rd order incl. curvature),
  so it needs `κ'`, measured `~G^{1.2}` → blow-up of the `dG/dt=G|nSn|`
  bound.

**2026-05-30 honesty pass.** The source was made to match this banner: the
capstone `sqg_regularity_conditional` was renamed `sqg_uniformHs_conditional`
(it is modus ponens on assumed inputs, not a regularity proof); the `True`
placeholder fields and the vacuous `.of_zero` witnesses were removed; and every
§10–§14 docstring, plus the README, now states the circularity plainly. "No
`sorry`, no axioms" remains literally true — and, per the banner, does not mean
the regularity content is real. Start at the §10 banner in `RieszTorus.lean`.

**2026-07-02 independent adversarial audit** (four independent refutation
passes; full record: NoetherSolve
`docs/findings/sqg_dead_end_independent_audit_2026_07_02.md`). The dead-end
verdict **stands**: exhaustive antecedent→conclusion mapping found no theorem
deriving Ḣˢ (s>1) — or even Ḣ¹ — control from the SQG dynamics; the vacuity
lint sits exactly at its ratcheted baseline (18). Three corrections to the
record:

1. **Banner numbers de-weighted.** The `corr(f,−κ)=0.44` and `κ' ~ G^{1.2}`
   figures quoted above are prose-only residue of a single noisy contour-FD
   run (no generating script or data survives; the one surviving PNG embeds a
   contradictory garbage fit). Honest phrasing: the §9 argument's needed
   inputs were **never supported** by the project's measurements, not
   "falsified by" them. Dead either way — burden of proof. The parity
   derivation (mechanism one order short) was independently re-derived and is
   CONFIRMED.
2. **"Córdoba–Fefferman ceiling" phrasing corrected** (see below).
3. **NEW: the FourierBridge Path-B non-zero capstones are uninhabitable on
   nonlinear data.** `HasSqgGalerkinAllSBound.ofGalerkin_nonZero` (:1117),
   `ofGalerkin_nonZero_fullyConcrete` (:1587) and
   `HasGalerkinGronwallClosure.ofGronwallODE` (:977) require
   `∀ t ≥ 0, Real.exp ((2*(K.K*Lip.L))*t) ≤ E` for a fixed `E` — satisfiable
   only when `K.K*Lip.L = 0`, i.e. zero nonlinear flux. So the §B.13/§B.15
   prose ("once Kato–Ponce lands, the fully unconditional Path B chain
   follows") is FALSE: a completed Kato–Ponce gives `K > 0` and the
   hypothesis stays unsatisfiable. **DONE 2026-07-02** (commit `865dec2`,
   merge gate green, vacuity lint at baseline 18): the §B.13/§B.15
   docstrings now state this — Path B yields `exp(CT)`-in-time bounds on
   `[0,T]`, never the time-global `Ms` that §11.34 consumes. Also note
   `HasVelocityRieszPreservation`,
   `FourierKatoPonceConst`, `HasVelocityLipSupBound` (FourierBridge :160,
   :296, :790) are `∃ c ≥ 0`-class shells that escape the linter's
   subject-free rule (zero-parameter structures); they gate nothing alone
   but the "four classical inputs" framing of §B is decorative.

What stands: **Theorem 1 (the identity)** is genuinely verified, and the
**§8 closed-form curvature correction** is correct and numerically verified.
Full account: `sqg_material_max_principle_falsified_2026_05_29.md`,
`sqg_pathC_resolution_artifact_no_missed_path_2026_05_30.md`, and
`sqg_salvage_identity_and_curvature_correction_2026_05_29.md` in the
NoetherSolve repo (`docs/findings/`).

**Last analysis-side entry point retired (2026-07-03).** The one qualitatively
open geometric-Lyapunov hunt reserved by the 2026-07-02 audit (§5) — a
Constantin–Vicol nonlinear-maximum-principle on the front-curvature field `κ` —
is now **certified dead** (adversarially verified against the CV primary source
arXiv:1110.0179): CV is structurally a *dissipative* tool and inviscid SQG has
no dissipation operator; the exact §8 production is linear in `κ` with the
log-criticality coefficient, and `nSn` depends on `κ′` (a derivative above what
any `κ`-bound controls). Full account: NoetherSolve
`docs/findings/sqg_cv_curvature_negative_cert_2026_07_02.md`; LEAP_QUEUE §2. The
paper's withdrawal was completed to match (`paper/sqg-identity.md`, commit
`f20959f`: §7.4 + §10 brought under the withdrawal banner, CV closure folded in).

## Status of the former "open items" (all were conditional-chain plumbing)

The 2026-04-23 banner and the item-by-item tracker that used to fill this file
are **superseded**. Items 1–6 were structural plumbing for the
conditional-regularity chain in `RieszTorus.lean` §10–§14. "✓ Closed" meant
*the Lean plumbing compiles* — never *regularity is proved*. With the chain
found circular, that distinction is the whole point:

| Former item | What "closed" actually meant |
|---|---|
| 1. Generic-`L²` Galerkin → `SqgSolution` extraction (Route B) | Galerkin ODE well-posedness + a packaging of an *assumed* Aubin–Lions extraction into an `SqgSolution`. Real ODE content; says nothing about regularity. |
| 2. `SqgEvolutionAxioms_strong` upgrade | Duhamel-level restatement of the same Galerkin solution. |
| 3. `MaterialMaxPrinciple.hOnePropagation` off the finite-support class | "Lifted" only by *assuming* a uniform `Ḣ¹` bound on the Galerkin sequence — i.e. assuming the conclusion. |
| 4. `BKMCriterionS2` off the finite-support class | Same: the lifted hypothesis is vacuous given assumed uniform `Ḣˢ` bounds. |
| 5. `Ḣˢ` bootstrap for `s > 2` | A Littlewood–Paley / Kato–Ponce program; its genuine byproduct is the §11.26 lattice-zeta product bound (below). The regularity goal it served is withdrawn. |
| 6. Mode-wise weak-form PDE identity | A structural weak-solution bridge on finite-support data. |

## No open regularity items

This repository's regularity route is a **confirmed dead end**, not an open
problem with remaining steps:

- The conditional chain is circular (above): it funnels through an *assumed*
  uniform `Ḣ¹` bound ≈ the conclusion.
- The geometric-depletion mechanism it was meant to encode is one order short
  (analytic parity result, independently re-verified 2026-07-02). Genuine
  obstruction: log-criticality (`‖S‖_∞ ≲ G log G`). *Framing corrected
  2026-07-02:* the earlier "double-exponential Córdoba–Fefferman ceiling"
  phrasing was imprecise — Córdoba 1998 / Córdoba–Fefferman 2002 are
  scenario-restricted collapse-rate *floors* (saddle / semi-uniform front
  collapse), not an upper bound on `‖∇θ‖_∞`; for smooth SQG **no a priori
  upper bound of any kind is proven** (double-exp-as-ceiling is a 2D-Euler
  theorem needing `‖ω‖_∞` conservation; realized SQG record is exponential
  growth, He–Kiselev Duke 2021). The wall is worse than the old phrasing
  suggested, not better.
- Full account in the NoetherSolve repo (`docs/findings/`):
  `sqg_material_max_principle_falsified_2026_05_29.md`,
  `sqg_pathC_resolution_artifact_no_missed_path_2026_05_30.md`.

The former "Next-session plan — Route A" (a ~4810-LOC Littlewood–Paley roadmap)
is **dropped**: it was a plan to discharge the *bootstrap* half of the circular
chain, which would not make the chain non-circular (the load-bearing
`MaterialMaxPrinciple` half is the assumed `Ḣ¹` bound ≈ the conclusion).

## What is genuinely proved and worth keeping

- **Theorem 1** — the shear–vorticity identity (`SqgIdentity/Basic.lean`) and
  the universal per-mode CZ selection-rule bound. Unconditional, machine-verified.
- **§8 closed-form curvature correction** (paper) — verified <0.2% across four
  independent pathways.
- **Reusable infrastructure** (mathlib-adjacent, no axioms): the §11.26–§11.27
  concrete Banach-algebra `Ḣˢ` product bound (explicit lattice-zeta constant,
  every `s > 1`); the Galerkin ODE well-posedness (§10.116); Fourier-form
  Rellich–Kondrachov (`FourierBridge.lean`); the torus Riesz / heat-semigroup
  multiplier machinery; and the companion package
  [`sqg-lean-proofs-fourier`](https://github.com/Brsanch/sqg-lean-proofs-fourier)
  (Littlewood–Paley / Bony paraproduct / Kato–Ponce commutator), intended for
  reuse by future NS / Euler / MHD work.

The detailed item-by-item and §-by-§ history is in `CHANGELOG.md` and git.

## Protocol

- One change per tagged release where practical; no compound changes.
- **Local verification gate (Apple Silicon):** `taskpolicy -b nice -n 19 env
  LEAN_NUM_THREADS=1 lake build` — panic-safe, and catches the cross-file
  duplicate-declaration errors that single-file `lake env lean` cannot (see
  `CONTRIBUTING.md`). CI is optional final confirmation.
- "What's left" answers come from this file.

## Ledger discipline for any future arc (adopted 2026-06-12)

Any new proof arc here tracks obligations as a per-claim ledger (one file per
claim, DAG of `dependencies`/`supports`), not by growing this file. Full
schema: `../references/proof_obligation_ledger_schema.md` (local shared refs
dir). The three load-bearing rules, self-contained:

1. **No self-certification.** `verified` = Lean-proved, zero sorry, zero
   external axiom, *per entry*. The central claim never carries more than
   `speculative` + a confidence number until external review. The §10–§14
   failure documented above — vacuous hypothesis structures under a true
   "no sorry, no axioms" headline — is exactly what this rule blocks: the
   headline is a per-entry status, never a theorem-level claim.
2. **No paraphrase nodes.** An entry whose dependencies and supports match an
   existing entry's is a reformulation, not progress; `supersedes` is for
   corrections only, never parallel routes.
3. **Dead ends become AK entries** (approach / obstruction-with-mechanism /
   history + named fix) and citation errors become CORR entries (including
   phantom-citation audits of our own bibliography) — machine-checkable
   claims, not prose.
