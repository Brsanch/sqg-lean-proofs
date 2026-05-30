# SQG Identity — Lean 4 Formalization

[![CI](https://github.com/Brsanch/sqg-lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Brsanch/sqg-lean-proofs/actions/workflows/lean_action_ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19583256.svg)](https://doi.org/10.5281/zenodo.19583256)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](./LICENSE)

A Lean 4 + mathlib formalization of Fourier-space identities for the inviscid
Surface Quasi-Geostrophic (SQG) equation on the 2-torus, together with a
conditional regularity roadmap.

Two algebraic theorems are fully machine-verified (the shear–vorticity
identity, and the per-mode CZ bound). A third item, a "conditional global
regularity" chain, was **withdrawn on 2026-05-29**: an audit found it
circular and substantively hollow — see the boxed status note below. The
repository does **not** prove SQG regularity in any non-circular sense.

The mathematical content is developed in the accompanying paper:

- **[`paper/sqg-identity.pdf`](./paper/sqg-identity.pdf)** — *The
  shear-vorticity identity and spectral concentration in SQG front dynamics.*
  ([markdown source](./paper/sqg-identity.md))

The formalization comprises over 25,850 lines of Lean 4 source in the
`RieszTorus` module and 2,490 lines in the `FourierBridge` module
(over 29,000 lines project-wide, wiring in the
[sqg-lean-proofs-fourier](https://github.com/Brsanch/sqg-lean-proofs-fourier)
companion package for classical Littlewood–Paley / Bony paraproduct /
quantitative uniform-in-N Kato–Ponce commutator content), with
**zero `sorry` and no axioms beyond mathlib** — but note (2026-05-29) the
regularity-chain gaps were hidden in vacuous `True`-equivalent hypothesis
structures (which remain, now documented as vacuous) and `True`-stubbed fields
(since removed), so "zero sorry, no axioms" does **not** mean the regularity
content is real. See the status note below.

**⚠️ Status note (2026-05-29) — the conditional regularity claim below is
WITHDRAWN (circular).** The named hypotheses `HasStrainLowerBound` (H-strain),
`HasBoundaryCurvatureBound` (H-bdry), `HasThermostatBound` (H-α) are
**logically vacuous** structures — content `∃ c ≥ 0` / `∃ α < 1` ≡ `True`
(`RieszTorus.lean` §14); the `MaterialMaxPrinciple` geometric core was
`True`-valued placeholder fields (since **removed**); the only real antecedent
(`hOnePropagation`) is a uniform-in-time `Ḣ¹` bound, which ≈ the conclusion.
So the chain reduces to "uniform enstrophy ⟹ regularity" — circular, same as
the NS Seregin route. The §9 argument behind it is falsified by the paper's own
numerics (`corr(f,−κ)=0.44`). See the `RieszTorus.lean` §10 banner and the
"conditional Theorem 2 roadmap" section below for the full account.

**Mathlib-adjacent infrastructure discharged in this repository** (each
full proof, no axioms added):
- §13 lattice Sobolev per-mode Ḣˢ sup bound (`RieszTorus.lean`).
- §B.15 inverse Fourier transform `lpOfFourierCoeff` on `𝕋²` via
  `mFourierBasis` (`RieszTorus.lean`).
- §B.16–§B.19 Rellich–Kondrachov compact embedding `H¹(𝕋²) ⊂⊂ L²` in
  Fourier form: `countable_diagonal_bounded_sequences` +
  `fourier_rellich_kondrachov` (`FourierBridge.lean`), enabling
  Aubin–Lions extraction on the Galerkin sequence.

## What is proven unconditionally

### Theorem 1 (Shear-Vorticity Identity)

For the SQG velocity field `u = ∇⊥(−Δ)^{−1/2} θ` on `𝕋²`, the Fourier
multiplier of `S_{nt} − ½ ω` is `|k|·sin²(φ_k)`:

```
F[S_nt − ½ω](k) = |k| · sin²(α − β) · θ̂(k)
```

where `k = |k|(cos α, sin α)` and the front normal is `n̂ = (cos β, sin β)`.
In particular, `S_nt − ½ω ≡ 0` for any one-dimensional front.

Lean statement: `sqg_shear_vorticity_identity` in
[`SqgIdentity/Basic.lean`](./SqgIdentity/Basic.lean).

### Per-mode selection-rule bound (universal CZ form)

Pointwise mode-level bound `‖Ŝ_nt − ω̂/2‖ ≤ |k|·‖θ̂‖` with equality
characterization, integrated via Parseval on `L²(𝕋ᵈ)` and restated as an
`Ḣ¹`-seminorm inequality. Lives in `SqgIdentity/Basic.lean` (mode-level,
`sqg_selection_rule_bound`) and
[`SqgIdentity/RieszTorus.lean`](./SqgIdentity/RieszTorus.lean) (integrated
via `sqg_selection_rule_Hs1`).

This is the universal Calderón–Zygmund bound. The accompanying paper's
Proposition 6.1 — the *pointwise parity-improved* bound
`|nSn_near(x*)| ≤ C·κ²·δ²·G` at the gradient maximum — is a **refinement
of** this Lean-verified bound using gradient-maximum parity cancellation;
its proof in `paper/sqg-identity.md` §6.1 operates at formal Taylor-expansion
+ parity-sector-cancellation level, is tighter than Córdoba's O(κA) form,
and is **not itself machine-verified**. Lean verifies the universal CZ
precursor that the paper's parity argument refines.

### Supporting infrastructure

`RieszTorus.lean` develops a self-contained Fourier-multiplier account of the
torus Riesz transforms, Leray–Helmholtz projector, fractional Sobolev scale,
Biot–Savart factorisation, tight mode-level strain/vorticity identities, the
α-fractional heat semigroup and its smoothing bounds, and a parallel suite
for the classical heat semigroup. All bounds are established without
general Calderón–Zygmund singular-integral theory: they follow from Parseval
plus explicit Fourier-symbol inequalities.

## The conditional "Theorem 2" roadmap — WITHDRAWN (circular)

⚠️ `RieszTorus.lean` §10–§14 formalizes a conditional regularity chain that the
2026-05-29 audit found **circular**. It does **not** prove SQG regularity. It is
retained in the source — with blunt, honest docstrings; start at the §10 banner
in `RieszTorus.lean` — as a precise record of which analytic facts the paper's
argument would need, not as a proof. See the boxed status note at the top of
this README. In brief:

- **The capstone is modus ponens.** `sqg_uniformHs_conditional` (formerly
  `sqg_regularity_conditional`) derives uniform `Ḣˢ` bounds from a
  `MaterialMaxPrinciple` (an **assumed** uniform `Ḣ¹`/enstrophy bound) and a
  `BKMCriterion` (an **assumed** `Ḣ¹ ⇒ Ḣˢ` bootstrap). A uniform `Ḣ¹` bound
  already implies regularity by subcritical continuation, so assuming it ≈
  assuming the conclusion. The `FracSobolevCalculus` argument is unused.
- **The named hypotheses are vacuous.** `HasStrainLowerBound`,
  `HasBoundaryCurvatureBound`, `HasThermostatBound` (§14) have content
  `∃ c ≥ 0` / `∃ α < 1` ≡ `True`; they condition on nothing. The geometric
  "§9" content was never formalized (it lived in `True`-valued fields, now
  removed).
- **The "discharged" capstones cover only trivial classes.** The chain is
  proved unconditionally on the zero solution, constants, and the
  finite-Fourier-support / uniform-ℓ∞ class — where regularity is immediate —
  and is "lifted off the finite-support class" only by *assuming* uniform
  `Ḣˢ` bounds on the Galerkin approximation (i.e. assuming the conclusion; the
  README previously, and correctly, called the lifted BKM hypothesis "vacuous",
  §10.168). None of this bears on regularity for general smooth SQG.

**Genuinely proved and reusable** (independent of the withdrawn framing): the
finite-support Galerkin ODE well-posedness
(`galerkin_time_global_unconditional_realSym`, §10.116) and its `SqgSolution`
packaging; the Fourier-form Rellich–Kondrachov compact embedding
(`FourierBridge.lean`); the torus Riesz / heat-semigroup multiplier machinery;
and the **concrete support-independent Banach-algebra `Ḣˢ` product bound** with
explicit lattice-zeta constant for every `s > 1` (§11.26–§11.27, unconditional).
These are real mathlib-adjacent infrastructure; only the regularity-chain
framing on top of them is withdrawn. The detailed §-by-§ development is recorded
in `CHANGELOG.md`.

<!-- The former 240-line "Capstones" catalog (§10.116–§10.175 Galerkin/Route-A/
Route-B closure narrative) was removed on 2026-05-30: it described the circular
chain above in "discharged / closure / unconditional" language that contradicted
the withdrawal banner. The Lean declarations still exist (with honest docstrings);
their history is in CHANGELOG.md. -->


## What is *not* proven

- **SQG global regularity — conditionally or otherwise.** The §10–§14 chain
  that targeted it is circular (see above and the `RieszTorus.lean` §10 banner).
- **The classical Kato–Ponce fractional Leibniz estimate on `𝕋²`** that would
  discharge the high-`s` Galerkin `Ḣˢ` bootstrap hypothesis. Even with it the
  chain stays circular: it discharges only the *bootstrap* half; the
  load-bearing `MaterialMaxPrinciple` (an assumed uniform `Ḣ¹` bound ≈ the
  conclusion) is untouched.
- **Deriving (H-strain) / (H-bdry) / (H-α) from the SQG dynamics** — the
  research problem the paper documented. The geometric-depletion mechanism they
  encode is, by the project's own numerics, one order short and yields at most
  double-exponential gradient growth (the known Córdoba–Fefferman ceiling), not
  the boundedness that regularity requires.

### Reusable byproducts of Routes A / B (the regularity goal they served is withdrawn)

Routes A and B were two attempts to discharge the Galerkin `Ḣˢ`-bound hypothesis
feeding the circular chain above. That goal is withdrawn, but two byproducts are
genuinely unconditional and reusable:

- **Concrete Banach-algebra `Ḣˢ` product bound** (§11.25–§11.27): support-
  independent, with explicit constant `2^{2s}·(2·latticeZetaConst s)`,
  `latticeZetaConst s = 8·ζ(2s−1) + 4·ζ(2s)`, for every `s > 1`, zero open
  hypotheses — including the Fourier-side form of `Ḣˢ ⊂ L∞` on `𝕋²` (§11.30).
- The companion package
  [`sqg-lean-proofs-fourier`](https://github.com/Brsanch/sqg-lean-proofs-fourier)
  develops the classical Littlewood–Paley / Bony-paraproduct / uniform-in-`N`
  Kato–Ponce commutator content
  (`‖[Jˢ, u·∇]g‖_{L²} ≤ C·(‖∇u‖_{L∞}‖g‖_{Ḣˢ} + ‖u‖_{Ḣˢ}‖∇g‖_{L∞})`), intended
  for reuse by future NS / Euler / MHD formalizations.

The remaining Route A "phases" (Littlewood–Paley primitives, paraproduct
hypothesis types with `C = 0` stubs, zero-datum exemplars) are plumbing toward
the withdrawn goal; the detailed §-by-§ record is in `CHANGELOG.md`. The
SQG-specific energy/Grönwall plumbing lives in `SqgIdentity/FourierBridge.lean`.

### Other open items (see `OPEN.md`)

- Item 1 classical analytical inputs consumed by v0.4.39 structural
  constructors (Arzelà–Ascoli + Cantor diagonal, strong-`L²`
  convergence, per-mode ODE / continuity / `H⁻²` discharges).
- Concrete `HasBumpToIndicatorSequence` witness (§10.135) from
  mathlib's `ContDiffBump` infrastructure.

## Canonical open-items tracker

See [`OPEN.md`](./OPEN.md) in the repo root for the authoritative
list of what remains, linked to tagged releases that closed each
item.

## Building

The project uses Lake and pins mathlib to v4.29.0.

```bash
# elan installs Lean 4 and Lake
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# Fetch pre-built mathlib olean cache, then build
lake exe cache get
lake build
```

A cold build with cache takes roughly five to ten minutes; incremental
builds are fast. Continuous integration runs the same command on every push.

### Paper

The paper is written in `paper/sqg-identity.md` and compiled to PDF via
pandoc + xelatex:

```bash
scripts/build-paper.sh
```

GitHub Actions rebuilds the PDF automatically on pushes to `main` that
touch `paper/sqg-identity.md`; pull requests that modify the markdown
without updating the PDF fail CI.

## Contributing

Bug reports, mathematical error reports, Lean proof improvements, and
typo fixes are welcome. See [`CONTRIBUTING.md`](./CONTRIBUTING.md) for
scope, local setup, and issue templates.

## Layout

```
SqgIdentity.lean             -- root module
SqgIdentity/
  Basic.lean                 -- Theorem 1 + per-mode selection-rule bound
                                (universal CZ form; paper Prop 6.1 precursor):
                                polar + Cartesian forms, ℓ² lift,
                                SqgFourierData bundle, Parseval bridge
  RieszTorus.lean            -- Riesz-transform symbols on 𝕋ᵈ, Leray–Helmholtz,
                                fractional Sobolev scale, fractional + classical
                                heat semigroup suites, §10 Theorem 2 roadmap
paper/
  sqg-identity.md            -- paper source (markdown)
  sqg-identity.pdf           -- paper PDF
lakefile.toml                -- project config
lean-toolchain               -- Lean version
CHANGELOG.md                 -- release-by-release formalization history
```

## Citing

See [`CITATION.cff`](./CITATION.cff) for the canonical citation. The
concept DOI [10.5281/zenodo.19583256](https://doi.org/10.5281/zenodo.19583256)
always resolves to the latest archived release.

## License

MIT — see [`LICENSE`](./LICENSE).
