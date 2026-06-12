# Contributing

Thank you for taking an interest in this formalization. The scope of
contribution most useful to this project is:

- **Mathematical errors** in the paper (`paper/sqg-identity.md`) — any
  statement that is wrong, any proof step that does not close, any
  constant that is off, any citation that is incorrect.
- **Lean proof improvements** — shorter proofs, better names,
  elimination of redundant hypotheses, replacement of project-local
  lemmas by mathlib lemmas that do the same work.
- **Typos / clarity** — in the paper, the Lean docstrings, the README,
  or the CHANGELOG.
- **Build issues** — if `lake build` fails on a fresh clone, or if
  `scripts/build-paper.sh` fails on a supported setup, please open an
  issue.

If you're considering a **research-direction change** — a new hypothesis,
a restructuring of the main theorem, an extension to a different equation
— please open an issue to discuss before writing the proof. The paper's
conditional-regularity framework has been through multiple rounds of
structural revision and landing arbitrary restructurings without
discussion is likely to introduce regressions.

## Local setup

### Lean formalization

The formalization uses Lean 4 with mathlib v4.29.0 (pinned via
`lean-toolchain` and `lake-manifest.json`). On a fresh clone:

```bash
lake exe cache get    # fetch precompiled mathlib (saves ~hours)
lake build            # build the formalization
```

A full build takes roughly 20–40 minutes on a modern laptop once the
mathlib cache is populated.

On Apple Silicon (M-series), an unthrottled `lake build` — and
`lake exe cache get` — can saturate the APFS daemon (`apfsd`) and trigger a
SoC-watchdog crash during the `.olean` write/finalization burst. Two safe
alternatives:

```bash
# Per-file iteration (no-write; type-checks against the existing cache, ~seconds):
LEAN_NUM_THREADS=1 lake env lean SqgIdentity/Basic.lean

# Full-graph build, panic-safe (throttled to background I/O priority):
taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build
```

The throttled full build is the local **merge gate**: it elaborates every file
fresh, so it catches cross-file duplicate-name conflicts that the single-file
check cannot — making a green local build a sufficient pre-merge check without
depending on CI.

### Paper

The paper is written in Markdown (`paper/sqg-identity.md`) and rendered
to PDF via pandoc + xelatex:

```bash
scripts/build-paper.sh
```

Requires pandoc ≥ 3.0 and a LaTeX engine with xelatex (TeX Live,
MacTeX, MiKTeX). On push to `main`, GitHub Actions rebuilds the PDF
automatically; on pull requests that change the markdown, CI fails
if the committed PDF is out of sync.

## What is / isn't machine-verified

Before you claim that something is "proven" or "verified," check
[`README.md`](./README.md) and [`OPEN.md`](./OPEN.md) for the current
authoritative state:

> **Note (2026-06-12):** the bullets below predate the 2026-05-29
> circularity audit and are superseded by the `OPEN.md` status banner:
> `HasStrainLowerBound`/`HasBoundaryCurvatureBound`/`HasThermostatBound`
> were found **logically vacuous** (≡ `True`), so the "conditional
> Theorem 2 chain" they parameterize conditions on nothing, and the
> former "open research hypotheses" framing is withdrawn. Theorem 1 and
> the per-mode selection-rule bound stand.

- **Machine-verified:** Theorem 1 (shear-vorticity identity), the
  universal per-mode selection-rule bound, the conditional Theorem 2
  chain parameterized by `HasStrainLowerBound` + `HasBoundaryCurvatureBound`
  (or `HasThermostatBound`), and the Path B bridge on the
  finite-Fourier-support class.
- **Paper-only (parity-heuristic, not machine-verified):**
  Proposition 6.1's pointwise κ²δ² refinement at the gradient maximum.
- **Open research hypotheses:** (H-strain), (H-bdry), (H-α), (B-spec)
  for general smooth initial data.

## Anti-vacuity audit probes (adopted 2026-06-12)

Run these against every new Prop-carrying structure or conditional-theorem
target before claiming it has content. Ported from
`eric-wieser/navier-stokes-misformalization` (Olšák/Wieser/Skřivan, which
formally refuted the lean-dojo NS Millennium statement with exactly these
two moves, against their pinned rev `aca048ef`); the same audit class found
the H-strain/H-bdry/H-α vacuity here.

1. **Degenerate instantiation.** Instantiate every field of the structure
   with degenerate data (`∅`, `0`, `default`, trivial witnesses) and try to
   discharge all Prop fields with `simp`/`trivial`. If it compiles, the
   hypothesis is vacuous — it conditions on nothing, and every theorem
   "conditional" on it is unconditional-but-empty.
2. **Bounded refutation.** Attempt `¬ P` via `nofun`/`simp`/`decide` on each
   top-level target Prop. Catches type-level unsatisfiability (their case:
   `Solution.T : ℝ` while the existence branch demands `T = (⊤ : WithTop ℝ)`).

Anti-patterns to grep for (defects, not style):

- `:=`-defaults on load-bearing structure fields (e.g.
  `domain : Set _ := {x | …}`) — defaults are overridable, never
  constraints; state the equation as a separate Prop field `domain_eq`.
- `A ∨ B` dichotomy targets — state and attack the branches separately.
- `∃ c ≥ 0, …`-shaped hypothesis content where any `c` works (≡ `True`).
- Keep the axiom ledger CI-checked: `#guard_msgs in #print axioms`.

A permanent `VacuityProbes.lean` regression file encoding probe 1 against the
known-vacuous §10–§14 structures is the natural follow-up (build-gated).

## Style

- Lean proofs: prefer `by` blocks with structured tactics over long
  `calc` chains where readability is comparable. Don't import
  `mathlib` wholesale when a specific namespace suffices.
- Paper prose: one idea per paragraph. State what is proved, what is
  conjectured, and what is numerical; do not blend.
- Commits: sentence-case subject under 72 characters; body wraps at 72
  and explains *why*, not *what*.

## Reporting issues

Use the GitHub issue tracker. Templates are provided for bug reports
and mathematical questions. For sensitive issues (e.g. claims of
mathematical error that you would prefer to discuss privately first),
email the author listed in `CITATION.cff`.

## License

Contributions are submitted under the MIT License (see
[`LICENSE`](./LICENSE)).
