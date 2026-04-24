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

On Apple Silicon, if `lake build` crashes with a SoC-level error or hangs,
set `LEAN_NUM_THREADS=1` and build single-file:

```bash
LEAN_NUM_THREADS=1 lake env lean SqgIdentity/Basic.lean
```

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

- **Machine-verified:** Theorem 1 (shear-vorticity identity), the
  universal per-mode selection-rule bound, the conditional Theorem 2
  chain parameterized by `HasStrainLowerBound` + `HasBoundaryCurvatureBound`
  (or `HasThermostatBound`), and the Path B bridge on the
  finite-Fourier-support class.
- **Paper-only (parity-heuristic, not machine-verified):**
  Proposition 6.1's pointwise κ²δ² refinement at the gradient maximum.
- **Open research hypotheses:** (H-strain), (H-bdry), (H-α), (B-spec)
  for general smooth initial data.

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
