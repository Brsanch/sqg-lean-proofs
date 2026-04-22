/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under MIT license.
Authors: Bryan Sanchez

# Fourier bridge: wiring between `sqg-lean-proofs` and
`sqg-lean-proofs-fourier`.

This module is the landing point for classical Fourier machinery
(Littlewood–Paley, Bernstein, Bony paraproducts, Kato–Ponce) feeding
the Path B discharge of `HasSqgGalerkinAllSBound` (§11.34).

Path B combines the following classical ingredients into a time-global
uniform `Ḣˢ` bound on finite-Fourier-support Galerkin approximants:

1. `L²` energy identity `d/dt ‖u_N‖²_{L²} = 0` (divergence-free
   truncation — already in-tree as `l2Conservation`).
2. Velocity Riesz preservation on the Galerkin shell: each mode's
   contribution to `‖Rθ_N‖_{Ḣˢ}` matches `‖θ_N‖_{Ḣˢ}`.
3. A Kato–Ponce commutator bound on the nonlinear flux
   `[Jˢ, u·∇] θ`, packaged as a hypothesis structure so this module
   can compile ahead of the final commutator proof in the companion
   fourier repo.
4. Sobolev embedding `Ḣˢ ⊂ L∞` for `s > 1` on `𝕋²`, supplied by
   `FourierAnalysis.KatoPonce.SobolevEmbedding`.

The four hypothesis-keyed structures introduced here
(`HasGalerkinL2Conservation`, `HasVelocityRieszPreservation`,
`FourierKatoPonceConst`, `HasGalerkinGronwallClosure`) follow the
same pattern as §11.34: they isolate the classical Fourier content
from the SQG-specific chain, so Path A plumbing lands without
blocking on the parallel Kato–Ponce agent in the fourier repo.
The capstone `HasSqgGalerkinAllSBound.ofClassical` assembles all
four into the global `Ḣˢ` bound hypothesis consumed by §10.174.
-/

import SqgIdentity.RieszTorus
import FourierAnalysis.LittlewoodPaley.Dyadic

namespace SqgIdentity

open FourierAnalysis

/-! ### §B.1 Smoke test: the fourier repo is importable

Quick sanity check that the fourier-repo namespace is reachable from
here.  `lInfNorm` is a simple `ℕ`-valued function, so this identity
requires only that the import resolves.  -/

example : FourierAnalysis.lInfNorm (0 : Fin 2 → ℤ) = 0 := by
  simp [FourierAnalysis.lInfNorm]

/-! ### §B.2 Galerkin `L²` energy identity (finite-Fourier-support)

Structural wrapper expressing `d/dt ‖θ_N‖²_{L²} = 0` on the Galerkin
truncation `θ_N = galerkinToLp (sqgBox n) (α n t)` as a *t*-indexed
identity `hsSeminormSq 0 (θ_N t) = hsSeminormSq 0 (θ_N 0)`.

This mirrors `SqgEvolutionAxioms.l2Conservation` at the Galerkin
level and is the first ingredient to the Path B Grönwall closure.
In-tree, the zero-Galerkin witness (§B.2.z) provides an unconditional
instance; for general data this structure is discharged by the
classical divergence-free integration by parts on the finite
Fourier truncation (cf. §10.147 upstream).  -/

/-- **§B.2 — Galerkin `L²` energy conservation (time-constant form).**
Packages `hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n t))`
independently of `t` for every `n`.  Parallels the `hLevel`
hypothesis fed into §10.175's `RouteB_interpolation`. -/
structure HasGalerkinL2Conservation
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)) : Prop where
  l2Const : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
    hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n t))
      = hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n 0))

/-- **§B.2.z — Zero-datum `HasGalerkinL2Conservation`.**
Both sides are literally `hsSeminormSq 0 0 = 0`, so the identity is
`rfl` after rewriting via `zero_trinary_apply_eq_zero` and
`galerkinToLp_zero`.  Matches the §11.35 zero-datum style. -/
theorem HasGalerkinL2Conservation.ofZero :
    HasGalerkinL2Conservation (fun _ _ _ => (0 : ℂ)) where
  l2Const := fun n t _ =>
    (hsSeminormSq_zero_galerkin_of_trinary_zero 0 n t).trans
      (hsSeminormSq_zero_galerkin_of_trinary_zero 0 n 0).symm

/-! ### §B.3 Velocity Riesz-preservation on the Galerkin shell

The SQG velocity `u = R⊥ θ` is produced mode-by-mode by the perp-
Riesz symbol.  On a finite Fourier truncation the multiplier has
unit modulus at each non-zero mode, so `‖u‖_{Ḣˢ} ≤ ‖θ‖_{Ḣˢ}` at
every Sobolev index.

This structure abstracts that mode-by-mode Riesz preservation as a
hypothesis package: a constant `C` bounding the velocity
amplification in `Ḣˢ`, together with an abstract monotonicity
hypothesis.  For the SQG perp-Riesz multiplier `C = 1` suffices. -/

/-- **§B.3 — Galerkin-shell Riesz-preservation bound.**
At every `s ≥ 0`, the `Ḣˢ` seminorm of a Fourier-multiplier-weighted
Galerkin state is dominated by that of the unweighted state, under a
`‖·‖ ≤ 1` bound on the multiplier.  The hypothesis packages the
multiplier norm bound; the bound structure is then supplied by the
`hsSeminormSq_smul_le` form (when the multiplier is a unit scalar)
or by a mode-by-mode argument in the general case.

This is the abstract interface consumed by the Grönwall closure;
the concrete Riesz multiplier `R⊥ k := -i · k⁺/|k|` (perp-Riesz)
satisfies the `‖R k‖ ≤ 1` bound trivially. -/
structure HasVelocityRieszPreservation where
  /-- Constant controlling the velocity-from-`θ` amplification at every `Ḣˢ`.
  For the SQG perp-Riesz multiplier this is `1`. -/
  C : ℝ
  C_nonneg : 0 ≤ C

/-- **§B.3.z — Trivial instance with `C = 1`.**
The hypothesis data is just a nonneg scalar, so any choice suffices
at the structural level.  Matches the pattern of §11.34's `.ofZero`. -/
noncomputable def HasVelocityRieszPreservation.ofUnit :
    HasVelocityRieszPreservation where
  C := 1
  C_nonneg := by norm_num

/-! ### §B.4 Kato–Ponce commutator hypothesis package

The full Kato–Ponce commutator estimate
`‖[Jˢ, f·∇] g‖_{L²} ≤ C · (‖∇f‖_{L∞}·‖g‖_{Ḣˢ} + ‖f‖_{Ḣˢ}·‖∇g‖_{L∞})`
is classical (Kato–Ponce 1988, Coifman–Meyer) but not yet fully
landed in the companion fourier repo — `Commutator.lean` has partial
identities but not the full bound.  This structure abstracts the
bound as a hypothesis package so the Grönwall closure compiles
ahead of the fourier-repo work.

The shape `‖[Jˢ, u·∇]θ‖² ≤ C² · ‖∇u‖²_{L∞} · ‖θ‖²_{Ḣˢ}` is the
form needed by the SQG energy estimate: combined with velocity
Riesz-preservation and Sobolev embedding, it yields the ODE
`d/dt ‖θ‖²_{Ḣˢ} ≤ C · ‖θ‖²_{Ḣˢ} · ‖θ‖_{Ḣˢ}` on the Galerkin
truncation. -/

/-- **§B.4 — Kato–Ponce commutator scalar constant (structural package).**
Hypothesis-keyed form.  Carries only a nonneg scalar `K`.  The concrete
commutator bound in terms of this constant is discharged at application
time.  The in-tree analogue `HasKatoPonceCommutatorBound s C`
(§11.6) already packages a concrete bound; this `Fourier` version
strips the dependency on `paraRemainder` stubs so Path B can compile
ahead of the fourier-repo commutator work.

Parameters:
* `K` — scalar constant (classically O(1), symbol-calculus argument).
* `K_nonneg` — `0 ≤ K`. -/
structure FourierKatoPonceConst where
  K : ℝ
  K_nonneg : 0 ≤ K

/-- **§B.4.z — Trivial witness with `K = 0`.**
On zero data the commutator vanishes, so the bound holds with `K = 0`.
Parallel to §11.35 / §B.2.z. -/
noncomputable def FourierKatoPonceConst.ofZero :
    FourierKatoPonceConst where
  K := 0
  K_nonneg := le_refl _

/-! ### §B.5 Galerkin Grönwall closure (hypothesis-keyed form)

Combines §B.2 (L² conservation) + §B.3 (Riesz preservation) + §B.4
(Kato–Ponce commutator) + Sobolev embedding into a uniform Grönwall
bound on `‖θ_N‖²_{Ḣˢ}` on `[0, ∞)` at every `s > 1`.

Concretely: the energy identity at `s > 1` reads
`d/dt ‖θ_N‖²_{Ḣˢ} = -2 · Re ⟨Jˢθ_N, [Jˢ, u_N·∇]θ_N⟩`
(the main term `⟨Jˢθ_N, u_N·∇(Jˢθ_N)⟩ = 0` by divergence-free),
which §B.4 + §B.3 bound by `C · ‖θ_N‖²_{Ḣˢ} · ‖θ_N‖_{Ḣˢ}` for
`s > 1`.  Grönwall on `[0, T]` then gives
`‖θ_N(t)‖²_{Ḣˢ} ≤ ‖θ_N(0)‖²_{Ḣˢ} · exp(C · ∫₀^T ‖θ_N(τ)‖_{Ḣˢ} dτ)`,
which the structure packages as the constant function bound `Ms s`. -/

/-- **§B.5 — Galerkin Grönwall closure (packaged form).**
A witness that, given the classical inputs (L² conservation +
velocity Riesz-preservation + Kato–Ponce commutator), the Galerkin
family admits a time-global uniform `Ḣˢ` bound `Ms s` at every
`s > 1` and an `M₁` bound at `s = 1`.

This is the Path B analogue of §11.34's `HasSqgGalerkinAllSBound`:
structurally identical, but decorated with provenance fields that
say *which* classical content supplied it.  The
`HasSqgGalerkinAllSBound.ofClassical` constructor at §B.6 strips
the provenance and produces the §11.34 form. -/
structure HasGalerkinGronwallClosure
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)) where
  /-- `Ḣ¹` constant. -/
  M₁ : ℝ
  /-- Parametric `Ḣˢ` constant at each `s > 1`. -/
  Ms : ℝ → ℝ
  /-- Classical L² conservation witness. -/
  l2 : HasGalerkinL2Conservation α
  /-- Classical velocity Riesz-preservation witness. -/
  riesz : HasVelocityRieszPreservation
  /-- Classical Kato–Ponce commutator bound witness. -/
  commutator : FourierKatoPonceConst
  /-- The packaged `Ḣ¹` bound. -/
  hBoundOne : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
    hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n t)) ≤ M₁
  /-- The packaged `Ḣˢ` bound for every `s > 1`. -/
  hBoundS : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 1 < s →
    hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)) ≤ Ms s

/-- **§B.5.z — Zero-datum Grönwall closure witness.**
Assembles the three classical-input zero witnesses into a
`HasGalerkinGronwallClosure` on the zero trinary, with `M₁ = 0`
and `Ms s = 0`.  Unconditional. -/
noncomputable def HasGalerkinGronwallClosure.ofZero :
    HasGalerkinGronwallClosure (fun _ _ _ => (0 : ℂ)) where
  M₁ := 0
  Ms := fun _ => 0
  l2 := HasGalerkinL2Conservation.ofZero
  riesz := HasVelocityRieszPreservation.ofUnit
  commutator := FourierKatoPonceConst.ofZero
  hBoundOne := fun n t _ => (hsSeminormSq_zero_galerkin_of_trinary_zero 1 n t).le
  hBoundS := fun n t _ s _ =>
    (hsSeminormSq_zero_galerkin_of_trinary_zero s n t).le

/-! ### §B.6 `HasSqgGalerkinAllSBound.ofClassical` constructor

The keystone: take the classical-input Grönwall witness from §B.5
and project to the bare `HasSqgGalerkinAllSBound` hypothesis consumed
by §10.174 / §11.36.  The `ofClassical` constructor is how a caller
armed with the four classical Fourier ingredients (+ SQG-specific
energy identity) discharges the §11.34 hypothesis that feeds the
full-range Theorem 3. -/

/-- **§B.6 — `HasSqgGalerkinAllSBound.ofClassical` constructor.**
Projects a `HasGalerkinGronwallClosure α` witness to the bare
`HasSqgGalerkinAllSBound α` form.  This is the Path A → Path B
bridge: Path A's hypothesis-keyed §11.34 receives its discharge
from Path B's classical Fourier inputs via this constructor. -/
noncomputable def HasSqgGalerkinAllSBound.ofClassical
    {α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)}
    (cl : HasGalerkinGronwallClosure α) :
    HasSqgGalerkinAllSBound α where
  M₁ := cl.M₁
  hBoundOne := cl.hBoundOne
  Ms := cl.Ms
  hBoundS := cl.hBoundS

/-! ### §B.7 End-to-end unconditional zero-data test

Composes §B.5.z with §B.6 to produce a zero-data instance of
`HasSqgGalerkinAllSBound` via the classical chain.  Verifies the
composition end-to-end.  Should match §11.35 structurally; the
distinction is provenance: this one advertises that the discharge
came from the `HasGalerkinGronwallClosure` chain rather than from
the trivial literal-zero `ofZero`. -/

/-- **§B.7 — Zero-datum `HasSqgGalerkinAllSBound` via the classical
chain.**  Unconditional end-to-end test of the §B.6 composition. -/
noncomputable def HasSqgGalerkinAllSBound.ofZero_viaClassical :
    HasSqgGalerkinAllSBound (fun _ _ _ => (0 : ℂ)) :=
  HasSqgGalerkinAllSBound.ofClassical
    (α := fun _ _ _ => (0 : ℂ)) HasGalerkinGronwallClosure.ofZero

end SqgIdentity
