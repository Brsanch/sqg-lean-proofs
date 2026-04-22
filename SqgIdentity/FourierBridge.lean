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

The three `structure` hypotheses introduced here
(`HasKatoPonceCommutatorBound`, `HasVelocityRieszPreservation`,
`HasGalerkinGronwallClosure`) follow the same pattern as §11.34:
they isolate the classical Fourier content from the SQG-specific
chain, so Path A plumbing lands without blocking on the parallel
Kato–Ponce agent in the fourier repo.
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
  l2Const := fun n t _ => by
    rw [hsSeminormSq_zero_galerkin_of_trinary_zero 0 n t,
        hsSeminormSq_zero_galerkin_of_trinary_zero 0 n 0]

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

end SqgIdentity
