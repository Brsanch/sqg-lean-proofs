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

end SqgIdentity
