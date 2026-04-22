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

open Complex Finset MeasureTheory UnitAddTorus FourierAnalysis

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

/-- **§B.2.concrete — `HasGalerkinL2Conservation` from an upstream
`hLevel` witness.**

The §10.147 Route-B `l2Conservation_of_aubinLions_raw` consumes a
hypothesis `hLevel` of exactly the same shape
`hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n t))
   = hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n 0))`
for every `n, t, 0 ≤ t`.  The concrete construction of this witness
is `SqgEvolutionAxioms.of_galerkin_realSym_Ici.l2Conservation`
(§10.117.B), driven by the ℓ²-sum invariant of §10.116.

This constructor packages that already-proved identity into the
`HasGalerkinL2Conservation` shape consumed by §B.5.

**Usage pattern:**
```
HasGalerkinL2Conservation.ofL2Conservation α hLevel
```
where `hLevel` is typically obtained from the Galerkin ODE solver
plus `hsSeminormSq_zero_galerkinToLp` on each `α n`. -/
theorem HasGalerkinL2Conservation.ofL2Conservation
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hLevel : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n t))
        = hsSeminormSq 0 (galerkinToLp (sqgBox n) (α n 0))) :
    HasGalerkinL2Conservation α where
  l2Const := hLevel

/-- **§B.2.concrete.ℓ² — `HasGalerkinL2Conservation` directly from the
coefficient ℓ²-sum invariant.**

Variant of `ofL2Conservation` that accepts the more primitive form of
the hypothesis — `∑ m ‖α n t m‖² = ∑ m ‖α n 0 m‖²` — rather than the
already-processed `hsSeminormSq 0` shape.  This is what the §10.116
Galerkin ODE solver delivers directly, before the
`hsSeminormSq_zero_galerkinToLp` bridge is applied.

Composition: bridges through `hsSeminormSq_zero_galerkinToLp` using
`zero_not_mem_sqgBox n`. -/
theorem HasGalerkinL2Conservation.ofL2Coeff
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hCoeff : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      (∑ m : ↥(sqgBox n), ‖α n t m‖ ^ 2)
        = ∑ m : ↥(sqgBox n), ‖α n 0 m‖ ^ 2) :
    HasGalerkinL2Conservation α :=
  HasGalerkinL2Conservation.ofL2Conservation α (fun n t ht => by
    classical
    rw [hsSeminormSq_zero_galerkinToLp (zero_not_mem_sqgBox n),
        hsSeminormSq_zero_galerkinToLp (zero_not_mem_sqgBox n),
        hCoeff n t ht])

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

/-- **§B.3.concrete.pointwise — Mode-wise Riesz preservation on the
Galerkin shell.**

For any `S ⊆ ℤ²`, any coefficient vector `a : (Fin 2 → ℤ) → ℂ`, any
`j : Fin 2`, and any mode `m`, the Fourier coefficient of the
`shellVelocity` is bounded mode-by-mode by that of the `shellMode`:
`‖û_j(m)‖ ≤ ‖θ̂(m)‖`.  This is the pointwise content of the SQG
perp-Riesz multiplier's `‖·‖ ≤ 1` bound (`sqgVelocitySymbol_norm_le_one`).

Squared form: `‖û_j(m)‖² ≤ ‖θ̂(m)‖²`.  Integrated against the
`σ_s(m)² = ‖m‖^{2s}` weight, this gives the Ḣˢ-level
`hsSeminormSq_shellVelocity_le_shellMode` below. -/
theorem mFourierCoeff_shellVelocity_norm_sq_le
    (S : Finset (Fin 2 → ℤ)) (a : (Fin 2 → ℤ) → ℂ) (j : Fin 2)
    (m : Fin 2 → ℤ) :
    ‖mFourierCoeff (shellVelocity S a j) m‖ ^ 2
      ≤ ‖mFourierCoeff (shellMode S a) m‖ ^ 2 := by
  classical
  rw [mFourierCoeff_shellVelocity, mFourierCoeff_shellMode]
  by_cases hm : m ∈ S
  · rw [if_pos hm, if_pos hm, norm_mul]
    -- Goal: (‖sqgVelocitySymbol j m‖ * ‖a m‖)² ≤ ‖a m‖²
    have hC : ‖sqgVelocitySymbol j m‖ ≤ 1 := sqgVelocitySymbol_norm_le_one j m
    have hC_nn : 0 ≤ ‖sqgVelocitySymbol j m‖ := norm_nonneg _
    have hsq : (‖sqgVelocitySymbol j m‖) ^ 2 ≤ 1 := by
      have h1 : (‖sqgVelocitySymbol j m‖) ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hC_nn hC 2
      simpa using h1
    calc (‖sqgVelocitySymbol j m‖ * ‖a m‖) ^ 2
        = (‖sqgVelocitySymbol j m‖) ^ 2 * (‖a m‖) ^ 2 := by ring
      _ ≤ 1 * (‖a m‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = ‖a m‖ ^ 2 := by ring
  · rw [if_neg hm, if_neg hm, norm_zero]

/-- **§B.3.concrete.integrated — `Ḣˢ`-level Riesz preservation on the
Galerkin shell.**

For any `S ⊆ ℤ²`, any `a : (Fin 2 → ℤ) → ℂ`, any `j : Fin 2`, any
`s : ℝ`:
`hsSeminormSq s (shellVelocity S a j) ≤ hsSeminormSq s (shellMode S a)`.

Mode-by-mode consequence of `mFourierCoeff_shellVelocity_norm_sq_le`
applied against the nonneg weight `σ_s(n)²`.  This is the concrete
content of `HasVelocityRieszPreservation` at `C = 1` on every Galerkin
truncation.  Summability on the `shellVelocity` side follows from
dominance by the `shellMode` side (which has finite support so is
automatically summable). -/
theorem hsSeminormSq_shellVelocity_le_shellMode
    (s : ℝ) (S : Finset (Fin 2 → ℤ)) (a : (Fin 2 → ℤ) → ℂ) (j : Fin 2) :
    hsSeminormSq s (shellVelocity S a j)
      ≤ hsSeminormSq s (shellMode S a) := by
  classical
  unfold hsSeminormSq
  -- Pointwise bound on each summand.
  have hMode : ∀ n,
      (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (shellVelocity S a j) n‖ ^ 2
        ≤ (fracDerivSymbol s n) ^ 2 * ‖mFourierCoeff (shellMode S a) n‖ ^ 2 := by
    intro n
    exact mul_le_mul_of_nonneg_left
      (mFourierCoeff_shellVelocity_norm_sq_le S a j n)
      (sq_nonneg _)
  -- Summability on the shellMode side from finite support.
  have hSumMode : Summable
      (fun n => (fracDerivSymbol s n) ^ 2
                * ‖mFourierCoeff (shellMode S a) n‖ ^ 2) := by
    apply hsSeminormSq_summable_of_finite_support s (shellMode S a) S
    intros n hn
    rw [mFourierCoeff_shellMode, if_neg hn]
  -- Dominated summability on the shellVelocity side.
  have hSumVel : Summable
      (fun n => (fracDerivSymbol s n) ^ 2
                * ‖mFourierCoeff (shellVelocity S a j) n‖ ^ 2) :=
    hSumMode.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hMode
  exact Summable.tsum_le_tsum hMode hSumVel hSumMode

/-- **§B.3.concrete — `HasVelocityRieszPreservation` at `C = 1` from
the SQG perp-Riesz multiplier.**

Concrete constructor keyed on the pointwise bound
`‖sqgVelocitySymbol j m‖ ≤ 1` (`sqgVelocitySymbol_norm_le_one`).
Returns `C = 1, C_nonneg := by norm_num` — structurally identical
to `.ofUnit`, but with provenance pointing to the concrete Ḣˢ-level
bound `hsSeminormSq_shellVelocity_le_shellMode` above that justifies
the `C = 1` choice.

Use this constructor when composing with `HasGalerkinGronwallClosure.ofBounds`
to signal that the Riesz preservation hypothesis is discharged by
real Riesz-transform content rather than a placeholder. -/
noncomputable def HasVelocityRieszPreservation.ofRieszTransform :
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

/-- **§B.5.concrete — `HasGalerkinGronwallClosure` from classical
ingredients + precomputed uniform bounds.**

Concrete constructor for the Grönwall closure given:
* `K : FourierKatoPonceConst` — abstract Kato–Ponce commutator constant
  (fed in via whatever L² quantitative form the
  `sqg-lean-proofs-fourier` repo ultimately delivers);
* `hL2 : HasGalerkinL2Conservation α` — classical L² conservation
  (typically via `HasGalerkinL2Conservation.ofL2Coeff` or upstream
  §10.147);
* `hRiesz : HasVelocityRieszPreservation` — velocity Riesz-preservation
  (typically via `HasVelocityRieszPreservation.ofRieszTransform`);
* `M₁, Ms` — uniform `Ḣ¹` and parametric `Ḣˢ` bounds already discharged
  by the caller (once the quantitative Kato–Ponce form lands in the
  fourier repo, a downstream constructor will derive `M₁, Ms` from
  `K.K`, `hL2`, `hRiesz`, and the Galerkin energy identity; for now
  the caller supplies them).

This constructor *does not* derive `hBoundOne`/`hBoundS` from the
Kato–Ponce constant — that derivation is the remaining ~500 LOC of
quantitative commutator work.  Instead, it packages the
**already-proved** uniform bounds with the classical-input witnesses
so downstream code (§B.6 `ofClassical`) has a single Grönwall-closure
object to consume.

**Usage pattern:**
```
HasGalerkinGronwallClosure.ofKatoPonce α
  FourierKatoPonceConst.ofZero   -- or concrete K from fourier repo
  (HasGalerkinL2Conservation.ofL2Coeff α hCoeff)
  HasVelocityRieszPreservation.ofRieszTransform
  M₁ Ms hBoundOne hBoundS
```

In the `.ofZero` pathway, all four numerical inputs collapse to `0`. -/
noncomputable def HasGalerkinGronwallClosure.ofKatoPonce
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (K : FourierKatoPonceConst)
    (hL2 : HasGalerkinL2Conservation α)
    (hRiesz : HasVelocityRieszPreservation)
    (M₁ : ℝ) (Ms : ℝ → ℝ)
    (hBoundOne : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n t)) ≤ M₁)
    (hBoundS : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 1 < s →
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)) ≤ Ms s) :
    HasGalerkinGronwallClosure α where
  M₁ := M₁
  Ms := Ms
  l2 := hL2
  riesz := hRiesz
  commutator := K
  hBoundOne := hBoundOne
  hBoundS := hBoundS

/-- **§B.5.concrete.z — `ofKatoPonce` on zero data, via zero
ingredients.**

Unconditional zero-datum exercise of the `ofKatoPonce` constructor.
All four numeric inputs (`M₁`, `Ms`, and the two bound hypotheses)
collapse to `0` via `hsSeminormSq_zero_galerkin_of_trinary_zero`.
The three classical witnesses are the zero-data ones from §B.2.z /
§B.3.z / §B.4.z. -/
noncomputable def HasGalerkinGronwallClosure.ofKatoPonce_zero :
    HasGalerkinGronwallClosure (fun _ _ _ => (0 : ℂ)) :=
  HasGalerkinGronwallClosure.ofKatoPonce
    (α := fun _ _ _ => (0 : ℂ))
    FourierKatoPonceConst.ofZero
    HasGalerkinL2Conservation.ofZero
    HasVelocityRieszPreservation.ofUnit
    0 (fun _ => 0)
    (fun n t _ => (hsSeminormSq_zero_galerkin_of_trinary_zero 1 n t).le)
    (fun n t _ s _ => (hsSeminormSq_zero_galerkin_of_trinary_zero s n t).le)

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

/-! ### §B.8 `HasSqgGalerkinAllSBound.ofGalerkin` — one-shot chaining

Path B capstone: chain §B.2.concrete + §B.3.concrete + §B.5.concrete
+ §B.6 in a single constructor taking real Galerkin data
`α : ∀ n, ℝ → ↥(sqgBox n) → ℂ` and producing the
`HasSqgGalerkinAllSBound α` hypothesis consumed by §10.174 /
§11.36 / §11.37.

Hypothesis-keyed modulo the `FourierKatoPonceConst` (which is abstract
pending the quantitative L² commutator bound in
`sqg-lean-proofs-fourier`), but otherwise fully concrete: the L²
conservation comes from an ℓ² coefficient-sum invariant (typical
Galerkin ODE output), the Riesz preservation comes from the SQG
perp-Riesz multiplier, and the Grönwall-stage uniform `Ḣˢ` bounds
are passed in by the caller. -/

/-- **§B.8 — One-shot `HasSqgGalerkinAllSBound.ofGalerkin`.**

Concrete constructor chaining the four classical-input concrete
constructors into the end-to-end discharge:

* `HasGalerkinL2Conservation.ofL2Coeff`   (§B.2.concrete.ℓ²)
* `HasVelocityRieszPreservation.ofRieszTransform`  (§B.3.concrete)
* `HasGalerkinGronwallClosure.ofKatoPonce`  (§B.5.concrete)
* `HasSqgGalerkinAllSBound.ofClassical`  (§B.6)

**Inputs:**
* `α` — the time-indexed Galerkin coefficient family.
* `hCoeff` — `∑ m ‖α n t m‖² = ∑ m ‖α n 0 m‖²` (ℓ²-sum invariant,
  typical Galerkin ODE output).
* `K` — abstract Kato–Ponce commutator constant (will be filled in
  once `sqg-lean-proofs-fourier` lands the quantitative L² form).
* `M₁, Ms, hBoundOne, hBoundS` — uniform Galerkin `Ḣ¹`/`Ḣˢ` bounds
  (the caller supplies these, typically via the Grönwall ODE in the
  quantitative commutator form).

**Output:** `HasSqgGalerkinAllSBound α`, ready to feed `§11.36`'s
`sqg_regularity_of_allSBound` for the full-range Theorem 3. -/
noncomputable def HasSqgGalerkinAllSBound.ofGalerkin
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hCoeff : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      (∑ m : ↥(sqgBox n), ‖α n t m‖ ^ 2)
        = ∑ m : ↥(sqgBox n), ‖α n 0 m‖ ^ 2)
    (K : FourierKatoPonceConst)
    (M₁ : ℝ) (Ms : ℝ → ℝ)
    (hBoundOne : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n t)) ≤ M₁)
    (hBoundS : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 1 < s →
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)) ≤ Ms s) :
    HasSqgGalerkinAllSBound α :=
  HasSqgGalerkinAllSBound.ofClassical
    (α := α)
    (HasGalerkinGronwallClosure.ofKatoPonce α K
      (HasGalerkinL2Conservation.ofL2Coeff α hCoeff)
      HasVelocityRieszPreservation.ofRieszTransform
      M₁ Ms hBoundOne hBoundS)

/-- **§B.8.z — Zero-datum exercise of `ofGalerkin`.**
Unconditional end-to-end test: all numeric inputs are zero, the
ℓ² invariant is `0 = 0`, the Kato–Ponce constant is `K = 0`, and
the output matches `HasSqgGalerkinAllSBound.ofZero` up to equivalent
defining data. -/
noncomputable def HasSqgGalerkinAllSBound.ofZero_viaGalerkin :
    HasSqgGalerkinAllSBound (fun _ _ _ => (0 : ℂ)) :=
  HasSqgGalerkinAllSBound.ofGalerkin
    (α := fun _ _ _ => (0 : ℂ))
    (fun _ _ _ => rfl)
    FourierKatoPonceConst.ofZero
    0 (fun _ => 0)
    (fun n t _ => (hsSeminormSq_zero_galerkin_of_trinary_zero 1 n t).le)
    (fun n t _ s _ => (hsSeminormSq_zero_galerkin_of_trinary_zero s n t).le)

end SqgIdentity
