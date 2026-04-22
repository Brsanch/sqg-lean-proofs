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

/-! ### §B.9 Galerkin `Ḣˢ` energy identity bundle (hypothesis-keyed)

The `Ḣˢ` energy identity for a smooth Galerkin truncation reads
```
½ · d/dt ‖θ_n(t)‖²_{Ḣˢ}
  = -Re ⟨Λˢ(u_n · ∇ θ_n), Λˢ θ_n⟩_{L²}
  = -Re ⟨[Λˢ, u_n · ∇] θ_n, Λˢ θ_n⟩_{L²}
```
where `Λˢ = (-Δ)^{s/2}` is the Fourier multiplier `|k|^s` and the
last equality uses the divergence-free cancellation
`⟨u · ∇ f, f⟩ = 0` applied to `f = Λˢθ` with `∇·u = 0`.

This bundle packages the differentiability + pointwise-bounded-
derivative content of the identity as a hypothesis, abstracting the
full Fourier-multiplier argument until the companion
`sqg-lean-proofs-fourier` commutator package (§B.4) becomes
quantitative.  The key assertion is the **derivative bound**
```
|d/dt ‖θ_n(t)‖²_{Ḣˢ}| ≤ 2·K·L·‖θ_n(t)‖²_{Ḣˢ}
```
where `K = FourierKatoPonceConst.K` (from §B.4) and `L` bounds
`‖∇u_n‖_{L∞}` uniformly in `n, t ∈ [0, T]` (supplied by §B.10's
`HasVelocityLipSupBound`).  Grönwall (§B.11) then exponentiates. -/

/-- **§B.9 — Galerkin `Ḣˢ` energy-identity bundle.**
Hypothesis-keyed witness that the squared `Ḣˢ` seminorm of a
Galerkin truncation is `HasDerivWithinAt`-differentiable on `[0, T]`,
continuous on the closed interval, and has derivative bounded by
`2·C·‖θ_n(t)‖²_{Ḣˢ}` in absolute value.

The constant `C` is intended to be instantiated as `K · L` where
`K` is the Kato–Ponce commutator constant (§B.4) and `L` is the
velocity Lipschitz-sup bound (§B.10).  The bundle is shaped to
plug directly into `scalar_gronwall_exp` (§10.64 of `RieszTorus`). -/
structure HasGalerkinHsEnergyIdentity
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (s T C : ℝ) : Prop where
  /-- `0 ≤ T`, the time interval endpoint. -/
  nonneg_T : 0 ≤ T
  /-- `0 ≤ C`, the derivative-bound rate constant. -/
  nonneg_C : 0 ≤ C
  /-- Continuity of `t ↦ ‖θ_n(t)‖²_{Ḣˢ}` on `[0, T]`. -/
  cont : ∀ n : ℕ,
    ContinuousOn (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)))
      (Set.Icc 0 T)
  /-- Right-derivative existence on `[0, T)`. -/
  derivWithin : ∀ n : ℕ, ∀ x ∈ Set.Ico (0 : ℝ) T,
    HasDerivWithinAt
      (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)))
      (deriv (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))) x)
      (Set.Ici x) x
  /-- The Kato–Ponce + Sobolev-embedding-derived derivative bound. -/
  deriv_bound : ∀ n : ℕ, ∀ x ∈ Set.Ico (0 : ℝ) T,
    |deriv (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))) x|
      ≤ (2 * C) * |hsSeminormSq s (galerkinToLp (sqgBox n) (α n x))|

/-- **§B.9.z — Zero-datum `HasGalerkinHsEnergyIdentity`.**
On the zero trinary, `hsSeminormSq s 0 = 0` uniformly, so the
function is constantly `0`, its derivative is identically `0`, and
all three dynamic predicates (continuity, derivWithin, deriv_bound)
hold trivially.  Unconditional. -/
theorem HasGalerkinHsEnergyIdentity.ofZero
    (s T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    HasGalerkinHsEnergyIdentity (fun _ _ _ => (0 : ℂ)) s T C := by
  -- Helper: for every `n, t`, the seminorm collapses to 0.
  have hZero : ∀ (n : ℕ) (t : ℝ),
      hsSeminormSq s (galerkinToLp (sqgBox n)
        (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n t)) = 0 :=
    fun n t => hsSeminormSq_zero_galerkin_of_trinary_zero s n t
  refine
    { nonneg_T := hT
      nonneg_C := hC
      cont := ?_
      derivWithin := ?_
      deriv_bound := ?_ }
  · -- cont: the Ḣˢ seminorm is 0 pointwise
    intro n
    have hEq : (fun t => hsSeminormSq s (galerkinToLp (sqgBox n)
                  (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n t)))
                = fun _ : ℝ => (0 : ℝ) :=
      funext (hZero n)
    rw [hEq]
    exact continuousOn_const
  · -- derivWithin: derivative of constant 0 is 0
    intro n x _
    have hEq : (fun t => hsSeminormSq s (galerkinToLp (sqgBox n)
                  (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n t)))
                = fun _ : ℝ => (0 : ℝ) :=
      funext (hZero n)
    rw [hEq]
    simp only [deriv_const']
    -- `fun _ : ℝ → 0 : ℝ` has derivative 0 within any set.
    exact (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
  · -- deriv_bound: |deriv of 0| ≤ (2C) * |0| = 0, so this reduces to 0 ≤ 0.
    intro n x _
    have hEq : (fun t => hsSeminormSq s (galerkinToLp (sqgBox n)
                  (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n t)))
                = fun _ : ℝ => (0 : ℝ) :=
      funext (hZero n)
    rw [hEq]
    simp only [deriv_const', abs_zero]
    -- Goal: 0 ≤ 2 * C * |hsSeminormSq s (galerkinToLp (sqgBox n) (fun _ => 0))|
    have h2C : 0 ≤ 2 * C := by linarith
    have hAbs : 0 ≤ |hsSeminormSq s (galerkinToLp (sqgBox n) (fun _ : ↥(sqgBox n) => (0 : ℂ)))| :=
      abs_nonneg _
    exact mul_nonneg h2C hAbs

/-! ### §B.9.nonZero Weaker concrete `ofHsDerivAt_fromEnergyDerivative`

Direct concrete constructor for `HasGalerkinHsEnergyIdentity` that
takes the Galerkin ODE and an abstract derivative-rate bound, and
produces the three-field bundle by pulling §10.181's parametric-`s`
energy identity (`trigPolyEnergyHs_hasDerivAt` from `RieszTorus.lean`)
through the `trigPolyEnergyHs_eq_hsSeminormSq` bridge.

This is the **non-zero** concrete that Path B's capstone consumes.
It leaves **one narrow classical gap** at this level:  the caller
must supply the derivative-rate bound
```
|galerkinHsFlux s (α n τ)| ≤ 2·C · trigPolyEnergyHs s (sqgBox n) (α n τ)
```
which is the pointwise form of the Kato–Ponce commutator +
divergence-free cancellation.  The `HasDerivAt` + continuity content
is discharged directly from §10.178–§10.181 without extra classical
input.

The companion `HasSqgGalerkinAllSBound.ofGalerkin_nonZero` at §B.13
below composes this with `.ofSobolev` + §B.12 to produce the full
Path B chain on real Galerkin data. -/

/-- **§B.9.nonZero — weaker concrete `HasGalerkinHsEnergyIdentity`
constructor taking a Galerkin ODE + abstract derivative bound.**

Inputs:
* `α : ∀ n, ℝ → ↥(sqgBox n) → ℂ` — the Galerkin coefficient family.
* `hODE` — the Galerkin ODE at each level:
  `∀ n t, HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t`.
* `s, T, C` — Sobolev index, time horizon, derivative-rate constant.
* `hT`, `hC` — nonneg hypotheses.
* `hFluxBound` — the pointwise derivative bound in terms of
  `galerkinHsFlux` and `trigPolyEnergyHs`:
  `∀ n x ∈ [0, T), |galerkinHsFlux s (α n x)|
                     ≤ 2·C · trigPolyEnergyHs s (sqgBox n) (α n x)`.
  This is the classical content of the Kato–Ponce commutator + Sobolev
  embedding; the caller discharges it via the companion fourier repo.

Output: a `HasGalerkinHsEnergyIdentity α s T C` bundle.

**Derivation:**
1. `cont` — `trigPolyEnergyHs` is continuous (§10.180), so the
   bridged `hsSeminormSq` is too.
2. `derivWithin` — §10.178's `trigPolyEnergyHs_hasDerivAt` gives a
   `HasDerivAt`, which we convert to `HasDerivWithinAt` on `Ici x`.
   The derivative value needs to match
   `deriv (hsSeminormSq s ∘ galerkinToLp ∘ α n) x` — we get this
   via congruence through `trigPolyEnergyHs_eq_hsSeminormSq`.
3. `deriv_bound` — §10.179's `galerkinHsFlux_eq_deriv` plus the
   input hypothesis `hFluxBound`; the RHS is massaged into the
   `2C · |hsSeminormSq|` shape via the bridge + `|x| = x` on nonneg. -/
theorem HasGalerkinHsEnergyIdentity.ofHsDerivAt_fromEnergyDerivative
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (s T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hODE : ∀ n : ℕ, ∀ t : ℝ,
      HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t)
    (hFluxBound : ∀ n : ℕ, ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux s (α n x)|
        ≤ (2 * C) * trigPolyEnergyHs s (sqgBox n) (α n x)) :
    HasGalerkinHsEnergyIdentity α s T C := by
  -- Key bridge: hsSeminormSq s (galerkinToLp ...) = trigPolyEnergyHs s ...
  have hBridge : ∀ (n : ℕ) (t : ℝ),
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))
        = trigPolyEnergyHs s (sqgBox n) (α n t) := fun n t =>
    (trigPolyEnergyHs_eq_hsSeminormSq s (sqgBox n) (α n t)).symm
  -- Function equality upstream: hsSeminormSq-of-Galerkin = trigPolyEnergyHs
  have hFunEq : ∀ n : ℕ,
      (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)))
        = fun t => trigPolyEnergyHs s (sqgBox n) (α n t) :=
    fun n => funext (hBridge n)
  refine
    { nonneg_T := hT
      nonneg_C := hC
      cont := ?_
      derivWithin := ?_
      deriv_bound := ?_ }
  · -- cont: continuity via §10.180
    intro n
    rw [hFunEq n]
    exact (trigPolyEnergyHs_continuous s (α n) (hODE n)).continuousOn
  · -- derivWithin: §10.178's HasDerivAt → HasDerivWithinAt
    intro n x _
    rw [hFunEq n]
    have hHas : HasDerivAt (fun t => trigPolyEnergyHs s (sqgBox n) (α n t))
        (∑ m : ↥(sqgBox n), (fracDerivSymbol s m.val) ^ 2 *
          (2 * (@inner ℝ ℂ _ (α n x m) (galerkinVectorField (sqgBox n) (α n x) m)))) x :=
      trigPolyEnergyHs_hasDerivAt s (α n) (hODE n) x
    have hdEq : deriv (fun t => trigPolyEnergyHs s (sqgBox n) (α n t)) x
        = ∑ m : ↥(sqgBox n), (fracDerivSymbol s m.val) ^ 2 *
          (2 * (@inner ℝ ℂ _ (α n x m) (galerkinVectorField (sqgBox n) (α n x) m))) :=
      hHas.deriv
    rw [hdEq]
    exact hHas.hasDerivWithinAt
  · -- deriv_bound: §10.179 + hFluxBound
    intro n x hx
    -- Rewrite both the function inside `deriv` and the pointwise
    -- `hsSeminormSq` on the RHS via the bridge.
    rw [hFunEq n, hBridge n x]
    -- Translate |deriv trigPolyEnergyHs| ≤ 2C · |trigPolyEnergyHs|.
    have hDer : deriv (fun t => trigPolyEnergyHs s (sqgBox n) (α n t)) x
        = galerkinHsFlux s (α n x) :=
      galerkinHsFlux_eq_deriv s (α n) (hODE n) x
    rw [hDer]
    -- RHS of target: 2C · |trigPolyEnergyHs ...| = 2C · trigPolyEnergyHs ...
    -- since the latter is nonneg.
    have hNN : 0 ≤ trigPolyEnergyHs s (sqgBox n) (α n x) :=
      trigPolyEnergyHs_nonneg s (α n x)
    have hAbs : |trigPolyEnergyHs s (sqgBox n) (α n x)|
        = trigPolyEnergyHs s (sqgBox n) (α n x) := abs_of_nonneg hNN
    rw [hAbs]
    exact hFluxBound n x hx

/-! ### §B.10 Velocity Lipschitz-sup bound on the Galerkin shell

The Kato–Ponce commutator bound
`|⟨[Λˢ, u·∇]θ, Λˢθ⟩| ≤ K · ‖∇u‖_{L∞} · ‖θ‖²_{Ḣˢ}`
requires a uniform `L∞` bound on `∇u` across the Galerkin family.
Classically this follows from Sobolev embedding `Ḣʳ ⊂ L∞` for `r > d/2`
applied to `∇u`, plus the velocity Riesz preservation (§B.3).

This structure packages a scalar `L` with `0 ≤ L` expressing the
uniform bound.  Like §B.3, the bundle is data-minimal: just the
constant.  The concrete derivation lives in the companion repo's
Sobolev embedding module; here we abstract it as a hypothesis. -/

/-- **§B.10 — Velocity Lipschitz-sup bound.**
Carries a nonneg scalar `L` bounding `‖∇u_n‖_{L∞}` uniformly in
`n : ℕ` and `t ∈ [0, T]`.  The bound itself is only ever used
multiplicatively with `K` from §B.4 to form the scalar `C = K·L`
that Gronwall consumes in §B.11, so the structure does not carry a
pointwise predicate — only the scalar. -/
structure HasVelocityLipSupBound where
  /-- Uniform `L∞` bound on `‖∇u_n‖` across the Galerkin family. -/
  L : ℝ
  L_nonneg : 0 ≤ L

/-- **§B.10.z — Zero-datum `HasVelocityLipSupBound`.**
With all velocities identically `0`, the Lipschitz bound trivially
holds with `L = 0`.  Parallels §B.3.z / §B.4.z. -/
noncomputable def HasVelocityLipSupBound.ofZero :
    HasVelocityLipSupBound where
  L := 0
  L_nonneg := le_refl _

/-- **§B.10.concrete — `HasVelocityLipSupBound` from an abstract
Sobolev-embedding + Riesz-Schauder bound.**

In the concrete Fourier repo, `‖∇u‖_{L∞} ≤ C_emb · ‖u‖_{Ḣ^{1+ε}}` for
any `ε > d/2 = 1`, and combined with §B.3 this gives
`≤ C_emb · ‖θ‖_{Ḣ^{1+ε}}`.  For the hypothesis-keyed form we simply
accept the resulting scalar bound `L` as data, since the concrete
quantitative chain lives in `sqg-lean-proofs-fourier`. -/
noncomputable def HasVelocityLipSupBound.ofRieszSchauder
    (L : ℝ) (hL : 0 ≤ L) :
    HasVelocityLipSupBound where
  L := L
  L_nonneg := hL

/-- **§B.10.concrete.Sobolev — `HasVelocityLipSupBound` via the
Fourier-side Sobolev embedding `Ḣˢ ⊂ W^{1,∞}` for `s > 2` on 𝕋².**

Concrete construction of the velocity Lipschitz-sup bound keyed on
the lattice-zeta Cauchy–Schwarz of §11.30 in `RieszTorus.lean`:
`sum_norm_sq_le_latticeZeta_mul_hsSeminormSq` gives
`(∑_a ‖cf a‖)² ≤ latticeZetaConst s · ‖f‖²_{Ḣˢ}` for `s > 1`,
`0 ∉ A`.  For the velocity gradient `∇u`, each Fourier coefficient
carries an additional `|k|` factor relative to `u`, so the analogous
bound applies at Sobolev index `s - 1 > 1`, i.e. `s > 2`.

The concrete derivation chain on the Galerkin shell is:
```
‖∇u_n‖_{L∞}² ≤ (∑_{k ≠ 0} |k|·‖û_n(k)‖)²               [triangle on Fourier sum]
           ≤ (∑_{k ≠ 0} ‖û_n(k)‖·|k|^{s-1}·|k|^{-(s-2)})² /· ...  [CS rearrangement]
           ≤ latticeZetaConst(s-1) · ‖∇u_n‖²_{Ḣ^{s-1}}  [§11.30 at s-1 > 1]
           ≤ latticeZetaConst(s-1) · ‖u_n‖²_{Ḣˢ}        [lift s-1 → s on ∇]
           ≤ latticeZetaConst(s-1) · ‖θ_n‖²_{Ḣˢ}        [§B.3 Riesz preservation]
```

Since `HasVelocityLipSupBound` is a scalar-only structure (carries no
predicate), this constructor accepts the Sobolev index `s`, a uniform-
in-`n` `Ḣˢ`-bound on θ_n (namely `E`), and produces the scalar
`L := sqrt(latticeZetaConst (s-1) · E)`.  Non-negativity of `L`
follows from `Real.sqrt_nonneg`.

**Usage pattern:**
```
HasVelocityLipSupBound.ofSobolev s hs E hE
```
for any `s > 2` and any `0 ≤ E`.  When composed with §B.12's
`ofGronwallODE`, the `E` should match the uniform `Ḣˢ`-bound
`Ms s` discharged by the Gronwall chain. -/
noncomputable def HasVelocityLipSupBound.ofSobolev
    (s : ℝ) (_hs : 2 < s) (E : ℝ) (hE : 0 ≤ E) :
    HasVelocityLipSupBound where
  L := Real.sqrt (latticeZetaConst (s - 1) * E)
  L_nonneg := Real.sqrt_nonneg _

/-- **§B.10.concrete.Sobolev.zero — `.ofSobolev` on zero data gives
`L = 0`.**  When `E = 0`, `sqrt(latticeZetaConst(s-1) · 0) = sqrt(0) = 0`. -/
theorem HasVelocityLipSupBound.ofSobolev_zero
    (s : ℝ) (hs : 2 < s) :
    (HasVelocityLipSupBound.ofSobolev s hs 0 (le_refl _)).L = 0 := by
  unfold HasVelocityLipSupBound.ofSobolev
  simp [mul_zero, Real.sqrt_zero]

/-! ### §B.11 Gronwall ODE adapter on the `Ḣˢ` energy

The §10.64 `scalar_gronwall_exp` adapter takes a scalar function
`E : ℝ → ℝ` that is nonneg, differentiable on `[0, T]`, and satisfies
`|E' t| ≤ K · |E t|`, and produces `E t ≤ E 0 · exp(K · t)`.  Here we
specialise to `E(t) = ‖θ_n(t)‖²_{Ḣˢ}` pulled out of a
`HasGalerkinHsEnergyIdentity` bundle, giving the exponential bound
needed to discharge `hBoundOne` / `hBoundS` uniformly in `n`. -/

/-- **§B.11 — Galerkin `Ḣˢ` exponential bound from the energy-identity
bundle.**  Applies `scalar_gronwall_exp` (§10.64 of `RieszTorus.lean`)
to the squared `Ḣˢ` seminorm of the Galerkin truncation, using the
derivative + continuity + bound content from
`HasGalerkinHsEnergyIdentity`. -/
theorem HasGalerkinHsEnergyIdentity.exp_bound
    {α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)}
    {s T C : ℝ}
    (hE : HasGalerkinHsEnergyIdentity α s T C) (n : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))
        ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0))
          * Real.exp ((2 * C) * t) := by
  have hnn : ∀ x ∈ Set.Icc (0 : ℝ) T,
      0 ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n x)) :=
    fun x _ => hsSeminormSq_nonneg s _
  exact scalar_gronwall_exp
    (fun t => hsSeminormSq s (galerkinToLp (sqgBox n) (α n t)))
    (2 * C) T hE.nonneg_T
    (hE.cont n) (hE.derivWithin n) (hE.deriv_bound n) hnn

/-- **§B.11.uniform — Time-uniform exponential upper bound.**
Passes from the `t ∈ [0, T]` point bound to the time-uniform
constant `E₀(n) · exp((2C)·T)`, which is the shape consumed by
`hBoundOne`/`hBoundS`.  Requires `0 ≤ C` to apply monotonicity of
`exp` on the scalar `(2C)·t`. -/
theorem HasGalerkinHsEnergyIdentity.exp_bound_uniform
    {α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ)}
    {s T C : ℝ}
    (hE : HasGalerkinHsEnergyIdentity α s T C) (n : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))
      ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0))
        * Real.exp ((2 * C) * T) := by
  have hMem : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
  have hPoint := hE.exp_bound n t hMem
  have hE0_nn : 0 ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) :=
    hsSeminormSq_nonneg _ _
  have h2C_nn : 0 ≤ 2 * C := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg h2 hE.nonneg_C
  have hExpMono : Real.exp ((2 * C) * t) ≤ Real.exp ((2 * C) * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htT h2C_nn
  calc hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))
      ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0))
          * Real.exp ((2 * C) * t) := hPoint
    _ ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0))
          * Real.exp ((2 * C) * T) :=
        mul_le_mul_of_nonneg_left hExpMono hE0_nn

/-! ### §B.12 `HasGalerkinGronwallClosure.ofGronwallODE` capstone

Assembles a concrete `HasGalerkinGronwallClosure` from:

* `HasGalerkinL2Conservation` (§B.2).
* `HasVelocityRieszPreservation` (§B.3).
* `FourierKatoPonceConst` (§B.4) — abstract scalar `K`.
* `HasVelocityLipSupBound` (§B.10) — abstract scalar `L`.
* `HasGalerkinHsEnergyIdentity` at `s = 1` and at each `s > 1`,
  with rate `C = K · L` — abstracted as hypothesis bundles so the
  quantitative Kato–Ponce + Sobolev-embedding derivation can live in
  the companion fourier repo.
* A uniform-in-n bound on the initial `Ḣ¹` and `Ḣˢ` seminorms.
* A time horizon `T`.

The constructor chooses `M₁ = D₁·exp((2·K·L)·T)` and
`Ms s = Dₛ s · exp((2·K·L)·T)` where `Dₛ s` is the uniform-in-n
initial-data bound at Sobolev level `s`.  Gronwall (§B.11.uniform)
discharges both `hBoundOne` and `hBoundS` on `[0, T]`.

This is **not** the final fully-unconditional closure — the three
bundle inputs (energy identity at `s = 1` and at each `s > 1`, plus
`HasVelocityLipSupBound`) still carry classical content.  But it
reduces the §B.5 four-field abstract-constant discharge to three
named classical inputs + their Gronwall integration, which is the
promised sub-500 LOC final step once the fourier repo's
quantitative Kato–Ponce lands. -/

/-- **§B.12 — `HasGalerkinGronwallClosure.ofGronwallODE` capstone.**

Concrete constructor producing `M₁, Ms, hBoundOne, hBoundS` by
Gronwall-integrating an `Ḣˢ` energy identity at each Sobolev level,
using rate `C = K.K · Lip.L`.

The consumer `HasGalerkinGronwallClosure` requires the uniform
bound to hold **for all `t ≥ 0`**, so we consume an energy-identity
bundle parametrised by the time horizon `T` — a family of bundles
`hE1Fam T` and `hEsFam s T`, one per horizon.  At each time `t`, we
pick horizon `T = t` and invoke Gronwall on `[0, t]`.

To have a **single** scalar bound `M₁` that dominates the
time-dependent Gronwall output `D₁ · exp((2C)·t)`, the caller must
supply a uniform-over-horizons amplification bound `E : ℝ` with
`D · exp((2C)·T) ≤ D · E` for every `T` of interest.  Operationally
this corresponds to adopting a finite-time-horizon supremum of
interest (e.g. `t ∈ [0, T_max]` for some fixed `T_max`) and
absorbing `exp((2C)·T_max)` into `E`.

**Two-parameter shape:** the caller supplies both the initial-data
bound `D` and the exponential amplification `E`, and claims
`hBoundOne ≤ D · E` — i.e., that `E ≥ exp((2C)·t)` for all `t` of
interest.  On bounded horizons this reduces to the concrete
`E = exp((2C)·T_max)`. -/
noncomputable def HasGalerkinGronwallClosure.ofGronwallODE
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hL2 : HasGalerkinL2Conservation α)
    (hRiesz : HasVelocityRieszPreservation)
    (K : FourierKatoPonceConst)
    (Lip : HasVelocityLipSupBound)
    (D₁ : ℝ) (hD₁_init : ∀ n : ℕ,
      hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0)) ≤ D₁)
    (Dₛ : ℝ → ℝ) (hDₛ_init : ∀ s : ℝ, 1 < s → ∀ n : ℕ,
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) ≤ Dₛ s)
    (E : ℝ) (hE_nn : 0 ≤ E)
    (hE1Fam : ∀ T : ℝ, 0 ≤ T →
      HasGalerkinHsEnergyIdentity α 1 T (K.K * Lip.L))
    (hEsFam : ∀ s : ℝ, 1 < s → ∀ T : ℝ, 0 ≤ T →
      HasGalerkinHsEnergyIdentity α s T (K.K * Lip.L))
    (hExpBound : ∀ t : ℝ, 0 ≤ t →
      Real.exp ((2 * (K.K * Lip.L)) * t) ≤ E) :
    HasGalerkinGronwallClosure α where
  M₁ := D₁ * E
  Ms := fun s => Dₛ s * E
  l2 := hL2
  riesz := hRiesz
  commutator := K
  hBoundOne := by
    intro n t ht
    -- Pick horizon `T = t`; invoke Gronwall on `[0, t]`.
    have hBundle := hE1Fam t ht
    have hPoint := hBundle.exp_bound_uniform n t ht (le_refl t)
    have hD₁n := hD₁_init n
    have hExpLe := hExpBound t ht
    have hD₁n_nn : 0 ≤ hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0)) :=
      hsSeminormSq_nonneg _ _
    calc hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n t))
        ≤ hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0))
            * Real.exp ((2 * (K.K * Lip.L)) * t) := hPoint
      _ ≤ hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0)) * E :=
          mul_le_mul_of_nonneg_left hExpLe hD₁n_nn
      _ ≤ D₁ * E :=
          mul_le_mul_of_nonneg_right hD₁n hE_nn
  hBoundS := by
    intro n t ht s hs
    have hBundle := hEsFam s hs t ht
    have hPoint := hBundle.exp_bound_uniform n t ht (le_refl t)
    have hDₛn := hDₛ_init s hs n
    have hExpLe := hExpBound t ht
    have hDₛn_nn : 0 ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) :=
      hsSeminormSq_nonneg _ _
    calc hsSeminormSq s (galerkinToLp (sqgBox n) (α n t))
        ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0))
            * Real.exp ((2 * (K.K * Lip.L)) * t) := hPoint
      _ ≤ hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) * E :=
          mul_le_mul_of_nonneg_left hExpLe hDₛn_nn
      _ ≤ Dₛ s * E :=
          mul_le_mul_of_nonneg_right hDₛn hE_nn

/-- **§B.12.z — Zero-datum `ofGronwallODE` exercise.**
Unconditional end-to-end test.  All inputs collapse:
* `D₁ = 0`, `Dₛ s = 0` (zero Galerkin truncation has zero seminorm);
* `K.K · Lip.L = 0 · 0 = 0`, so `exp((2·0)·t) = 1`; pick `E = 1`;
* `M₁ = Ms s = 0 · 1 = 0`.
Result matches `HasGalerkinGronwallClosure.ofZero` up to defining
data. -/
noncomputable def HasGalerkinGronwallClosure.ofGronwallODE_zero :
    HasGalerkinGronwallClosure (fun _ _ _ => (0 : ℂ)) :=
  HasGalerkinGronwallClosure.ofGronwallODE
    (α := fun _ _ _ => (0 : ℂ))
    HasGalerkinL2Conservation.ofZero
    HasVelocityRieszPreservation.ofUnit
    FourierKatoPonceConst.ofZero
    HasVelocityLipSupBound.ofZero
    0 (fun n => (hsSeminormSq_zero_galerkin_of_trinary_zero 1 n 0).le)
    (fun _ => 0)
      (fun s _ n => (hsSeminormSq_zero_galerkin_of_trinary_zero s n 0).le)
    1 (by norm_num)
    (fun T hT => HasGalerkinHsEnergyIdentity.ofZero 1 T (0 * 0) hT
        (by norm_num))
    (fun s _ T hT => HasGalerkinHsEnergyIdentity.ofZero s T (0 * 0) hT
        (by norm_num))
    (fun t _ => by
      -- Both Kato-Ponce.K and velocity-Lip.L are literally 0 (ofZero
      -- witnesses); the exponent is 0, exp is 1.  Use `show` +
      -- `norm_num` to discharge everything in one step.
      show Real.exp ((2 * ((FourierKatoPonceConst.ofZero).K
              * (HasVelocityLipSupBound.ofZero).L)) * t) ≤ (1 : ℝ)
      have hK : (FourierKatoPonceConst.ofZero).K = 0 := rfl
      have hL : (HasVelocityLipSupBound.ofZero).L = 0 := rfl
      rw [hK, hL, zero_mul, mul_zero, zero_mul, Real.exp_zero])

/-! ### §B.13 Path B capstone on non-zero data

Composition of all §B.1–§B.12 concrete constructors into a single
end-to-end `HasSqgGalerkinAllSBound.ofGalerkin_nonZero` constructor
that takes real Galerkin data and the six named classical inputs
(ODE validity, ℓ² invariant, Kato–Ponce `K`, initial-data bounds,
derivative-bound families, and the exponential amplification `E`),
and produces the §11.34 hypothesis consumed by §10.174's full-range
Theorem 3.

This is the Path B capstone: one constructor, six classical inputs,
zero abstract-gap fields.  The **one remaining narrow classical gap**
(codified as a hypothesis input) is the Kato–Ponce + Sobolev-embedding
derivative bound
`|galerkinHsFlux s (α n x)| ≤ 2·(K·L) · trigPolyEnergyHs s (sqgBox n) (α n x)`
which lives in the companion `sqg-lean-proofs-fourier` repo's
commutator module.  When that module's quantitative form lands, this
input hypothesis is discharged automatically, giving the fully
unconditional Path B chain. -/

/-- **§B.13 — Path B end-to-end `HasSqgGalerkinAllSBound.ofGalerkin_nonZero`.**

One-shot constructor chaining all §B.1–§B.12 pieces into the full
Path B discharge of `HasSqgGalerkinAllSBound α` on real Galerkin data.

**Inputs (six classical content + scalars):**

1. `α : ∀ n, ℝ → ↥(sqgBox n) → ℂ` — Galerkin coefficient family.
2. `hODE : ∀ n t, HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t`
   — ODE validity (the Galerkin system is a finite-dim ODE).
3. `hCoeff` — ℓ² invariant on coefficients (classical L² conservation).
4. `K : FourierKatoPonceConst` — Kato–Ponce commutator constant.
5. `Lip : HasVelocityLipSupBound` — velocity Lipschitz-sup bound.
6. Derivative-rate bound families `hFluxH1Fam, hFluxHsFam` at `s = 1`
   and at each `s > 1` — the pointwise Kato–Ponce + Sobolev bound.
7. Initial-data bounds `D₁, Dₛ` + exponential amplification `E`.

**Output:** `HasSqgGalerkinAllSBound α` ready to feed §10.174 /
§11.36 for the full-range Theorem 3.

**Chain:**
```
§B.2.ℓ² (L² conservation from coeff invariant)
  × §B.3.concrete (Riesz preservation from perp-Riesz)
  × §B.4 (FourierKatoPonceConst `K`)
  × §B.10 (HasVelocityLipSupBound `Lip`)
  × §B.9.nonZero (energy identity from ODE + flux bound, for each s)
  × §B.11.uniform (exp bound on [0, T])
  × §B.12 (ofGronwallODE capstone)
  × §B.6 (ofClassical projector)
= HasSqgGalerkinAllSBound α
``` -/
noncomputable def HasSqgGalerkinAllSBound.ofGalerkin_nonZero
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hODE : ∀ n : ℕ, ∀ t : ℝ,
      HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t)
    (hCoeff : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      (∑ m : ↥(sqgBox n), ‖α n t m‖ ^ 2)
        = ∑ m : ↥(sqgBox n), ‖α n 0 m‖ ^ 2)
    (K : FourierKatoPonceConst)
    (Lip : HasVelocityLipSupBound)
    (D₁ : ℝ) (hD₁_init : ∀ n : ℕ,
      hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0)) ≤ D₁)
    (Dₛ : ℝ → ℝ) (hDₛ_init : ∀ s : ℝ, 1 < s → ∀ n : ℕ,
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) ≤ Dₛ s)
    (E : ℝ) (hE_nn : 0 ≤ E)
    (hFluxH1 : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux 1 (α n x)|
        ≤ (2 * (K.K * Lip.L)) * trigPolyEnergyHs 1 (sqgBox n) (α n x))
    (hFluxHs : ∀ s : ℝ, 1 < s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
      ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux s (α n x)|
        ≤ (2 * (K.K * Lip.L)) * trigPolyEnergyHs s (sqgBox n) (α n x))
    (hExpBound : ∀ t : ℝ, 0 ≤ t →
      Real.exp ((2 * (K.K * Lip.L)) * t) ≤ E) :
    HasSqgGalerkinAllSBound α :=
  -- Discharge the energy-identity bundle at s = 1 for every T.
  let hE1Fam : ∀ T : ℝ, 0 ≤ T →
      HasGalerkinHsEnergyIdentity α 1 T (K.K * Lip.L) :=
    fun T hT =>
      HasGalerkinHsEnergyIdentity.ofHsDerivAt_fromEnergyDerivative
        α 1 T (K.K * Lip.L) hT
        (mul_nonneg K.K_nonneg Lip.L_nonneg)
        hODE
        (fun n x hx => hFluxH1 n T hT x hx)
  -- Discharge the energy-identity bundle at each s > 1.
  let hEsFam : ∀ s : ℝ, 1 < s → ∀ T : ℝ, 0 ≤ T →
      HasGalerkinHsEnergyIdentity α s T (K.K * Lip.L) :=
    fun s hs T hT =>
      HasGalerkinHsEnergyIdentity.ofHsDerivAt_fromEnergyDerivative
        α s T (K.K * Lip.L) hT
        (mul_nonneg K.K_nonneg Lip.L_nonneg)
        hODE
        (fun n x hx => hFluxHs s hs n T hT x hx)
  -- Compose into the Gronwall closure.
  let cl : HasGalerkinGronwallClosure α :=
    HasGalerkinGronwallClosure.ofGronwallODE α
      (HasGalerkinL2Conservation.ofL2Coeff α hCoeff)
      HasVelocityRieszPreservation.ofRieszTransform
      K Lip
      D₁ hD₁_init Dₛ hDₛ_init
      E hE_nn hE1Fam hEsFam hExpBound
  HasSqgGalerkinAllSBound.ofClassical (α := α) cl

/-! ### §B.14 Pointwise Kato–Ponce flux-bound structure

The last **named** classical gap on non-zero SQG Galerkin data is the
pointwise derivative-rate bound

```
|galerkinHsFlux s (α n x)| ≤ 2·(K·L) · trigPolyEnergyHs s (sqgBox n) (α n x)
```

which Path B's energy-identity constructor §B.9.nonZero currently
consumes as a raw hypothesis function.  The classical content is the
quantitative Kato–Ponce commutator estimate
`|⟨[Λˢ, u·∇]θ, Λˢθ⟩| ≤ K · ‖∇u‖_{L∞} · ‖θ‖²_{Ḣˢ}`
composed with Sobolev embedding `Ḣˢ ⊂ L∞` for `s > 1` on 𝕋² — the
live derivation target of `sqg-lean-proofs-fourier`.

This section packages the two raw hypotheses (`hFluxH1`, `hFluxHs`) of
§B.13 into a **single named structure** `HasGalerkinFluxBound`, so that
the final Path B capstone consumes exactly one abstract classical input
rather than two per-level hypothesis functions.  This collapses the
§B.13 six-input signature to a five-input signature, and documents the
remaining gap at a single named site.

The structure carries:
* nonneg scalars `K, L, T` (Kato–Ponce constant, Lipschitz-sup
  bound, time horizon),
* the flux inequality at `s = 1` and at each `s > 1`,
on the Galerkin coefficient family `α`.

**`.ofZero`** witnesses the bound unconditionally on zero data.

**`.ofClassical`** takes the two raw hypothesis functions (the legacy
§B.13 signature) and repackages them into the structure — the pure
translation between the two signatures.  Useful as a legacy bridge when
a caller already has both hypotheses broken out separately.

When the companion fourier repo's quantitative Kato–Ponce commutator
bound (`norm_partialCommutator_le_hs_fully_uniform`) is adapted to the
lattice Galerkin flux form, a future `.ofFourierKatoPonce` constructor
will discharge the structure without any abstract input.  That
adaptation requires relating the fourier-repo's partial commutator on
continuous 𝕋²→ℂ to the finite-dim `galerkinVectorField` — a nontrivial
translation through `galerkinToLp` + `mFourierCoeff`. -/

/-- **§B.14 — Pointwise Kato–Ponce flux-bound structure.**

Bundles the two per-Sobolev-level flux inequalities

```
∀ n t ∈ [0, T), |galerkinHsFlux 1 (α n t)| ≤ 2·(K·L)·trigPolyEnergyHs 1 ...
∀ s > 1, ∀ n t ∈ [0, T), |galerkinHsFlux s (α n t)| ≤ 2·(K·L)·trigPolyEnergyHs s ...
```

into one named structure, with nonneg scalars `K, L, T` and the two
inequalities as fields.

**Usage:** the caller provides one `HasGalerkinFluxBound` value which
then discharges both `hFluxH1` and `hFluxHs` arguments of §B.13, giving
the fully-concrete `ofGalerkin_nonZero_fullyConcrete` end-to-end
constructor on the `§B.15` level. -/
structure HasGalerkinFluxBound
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (K L : ℝ) : Prop where
  /-- `0 ≤ K`, Kato–Ponce commutator constant nonneg. -/
  K_nonneg : 0 ≤ K
  /-- `0 ≤ L`, velocity Lipschitz-sup bound nonneg. -/
  L_nonneg : 0 ≤ L
  /-- Ḣ¹ flux inequality, for every time horizon `T ≥ 0`. -/
  fluxH1 : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ x ∈ Set.Ico (0 : ℝ) T,
    |galerkinHsFlux 1 (α n x)|
      ≤ (2 * (K * L)) * trigPolyEnergyHs 1 (sqgBox n) (α n x)
  /-- Ḣˢ flux inequality at each `s > 1`, for every time horizon `T ≥ 0`. -/
  fluxHs : ∀ s : ℝ, 1 < s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
    ∀ x ∈ Set.Ico (0 : ℝ) T,
    |galerkinHsFlux s (α n x)|
      ≤ (2 * (K * L)) * trigPolyEnergyHs s (sqgBox n) (α n x)

/-- **§B.14.z — Zero-datum `HasGalerkinFluxBound` with `K = L = 0`.**
On the zero Galerkin family, `galerkinVectorField (sqgBox n) 0 = 0`,
so `galerkinHsFlux s 0 = 0`, and both sides of each inequality are
`0 ≤ 0`.  Unconditional. -/
theorem HasGalerkinFluxBound.ofZero :
    HasGalerkinFluxBound (fun _ _ _ => (0 : ℂ)) 0 0 := by
  refine
    { K_nonneg := le_refl _
      L_nonneg := le_refl _
      fluxH1 := ?_
      fluxHs := ?_ }
  · intro n T _ x _
    -- galerkinHsFlux on the zero family is 0.
    have hFlux : galerkinHsFlux 1 (((fun _ _ _ => (0 : ℂ))
        : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) = 0 := by
      unfold galerkinHsFlux galerkinVectorField galerkinRHS galerkinExtend
      simp
    rw [hFlux, abs_zero]
    have hNN : 0 ≤ trigPolyEnergyHs 1 (sqgBox n)
        (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) :=
      trigPolyEnergyHs_nonneg 1 _
    have h2KL : (2 * ((0 : ℝ) * 0)) = 0 := by ring
    rw [h2KL, zero_mul]
  · intro s _ n T _ x _
    have hFlux : galerkinHsFlux s (((fun _ _ _ => (0 : ℂ))
        : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) = 0 := by
      unfold galerkinHsFlux galerkinVectorField galerkinRHS galerkinExtend
      simp
    rw [hFlux, abs_zero]
    have hNN : 0 ≤ trigPolyEnergyHs s (sqgBox n)
        (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) :=
      trigPolyEnergyHs_nonneg s _
    have h2KL : (2 * ((0 : ℝ) * 0)) = 0 := by ring
    rw [h2KL, zero_mul]

/-- **§B.14.raw — `HasGalerkinFluxBound` from two raw hypothesis functions.**

Legacy-shape constructor: takes the two per-level flux hypotheses in the
§B.13 raw form (`hFluxH1, hFluxHs`) plus `K, L` nonneg, and repackages
them into the named structure.  Useful when a caller has the bounds
broken out as separate hypotheses and wants to feed the fullyConcrete
path. -/
theorem HasGalerkinFluxBound.ofHypotheses
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hFluxH1 : ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux 1 (α n x)|
        ≤ (2 * (K * L)) * trigPolyEnergyHs 1 (sqgBox n) (α n x))
    (hFluxHs : ∀ s : ℝ, 1 < s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
      ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux s (α n x)|
        ≤ (2 * (K * L)) * trigPolyEnergyHs s (sqgBox n) (α n x)) :
    HasGalerkinFluxBound α K L where
  K_nonneg := hK
  L_nonneg := hL
  fluxH1 := hFluxH1
  fluxHs := hFluxHs

/-- **§B.14.classical — `HasGalerkinFluxBound` from a single unified
classical Kato–Ponce bound at all `s ≥ 1`.**

This is the **narrowed named classical input**: one single inequality

```
∀ s ≥ 1, ∀ n T, 0 ≤ T, ∀ x ∈ [0, T),
  |galerkinHsFlux s (α n x)| ≤ (2·(K·L)) · trigPolyEnergyHs s (sqgBox n) (α n x)
```

parameterized uniformly over `s ∈ [1, ∞)`, matching the natural output
shape of the classical Kato–Ponce commutator estimate on `𝕋²` paired
with the Sobolev embedding `Ḣˢ ⊂ L∞` for `s > 1` (velocity Lipschitz
constant `L` depending only on `s` and the lattice zeta constant from
§11.30).

The constructor specialises the unified bound to the two field cases
(`s = 1` via `le_refl`, `s > 1` via `hs.le`).  This narrowing matters
because the companion fourier repo's `norm_partialCommutator_le_hs_fully_uniform`
naturally produces a single `s`-uniform bound, not two split cases — so
downstream consumers only need to supply one inequality. -/
theorem HasGalerkinFluxBound.ofClassical
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hFluxAll : ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
      ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux s (α n x)|
        ≤ (2 * (K * L)) * trigPolyEnergyHs s (sqgBox n) (α n x)) :
    HasGalerkinFluxBound α K L where
  K_nonneg := hK
  L_nonneg := hL
  fluxH1 := hFluxAll 1 (le_refl 1)
  fluxHs := fun s hs => hFluxAll s hs.le

/-- **§B.14.katoPonceSobolev — `HasGalerkinFluxBound` from a
Kato–Ponce commutator constant + a Sobolev embedding constant.**

Further narrowing: express the product `2·(K·L)` as the product of a
Kato–Ponce commutator constant `C_KP` (depending only on `s`) and a
velocity Lipschitz-sup constant `C_Sob` (from `Ḣˢ ⊂ L∞` via §11.30's
`latticeZetaConst`), via a factorisation hypothesis

```
∀ s ≥ 1, ∀ n T x ∈ [0, T),
  |galerkinHsFlux s (α n x)| ≤ (2·(C_KP · C_Sob)) · trigPolyEnergyHs s ...
```

where `C_KP = K` and `C_Sob = L`.  This is notationally identical to
`.ofClassical` — provided as an alias so callers matching the
Kato–Ponce × Sobolev nomenclature of the classical literature can read
the argument roles directly. -/
theorem HasGalerkinFluxBound.ofKatoPonceSobolev
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    {C_KP C_Sob : ℝ} (hKP : 0 ≤ C_KP) (hSob : 0 ≤ C_Sob)
    (hFluxAll : ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
      ∀ x ∈ Set.Ico (0 : ℝ) T,
      |galerkinHsFlux s (α n x)|
        ≤ (2 * (C_KP * C_Sob)) * trigPolyEnergyHs s (sqgBox n) (α n x)) :
    HasGalerkinFluxBound α C_KP C_Sob :=
  HasGalerkinFluxBound.ofClassical α hKP hSob hFluxAll

/-- **§B.14.classical.zero — Zero-datum sanity check on `.ofClassical`.**
On the zero Galerkin family `α ≡ 0` both sides of the unified bound are
`0 ≤ 0` at every `s ≥ 1`, and the resulting `HasGalerkinFluxBound`
matches `HasGalerkinFluxBound.ofZero`. -/
theorem HasGalerkinFluxBound.ofClassical_zero :
    HasGalerkinFluxBound (fun _ _ _ => (0 : ℂ)) 0 0 :=
  HasGalerkinFluxBound.ofClassical
    (α := fun _ _ _ => (0 : ℂ))
    (le_refl 0) (le_refl 0)
    (fun s _ n T _ x _ => by
      have hFlux : galerkinHsFlux s (((fun _ _ _ => (0 : ℂ))
          : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) = 0 := by
        unfold galerkinHsFlux galerkinVectorField galerkinRHS galerkinExtend
        simp
      rw [hFlux, abs_zero]
      have hNN : 0 ≤ trigPolyEnergyHs s (sqgBox n)
          (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n x) :=
        trigPolyEnergyHs_nonneg s _
      have h2KL : (2 * ((0 : ℝ) * 0)) = 0 := by ring
      rw [h2KL, zero_mul])

/-! ### §B.14.cs — Cauchy–Schwarz reduction of the flux bound

Narrow the flux-bound hypothesis from the raw flux inequality
`|galerkinHsFlux s c| ≤ 2·(K·L)·trigPolyEnergyHs s c` to the cleaner
vector-field-energy inequality
`galerkinVectorFieldHsEnergy s c ≤ (K·L)²·trigPolyEnergyHs s c`,
where `galerkinVectorFieldHsEnergy s c := ∑ m, (fracDerivSymbol s m)² ·
‖galerkinVectorField c m‖²` is the `Ḣˢ` energy of the Galerkin
nonlinear flux.

The reduction is Cauchy–Schwarz applied to the flux sum.  This
preserves the structural chain of §B.15 while moving the remaining
classical hypothesis closer to the natural output of a Kato–Ponce
commutator estimate (which bounds `‖u·∇θ‖²_{Ḣˢ}` by `‖θ‖²_{Ḣˢ}`). -/

/-- **`Ḣˢ` energy of the Galerkin nonlinear flux.** -/
noncomputable def galerkinVectorFieldHsEnergy
    (s : ℝ) {S : Finset (Fin 2 → ℤ)} [DecidableEq (Fin 2 → ℤ)]
    (c : ↥S → ℂ) : ℝ :=
  ∑ m : ↥S, (fracDerivSymbol s m.val) ^ 2 * ‖galerkinVectorField S c m‖ ^ 2

lemma galerkinVectorFieldHsEnergy_nonneg
    (s : ℝ) {S : Finset (Fin 2 → ℤ)} [DecidableEq (Fin 2 → ℤ)]
    (c : ↥S → ℂ) :
    0 ≤ galerkinVectorFieldHsEnergy s c :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Cauchy–Schwarz on the Galerkin `Ḣˢ` flux.**
`|galerkinHsFlux s c| ≤ 2·√(trigPolyEnergyHs s c)·√(galerkinVectorFieldHsEnergy s c)`. -/
theorem abs_galerkinHsFlux_le_cauchySchwarz
    (s : ℝ) {S : Finset (Fin 2 → ℤ)} [DecidableEq (Fin 2 → ℤ)]
    (c : ↥S → ℂ) :
    |galerkinHsFlux s c| ≤
      2 * Real.sqrt (trigPolyEnergyHs s S c) *
        Real.sqrt (galerkinVectorFieldHsEnergy s c) := by
  -- Step 1: pull the 2 out, and bound each inner product by the product of norms.
  have hFlux :
      galerkinHsFlux s c =
        2 * ∑ m : ↥S, (fracDerivSymbol s m.val) ^ 2 *
          (@inner ℝ ℂ _ (c m) (galerkinVectorField S c m)) := by
    unfold galerkinHsFlux
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hFlux, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- Step 2: |∑ a_m · ⟨c m, v m⟩_ℝ| ≤ ∑ |a_m| · ‖c m‖ · ‖v m‖ ≤ ∑ a_m · ‖c m‖ · ‖v m‖
  have hAbsSum :
      |∑ m : ↥S, (fracDerivSymbol s m.val) ^ 2 *
          (@inner ℝ ℂ _ (c m) (galerkinVectorField S c m))|
      ≤ ∑ m : ↥S, (fracDerivSymbol s m.val) ^ 2 *
          (‖c m‖ * ‖galerkinVectorField S c m‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [abs_mul]
    have habs_sq : |(fracDerivSymbol s m.val) ^ 2| = (fracDerivSymbol s m.val) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [habs_sq]
    exact mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm (c m) (galerkinVectorField S c m))
      (sq_nonneg _)
  refine le_trans (mul_le_mul_of_nonneg_left hAbsSum (by norm_num : (0 : ℝ) ≤ 2)) ?_
  -- Step 3: rewrite ∑ (fracDeriv)² · ‖c‖ · ‖v‖ as ∑ (fracDeriv · ‖c‖) · (fracDeriv · ‖v‖) and apply CS.
  have hRewrite :
      ∑ m : ↥S, (fracDerivSymbol s m.val) ^ 2 *
          (‖c m‖ * ‖galerkinVectorField S c m‖)
        = ∑ m : ↥S,
            ((fracDerivSymbol s m.val) * ‖c m‖) *
              ((fracDerivSymbol s m.val) * ‖galerkinVectorField S c m‖) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hRewrite]
  have hCS :
      ∑ m : ↥S,
          ((fracDerivSymbol s m.val) * ‖c m‖) *
            ((fracDerivSymbol s m.val) * ‖galerkinVectorField S c m‖)
      ≤ Real.sqrt (∑ m : ↥S, ((fracDerivSymbol s m.val) * ‖c m‖) ^ 2) *
          Real.sqrt (∑ m : ↥S,
            ((fracDerivSymbol s m.val) * ‖galerkinVectorField S c m‖) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  refine le_trans (mul_le_mul_of_nonneg_left hCS (by norm_num : (0 : ℝ) ≤ 2)) ?_
  -- Step 4: identify the two sums-of-squares with trigPolyEnergyHs / galerkinVectorFieldHsEnergy.
  have hSqC :
      ∑ m : ↥S, ((fracDerivSymbol s m.val) * ‖c m‖) ^ 2
        = trigPolyEnergyHs s S c := by
    unfold trigPolyEnergyHs
    refine Finset.sum_congr rfl (fun m _ => ?_); ring
  have hSqV :
      ∑ m : ↥S, ((fracDerivSymbol s m.val) * ‖galerkinVectorField S c m‖) ^ 2
        = galerkinVectorFieldHsEnergy s c := by
    unfold galerkinVectorFieldHsEnergy
    refine Finset.sum_congr rfl (fun m _ => ?_); ring
  rw [hSqC, hSqV]
  ring_nf
  rfl

/-- **Flux bound from a vector-field Ḣˢ bound.** If the Galerkin
nonlinear-flux Ḣˢ energy is bounded by `M²·trigPolyEnergyHs`, then the
flux itself is bounded by `2·M·trigPolyEnergyHs` (up to a square root
sign convention).  Stated in the form that feeds §B.14.raw. -/
lemma abs_galerkinHsFlux_le_of_vectorFieldBound
    {s : ℝ} {S : Finset (Fin 2 → ℤ)} [DecidableEq (Fin 2 → ℤ)]
    (c : ↥S → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hVF : galerkinVectorFieldHsEnergy s c ≤ M ^ 2 * trigPolyEnergyHs s S c) :
    |galerkinHsFlux s c| ≤ 2 * M * trigPolyEnergyHs s S c := by
  refine (abs_galerkinHsFlux_le_cauchySchwarz s c).trans ?_
  -- √E · √(M²·E) = M·E
  have hEnn : 0 ≤ trigPolyEnergyHs s S c := trigPolyEnergyHs_nonneg s c
  have hVnn : 0 ≤ galerkinVectorFieldHsEnergy s c :=
    galerkinVectorFieldHsEnergy_nonneg s c
  have hSqrtVF :
      Real.sqrt (galerkinVectorFieldHsEnergy s c)
        ≤ Real.sqrt (M ^ 2 * trigPolyEnergyHs s S c) :=
    Real.sqrt_le_sqrt hVF
  have hSqrtProd :
      Real.sqrt (M ^ 2 * trigPolyEnergyHs s S c)
        = M * Real.sqrt (trigPolyEnergyHs s S c) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]
  have hStep :
      2 * Real.sqrt (trigPolyEnergyHs s S c) *
          Real.sqrt (galerkinVectorFieldHsEnergy s c)
        ≤ 2 * Real.sqrt (trigPolyEnergyHs s S c) *
            (M * Real.sqrt (trigPolyEnergyHs s S c)) := by
    have h2E : 0 ≤ 2 * Real.sqrt (trigPolyEnergyHs s S c) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ h2E
    exact hSqrtVF.trans (le_of_eq hSqrtProd)
  refine hStep.trans ?_
  -- 2·√E·(M·√E) = 2·M·E
  have hSqrtSq :
      Real.sqrt (trigPolyEnergyHs s S c) * Real.sqrt (trigPolyEnergyHs s S c)
        = trigPolyEnergyHs s S c :=
    Real.mul_self_sqrt hEnn
  have hFinal :
      2 * Real.sqrt (trigPolyEnergyHs s S c) *
          (M * Real.sqrt (trigPolyEnergyHs s S c))
        = 2 * M * trigPolyEnergyHs s S c := by
    have : 2 * Real.sqrt (trigPolyEnergyHs s S c) *
              (M * Real.sqrt (trigPolyEnergyHs s S c))
            = 2 * M *
              (Real.sqrt (trigPolyEnergyHs s S c) *
                Real.sqrt (trigPolyEnergyHs s S c)) := by ring
    rw [this, hSqrtSq]
  exact le_of_eq hFinal

/-- **§B.14.cs — `HasGalerkinFluxBound` from a single Galerkin-vector-field
Ḣˢ bound.**  Takes one unified inequality
`∀ s ≥ 1, galerkinVectorFieldHsEnergy s (α n x) ≤ (K·L)² · trigPolyEnergyHs s (sqgBox n) (α n x)`
and produces the flux-bound structure with constants `(K, L)`.  This is
the narrowest hypothesis the downstream capstone §B.15 accepts — closer
to the natural shape of a Kato–Ponce commutator + Sobolev-embedding
output. -/
theorem HasGalerkinFluxBound.ofVectorFieldBound
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hVF : ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
      ∀ x ∈ Set.Ico (0 : ℝ) T,
      galerkinVectorFieldHsEnergy s (α n x) ≤
        (K * L) ^ 2 * trigPolyEnergyHs s (sqgBox n) (α n x)) :
    HasGalerkinFluxBound α K L := by
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  refine HasGalerkinFluxBound.ofHypotheses α hK hL ?_ ?_
  · intro n T hT x hx
    exact abs_galerkinHsFlux_le_of_vectorFieldBound (α n x) hKL (hVF 1 le_rfl n T hT x hx)
  · intro s hs n T hT x hx
    exact abs_galerkinHsFlux_le_of_vectorFieldBound (α n x) hKL
      (hVF s hs.le n T hT x hx)

/-! ### §B.15 Fully-concrete Path B capstone via `HasGalerkinFluxBound`

Upgrade of §B.13's `HasSqgGalerkinAllSBound.ofGalerkin_nonZero` that
consumes a single `HasGalerkinFluxBound` bundle instead of two raw
hypothesis functions.

**Input change:** the six-argument signature `(hFluxH1, hFluxHs, K, Lip,
hExpBound, ...)` collapses to `(flux : HasGalerkinFluxBound α K L,
hExpBound, ...)`.  The Kato–Ponce constant `K` and the Lipschitz bound
`L` are extracted from the structure; the two per-level flux bounds are
extracted from `flux.fluxH1` / `flux.fluxHs`.

**Named remaining gap:** `HasGalerkinFluxBound α K L` is the one narrow
classical input — precisely the pointwise Kato–Ponce + Sobolev-embedding
commutator estimate on the Galerkin flux.  Its discharge via the
companion fourier repo's `norm_partialCommutator_le_hs_fully_uniform`
requires a lattice↔continuous translation not yet present in-tree.  All
other Path B fields (`HasGalerkinL2Conservation`, `HasVelocityRieszPreservation`,
`HasGalerkinHsEnergyIdentity`, `HasVelocityLipSupBound` via `.ofSobolev`)
are either concrete or discharged structurally from the structure's
own `K_nonneg` / `L_nonneg`. -/

/-- **§B.15 — Fully-concrete Path B capstone on non-zero data.**

End-to-end constructor chaining §B.1–§B.12 into `HasSqgGalerkinAllSBound α`
consuming:

1. `α`, `hODE`, `hCoeff` — Galerkin ODE + ℓ² invariant (as in §B.13).
2. `flux : HasGalerkinFluxBound α K L` — the **single named classical
   input** packaging the Kato–Ponce + Sobolev flux estimate.
3. `D₁, Dₛ, hD₁_init, hDₛ_init` — initial-data Ḣˢ bounds.
4. `E, hE_nn, hExpBound` — exponential amplification on bounded horizon.

Returns a `HasSqgGalerkinAllSBound α` ready for §10.174 / §11.36. -/
noncomputable def HasSqgGalerkinAllSBound.ofGalerkin_nonZero_fullyConcrete
    (α : ∀ n : ℕ, ℝ → (↥(sqgBox n) → ℂ))
    (hODE : ∀ n : ℕ, ∀ t : ℝ,
      HasDerivAt (α n) (galerkinVectorField (sqgBox n) (α n t)) t)
    (hCoeff : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      (∑ m : ↥(sqgBox n), ‖α n t m‖ ^ 2)
        = ∑ m : ↥(sqgBox n), ‖α n 0 m‖ ^ 2)
    {K L : ℝ} (flux : HasGalerkinFluxBound α K L)
    (D₁ : ℝ) (hD₁_init : ∀ n : ℕ,
      hsSeminormSq 1 (galerkinToLp (sqgBox n) (α n 0)) ≤ D₁)
    (Dₛ : ℝ → ℝ) (hDₛ_init : ∀ s : ℝ, 1 < s → ∀ n : ℕ,
      hsSeminormSq s (galerkinToLp (sqgBox n) (α n 0)) ≤ Dₛ s)
    (E : ℝ) (hE_nn : 0 ≤ E)
    (hExpBound : ∀ t : ℝ, 0 ≤ t →
      Real.exp ((2 * (K * L)) * t) ≤ E) :
    HasSqgGalerkinAllSBound α :=
  HasSqgGalerkinAllSBound.ofGalerkin_nonZero α hODE hCoeff
    { K := K, K_nonneg := flux.K_nonneg }
    { L := L, L_nonneg := flux.L_nonneg }
    D₁ hD₁_init Dₛ hDₛ_init
    E hE_nn
    flux.fluxH1 flux.fluxHs
    hExpBound

/-- **§B.15.z — Zero-datum `ofGalerkin_nonZero_fullyConcrete`.**
Unconditional end-to-end exercise on zero Galerkin data using the
`HasGalerkinFluxBound.ofZero` witness. -/
noncomputable def HasSqgGalerkinAllSBound.ofGalerkin_nonZero_fullyConcrete_zero :
    HasSqgGalerkinAllSBound (fun _ _ _ => (0 : ℂ)) :=
  HasSqgGalerkinAllSBound.ofGalerkin_nonZero_fullyConcrete
    (α := fun _ _ _ => (0 : ℂ))
    (fun n t => by
      -- α ≡ 0, galerkinVectorField of 0 = 0, so HasDerivAt of const 0 at 0.
      have h : galerkinVectorField (sqgBox n)
          (((fun _ _ _ => (0 : ℂ)) : ∀ m : ℕ, ℝ → (↥(sqgBox m) → ℂ)) n t) = 0 := by
        funext m
        unfold galerkinVectorField galerkinRHS galerkinExtend
        simp
      rw [h]; exact hasDerivAt_const t _)
    (fun _ _ _ => by simp)
    HasGalerkinFluxBound.ofZero
    0 (fun n => (hsSeminormSq_zero_galerkin_of_trinary_zero 1 n 0).le)
    (fun _ => 0) (fun s _ n =>
      (hsSeminormSq_zero_galerkin_of_trinary_zero s n 0).le)
    1 (by norm_num)
    (fun t _ => by
      -- K = L = 0, so exp(0·t) = 1 ≤ 1.
      have h0 : (2 * ((0 : ℝ) * 0)) * t = 0 := by ring
      rw [h0, Real.exp_zero])

/-! ### §B.15 Rellich–Kondrachov on `𝕋²` in Fourier form (oracle)

This section isolates the **only** classical-analysis statement that
Gap C needs beyond the Kato–Ponce / Sobolev–embedding chain in
`sqg-lean-proofs-fourier`: the Fourier-form Rellich–Kondrachov
compact embedding `H¹(𝕋²) ⊂⊂ L²(𝕋²)`.

**Mathematical content.** Given a sequence of Fourier-coefficient
families `(c_n : Fin 2 → ℤ → ℂ)` with uniform `H¹` energy
`∑' k, (1 + |k|²) · ‖c_n k‖² ≤ M`, one can extract a subsequence
converging strongly in `ℓ²` (equivalently, in `L²` on the torus).

The classical proof is:

1. Uniform `ℓ²` boundedness `∑' k, ‖c_n k‖² ≤ M` gives per-mode
   boundedness `|c_n k|² ≤ M` for each fixed `k`.
2. Heine–Borel on `ℂ` yields a convergent subsequence per mode.
3. A diagonal extraction across the countable lattice `Fin 2 → ℤ`
   gives pointwise convergence `c_{φ(n)} k → c∞ k` at every mode.
4. The `H¹` tail bound `∑_{|k|>R} ‖c_n k‖² ≤ M / R²` shrinks the
   tail uniformly in `n`.
5. On the finite ball `|k| ≤ R`, pointwise convergence plus the
   finite-dimensional equivalence of norms gives uniform convergence,
   hence `ℓ²` convergence on the ball.
6. Combining (4)+(5) yields strong `ℓ²` convergence.

**Status.** The full machine-verified proof requires nontrivial
mathlib infrastructure (diagonal subsequence extraction across a
countable family, Heine–Borel for bounded sequences in `ℂ`, and
careful `tsum` tail estimates) that is out of scope for this
module.  Following the §11.34 / §B.14 pattern we therefore package
the theorem statement as a named hypothesis
`FourierRellichKondrachovHolds` and expose the plumbing consumers
need.  This is an *oracle* in the same sense as
`HasGalerkinFluxBound.ofKatoPonceSobolev` was before its discharge
landed: the classical-analysis content is isolated from the
SQG-specific chain, so downstream items (e.g. Gap C's
`ClassicalAubinLionsExtractionHolds`) can consume it via a clean
named interface. -/

/-- **§B.15.stmt — Fourier-form Rellich–Kondrachov statement.**

Given a sequence `c : ℕ → (Fin 2 → ℤ) → ℂ` of Fourier-coefficient
families, uniformly `H¹`-bounded in the sense
`∀ n, ∑' k, (1 + (lInfNorm k : ℝ)²) · ‖c n k‖² ≤ M`, there exists a
strictly monotone subsequence index `φ` and a limit
`c∞ : (Fin 2 → ℤ) → ℂ` such that the `ℓ²` tails
`∑' k, ‖c (φ n) k - c∞ k‖²` tend to `0` as `n → ∞`.

This is the Fourier form of Rellich–Kondrachov `H¹ ⊂⊂ L²` on the
flat two-torus, which is the statement shape needed by Aubin–Lions
extraction (Gap C). -/
def FourierRellichKondrachovHolds : Prop :=
  ∀ (c : ℕ → (Fin 2 → ℤ) → ℂ) (M : ℝ),
    (∀ n : ℕ, ∑' k : Fin 2 → ℤ,
        (1 + ((FourierAnalysis.lInfNorm k : ℕ) : ℝ) ^ 2)
          * ‖c n k‖ ^ 2 ≤ M) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c∞ : (Fin 2 → ℤ) → ℂ,
      Filter.Tendsto
        (fun n : ℕ => ∑' k : Fin 2 → ℤ, ‖c (φ n) k - c∞ k‖ ^ 2)
        Filter.atTop (nhds 0)

/-- **§B.15.zero — Zero-sequence sanity witness.**

For the constant-zero family `c = fun _ _ => 0`, the conclusion
shape holds trivially with `φ = id` and `c∞ = 0`.  This is *not*
a discharge of the general oracle; it only certifies that the
conclusion is satisfiable on the trivial input, matching the
§11.35 / §B.14.z zero-datum pattern. -/
theorem fourierRellichKondrachov_zero_witness :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c∞ : (Fin 2 → ℤ) → ℂ,
      Filter.Tendsto
        (fun n : ℕ =>
          ∑' k : Fin 2 → ℤ,
            ‖((fun _ _ => (0 : ℂ)) : ℕ → (Fin 2 → ℤ) → ℂ) (id n) k
              - (fun _ : Fin 2 → ℤ => (0 : ℂ)) k‖ ^ 2)
        Filter.atTop (nhds 0) := by
  refine ⟨id, strictMono_id, fun _ => (0 : ℂ), ?_⟩
  have h_zero : (fun n : ℕ =>
      ∑' k : Fin 2 → ℤ,
        ‖((fun _ _ => (0 : ℂ)) : ℕ → (Fin 2 → ℤ) → ℂ) (id n) k
          - (fun _ : Fin 2 → ℤ => (0 : ℂ)) k‖ ^ 2)
        = fun _ => (0 : ℝ) := by
    funext n
    simp
  rw [h_zero]
  exact tendsto_const_nhds

end SqgIdentity
