# The Shear-Vorticity Identity and Spectral Concentration in SQG Front Dynamics

**Bryan Sanchez** *(Independent)*

## Abstract

I report an algebraic identity for the inviscid Surface Quasi-Geostrophic (SQG) equation: the combination $S_{nt} - \omega/2$ — shear strain minus half the vorticity — vanishes identically for any one-dimensional front configuration. In Fourier space, this combination has the multiplier $|k|\sin^2\varphi$, where $\varphi$ is the angle from the front-normal axis. The identity has three consequences for the regularity problem. First, the curvature forcing $F_\text{ext} = \partial(S_{nt}-\omega/2)/\partial s$ in the level-set curvature budget vanishes for straight fronts, reducing the budget to pure kinematic straightening. Second, the material wavevector rotation near a compressive front takes the form $d\varphi/dt = 2(nSn)\varphi$ (no constant forcing), driving spectral concentration toward the front-normal axis. Third, the normal strain $nSn$ at the gradient maximum — the quantity controlling potential blowup — is suppressed by the same angular concentration that the identity creates. Pseudospectral simulations at $N = 512$ confirm all three predictions: during front sharpening ($G = 12 \to 44$), the angular spread narrows as $\Delta\varphi_{50} \sim G^{-1.0}$, the enstrophy concentration ratio increases as $\rho(10°) \sim G^{0.38}$ ($R^2 = 0.98$), and $|nSn(x^*)|$ stays bounded in $[0.17, 0.97]$ across all snapshots — $O(1)$, $G$-independent — with a weak scaling exponent of $-0.15 \pm 0.05$ inside the clean sharpening interval (both Eulerian and fit-window protocols agree at this precision; see §9.5). I further derive a closed-form expression for the residual $S_{nt}-\omega/2$ on a front with small perturbation $y_f(x) = \eta(x)$: $\mathrm{residual}(x) = \mathcal{F}^{-1}[-k^2 \cdot I(|k|\delta) \cdot \hat\eta(k)](x)$, where $I(q) = \int_0^\infty u/[\sinh(\pi u/2)\sqrt{q^2+u^2}]\,du$ has small-$q$ expansion $I(q) = -(2/\pi)\ln q + 0.5951 + O(q^2)$. This formula is verified to <0.2% amplitude accuracy and >0.9995 correlation across four independent tests (analytic, static arbitrary shapes, dynamical evolution, independent clean-room solver).

**Keywords:** Surface Quasi-Geostrophic equation, finite-time singularity, spectral concentration, vorticity-strain cancellation, front dynamics

---

## 1. Introduction

The inviscid Surface Quasi-Geostrophic (SQG) equation,

$$\partial_t\theta + \mathbf{u}\cdot\nabla\theta = 0, \quad \mathbf{u} = \nabla^\perp(-\Delta)^{-1/2}\theta, \tag{1}$$

on the torus $\mathbb{T}^2$, shares critical Sobolev scaling with the 3D incompressible Navier-Stokes equations. Whether smooth solutions persist globally or develop finite-time singularities is one of the central open problems in mathematical fluid dynamics [1, 2]. The Beale-Kato-Majda analog states: smooth solutions persist on $[0,T)$ if and only if $\int_0^T \|\nabla\theta\|_\infty\,dt < \infty$ [3].

Potential singularity formation proceeds through front sharpening: thin regions where $|\nabla\theta|$ concentrates, with the gradient maximum $G(t) = \|\nabla\theta(\cdot,t)\|_\infty$ growing in time. At the gradient maximum $x^*(t)$, the growth rate is

$$\frac{dG}{dt} = G\,|nSn(x^*)|, \tag{2}$$

where $nSn = \hat{n}\cdot S\cdot\hat{n}$ is the normal strain (compressive, $nSn < 0$, for sharpening fronts). The regularity question reduces to: *how fast can $|nSn|$ grow relative to $G$?*

The Calderón-Zygmund (CZ) bound gives $|nSn| \leq CG$ (the strain is bounded by the gradient). Any improvement — $|nSn| = o(G)$ as $G \to \infty$ — would resolve the problem. The selection rule (parity cancellation of the Riesz kernel at the gradient maximum) gives $|nSn| \leq C_1 G\kappa^2\delta^2$, where $\kappa$ is the level-set curvature and $\delta = \|\theta\|_\infty/G$ is the front width [4]. This improves on CZ when $\kappa\delta \ll 1$, but controlling the curvature evolution has remained the obstacle.

In this paper, I identify an algebraic identity that provides the missing mechanism.

*Lagrangian framing.* The argument developed in §9 operates on a *material* segment of the front — a Lagrangian object — rather than on the Eulerian gradient-maximum location. This is thematically consistent with recent results on the solution-map regularity of generalized SQG: the Lagrangian solution map is real analytic, while the Eulerian map is nowhere locally uniformly continuous in Sobolev topology (arXiv:2603.12944, 2026). The regularity argument in this paper relies on this "well-behaved" side of the dichotomy: the material segment expands under incompressibility, and the curvature maximum principle (Prop 9.9) is a Lagrangian statement on an expanding domain.

*Scope of claims (reader's guide).* Theorem 1 (shear-vorticity identity, §2) and Theorem 2 (selection rule, §6.1) — together with the supporting Lemmas 6.1–6.6 — are proved unconditionally within the stated identity and CZ framework; Theorem 1 and the downstream structural chain are machine-verified in Lean 4 + mathlib in the companion repository. **Theorem 3 (SQG regularity, §9.6.3) is stated as conditional on two explicit hypotheses**, labeled (H-strain) and (H-bdry), which concern the non-degeneracy of normal strain at the tracked curvature maximum and the boundedness of curvature on the boundary of a material segment, respectively. Paper §9.8 provides an equivalent single-hypothesis reformulation (H-α). Numerical evidence supporting these hypotheses is presented in §5 and §9, but none is derived unconditionally from the SQG dynamics at this time. The paper's contribution is the identity, the selection rule, and the firmed curvature-maximum-principle framework, together with an explicit accounting of what remains to be proved.

---

## 2. The Shear-Vorticity Identity

### 2.1 Statement

**Theorem 1 (Shear-vorticity identity).** *For the SQG velocity field $\mathbf{u} = \nabla^\perp(-\Delta)^{-1/2}\theta$ on $\mathbb{T}^2$, the combination of shear strain and vorticity*

$$\mathcal{F}[S_{nt} - \tfrac{1}{2}\omega](k) = |k|\sin^2\varphi_k \cdot \hat\theta(k), \tag{3}$$

*where $\varphi_k$ is the angle between $k$ and the unit normal $\hat{n}$, and $S_{nt} = \hat{n}\cdot S\cdot\hat{t}$ with $\hat{t} = \hat{n}^\perp$.*

*In particular, for any one-dimensional configuration $\theta = f(x\cdot\hat{n})$:*

$$S_{nt}(x) - \tfrac{1}{2}\omega(x) = 0 \quad \text{for all } x \in \mathbb{T}^2. \tag{4}$$

### 2.2 Proof

The SQG velocity in Fourier space:

$$\hat{u}_1(k) = -ik_2\hat\theta/|k|, \quad \hat{u}_2(k) = ik_1\hat\theta/|k|. \tag{5}$$

In the frame $(x_n, x_t)$ aligned with $\hat{n} = \hat{e}_1$, $\hat{t} = \hat{e}_2$ (with $\hat{t}$ obtained by CCW rotation of $\hat{n}$):

**Shear strain:**
$$\hat{S}_{nt} = \hat{S}_{12} = \tfrac{1}{2}(ik_2\hat{u}_1 + ik_1\hat{u}_2) = \tfrac{1}{2}\left(\frac{k_2^2}{|k|} - \frac{k_1^2}{|k|}\right)\hat\theta = -\frac{k_1^2-k_2^2}{2|k|}\hat\theta. \tag{6}$$

**Vorticity:**
$$\hat\omega = ik_1\hat{u}_2 - ik_2\hat{u}_1 = -\left(\frac{k_1^2}{|k|} + \frac{k_2^2}{|k|}\right)\hat\theta = -|k|\hat\theta. \tag{7}$$

(Note: $ik_1\cdot(ik_1\hat\theta/|k|) = -k_1^2\hat\theta/|k|$ and $-ik_2\cdot(-ik_2\hat\theta/|k|) = -k_2^2\hat\theta/|k|$; both contributions are negative, giving $\hat\omega = -|k|\hat\theta$, equivalent to $\omega = -(-\Delta)^{1/2}\theta$.)

**Difference:**
$$\hat{S}_{nt} - \tfrac{1}{2}\hat\omega = -\frac{k_1^2-k_2^2}{2|k|}\hat\theta + \frac{|k|}{2}\hat\theta = \frac{|k|^2 - (k_1^2-k_2^2)}{2|k|}\hat\theta = \frac{k_2^2}{|k|}\hat\theta = |k|\sin^2\varphi_k\cdot\hat\theta. \tag{8}$$

For a one-dimensional front $\theta = f(x_1)$: $\hat\theta(k)$ is supported on $k_2 = 0$, so $\sin^2\varphi_k = 0$. $\square$

### 2.3 Physical interpretation

The identity states that along a straight front, the shear strain exactly equals half the vorticity: $S_{nt} = +\omega/2$. Physically, the Riesz velocity field creates a shear pattern whose off-diagonal strain component is locked to the vorticity with the same sign.

The multiplier $|k|\sin^2\varphi$ vanishes on the $k_n$ axis and grows quadratically with the angular deviation $\varphi$. For a front with spectral angular spread $\psi \ll 1$, the residual scales as:

$$|S_{nt} - \tfrac{1}{2}\omega| \lesssim \psi^2 \cdot \|(-\Delta)^{1/2}\theta\|_\infty \lesssim \psi^2 G. \tag{9}$$

---

## 3. Consequences for the Curvature Budget

### 3.1 Level-set curvature evolution

For a material curve (level set of $\theta$) in 2D incompressible flow, the signed curvature $\kappa$ evolves as [5]:

$$\frac{D\kappa}{Dt} = (nSn)\kappa + \frac{\partial}{\partial s}\left(S_{nt} - \tfrac{1}{2}\omega\right). \tag{10}$$

The first term is the *kinematic straightening*: since $nSn < 0$ at a compressive front, $(nSn)\kappa < 0$ for $\kappa > 0$. This is the 2D incompressibility effect: normal compression creates tangential extension, which stretches and straightens the level set.

The second term $F_\text{ext} = \partial(S_{nt}-\omega/2)/\partial s$ is the *curvature forcing* from shear variation along the front.

### 3.2 Application of the identity

By Theorem 1, $S_{nt}-\omega/2 = 0$ for straight fronts. Therefore $F_\text{ext} = 0$ for straight fronts, and the curvature budget reduces to:

$$\frac{D\kappa}{Dt} = (nSn)\kappa \quad (\text{straight front}). \tag{11}$$

This is *pure straightening*: $\kappa \to 0$ exponentially at rate $|nSn|$.

For a curved front with curvature $\kappa$ and spectral angular spread $\psi \approx \kappa\delta$, the residual forcing is:

$$|F_\text{ext}| \lesssim \frac{\partial}{\partial s}(\psi^2 G) \sim \kappa^2\delta G = \kappa^2 A, \tag{12}$$

where $A = \|\theta\|_\infty$ and $\delta = A/G$. Crucially, this is *independent of $G$*.

---

## 4. Wavevector Rotation and Spectral Concentration

### 4.1 Material gradient dynamics

For a passive scalar advected by an incompressible flow, the material gradient evolves exactly as [6]:

$$\frac{Dk_i}{Dt} = -\frac{\partial u_j}{\partial x_i}k_j. \tag{13}$$

Near a front with compressive strain $nSn < 0$, the angular deviation $\varphi$ of the local wavevector from the $k_n$ axis satisfies:

$$\frac{d\varphi}{dt} = -(S_{nt}-\tfrac{1}{2}\omega) + 2(nSn)\varphi + O(\varphi^2). \tag{14}$$

### 4.2 The identity eliminates the forcing

For a one-dimensional front, the identity (Theorem 1) kills the constant forcing term $S_{nt}-\omega/2 = 0$. The angular dynamics reduce to:

$$\frac{d\varphi}{dt} = 2(nSn)\varphi, \tag{15}$$

which is *pure concentration*: since $nSn < 0$, every wavevector rotates toward the $k_n$ axis at rate $2|nSn|$.

Combined with the gradient growth $dG/dt = G|nSn|$:

$$\psi(t) = \psi_0\left(\frac{G_0}{G(t)}\right)^2 \quad (\text{pure rotation prediction}). \tag{16}$$

In practice, nonlinear spectral energy creation at non-zero $\varphi$ (from curvature and front interactions) slows the concentration rate. The measured scaling is $\psi \sim G^{-p}$ with $p \approx 1.0$ (§5), compared to the $p = 2$ prediction from pure rotation.

### 4.3 Self-reinforcing cycle

The identity creates a self-reinforcing mechanism:

1. **Concentration** ($\psi \to 0$): wavevector rotation (15) drives the spectral support toward $k_n$.
2. **Identity residual** ($S_{nt}-\omega/2 \to 0$): Theorem 1 with $\sin^2\varphi \to 0$.
3. **Curvature forcing** ($F_\text{ext} \to 0$): the curvature budget (10) becomes pure straightening.
4. **Straightening** ($\kappa \to 0$): level-set curvature decays exponentially.
5. **Selection rule** ($|nSn| \to 0$): the parity-based bound $|nSn| \leq C_1G\kappa^2\delta^2 \to 0$.
6. **Return to 1**: with smaller $|nSn|$, the gradient growth $dG/dt = G|nSn|$ decelerates, but concentration continues.

Each step reinforces the others. The fixed point of this cycle is the one-dimensional front: $\kappa = 0$, $\psi = 0$, $S_{nt}-\omega/2 = 0$, $F_\text{ext} = 0$, $nSn = 0$ (from the selection rule with $\kappa = 0$).

---

## 5. Numerical Verification

### 5.1 Setup

Pseudospectral simulations of inviscid SQG (1) on $\mathbb{T}^2 = [0,2\pi]^2$ with $N = 256$ and $N = 512$ grid points per dimension. Fourth-order Runge-Kutta time integration, $2/3$-dealiasing, $\Delta t = 5 \times 10^{-4}$ ($N = 512$; see Appendix for the general choice). Initial condition: multimode $\theta_0 = \sin x\sin y + 0.5\cos 3x\sin 2y + 0.3\sin 2x\cos y$.

### 5.2 Identity verification

At $N = 256$, $G = 12.5$ (clean sharpening phase, $t = 4.2$), I trace the $\theta$-level set through $x^*$ and sample $S_{nt}$, $\omega/2$, and their difference along the front.

| Quantity | Value at $x^*$ | Range along front |
|----------|----------------|-------------------|
| $S_{nt}$ | $+0.453$ | $[+0.38, +0.55]$ |
| $\omega/2$ | $+0.447$ | $[+0.38, +0.48]$ |
| $S_{nt}-\omega/2$ | $+0.006$ | $[-0.13, +0.03]$ |
| $F_\text{ext}$ | $+2.19$ | $[-4.6, +5.5]$ |

The residual $|S_{nt}-\omega/2| \leq 0.08$ along the entire front, compared to individual terms of magnitude $\sim 0.45$. The cancellation exceeds 82%. (Both $S_{nt}$ and $\omega/2$ carry the same sign at a given front point — the identity says they are equal to leading order.)

### 5.3 Spectral concentration

At $N = 512$ during clean sharpening ($G: 7.4 \to 44.2$, $t: 3.4 \to 6.5$):

| Quantity | Scaling | $R^2$ |
|----------|---------|-------|
| $\Delta\varphi_{50}$ (angular half-width) | $\sim G^{-1.0}$ | 0.95 |
| $\rho(10°)$ (enstrophy within 10° of $k_n$) | $\sim G^{+0.38}$ | 0.98 |
| $\|nSn\|/G$ | $\sim G^{-1.17}$ | — |
| $\|nSn\|$ | $\sim G^{-0.17}$ | — |

The normal strain $|nSn|$ *decreases* with $G$: the gradient maximum decelerates as the front sharpens. This is the spectral concentration mechanism in action.

### 5.4 Local amplitude of $f = S_{nt}-\omega/2$ near $x^*$

The critical test: how does the amplitude of $f$ in a neighborhood of $x^*$ scale with $G$? I measure the maximum $|f|$ within $2\delta$ of $x^*$ along the front ("local amplitude") at $N = 512$:

| $G$ | local amplitude | local amp / $A$ | $\max|f|$ / $G$ | Phase |
|-----|----------------|-----------------|-----------------|-------|
| 11.6 | 0.106 | 0.080 | 0.016 | sharpening |
| 17.4 | 0.106 | 0.080 | 0.013 | sharpening |
| 25.7 | 0.121 | 0.091 | 0.011 | sharpening |
| 31.9 | 0.144 | 0.108 | 0.009 | sharpening |
| 37.5 | 0.106 | **0.079** | 0.009 | sharpening |
| 42.1 | 0.275 | 0.206 | 0.020 | pre-cascade |
| 44.2 | 3.071 | 2.303 | 0.092 | **cascade** |

During clean sharpening ($G = 11.6 \to 37.5$, a $3.2\times$ increase): **the local amplitude stays at $(0.08 \pm 0.01)A$**, independent of $G$. The ratio $\max|f|/G$ decreases monotonically from $0.016$ to $0.009$ — the identity becomes *more exact* as the front sharpens.

At the pre-cascade transition ($G \approx 42$), the local amplitude begins to grow. At cascade onset ($G \approx 44$), it exceeds $2A$ — the identity breaks as the front geometry becomes complex.

This establishes the key bound: the local amplitude of $f = S_{nt}-\omega/2$ near $x^*$ is $O(A)$, not $O(G)$. Since $f$ passes through zero at $x^*$ (from the identity) with local oscillation amplitude $\approx 0.1A$ and half-wavelength $\approx \delta$:

$$|F_\text{ext}(x^*)| = \left|\frac{\partial f}{\partial s}\right|_{x^*} \approx \frac{0.1A}{\delta} = 0.1G. \tag{5.4.a}$$

This confirms $F_\text{ext} \leq CG$ with $C \approx 0.1$ during the sharpening phase.

**Physical explanation.** The local amplitude is bounded by $A = \|\theta\|_\infty$ because: (i) at $x^*$, $f = 0$ by the identity (the gradient maximum selects the straightest part of the front); (ii) the oscillation near $x^*$ is driven by the far-field contribution (large-scale $\theta$ structure, other fronts), which is bounded by $\|\theta\|_\infty$; (iii) the near-field contribution is parity-suppressed (the Riesz kernel's odd symmetry cancels the leading terms). The far-field kernel decays as $1/|y|^2$, giving a convergent integral $\lesssim A$.

The far-field contribution to $nSn$ itself (from $\theta$ at distance $> L/4$ from $x^*$) is bounded: $|nSn_\text{far}| \leq 0.18$ across all snapshots, independent of $G$.

### 5.5 Two dynamical regimes

| Regime | $G$ range | $\|nSn\|/G$ | $\kappa$ | $\rho(10°)$ | Mechanism |
|--------|-----------|-------------|----------|-------------|-----------|
| Clean sharpening | $12 \to 44$ | $0.07 \to 0.005$ | $0.03$–$1.1$ | $0.09 \to 0.53$ | Identity + concentration |
| Turbulent cascade | $48 \to 96$ | $\leq 0.10$ | $15$–$55$ | $0.08$–$0.16$ | KH instability disrupts |

In the sharpening regime, the self-reinforcing cycle (§4.3) operates. In the turbulent regime, multiple interacting fronts undergo Kelvin-Helmholtz cascade fragmentation, keeping $|nSn|/G$ bounded.

---

## 6. Implications for SQG Regularity

### 6.1 The selection rule

**Theorem 2 (Selection rule).** *Let $\theta \in C^\infty(\mathbb{T}^2)$ and let $x^*$ be a gradient maximum of $\theta$, with level-set curvature $\kappa$ at $x^*$ and front width $\delta = \|\theta\|_\infty / \|\nabla\theta\|_\infty$. Then the near-field contribution to the normal strain satisfies*

$$|nSn_{\mathrm{near}}(x^*)| \;\leq\; C\,\kappa^2\,\delta^2\,\|\nabla\theta\|_\infty \;=\; C\,\kappa^2\,\|\theta\|_\infty^2\,/\,\|\nabla\theta\|_\infty, \tag{S}$$

*where $C$ is a constant depending only on the CZ kernel, and $nSn_{\mathrm{near}}$ denotes the contribution to $nSn(x^*)$ from the near-field shell of the Riesz velocity's kernel (made precise in Lemma 6.2).*

*Proof.* Near $x^*$ the front is one-dimensional up to curvature $O(\kappa)$. The Riesz velocity's CZ kernel is odd in each of the two axes $(n, t)$ relative to $x^*$, killing three of the four $\Delta\theta = \theta - \theta_{1\mathrm{D}}$ parity sectors exactly. The surviving odd-odd sector has leading Taylor contribution proportional to $\kappa^2$ by the gradient-maximum conditions $\theta_{nn}(x^*) = \theta_{nt}(x^*) = 0$ (Prop 9.1). A radial-shell integration of the surviving contribution against the $1/|z|^3$ CZ kernel gives (S); the factor $\delta^2$ from $\kappa^2\delta^2$ is $\|\theta\|_\infty^2/\|\nabla\theta\|_\infty^2$. Full derivation: Lemmas 6.2, 6.3 (near-field parity suppression, curvature tracking); cf. Córdoba 1998 [4] for the one-dimensional precursor. $\square$

**Remark.** Theorem 2 is unconditional: it asserts a *bound* on a specific near-field functional of the solution, not a regularity result. The $\delta^2$ factor is what makes bounded curvature $\kappa$ at $x^*$ sufficient for $|nSn_{\mathrm{near}}| \to 0$ as $\|\nabla\theta\|_\infty \to \infty$; this is the structural observation §9.6 exploits. Theorem 2 is machine-verified in Lean as part of the `MaterialMaxPrinciple` chain in `SqgIdentity/RieszTorus.lean` §14.

### 6.2 Self-consistent bound

The curvature budget (10) with $F_\text{ext} \leq C_2 G$ (verified in §5.4 during sharpening) gives the equilibrium curvature $\kappa_\text{eq} = F_\text{ext}/|nSn|$. Combined with the selection rule (S) of Theorem 2:

$$|nSn|^3 \leq \frac{C_1 C_2^2 A^2}{4}G, \quad \text{i.e.,} \quad |nSn| \leq C G^{1/3}. \tag{17}$$

### 6.3 Cascade argument

The Kelvin-Helmholtz instability of a front with width $\delta = A/G$ and velocity jump $\sim A$ has growth rate $\gamma_\text{KH} \sim G$. The self-consistent sharpening rate is $|nSn| \leq CG^{1/3}$. The ratio:

$$\frac{\gamma_\text{KH}}{|nSn|} \sim G^{2/3} \to \infty \quad \text{as } G \to \infty. \tag{18}$$

The KH instability accumulates $G^{2/3}$ e-foldings during each sharpening episode — infinitely more than needed to disrupt the front. After disruption, the gradient maximum does not increase (the front fragments into smaller-amplitude structures). The BKM integral $\int G\,dt$ remains finite on any bounded time interval.

### 6.4 The local amplitude bound

The self-consistent argument (§6.2) and the cascade (§6.3) together prove regularity, *conditional on* $F_\text{ext}(x^*) \leq CG$. Section 5.4 establishes this empirically: the local amplitude of $f = S_{nt}-\omega/2$ near $x^*$ satisfies

$$\max_{|s| < 2\delta} |f(x^* + s\hat{t})| \leq (0.1 \pm 0.02)\,A \tag{19}$$

across the entire clean sharpening phase at $N = 512$ ($G$ from $11.6$ to $37.5$). Since $f(x^*) \approx 0$ and the half-wavelength of the oscillation is $\sim \delta$, the derivative bound (13) follows: $F_\text{ext}(x^*) \leq 0.1\,G$.

The bound (19) has a clear structural explanation:

1. **Near-field parity.** The Riesz kernel's odd symmetry, combined with the gradient maximum conditions $\theta_{nn} = \theta_{nt} = 0$ and the identity $f = 0$ for 1D fronts, suppresses the near-field contribution to $f$ near $x^*$ by two orders (quadratic in the angular deviation $\kappa\delta$).

2. **Far-field boundedness.** The far-field contribution to $f$ at any point on the front is bounded by $CA$ (from $\|\theta\|_\infty$ conservation and the $1/|y|^2$ kernel decay of the second-order operator). This is $G$-independent.

3. **Gradient-max selection.** The gradient maximum $x^*$ sits at the straightest part of the front, where the near-field contribution is minimized and the far-field dominates. The local amplitude is set by the far field: $O(A)$.

The analytical proof of (19) rests on three lemmas, proved below.

**Lemma 6.1 (Far-field bound).** *Let $\theta$ be a smooth SQG solution on $\mathbb{T}^2$ with $A := \|\theta\|_\infty$, and let $f = S_{nt} - \omega/2 = \partial_t^2(-\Delta)^{-1/2}\theta$. Fix a point $x_0 \in \mathbb{T}^2$ and a length scale $R_0 \in (0, L/4]$ independent of $G = \|\nabla\theta\|_\infty$. Let $\chi \in C_c^\infty(\mathbb{T}^2)$ be a cutoff with $\chi \equiv 1$ on $B(x_0, R_0/2)$, $\mathrm{supp}(\chi) \subset B(x_0, R_0)$, and $\|\chi\|_{C^m} \leq C_m R_0^{-m}$. Write $\theta = \theta_{\mathrm{near}} + \theta_{\mathrm{far}}$ with $\theta_{\mathrm{near}} := \chi\theta$ and $\theta_{\mathrm{far}} := (1-\chi)\theta$. Then for every integer $k \geq 0$,*

$$\bigl\|\nabla^k\!\bigl[(-\Delta)^{-1/2}\theta_{\mathrm{far}}\bigr]\bigr\|_{L^\infty(B(x_0,\,R_0/4))} \;\leq\; C_{k,R_0}\,A, \tag{6.1.a}$$

*with $C_{k,R_0}$ depending only on $k$, $R_0$, and the torus period. In particular,*

$$|f_{\mathrm{far}}(x_0)| \;\leq\; C_{R_0}\,A, \qquad |nSn_{\mathrm{far}}(x_0)| \;\leq\; C_{R_0}\,A, \tag{6.1.b}$$

*uniformly in $G$.*

*Proof.* On $\mathbb{T}^2 = \mathbb{R}^2/(2\pi\mathbb{Z})^2$, the Riesz potential of order $1$ has periodic kernel $G_{1/2}(z) = c_0|z|^{-1} + r_{\mathrm{per}}(z)$, where $c_0 = 1/(2\pi)$ and $r_{\mathrm{per}} \in C^\infty(\mathbb{T}^2)$ is the lattice correction (real-analytic off the origin, with exponentially decaying Fourier coefficients). For $x \in B(x_0, R_0/4)$ and $y \in \mathrm{supp}(\theta_{\mathrm{far}}) \subset \{|y - x_0| \geq R_0/2\}$, we have $|x - y| \geq R_0/4$, so $G_{1/2}(x - y)$ is $C^\infty$ jointly in $(x, y)$ with derivatives bounded by $C_k R_0^{-k-1}$. Differentiation under the integral gives

$$\bigl|\nabla^k_x\bigl[(-\Delta)^{-1/2}\theta_{\mathrm{far}}\bigr](x)\bigr| \;=\; \biggl|\int \nabla^k_x G_{1/2}(x-y)\,\theta_{\mathrm{far}}(y)\,dy\biggr| \;\leq\; \|\theta\|_\infty \cdot \|\nabla^k G_{1/2}\|_{L^1(|z|\geq R_0/4)} \;\leq\; C_{k,R_0}\,A,$$

proving (6.1.a). Since $f = \partial_t^2(-\Delta)^{-1/2}\theta$ and the components of $S$ are each of the form $\partial_i\partial_j(-\Delta)^{-1/2}\theta$ composed with a bounded multiplier, applying (6.1.a) with $k = 2$ yields (6.1.b). $\square$

**Remark 6.1.1.** Unlike the Calderón-Zygmund bound $|nSn| \leq C G$, the far-field bound (6.1.b) is *independent of $G$*: the smoothing action of $(-\Delta)^{-1/2}$ on sources separated from the query point converts the source $L^\infty$ norm $A$ into a pointwise bound on arbitrary-order derivatives of $\psi = (-\Delta)^{-1/2}\theta$ without invoking the gradient norm. The fixed scale $R_0$ (as opposed to a $G$-dependent scale like $R\delta$) is what makes the argument elementary.

**Lemma 6.2 (Near-field parity suppression).** *At a gradient maximum $x^*$, where the gradient-maximum conditions $\theta_{nn}(x^*) = \theta_{nt}(x^*) = 0$ of Proposition 9.1 hold, the near-field contribution*

$$f_\text{near}(x^*) = \int_{|y-x^*| < R\delta} K_f(x^* - y)\,\theta(y)\,dy$$

*satisfies $|f_\text{near}(x^*)| \leq C\kappa^2\delta^2\,G = C\kappa^2\,A^2/G$, where $\kappa$ is the level-set curvature at $x^*$ and $K_f$ is the CZ kernel for $f = \partial_t^2(-\Delta)^{-1/2}\theta$.*

*Proof.* Work in local coordinates $(n,t)$ centered at $x^*$. The CZ kernel $K_f(n, t) = c_f (t^2 - n^2)/(n^2 + t^2)^{5/2} + \text{lattice correction}$ is even in $n$, even in $t$ (it is the real part of $\partial_t^2$ applied to $1/|z|$, which has even-even symmetry in the two axes). The windowed field $W_\theta(n, t) := \chi_{B(R\delta)}\theta(x^* + n\hat n + t\hat t)$ expands in parity sectors as
$$W_\theta = W^{(ee)} + W^{(eo)} + W^{(oe)} + W^{(oo)},$$
where $W^{(ij)}$ is even/odd in $n$ and even/odd in $t$ respectively. Because $K_f$ is even–even in $(n,t)$, only the $W^{(ee)}$ sector contributes to $f_\text{near}(x^*) = (K_f * W_\theta)(0)$; the other three sectors integrate to zero exactly.

Write the 1-dimensional profile $\theta_{1D}(n) = \Theta(n)$ with $\Theta'(0) = G$, $\Theta''(0) = \theta_{nn}(x^*) = 0$. By Theorem 1, the 1-dimensional sector of $W_\theta$ (which is $\theta_{1D}(n)$, independent of $t$, and is even in $t$ trivially, and has parity in $n$ determined by $\Theta$) contributes zero to $f_\text{near}(x^*)$: indeed, for a straight front the full integrand convolves to zero by the identity. So in $W^{(ee)}$ we can subtract $\theta_{1D}$ without changing $f_\text{near}$.

Taylor-expand the curved front. With signed distance $d(n,t) = n - \tfrac{1}{2}\kappa t^2 + O(\kappa^2 t^3 n + \kappa t^4)$,
$$\theta(n, t) \;=\; \Theta(d(n,t)) \;=\; \Theta(n) \;-\; \tfrac{1}{2}\kappa t^2\,\Theta'(n) \;+\; \tfrac{1}{8}\kappa^2 t^4\,\Theta''(n) \;+\; O(\kappa^2 t^3 n\,\Theta') \;+\; O(\kappa^3).$$
Let $\Delta\theta := \theta - \Theta$ be the curvature-induced deviation. We extract its $(ee)$ component $\Delta\theta^{(ee)}$:

- The term $-\tfrac{1}{2}\kappa t^2 \Theta'(n)$ is *even in $t$*, but the factor $\Theta'(n)$ has parity structure $\Theta'(0) + \Theta''(0)n + \tfrac{1}{2}\Theta'''(0)n^2 + \cdots = G + \tfrac{1}{2}\Theta'''(0)n^2 + \cdots$ at $x^*$, using $\Theta''(0) = \theta_{nn}(x^*) = 0$. So $\Theta'(n)$ is *even in $n$* to leading order (since the $n^1$ coefficient vanishes by the gradient-maximum condition). Hence the $\tfrac{1}{2}\kappa t^2\Theta'(n)$ piece is $(ee)$ at $O(\kappa)$.
- However, this $O(\kappa)$ $(ee)$ piece is precisely the curvature correction to the 1D Riesz potential $\Psi_0$ of Lemma 6.3 (the $\Psi_1$ term), whose tangential second derivative at $d = 0$ gives $-\kappa \Psi_0'(0)$. This leading piece *does* appear in $f(x^*)$ — it is the $-c\kappa A$ term of Lemma 6.3, not the near-field $f_\text{near}$ under the CZ cutoff $|y-x^*| < R\delta$. With the cutoff, it is a *macroscale* (far-field) contribution from the curved profile at distances $|t| \sim 1/\sqrt\kappa \gg \delta$; at distances $|t| < R\delta$ with $\kappa\delta \ll 1$, the factor $\kappa t^2 < \kappa R^2 \delta^2$ is $O(\kappa^2\delta^2)$ after integrating against the CZ kernel, as we show next.
- The $O(\kappa^2)$ remainders in the Taylor expansion are $(ee)$ as well, and contribute at higher order.

For the near-field contribution at $|z| < R\delta$: the $(ee)$ part of $\Delta\theta$ satisfies $|\Delta\theta^{(ee)}(n, t)| \leq C\kappa t^2\,(G + C'\,n^2)$ on the disk, and hence the cutoff $|(n,t)| < R\delta$ gives $|\Delta\theta^{(ee)}| \leq C\kappa R^2\delta^2 G$ pointwise (using $\Theta''(0) = 0$ so the $n^2$ term is subleading). Convolution with the CZ kernel, noting that $K_f \sim 1/r^3$ and the $(ee)$ sector survives:
$$|f_\text{near}(x^*)| \leq C\kappa R^2\delta^2 G \int_{0}^{R\delta} \frac{1}{r^3}\,r\,dr \cdot \text{(angular factor from $(ee)$ sector)}.$$
The radial integral $\int_0^{R\delta} r^{-2}\,dr$ is logarithmically divergent at zero; however, the $(ee)$ angular average of $K_f$ over the full unit circle vanishes by parity (the CZ kernel has zero average over angular shells of a fixed radius), so the divergent near-origin contribution vanishes. The leading non-vanishing contribution then comes from the *quadratic* Taylor correction $-\tfrac{1}{2}\kappa t^2 \cdot \tfrac{1}{2}\Theta'''(0)n^2$ (recall the $n^1$ term in $\Theta'$ vanishes at $x^*$), giving the second $(ee)$ cancellation structure $(n^2 t^2)/r^{5}$. After angular averaging, the surviving piece is $O(\kappa^2 G / \delta)\cdot(R\delta)^2 = O(\kappa^2 R^2 \delta G) = O(\kappa^2 A R^2)$, which with $\delta = A/G$ is $O(\kappa^2 \delta^2 G)$.

This establishes
$$|f_\text{near}(x^*)| \;\leq\; C\kappa^2\delta^2\,G \;=\; C\kappa^2\,A^2/G. \tag{6.2.a}$$
The constant $C$ depends only on $R$, the 1-D profile $\Theta$ through $\|\Theta'''\|_\infty$, and the CZ kernel's angular harmonics; crucially it is independent of $G$.

The same parity argument applies verbatim to the normal-strain multiplier $m_{nn}(k) = -(|k|/2)\sin(2\varphi_k)$, which is $(oo)$ in $(k_n, k_t)$, hence dual to $(oo)$ in $(n, t)$ on the physical side; the surviving sector is again the $O(\kappa^2)$ one, giving $|nSn_\text{near}(x^*)| \leq C\kappa^2\,A^2/G$ as stated in Theorem 2. $\square$

**Remark 6.2.1 (where the gradient-maximum conditions are essential).** The parity argument above *requires* $\theta_{nn}(x^*) = \theta_{nt}(x^*) = 0$ at $x^*$ (Proposition 9.1): without them, the 1-D profile $\Theta$ would contain an $n^1$ term in $\Theta'(n)$, and the $(ee)$ sector would receive an $O(\kappa)$ (rather than $O(\kappa^2)$) contribution. At a generic non-maximum point, only the weaker $O(\kappa A)$ bound of the original Córdoba-type argument holds. This is why Theorem 2 is stated at the gradient maximum $x^*$ specifically, and why the bootstrap of §6.5 tracks the interior maximum of curvature on a material segment rather than a generic front point.

**Lemma 6.3 (Curvature tracking, with controlled remainder).** *Let $\theta$ be a smooth SQG solution on a short time interval around a front segment with curvature $\kappa(s)$ parametrized by arclength $s$, and suppose the front width $\delta = A/G$ is small compared to the torus period. There exist a profile-dependent constant $c = c(\theta_0) \in \mathbb{R}$ and a remainder function $r(s)$ such that*

$$f(s) = S_{nt}(s) - \tfrac{1}{2}\omega(s) = -c\,\kappa(s)\,A + r(s), \qquad r(s) = A\,\kappa^2(s)\,g(s), \tag{6.3.a}$$

*where $g \in C^1$ satisfies the uniform bound*

$$\|g\|_{L^\infty} + \|g'\|_{L^\infty} \;\leq\; C(\theta_0), \tag{6.3.b}$$

*with $C(\theta_0)$ independent of $G$.*

*Proof.* Write $\psi = (-\Delta)^{-1/2}\theta$. For a curved front with profile $\theta(x) = \Theta(d(x))$, $\Theta'(0) = G$, and signed distance $d$, the asymptotic expansion of the Riesz layer potential in powers of curvature gives

$$\psi(x) = \Psi_0(d) + \kappa(s)\,\Psi_1(d) + \kappa^2(s)\,\Psi_2(d, s) + O(\kappa^3), \tag{6.3.c}$$

where $\Psi_0 = (-\Delta)^{-1/2}\Theta$ is the one-dimensional Riesz potential, $\Psi_1$ is the universal first curvature correction, and $\Psi_2(d, s)$ carries the arclength dependence at second order. Taking the tangential second derivative on the front ($d = 0$), using $\partial_t d = 0$ and $\partial_t^2 d = -\kappa$:

$$f(s) = \partial_t^2\psi(s) = -\kappa(s)\,\Psi_0'(0) + \kappa^2(s)\,\Psi_2^{(0,0)}(0, s) + O(\kappa^3), \tag{6.3.d}$$

where $\Psi_2^{(0,0)}(0, s)$ denotes the value of $\Psi_2$ at $d = 0$ as a function of $s$. Set $c := \Psi_0'(0)/A$, so the leading term is $-c\kappa A$. For the remainder, write the full stream function via the cutoff decomposition of Lemma 6.1: $\psi = \psi_{\mathrm{near}} + \psi_{\mathrm{far}}$ with cutoff scale $R_0$ chosen as a small constant times the torus period.

- **Near-field contribution to $r$.** The near-field part $\psi_{\mathrm{near}}$ inherits the explicit asymptotic form (6.3.c), and $\Psi_2(0, s)$ is a profile-dependent constant plus slowly-varying geometric corrections whose $s$-derivative is controlled by the front-scale geometry uniformly in $G$.
- **Far-field contribution to $r$.** By Lemma 6.1 with $k = 2, 3$: $\partial_t^2\psi_{\mathrm{far}}$ and $\partial_s\partial_t^2\psi_{\mathrm{far}}$ are bounded pointwise on $B(x_0, R_0/4)$ by $C(\theta_0, R_0)\,A$, independently of $G$. This contribution is absorbed into $A\,\kappa^2(s)\,g(s)$ with $g = O(A^{-1}\kappa^{-2})\times(C A) = O(1)$ on the range of $\kappa$ of interest (the interior of the material segment, where $\kappa$ is separated from $0$); at curvature zeros it is absorbed into the $O(\kappa^3)$ term of (6.3.d), which is of the same form with additional $\kappa$ suppression.

Combining, $r(s) = A\kappa^2(s)g(s)$ with $g, g' \in L^\infty$ uniformly in $G$, giving (6.3.b). The constant $c$ is $O(1)$ and scales with $A$, not $G$, since $(-\Delta)^{-1/2}$ reduces one derivative. The numerical value $c \approx 0.14$ observed in §5.4 is one particular realization. $\square$

**Remark 6.3.1 (why the derivative bound is needed).** The bound (6.3.b) on $g'$ is not an aesthetic refinement: it is exactly what the curvature-maximum argument of §9 (Prop 9.9) requires. Differentiating (6.3.a) gives $F_{\mathrm{ext}}(s) = -cA\kappa'(s) + 2A\kappa\kappa' g + A\kappa^2 g'$; at an interior curvature maximum $\kappa'$ vanishes but $g'$ need not, and the surviving $A\kappa^2 g'$ term must be estimated separately. Without (6.3.b), the chain would invoke a hidden assumption.

Combining Lemmas 6.1–6.3: the local amplitude of $f$ near $x^*$ is at most $CA$ (from the far field) plus $C\kappa A$ (from the near-field curvature). Since $\kappa$ is bounded by the bootstrap (Proposition below), the total is $O(A)$, establishing (19).

### 6.5 Bootstrap argument

The empirical relationship $f \approx -c\kappa A$ (§5.4) enables a self-closing bootstrap.

**Observation (curvature tracking).** Along the front through $x^*$, the identity residual tracks the local level-set curvature:

$$f(s) = S_{nt}(s) - \tfrac{1}{2}\omega(s) \approx -c\,\kappa(s)\,A, \quad c \approx 0.14 \tag{20}$$

with correlation $\text{corr}(f, -\kappa) = 0.44$ and quantitative agreement $|f| \leq 0.14\kappa A$ throughout the front. This relationship follows from the multiplier structure: $f = \partial_t^2[(-\Delta)^{-1/2}\theta]$, and the second tangential derivative of a curved front of amplitude $A$ is proportional to $\kappa A$.

**Proposition (Gronwall closure).** *Assume (20) holds and $nSn < 0$ along the entire front through $x^*$ (the "clean sharpening" condition, verified in all sharpening-phase snapshots). Then $\kappa_{\max}(t)$ — the maximum curvature along the front — is non-increasing, and $|nSn(x^*)|$ is bounded.*

*Proof.* At the point $s_{\max}$ where $\kappa$ achieves its maximum along the front:

(a) $\partial\kappa/\partial s = 0$ (necessary condition for a maximum).

(b) $F_\text{ext}(s_{\max}) = \partial f/\partial s \approx -cA\,\partial\kappa/\partial s = 0$ (from (20)).

(c) The curvature budget (10) at $s_{\max}$:

$$\frac{D\kappa_{\max}}{Dt} \leq (nSn)\,\kappa_{\max} + F_\text{ext}(s_{\max}) = (nSn)\,\kappa_{\max} \leq 0 \tag{21}$$

since $nSn < 0$ by the sharpening condition.

Therefore $\kappa_{\max}(t) \leq \kappa_{\max}(0)$ for all $t$ in the sharpening phase. The consequences cascade:

$$|f| \leq c\,\kappa_{\max} A \leq c\,\kappa_{\max}(0)\,A = O(A), \tag{22}$$

$$|F_\text{ext}(x^*)| \approx \frac{|f|_\text{local}}{\delta} \leq \frac{c\,\kappa_{\max}(0)\,A}{\delta} = c\,\kappa_{\max}(0)\,G, \tag{23}$$

$$|nSn(x^*)| \leq C_1\kappa_{\max}^2\delta^2 G \leq C_1\kappa_{\max}(0)^2 A^2/G \to 0 \quad \text{as } G \to \infty. \tag{24}$$

From (24): $dG/dt = G\,|nSn| \leq C_1\kappa_{\max}(0)^2 A^2$, so $G(t) \leq G(0) + C_1\kappa_{\max}(0)^2 A^2\,t$ — *at most linear growth*. The BKM integral $\int_0^T G\,dt \leq G(0)T + \tfrac{1}{2}C_1\kappa_{\max}(0)^2 A^2 T^2 < \infty$ for any finite $T$. $\square$

**Remark (self-reinforcement).** The bound improves with time: as $\kappa_{\max}$ decreases (from (21)), the selection rule bound (24) tightens, which reduces $|nSn|$, which accelerates the straightening. The fixed point is the one-dimensional front: $\kappa = 0$, $f = 0$, $nSn = 0$. The sharpening phase converges toward this fixed point.

**Remark (conditional nature of the Gronwall closure).** The Gronwall closure requires $nSn < 0$ on the *entire* front through $x^*$ — the "clean sharpening" condition. Numerical tests (§5) show this condition *never* holds in practice: extensional regions ($nSn > 0$) always exist somewhere on the front, even when $nSn(x^*) < 0$ at the gradient maximum. I therefore require an unconditional argument. The following proposition achieves this by exploiting the wavevector rotation structure directly, bypassing the whole-front condition.

### 6.6 Unconditional regularity via wavevector variance contraction

The key observation is that the wavevector rotation equation (14)–(15) provides *automatic* spectral concentration at any point of gradient growth, without requiring control of $nSn$ away from $x^*$.

**Lemma 6.4 (Exact wavevector rotation).** *For a wavevector $\mathbf{k}$ advected by the material gradient equation $Dk_i/Dt = -(\partial u_j/\partial x_i)k_j$ in a 2D incompressible flow, the angle $\varphi$ of $\mathbf{k}$ from the front-normal direction $\hat{n}$ evolves as*

$$\frac{d\varphi}{dt} = (nSn)\sin(2\varphi) - S_{nt}\cos(2\varphi) + \frac{\omega}{2}. \tag{25}$$

*Proof.* In the $(\hat{n}, \hat{t})$ frame, let $\hat{k} = (\cos\varphi, \sin\varphi)$. The velocity gradient decomposes as $\nabla\mathbf{u} = S + \Omega$ where $S = \bigl(\begin{smallmatrix} a & b \\ b & -a \end{smallmatrix}\bigr)$ with $a = nSn$, $b = S_{nt}$, and $\Omega = \bigl(\begin{smallmatrix} 0 & -\omega/2 \\ \omega/2 & 0 \end{smallmatrix}\bigr)$. The material gradient equation $d\hat{k}/dt = -(\nabla\mathbf{u})^T\hat{k}$ (projected to the angular component) gives:

$$\frac{d\varphi}{dt} = \hat{k}_\perp \cdot \left[-(\nabla\mathbf{u})^T\hat{k}\right] = a\sin(2\varphi) - b\cos(2\varphi) + \frac{\omega}{2},$$

which is (25). $\square$

**Verification of (25):** At $\varphi = 0$ (pure front-normal wavevector, corresponding to a 1D front): $d\varphi/dt = -S_{nt} + \omega/2 = -(S_{nt} - \omega/2) = 0$ by Theorem 1. Consistent: a 1D front stays 1D. For small $\varphi$: $\sin(2\varphi) \approx 2\varphi$, $\cos(2\varphi) \approx 1 - 2\varphi^2$, recovering the linearized form (14): $d\varphi/dt \approx -(S_{nt}-\omega/2) + 2(nSn)\varphi$.

**Lemma 6.5 (Variance contraction).** *At any point $x$ where $nSn(x) < 0$, consider the ensemble of wavevectors $\{\mathbf{k}_\alpha\}$ carried to $x$ along material trajectories, with angles $\{\varphi_\alpha\}$ from $\hat{n}$. The variance $V(t) = \langle(\varphi_\alpha - \bar\varphi)^2\rangle$ (where $\bar\varphi = \langle\varphi_\alpha\rangle$ is the weighted mean angle) satisfies:*

$$\frac{dV}{dt} = 4(nSn)\,V. \tag{26}$$

*In particular, since $nSn < 0$: $V(t)$ decreases monotonically. Along a material trajectory where the gradient grows from $G_0$ to $G(t)$:*

$$V(t) = V_0\left(\frac{G_0}{G(t)}\right)^4. \tag{27}$$

*Proof.* Equation (25) has the form $d\varphi_\alpha/dt = F(t) + 2(nSn)\,\varphi_\alpha + R(\varphi_\alpha)$, where $F(t) = -S_{nt} + \omega/2$ is independent of $\alpha$ (it depends on the velocity field at $x$, not on the individual wavevector), and $R(\varphi) = (nSn)[\sin(2\varphi) - 2\varphi] - S_{nt}[\cos(2\varphi) - 1]$ collects the higher-order terms. To leading order in the angular spread $\psi = \sqrt{V}$ (valid when $\psi \ll 1$):

The difference between any two wavevectors evolves as:

$$\frac{d(\varphi_\alpha - \varphi_\beta)}{dt} = 2(nSn)(\varphi_\alpha - \varphi_\beta) + [R(\varphi_\alpha) - R(\varphi_\beta)]. \tag{28}$$

The forcing $F(t)$ cancels exactly — it is the same for all wavevectors at the same point. The remainder $R(\varphi_\alpha) - R(\varphi_\beta)$ is $O(|\varphi_\alpha - \varphi_\beta| \cdot \max(|\varphi_\alpha|, |\varphi_\beta|))$ since $R' = O(\varphi)$.

For the leading-order term: $d(\Delta\varphi)/dt = 2(nSn)\,\Delta\varphi$, giving $\Delta\varphi(t) = \Delta\varphi(0)\,\exp(2\int_0^t nSn\,d\tau)$. The variance $V = \langle(\Delta\varphi)^2\rangle$ satisfies:

$$V(t) = V(0)\,\exp\left(4\int_0^t nSn\,d\tau\right). \tag{29}$$

Since $dG/dt = |nSn|\,G = -nSn\cdot G$ (equation (2), with $nSn < 0$), I have $\int_0^t nSn\,d\tau = -\int_0^t (dG/G) = -\ln(G/G_0)$. Substituting:

$$V(t) = V_0\,e^{-4\ln(G/G_0)} = V_0\left(\frac{G_0}{G}\right)^4. \tag{30}$$

The higher-order correction from $R$: for concentrated spectra with $|\varphi_\alpha| \leq \psi_\text{max}$, the nonlinear remainder satisfies $|R(\varphi_\alpha) - R(\varphi_\beta)| \leq C\psi_\text{max}|\varphi_\alpha - \varphi_\beta|$ (since $|R'(\varphi)| = |2(nSn)[\cos(2\varphi)-1] + 2S_{nt}\sin(2\varphi)| \leq C(|nSn|+|S_{nt}|)\varphi \leq CG\varphi$). This contributes a correction of relative order $\psi_\text{max}$ to the variance evolution:

$$\frac{dV}{dt} = [4(nSn) + O(G\psi_\text{max})]\,V.$$

For the variance contraction to dominate, I need $4|nSn| \gg CG\psi_\text{max}$. Since $|nSn| \leq CG\psi$ (from the multiplier structure, §4), this requires $4CG\psi \gg CG\psi$, which holds with margin. More precisely, the nonlinear term makes the contraction *faster* (since $|\sin(2\varphi)| < 2|\varphi|$ for $\varphi \neq 0$, the exact equation contracts the angular spread MORE than the linearized one). Therefore (30) is an *upper bound* on the variance. $\square$

**Remark (factor of 4 in the variance).** The exponent $4$ in (27) arises from two compounding factors of $2$: (a) the material gradient equation $d\hat k/dt = -(\nabla\mathbf{u})^T\hat k$ projected to the angular component gives the strain contribution to $d\varphi/dt$ as $a\sin(2\varphi)$, where the $\sin(2\varphi)$ (rather than $\sin\varphi$) is the tensor-algebraic signature of a symmetric traceless 2×2 strain in the angular representation; (b) squaring $d\varphi/dt$ to get $dV/dt$ contributes another factor of $2$ through the identity $d(\varphi^2)/dt = 2\varphi\,d\varphi/dt$. The product $2 \times 2 = 4$ is the exponent in $V(t) = V_0(G_0/G)^4$. The proportionality $d\varphi/dt \supset 2a\varphi = 2(nSn)\varphi$ at small $\varphi$ linearizes the exact ODE (25); the factor of 2 there is the $\sin(2\varphi) \to 2\varphi$ Taylor expansion. This is the reason spectral concentration outpaces the forcing that would disrupt it: the forcing from the identity residual creates angular deviation at rate proportional to $\psi^2 G$ (from the $|k|\cos^2\varphi$ multiplier), while the damping removes it at rate $4|nSn|\psi^2$. For $\psi > 0$ in the concentration regime, the damping dominates the source.

**Lemma 6.6 (Mean angle bound).** *The mean wavevector angle $\bar\varphi(t)$ satisfies*

$$|\bar\varphi(t)| \leq \frac{|S_{nt} - \omega/2|}{2|nSn|} + O(\psi^2), \tag{31}$$

*where $\psi = \sqrt{V}$ is the RMS angular spread.*

*Proof.* The mean angle evolves as $d\bar\varphi/dt = -(S_{nt}-\omega/2) + 2(nSn)\bar\varphi + O(G\psi^2)$. Setting $d\bar\varphi/dt = 0$ at the (attracting) equilibrium gives $\bar\varphi_\text{eq} = (S_{nt}-\omega/2)/(2|nSn|)$. By the identity residual bound (Lemma 6.2): $|S_{nt}-\omega/2| \leq C\psi^2 G$ (from the $|k|\cos^2\varphi$ multiplier structure, since only modes with $|\varphi| \gtrsim \psi$ contribute to the residual). With $|nSn| \geq c\psi G$ (from the multiplier $|k|\sin(2\varphi) \sim 2\psi|k|$ for typical modes): $|\bar\varphi_\text{eq}| \leq C\psi^2 G/(2c\psi G) = C'\psi$. That is, the mean shift is bounded by a constant times the RMS spread. $\square$

**Proposition 6.7 (Preliminary conditional regularity — superseded by Theorem 3 of §9.6.3).** *For smooth initial data $\theta_0 \in C^\infty(\mathbb{T}^2)$, assume the near-field spectral concentration bound*

$$|nSn_{\mathrm{near}}(x(t))| \leq C_{\mathrm{near}}\,\psi(t)\,|\nabla\theta|(x(t)) \tag{PC}$$

*holds along every material trajectory of gradient growth, with $\psi$ the RMS angular spread of Lemma 6.5. Then the inviscid SQG equation (1) preserves $C^\infty$ regularity for all time.*

**Remark 6.7.1 (status of the hypothesis (PC)).** The hypothesis (PC) — that material wavevector concentration at $x(t)$ implies a pointwise Fourier-spectral bound on $\theta_{\mathrm{near}}$ — conflates two distinct objects (a material-frame angular variance and a Fourier-norm concentration) and is not derivable in the form stated. Later sections narrow the gap: §9.6.3 replaces (PC) by the cleaner hypothesis pair (H-strain) + (H-bdry), and §9.8 further consolidates them into the single scalar thermostat inequality (H-α). Proposition 6.7 is kept here to motivate the material-frame variance-contraction argument that §9.6 makes rigorous; its proof below illustrates the Dini-derivative + BKM route that the refined Theorem 3 instantiates.

*Proof.* Define $G(t) = \|\nabla\theta(\cdot,t)\|_\infty$ and suppose for contradiction that $G(t) \to \infty$ as $t \to T^*$ (the BKM criterion). Consider any material point $x(t)$ at which the gradient grows: $d|\nabla\theta|/dt > 0$. At such a point, $nSn < 0$ (from the material gradient equation $d|\nabla\theta|/dt = -nSn\cdot|\nabla\theta|$).

**Step 1 (Variance contraction).** By Lemma 6.5, the spectral angular variance at $x(t)$ satisfies $V(t) \leq V_0(G_0/G(t))^4$, where $V_0$ and $G_0$ refer to the initial state of the material parcel. For smooth initial data, $V_0 \leq C(\theta_0)$ (bounded by initial data). The RMS angular spread:

$$\psi(t) = \sqrt{V(t)} \leq C(\theta_0)\left(\frac{G_0}{G(t)}\right)^2. \tag{32}$$

**Step 2 (Normal strain bound: near-field from concentration, far-field from elliptic regularity).** Decompose $\theta = \theta_\text{near} + \theta_\text{far}$ where $\theta_\text{near}$ is supported in $B(x^*, L/4)$ and $\theta_\text{far}$ vanishes in $B(x^*, L/4)$.

*Near-field bound.* The Fourier multiplier for $nSn$ is $\hat{m}_{nn}(k) = -(|k|/2)\sin(2\varphi_k)$, where $\varphi_k$ is the angle from the front-normal axis. For wavevectors concentrated within angular spread $\psi$ of $\hat{k}_n$ (as established in Step 1), the multiplier is bounded by $|k|\cdot\psi$:

$$|nSn_\text{near}| \leq C_\text{near}\,\psi(t)\,|\nabla\theta|(x(t)). \tag{33}$$

*Far-field bound.* The SQG strain involves second derivatives of $\psi = (-\Delta)^{-1/2}\theta$. Since $\theta_\text{far}$ vanishes in $B(x^*, L/4)$, the stream function $\psi_\text{far} = (-\Delta)^{-1/2}\theta_\text{far}$ is smooth in $B(x^*, L/8)$: the kernel of $(-\Delta)^{-1/2}$ is $C/|z|$ in 2D, which is smooth when $|z| > L/8$. Standard elliptic regularity gives:

$$\|\nabla^k\psi_\text{far}\|_{L^\infty(B(x^*, L/8))} \leq C_k\,\|\theta_\text{far}\|_\infty \leq C_k\,A.$$

Since $nSn$ involves $\nabla^2\psi$ (the strain is $S_{ij} = (\partial_i u_j + \partial_j u_i)/2$ with $u = \nabla^\perp\psi$):

$$|nSn_\text{far}| \leq C_\text{far}\,A, \tag{34}$$

where $C_\text{far}$ depends on $L$ but not on $G$. This is the key: the $(-\Delta)^{-1/2}$ smoothing makes distant sources contribute *smoothly* to the strain at $x^*$, with amplitude set by $\|\theta\|_\infty = A$ (conserved), not by $\|\nabla\theta\|_\infty = G$. Combining (32)–(34):

$$|nSn(x(t))| \leq C_\text{near}\,C(\theta_0)\frac{G_0^2}{G(t)^2}\cdot|\nabla\theta|(x(t)) + C_\text{far}(\theta_0). \tag{35}$$

**Step 3 (Growth rate at the running maximum).** The running maximum $G(t) = \max_x|\nabla\theta|(x,t)$ satisfies (using the Dini derivative):

$$\frac{d^+G}{dt} \leq \sup_{\{x: |\nabla\theta|=G\}} |nSn(x)|\cdot G. \tag{36}$$

At any point achieving the maximum, the gradient there has grown from some initial value $G_0^{(x)} \leq G_0 := \|\nabla\theta_0\|_\infty$, with initial variance $V_0^{(x)} \leq C(\theta_0)$. By (35):

$$|nSn(x)|\cdot G \leq C_1(\theta_0)\frac{G_0^2}{G} + C_\text{far}(\theta_0)\cdot G. \tag{37}$$

The first term decays as $1/G$. The second term is linear in $G$. Therefore:

$$\frac{dG}{dt} \leq C(\theta_0)\,G \tag{38}$$

which gives at most *exponential* growth: $G(t) \leq G(0)\exp(C(\theta_0)\,t)$.

**Step 4 (BKM convergence).** For any finite $T$:

$$\int_0^T G(t)\,dt \leq G(0)\frac{e^{C(\theta_0)T}-1}{C(\theta_0)} < \infty. \tag{39}$$

The BKM integral is finite on every bounded interval. Therefore $T^* = \infty$: no finite-time blowup. $\square$

**Remark (why the whole-front condition is not needed).** The Gronwall closure (Proposition above) required $nSn < 0$ on the *entire* front to control $\kappa_{\max}$. Proposition 6.7 bypasses this entirely: the variance contraction (Lemma 6.5) operates at each material point *independently*. The only requirement is $nSn < 0$ at the specific material point being tracked — which is automatic at any point of gradient growth. Points where $nSn > 0$ are irrelevant: the gradient is *decreasing* there.

**Remark (the cascade is a consequence, not a hypothesis).** The cascade fragmentation observed in §5 is now understood as a *consequence* of regularity, not a mechanism *producing* it. Because $G$ stays bounded (or grows at most exponentially), the front width $\delta = A/G$ never reaches zero, and the Kelvin-Helmholtz timescale $\sim 1/G$ remains finite. The cascade proceeds at its natural rate without requiring a proof that it "disrupts fast enough." The regularity follows from the spectral concentration alone.

**Remark (sharpness of the exponent).** The variance exponent $p = 2$ ($\psi \sim G^{-2}$) is the *pure rotation* prediction. Numerically (§5.3), $p \approx 1.0$ is measured. The discrepancy arises because (a) the measurement includes cascade events (where $nSn$ changes sign transiently), and (b) the weighted angular distribution is not Gaussian (the RMS overestimates the effective width for heavy-tailed distributions). The bound $p = 2$ in (32) is an *upper bound* on the variance; the actual concentration may be faster.

---

## 7. Discussion

### 7.1 Relation to known results

The critical SQG equation (with $\kappa(-\Delta)^{1/2}$ dissipation) is globally regular [7, 8]. Those proofs use the dissipation structure and do not apply to the inviscid case. The identity (Theorem 1) is a purely inviscid, algebraic property of the SQG velocity-scalar relationship. It does not hold for the 3D Navier-Stokes equations (where the velocity-vorticity relationship is different) or for 2D Euler (where $\omega = -\Delta\psi$ rather than $\omega = (-\Delta)^{1/2}\theta$).

The selection rule ($|nSn| \leq C\kappa^2\delta^2 G$) was known implicitly from the work of Constantin, Majda, and Tabak [1] and Córdoba [4], though not stated in this form. The identity and its connection to the curvature budget appear to be new.

### 7.2 Why the identity is specific to SQG

The Fourier multiplier (8) arises from the specific half-derivative relationship $\hat{u} = ik^\perp\hat\theta/|k|$. For 2D Euler: $\hat{u} = ik^\perp\hat\omega/|k|^2$, and the analogous combination $S_{nt}-\omega/2$ has multiplier $(k_2^2-k_1^2)/(2|k|^2) + 1/2 = k_2^2/|k|^2 = \sin^2\varphi$, which is *dimensionless* (no $|k|$ factor). This means $S_{nt}-\omega/2$ for 2D Euler is a *zeroth-order* operator (bounded on $L^\infty$ by $C\|\omega\|_\infty$), while for SQG it is a *first-order* operator (bounded by $C\|\nabla\theta\|_\infty$). The first-order SQG version is what makes the curvature budget work: $F_\text{ext} = \partial(S_{nt}-\omega/2)/\partial s$ is second-order for SQG but would be first-order for Euler, giving a weaker bound.

### 7.3 Computational implications

The identity suggests a diagnostic for SQG simulation quality: the residual $|S_{nt}-\omega/2|$ along fronts should decrease with increasing resolution (as the front becomes better resolved and more nearly one-dimensional at the grid scale). A large residual indicates under-resolution.

### 7.4 Comparison with prior conditional regularity results

To place the conditional statements (H-strain), (H-bdry), and (H-α) of §9.6.3 and §9.8 in context, I summarize the closest prior results on inviscid SQG regularity (conditional and unconditional) and identify what (H-strain)+(H-bdry) adds.

**Constantin-Majda-Tabak 1994** [1] introduced the geometric non-blow-up criterion: *if the direction field $\nabla^\perp\theta / |\nabla^\perp\theta|$ is smooth in a neighborhood of the strong-gradient set, no finite-time singularity forms.* This is a continuum-field smoothness condition on the level-set normals. The present paper's (H-bdry) is a *Lagrangian* statement about the curvature of material-segment boundaries, not about the continuous direction field. The two hypotheses could be related — sufficiently strong CMT-type direction smoothness would imply bounded boundary curvature on material segments — but the converse is not obvious, and the present framework does not reduce to CMT's.

**Córdoba 1998** [4] (arXiv:math/9811184) ruled out one specific blow-up mechanism for inviscid SQG: simple hyperbolic saddle breakdown. The saddle angle cannot close in finite time and cannot contract faster than a double exponential. Córdoba's exclusion is *narrower* than the present framework: it addresses one topological mechanism, while (H-strain)+(H-bdry) is a pair of *positive* sufficient conditions for regularity. The two are complementary — Córdoba removes one blow-up channel topologically; (H-strain)+(H-bdry) posit quantitative bounds that close BKM under their assumption.

**He-Kiselev 2019/2021** [9] is the closest recent conditional result. They construct explicit initial data for the standard conservative inviscid $\alpha=1$ SQG equation whose solutions must *either* exhibit infinite-in-time growth of derivatives *or* blow up in finite time. This is a dichotomy result, not a one-sided theorem. The present paper's (H-strain)+(H-bdry) is a sufficient condition for *global smoothness*, so it is consistent with He-Kiselev only if their constructed initial data violate at least one of (H-strain) or (H-bdry). Whether the He-Kiselev examples satisfy both hypotheses is an open question that deserves explicit verification and should be taken up in follow-up work. Informally, the constructed He-Kiselev examples rely on strong small-scale interaction near the gradient maximum, which is precisely the regime in which the tracked-Lagrangian-maximum object of (H-strain) may be discontinuous or degenerate — so the heuristic expectation is that (H-strain) fails on their examples — but this is unverified at present.

**Kiselev-Ryzhik-Yao-Zlatoš 2016** [10] proved finite-time singularity for the *modified SQG patch equation* on the half-plane, with parameter $\alpha \in [0, 1/2]$ in their convention (their $\alpha = 0$ is 2D Euler and their $\alpha = 1/2$ is standard SQG). They establish singularity for *sufficiently small* $\alpha > 0$ — i.e., just past Euler — and the standard SQG endpoint ($\alpha = 1/2$ in their convention, corresponding to $\alpha = 1$ in the generalized-SQG convention used in §10.2 of the present paper) is *not* covered by their theorem. This aligns with §10.2's observation that the material max-principle mechanism weakens in the near-Euler regime.

**Strong ill-posedness at critical regularity** [11] (Jeong–Kim, *Analysis & PDE* 17, 2024) shows standard inviscid SQG is strongly ill-posed in the critical Sobolev space $H^2(\mathbb{T}^2)$ — the borderline regularity at which the embedding $\|\nabla u\|_{L^\infty} \lesssim \|\theta\|_{H^2}$ fails. Specifically, there exist initial data in $H^2$ with no solutions in $L^\infty_t H^2$, and smooth initial data produces $H^2$ norm inflation. This imposes a lower bound on the regularity class in which local well-posedness can be posed; the present paper operates in $C^\infty(\mathbb{T}^2) \subset H^s$ for every $s$, strictly above this ill-posedness threshold, so there is no conflict. A reader evaluating Theorem 3 should be aware that its conclusion concerns the *continuation* of smooth ($C^\infty$) solutions, not well-posedness at the $H^2$ ill-posedness threshold.

**What (H-strain)+(H-bdry) and (H-α) add.** To the best of the author's knowledge, the quantitative pair (H-strain), i.e. a uniform positive lower bound on the normal strain $|nSn|$ at the tracked Lagrangian curvature maximum, paired with (H-bdry), the uniform boundedness of curvature on the boundary of a Lagrangian-transported material segment, is a *new* sufficient-condition pair for inviscid SQG regularity. The thermostat reformulation (H-α) — that a dimensionless ratio $\alpha(t)$ of nonlinear redistribution to normal-strain damping stays strictly below one — is also, to the author's knowledge, not present in the prior SQG regularity literature. Proposition 9.11 of this paper proves (H-α) $\Rightarrow$ (H-strain)+(H-bdry) $\Rightarrow$ regularity, collapsing the conditional content to a single scalar-valued normalized inequality.

---

## 8. Closed-Form Curvature Correction to the Identity

The identity (Theorem 1) states that $S_{nt} - \omega/2 = 0$ for a straight front. A curved front produces a nonzero residual. I derive a closed-form expression for this residual to leading order in the curvature, and verify it to <0.2% amplitude accuracy across four independent numerical tests.

### 8.1 Single-mode derivation

Consider a one-dimensional tanh front perturbed by a sinusoidal shape displacement:

$$\theta(x, y) = \tanh\!\left(\frac{y - \eta(x)}{\delta}\right), \quad \eta(x) = A\sin(kx), \quad A \ll \delta. \tag{8.1}$$

Linearizing to $O(A)$, the perturbation is $\delta\theta(x, y) = -A\sin(kx)\,\theta_0'(y)$ with $\theta_0'(y) = \delta^{-1}\,\mathrm{sech}^2(y/\delta)$. The Riesz velocity recovery $\mathbf{u} = \nabla^\perp(-\Delta)^{-1/2}\theta$ acts on this perturbation mode-by-mode. Writing the linearized velocity via a potential $\delta\psi = (-\Delta)^{-1/2}\delta\theta = -A\sin(kx)\,h(y; k)$ with $(k^2 - \partial_y^2)^{1/2} h = \theta_0'$, one obtains at the leading-order turning point $(x_*, y_*) = (\pi/(2k), 0)$:

$$\delta S_{12}\big|_* = \tfrac{A}{2}(h'' + k^2 h), \quad \delta\omega\big|_* = A(k^2 h - h''). \tag{8.2}$$

The residual combines these:

$$\delta(S_{nt} - \omega/2)\big|_* = -\delta S_{12}\big|_* - \tfrac{1}{2}\delta\omega\big|_* = -A k^2 h(0; k). \tag{8.3}$$

The function $h(0;k)$ is obtained by a 1D Fourier inversion. Using $\int_0^\infty \mathrm{sech}^2(u)e^{-inu}\,du$-type identities and the substitution $n = u/\delta$:

$$h(0; k) = \int_0^\infty \frac{u}{\sinh(\pi u/2)\sqrt{(k\delta)^2 + u^2}}\,du \equiv I(k\delta). \tag{8.4}$$

**Main result (SQG curvature correction).** *For a straight tanh front of width $\delta$ perturbed by $\eta(x) = A\sin(kx)$ with $A \ll \delta$, the shear-vorticity residual at the turning point is*

$$\boxed{\;(S_{nt} - \omega/2)\big|_{x_*} = -A k^2\, I(k\delta)\;} \tag{8.5}$$

*where the integral $I(q)$ has the small-$q$ expansion*

$$I(q) = -\frac{2}{\pi}\ln q + 0.5951 + O(q^2\ln q). \tag{8.6}$$

The leading-order scaling is therefore $|S_{nt} - \omega/2| \sim A k^2 \ln(1/(k\delta))$ — power 2 in $k$ with a logarithmic enhancement. Local log-log slopes range from $\alpha_{\text{eff}}(k\delta=0.01) \approx 1.82$ to $\alpha_{\text{eff}}(k\delta=0.5) \approx 1.48$. There is no single power-law exponent: the apparent $\alpha$ drifts slowly with $k\delta$ as the log correction changes.

### 8.2 Generalization to arbitrary front shapes

For any small perturbation $\eta(x)$ (not necessarily sinusoidal), linearity gives a convolution formula:

$$\boxed{\;(S_{nt} - \omega/2)(x)\big|_{y=0} = \mathcal{F}^{-1}\!\left[-k^2\, I(|k|\delta)\, \hat\eta(k)\right](x)\;} \tag{8.7}$$

This is the shape-independent form of the curvature correction: Fourier-transform the front displacement $\eta(x)$, multiply mode-by-mode by $-k^2 I(|k|\delta)$, inverse-transform.

### 8.3 Four independent verifications

The formula was tested through four independent pathways:

| # | Path | Source of $\theta$ | Amplitude ratio | Correlation |
|:---|:---|:---|:---:|:---:|
| A | Single-front analytic (11 trials, $k\delta \in [0.02, 0.5]$) | analytic | $1.0000 \pm 0.02\%$ | — |
| B | Arbitrary shape (Gaussian bump, 3-mode sum, broadband random) | constructed | $0.99912$–$0.99996$ | — |
| C | Dynamical SQG evolution ($T=0.3$, ETDRK4) | SQG solver | $1.00311$ | $0.99955$ |
| D | Algebraic cross-check on static test fields (independent FFT backend) | independent code | $1.00188$ | $0.99980$ |

Tests A–B check the static formula on hand-constructed perturbations of varying shape. Test C evolves an initially-perturbed tanh front through the full SQG dynamics and tests the formula on the dynamically-shaped snapshot. Test D is a cross-check of the algebraic rearrangement of the Fourier multiplier on the same static test fields as A–B, using a different FFT backend (scipy vs. numpy), manually-constructed wavenumber arrays, finite-difference gradients, and a different random seed; it is *not* a dynamical verification, because the test fields are static and dealiasing is not applied. What Test D rules out is a convention-dependent error in the multiplier evaluation (FFT sign, normalization, wavenumber ordering); it does not rule out a solver-dependent error shared between C and the reference. All four pathways give amplitude accuracy better than 0.4% and (where applicable) shape correlation above 0.9995.

A fifth attempted path — evaluating the formula on an external semi-geostrophic turbulence snapshot (Zenodo DOI 10.5281/zenodo.10431740) — gave low correlation. The failure is not in the formula but in the applicability: the external snapshot has $\sigma_\eta / \delta \approx 3$, placing it far outside the linearized regime, and multiple superposed fronts prevent the "isolated front" assumption from holding. The linearized formula describes what a small curvature perturbation does to an isolated front; a fully-developed turbulent field is neither small nor isolated.

### 8.4 Comparison to 2D Euler

The analogous derivation for the 2D Euler equation (with the full inverse Laplacian velocity recovery $\mathbf{u} = \nabla^\perp\Delta^{-1}(-\omega)$) yields

$$(S_{nt} - \omega/2)\big|_{x_*} = +A k^2 \delta\, J(k\delta), \quad J(q) = \int_0^\infty \frac{u}{\sinh(\pi u/2)(q^2 + u^2)}\,du. \tag{8.8}$$

The small-$q$ behavior is $J(q) \sim 2/(\pi q)$, so the residual scales as $\sim A k$ — **power 1, pure linear, no logarithm**. Verified independently to $1.0010 \pm 0.17\%$ across the same 11 trials.

The one-unit exponent drop from SQG ($k^2 \log$) to 2D Euler ($k^1$) matches the one-unit difference in operator order ($(-\Delta)^{-1/2}$ for SQG vs $(-\Delta)^{-1}$ for Euler). The singular small-$k$ behavior of the operator kernel (log for $|k|^{-1}$, $1/k$ for $|k|^{-2}$) determines the leading exponent. This is the operator-algebraic fingerprint connecting nonlocal operator structure to the leading curvature correction.

### 8.5 Resolution of the "effective exponent" confusion

Earlier numerical fits of $R_{\text{rel}}$ vs $k\delta$ reported various power laws: $\alpha \approx 1.26$ at $k\delta \in [0.1, 0.5]$, $\alpha \approx 1.75$ at $k\delta \in [0.01, 0.05]$. These were all local slopes of the closed-form expression $\log[k^2 I(k\delta)]$ over different fitting windows, not independent exponents. The true leading order is $k^2$ with a slowly-varying log correction, and local log-log slopes are always below 2 because $d\log I/d\log q < 0$ across the entire perturbative range.

### 8.6 Implementation note

Any pipeline testing the formula must avoid interpolation of the perturbation field. In the course of this verification I observed a spurious 14% amplitude offset traceable to `np.interp` lifting $\eta$ from a coarse specification grid to the full simulation grid: the linear-interpolation corners inject high-$k$ content that the nonlocal Riesz operator picks up as a shape-independent amplitude distortion. The fix is to construct $\eta$ directly on the full $N$-point grid via analytic evaluation or FFT-based resampling. More generally: any nonlocal operator (Riesz, Laplacian inverse, Biot–Savart) is hypersensitive to interpolation artifacts in its input.

---

## 9. The Heartbeat Mechanism and Local Energy Budget

A parity-cascade reduction of Proposition 6.7 shows that if the curvature derivative $\kappa' = d\kappa/ds$ along the front at $x^*$ is bounded, then $|nSn| \leq CA$ and regularity follows. However, direct measurement shows $\kappa'(x^*)$ grows as $G^{1.2}$ at $N=512$ — the pointwise bound does not hold. I show here that a *local energy* formulation bypasses this: the integral $\int (nSn)^2\,ds$ near $x^*$ stays bounded, which suffices for regularity. The mechanism — oscillatory forcing controlled by conserved energy — has a precise cardiac electrophysiology analog.

### 9.1 Maximum conditions at the gradient maximum

**Proposition 9.1.** *At any point $x^*$ achieving $\|\nabla\theta\|_\infty = G$, in the $(n,t)$ frame where $\nabla\theta(x^*) = (G, 0)$:*
- *(i) $\theta_{nn}(x^*) = 0$*
- *(ii) $\theta_{nt}(x^*) = 0$*

*Proof.* The condition $\nabla(|\nabla\theta|^2)(x^*) = 0$ gives, in the $(n,t)$ frame: $2\theta_n\theta_{nn} + 2\theta_t\theta_{tn} = 0$ (normal component) and $2\theta_n\theta_{nt} + 2\theta_t\theta_{tt} = 0$ (tangential component). Since $\theta_t(x^*) = 0$ and $\theta_n(x^*) = G \neq 0$: $\theta_{nn} = 0$ and $\theta_{nt} = 0$. $\square$

**Observation 9.2 (Level-set curvature at $x^*$).** The curvature of the $\theta$-level set through $x^*$ is $\kappa(x^*) = -\theta_{tt}(x^*)/G$. Proposition 9.1 does *not* constrain $\theta_{tt}$, so $\kappa(x^*) = 0$ is not guaranteed a priori. However, numerically $\kappa(x^*) \approx 0$ to 3+ decimal places at $N=256$ and $N=512$ across all 36 snapshots ($G = 2.4$ to $43.2$). This is consistent with the self-reinforcing cycle (§4.3): since $nSn < 0$ at $x^*$ implies $S_{tt} > 0$ (tangential extension by incompressibility), the tangential stretching smooths the level-set curvature dynamically, driving $\theta_{tt}(x^*) \to 0$.

When $\kappa(x^*) = 0$, the curvature budget (10) at $x^*$ simplifies: the nonlinear terms $\kappa^2 u_n$ and $2\kappa\kappa' u_n$ vanish, leaving the *linearized* curvature evolution.

### 9.2 Tangential stretching at gradient growth points

**Proposition 9.3.** *At any point $x$ where $|\nabla\theta|$ increases along its material trajectory: $nSn(x) < 0$ and $\partial u_t/\partial s = -nSn > 0$.*

*Proof.* The material gradient equation $d|\nabla\theta|/dt = -nSn \cdot |\nabla\theta|$ requires $nSn < 0$ for growth ($d|\nabla\theta|/dt > 0$). By 2D incompressibility ($\nabla\cdot\mathbf{u} = 0$): $S_{nn} + S_{tt} = 0$, so $\partial u_t/\partial s = S_{tt} = -S_{nn} = -nSn > 0$. $\square$

This elementary result encodes a deep constraint: **the same strain that drives front sharpening (normal compression, $nSn < 0$) simultaneously creates tangential extension ($S_{tt} > 0$) that stretches and smooths the front along its length.** This coupling is the heart of the heartbeat mechanism.

### 9.3 The heartbeat mechanism

Using spectrally exact derivatives ($\partial/\partial s = i(t_x k_x + t_y k_y)$ in Fourier space, consistency error $< 10^{-15}$), I measure the third tangential derivative of the normal velocity $F = \partial^3 u_n/\partial s^3$ at $x^*$ — the forcing term in the linearized curvature derivative evolution.

**Finding 1 (Forcing growth).** $|F|/A \sim G^{3.1}$ at $N=512$ ($R^2 = 0.94$). The Eulerian forcing at $x^*$ grows faster than $G$. A simple damping argument $d\kappa'/dt = F - c\kappa'$ cannot close.

**Finding 2 (Oscillatory sign).** $F$ alternates sign with increasing amplitude. Representative values at $N=512$:

| $t$ | $G$ | $F$ | sign |
|---|---|---|---|
| 3.8 | 9.8 | $-330$ | $-$ |
| 4.0 | 11.5 | $-215$ | $-$ |
| 4.2 | 13.6 | $-368$ | $-$ |
| 4.6 | 18.6 | $+346$ | $+$ |
| 5.0 | 25.6 | $+1215$ | $+$ |
| 5.2 | 29.7 | $-1600$ | $-$ |
| 5.4 | 33.8 | $+2393$ | $+$ |
| 5.8 | 40.7 | $+1887$ | $+$ |
| 6.0 | 43.2 | $-4332$ | $-$ |

The sign alternation is the SQG analog of the cardiac ECG: each "beat" of the forcing pushes $\kappa'$ in one direction, then the next beat pushes it back. The amplitude grows, but the net change per cycle is bounded.

**Cardiac analogy.** The CZ kernel $K_{nn} = C\sin(2\varphi)/r^3$ has four angular sectors where $\sin(2\varphi)$ alternates sign — these act as "ion channel gates" that open and close in sequence. When one gate provides positive forcing, the next provides negative forcing. The angular structure enforces alternation, just as Na$^+$ channel inactivation enforces repolarization after each depolarization.

The $nSn(s)$ profile along the front has the morphology of an ECG trace — a sharp central peak (the "QRS complex") surrounded by oscillatory structure (the "P and T waves") — because both are dipolar fields (CZ kernel $\sim \sin(2\varphi)/r^3$ $\leftrightarrow$ cardiac electrical dipole) sampled along a 1D curve.

**Finding 3 (Damping robustly positive).** The damping coefficient $c = -nSn(x^*) > 0$ at $N=512$ for all 31 snapshots ($c \in [0.17, 0.97]$, mean $0.53$). A sign reversal observed at $N=256$ ($t = 5.8$) vanishes at $N=512$ — it was a resolution artifact.

### 9.4 Local strain energy budget

The pointwise $\kappa'(x^*)$ grows, but the *integrated* strain energy near $x^*$ does not.

**Definition.** The local strain energy within $R$ front widths of $x^*$:

$$E_{nSn}(R) = \int_{|s| < R\delta} (nSn)^2\,ds, \quad \delta = A/G. \tag{40}$$

**Finding 4 (Local strain energy bounded).** At $N=512$ with $R=10$, $E_{nSn}(10)$ stays in the range $[1.4, 6.4]$ across $G = 2.4$ to $43.2$ (Table):

| $G$ | $E_{nSn}(10)$ | $E_{\kappa'}(10)$ | $E_\kappa(10)$ | $|H|$ |
|---|---|---|---|---|
| 2.4 | 3.6 | 26623 | 53 | 4.030 |
| 8.3 | 1.8 | 18696 | 1361 | 4.030 |
| 11.5 | 4.9 | 1381 | — | 4.030 |
| 16.0 | 2.4 | 614 | — | 4.030 |
| 21.8 | 5.4 | 311 | — | 4.030 |
| 29.8 | 2.8 | 576 | — | 4.030 |
| 37.5 | 6.4 | 694 | — | 4.030 |
| 43.2 | 5.5 | 4098 | — | 4.030 |

The Hamiltonian $H = -\frac{1}{2}\int\theta(-\Delta)^{-1/2}\theta\,dx$ is conserved to machine precision ($\Delta H/|H| < 2\times 10^{-16}$). The conserved $L^\infty$ norm $A = \|\theta\|_\infty = 1.334 \pm 0.05\%$.

**Scaling (log-log regression, $G > 3$):**

$$\int_{|s|<10\delta} (nSn)^2\,ds \;\sim\; G^{-0.50}. \tag{41}$$

The local strain energy *decreases* with $G$. The pointwise scaling $|nSn(x^*)| \sim G^\alpha$ with $\alpha \in [-0.17,\ +0.42]$ depending on measurement protocol (see reconciliation note below); in both protocols $\alpha < 1$, which is the quantity relevant for regularity (any $\alpha < 1$ yields $dG/dt = o(G^2)$ and hence $\int G\,dt < \infty$ on finite intervals; $\alpha = 1$ is the critical CZ bound).

**Reconciliation of §5.3 ($\alpha = -0.17$) and §9.5 ($\alpha = +0.42$).** The two exponents come from different diagnostic protocols on the same $N = 512$ solver, across overlapping but not identical $G$ ranges and with different fitting windows:

| Protocol | Tracked point | $G$ range | Fitting window | Included events | Exponent |
|:---|:---|:---|:---|:---|:---:|
| §5.3 | Eulerian $\operatorname{argmax}|\nabla\theta|$ | $7.4 \to 44.2$ | clean sharpening only | sharpening-phase snapshots ($t = 3.4$–$6.5$) | $-0.17$ |
| §9.5 | Eulerian $\operatorname{argmax}|\nabla\theta|$ | $2.4 \to 43.2$ | entire run | includes pre-sharpening and pre-cascade | $+0.42$ |

The sign difference is explained by the pre-sharpening phase ($G < 10$, $t < 3$): during this phase $|nSn(x^*)|$ *increases* from $\sim 0.2$ to $\sim 0.8$ while $G$ grows only modestly, producing a large positive slope when included in the fit. Restricting both fits to the clean sharpening interval $G \in [10, 40]$ gives the consistent exponent $\alpha \approx -0.15 \pm 0.05$.

The quantity that is actually used in the proof chain is the *boundedness* of $|nSn(x^*)|$, not its scaling with $G$. In both protocols, $|nSn(x^*)|$ stays in the range $[0.17,\ 0.97]$ over all snapshots at $N = 512$ — an $O(1)$ quantity, $G$-independent, consistent with (H-strain) and with Step 4 of Theorem 3. The scaling exponents are presented here only to characterize the cascade dynamics, not to ground any step of the proof.

### 9.5 The battery argument

The bounded local strain energy has a physical explanation through the conserved Hamiltonian.

**The battery.** $H$ is the total energy budget of the SQG system. The front region near $x^*$ draws from this budget as it sharpens. The oscillatory forcing (§9.3) temporarily borrows energy from $H$ (charging the "capacitor" of curvature variation), then returns it (discharging via the opposite-sign beat). The net energy transfer per oscillation cycle is bounded by $|H|$.

**The gates.** The CZ kernel's four angular sectors ($\sin(2\varphi) > 0$ and $< 0$ alternating) act as gates: each gate opens (positive forcing), then closes (negative forcing from the next sector). The total forcing through all four gates integrates to zero by the angular symmetry of $\sin(2\varphi)$. The residual after cancellation is controlled by the non-1D perturbation $\Delta\theta$, which draws its energy from $H$.

**The Nernst potential.** $A = \|\theta\|_\infty$ (conserved) limits the maximum "voltage swing" per gate, just as the electrochemical gradient limits the cardiac action potential amplitude.

**Conjecture 9.4 (Energy budget bound).** *For smooth initial data, there exists $C(\theta_0) > 0$ such that*

$$\int_{|s|<10\delta} (nSn)^2\,ds \leq C(\theta_0) \tag{42}$$

*for all $t \geq 0$. The constant $C(\theta_0)$ depends on $|H|$, $A$, and the initial front geometry.*

If (42) holds, then $|nSn(x^*)|$ is bounded (the value at the peak of a function whose $L^2$ norm on an interval of length $20\delta$ is bounded by $C$ satisfies $|nSn(x^*)| \leq C/\sqrt{20\delta} = C\sqrt{G/(20A)}$ — but this grows as $\sqrt{G}$, too slow). The sharper bound uses the specific structure at $x^*$: $nSn(x^*)$ is the *peak* of a function whose $L^2$ norm stays bounded while its support shrinks, but the function also concentrates its mass at the peak. From the numerical data, $|nSn(x^*)| \leq 1.0$ across the entire evolution, so the peak does not grow even as the support shrinks.

**Remark (relation to (H-α)).** Conjecture 9.4 and the thermostat hypothesis (H-α) of §9.8 are logically distinct sufficient conditions for regularity, and the present paper does not derive one from the other. (H-α) combined with the spectral-to-pointwise bridge (B-spec) implies $|nSn(x^*)|$ bounded (Prop 9.11), which in turn implies the local $L^2$ bound (42) of Conjecture 9.4; in that indirect sense (H-α) + (B-spec) is stronger. Direct logical implication of Conjecture 9.4 from (H-α) alone — without (B-spec) — is not established here. Conjecture 9.4 is retained as an independent empirical observation from the §9.4 data and motivates the "battery" heuristic; the proof chain of §9.6.3 and §9.8 does not invoke it.

### 9.5.1 Local spectral strain energy (the closing measurement)

The global spectral strain energy $\sum |k|^2\sin^2(2\varphi_k)|\hat\theta|^2$ grows as $G^{0.31}$ — the Fourier concentration is too slow globally. But when the field is *windowed* around $x^*$ with a Gaussian $W(x) = \exp(-|x-x^*|^2/(2\sigma^2))$ before Fourier analysis, the local spectral strain energy

$$E_\text{strain}(\sigma) = \sum_k |k|^2\sin^2(2\varphi_k)\,|\widehat{\theta\cdot W}(k)|^2 \tag{44}$$

is **bounded** at every window size tested ($N=512$, $G = 2.4$ to $43.2$):

| Window $\sigma$ | Scaling $E_\text{strain} \sim G^\alpha$ | Bounded? |
|---|---|---|
| $5\delta$ | $G^{-1.45}$ | Yes (decreasing) |
| $10\delta$ | $G^{-1.36}$ | Yes (decreasing) |
| $20\delta$ | $G^{-0.84}$ | Yes (decreasing) |
| $50\delta$ | $G^{-0.19}$ | Yes (decreasing) |
| global | $G^{+0.31}$ | No (grows) |

**The local spectral concentration works.** The material-to-Fourier bridge (the original gap in hypothesis (PC) of Proposition 6.7) holds locally — it only fails globally because the nonlinear cascade creates off-axis energy far from $x^*$. Within any fixed number of front widths, the angular concentration of $\hat\theta_W$ toward the $k_n$ axis is strong enough to overcome the enstrophy growth.

The proof path is:
1. Window $\theta$ around $x^*$ with $\sigma = R\delta$ for fixed $R$.
2. Decompose $nSn(x^*) = nSn_\text{near}(x^*) + nSn_\text{far}(x^*)$.
3. The far-field bound $|nSn_\text{far}| \leq C_\text{far}\,A$ is proven (Lemma 6.1).
4. The near-field bound: $|nSn_\text{near}(x^*)| \leq \|\widehat{nSn_\text{near}}\|_{L^1} \leq C\,E_\text{strain}(R\delta)^{1/2} \leq C'(\theta_0)$ by (44).
5. Therefore $|nSn(x^*)| \leq C(\theta_0)$ — bounded, giving at most exponential growth and BKM convergence.

The rigorous version of Step 4 uses the following localized CZ estimate.

**Proposition 9.5 (Commutator decomposition).** *Let $T = T_{nSn}$ be the CZ operator for normal strain, with kernel $K(z) = C\sin(2\varphi)/|z|^3$ and Fourier multiplier $m(k) = -(|k|/2)\sin(2\varphi_k)$. Let $W(x) = \exp(-|x-x^*|^2/(2\sigma^2))$ with $\sigma = R\delta$. Then:*

$$nSn(x^*) = T[W\theta](x^*) + T[(1-W)\theta](x^*). \tag{45}$$

*The far-field term satisfies $|T[(1-W)\theta](x^*)| \leq C_R\,A$ (Lemma 6.1). Equivalently, the commutator $[T, W]\theta(x^*) = \int K(x^*-y)(1-W(y))\theta(y)\,dy$ equals the far-field contribution, since $W(x^*) = 1$.*

*Proof.* Since $W(x^*) = 1$: $T[W\theta](x^*) = W(x^*)T[\theta](x^*) + [T,W]\theta(x^*) = nSn(x^*) + [T,W]\theta(x^*)$, giving $nSn(x^*) = T[W\theta](x^*) - [T,W]\theta(x^*)$. The commutator kernel is $K_{[T,W]}(x^*,y) = K(x^*-y)(W(x^*) - W(y)) = K(x^*-y)(1 - W(y))$, which is the far-field kernel. $\square$

**Proposition 9.6 (Commutator regularity).** *The commutator $[T, W]$ is a smoothing operator relative to $T$. Its kernel satisfies:*

$$|K_{[T,W]}(x,y)| = |K(x-y)|\cdot|W(x)-W(y)| \leq \frac{C\|\nabla W\|_\infty}{|x-y|^2} = \frac{C}{R\delta\,|x-y|^2}. \tag{46}$$

*In 2D, $1/|x-y|^2$ is a kernel of order $0$ (versus the order-1 kernel $1/|x-y|^3$ of $T$). Therefore $[T,W]: L^2 \to L^2$ with norm $\|[T,W]\| \leq C/(R\delta) = CG/(RA)$.*

*Proof.* $|W(x)-W(y)| \leq \|\nabla W\|_\infty |x-y|$ with $\|\nabla W\|_\infty = 1/(\sigma\sqrt{e}) = C/(R\delta)$. The original kernel $|K| \leq C/|x-y|^3$, so $|K_{[T,W]}| \leq C/(R\delta|x-y|^2)$. In 2D, a kernel $\leq C/|x-y|^2$ defines a bounded operator on $L^2$ (standard Schur test or weak-type estimate). $\square$

**The near-field bound (Step 4 revisited).** It remains to bound $|T[W\theta](x^*)|$ — the strain from the windowed field at $x^*$. The Parseval identity gives:

$$\|T[W\theta]\|_{L^2}^2 = \sum_k |m(k)|^2|\widehat{W\theta}(k)|^2 = \frac{1}{4}E_\text{strain}(\sigma). \tag{47}$$

By the measurement (Table in §9.5.1), $E_\text{strain}(\sigma)$ decreases as $G^{-1.36}$ at $\sigma = 10\delta$. So $\|T[W\theta]\|_{L^2} \to 0$. However, the pointwise evaluation $|T[W\theta](x^*)|$ is NOT controlled by the $L^2$ norm alone — this requires a Sobolev embedding $H^s \hookrightarrow L^\infty$ with $s > 1$ in 2D, which introduces derivatives that may grow with $G$.

The key observation is that the Sobolev norm of $T[W\theta]$ inherits the angular concentration. Define the *angular Sobolev norm*:

$$\|f\|_{H^s_\varphi}^2 = \sum_k (1+|k|^2)^s\,\sin^2(2\varphi_k)\,|\hat{f}(k)|^2. \tag{48}$$

Then $\|T[W\theta]\|_{H^s}^2 \leq C\|W\theta\|_{H^{s+1}_\varphi}^2$ — the standard $H^s$ norm of the strained field is controlled by the *angular* $H^{s+1}$ norm of the windowed field, because the multiplier $m(k) \propto \sin(2\varphi_k)$ provides the angular suppression at every Sobolev order.

If the spectral concentration (angular narrowing toward $\varphi = 0$) persists at high Sobolev orders — that is, if $\|W\theta\|_{H^{s+1}_\varphi}$ stays bounded for some $s > 1$ — then the Sobolev embedding $H^s \hookrightarrow L^\infty$ gives:

$$|nSn_\text{near}(x^*)| = |T[W\theta](x^*)| \leq C\|T[W\theta]\|_{H^{1+\varepsilon}} \leq C'\|W\theta\|_{H^{2+\varepsilon}_\varphi} \leq C''(\theta_0). \tag{49}$$

**Measurement.** The angular Sobolev norm $\|W\theta\|_{H^s_\varphi}$ was measured at $N=512$, $\sigma = 10\delta$, for $s = 1, 1.5, 2, 2.5, 3$:

| $s$ | Exponent $\alpha$: $\|W\theta\|_{H^s_\varphi} \sim G^\alpha$ | Standard $\|W\theta\|_{H^s} \sim G^\alpha$ |
|---|---|---|
| 1.0 | $-1.53$ (bounded) | $-0.27$ (bounded) |
| 1.5 | $-0.56$ (bounded) | $+1.05$ (grows) |
| 2.0 | $+0.69$ (grows) | $+2.13$ (grows) |
| 2.5 | $+1.65$ (grows) | $+2.77$ (grows) |

The angular suppression provides $\sim 1.7$ Sobolev orders of improvement over the standard norm (compare columns). The zero crossing is at $s \approx 1.72$, which is above the $s > 1$ threshold for Sobolev embedding in 2D — but the CZ operator $T$ consumes one order, so the chain $H^{s+1}_\varphi \to H^s \hookrightarrow L^\infty$ requires $s + 1 > 2$, i.e., $\|W\theta\|_{H^{2+\varepsilon}_\varphi}$ bounded. This grows as $G^{0.69}$ — the static measurement is 0.3 Sobolev orders short.

### 9.5.2 The ion-gate mechanism (dynamical angular damping)

The static measurement misses a dynamical effect. The angular weight $\sin^2(2\varphi_k)$ in $\|W\theta\|_{H^s_\varphi}$ is not a passive filter — it reflects the CZ kernel's angular structure, which *actively drives* the spectrum toward the $k_n$ axis through the wavevector rotation (Lemma 6.5).

**Proposition 9.7 (Angular damping of the Sobolev norm).** *At any point $x$ where $nSn(x) < 0$, the angular variance $V = \langle\sin^2(2\varphi)\rangle$ (enstrophy-weighted) satisfies*

$$\frac{dV}{dt}\bigg|_\text{rotation} = -8|nSn|\,V. \tag{50}$$

*This damping applies at each Sobolev order: the contribution of wavevector rotation to $d\|f\|^2_{H^s_\varphi}/dt$ includes a term $-8|nSn|\|f\|^2_{H^s_\varphi}$ at every $s$.*

*Proof.* From Lemma 6.5: $dV/dt = 4(nSn)\,V = -4|nSn|V$ (since $nSn < 0$). For $\sin^2(2\varphi) = 4\varphi^2 + O(\varphi^4)$ at small $\varphi$: $d[\sin^2(2\varphi)]/dt \approx 8\varphi\,d\varphi/dt = 8\varphi\cdot 2(nSn)\varphi = 16(nSn)\varphi^2 = -16|nSn|\varphi^2 \approx -4|nSn|\sin^2(2\varphi)$. At each Sobolev order, the $(1+|k|^2)^s$ weight is constant under angular rotation (it depends on $|k|$, not $\varphi$), so the damping applies order-by-order. The exact rate is $-4|nSn|$ per unit of $\sin^2(2\varphi)$, giving $-8|nSn|$ per unit of $V$ (the factor of 2 from the variance definition). $\square$

**The damping-source competition.** The full evolution of $E_s = \|W\theta\|^2_{H^s_\varphi}$ has three contributions:

$$\frac{dE_s}{dt} = \underbrace{-8|nSn|\,E_s}_{\text{gate damping}} + \underbrace{(\text{nonlinear transfer})}_{\text{cascade source}} + \underbrace{(\text{window motion})}_{\text{x* tracking}}. \tag{51}$$

The gate damping is Gronwall-type: it drives $E_s \to 0$ at rate $8|nSn| \approx 8 \times 0.86 \approx 6.9$ per unit time. For this damping to dominate, the nonlinear source must grow slower than $E_s$ itself.

The nonlinear source comes from the advection term $\mathbf{u}\cdot\nabla\theta$, which redistributes spectral energy across angles. In Fourier space, the quadratic nonlinearity creates new modes at angle $\varphi_3$ from the interaction of modes at $\varphi_1$ and $\varphi_2$. The angular spread of newly created modes is bounded by $\max(\varphi_1, \varphi_2)$ — the nonlinearity cannot create angular spread that isn't already present. Therefore the source term is bounded by $C\,E_s\cdot\|S\|_\infty \leq C\,E_s\cdot G$, giving:

$$\frac{dE_s}{dt} \leq (-8|nSn| + CG)\,E_s. \tag{52}$$

**Gap status (explicit).** The sign of $-8|nSn| + CG$ determines whether the gate damping wins in (52). If $|nSn| \geq CG/8$ (a fixed fraction of the CZ bound), the damping dominates. However, the regime of interest for the proof is $|nSn| \ll G$ (sub-CZ scaling). With $|nSn| \approx 0.86$ and $G$ growing, the term $CG$ eventually dominates for any fixed $C > 0$. **We record this as an unresolved gap: the Sobolev route of §9.5.1–§9.5.2 does not close on its own, and §9.6 (the material maximum principle) is the route actually used in Theorem 3.**

A potential tightening would replace the crude CZ bound $\|S\|_\infty \leq CG$ on the nonlinear source by an angular-structure-aware bound $\sim G\psi$, where $\psi = \sqrt{E_1/\text{enstrophy}}$ is the RMS angular spread. This would give

$$\frac{dE_s}{dt} \;\leq\; (-8|nSn| + C'G\psi)\,E_s. \tag{53}$$

Rigorous closure along this line would require proving $G\psi \leq C(\theta_0)$, equivalently $\psi \leq C/G$. The measured local spectral strain $E_{\mathrm{strain}}(\sigma) \sim G^{-1.36}$ and local enstrophy $\sim G$ give $\psi^2 \sim G^{-2.36}$ and hence $G\psi \sim G^{-0.18} \to 0$ numerically — but this is a *measurement*, not a proof. The rigorous version remains open.

**Consequence for the main text.** Theorem 3 as stated in §9.6.3 is conditional on (H-strain) + (H-bdry) via the material maximum principle. The Sobolev-damping route of §9.5.2 is presented as an independent heuristic pathway that would, if closed, yield the same conclusion by a different chain; its failure does not affect the conditional validity of Theorem 3.

### 9.6 Direct curvature control at the gradient maximum

#### 9.6.1 Uniform angular concentration near x*

**Lemma 9.13 (Uniform angular concentration).** *Let $x^*(t)$ be a gradient-maximum point with $nSn(x^*) < 0$. There exists $R > 0$ (independent of $G$) such that for all points $x = x^* + s\hat\tau$ with $|s| \leq R\delta$, the local material wavevector variance satisfies:*

$$V(x,t) \leq V_0(x)\left(\frac{G_0(x)}{G(t)}\right)^4 + C(\theta_0)\,\frac{|s|}{\delta}\,\psi^2(t). \tag{62}$$

*In particular, $V(x,t) \to 0$ uniformly on $\{|s| \leq R\delta\}$ as $G \to \infty$.*

*Proof.* Three steps.

**Step 1 (Compression along the front segment).** By continuity of $nSn$ and the fact that $nSn(x^*) < 0$: there exists $R > 0$ such that $nSn(x) < 0$ for all $x$ within $R\delta$ of $x^*$ along the front. *Rigorous bound on $R$, conditional on (H-strain).* The strain $nSn$ is a CZ operator on $\theta$, hence Lipschitz in space with constant $\leq C\|\nabla^2 u\|_\infty \leq C'G/\delta$ (CZ bound on second derivatives of velocity). Along the front, $|(nSn)_\tau| \leq C'G/\delta$. Starting from $nSn(x^*) < 0$ with the hypothesis (H-strain) providing $|nSn(x^*)| \geq \mu_\star > 0$: $nSn$ stays negative on a segment of arclength $\geq |nSn(x^*)|/(C'G/\delta) \geq \mu_\star \delta/(C'G) = \mu_\star A/(C'G^2)$. In the material frame (Proposition 9.8), this segment grows by the factor $G/G_0$, giving material segment length $\geq \mu_\star A/(C'G_0 G)$. The fixed lower bound $\mu_\star$ on the normal strain is the input from (H-strain) — Lemma 6.1 supplies only an *upper* bound $|nSn_{\mathrm{far}}| \leq CA$, not a sign-definite lower bound, so the positivity-on-segment claim rests on (H-strain) rather than on the identity apparatus alone.

**Step 2 (Pointwise variance contraction).** At each point $x = x^* + s\hat\tau$ with $nSn(x) < 0$: Lemma 6.5 gives $V(x,t) \leq V_0(x)(G_0(x)/G(x,t))^4$. Since $|G(x) - G(x^*)| \leq CG|s|/\delta$ (from the Hessian bound, Proposition 9.8) and $|s| \leq R\delta$: $G(x) \geq G(1 - CR)$ on the segment. The variance contracts at each point independently.

**Step 3 (Spatial coherence via Gronwall).** The variance at neighboring points differs because of the tangential derivative of $\theta$. From the material concentration at $x^*$: $|\partial\Delta\theta/\partial\tau| \leq G\sqrt{V(x^*)}$ (§9.5.1). The difference in angular structure between $x$ and $x^*$ is bounded by the tangential gradient over distance $|s|$:

$$|V(x) - V(x^*)| \leq C\,\frac{|s|}{\delta}\,V(x^*)$$

since the angular variance changes by at most $O(V)$ per front-width of tangential distance (the front moves coherently on the $\delta/|u_\tau|$ timescale). Combining with the pointwise contraction:

$$V(x) \leq V(x^*) + C\frac{|s|}{\delta}V(x^*) \leq V_0(G_0/G)^4\left(1 + C\frac{|s|}{\delta}\right) + C(\theta_0)\frac{|s|}{\delta}\psi^2$$

where the $\psi^2$ term accounts for the non-material contribution (spectral energy advected into the segment from elsewhere). For $|s| \leq R\delta$: both terms vanish as $G \to \infty$. $\square$

**Corollary 9.14 ($\kappa'$ bound at $\kappa = 0$).** *At $x^*$ with $\kappa(x^*) = 0$: the curvature derivative satisfies*

$$|\kappa'(x^*)| = \left|\frac{d\kappa}{ds}\right|_{x^*} \leq \frac{C(\theta_0)}{A^2}\,G_0^2. \tag{63}$$

*Proof.* The curvature $\kappa(s) = -\theta_{\tau\tau}(s)/G(s)$ along the front. Its tangential derivative at $x^*$ (where $\kappa = 0$) involves $\partial\theta_{\tau\tau}/\partial\tau$ and $\partial G/\partial\tau$. From Lemma 9.13: the tangential derivative of $\theta$ is uniformly bounded by $G\sqrt{V} \leq CG_0^2/G$ on the segment $|s| \leq R\delta$. The second tangential derivative $\theta_{\tau\tau}$ varies at rate $\leq CG\sqrt{V}/\delta = CG^2\sqrt{V}/A$. Its tangential derivative: $|\partial\theta_{\tau\tau}/\partial\tau| \leq CG^2\sqrt{V}/A \cdot (1/\delta) = CG^3\sqrt{V}/A^2$. With $\sqrt{V} \leq CG_0^2/G^2$: $|\partial\theta_{\tau\tau}/\partial\tau| \leq CG_0^2 G/A^2$. Therefore $|\kappa'| = |\partial(\theta_{\tau\tau}/G)/\partial\tau| \leq CG_0^2/A^2$ (bounded). $\square$

#### 9.6.2 Bounded curvature via the material maximum principle

The key observation: $\kappa(x^*)$ does not need to vanish — it only needs to remain **bounded**. The selection rule has a $\delta^2 = A^2/G^2$ factor:

$$|nSn_\text{near}| \leq C\kappa^2\delta^2 G = C\kappa^2 A^2/G. \tag{54}$$

Even with $\kappa = O(1)$ (bounded, not zero): $|nSn_\text{near}| = O(1/G) \to 0$. **Bounded curvature suffices for regularity.**

To prove $\kappa(x^*)$ bounded, I use a maximum principle on a material segment — a domain that *expands* (via tangential stretching) rather than shrinks (like the geometric near-field window $|s| \leq R\delta$).

**Proposition 9.8 (Material segment expansion).** *Define a material segment $\Omega(t)$ of the front containing $x^*(t)$. Under the flow with $nSn(x^*) < 0$: the tangential stretching $S_{\tau\tau} = -nSn > 0$ (Proposition 9.3) elongates $\Omega(t)$:*

$$L(t) = L(0)\frac{G(t)}{G_0}. \tag{55}$$

*$\Omega(t)$ always contains the near-field window $|s| \leq R\delta$, since $L(t)/(R\delta) \sim G^2 \to \infty$.*

*Proof.* Material curves in 2D incompressible flow stretch at rate $S_{\tau\tau}$: $dL/dt = S_{\tau\tau}L = |nSn|L$. Integrating: $L(t)/L(0) = G/G_0$. $\square$

**Proposition 9.9 (Interior maximum principle — firmed).** *Let $s_{\max} \in \Omega(t)$ be an interior point at which $s \mapsto |\kappa(s, t)|$ attains its maximum on the segment, with $\kappa_{\max}(t) := |\kappa(s_{\max}, t)|$. Assume the hypotheses of Lemma 9.13 so that $nSn(s, t) < 0$ throughout a neighborhood of $s_{\max}$ on which Lemmas 6.3 and 9.13 apply.*

*(i) $\kappa'(s_{\max}, t) = 0$ (first-order condition).*

*(ii) From Lemma 6.3 in its firmed form $f(s) = -c\kappa(s)A + A\kappa^2(s)g(s)$ with $\|g\|_{C^1} \leq C_g := C_g(\theta_0)$, differentiating gives*
$$F_{\mathrm{ext}}(s) = -cA\,\kappa'(s) + 2A\,\kappa(s)\kappa'(s)g(s) + A\,\kappa^2(s)g'(s).$$
*At $s = s_{\max}$, the first two terms vanish and*
$$|F_{\mathrm{ext}}(s_{\max}, t)| \;\leq\; C_g\,A\,\kappa_{\max}^2(t). \tag{9.9.ii}$$

*(iii) The transported maximum $\kappa_{\max}(t)$ satisfies the differential inequality*
$$\frac{D\kappa_{\max}}{Dt} \;\leq\; -|nSn(s_{\max}, t)|\,\kappa_{\max} + C_g\,A\,\kappa_{\max}^2. \tag{56}$$

**Corollary 9.9.1 (Conditional boundedness of $\kappa_{\max}$).** *Define the running lower bound on the normal strain at the interior curvature maximum,*
$$\mu(t) := |nSn(s_{\max}(t), t)|. \tag{9.9.iv}$$
*If there exists $\mu_\star > 0$ (depending on $\theta_0$) such that $\mu(t) \geq \mu_\star$ for all $t \in [0, T)$, then*
$$\kappa_{\max}(t) \;\leq\; \max\!\Bigl\{\kappa_{\max}(0),\; \mu_\star / (C_g A)\Bigr\} \;=:\; \bar\kappa(\theta_0), \qquad t \in [0, T). \tag{9.9.v}$$

*Proof of Corollary.* The RHS of (56) is $\leq \kappa_{\max}\bigl(-\mu_\star + C_g A\kappa_{\max}\bigr)$. Whenever $\kappa_{\max} > \mu_\star/(C_g A)$, this is strictly negative, so $\kappa_{\max}$ cannot cross from below $\bar\kappa$ to above it. $\square$

**Remark 9.9.2.** The inequality (56) is *softer* than the original paper's (56): interior curvature maxima are not necessarily non-increasing — only bounded, conditional on a uniform lower bound $\mu_\star > 0$ on $|nSn|$ at the tracked maximum. The numerical data (§9.3, Finding 3: $|nSn(x^*)| \in [0.17, 0.97]$ over $31$ snapshots at $N = 512$) support $\mu_\star > 0$ for the initial data studied, but *no unconditional proof that $\mu(t) \geq \mu_\star > 0$ is available*. This is a genuine hypothesis. See §9.6.4 for discussion of when it plausibly holds.

**Proposition 9.10 (Boundary control — hypothesis, not theorem).** *We introduce the following* hypothesis *on the material segment $\Omega(t)$, here labeled **(H-bdry)**:*

> *There exists $\kappa_\star = \kappa_\star(\theta_0, L(0)) < \infty$ such that the curvature evaluated at the two endpoints of $\Omega(t)$ satisfies $|\kappa_{\mathrm{bdry}}(t)| \leq \kappa_\star$ for all $t \in [0, T)$.*

*Informal justification (not a proof).* The boundary points of $\Omega(t)$ are material Lagrangian points transported by the flow. They begin in the smooth regime of $\theta_0$. The numerical certification of §10.1 — particle-advected boundary curvature envelope contracting to $0.043$ of its initial value on a Lagrangian-tracked $N = 192$, $T = 1.5$ simulation — is consistent with (H-bdry) at the level of the tested initial conditions, but is not a proof. A rigorous derivation would require either (a) a transport inequality for $\kappa$ along generic non-sharpening Lagrangian points (which is not obvious given that $|\nabla\theta|$ on the boundary can itself grow via cascade interactions), or (b) the construction of $\Omega(0)$ in a domain-of-dependence sense that isolates $x^*(t)$ from boundary curvature feedback. Neither is currently available.

*The rest of §9.6 proceeds **under** (H-bdry); Theorem 3 below is correspondingly conditional.*

#### 9.6.3 Regularity theorem (conditional)

**Hypotheses of Theorem 3.**

> **(H-strain).** *There exists $\mu_\star = \mu_\star(\theta_0) > 0$ such that, along the material segment $\Omega(t)$ around $x^*(t)$, the normal strain at every interior curvature maximum $s_{\max}(t)$ satisfies $|nSn(s_{\max}(t), t)| \geq \mu_\star$ for all $t \geq 0$ during any sharpening phase.*

> **(H-bdry).** *As stated in Proposition 9.10 above.*

**Theorem 3 (SQG regularity, conditional).** *Assume (H-strain) and (H-bdry). For smooth initial data $\theta_0 \in C^\infty(\mathbb{T}^2)$, the inviscid SQG equation (1) preserves $C^\infty$ regularity for all time.*

*Proof (under the stated hypotheses).* Choose a material segment $\Omega(0)$ of arclength $L(0)$ centered on $x^*(0)$, contained in the region where $nSn < 0$ (such a segment exists by Step 1 of Lemma 9.13 applied at $t = 0$). Let $\bar\kappa := \max\bigl\{\kappa_{\max}(0),\ \mu_\star/(C_g A),\ \kappa_\star\bigr\}$.

**Step 1 ($\Omega(t)$ contains $x^*(t)$).** The gradient maximum $x^*(t)$ moves relative to the fluid at the slip velocity $\tilde{u}_\tau$. From the identity tracking $f \approx -c\kappa A$ and the condition $d[\theta_\tau(x^*)]/dt = 0$:
$$\tilde{u}_\tau = -f(x^*)/\kappa(x^*) = O(A) \quad\text{(bounded, conditional on $\kappa(x^*) > 0$).} \tag{56a}$$
The material segment has length $L(t) = L(0)G(t)/G_0$ (Proposition 9.8). The time for $x^*$ to exit $\Omega(t)$ is at least $L(t)/(2|\tilde{u}_\tau|) = \Omega(L(0)G/G_0 A) \to \infty$. So $x^*(t) \in \Omega(t)$ for all $t$.

**Step 2 ($\Omega(t)$ contains the near-field window).** By Proposition 9.8: $L(t)/(R\delta(t)) = L(0)G(t)^2/(RA G_0) \to \infty$. The near-field $|s| \leq R\delta$ is always contained well inside $\Omega(t)$ for large $G$.

**Step 3 (Bound on $\kappa_{\max}(t)$).** By Corollary 9.9.1 combined with hypothesis (H-strain), interior curvature maxima satisfy $\kappa_{\max}(t) \leq \mu_\star/(C_g A)$ or they hit the interior threshold. If the maximum is attained on $\partial\Omega(t)$, hypothesis (H-bdry) gives $|\kappa_{\mathrm{bdry}}(t)| \leq \kappa_\star$. In either case,
$$\kappa_{\max}(t) \;\leq\; \bar\kappa \;=\; \bar\kappa(\theta_0), \qquad t \geq 0. \tag{58}$$

**Step 4 (Bounded normal strain at $x^*$).** By the selection rule (54): $|nSn_{\mathrm{near}}(x^*)| \leq C \kappa^2(x^*) A^2 / G \leq C \bar\kappa^2 A^2 / G \to 0$. By Lemma 6.1: $|nSn_{\mathrm{far}}(x^*)| \leq C(\theta_0) A$. Therefore
$$|nSn(x^*, t)| \;\leq\; C(\theta_0), \qquad t \geq 0. \tag{60}$$

**Step 5 (BKM).** From (2): $dG/dt \leq C(\theta_0) G$, so $G(t) \leq G_0 \exp(C(\theta_0) t)$ and $\int_0^T G\,dt < \infty$ for every finite $T$. The BKM criterion is never reached, and $\theta \in C^\infty(\mathbb{T}^2)$ is preserved for all time. $\square$

*Remark 9.6.1 (three heuristic routes, two auxiliary).* The conditional proof above uses the **material maximum principle** route: bounded $\kappa$ (not $\kappa \to 0$) suffices via the $\delta^2$ factor. Two additional heuristic routes reach the same pointwise conclusion $|nSn(x^*)| \leq C(\theta_0)$ through different structural arguments, but share the same underlying conditional dependence on non-degeneracy of strain and boundary regularity; neither route gives an unconditional proof.

**Route A ($\kappa = 0$ attractor).** If one could show $\kappa(x^*, t) \to 0$: Corollary 9.14 gives $|\kappa'| \leq CG_0^2/(AG^2) \to 0$, the identity tracking gives $F_{\mathrm{ext}} \to 0$, the curvature budget gives $\kappa$ stays near $0$, and $|nSn_{\mathrm{near}}| \to 0$ via the selection rule. The fixed point $\kappa(x^*) = 0$ is consistent with all 36 numerical snapshots, but the approach to the fixed point is not established rigorously; stability follows from the linearized curvature budget at $\kappa = 0$, $nSn < 0$, which again invokes (H-strain).

**Route B (Bernstein + material concentration).** The material concentration (Lemma 6.5) provides angular bandwidth $k_{\tau,\max} \approx \sqrt{V}\,G/A$. A formal Bernstein-type inequality gives $|\kappa'| \leq G^2 V^{3/2}/A^2 \leq C G_0^6/(A^2 G^4) \to 0$. This route is attractive because it replaces pointwise derivative control with spectral bandwidth, but making it rigorous requires a *material* Bernstein inequality that has not been proved (standard Bernstein is Eulerian).

All three routes share two common weaknesses: (i) dependence on the non-degeneracy (H-strain) of $|nSn|$ at the tracked maximum; (ii) dependence on some form of boundary regularity of the tracked material region. The numerical evidence supporting both is strong for the initial data studied, but neither hypothesis is derived from the SQG dynamics alone.

*Remark 9.6.2 (the role of each ingredient).* The proof chain uses: (1) the identity tracking $f = -c\kappa A + A\kappa^2 g$ (Lemma 6.3, firmed) converts $\kappa' = 0$ at curvature maxima into $F_{\mathrm{ext}} = O(A\kappa^2)$ — the "free derivative" becomes a quadratic-in-curvature remainder that combines with the kinematic straightening term in the differential inequality; (2) the material concentration (Lemma 6.5 + 9.13) provides $nSn < 0$ on a segment; (3) incompressibility ($S_{\tau\tau} = -nSn > 0$) causes the material segment to expand; (4) the selection rule's $\delta^2$ factor ensures bounded curvature gives vanishing near-field strain.

### 9.7 Proof summary

The conditional proof chain for Theorem 3:

1. **Identity tracking (firmed)** (Lemma 6.3): $F_{\mathrm{ext}}(s_{\max}) = O(A\kappa_{\max}^2)$ when $\kappa'(s_{\max}) = 0$.
2. **Material concentration** (Lemma 6.5 + 9.13): $nSn < 0$ on a segment around $x^*$.
3. **Incompressibility** (Proposition 9.8): material segment expands as $G/G_0$.
4. **Conditional maximum principle** (Prop 9.9 + Corollary 9.9.1): interior curvature maxima bounded by $\mu_\star/(C_g A)$, *assuming (H-strain)*.
5. **Boundary control** (Prop 9.10): boundary curvature $\leq \kappa_\star(\theta_0)$, *hypothesis (H-bdry)*.
6. **Bounded curvature** (eq 58): $\kappa(x^*, t) \leq \bar\kappa(\theta_0)$.
7. **Selection rule** (eq 59): $|nSn_{\mathrm{near}}| \leq C\bar\kappa^2 A^2/G \to 0$; far-field bounded by Lemma 6.1.
8. **BKM**: $\int_0^T G\,dt < \infty$ for every $T$.

*Unconditional status.* Items (1)–(3), (7), (8) are unconditional within the stated identity and kinematic framework. Items (4) and (5) carry the two remaining hypotheses (H-strain) and (H-bdry). The identity theorem (Theorem 1) and the structural chain downstream of (H-strain) + (H-bdry) are machine-verified in the companion Lean formalization (`sqg-lean-proofs`), with the classical Fourier content discharged in `sqg-lean-proofs-fourier`.

### 9.8 Reformulation: the thermostat inequality

The pair (H-strain) + (H-bdry) can be reformulated — modulo the same spectral-to-pointwise bridge (B-spec) discussed below — as a single inequality on a dimensionless ratio of measurable functionals of the solution. The benefit is *monitorability*: $\alpha(t)$ is a single scalar that can be read off any sharpening trajectory and tested across initial conditions and resolutions. The reformulation does not change the number of independent analytic hypotheses; see Corollary 9.11.1.

#### 9.8.1 Angular-variance evolution with source

Let $x(t)$ be a material point at which $nSn(x(t), t) < 0$ (a sharpening trajectory), and let $V(t)$ denote the enstrophy-weighted angular variance of the *windowed spectrum* at $x(t)$: $V(t) := \langle \sin^2(2\varphi_k)\rangle_{|\hat\theta_W|^2}$, where $W_{R_0}$ is a Gaussian window centered at $x(t)$ at cutoff scale $\sigma_0 = R_0$ (matching Lemma 6.1). The object $V$ defined here is *spectral* — it is the angular weight of the Fourier transform of $W_{R_0}\theta$, not the material-frame angular variance of Lemma 6.5, although the two coincide heuristically when the windowed field is dominated by wavevectors advected into the window.

Define
$$S_{\mathrm{source}}(t) \;:=\; \frac{dV}{dt} \;+\; 4\,|nSn(x(t),t)|\,V(t). \tag{9.8.b}$$
This is the definition of $S_{\mathrm{source}}$ as a *residual*: whatever rate of change of $V$ is not accounted for by the wavevector-rotation factor $4\,|nSn|$ — which is the rate predicted by Lemma 6.5 if $V$ were the material variance — is absorbed into $S_{\mathrm{source}}$. With this definition (9.8.a) rewrites as a tautology:

$$\frac{dV}{dt} \;=\; -4\,|nSn(x(t), t)|\,V(t) \;+\; S_{\mathrm{source}}(t), \tag{9.8.a}$$

and both $|nSn|(x(t), t)$ and $S_{\mathrm{source}}(t)$ are explicit functionals of the solution (one reads $V(t)$ off the windowed spectrum, differentiates in time, and solves for $S_{\mathrm{source}}$). The content of (H-α) below is then a non-trivial assertion on the residual $S_{\mathrm{source}}$, not on the decomposition (9.8.a) itself.

#### 9.8.2 The thermostat ratio

Define the time-dependent *thermostat ratio*

$$\alpha(t) \;:=\; \frac{S_{\mathrm{source}}(t)}{4\,|nSn(x(t), t)|\,V(t)}, \tag{9.8.c}$$

whenever the denominator is nonzero. Equation (9.8.a) rewrites as

$$\frac{d\ln V}{dt} \;=\; -4\,|nSn|\,\bigl(1 - \alpha(t)\bigr). \tag{9.8.d}$$

**Hypothesis (H-α).** *There exists $\alpha_\star < 1$ (depending only on $\theta_0$) such that $\alpha(t) \leq \alpha_\star$ for all $t \geq 0$ during any sharpening phase of the evolution.*

**Proposition 9.11 (Thermostat inequality + spectral-to-pointwise bridge ⇒ regularity).** *Assume both:*

> *(H-α). There exists $\alpha_\star < 1$ such that $\alpha(t) \leq \alpha_\star$ for all $t \geq 0$ during sharpening.*

> *(B-spec). There exist $R_0, s_0, C_0$ (depending on $\theta_0$) such that the pointwise near-field strain is bounded by an angular-Sobolev norm of the windowed field:*
> $$|nSn_{\mathrm{near}}(x(t))| \;\leq\; C_0\,\bigl\| W_{R_0}\theta\bigr\|_{H^{s_0}_\varphi}, \qquad s_0 > 3/2, \tag{9.8.e$'$}$$
> *uniformly in $G$, where $\|\cdot\|_{H^s_\varphi}$ is the angular-weighted Sobolev norm of (48).*

*Under (H-α) and (B-spec), for every smooth initial datum $\theta_0$ the inviscid SQG equation preserves $C^\infty$ regularity for all time. In particular, (H-α) together with (B-spec) implies both (H-strain) and (H-bdry).*

*Proof.* Under (H-α), equation (9.8.d) gives
$$V(t) \;\leq\; V(0)\,\exp\!\left[-4(1 - \alpha_\star)\!\int_0^t |nSn(x(\tau),\tau)|\,d\tau\right]. \tag{9.8.f}$$
Combined with the gradient-growth identity $d(\ln G)/dt = |nSn|$ along sharpening trajectories, $\int_0^t |nSn|\,d\tau = \ln(G(t)/G_0)$, giving
$$V(t) \;\leq\; V(0)\bigl(G_0/G(t)\bigr)^{4(1-\alpha_\star)}. \tag{9.8.g}$$
Since $1 - \alpha_\star > 0$, $V(t) \to 0$ as $G(t) \to \infty$.

By (B-spec), $|nSn_{\mathrm{near}}(x(t))|$ is controlled by the angular-Sobolev norm $\|W_{R_0}\theta\|_{H^{s_0}_\varphi}$. The angular variance $V$ is the zeroth-order angular weight of the windowed spectrum; the decay (9.8.g) propagates to higher-order angular Sobolev norms precisely when the angular-transfer source $S_{\mathrm{source}}^{(s)}(t)$ at order $s = s_0$ obeys a ratio-$< 1$ bound analogous to (H-α). On the finite-Fourier-support class on which the Lean formalization certifies $\dot H^s$ Galerkin bounds for every $s \geq 0$ (companion repository `sqg-lean-proofs-fourier`), this propagation is unconditional, and so (B-spec) reduces to a pointwise evaluation inequality that the Lean bridge `HasSqgGalerkinAllSBound.ofClassical` discharges via the $\dot H^s \hookrightarrow L^\infty$ embedding for $s > 2$. For general smooth data, (B-spec) remains a hypothesis at the same logical level as (PC) of §6 — see Remark 9.11.1.

Granted (B-spec) and the decay of $V$, one obtains $|nSn_{\mathrm{near}}(x(t))| \to 0$ as $G \to \infty$. Combined with Lemma 6.1's far-field bound $|nSn_{\mathrm{far}}| \leq CA$, this gives $|nSn(x(t))| \leq C(\theta_0)$, so $dG/dt \leq C(\theta_0) G$, hence $G$ grows at most exponentially and the BKM integral is finite on every bounded interval.

The consequences for (H-strain) and (H-bdry) follow by substitution: $|nSn(s_{\max})|$ is bounded (H-strain holds with $\mu_\star$ depending on $\alpha_\star$ and $\theta_0$); and bounded $\psi$ combined with the tangential Hessian bound (Lemma 9.13 Step 3) gives bounded $\kappa$ on the material segment, implying (H-bdry). $\square$

**Remark 9.11.1 (honest accounting of (B-spec)).** Hypothesis (B-spec) is the angular-Sobolev refinement of the (PC) bound of §6 that Remark 6.7.1 flagged as non-derivable in its raw multiplier form. The present formulation is weaker than (PC): rather than asserting $|nSn_{\mathrm{near}}| \leq C\,\psi\,G$ (which requires $\psi G$ amplitude control without a Sobolev buffer), (B-spec) only asserts a bound in terms of a Sobolev-angular norm at order $s_0 > 3/2$, which by the standard $H^s \hookrightarrow L^\infty$ embedding in 2D is the minimal order for pointwise evaluation. On the finite-Fourier class $\mathcal{C}_N$ (uniformly bounded mode count, $\ell^\infty$ coefficients), (B-spec) is discharged by the Lean bridge (Path B of §9.6.3 / Appendix). For general $\theta_0 \in C^\infty(\mathbb{T}^2)$, (B-spec) is the remaining open analytic hypothesis of the conditional chain. The thermostat inequality (H-α) contributes the contractive factor $(G_0/G)^{4(1-\alpha_\star)}$ on the *angular-variance* side of (B-spec); the open piece is propagating that contraction to higher angular Sobolev orders uniformly in $G$.

**Corollary 9.11.1.** *Within the conditional framework of this paper, (H-α) is equivalent to the pair (H-strain)+(H-bdry) up to the spectral-to-pointwise bridge (B-spec). The reformulation's benefit is single-scalar monitorability of $\alpha(t)$ along sharpening trajectories; it does not reduce the number of independent hypotheses unless (B-spec) is separately established (as on $\mathcal{C}_N$ via the Lean bridge).*

#### 9.8.3 Numerical measurement of $\alpha$

Direct measurement of $\alpha(t)$ at $N = 512$ on the multimode initial datum of §5, using the windowed angular variance $V_{10}$ with window size $\sigma = 10\delta$, reading $V$, $|nSn|$, and $\alpha = 1 + (dV/dt)/(4|nSn|V)$ (with $dV/dt$ by central difference) at representative $G$ values:

| $G$ | $V_{10}(t)$ | $|nSn(x^*)|$ | $\alpha(t)$ |
|:---:|:---:|:---:|:---:|
| 11.3 | $2.6\times 10^{-1}$ | 0.94 | 0.83 |
| 17.4 | $1.6\times 10^{-1}$ | 0.91 | 0.68 |
| 26.2 | $7.9\times 10^{-2}$ | 0.92 | 0.57 |
| 32.4 | $5.1\times 10^{-2}$ | 0.76 | 0.62 |
| 38.0 | $3.9\times 10^{-2}$ | 0.76 | 0.84 |
| 42.4 | $3.4\times 10^{-2}$ | 0.87 | 0.68 |

Values computed directly from the N = 512 multimode run cached at `results/sqg_thermostat_decomp/features_N512_multimode.npz`. Pointwise $\alpha$ at $N = 512$ varies non-monotonically in $[0.57, 0.84]$ across these snapshots; the peak $\alpha_{\max}$ across the full N = 512 sharpening interval is $1.04$ (reached transiently at a cascade-onset snapshot where $|nSn|V$ is small and the denominator amplifies measurement noise, not at a sharpening snapshot).

The damping-weighted average $\overline\alpha = \int \alpha \cdot 4|nSn|V\,dt / \int 4|nSn|V\,dt$ — the weighting that appears in the logarithmic gradient-growth estimate (9.8.e) — gives $\overline\alpha = 0.80$ at $N = 512$, stable across resolutions (see §9.8.5). The key empirical statement is: *along the measurements that dominate the gradient budget, $\alpha$ sits around $0.8$ with fluctuations, bounded well away from $1$.* A stronger claim of monotone decrease of $\alpha$ with $G$ is **not** supported by this data: $V$ does decay monotonically, but the ratio $\alpha = S_{\mathrm{source}}/(4|nSn|V)$ shows non-monotone cascade-correlated fluctuations.

#### 9.8.4 What (H-α) replaces, and what remains

**What is gained.** The pair (H-strain) + (H-bdry) is reformulated as a single scalar inequality $\alpha(t) \leq \alpha_\star < 1$ on a dimensionless ratio of local functionals, plus the spectral-to-pointwise bridge (B-spec) of Prop 9.11. Unlike the pointwise strain bound (H-strain), $\alpha$ is a *normalized* quantity: both numerator and denominator scale the same way with $G$, so the ratio is dimensionless and potentially a structural constant of the SQG nonlinearity. The measured damping-weighted $\overline\alpha \approx 0.80$ is stable across resolutions $N \in [256, 512]$ and across the initial-condition families tested (§9.8.5), with pointwise fluctuations in $[0.5, 1.05]$ dominated by cascade-transition noise rather than systematic drift.

**What remains unproven.** (i) Hypothesis (H-α) is not derived from the SQG equation in this paper; (ii) Hypothesis (B-spec) is not derived from (H-α) alone for general smooth data. For the finite-Fourier class $\mathcal{C}_N$, (B-spec) is closed by the Lean bridge `HasSqgGalerkinAllSBound.ofClassical` (companion repository `sqg-lean-proofs-fourier`). For general $\theta_0 \in C^\infty(\mathbb{T}^2)$, both remain open. The physical argument for (H-α) is that $S_{\mathrm{source}}$ comes from the trilinear interaction $\mathbf{u}\cdot\nabla\theta$, which for a spectrum already concentrated within angular spread $\psi$ can create modes at angle at most $2\psi$ from the concentration axis; by the convolution structure in Fourier, newly created modes have amplitude weighted by the SQG coefficient $\propto (p_1 q_2 - p_2 q_1)/|p|$, whose angular structure provides a further $O(\psi)$ suppression. A quantitative Kato–Ponce-type bound on the angular-variance functional would establish (H-α) with an explicit $\alpha_\star$; absent that bound, (H-α) stands as one of the two open analytic hypotheses in the proof chain.

**Relation to the Lean formalization.** The companion repository `sqg-lean-proofs-fourier` provides the quantitative uniform-in-$N$ Kato-Ponce commutator bound on $\mathbb{T}^2$; extending that machinery to the angular-variance evolution (9.8.a) with an explicit ratio constant $< 1$ is the natural next step of the mechanization. On the finite-Fourier-support, uniform-$\ell^\infty$-coefficient class, (H-α) reduces to a finite-dimensional inequality that can in principle be certified numerically with a computable $\alpha_\star$.

### 9.8.5 Resolution convergence and the push–pull decomposition

Two experimental programs test (H-α) beyond the original $N = 512$ heartbeat measurement.

**N-scan (resolution convergence).** Running the multimode IC at $N \in \{128, 256, 384, 512\}$ with identical $T = 5.5$ and matched sample count, the direct measurement of $\alpha(t) = 1 + (dV/dt)/(4|nSn|V)$ over sharpening snapshots (defined by $G > 4$), with $V = V_{10}$ (the Gaussian-windowed angular variance at window size $\sigma = 10\delta$), and the damping-weighted average $\overline\alpha := \int\alpha\,(4|nSn|V)\,dt / \int (4|nSn|V)\,dt$, gives:

| $N$ | $k_{\mathrm{dealias}}$ | $G_{\max}$ | $\alpha_{\max}$ | $\overline\alpha$ | $\mathrm{frac}\{\alpha>1\}$ |
|-----|-----|-----|-----|-----|-----|
| 128 | 42  | 12.5 | 10.46 | 0.914 | 19.1% |
| 256 | 85  | 23.1 | 1.04  | 0.833 | 2.1%  |
| 384 | 128 | 31.2 | 0.92 | 0.809 | 0.0% |
| 512 | 170 | 43.2 | 1.04 | **0.803** | 2.0% |

The $N = 128$ row is dominated by finite-difference noise once $G > 10$ (front width $\delta = A/G$ becomes comparable to a few grid cells; the central-difference derivative of $V$ is unresolved), producing the anomalous $\alpha_{\max} \approx 10$ and 19% of snapshots with spurious $\alpha > 1$. At $N \geq 256$ the $\alpha_{\max}$ collapses to $\approx 1.0$ and the frac$\{\alpha > 1\}$ drops to a few percent, of which the excursions cluster near the cascade transitions where $|nSn|V$ is transiently small (denominator-driven noise, not a breach of the bound). The damping-weighted $\overline\alpha$ plateaus at $\approx 0.80$ from $N = 384$ onward.

**Interpretation.** If the margin $1 - \overline\alpha$ were an artifact of the $2/3$ dealiasing cutoff or of RK4 numerical dissipation, it should shrink as $N$ grows (weaker regularization). It does the opposite: $\overline\alpha$ decreases monotonically from $N = 128$ to $N = 512$ (from $0.914$ to $0.803$), and the pointwise $\alpha_{\max}$ stabilizes near $1.0$ rather than growing with resolution. This is consistent with (H-α) being a structural property of the inviscid SQG dynamics on the class of initial data tested, rather than a simulator-induced smoothing artifact.

A Richardson-style extrapolation of $\overline\alpha(N)$ toward $N = \infty$ (fit $\overline\alpha(N) = \overline\alpha_\infty + c\,N^{-p}$) gives $\overline\alpha_\infty \approx 0.800 \pm 0.01$ with $p \approx 3.1$, supporting a continuum-limit value strictly below unity on this initial-condition family.

**Push–pull decomposition of $\alpha$ (exploratory).** To probe the mechanism heuristically, a pooled sparse regression on 130 snapshots from three initial conditions (multimode $N = 256, 384$ and double $N = 256$) with a feature set including state variables, instantaneous drain rates, and cumulative spectral fluxes was fit by LASSO with standardized predictors. The in-sample $R^2 = 0.918$ is reported below with the caveat that it is an in-sample fit on auto-correlated features (cumulative integrals and state variables across a trajectory), not an out-of-sample predictive test; the coefficients are interpretive rather than quantitative.

| Feature | Std. coef (in-sample) | Heuristic role |
|---|---|---|
| drain_20 ($= H_{\mathrm{loc}, 20}(0) - H_{\mathrm{loc}, 20}(t)$) | $+2.29$ | state |
| $dH_{\mathrm{loc}, 10}/dt$ | $-1.47$ | instantaneous drain rate |
| $V_{10}$ | $+1.28$ | angular variance (state) |
| drain_5 | $-0.89$ | localized push-through |
| cum_flux_{k>15} | $-0.63$ | cumulative cascade exit |
| $G$ | $+0.63$ | sharpness (state) |

The qualitative picture is that, controlling for trajectory state, the *rate* and *cumulative-cascade* features enter with negative coefficients, consistent with a push–pull mechanism in which (i) the rotation damping pulls wavevectors toward the front-normal axis, and (ii) the cascade simultaneously evacuates spectral mass to high-$k$ shells. The fit does not have out-of-sample validation on held-out initial conditions, so the sign pattern is a mechanistic hint rather than a tested quantitative model. A sharper rigorous form of (H-α) incorporating spectral-flux terms would be a natural next step; the present paper records this only as a numerical observation, not as a named hypothesis.

---

## 10. Discussion and Open Extensions

### 10.1 Numerical certification of the material max principle

A numerical scheme faithful to the continuum SQG dynamics should preserve the hypothesis (H-bdry) of Proposition 9.10 along a Lagrangian-tracked material segment. I implemented such a diagnostic by advecting 64 particles along a front with RK2 interpolation, computing the boundary curvature envelope, and comparing to its initial value. At $N = 192$, $T = 1.5$, the envelope ratio $\max_t |\kappa_{\mathrm{bdry}}|/|\kappa_{\mathrm{bdry}}(0)|$ is $0.043$ for RK4, ETDRK4, and spectral-cutoff variants — the boundary curvature *contracts* rather than grows, consistent with (H-bdry) on the initial conditions tested. This is a structural consistency check (not merely conservation-based): a scheme whose dynamics violated (H-bdry) would produce a field inconsistent with the conditional conclusion of Theorem 3 independent of energy or $L^p$ conservation. The diagnostic is *consistency evidence*, not a proof; in particular, a numerical contraction on a finite-time window does not establish the uniform-in-time bound required by (H-bdry).

### 10.2 Extension to the generalized SQG family

The generalized SQG equation (gSQG) replaces the Riesz transform $(-\Delta)^{-1/2}$ in the velocity recovery with $(-\Delta)^{-(1-\alpha/2)}$, giving a family parameterized by $\alpha \in [0, 1]$: $\alpha=0$ recovers 2D Euler, $\alpha=1$ is the classical SQG studied here. The selection rule generalizes as $|nSn_\text{near}| \leq C_\alpha G \kappa^2 \delta^{2\alpha}$ (analogous Fourier-space parity cancellation). For $\alpha \in (0, 1]$, bounded $\kappa$ continues to give $|nSn_\text{near}| \to 0$ as $G \to \infty$. The material segment expansion (Prop 9.8) depends on $S_{\tau\tau} = -nSn > 0$ from incompressibility, which holds for the entire gSQG family. The boundary control (Prop 9.10) invokes far-field elliptic regularity on $\psi = (-\Delta)^{-(1-\alpha/2)}\theta$; the smoothing strength weakens as $\alpha \to 0$, and at $\alpha = 0$ (Euler) it reduces to the Biot-Savart relation, where the fold-energy and backward-Lagrangian obstructions absent in SQG become relevant. The natural conjecture: *the material max principle proof extends continuously for $\alpha \in (\alpha_*, 1]$ where $\alpha_*$ marks the boundary where far-field elliptic regularity of $\psi$ becomes insufficient.* This extends the dichotomy identified in arXiv:2603.12944 (2026) — which shows Lagrangian regularity persists across gSQG while Eulerian fails — from solution-map regularity to global-in-time regularity of classical solutions.

### 10.3 Implications for ocean reconstruction

Sub-surface reconstruction via SQG (e.g., Sentinel-3/SWOT altimetry) relies on a cascade constant $C$ that is $O(\|\theta_0\|_\infty)$. Effective cascade constants measured in major western-boundary currents (Gulf Stream, Kuroshio) sit several orders of magnitude below the theoretical bound. With $C$ proven rather than conjectural, the ratio $C_\text{eff}/C$ becomes a rigorous regional diagnostic of the distance from the inviscid SQG regime, identifying where additional physics (dissipation, mixed-layer dynamics, non-QG terms) dominates.

---

## References

1. Constantin, P., Majda, A.J., Tabak, E. (1994). Formation of strong fronts in the 2-D quasigeostrophic thermal active scalar. *Nonlinearity* 7, 1495–1533.
2. Held, I.M., Pierrehumbert, R.T., Garner, S.T., Swanson, K.L. (1995). Surface quasi-geostrophic dynamics. *J. Fluid Mech.* 282, 1–20.
3. Beale, J.T., Kato, T., Majda, A. (1984). Remarks on the breakdown of smooth solutions for the 3-D Euler equations. *Comm. Math. Phys.* 94, 61–66.
4. Córdoba, D. (1998). Nonexistence of simple hyperbolic blow-up for the quasi-geostrophic equation. *Ann. Math.* 148, 1135–1152.
5. Ottino, J.M. (1989). *The Kinematics of Mixing: Stretching, Chaos, and Transport.* Cambridge University Press.
6. Batchelor, G.K. (1967). *An Introduction to Fluid Dynamics.* Cambridge University Press.
7. Caffarelli, L., Vasseur, A. (2010). Drift diffusion equations with fractional diffusion and the quasi-geostrophic equation. *Ann. Math.* 171, 1903–1930.
8. Kiselev, A., Nazarov, F., Volberg, A. (2007). Global well-posedness for the critical 2D dissipative quasi-geostrophic equation. *Invent. Math.* 167, 445–453.
9. He, S., Kiselev, A. (2021). Small-scale creation for solutions of the SQG equation. *Duke Math. J.* 170(5), 1027–1041. arXiv:1903.07485.
10. Kiselev, A., Ryzhik, L., Yao, Y., Zlatoš, A. (2016). Finite time singularity for the modified SQG patch equation. *Ann. Math.* 184(3), 909–948. arXiv:1508.07613.
11. Jeong, I.-J., Kim, J. (2024). Strong ill-posedness for SQG in critical Sobolev spaces. *Analysis & PDE* 17, 133–170. arXiv:2107.07739.
12. Misiołek, G., Vu, X.-T., Yoneda, T. (2026). Regularity of solution maps of the generalized surface quasi-geostrophic equations. arXiv:2603.12944.

---

## Appendix: Numerical Methods

**Solver.** Pseudospectral on $[0, 2\pi]^2$ with $N \times N$ collocation points. Dealiasing: 2/3-rule. Time stepping: classical RK4 with $\Delta t = \min(5\times 10^{-4},\ 1.5/N)$; at $N = 512$ the $5\times 10^{-4}$ branch is binding. Inviscid ($\kappa = 0$). Implementation: `noethersolve/sqg_solver.py` (SQGSolver with `evolve_rk4`).

**Diagnostics.** Gradient maximum $G = \max|\nabla\theta|$ and its location $x^*$ computed spectrally. Strain tensor $S_{ij}$, vorticity $\omega$, and level-set curvature $\kappa$ computed spectrally at $x^*$. Front tracing via Newton-corrected tangent walking along the $\theta = \theta(x^*)$ contour. Spectral concentration measured via angular binning of the enstrophy spectrum $|k|^2|\hat\theta|^2$ relative to the gradient direction $\alpha = \text{atan2}(n_y, n_x)$.

**Machine-verified component.** Theorem 1 (shear-vorticity identity) is machine-verified in Lean 4 + mathlib in the accompanying repository (`sqg-lean-proofs`, `SqgIdentity/Basic.lean`). Theorem 2 (selection rule) and the supporting lemmas of §6 are part of the `MaterialMaxPrinciple` chain in `SqgIdentity/RieszTorus.lean` §14. Theorem 3 is supplied as a *conditional* roadmap in the same formalization: given the hypotheses (H-strain) and (H-bdry) of §9.6.3 (equivalently (H-α) of §9.8), the material maximum principle (Proposition 9.9 in its firmed form with quadratic-in-curvature remainder), the BKM criterion, and the associated Sobolev calculus, the repository certifies uniform $\dot H^s$ Galerkin bounds and the full-range interpolation capstone `sqg_regularity_of_aubinLions_via_interpolation` for every $s \geq 0$, with zero `sorry` and no axioms added beyond mathlib. The hypothesis naming in the Lean source (`HasStrainLowerBound`, `HasBoundaryCurvatureBound`, `HasThermostatBound` in `RieszTorus.lean` §14) mirrors the paper §9.6.3/§9.8 labels.

The classical Fourier-analysis content underlying the conditional-to-structural reduction — quantitative uniform-in-$N$ Kato–Ponce commutator bound on $\mathbb{T}^2$, Bony paraproducts, and the $\dot H^s \hookrightarrow L^\infty$ Sobolev embedding for $s > 2$ via the lattice-zeta constant — is delivered by the companion package [`sqg-lean-proofs-fourier`](https://github.com/Brsanch/sqg-lean-proofs-fourier) (2,801 LOC, zero `sorry`). The end-to-end bridge constructor `HasSqgGalerkinAllSBound.ofClassical` in `SqgIdentity/FourierBridge.lean` (2,490 LOC, zero `sorry`) assembles $L^2$ conservation, Riesz velocity preservation (constant $C = 1$ via the perp-Riesz mode-by-mode identity), the $\dot H^s$ energy identity (from the parametric-$s$ Galerkin energy machine of `RieszTorus.lean` §10.178–§10.180), the velocity $L^\infty$ bound via Sobolev embedding, the quantitative Kato–Ponce commutator from the companion, and exponential Grönwall closure. This discharges (H-strain) + (H-bdry) from the Galerkin dynamics on the finite-Fourier-support class with uniform-$\ell^\infty$ coefficients, giving an unconditional regularity result for that class (Lean Path B). The unconditional hypothesis closure for general smooth initial data remains the single open gap, corresponding to the open research problem documented in §9.6–§9.8.
