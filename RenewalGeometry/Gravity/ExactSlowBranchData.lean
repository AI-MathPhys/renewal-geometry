/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Shared data of the exact slow-constraint branch
  (`eq:supp-exact-weak-decomposition`, `eq:main-exact-five-map`,
  `eq:supp-L0-definition`, `eq:supp-f0-definition`,
  `eq:supp-exact-complete-LS-blocks`, `eq:supp-exact-Xi-reduced`,
  `eq:supp-exact-reduced-functions`, `eq:supp-exact-slope-polynomial`,
  `eq:supp-exact-original-slope-directions`, `eq:supp-exact-g2`,
  `eq:supp-exact-R-two-row`; emergent-spacetime manuscript)

Reusable encodings of the finite objects of the exact constraint branch.  As in
`Gravity/SupplementExactConstraintRankExact.lean`, all matrices enter as abstract
(continuous) linear maps between real normed spaces; their identification with the
coefficients of the actual finite action is not formalised.

Notation (paper → Lean):
* `x`-space `ℝ²⁹⁴` → `Xs`, weak space `ℝ²⁹` → `W`, weak-zero space `𝒵_g` → `Zg`,
  constant-shift space `ℋ` → `Hs`; the slow variable is `ξ = (x, z) : Xs × W`.
* `Φ₀(x, z) = C_red x + B z` → `leadingConstraint Cred B`.
* `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` with projections `p_g, p_H` and insertions `J_g, J_H`
  → `WeakDecomposition B Jg JH pg pH`; `ker B = 𝒵_g ⊕ ℋ` → `KernelSplit B Jg JH`.
* `𝔪(ξ) = p_H Φ₁(ξ)`, `𝔤(ξ) = p_g C_red (b_s + Σ₀(ξ))`, `𝔆_sl = (𝔤, 𝔪)`
  → `slowMean`, `slowGradient`, `slowConstraint`.
* `𝓛₀ κ = (p_g C_red Df(0) κ, p_H Dg(0) κ)` and `f₀` → `initialGateMap`,
  `initialForcing`; its restriction to `𝒦₀ = ker Φ₀` → `initialGateOnKernel`.
* For an arbitrary linear map `L` on a direct sum `K = J_g 𝒵_g ⊕ E_x 𝒳_h`, the blocks
  `𝒜_g, ℬ_x, 𝒞_g, 𝒟_x` of `eq:supp-exact-complete-LS-blocks` → `blockAg`, `blockBx`,
  `blockCg`, `blockDx`, and `ℋ_x = 𝒟_x - 𝒞_g 𝒜_g⁻¹ ℬ_x` → `reducedHx` (the inverse
  `𝒜_g⁻¹` is passed explicitly as `AgInv`).
* Second derivative `D²φ(x)[u, w]` → `sndDeriv φ x u w`, with the second-order chain
  rule `sndDeriv_comp`.
* `Ξ(r, y) = 𝖤 r + J_g γ(r, y) + J_H y` → `reducedChart`; `𝓕 = L_X f ∘ Ξ`,
  `𝓗 = 𝔠_H ∘ Ξ` → `reducedDrift`, `reducedHarmonic`; the slope polynomial
  `𝒬(c) = 𝓗_r 𝓕_r v + 𝓗_rr[v,v] + 2𝓗_ry[v,c] + 𝓗_yy[c,c]` → `slopePolynomial`.
* `Ê = 𝖤 - J_g 𝒜_g⁻¹ D𝔠_g(0) 𝖤`, `b_* = Ê v`, `b(c) = b_* + J_H c`,
  `a_* = Ê L_X Df(0) b_*` → `hatE`, `slopeBase`, `slopeDirection`, `slopeAccel`.
* `𝔤₂ = D²𝔠_g(0)`, `𝒞 = 𝒞_g 𝒜_g⁻¹`, `ℛ(c) = 2𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)`
  → `gTwo`, `scriptC`, `scriptR`.
-/

namespace RenewalGeometry
namespace ExactSlowBranch

open Module Filter Topology

/-! ## The leading slow constraint and the weak decomposition -/

section Decomposition

variable {Xs W Zg Hs : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]

/-- The leading slow constraint `Φ₀(x, z) = C_red x + B z`
(`eq:supp-exact-slow-coefficients`). -/
def leadingConstraint (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) : Xs × W →L[ℝ] W :=
  Cred.coprod B

@[simp]
theorem leadingConstraint_apply (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (ξ : Xs × W) :
    leadingConstraint Cred B ξ = Cred ξ.1 + B ξ.2 := rfl

/-- The direct decomposition `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` of
`eq:supp-exact-weak-decomposition`, given by the insertions `J_g, J_H` and the two
indicated projections `p_g, p_H`, which annihilate `Ran B`. -/
structure WeakDecomposition (B : W →L[ℝ] W) (Jg : Zg →L[ℝ] W) (JH : Hs →L[ℝ] W)
    (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) : Prop where
  pg_Jg : ∀ z, pg (Jg z) = z
  pH_JH : ∀ h, pH (JH h) = h
  pg_JH : ∀ h, pg (JH h) = 0
  pH_Jg : ∀ z, pH (Jg z) = 0
  pg_B : ∀ w, pg (B w) = 0
  pH_B : ∀ w, pH (B w) = 0
  split : ∀ w, ∃ z, w = B z + Jg (pg w) + JH (pH w)

/-- `ker B = 𝒵_g ⊕ ℋ` (used in `lem:supp-exact-two-row-elimination`). -/
structure KernelSplit (B : W →L[ℝ] W) (Jg : Zg →L[ℝ] W) (JH : Hs →L[ℝ] W) : Prop where
  B_Jg : ∀ z, B (Jg z) = 0
  B_JH : ∀ h, B (JH h) = 0
  ker_le : ∀ w, B w = 0 → ∃ z h, w = Jg z + JH h

/-- A vector with vanishing `p_g` and `p_H` projections lies in `Ran B`. -/
theorem WeakDecomposition.mem_range_of_proj_zero {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W}
    {JH : Hs →L[ℝ] W} {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}
    (hD : WeakDecomposition B Jg JH pg pH) {w : W} (hg : pg w = 0) (hH : pH w = 0) :
    ∃ z, B z = w := by
  obtain ⟨z, hz⟩ := hD.split w
  exact ⟨z, by rw [hz, hg, hH]; simp⟩

/-- `Ran Φ₀ = ker p_H` under the weak decomposition and the coupling tests
`p_H C_red = 0`, `p_g C_red` onto `𝒵_g` (the range part of
`prop:supp-exact-slow-rank`, used in `prop:supp-exact-slow-correction`). -/
theorem range_leadingConstraint {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W}
    {JH : Hs →L[ℝ] W} {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}
    (hD : WeakDecomposition B Jg JH pg pH) (hHC : ∀ x, pH (Cred x) = 0)
    (hgC : Function.Surjective fun x => pg (Cred x)) :
    LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)
      = LinearMap.ker (pH : W →ₗ[ℝ] Hs) := by
  ext w
  constructor
  · rintro ⟨ξ, rfl⟩
    simp [LinearMap.mem_ker, hHC, hD.pH_B]
  · intro hw
    have hw' : pH w = 0 := hw
    obtain ⟨x, hx⟩ := hgC (pg w)
    have hx' : pg (Cred x) = pg w := hx
    obtain ⟨z, hz⟩ := hD.mem_range_of_proj_zero (w := w - Cred x)
      (by rw [map_sub, hx', sub_self])
      (by rw [map_sub, hw', hHC, sub_self])
    exact ⟨(x, z), by simp [hz]⟩

/-- The mean (harmonic) slow compatibility `𝔪(ξ) = p_H Φ₁(ξ)`. -/
def slowMean (pH : W →L[ℝ] Hs) (Φ₁ : Xs × W → W) (ξ : Xs × W) : Hs := pH (Φ₁ ξ)

/-- The gradient slow compatibility `𝔤(ξ) = p_g C_red (b_s + Σ₀(ξ))`. -/
def slowGradient (pg : W →L[ℝ] Zg) (Cred : Xs →L[ℝ] W) (bs : Xs) (Sig0 : Xs × W → Xs)
    (ξ : Xs × W) : Zg := pg (Cred (bs + Sig0 ξ))

/-- The five-component slow compatibility map
`𝔆_sl(ξ) = (p_g C_red [b_s + Σ₀(ξ)], p_H Φ₁(ξ))` (`eq:main-exact-five-map`). -/
def slowConstraint (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W) (bs : Xs)
    (Sig0 : Xs × W → Xs) (Φ₁ : Xs × W → W) (ξ : Xs × W) : Zg × Hs :=
  (slowGradient pg Cred bs Sig0 ξ, slowMean pH Φ₁ ξ)

/-- The initial gate map `𝓛₀ κ = (p_g C_red Df(0) κ, p_H Dg(0) κ)`
(`eq:supp-L0-definition`) on the full slow space; `Df0 = Df(0)`, `Dg0 = Dg(0)`. -/
def initialGateMap (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (Df0 : Xs × W →L[ℝ] Xs) (Dg0 : Xs × W →L[ℝ] W) : Xs × W →L[ℝ] Zg × Hs :=
  (pg.comp (Cred.comp Df0)).prod (pH.comp Dg0)

@[simp]
theorem initialGateMap_apply (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (Df0 : Xs × W →L[ℝ] Xs) (Dg0 : Xs × W →L[ℝ] W) (κ : Xs × W) :
    initialGateMap pg pH Cred Df0 Dg0 κ = (pg (Cred (Df0 κ)), pH (Dg0 κ)) := rfl

/-- The initial forcing `f₀ = (p_g {C_red s₀ + Dg(0) b}, p_H (h₀ - b_w))`
(`eq:supp-f0-definition`). -/
def initialForcing (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (Dg0 : Xs × W →L[ℝ] W) (s₀ : Xs) (b : Xs × W) (h₀ : W) : Zg × Hs :=
  (pg (Cred s₀ + Dg0 b), pH (h₀ - b.2))

/-- The initial gate map restricted to the critical kernel `𝒦₀ = ker Φ₀`, the map whose
Lyapunov–Schmidt reduction is `thm:supp-exact-three-row`. -/
def initialGateOnKernel (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) (Cred : Xs →L[ℝ] W)
    (B : W →L[ℝ] W) (Df0 : Xs × W →L[ℝ] Xs) (Dg0 : Xs × W →L[ℝ] W) :
    LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W) →ₗ[ℝ] Zg × Hs :=
  (initialGateMap pg pH Cred Df0 Dg0).toLinearMap.domRestrict
    (LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))

/-- A weak insertion `J : 𝒵 → ℝ²⁹` with `B J = 0`, viewed as a map into
`𝒦₀ = ker Φ₀` via `z ↦ (0, J z)` (the convention "when composed with a map on `𝒦₀`,
`J_g` means `(0, J_g ·)`"). -/
def kernelInsertion {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (J : Z →L[ℝ] W) (hJ : ∀ z, B (J z) = 0) :
    Z →ₗ[ℝ] LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W) :=
  LinearMap.codRestrict (LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))
    ((ContinuousLinearMap.inr ℝ Xs W).comp J).toLinearMap
    (fun z => by simp [LinearMap.mem_ker, hJ])

@[simp]
theorem kernelInsertion_apply {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (J : Z →L[ℝ] W) (hJ : ∀ z, B (J z) = 0) (z : Z) :
    (kernelInsertion Cred B J hJ z : Xs × W) = (0, J z) := rfl

end Decomposition

/-! ## Lyapunov–Schmidt blocks of a map on a direct sum -/

section Blocks

variable {K Zg Xh Hs : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup Zg] [Module ℝ Zg]
  [AddCommGroup Xh] [Module ℝ Xh] [AddCommGroup Hs] [Module ℝ Hs]

/-- Upper vertical block `𝒜_g` of `𝓛₀ (J_g z + E_x x)`
(`eq:supp-exact-complete-LS-blocks`). -/
def blockAg (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) : Zg →ₗ[ℝ] Zg :=
  (LinearMap.fst ℝ Zg Hs).comp (L.comp Jg)

/-- Upper horizontal block `ℬ_x`. -/
def blockBx (L : K →ₗ[ℝ] Zg × Hs) (Ex : Xh →ₗ[ℝ] K) : Xh →ₗ[ℝ] Zg :=
  (LinearMap.fst ℝ Zg Hs).comp (L.comp Ex)

/-- Lower vertical block `𝒞_g`. -/
def blockCg (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) : Zg →ₗ[ℝ] Hs :=
  (LinearMap.snd ℝ Zg Hs).comp (L.comp Jg)

/-- Lower horizontal block `𝒟_x`. -/
def blockDx (L : K →ₗ[ℝ] Zg × Hs) (Ex : Xh →ₗ[ℝ] K) : Xh →ₗ[ℝ] Hs :=
  (LinearMap.snd ℝ Zg Hs).comp (L.comp Ex)

/-- The reduced (Schur) block `ℋ_x = 𝒟_x - 𝒞_g 𝒜_g⁻¹ ℬ_x`
(`eq:supp-exact-complete-LS-blocks`), with `AgInv = 𝒜_g⁻¹`. -/
def reducedHx (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) (Ex : Xh →ₗ[ℝ] K)
    (AgInv : Zg →ₗ[ℝ] Zg) : Xh →ₗ[ℝ] Hs :=
  blockDx L Ex - (blockCg L Jg).comp (AgInv.comp (blockBx L Ex))

/-- `𝓛₀ (J_g z + E_x x) = (𝒜_g z + ℬ_x x, 𝒞_g z + 𝒟_x x)`
(`eq:supp-exact-complete-LS-blocks`). -/
theorem map_split_eq_blocks (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) (Ex : Xh →ₗ[ℝ] K)
    (z : Zg) (x : Xh) :
    L (Jg z + Ex x) = (blockAg L Jg z + blockBx L Ex x, blockCg L Jg z + blockDx L Ex x) := by
  rw [map_add]; rfl

theorem reducedHx_apply (L : K →ₗ[ℝ] Zg × Hs) (Jg : Zg →ₗ[ℝ] K) (Ex : Xh →ₗ[ℝ] K)
    (AgInv : Zg →ₗ[ℝ] Zg) (x : Xh) :
    reducedHx L Jg Ex AgInv x = blockDx L Ex x - blockCg L Jg (AgInv (blockBx L Ex x)) := rfl

end Blocks

/-! ## Second derivatives and the second-order chain rule -/

section SecondDerivative

variable {P V F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second (Fréchet) derivative `D²φ(x)[u, w]`. -/
noncomputable def sndDeriv (φ : P → F) (x u w : P) : F := fderiv ℝ (fderiv ℝ φ) x u w

/-- **Second-order chain rule.** For `C²` maps,
`D²(φ ∘ Ξ)(p)[u, w] = D²φ(Ξ p)[DΞ(p) u, DΞ(p) w] + Dφ(Ξ p)[D²Ξ(p)[u, w]]`. -/
theorem sndDeriv_comp (φ : V → F) (Ξ : P → V) (p : P) (hφ : ContDiffAt ℝ 2 φ (Ξ p))
    (hΞ : ContDiffAt ℝ 2 Ξ p) (u w : P) :
    sndDeriv (φ ∘ Ξ) p u w
      = sndDeriv φ (Ξ p) (fderiv ℝ Ξ p u) (fderiv ℝ Ξ p w)
        + fderiv ℝ φ (Ξ p) (sndDeriv Ξ p u w) := by
  have hφ1 : ∀ᶠ y in 𝓝 (Ξ p), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hΞ1 : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ Ξ q :=
    (hΞ.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hΞc : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ φ (Ξ q) :=
    hΞ.continuousAt.eventually hφ1
  have heq : fderiv ℝ (φ ∘ Ξ) =ᶠ[𝓝 p] fun q => (fderiv ℝ φ (Ξ q)).comp (fderiv ℝ Ξ q) := by
    filter_upwards [hΞ1, hΞc] with q h1 h2
    exact fderiv_comp q h2 h1
  have hD2φ : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (Ξ p)) (Ξ p) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hD2Ξ : HasFDerivAt (fderiv ℝ Ξ) (fderiv ℝ (fderiv ℝ Ξ) p) p :=
    ((hΞ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => fderiv ℝ φ (Ξ q))
      ((fderiv ℝ (fderiv ℝ φ) (Ξ p)).comp (fderiv ℝ Ξ p)) p :=
    hD2φ.comp p (hΞ.differentiableAt two_ne_zero).hasFDerivAt
  have hall := hcomp.clm_comp hD2Ξ
  unfold sndDeriv
  rw [heq.fderiv_eq, hall.fderiv]
  simp [add_comm]

/-- The second derivative of a map vanishing near `p` is zero. -/
theorem sndDeriv_of_eventually_zero (φ : P → F) (p : P) (h : φ =ᶠ[𝓝 p] 0) (u w : P) :
    sndDeriv φ p u w = 0 := by
  unfold sndDeriv
  have h1 : fderiv ℝ φ =ᶠ[𝓝 p] fderiv ℝ (0 : P → F) := h.fderiv
  rw [h1.fderiv_eq]
  simp

/-- The first derivative of a map vanishing near `p` is zero. -/
theorem fderiv_of_eventually_zero (φ : P → F) (p : P) (h : φ =ᶠ[𝓝 p] 0) :
    fderiv ℝ φ p = 0 := by
  rw [h.fderiv_eq]; simp

end SecondDerivative

/-! ## Reduced coordinates and the slope polynomial -/

section Slope

variable {R Y Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- The reduced chart `Ξ(r, y) = 𝖤 r + J_g γ(r, y) + J_H y`
(`eq:supp-exact-Xi-reduced`). -/
def reducedChart (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V) (γ : R × Y → Zg)
    (q : R × Y) : V :=
  E q.1 + Jg (γ q) + JH q.2

/-- The reduced regular drift `𝓕(r, y) = L_X f(Ξ(r, y))`
(`eq:supp-exact-reduced-functions`). -/
def reducedDrift (LX : Xs →L[ℝ] R) (f : V → Xs) (Ξ : R × Y → V) (q : R × Y) : R :=
  LX (f (Ξ q))

/-- The reduced harmonic constraint `𝓗(r, y) = 𝔠_H(Ξ(r, y))`
(`eq:supp-exact-reduced-functions`). -/
def reducedHarmonic (cH : V → Ho) (Ξ : R × Y → V) (q : R × Y) : Ho := cH (Ξ q)

/-- The slope polynomial
`𝒬(c) = 𝓗_r 𝓕_r v + 𝓗_rr[v, v] + 2 𝓗_ry[v, c] + 𝓗_yy[c, c]`
(`eq:supp-exact-slope-polynomial`), with partial derivatives at `(0, 0)` read off the
full derivatives along `(v, 0)` and `(0, c)`. -/
noncomputable def slopePolynomial (Fr : R × Y → R) (H : R × Y → Ho) (v : R) (c : Y) : Ho :=
  fderiv ℝ H 0 (fderiv ℝ Fr 0 (v, 0), 0) + sndDeriv H 0 (v, 0) (v, 0)
    + (2 : ℝ) • sndDeriv H 0 (v, 0) (0, c) + sndDeriv H 0 (0, c) (0, c)

/-- `Ê = 𝖤 - J_g 𝒜_g⁻¹ D𝔠_g(0) 𝖤` (`eq:supp-exact-original-slope-directions`), with
`Dcg = D𝔠_g(0)` and `AgInv = 𝒜_g⁻¹`. -/
def hatE (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (AgInv : Zg →L[ℝ] Zg) (Dcg : V →L[ℝ] Zg) :
    R →L[ℝ] V :=
  E - Jg.comp (AgInv.comp (Dcg.comp E))

/-- `b_* = Ê v`. -/
def slopeBase (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (AgInv : Zg →L[ℝ] Zg) (Dcg : V →L[ℝ] Zg)
    (v : R) : V :=
  hatE E Jg AgInv Dcg v

/-- `b(c) = b_* + J_H c`. -/
def slopeDirection (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V) (AgInv : Zg →L[ℝ] Zg)
    (Dcg : V →L[ℝ] Zg) (v : R) (c : Y) : V :=
  slopeBase E Jg AgInv Dcg v + JH c

/-- `a_* = Ê L_X Df(0) b_*`, with `Df = Df(0)`. -/
def slopeAccel (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (AgInv : Zg →L[ℝ] Zg) (Dcg : V →L[ℝ] Zg)
    (LX : Xs →L[ℝ] R) (Df : V →L[ℝ] Xs) (v : R) : V :=
  hatE E Jg AgInv Dcg (LX (Df (slopeBase E Jg AgInv Dcg v)))

/-- `𝔤₂(u, w) = D²𝔠_g(0)[u, w]` (`eq:supp-exact-g2`). -/
noncomputable def gTwo (cg : V → Zg) (u w : V) : Zg := sndDeriv cg 0 u w

/-- `𝒞 = 𝒞_g 𝒜_g⁻¹` (`eq:supp-exact-R-two-row`). -/
def scriptC (Cg : Zg →L[ℝ] Ho) (AgInv : Zg →L[ℝ] Zg) : Zg →L[ℝ] Ho := Cg.comp AgInv

/-- `ℛ(c) = 2 𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)` (`eq:supp-exact-R-two-row`). -/
noncomputable def scriptR (cg : V → Zg) (JH : Y →L[ℝ] V) (bstar : V) (c : Y) : Zg :=
  (2 : ℝ) • gTwo cg bstar (JH c) + gTwo cg (JH c) (JH c)

end Slope

end ExactSlowBranch
end RenewalGeometry
