/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The initial acceleration-defect identity of the slow source system
  (`thm:supp-exact-initial-gate`, `cor:supp-exact-initial-repair`,
  `eq:supp-exact-initial-jets-corrected`, `eq:supp-exact-initial-xprime`,
  `eq:supp-L0-definition`, `eq:supp-f0-definition`, `eq:supp-exact-initial-H-automatic`,
  `eq:supp-exact-initial-acceleration-defect`, `eq:supp-exact-initial-pole-identity`,
  `eq:supp-exact-initial-differentiated-pole`; emergent-spacetime manuscript)

The slow system in source form (`eq:supp-exact-source-x`, `eq:supp-exact-source-z`) is
`x_τ = f(ξ) + a s(a, ξ, u)`, `z_τ = a⁻² Φ₀(ξ) + a⁻¹ g(ξ) + h(a, ξ, u)`, `ξ = (x, z)`,
`Φ₀(x, z) = C_red x + B z`, with the projections `p_g`, `p_H` of the weak decomposition
annihilating `Ran B` and `p_H C_red = 0` (`eq:supp-exact-weak-decomposition`).  In the
manuscript `f = b_s + Σ₀`, `g = Φ₁` (so `g(0) = 0`, `ExactSlowExpansion.phi1_zero`) and
`h = b_w + Φ̂₂`; here `f, g, s, h` are arbitrary maps with the regularity used by the proof.

An exact family is indexed by the amplitude `a ↓ 0` (filter `𝓝[>] 0`); its histories
`x_a, z_a, u_a` are defined for `τ ≥ 0` and differentiated within `[0, ∞)` at the initial cut.

* `tendsto_inv_smul_sub_of_differentiableAt` (general): if `φ` is differentiable at `0` and
  `ξ_a = aκ + O(a²)`, then `a⁻¹(φ(ξ_a) - φ(0)) → Dφ(0)κ`.
* **`initial_gate_rows`** (first part of `thm:supp-exact-initial-gate`): under the jets
  `eq:supp-exact-initial-jets-corrected`, `Φ₀κ = 0` (`κ ∈ 𝒦₀`), `f(0) = b_s`, and the
  harmonic rows are automatic: `(𝓛₀κ + f₀)_H = 0` (`eq:supp-exact-initial-H-automatic`).
* **`initial_gate_defect`** (second part): if the histories are twice, and the composed source
  `h(a, ξ_a, u_a)` once, differentiable at the initial cut, then
  `a p_g{z_{a,ττ}(0) - d/dτ h(a, ξ_a, u_a)|₀} → (𝓛₀κ + f₀)_g
     = p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b}` (`eq:supp-exact-initial-acceleration-defect`),
  via the exact pole identity and its derivative (`eq:supp-exact-initial-differentiated-pole`).
* **`initial_gate`**: both parts together with the final clause: the complete five-row
  equation `𝓛₀κ = -f₀` holds iff the two-row acceleration defect tends to zero.
* **`initial_repair`**, **`initial_repair_of_bounded`** (`cor:supp-exact-initial-repair`):
  if the projected difference is `o(a⁻¹)` then `𝓛₀κ = -f₀`; uniform bounds for
  `z_{a,ττ}(0)` and the source derivative suffice.
* Non-vacuity: `initial_gate_nonvacuous` instantiates the whole hypothesis packet on an
  explicit linear family (`x_a(τ) = aτ`, `z_a ≡ 0` in `ℝ × ℝ`), with nonzero acceleration data.
-/

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace ExactInitialGate

section General

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- If `ξ_a - aκ = O(a²)` along `𝓝[>] 0`, then `a⁻¹ ξ_a → κ`. -/
theorem tendsto_inv_smul_of_isBigO {ξ : ℝ → E} {κ : E}
    (hξ : (fun a => ξ a - a • κ) =O[𝓝[>] 0] fun a => a ^ 2) :
    Tendsto (fun a => a⁻¹ • ξ a) (𝓝[>] 0) (𝓝 κ) := by
  have h1 : (fun a => a⁻¹ • (ξ a - a • κ)) =O[𝓝[>] 0] fun a => a⁻¹ * a ^ 2 := by
    have : (fun a : ℝ => a⁻¹) =O[𝓝[>] 0] (fun a : ℝ => a⁻¹) := isBigO_refl _ _
    exact this.smul hξ
  have h2 : (fun a : ℝ => a⁻¹ * a ^ 2) =ᶠ[𝓝[>] 0] fun a => a := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have : a ≠ 0 := ne_of_gt ha
    field_simp
  have h3 : Tendsto (fun a => a⁻¹ • (ξ a - a • κ)) (𝓝[>] 0) (𝓝 0) := by
    refine (h1.trans_eventuallyEq h2).trans_tendsto ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
  have h4 : ∀ᶠ a in 𝓝[>] (0 : ℝ), a⁻¹ • ξ a = a⁻¹ • (ξ a - a • κ) + κ := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have : a ≠ 0 := ne_of_gt ha
    rw [smul_sub, smul_smul, inv_mul_cancel₀ this, one_smul, sub_add_cancel]
  have := h3.add_const κ
  rw [zero_add] at this
  exact this.congr' (h4.mono fun a ha => ha.symm)

/-- If `ξ_a - aκ = O(a²)` along `𝓝[>] 0`, then `ξ_a = O(a)`. -/
theorem isBigO_self_of_isBigO {ξ : ℝ → E} {κ : E}
    (hξ : (fun a => ξ a - a • κ) =O[𝓝[>] 0] fun a => a ^ 2) :
    ξ =O[𝓝[>] 0] fun a => a := by
  have h1 : (fun a : ℝ => a ^ 2) =O[𝓝[>] 0] fun a => a := by
    have : (fun a : ℝ => a ^ 2) = fun a => a * a := by ext a; ring
    rw [this]
    have hb : (fun a : ℝ => a) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)).isBigO_one ℝ
    simpa using (isBigO_refl (fun a : ℝ => a) (𝓝[>] 0)).mul hb
  have h2 : (fun a : ℝ => a • κ) =O[𝓝[>] 0] fun a => a :=
    isBigO_of_le' _ fun a => by rw [norm_smul, mul_comm]
  have h3 := (hξ.trans h1).add h2
  simpa using h3

/-- If `ξ_a - aκ = O(a²)` along `𝓝[>] 0`, then `ξ_a → 0`. -/
theorem tendsto_zero_of_isBigO {ξ : ℝ → E} {κ : E}
    (hξ : (fun a => ξ a - a • κ) =O[𝓝[>] 0] fun a => a ^ 2) :
    Tendsto ξ (𝓝[>] 0) (𝓝 0) :=
  (isBigO_self_of_isBigO hξ).trans_tendsto
    (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl))

/-- **First-order difference quotient along a jet.**  If `φ` is differentiable at `0` and
`ξ_a = aκ + O(a²)` along `𝓝[>] 0`, then `a⁻¹(φ(ξ_a) - φ(0)) → Dφ(0)κ`. -/
theorem tendsto_inv_smul_sub_of_differentiableAt {φ : E → G} (hφ : DifferentiableAt ℝ φ 0)
    {ξ : ℝ → E} {κ : E} (hξ : (fun a => ξ a - a • κ) =O[𝓝[>] 0] fun a => a ^ 2) :
    Tendsto (fun a => a⁻¹ • (φ (ξ a) - φ 0)) (𝓝[>] 0) (𝓝 (fderiv ℝ φ 0 κ)) := by
  set L := fderiv ℝ φ 0
  -- remainder `r(y) = φ y - φ 0 - L y = o(y)`
  have hr : (fun y => φ y - φ 0 - L y) =o[𝓝 0] fun y => y := by
    have := hφ.hasFDerivAt.isLittleO
    simpa using this
  have hξ0 := tendsto_zero_of_isBigO hξ
  have hr' : (fun a => φ (ξ a) - φ 0 - L (ξ a)) =o[𝓝[>] 0] fun a => a :=
    (hr.comp_tendsto hξ0).trans_isBigO (isBigO_self_of_isBigO hξ)
  have hr'' : Tendsto (fun a => a⁻¹ • (φ (ξ a) - φ 0 - L (ξ a))) (𝓝[>] 0) (𝓝 0) := by
    have := hr'.tendsto_inv_smul_nhds_zero
    simpa using this
  have hL : Tendsto (fun a => L (a⁻¹ • ξ a)) (𝓝[>] 0) (𝓝 (L κ)) :=
    (L.continuous.tendsto κ).comp (tendsto_inv_smul_of_isBigO hξ)
  have := hr''.add hL
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun a => ?_)
  simp only [map_smul, ← smul_add]
  congr 1
  abel

end General

/-! ### The slow source system and the initial gate -/

section Gate

variable {Xs W U Zg Ho : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- The leading slow constraint `Φ₀(x, z) = C_red x + B z`. -/
def phi0 (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) : Xs × W →L[ℝ] W :=
  Cred.comp (ContinuousLinearMap.fst ℝ Xs W) + B.comp (ContinuousLinearMap.snd ℝ Xs W)

theorem phi0_apply (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (ξ : Xs × W) :
    phi0 Cred B ξ = Cred ξ.1 + B ξ.2 := rfl

/-- The right-hand side of the singular slow equation
`z_τ = a⁻² Φ₀(ξ) + a⁻¹ g(ξ) + h(a, ξ, u)` (`eq:supp-exact-source-z`). -/
def zField (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (g : Xs × W → W)
    (h : ℝ × (Xs × W) × U → W) (a : ℝ) (ξ : Xs × W) (u : U) : W :=
  (a ^ 2)⁻¹ • phi0 Cred B ξ + a⁻¹ • g ξ + h (a, ξ, u)

/-- The regular slow equation `x_τ = f(ξ) + a s(a, ξ, u)` (`eq:supp-exact-source-x`). -/
def xField (f : Xs × W → Xs) (s : ℝ × (Xs × W) × U → Xs) (a : ℝ) (ξ : Xs × W) (u : U) : Xs :=
  f ξ + a • s (a, ξ, u)

/-- `𝓛₀κ = (p_g C_red Df(0)κ, p_H Dg(0)κ)` (`eq:supp-L0-definition`). -/
def calL0 (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Ho) (Cred : Xs →L[ℝ] W) (Df0 : Xs × W →L[ℝ] Xs)
    (Dg0 : Xs × W →L[ℝ] W) (κ : Xs × W) : Zg × Ho :=
  (pg (Cred (Df0 κ)), pH (Dg0 κ))

/-- `f₀ = (p_g{C_red s₀ + Dg(0)b}, p_H(h₀ - b_w))` (`eq:supp-f0-definition`). -/
def calF0 (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Ho) (Cred : Xs →L[ℝ] W) (Dg0 : Xs × W →L[ℝ] W)
    (s0 : Xs) (h0 : W) (b : Xs × W) : Zg × Ho :=
  (pg (Cred s0 + Dg0 b), pH (h0 - b.2))

/-- **First part of `thm:supp-exact-initial-gate`.**  Let an exact family `a ↦ (x_a, z_a, u_a)`
(`a ↓ 0`) satisfy the slow source system at the initial cut, with initial derivatives
`ẋ_a, ż_a` (within `[0, ∞)`), and the jets `eq:supp-exact-initial-jets-corrected`:
`ξ_a(0) = aκ + O(a²)`, `∂_τξ_a(0) → b = (b_s, b_w)`, `u_a(0) → u₀`, `p_g C_red b_s = 0`.
Assume `f` differentiable at `0`, `g` differentiable at `0` with `g(0) = 0` (`g = Φ₁`), and
`s`, `h` continuous at `(0, 0, u₀)`.  Then `Φ₀κ = 0` (`κ ∈ 𝒦₀`), `f(0) = b_s`, the regular
initial rate has the expansion `eq:supp-exact-initial-xprime`
(`a⁻¹(∂_τx_a(0) - b_s) → Df(0)κ + s₀`), and the harmonic rows are automatic:
`(𝓛₀κ + f₀)_H = 0` (`eq:supp-exact-initial-H-automatic`). -/
theorem initial_gate_rows (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0)
    (f : Xs × W → Xs) (g : Xs × W → W) (s : ℝ × (Xs × W) × U → Xs)
    (h : ℝ × (Xs × W) × U → W)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0) (hg0 : g 0 = 0)
    {u0 : U} (hs : ContinuousAt s (0, 0, u0)) (hh : ContinuousAt h (0, 0, u0))
    (x : ℝ → ℝ → Xs) (z : ℝ → ℝ → W) (u : ℝ → ℝ → U) (xd : ℝ → Xs) (zd : ℝ → W)
    (hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0)
    (hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0)
    (hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0))
    (hzeq : ∀ᶠ a in 𝓝[>] 0, zd a = zField Cred B g h a (x a 0, z a 0) (u a 0))
    {κ : Xs × W} {bs : Xs} {bw : W}
    (hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2)
    (hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw)))
    (hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0)) :
    phi0 Cred B κ = 0 ∧ f 0 = bs ∧
      Tendsto (fun a => a⁻¹ • (xd a - bs)) (𝓝[>] 0) (𝓝 (fderiv ℝ f 0 κ + s (0, 0, u0))) ∧
      (calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ +
        calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw)).2 = 0 := by
  set ξ : ℝ → Xs × W := fun a => (x a 0, z a 0)
  have hξ0 : Tendsto ξ (𝓝[>] 0) (𝓝 0) := tendsto_zero_of_isBigO hκ
  have ha0 : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)
  have htrip : Tendsto (fun a => (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 ((0 : ℝ), (0 : Xs × W), u0)) :=
    ha0.prodMk_nhds (hξ0.prodMk_nhds hu)
  have hsl : Tendsto (fun a => s (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 (s (0, 0, u0))) :=
    hs.tendsto.comp htrip
  have hhl : Tendsto (fun a => h (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 (h (0, 0, u0))) :=
    hh.tendsto.comp htrip
  have hxdl : Tendsto xd (𝓝[>] 0) (𝓝 bs) := (continuous_fst.tendsto _).comp hb
  have hzdl : Tendsto zd (𝓝[>] 0) (𝓝 bw) := (continuous_snd.tendsto _).comp hb
  -- `f(0) = b_s`
  have hfl : Tendsto (fun a => f (ξ a) + a • s (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 (f 0)) := by
    have h1 : Tendsto (fun a => f (ξ a)) (𝓝[>] 0) (𝓝 (f 0)) :=
      hf.continuousAt.tendsto.comp hξ0
    have h2 : Tendsto (fun a => a • s (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ha0.smul hsl
    simpa using h1.add h2
  have hf0 : f 0 = bs := by
    refine tendsto_nhds_unique (hfl.congr' ?_) hxdl
    filter_upwards [hxeq] with a ha
    rw [ha]; rfl
  -- the expansion of the regular initial rate
  have hxp : Tendsto (fun a => a⁻¹ • (xd a - bs)) (𝓝[>] 0) (𝓝 (fderiv ℝ f 0 κ + s (0, 0, u0))) := by
    have h1 := tendsto_inv_smul_sub_of_differentiableAt hf hκ
    refine (h1.add hsl).congr' ?_
    filter_upwards [hxeq, self_mem_nhdsWithin] with a ha hpos
    have hne : a ≠ 0 := ne_of_gt hpos
    rw [ha, ← hf0]
    simp only [xField, ξ]
    rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
  -- `Φ₀κ = 0`: multiply the singular equation by `a`
  have hphi : phi0 Cred B κ = 0 := by
    have hl : Tendsto (fun a => a • zd a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ha0.smul hzdl
    have hr : Tendsto (fun a => phi0 Cred B (a⁻¹ • ξ a) + g (ξ a) + a • h (a, ξ a, u a 0))
        (𝓝[>] 0) (𝓝 (phi0 Cred B κ)) := by
      have h1 : Tendsto (fun a => phi0 Cred B (a⁻¹ • ξ a)) (𝓝[>] 0) (𝓝 (phi0 Cred B κ)) :=
        ((phi0 Cred B).continuous.tendsto κ).comp (tendsto_inv_smul_of_isBigO hκ)
      have h2 : Tendsto (fun a => g (ξ a)) (𝓝[>] 0) (𝓝 0) := by
        have := hg.continuousAt.tendsto.comp hξ0
        rw [hg0] at this
        exact this
      have h3 : Tendsto (fun a => a • h (a, ξ a, u a 0)) (𝓝[>] 0) (𝓝 0) := by
        simpa using ha0.smul hhl
      simpa using (h1.add h2).add h3
    refine tendsto_nhds_unique (hr.congr' ?_) hl
    filter_upwards [hzeq, self_mem_nhdsWithin] with a ha hpos
    have hne : a ≠ 0 := ne_of_gt hpos
    rw [ha]
    simp only [zField, smul_add, smul_smul, map_smul, ξ]
    congr 2
    · congr 1; field_simp
    · rw [mul_inv_cancel₀ hne, one_smul]
  -- the harmonic rows
  have hH : pH bw = pH (fderiv ℝ g 0 κ) + pH (h (0, 0, u0)) := by
    have hl : Tendsto (fun a => pH (zd a)) (𝓝[>] 0) (𝓝 (pH bw)) :=
      (pH.continuous.tendsto bw).comp hzdl
    have hr : Tendsto (fun a => pH (a⁻¹ • (g (ξ a) - g 0)) + pH (h (a, ξ a, u a 0))) (𝓝[>] 0)
        (𝓝 (pH (fderiv ℝ g 0 κ) + pH (h (0, 0, u0)))) :=
      (((pH.continuous.tendsto _).comp (tendsto_inv_smul_sub_of_differentiableAt hg hκ))).add
        ((pH.continuous.tendsto _).comp hhl)
    refine tendsto_nhds_unique hl (hr.congr' ?_)
    filter_upwards [hzeq] with a ha
    rw [ha]
    simp only [zField, map_add, map_smul, hg0, sub_zero]
    have h1 : pH (phi0 Cred B (ξ a)) = 0 := by
      simp only [phi0_apply, map_add]
      rw [← ContinuousLinearMap.comp_apply, hpHC, ← ContinuousLinearMap.comp_apply, hpHB]
      simp
    rw [h1, smul_zero, zero_add]
  refine ⟨hphi, hf0, hxp, ?_⟩
  simp only [calL0, calF0, Prod.snd_add, map_sub, hH]
  abel

/-- The exact pole identity `Φ₀ξ + a g(ξ) = a²{z_τ - h(a, ξ, u)}`
(`eq:supp-exact-initial-pole-identity`): pointwise algebra of the singular equation. -/
theorem pole_identity (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (g : Xs × W → W)
    (h : ℝ × (Xs × W) × U → W) {a : ℝ} (ha : a ≠ 0) (ξ : Xs × W) (u : U) :
    phi0 Cred B ξ + a • g ξ = (a ^ 2) • (zField Cred B g h a ξ u - h (a, ξ, u)) := by
  simp only [zField, add_sub_cancel_right, smul_add, smul_smul]
  have h1 : a ^ 2 * (a ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 ha)
  have h2 : a ^ 2 * a⁻¹ = a := by field_simp
  rw [h1, h2, one_smul]

/-- **Second part of `thm:supp-exact-initial-gate`** (`eq:supp-exact-initial-acceleration-defect`).
In addition to the hypotheses of `initial_gate_rows`, let the singular equation hold on an
initial interval `[0, τ_a)` (as one-sided derivatives within `[0, ∞)`), let `g` be `C¹` near
`0`, and let the histories be twice (`∂_τ z_a` has derivative `z_{a,ττ}(0)` at the cut) and
the composed source `τ ↦ h(a, ξ_a(τ), u_a(τ))` once differentiable at the initial cut, with
derivative `ḣ_a`.  Then the projected acceleration defect converges:
`a p_g{z_{a,ττ}(0) - ḣ_a} → p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b} = (𝓛₀κ + f₀)_g`. -/
theorem initial_gate_defect (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (f : Xs × W → Xs) (g : Xs × W → W) (s : ℝ × (Xs × W) × U → Xs)
    (h : ℝ × (Xs × W) × U → W)
    (hf : DifferentiableAt ℝ f 0) (hg1 : ContDiffAt ℝ 1 g 0) (hg0 : g 0 = 0)
    {u0 : U} (hs : ContinuousAt s (0, 0, u0)) (hh : ContinuousAt h (0, 0, u0))
    (x : ℝ → ℝ → Xs) (z : ℝ → ℝ → W) (u : ℝ → ℝ → U) (xd : ℝ → Xs) (zd zdd hd : ℝ → W)
    (hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0)
    (hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0)
    (hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0))
    (hzsys : ∀ᶠ a in 𝓝[>] 0, ∀ᶠ τ in 𝓝[≥] 0,
      HasDerivWithinAt (z a) (zField Cred B g h a (x a τ, z a τ) (u a τ)) (Ici 0) τ)
    (hzdd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (derivWithin (z a) (Ici 0)) (zdd a) (Ici 0) 0)
    (hhd : ∀ᶠ a in 𝓝[>] 0,
      HasDerivWithinAt (fun τ => h (a, (x a τ, z a τ), u a τ)) (hd a) (Ici 0) 0)
    {κ : Xs × W} {bs : Xs} {bw : W}
    (hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2)
    (hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw)))
    (hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0))
    (hgate : pg (Cred bs) = 0) :
    Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0)
      (𝓝 (pg (Cred (fderiv ℝ f 0 κ) + Cred (s (0, 0, u0)) + fderiv ℝ g 0 (bs, bw)))) := by
  set ξ : ℝ → Xs × W := fun a => (x a 0, z a 0)
  -- the singular equation at the cut
  have hzeq : ∀ᶠ a in 𝓝[>] 0, zd a = zField Cred B g h a (ξ a) (u a 0) := by
    filter_upwards [hzd, hzsys] with a h1 h2
    exact ((uniqueDiffOn_Ici (0 : ℝ)) 0 self_mem_Ici).eq_deriv _ h1
      (h2.self_of_nhdsWithin self_mem_Ici)
  obtain ⟨-, hf0, hxp, -⟩ := initial_gate_rows Cred B pg pH hpHC hpHB f g s h hf
    (hg1.differentiableAt one_ne_zero) hg0 hs hh x z u xd zd hxd hzd hxeq hzeq hκ hb hu
  have hξ0 : Tendsto ξ (𝓝[>] 0) (𝓝 0) := tendsto_zero_of_isBigO hκ
  -- `g` is differentiable near `0`, and `Dg` is continuous at `0`
  have hgev : ∀ᶠ y in 𝓝 (0 : Xs × W), DifferentiableAt ℝ g y :=
    (hg1.eventually (by simp)).mono fun y hy => hy.differentiableAt one_ne_zero
  have hDgc : ContinuousAt (fderiv ℝ g) 0 :=
    (hg1.fderiv_right (m := 0) le_rfl).continuousAt
  -- the differentiated pole identity, eventually in `a`
  have hdiff : ∀ᶠ a in 𝓝[>] 0, phi0 Cred B (xd a, zd a) + a • fderiv ℝ g (ξ a) (xd a, zd a)
      = (a ^ 2) • (zdd a - hd a) := by
    filter_upwards [hxd, hzd, hzsys, hzdd, hhd, self_mem_nhdsWithin, hξ0.eventually hgev]
      with a hx hz hsys hdd hhd' hpos hgd
    have hne : a ≠ 0 := ne_of_gt hpos
    have hξd : HasDerivWithinAt (fun τ => (x a τ, z a τ)) (xd a, zd a) (Ici 0) 0 :=
      hx.prodMk hz
    -- left-hand side derivative
    have hL : HasDerivWithinAt (fun τ => phi0 Cred B (x a τ, z a τ) + a • g (x a τ, z a τ))
        (phi0 Cred B (xd a, zd a) + a • fderiv ℝ g (ξ a) (xd a, zd a)) (Ici 0) 0 := by
      have h1 := (phi0 Cred B).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hξd
      have h2 := hgd.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hξd
      exact h1.add (h2.const_smul a)
    -- right-hand side derivative
    have hR : HasDerivWithinAt
        (fun τ => (a ^ 2) • (derivWithin (z a) (Ici 0) τ - h (a, (x a τ, z a τ), u a τ)))
        ((a ^ 2) • (zdd a - hd a)) (Ici 0) 0 :=
      (hdd.sub hhd').const_smul (a ^ 2)
    -- the two functions agree on `[0, ∞)` near `0`
    have heq : (fun τ => phi0 Cred B (x a τ, z a τ) + a • g (x a τ, z a τ)) =ᶠ[𝓝[≥] 0]
        (fun τ => (a ^ 2) • (derivWithin (z a) (Ici 0) τ - h (a, (x a τ, z a τ), u a τ))) := by
      filter_upwards [hsys, self_mem_nhdsWithin] with τ hτ hτmem
      rw [hτ.derivWithin ((uniqueDiffOn_Ici 0) τ hτmem)]
      exact pole_identity Cred B g h hne _ _
    have hR' := hR.congr_of_eventuallyEq heq (by
      simpa using (heq.self_of_nhdsWithin self_mem_Ici))
    exact ((uniqueDiffOn_Ici (0 : ℝ)) 0 self_mem_Ici).eq_deriv _ hL hR'
  -- divide by `a` and pass to the limit
  have hlim1 : Tendsto (fun a => pg (Cred (a⁻¹ • (xd a - bs)))) (𝓝[>] 0)
      (𝓝 (pg (Cred (fderiv ℝ f 0 κ + s (0, 0, u0))))) :=
    ((pg.comp Cred).continuous.tendsto _).comp hxp
  have hlim2 : Tendsto (fun a => pg (fderiv ℝ g (ξ a) (xd a, zd a))) (𝓝[>] 0)
      (𝓝 (pg (fderiv ℝ g 0 (bs, bw)))) :=
    (pg.continuous.tendsto _).comp
      ((isBoundedBilinearMap_apply.continuous.tendsto _).comp
        ((hDgc.tendsto.comp hξ0).prodMk_nhds hb))
  have := hlim1.add hlim2
  rw [← map_add, map_add Cred] at this
  refine this.congr' ?_
  filter_upwards [hdiff, self_mem_nhdsWithin] with a hda hpos
  have hne : a ≠ 0 := ne_of_gt hpos
  have hpg := congrArg pg hda
  simp only [phi0_apply, map_add, map_smul] at hpg
  have hB : pg (B (zd a)) = 0 := by
    rw [← ContinuousLinearMap.comp_apply, hpgB]; rfl
  rw [hB, add_zero] at hpg
  -- `a • pg(zdd - hd) = a⁻¹ • pg(Cred xd) + pg(Dg ξ̇)`
  have key : a • pg (zdd a - hd a) = a⁻¹ • pg (Cred (xd a)) + pg (fderiv ℝ g (ξ a) (xd a, zd a)) := by
    have : (a ^ 2) • pg (zdd a - hd a) = a • (a • pg (zdd a - hd a)) := by
      rw [smul_smul, sq]
    rw [this] at hpg
    have hpg' := congrArg (fun v => a⁻¹ • v) hpg
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul] at hpg'
    have ha3 : a⁻¹ * (a * a) = a := by field_simp
    rw [ha3] at hpg'
    exact hpg'.symm
  rw [key, map_smul, map_smul, map_sub, map_sub, hgate, sub_zero]

/-- **`thm:supp-exact-initial-gate`** (complete statement).  Under the hypotheses of
`initial_gate_defect`: `κ ∈ 𝒦₀`, the harmonic rows `(𝓛₀κ + f₀)_H` vanish, the projected
acceleration defect `a p_g{z_{a,ττ}(0) - ḣ_a}` converges to `(𝓛₀κ + f₀)_g`, and consequently the
complete five-row equation `𝓛₀κ = -f₀` holds iff the two-row acceleration defect tends to `0`. -/
theorem initial_gate (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (f : Xs × W → Xs) (g : Xs × W → W) (s : ℝ × (Xs × W) × U → Xs)
    (h : ℝ × (Xs × W) × U → W)
    (hf : DifferentiableAt ℝ f 0) (hg1 : ContDiffAt ℝ 1 g 0) (hg0 : g 0 = 0)
    {u0 : U} (hs : ContinuousAt s (0, 0, u0)) (hh : ContinuousAt h (0, 0, u0))
    (x : ℝ → ℝ → Xs) (z : ℝ → ℝ → W) (u : ℝ → ℝ → U) (xd : ℝ → Xs) (zd zdd hd : ℝ → W)
    (hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0)
    (hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0)
    (hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0))
    (hzsys : ∀ᶠ a in 𝓝[>] 0, ∀ᶠ τ in 𝓝[≥] 0,
      HasDerivWithinAt (z a) (zField Cred B g h a (x a τ, z a τ) (u a τ)) (Ici 0) τ)
    (hzdd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (derivWithin (z a) (Ici 0)) (zdd a) (Ici 0) 0)
    (hhd : ∀ᶠ a in 𝓝[>] 0,
      HasDerivWithinAt (fun τ => h (a, (x a τ, z a τ), u a τ)) (hd a) (Ici 0) 0)
    {κ : Xs × W} {bs : Xs} {bw : W}
    (hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2)
    (hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw)))
    (hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0))
    (hgate : pg (Cred bs) = 0) :
    phi0 Cred B κ = 0 ∧
      (calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ +
        calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw)).2 = 0 ∧
      Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0)
        (𝓝 (calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ +
          calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw)).1) ∧
      (calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ =
          -calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw) ↔
        Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0) (𝓝 0)) := by
  have hzeq : ∀ᶠ a in 𝓝[>] 0, zd a = zField Cred B g h a (x a 0, z a 0) (u a 0) := by
    filter_upwards [hzd, hzsys] with a h1 h2
    exact ((uniqueDiffOn_Ici (0 : ℝ)) 0 self_mem_Ici).eq_deriv _ h1
      (h2.self_of_nhdsWithin self_mem_Ici)
  obtain ⟨hphi, -, -, hH⟩ := initial_gate_rows Cred B pg pH hpHC hpHB f g s h hf
    (hg1.differentiableAt one_ne_zero) hg0 hs hh x z u xd zd hxd hzd hxeq hzeq hκ hb hu
  have hdef := initial_gate_defect Cred B pg pH hpHC hpHB hpgB f g s h hf hg1 hg0 hs hh x z u
    xd zd zdd hd hxd hzd hxeq hzsys hzdd hhd hκ hb hu hgate
  set L := calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ
  set F := calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw)
  have hg : (L + F).1 = pg (Cred (fderiv ℝ f 0 κ) + Cred (s (0, 0, u0)) + fderiv ℝ g 0 (bs, bw)) := by
    simp only [L, F, calL0, calF0, Prod.fst_add, map_add]
    abel
  rw [← hg] at hdef
  refine ⟨hphi, hH, hdef, ?_⟩
  constructor
  · intro hLF
    have : L + F = 0 := by rw [hLF, neg_add_cancel]
    rw [this] at hdef
    simpa using hdef
  · intro h0
    have h1 : (L + F).1 = 0 := tendsto_nhds_unique hdef h0
    have : L + F = 0 := Prod.ext h1 hH
    exact eq_neg_of_add_eq_zero_left this

/-- **`cor:supp-exact-initial-repair`.**  If the projected difference
`p_g{z_{a,ττ}(0) - ḣ_a}` is `o(a⁻¹)` (i.e. `a p_g{...} → 0`), then `𝓛₀κ = -f₀`. -/
theorem initial_repair (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (f : Xs × W → Xs) (g : Xs × W → W) (s : ℝ × (Xs × W) × U → Xs)
    (h : ℝ × (Xs × W) × U → W)
    (hf : DifferentiableAt ℝ f 0) (hg1 : ContDiffAt ℝ 1 g 0) (hg0 : g 0 = 0)
    {u0 : U} (hs : ContinuousAt s (0, 0, u0)) (hh : ContinuousAt h (0, 0, u0))
    (x : ℝ → ℝ → Xs) (z : ℝ → ℝ → W) (u : ℝ → ℝ → U) (xd : ℝ → Xs) (zd zdd hd : ℝ → W)
    (hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0)
    (hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0)
    (hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0))
    (hzsys : ∀ᶠ a in 𝓝[>] 0, ∀ᶠ τ in 𝓝[≥] 0,
      HasDerivWithinAt (z a) (zField Cred B g h a (x a τ, z a τ) (u a τ)) (Ici 0) τ)
    (hzdd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (derivWithin (z a) (Ici 0)) (zdd a) (Ici 0) 0)
    (hhd : ∀ᶠ a in 𝓝[>] 0,
      HasDerivWithinAt (fun τ => h (a, (x a τ, z a τ), u a τ)) (hd a) (Ici 0) 0)
    {κ : Xs × W} {bs : Xs} {bw : W}
    (hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2)
    (hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw)))
    (hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0))
    (hgate : pg (Cred bs) = 0)
    (hsmall : (fun a => pg (zdd a - hd a)) =o[𝓝[>] 0] fun a => a⁻¹) :
    calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ =
      -calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw) := by
  refine (initial_gate Cred B pg pH hpHC hpHB hpgB f g s h hf hg1 hg0 hs hh x z u xd zd zdd hd
    hxd hzd hxeq hzsys hzdd hhd hκ hb hu hgate).2.2.2.2 ?_
  -- `a • o(a⁻¹) → 0`
  have h1 : (fun a => a • pg (zdd a - hd a)) =o[𝓝[>] 0] fun a => a * a⁻¹ :=
    (isBigO_refl (fun a : ℝ => a) _).smul_isLittleO hsmall
  have h2 : (fun a : ℝ => a * a⁻¹) =ᶠ[𝓝[>] 0] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact mul_inv_cancel₀ (ne_of_gt ha)
  exact (isLittleO_one_iff ℝ).mp (h1.trans_eventuallyEq h2)

/-- Second sentence of `cor:supp-exact-initial-repair`: uniform bounds for `z_{a,ττ}(0)` and for
the source derivative `ḣ_a` are sufficient. -/
theorem initial_repair_of_bounded (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (f : Xs × W → Xs) (g : Xs × W → W) (s : ℝ × (Xs × W) × U → Xs)
    (h : ℝ × (Xs × W) × U → W)
    (hf : DifferentiableAt ℝ f 0) (hg1 : ContDiffAt ℝ 1 g 0) (hg0 : g 0 = 0)
    {u0 : U} (hs : ContinuousAt s (0, 0, u0)) (hh : ContinuousAt h (0, 0, u0))
    (x : ℝ → ℝ → Xs) (z : ℝ → ℝ → W) (u : ℝ → ℝ → U) (xd : ℝ → Xs) (zd zdd hd : ℝ → W)
    (hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0)
    (hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0)
    (hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0))
    (hzsys : ∀ᶠ a in 𝓝[>] 0, ∀ᶠ τ in 𝓝[≥] 0,
      HasDerivWithinAt (z a) (zField Cred B g h a (x a τ, z a τ) (u a τ)) (Ici 0) τ)
    (hzdd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (derivWithin (z a) (Ici 0)) (zdd a) (Ici 0) 0)
    (hhd : ∀ᶠ a in 𝓝[>] 0,
      HasDerivWithinAt (fun τ => h (a, (x a τ, z a τ), u a τ)) (hd a) (Ici 0) 0)
    {κ : Xs × W} {bs : Xs} {bw : W}
    (hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2)
    (hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw)))
    (hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0))
    (hgate : pg (Cred bs) = 0)
    (hzbd : zdd =O[𝓝[>] 0] fun _ => (1 : ℝ)) (hhbd : hd =O[𝓝[>] 0] fun _ => (1 : ℝ)) :
    calL0 pg pH Cred (fderiv ℝ f 0) (fderiv ℝ g 0) κ =
      -calF0 pg pH Cred (fderiv ℝ g 0) (s (0, 0, u0)) (h (0, 0, u0)) (bs, bw) := by
  refine initial_repair Cred B pg pH hpHC hpHB hpgB f g s h hf hg1 hg0 hs hh x z u xd zd zdd hd
    hxd hzd hxeq hzsys hzdd hhd hκ hb hu hgate ?_
  have h1 : (fun a => pg (zdd a - hd a)) =O[𝓝[>] 0] fun _ => (1 : ℝ) :=
    (pg.isBigO_comp _ _).trans (hzbd.sub hhbd)
  refine h1.trans_isLittleO ?_
  -- `1 = o(a⁻¹)` as `a ↓ 0`
  refine isLittleO_iff.mpr fun c hc => ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c by positivity)] with a ha
  rw [norm_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha.1)]
  rw [le_mul_inv_iff₀ ha.1, one_mul]
  exact ha.2.le

/-! ### Non-vacuity -/

/-- Non-vacuity of the hypothesis packet of `initial_gate`, with a **nonzero** defect.  In
`ℝ × ℝ` take `C_red = p_g = id`, `B = 0`, `p_H = 0`, `f = g = h = 0`, `s ≡ 1`, and the exact
family `x_a(τ) = aτ`, `z_a(τ) = τ²/(2a)`, `u ≡ 0`: then `κ = 0`, `b = 0`, `z_{a,ττ}(0) = a⁻¹`,
and the two-row defect `a p_g z_{a,ττ}(0) ≡ 1 = p_g C_red s₀` does not vanish. -/
theorem initial_gate_nonvacuous :
    Tendsto (fun a : ℝ => a • (ContinuousLinearMap.id ℝ ℝ) (a⁻¹ - 0)) (𝓝[>] 0)
      (𝓝 (calL0 (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
          (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) 0 +
        calF0 (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
          (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) ((fun _ : ℝ × (ℝ × ℝ) × ℝ => (1 : ℝ)) (0, 0, 0))
          ((fun _ : ℝ × (ℝ × ℝ) × ℝ => (0 : ℝ)) (0, 0, 0)) (0, 0)).1) ∧
    calL0 (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
        (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) 0 ≠
      -calF0 (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
          (fderiv ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) 0) ((fun _ : ℝ × (ℝ × ℝ) × ℝ => (1 : ℝ)) (0, 0, 0))
          ((fun _ : ℝ × (ℝ × ℝ) × ℝ => (0 : ℝ)) (0, 0, 0)) (0, 0) := by
  set I := ContinuousLinearMap.id ℝ ℝ
  have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have key := initial_gate (U := ℝ) I (0 : ℝ →L[ℝ] ℝ) I (0 : ℝ →L[ℝ] ℝ) (by simp) (by simp)
    (by simp) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (differentiableAt_const _) contDiffAt_const rfl continuousAt_const continuousAt_const
    (fun a τ => a * τ) (fun a τ => τ ^ 2 / (2 * a)) (fun _ _ => 0) (fun a => a) (fun _ => 0)
    (fun a => a⁻¹) (fun _ => 0)
    (Eventually.of_forall fun a => by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).hasDerivWithinAt)
    (Eventually.of_forall fun a => by
      have := ((hasDerivAt_pow 2 (0 : ℝ)).div_const (2 * a)).hasDerivWithinAt (s := Ici 0)
      simpa using this)
    (Eventually.of_forall fun a => by simp [xField])
    (hpos.mono fun a ha => Eventually.of_forall fun τ => by
      have h1 := ((hasDerivAt_pow 2 τ).div_const (2 * a)).hasDerivWithinAt (s := Ici 0)
      convert h1 using 1
      simp only [zField, phi0_apply, I, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
        add_zero, smul_zero, smul_eq_mul]
      field_simp
      ring)
    (hpos.mono fun a ha => by
      have hd : ∀ τ ∈ Ici (0 : ℝ), derivWithin (fun τ => τ ^ 2 / (2 * a)) (Ici 0) τ = τ / a := by
        intro τ hτ
        rw [(((hasDerivAt_pow 2 τ).div_const (2 * a)).hasDerivWithinAt).derivWithin
          ((uniqueDiffOn_Ici 0) τ hτ)]
        field_simp
        ring
      have h1 : HasDerivWithinAt (fun τ : ℝ => τ / a) a⁻¹ (Ici 0) 0 := by
        simpa [div_eq_mul_inv] using ((hasDerivAt_id (0 : ℝ)).mul_const a⁻¹).hasDerivWithinAt
      exact h1.congr (fun τ hτ => hd τ hτ) (hd 0 self_mem_Ici))
    (Eventually.of_forall fun a => hasDerivWithinAt_const _ _ _)
    (κ := 0) (bs := 0) (bw := 0) (by simpa using isBigO_zero _ _)
    (by
      have : Tendsto (fun a : ℝ => ((a, (0 : ℝ)) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 (0, 0)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)).prodMk_nhds
          tendsto_const_nhds
      exact this)
    tendsto_const_nhds (by simp)
  refine ⟨key.2.2.1, fun hc => ?_⟩
  have h0 := key.2.2.2.mp hc
  have h1 : Tendsto (fun a : ℝ => a • I (a⁻¹ - 0)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with a ha
    simp [I, mul_inv_cancel₀ (ne_of_gt ha)]
  exact one_ne_zero (tendsto_nhds_unique h1 h0)

end Gate

end ExactInitialGate
end RenewalGeometry

end
