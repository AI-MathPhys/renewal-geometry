/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.LeadingRayExact

/-!
# Reference-compatible origin and Gaussian marginal block

Exact formalization for `thm:SM-reference-origin-marginal-block` (RG.4–RG.7).

* **RG.4** (`shellAction_zero`, `reduced_shell_zero`): on a finite fine space with a strictly
  positive reference law `ρ_Y` and pushed-forward coarse reference `ρ_X = π_*ρ_Y`, the exact
  shell action `e^{-S_eff(x)} = E_{ρ_Y}[e^{-S_Y} ∣ π = x]` of the zero fine-action packet is
  identically zero; composing with any zero-preserving coefficient normalization and invariant
  tail graph gives `Σ_red(0) = 0`.  A nonzero affine translation is therefore a reference,
  normalization, tail-origin, or action-bank defect.
* **RG.5** (`gradedScale`, `ker_one_sub_gradedScale`): at the Gaussian origin the engineering
  grading acts blockwise as `b^(4-Δ)` on the operator-dimension-`Δ` bank; for `1 < b` the
  kernel of `I - DΣ_red(0)` is exactly the dimension-four block `E₄`, a semisimple marginal
  block, and only the strictly irrelevant complement is linearly slaved
  (`gradedScale_slaved_complement`).
* **RG.6/RG.7** (`gaussian_trajectory_ray`): every differentiable Gaussian trajectory
  `x(s) = s•a + O(s²)` of the reduced marginal step `x⁺ = x + 𝒬(x,x) + O(‖x‖³)` under a gauge
  step `s⁺ = s + βs² + O(s³)` satisfies the ray equation `𝒬(a,a) = β_a • a` — instantiating
  the complete leading-ray equation (RG.3i) with `K₁ = 0`, `b = 0`.
* `gauge_scalar_insufficient`: a single scalar gauge read (such as the held-out value
  `29/132`) cannot select the complete ray: two non-proportional directions can satisfy the
  same ray equation with the same eigenvalue.
-/

open Filter Asymptotics
open scoped Topology

namespace NCG
namespace ReferenceOrigin

/-! ### RG.4: reference-compatible origin -/

section Shell

variable {ΩY ΩX : Type*} [Fintype ΩY] [DecidableEq ΩX]

/-- The pushed-forward coarse reference law `ρ_X = π_* ρ_Y`. -/
noncomputable def pushRef (π : ΩY → ΩX) (ρ : ΩY → ℝ) (x : ΩX) : ℝ :=
  ∑ y ∈ {y | π y = x}, ρ y

/-- The exact shell action `S_eff(x) = -log E_{ρ_Y}[e^{-S_Y} ∣ π = x]` of a fine action
packet `S` (RG.3), relative to the pushed-forward reference. -/
noncomputable def shellAction (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ) (x : ΩX) : ℝ :=
  -Real.log ((∑ y ∈ {y | π y = x}, ρ y * Real.exp (-S y)) / pushRef π ρ x)

theorem pushRef_pos (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y)
    (hπ : Function.Surjective π) (x : ΩX) : 0 < pushRef π ρ x := by
  obtain ⟨y0, hy0⟩ := hπ x
  refine Finset.sum_pos' (fun y _ => (hρ y).le) ⟨y0, ?_, hρ y0⟩
  simp [hy0]

/-- **RG.4, core**: the exact shell action of the zero fine-action packet vanishes: at zero
action the conditional weight is one, so the coarse action is zero relative to the
pushed-forward reference. -/
theorem shellAction_zero (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y)
    (hπ : Function.Surjective π) (x : ΩX) : shellAction π ρ 0 x = 0 := by
  have hpos := pushRef_pos π hρ hπ x
  have hnum : (∑ y ∈ {y | π y = x}, ρ y * Real.exp (-(0 : ΩY → ℝ) y)) = pushRef π ρ x := by
    unfold pushRef
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [shellAction, hnum, div_self hpos.ne', Real.log_one, neg_zero]

/-- **RG.4**: if the reference laws are compatible (`ρ_X = π_*ρ_Y`), the fine zero-action
packet obeys `S_Y(·;0) = 0`, and the coefficient normalization and invariant tail graph
preserve zero, then the reduced shell satisfies `Σ_red(0) = 0`.  A nonzero affine translation
is a reference, normalization, tail-origin, or action-bank defect rather than a free
selector. -/
theorem reduced_shell_zero {E B : Type*} [Zero E] [Zero B]
    (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y) (hπ : Function.Surjective π)
    (fineAction : B → ΩY → ℝ) (hfine : fineAction 0 = 0)
    (tailGraph : (ΩX → ℝ) → E) (htail : tailGraph 0 = 0)
    (normalize : E → E) (hnorm : normalize 0 = 0) :
    normalize (tailGraph (shellAction π ρ (fineAction 0))) = 0 := by
  rw [hfine, show shellAction π ρ 0 = 0 from funext (shellAction_zero π hρ hπ), htail, hnorm]

end Shell

/-! ### RG.5: the Gaussian marginal block -/

section Graded

variable {V : Fin 5 → Type*} [∀ Δ, AddCommGroup (V Δ)] [∀ Δ, Module ℝ (V Δ)]

/-- The engineering-grading Jacobian at the Gaussian origin: `DΣ_red(0) = ⊕_Δ b^(4-Δ) I`
blockwise on the operator-dimension decomposition of the renormalizable bank. -/
def gradedScale (b : ℝ) : (∀ Δ, V Δ) →ₗ[ℝ] ∀ Δ, V Δ where
  toFun x Δ := b ^ (4 - Δ.val) • x Δ
  map_add' x y := by funext Δ; simp [smul_add]
  map_smul' c x := by funext Δ; simp [smul_comm c]

@[simp] theorem gradedScale_apply (b : ℝ) (x : ∀ Δ, V Δ) (Δ : Fin 5) :
    gradedScale b x Δ = b ^ (4 - Δ.val) • x Δ := rfl

section GaussianJacobian

variable {W : Fin 5 → Type*}
  [∀ Δ, NormedAddCommGroup (W Δ)] [∀ Δ, NormedSpace ℝ (W Δ)]
  [∀ Δ, FiniteDimensional ℝ (W Δ)]

/-- The Gaussian reduced shell as a genuine continuous linear map.  Its
block on engineering dimension `Δ` is multiplication by `b^(4-Δ)`. -/
noncomputable def gaussianReducedShell (b : ℝ) :
    (∀ Δ, W Δ) →L[ℝ] ∀ Δ, W Δ :=
  ⟨gradedScale (V := W) b,
    (gradedScale (V := W) b).continuous_of_finiteDimensional⟩

@[simp] theorem gaussianReducedShell_apply (b : ℝ) (x : ∀ Δ, W Δ)
    (Δ : Fin 5) :
    gaussianReducedShell (W := W) b x Δ = b ^ (4 - Δ.val) • x Δ :=
  rfl

/-- **RG.5, Jacobian identification.**  Once the manuscript's Gaussian
engineering scaling law is stated as the reduced shell itself, its Fréchet
derivative is exactly the block-diagonal engineering grading at every point,
in particular at the Gaussian origin. -/
theorem gaussianReducedShell_hasFDerivAt (b : ℝ) (x : ∀ Δ, W Δ) :
    HasFDerivAt (gaussianReducedShell (W := W) b)
      (gaussianReducedShell (W := W) b) x :=
  (gaussianReducedShell (W := W) b).hasFDerivAt

theorem fderiv_gaussianReducedShell (b : ℝ) (x : ∀ Δ, W Δ) :
    fderiv ℝ (gaussianReducedShell (W := W) b) x =
      gaussianReducedShell (W := W) b :=
  (gaussianReducedShell_hasFDerivAt (W := W) b x).fderiv

end GaussianJacobian

/-- The dimension-four marginal block `E₄` inside the graded coefficient bank. -/
def dimFourBlock : Submodule ℝ (∀ Δ, V Δ) where
  carrier := {x | ∀ Δ : Fin 5, Δ ≠ 4 → x Δ = 0}
  add_mem' hx hy Δ hΔ := by simp [hx Δ hΔ, hy Δ hΔ]
  zero_mem' Δ _ := rfl
  smul_mem' c x hx Δ hΔ := by simp [hx Δ hΔ]

theorem mem_dimFourBlock {x : ∀ Δ, V Δ} :
    x ∈ dimFourBlock (V := V) ↔ ∀ Δ : Fin 5, Δ ≠ 4 → x Δ = 0 := Iff.rfl

/-- **RG.5**: for `1 < b` the kernel of `I - DΣ_red(0)` is exactly the complete
dimension-four coefficient bank: `ker (I - ⊕_Δ b^(4-Δ) I) = E₄`, a semisimple marginal
block. -/
theorem ker_one_sub_gradedScale {b : ℝ} (hb : 1 < b) :
    LinearMap.ker (LinearMap.id - gradedScale (V := V) b) = dimFourBlock := by
  ext x
  simp only [LinearMap.mem_ker, mem_dimFourBlock]
  constructor
  · intro hx Δ hΔ
    have h := congrFun hx Δ
    simp only [LinearMap.sub_apply, LinearMap.id_apply, gradedScale_apply,
      Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
    have hpow : b ^ (4 - Δ.val) ≠ 1 := by
      have hval : Δ.val ≠ 4 := fun hv => hΔ (Fin.ext (by omega))
      exact ne_of_gt (one_lt_pow₀ hb (by omega))
    have : (1 - b ^ (4 - Δ.val)) • x Δ = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    have hcoeff : (1 : ℝ) - b ^ (4 - Δ.val) ≠ 0 := sub_ne_zero.mpr (Ne.symm hpow)
    exact (smul_eq_zero.mp this).resolve_left hcoeff
  · intro hx
    funext Δ
    by_cases hΔ : Δ = 4
    · subst hΔ
      simp
    · simp [hx Δ hΔ]

/-- Only the strictly irrelevant complement can be linearly slaved: on every block with
`Δ ≠ 4` the map `I - DΣ_red(0)` acts as the invertible scalar `1 - b^(4-Δ)`, so the
complementary coordinate is uniquely solved (slaved), while on `E₄` the map vanishes. -/
theorem gradedScale_slaved_complement {b : ℝ} (hb : 1 < b) (Δ : Fin 5) (hΔ : Δ ≠ 4)
    (w : V Δ) : ∃! v : V Δ, v - b ^ (4 - Δ.val) • v = w := by
  have hval : Δ.val ≠ 4 := fun hv => hΔ (Fin.ext (by omega))
  have hne : 4 - Δ.val ≠ 0 := by omega
  have hcoeff : (1 : ℝ) - b ^ (4 - Δ.val) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_of_gt (one_lt_pow₀ hb hne)))
  refine ⟨(1 - b ^ (4 - Δ.val))⁻¹ • w, ?_, ?_⟩
  · change (1 - b ^ (4 - Δ.val))⁻¹ • w - b ^ (4 - Δ.val) • ((1 - b ^ (4 - Δ.val))⁻¹ • w) = w
    rw [show ∀ v : V Δ, v - b ^ (4 - Δ.val) • v = (1 - b ^ (4 - Δ.val)) • v from
      fun v => by rw [sub_smul, one_smul], smul_smul, mul_inv_cancel₀ hcoeff, one_smul]
  · intro v hv
    have : (1 - b ^ (4 - Δ.val)) • v = w := by
      rw [sub_smul, one_smul]; exact hv
    rw [← this, smul_smul, inv_mul_cancel₀ hcoeff, one_smul]

end Graded

/-! ### RG.6/RG.7: the Gaussian trajectory ray equation -/

section Ray

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **RG.7**: every differentiable Gaussian trajectory `x(s) = s•a + O(s²)` of the reduced
marginal step `x⁺ = x + 𝒬(x,x) + O(‖x‖³)` (RG.6), driven by a gauge step
`s⁺ = s + βs² + O(s³)`, must solve the ray equation `𝒬(a,a) = β_a • a`.  This is the
complete leading equation (RG.3i) with `K₁ = 0` and `b = 0`. -/
theorem gaussian_trajectory_ray (Q : E →L[ℝ] E →L[ℝ] E) (z : ℝ → E) (γ : ℝ → ℝ)
    (a z₂ : E) (β : ℝ)
    (hz : (fun s => z s - s • a - s ^ 2 • z₂) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hγ : (fun s => γ s - s - β * s ^ 2) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hrec : (fun s => z (γ s) - (z s + Q (z s) (z s))) =o[𝓝 0] fun s : ℝ => s ^ 2) :
    Q a a = β • a := by
  have hrec' : (fun s => z (γ s) - (z s + s ^ 2 • (0 : E) + Q (z s) (z s)
      - s • (0 : E →L[ℝ] E) (z s))) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine hrec.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards with s
    simp
  have h := LeadingRay.leading_ray_eq Q 0 z γ a z₂ 0 β hz hγ hrec'
  simp only [zero_apply, sub_zero, zero_add] at h
  exact sub_eq_zero.mp h

/-- A single scalar gauge read cannot select the complete ray: on the two-dimensional
coefficient bank the coordinatewise quadratic shell admits two non-proportional Gaussian
ray directions with the same eigenvalue `β = 1`, hence the same scalar gauge comparison. -/
theorem gauge_scalar_insufficient :
    ∃ (Q : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (a₁ a₂ : Fin 2 → ℝ) (β : ℝ),
      (∀ x u v, Q (x + u) v = Q x v + Q u v ∧ Q v (x + u) = Q v x + Q v u) ∧
      (∀ (c : ℝ) x v, Q (c • x) v = c • Q x v ∧ Q v (c • x) = c • Q v x) ∧
      Q a₁ a₁ = β • a₁ ∧ Q a₂ a₂ = β • a₂ ∧ ∀ c : ℝ, a₂ ≠ c • a₁ := by
  refine ⟨fun x y i => x i * y i, ![1, 0], ![0, 1], 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x u v
    constructor <;> (funext i; simp only [Pi.add_apply]; ring)
  · intro c x v
    constructor <;> (funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring)
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp
  · intro c hc
    have h1 := congrFun hc 1
    simp at h1

end Ray

/-- **Bundle for `thm:SM-reference-origin-marginal-block`**: RG.4 (reference-compatible
origin), RG.5 (Gaussian marginal block and slaved complement), and RG.7 (Gaussian
trajectory ray equation). -/
theorem sm_reference_origin_marginal_block
    {ΩY ΩX : Type*} [Fintype ΩY] [DecidableEq ΩX]
    {E B : Type*} [Zero E] [Zero B]
    (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y) (hπ : Function.Surjective π)
    (fineAction : B → ΩY → ℝ) (hfine : fineAction 0 = 0)
    (tailGraph : (ΩX → ℝ) → E) (htail : tailGraph 0 = 0)
    (normalize : E → E) (hnorm : normalize 0 = 0)
    {V : Fin 5 → Type*} [∀ Δ, AddCommGroup (V Δ)] [∀ Δ, Module ℝ (V Δ)]
    {b : ℝ} (hb : 1 < b)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : F →L[ℝ] F →L[ℝ] F) (z : ℝ → F) (γ : ℝ → ℝ) (a z₂ : F) (β : ℝ)
    (hz : (fun s => z s - s • a - s ^ 2 • z₂) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hγ : (fun s => γ s - s - β * s ^ 2) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hrec : (fun s => z (γ s) - (z s + Q (z s) (z s))) =o[𝓝 0] fun s : ℝ => s ^ 2) :
    normalize (tailGraph (shellAction π ρ (fineAction 0))) = 0 ∧
    LinearMap.ker (LinearMap.id - gradedScale (V := V) b) = dimFourBlock ∧
    Q a a = β • a :=
  ⟨reduced_shell_zero π hρ hπ fineAction hfine tailGraph htail normalize hnorm,
   ker_one_sub_gradedScale hb,
   gaussian_trajectory_ray Q z γ a z₂ β hz hγ hrec⟩

end ReferenceOrigin
end NCG
