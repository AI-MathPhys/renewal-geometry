/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SchurBlockExact

/-!
# Nested Schur jets of a width family

Machinery for `thm:SM-localizer-jets` (RG.3g)–(RG.3h).  For a differentiable width family
`L : ℝ → M m n` with `L 0` supported on the hard block (`P L₀ = 0`, `L₀ P = 0`) and
`P + Q L₀ Q` a unit, the induced kernel localizer `𝒮(L s)` has

* first jet `𝒮'(0) = P L₁ P` (`hasDerivAt_schur_zero`), and
* second jet `𝒮''(0) = P L₂ P - 2 P L₁ Q [P + Q L₀ Q]⁻¹ Q L₁ P` (`hasDerivAt_schurDeriv_zero`),

where `L₁ = L'(0)`, `L₂ = L''(0)`.  The negative relaxation term is exactly the derivative of
the hard-range Schur term.  One-sided positivity: a real function vanishing at `0` and
nonnegative on `s > 0` has nonnegative first derivative at `0`, and nonnegative second
derivative when the first vanishes (`deriv_nonneg_of_nonneg_right`,
`deriv2_nonneg_of_nonneg_right`); applied to the quadratic forms of `𝒮(L s)` these give
`K₁ = P L₁ P ⪰ 0` and `K₂ ⪰ 0` on `ker K₁` (`quadForm_jet1_nonneg`, `quadForm_jet2_nonneg`).

Derivatives are taken with respect to the `L∞` operator-norm topology on matrices (which agrees
with the product topology).
-/

open Matrix Filter Set
open scoped Matrix.Norms.Operator Topology

namespace NCG
namespace SchurJets

open NCG.SchurBlock

attribute [local instance 2000] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Derivative of the hard-range inverse -/

/-- The formal derivative of `[P + Q L Q]⁻¹` along `L'`. -/
noncomputable def hardInvDeriv (L L' : M m n) : M m n :=
  -(hardInv L * (Q * L' * Q) * hardInv L)

theorem hasDerivAt_hardInv {L : ℝ → M m n} {L' : M m n} {s : ℝ} (hL : HasDerivAt L L' s)
    (hu : IsUnit (P + Q * L s * Q)) :
    HasDerivAt (fun t => hardInv (L t)) (hardInvDeriv (L s) L') s := by
  obtain ⟨u, hu⟩ := hu
  have hinner : HasDerivAt (fun t => P + Q * L t * Q) (Q * L' * Q) s := by
    have h1 := ((hasDerivAt_const s (Q : M m n)).mul hL).mul (hasDerivAt_const s (Q : M m n))
    have h2 := (hasDerivAt_const s (P : M m n)).add h1
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h2
    exact h2
  have hval : hardInv (L s) = (↑u⁻¹ : M m n) := by
    rw [hardInv, ← hu, Ring.inverse_unit]
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have h := hinv.comp_hasDerivAt s hinner
  simp only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at h
  unfold hardInvDeriv
  rw [hval]
  exact h

/-! ### First jet -/

section Jets

variable (L : ℝ → M m n) (L' : ℝ → M m n)

/-- The formal derivative of `𝒮(L s)`. -/
noncomputable def schurDeriv (s : ℝ) : M m n :=
  P * L' s * P
    - (P * L' s * Q * hardInv (L s) * Q * L s * P
      + P * L s * Q * hardInvDeriv (L s) (L' s) * Q * L s * P
      + P * L s * Q * hardInv (L s) * Q * L' s * P)

/-- `𝒮(L s)` is differentiable wherever the hard block is invertible, with derivative
`schurDeriv`. -/
theorem hasDerivAt_schur {s : ℝ} (hL : HasDerivAt L (L' s) s) (hu : IsUnit (P + Q * L s * Q)) :
    HasDerivAt (fun t => schur (L t)) (schurDeriv L L' s) s := by
  have hP := hasDerivAt_const s (P : M m n)
  have hQ := hasDerivAt_const s (Q : M m n)
  have hinv := hasDerivAt_hardInv hL hu
  have h1 := (hP.mul hL).mul hP
  have h2 := (((((hP.mul hL).mul hQ).mul hinv).mul hQ).mul hL).mul hP
  have h3 := h1.sub h2
  simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h3
  refine h3.congr_deriv ?_
  unfold schurDeriv
  noncomm_ring

variable (L₂ : M m n)

/-- **(RG.3g)**: at a kernel-supported origin (`P L₀ = 0`, `L₀ P = 0`) the first jet of the
induced localizer is `K₁ = P L₁ P`. -/
theorem schurDeriv_zero (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0) :
    schurDeriv L L' 0 = P * L' 0 * P := by
  have e1 : P * L 0 * Q * hardInvDeriv (L 0) (L' 0) * Q * L 0 * P = 0 := by
    rw [hP0]; simp
  have e2 : P * L 0 * Q * hardInv (L 0) * Q * L' 0 * P = 0 := by
    rw [hP0]; simp
  have e3 : P * L' 0 * Q * hardInv (L 0) * Q * L 0 * P = 0 := by
    rw [mul_assoc _ (L 0) P, h0P]; simp
  rw [schurDeriv, e1, e2, e3]
  simp

theorem hasDerivAt_schur_zero (hL : HasDerivAt L (L' 0) 0) (hu : IsUnit (P + Q * L 0 * Q))
    (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0) :
    HasDerivAt (fun t => schur (L t)) (P * L' 0 * P) 0 := by
  rw [← schurDeriv_zero L L' hP0 h0P]
  exact hasDerivAt_schur L L' hL hu

/-! ### Second jet -/

/-- **(RG.3h)**: the second jet `K₂ = P L₂ P - 2 P L₁ Q [P + Q L₀ Q]⁻¹ Q L₁ P`. -/
noncomputable def secondJet : M m n :=
  P * L₂ * P - (2 : ℝ) • (P * L' 0 * Q * hardInv (L 0) * Q * L' 0 * P)

/-- The derivative of `schurDeriv` at a kernel-supported origin is the second jet. -/
theorem hasDerivAt_schurDeriv_zero (hL : ∀ s, HasDerivAt L (L' s) s) (hL' : HasDerivAt L' L₂ 0)
    (hu : IsUnit (P + Q * L 0 * Q)) (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0) :
    HasDerivAt (schurDeriv L L') (secondJet L L' L₂) 0 := by
  have hP := hasDerivAt_const (0 : ℝ) (P : M m n)
  have hQ := hasDerivAt_const (0 : ℝ) (Q : M m n)
  have hL0 := hL 0
  have hinv := hasDerivAt_hardInv hL0 hu
  have hQLQ : HasDerivAt (fun t => Q * L' t * Q) (Q * L₂ * Q) 0 := by
    have h := (hQ.mul hL').mul hQ
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h
    exact h
  have hinvD : HasDerivAt (fun t => hardInvDeriv (L t) (L' t))
      (-(hardInvDeriv (L 0) (L' 0) * (Q * L' 0 * Q) * hardInv (L 0)
        + hardInv (L 0) * (Q * L₂ * Q) * hardInv (L 0)
        + hardInv (L 0) * (Q * L' 0 * Q) * hardInvDeriv (L 0) (L' 0))) 0 := by
    have h := (((hinv.mul hQLQ).mul hinv).neg)
    simp only [Pi.mul_apply] at h
    refine h.congr_deriv ?_
    noncomm_ring
  have hA : HasDerivAt (fun t => P * L' t * P) (P * L₂ * P) 0 := by
    have h := (hP.mul hL').mul hP
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h
    exact h
  have hT1 : HasDerivAt (fun t => P * L' t * Q * hardInv (L t) * Q * L t * P)
      (P * L' 0 * Q * hardInv (L 0) * Q * L' 0 * P) 0 := by
    have h := (((((hP.mul hL').mul hQ).mul hinv).mul hQ).mul hL0).mul hP
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h
    refine h.congr_deriv ?_
    simp only [mul_assoc, add_mul, h0P, mul_zero, add_zero, zero_add]
  have hT2 : HasDerivAt (fun t => P * L t * Q * hardInvDeriv (L t) (L' t) * Q * L t * P)
      (0 : M m n) 0 := by
    have h := (((((hP.mul hL0).mul hQ).mul hinvD).mul hQ).mul hL0).mul hP
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h
    refine h.congr_deriv ?_
    have hP0' : ∀ X : M m n, P * (L 0 * X) = 0 := fun X => by rw [← mul_assoc, hP0, zero_mul]
    simp only [mul_assoc, h0P, hP0', mul_zero, zero_mul, add_zero]
  have hT3 : HasDerivAt (fun t => P * L t * Q * hardInv (L t) * Q * L' t * P)
      (P * L' 0 * Q * hardInv (L 0) * Q * L' 0 * P) 0 := by
    have h := (((((hP.mul hL0).mul hQ).mul hinv).mul hQ).mul hL').mul hP
    simp only [Pi.mul_apply, zero_mul, mul_zero, add_zero, zero_add] at h
    refine h.congr_deriv ?_
    have hP0' : ∀ X : M m n, P * (L 0 * X) = 0 := fun X => by rw [← mul_assoc, hP0, zero_mul]
    simp only [mul_assoc, hP0', zero_mul, add_zero]
  have h := hA.sub ((hT1.add hT2).add hT3)
  refine h.congr_deriv ?_
  unfold secondJet
  rw [two_smul]
  abel

end Jets

/-! ### One-sided positivity of jets -/

/-- A function vanishing at `0` and nonnegative on `s > 0` has nonnegative derivative at `0`. -/
theorem deriv_nonneg_of_nonneg_right {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0) (h0 : f 0 = 0)
    (hpos : ∀ s, 0 < s → 0 ≤ f s) : 0 ≤ f' := by
  have hset : Ioi (0 : ℝ) \ {0} = Ioi 0 :=
    Set.sdiff_singleton_eq_self (by simp)
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp (hf.hasDerivWithinAt (s := Ioi 0))
  rw [hset] at hslope
  refine ge_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_field, h0, sub_zero, sub_zero]
  exact div_nonneg (hpos s hs) (le_of_lt hs)

/-- A function with `f 0 = 0`, `f' 0 = 0` that is nonnegative on `s > 0` has nonnegative second
derivative at `0`. -/
theorem deriv2_nonneg_of_nonneg_right {f f' : ℝ → ℝ} {f'' : ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : HasDerivAt f' f'' 0) (h0 : f 0 = 0) (h1 : f' 0 = 0) (hpos : ∀ s, 0 < s → 0 ≤ f s) :
    0 ≤ f'' := by
  by_contra hneg
  push Not at hneg
  have hset : Ioi (0 : ℝ) \ {0} = Ioi 0 :=
    Set.sdiff_singleton_eq_self (by simp)
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp (hf'.hasDerivWithinAt (s := Ioi 0))
  rw [hset] at hslope
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), slope f' 0 s < 0 :=
    hslope.eventually (gt_mem_nhds hneg)
  have hev' : ∀ᶠ s in 𝓝[>] (0 : ℝ), f' s < 0 := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
    rw [slope_def_field, h1, sub_zero, sub_zero] at hs
    exact ((div_neg_iff.mp hs).resolve_left fun h => absurd hs' (not_lt.mpr h.2.le)).1
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev'
  obtain ⟨δ, hδ, hδ'⟩ := hev'
  have hneg' : ∀ s ∈ Ioo (0 : ℝ) δ, f' s < 0 := by
    intro s hs
    exact hδ' (by rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hs.1]; exact hs.2) hs.1
  have hanti : StrictAntiOn f (Icc 0 δ) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 δ) ?_ ?_
    · exact fun s _ => (hf s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hf s).deriv]
      exact hneg' s hs
  have h2 : f (δ / 2) < f 0 :=
    hanti ⟨le_rfl, hδ.le⟩ ⟨by positivity, by linarith⟩ (by positivity)
  rw [h0] at h2
  exact absurd (hpos (δ / 2) (by positivity)) (not_le.mpr h2)

/-! ### Quadratic forms of the jets -/

/-- The quadratic form `x ↦ x ⬝ᵥ (A *ᵥ x)` as a continuous linear functional of `A`. -/
noncomputable def quadForm (x : m ⊕ n → ℝ) : M m n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => x ⬝ᵥ (A *ᵥ x)
      map_add' := fun A B => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun c A => by simp [smul_mulVec, dotProduct_smul] }

omit [DecidableEq m] [DecidableEq n] in
theorem quadForm_apply (x : m ⊕ n → ℝ) (A : M m n) : quadForm x A = x ⬝ᵥ (A *ᵥ x) := rfl

omit [DecidableEq m] [DecidableEq n] in
theorem hasDerivAt_quadForm {F : ℝ → M m n} {F' : M m n} {s : ℝ} (hF : HasDerivAt F F' s)
    (x : m ⊕ n → ℝ) : HasDerivAt (fun t => x ⬝ᵥ (F t *ᵥ x)) (x ⬝ᵥ (F' *ᵥ x)) s := by
  have h := (quadForm x).hasFDerivAt.comp_hasDerivAt s hF
  simp only [Function.comp_def] at h
  exact h

variable (L L' : ℝ → M m n) (L₂ : M m n)

/-- **(RG.3g) positivity**: if `𝒮(L s) ⪰ 0` for `s > 0` and the origin is kernel supported, the
first jet `K₁ = P L₁ P` is positive semidefinite. -/
theorem quadForm_jet1_nonneg (hL : HasDerivAt L (L' 0) 0) (hu : IsUnit (P + Q * L 0 * Q))
    (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0)
    (hpos : ∀ s, 0 < s → (schur (L s)).PosSemidef) (x : m ⊕ n → ℝ) :
    0 ≤ x ⬝ᵥ ((P * L' 0 * P) *ᵥ x) := by
  have hS0 : schur (L 0) = 0 := by
    rw [schur, hP0]
    simp
  refine deriv_nonneg_of_nonneg_right
    (hasDerivAt_quadForm (hasDerivAt_schur_zero L L' hL hu hP0 h0P) x)
    (by rw [hS0]; simp) fun s hs => ?_
  have := (hpos s hs).dotProduct_mulVec_nonneg x
  simpa using this

/-- **(RG.3h) positivity**: on `ker K₁` the second jet is positive semidefinite. -/
theorem quadForm_jet2_nonneg (hL : ∀ s, HasDerivAt L (L' s) s) (hL' : HasDerivAt L' L₂ 0)
    (hu : ∀ s, IsUnit (P + Q * L s * Q)) (hP0 : P * L 0 = 0) (h0P : L 0 * P = 0)
    (hpos : ∀ s, 0 < s → (schur (L s)).PosSemidef) (x : m ⊕ n → ℝ)
    (hx : (P * L' 0 * P) *ᵥ x = 0) : 0 ≤ x ⬝ᵥ (secondJet L L' L₂ *ᵥ x) := by
  have hS0 : schur (L 0) = 0 := by
    rw [schur, hP0]
    simp
  refine deriv2_nonneg_of_nonneg_right (f := fun t => x ⬝ᵥ (schur (L t) *ᵥ x))
    (f' := fun t => x ⬝ᵥ (schurDeriv L L' t *ᵥ x))
    (fun s => hasDerivAt_quadForm (hasDerivAt_schur L L' (hL s) (hu s)) x)
    (hasDerivAt_quadForm (hasDerivAt_schurDeriv_zero L L' L₂ hL hL' (hu 0) hP0 h0P) x)
    (by simp [hS0]) (by simp [schurDeriv_zero L L' hP0 h0P, hx]) fun s hs => ?_
  have := (hpos s hs).dotProduct_mulVec_nonneg x
  simpa using this

end SchurJets
end NCG
