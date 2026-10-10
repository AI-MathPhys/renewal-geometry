/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.PalatiniEulerIdentity

/-!
# Metric divergence calculus and the Euler row of a first-order density in one direction

Generic infrastructure for bridge step P3 (matter rows) of `thm:native-closure`
(Einstein–Standard-Model action-closure manuscript).

* `contEuler_apply` — the continuum Euler covector evaluated on one field direction `w`:
  `𝓔₀(Y)(z)[w] = DL(J¹Y)(w, 0) - Σ_μ ∂_μ[DL(J¹Y)(0, e_μ ⊗ w)](z)`;
* metric calculus for the metric field `g = eᵀηe` of a coframe field (`det e > 0`):
  `pd_volume` (`∂_μ v = v Γ^a_{aμ}`), `pd_ginv` (`∂_μ g^{ab} = ∂g⁻¹` jet) and the
  metric-compatibility form `dginv_eq_chr` (`∂_α g^{ab} = -g^{ac}Γ^b_{αc} - g^{bc}Γ^a_{αc}`);
* **`sum_pd_vec_density`** — divergence of a vector density:
  `Σ_μ ∂_μ(v g^{μρ}W_ρ) = v g^{μρ}(∂_ρW_μ - Γ^l_{ρμ}W_l)`;
* **`sum_pd_form_density`** — divergence of an antisymmetric 2-tensor density:
  `Σ_μ ∂_μ(v g^{μρ}g^{νσ}f_{ρσ}) = v g^{νσ} g^{μρ}(∂_ρf_{μσ} - Γ^l_{ρμ}f_{lσ} - Γ^l_{ρσ}f_{μl})`
  (the Christoffel form of the Yang–Mills divergence, `ActualJetGauge.ymDiv`).
-/

namespace RenewalGeometry

namespace NativeMatterEuler

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem PalatiniEuler
open NativeScaling (Mat eta metric readerOmega)
open NativeDensity (volume)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open Filter Topology Set
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The Euler covector in one direction -/

section Row

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The Euler covector evaluated on one direction**:
`𝓔₀(Y)(z)[w] = DL(J¹Y(z))(w, 0) - Σ_μ ∂_μ[z' ↦ DL(J¹Y(z'))(0, e_μ ⊗ w)](z)`. -/
theorem contEuler_apply {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y)
    (hJU : ∀ y, jet1 Y y ∈ U) (z : R4) (w : V) :
    contEuler L Y z w = fderiv ℝ L (jet1 Y z) (w, 0) -
      ∑ μ, pd (fun z' => fderiv ℝ L (jet1 Y z') (0, Pi.single μ w)) μ z := by
  have hF := ContEulerCalc.contDiff_fderiv_jet1 hU hL hY hJU
  unfold contEuler
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  set C : V →L[ℝ] V × (Fin 4 → V) := (ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)
  have hd : DifferentiableAt ℝ (fun z' => (fderiv ℝ L (jet1 Y z')).comp C) z :=
    ((hF.clm_comp contDiff_const).differentiable (by simp)) z
  have h := fderiv_clm_apply hd (differentiableAt_const w)
  unfold SobolevOpen.pd
  have hC : ∀ z', ((fderiv ℝ L (jet1 Y z')).comp C) w =
      fderiv ℝ L (jet1 Y z') (0, Pi.single μ w) := fun z' => by
    simp [C, ContinuousLinearMap.inr_apply]
  simp only [← hC]
  rw [h]
  simp [evec]

end Row

/-! ### Metric calculus of a coframe field -/

section Metric

variable {e : R4 → Mat}

theorem ginv_symm (z : R4) (a b : Fin 4) : ginvOf (gF e z) a b = ginvOf (gF e z) b a :=
  ginvOf_symm' (fun μ ν => gF_symm z μ ν) a b

/-- `∂_μ g^{ab}`: the coordinate derivative of the inverse metric field is the jet `dginv`. -/
theorem hasDerivAt_ginv_line (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4)
    (μ a b : Fin 4) :
    HasDerivAt (fun s : ℝ => ginvOf (gF e (z + s • Pi.single μ 1)) a b)
      (dginv (ginvOf (gF e z)) (dF (gF e) z) μ a b) 0 := by
  have hgd : Differentiable ℝ (gF e) := differentiable_gF (he.differentiable (by simp))
  have h := JetCurve.hasDerivAt_ginvOf (g := fun s => gF e (z + s • Pi.single μ 1)) (t := 0)
    (dg := dF (gF e) z) μ (fun μ' ν' => hasDerivAt_line_apply μ (hgd z) μ' ν')
    (by simpa using (det_gF_neg hdet z).ne) a b
  simpa using h

theorem differentiableAt_ginv (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4)
    (a b : Fin 4) : DifferentiableAt ℝ (fun y => ginvOf (gF e y) a b) z :=
  ((ActualJetSmooth.ContDiffAt.ginvOf (contDiff_gF he).contDiffAt (det_gF_neg hdet z).ne a b)
    |>.differentiableAt (by simp))

theorem contDiff_ginv (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (a b : Fin 4) :
    ContDiff ℝ ∞ (fun y => ginvOf (gF e y) a b) :=
  (metric_jets_smooth he hdet).2.1 a b

theorem pd_ginv (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (μ a b : Fin 4) :
    pd (fun y => ginvOf (gF e y) a b) μ z = dginv (ginvOf (gF e z)) (dF (gF e) z) μ a b :=
  pd_eq_of_line' (differentiableAt_ginv he hdet z a b) (hasDerivAt_ginv_line he hdet z μ a b)

theorem volume_eq_volM (y : R4) : volume (e y) = volM (gF e y) := rfl

/-- `∂_μ v = v Γ^a_{aμ}` (Jacobi's formula). -/
theorem hasDerivAt_volume_line (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4)
    (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => volume (e (z + s • Pi.single μ 1)))
      (volume (e z) * ∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a μ) 0 := by
  have hgd : Differentiable ℝ (gF e) := differentiable_gF (he.differentiable (by simp))
  have h := hasDerivAt_volM_curve (G := fun s => gF e (z + s • Pi.single μ 1))
    (k := dF (gF e) z μ) (t := 0) (fun μ' ν' => hasDerivAt_line_apply μ (hgd z) μ' ν')
    (by simpa using det_gF_neg hdet z) (by simpa using fun μ' ν' => gF_symm (e := e) z μ' ν')
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  rw [trace_chr _ _ (ginv_symm z) (fun α => dF_gF_symm (he.differentiable (by simp)) z α)]
  unfold trG
  rw [volume_eq_volM]
  ring

theorem differentiableAt_volume (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) :
    DifferentiableAt ℝ (fun y => volume (e y)) z :=
  ((contDiff_volume_comp he hdet).differentiable (by simp)) z

theorem pd_volume (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) (μ : Fin 4) :
    pd (fun y => volume (e y)) μ z =
      volume (e z) * ∑ a, chr (ginvOf (gF e z)) (dF (gF e) z) a a μ :=
  pd_eq_of_line' (differentiableAt_volume he hdet z) (hasDerivAt_volume_line he hdet z μ)

end Metric

/-- **Metric compatibility on jets**: for a symmetric inverse metric and a first jet symmetric in
its last two slots, `∂_α g^{ab} = -g^{ac}Γ^b_{αc} - g^{bc}Γ^a_{αc}`. -/
theorem dginv_eq_chr {n : Type*} [Fintype n] [DecidableEq n] (gi : n → n → ℝ)
    (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (α a b : n) :
    dginv gi dg α a b = -∑ c, (gi a c * chr gi dg b α c + gi b c * chr gi dg a α c) := by
  unfold dginv chr
  congr 1
  rw [Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun c σ => gi b c * (1 / 2 * (gi a σ * (dg α σ c + dg c σ α -
    dg σ α c))))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 := hdg α σ c
  have h2 := hdg c σ α
  have h3 := hdg σ α c
  have h4 := hgi σ b
  rw [h4, h1, h2, h3]
  ring

/-- The jet algebra behind the divergence of a vector density (`sum_pd_vec_density`). -/
theorem vec_div_alg {n : Type*} [Fintype n] [DecidableEq n] (gi : n → n → ℝ)
    (Γ : n → n → n → ℝ) (W : n → ℝ) (dW : n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hΓ : ∀ l a b, Γ l a b = Γ l b a) :
    ∑ μ, ((∑ a, Γ a a μ) * ∑ ρ, gi μ ρ * W ρ +
      ∑ ρ, ((-∑ c, (gi μ c * Γ ρ μ c + gi ρ c * Γ μ μ c)) * W ρ + gi μ ρ * dW μ ρ)) =
    ∑ μ, ∑ ρ, gi μ ρ * (dW ρ μ - ∑ l, Γ l ρ μ * W l) := by
  have eA0 : ∑ μ, ∑ ρ, ∑ a, Γ a a μ * gi μ ρ * W ρ = ∑ μ, ∑ a, ∑ ρ, Γ a a μ * gi μ ρ * W ρ :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_comm
  have eL : ∑ μ, ((∑ a, Γ a a μ) * ∑ ρ, gi μ ρ * W ρ +
      ∑ ρ, ((-∑ c, (gi μ c * Γ ρ μ c + gi ρ c * Γ μ μ c)) * W ρ + gi μ ρ * dW μ ρ)) =
      ∑ μ, ∑ a, ∑ ρ, Γ a a μ * gi μ ρ * W ρ - ∑ μ, ∑ ρ, ∑ c, gi μ c * Γ ρ μ c * W ρ -
        ∑ μ, ∑ ρ, ∑ c, gi ρ c * Γ μ μ c * W ρ + ∑ μ, ∑ ρ, gi μ ρ * dW μ ρ := by
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, neg_mul,
      Finset.sum_neg_distrib, add_mul, mul_assoc]
    simp only [← mul_assoc] at eA0 ⊢
    linarith [eA0]
  have eR : ∑ μ, ∑ ρ, gi μ ρ * (dW ρ μ - ∑ l, Γ l ρ μ * W l) =
      ∑ μ, ∑ ρ, gi μ ρ * dW ρ μ - ∑ μ, ∑ ρ, ∑ l, gi μ ρ * Γ l ρ μ * W l := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  have eA : ∑ μ, ∑ a, ∑ ρ, Γ a a μ * gi μ ρ * W ρ = ∑ μ, ∑ ρ, ∑ c, gi ρ c * Γ μ μ c * W ρ :=
    sum3_reindex _ _ { toFun := fun x => (x.2.1, x.2.2, x.1)
                       invFun := fun x => (x.2.2, x.1, x.2.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]; rw [hgi x.1 x.2.2]; ring
  have eB : ∑ μ, ∑ ρ, ∑ c, gi μ c * Γ ρ μ c * W ρ = ∑ μ, ∑ ρ, ∑ l, gi μ ρ * Γ l ρ μ * W l :=
    sum3_reindex _ _ { toFun := fun x => (x.1, x.2.2, x.2.1)
                       invFun := fun x => (x.1, x.2.2, x.2.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]; rw [hΓ x.2.1 x.1 x.2.2]
  have eD : ∑ μ, ∑ ρ, gi μ ρ * dW μ ρ = ∑ μ, ∑ ρ, gi μ ρ * dW ρ μ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgi]
  rw [eL, eR, eA, eB, eD]
  ring

/-- The jet algebra behind the divergence of an antisymmetric 2-tensor density
(`sum_pd_form_density`). -/
theorem form_div_alg {n : Type*} [Fintype n] [DecidableEq n] (gi : n → n → ℝ)
    (Γ : n → n → n → ℝ) (f : n → n → ℝ) (df : n → n → n → ℝ)
    (ν : n) (hΓ : ∀ l a b, Γ l a b = Γ l b a)
    (hf : ∀ a b, f a b = -f b a) :
    ∑ μ, ∑ ρ, gi μ ρ * (∑ σ, ((-∑ c, (gi ν c * Γ σ ρ c + gi σ c * Γ ν ρ c)) * f μ σ +
        gi ν σ * df ρ μ σ) - ∑ l, Γ l ρ μ * ∑ σ, gi ν σ * f l σ) =
      ∑ σ, gi ν σ * ∑ μ, ∑ ρ, gi μ ρ * (df ρ μ σ - ∑ l, (Γ l ρ μ * f l σ + Γ l ρ σ * f μ l)) := by
  set T1 := ∑ μ, ∑ ρ, ∑ σ, ∑ c, gi μ ρ * gi ν c * Γ σ ρ c * f μ σ
  set T2 := ∑ μ, ∑ ρ, ∑ σ, ∑ c, gi μ ρ * gi σ c * Γ ν ρ c * f μ σ
  set T3 := ∑ μ, ∑ ρ, ∑ σ, gi μ ρ * gi ν σ * df ρ μ σ
  set T4 := ∑ μ, ∑ ρ, ∑ l, ∑ σ, gi μ ρ * Γ l ρ μ * gi ν σ * f l σ
  set R1 := ∑ σ, ∑ μ, ∑ ρ, ∑ l, gi ν σ * gi μ ρ * Γ l ρ σ * f μ l
  set R3 := ∑ σ, ∑ μ, ∑ ρ, gi ν σ * gi μ ρ * df ρ μ σ
  set R4 := ∑ σ, ∑ μ, ∑ ρ, ∑ l, gi ν σ * gi μ ρ * Γ l ρ μ * f l σ
  have eL : ∑ μ, ∑ ρ, gi μ ρ * (∑ σ, ((-∑ c, (gi ν c * Γ σ ρ c + gi σ c * Γ ν ρ c)) * f μ σ +
        gi ν σ * df ρ μ σ) - ∑ l, Γ l ρ μ * ∑ σ, gi ν σ * f l σ) = -T1 - T2 + T3 - T4 := by
    simp only [T1, T2, T3, T4, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_add_distrib, neg_mul, mul_neg, Finset.sum_neg_distrib, add_mul, mul_add]
    simp only [← mul_assoc]
    ring
  have eR : ∑ σ, gi ν σ * ∑ μ, ∑ ρ, gi μ ρ * (df ρ μ σ - ∑ l, (Γ l ρ μ * f l σ + Γ l ρ σ * f μ l))
      = R3 - R4 - R1 := by
    simp only [R1, R3, R4, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib,
      mul_add]
    simp only [← mul_assoc]
    ring
  have e1 : T1 = R1 :=
    sum4_reindex _ _ { toFun := fun x => (x.2.2.2, x.1, x.2.1, x.2.2.1)
                       invFun := fun x => (x.2.1, x.2.2.1, x.2.2.2, x.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]; ring
  have e3 : T3 = R3 :=
    sum3_reindex _ _ { toFun := fun x => (x.2.2, x.1, x.2.1)
                       invFun := fun x => (x.2.1, x.2.2, x.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]; ring
  have e4 : T4 = R4 :=
    sum4_reindex _ _ { toFun := fun x => (x.2.2.2, x.1, x.2.1, x.2.2.1)
                       invFun := fun x => (x.2.1, x.2.2.1, x.2.2.2, x.1)
                       left_inv := fun x => rfl
                       right_inv := fun x => rfl } fun x => by
        simp only [Equiv.coe_fn_mk]; ring
  have e2 : T2 = -T2 := by
    have h : T2 = ∑ μ, ∑ ρ, ∑ σ, ∑ c, -(gi μ ρ * gi σ c * Γ ν ρ c * f μ σ) :=
      sum4_reindex _ _ { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
                         invFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
                         left_inv := fun x => rfl
                         right_inv := fun x => rfl } fun x => by
          simp only [Equiv.coe_fn_mk]
          rw [hf x.2.2.1 x.1, hΓ ν x.2.2.2 x.2.1]; ring
    calc T2 = _ := h
      _ = -T2 := by simp only [Finset.sum_neg_distrib]; rfl
  have e2' : T2 = 0 := by linarith
  rw [eL, eR, e1, e3, e4, e2']
  ring

/-! ### Divergence of densities built from the metric of a coframe field -/

section Divergence

variable {e : R4 → Mat}

theorem line_zero (z : R4) (μ : Fin 4) : z + (0 : ℝ) • Pi.single μ (1 : ℝ) = z := by simp

/-- **Divergence of a vector density**: for a smooth coframe field with `det e > 0` and smooth
`W_ρ`, `Σ_μ ∂_μ(v g^{μρ}W_ρ) = v g^{μρ}(∂_ρW_μ - Γ^l_{ρμ}W_l)` (`g = eᵀηe`, `Γ` its Christoffel
symbols). -/
theorem sum_pd_vec_density (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det)
    {W : R4 → Fin 4 → ℝ} (hW : ∀ ρ, ContDiff ℝ ∞ (fun y => W y ρ)) (z : R4) :
    ∑ μ, pd (fun y => volume (e y) * ∑ ρ, ginvOf (gF e y) μ ρ * W y ρ) μ z =
      volume (e z) * ∑ μ, ∑ ρ, ginvOf (gF e z) μ ρ * (pd (fun y => W y μ) ρ z -
        ∑ l, chr (ginvOf (gF e z)) (dF (gF e) z) l ρ μ * W z l) := by
  set gi := ginvOf (gF e z)
  set Γ := chr gi (dF (gF e) z)
  have hWd : ∀ ρ, Differentiable ℝ (fun y => W y ρ) := fun ρ => (hW ρ).differentiable (by simp)
  have hpd : ∀ μ, pd (fun y => volume (e y) * ∑ ρ, ginvOf (gF e y) μ ρ * W y ρ) μ z =
      volume (e z) * (∑ a, Γ a a μ) * ∑ ρ, gi μ ρ * W z ρ +
        volume (e z) * ∑ ρ, (dginv gi (dF (gF e) z) μ μ ρ * W z ρ +
          gi μ ρ * pd (fun y => W y ρ) μ z) := by
    intro μ
    have hd : DifferentiableAt ℝ (fun y => volume (e y) * ∑ ρ, ginvOf (gF e y) μ ρ * W y ρ) z :=
      (differentiableAt_volume he hdet z).mul (DifferentiableAt.fun_sum fun ρ _ =>
        (differentiableAt_ginv he hdet z μ ρ).mul (hWd ρ z))
    refine pd_eq_of_line' hd ?_
    have h := (hasDerivAt_volume_line he hdet z μ).fun_mul (HasDerivAt.fun_sum (u := Finset.univ)
      fun ρ _ => (hasDerivAt_ginv_line he hdet z μ μ ρ).fun_mul (hasDerivAt_line' μ (hWd ρ z)))
    simp only [line_zero] at h
    refine h.congr_deriv ?_
    simp only [gi, Γ]
  simp only [hpd]
  have hgi : ∀ a b, gi a b = gi b a := ginv_symm z
  have hdg : ∀ α μ ν, dF (gF e) z α μ ν = dF (gF e) z α ν μ := fun α =>
    dF_gF_symm (he.differentiable (by simp)) z α
  have hΓ : ∀ l a b, Γ l a b = Γ l b a := chr_symm gi _ hdg
  simp only [dginv_eq_chr gi _ hgi hdg]
  rw [← vec_div_alg gi Γ (W z) (fun μ ρ => pd (fun y => W y ρ) μ z) hgi hΓ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- **Divergence of an antisymmetric 2-tensor density**: for a smooth coframe field with
`det e > 0` and a smooth antisymmetric `f_{ρσ}`,
`Σ_μ ∂_μ(v g^{μρ}g^{νσ}f_{ρσ}) = v g^{νσ} g^{μρ}(∂_ρf_{μσ} - Γ^l_{ρμ}f_{lσ} - Γ^l_{ρσ}f_{μl})`. -/
theorem sum_pd_form_density (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det)
    {f : R4 → Fin 4 → Fin 4 → ℝ} (hf : ∀ ρ σ, ContDiff ℝ ∞ (fun y => f y ρ σ))
    (hanti : ∀ y ρ σ, f y ρ σ = -f y σ ρ) (ν : Fin 4) (z : R4) :
    ∑ μ, pd (fun y => volume (e y) * ∑ ρ, ∑ σ, ginvOf (gF e y) μ ρ * ginvOf (gF e y) ν σ *
        f y ρ σ) μ z =
      volume (e z) * ∑ σ, ginvOf (gF e z) ν σ * ∑ μ, ∑ ρ, ginvOf (gF e z) μ ρ *
        (pd (fun y => f y μ σ) ρ z - ∑ l, (chr (ginvOf (gF e z)) (dF (gF e) z) l ρ μ * f z l σ +
          chr (ginvOf (gF e z)) (dF (gF e) z) l ρ σ * f z μ l)) := by
  set gi := ginvOf (gF e z)
  set Γ := chr gi (dF (gF e) z)
  set W : R4 → Fin 4 → ℝ := fun y ρ => ∑ σ, ginvOf (gF e y) ν σ * f y ρ σ with hWdef
  have hW : ∀ ρ, ContDiff ℝ ∞ (fun y => W y ρ) := fun ρ =>
    ContDiff.sum fun σ _ => (contDiff_ginv he hdet ν σ).mul (hf ρ σ)
  have hfd : ∀ ρ σ, Differentiable ℝ (fun y => f y ρ σ) := fun ρ σ =>
    (hf ρ σ).differentiable (by simp)
  have hrw : ∀ μ, (fun y => volume (e y) * ∑ ρ, ∑ σ, ginvOf (gF e y) μ ρ *
      ginvOf (gF e y) ν σ * f y ρ σ) =
      fun y => volume (e y) * ∑ ρ, ginvOf (gF e y) μ ρ * W y ρ := by
    intro μ
    funext y
    simp only [hWdef, Finset.mul_sum, mul_assoc]
  simp only [hrw]
  rw [sum_pd_vec_density he hdet hW z]
  have hdW : ∀ ρ μ, pd (fun y => W y μ) ρ z =
      ∑ σ, (dginv gi (dF (gF e) z) ρ ν σ * f z μ σ + gi ν σ * pd (fun y => f y μ σ) ρ z) := by
    intro ρ μ
    have hd : DifferentiableAt ℝ (fun y => W y μ) z :=
      DifferentiableAt.fun_sum fun σ _ => (differentiableAt_ginv he hdet z ν σ).mul (hfd μ σ z)
    refine pd_eq_of_line' hd ?_
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ =>
      (hasDerivAt_ginv_line he hdet z ρ ν σ).fun_mul (hasDerivAt_line' ρ (hfd μ σ z))
    simp only [line_zero] at h
    exact h
  simp only [hdW]
  have hgi : ∀ a b, gi a b = gi b a := ginv_symm z
  have hdg : ∀ α μ ν, dF (gF e) z α μ ν = dF (gF e) z α ν μ := fun α =>
    dF_gF_symm (he.differentiable (by simp)) z α
  have hΓ : ∀ l a b, Γ l a b = Γ l b a := chr_symm gi _ hdg
  simp only [dginv_eq_chr gi _ hgi hdg]
  rw [← form_div_alg gi Γ (f z) (fun ρ μ σ => pd (fun y => f y μ σ) ρ z) ν hΓ (hanti z)]

end Divergence

end

end NativeMatterEuler

end RenewalGeometry
