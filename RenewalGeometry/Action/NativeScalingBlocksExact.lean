/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Action.ShiftedJetActionHessianExact
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmExact

/-!
# Amplitude-preserving scaling of the native link data
  (`lem:native-scaling`, Einstein–Standard-Model action-closure manuscript)

Building blocks of the local action `eq:native-densities` and the exact
substitution identities behind `lem:native-scaling` (`ρ = hK`, `ν = K⁻¹`,
nodal amplitudes unchanged):

* the algebraic Cartan reader `eq:native-LC-reader`
  `G_{λ,μν}(e,q) = η_{ab}(q^a_{λμ} e^b_ν + e^a_μ q^b_{λν})`,
  `Γ^ρ_{μν} = ½ g^{ρσ}(G_{μ,νσ} + G_{ν,μσ} - G_{σ,μν})`,
  `Ω_μ(e,q)^a_b = e^a_ρ Γ^ρ_{μν} e_b^ν - q^a_{μν} e_b^ν`
  (`readerG`, `readerGamma`, `readerOmega`), which is linear in the jet `q`
  (`readerOmega_smul`, `readerOmega_add`);
* `ω_{μ,h} = Ω(e, δ⁺_h e)` (`omegaLink`) satisfies `ω_h = K ω̃_ρ`
  (`omegaLink_scale`) and `e^{h ω_h} = e^{ρ ω̃_ρ}` (`exp_omegaLink_scale`);
* the gauge plaquette `U_μ(x) U_ν(x+e_μ) U_μ(x+e_ν)⁻¹ U_ν(x)⁻¹`
  (`gaugePlaquette`) is the shifted product of `lem:native-plaquette` with
  arguments `(A_μ, A_ν, δ⁺_μ A_ν, δ⁺_ν A_μ)` (`gaugePlaquette_eq_product`);
  the logarithmic field strength `F^h = h⁻² log(...)` (`fieldStrength`) is
  the removable-quotient map `Φ` of `lem:native-plaquette`
  (`fieldStrength_eq_logPlaquette`) and obeys the exact scaling
  `F^h[A] = K² F^ρ[νA]` (`fieldStrength_scale`);
* the Higgs link `K^h_μ` (`higgsLink`) and the covariant Dirac difference
  `∇^h_μ Ψ` (`diracDiff`, with spin link `V_μ = e^{hσ(ω_h)} ρ_S(U_μ)`)
  carry exactly one factor `K` (`higgsLink_scale`, `diracDiff_scale`).

Not covered here (disclosed): the assembly of the four densities of
`eq:native-densities` and the uniform regularity in `(ρ, ν)` of the normalised
stencil densities (the analytic clause of `lem:native-scaling`).
-/

open NormedSpace Finset Matrix

namespace RenewalGeometry
namespace NativeScaling

open ShiftedJetAction (Grid unitVec)

variable {n : ℕ} [NeZero n]

/-- Normalised first differences rescale by `K`: `δ⁺_h y = K δ⁺_{hK} y`. -/
theorem fwdDiff_scale {V : Type*} [AddCommGroup V] [Module ℝ V] {h K : ℝ}
    (hK : K ≠ 0) (μ : Fin 4) (y : Grid n → V) (x : Grid n) :
    ShiftedJetAction.fwdDiff h μ y x = K • ShiftedJetAction.fwdDiff (h * K) μ y x := by
  unfold ShiftedJetAction.fwdDiff
  rw [smul_smul]
  congr 1
  field_simp

/-! ### The algebraic Cartan reader `eq:native-LC-reader` -/

/-- Real `4 × 4` matrices: coframes `e^a_μ` (row `a`, column `μ`) and jets. -/
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)`. -/
def eta : Mat := Matrix.diagonal ![-1, 1, 1, 1]

/-- The metric `g_{μν} = η_{ab} e^a_μ e^b_ν`. -/
def metric (e : Mat) : Mat := eᵀ * eta * e

/-- `G_{λ,μν}(e,q) = η_{ab}(q^a_{λμ} e^b_ν + e^a_μ q^b_{λν})`. -/
def readerG (e : Mat) (q : Fin 4 → Mat) (lam : Fin 4) : Mat :=
  (q lam)ᵀ * eta * e + eᵀ * eta * q lam

/-- `Γ^ρ_{μν}(e,q) = ½ g^{ρσ}(G_{μ,νσ} + G_{ν,μσ} - G_{σ,μν})`. -/
noncomputable def readerGamma (e : Mat) (q : Fin 4 → Mat) (ρ μ ν : Fin 4) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ σ, (metric e)⁻¹ ρ σ *
    (readerG e q μ ν σ + readerG e q ν μ σ - readerG e q σ μ ν)

/-- `Ω_μ(e,q)^a_b = e^a_ρ Γ^ρ_{μν} e_b^ν - q^a_{μν} e_b^ν`, with `e_b^ν = (e⁻¹)^ν_b`. -/
noncomputable def readerOmega (e : Mat) (q : Fin 4 → Mat) (μ : Fin 4) : Mat :=
  fun a b => ∑ ρ, ∑ ν, e a ρ * readerGamma e q ρ μ ν * e⁻¹ ν b - ∑ ν, q μ a ν * e⁻¹ ν b

theorem readerG_smul (e : Mat) (K : ℝ) (q : Fin 4 → Mat) (lam : Fin 4) :
    readerG e (K • q) lam = K • readerG e q lam := by
  simp [readerG, Matrix.transpose_smul, smul_add]

theorem readerG_add (e : Mat) (q q' : Fin 4 → Mat) (lam : Fin 4) :
    readerG e (q + q') lam = readerG e q lam + readerG e q' lam := by
  simp only [readerG, Pi.add_apply, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem readerGamma_smul (e : Mat) (K : ℝ) (q : Fin 4 → Mat) (ρ μ ν : Fin 4) :
    readerGamma e (K • q) ρ μ ν = K * readerGamma e q ρ μ ν := by
  simp only [readerGamma, readerG_smul, Matrix.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  ring

theorem readerGamma_add (e : Mat) (q q' : Fin 4 → Mat) (ρ μ ν : Fin 4) :
    readerGamma e (q + q') ρ μ ν = readerGamma e q ρ μ ν + readerGamma e q' ρ μ ν := by
  simp only [readerGamma, readerG_add, Matrix.add_apply, ← mul_add, ← sum_add_distrib]
  refine congrArg _ (sum_congr rfl fun σ _ => ?_)
  ring

/-- The Cartan reader is linear in the jet: `Ω(e, K q) = K Ω(e, q)`. -/
theorem readerOmega_smul (e : Mat) (K : ℝ) (q : Fin 4 → Mat) (μ : Fin 4) :
    readerOmega e (K • q) μ = K • readerOmega e q μ := by
  ext a b
  simp only [readerOmega, readerGamma_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    mul_sum, mul_sub]
  congr 1
  · refine sum_congr rfl fun ρ _ => sum_congr rfl fun ν _ => ?_
    ring
  · refine sum_congr rfl fun ν _ => ?_
    ring

theorem readerOmega_add (e : Mat) (q q' : Fin 4 → Mat) (μ : Fin 4) :
    readerOmega e (q + q') μ = readerOmega e q μ + readerOmega e q' μ := by
  ext a b
  simp only [readerOmega, readerGamma_add, Pi.add_apply, Matrix.add_apply, mul_add, add_mul,
    sum_add_distrib]
  ring

/-- `ω_{μ,h}(x) = Ω_μ(e(x), δ⁺_h e(x))`. -/
noncomputable def omegaLink (h : ℝ) (e : Grid n → Mat) (x : Grid n) (μ : Fin 4) : Mat :=
  readerOmega (e x) (fun lam => ShiftedJetAction.fwdDiff h lam e x) μ

/-- `ω_h = K ω̃_ρ` with `ρ = hK`: the reader is linear in the first difference. -/
theorem omegaLink_scale {h K : ℝ} (hK : K ≠ 0) (e : Grid n → Mat) (x : Grid n) (μ : Fin 4) :
    omegaLink h e x μ = K • omegaLink (h * K) e x μ := by
  unfold omegaLink
  rw [← readerOmega_smul]
  congr 1
  funext lam
  exact fwdDiff_scale hK lam e x

/-- `e^{h ω_h} = e^{ρ ω̃_ρ}`. -/
theorem exp_omegaLink_scale {h K : ℝ} (hK : K ≠ 0) (e : Grid n → Mat) (x : Grid n)
    (μ : Fin 4) :
    exp (h • omegaLink h e x μ) = exp ((h * K) • omegaLink (h * K) e x μ) := by
  rw [omegaLink_scale hK, smul_smul]

/-! ### The gauge plaquette and the logarithmic field strength -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- The gauge plaquette `U_μ(x) U_ν(x+e_μ) U_μ(x+e_ν)⁻¹ U_ν(x)⁻¹`, `U_μ = e^{h A_μ}`
(`eq:native-plaquettes`). -/
noncomputable def gaugePlaquette (h : ℝ) (A : Fin 4 → Grid n → 𝔄) (x : Grid n) (μ ν : Fin 4) :
    𝔄 :=
  exp (h • A μ x) * exp (h • A ν (x + unitVec n μ)) * exp (-(h • A μ (x + unitVec n ν))) *
    exp (-(h • A ν x))

/-- The gauge plaquette is the shifted product of `lem:native-plaquette` with arguments
`X = A_μ(x)`, `Y = A_ν(x)`, `a = δ⁺_μ A_ν(x)`, `b = δ⁺_ν A_μ(x)`. -/
theorem gaugePlaquette_eq_product {h : ℝ} (hh : h ≠ 0) (A : Fin 4 → Grid n → 𝔄) (x : Grid n)
    (μ ν : Fin 4) :
    gaugePlaquette h A x μ ν = ShiftedPlaquette.product h (A μ x) (A ν x)
      (ShiftedJetAction.fwdDiff h μ (A ν) x) (ShiftedJetAction.fwdDiff h ν (A μ) x) := by
  unfold gaugePlaquette ShiftedPlaquette.product ShiftedJetAction.fwdDiff
  have h2 : h ^ 2 * h⁻¹ = h := by
    field_simp
  congr 2
  · rw [smul_smul, h2, smul_sub, add_sub_cancel]
  · congr 1
    rw [smul_smul, h2, smul_sub]
    abel

/-- The logarithmic field strength `F^h_{μν} = h⁻² log(plaquette)` with the series
logarithm near the identity. -/
noncomputable def fieldStrength (h : ℝ) (A : Fin 4 → Grid n → 𝔄) (x : Grid n) (μ ν : Fin 4) :
    𝔄 :=
  (h ^ 2)⁻¹ • ShiftedPlaquette.logOneAdd (gaugePlaquette h A x μ ν - 1)

/-- The field strength is the removable-quotient map `Φ` of `lem:native-plaquette`
evaluated at the shifted first jet of `A`. -/
theorem fieldStrength_eq_logPlaquette {h : ℝ} (hh : h ≠ 0) (A : Fin 4 → Grid n → 𝔄)
    (x : Grid n) (μ ν : Fin 4) :
    fieldStrength h A x μ ν = ShiftedPlaquette.logPlaquette (A μ x) (A ν x)
      (ShiftedJetAction.fwdDiff h μ (A ν) x) (ShiftedJetAction.fwdDiff h ν (A μ) x) h := by
  unfold fieldStrength
  rw [gaugePlaquette_eq_product hh, ← ShiftedPlaquette.sq_smul_logPlaquette _ _ _ _ hh,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hh), one_smul]

/-- `U_μ = e^{hA} = e^{ρ (νA)}`: the plaquette of `A` at mesh `h` is the plaquette of
`νA` at mesh `ρ = hK`. -/
theorem gaugePlaquette_scale {h K : ℝ} (hK : K ≠ 0) (A : Fin 4 → Grid n → 𝔄) (x : Grid n)
    (μ ν : Fin 4) :
    gaugePlaquette h A x μ ν = gaugePlaquette (h * K) (K⁻¹ • A) x μ ν := by
  unfold gaugePlaquette
  simp only [Pi.smul_apply, smul_smul, mul_assoc, mul_inv_cancel₀ hK, mul_one]

/-- `lem:native-scaling`, gauge sector: `F^h[A] = K² F^{ρ}[νA]` exactly. -/
theorem fieldStrength_scale {h K : ℝ} (hK : K ≠ 0) (A : Fin 4 → Grid n → 𝔄) (x : Grid n)
    (μ ν : Fin 4) :
    fieldStrength h A x μ ν = K ^ 2 • fieldStrength (h * K) (K⁻¹ • A) x μ ν := by
  unfold fieldStrength
  rw [← gaugePlaquette_scale hK, smul_smul]
  congr 1
  field_simp

/-! ### Matter links -/

/-- The Higgs link `K^h_μ = (ρ_H(U_μ) H(x+e_μ) - H(x))/h` (`eq:native-matter-links`). -/
noncomputable def higgsLink {𝓗 : Type*} [AddCommGroup 𝓗] [Module ℝ 𝓗] (h : ℝ)
    (ρH : 𝔄 → 𝓗 → 𝓗) (A : Fin 4 → Grid n → 𝔄) (H : Grid n → 𝓗) (x : Grid n) (μ : Fin 4) :
    𝓗 :=
  h⁻¹ • (ρH (exp (h • A μ x)) (H (x + unitVec n μ)) - H x)

/-- `lem:native-scaling`, Higgs sector: the Higgs link carries one factor `K`. -/
theorem higgsLink_scale {𝓗 : Type*} [AddCommGroup 𝓗] [Module ℝ 𝓗] {h K : ℝ} (hK : K ≠ 0)
    (ρH : 𝔄 → 𝓗 → 𝓗) (A : Fin 4 → Grid n → 𝔄) (H : Grid n → 𝓗) (x : Grid n) (μ : Fin 4) :
    higgsLink h ρH A H x μ = K • higgsLink (h * K) ρH (K⁻¹ • A) H x μ := by
  unfold higgsLink
  rw [smul_smul]
  congr 1
  · field_simp
  · simp only [Pi.smul_apply, smul_smul, mul_assoc, mul_inv_cancel₀ hK, mul_one]

/-- The spin link `V_μ = e^{h σ(ω_{μ,h})} ρ_S(U_μ)` (`eq:native-matter-links`), with `σ` the
(linear) spin representation of the Lie algebra and `ρ_S` the gauge representation, both
valued in an algebra `𝔖` of operators on the spinor space. -/
noncomputable def spinLink {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    (h : ℝ) (σ : Mat →ₗ[ℝ] 𝔖) (ρS : 𝔄 → 𝔖) (e : Grid n → Mat) (A : Fin 4 → Grid n → 𝔄)
    (x : Grid n) (μ : Fin 4) : 𝔖 :=
  exp (h • σ (omegaLink h e x μ)) * ρS (exp (h • A μ x))

theorem spinLink_scale {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    {h K : ℝ} (hK : K ≠ 0) (σ : Mat →ₗ[ℝ] 𝔖) (ρS : 𝔄 → 𝔖) (e : Grid n → Mat)
    (A : Fin 4 → Grid n → 𝔄) (x : Grid n) (μ : Fin 4) :
    spinLink h σ ρS e A x μ = spinLink (h * K) σ ρS e (K⁻¹ • A) x μ := by
  unfold spinLink
  rw [omegaLink_scale hK, map_smul, smul_smul]
  simp only [Pi.smul_apply, smul_smul, mul_assoc, mul_inv_cancel₀ hK, mul_one]

/-- The covariant Dirac difference `∇^h_μ Ψ = (V_μ Ψ(x+e_μ) - Ψ(x))/h`
(`eq:native-spin-differences`), with `𝔖` acting on the spinor space `𝓢`. -/
noncomputable def diracDiff {𝔖 𝓢 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖]
    [CompleteSpace 𝔖] [AddCommGroup 𝓢] [Module ℝ 𝓢] (act : 𝔖 → 𝓢 → 𝓢) (h : ℝ)
    (σ : Mat →ₗ[ℝ] 𝔖) (ρS : 𝔄 → 𝔖) (e : Grid n → Mat) (A : Fin 4 → Grid n → 𝔄)
    (Ψ : Grid n → 𝓢) (x : Grid n) (μ : Fin 4) : 𝓢 :=
  h⁻¹ • (act (spinLink h σ ρS e A x μ) (Ψ (x + unitVec n μ)) - Ψ x)

/-- `lem:native-scaling`, Dirac sector: each covariant difference carries one factor `K`. -/
theorem diracDiff_scale {𝔖 𝓢 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖]
    [CompleteSpace 𝔖] [AddCommGroup 𝓢] [Module ℝ 𝓢] (act : 𝔖 → 𝓢 → 𝓢) {h K : ℝ}
    (hK : K ≠ 0) (σ : Mat →ₗ[ℝ] 𝔖) (ρS : 𝔄 → 𝔖) (e : Grid n → Mat) (A : Fin 4 → Grid n → 𝔄)
    (Ψ : Grid n → 𝓢) (x : Grid n) (μ : Fin 4) :
    diracDiff act h σ ρS e A Ψ x μ = K • diracDiff act (h * K) σ ρS e (K⁻¹ • A) Ψ x μ := by
  unfold diracDiff
  rw [spinLink_scale hK, smul_smul]
  congr 1
  field_simp

end NativeScaling
end RenewalGeometry
