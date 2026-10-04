/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.PalatiniTorsionCoefficientModelExact

/-!
# Connection variation of the Palatini–Holst action (`thm:supp-palatini-torsion`)

This file closes the clause of `thm:supp-palatini-torsion` (emergent-spacetime manuscript)
"for the Palatini–Holst action the spinless connection Euler equation is `D(P_{α,β} B) = 0`",
in the coefficient model of `PalatiniTorsionCoefficientModelExact` (chart `Pt = ℝ⁴`, coframe
`e^I_μ`, connection `ω^I{}_{Kμ}`, `pd` = Fréchet derivative along coordinate vectors, internal
action `act`, `starC`, `palatiniC`, Levi-Civita symbol `leviCivita`).

## The action

* `curvature ω` : `R^A{}_{Bρσ} = ∂_ρ ω^A{}_{Bσ} - ∂_σ ω^A{}_{Bρ} + ω^A{}_{Kρ} ω^K{}_{Bσ}
  - ω^A{}_{Kσ} ω^K{}_{Bρ}` (`R = dω + ω ∧ ω`, quadratic in `ω`);
* `lagrangian α β λ e ω` : the coordinate density
  `¼ ε^{μνρσ} η_A (P_{α,β} B)^{AB}{}_{μν} R^A{}_{Bρσ} + λ det e` of the four-form
  `⟨P_{α,β} e ∧ e, R(ω)⟩ + λ L_vol`.  Here `⟨B, R⟩ = e^I ∧ e^J ∧ R_{IJ}` is the Holst density and,
  in the star convention of the coefficient model (`ε^{0123} = 1`, i.e. `ε_{0123} = -1`),
  `⟨⋆B, R⟩ = ½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}` is the Palatini density, so this is
  `α L_Holst + β L_Palatini + λ L_vol` (`eq:main-phv-densities`, `eq:main-phv-coefficients`);
* `relAction … δ U t = ∫_U (L(ω + t δ) - L(ω))` : the variation of the action over the chart
  domain `U` (only differences are integrated);
* `IsLorentzVariation U δ` : `δ` smooth, compactly supported, `tsupport δ ⊆ U`, and
  `so(1,3)`-valued at every point;
* `IsConnectionStationary` : `d/dt|₀ relAction = 0` for every such `δ`.

## Results

* `curvArr_add_smul`, `lagrangian_add_smul`, `relAction_eq` : the exact expansion
  `R(ω + tδ) = R(ω) + t D_ωδ + t² δ∧δ`, hence `t ↦ S_U(ω + tδ) - S_U(ω)` is the quadratic
  polynomial `t ∫ ¼ε⟨PB, D_ωδ⟩ + t² ∫ ¼ε⟨PB, δ∧δ⟩` (`deriv_relAction`);
* `integral_pd_mul` (integration by parts on `ℝ⁴`, from Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) and
  `integral_firstVarDensity_smul_const` : along `δ = ψ c` the first variation is `¼ ∫ ψ E_c`;
* `eulerDensity_eq`, `eulerDensity_eq_Zf` : `E_c = -2 Σ η_A c^A{}_{Bσ} Zf^{AB}{}_σ` for Lorentz
  `ω` (Lorentz property used to move the connection onto `PB`), and `sum_eps_covD` :
  `Σ ε^{μνρσ} D(PB)^{AB}{}_{μνρ} = 3 Zf^{AB}{}_σ`;
* `eq_zero_on_of_integral_mul_eq_zero` (fundamental lemma, from
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` plus continuity), elementary Lorentz
  test coefficients `testCoeff`, and `eq_zero_of_eps_contract` (`ε`-contraction is injective on
  three-forms);
* **`eulerResidual_eq_zero_of_isConnectionStationary`** : stationarity ⟹ `D(P_{α,β} B) = 0` on `U`;
* **`isConnectionStationary_of_eulerResidual_eq_zero`** : the converse;
* **`torsion_eq_zero_of_isConnectionStationary`** : with `(α, β) ≠ (0, 0)` and `det e ≠ 0`,
  stationarity ⟹ `T = 0` on `U` (via `torsion_eq_zero_of_euler`);
* `palatini_torsion_exact` : the packaged statement of `thm:supp-palatini-torsion`.

Rendering: the chart is `ℝ⁴` with fields of class `C¹` on it, the connection is Lorentz
(`so(1,3)`-valued) everywhere, and the action is varied on an arbitrary open chart domain `U`
with variations compactly supported in `U`.
-/

open scoped BigOperators

noncomputable section

namespace RenewalGeometry.PalatiniHolstVariation

open PalatiniTorsionModel

/-- Internal/form coefficient arrays with three indices. -/
abbrev Arr3 : Type := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Internal/form coefficient arrays with four indices. -/
abbrev Arr4 : Type := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

local macro "sc" : tactic => `(tactic| refine Finset.sum_congr rfl fun _ _ => ?_)

/-! ## The Levi-Civita symbol -/

theorem leviCivita_swap34 (a b c d : Fin 4) : leviCivita a b c d = -leviCivita a b d c := by
  have h : ∀ a b c d : Fin 4, leviCivitaZ a b c d = -leviCivitaZ a b d c := by decide
  unfold leviCivita; rw [h a b c d]; push_cast; ring

theorem leviCivita_cyc (a b c d : Fin 4) : leviCivita a b c d = leviCivita c a b d := by
  have h : ∀ a b c d : Fin 4, leviCivitaZ a b c d = leviCivitaZ c a b d := by decide
  unfold leviCivita; rw [h a b c d]

/-! ## Reordering finite sums -/

theorem sum_swap_first_last5 (X : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, X a b c d e = ∑ e, ∑ b, ∑ c, ∑ d, ∑ a, X a b c d e := by
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, e]; rw [Finset.sum_comm]
  conv_lhs => enter [2, e, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, e, 2, b, 2, c]; rw [Finset.sum_comm]

theorem sum_swap_first_last4 (X : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, X a b c d = ∑ d, ∑ b, ∑ c, ∑ a, X a b c d := by
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, d]; rw [Finset.sum_comm]
  conv_lhs => enter [2, d, 2, b]; rw [Finset.sum_comm]

theorem sum_rot4 (X : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, X a b c d = ∑ b, ∑ c, ∑ d, ∑ a, X a b c d := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, b, 2, c]; rw [Finset.sum_comm]

theorem sum_rot3 (X : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, X a b c = ∑ b, ∑ c, ∑ a, X a b c := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]

/-! ## The action pairing `ε^{μνρσ} ⟨F_{μν}, R_{ρσ}⟩` -/

/-- The pairing `Σ ε^{μνρσ} η_A F^{AB}_{μν} R^A{}_{Bρσ}` of an internal-bivector two-form `F`
(`F A B μ ν = F^{AB}_{μν}`) with a curvature-type two-form `R` (`R A B ρ σ = R^A{}_{Bρσ}`);
`η_A R^A{}_B = R_{AB}` lowers the first internal index. -/
def pairing (F R : Arr4) : ℝ :=
  ∑ ρ, ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν, leviCivita μ ν ρ σ * eta A * F A B μ ν * R A B ρ σ

theorem pairing_add (F R R' : Arr4) : pairing F (R + R') = pairing F R + pairing F R' := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_sub (F R R' : Arr4) : pairing F (R - R') = pairing F R - pairing F R' := by
  simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul (F R : Arr4) (t : ℝ) : pairing F (t • R) = t * pairing F R := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  sc; sc; sc; sc; sc; sc; ring

theorem pairing_zero (F : Arr4) : pairing F 0 = 0 := by
  simp [pairing]

/-- Exchange of the two curvature form slots. -/
def swapRS (R : Arr4) : Arr4 := fun A B ρ σ => R A B σ ρ

theorem pairing_swapRS (F R : Arr4) : pairing F (swapRS R) = -pairing F R := by
  unfold pairing swapRS
  conv_lhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  sc; sc; sc; sc; sc; sc
  rw [leviCivita_swap34]; ring

/-! ## The derivative part of the first variation -/

/-- `(dδ)` for `δ = ψ c` with gradient `p = ∂ψ`: `p_ρ c_{ABσ} - p_σ c_{ABρ}`. -/
def derivForm (p : Fin 4 → ℝ) (c : Arr3) : Arr4 :=
  fun A B ρ σ => p ρ * c A B σ - p σ * c A B ρ

/-- The coefficient of `∂_ρ ψ` in the first variation along `δ = ψ c`. -/
def gfun (F : Arr4) (c : Arr3) (ρ : Fin 4) : ℝ :=
  2 * ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν, (leviCivita μ ν ρ σ * eta A * c A B σ) * F A B μ ν

theorem pairing_derivForm (F : Arr4) (p : Fin 4 → ℝ) (c : Arr3) :
    pairing F (derivForm p c) = ∑ ρ, p ρ * gfun F c ρ := by
  have h : derivForm p c = (fun A B ρ σ => p ρ * c A B σ) -
      swapRS (fun A B ρ σ => p ρ * c A B σ) := by
    funext A B ρ σ; rfl
  rw [h, pairing_sub, pairing_swapRS, sub_neg_eq_add, ← two_mul]
  simp only [pairing, gfun, Finset.mul_sum]
  sc; sc; sc; sc; sc; sc; ring

/-! ## The algebraic part of the first variation -/

/-- Linearised `ω ∧ ω` term: `[ω, δ]` part of `D_ω δ`. -/
def algCurv (w d : Arr3) : Arr4 := fun A B ρ σ =>
  ∑ K, (w A K ρ * d K B σ + d A K ρ * w K B σ - w A K σ * d K B ρ - d A K σ * w K B ρ)

def Z1 (w c : Arr3) : Arr4 := fun A B ρ σ => ∑ K, w A K ρ * c K B σ

def Z2 (w c : Arr3) : Arr4 := fun A B ρ σ => ∑ K, c A K ρ * w K B σ

theorem algCurv_eq (w c : Arr3) :
    algCurv w c = Z1 w c + Z2 w c - swapRS (Z1 w c) - swapRS (Z2 w c) := by
  funext A B ρ σ
  simp only [algCurv, Z1, Z2, swapRS, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_four]
  ring

theorem pairing_algCurv (F : Arr4) (w c : Arr3) :
    pairing F (algCurv w c) = 2 * pairing F (Z1 w c) - 2 * pairing F (swapRS (Z2 w c)) := by
  have h2 : pairing F (Z2 w c) = -pairing F (swapRS (Z2 w c)) := by
    rw [← pairing_swapRS]; rfl
  rw [algCurv_eq, pairing_sub, pairing_sub, pairing_add, pairing_swapRS F (Z1 w c), h2]
  ring

theorem pairing_Z1 (F : Arr4) {w : Arr3} (hw : ∀ ρ, IsLorentz (fun P Q => w P Q ρ)) (c : Arr3) :
    pairing F (Z1 w c) = -∑ ρ, ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν,
      leviCivita μ ν ρ σ * eta A * c A B σ * ∑ K, w A K ρ * F K B μ ν := by
  unfold pairing Z1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  sc; sc
  rw [sum_swap_first_last5]
  sc; sc; sc; sc; sc
  rename_i ρ _ σ _ A _ B _ μ _ ν _ K _
  have hl := hw ρ K A
  simp only at hl
  linear_combination (leviCivita μ ν ρ σ * F K B μ ν * c A B σ) * hl

theorem pairing_swapZ2 (F : Arr4) (w c : Arr3) :
    pairing F (swapRS (Z2 w c)) = ∑ ρ, ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν,
      leviCivita μ ν ρ σ * eta A * c A B σ * ∑ K, w B K ρ * F A K μ ν := by
  unfold pairing Z2 swapRS
  simp only [Finset.mul_sum]
  sc; sc; sc
  rw [sum_swap_first_last4]
  sc; sc; sc; sc; ring

theorem sum_gfun (dF : Fin 4 → Arr4) (c : Arr3) :
    ∑ ρ, gfun (dF ρ) c ρ = 2 * ∑ ρ, ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν,
      leviCivita μ ν ρ σ * eta A * c A B σ * dF ρ A B μ ν := by
  simp only [gfun, Finset.mul_sum]

/-- One cyclic term `∂_ρ F_{μν} + ω_ρ · F_{μν}` of the exterior covariant derivative, in arrays. -/
def covTermArr (F : Arr4) (dF : Fin 4 → Arr4) (w : Arr3) (ρ μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun A B => dF ρ A B μ ν + act (fun P Q => w P Q ρ) (fun P Q => F P Q μ ν) A B

/-- The Euler density: coefficient of `ψ` after integrating the first variation along `δ = ψ c`
by parts. -/
def eulerDensity (F : Arr4) (dF : Fin 4 → Arr4) (w c : Arr3) : ℝ :=
  pairing F (algCurv w c) - ∑ ρ, gfun (dF ρ) c ρ

theorem eulerDensity_eq (F : Arr4) (dF : Fin 4 → Arr4) {w : Arr3}
    (hw : ∀ ρ, IsLorentz (fun P Q => w P Q ρ)) (c : Arr3) :
    eulerDensity F dF w c = -2 * ∑ ρ, ∑ σ, ∑ A, ∑ B, ∑ μ, ∑ ν,
      leviCivita μ ν ρ σ * eta A * c A B σ * covTermArr F dF w ρ μ ν A B := by
  rw [eulerDensity, pairing_algCurv, pairing_Z1 F hw, pairing_swapZ2, sum_gfun]
  simp only [covTermArr, act, Finset.sum_add_distrib, mul_add]
  ring

theorem sum_rot3' (X : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, X a b c = ∑ c, ∑ a, ∑ b, X a b c := by
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

/-! ## Elementary Lorentz test coefficients -/

/-- Kronecker delta. -/
def kd (i j : Fin 4) : ℝ := if i = j then 1 else 0

/-- Elementary Lorentz-valued test coefficient
`c^A{}_{Bσ} = η_A (δ^A_a δ_B^b - δ^A_b δ_B^a) δ_σ^s`. -/
def testCoeff (a b s : Fin 4) : Arr3 :=
  fun A B σ => eta A * (kd σ s * (kd A a * kd B b - kd A b * kd B a))

theorem eta_mul_eta_mul (A : Fin 4) (x : ℝ) : eta A * (eta A * x) = x := by
  rw [← mul_assoc, eta_sq, one_mul]

theorem testCoeff_isLorentz (a b s σ : Fin 4) :
    IsLorentz (fun P Q => testCoeff a b s P Q σ) := by
  intro P Q
  simp only [testCoeff, eta_mul_eta_mul]
  ring

theorem sum_testCoeff (a b s : Fin 4) (Z : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ σ, ∑ A, ∑ B, eta A * testCoeff a b s A B σ * Z A B σ = Z a b s - Z b a s := by
  simp only [testCoeff, eta_mul_eta_mul, kd]
  simp [ite_mul, mul_ite, sub_mul, mul_sub, Finset.sum_sub_distrib]

/-- The `ε`-contracted cyclic term `Σ ε^{μνρσ} (∂_ρ F_{μν} + ω_ρ · F_{μν})^{AB}`. -/
def Zf (F : Arr4) (dF : Fin 4 → Arr4) (w : Arr3) (A B σ : Fin 4) : ℝ :=
  ∑ ρ, ∑ μ, ∑ ν, leviCivita μ ν ρ σ * covTermArr F dF w ρ μ ν A B

/-- The Euler density for an arbitrary constant coefficient `c`:
`E_c = -2 Σ_{σ,A,B} η_A c^A{}_{Bσ} Zf^{AB}{}_σ`. -/
theorem eulerDensity_eq_Zf (F : Arr4) (dF : Fin 4 → Arr4) {w : Arr3}
    (hw : ∀ ρ, IsLorentz (fun P Q => w P Q ρ)) (c : Arr3) :
    eulerDensity F dF w c = -2 * ∑ σ, ∑ A, ∑ B, eta A * c A B σ * Zf F dF w A B σ := by
  rw [eulerDensity_eq F dF hw, sum_rot4]
  congr 1
  simp only [Zf, Finset.mul_sum]
  sc; sc; sc; sc; sc; sc; ring

theorem eulerDensity_testCoeff (F : Arr4) (dF : Fin 4 → Arr4) {w : Arr3}
    (hw : ∀ ρ, IsLorentz (fun P Q => w P Q ρ)) (a b s : Fin 4) :
    eulerDensity F dF w (testCoeff a b s) = -2 * (Zf F dF w a b s - Zf F dF w b a s) := by
  rw [eulerDensity_eq_Zf F dF hw, sum_testCoeff]

/-- Cyclic resummation: `Σ ε (H_{μνρ} + H_{νρμ} + H_{ρμν}) = 3 Σ ε H_{ρμν}`. -/
theorem sum_eps_cyclic (σ : Fin 4) (H : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * (H μ ν ρ + H ν ρ μ + H ρ μ ν) =
      3 * ∑ ρ, ∑ μ, ∑ ν, leviCivita μ ν ρ σ * H ρ μ ν := by
  have h1 : ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * H μ ν ρ =
      ∑ ρ, ∑ μ, ∑ ν, leviCivita μ ν ρ σ * H ρ μ ν := by
    sc; sc; sc
    rename_i a _ b _ c _
    rw [leviCivita_cyc b c a σ]
  have h2 : ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * H ρ μ ν =
      ∑ ρ, ∑ μ, ∑ ν, leviCivita μ ν ρ σ * H ρ μ ν := sum_rot3' _
  have h3 : ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * H ν ρ μ =
      ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * H μ ν ρ := by
    rw [sum_rot3]
    sc; sc; sc
    rename_i a _ b _ c _
    rw [← leviCivita_cyc a b c σ]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h3, h1, h2]
  ring

/-- **`ε`-contraction is injective on three-forms**: a totally antisymmetric `X_{μνρ}` with
`Σ ε^{μνρσ} X_{μνρ} = 0` for every `σ` vanishes. -/
theorem eq_zero_of_eps_contract (X : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h1 : ∀ μ ν ρ, X μ ν ρ = -X ν μ ρ) (h2 : ∀ μ ν ρ, X μ ν ρ = -X μ ρ ν)
    (h : ∀ σ, ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * X μ ν ρ = 0) : X = 0 := by
  have z : ∀ σ, ∀ μ ν ρ : Fin 4, μ ≠ σ → ν ≠ σ → ρ ≠ σ → μ < ν → ν < ρ → X μ ν ρ = 0 := by
    intro σ
    have hs := h σ
    simp only [Fin.sum_univ_four] at hs
    fin_cases σ <;>
    simp (config := {decide := true}) only [leviCivita, leviCivitaZ, inversions] at hs <;>
    norm_num at hs <;>
    intro μ ν ρ hμ hν hρ hμν hνρ <;>
    fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> simp at hμ hν hρ hμν hνρ ⊢ <;>
    linarith [h1 0 1 2, h1 0 1 3, h1 0 2 3, h1 1 2 3, h2 0 1 2, h2 0 1 3, h2 0 2 3, h2 1 2 3,
      h2 1 0 2, h2 1 0 3, h2 2 0 3, h2 2 1 3, h1 0 2 1, h1 0 3 1, h1 0 3 2, h1 1 3 2,
      h1 1 2 0, h1 1 3 0, h1 2 3 0, h1 2 3 1]
  funext μ ν ρ
  have k1 := h1 μ ν ρ
  have k2 := h2 μ ν ρ
  have k3 := h2 ν μ ρ
  have k4 := h1 μ ρ ν
  have k5 := h1 ν ρ μ
  have z0 := z 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have z1 := z 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have z2 := z 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have z3 := z 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> simp at k1 k2 k3 k4 k5 ⊢ <;> linarith

/-! ## Fields on the chart -/

/-- The field `(P_{α,β} B)^{IJ}_{μν}` (`B = e ∧ e`). -/
def PB (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) : Pt → Arr4 :=
  fun y I J μ ν => capply (palatiniC α β) (fun A C => bivectorField e y A C μ ν) I J

theorem eulerResidual_eq_covD (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Arr3) (x : Pt) :
    eulerResidual α β e ω x = covD ω (PB α β e) x := rfl

/-- Coordinate derivatives of a three-index field: `dArr3 f x ρ A B σ = ∂_ρ f^A{}_{Bσ}(x)`. -/
def dArr3 (f : Pt → Arr3) (x : Pt) : Fin 4 → Arr3 :=
  fun ρ A B σ => pd ρ (fun y => f y A B σ) x

/-- Coordinate derivatives of a four-index field. -/
def dArr4 (f : Pt → Arr4) (x : Pt) : Fin 4 → Arr4 :=
  fun ρ A B μ ν => pd ρ (fun y => f y A B μ ν) x

/-- Curvature components `R^A{}_{Bρσ} = ∂_ρ ω^A{}_{Bσ} - ∂_σ ω^A{}_{Bρ}
+ ω^A{}_{Kρ} ω^K{}_{Bσ} - ω^A{}_{Kσ} ω^K{}_{Bρ}` (`R = dω + ω ∧ ω`), from the connection value `w`
and its derivatives `dw`. -/
def curvArr (w : Arr3) (dw : Fin 4 → Arr3) : Arr4 := fun A B ρ σ =>
  dw ρ A B σ - dw σ A B ρ + ∑ K, (w A K ρ * w K B σ - w A K σ * w K B ρ)

/-- The curvature two-form of the connection field `ω`. -/
def curvature (ω : Pt → Arr3) (x : Pt) : Arr4 := curvArr (ω x) (dArr3 ω x)

/-- `D_ω δ`: the linearisation of the curvature in the direction `δ` (with derivatives `dd`). -/
def linCurv (w d : Arr3) (dd : Fin 4 → Arr3) : Arr4 := fun A B ρ σ =>
  dd ρ A B σ - dd σ A B ρ + algCurv w d A B ρ σ

/-- `δ ∧ δ`: the quadratic part of the curvature in the direction `δ`. -/
def quadCurv (d : Arr3) : Arr4 := fun A B ρ σ => ∑ K, (d A K ρ * d K B σ - d A K σ * d K B ρ)

/-- **Exact expansion** `R(ω + t δ) = R(ω) + t D_ω δ + t² δ ∧ δ` (coefficient level). -/
theorem curvArr_add_smul (w d : Arr3) (dw dd : Fin 4 → Arr3) (t : ℝ) :
    curvArr (w + t • d) (dw + t • dd) = curvArr w dw + t • linCurv w d dd + t ^ 2 • quadCurv d := by
  funext A B ρ σ
  simp only [curvArr, linCurv, algCurv, quadCurv, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four]
  ring

/-- **The Palatini–Holst Lagrangian density** on the chart,
`L(e, ω) = ¼ ε^{μνρσ} ⟨(P_{α,β} B)_{μν}, R(ω)_{ρσ}⟩ + λ det e`
(the coordinate density of the four-form `⟨P_{α,β} e ∧ e, R(ω)⟩ + λ L_vol`, with
`⟨X, Y⟩ = X^{AB} Y_{AB}`). -/
def lagrangian (α β lam : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Arr3) (x : Pt) : ℝ :=
  pairing (PB α β e x) (curvature ω x) / 4 + lam * Matrix.det (e x : Matrix (Fin 4) (Fin 4) ℝ)

/-- First-variation density `¼ ε ⟨P B, D_ω δ⟩`. -/
def firstVarDensity (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω δ : Pt → Arr3) (x : Pt) : ℝ :=
  pairing (PB α β e x) (linCurv (ω x) (δ x) (dArr3 δ x)) / 4

/-- Second-variation density `¼ ε ⟨P B, δ ∧ δ⟩`. -/
def secondVarDensity (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (δ : Pt → Arr3) (x : Pt) : ℝ :=
  pairing (PB α β e x) (quadCurv (δ x)) / 4

theorem dArr3_add_smul {ω δ : Pt → Arr3} {x : Pt}
    (hω : ∀ A B σ, DifferentiableAt ℝ (fun y => ω y A B σ) x)
    (hδ : ∀ A B σ, DifferentiableAt ℝ (fun y => δ y A B σ) x) (t : ℝ) :
    dArr3 (fun y => ω y + t • δ y) x = dArr3 ω x + t • dArr3 δ x := by
  funext ρ A B σ
  simp only [dArr3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [pd_add (hω A B σ) ((hδ A B σ).const_mul t), pd_const_mul (hδ A B σ)]

/-- **Exact expansion of the Lagrangian**: `L(ω + t δ) - L(ω) = t · ¼ε⟨PB, D_ωδ⟩ + t² · ¼ε⟨PB, δ∧δ⟩`. -/
theorem lagrangian_add_smul (α β lam : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) {ω δ : Pt → Arr3} {x : Pt}
    (hω : ∀ A B σ, DifferentiableAt ℝ (fun y => ω y A B σ) x)
    (hδ : ∀ A B σ, DifferentiableAt ℝ (fun y => δ y A B σ) x) (t : ℝ) :
    lagrangian α β lam e (fun y => ω y + t • δ y) x - lagrangian α β lam e ω x =
      t * firstVarDensity α β e ω δ x + t ^ 2 * secondVarDensity α β e δ x := by
  simp only [lagrangian, curvature, firstVarDensity, secondVarDensity]
  rw [dArr3_add_smul hω hδ t, curvArr_add_smul, pairing_add, pairing_add, pairing_smul,
    pairing_smul]
  ring

/-! ## Regularity helpers -/

theorem pd_neg (μ : Fin 4) (f : Pt → ℝ) (x : Pt) : pd μ (fun y => -f y) x = -pd μ f x := by
  unfold pd; rw [fderiv_fun_neg]; rfl

theorem pd_mul_const {f : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x) (k : ℝ) (μ : Fin 4) :
    pd μ (fun y => f y * k) x = pd μ f x * k := by
  unfold pd; rw [(hf.hasFDerivAt.mul_const k).fderiv]
  simp [mul_comm]

theorem continuous_pd {f : Pt → ℝ} (hf : ContDiff ℝ 1 f) (μ : Fin 4) : Continuous (pd μ f) := by
  show Continuous fun x => fderiv ℝ f x (Pi.single μ 1)
  exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem pd_eq_zero_of_notMem_tsupport {f : Pt → ℝ} {x : Pt} (hx : x ∉ tsupport f) (μ : Fin 4) :
    pd μ f x = 0 := by
  have h : fderiv ℝ f x = 0 := by
    by_contra hne
    exact hx (support_fderiv_subset ℝ hne)
  simp [pd, h]

theorem contDiff_PB (α β : ℝ) {e : Pt → Fin 4 → Fin 4 → ℝ} {n : WithTop ℕ∞} (he : ContDiff ℝ n e) :
    ContDiff ℝ n (PB α β e) := by
  unfold PB capply bivectorField
  fun_prop

theorem contDiff_comp3 {f : Pt → Arr3} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (A B σ : Fin 4) :
    ContDiff ℝ n (fun y => f y A B σ) := by fun_prop

theorem contDiff_comp4 {f : Pt → Arr4} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (A B μ ν : Fin 4) :
    ContDiff ℝ n (fun y => f y A B μ ν) := by fun_prop

theorem continuous_dArr3 {f : Pt → Arr3} (hf : ContDiff ℝ 1 f) : Continuous (dArr3 f) := by
  refine continuous_pi fun ρ => continuous_pi fun A => continuous_pi fun B =>
    continuous_pi fun σ => ?_
  exact continuous_pd (contDiff_comp3 hf A B σ) ρ

theorem continuous_dArr4 {f : Pt → Arr4} (hf : ContDiff ℝ 1 f) : Continuous (dArr4 f) := by
  refine continuous_pi fun ρ => continuous_pi fun A => continuous_pi fun B =>
    continuous_pi fun μ => continuous_pi fun ν => ?_
  exact continuous_pd (contDiff_comp4 hf A B μ ν) ρ

theorem continuous_pairing {F R : Pt → Arr4} (hF : Continuous F) (hR : Continuous R) :
    Continuous (fun x => pairing (F x) (R x)) := by
  unfold pairing; fun_prop

theorem continuous_linCurv {w d : Pt → Arr3} {dd : Pt → Fin 4 → Arr3} (hw : Continuous w)
    (hd : Continuous d) (hdd : Continuous dd) :
    Continuous (fun x => linCurv (w x) (d x) (dd x)) := by
  unfold linCurv algCurv; fun_prop

theorem continuous_quadCurv {d : Pt → Arr3} (hd : Continuous d) :
    Continuous (fun x => quadCurv (d x)) := by
  unfold quadCurv; fun_prop

theorem linCurv_zero (w : Arr3) : linCurv w 0 0 = 0 := by
  funext A B ρ σ; simp [linCurv, algCurv]

theorem quadCurv_zero : quadCurv 0 = 0 := by
  funext A B ρ σ; simp [quadCurv]

theorem eq_zero_of_notMem_tsupport {δ : Pt → Arr3} {x : Pt} (hx : x ∉ tsupport δ) :
    δ x = 0 ∧ dArr3 δ x = 0 := by
  refine ⟨image_eq_zero_of_notMem_tsupport hx, ?_⟩
  funext ρ A B σ
  have hsub : tsupport (fun y => δ y A B σ) ⊆ tsupport δ :=
    tsupport_comp_subset (g := fun d : Arr3 => d A B σ) rfl δ
  exact pd_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)) ρ

theorem firstVarDensity_eq_zero {α β : ℝ} {e : Pt → Fin 4 → Fin 4 → ℝ} {ω δ : Pt → Arr3} {x : Pt}
    (hx : x ∉ tsupport δ) : firstVarDensity α β e ω δ x = 0 := by
  obtain ⟨h0, h1⟩ := eq_zero_of_notMem_tsupport hx
  simp [firstVarDensity, h0, h1, linCurv_zero, pairing_zero]

theorem secondVarDensity_eq_zero {α β : ℝ} {e : Pt → Fin 4 → Fin 4 → ℝ} {δ : Pt → Arr3} {x : Pt}
    (hx : x ∉ tsupport δ) : secondVarDensity α β e δ x = 0 := by
  obtain ⟨h0, -⟩ := eq_zero_of_notMem_tsupport hx
  simp [secondVarDensity, h0, quadCurv_zero, pairing_zero]

/-! ## The relative action and connection stationarity -/

open MeasureTheory

/-- **The relative Palatini–Holst action** on the chart domain `U`:
`t ↦ S_U(ω + t δ) - S_U(ω) = ∫_U (L(ω + t δ) - L(ω))`.  (Only differences of the action are
integrated, so no integrability of `L(ω)` itself over `U` is needed; for a variation supported in
`U` this is the variation of the action over any domain containing `U`.) -/
def relAction (α β lam : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω δ : Pt → Arr3) (U : Set Pt)
    (t : ℝ) : ℝ :=
  ∫ x in U, (lagrangian α β lam e (fun y => ω y + t • δ y) x - lagrangian α β lam e ω x)

/-- **Admissible connection variations** on `U`: smooth, compactly supported in `U`, and
`so(1,3)`-valued (`δ_{IK σ} = η_{II} δ^I{}_{Kσ}` antisymmetric) at every point. -/
structure IsLorentzVariation (U : Set Pt) (δ : Pt → Arr3) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) δ
  compact : HasCompactSupport δ
  subset : tsupport δ ⊆ U
  lorentz : ∀ x σ, IsLorentz (fun P Q => δ x P Q σ)

/-- **Connection stationarity** of the Palatini–Holst action on `U`: the first variation
`d/dt|_{t=0} (S_U(ω + t δ) - S_U(ω))` vanishes for every admissible Lorentz variation. -/
def IsConnectionStationary (α β lam : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Arr3)
    (U : Set Pt) : Prop :=
  ∀ δ, IsLorentzVariation U δ → deriv (relAction α β lam e ω δ U) 0 = 0

theorem integrable_firstVarDensity {α β : ℝ} {e : Pt → Fin 4 → Fin 4 → ℝ} {ω δ : Pt → Arr3}
    (he : ContDiff ℝ 1 e) (hω : Continuous ω) (hδ : ContDiff ℝ 1 δ) (hδc : HasCompactSupport δ) :
    Integrable (firstVarDensity α β e ω δ) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · unfold firstVarDensity
    exact (continuous_pairing (contDiff_PB α β he).continuous
      (continuous_linCurv hω hδ.continuous (continuous_dArr3 hδ))).div_const 4
  · refine hδc.mono' fun x hx => ?_
    by_contra h
    exact hx (firstVarDensity_eq_zero h)

theorem integrable_secondVarDensity {α β : ℝ} {e : Pt → Fin 4 → Fin 4 → ℝ} {δ : Pt → Arr3}
    (he : ContDiff ℝ 1 e) (hδ : ContDiff ℝ 1 δ) (hδc : HasCompactSupport δ) :
    Integrable (secondVarDensity α β e δ) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · unfold secondVarDensity
    exact (continuous_pairing (contDiff_PB α β he).continuous
      (continuous_quadCurv hδ.continuous)).div_const 4
  · refine hδc.mono' fun x hx => ?_
    by_contra h
    exact hx (secondVarDensity_eq_zero h)

/-- **The relative action is an exact quadratic polynomial in `t`**:
`S_U(ω + tδ) - S_U(ω) = t ∫ ¼ε⟨PB, D_ωδ⟩ + t² ∫ ¼ε⟨PB, δ∧δ⟩` for `C¹` variations compactly
supported in `U`. -/
theorem relAction_eq (α β lam : ℝ) {e : Pt → Fin 4 → Fin 4 → ℝ} {ω δ : Pt → Arr3} {U : Set Pt}
    (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω) (hδ : ContDiff ℝ 1 δ)
    (hδc : HasCompactSupport δ) (hU : tsupport δ ⊆ U) :
    relAction α β lam e ω δ U = fun t =>
      t * (∫ x, firstVarDensity α β e ω δ x) + t ^ 2 * ∫ x, secondVarDensity α β e δ x := by
  funext t
  have hωd : ∀ x A B σ, DifferentiableAt ℝ (fun y => ω y A B σ) x := fun x A B σ =>
    ((contDiff_comp3 hω A B σ).differentiable one_ne_zero) x
  have hδd : ∀ x A B σ, DifferentiableAt ℝ (fun y => δ y A B σ) x := fun x A B σ =>
    ((contDiff_comp3 hδ A B σ).differentiable one_ne_zero) x
  have hpt : (fun x => lagrangian α β lam e (fun y => ω y + t • δ y) x - lagrangian α β lam e ω x)
      = fun x => t * firstVarDensity α β e ω δ x + t ^ 2 * secondVarDensity α β e δ x :=
    funext fun x => lagrangian_add_smul α β lam e (hωd x) (hδd x) t
  unfold relAction
  rw [hpt, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_add ((integrable_firstVarDensity he hω.continuous hδ hδc).const_mul t)
      ((integrable_secondVarDensity he hδ hδc).const_mul (t ^ 2)), integral_const_mul,
      integral_const_mul]
  · intro x hx
    have hx' : x ∉ tsupport δ := fun h => hx (hU h)
    simp [firstVarDensity_eq_zero hx', secondVarDensity_eq_zero hx']

theorem deriv_quadratic (a b : ℝ) : deriv (fun t : ℝ => t * a + t ^ 2 * b) 0 = a := by
  have h3 := ((hasDerivAt_id (0 : ℝ)).mul_const a).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const b)
  have hf : (fun t : ℝ => t * a + t ^ 2 * b) = ((fun y => id y * a) + fun y => y ^ 2 * b) := rfl
  rw [hf, h3.deriv]
  simp

/-- The first variation of the action is `∫ ¼ε⟨PB, D_ωδ⟩`. -/
theorem deriv_relAction (α β lam : ℝ) {e : Pt → Fin 4 → Fin 4 → ℝ} {ω δ : Pt → Arr3} {U : Set Pt}
    (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω) (hδ : ContDiff ℝ 1 δ)
    (hδc : HasCompactSupport δ) (hU : tsupport δ ⊆ U) :
    deriv (relAction α β lam e ω δ U) 0 = ∫ x, firstVarDensity α β e ω δ x := by
  rw [relAction_eq α β lam he hω hδ hδc hU, deriv_quadratic]

/-! ## The first variation along `δ = ψ c`: integration by parts -/

theorem dArr3_smul_const {ψ : Pt → ℝ} {x : Pt} (hψ : DifferentiableAt ℝ ψ x) (c : Arr3) :
    dArr3 (fun y => ψ y • c) x = fun ρ => pd ρ ψ x • c := by
  funext ρ A B σ
  simp only [dArr3, Pi.smul_apply, smul_eq_mul]
  exact pd_mul_const hψ _ ρ

theorem linCurv_smul_const (w c : Arr3) (s : ℝ) (p : Fin 4 → ℝ) :
    linCurv w (s • c) (fun ρ => p ρ • c) = derivForm p c + s • algCurv w c := by
  funext A B ρ σ
  simp only [linCurv, derivForm, algCurv, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_four]
  ring

theorem firstVarDensity_smul_const (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Arr3)
    {ψ : Pt → ℝ} (hψ : Differentiable ℝ ψ) (c : Arr3) (x : Pt) :
    firstVarDensity α β e ω (fun y => ψ y • c) x =
      (∑ ρ, pd ρ ψ x * gfun (PB α β e x) c ρ +
        ψ x * pairing (PB α β e x) (algCurv (ω x) c)) / 4 := by
  simp only [firstVarDensity]
  rw [dArr3_smul_const (hψ x) c, linCurv_smul_const, pairing_add, pairing_derivForm, pairing_smul]

/-- Derivatives pass through the linear functional `gfun`. -/
theorem pd_gfun {F : Pt → Arr4} (hF : Differentiable ℝ F) (c : Arr3) (ρ ρ' : Fin 4) (x : Pt) :
    pd ρ' (fun y => gfun (F y) c ρ) x = gfun (dArr4 F x ρ') c ρ := by
  unfold gfun dArr4
  rw [pd_const_mul (by fun_prop) 2]
  congr 1
  rw [pd_sum]
  · sc
    rw [pd_sum]
    · sc
      rw [pd_sum]
      · sc
        rw [pd_sum]
        · sc
          rw [pd_sum]
          · sc
            exact pd_const_mul (by fun_prop) _ ρ'
          · intro i _; fun_prop
        · intro i _; fun_prop
      · intro i _; fun_prop
    · intro i _; fun_prop
  · intro i _; fun_prop

/-- **Integration by parts on the chart**: `∫ ∂_ρ ψ · f = -∫ ψ · ∂_ρ f` for `f ∈ C¹` and
`ψ ∈ C¹` with compact support. -/
theorem integral_pd_mul {f ψ : Pt → ℝ} (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (ρ : Fin 4) :
    ∫ x, pd ρ ψ x * f x = -∫ x, ψ x * pd ρ f x := by
  have hfc := hf.continuous
  have hψco := hψ.continuous
  have h1 : MeasureTheory.Integrable (fun x => fderiv ℝ f x (Pi.single ρ 1) * ψ x) :=
    ((continuous_pd hf ρ).mul hψco).integrable_of_hasCompactSupport hψc.mul_left
  have h2 : MeasureTheory.Integrable (fun x => f x * fderiv ℝ ψ x (Pi.single ρ 1)) :=
    (hfc.mul (continuous_pd hψ ρ)).integrable_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (Pi.single ρ 1)).mul_left
  have h3 : MeasureTheory.Integrable (fun x => f x * ψ x) :=
    (hfc.mul hψco).integrable_of_hasCompactSupport hψc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hψ.differentiable one_ne_zero) x)
  simp only [pd]
  rw [show (fun x => fderiv ℝ ψ x (Pi.single ρ 1) * f x) =
      fun x => f x * fderiv ℝ ψ x (Pi.single ρ 1) from funext fun x => mul_comm _ _, key,
    show (fun x => fderiv ℝ f x (Pi.single ρ 1) * ψ x) =
      fun x => ψ x * fderiv ℝ f x (Pi.single ρ 1) from funext fun x => mul_comm _ _]

/-- **First variation along `δ = ψ c`**, after integration by parts:
`∫ ¼ε⟨PB, D_ω(ψ c)⟩ = ¼ ∫ ψ · E_c`, with `E_c = ε⟨PB, [ω, c]⟩ - Σ_ρ ∂_ρ(…)` the Euler density. -/
theorem integral_firstVarDensity_smul_const (α β : ℝ) {e : Pt → Fin 4 → Fin 4 → ℝ}
    {ω : Pt → Arr3} (he : ContDiff ℝ 1 e) (hω : Continuous ω) {ψ : Pt → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (c : Arr3) :
    ∫ x, firstVarDensity α β e ω (fun y => ψ y • c) x =
      (∫ x, ψ x * eulerDensity (PB α β e x) (dArr4 (PB α β e) x) (ω x) c) / 4 := by
  have hPB := contDiff_PB α β he
  have hPBc := hPB.continuous
  have hdPB := continuous_dArr4 hPB
  have hψco := hψ.continuous
  have hg : ∀ ρ, ContDiff ℝ 1 (fun x => gfun (PB α β e x) c ρ) := by
    intro ρ; unfold gfun; fun_prop
  have hh : Continuous (fun x => pairing (PB α β e x) (algCurv (ω x) c)) :=
    continuous_pairing hPBc (by unfold algCurv; fun_prop)
  have hgd : ∀ ρ, Continuous (fun x => gfun (dArr4 (PB α β e) x ρ) c ρ) := by
    intro ρ; unfold gfun; fun_prop
  have hI : ∀ ρ, ∫ x, pd ρ ψ x * gfun (PB α β e x) c ρ =
      -∫ x, ψ x * gfun (dArr4 (PB α β e) x ρ) c ρ := by
    intro ρ
    have := integral_pd_mul (hg ρ) hψ hψc ρ
    simp only [pd_gfun (hPB.differentiable one_ne_zero)] at this
    exact this
  have i1 : ∀ ρ, MeasureTheory.Integrable (fun x => pd ρ ψ x * gfun (PB α β e x) c ρ) := by
    intro ρ
    exact ((continuous_pd hψ ρ).mul (hg ρ).continuous).integrable_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (Pi.single ρ 1)).mul_right
  have i2 : MeasureTheory.Integrable (fun x => ψ x * pairing (PB α β e x) (algCurv (ω x) c)) :=
    (hψco.mul hh).integrable_of_hasCompactSupport hψc.mul_right
  have i3 : ∀ ρ, MeasureTheory.Integrable
      (fun x => ψ x * gfun (dArr4 (PB α β e) x ρ) c ρ) := by
    intro ρ
    exact (hψco.mul (hgd ρ)).integrable_of_hasCompactSupport hψc.mul_right
  simp_rw [firstVarDensity_smul_const α β e ω (hψ.differentiable one_ne_zero) c]
  rw [MeasureTheory.integral_div]
  congr 1
  unfold eulerDensity
  simp_rw [mul_sub, Finset.mul_sum]
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_finsetSum _ fun ρ _ => i1 ρ) i2,
    MeasureTheory.integral_sub i2 (MeasureTheory.integrable_finsetSum _ fun ρ _ => i3 ρ),
    MeasureTheory.integral_finsetSum _ fun ρ _ => i1 ρ,
    MeasureTheory.integral_finsetSum _ fun ρ _ => i3 ρ]
  simp only [hI, Finset.sum_neg_distrib]
  ring

/-! ## Antisymmetries -/

theorem PB_antisymm_internal (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (y : Pt) (A B μ ν : Fin 4) :
    PB α β e y A B μ ν = -PB α β e y B A μ ν := by
  have h := capply_palatiniC α β (fun A C => bivectorField e y A C μ ν)
  have hs := capply_starC_antisymm (fun A C => bivectorField e y A C μ ν) A B
  show capply (palatiniC α β) (fun A C => bivectorField e y A C μ ν) A B =
    -capply (palatiniC α β) (fun A C => bivectorField e y A C μ ν) B A
  rw [h]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  simp only [bivectorField]
  ring

theorem PB_antisymm_form (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (y : Pt) (A B μ ν : Fin 4) :
    PB α β e y A B μ ν = -PB α β e y A B ν μ := by
  simp only [PB, capply, bivectorField]
  rw [← Finset.sum_neg_distrib]
  sc
  rw [← Finset.sum_neg_distrib]
  sc
  ring

theorem act_neg_arg (w b : Fin 4 → Fin 4 → ℝ) : act w (fun P Q => -b P Q) = -act w b := by
  funext I J
  simp only [act, Pi.neg_apply, ← Finset.sum_neg_distrib]
  sc; ring

/-- Each cyclic term of `D F` is antisymmetric in its two form slots when `F` is. -/
theorem covTerm_antisymm (ω : Pt → Arr3) {F : Pt → Arr4}
    (hF : ∀ y A B μ ν, F y A B μ ν = -F y A B ν μ) (x : Pt) (μ ν ρ A C : Fin 4) :
    covTerm ω F x μ ν ρ A C = -covTerm ω F x μ ρ ν A C := by
  have h1 : (fun y => F y A C ν ρ) = fun y => -F y A C ρ ν := funext fun y => hF y A C ν ρ
  have h2 : (fun P Q => F x P Q ν ρ) = fun P Q => -F x P Q ρ ν :=
    funext fun P => funext fun Q => hF x P Q ν ρ
  simp only [covTerm]
  rw [h1, h2, pd_neg, act_neg_arg]
  simp only [Pi.neg_apply]
  ring

theorem covD_swap12 (ω : Pt → Arr3) {F : Pt → Arr4}
    (hF : ∀ y A B μ ν, F y A B μ ν = -F y A B ν μ) (x : Pt) (A B μ ν ρ : Fin 4) :
    covD ω F x A B μ ν ρ = -covD ω F x A B ν μ ρ := by
  simp only [covD]
  rw [covTerm_antisymm ω hF x ν μ ρ, covTerm_antisymm ω hF x μ ρ ν,
    covTerm_antisymm ω hF x ρ ν μ]
  ring

theorem covD_swap23 (ω : Pt → Arr3) {F : Pt → Arr4}
    (hF : ∀ y A B μ ν, F y A B μ ν = -F y A B ν μ) (x : Pt) (A B μ ν ρ : Fin 4) :
    covD ω F x A B μ ν ρ = -covD ω F x A B μ ρ ν := by
  simp only [covD]
  rw [covTerm_antisymm ω hF x μ ρ ν, covTerm_antisymm ω hF x ρ ν μ,
    covTerm_antisymm ω hF x ν μ ρ]
  ring

/-- `Zf` is antisymmetric in its internal indices for internally antisymmetric `F`, `dF`. -/
theorem Zf_antisymm (F : Arr4) (dF : Fin 4 → Arr4) (w : Arr3)
    (hF : ∀ A B μ ν, F A B μ ν = -F B A μ ν) (hdF : ∀ ρ A B μ ν, dF ρ A B μ ν = -dF ρ B A μ ν)
    (A B σ : Fin 4) : Zf F dF w A B σ = -Zf F dF w B A σ := by
  simp only [Zf, ← Finset.sum_neg_distrib]
  sc; sc; sc
  rename_i ρ _ μ _ ν _
  have e1 : act (fun P Q => w P Q ρ) (fun P Q => F P Q μ ν) A B =
      -act (fun P Q => w P Q ρ) (fun P Q => F P Q μ ν) B A := by
    simp only [act, ← Finset.sum_neg_distrib]
    sc
    rename_i K _
    rw [hF K A μ ν, hF B K μ ν]
    ring
  simp only [covTermArr]
  rw [e1, hdF ρ A B μ ν]
  ring

/-- The `ε`-contraction of the Euler residual: `Σ ε^{μνρσ} (D F)^{AB}_{μνρ} = 3 Zf`. -/
theorem sum_eps_covD (ω : Pt → Arr3) (F : Pt → Arr4) (x : Pt) (A B σ : Fin 4) :
    ∑ μ, ∑ ν, ∑ ρ, leviCivita μ ν ρ σ * covD ω F x A B μ ν ρ =
      3 * Zf (F x) (dArr4 F x) (ω x) A B σ := by
  simp only [covD]
  exact sum_eps_cyclic σ (fun a b c => covTerm ω F x a b c A B)

/-! ## The fundamental lemma of the calculus of variations on an open chart domain -/

theorem eq_zero_on_of_integral_mul_eq_zero {U : Set Pt} (hU : IsOpen U) {f : Pt → ℝ}
    (hf : Continuous f)
    (h : ∀ ψ : Pt → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ψ x * f x = 0) :
    ∀ x ∈ U, f x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrable.locallyIntegrableOn U)
    (fun g hg hgc hgU => by simpa [smul_eq_mul] using h g hg hgc hgU)
  intro x hx
  by_contra hne
  have hW : IsOpen (U ∩ {y | f y ≠ 0}) := hU.inter (isOpen_ne_fun hf continuous_const)
  have h0 : MeasureTheory.volume (U ∩ {y | f y ≠ 0}) = 0 := by
    rw [MeasureTheory.ae_iff] at hae
    refine MeasureTheory.measure_mono_null ?_ hae
    intro y hy hy'
    exact hy.2 (hy' hy.1)
  exact hW.measure_ne_zero MeasureTheory.volume ⟨x, hx, hne⟩ h0

/-! ## Connection stationarity ⟹ Euler equation ⟹ `T = 0` -/

theorem continuous_Zf (α β : ℝ) {e : Pt → Fin 4 → Fin 4 → ℝ} {ω : Pt → Arr3}
    (he : ContDiff ℝ 1 e) (hω : Continuous ω) (A B σ : Fin 4) :
    Continuous (fun x => Zf (PB α β e x) (dArr4 (PB α β e) x) (ω x) A B σ) := by
  have hPBc := (contDiff_PB α β he).continuous
  have hdPB := continuous_dArr4 (contDiff_PB α β he)
  unfold Zf covTermArr act
  fun_prop

theorem dArr4_PB_antisymm (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (x : Pt) (ρ A B μ ν : Fin 4) :
    dArr4 (PB α β e) x ρ A B μ ν = -dArr4 (PB α β e) x ρ B A μ ν := by
  simp only [dArr4]
  rw [show (fun y => PB α β e y A B μ ν) = fun y => -PB α β e y B A μ ν from
    funext fun y => PB_antisymm_internal α β e y A B μ ν, pd_neg]

/-- **The spinless connection Euler equation is `D(P_{α,β} B) = 0`.**  If the Palatini–Holst
action is stationary on the open chart domain `U` under all smooth, compactly supported,
`so(1,3)`-valued connection variations (`IsConnectionStationary`), then the Euler residual
`D(P_{α,β} B)` vanishes at every point of `U`.  (Coframe and Lorentz connection of class `C¹`.) -/
theorem eulerResidual_eq_zero_of_isConnectionStationary {α β lam : ℝ}
    {e : Pt → Fin 4 → Fin 4 → ℝ} {ω : Pt → Arr3} (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω)
    (hωL : ∀ x ρ, IsLorentz (fun P Q => ω x P Q ρ)) {U : Set Pt} (hU : IsOpen U)
    (hstat : IsConnectionStationary α β lam e ω U) :
    ∀ x ∈ U, eulerResidual α β e ω x = 0 := by
  have hZ : ∀ a b s, ∀ x ∈ U, Zf (PB α β e x) (dArr4 (PB α β e) x) (ω x) a b s = 0 := by
    intro a b s
    refine eq_zero_on_of_integral_mul_eq_zero hU (continuous_Zf α β he hω.continuous a b s) ?_
    intro ψ hψ hψc hψU
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hadm : IsLorentzVariation U (fun y => ψ y • testCoeff a b s) :=
      { smooth := hψ.smul contDiff_const
        compact := hψc.smul_right
        subset := (tsupport_smul_subset_left _ _).trans hψU
        lorentz := fun x σ => by
          intro P Q
          have := testCoeff_isLorentz a b s σ P Q
          simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
          linear_combination ψ x * this }
    have h0 := hstat _ hadm
    have hδ1 : ContDiff ℝ 1 (fun y => ψ y • testCoeff a b s) := hψ1.smul contDiff_const
    rw [deriv_relAction (δ := fun y => ψ y • testCoeff a b s) α β lam he hω hδ1 hadm.compact
      hadm.subset, integral_firstVarDensity_smul_const α β he hω.continuous hψ1 hψc] at h0
    have hE : ∀ x, ψ x * eulerDensity (PB α β e x) (dArr4 (PB α β e) x) (ω x) (testCoeff a b s)
        = -4 * (ψ x * Zf (PB α β e x) (dArr4 (PB α β e) x) (ω x) a b s) := by
      intro x
      rw [eulerDensity_testCoeff _ _ (hωL x),
        Zf_antisymm _ _ _ (fun A B μ ν => PB_antisymm_internal α β e x A B μ ν)
          (dArr4_PB_antisymm α β e x) b a s]
      ring
    simp_rw [hE] at h0
    rw [MeasureTheory.integral_const_mul] at h0
    linarith
  intro x hx
  rw [eulerResidual_eq_covD]
  have hX : ∀ A B, (fun μ ν ρ => covD ω (PB α β e) x A B μ ν ρ) = 0 := by
    intro A B
    refine eq_zero_of_eps_contract _
      (fun μ ν ρ => covD_swap12 ω (PB_antisymm_form α β e) x A B μ ν ρ)
      (fun μ ν ρ => covD_swap23 ω (PB_antisymm_form α β e) x A B μ ν ρ) (fun σ => ?_)
    rw [sum_eps_covD, hZ A B σ x hx, mul_zero]
  funext A B μ ν ρ
  exact congrFun (congrFun (congrFun (hX A B) μ) ν) ρ

/-- **Connection stationarity implies `T = 0`** (`thm:supp-palatini-torsion`): for
`(α, β) ≠ (0, 0)`, a `C¹` coframe nondegenerate on `U` and a `C¹` Lorentz connection, stationarity
of the Palatini–Holst action under compactly supported Lorentz variations in `U` forces the
torsion `T = De` to vanish on `U`. -/
theorem torsion_eq_zero_of_isConnectionStationary {α β lam : ℝ} (hαβ : (α, β) ≠ (0, 0))
    {e : Pt → Fin 4 → Fin 4 → ℝ} {ω : Pt → Arr3} (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω)
    (hωL : ∀ x ρ, IsLorentz (fun P Q => ω x P Q ρ)) {U : Set Pt} (hU : IsOpen U)
    (hdet : ∀ x ∈ U, IsUnit (Matrix.det (e x : Matrix (Fin 4) (Fin 4) ℝ)))
    (hstat : IsConnectionStationary α β lam e ω U) :
    ∀ x ∈ U, torsion e ω x = 0 := by
  intro x hx
  have hed := he.differentiable one_ne_zero
  exact torsion_eq_zero_of_euler hαβ e ω x (fun I μ => by fun_prop) (hdet x hx) (hωL x)
    (eulerResidual_eq_zero_of_isConnectionStationary he hω hωL hU hstat x hx)

/-! ## The converse: the Euler equation implies stationarity (non-vacuity) -/

/-- Standard basis of three-index arrays. -/
def basisE (i : Fin 4 × Fin 4 × Fin 4) : Arr3 := fun A B σ => kd A i.1 * kd B i.2.1 * kd σ i.2.2

theorem sum_basisE (G : Fin 4 × Fin 4 × Fin 4 → ℝ) (A B σ : Fin 4) :
    ∑ i, G i * basisE i A B σ = G (A, B, σ) := by
  rw [Finset.sum_eq_single (A, B, σ)]
  · simp [basisE, kd]
  · rintro ⟨a, b, s⟩ _ hi
    simp only [basisE, kd]
    split_ifs <;> simp_all
  · simp

theorem linCurv_add (w d d' : Arr3) (dd dd' : Fin 4 → Arr3) :
    linCurv w (d + d') (dd + dd') = linCurv w d dd + linCurv w d' dd' := by
  funext A B ρ σ
  simp only [linCurv, algCurv, Pi.add_apply, Fin.sum_univ_four]
  ring

theorem linCurv_sum {ι : Type*} (w : Arr3) (s : Finset ι) (d : ι → Arr3)
    (dd : ι → Fin 4 → Arr3) :
    linCurv w (∑ i ∈ s, d i) (∑ i ∈ s, dd i) = ∑ i ∈ s, linCurv w (d i) (dd i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linCurv_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, linCurv_add, ih]

theorem pairing_sum {ι : Type*} (F : Arr4) (s : Finset ι) (R : ι → Arr4) :
    pairing F (∑ i ∈ s, R i) = ∑ i ∈ s, pairing F (R i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairing_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairing_add, ih]

/-- The first-variation density is the sum of its values along the basis directions. -/
theorem firstVarDensity_eq_sum_basis (α β : ℝ) (e : Pt → Fin 4 → Fin 4 → ℝ) (ω : Pt → Arr3)
    {δ : Pt → Arr3} (hδ : ContDiff ℝ 1 δ) (x : Pt) :
    firstVarDensity α β e ω δ x =
      ∑ i, firstVarDensity α β e ω (fun y => δ y i.1 i.2.1 i.2.2 • basisE i) x := by
  have hd : ∀ i : Fin 4 × Fin 4 × Fin 4,
      Differentiable ℝ (fun y => δ y i.1 i.2.1 i.2.2) := fun i =>
    (contDiff_comp3 hδ i.1 i.2.1 i.2.2).differentiable one_ne_zero
  have h1 : δ x = ∑ i, δ x i.1 i.2.1 i.2.2 • basisE i := by
    funext A B σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (sum_basisE (fun i => δ x i.1 i.2.1 i.2.2) A B σ).symm
  have h2 : dArr3 δ x = ∑ i, fun ρ => pd ρ (fun y => δ y i.1 i.2.1 i.2.2) x • basisE i := by
    funext ρ A B σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (sum_basisE (fun i => pd ρ (fun y => δ y i.1 i.2.1 i.2.2) x) A B σ).symm
  simp only [firstVarDensity]
  simp only [dArr3_smul_const ((hd _) x)]
  rw [h1, h2, linCurv_sum, pairing_sum, Finset.sum_div]
  simp only [← h1]

/-- **Converse (`D(P_{α,β}B) = 0` on `U` ⟹ stationarity)**: if the Euler residual vanishes on `U`
then the Palatini–Holst action is connection-stationary on `U`.  Together with
`eulerResidual_eq_zero_of_isConnectionStationary` this identifies `D(P_{α,β} B) = 0` as exactly
the spinless connection Euler equation. -/
theorem isConnectionStationary_of_eulerResidual_eq_zero {α β lam : ℝ}
    {e : Pt → Fin 4 → Fin 4 → ℝ} {ω : Pt → Arr3} (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω)
    (hωL : ∀ x ρ, IsLorentz (fun P Q => ω x P Q ρ)) {U : Set Pt}
    (hE : ∀ x ∈ U, eulerResidual α β e ω x = 0) :
    IsConnectionStationary α β lam e ω U := by
  intro δ hδ
  have hδ1 : ContDiff ℝ 1 δ := hδ.smooth.of_le (by exact_mod_cast le_top)
  rw [deriv_relAction α β lam he hω hδ1 hδ.compact hδ.subset]
  have hψ : ∀ i : Fin 4 × Fin 4 × Fin 4, ContDiff ℝ 1 (fun y => δ y i.1 i.2.1 i.2.2) :=
    fun i => contDiff_comp3 hδ1 i.1 i.2.1 i.2.2
  have hψc : ∀ i : Fin 4 × Fin 4 × Fin 4, HasCompactSupport (fun y => δ y i.1 i.2.1 i.2.2) :=
    fun i => hδ.compact.comp_left (g := fun d : Arr3 => d i.1 i.2.1 i.2.2) rfl
  simp_rw [firstVarDensity_eq_sum_basis α β e ω hδ1]
  rw [MeasureTheory.integral_finsetSum
    (f := fun i x => firstVarDensity α β e ω (fun y => δ y i.1 i.2.1 i.2.2 • basisE i) x) _
    fun i _ => by
      exact integrable_firstVarDensity he hω.continuous ((hψ i).smul contDiff_const)
        (hψc i).smul_right]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_firstVarDensity_smul_const α β he hω.continuous (hψ i) (hψc i)]
  have hz : ∀ x, δ x i.1 i.2.1 i.2.2 *
      eulerDensity (PB α β e x) (dArr4 (PB α β e) x) (ω x) (basisE i) = 0 := by
    intro x
    by_cases hx : x ∈ U
    · have hZ : ∀ A B σ, Zf (PB α β e x) (dArr4 (PB α β e) x) (ω x) A B σ = 0 := by
        intro A B σ
        have h3 := sum_eps_covD ω (PB α β e) x A B σ
        rw [← eulerResidual_eq_covD, hE x hx] at h3
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h3
        linarith
      rw [eulerDensity_eq_Zf _ _ (hωL x)]
      simp [hZ]
    · have : δ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hδ.subset h)
      simp [this]
  simp [hz]

/-! ## Non-vacuity -/

/-- The identity coframe. -/
def idCoframe : Pt → Fin 4 → Fin 4 → ℝ := fun _ I μ => if I = μ then 1 else 0

/-- The identity coframe with the zero connection satisfies the stationarity hypothesis on the
whole chart (so `IsConnectionStationary` is not vacuous), and the derived Euler equation and
torsion-freeness hold. -/
example (α β lam : ℝ) (hαβ : (α, β) ≠ (0, 0)) :
    IsConnectionStationary α β lam idCoframe (fun _ => 0) Set.univ ∧
      (∀ x, eulerResidual α β idCoframe (fun _ => 0) x = 0) ∧
      (∀ x, torsion idCoframe (fun _ => 0) x = 0) := by
  have he : ContDiff ℝ 1 idCoframe := contDiff_const
  have hω : ContDiff ℝ 1 (fun _ : Pt => (0 : Arr3)) := contDiff_const
  have hωL : ∀ (x : Pt) ρ, IsLorentz (fun P Q => (fun _ : Pt => (0 : Arr3)) x P Q ρ) :=
    fun x ρ I K => by simp
  have hT : ∀ x, torsion idCoframe (fun _ => 0) x = 0 := by
    intro x; funext I μ ν; simp [torsion, pd, idCoframe]
  have hE : ∀ x, eulerResidual α β idCoframe (fun _ => 0) x = 0 := by
    intro x
    have hed : ∀ I μ, DifferentiableAt ℝ (fun y => idCoframe y I μ) x := fun I μ =>
      differentiableAt_const _
    rw [eulerResidual_eq α β _ _ x hed (hωL x), hT x]
    funext I J μ ν ρ
    simp [palatiniApply, cartan, capply]
  have hstat : IsConnectionStationary α β lam idCoframe (fun _ => 0) Set.univ :=
    isConnectionStationary_of_eulerResidual_eq_zero he hω hωL fun x _ => hE x
  refine ⟨hstat, fun x => ?_, fun x => ?_⟩
  · exact eulerResidual_eq_zero_of_isConnectionStationary he hω hωL isOpen_univ hstat x
      (Set.mem_univ x)
  · refine torsion_eq_zero_of_isConnectionStationary hαβ he hω hωL isOpen_univ ?_ hstat x
      (Set.mem_univ x)
    intro y _
    have h1 : (Matrix.of fun I μ : Fin 4 => if I = μ then (1 : ℝ) else 0) = 1 := by
      ext I μ; simp [Matrix.one_apply]
    show IsUnit (Matrix.det (Matrix.of fun I μ : Fin 4 => if I = μ then (1 : ℝ) else 0))
    rw [h1, Matrix.det_one]
    exact isUnit_one

/-- A non-trivial admissible variation exists (so the stationarity hypothesis is a genuine
constraint): any smooth bump `ψ` supported in `U` times an elementary Lorentz coefficient. -/
example {U : Set Pt} {ψ : Pt → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (a b s : Fin 4) :
    IsLorentzVariation U (fun y => ψ y • testCoeff a b s) :=
  { smooth := hψ.smul contDiff_const
    compact := hψc.smul_right
    subset := (tsupport_smul_subset_left _ _).trans hψU
    lorentz := fun x σ => by
      intro P Q
      have := testCoeff_isLorentz a b s σ P Q
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination ψ x * this }

/-! ## The packaged statement of `thm:supp-palatini-torsion` -/

/-- **`thm:supp-palatini-torsion`** (coefficient model on a chart of `ℝ⁴`).  Let
`(α, β) ≠ (0, 0)`, `e` a `C¹` coframe and `ω` a `C¹` Lorentz connection, `U` an open chart
domain.
1. `P_{α,β}^{-1} = (α I - β ⋆)/(α² + β²)` on bivectors (both sides);
2. connection stationarity of the Palatini–Holst action on `U` holds iff the spinless connection
   Euler equation `D(P_{α,β} B) = 0` holds on `U`;
3. the Cartan map `𝒦_e` is injective at every point where the coframe is nondegenerate;
4. if the coframe is nondegenerate on `U`, connection stationarity implies `T = 0` on `U`;
5. at any point, a lower singular-value bound `κ‖v‖ ≤ ‖𝒦_e v‖` gives
   `‖T‖ ≤ κ⁻¹ ‖P_{α,β}^{-1}‖ ‖D(P_{α,β} B)‖`. -/
theorem palatini_torsion_exact {α β lam : ℝ} (hαβ : (α, β) ≠ (0, 0))
    {e : Pt → Fin 4 → Fin 4 → ℝ} {ω : Pt → Arr3} (he : ContDiff ℝ 1 e) (hω : ContDiff ℝ 1 ω)
    (hωL : ∀ x ρ, IsLorentz (fun P Q => ω x P Q ρ)) {U : Set Pt} (hU : IsOpen U) :
    (∀ b : Fin 4 → Fin 4 → ℝ, IsAntisymm b →
        capply (inverseC α β) (capply (palatiniC α β) b) = b ∧
          capply (palatiniC α β) (capply (inverseC α β) b) = b) ∧
      (IsConnectionStationary α β lam e ω U ↔ ∀ x ∈ U, eulerResidual α β e ω x = 0) ∧
      (∀ x, IsUnit (Matrix.det (e x : Matrix (Fin 4) (Fin 4) ℝ)) →
        ∀ T : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, T I μ ν = -T I ν μ) →
          cartan (e x) T = 0 → T = 0) ∧
      ((∀ x ∈ U, IsUnit (Matrix.det (e x : Matrix (Fin 4) (Fin 4) ℝ))) →
        IsConnectionStationary α β lam e ω U → ∀ x ∈ U, torsion e ω x = 0) ∧
      (∀ x (κ : ℝ), 0 < κ → (∀ v : Fin 4 → Fin 4 → Fin 4 → ℝ, (∀ I μ ν, v I μ ν = -v I ν μ) →
          κ * ‖v‖ ≤ ‖cartan (e x) v‖) →
        ‖torsion e ω x‖ ≤ κ⁻¹ * (‖inverseApplyCLM α β‖ * ‖eulerResidual α β e ω x‖)) := by
  have hs := sq_add_sq_ne_zero hαβ
  have hed := he.differentiable one_ne_zero
  refine ⟨fun b hb => ⟨inverseC_palatiniC hs hb, palatiniC_inverseC hs hb⟩,
    ⟨eulerResidual_eq_zero_of_isConnectionStationary he hω hωL hU,
      isConnectionStationary_of_eulerResidual_eq_zero he hω hωL⟩,
    fun x hx T hT hK => cartan_injective_of_isUnit_det (e x) hx hT hK,
    fun hdet hstat => torsion_eq_zero_of_isConnectionStationary hαβ he hω hωL hU hdet hstat,
    fun x κ hκ hfloor => norm_torsion_le_residual' hαβ e ω x (fun I μ => by fun_prop) (hωL x) κ hκ
      hfloor⟩

end RenewalGeometry.PalatiniHolstVariation
