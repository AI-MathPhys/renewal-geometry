/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LogarithmicSiteGaugeDifferential
import RenewalGeometry.GaugeTheory.LogarithmicFaddeevPopovInverse
import RenewalGeometry.GaugeTheory.CoulombAprioriEstimate

/-!
# Algebra of the Coulomb homotopy: transport of the Faddeev–Popov operator, skewness, and the
  chain rule with unitary gauges (for `thm:finite-Coulomb-normalization`, Einstein–SM action
  closure)

Setting.  The gauge group is the unitary group of a C*-algebra `𝔸` (for `U(N)`: `N × N`
complex matrices with the operator norm; for `U(3) × U(2)`: block matrices), its Lie algebra the
skew-adjoint elements `star a = -a`, and the invariant Lie-algebra metric is carried by a real
inner product space `E` with a linear identification `toE : 𝔸 ≃L[ℝ] E` (for matrices: the
Frobenius inner product `Re tr(X^* Y)`).  The bracket on `E` is the transported commutator
`brE toE a v = toE [toE⁻¹ a, toE⁻¹ v]`.

* Generic transport (`map_dexpJ`, `map_exp'`, `map_ringInverse`, `map_halfCoth`): continuous
  `ℝ`-linear multiplicative maps commute with `𝒥`, `exp`, inverses and `𝒦(Z) = (Z/2)coth(Z/2)`;
  `commute_halfCoth`: an element commuting with `Z` commutes with `𝒦(Z)`.
* `toE_gaugeFlux`: the `𝔸`-valued logarithmic gauge flux of `lem:native-log-gauge-differential`
  read in `E` is exactly the flux of the Faddeev–Popov operator `eq:native-FP` with the bracket
  `brE toE`.
* `fp_solution_skew`: on a skew-adjoint connection, the mean-zero solution of `M_A ξ = δ_h R` with
  skew-adjoint `R` is skew-adjoint (uniqueness of `lem:native-FP-inverse` and the symmetry
  `X ↦ -X^*`), and `ringInverse_dexpJ_skew`: `𝒥(h ad_A)⁻¹` preserves skew-adjointness.
* `homotopy_derivative_star`: the exact chain rule of the Coulomb homotopy
  (`eq:native-Coulomb-homotopy-ODE`) for unitary gauges written with `q⁻¹ = q^*` and one-sided
  derivatives within an arbitrary set.
* `logChart_skew`: the chart logarithm of a unitary near `1` is skew-adjoint.
-/

open NormedSpace Filter Topology Finset

namespace RenewalGeometry.CoulombHomotopy

open OperatorHalfCoth MatrixExpDerivative SeriesLogChart GridSobolev LogGaugeDifferential

noncomputable section

/-! ### Transport by multiplicative continuous linear maps -/

section Transport

variable {𝔹 𝔹' : Type*} [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] [CompleteSpace 𝔹] [NormOneClass 𝔹]
  [NormedRing 𝔹'] [NormedAlgebra ℝ 𝔹'] [CompleteSpace 𝔹'] [NormOneClass 𝔹']

theorem map_pow_of_mul (φ : 𝔹 →L[ℝ] 𝔹') (hmul : ∀ x y, φ (x * y) = φ x * φ y) (h1 : φ 1 = 1)
    (Z : 𝔹) (k : ℕ) : φ (Z ^ k) = φ Z ^ k := by
  induction k with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, hmul, ih, pow_succ]

theorem map_dexpJ (φ : 𝔹 →L[ℝ] 𝔹') (hmul : ∀ x y, φ (x * y) = φ x * φ y) (h1 : φ 1 = 1)
    (Z : 𝔹) : φ (dexpJ Z) = dexpJ (φ Z) := by
  have h := (hasSum_dexpJ Z).mapL φ
  refine h.unique ((hasSum_dexpJ (φ Z)).congr_fun fun k => ?_)
  rw [map_smul, map_pow_of_mul φ hmul h1]

theorem map_exp' (φ : 𝔹 →L[ℝ] 𝔹') (hmul : ∀ x y, φ (x * y) = φ x * φ y) (h1 : φ 1 = 1)
    (Z : 𝔹) : φ (exp Z) = exp (φ Z) := by
  have h := (exp_series_hasSum_exp' (𝕂 := ℝ) Z).mapL φ
  refine h.unique ((exp_series_hasSum_exp' (𝕂 := ℝ) (φ Z)).congr_fun fun k => ?_)
  rw [map_smul, map_pow_of_mul φ hmul h1]

theorem map_ringInverse (φ : 𝔹 →L[ℝ] 𝔹') (hmul : ∀ x y, φ (x * y) = φ x * φ y) (h1 : φ 1 = 1)
    {x : 𝔹} (hx : IsUnit x) : φ (Ring.inverse x) = Ring.inverse (φ x) := by
  have a1 : φ (Ring.inverse x) * φ x = 1 := by rw [← hmul, Ring.inverse_mul_cancel _ hx, h1]
  have a2 : φ x * φ (Ring.inverse x) = 1 := by rw [← hmul, Ring.mul_inverse_cancel _ hx, h1]
  have hu : IsUnit (φ x) := ⟨⟨φ x, φ (Ring.inverse x), a2, a1⟩, rfl⟩
  calc φ (Ring.inverse x) = Ring.inverse (φ x) * φ x * φ (Ring.inverse x) := by
        rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (φ x) := by rw [mul_assoc, a2, mul_one]

theorem map_halfCoth (φ : 𝔹 →L[ℝ] 𝔹') (hmul : ∀ x y, φ (x * y) = φ x * φ y) (h1 : φ 1 = 1)
    {Z : 𝔹} (hZ : IsUnit (dexpJ Z)) : φ (halfCoth Z) = halfCoth (φ Z) := by
  rw [halfCoth, halfCoth, hmul, map_ringInverse φ hmul h1 hZ, map_dexpJ φ hmul h1, map_smul,
    map_add, h1, map_exp' φ hmul h1]

theorem commute_dexpJ {σ Z : 𝔹} (hc : Commute σ Z) : Commute σ (dexpJ Z) := by
  have h1 := (hasSum_dexpJ Z).mul_left σ
  have h2 := (hasSum_dexpJ Z).mul_right σ
  refine h1.unique (h2.congr_fun fun k => ?_)
  rw [smul_mul_assoc, mul_smul_comm, (hc.pow_right k).eq]

theorem commute_halfCoth {σ Z : 𝔹} (hc : Commute σ Z) (hZ : IsUnit (dexpJ Z)) :
    Commute σ (halfCoth Z) := by
  obtain ⟨u, hu⟩ := hZ
  have hJ : Commute σ (u : 𝔹) := hu ▸ commute_dexpJ hc
  have hinv : Commute σ (Ring.inverse (dexpJ Z)) := by
    rw [← hu, Ring.inverse_unit]
    exact hJ.units_inv_right
  rw [halfCoth]
  exact hinv.mul_right (((Commute.one_right σ).add_right hc.exp_right).smul_right _)

end Transport

/-! ### The C*-algebra setting and the transported bracket -/

variable {𝔸 : Type*} [CStarAlgebra 𝔸] [Nontrivial 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]

theorem ringInverse_unitary {u : 𝔸} (hu : u ∈ unitary 𝔸) : Ring.inverse u = star u := by
  have hU : IsUnit u := ⟨Unitary.toUnits ⟨u, hu⟩, rfl⟩
  calc Ring.inverse u = Ring.inverse u * (u * star u) := by
        rw [Unitary.mul_star_self_of_mem hu, mul_one]
    _ = star u := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]

/-- `ad` as a continuous linear map `𝔸 →L (𝔸 →L 𝔸)`. -/
def adL : 𝔸 →L[ℝ] (𝔸 →L[ℝ] 𝔸) :=
  ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip

theorem adL_apply (X : 𝔸) : adL X = adOp X := rfl

variable (toE : 𝔸 ≃L[ℝ] E)

/-- Conjugation `T ↦ toE ∘ T ∘ toE⁻¹` of operators. -/
def conjE : (𝔸 →L[ℝ] 𝔸) →L[ℝ] (E →L[ℝ] E) :=
  (toE.arrowCongr toE).toContinuousLinearMap

theorem conjE_apply (T : 𝔸 →L[ℝ] 𝔸) (v : E) : conjE toE T v = toE (T (toE.symm v)) :=
  ContinuousLinearEquiv.arrowCongr_apply _ _ _ _

theorem conjE_mul (S T : 𝔸 →L[ℝ] 𝔸) : conjE toE (S * T) = conjE toE S * conjE toE T := by
  ext v; simp [conjE_apply]

theorem conjE_one : conjE toE (1 : 𝔸 →L[ℝ] 𝔸) = 1 := by
  ext v; simp [conjE_apply]

/-- The transported bracket `[a, v]_E = toE [toE⁻¹ a, toE⁻¹ v]`. -/
def brE : E →L[ℝ] E →L[ℝ] E :=
  (conjE toE).comp (adL.comp (toE.symm : E →L[ℝ] 𝔸))

theorem brE_apply (a v : E) : brE toE a v = toE (adOp (toE.symm a) (toE.symm v)) := by
  simp [brE, conjE_apply, adL_apply]

theorem brE_toE (a X : 𝔸) : brE toE (toE a) (toE X) = toE (adOp a X) := by
  rw [brE_apply]; simp

theorem conjE_smul_adOp (h : ℝ) (X : 𝔸) : conjE toE (h • adOp X) = h • brE toE (toE X) := by
  ext v; simp [conjE_apply, brE_apply]

theorem toE_halfCoth {h : ℝ} {X : 𝔸} (hX : ‖h • X‖ ≤ 1 / 8) (v : 𝔸) :
    toE (halfCoth (h • adOp X) v) = halfCoth (h • brE toE (toE X)) (toE v) := by
  have hJ : IsUnit (dexpJ (h • adOp X)) := by
    have := isUnit_dexpJ_adOp_of_norm_le (h • X) hX
    rwa [adOp_smul] at this
  have := map_halfCoth (conjE toE) (conjE_mul toE) (conjE_one toE) hJ
  rw [conjE_smul_adOp] at this
  have h2 := congrArg (fun T : E →L[ℝ] E => T (toE v)) this
  simpa [conjE_apply] using h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem toE_gridFwd (h : ℝ) (μ : ι) (ξ : (ι → ZMod n) → 𝔸) (x : ι → ZMod n) :
    toE (gridFwd h μ ξ x) = gridFwd h μ (fun y => toE (ξ y)) x := by
  simp [gridFwd, map_sub, map_smul]

theorem toE_midAvg (μ : ι) (ξ : (ι → ZMod n) → 𝔸) (x : ι → ZMod n) :
    toE (midAvgA μ ξ x) = FaddeevPopov.midAvg μ (fun y => toE (ξ y)) x := by
  simp [midAvgA, FaddeevPopov.midAvg, map_add, map_smul]

/-- **The gauge flux read in `E` is the Faddeev–Popov flux** (`eq:native-FP`). -/
theorem toE_gaugeFlux {h : ℝ} (A : ι → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) (hA : ‖h • A μ x‖ ≤ 1 / 8) :
    toE (gaugeFlux h A ξ μ x) =
      FaddeevPopov.fpFlux (brE toE) h (fun ν y => toE (A ν y)) (fun y => toE (ξ y)) μ x := by
  simp only [gaugeFlux, FaddeevPopov.fpFlux, map_add, toE_halfCoth toE hA, toE_gridFwd,
    ← toE_midAvg, brE_toE]

/-! ### The symmetry `X ↦ -X^*` and skewness -/

/-- `σ(X) = -X^*` on `𝔸`. -/
def sigmaA : 𝔸 →L[ℝ] 𝔸 := -((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)

theorem sigmaA_apply (X : 𝔸) : sigmaA X = -star X := rfl

theorem commute_sigmaA_adOp {a : 𝔸} (ha : star a = -a) : Commute sigmaA (adOp a) := by
  ext X
  simp only [ContinuousLinearMap.mul_apply, sigmaA_apply, adOp_apply, star_sub, star_mul, ha]
  noncomm_ring

/-- `σ_E = toE ∘ σ ∘ toE⁻¹`. -/
def sigmaE : E →L[ℝ] E := conjE toE sigmaA

theorem sigmaE_apply (v : E) : sigmaE toE v = toE (-star (toE.symm v)) := by
  rw [sigmaE, conjE_apply, sigmaA_apply]

theorem commute_sigmaE_brE {a : 𝔸} (ha : star a = -a) (h : ℝ) :
    Commute (sigmaE toE) (h • brE toE (toE a)) := by
  rw [sigmaE, ← conjE_smul_adOp]
  have := ((commute_sigmaA_adOp ha).smul_right h)
  have e := congrArg (conjE toE) this.eq
  rw [conjE_mul, conjE_mul] at e
  exact e

/-- `𝒥(h ad_a)⁻¹` maps skew-adjoint elements to skew-adjoint elements (`a` skew, `‖h a‖ ≤ 1/8`). -/
theorem ringInverse_dexpJ_skew {a : 𝔸} (ha : star a = -a) {h : ℝ} (hX : ‖h • a‖ ≤ 1 / 8)
    {w : 𝔸} (hw : star w = -w) :
    star (Ring.inverse (dexpJ (h • adOp a)) w) = -(Ring.inverse (dexpJ (h • adOp a)) w) := by
  have hJ : IsUnit (dexpJ (h • adOp a)) := by
    have := isUnit_dexpJ_adOp_of_norm_le (h • a) hX
    rwa [adOp_smul] at this
  obtain ⟨u, hu⟩ := hJ
  have hc : Commute sigmaA (dexpJ (h • adOp a)) :=
    commute_dexpJ ((commute_sigmaA_adOp ha).smul_right h)
  have hinv : Commute sigmaA (Ring.inverse (dexpJ (h • adOp a))) := by
    rw [← hu, Ring.inverse_unit]; exact (hu ▸ hc).units_inv_right
  have e := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T w) hinv.eq
  simp only [ContinuousLinearMap.mul_apply, sigmaA_apply] at e
  rw [show -star w = w by rw [hw, neg_neg]] at e
  rw [← neg_neg (star _), e]

variable [NeZero n]

theorem sigmaE_codiff (h : ℝ) (W : ι → (ι → ZMod n) → E) :
    (fun x => sigmaE toE (periodicHodgeCodiff h gridStep W x)) =
      periodicHodgeCodiff h gridStep (fun μ y => sigmaE toE (W μ y)) := by
  funext x
  simp [periodicHodgeCodiff, periodicHodgeBwd, map_neg, map_sum, map_smul, map_sub]

/-- `M_A` commutes with `σ_E` on a skew-adjoint connection. -/
theorem fpOp_sigma (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (hA : ∀ μ x, star (A μ x) = -A μ x)
    (hU : ∀ μ x, IsUnit (dexpJ (h • brE toE (toE (A μ x))))) (ξ : (ι → ZMod n) → E) :
    FaddeevPopov.fpOp (brE toE) h (fun μ y => toE (A μ y)) (fun y => sigmaE toE (ξ y)) =
      fun x => sigmaE toE (FaddeevPopov.fpOp (brE toE) h (fun μ y => toE (A μ y)) ξ x) := by
  unfold FaddeevPopov.fpOp
  rw [sigmaE_codiff]
  congr 1
  funext μ x
  have hc := commute_sigmaE_brE toE (hA μ x) h
  have hK := commute_halfCoth hc (hU μ x)
  have hfwd : gridFwd h μ (fun y => sigmaE toE (ξ y)) x = sigmaE toE (gridFwd h μ ξ x) := by
    simp [gridFwd, map_sub, map_smul]
  have hmid : FaddeevPopov.midAvg μ (fun y => sigmaE toE (ξ y)) x =
      sigmaE toE (FaddeevPopov.midAvg μ ξ x) := by
    simp [FaddeevPopov.midAvg, map_add, map_smul]
  have hbr : brE toE (toE (A μ x)) (sigmaE toE (FaddeevPopov.midAvg μ ξ x)) =
      sigmaE toE (brE toE (toE (A μ x)) (FaddeevPopov.midAvg μ ξ x)) := by
    have := congrArg (fun T : E →L[ℝ] E => T (FaddeevPopov.midAvg μ ξ x))
      (commute_sigmaE_brE toE (hA μ x) 1).eq
    simpa using this.symm
  simp only [FaddeevPopov.fpFlux, hfwd, hmid, hbr, map_add]
  congr 1
  have := congrArg (fun T : E →L[ℝ] E => T (gridFwd h μ ξ x)) hK.eq
  simpa using this.symm

theorem sigmaE_eq_iff (v : E) : sigmaE toE v = v ↔ star (toE.symm v) = -(toE.symm v) := by
  rw [sigmaE_apply]
  constructor
  · intro hv
    have := congrArg toE.symm hv
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    exact neg_eq_iff_eq_neg.1 this
  · intro hv
    rw [hv, neg_neg, ContinuousLinearEquiv.apply_symm_apply]

/-- **Skewness of the transverse solution**: if `A` and `R` are skew-adjoint and `‖A_μ‖_{4,h}` is
below the Faddeev–Popov threshold, the mean-zero solution of `M_A ξ = δ_h R` is skew-adjoint. -/
theorem fp_solution_skew (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (A R : ι → (ι → ZMod n) → 𝔸) (hA : ∀ μ x, star (A μ x) = -A μ x)
    (hR : ∀ μ x, star (R μ x) = -R μ x)
    (hsmall : ∀ μ, gridL4Norm h (fun y => toE (A μ y)) < FaddeevPopov.rFP (brE toE))
    (ξ : (ι → ZMod n) → E) (hξ : ∑ x, ξ x = 0)
    (hM : FaddeevPopov.fpOp (brE toE) h (fun μ y => toE (A μ y)) ξ =
      periodicHodgeCodiff h gridStep (fun μ y => toE (R μ y))) :
    ∀ x, star (toE.symm (ξ x)) = -(toE.symm (ξ x)) := by
  have hU : ∀ μ x, IsUnit (dexpJ (h • brE toE (toE (A μ x)))) := fun μ x =>
    (dexpJ_isUnit_and_norm_inverse_le _ (FaddeevPopov.chart_of_small hι (brE toE) hh
      (fun μ y => toE (A μ y)) hsmall μ x).le).1
  have hσR : (fun μ y => sigmaE toE (toE (R μ y))) = fun μ y => toE (R μ y) := by
    funext μ y
    rw [sigmaE_eq_iff, ContinuousLinearEquiv.symm_apply_apply]
    exact hR μ y
  obtain ⟨ξ₀, _, huniq⟩ := FaddeevPopov.fp_bijective hι (brE toE) hh
    (fun μ y => toE (A μ y)) hsmall (periodicHodgeCodiff h gridStep (fun μ y => toE (R μ y)))
    (FaddeevPopov.sum_codiff h _)
  have h1 := huniq ξ ⟨hξ, hM⟩
  have h2 := huniq (fun y => sigmaE toE (ξ y)) ⟨by
      rw [← map_sum, hξ, map_zero], by
      rw [fpOp_sigma toE h A hA hU ξ, hM, sigmaE_codiff, hσR]⟩
  intro x
  rw [← sigmaE_eq_iff]
  have := congrFun (h2.trans h1.symm) x
  exact this

/-! ### Unitary links: skew logarithms and the chain rule -/

/-- The chart logarithm of a unitary near `1` is skew-adjoint. -/
theorem logChart_skew {P : 𝔸} (hP : P ∈ unitary 𝔸) (h1 : ‖P - 1‖ ≤ 1 / 64) :
    star (logChart P) = -logChart P := by
  have hL : ‖logChart P‖ ≤ 1 / 32 :=
    (norm_logChart_le (P := P) (by linarith)).trans (by linarith)
  have hstar : ‖star P - 1‖ < 1 := by
    rw [show star P - 1 = star (P - 1) by rw [star_sub, star_one], norm_star]; linarith
  have e1 : star P = exp (-logChart P) := by
    have hm : exp (-logChart P) * P = 1 := by
      have := exp_neg_mul_exp (logChart P)
      rwa [exp_logChart (P := P) (by linarith)] at this
    calc star P = exp (-logChart P) * P * star P := by rw [hm, one_mul]
      _ = exp (-logChart P) := by rw [mul_assoc, Unitary.mul_star_self_of_mem hP, mul_one]
  have := logChart_star (by linarith) hstar
  rw [e1, logChart_exp (by rwa [norm_neg])] at this
  exact this.symm

theorem hasDerivWithinAt_log_comp' (X : 𝔸) (hJ : IsUnit (dexpJ (adOp X))) {Log : 𝔸 → 𝔸}
    (hLog : ∀ᶠ Y in 𝓝 X, Log (exp Y) = Y) {γ : ℝ → 𝔸} {γ' : 𝔸} {S : Set ℝ} {s : ℝ}
    (hγ : HasDerivWithinAt γ γ' S s) (hs : γ s = exp X) :
    HasDerivWithinAt (fun t => Log (γ t)) (Ring.inverse (dexpJ (adOp X)) (γ' * exp (-X))) S s := by
  have := (hasStrictFDerivAt_log_of_eventually X hJ hLog).hasFDerivAt.comp_hasDerivWithinAt_of_eq
    s hγ hs.symm
  simp only [ContinuousLinearEquiv.coe_coe, dexpCLE_symm_apply] at this
  exact this

/-- **The exact chain rule of the Coulomb homotopy for unitary gauges** (one-sided form): if
`q̇_y = ξ_y q_y` within `S` at `s₀` with skew-adjoint `ξ`, the gauges `q_y(s₀)` are unitary, the
chart inverts `exp` near `h A_μ(x)` with `q_x e^{s₀hB} q_{x+μ}^* = e^{hA_μ(x)}`, and `𝒥(h ad_A)` is
invertible, then `d/ds h⁻¹ Log(q_x e^{shB} q_{x+μ}^*) = 𝒥(h ad_A)⁻¹ (q_x B q_x^*) -
(𝒦(h ad_A) D^+ξ + [A, m ξ])`. -/
theorem homotopy_derivative_star (Log : 𝔸 → 𝔸) {h : ℝ} (hh : h ≠ 0)
    (B : ι → (ι → ZMod n) → 𝔸) (q : ℝ → (ι → ZMod n) → 𝔸) (ξ : (ι → ZMod n) → 𝔸) {S : Set ℝ}
    (s₀ : ℝ) (A : ι → (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n)
    (hq : ∀ y, HasDerivWithinAt (fun s => q s y) (ξ y * q s₀ y) S s₀)
    (hξ : ∀ y, star (ξ y) = -ξ y) (hu : ∀ y, q s₀ y ∈ unitary 𝔸)
    (hA : q s₀ x * exp (s₀ • (h • B μ x)) * star (q s₀ (x + gridStep μ)) = exp (h • A μ x))
    (hLog : ∀ᶠ Y in 𝓝 (h • A μ x), Log (exp Y) = Y) (hJ : IsUnit (dexpJ (h • adOp (A μ x)))) :
    HasDerivWithinAt (fun s => h⁻¹ • Log (q s x * exp (s • (h • B μ x)) *
        star (q s (x + gridStep μ))))
      (Ring.inverse (dexpJ (h • adOp (A μ x))) (q s₀ x * B μ x * star (q s₀ x)) -
        gaugeFlux h A ξ μ x) S s₀ := by
  set y := x + gridStep μ
  set E' := exp (s₀ • (h • B μ x))
  set Qi := star (q s₀ y)
  set Qx := star (q s₀ x)
  have hQ : q s₀ y * Qi = 1 := Unitary.mul_star_self_of_mem (hu y)
  have hQx' : Qx * q s₀ x = 1 := Unitary.star_mul_self_of_mem (hu x)
  have hinv : HasDerivWithinAt (fun s => star (q s y)) (-(Qi * ξ y)) S s₀ := by
    have := (hq y).star
    rwa [star_mul, hξ, mul_neg] at this
  have hE := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (h • B μ x) s₀).hasDerivWithinAt (s := S)
  have hγ := ((hq x).mul hE).mul hinv
  have hJ' : IsUnit (dexpJ (adOp (h • A μ x))) := by rw [adOp_smul]; exact hJ
  have hd := (hasDerivWithinAt_log_comp' (h • A μ x) hJ' hLog hγ hA).const_smul h⁻¹
  refine hd.congr_deriv ?_
  have hm := exp_mul_exp_neg (h • A μ x)
  have hγ0 : q s₀ x * E' * Qi = exp (h • A μ x) := hA
  have hEQ : E' * Qi * exp (-(h • A μ x)) = Qx := by
    have h2 : q s₀ x * (E' * Qi * exp (-(h • A μ x))) = 1 := by
      rw [← mul_assoc, ← mul_assoc, hγ0, hm]
    calc E' * Qi * exp (-(h • A μ x)) = Qx * (q s₀ x * (E' * Qi * exp (-(h • A μ x)))) := by
          rw [← mul_assoc, hQx', one_mul]
      _ = Qx := by rw [h2, mul_one]
  have hconj := exp_smul_adOp_apply (h • A μ x) (ξ y) 1
  rw [one_smul, one_smul] at hconj
  have key : (ξ x * q s₀ x * E' + q s₀ x * (h • B μ x * E')) * Qi +
      q s₀ x * E' * -(Qi * ξ y) = ξ x * exp (h • A μ x) + h • (q s₀ x * B μ x * (E' * Qi)) -
        exp (h • A μ x) * ξ y := by
    rw [← hγ0]
    simp only [add_mul, mul_add, mul_neg, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel
  have key2 : ((ξ x * q s₀ x * E' + q s₀ x * (h • B μ x * E')) * Qi +
      q s₀ x * E' * -(Qi * ξ y)) * exp (-(h • A μ x)) =
        h • (q s₀ x * B μ x * Qx) + (ξ x - exp (adOp (h • A μ x)) (ξ y)) := by
    rw [key, hconj, sub_mul, add_mul, mul_assoc (ξ x), hm, mul_one, smul_mul_assoc,
      mul_assoc (q s₀ x * B μ x), hEQ, mul_assoc (exp (h • A μ x))]
    abel
  change h⁻¹ • Ring.inverse (dexpJ (adOp (h • A μ x)))
    (((ξ x * q s₀ x * E' + q s₀ x * (h • B μ x * E')) * Qi + q s₀ x * E' * -(Qi * ξ y)) *
      exp (-(h • A μ x))) = _
  rw [key2, adOp_smul, map_add, smul_add, map_smul, smul_smul, inv_mul_cancel₀ hh, one_smul,
    inverse_dexpJ_gauge_identity h hh (A μ x) (ξ x) (ξ y) hJ]
  simp only [gaugeFlux, midAvgA, gridFwd]
  abel

end

end RenewalGeometry.CoulombHomotopy
