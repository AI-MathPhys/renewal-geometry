/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.FlatTorusSpinAtlas
import RenewalGeometry.OperatorLimits.SelfAdjointFromStableDiscretization

/-!
# The variable-coefficient density-symmetric Dirac operator on the periodic box

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, clause
`eq:supp-local-norm-resolvent`: the continuum operator of the fixed smooth periodic coordinate
extension,

`D̂_g = -(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j})`,  `∇_j = ∂_j + Ω_j`

(`lem:supp-density-symmetric`), on `L²(𝕋ᵈ; ℂ^K)` with domain `H¹`, for continuous periodic
Hermitian Clifford coefficients `c^j` that are differentiable along `e_j` with continuous
derivative `∂_j c^j`, and a continuous skew-Hermitian connection `Ω_j`.

* `integral_lineDeriv_eq_zero`: `∫_{𝕋ᵈ} ∂_j F = 0` (translation invariance of the Haar measure
  and differentiation under the integral sign).
* `mulMat`: multiplication by a continuous matrix field on `L²(𝕋ᵈ; ℂ^K)`; `vecL2`: continuous
  sections as `L²` vectors, `inner_vecL2`, `mulMat_vecL2`.
* Fourier coordinates for `H¹`: `V = ℓ²(ℤᵈ × Fin K)` with the compact embedding
  `FlatTorusSpinAtlas.sobolev` (relative to a fixed constant Hermitian frame `c₀`, used only to
  choose an orthonormal basis of each fibre); `derivH1 j : V → L²` is `∂_j` on `H¹`
  (`derivH1_single`: `∂_j (e^{2πik·x} v) = 2πi k_j e^{2πik·x} v`).
* `Coeffs.op : V →L L²`: `D̂_g u = Σ_j c^j (-i ∂_j u) + B u` with
  `B = -(i/2) Σ_j (∂_j c^j + c^j Ω_j + Ω_j c^j)` — the expansion of the density-symmetric form by
  the Leibniz rule (`Coeffs.op_planeWave_eq_densitySymmetric` checks it pointwise on plane waves
  against `-(i/2) Σ_j (c^j ∇_j ψ + ∇_j (c^j ψ))` with the derivative of `c^j ψ` along `e_j`).
* `Coeffs.op_symm`: **symmetry on `H¹`**, `⟪D̂_g a, b⟫ = ⟪a, D̂_g b⟫`, by integration by parts on
  plane waves and continuity.
* `sobolev_injective`, `sobolev_denseRange`, `isClosed_sobolev_image_closedBall`,
  `finCore_dense`: the properties of `H¹ ↪ L²` needed by `StableDiscretization`.
* `Coeffs.LatticeDiscretization`: self-adjoint lattice stages on `(ℤ/(n+1))ᵈ` with
  `W_h = 𝒥⁰_h`, `S_h = (𝒥⁰_h)^*`, the flat trigonometric reconstruction, the graph estimate (A2)
  and the plane-wave core condition (A3).  From it: `LatticeDiscretization.dirac`, **the
  self-adjoint realisation of `D̂_g` with domain `H¹`** (`dirac_domain`, `dirac_sobolev`,
  `isSelfAdjoint_dirac`), and `eq:supp-local-norm-resolvent` together with the spectral
  projection clause (`tendsto_norm_resolvent`, `tendsto_norm_spectralProjection`).
* `covStage`, `isSelfAdjoint_covStage`: the covariant Wilson operator `eq:supp-general-Wilson`
  with sampled variable coefficients and links as a self-adjoint stage operator;
  `discreteNorm_covStage_le`: (A2) from the squared Gårding estimate of `covariant_garding`;
  `Coeffs.covariantDiscretization(OfGarding)`: the covariant discretization from (A2)/(A3).
* `covVarWilson_planeWave`, `covStage_adjoint_modeVec`: the exact action of the covariant
  stage on sampled plane waves through the local symbol `covPlaneSymbol` (first step of (A3)).
* Non-vacuity: `flatDiscretization` (constant coefficients, every hypothesis derived; the Pauli
  example on `𝕋²` runs the whole chain) and `cosCoeffs` (a non-constant coefficient
  `(3 + 2 cos 2πx) I`).

Not done here: (A2) and (A3) for the covariant stages with genuinely variable coefficients
(the hypotheses of `Coeffs.covariantDiscretizationOfGarding`).
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus Filter Topology Matrix
open scoped BigOperators Real ENNReal InnerProductSpace lp

noncomputable section

namespace RenewalGeometry.VariableTorusDirac

open FlatTorusSpinAtlas

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {d K : ℕ}

/-! ### Integration by parts on the torus -/

/-- The point `t e_j` of the torus. -/
def lineVec (j : Fin d) (t : ℝ) : UnitAddTorus (Fin d) := Pi.single j (t : UnitAddCircle)

theorem lineVec_add (j : Fin d) (s t : ℝ) : lineVec j (s + t) = lineVec j s + lineVec j t := by
  unfold lineVec
  rw [AddCircle.coe_add, Pi.single_add]

theorem continuous_lineVec (j : Fin d) : Continuous (lineVec (d := d) j) := by
  unfold lineVec
  exact continuous_pi fun i => by
    by_cases h : i = j
    · subst h; simpa using (AddCircle.continuous_mk' (1 : ℝ))
    · simp only [Pi.single_apply, h, ite_false]; exact continuous_const

/-- **`∫_{𝕋ᵈ} ∂_j F = 0`** for a continuous `F` with continuous derivative `F'` along `e_j`. -/
theorem integral_lineDeriv_eq_zero {F F' : UnitAddTorus (Fin d) → ℂ} (j : Fin d)
    (hF : Continuous F) (hF' : Continuous F')
    (hder : ∀ y, HasDerivAt (fun t : ℝ => F (y + lineVec j t)) (F' y) 0) :
    ∫ y, F' y = 0 := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖F' y‖ ≤ C :=
    ⟨‖(⟨F', hF'⟩ : C(UnitAddTorus (Fin d), ℂ))‖, fun y =>
      (⟨F', hF'⟩ : C(UnitAddTorus (Fin d), ℂ)).norm_coe_le_norm y⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun t y => F (y + lineVec j t)) (F' := fun t y => F' (y + lineVec j t))
    (bound := fun _ => C) Filter.univ_mem
    (Eventually.of_forall fun t =>
      (hF.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    ((hF.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      isCompact_univ |> integrableOn_univ.mp)
    ((hF'.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun y t _ => hC _) (integrable_const C)
    (Eventually.of_forall fun y t _ => by
      have h := hder (y + lineVec j t)
      have h' : HasDerivAt (fun s : ℝ => F (y + lineVec j t + lineVec j s))
          (F' (y + lineVec j t)) (t - t) := by rwa [sub_self]
      have h2 := h'.comp_sub_const t t
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp only
      rw [add_assoc, ← lineVec_add, add_sub_cancel])
  have hconst : (fun t : ℝ => ∫ y, F (y + lineVec j t)) = fun _ => ∫ y, F y := by
    funext t
    exact integral_add_right_eq_self (μ := volume) F (lineVec j t)
  have h0 := key.2
  rw [hconst] at h0
  have h1 := h0.unique (hasDerivAt_const (0 : ℝ) (∫ y, F y))
  simpa [lineVec] using h1

/-! ### Multiplication operators and continuous sections -/

/-- Multiplication by a continuous function on `L²(𝕋ᵈ)`. -/
def mulL2 (φ : C(UnitAddTorus (Fin d), ℂ)) : L2T d →L[ℂ] L2T d :=
  LinearMap.mkContinuous
    { toFun := fun g => (ContinuousMap.toLp ∞ volume ℂ φ) • g
      map_add' := fun f g => Lp.add_smul _ _ _
      map_smul' := fun c g => by
        rw [RingHom.id_apply]
        exact (Lp.smul_comm (𝕜' := ℂ) (p := ∞) (q := 2) (r := 2) c
          (ContinuousMap.toLp ∞ volume ℂ φ) g).symm }
    ‖φ‖ (fun g => by
      refine (Lp.norm_smul_le _ _).trans ?_
      gcongr
      have h1 := ContinuousMap.toLp_norm_le (p := ∞)
        (μ := (volume : Measure (UnitAddTorus (Fin d)))) (𝕜 := ℂ) (E := ℂ)
      have h2 := (ContinuousMap.toLp (E := ℂ) ∞
        (volume : Measure (UnitAddTorus (Fin d))) ℂ).le_opNorm φ
      simp only [ENNReal.toReal_top, _root_.inv_zero] at h1
      exact h2.trans (by simpa using mul_le_mul_of_nonneg_right h1 (norm_nonneg φ)))

/-- `L²` class of a continuous function. -/
abbrev toL2 (φ : C(UnitAddTorus (Fin d), ℂ)) : L2T d := ContinuousMap.toLp 2 volume ℂ φ

theorem mulL2_toL2 (φ ψ : C(UnitAddTorus (Fin d), ℂ)) : mulL2 φ (toL2 ψ) = toL2 (φ * ψ) := by
  have e : mulL2 φ (toL2 ψ) = ((ContinuousMap.toLp ∞ volume ℂ φ) • toL2 ψ : L2T d) := rfl
  rw [e]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (ContinuousMap.toLp ∞ volume ℂ φ) (toL2 ψ),
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) volume φ,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume ψ,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (φ * ψ)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.smul_apply', h2, h3]
  rfl

/-- A component of a continuous vector field. -/
def compCM (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) (a : Fin K) : C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => Φ x a, (continuous_apply a).comp Φ.continuous⟩

/-- A continuous section `Φ : 𝕋ᵈ → ℂ^K` as a vector of `L²(𝕋ᵈ; ℂ^K)`. -/
def vecL2 (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) : SpinorL2 d K :=
  WithLp.toLp 2 fun a => toL2 (compCM Φ a)

theorem vecL2_apply (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) (a : Fin K) :
    vecL2 Φ a = toL2 (compCM Φ a) := rfl

theorem integrable_of_continuous {f : UnitAddTorus (Fin d) → ℂ} (hf : Continuous f) :
    Integrable f :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

/-- `⟪Φ, Ψ⟫_{L²} = ∫ Σ_a conj(Φ_a) Ψ_a`. -/
theorem inner_vecL2 (Φ Ψ : C(UnitAddTorus (Fin d), Fin K → ℂ)) :
    ⟪vecL2 Φ, vecL2 Ψ⟫_ℂ = ∫ x, ∑ a, conj (Φ x a) * Ψ x a := by
  rw [PiLp.inner_apply]
  simp only [vecL2_apply, ContinuousMap.inner_toLp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [compCM, ContinuousMap.coe_mk]
    ring
  · intro a _
    exact integrable_of_continuous (Continuous.mul
      (Complex.continuous_conj.comp ((continuous_apply a).comp Φ.continuous))
      ((continuous_apply a).comp Ψ.continuous))

/-- The continuous field `x ↦ F(x) Φ(x)`. -/
def mulVecCM (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) : C(UnitAddTorus (Fin d), Fin K → ℂ) :=
  ⟨fun x => F x *ᵥ Φ x, F.continuous.matrix_mulVec Φ.continuous⟩

/-- An entry of a continuous matrix field. -/
def entryCM (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)) (a b : Fin K) :
    C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => F x a b, (continuous_apply b).comp ((continuous_apply a).comp F.continuous)⟩

/-- **Multiplication by a continuous matrix field** on `L²(𝕋ᵈ; ℂ^K)`. -/
def mulMat (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)) :
    SpinorL2 d K →L[ℂ] SpinorL2 d K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin K => L2T d)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun a => ∑ b, mulL2 (entryCM F a b) ∘L
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin K => L2T d) b ∘L
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin K => L2T d)).toContinuousLinearMap)

theorem mulMat_apply (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    (f : SpinorL2 d K) (a : Fin K) : mulMat F f a = ∑ b, mulL2 (entryCM F a b) (f b) := by
  simp [mulMat]

theorem mulMat_vecL2 (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) : mulMat F (vecL2 Φ) = vecL2 (mulVecCM F Φ) := by
  ext1 a
  rw [mulMat_apply, vecL2_apply]
  simp only [vecL2_apply, mulL2_toL2]
  rw [← map_sum]
  congr 1
  ext x
  simp [compCM, entryCM, mulVecCM, Matrix.mulVec, dotProduct]

theorem vecL2_add (Φ Ψ : C(UnitAddTorus (Fin d), Fin K → ℂ)) :
    vecL2 (Φ + Ψ) = vecL2 Φ + vecL2 Ψ := by
  ext1 a
  simp only [vecL2_apply, PiLp.add_apply]
  rw [← map_add]
  rfl

theorem vecL2_smul (c : ℂ) (Φ : C(UnitAddTorus (Fin d), Fin K → ℂ)) :
    vecL2 (c • Φ) = c • vecL2 Φ := by
  ext1 a
  simp only [vecL2_apply, PiLp.smul_apply]
  rw [← map_smul]
  rfl

theorem vecL2_zero : vecL2 (0 : C(UnitAddTorus (Fin d), Fin K → ℂ)) = 0 := by
  ext1 a
  rw [vecL2_apply]
  have : compCM (0 : C(UnitAddTorus (Fin d), Fin K → ℂ)) a = 0 := rfl
  rw [this]
  exact map_zero (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ)

/-- The plane wave `x ↦ e^{2πik·x} v` as a continuous section. -/
def planeWave (k : Fin d → ℤ) (v : Fin K → ℂ) : C(UnitAddTorus (Fin d), Fin K → ℂ) :=
  ⟨fun x => mFourier k x • v, (mFourier k).continuous.smul continuous_const⟩

theorem modeVec_eq_vecL2 (k : Fin d → ℤ) (v : Fiber K) :
    modeVec k v = vecL2 (planeWave k (v : Fin K → ℂ)) := by
  ext1 a
  rw [modeVec_apply, vecL2_apply, mFourierLp, ← map_smul]
  congr 1
  ext x
  simp [compCM, planeWave, mul_comm]

/-! ### Extension from the standard basis of `ℓ²` -/

/-- A continuous additive map on `ℓ²` whose zero set is stable under scalars and contains the
standard basis vanishes identically. -/
theorem eq_zero_of_single {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] (F : ℓ²(ι, ℂ) → E)
    (hcont : Continuous F) (hadd : ∀ x y, F (x + y) = F x + F y)
    (hsmul : ∀ (c : ℂ) x, F x = 0 → F (c • x) = 0)
    (hsingle : ∀ i, F (lp.single 2 i (1 : ℂ)) = 0) (x : ℓ²(ι, ℂ)) : F x = 0 := by
  have hF0 : F 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  set G : ℓ²(ι, ℂ) →+ E := AddMonoidHom.mk' F hadd
  have hs := lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x
  have hterm : ∀ i, F (lp.single 2 i (x i)) = 0 := by
    intro i
    have : (lp.single 2 i (x i) : ℓ²(ι, ℂ)) = x i • lp.single 2 i (1 : ℂ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hsmul _ _ (hsingle i)
  have hpart : ∀ s : Finset ι, F (∑ i ∈ s, lp.single 2 i (x i)) = 0 := by
    intro s
    have : F (∑ i ∈ s, lp.single 2 i (x i)) = G (∑ i ∈ s, lp.single 2 i (x i)) := rfl
    rw [this, map_sum]
    exact Finset.sum_eq_zero fun i _ => hterm i
  have hlim := (hcont.tendsto x).comp hs
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun s => (hpart s).symm)

/-! ### Fourier coordinates for `H¹` and the weak derivatives -/

section fourier

variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

/-- The multiplier `2πi k_j (1 + |k|²)^{-1/2}` of `∂_j` in `H¹` coordinates. -/
def derMult (j : Fin d) (p : Idx d K) : ℂ := (2 * π * Complex.I * (p.1 j : ℂ)) * sobMult p

theorem norm_derMult_le (j : Fin d) (p : Idx d K) : ‖derMult j p‖ ≤ 2 * π := by
  rw [derMult, norm_mul, sobMult, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 (sobWeight_pos p.1))]
  have hk : ‖(2 * π * Complex.I * (p.1 j : ℂ))‖ = 2 * π * |((p.1 j : ℤ) : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    push_cast
    rw [Complex.norm_intCast]
    ring
  rw [hk]
  have hs := Real.sqrt_pos.2 (sobWeight_pos p.1)
  have habs : |((p.1 j : ℤ) : ℝ)| ≤ Real.sqrt (sobWeight p.1) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    unfold sobWeight
    have : ((p.1 j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((p.1 i : ℤ) : ℝ) ^ 2 :=
      single_le_sum (f := fun i => ((p.1 i : ℤ) : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ j)
    linarith
  rw [mul_assoc]
  have h2 : |((p.1 j : ℤ) : ℝ)| * (Real.sqrt (sobWeight p.1))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hs]; exact habs
  have hpi : 0 ≤ 2 * π := by positivity
  calc 2 * π * (|((p.1 j : ℤ) : ℝ)| * (Real.sqrt (sobWeight p.1))⁻¹) ≤ 2 * π * 1 :=
        mul_le_mul_of_nonneg_left h2 hpi
    _ = 2 * π := mul_one _

/-- **The weak derivative `∂_j : H¹ → L²`** in Fourier coordinates. -/
def derivH1 (j : Fin d) : ℓ²(Idx d K, ℂ) →L[ℂ] SpinorL2 d K :=
  (eigBasis hc₀).repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    HilbertBasisDiagonal.mulCLM (derMult j) (norm_derMult_le j)

theorem mulCLM_single' (m : Idx d K → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C) (q : Idx d K) (b : ℂ) :
    HilbertBasisDiagonal.mulCLM m hm (lp.single (E := fun _ : Idx d K => ℂ) 2 q b) =
      lp.single (E := fun _ : Idx d K => ℂ) 2 q (m q * b) := by
  classical
  ext p
  rw [HilbertBasisDiagonal.mulCLM_apply, lp.single_apply, lp.single_apply, Pi.single_apply,
    Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem repr_symm_single_smul (q : Idx d K) (b : ℂ) :
    (eigBasis hc₀).repr.symm (lp.single 2 q b) = b • eigBasis hc₀ q := by
  classical
  rw [show (lp.single 2 q b : ℓ²(Idx d K, ℂ)) = b • lp.single 2 q (1 : ℂ) by
    rw [← lp.single_smul, smul_eq_mul, mul_one], map_smul, HilbertBasis.repr_symm_single]

/-- `H¹ ↪ L²` on a basis vector: `sobolev e_p = (1 + |k|²)^{-1/2} e^{2πik·x} u_i`. -/
theorem sobolev_single (p : Idx d K) :
    sobolev hc₀ (lp.single 2 p (1 : ℂ)) = sobMult p • eigBasis hc₀ p := by
  rw [sobolev, ContinuousLinearMap.comp_apply, mulCLM_single' _ _ p, mul_one]
  exact repr_symm_single_smul hc₀ p _

/-- `∂_j` on a basis vector: `∂_j e_p = 2πi k_j (1 + |k|²)^{-1/2} e^{2πik·x} u_i`. -/
theorem derivH1_single (j : Fin d) (p : Idx d K) :
    derivH1 hc₀ j (lp.single 2 p (1 : ℂ)) = derMult j p • eigBasis hc₀ p := by
  rw [derivH1, ContinuousLinearMap.comp_apply, mulCLM_single' _ _ p, mul_one]
  exact repr_symm_single_smul hc₀ p _

theorem eigBasis_eq_vecL2 (p : Idx d K) :
    eigBasis hc₀ p = vecL2 (planeWave p.1 (evec hc₀ p.1 p.2 : Fin K → ℂ)) := by
  rw [eigBasis_apply, eigVec, modeVec_eq_vecL2]

/-- `derivH1` is the derivative: `∂_j (e^{2πik·x} v)(y) = 2πi k_j e^{2πik·y} v` along the
coordinate line, and `derMult j p = 2πi k_j sobMult p`. -/
theorem hasDerivAt_planeWave (k : Fin d → ℤ) (v : Fin K → ℂ) (j : Fin d)
    (y : UnitAddTorus (Fin d)) :
    HasDerivAt (fun t : ℝ => planeWave k v (y + lineVec j t))
      ((2 * π * Complex.I * (k j : ℂ)) • planeWave k v y) 0 := by
  rw [hasDerivAt_pi]
  intro a
  have h := (hasDerivAt_mFourier_line k j y).mul_const (v a)
  simpa [planeWave, lineVec, mul_assoc] using h

end fourier

/-! ### The variable-coefficient operator -/

/-- **Coefficients of the periodic extension** (`lem:supp-density-symmetric`,
`eq:supp-geometric-dirac` after density conjugation): continuous Hermitian Clifford coefficients
`c^j` (in the doubled form `ĉ^j` when used for `D̂`), differentiable along `e_j` with continuous
derivative `∂_j c^j` (`dc j`), and a continuous skew-Hermitian spin connection `Ω_j`, all on
the torus `𝕋ᵈ` (the fixed smooth periodic coordinate extension). -/
structure Coeffs (d K : ℕ) where
  /-- The Clifford coefficients `c^j(x)`. -/
  c : Fin d → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)
  /-- The derivative `∂_j c^j(x)` along `e_j`. -/
  dc : Fin d → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)
  /-- The spin connection `Ω_j(x)`. -/
  Ω : Fin d → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)
  c_herm : ∀ j x, (c j x)ᴴ = c j x
  Ω_skew : ∀ j x, (Ω j x)ᴴ = -Ω j x
  hasDerivAt_c : ∀ j y (v : Fin K → ℂ),
    HasDerivAt (fun t : ℝ => c j (y + lineVec j t) *ᵥ v) (dc j y *ᵥ v) 0

namespace Coeffs

variable (C : Coeffs d K)

/-- Entries of `c^j` along the line are differentiable with derivative the entries of `∂_j c^j`. -/
theorem hasDerivAt_entry (j : Fin d) (y : UnitAddTorus (Fin d)) (a b : Fin K) :
    HasDerivAt (fun t : ℝ => C.c j (y + lineVec j t) a b) (C.dc j y a b) 0 := by
  classical
  have h1 := (hasDerivAt_pi.mp (C.hasDerivAt_c j y (Pi.single b 1))) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1

/-- `∂_j c^j` is Hermitian (derivative of a Hermitian field). -/
theorem dc_herm (j : Fin d) (y : UnitAddTorus (Fin d)) : (C.dc j y)ᴴ = C.dc j y := by
  ext a b
  rw [conjTranspose_apply]
  have h1 := (C.hasDerivAt_entry j y b a).star
  have h2 := C.hasDerivAt_entry j y a b
  have he : (fun t : ℝ => star (C.c j (y + lineVec j t) b a)) =
      fun t : ℝ => C.c j (y + lineVec j t) a b := by
    funext t
    have := congrFun (congrFun (C.c_herm j (y + lineVec j t)) a) b
    rw [conjTranspose_apply] at this
    exact this
  rw [he] at h1
  exact h1.unique h2

/-- The zeroth-order part `B = -(i/2) Σ_j (∂_j c^j + c^j Ω_j + Ω_j c^j)` of
`-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)`. -/
def pot : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ) :=
  (-(Complex.I / 2)) • ∑ j, (C.dc j + C.c j * C.Ω j + C.Ω j * C.c j)

theorem pot_apply (x : UnitAddTorus (Fin d)) :
    C.pot x = (-(Complex.I / 2)) • ∑ j, (C.dc j x + C.c j x * C.Ω j x + C.Ω j x * C.c j x) := by
  simp [pot]

/-- `Bᴴ - B = i Σ_j ∂_j c^j`. -/
theorem pot_conjTranspose_sub (x : UnitAddTorus (Fin d)) :
    (C.pot x)ᴴ - C.pot x = Complex.I • ∑ j, C.dc j x := by
  rw [pot_apply, conjTranspose_smul, conjTranspose_sum]
  simp only [conjTranspose_add, conjTranspose_mul, C.dc_herm, C.c_herm, C.Ω_skew]
  have hI : star (-(Complex.I / 2)) = Complex.I / 2 := by
    simp [Complex.conj_I, neg_div]
  rw [hI]
  simp only [Matrix.neg_mul, Matrix.mul_neg, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

/-- **The continuum operator `D̂_g` on `H¹`** (Fourier coordinates):
`D̂_g u = Σ_j c^j (-i ∂_j u) + B u`, `B = -(i/2) Σ_j (∂_j c^j + c^j Ω_j + Ω_j c^j)`, i.e.
`-(i/2) Σ_j (c^j ∇_j + ∇_j c^j) u` expanded by the Leibniz rule. -/
def op : ℓ²(Idx d K, ℂ) →L[ℂ] SpinorL2 d K :=
  ∑ j, mulMat (C.c j) ∘L ((-Complex.I) • derivH1 hc₀ j) + mulMat C.pot ∘L sobolev hc₀

/-- The frozen symbol field `A_k(x) = Σ_j 2π k_j c^j(x) + B(x)`. -/
def symbField (k : Fin d → ℤ) : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ) :=
  ∑ j, ((2 * π * (k j : ℝ) : ℝ) : ℂ) • C.c j + C.pot

theorem symbField_apply (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    C.symbField k x = ∑ j, ((2 * π * (k j : ℝ) : ℝ) : ℂ) • C.c j x + C.pot x := by
  simp [symbField]

/-- `D̂_g` on a basis vector: `D̂_g e_p = sobMult p · A_k(x) e^{2πik·x} u_i`. -/
theorem op_single (p : Idx d K) :
    C.op hc₀ (lp.single 2 p (1 : ℂ)) =
      sobMult p • vecL2 (mulVecCM (C.symbField p.1)
        (planeWave p.1 (evec hc₀ p.1 p.2 : Fin K → ℂ))) := by
  set Φ := planeWave p.1 (evec hc₀ p.1 p.2 : Fin K → ℂ)
  have hsum : ∀ (F G : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)),
      mulVecCM (F + G) Φ = mulVecCM F Φ + mulVecCM G Φ := by
    intro F G; ext x a; simp [mulVecCM, Matrix.add_mulVec]
  have hsmul : ∀ (s : ℂ) (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)),
      mulVecCM (s • F) Φ = s • mulVecCM F Φ := by
    intro s F; ext x a; simp [mulVecCM, Matrix.smul_mulVec]
  have hfin : ∀ (s : Finset (Fin d)) (F : Fin d → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)),
      mulVecCM (∑ j ∈ s, F j) Φ = ∑ j ∈ s, mulVecCM (F j) Φ := by
    intro s F
    classical
    induction s using Finset.induction_on with
    | empty => ext x a; simp [mulVecCM]
    | insert i s hi ih => rw [sum_insert hi, sum_insert hi, hsum, ih]
  have hvec : ∀ (s : Finset (Fin d)) (Ψ : Fin d → C(UnitAddTorus (Fin d), Fin K → ℂ)),
      vecL2 (∑ j ∈ s, Ψ j) = ∑ j ∈ s, vecL2 (Ψ j) := by
    intro s Ψ
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact vecL2_zero
    | insert i s hi ih => rw [sum_insert hi, sum_insert hi, vecL2_add, ih]
  rw [op, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, derivH1_single,
    sobolev_single, map_smul, eigBasis_eq_vecL2, mulMat_vecL2]
  rw [symbField, hsum, hfin, vecL2_add, hvec, smul_add, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsmul, vecL2_smul, smul_smul, smul_smul, derMult]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end Coeffs

/-! ### Symmetry of `D̂_g` on `H¹` (integration by parts) -/

namespace Coeffs

variable (C : Coeffs d K)

theorem sum_conj_mul_eq_dotProduct (X Y : Fin K → ℂ) :
    ∑ a, conj (X a) * Y a = star X ⬝ᵥ Y := by
  simp [dotProduct, Pi.star_apply]

/-- The pointwise identity behind the integration by parts:
`⟨A_k e_k v, e_l w⟩ - ⟨e_k v, A_l e_l w⟩ = e_{l-k} ⟨v, (A_kᴴ - A_l) w⟩`. -/
theorem pointwise_sub (k l : Fin d → ℤ) (v w : Fin K → ℂ) (x : UnitAddTorus (Fin d)) :
    (∑ a, conj ((C.symbField k x *ᵥ (mFourier k x • v)) a) * (mFourier l x • w) a) -
      ∑ a, conj ((mFourier k x • v) a) * (C.symbField l x *ᵥ (mFourier l x • w)) a =
    mFourier (l - k) x * (star v ⬝ᵥ (((C.symbField k x)ᴴ - C.symbField l x) *ᵥ w)) := by
  rw [sum_conj_mul_eq_dotProduct, sum_conj_mul_eq_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, star_smul, Matrix.sub_mulVec, dotProduct_sub]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have hE : mFourier (l - k) x = star (mFourier k x) * mFourier l x := by
    rw [sub_eq_add_neg, add_comm, mFourier_add, mFourier_neg]
    rfl
  rw [hE]
  ring

/-- `A_kᴴ - A_l = Σ_j 2π (k_j - l_j) c^j + i Σ_j ∂_j c^j`. -/
theorem symbField_conjTranspose_sub (k l : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    (C.symbField k x)ᴴ - C.symbField l x =
      ∑ j, (((2 * π * ((k j : ℝ) - (l j : ℝ)) : ℝ) : ℂ) • C.c j x + Complex.I • C.dc j x) := by
  rw [symbField_apply, symbField_apply, conjTranspose_add, conjTranspose_sum]
  simp only [conjTranspose_smul, C.c_herm, Complex.star_def, Complex.conj_ofReal]
  have h := C.pot_conjTranspose_sub x
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← h]
  have : ∀ j, (((2 * π * ((k j : ℝ) - (l j : ℝ)) : ℝ) : ℂ) • C.c j x) =
      ((2 * π * (k j : ℝ) : ℝ) : ℂ) • C.c j x - ((2 * π * (l j : ℝ) : ℝ) : ℂ) • C.c j x := by
    intro j
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  simp_rw [this, Finset.sum_sub_distrib]
  abel

/-- The line derivative of `γ_j = ⟨v, c^j w⟩`. -/
theorem hasDerivAt_inner_c (j : Fin d) (v w : Fin K → ℂ) (y : UnitAddTorus (Fin d)) :
    HasDerivAt (fun t : ℝ => star v ⬝ᵥ (C.c j (y + lineVec j t) *ᵥ w))
      (star v ⬝ᵥ (C.dc j y *ᵥ w)) 0 := by
  have hc := hasDerivAt_pi.mp (C.hasDerivAt_c j y w)
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun a (t : ℝ) => star v a * (C.c j (y + lineVec j t) *ᵥ w) a)
    (fun a _ => (hc a).const_mul (star v a))
  simpa [dotProduct] using hs

omit C in
theorem continuous_inner_c (F : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    (v w : Fin K → ℂ) : Continuous fun x => star v ⬝ᵥ (F x *ᵥ w) :=
  continuous_const.dotProduct (F.continuous.matrix_mulVec continuous_const)

/-- **Integration by parts for the plane-wave matrix elements**:
`⟪A_k e_k v, e_l w⟫ = ⟪e_k v, A_l e_l w⟫`. -/
theorem inner_symbField_planeWave (k l : Fin d → ℤ) (v w : Fin K → ℂ) :
    ⟪vecL2 (mulVecCM (C.symbField k) (planeWave k v)), vecL2 (planeWave l w)⟫_ℂ =
      ⟪vecL2 (planeWave k v), vecL2 (mulVecCM (C.symbField l) (planeWave l w))⟫_ℂ := by
  rw [inner_vecL2, inner_vecL2, ← sub_eq_zero]
  have hint : ∀ (Φ Ψ : C(UnitAddTorus (Fin d), Fin K → ℂ)),
      Integrable (fun x => ∑ a, conj (Φ x a) * Ψ x a) := by
    intro Φ Ψ
    refine integrable_of_continuous (continuous_finset_sum _ fun a _ => ?_)
    exact (Complex.continuous_conj.comp ((continuous_apply a).comp Φ.continuous)).mul
      ((continuous_apply a).comp Ψ.continuous)
  rw [← integral_sub (hint _ _) (hint _ _)]
  set g : UnitAddTorus (Fin d) → ℂ := fun x => mFourier (l - k) x
  set γ : Fin d → UnitAddTorus (Fin d) → ℂ := fun j x => star v ⬝ᵥ (C.c j x *ᵥ w)
  set δ : Fin d → UnitAddTorus (Fin d) → ℂ := fun j x => star v ⬝ᵥ (C.dc j x *ᵥ w)
  set F' : Fin d → UnitAddTorus (Fin d) → ℂ := fun j x =>
    (2 * π * Complex.I * (((l - k) j : ℤ) : ℂ)) * g x * γ j x + g x * δ j x
  have hcont_g : Continuous g := (mFourier (l - k)).continuous
  have hF'cont : ∀ j, Continuous (F' j) := fun j =>
    ((continuous_const.mul hcont_g).mul (continuous_inner_c (C.c j) v w)).add
      (hcont_g.mul (continuous_inner_c (C.dc j) v w))
  have hpt : ∀ x, (∑ a, conj (mulVecCM (C.symbField k) (planeWave k v) x a) *
        planeWave l w x a) -
      ∑ a, conj (planeWave k v x a) * mulVecCM (C.symbField l) (planeWave l w) x a =
      ∑ j, Complex.I * F' j x := by
    intro x
    have := C.pointwise_sub k l v w x
    simp only [mulVecCM, planeWave, ContinuousMap.coe_mk]
    rw [this, C.symbField_conjTranspose_sub, Matrix.sum_mulVec, dotProduct_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [F', g, γ, δ, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, Pi.sub_apply, Int.cast_sub]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum (f := fun j x => Complex.I * F' j x) Finset.univ
    fun j _ => integrable_of_continuous (continuous_const.mul (hF'cont j))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul]
  have hzero : ∫ x, F' j x = 0 := by
    refine integral_lineDeriv_eq_zero (F := fun x => g x * γ j x) j
      (hcont_g.mul (continuous_inner_c (C.c j) v w)) (hF'cont j) fun y => ?_
    have hg := hasDerivAt_mFourier_line (l - k) j y
    have hγ := C.hasDerivAt_inner_c j v w y
    have := hg.fun_mul hγ
    have h0 : lineVec j (0 : ℝ) = (0 : UnitAddTorus (Fin d)) := by simp [lineVec]
    have h0' : (Pi.single j ((0 : ℝ) : UnitAddCircle) : UnitAddTorus (Fin d)) = 0 := by simp
    simp only [h0, h0', add_zero] at this
    exact this
  rw [hzero, mul_zero]

variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

theorem sobMult_conj (p : Idx d K) : conj (sobMult p) = sobMult p := by
  rw [sobMult, Complex.conj_ofReal]

/-- Symmetry of `D̂_g` on the Fourier basis of `H¹`. -/
theorem op_symm_single (p q : Idx d K) :
    ⟪C.op hc₀ (lp.single 2 p (1 : ℂ)), sobolev hc₀ (lp.single 2 q (1 : ℂ))⟫_ℂ =
      ⟪sobolev hc₀ (lp.single 2 p (1 : ℂ)), C.op hc₀ (lp.single 2 q (1 : ℂ))⟫_ℂ := by
  rw [C.op_single, C.op_single, sobolev_single, sobolev_single, eigBasis_eq_vecL2,
    eigBasis_eq_vecL2, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    C.inner_symbField_planeWave]

/-- **Symmetry of `D̂_g` on `H¹`**: `⟪D̂_g a, b⟫ = ⟪a, D̂_g b⟫` for all `a, b ∈ H¹`. -/
theorem op_symm (a b : ℓ²(Idx d K, ℂ)) :
    ⟪C.op hc₀ a, sobolev hc₀ b⟫_ℂ = ⟪sobolev hc₀ a, C.op hc₀ b⟫_ℂ := by
  classical
  -- first `a` a basis vector
  have hfirst : ∀ p (b : ℓ²(Idx d K, ℂ)),
      ⟪C.op hc₀ (lp.single 2 p (1 : ℂ)), sobolev hc₀ b⟫_ℂ -
        ⟪sobolev hc₀ (lp.single 2 p (1 : ℂ)), C.op hc₀ b⟫_ℂ = 0 := by
    intro p
    refine eq_zero_of_single (fun b => ⟪C.op hc₀ (lp.single 2 p (1 : ℂ)), sobolev hc₀ b⟫_ℂ -
        ⟪sobolev hc₀ (lp.single 2 p (1 : ℂ)), C.op hc₀ b⟫_ℂ) ?_ ?_ ?_ ?_
    · exact (continuous_const.inner (sobolev hc₀).continuous).sub
        (continuous_const.inner (C.op hc₀).continuous)
    · intro x y
      simp only [map_add, inner_add_right]
      ring
    · intro c x hx
      simp only [map_smul, inner_smul_right, ← mul_sub, hx, mul_zero]
    · intro q
      rw [C.op_symm_single, sub_self]
  have hall := eq_zero_of_single (fun a => ⟪C.op hc₀ a, sobolev hc₀ b⟫_ℂ -
      ⟪sobolev hc₀ a, C.op hc₀ b⟫_ℂ)
    (((C.op hc₀).continuous.inner continuous_const).sub
      ((sobolev hc₀).continuous.inner continuous_const))
    (fun x y => by simp only [map_add, inner_add_left]; ring)
    (fun c x hx => by simp only [map_smul, inner_smul_left, ← mul_sub, hx, mul_zero])
    (fun p => hfirst p b) a
  exact sub_eq_zero.mp hall

end Coeffs

/-! ### The embedding `H¹ ↪ L²` -/

section sobolevProps

variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

theorem sobMult_ne_zero (p : Idx d K) : sobMult p ≠ 0 := by
  rw [sobMult]
  have := Real.sqrt_pos.2 (sobWeight_pos p.1)
  exact_mod_cast (inv_pos.2 this).ne'

theorem repr_sobolev_apply (a : ℓ²(Idx d K, ℂ)) (p : Idx d K) :
    (eigBasis hc₀).repr (sobolev hc₀ a) p = sobMult p * a p := by
  rw [sobolev, ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply, HilbertBasisDiagonal.mulCLM_apply]

theorem sobolev_injective : Function.Injective (sobolev hc₀) := by
  intro a b h
  ext p
  have := congrArg (fun f => (eigBasis hc₀).repr f p) h
  simp only [repr_sobolev_apply] at this
  exact mul_left_cancel₀ (sobMult_ne_zero p) this

theorem sobolev_denseRange : DenseRange (sobolev hc₀) := by
  have hsub : Submodule.span ℂ (Set.range (eigBasis hc₀)) ≤
      LinearMap.range (sobolev hc₀).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    refine ⟨lp.single 2 p ((sobMult p)⁻¹), ?_⟩
    change sobolev hc₀ _ = _
    rw [show (lp.single 2 p ((sobMult p)⁻¹) : ℓ²(Idx d K, ℂ)) =
      (sobMult p)⁻¹ • lp.single 2 p (1 : ℂ) by rw [← lp.single_smul, smul_eq_mul, mul_one],
      map_smul, sobolev_single, smul_smul, inv_mul_cancel₀ (sobMult_ne_zero p), one_smul]
  have hd := (eigBasis hc₀).dense_span
  intro x
  have hx : x ∈ (Submodule.span ℂ (Set.range (eigBasis hc₀))).topologicalClosure := by
    rw [hd]; trivial
  exact closure_mono (fun y hy => by
    obtain ⟨a, ha⟩ := hsub hy
    exact ⟨a, ha⟩) hx

/-- Closed balls of `H¹` have closed images in `L²` (coordinatewise weak limits). -/
theorem isClosed_sobolev_image_closedBall (R : ℝ) :
    IsClosed (sobolev hc₀ '' Metric.closedBall 0 R) := by
  classical
  refine isClosed_of_closure_subset fun u hu => ?_
  obtain ⟨x, hx, hxu⟩ := mem_closure_iff_seq_limit.mp hu
  choose a ha hax using hx
  have hR : 0 ≤ R := by
    have := ha 0
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (norm_nonneg _).trans this
  set w := (eigBasis hc₀).repr u
  have hcoord : ∀ p, Tendsto (fun n => a n p) atTop (𝓝 (w p / sobMult p)) := by
    intro p
    have h1 : Tendsto (fun n => (eigBasis hc₀).repr (x n)) atTop (𝓝 w) :=
      ((eigBasis hc₀).repr.continuous.tendsto u).comp hxu
    have h2 : Tendsto (fun n => (eigBasis hc₀).repr (x n) p) atTop (𝓝 (w p)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h1
      have := lp.norm_apply_le_norm (two_ne_zero) ((eigBasis hc₀).repr (x n) - w) p
      simpa using this
    have h3 : ∀ n, (eigBasis hc₀).repr (x n) p = sobMult p * a n p := by
      intro n; rw [← hax n, repr_sobolev_apply]
    simp_rw [h3] at h2
    have := h2.div_const (sobMult p)
    refine this.congr fun n => ?_
    field_simp [sobMult_ne_zero p]
  set A : Idx d K → ℂ := fun p => w p / sobMult p
  have hsum : ∀ s : Finset (Idx d K), ∑ p ∈ s, ‖A p‖ ^ (2 : ℝ≥0∞).toReal ≤ R ^ (2 : ℝ≥0∞).toReal := by
    intro s
    have hlim : Tendsto (fun n => ∑ p ∈ s, ‖a n p‖ ^ (2 : ℝ≥0∞).toReal) atTop
        (𝓝 (∑ p ∈ s, ‖A p‖ ^ (2 : ℝ≥0∞).toReal)) :=
      tendsto_finset_sum _ fun p _ =>
        ((hcoord p).norm.rpow_const (Or.inr (by norm_num)))
    refine le_of_tendsto' hlim fun n => ?_
    refine (lp.sum_rpow_le_norm_rpow (by norm_num) (a n) s).trans ?_
    have := ha n
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact Real.rpow_le_rpow (norm_nonneg _) this (by norm_num)
  have hmem : Memℓp A 2 := memℓp_gen' hsum
  set A' : ℓ²(Idx d K, ℂ) := ⟨A, hmem⟩
  refine ⟨A', ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact lp.norm_le_of_forall_sum_le (by norm_num) hR hsum
  · apply (eigBasis hc₀).repr.injective
    ext p
    rw [repr_sobolev_apply]
    change sobMult p * (w p / sobMult p) = w p
    field_simp [sobMult_ne_zero p]

/-- The finite Fourier sums (trigonometric polynomials) in `H¹` coordinates. -/
def finCore : Submodule ℂ ℓ²(Idx d K, ℂ) :=
  Submodule.span ℂ (Set.range fun p : Idx d K => lp.single 2 p (1 : ℂ))

theorem finCore_dense : Dense (finCore (d := d) (K := K) : Set ℓ²(Idx d K, ℂ)) := by
  classical
  intro x
  have hs := lp.hasSum_single (E := fun _ : Idx d K => ℂ) (p := 2) (by norm_num) x
  refine mem_closure_of_tendsto hs (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [show (lp.single 2 p (x p) : ℓ²(Idx d K, ℂ)) = x p • lp.single 2 p (1 : ℂ) by
    rw [← lp.single_smul, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

end sobolevProps

/-! ### Stable lattice discretizations of `D̂_g` and the self-adjoint realisation -/

namespace Coeffs

variable (C : Coeffs d K)

/-- **A stable lattice discretization of `D̂_g`** on the periodic lattices `(ℤ/(n+1))ᵈ`
(mesh `h = 1/(n+1)`), with the piecewise-constant embedding `W_h = 𝒥⁰_h`, the samples
`S_h = (𝒥⁰_h)^*`, and the trigonometric reconstruction `I_h` and discrete `H¹` norm of the
periodic flat torus (`FlatTorusSpinAtlas`, coefficient independent): self-adjoint stage
operators with the graph estimate (A2) `eq:supp-general-Garding` and the plane-wave core
condition (A3) `W_h D_h S_h ψ → D̂_g ψ` for `ψ = e^{2πik·x} v`. -/
structure LatticeDiscretization where
  /-- The stage operators `D_h` on `ℓ²((ℤ/(n+1))ᵈ; ℂ^K)`. -/
  stage : ∀ n : ℕ, Stage d K (n + 1) →L[ℂ] Stage d K (n + 1)
  stage_selfAdjoint : ∀ n, IsSelfAdjoint (stage n)
  graphConst : ℝ
  graphConst_nonneg : 0 ≤ graphConst
  /-- (A2) `‖u‖_{1,h} ≤ C (‖D_h u‖ + ‖u‖)`. -/
  discreteNorm_le : ∀ n u, discreteNorm d K (n + 1) u ≤ graphConst * (‖stage n u‖ + ‖u‖)
  /-- (A3) on plane waves. -/
  planeWave_tendsto : ∀ (k : Fin d → ℤ) (v : Fin K → ℂ),
    Tendsto (fun n => embed d K (n + 1) (stage n
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap
        (vecL2 (planeWave k v))))) atTop
      (𝓝 (vecL2 (mulVecCM (C.symbField k) (planeWave k v))))

variable {C}
variable {c₀ : Fin d → Matrix (Fin K) (Fin K) ℂ} (hc₀ : ∀ j, (c₀ j)ᴴ = c₀ j)

/-- (A3) on the whole core of finite Fourier sums. -/
theorem LatticeDiscretization.core_tendsto (L : C.LatticeDiscretization) (a : ℓ²(Idx d K, ℂ))
    (ha : a ∈ finCore) :
    Tendsto (fun n => embed d K (n + 1) (L.stage n
      (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap (sobolev hc₀ a))))
      atTop (𝓝 (C.op hc₀ a)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [sobolev_single, C.op_single, eigBasis_eq_vecL2]
    simp only [map_smul]
    exact (L.planeWave_tendsto p.1 _).const_smul _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
  | smul c x hx ihx => simpa only [map_smul] using ihx.const_smul c

/-- **The stable discretization** in the abstract form of `StableDiscretization`. -/
def LatticeDiscretization.toStable (L : C.LatticeDiscretization) :
    StableDiscretization (SpinorL2 d K) ℓ²(Idx d K, ℂ) (fun n => Stage d K (n + 1)) where
  sobolev := sobolev hc₀
  sobolev_compact := isCompactOperator_sobolev hc₀
  sobolev_injective := sobolev_injective hc₀
  sobolev_denseRange := sobolev_denseRange hc₀
  sobolev_closedBall := isClosed_sobolev_image_closedBall hc₀
  op := C.op hc₀
  op_symm := C.op_symm hc₀
  core := finCore
  core_dense := finCore_dense
  embed n := embed d K (n + 1)
  stage := L.stage
  stage_selfAdjoint := L.stage_selfAdjoint
  embed_adjoint_tendsto := tendsto_embed_adjoint
  discreteNorm n := discreteNorm d K (n + 1)
  discreteNorm_nonneg n u := discreteNorm_nonneg u
  reconstruct n := recLin d K (n + 1) hc₀
  reconstructConst := 1
  reconstructConst_nonneg := zero_le_one
  norm_reconstruct_le n u := norm_recLin_le hc₀ u
  reconstructError n := reconError d (n + 1)
  reconstructError_nonneg n := by unfold reconError; positivity
  reconstructError_tendsto := tendsto_reconError
  norm_sobolev_reconstruct_sub_embed_le n u := by
    rw [sobolev_recLin]
    exact norm_interp_sub_embed_le u
  graphConst := L.graphConst
  graphConst_nonneg := L.graphConst_nonneg
  discreteNorm_le := L.discreteNorm_le
  sample n ψ := ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap
    (sobolev hc₀ ψ)
  embed_sample_tendsto ψ := tendsto_embed_adjoint (sobolev hc₀ ψ)
  embed_stage_sample_tendsto ψ := L.core_tendsto hc₀ ψ ψ.2

/-- **The self-adjoint realisation `D̂_g`** of `-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)` on
`L²(𝕋ᵈ; ℂ^K)` with domain `H¹`, obtained from a stable lattice discretization. -/
def LatticeDiscretization.dirac (L : C.LatticeDiscretization) :
    SelfAdjointResolventData (SpinorL2 d K) :=
  (L.toStable hc₀).limit

/-- The domain of `D̂_g` is `H¹ = range (H¹ ↪ L²)`. -/
theorem LatticeDiscretization.dirac_domain (L : C.LatticeDiscretization) :
    (L.dirac hc₀).op.domain = LinearMap.range (sobolev hc₀).toLinearMap := rfl

/-- `D̂_g` acts on `H¹` as the differential operator `C.op`. -/
theorem LatticeDiscretization.dirac_sobolev (L : C.LatticeDiscretization)
    (a : ℓ²(Idx d K, ℂ)) :
    (L.dirac hc₀).op ⟨sobolev hc₀ a, ⟨a, rfl⟩⟩ = C.op hc₀ a :=
  (L.toStable hc₀).limit_op_sobolev a

/-- `D̂_g` is self-adjoint (Mathlib's `LinearPMap.adjoint`). -/
theorem LatticeDiscretization.isSelfAdjoint_dirac (L : C.LatticeDiscretization) :
    IsSelfAdjoint (L.dirac hc₀).op :=
  (L.toStable hc₀).isSelfAdjoint_limit

/-- **`eq:supp-local-norm-resolvent`** (for a stable lattice discretization of the periodic
extension): `‖𝒥⁰_h (D_h - z)⁻¹ (𝒥⁰_h)^* - (D̂_g - z)⁻¹‖ → 0` for every non-real `z`. -/
theorem LatticeDiscretization.tendsto_norm_resolvent (L : C.LatticeDiscretization) {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun n => ‖(embed d K (n + 1)).toContinuousLinearMap ∘L
        (L.toStable hc₀).stageRes n hz ∘L
        ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap -
        (L.dirac hc₀).resolvent z hz‖) atTop (𝓝 0) :=
  (L.toStable hc₀).tendsto_norm_resolvent hz

/-- **Spectral projections** of the periodic extension: isolated bounded-energy spectral
projections converge in norm. -/
theorem LatticeDiscretization.tendsto_norm_spectralProjection (L : C.LatticeDiscretization)
    {a b : ℝ} (hab : a < b) (ha : (L.dirac hc₀).opEigenspace (a : ℂ) = ⊥)
    (hb : (L.dirac hc₀).opEigenspace (b : ℂ) = ⊥) :
    Tendsto (fun n => ‖(L.toStable hc₀).toAtlas.embeddedSpectralProjection a b n -
      (L.dirac hc₀).spectralProjection a b‖) atTop (𝓝 0) :=
  (L.toStable hc₀).tendsto_norm_spectralProjection hab ha hb

end Coeffs

/-! ### `D̂_g` is the density-symmetric operator `-(i/2) Σ_j (c^j ∇_j + ∇_j c^j)` -/

namespace Coeffs

variable (C : Coeffs d K)

/-- Leibniz rule along `e_j` for `c^j ψ`. -/
theorem hasDerivAt_mulVec_line (j : Fin d) (x : UnitAddTorus (Fin d))
    {ψ : UnitAddTorus (Fin d) → Fin K → ℂ} {Dψ : Fin K → ℂ}
    (hψ : HasDerivAt (fun t : ℝ => ψ (x + lineVec j t)) Dψ 0) :
    HasDerivAt (fun t : ℝ => C.c j (x + lineVec j t) *ᵥ ψ (x + lineVec j t))
      (C.dc j x *ᵥ ψ x + C.c j x *ᵥ Dψ) 0 := by
  rw [hasDerivAt_pi]
  intro a
  have hcomp : ∀ b : Fin K, HasDerivAt (fun t : ℝ => ψ (x + lineVec j t) b) (Dψ b) 0 :=
    fun b => (hasDerivAt_pi.mp hψ) b
  have hk : ∀ b : Fin K, HasDerivAt
      (fun t : ℝ => C.c j (x + lineVec j t) a b * ψ (x + lineVec j t) b)
      (C.dc j x a b * ψ x b + C.c j x a b * Dψ b) 0 := by
    intro b
    have := (C.hasDerivAt_entry j x a b).fun_mul (hcomp b)
    have h0 : x + lineVec j (0 : ℝ) = x := by simp [lineVec]
    simpa [h0] using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (A := fun b (t : ℝ) =>
    C.c j (x + lineVec j t) a b * ψ (x + lineVec j t) b) fun b _ => hk b
  convert hsum using 1
  · funext t
    simp only [Matrix.mulVec, dotProduct]
  · rw [Pi.add_apply, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      ← Finset.sum_add_distrib]

/-- **`D̂_g` is the density-symmetric Dirac operator on plane waves**
(`lem:supp-density-symmetric`): for `ψ = e^{2πik·x} v`, at every point,
`A_k(x) ψ(x) = -(i/2) Σ_j (c^j (∂_j ψ + Ω_j ψ) + (∂_j (c^j ψ) + Ω_j c^j ψ))`, where `∂_j ψ` and
`∂_j (c^j ψ)` are the (unique) derivatives along the coordinate line. Together with
`op_single` this identifies `C.op` with `-(i/2) Σ_j (M_{c^j} ∇_j + ∇_j M_{c^j})` on
trigonometric polynomials. -/
theorem symbField_mulVec_eq_densitySymmetric (k : Fin d → ℤ) (v : Fin K → ℂ)
    (x : UnitAddTorus (Fin d)) {Dψ Dcψ : Fin d → Fin K → ℂ}
    (hψ : ∀ j, HasDerivAt (fun t : ℝ => planeWave k v (x + lineVec j t)) (Dψ j) 0)
    (hcψ : ∀ j, HasDerivAt
      (fun t : ℝ => C.c j (x + lineVec j t) *ᵥ planeWave k v (x + lineVec j t)) (Dcψ j) 0) :
    C.symbField k x *ᵥ planeWave k v x =
      (-(Complex.I / 2)) • ∑ j, (C.c j x *ᵥ (Dψ j + C.Ω j x *ᵥ planeWave k v x) +
        (Dcψ j + C.Ω j x *ᵥ (C.c j x *ᵥ planeWave k v x))) := by
  have hD : ∀ j, Dψ j = (2 * π * Complex.I * (k j : ℂ)) • planeWave k v x := by
    intro j
    have h1 := hasDerivAt_planeWave k v j x
    have h0 : x + lineVec j (0 : ℝ) = x := by simp [lineVec]
    exact (hψ j).unique (by simpa [h0] using h1)
  have hDc : ∀ j, Dcψ j = C.dc j x *ᵥ planeWave k v x + C.c j x *ᵥ Dψ j := fun j =>
    (hcψ j).unique (C.hasDerivAt_mulVec_line j x (hψ j))
  simp_rw [hDc, hD]
  set ψ := planeWave k v x
  rw [symbField_apply, pot_apply, Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec]
  have h2 : (-(Complex.I / 2)) * (2 * π * Complex.I * (k j : ℂ)) = ((π * k j : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have h3 : (((2 * π * (k j : ℝ) : ℝ) : ℂ)) = 2 * ((π * k j : ℝ) : ℂ) := by push_cast; ring
  rw [h3]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

end Coeffs

/-! ### Non-vacuity: the flat periodic torus -/

section flat

/-- Constant coefficients `c^j(x) = c^j`, `Ω = 0`. -/
def constCoeffs (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (hc : ∀ j, (c j)ᴴ = c j) :
    Coeffs d K where
  c j := ContinuousMap.const _ (c j)
  dc _ := 0
  Ω _ := 0
  c_herm j _ := hc j
  Ω_skew _ _ := by simp
  hasDerivAt_c j _ v := by simpa using hasDerivAt_const (0 : ℝ) (c j *ᵥ v)

theorem constCoeffs_symbField (c : Fin d → Matrix (Fin K) (Fin K) ℂ) (hc : ∀ j, (c j)ᴴ = c j)
    (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    (constCoeffs c hc).symbField k x = symbol c k := by
  rw [Coeffs.symbField_apply, Coeffs.pot_apply]
  simp [constCoeffs, symbol]

/-- **The flat periodic torus gives a stable lattice discretization** of the constant-coefficient
operator (`cor:supp-flat-torus-spin`): the frozen Wilson stage operators, (A2) from the Fourier
Gårding estimate, (A3) from the plane-wave symbol limit. -/
def flatDiscretization (D : DoubledFlatData d K) :
    (constCoeffs D.c D.herm).LatticeDiscretization where
  stage n := stage d K (n + 1) D.ϖ D.c D.Γ
  stage_selfAdjoint _ := isSelfAdjoint_stage D.ϖ D.c D.Γ D.herm D.normal_herm
  graphConst := Real.sqrt (max 1 (min D.lam (D.ϖ ^ 2))⁻¹)
  graphConst_nonneg := Real.sqrt_nonneg _
  discreteNorm_le _ u := discreteNorm_le D.ϖ D.c D.Γ D.lam D.Lam D.lam_pos D.wilson_ne
    D.Lam_nonneg D.g D.clifford D.herm D.normal_herm D.low D.up u
  planeWave_tendsto k v := by
    have h := tendsto_embed_stage_adjoint_modeVec D.ϖ D.c D.Γ k (WithLp.toLp 2 v)
    rw [modeVec_eq_vecL2, modeVec_eq_vecL2] at h
    have e : vecL2 (mulVecCM ((constCoeffs D.c D.herm).symbField k) (planeWave k v)) =
        vecL2 (planeWave k ((WithLp.toLp 2 (symbol D.c k *ᵥ v) : Fiber K) : Fin K → ℂ)) := by
      congr 1
      ext x a
      simp [mulVecCM, planeWave, constCoeffs_symbField, Matrix.mulVec_smul]
    rw [e]
    exact h

/-- **Non-vacuity** (Pauli matrices on the flat two-torus, doubled module, `ϖ = 1`, `z = i`):
the stable-discretization theorem applies, and the self-adjoint realisation it produces has
domain `H¹`. -/
example : Tendsto (fun n =>
    ‖(embed 2 (2 * 2) (n + 1)).toContinuousLinearMap ∘L
      ((flatDiscretization (ofUndoubled pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford
        Matrix.PosDef.one 1 one_pos)).toStable
          (ofUndoubled pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford Matrix.PosDef.one 1
            one_pos).herm).stageRes n (z := Complex.I) (by simp) ∘L
      ContinuousLinearMap.adjoint (embed 2 (2 * 2) (n + 1)).toContinuousLinearMap -
      ((flatDiscretization (ofUndoubled pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford
        Matrix.PosDef.one 1 one_pos)).dirac
          (ofUndoubled pauliCoeff 1 pauliCoeff_herm pauliCoeff_clifford Matrix.PosDef.one 1
            one_pos).herm).resolvent Complex.I (by simp)‖) atTop (𝓝 0) :=
  Coeffs.LatticeDiscretization.tendsto_norm_resolvent _ _ (by simp)

end flat

/-! ### The covariant Wilson stages with sampled variable coefficients -/

section covariant

open CovariantWilsonGarding VariableWilsonGarding FrozenWilsonGarding LatticeTorusPlancherel

variable {m : ℕ} [NeZero m]

theorem covSymmetricDifference_add' (h : ℝ) (U : TorusLinks d m K) (j : Fin d)
    (u v : TorusSection d m K) :
    covSymmetricDifference h U j (u + v) =
      covSymmetricDifference h U j u + covSymmetricDifference h U j v := by
  funext x
  simp only [covSymmetricDifference, covShift, covShiftAdj, Pi.add_apply, Matrix.mulVec_add]
  rw [← smul_add]
  congr 1
  abel

theorem covSymmetricDifference_smul' (h : ℝ) (U : TorusLinks d m K) (j : Fin d) (a : ℂ)
    (u : TorusSection d m K) :
    covSymmetricDifference h U j (a • u) = a • covSymmetricDifference h U j u := by
  funext x
  simp only [covSymmetricDifference, covShift, covShiftAdj, Pi.smul_apply, Matrix.mulVec_smul]
  rw [← smul_sub, smul_comm]

theorem covWilsonTerm_add' (h : ℝ) (U : TorusLinks d m K) (u v : TorusSection d m K) :
    covWilsonTerm h U (u + v) = covWilsonTerm h U u + covWilsonTerm h U v := by
  funext x
  simp only [covWilsonTerm, covShift, covShiftAdj, Pi.add_apply, Matrix.mulVec_add]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_add]
  abel

theorem covWilsonTerm_smul' (h : ℝ) (U : TorusLinks d m K) (a : ℂ) (u : TorusSection d m K) :
    covWilsonTerm h U (a • u) = a • covWilsonTerm h U u := by
  funext x
  simp only [covWilsonTerm, covShift, covShiftAdj, Pi.smul_apply, Matrix.mulVec_smul]
  rw [smul_comm a ((2 * (h : ℂ))⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_sub, smul_sub, smul_comm a (2 : ℂ)]

theorem varMul_smul' (c : Grid d m → Matrix (Fin K) (Fin K) ℂ) (a : ℂ) (u : TorusSection d m K) :
    varMul c (a • u) = a • varMul c u := by
  funext x; simp [varMul, Matrix.mulVec_smul]

theorem covVarWilson_add (h ϖ : ℝ) (c : CoefficientField d m K) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (u v : TorusSection d m K) :
    covVarWilson h ϖ c U Γ (u + v) = covVarWilson h ϖ c U Γ u + covVarWilson h ϖ c U Γ v := by
  simp only [covVarWilson, varMul_add, covSymmetricDifference_add', covWilsonTerm_add',
    matMul_add', smul_add, Finset.sum_add_distrib]
  abel

theorem covVarWilson_smul (h ϖ : ℝ) (c : CoefficientField d m K) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (a : ℂ) (u : TorusSection d m K) :
    covVarWilson h ϖ c U Γ (a • u) = a • covVarWilson h ϖ c U Γ u := by
  simp only [covVarWilson, varMul_smul', covSymmetricDifference_smul', covWilsonTerm_smul',
    matMul_smul', smul_add, Finset.smul_sum, smul_comm a]

/-- The sampled coefficient field `x ↦ ĉ^j(x/m)` of `C` on the lattice torus `(ℤ/m)ᵈ`. -/
def Coeffs.sampled (C : Coeffs d K) (m : ℕ) [NeZero m] : CoefficientField d m K :=
  fun x j => C.c j (TorusCellEmbedding.samplePt x)

/-- The covariant Wilson operator `D̃^W_{g,h}` (`eq:supp-general-Wilson`, mesh `h = 1/m`) with
sampled variable coefficients and links `U`, on the stage space. -/
def covStageLin (C : Coeffs d K) (m : ℕ) [NeZero m] (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) : Stage d K m →ₗ[ℂ] Stage d K m where
  toFun v := eucl (covVarWilson (m : ℝ)⁻¹ ϖ (C.sampled m) U Γ (toSec v))
  map_add' v w := by
    change eucl (covVarWilson _ ϖ _ U Γ (toSec v + toSec w)) = _
    rw [covVarWilson_add]; rfl
  map_smul' a v := by
    change eucl (covVarWilson _ ϖ _ U Γ (a • toSec v)) = _
    rw [covVarWilson_smul]; rfl

/-- The covariant Wilson stage as a bounded operator. -/
def covStage (C : Coeffs d K) (m : ℕ) [NeZero m] (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) : Stage d K m →L[ℂ] Stage d K m :=
  LinearMap.toContinuousLinearMap (covStageLin C m ϖ U Γ)

theorem covStage_apply (C : Coeffs d K) (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (v : Stage d K m) :
    covStage C m ϖ U Γ v = eucl (covVarWilson (m : ℝ)⁻¹ ϖ (C.sampled m) U Γ (toSec v)) := rfl

/-- **Self-adjointness of the covariant Wilson stage** (`thm:supp-general-Wilson-ellipticity`:
"the symmetric placement of coefficients makes the finite operator self-adjoint"). -/
theorem isSelfAdjoint_covStage (C : Coeffs d K) (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ) (hΓU : ∀ j x, Γ * U j x = U j x * Γ) :
    IsSelfAdjoint (covStage C m ϖ U Γ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  change ⟪covStage C m ϖ U Γ v, w⟫_ℂ = ⟪v, covStage C m ϖ U Γ w⟫_ℂ
  rw [covStage_apply, covStage_apply, ← eucl_toSec w, ← eucl_toSec v, toSec_eucl, toSec_eucl,
    ← gridInner_eq_inner, ← gridInner_eq_inner]
  exact covVarWilson_symmetric _ ϖ _ U Γ (fun x j => C.c_herm j _) hΓ hΓU _ _

/-- **(A2) from the squared Gårding estimate.**  If the covariant Wilson operator at mesh
`h = 1/m` satisfies `‖u‖²_{1,h} ≤ C (‖D̃^Ω u‖²_h + ‖u‖²_h)` on all lattice sections (the conclusion
of `CovariantWilsonGarding.covariant_garding`, `eq:supp-general-Garding`), then the stage
operator satisfies (A2) in the normalisation of `FlatTorusSpinAtlas.discreteNorm`:
`‖v‖_{1,h} ≤ √C (‖D_h v‖ + ‖v‖)`. -/
theorem discreteNorm_covStage_le (C : Coeffs d K) (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) {G : ℝ} (hG0 : 0 ≤ G)
    (hgard : ∀ u : TorusSection d m K, h1NormSq (m : ℝ)⁻¹ u ≤
      G * (gridNormSq (m : ℝ)⁻¹ (covVarWilson (m : ℝ)⁻¹ ϖ (C.sampled m) U Γ u) +
        gridNormSq (m : ℝ)⁻¹ u))
    (v : Stage d K m) :
    discreteNorm d K m v ≤ Real.sqrt G * (‖covStage C m ϖ U Γ v‖ + ‖v‖) := by
  have key := hgard (phys v)
  have hD : gridNormSq (m : ℝ)⁻¹ (covVarWilson (m : ℝ)⁻¹ ϖ (C.sampled m) U Γ (phys v)) =
      ‖covStage C m ϖ U Γ v‖ ^ 2 := by
    rw [phys, covVarWilson_smul, gridNormSq_phys]
    rfl
  have hu : gridNormSq (m : ℝ)⁻¹ (phys v) = ‖v‖ ^ 2 := gridNormSq_phys_eq v
  rw [hD, hu] at key
  unfold discreteNorm
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖covStage C m ϖ U Γ v‖ + ‖v‖),
    ← Real.sqrt_mul hG0]
  refine Real.sqrt_le_sqrt (key.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ hG0
  nlinarith [norm_nonneg (covStage C m ϖ U Γ v), norm_nonneg v]

/-- **The covariant Wilson discretization** of `D̂_g` as a `LatticeDiscretization`, from the two
discrete estimates still to be verified for variable coefficients: the graph estimate (A2)
(`eq:supp-general-Garding` in the normalisation of `FlatTorusSpinAtlas.discreteNorm`) and the
plane-wave core condition (A3) (`lem:supp-general-core` on the periodic box). -/
def Coeffs.covariantDiscretization (C : Coeffs d K) (ϖ : ℝ) (U : ∀ n : ℕ, TorusLinks d (n + 1) K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ) (hΓU : ∀ n j x, Γ * U n j x = U n j x * Γ)
    (G : ℝ) (hG : 0 ≤ G)
    (hA2 : ∀ n (u : Stage d K (n + 1)),
      discreteNorm d K (n + 1) u ≤ G * (‖covStage C (n + 1) ϖ (U n) Γ u‖ + ‖u‖))
    (hA3 : ∀ (k : Fin d → ℤ) (v : Fin K → ℂ),
      Tendsto (fun n => embed d K (n + 1) (covStage C (n + 1) ϖ (U n) Γ
        (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap
          (vecL2 (planeWave k v))))) atTop
        (𝓝 (vecL2 (mulVecCM (C.symbField k) (planeWave k v))))) :
    C.LatticeDiscretization where
  stage n := covStage C (n + 1) ϖ (U n) Γ
  stage_selfAdjoint n := isSelfAdjoint_covStage C ϖ (U n) Γ hΓ (hΓU n)
  graphConst := G
  graphConst_nonneg := hG
  discreteNorm_le := hA2
  planeWave_tendsto := hA3

/-- The covariant Wilson discretization with (A2) supplied in the form of the squared Gårding
estimate of `CovariantWilsonGarding.covariant_garding` at every mesh, with one constant `G`. -/
def Coeffs.covariantDiscretizationOfGarding (C : Coeffs d K) (ϖ : ℝ)
    (U : ∀ n : ℕ, TorusLinks d (n + 1) K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (hΓ : Γᴴ = Γ) (hΓU : ∀ n j x, Γ * U n j x = U n j x * Γ)
    (G : ℝ) (hG : 0 ≤ G)
    (hgard : ∀ n (u : TorusSection d (n + 1) K), h1NormSq ((n + 1 : ℕ) : ℝ)⁻¹ u ≤
      G * (gridNormSq ((n + 1 : ℕ) : ℝ)⁻¹
          (covVarWilson ((n + 1 : ℕ) : ℝ)⁻¹ ϖ (C.sampled (n + 1)) (U n) Γ u) +
        gridNormSq ((n + 1 : ℕ) : ℝ)⁻¹ u))
    (hA3 : ∀ (k : Fin d → ℤ) (v : Fin K → ℂ),
      Tendsto (fun n => embed d K (n + 1) (covStage C (n + 1) ϖ (U n) Γ
        (ContinuousLinearMap.adjoint (embed d K (n + 1)).toContinuousLinearMap
          (vecL2 (planeWave k v))))) atTop
        (𝓝 (vecL2 (mulVecCM (C.symbField k) (planeWave k v))))) :
    C.LatticeDiscretization :=
  C.covariantDiscretization ϖ U Γ hΓ hΓU (Real.sqrt G) (Real.sqrt_nonneg _)
    (fun n u => discreteNorm_covStage_le C ϖ (U n) Γ hG (hgard n) u) hA3

end covariant

/-! ### Non-vacuity of the coefficient class: a genuinely variable coefficient -/

section variableExample

/-- The frequencies `±1` on the circle `𝕋¹`. -/
def freqOne : Fin 1 → ℤ := fun _ => 1

/-- The real scalar field `s(x) = 3 + e^{2πix} + e^{-2πix} = 3 + 2 cos 2πx` on `𝕋¹`. -/
def cosField : C(UnitAddTorus (Fin 1), ℂ) :=
  ContinuousMap.const _ 3 + mFourier freqOne + mFourier (-freqOne)

/-- Its derivative `2πi e^{2πix} - 2πi e^{-2πix} = -4π sin 2πx`. -/
def cosFieldDeriv : C(UnitAddTorus (Fin 1), ℂ) :=
  (2 * π * Complex.I) • mFourier freqOne - (2 * π * Complex.I) • mFourier (-freqOne)

theorem conj_cosField (x : UnitAddTorus (Fin 1)) : conj (cosField x) = cosField x := by
  simp only [cosField, ContinuousMap.add_apply, ContinuousMap.const_apply, map_add]
  rw [← mFourier_neg, ← mFourier_neg (n := -freqOne), neg_neg, map_ofNat]
  ring

theorem hasDerivAt_cosField (y : UnitAddTorus (Fin 1)) :
    HasDerivAt (fun t : ℝ => cosField (y + lineVec 0 t)) (cosFieldDeriv y) 0 := by
  have h1 := hasDerivAt_mFourier_line freqOne 0 y
  have h2 := hasDerivAt_mFourier_line (-freqOne) 0 y
  have h := ((hasDerivAt_const (0 : ℝ) (3 : ℂ)).fun_add h1).fun_add h2
  have hval : cosFieldDeriv y = 0 + 2 * π * Complex.I * ((freqOne 0 : ℤ) : ℂ) * mFourier freqOne y +
      2 * π * Complex.I * (((-freqOne) 0 : ℤ) : ℂ) * mFourier (-freqOne) y := by
    simp only [cosFieldDeriv, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      freqOne, Pi.neg_apply]
    push_cast
    ring
  rw [hval]
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [cosField, lineVec]

/-- **A non-constant coefficient** `c^1(x) = (3 + 2 cos 2πx) I` on `𝕋¹` (scalar fibre), with
`Ω = 0`: the class `Coeffs` contains genuinely variable coefficients. -/
def cosCoeffs : Coeffs 1 1 where
  c _ := cosField • ContinuousMap.const _ (1 : Matrix (Fin 1) (Fin 1) ℂ)
  dc _ := cosFieldDeriv • ContinuousMap.const _ (1 : Matrix (Fin 1) (Fin 1) ℂ)
  Ω _ := 0
  c_herm _ x := by
    simp only [ContinuousMap.smul_apply', ContinuousMap.const_apply, conjTranspose_smul,
      conjTranspose_one]
    rw [Complex.star_def, conj_cosField]
  Ω_skew _ _ := by simp
  hasDerivAt_c j y v := by
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have := (hasDerivAt_cosField y).smul_const v
    simpa [ContinuousMap.smul_apply', Matrix.smul_mulVec] using this

/-- The coefficient `cosCoeffs` takes the value `5 I` at `x = 0` (its minimum value is `1`). -/
theorem cosCoeffs_c_zero : cosCoeffs.c 0 0 = (5 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp only [cosCoeffs, ContinuousMap.smul_apply', ContinuousMap.const_apply, cosField,
    ContinuousMap.add_apply]
  rw [mFourier_neg]
  have h0 : mFourier freqOne (0 : UnitAddTorus (Fin 1)) = 1 := by
    rw [← sub_self (0 : UnitAddTorus (Fin 1))]
    simp [mFourier]
  rw [h0]
  norm_num

/-- Symmetry of `D̂_g` on all of `H¹` for the non-constant coefficient `cosCoeffs` (Fourier frame
`c₀ = 0`). -/
example (a b : ℓ²(Idx 1 1, ℂ)) :
    ⟪cosCoeffs.op (c₀ := fun _ => 0) (fun _ => by simp) a,
        sobolev (c := fun _ => 0) (fun _ => by simp) b⟫_ℂ =
      ⟪sobolev (c := fun _ => 0) (fun _ => by simp) a,
        cosCoeffs.op (c₀ := fun _ => 0) (fun _ => by simp) b⟫_ℂ :=
  cosCoeffs.op_symm _ a b

end variableExample

/-! ### The covariant Wilson operator on lattice plane waves (first step of (A3)) -/

section planeWaveSymbol

open CovariantWilsonGarding VariableWilsonGarding FrozenWilsonGarding LatticeTorusPlancherel
  TorusCellEmbedding

variable {m : ℕ} [NeZero m]

/-- The local symbol of the covariant Wilson operator on the lattice plane wave
`x ↦ χ(x) w`, `χ(x + e_j) = ω_j χ(x)`:
`½ Σ_j (c^j(x) P_j(x) + Q_j(x)) + ϖ Γ W(x)` with
`P_j = (2ih)⁻¹ (ω_j U_j(x) - ω̄_j U_j(x-e_j)^*)`,
`Q_j = (2ih)⁻¹ (ω_j U_j(x) c^j(x+e_j) - ω̄_j U_j(x-e_j)^* c^j(x-e_j))`,
`W = (2h)⁻¹ Σ_j (2 - ω_j U_j(x) - ω̄_j U_j(x-e_j)^*)`. -/
noncomputable def covPlaneSymbol (h ϖ : ℝ) (c : CoefficientField d m K) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (ω : Fin d → ℂ) (x : Grid d m) :
    Matrix (Fin K) (Fin K) ℂ :=
  (2 : ℂ)⁻¹ • ∑ j, (c x j * ((2 * Complex.I * (h : ℂ))⁻¹ •
        (ω j • U j x - conj (ω j) • (U j (x - Pi.single j 1))ᴴ)) +
      (2 * Complex.I * (h : ℂ))⁻¹ • (ω j • (U j x * c (x + Pi.single j 1) j) -
        conj (ω j) • ((U j (x - Pi.single j 1))ᴴ * c (x - Pi.single j 1) j))) +
    (ϖ : ℂ) • (Γ * ((2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • (1 : Matrix (Fin K) (Fin K) ℂ) -
      ω j • U j x - conj (ω j) • (U j (x - Pi.single j 1))ᴴ)))

/-- **Exact action on lattice plane waves**: for the character `χ = latticeChar ℓ`,
`D̃^Ω (χ w) = χ · covPlaneSymbol(ω) w` with `ω_j = χ(e_j)`. -/
theorem covVarWilson_planeWave (h ϖ : ℝ) (c : CoefficientField d m K) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (ℓ : Grid d m) (w : Fin K → ℂ) :
    covVarWilson h ϖ c U Γ (fun x => latticeChar ℓ x • w) =
      fun x => latticeChar ℓ x • (covPlaneSymbol h ϖ c U Γ
        (fun j => latticeChar ℓ (Pi.single j 1)) x *ᵥ w) := by
  funext x
  have hp : ∀ j, latticeChar ℓ (x + Pi.single j 1) =
      latticeChar ℓ x * latticeChar ℓ (Pi.single j 1) := fun j => latticeChar_add_right _ _ _
  have hm : ∀ j, latticeChar ℓ (x - Pi.single j 1) =
      latticeChar ℓ x * conj (latticeChar ℓ (Pi.single j 1)) := fun j =>
    latticeChar_sub_right _ _ _
  simp only [covVarWilson, covSymmetricDifference, covWilsonTerm, covShift, covShiftAdj, varMul,
    coeff, matMul, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, hp, hm, covPlaneSymbol]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_sum, Matrix.one_mulVec, smul_add, smul_sub, Finset.smul_sum, smul_smul]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by module

/-- **The covariant stage on sampled plane waves**: with `S_h = (𝒥⁰_h)^*`,
`D_h S_h (e^{2πik·x} v) = γ_h(k) m^{-d/2} χ_k(x) · covPlaneSymbol(x) v`, `χ_k` the lattice
character of `k`, `γ_h(k) = modeFactor → 1`.  (A3) on plane waves is thereby reduced to the
uniform convergence `covPlaneSymbol(x) → A_k(x/m)` and the continuity of `A_k e_k`. -/
theorem covStage_adjoint_modeVec (C : Coeffs d K) (ϖ : ℝ) (U : TorusLinks d m K)
    (Γ : Matrix (Fin K) (Fin K) ℂ) (k : Fin d → ℤ) (v : Fiber K) :
    covStage C m ϖ U Γ
        (ContinuousLinearMap.adjoint (embed d K m).toContinuousLinearMap (modeVec k v)) =
      modeFactor m k • eucl (((scale m d : ℝ) : ℂ)⁻¹ • fun x => latticeChar (zcast m k) x •
        (covPlaneSymbol (m : ℝ)⁻¹ ϖ (C.sampled m) U Γ
          (fun j => latticeChar (zcast m k) (Pi.single j 1)) x *ᵥ (v : Fin K → ℂ))) := by
  rw [embed_adjoint_modeVec, map_smul, covStage_apply, toSec_stageWave, covVarWilson_smul,
    covVarWilson_planeWave]

end planeWaveSymbol

end RenewalGeometry.VariableTorusDirac
