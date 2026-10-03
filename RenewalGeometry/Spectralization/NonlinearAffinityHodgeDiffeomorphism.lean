/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.NonlinearAffinityHodgeExact
/-!
# The affinity map is a diffeomorphism; strict convexity of the affinity functional

This file completes `thm:supp-nonlinear-Hodge` and `thm:summary-affinity` of
`papers/predictive_spectral_geometry` on top of `NonlinearAffinityHodgeExact` (coercivity,
existence/uniqueness of the mean-zero minimiser, bijectivity of the affinity map).

* **Strict convexity.**  `log cosh` is strictly convex (`strictConvexOn_logCosh`, its derivative
  `tanh` is strictly increasing), and the affinity functional
  `𝓕_α(φ) = Σ_e c_e log cosh(a₀_e + (Bᵀφ)_e)` is strictly convex on the mean-zero potentials
  (`strictConvexOn_affinityFunctional`), because `Bᵀ` is injective there.  Uniqueness of the
  minimiser follows directly (`meanZeroMinimizer_unique_of_strictConvexOn`).
* **Calculus of `artanh`.**  `artanh' (y) = 1/(1-y²)` and `artanh` is `C^∞` on `(-1,1)`
  (`hasDerivAt_artanh`, `contDiffAt_artanh`).
* **Diffeomorphism.**  On the open subset `𝒥(G,c) = {j ∈ Ker B : |j| < c}` of the
  finite-dimensional space `Ker B`, the affinity map `𝔄 : j ↦ [artanh(j/c)] ∈ H¹(G;ℝ)` is `C^∞`,
  its derivative `v ↦ [diag(1/(c(1-(j/c)²))) v]` is a linear isomorphism `Ker B ≃ H¹` (injective
  by the positive weighted pairing, and `dim Ker B = dim H¹` by rank–nullity and
  `rank Bᵀ = rank B`), so by the inverse function theorem the global inverse
  `α ↦ j_α` (well defined by bijectivity) agrees near every point with a `C^∞` local inverse.
  The result is packaged as an `OpenPartialHomeomorph` from `Ker B` to `H¹(G;ℝ)` with source
  `𝒥(G,c)`, target everything, `C^∞` in both directions (`affinityPartialHomeomorph`,
  `affinity_diffeomorphism`).
* The inverse is the variational one: `j_α = c tanh(a₀ + Bᵀφ_α)` for the mean-zero minimiser
  `φ_α` (`classCurrent_mk_eq_currentOfPotential`), and the directed generator
  `k = (c + j_α)/m` is a function of the class (`summary_affinity`).

`H¹(G;ℝ) = ℝ^E / Ran Bᵀ` carries its quotient norm (`Ran Bᵀ` is closed, being
finite-dimensional).
-/

open Matrix Finset Filter Topology Set
open scoped ContDiff

namespace RenewalGeometry
namespace NonlinearAffinityHodge

open ModularAffinityReversalPacket

/-! ## Strict convexity of `log cosh` -/

/-- `tanh` is strictly increasing. -/
theorem strictMono_tanh : StrictMono Real.tanh := fun x y hxy => by
  by_contra h
  push Not at h
  have := Real.artanh_le_artanh (Real.neg_one_lt_tanh y) (Real.tanh_lt_one x) h
  rw [Real.artanh_tanh, Real.artanh_tanh] at this
  linarith

/-- `(log cosh)' = tanh`. -/
theorem hasDerivAt_logCosh (x : ℝ) :
    HasDerivAt (fun t => Real.log (Real.cosh t)) (Real.tanh x) x := by
  have h := (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  exact h

/-- `log cosh` is strictly convex on `ℝ`. -/
theorem strictConvexOn_logCosh : StrictConvexOn ℝ univ (fun t => Real.log (Real.cosh t)) := by
  have hd : deriv (fun t => Real.log (Real.cosh t)) = Real.tanh :=
    funext fun x => (hasDerivAt_logCosh x).deriv
  refine StrictMonoOn.strictConvexOn_of_deriv convex_univ ?_ ?_
  · exact (Real.continuous_cosh.log fun t => (Real.cosh_pos t).ne').continuousOn
  · rw [hd]
    exact strictMono_tanh.strictMonoOn _

/-! ## Strict convexity of the affinity functional on mean-zero potentials -/

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The mean-zero vertex potentials `V₀ = {φ : Σ_x φ_x = 0}`. -/
def meanZeroPotentials (V : Type*) [Fintype V] : Set (V → ℝ) := {φ | ∑ x, φ x = 0}

theorem convex_meanZeroPotentials : Convex ℝ (meanZeroPotentials V) := by
  have : meanZeroPotentials V = (LinearMap.ker (sumLinear V) : Set (V → ℝ)) := by
    ext φ
    simp [meanZeroPotentials, sumLinear]
  rw [this]
  exact (LinearMap.ker (sumLinear V)).convex

variable {B : Matrix V E ℝ} {c a₀ : E → ℝ}

/-- On mean-zero potentials, `Bᵀ` is injective for a connected incidence. -/
theorem eq_of_transpose_mulVec_eq (hB : IsConnectedIncidence B) {φ ψ : V → ℝ}
    (hφ : φ ∈ meanZeroPotentials V) (hψ : ψ ∈ meanZeroPotentials V)
    (h : Bᵀ *ᵥ φ = Bᵀ *ᵥ ψ) : φ = ψ := by
  have hk : φ - ψ ∈ LinearMap.ker (gradientMean B) := by
    rw [LinearMap.mem_ker]
    refine Prod.ext ?_ ?_
    · show Bᵀ *ᵥ (φ - ψ) = 0
      rw [mulVec_sub, h, sub_self]
    · show ∑ x, (φ - ψ) x = 0
      simp only [meanZeroPotentials, mem_ofPred_eq] at hφ hψ
      simp [sum_sub_distrib, hφ, hψ]
  rw [gradientMean_ker hB, Submodule.mem_bot] at hk
  exact sub_eq_zero.mp hk

/-- **Strict convexity** (thm:supp-nonlinear-Hodge): for a connected incidence and positive
conductances, `𝓕_α(φ) = Σ_e c_e log cosh(a₀_e + (Bᵀφ)_e)` is strictly convex on the mean-zero
potentials. -/
theorem strictConvexOn_affinityFunctional (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    (a₀ : E → ℝ) : StrictConvexOn ℝ (meanZeroPotentials V) (affinityFunctional B c a₀) := by
  refine ⟨convex_meanZeroPotentials, fun φ hφ ψ hψ hne s t hs ht hst => ?_⟩
  set x : E → ℝ := fun e => a₀ e + (Bᵀ *ᵥ φ) e
  set y : E → ℝ := fun e => a₀ e + (Bᵀ *ᵥ ψ) e
  have harg : ∀ e, a₀ e + (Bᵀ *ᵥ (s • φ + t • ψ)) e = s * x e + t * y e := by
    intro e
    simp only [x, y, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : a₀ e = s * a₀ e + t * a₀ e := by rw [← add_mul, hst, one_mul]
    linarith
  have hconv := strictConvexOn_logCosh
  have hle : ∀ e, c e * Real.log (Real.cosh (s * x e + t * y e)) ≤
      s * (c e * Real.log (Real.cosh (x e))) + t * (c e * Real.log (Real.cosh (y e))) := by
    intro e
    have := hconv.convexOn.2 (mem_univ (x e)) (mem_univ (y e)) hs.le ht.le hst
    simp only [smul_eq_mul] at this
    nlinarith [hc e]
  -- some edge separates the two arguments
  obtain ⟨e₀, he₀⟩ : ∃ e, x e ≠ y e := by
    by_contra hall
    push Not at hall
    apply hne
    refine eq_of_transpose_mulVec_eq hB hφ hψ (funext fun e => ?_)
    have := hall e
    simp only [x, y] at this
    linarith
  have hlt : c e₀ * Real.log (Real.cosh (s * x e₀ + t * y e₀)) <
      s * (c e₀ * Real.log (Real.cosh (x e₀))) + t * (c e₀ * Real.log (Real.cosh (y e₀))) := by
    have := hconv.2 (mem_univ (x e₀)) (mem_univ (y e₀)) he₀ hs ht hst
    simp only [smul_eq_mul] at this
    nlinarith [hc e₀]
  simp only [affinityFunctional, smul_eq_mul, harg]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_lt_sum (fun e _ => hle e) ⟨e₀, mem_univ _, hlt⟩

/-- Uniqueness of the mean-zero minimiser via strict convexity (the paper's route). -/
theorem meanZeroMinimizer_unique_of_strictConvexOn (hB : IsConnectedIncidence B)
    (hc : ∀ e, 0 < c e) {φ φ' : V → ℝ} (hφ : IsMeanZeroMinimizer B c a₀ φ)
    (hφ' : IsMeanZeroMinimizer B c a₀ φ') : φ = φ' := by
  have hmin : ∀ {ψ}, IsMeanZeroMinimizer B c a₀ ψ →
      IsMinOn (affinityFunctional B c a₀) (meanZeroPotentials V) ψ :=
    fun hψ χ hχ => hψ.2 χ hχ
  exact (strictConvexOn_affinityFunctional hB hc a₀).eq_of_isMinOn (hmin hφ) (hmin hφ') hφ.1 hφ'.1

/-! ## Calculus of `artanh` on `(-1, 1)` -/

/-- On `(-1,1)`, `artanh y = ½ log((1+y)/(1-y))` near `y`. -/
theorem artanh_eventuallyEq {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh =ᶠ[𝓝 y] fun t => 1 / 2 * Real.log ((1 + t) / (1 - t)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
  exact Real.artanh_eq_half_log (Ioo_subset_Icc_self ht)

/-- `artanh' (y) = 1/(1-y²)` on `(-1,1)`. -/
theorem hasDerivAt_artanh {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - y ^ 2)) y := by
  have h1 : 0 < 1 + y := by linarith [hy.1]
  have h2 : 0 < 1 - y := by linarith [hy.2]
  have hq : HasDerivAt (fun t : ℝ => (1 + t) / (1 - t))
      ((1 * (1 - y) - (1 + y) * (-1)) / (1 - y) ^ 2) y :=
    ((hasDerivAt_id y).const_add 1).div ((hasDerivAt_id y).const_sub 1) h2.ne'
  have hlog := (hq.log (div_pos h1 h2).ne').const_mul (1 / 2 : ℝ)
  refine (hlog.congr_of_eventuallyEq (artanh_eventuallyEq hy)).congr_deriv ?_
  have h3 : 1 - y ^ 2 = (1 + y) * (1 - y) := by ring
  rw [h3]
  field_simp
  ring

/-- `artanh` is `C^n` on `(-1,1)` for every `n`. -/
theorem contDiffAt_artanh {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n Real.artanh y := by
  have h1 : 0 < 1 + y := by linarith [hy.1]
  have h2 : 0 < 1 - y := by linarith [hy.2]
  have hq : ContDiffAt ℝ n (fun t : ℝ => (1 + t) / (1 - t)) y :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id) h2.ne'
  have hlog : ContDiffAt ℝ n (fun t : ℝ => 1 / 2 * Real.log ((1 + t) / (1 - t))) y :=
    contDiffAt_const.mul (hq.log (div_pos h1 h2).ne')
  exact hlog.congr_of_eventuallyEq (artanh_eventuallyEq hy)

/-! ## The affinity map on the open current box -/

/-- The open current box `{j : |j_e| < c_e}`; the fibre is its intersection with `Ker B`. -/
def currentBox (c : E → ℝ) : Set (E → ℝ) := {j | ∀ e, |j e| < c e}

theorem isOpen_currentBox (c : E → ℝ) : IsOpen (currentBox c) := by
  have : currentBox c = ⋂ e, {j : E → ℝ | |j e| < c e} := by
    ext j
    simp [currentBox]
  rw [this]
  exact isOpen_iInter_of_finite fun e =>
    isOpen_lt ((continuous_apply e).abs) continuous_const

/-- The derivative weights `w_e = 1/(c_e (1 - (j_e/c_e)²)) > 0` of `j ↦ artanh(j/c)`. -/
noncomputable def affinityWeight (c j : E → ℝ) (e : E) : ℝ :=
  1 / (c e * (1 - (j e / c e) ^ 2))

theorem affinityWeight_pos (hc : ∀ e, 0 < c e) {j : E → ℝ} (hj : j ∈ currentBox c) (e : E) :
    0 < affinityWeight c j e := by
  have hy := div_mem_Ioo_of_abs_lt (hj e)
  have : 0 < 1 - (j e / c e) ^ 2 := by nlinarith [hy.1, hy.2]
  exact one_div_pos.mpr (mul_pos (hc e) this)

/-- The diagonal derivative `v ↦ w ⊙ v`. -/
noncomputable def affinityDeriv (c j : E → ℝ) : (E → ℝ) →L[ℝ] (E → ℝ) :=
  ContinuousLinearMap.pi fun e => affinityWeight c j e • ContinuousLinearMap.proj e

theorem affinityDeriv_apply (c j v : E → ℝ) (e : E) :
    affinityDeriv c j v e = affinityWeight c j e * v e := rfl

/-- `D(artanh(j/c)) = diag(w)`. -/
theorem hasFDerivAt_affinity (hc : ∀ e, 0 < c e) {j : E → ℝ} (hj : j ∈ currentBox c) :
    HasFDerivAt (affinity c) (affinityDeriv c j) j := by
  rw [hasFDerivAt_pi']
  intro e
  have hy := div_mem_Ioo_of_abs_lt (hj e)
  have hlin : HasFDerivAt (fun x : E → ℝ => x e / c e)
      ((c e)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : E => ℝ) e) j := by
    have := (hasFDerivAt_apply (𝕜 := ℝ) e j).mul_const (c e)⁻¹
    refine (this.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · ext v
      simp [mul_comm]
    · simp [div_eq_mul_inv]
  have hcomp := (hasDerivAt_artanh hy).comp_hasFDerivAt j hlin
  refine hcomp.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, affinityDeriv, ContinuousLinearMap.pi_apply,
    affinityWeight]
  have hce := (hc e).ne'
  have hy2 : 1 - (j e / c e) ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
  field_simp

/-- `j ↦ artanh(j/c)` is `C^n` on the open current box. -/
theorem contDiffAt_affinity {j : E → ℝ} (hj : j ∈ currentBox c) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (affinity c) j := by
  refine contDiffAt_pi.2 fun e => ?_
  have hy := div_mem_Ioo_of_abs_lt (hj e)
  exact (contDiffAt_artanh hy).comp j ((contDiffAt_apply ℝ ℝ e j).div_const (c e))

/-! ## `H¹(G;ℝ)` as a finite-dimensional normed space -/

/-- `Ran Bᵀ` is closed (finite dimension), so `H¹(G;ℝ) = ℝ^E / Ran Bᵀ` is a normed space. -/
instance isClosed_range_mulVecLin_transpose (B : Matrix V E ℝ) :
    IsClosed ((LinearMap.range (Matrix.mulVecLin Bᵀ) : Submodule ℝ (E → ℝ)) : Set (E → ℝ)) :=
  Submodule.closed_of_finiteDimensional _

/-- The quotient map `ℝ^E → H¹(G;ℝ)` as a continuous linear map. -/
noncomputable def cohomologyMap (B : Matrix V E ℝ) : (E → ℝ) →L[ℝ] FirstCohomology B :=
  LinearMap.toContinuousLinearMap (Submodule.mkQ _)

theorem cohomologyMap_apply (B : Matrix V E ℝ) (a : E → ℝ) :
    cohomologyMap B a = Submodule.Quotient.mk a := rfl

/-- The divergence-free currents `Ker B`. -/
abbrev Cycles (B : Matrix V E ℝ) : Submodule ℝ (E → ℝ) := LinearMap.ker (Matrix.mulVecLin B)

/-- **`dim Ker B = dim H¹(G;ℝ)`** (rank–nullity and `rank Bᵀ = rank B`). -/
theorem finrank_cycles_eq_finrank_firstCohomology (B : Matrix V E ℝ) :
    Module.finrank ℝ (Cycles B) = Module.finrank ℝ (FirstCohomology B) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (Matrix.mulVecLin Bᵀ))
  have h3 : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin Bᵀ)) =
      Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin B)) := by
    have := Matrix.rank_transpose B
    simpa only [Matrix.rank] using this
  unfold Cycles FirstCohomology
  omega

/-! ## The affinity map on `Ker B` and its derivative -/

/-- The fibre `𝒥(G,c)` as a subset of the cycle space `Ker B`. -/
def fibreCycles (B : Matrix V E ℝ) (c : E → ℝ) : Set (Cycles B) :=
  {v | (v : E → ℝ) ∈ currentBox c}

theorem isOpen_fibreCycles (B : Matrix V E ℝ) (c : E → ℝ) : IsOpen (fibreCycles B c) :=
  (isOpen_currentBox c).preimage continuous_subtype_val

theorem mem_fibreCycles_iff {v : Cycles B} :
    v ∈ fibreCycles B c ↔ (v : E → ℝ) ∈ CurrentFibre B c :=
  ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩

theorem mem_currentFibre_iff {j : E → ℝ} :
    j ∈ CurrentFibre B c ↔ j ∈ Cycles B ∧ j ∈ currentBox c := Iff.rfl

/-- The affinity map `𝔄 : Ker B → H¹(G;ℝ)`, `v ↦ [artanh(v/c)]`. -/
noncomputable def affinityClassCycles (B : Matrix V E ℝ) (c : E → ℝ) (v : Cycles B) :
    FirstCohomology B :=
  affinityClass B c v

theorem affinityClassCycles_eq (B : Matrix V E ℝ) (c : E → ℝ) :
    affinityClassCycles B c = cohomologyMap B ∘ affinity c ∘ (Cycles B).subtypeL := rfl

/-- The derivative of `𝔄` at `j`: `v ↦ [w ⊙ v]`. -/
noncomputable def affinityClassDeriv (B : Matrix V E ℝ) (c j : E → ℝ) :
    Cycles B →L[ℝ] FirstCohomology B :=
  (cohomologyMap B).comp ((affinityDeriv c j).comp (Cycles B).subtypeL)

theorem hasFDerivAt_affinityClassCycles (hc : ∀ e, 0 < c e) {v : Cycles B}
    (hv : v ∈ fibreCycles B c) :
    HasFDerivAt (affinityClassCycles B c) (affinityClassDeriv B c v) v := by
  rw [affinityClassCycles_eq]
  exact (cohomologyMap B).hasFDerivAt.comp v
    ((hasFDerivAt_affinity hc hv).comp v (Cycles B).subtypeL.hasFDerivAt)

theorem contDiffAt_affinityClassCycles {v : Cycles B} (hv : v ∈ fibreCycles B c)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (affinityClassCycles B c) v := by
  rw [affinityClassCycles_eq]
  exact (cohomologyMap B).contDiff.contDiffAt.comp v
    ((contDiffAt_affinity hv).comp v (Cycles B).subtypeL.contDiff.contDiffAt)

/-- The derivative `v ↦ [w ⊙ v]` is injective on `Ker B` for positive weights: if
`w ⊙ v = Bᵀφ` then `Σ_e w_e v_e² = ⟨v, Bᵀφ⟩ = ⟨Bv, φ⟩ = 0`. -/
theorem affinityClassDeriv_injective (hc : ∀ e, 0 < c e) {j : E → ℝ} (hj : j ∈ currentBox c) :
    Function.Injective (affinityClassDeriv B c j) := by
  refine (injective_iff_map_eq_zero (affinityClassDeriv B c j)).2 fun v hv => ?_
  have hmem : affinityDeriv c j v ∈ LinearMap.range (Matrix.mulVecLin Bᵀ) :=
    (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨φ, hφ⟩ := LinearMap.mem_range.1 hmem
  rw [Matrix.mulVecLin_apply] at hφ
  have hBv : B *ᵥ (v : E → ℝ) = 0 := v.2
  have hpair : ∑ e, affinityWeight c j e * (v : E → ℝ) e ^ 2 = 0 := by
    have h1 : (v : E → ℝ) ⬝ᵥ (Bᵀ *ᵥ φ) = 0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hBv, zero_dotProduct]
    rw [hφ] at h1
    rw [← h1]
    simp only [dotProduct, affinityDeriv_apply]
    exact sum_congr rfl fun e _ => by ring
  have hzero := (sum_eq_zero_iff_of_nonneg fun e _ =>
    mul_nonneg (affinityWeight_pos hc hj e).le (sq_nonneg _)).1 hpair
  ext e
  have := hzero e (mem_univ e)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (affinityWeight_pos hc hj e).ne'
  · simpa using h

/-- The derivative of `𝔄` is a linear isomorphism `Ker B ≃ H¹(G;ℝ)`. -/
noncomputable def affinityClassDerivEquiv (hc : ∀ e, 0 < c e) {j : E → ℝ}
    (hj : j ∈ currentBox c) : Cycles B ≃L[ℝ] FirstCohomology B :=
  (LinearEquiv.ofBijective (affinityClassDeriv B c j : Cycles B →ₗ[ℝ] FirstCohomology B)
    ⟨affinityClassDeriv_injective hc hj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (finrank_cycles_eq_finrank_firstCohomology B)).1
        (affinityClassDeriv_injective hc hj)⟩).toContinuousLinearEquiv

theorem coe_affinityClassDerivEquiv (hc : ∀ e, 0 < c e) {j : E → ℝ} (hj : j ∈ currentBox c) :
    ((affinityClassDerivEquiv (B := B) hc hj : Cycles B →L[ℝ] FirstCohomology B)) =
      affinityClassDeriv B c j := by
  ext v
  rfl

/-! ## The global inverse `α ↦ j_α` and its smoothness -/

/-- The inverse of the affinity map, `α ↦ j_α` (the unique fibre current of class `α`;
junk outside the hypotheses of `affinityClass_bijOn`). -/
noncomputable def classCurrent (B : Matrix V E ℝ) (c : E → ℝ) (α : FirstCohomology B) :
    E → ℝ :=
  Function.invFunOn (affinityClass B c) (CurrentFibre B c) α

variable (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
include hB hc

theorem classCurrent_mem (α : FirstCohomology B) : classCurrent B c α ∈ CurrentFibre B c :=
  Function.invFunOn_mem ((affinityClass_bijOn hB hc).surjOn (mem_univ α))

theorem affinityClass_classCurrent (α : FirstCohomology B) :
    affinityClass B c (classCurrent B c α) = α :=
  Function.invFunOn_eq ((affinityClass_bijOn hB hc).surjOn (mem_univ α))

theorem classCurrent_affinityClass {j : E → ℝ} (hj : j ∈ CurrentFibre B c) :
    classCurrent B c (affinityClass B c j) = j :=
  (affinityClass_bijOn hB hc).injOn (classCurrent_mem hB hc _) hj
    (affinityClass_classCurrent hB hc _)

/-- The inverse as a map into `Ker B`. -/
noncomputable def classCycle (α : FirstCohomology B) : Cycles B :=
  ⟨classCurrent B c α, (classCurrent_mem hB hc α).1⟩

theorem classCycle_mem (α : FirstCohomology B) : classCycle hB hc α ∈ fibreCycles B c :=
  (classCurrent_mem hB hc α).2

theorem affinityClassCycles_classCycle (α : FirstCohomology B) :
    affinityClassCycles B c (classCycle hB hc α) = α :=
  affinityClass_classCurrent hB hc α

theorem classCycle_affinityClassCycles {v : Cycles B} (hv : v ∈ fibreCycles B c) :
    classCycle hB hc (affinityClassCycles B c v) = v :=
  Subtype.ext (classCurrent_affinityClass hB hc (mem_fibreCycles_iff.1 hv))

/-- **Smoothness of the inverse** (inverse function theorem, globalised by bijectivity):
`α ↦ j_α` is `C^∞` from `H¹(G;ℝ)` to `Ker B`. -/
theorem contDiff_classCycle : ContDiff ℝ ∞ (classCycle hB hc) := by
  refine contDiff_iff_contDiffAt.2 fun α => ?_
  set v := classCycle hB hc α
  have hv : v ∈ fibreCycles B c := classCycle_mem hB hc α
  have hfC : ContDiffAt ℝ ∞ (affinityClassCycles B c) v := contDiffAt_affinityClassCycles hv
  have hv' : (v : E → ℝ) ∈ currentBox c := hv
  have hfD : HasFDerivAt (affinityClassCycles B c)
      ((affinityClassDerivEquiv (B := B) hc hv' : Cycles B →L[ℝ] FirstCohomology B)) v := by
    rw [coe_affinityClassDerivEquiv]
    exact hasFDerivAt_affinityClassCycles hc hv
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hfC.hasStrictFDerivAt' hfD hn
  have hloc : ∀ᶠ w in 𝓝 v, classCycle hB hc (affinityClassCycles B c w) = w :=
    Filter.eventually_of_mem ((isOpen_fibreCycles B c).mem_nhds hv) fun w hw =>
      classCycle_affinityClassCycles hB hc hw
  have heq := hs.localInverse_unique hloc
  have hinv := hfC.to_localInverse hfD hn
  have hfv : affinityClassCycles B c v = α := affinityClassCycles_classCycle hB hc α
  rw [hfv] at heq hinv
  exact hinv.congr_of_eventuallyEq heq

/-- `α ↦ j_α` is `C^∞` as a map `H¹(G;ℝ) → ℝ^E`. -/
theorem contDiff_classCurrent : ContDiff ℝ ∞ (classCurrent B c) :=
  (Cycles B).subtypeL.contDiff.comp (contDiff_classCycle hB hc)

/-- **The affinity diffeomorphism** `𝒥(G,c) ≅ H¹(G;ℝ)` as an open partial homeomorphism from
`Ker B` with source the fibre and target all of `H¹`. -/
noncomputable def affinityPartialHomeomorph : OpenPartialHomeomorph (Cycles B) (FirstCohomology B)
    where
  toFun := affinityClassCycles B c
  invFun := classCycle hB hc
  source := fibreCycles B c
  target := univ
  map_source' _ _ := mem_univ _
  map_target' α _ := classCycle_mem hB hc α
  left_inv' _ hv := classCycle_affinityClassCycles hB hc hv
  right_inv' α _ := affinityClassCycles_classCycle hB hc α
  open_source := isOpen_fibreCycles B c
  open_target := isOpen_univ
  continuousOn_toFun := fun _ hv => (contDiffAt_affinityClassCycles (n := 0) hv).continuousAt
    |>.continuousWithinAt
  continuousOn_invFun := (contDiff_classCycle hB hc).continuous.continuousOn

/-- **`thm:supp-nonlinear-Hodge`, diffeomorphism clause.**  The affinity map
`𝔄 : 𝒥(G,c) → H¹(G;ℝ)`, `j ↦ [artanh(j/c)]`, is a `C^∞` diffeomorphism from the open subset
`𝒥(G,c)` of `Ker B` onto `H¹(G;ℝ)`: it is a homeomorphism of the source onto the target,
`C^∞` on the source, with `C^∞` inverse; its differential at every point is a linear
isomorphism. -/
theorem affinity_diffeomorphism :
    (affinityPartialHomeomorph hB hc).source = fibreCycles B c ∧
    (affinityPartialHomeomorph hB hc).target = univ ∧
    (∀ v, (affinityPartialHomeomorph hB hc) v = affinityClass B c v) ∧
    ContDiffOn ℝ ∞ (affinityPartialHomeomorph hB hc) (affinityPartialHomeomorph hB hc).source ∧
    ContDiff ℝ ∞ (affinityPartialHomeomorph hB hc).symm ∧
    (∀ (v : Cycles B) (hv : (v : E → ℝ) ∈ currentBox c),
      HasFDerivAt (affinityPartialHomeomorph hB hc)
        ((affinityClassDerivEquiv (B := B) hc hv : Cycles B →L[ℝ] FirstCohomology B)) v) := by
  refine ⟨rfl, rfl, fun _ => rfl, fun v hv => (contDiffAt_affinityClassCycles hv).contDiffWithinAt,
    contDiff_classCycle hB hc, fun v hv => ?_⟩
  rw [coe_affinityClassDerivEquiv]
  exact hasFDerivAt_affinityClassCycles hc hv

/-- The inverse is the variational one: for a representative `a₀` of `α` and the mean-zero
minimiser `φ_α` of `𝓕_α`, `j_α = c tanh(a₀ + Bᵀφ_α)` (eq:supp-affinity-inverse). -/
theorem classCurrent_mk_eq_currentOfPotential (a₀ : E → ℝ) {φ : V → ℝ}
    (hφ : IsMeanZeroMinimizer B c a₀ φ) :
    classCurrent B c (Submodule.Quotient.mk a₀) = currentOfPotential B c a₀ φ := by
  obtain ⟨j, -, huniq⟩ := existsUnique_current_of_class hB hc a₀
  have h1 : IsExact B (affinity c (classCurrent B c (Submodule.Quotient.mk a₀)) - a₀) := by
    have := affinityClass_classCurrent hB hc (Submodule.Quotient.mk a₀)
    unfold affinityClass at this
    obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 this)
    exact ⟨ψ, hψ.symm⟩
  rw [huniq _ ⟨classCurrent_mem hB hc _, h1⟩,
    huniq _ ⟨currentOfPotential_mem_currentFibre hB hc hφ,
      isExact_affinity_currentOfPotential_sub hc φ⟩]

/-- **`thm:supp-nonlinear-Hodge` (Affinity coordinates for a fixed-traffic Markov fibre),
complete.**  For a connected incidence `B` and positive conductances `c`:

1. the affinity map `𝔄 : 𝒥(G,c) → H¹(G;ℝ)` is a `C^∞` diffeomorphism from the open fibre in
   `Ker B` onto `H¹(G;ℝ)` (`affinity_diffeomorphism`);
2. for every representative `a₀`, `𝓕_α` is strictly convex on mean-zero potentials and coercive
   (`𝓕_α + (Σφ)² → ∞`, which equals `𝓕_α` on mean-zero potentials);
3. its unique mean-zero minimiser `φ_α` gives `j_α = c tanh(a₀ + Bᵀφ_α)` with `Bj_α = 0`, the
   inverse image of `[a₀]` under `𝔄`, and the unique fibre current of class `[a₀]`. -/
theorem nonlinear_hodge_diffeomorphism :
    ContDiffOn ℝ ∞ (affinityPartialHomeomorph hB hc) (fibreCycles B c) ∧
    ContDiff ℝ ∞ (affinityPartialHomeomorph hB hc).symm ∧
    (∀ a₀ : E → ℝ,
      StrictConvexOn ℝ (meanZeroPotentials V) (affinityFunctional B c a₀) ∧
      Tendsto (regularizedFunctional B c a₀) (cocompact (V → ℝ)) atTop ∧
      (∃! φ : V → ℝ, IsMeanZeroMinimizer B c a₀ φ) ∧
      ∀ φ, IsMeanZeroMinimizer B c a₀ φ →
        B *ᵥ currentOfPotential B c a₀ φ = 0 ∧
        classCurrent B c (Submodule.Quotient.mk a₀) = currentOfPotential B c a₀ φ ∧
        ∀ j ∈ CurrentFibre B c, affinityClass B c j = Submodule.Quotient.mk a₀ →
          j = currentOfPotential B c a₀ φ) := by
  obtain ⟨-, -, -, h1, h2, -⟩ := affinity_diffeomorphism hB hc
  refine ⟨h1, h2, fun a₀ => ⟨strictConvexOn_affinityFunctional hB hc a₀,
    tendsto_regularizedFunctional_cocompact hB hc a₀, (nonlinear_hodge hB hc a₀).1,
    fun φ hφ => ⟨mulVec_currentOfPotential_eq_zero_of_isMeanZeroMinimizer hB hφ,
      classCurrent_mk_eq_currentOfPotential hB hc a₀ hφ, fun j hj hcl => ?_⟩⟩⟩
  rw [← classCurrent_mk_eq_currentOfPotential hB hc a₀ hφ, ← hcl,
    classCurrent_affinityClass hB hc hj]

/-- **`thm:summary-affinity` (Cohomological reconstruction of directed stationary dynamics).**
For fixed connected `(G, m, c)` with `c > 0`: `𝔄` is a diffeomorphism (as in
`nonlinear_hodge_diffeomorphism`); the unique minimiser of the log-cosh functional for a
representative `a₀` of `α` gives `a_α = a₀ + Bᵀφ_α`, `j_α = c tanh a_α = 𝔄⁻¹(α)`, and the
complete directed generator `k_{xy} = (c_{xy} + j_{α,xy})/m_x` (`forwardRate`), which every
fibre current of class `α` shares. -/
theorem summary_affinity (m : V → ℝ) (tail : E → V) (a₀ : E → ℝ) :
    ContDiffOn ℝ ∞ (affinityPartialHomeomorph hB hc) (fibreCycles B c) ∧
    ContDiff ℝ ∞ (affinityPartialHomeomorph hB hc).symm ∧
    ∃! φ : V → ℝ, IsMeanZeroMinimizer B c a₀ φ ∧
      affinity c (classCurrent B c (Submodule.Quotient.mk a₀)) = a₀ + Bᵀ *ᵥ φ ∧
      classCurrent B c (Submodule.Quotient.mk a₀) =
        (fun e => c e * Real.tanh ((a₀ + Bᵀ *ᵥ φ) e)) ∧
      (∀ e, FiniteGraphSpectralUniversalityFibre.forwardRate m tail c
          (classCurrent B c (Submodule.Quotient.mk a₀)) e =
        (c e + c e * Real.tanh ((a₀ + Bᵀ *ᵥ φ) e)) / m (tail e)) ∧
      ∀ j ∈ CurrentFibre B c, affinityClass B c j = Submodule.Quotient.mk a₀ →
        FiniteGraphSpectralUniversalityFibre.forwardRate m tail c j =
          FiniteGraphSpectralUniversalityFibre.forwardRate m tail c
            (classCurrent B c (Submodule.Quotient.mk a₀)) := by
  obtain ⟨h1, h2, h3⟩ := nonlinear_hodge_diffeomorphism hB hc
  refine ⟨h1, h2, ?_⟩
  obtain ⟨-, -, ⟨φ, hφ, huniq⟩, hrest⟩ := h3 a₀
  obtain ⟨-, hj, hall⟩ := hrest φ hφ
  refine ⟨φ, ⟨hφ, ?_, ?_, fun e => ?_, fun j hjF hcl => ?_⟩, fun φ' hφ' => huniq φ' hφ'.1⟩
  · rw [hj, affinity_currentOfPotential hc]
  · rw [hj]
    rfl
  · rw [hj]
    rfl
  · rw [hall j hjF hcl, hj]

omit hB hc in
/-- Non-vacuity: the two-vertex, one-edge graph (`B = (-1, 1)ᵀ`) is a connected incidence. -/
theorem isConnectedIncidence_twoVertex :
    IsConnectedIncidence
      (Matrix.of fun (x : Fin 2) (_ : Fin 1) => if x = 0 then (-1 : ℝ) else 1) := by
  refine ⟨?_, fun φ hφ => ⟨φ 0, ?_⟩⟩
  · funext e
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  · have := congrFun hφ 0
    simp [mulVec, dotProduct, Fin.sum_univ_two] at this
    funext x
    fin_cases x
    · rfl
    · simp only [Fin.mk_one, Fin.isValue]
      linarith

example : ContDiff ℝ ∞ (classCurrent (Matrix.of fun (x : Fin 2) (_ : Fin 1) =>
    if x = 0 then (-1 : ℝ) else 1) (fun _ => 1)) :=
  contDiff_classCurrent isConnectedIncidence_twoVertex (fun _ => one_pos)

end NonlinearAffinityHodge
end RenewalGeometry
