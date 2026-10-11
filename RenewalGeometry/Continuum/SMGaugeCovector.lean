/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SMGaugeDiracInvariance

/-!
# `G_SM` gauge invariance of the complete first-variation covector
  (`lem:equivariant-tests`, `thm:critical-quotient-defect`; Einstein–Standard-Model
  action-closure manuscript)

Field-level gauge action of a `C²` gauge `R : ℝ⁴ → G_SM` on field tuples of the defining-carrier
rendering (`gaugeTuple`: `A ↦ R·A = R A R^* - (∂R) R^*`, doublet `H ↦ R₂ H`, spinors `Ψ ↦ RΨ`,
dual spinors `Ψ̄ ↦ Ψ̄ R^*`) and on tests (`gaugeTest`: `a ↦ R a R^*`, the linear part).

* `redJet_gaugeTuple`: the reduced jet of the transformed fields is the jet action
  `gaugeJet (R x) (∂R(x))` of the reduced jet (curvature covariance `F_{R·A} = R F_A R^*`
  `CurvatureCovariance.curvM_gaugeConn`; covariance of `D_AH` through the embedding of the doublet
  in `ℂ³ ⊕ ℂ²` and `covDerV_gauge_at`; product rule for the spinor jets);
* `fullPt_redJet_gaugeTuple`: invariance of the complete jet density
  `gravPt + bosonPt + diracPt` along the transformed fields;
* **`fullCov_gauge`**: invariance of the complete first-variation covector:
  `Cov(j(R·z))(j¹(R·v)) = Cov(j z)(j¹ v)` pointwise, for every test `v` (metric and matter
  directions), by differentiating the invariant density along `z + ε v̂`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SMGaugeJet

open SobolevOpen CriticalGauge CriticalQuotient BallAnalysis.SMGaugeStructure SMGaugeLie
  EinsteinSM CurvatureCovariance

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Derivatives of components -/

theorem pd_apply_gen {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → ι → F} {x : E4} (hf : DifferentiableAt ℝ f x) (μ : Fin 4) (i : ι) :
    pd (fun y => f y i) μ x = pd f μ x i := by
  unfold pd
  have h : HasFDerivAt (fun y => f y i) ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).hasFDerivAt.comp x
      hf.hasFDerivAt
  rw [h.fderiv]; rfl

theorem differentiableAt_apply_gen {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E4 → ι → F} {x : E4} (hf : DifferentiableAt ℝ f x) (i : ι) :
    DifferentiableAt ℝ (fun y => f y i) x :=
  differentiableAt_pi.mp hf i

theorem pd_congr_ev {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F}
    {x : E4} (h : f =ᶠ[𝓝 x] g) (μ : Fin 4) : pd f μ x = pd g μ x := by
  unfold pd; rw [h.fderiv_eq]

/-! ### The field-level gauge action -/

/-- The matrix connection of a `ConnFibre` field. -/
def connM (A : E4 → ConnFibre) : MConn 5 := fun μ y => Matrix.of (A y μ)

/-- **Gauge action on field tuples** (defining-carrier rendering). -/
def gaugeTuple (R : E4 → M5) (z : FieldTuple (Fin 5)) : FieldTuple (Fin 5) :=
  FieldTuple.mk z.e (fun y μ i j => gaugeConn R (connM z.A) μ y i j)
    (fun y => higgsG (R y) (z.H y)) (fun y => spinG (R y) (z.Ψ y))
    (fun y => cospinG (R y) (z.Ψb y))

/-- **Gauge action on tests** (linear part: `a ↦ R a R^*`). -/
def gaugeTest (R : E4 → M5) (v : FieldTuple (Fin 5)) : FieldTuple (Fin 5) :=
  FieldTuple.mk v.e (fun y μ => adG (R y) (v.A y μ)) (fun y => higgsG (R y) (v.H y))
    (fun y => spinG (R y) (v.Ψ y)) (fun y => cospinG (R y) (v.Ψb y))

@[simp] theorem gaugeTuple_e (R : E4 → M5) (z : FieldTuple (Fin 5)) :
    (gaugeTuple R z).e = z.e := rfl
@[simp] theorem gaugeTest_e (R : E4 → M5) (v : FieldTuple (Fin 5)) :
    (gaugeTest R v).e = v.e := rfl

theorem connM_gaugeTuple (R : E4 → M5) (z : FieldTuple (Fin 5)) :
    connM (gaugeTuple R z).A = gaugeConn R (connM z.A) := rfl

/-! ### The doublet inside `ℂ³ ⊕ ℂ²` -/

/-- The doublet embedded in the weak block of `ℂ³ ⊕ ℂ²`. -/
def embH (v : HiggsFibre) : Fin 5 → ℂ := Fin.append (fun _ : Fin 3 => (0 : ℂ)) v

/-- The weak-block projection. -/
def projH (u : Fin 5 → ℂ) : HiggsFibre := fun i => u (Fin.natAdd 3 i)

@[simp] theorem embH_castAdd (v : HiggsFibre) (k : Fin 3) : embH v (Fin.castAdd 2 k) = 0 :=
  Fin.append_left _ _ k

@[simp] theorem embH_natAdd (v : HiggsFibre) (k : Fin 2) : embH v (Fin.natAdd 3 k) = v k :=
  Fin.append_right _ _ k

theorem projH_embH (v : HiggsFibre) : projH (embH v) = v := by
  funext i; simp [projH]

theorem mulVec_embH_natAdd (X : M5) (v : HiggsFibre) (i : Fin 2) :
    (X *ᵥ embH v) (Fin.natAdd 3 i) = ∑ j, X (Fin.natAdd 3 i) (Fin.natAdd 3 j) * v j := by
  simp only [mulVec, dotProduct]
  rw [sum_fin5]
  simp

theorem higgsAct_eq_proj (X : LieFibre) (v : HiggsFibre) :
    higgsAct X v = projH (Matrix.of X *ᵥ embH v) := by
  funext i
  simp only [higgsAct, projH, mulVec_embH_natAdd, of_apply]

theorem higgsG_eq_proj (g : M5) (v : HiggsFibre) : higgsG g v = projH (g *ᵥ embH v) := by
  funext i
  simp only [projH]
  rw [mulVec_embH_natAdd]
  rfl

theorem embH_higgsG {g : M5} (hg : IsSMBlock g) (v : HiggsFibre) :
    embH (higgsG g v) = g *ᵥ embH v := by
  funext k
  refine Fin.addCases (m := 3) (n := 2)
    (motive := fun k => embH (higgsG g v) k = (g *ᵥ embH v) k) (fun k => ?_) (fun k => ?_) k
  · rw [embH_castAdd]
    simp only [mulVec, dotProduct]
    rw [sum_fin5]
    simp only [embH_castAdd, mul_zero, Finset.sum_const_zero, zero_add, embH_natAdd]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), zero_mul]
  · rw [embH_natAdd, higgsG_eq_proj]
    rfl

theorem projH_mulVec {g : M5} (hg : IsSMBlock g) (u : Fin 5 → ℂ) :
    projH (g *ᵥ u) = higgsG g (projH u) := by
  funext i
  simp only [projH, higgsG, mulVec, dotProduct, wk, submatrix_apply]
  rw [sum_fin5]
  have : ∑ k : Fin 3, g (Fin.natAdd 3 i) (Fin.castAdd 2 k) * u (Fin.castAdd 2 k) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [hg _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), zero_mul]
  rw [this, zero_add]

/-- The embedding as a continuous linear map. -/
def embHL : HiggsFibre →L[ℝ] (Fin 5 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := embH
      map_add' := fun v w => by
        funext k
        refine Fin.addCases (m := 3) (n := 2) (motive := fun k => embH (v + w) k = (embH v + embH w) k)
          (fun k => ?_) (fun k => ?_) k <;> simp
      map_smul' := fun c v => by
        funext k
        refine Fin.addCases (m := 3) (n := 2)
          (motive := fun k => embH (c • v) k = (RingHom.id ℝ c • embH v) k)
          (fun k => ?_) (fun k => ?_) k <;> simp }

theorem embHL_apply (v : HiggsFibre) : embHL v = embH v := rfl

theorem pdV_embH {H : E4 → HiggsFibre} {x : E4} (hH : DifferentiableAt ℝ H x) (μ : Fin 4) :
    projH (pdV (fun y => embH (H y)) μ x) = pd H μ x := by
  funext i
  simp only [projH, pdV, embH_natAdd]
  exact pd_apply_gen hH μ i

theorem vDiffAt_embH {H : E4 → HiggsFibre} {x : E4} (hH : DifferentiableAt ℝ H x) :
    VDiffAt (fun y => embH (H y)) x := fun c =>
  differentiableAt_pi.mp (embHL.differentiableAt.comp x hH) c

/-! ### The reduced jet of the transformed fields -/

/-- Regularity of a gauge at a point: `C²` entries at `x` and values in `G_SM` near `x`. -/
structure GaugeAt (R : E4 → M5) (x : E4) : Prop where
  c2 : ∀ c e, ContDiffAt ℝ 2 (fun y => R y c e) x
  mem : ∀ᶠ y in 𝓝 x, R y ∈ GSM

theorem GaugeAt.mdiff {R : E4 → M5} {x : E4} (h : GaugeAt R x) : MDiffAt R x := fun c e =>
  (h.c2 c e).differentiableAt (by norm_num)

theorem GaugeAt.unitary {R : E4 → M5} {x : E4} (h : GaugeAt R x) :
    ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ := h.mem.mono fun _ hy => hy.1

theorem GaugeAt.skew {R : E4 → M5} {x : E4} (h : GaugeAt R x) (μ : Fin 4) :
    star (pdM R μ x) * R x = -(star (R x) * pdM R μ x) := by
  have hs := star_pdM_of_unitary h.unitary h.mdiff μ
  have hu : star (R x) * R x = 1 := mem_unitaryGroup_iff'.mp h.unitary.self_of_nhds
  rw [hs, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]

/-- Differentiability of a `ConnFibre` field gives `MDiffAt` of its matrix components. -/
theorem mdiffAt_connM {A : E4 → ConnFibre} {x : E4} (hA : DifferentiableAt ℝ A x) (μ : Fin 4) :
    MDiffAt (connM A μ) x := fun c e =>
  differentiableAt_apply_gen (differentiableAt_apply_gen (differentiableAt_apply_gen hA μ) c) e

/-- The library curvature in matrix form. -/
theorem curvatureF_eq_curvM {A : E4 → ConnFibre} {x : E4} (hA : DifferentiableAt ℝ A x)
    (μ ν : Fin 4) (i j : Fin 5) : curvatureF A x μ ν i j = curvM (connM A) μ ν x i j := by
  have hν := differentiableAt_apply_gen hA ν
  have hμ := differentiableAt_apply_gen hA μ
  simp only [curvatureF, curvM, Pi.add_apply, Pi.sub_apply, Matrix.add_apply, Matrix.sub_apply,
    pdM, of_apply, connM, EinsteinSM.comm, mmul, Matrix.mul_apply]
  rw [← pd_apply_gen hν μ i, ← pd_apply_gen hμ ν i,
    ← pd_apply_gen (differentiableAt_apply_gen hν i) μ j,
    ← pd_apply_gen (differentiableAt_apply_gen hμ i) ν j]

theorem differentiableAt_gaugeTuple_A {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4}
    (hR : GaugeAt R x) (hA : DifferentiableAt ℝ z.A x) :
    DifferentiableAt ℝ (gaugeTuple R z).A x := by
  have hRd := hR.mdiff
  have hpR := mdiffAt_pdM hR.c2
  refine differentiableAt_pi.mpr fun μ => differentiableAt_pi.mpr fun i =>
    differentiableAt_pi.mpr fun j => ?_
  show DifferentiableAt ℝ (fun y => gaugeConn R (connM z.A) μ y i j) x
  simp only [gaugeConn, Matrix.sub_apply]
  exact ((((hRd.mul (mdiffAt_connM hA μ)).mul hRd.star) i j).sub
    (((hpR μ).mul hRd.star) i j))

theorem curvatureF_gaugeTuple {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4}
    (hR : GaugeAt R x) (hA : DifferentiableAt ℝ z.A x) (μ ν : Fin 4) :
    curvatureF (gaugeTuple R z).A x μ ν = adG (R x) (curvatureF z.A x μ ν) := by
  funext i j
  rw [curvatureF_eq_curvM (differentiableAt_gaugeTuple_A hR hA), connM_gaugeTuple,
    curvM_gaugeConn hR.unitary hR.c2 (mdiffAt_connM hA) μ ν]
  have hc : curvM (connM z.A) μ ν x = Matrix.of (curvatureF z.A x μ ν) := by
    ext a b; exact (curvatureF_eq_curvM hA μ ν a b).symm
  rw [hc]
  rfl

theorem covDerivHiggs_gaugeTuple {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4}
    (hR : GaugeAt R x) (hH : DifferentiableAt ℝ z.H x) (μ : Fin 4) :
    covDerivHiggs (gaugeTuple R z).A (gaugeTuple R z).H x μ =
      higgsG (R x) (covDerivHiggs z.A z.H x μ) := by
  have hblock : ∀ᶠ y in 𝓝 x, IsSMBlock (R y) := hR.mem.mono fun _ hy => hy.2.1
  -- the transformed doublet, embedded, is `R ⋅ embH H` near `x`
  have hev : (fun y => embH ((gaugeTuple R z).H y)) =ᶠ[𝓝 x] fun y => R y *ᵥ embH (z.H y) :=
    hblock.mono fun y hy => embH_higgsG hy (z.H y)
  have hHd' : DifferentiableAt ℝ (gaugeTuple R z).H x := by
    refine differentiableAt_pi.mpr fun i => ?_
    show DifferentiableAt ℝ (fun y => higgsG (R y) (z.H y) i) x
    simp only [higgsG, mulVec, dotProduct, wk, submatrix_apply]
    exact DifferentiableAt.fun_sum fun j _ =>
      (hR.mdiff _ _).mul (differentiableAt_apply_gen hH j)
  have key : covDerV (connM (gaugeTuple R z).A) (fun y => embH ((gaugeTuple R z).H y)) μ x =
      R x *ᵥ covDerV (connM z.A) (fun y => embH (z.H y)) μ x := by
    have h1 : pdV (fun y => embH ((gaugeTuple R z).H y)) μ x =
        pdV (fun y => R y *ᵥ embH (z.H y)) μ x := by
      funext c
      exact pd_congr_ev (hev.mono fun y hy => congrFun hy c) μ
    have h2 : embH ((gaugeTuple R z).H x) = R x *ᵥ embH (z.H x) := hev.self_of_nhds
    have h3 := covDerV_gauge_at hR.unitary.self_of_nhds (connM z.A) hR.mdiff (vDiffAt_embH hH) μ
    simp only [covDerV] at h3 ⊢
    rw [h1, h2, connM_gaugeTuple]
    exact h3
  have hcov : ∀ (A : E4 → ConnFibre) (H : E4 → HiggsFibre), DifferentiableAt ℝ H x →
      covDerivHiggs A H x μ = projH (covDerV (connM A) (fun y => embH (H y)) μ x) := by
    intro A H hHx
    simp only [covDerivHiggs, covDerV]
    funext i
    simp only [Pi.add_apply, projH] at *
    rw [show pdV (fun y => embH (H y)) μ x (Fin.natAdd 3 i) = pd H μ x i from
      congrFun (pdV_embH hHx μ) i]
    rw [higgsAct_eq_proj]
    rfl
  rw [hcov _ _ hHd', key, projH_mulVec hblock.self_of_nhds, ← hcov _ _ hH]

theorem pd_spinG {R : E4 → M5} {Ψ : E4 → SpinorFibre (Fin 5)} {x : E4} (hR : MDiffAt R x)
    (hΨ : DifferentiableAt ℝ Ψ x) (μ : Fin 4) :
    pd (fun y => spinG (R y) (Ψ y)) μ x = spinG (R x) (pd Ψ μ x) + spinG (pdM R μ x) (Ψ x) := by
  have hs : ∀ s, VDiffAt (fun y => Ψ y s) x := fun s c =>
    differentiableAt_apply_gen (differentiableAt_apply_gen hΨ s) c
  have hd : DifferentiableAt ℝ (fun y => spinG (R y) (Ψ y)) x := by
    refine differentiableAt_pi.mpr fun s => differentiableAt_pi.mpr fun c => ?_
    exact (VDiffAt.mulVec hR (hs s)) c
  funext s c
  rw [← pd_apply_gen hd μ s, ← pd_apply_gen (differentiableAt_apply_gen hd s) μ c]
  have := congrFun (pdV_mulVec hR (hs s) μ) c
  simp only [pdV] at this
  simp only [spinG, Pi.add_apply]
  rw [this, Pi.add_apply, add_comm]
  congr 2
  funext d
  simp only [pdV]
  rw [pd_apply_gen (differentiableAt_apply_gen hΨ s) μ d, pd_apply_gen hΨ μ s]

theorem pd_cospinG {R : E4 → M5} {Ψ : E4 → SpinorFibre (Fin 5)} {x : E4} (hR : MDiffAt R x)
    (hΨ : DifferentiableAt ℝ Ψ x) (μ : Fin 4) :
    pd (fun y => cospinG (R y) (Ψ y)) μ x =
      cospinG (R x) (pd Ψ μ x) + cospinG (pdM R μ x) (Ψ x) := by
  have h := pd_spinG (R := dualGauge R) hR.dualGauge hΨ μ
  simp only [spinG, cospinG, dualGauge, pdM_dualGauge hR] at h ⊢
  exact h

/-- **The reduced jet of gauge-transformed fields** is the jet action of the reduced jet. -/
theorem redJet_gaugeTuple {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4} (hR : GaugeAt R x)
    (hA : DifferentiableAt ℝ z.A x) (hH : DifferentiableAt ℝ z.H x)
    (hΨ : DifferentiableAt ℝ z.Ψ x) (hΨb : DifferentiableAt ℝ z.Ψb x) :
    redJet (gaugeTuple R z) x = gaugeJet (R x) (fun μ => pdM R μ x) (redJet z x) := by
  refine RJet.ext' rfl rfl rfl ?_ rfl ?_ rfl ?_ rfl ?_
  · funext μ ν
    exact curvatureF_gaugeTuple hR hA μ ν
  · funext μ
    exact covDerivHiggs_gaugeTuple hR hH μ
  · funext μ
    exact pd_spinG hR.mdiff hΨ μ
  · funext μ
    exact pd_cospinG hR.mdiff hΨb μ


/-! ### Differentiability of transformed fields and tests -/

theorem differentiableAt_higgsG {R : E4 → M5} {H : E4 → HiggsFibre} {x : E4} (hR : MDiffAt R x)
    (hH : DifferentiableAt ℝ H x) : DifferentiableAt ℝ (fun y => higgsG (R y) (H y)) x := by
  refine differentiableAt_pi.mpr fun i => ?_
  simp only [higgsG, mulVec, dotProduct, wk, submatrix_apply]
  exact DifferentiableAt.fun_sum fun j _ => (hR _ _).mul (differentiableAt_apply_gen hH j)

theorem differentiableAt_spinG {R : E4 → M5} {Ψ : E4 → SpinorFibre (Fin 5)} {x : E4}
    (hR : MDiffAt R x) (hΨ : DifferentiableAt ℝ Ψ x) :
    DifferentiableAt ℝ (fun y => spinG (R y) (Ψ y)) x := by
  refine differentiableAt_pi.mpr fun s => differentiableAt_pi.mpr fun c => ?_
  exact (VDiffAt.mulVec hR fun c => differentiableAt_apply_gen
    (differentiableAt_apply_gen hΨ s) c) c

theorem differentiableAt_cospinG {R : E4 → M5} {Ψ : E4 → SpinorFibre (Fin 5)} {x : E4}
    (hR : MDiffAt R x) (hΨ : DifferentiableAt ℝ Ψ x) :
    DifferentiableAt ℝ (fun y => cospinG (R y) (Ψ y)) x :=
  differentiableAt_spinG (R := dualGauge R) hR.dualGauge hΨ

theorem differentiableAt_adG {R : E4 → M5} {a : E4 → ConnFibre} {x : E4} (hR : MDiffAt R x)
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (fun y μ => adG (R y) (a y μ)) x := by
  refine differentiableAt_pi.mpr fun μ => differentiableAt_pi.mpr fun i =>
    differentiableAt_pi.mpr fun j => ?_
  exact ((hR.mul (mdiffAt_connM ha μ)).mul hR.star) i j

/-! ### The complete density and covector -/

section Full

variable {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)

/-- The complete jet density `gravPt + bosonPt + diracPt` (defining carrier). -/
def fullPt (θ : CoefficientBank Ysec) (J : RJet (Fin 5)) : ℝ :=
  gravPt θ J + bosonPt θ J + diracPt (defCarrier Ysec mY) θ J

/-- The complete first-variation covector `gravCov + bosonCov + diracCov` (defining carrier). -/
def fullCov (θ : CoefficientBank Ysec) (J : RJet (Fin 5)) : RJet (Fin 5) →L[ℝ] ℝ :=
  gravCov θ J + bosonCov θ J + diracCov (defCarrier Ysec mY) θ J

theorem fullPt_gaugeJet (θ : CoefficientBank Ysec) {g : M5} (hg : g ∈ GSM) (dg : Fin 4 → M5)
    (hdg : ∀ μ, star (dg μ) * g = -(star g * dg μ)) (J : RJet (Fin 5)) :
    fullPt mY θ (gaugeJet g dg J) = fullPt mY θ J := by
  simp only [fullPt, gravPt_gaugeJet, bosonPt_gaugeJet θ hg, diracPt_gaugeJet mY θ hg.1 dg hdg]

theorem differentiableAt_fullPt (θ : CoefficientBank Ysec) {J : RJet (Fin 5)}
    (hJ : J ∈ jetGL (Fin 5)) : DifferentiableAt ℝ (fullPt mY θ) J := by
  have hn : jetGL (Fin 5) ∈ 𝓝 J := isOpen_jetGL.mem_nhds hJ
  have h1 : DifferentiableAt ℝ (gravPt (C := Fin 5) θ) J :=
    ((contDiffOn_gravPt θ (n := 1)).contDiffAt hn).differentiableAt one_ne_zero
  have h2 : DifferentiableAt ℝ (bosonPt (C := Fin 5) θ) J := (hasFDerivAt_bosonPt θ hJ).1
  have h3 : DifferentiableAt ℝ (diracPt (defCarrier Ysec mY) θ) J :=
    ((contDiffOn_diracPt (defCarrier Ysec mY) θ (n := 1)).contDiffAt hn).differentiableAt
      one_ne_zero
  exact (h1.add h2).add h3

theorem fderiv_fullPt_redVar (θ : CoefficientBank Ysec) {J : RJet (Fin 5)}
    (hJ : J ∈ jetGL (Fin 5)) (T : RJet (Fin 5)) :
    fderiv ℝ (fullPt mY θ) J (redVar J T) = fullCov mY θ J T := by
  have hn : jetGL (Fin 5) ∈ 𝓝 J := isOpen_jetGL.mem_nhds hJ
  have h1 : DifferentiableAt ℝ (gravPt (C := Fin 5) θ) J :=
    ((contDiffOn_gravPt θ (n := 1)).contDiffAt hn).differentiableAt one_ne_zero
  have h2 : DifferentiableAt ℝ (bosonPt (C := Fin 5) θ) J := (hasFDerivAt_bosonPt θ hJ).1
  have h3 : DifferentiableAt ℝ (diracPt (defCarrier Ysec mY) θ) J :=
    ((contDiffOn_diracPt (defCarrier Ysec mY) θ (n := 1)).contDiffAt hn).differentiableAt
      one_ne_zero
  have e : fullPt mY θ = gravPt θ + bosonPt θ + diracPt (defCarrier Ysec mY) θ := rfl
  rw [e, fderiv_add (h1.add h2) h3, fderiv_add h1 h2]
  simp only [ContinuousLinearMap.add_apply, fullCov]
  rw [fderiv_gravPt_redVar θ hJ, (hasFDerivAt_bosonPt θ hJ).2, ← bosonCov_apply,
    fderiv_diracPt_redVar (defCarrier Ysec mY) θ hJ]

end Full

/-- The derivative of a function along a quadratic curve `J + ε J₁ + ε² J₂` at `ε = 0`. -/
theorem hasDerivAt_quad_curve {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : W → ℝ} {J J₁ J₂ : W} (hf : DifferentiableAt ℝ f J) :
    HasDerivAt (fun ε : ℝ => f (J + ε • J₁ + ε ^ 2 • J₂)) (fderiv ℝ f J J₁) 0 := by
  have hc : HasDerivAt (fun ε : ℝ => J + ε • J₁ + ε ^ 2 • J₂) J₁ 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => ε • J₁) J₁ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const J₁
    have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 • J₂) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).smul_const J₂
    have h3 := (h1.const_add J).add h2
    rw [add_zero] at h3
    exact h3
  have hf' : HasFDerivAt f (fderiv ℝ f J) (J + (0 : ℝ) • J₁ + (0 : ℝ) ^ 2 • J₂) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hc

/-- The gauge action commutes with the variation `z ↦ z + ε v̂` (the test transforms linearly). -/
theorem gaugeTuple_variation (R : E4 → M5) (z v : FieldTuple (Fin 5)) (ε : ℝ) :
    gaugeTuple R (z + ε • variationDirection z v) =
      gaugeTuple R z + ε • variationDirection (gaugeTuple R z) (gaugeTest R v) := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext y μ i j
    change gaugeConn R (connM (z.A + ε • v.A)) μ y i j =
      gaugeConn R (connM z.A) μ y i j + ε • adG (R y) (v.A y μ) i j
    simp only [gaugeConn, connM, adG, Matrix.sub_apply, Pi.add_apply, Pi.smul_apply]
    have : Matrix.of (z.A y μ + ε • v.A y μ) = Matrix.of (z.A y μ) + ε • Matrix.of (v.A y μ) :=
      rfl
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply]
    abel
  · funext y
    change higgsG (R y) (z.H y + ε • v.H y) = higgsG (R y) (z.H y) + ε • higgsG (R y) (v.H y)
    simp only [higgsG, mulVec_add, mulVec_smul]
  · funext y
    change spinG (R y) (z.Ψ y + ε • v.Ψ y) = spinG (R y) (z.Ψ y) + ε • spinG (R y) (v.Ψ y)
    funext s
    simp only [spinG, Pi.add_apply, Pi.smul_apply, mulVec_add, mulVec_smul]
  · funext y
    change cospinG (R y) (z.Ψb y + ε • v.Ψb y) =
      cospinG (R y) (z.Ψb y) + ε • cospinG (R y) (v.Ψb y)
    funext s
    simp only [cospinG, Pi.add_apply, Pi.smul_apply, mulVec_add, mulVec_smul]

/-- Differentiability data of a field tuple at a point. -/
structure DiffAt (z : FieldTuple (Fin 5)) (x : E4) : Prop where
  e : DifferentiableAt ℝ z.e x
  A : DifferentiableAt ℝ z.A x
  H : DifferentiableAt ℝ z.H x
  Ψ : DifferentiableAt ℝ z.Ψ x
  Ψb : DifferentiableAt ℝ z.Ψb x

theorem DiffAt.gaugeTuple {R : E4 → M5} {z : FieldTuple (Fin 5)} {x : E4} (hR : GaugeAt R x)
    (hz : DiffAt z x) : DiffAt (gaugeTuple R z) x :=
  ⟨hz.e, differentiableAt_gaugeTuple_A hR hz.A, differentiableAt_higgsG hR.mdiff hz.H,
    differentiableAt_spinG hR.mdiff hz.Ψ, differentiableAt_cospinG hR.mdiff hz.Ψb⟩

theorem DiffAt.gaugeTest {R : E4 → M5} {v : FieldTuple (Fin 5)} {x : E4} (hR : MDiffAt R x)
    (hv : DiffAt v x) : DiffAt (gaugeTest R v) x :=
  ⟨hv.e, differentiableAt_adG hR hv.A, differentiableAt_higgsG hR hv.H,
    differentiableAt_spinG hR hv.Ψ, differentiableAt_cospinG hR hv.Ψb⟩

theorem DiffAt.variation {z v : FieldTuple (Fin 5)} {x : E4} (hz : DiffAt z x)
    (hv : DiffAt v x) (ε : ℝ) : DiffAt (z + ε • variationDirection z v) x :=
  ⟨hz.e.add ((differentiableAt_metricLift hz.e hv.e).const_smul ε),
    hz.A.add (hv.A.const_smul ε), hz.H.add (hv.H.const_smul ε), hz.Ψ.add (hv.Ψ.const_smul ε),
    hz.Ψb.add (hv.Ψb.const_smul ε)⟩

/-- **`G_SM` gauge invariance of the complete first-variation covector**: for a `C²` gauge
`R : ℝ⁴ → G_SM` near `x`, fields `z` and a test `v` (metric and matter directions) differentiable
at `x` with nondegenerate coframe,
`Cov(j(R·z)(x))(j¹(R·v)(x)) = Cov(j z(x))(j¹ v(x))`. -/
theorem fullCov_gauge {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) (θ : CoefficientBank Ysec)
    {R : E4 → M5} {x : E4} (hR : GaugeAt R x) {z v : FieldTuple (Fin 5)} (hz : DiffAt z x)
    (hv : DiffAt v x) (hGL : z.e x ∈ coframeGL) :
    fullCov mY θ (redJet (gaugeTuple R z) x) (testJet (gaugeTest R v) x) =
      fullCov mY θ (redJet z x) (testJet v x) := by
  have hgz := hz.gaugeTuple hR
  have hgv := hv.gaugeTest hR.mdiff
  have hJ : redJet z x ∈ jetGL (Fin 5) := hGL
  have hJ' : redJet (gaugeTuple R z) x ∈ jetGL (Fin 5) := hGL
  have hcurve : ∀ ε : ℝ,
      fullPt mY θ (redJet (gaugeTuple R z) x + ε • redVar (redJet (gaugeTuple R z) x)
          (testJet (gaugeTest R v) x) + ε ^ 2 • redVar2 (testJet (gaugeTest R v) x)) =
        fullPt mY θ (redJet z x + ε • redVar (redJet z x) (testJet v x) +
          ε ^ 2 • redVar2 (testJet v x)) := by
    intro ε
    have hw := hz.variation hv ε
    rw [← redJet_variation hgz.e hgz.A hgz.H hgz.Ψ hgz.Ψb hgv.e hgv.A hgv.H hgv.Ψ hgv.Ψb ε,
      ← redJet_variation hz.e hz.A hz.H hz.Ψ hz.Ψb hv.e hv.A hv.H hv.Ψ hv.Ψb ε,
      ← gaugeTuple_variation, redJet_gaugeTuple hR hw.A hw.H hw.Ψ hw.Ψb]
    exact fullPt_gaugeJet mY θ (hR.mem.self_of_nhds) _ (fun μ => hR.skew μ) _
  have h1 := hasDerivAt_quad_curve (J₂ := redVar2 (testJet (gaugeTest R v) x))
    (J₁ := redVar (redJet (gaugeTuple R z) x) (testJet (gaugeTest R v) x))
    (differentiableAt_fullPt mY θ hJ')
  have h2 := hasDerivAt_quad_curve (J₂ := redVar2 (testJet v x))
    (J₁ := redVar (redJet z x) (testJet v x)) (differentiableAt_fullPt mY θ hJ)
  rw [funext hcurve] at h1
  rw [← fderiv_fullPt_redVar mY θ hJ', ← fderiv_fullPt_redVar mY θ hJ]
  exact h1.unique h2

end RenewalGeometry.SMGaugeJet
