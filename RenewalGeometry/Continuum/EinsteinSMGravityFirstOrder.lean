/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMFermionicContinuity

/-!
# The first-order gravitational representative and the gravity sector of
  `prop:reduced-continuity` (Einstein–Standard-Model action-closure manuscript)

* `scalarCurv_vol_eq`: for a smooth coframe with nondegenerate value at `x`,
  `√|g| R = L₁(e, ∂e) + Σ_c ∂_c W^c(e)`, where `L₁ = ehFirstOrder = Q(e)(∂e, ∂e)` is quadratic in
  `∂e` with smooth chart coefficients (`ehBilin`, the first-order metric `ΓΓ` representative of the
  Einstein–Hilbert density) and `W^c = Σ_{b,d} √|g| g^{bd} Γ^c_{db} - Σ_{a,b} √|g| g^{bc} Γ^a_{ab}`
  (`ehFlux`).
* `integral_div_slab_eq_zero`: divergences of `C¹` fields vanishing on the time faces and
  spatially periodic integrate to zero over the slab box (Mathlib divergence theorem on boxes).
* `gravVariation_eq_firstOrder`: the first variation of the (second-order) gravitational action
  equals that of the first-order representative `gravPt = (L₁ - 2Λ√|g|)/(2κ)`;
  `gravVariation_eq_cov`: `D𝒮_g(z)[v] = ∫_Q gravCov(redJet z)(testJet v)`.
* `gravCov_tendsto`: `L¹` convergence of the gravitational covectors (coefficient-bilinear in
  `∂e`, strong `L²`).
* **`gravVariation_dual_tendsto`** (`prop:reduced-continuity`, gravity sector) and
  **`actionVariation_dual_tendsto`** (`prop:reduced-continuity`, complete action: gravity +
  Yang–Mills + Higgs + Dirac–Yukawa), with a non-vacuity example.

Rendering: slab box `Q = (t₀,t₁) × (0,1)³` whose open time interval contains the time support of
`K` (`CylRegion.exists_slab_Ioo`); the limit functionals are the first-order covector formulas on
the limit jet; the first-order representative is the metric `ΓΓ` form obtained by integrating the
library's second-order density by parts (the manuscript's Palatini-type representative).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### The first-order Einstein–Hilbert density -/

section FirstOrder

/-- `V^{bd}(e) = √|g| g^{bd}`. -/
def volInvMetric (e : CoframeFibre) (b d : Fin 4) : ℝ := volFactor e * metricInv e b d

/-- Christoffel symbols from a coframe value and coframe jet. -/
def christoffelJ (e : CoframeFibre) (de : CoframeJet) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel (fun i j => metricInv e i j) (dMetricAlg e de)

/-- **The first-order Einstein–Hilbert density** `L₁(e, ∂e)`:
`Σ_{b,d,a} [-∂_aV^{bd} Γ^a_{db} + ∂_dV^{bd} Γ^a_{ab} + V^{bd}(Γ^a_{ak}Γ^k_{db} - Γ^a_{dk}Γ^k_{ab})]`,
with `∂_aV^{bd} = DV^{bd}(e)[∂_a e]`. -/
def ehFirstOrder (e : CoframeFibre) (de : CoframeJet) : ℝ :=
  ∑ b, ∑ d, ∑ a, (-(fderiv ℝ (fun e => volInvMetric e b d) e (de a) * christoffelJ e de a d b) +
    fderiv ℝ (fun e => volInvMetric e b d) e (de d) * christoffelJ e de a a b +
    volInvMetric e b d * ((∑ k, christoffelJ e de a a k * christoffelJ e de k d b) -
      ∑ k, christoffelJ e de a d k * christoffelJ e de k a b))

/-- The divergence flux `W^c = Σ_{b,d} V^{bd}Γ^c_{db} - Σ_{a,b} V^{bc}Γ^a_{ab}`. -/
def ehFlux (e : E4 → CoframeFibre) (c : Fin 4) (y : E4) : ℝ :=
  (∑ b, ∑ d, volInvMetric (e y) b d * christoffelF e y c d b) -
    ∑ a, ∑ b, volInvMetric (e y) b c * christoffelF e y a a b

theorem contDiffAt_volInvMetric {n : WithTop ℕ∞} {e : CoframeFibre} (he : e ∈ coframeGL)
    (b d : Fin 4) : ContDiffAt ℝ n (fun e => volInvMetric e b d) e :=
  (contDiffAt_volFactor he).mul (contDiffAt_metricInv b d he)

theorem pd_sub' {f g : E4 → ℝ} {x : E4} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y - g y) i x = pd f i x - pd g i x := by
  unfold pd
  rw [fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

theorem sum_rot3 (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ c, ∑ b, ∑ d, f c b d = ∑ b, ∑ d, ∑ c, f c b d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **`√|g| R = L₁(e, ∂e) + Σ_c ∂_c W^c`** for a smooth coframe on an open set, at a point with
nondegenerate coframe value. -/
theorem scalarCurv_vol_eq {e : E4 → CoframeFibre} {U : Set E4} (hU : IsOpen U)
    (he : ContDiffOn ℝ ∞ e U) {x : E4} (hx : x ∈ U) (hGL : e x ∈ coframeGL) :
    scalarCurvF e x * volFactor (e x) =
      ehFirstOrder (e x) (fun i => pd e i x) + ∑ c, pd (ehFlux e c) c x := by
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ e y := fun y hy =>
    (he.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hpdc : ∀ i, ContDiffOn ℝ ∞ (fun y => pd e i y) U := fun i =>
    (he.fderiv_of_isOpen hU le_rfl).clm_apply contDiffOn_const
  have hpd : ∀ i, DifferentiableAt ℝ (fun y => pd e i y) x := fun i =>
    ((hpdc i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hex : DifferentiableAt ℝ e x := hdiff x hx
  -- differentiability of the coefficient pieces
  have hE : ∀ a μ, DifferentiableAt ℝ (fun y => e y a μ) x := fun a μ =>
    differentiableAt_apply₂ hex a μ
  have hDE : ∀ i a μ, DifferentiableAt ℝ (fun y => pd e i y a μ) x := fun i a μ =>
    differentiableAt_apply₂ (hpd i) a μ
  have hMI : ∀ a b, DifferentiableAt ℝ (fun y => metricInv (e y) a b) x := fun a b =>
    ((contDiffAt_metricInv a b hGL (n := 1)).differentiableAt one_ne_zero).comp x hex
  have hV : ∀ b d, DifferentiableAt ℝ (fun y => volInvMetric (e y) b d) x := fun b d =>
    ((contDiffAt_volInvMetric hGL b d (n := 1)).differentiableAt one_ne_zero).comp x hex
  have hVpd : ∀ b d i, pd (fun y => volInvMetric (e y) b d) i x =
      fderiv ℝ (fun e => volInvMetric e b d) (e x) (pd e i x) := fun b d i => by
    unfold pd
    rw [show (fun y => volInvMetric (e y) b d) = (fun e => volInvMetric e b d) ∘ e from rfl,
      fderiv_comp x ((contDiffAt_volInvMetric hGL b d (n := 1)).differentiableAt one_ne_zero) hex]
    rfl
  -- the Christoffel symbols along the coframe
  have hΓeq : ∀ᶠ y in 𝓝 x, christoffelF e y = christoffelJ (e y) (fun i => pd e i y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have : dMetric e y = dMetricAlg (e y) (fun i => pd e i y) := by
      funext i μ ν; exact pd_metricAt (hdiff y hy) i μ ν
    simp only [christoffelF, christoffelJ, this]
  have hΓx : christoffelF e x = christoffelJ (e x) (fun i => pd e i x) := hΓeq.self_of_nhds
  have hΓd : ∀ a d b, DifferentiableAt ℝ (fun y => christoffelF e y a d b) x := by
    intro a d b
    have h : DifferentiableAt ℝ (fun y => christoffelJ (e y) (fun i => pd e i y) a d b) x := by
      unfold christoffelJ christoffel dMetricAlg
      fun_prop
    exact h.congr_of_eventuallyEq (hΓeq.mono fun y hy => by
      show christoffelF e y a d b = _
      rw [hy])
  -- the divergence of the flux
  set P : Fin 4 → Fin 4 → Fin 4 → ℝ := fun b d i => pd (fun y => volInvMetric (e y) b d) i x
    with hP
  set Γ := christoffelF e x with hΓdef
  set dΓ : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
    fun c a d b => pd (fun y => christoffelF e y a d b) c x with hdΓ
  have hflux : ∀ c, pd (ehFlux e c) c x =
      (∑ b, ∑ d, (P b d c * Γ c d b + volInvMetric (e x) b d * dΓ c c d b)) -
      ∑ a, ∑ b, (P b c c * Γ a a b + volInvMetric (e x) b c * dΓ c a a b) := by
    intro c
    have h1 : ∀ b d, DifferentiableAt ℝ
        (fun y => volInvMetric (e y) b d * christoffelF e y c d b) x := fun b d =>
      (hV b d).mul (hΓd c d b)
    have h2 : ∀ a b, DifferentiableAt ℝ
        (fun y => volInvMetric (e y) b c * christoffelF e y a a b) x := fun a b =>
      (hV b c).mul (hΓd a a b)
    unfold ehFlux
    rw [pd_sub' (f := fun y => ∑ b, ∑ d, volInvMetric (e y) b d * christoffelF e y c d b)
        (g := fun y => ∑ a, ∑ b, volInvMetric (e y) b c * christoffelF e y a a b)
        (DifferentiableAt.fun_sum fun b _ => DifferentiableAt.fun_sum fun d _ => h1 b d)
        (DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ => h2 a b),
      pd_sum (f := fun b y => ∑ d, volInvMetric (e y) b d * christoffelF e y c d b) _
        (fun b _ => DifferentiableAt.fun_sum fun d _ => h1 b d),
      pd_sum (f := fun a y => ∑ b, volInvMetric (e y) b c * christoffelF e y a a b) _
        (fun a _ => DifferentiableAt.fun_sum fun b _ => h2 a b)]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [pd_sum (f := fun d y => volInvMetric (e y) b d * christoffelF e y c d b) _
        (fun d _ => h1 b d)]
      exact Finset.sum_congr rfl fun d _ => pd_mul' (hV b d) (hΓd c d b) c
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [pd_sum (f := fun b y => volInvMetric (e y) b c * christoffelF e y a a b) _
        (fun b _ => h2 a b)]
      exact Finset.sum_congr rfl fun b _ => pd_mul' (hV b c) (hΓd a a b) c
  have hdiv : ∑ c, pd (ehFlux e c) c x = ∑ b, ∑ d, ∑ a,
      ((P b d a * Γ a d b + volInvMetric (e x) b d * dΓ a a d b) -
        (P b d d * Γ a a b + volInvMetric (e x) b d * dΓ d a a b)) := by
    simp only [hflux, Finset.sum_sub_distrib]
    rw [sum_rot3 (fun c b d => P b d c * Γ c d b + volInvMetric (e x) b d * dΓ c c d b)]
    have hB : ∑ c, ∑ a, ∑ b, (P b c c * Γ a a b + volInvMetric (e x) b c * dΓ c a a b) =
        ∑ b, ∑ d, ∑ a, (P b d d * Γ a a b + volInvMetric (e x) b d * dΓ d a a b) := by
      rw [show (∑ c, ∑ a, ∑ b, (P b c c * Γ a a b + volInvMetric (e x) b c * dΓ c a a b)) =
          ∑ c, ∑ b, ∑ a, (P b c c * Γ a a b + volInvMetric (e x) b c * dΓ c a a b) from
        Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
    rw [hB]
  rw [hdiv]
  have hL : ehFirstOrder (e x) (fun i => pd e i x) = ∑ b, ∑ d, ∑ a,
      (-(P b d a * Γ a d b) + P b d d * Γ a a b +
        volInvMetric (e x) b d * ((∑ k, Γ a a k * Γ k d b) - ∑ k, Γ a d k * Γ k a b)) := by
    simp only [ehFirstOrder, hP, hVpd, hΓx]
  rw [hL]
  simp only [scalarCurvF, scalarCurv, ricci, riemann, dChristoffelF, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun a _ => ?_
  simp only [volInvMetric, hdΓ, hΓdef]
  ring

end FirstOrder

/-! ### Divergences integrate to zero on the slab box -/

section Divergence

theorem insertNth_succ_one (j : Fin 3) (y : Fin 3 → ℝ) :
    (Fin.insertNth j.succ (1 : ℝ) y : E4) =
      Fin.insertNth j.succ (0 : ℝ) y + spatialShift (Pi.single j (1 : ℤ)) := by
  ext k
  fin_cases j <;> fin_cases k <;>
    simp [Fin.insertNth, Fin.succAboveCases, spatialShift, Pi.single_apply, Fin.cons] <;> rfl

theorem closure_slab_eq {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) :
    closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set =
      Icc (slabChart t₀ t₁ h0 h01 h1 (T := T)).a (slabChart t₀ t₁ h0 h01 h1 (T := T)).b := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  simp only [ChartBox.set, SobolevOpen.box]
  rw [closure_pi_set, ← pi_univ_Icc]
  exact Set.pi_congr rfl fun i _ => closure_Ioo (Q.lt i).ne

/-- **The divergence of a `C¹` field vanishing on the time faces and periodic in space integrates
to zero over the slab box** (divergence theorem on boxes; the spatial faces cancel by
periodicity). -/
theorem integral_div_slab_eq_zero {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {f : Fin 4 → E4 → ℝ} {U : Set E4} (hU : IsOpen U)
    (hQU : closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ U)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) U)
    (htime : ∀ x : E4, (x 0 = t₀ ∨ x 0 = t₁) → f 0 x = 0)
    (hper : ∀ (j : Fin 3) (x : E4), f j.succ (x + spatialShift (Pi.single j (1 : ℤ))) =
      f j.succ x) :
    ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, ∑ i, pd (f i) i x = 0 := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  have hIcc : Icc Q.a Q.b ⊆ U := (closure_slab_eq h0 h01 h1).symm.subset.trans hQU
  have hle : Q.a ≤ Q.b := fun i => (Q.lt i).le
  have hdiff : ∀ i, ∀ x ∈ U, HasFDerivAt (f i) (fderiv ℝ (f i) x) x := fun i x hx =>
    (((hf i).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
  have hcont : ∀ i, ContinuousOn (fun x => fderiv ℝ (f i) x) U := fun i =>
    (hf i).continuousOn_fderiv_of_isOpen hU le_rfl
  have hset : (Q.set : Set E4) =ᵐ[volume] Icc Q.a Q.b := by
    simp only [ChartBox.set, SobolevOpen.box]
    rw [volume_pi]
    exact Measure.univ_pi_Ioo_ae_eq_Icc
  rw [setIntegral_congr_set hset]
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' Q.a Q.b hle f
    (fun i x => fderiv ℝ (f i) x) ∅ countable_empty
    (fun i => (hf i).continuousOn.mono hIcc)
    (fun x hx i => hdiff i x (hIcc (by
      rw [← pi_univ_Icc]
      exact fun k _ => Ioo_subset_Icc_self (hx.1 k (mem_univ k)))))
    ((ContinuousOn.integrableOn_compact isCompact_Icc
      (continuousOn_finset_sum _ fun i _ => ((hcont i).mono hIcc).clm_apply continuousOn_const)))
  simp only [pd]
  rw [hdiv, Fin.sum_univ_succ]
  have h0f : ∀ y : Fin 3 → ℝ, f 0 (Fin.insertNth 0 (Q.b 0) y) = 0 ∧
      f 0 (Fin.insertNth 0 (Q.a 0) y) = 0 := fun y =>
    ⟨htime _ (Or.inr (by simp [hQdef, slabChart])), htime _ (Or.inl (by simp [hQdef, slabChart]))⟩
  have hsf : ∀ (j : Fin 3) (y : Fin 3 → ℝ), f j.succ (Fin.insertNth j.succ (Q.b j.succ) y) =
      f j.succ (Fin.insertNth j.succ (Q.a j.succ) y) := fun j y => by
    have hb : Q.b j.succ = 1 := by simp [hQdef, slabChart]
    have ha : Q.a j.succ = 0 := by simp [hQdef, slabChart]
    rw [hb, ha, insertNth_succ_one, hper]
  simp only [h0f, integral_zero, sub_self, zero_add, hsf, Finset.sum_const_zero]

end Divergence

/-! ### Smoothness, periodicity and locality of the flux -/

section FluxProps

theorem christoffelF_eq_J {e : E4 → CoframeFibre} {y : E4} (he : DifferentiableAt ℝ e y) :
    christoffelF e y = christoffelJ (e y) (fun i => pd e i y) := by
  have : dMetric e y = dMetricAlg (e y) (fun i => pd e i y) := by
    funext i μ ν; exact pd_metricAt he i μ ν
  simp only [christoffelF, christoffelJ, this]

/-- The flux is `C¹` on an open set where the coframe is smooth and nondegenerate. -/
theorem contDiffOn_ehFlux {e : E4 → CoframeFibre} {U : Set E4} (hU : IsOpen U)
    (he : ContDiffOn ℝ ∞ e U) (hGL : ∀ y ∈ U, e y ∈ coframeGL) (c : Fin 4) :
    ContDiffOn ℝ 1 (ehFlux e c) U := by
  intro y hy
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ e y := fun y hy =>
    (he.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hpdc : ∀ i, ContDiffOn ℝ ∞ (fun y => pd e i y) U := fun i =>
    (he.fderiv_of_isOpen hU le_rfl).clm_apply contDiffOn_const
  have heA : ContDiffAt ℝ 1 e y := (he.contDiffAt (hU.mem_nhds hy)).of_le (by simp)
  have hE : ∀ a μ, ContDiffAt ℝ 1 (fun y => e y a μ) y := fun a μ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp heA a) μ
  have hDE : ∀ i a μ, ContDiffAt ℝ 1 (fun y => pd e i y a μ) y := fun i a μ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp
      (((hpdc i).contDiffAt (hU.mem_nhds hy)).of_le (by simp)) a) μ
  have hMI : ∀ a b, ContDiffAt ℝ 1 (fun y => metricInv (e y) a b) y := fun a b =>
    (contDiffAt_metricInv a b (hGL y hy)).comp y heA
  have hV : ∀ b d, ContDiffAt ℝ 1 (fun y => volInvMetric (e y) b d) y := fun b d =>
    (contDiffAt_volInvMetric (hGL y hy) b d).comp y heA
  have hrhs : ContDiffAt ℝ 1 (fun y =>
      (∑ b, ∑ d, volInvMetric (e y) b d * christoffelJ (e y) (fun i => pd e i y) c d b) -
        ∑ a, ∑ b, volInvMetric (e y) b c * christoffelJ (e y) (fun i => pd e i y) a a b) y := by
    unfold christoffelJ christoffel dMetricAlg
    fun_prop
  refine (hrhs.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds hy] with y' hy'
  simp only [ehFlux, christoffelF_eq_J (hdiff y' hy')]

theorem pd_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F} {s : E4}
    (hf : ∀ y, f (y + s) = f y) (i : Fin 4) (y : E4) : pd f i (y + s) = pd f i y := by
  unfold pd
  have h : (fun z => f (z + s)) = f := funext hf
  rw [← fderiv_comp_add_right, h]

theorem ehFlux_periodic {e : E4 → CoframeFibre} {s : E4} (he : ∀ y, e (y + s) = e y)
    (c : Fin 4) (y : E4) : ehFlux e c (y + s) = ehFlux e c y := by
  have hm : ∀ μ ν i, pd (fun y => metricAt (e y) μ ν) i (y + s) =
      pd (fun y => metricAt (e y) μ ν) i y := fun μ ν i =>
    pd_periodic (f := fun y => metricAt (e y) μ ν) (fun y => by rw [he]) i y
  have hd : dMetric e (y + s) = dMetric e y := by funext i μ ν; exact hm μ ν i
  have hc : christoffelF e (y + s) = christoffelF e y := by
    simp only [christoffelF, hd, he]
  simp only [ehFlux, hc, he]

theorem christoffelF_congr {e e' : E4 → CoframeFibre} {x : E4} (h : e =ᶠ[𝓝 x] e') :
    christoffelF e x = christoffelF e' x := by
  have hd : dMetric e x = dMetric e' x := by
    funext i μ ν; exact pd_congr (h.fun_comp fun f => metricAt f μ ν) i
  simp only [christoffelF, hd, h.eq_of_nhds]

theorem ehFlux_congr {e e' : E4 → CoframeFibre} {x : E4} (h : e =ᶠ[𝓝 x] e') (c : Fin 4) :
    ehFlux e c x = ehFlux e' c x := by
  simp only [ehFlux, christoffelF_congr h, h.eq_of_nhds]

theorem gravityDensity_congr {Ysec : Type} (θ : CoefficientBank Ysec) {e e' : E4 → CoframeFibre}
    {x : E4} (h : e =ᶠ[𝓝 x] e') : gravityDensity θ e x = gravityDensity θ e' x := by
  have hc : ∀ᶠ y in 𝓝 x, christoffelF e y = christoffelF e' y :=
    h.eventuallyEq_nhds.mono fun y hy => christoffelF_congr hy
  have hdc : dChristoffelF e x = dChristoffelF e' x := by
    funext c a d b
    exact pd_congr (hc.mono fun y hy => by simp only [hy]) c
  simp only [gravityDensity, scalarCurvF, hdc, christoffelF_congr h, h.eq_of_nhds]

end FluxProps

/-! ### The first-order density as a bilinear form in `∂e` -/

section EHBilin

theorem christoffel_add_dg (g : Fin 4 → Fin 4 → ℝ) (d d' : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    christoffel g (d + d') = christoffel g d + christoffel g d' := by
  funext c i j
  simp only [christoffel, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

theorem christoffelJ_add (e : CoframeFibre) (d d' : CoframeJet) :
    christoffelJ e (d + d') = christoffelJ e d + christoffelJ e d' := by
  simp only [christoffelJ, dMetricAlg_add, christoffel_add_dg]

/-- The bilinear form `Q(e)(d, d')` with `L₁(e, ∂e) = Q(e)(∂e, ∂e)`. -/
def ehForm (e : CoframeFibre) (d d' : CoframeJet) : ℝ :=
  ∑ b, ∑ dd, ∑ a, (-(fderiv ℝ (fun e => volInvMetric e b dd) e (d a) * christoffelJ e d' a dd b) +
    fderiv ℝ (fun e => volInvMetric e b dd) e (d dd) * christoffelJ e d' a a b +
    volInvMetric e b dd * ((∑ k, christoffelJ e d a a k * christoffelJ e d' k dd b) -
      ∑ k, christoffelJ e d a dd k * christoffelJ e d' k a b))

theorem ehFirstOrder_eq (e : CoframeFibre) (de : CoframeJet) :
    ehFirstOrder e de = ehForm e de de := rfl

/-- `Q(e)` as a continuous bilinear map. -/
def ehBilin (e : CoframeFibre) : CoframeJet →L[ℝ] CoframeJet →L[ℝ] ℝ :=
  addBilinL (ehForm e)
    (fun d d' d'' => by
      simp only [ehForm, christoffelJ_add, Pi.add_apply, map_add, add_mul, mul_add,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, neg_add]
      ring)
    (fun d d' d'' => by
      simp only [ehForm, christoffelJ_add, Pi.add_apply, map_add, add_mul, mul_add,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, neg_add]
      ring)
    (by
      have h : ∀ b dd, Continuous (fderiv ℝ (fun e => volInvMetric e b dd) e) := fun b dd =>
        (fderiv ℝ (fun e => volInvMetric e b dd) e).continuous
      unfold ehForm christoffelJ christoffel dMetricAlg
      fun_prop)

theorem ehBilin_apply (e : CoframeFibre) (d d' : CoframeJet) : ehBilin e d d' = ehForm e d d' :=
  rfl

theorem contDiffOn_ehBilin {n : WithTop ℕ∞} : ContDiffOn ℝ n ehBilin coframeGL := by
  refine contDiffOn_clm_apply.mpr fun d => contDiffOn_clm_apply.mpr fun d' => ?_
  intro e₀ he₀
  have hMI : ∀ a b, ContDiffAt ℝ n (fun e : CoframeFibre => metricInv e a b) e₀ := fun a b =>
    contDiffAt_metricInv a b he₀
  have hV : ∀ b dd, ContDiffAt ℝ n (fun e => volInvMetric e b dd) e₀ := fun b dd =>
    contDiffAt_volInvMetric he₀ b dd
  have hDV : ∀ b dd (h : CoframeFibre),
      ContDiffAt ℝ n (fun e => fderiv ℝ (fun e => volInvMetric e b dd) e h) e₀ := fun b dd h =>
    ((contDiffAt_volInvMetric (n := n + 1) he₀ b dd).fderiv_right le_rfl).clm_apply
      contDiffAt_const
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ n (fun e => ehForm e d d') e₀
  unfold ehForm christoffelJ christoffel dMetricAlg
  fun_prop

/-- **The first-order gravitational jet density as a smooth function on the chart.** -/
theorem gravPt_eq {C : Type} [Fintype C] {Ysec : Type} (θ : CoefficientBank Ysec) (R : RJet C) :
    (ehFirstOrder R.e R.de - 2 * θ.Lambda * volFactor R.e) / (2 * θ.kappa) =
      (2 * θ.kappa)⁻¹ * (ehBilin R.e R.de R.de - 2 * θ.Lambda * volFactor R.e) := by
  rw [ehFirstOrder_eq, ehBilin_apply, div_eq_inv_mul]

end EHBilin

/-! ### The gravitational first variation equals that of the first-order representative -/

section GravityIdentity

variable {C : Type} [Fintype C] {T : ℝ} {left : C → Bool} {Ysec : Type}

/-- **The first-order gravitational jet density** `(L₁(e,∂e) - 2Λ√|g|)/(2κ)`. -/
def gravPt (θ : CoefficientBank Ysec) (R : RJet C) : ℝ :=
  (ehFirstOrder R.e R.de - 2 * θ.Lambda * volFactor R.e) / (2 * θ.kappa)

theorem gravityDensity_eq (θ : CoefficientBank Ysec) {e : E4 → CoframeFibre} {U : Set E4}
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U) {x : E4} (hx : x ∈ U) (hGL : e x ∈ coframeGL) :
    gravityDensity θ e x =
      (ehFirstOrder (e x) (fun i => pd e i x) - 2 * θ.Lambda * volFactor (e x)) /
        (2 * θ.kappa) + (∑ c, pd (ehFlux e c) c x) / (2 * θ.kappa) := by
  have h := scalarCurv_vol_eq hU he hx hGL
  unfold gravityDensity
  rw [div_mul_eq_mul_div, sub_mul, h]
  ring

theorem variation_eventuallyEq_set {r : ℕ} {K : CylRegion T} (z : FieldTuple C)
    (v : CrTest left r K) {S : Set ℝ} (hK : ∀ p ∈ K.carrier, p.1 ∈ S) {x : E4}
    (hx : x 0 ∉ S) (ε : ℝ) :
    (z + ε • variationDirection z v.val).e =ᶠ[𝓝 x] z.e := by
  have he : v.val.e =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hK _ ((isCylTest_e v).support h))
  filter_upwards [he] with y hy
  change z.e y + ε • metricLiftL (z.e y) (v.val.e y) = z.e y
  rw [show v.val.e y = 0 from hy, map_zero, smul_zero, add_zero]

theorem smooth_variation_e (z : SmoothFields T left) {r : ℕ} {K : CylRegion T}
    (v : CrTest left r K) (ε : ℝ) :
    ContDiffOn ℝ ∞ (z.z + ε • variationDirection z.z v.val).e (cylSlab T) := by
  have h1 : ContDiffOn ℝ ∞ (fun x => metricLiftL (z.z.e x) (v.val.e x)) (cylSlab T) :=
    ((contDiff_metricLiftL (n := ∞)).comp_contDiffOn z.smooth_e).clm_apply
      (isCylTest_e v).smooth.contDiffOn
  exact z.smooth_e.add (h1.const_smul ε)

theorem periodic_variation_e (z : SmoothFields T left) {r : ℕ} {K : CylRegion T}
    (v : CrTest left r K) (ε : ℝ) (n : Fin 3 → ℤ) (y : E4) :
    (z.z + ε • variationDirection z.z v.val).e (y + spatialShift n) =
      (z.z + ε • variationDirection z.z v.val).e y := by
  change z.z.e (y + spatialShift n) + ε • metricLiftL (z.z.e (y + spatialShift n))
      (v.val.e (y + spatialShift n)) = z.z.e y + ε • metricLiftL (z.z.e y) (v.val.e y)
  rw [z.periodic_e, (isCylTest_e v).periodic]

/-- Nondegeneracy of the varied coframe on the closed slab box for small `ε`. -/
theorem eventually_variation_mem_GL {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    (z : SmoothFields T left) {r : ℕ} {K : CylRegion T} (v : CrTest left r K)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
      (z.z + ε • variationDirection z.z v.val).e x ∈ coframeGL := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  obtain ⟨δ, hδ, hδGL⟩ := hKe.exists_cthickening_subset_open isOpen_coframeGL hKGL
  have hcont : ContinuousOn (fun x => metricLiftL (z.z.e x) (v.val.e x)) (closure Q.set) :=
    ((continuous_metricLiftL.comp_continuousOn z.smooth_e.continuousOn).clm_apply
      (isCylTest_e v).smooth.continuous.continuousOn).mono hclS
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hball : Metric.ball (0 : ℝ) (δ / (max M 0 + 1)) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hball] with ε hε x hx
  refine hδGL (Metric.mem_cthickening_of_dist_le _ (z.z.e x) δ Ke (hzK x hx) ?_)
  have hε' : |ε| < δ / (max M 0 + 1) := by simpa [Real.dist_eq] using hε
  change dist (z.z.e x + ε • metricLiftL (z.z.e x) (v.val.e x)) (z.z.e x) ≤ δ
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |ε| * ‖metricLiftL (z.z.e x) (v.val.e x)‖ ≤ (δ / (max M 0 + 1)) * max M 0 :=
        mul_le_mul hε'.le ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith

/-- **The gravitational first variation equals the first variation of the first-order
representative** `gravPt` (integration by parts of the second-order Einstein–Hilbert density:
the divergence term integrates to zero over the slab box). -/
theorem gravVariation_eq_firstOrder (θ : CoefficientBank Ysec) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁)
    {r : ℕ} (z : SmoothFields T left) (v : CrTest left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    actionVariation T (fun z' x => gravityDensity θ z'.e x) z.z (variationDirection z.z v.val) =
      actionVariation T (fun z' x => gravPt θ (redJet z' x)) z.z
        (variationDirection z.z v.val) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQdef
  set w := variationDirection z.z v.val with hw
  have hO : IsOpen Q.set := SobolevOpen.isOpen_box Q.a Q.b
  have hQm : MeasurableSet Q.set := hO.measurableSet
  have hclS : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hc : IsCompact (closure Q.set) := isCompact_closure_slabChart h0 h01 h1
  have hKI : ∀ p ∈ K.carrier, p.1 ∈ Icc t₀ t₁ := fun p hp => Ioo_subset_Icc_self (hK p hp)
  unfold actionVariation
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_variation_mem_GL h0 h01 h1 z v hKe hKGL hzK] with ε hε
  set zε := z.z + ε • w with hzε
  have hsε : ContDiffOn ℝ ∞ zε.e (cylSlab T) := smooth_variation_e z v ε
  have hs0 : ContDiffOn ℝ ∞ (z.z + (0 : ℝ) • w).e (cylSlab T) := smooth_variation_e z v 0
  have hz0 : z.z + (0 : ℝ) • w = z.z := by simp
  -- vanishing outside the time slab
  have hout1 : ∀ x, x 0 ∉ Icc t₀ t₁ →
      gravityDensity θ zε.e x - gravityDensity θ z.z.e x = 0 := fun x hx => by
    rw [gravityDensity_congr θ (variation_eventuallyEq_set z.z v hKI hx ε), sub_self]
  have hout2 : ∀ x, x 0 ∉ Icc t₀ t₁ →
      gravPt θ (redJet zε x) - gravPt θ (redJet z.z x) = 0 := fun x hx => by
    obtain ⟨h1', h2', h3', h4', h5'⟩ := variation_eventuallyEq z.z v hKI hx ε
    rw [redJet_congr h1' h2' h3' h4' h5', sub_self]
  rw [setIntegral_cylFund_eq_slab h0 h01 h1 hout1, setIntegral_cylFund_eq_slab h0 h01 h1 hout2]
  -- the open set where both coframes are nondegenerate
  set U' := cylSlab T ∩ (z.z.e ⁻¹' coframeGL ∩ zε.e ⁻¹' coframeGL) with hU'
  have hU'o : IsOpen U' := by
    have h1' := z.smooth_e.continuousOn.isOpen_inter_preimage (isOpen_cylSlab T) isOpen_coframeGL
    have h2' := hsε.continuousOn.isOpen_inter_preimage (isOpen_cylSlab T) isOpen_coframeGL
    have : U' = (cylSlab T ∩ z.z.e ⁻¹' coframeGL) ∩ (cylSlab T ∩ zε.e ⁻¹' coframeGL) := by
      ext y; simp only [hU', mem_inter_iff, mem_preimage]; tauto
    rw [this]; exact h1'.inter h2'
  have hQU' : closure Q.set ⊆ U' := fun x hx =>
    ⟨hclS hx, hKGL (hzK x hx), hε x hx⟩
  have hF : ∀ c, ContDiffOn ℝ 1 (fun y => ehFlux zε.e c y - ehFlux z.z.e c y) U' := fun c =>
    (contDiffOn_ehFlux hU'o (hsε.mono inter_subset_left) (fun y hy => hy.2.2) c).sub
      (contDiffOn_ehFlux hU'o (z.smooth_e.mono inter_subset_left) (fun y hy => hy.2.1) c)
  -- pointwise splitting on the box
  have hpt : ∀ x ∈ Q.set, gravityDensity θ zε.e x - gravityDensity θ z.z.e x =
      (gravPt θ (redJet zε x) - gravPt θ (redJet z.z x)) +
        (∑ c, pd (fun y => ehFlux zε.e c y - ehFlux z.z.e c y) c x) / (2 * θ.kappa) := by
    intro x hx
    have hxU := hQU' (subset_closure hx)
    have hDε : ∀ c, DifferentiableAt ℝ (ehFlux zε.e c) x := fun c =>
      ((contDiffOn_ehFlux hU'o (hsε.mono inter_subset_left) (fun y hy => hy.2.2) c).contDiffAt
        (hU'o.mem_nhds hxU)).differentiableAt one_ne_zero
    have hD0 : ∀ c, DifferentiableAt ℝ (ehFlux z.z.e c) x := fun c =>
      ((contDiffOn_ehFlux hU'o (z.smooth_e.mono inter_subset_left) (fun y hy => hy.2.1)
        c).contDiffAt (hU'o.mem_nhds hxU)).differentiableAt one_ne_zero
    rw [gravityDensity_eq θ (isOpen_cylSlab T) hsε hxU.1 hxU.2.2,
      gravityDensity_eq θ (isOpen_cylSlab T) z.smooth_e hxU.1 hxU.2.1]
    simp only [fun c => pd_sub' (hDε c) (hD0 c) c, Finset.sum_sub_distrib]
    simp only [gravPt, redJet, RJet.mk_e, RJet.mk_de]
    ring
  rw [setIntegral_congr_fun hQm hpt]
  -- integrability
  have hmemLp : ∀ {f : E4 → ℝ}, ContinuousOn f (closure Q.set) →
      Integrable f (volume.restrict Q.set) := fun hf =>
    memLp_one_iff_integrable.mp (memLp_of_continuousOn_closure hO hc hf 1)
  have hG : ContinuousOn (gravPt (C := C) θ) (jetGL C) := by
    have hb : ContinuousOn (fun R : RJet C => ehBilin R.e R.de R.de) (jetGL C) :=
      (((contDiffOn_ehBilin (n := 0)).continuousOn.comp (πe (C := C)).continuous.continuousOn
        (fun R hR => hR)).clm_apply (πde (C := C)).continuous.continuousOn).clm_apply
        (πde (C := C)).continuous.continuousOn
    have hv : ContinuousOn (fun R : RJet C => volFactor R.e) (jetGL C) :=
      (contDiffOn_volFactor (n := 0)).continuousOn.comp (πe (C := C)).continuous.continuousOn
        (fun R hR => hR)
    have : gravPt (C := C) θ = fun R => (2 * θ.kappa)⁻¹ *
        (ehBilin R.e R.de R.de - 2 * θ.Lambda * volFactor R.e) := funext fun R => gravPt_eq θ R
    rw [this]
    exact continuousOn_const.mul (hb.sub (continuousOn_const.mul hv))
  have hJε : ContinuousOn (fun x => gravPt θ (redJet zε x)) (closure Q.set) := by
    have hr := (continuousOn_redJet_of (C := C) hsε (z.smooth_A.add (((isCylTest_A v).smooth.contDiffOn).const_smul ε))
      (z.smooth_H.add (((isCylTest_H v).smooth.contDiffOn).const_smul ε))
      (z.smooth_Ψ.add (((isCylTest_Ψ v).smooth.contDiffOn).const_smul ε))
      (z.smooth_Ψb.add (((isCylTest_Ψb v).smooth.contDiffOn).const_smul ε))).mono hclS
    exact hG.comp hr fun x hx => hε x hx
  have hJ0 : ContinuousOn (fun x => gravPt θ (redJet z.z x)) (closure Q.set) :=
    hG.comp ((continuousOn_redJet z).mono hclS) fun x hx => hKGL (hzK x hx)
  have hdivc : ContinuousOn (fun x => ∑ c, pd (fun y => ehFlux zε.e c y - ehFlux z.z.e c y) c x)
      (closure Q.set) :=
    (continuousOn_finsetSum _ fun c _ =>
      (((hF c).continuousOn_fderiv_of_isOpen hU'o le_rfl).clm_apply continuousOn_const)).mono hQU'
  rw [integral_add (hmemLp (f := fun x => gravPt θ (redJet zε x) - gravPt θ (redJet z.z x))
      (hJε.sub hJ0))
    (hmemLp (f := fun x => (∑ c, pd (fun y => ehFlux zε.e c y - ehFlux z.z.e c y) c x) /
      (2 * θ.kappa)) (hdivc.div_const _)), integral_div]
  have htime : ∀ x : E4, (x 0 = t₀ ∨ x 0 = t₁) →
      (fun y => ehFlux zε.e 0 y - ehFlux z.z.e 0 y) x = 0 := by
    intro x hx
    have hxS : x 0 ∉ Ioo t₀ t₁ := by
      rcases hx with hx | hx <;> simp [hx]
    have h : zε.e =ᶠ[𝓝 x] z.z.e := variation_eventuallyEq_set z.z v hK hxS ε
    show ehFlux zε.e 0 x - ehFlux z.z.e 0 x = 0
    rw [ehFlux_congr h 0, sub_self]
  have hper : ∀ (j : Fin 3) (x : E4),
      (fun y => ehFlux zε.e j.succ y - ehFlux z.z.e j.succ y) (x + spatialShift (Pi.single j 1)) =
        (fun y => ehFlux zε.e j.succ y - ehFlux z.z.e j.succ y) x := by
    intro j x
    have hp : ∀ y, zε.e (y + spatialShift (Pi.single j 1)) = zε.e y :=
      fun y => periodic_variation_e z v ε _ y
    show ehFlux zε.e j.succ (x + spatialShift (Pi.single j 1)) -
      ehFlux z.z.e j.succ (x + spatialShift (Pi.single j 1)) = _
    rw [ehFlux_periodic hp j.succ x, ehFlux_periodic (z.periodic_e _) j.succ x]
  rw [integral_div_slab_eq_zero h0 h01 h1 hU'o hQU' hF htime hper, zero_div, add_zero]

end GravityIdentity

/-! ### The gravitational covector -/

section GravityCov

variable {C : Type} [Fintype C] {Ysec : Type}

/-- Quadratic part `(d, d', T) ↦ DQ(e)[ė(k)](d, d') + Q(e)(Dė(e)[d]k, d') + Q(e)(d', Dė(e)[d]k)`. -/
def gravC1 (e : CoframeFibre) : CoframeJet →L[ℝ] CoframeJet →L[ℝ] RJet C →L[ℝ] ℝ :=
  addTrilinL (fun d d' T => fderiv ℝ ehBilin e (metricLiftL e T.e) d d' +
      ehBilin e (dLiftL e d T.e) d' + ehBilin e d' (dLiftL e d T.e))
    (fun d₁ d₂ d' T => by
      simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (fun d d₁ d₂ T => by
      simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (fun d d' T T' => by
      simp only [RJet.add_e, map_add, ContinuousLinearMap.add_apply]; ring)
    (by
      have h1 : Continuous fun T : RJet C => T.e := (πe (C := C)).continuous
      fun_prop)

/-- Linear part `(d, T) ↦ Q(e)(ė(∂k), d) + Q(e)(d, ė(∂k))`. -/
def gravC2 (e : CoframeFibre) : CoframeJet →L[ℝ] RJet C →L[ℝ] ℝ :=
  addBilinL (fun d T => ehBilin e (liftJetL e T.de) d + ehBilin e d (liftJetL e T.de))
    (fun d₁ d₂ T => by simp only [map_add, ContinuousLinearMap.add_apply]; ring)
    (fun d T T' => by simp only [RJet.add_de, map_add, ContinuousLinearMap.add_apply]; ring)
    (by
      have h1 : Continuous fun T : RJet C => T.de := (πde (C := C)).continuous
      fun_prop)

/-- Volume part `(s, T) ↦ s · D√|g|(e)[ė(k)]`. -/
def gravC3 (e : CoframeFibre) : ℝ →L[ℝ] RJet C →L[ℝ] ℝ :=
  addBilinL (fun s T => s * fderiv ℝ volFactor e (metricLiftL e T.e))
    (fun s s' T => by ring)
    (fun s T T' => by simp only [RJet.add_e, map_add]; ring)
    (by
      have h1 : Continuous fun T : RJet C => T.e := (πe (C := C)).continuous
      fun_prop)

/-- **The gravitational covector** `T ↦ D(gravPt)(R)[redVar R T]` in terms of field values. -/
def gravCovF (θ : CoefficientBank Ysec) (e : CoframeFibre) (de : CoframeJet) :
    RJet C →L[ℝ] ℝ :=
  (2 * θ.kappa)⁻¹ • (gravC1 e de de + gravC2 e de + (-(2 * θ.Lambda)) • gravC3 e 1)

def gravCov (θ : CoefficientBank Ysec) (R : RJet C) : RJet C →L[ℝ] ℝ := gravCovF θ R.e R.de

theorem gravPt_eq' (θ : CoefficientBank Ysec) :
    gravPt (C := C) θ = fun R => (2 * θ.kappa)⁻¹ *
      (ehBilin (πe R) (πde R) (πde R) - 2 * θ.Lambda * volFactor (πe R)) :=
  funext fun R => gravPt_eq θ R

theorem contDiffOn_gravPt (θ : CoefficientBank Ysec) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (gravPt (C := C) θ) (jetGL C) := by
  have hm : MapsTo (fun R : RJet C => πe R) (jetGL C) coframeGL := fun R hR => hR
  have hb := (contDiffOn_ehBilin (n := n)).comp (πe (C := C)).contDiff.contDiffOn hm
  have hv := (contDiffOn_volFactor (n := n)).comp (πe (C := C)).contDiff.contDiffOn hm
  rw [gravPt_eq']
  exact contDiffOn_const.mul (((hb.clm_apply (πde (C := C)).contDiff.contDiffOn).clm_apply
    (πde (C := C)).contDiff.contDiffOn).sub (contDiffOn_const.mul hv))

theorem fderiv_gravPt_redVar (θ : CoefficientBank Ysec) {R : RJet C} (hR : R ∈ jetGL C)
    (T' : RJet C) : fderiv ℝ (gravPt θ) R (redVar R T') = gravCov θ R T' := by
  have hb := hasFDerivAt_coeff_bilin (C := C) (Φ := ehBilin) πe πde πde (R := R)
    (((contDiffOn_ehBilin (n := 1)).contDiffAt (isOpen_coframeGL.mem_nhds hR)).differentiableAt
      one_ne_zero)
  have hvd : DifferentiableAt ℝ volFactor (πe R) :=
    (contDiffAt_volFactor hR (n := 1)).differentiableAt one_ne_zero
  have hv : HasFDerivAt (fun R : RJet C => volFactor (πe R))
      ((fderiv ℝ volFactor (πe R)).comp (πe (C := C))) R :=
    hvd.hasFDerivAt.comp R (πe (C := C)).hasFDerivAt
  have htot := ((hb.1.hasFDerivAt.fun_sub (hv.const_mul (2 * θ.Lambda))).const_mul
    (2 * θ.kappa)⁻¹)
  rw [gravPt_eq', htot.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
    hb.2, ContinuousLinearMap.comp_apply]
  have hde : (redVar R T').de = dLiftL R.e R.de T'.e + liftJetL R.e T'.de := by
    funext μ; rfl
  have he : πe (redVar R T') = metricLiftL R.e T'.e := rfl
  have hde' : πde (redVar R T') = dLiftL R.e R.de T'.e + liftJetL R.e T'.de := hde
  rw [he, hde']
  simp only [gravCov, gravCovF, gravC1, gravC2, gravC3, addTrilinL_apply, addBilinL_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, map_add,
    πe_apply, πde_apply]
  ring

theorem continuousOn_gravC1 : ContinuousOn (gravC1 (C := C)) coframeGL := by
  refine continuousOn_clm_apply.mpr fun d => continuousOn_clm_apply.mpr fun d' =>
    continuousOn_clm_apply.mpr fun T => ?_
  have hb : ContinuousOn ehBilin coframeGL := (contDiffOn_ehBilin (n := 0)).continuousOn
  have hfd : ContinuousOn (fderiv ℝ ehBilin) coframeGL :=
    (contDiffOn_ehBilin (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  have hdl : ContinuousOn (fun e => dLiftL e d T.e) coframeGL :=
    (continuous_dLiftL_apply d T.e).continuousOn
  show ContinuousOn (fun e => fderiv ℝ ehBilin e (metricLiftL e T.e) d d' +
    ehBilin e (dLiftL e d T.e) d' + ehBilin e d' (dLiftL e d T.e)) coframeGL
  exact ((((hfd.clm_apply (continuous_metricLiftL.continuousOn.clm_apply continuousOn_const)).clm_apply
    continuousOn_const).clm_apply continuousOn_const).add
    ((hb.clm_apply hdl).clm_apply continuousOn_const)).add
    ((hb.clm_apply continuousOn_const).clm_apply hdl)

theorem continuousOn_gravC2 : ContinuousOn (gravC2 (C := C)) coframeGL := by
  refine continuousOn_clm_apply.mpr fun d => continuousOn_clm_apply.mpr fun T => ?_
  have hb : ContinuousOn ehBilin coframeGL := (contDiffOn_ehBilin (n := 0)).continuousOn
  have hl : ContinuousOn (fun e => liftJetL e T.de) coframeGL :=
    (continuous_liftJetL_apply T.de).continuousOn
  show ContinuousOn (fun e => ehBilin e (liftJetL e T.de) d + ehBilin e d (liftJetL e T.de))
    coframeGL
  exact ((hb.clm_apply hl).clm_apply continuousOn_const).add
    ((hb.clm_apply continuousOn_const).clm_apply hl)

theorem continuousOn_gravC3 : ContinuousOn (gravC3 (C := C)) coframeGL := by
  refine continuousOn_clm_apply.mpr fun s => continuousOn_clm_apply.mpr fun T => ?_
  have hfd : ContinuousOn (fderiv ℝ volFactor) coframeGL :=
    (contDiffOn_volFactor (n := 1)).continuousOn_fderiv_of_isOpen isOpen_coframeGL le_rfl
  show ContinuousOn (fun e => s * fderiv ℝ volFactor e (metricLiftL e T.e)) coframeGL
  exact continuousOn_const.mul (hfd.clm_apply
    (continuous_metricLiftL.continuousOn.clm_apply continuousOn_const))

section Conv

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- **The gravitational covectors converge in `L¹`** under coframe convergence in measure inside a
compact chart set, strong `L²` convergence of `∂e`, and convergence of `(2κ)⁻¹` and `Λ`. -/
theorem gravCov_tendsto {Ke : Set CoframeFibre} {e : ℕ → X → CoframeFibre}
    {e₀ : X → CoframeFibre} (he : CoframeConv μ Ke e e₀) {de : ℕ → X → CoframeJet}
    {de₀ : X → CoframeJet} (hde : RenewalGeometry.LpTendsto μ 2 de de₀)
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hl : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda)))) :
    RenewalGeometry.LpTendsto μ 1 (fun n x => gravCovF (C := C) (θ n) (e n x) (de n x))
      (fun x => gravCovF θ₀ (e₀ x) (de₀ x)) := by
  have h1 := he.bilin (continuousOn_gravC1 (C := C)) hde hde
  have h2 := (he.apply (continuousOn_gravC2 (C := C)) (p := 2) (by norm_num) hde).mono
    (p := 1) (by norm_num) (by norm_num)
  have h3 := he.apply (continuousOn_gravC3 (C := C)) (p := 1) (by norm_num)
    (FirstVariationCalculus.LpTendsto.const_seq (μ := μ) (p := 1)
      (tendsto_const_nhds (x := (1 : ℝ))))
  exact FirstVariationCalculus.LpTendsto.smul_seq hk ((h1.add h2).add
    (FirstVariationCalculus.LpTendsto.smul_seq hl h3))

end Conv

end GravityCov

/-! ### Slabs with the test region in the open time interval -/

/-- Every compact region of `M` has a slab box whose open time interval contains it. -/
theorem CylRegion.exists_slab_Ioo {T : ℝ} (hT : 0 < T) (K : CylRegion T) :
    ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ < t₁ ∧ t₁ < T ∧ ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁ := by
  obtain ⟨t₀, t₁, h0, h01, h1, hK⟩ := K.exists_slab hT
  refine ⟨t₀ / 2, (t₁ + T) / 2, by positivity, by linarith, by linarith, fun p hp => ?_⟩
  obtain ⟨ha, hb⟩ := hK p hp
  exact ⟨by linarith, by linarith⟩

/-! ### `prop:reduced-continuity`: the gravity sector and the complete action -/

section GravityMain

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec) {T : ℝ} {left : FC.C → Bool}

/-- **First variation of the gravitational action of smooth fields** (second-order
Einstein–Hilbert density, integrated by parts): `D𝒮_g(z)[v] = ∫_Q gravCov(redJet z)(testJet v)`,
for a test region whose time support lies in the open slab `(t₀, t₁)`. -/
theorem gravVariation_eq_cov (θ : CoefficientBank Ysec) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁)
    {r : ℕ} (z : SmoothFields T left) (v : CrTest left r K) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hKGL : Ke ⊆ coframeGL)
    (hzK : ∀ x ∈ closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, z.z.e x ∈ Ke) :
    firstVariation T FC θ .gravity z.z v.val =
      ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set,
        gravCov θ (redJet z.z x) (testJet v.val x) := by
  show actionVariation T (fun z' x => gravityDensity θ z'.e x) z.z
    (variationDirection z.z v.val) = _
  rw [gravVariation_eq_firstOrder θ h0 h01 h1 hK z v hKe hKGL hzK]
  exact actionVariation_eq_cov h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) z v hKe
    hKGL hzK (isLocalDensity_of_redJet fun z x => rfl) (contDiffOn_gravPt θ)
    (fun z' x _ _ _ _ _ _ => rfl) (fun R hR T' => fderiv_gravPt_redVar θ hR T')

/-- Convergence of the gravitational couplings `(2κ)⁻¹`, `-2Λ` under bank convergence inside a
compact physical set. -/
theorem bank_gravity_tendsto {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hP : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) (ht : BankTendsto θ θ₀) :
    Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹) ∧
      Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))) := by
  have hc : ∀ k : Fin 7, Tendsto (fun n => (bankCoords (θ n)).1 k) atTop
      (𝓝 ((bankCoords θ₀).1 k)) := fun k =>
    (((continuous_apply k).comp continuous_fst).tendsto _).comp ht
  have h0 : Tendsto (fun n => (θ n).kappa) atTop (𝓝 θ₀.kappa) := by simpa [bankCoords] using hc 0
  have h1 : Tendsto (fun n => (θ n).Lambda) atTop (𝓝 θ₀.Lambda) := by
    simpa [bankCoords] using hc 1
  obtain ⟨P, ⟨hPc, hPphys⟩, hθP⟩ := hP
  obtain ⟨θ₁, hθ₁, heq⟩ : bankCoords θ₀ ∈ bankCoords '' P :=
    hPc.isClosed.mem_of_tendsto ht (Eventually.of_forall fun n => mem_image_of_mem _ (hθP n))
  have e0 : θ₁.kappa = θ₀.kappa := by simpa [bankCoords] using congrArg (fun c => c.1 0) heq
  have hk0 : 2 * θ₀.kappa ≠ 0 := mul_ne_zero two_ne_zero (e0 ▸ (hPphys hθ₁).1.ne')
  exact ⟨(tendsto_const_nhds.mul h0).inv₀ hk0, (tendsto_const_nhds.mul h1).neg⟩

/-- The first variation of the gravitational action at limit fields (first-order covector
formula on the limit jet). -/
def gravLimitVariation (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    {r : ℕ} {K : CylRegion T} (v : CrTest left r K) : ℝ :=
  ∫ x in Q.set, gravCov θ (limitJet L x) (testJet v.val x)

/-- **`prop:reduced-continuity`, gravity sector.**  Under the reduced convergence on the slab box
(whose open time interval contains the time support of `K`), the gravitational first variations
`D𝒮_{g,θ_h}(z_h) = firstVariation T FC θ_h .gravity` converge in the dual norm of `𝒱_K^r`
(`r ≥ 1`) to the first-order (integrated-by-parts) first variation of the limit fields. -/
theorem gravVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |firstVariation T FC (θ n) .gravity (z n).z v.val -
        gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v| ≤ ε * ‖v‖ := by
  obtain ⟨Ke, hKe, hzKe, hLKe⟩ := hRC.coframe_chart
  obtain ⟨hcl, hmem, he⟩ := coframe_slab_data h0 h01 h1 hKe hzKe hLKe hRC.coframe_mem
    hRC.coframe_tendsto
  have hde : RenewalGeometry.LpTendsto (slabChart t₀ t₁ h0 h01 h1 (T := T)).μ 2
      (fun n x => (redJet (z n).z x).de) (fun x => (limitJet L x).de) :=
    (coframeJet_L2_tendsto hmem hRC.coframe_mem hRC.coframe_tendsto).congr
      (fun n => Eventually.of_forall fun x => toJet_reJet_coframeGrad x)
      (Eventually.of_forall fun x => rfl)
  obtain ⟨hk, hl⟩ := bank_gravity_tendsto hRC.bank_compact hRC.bank_tendsto
  have hconv := gravCov_tendsto (C := FC.C) he hde hk hl
  filter_upwards [dual_tendsto_of_L1 (left := left) (K := K) hr hconv hε] with n hn v
  rw [gravVariation_eq_cov FC (θ n) h0 h01 h1 hK (z n) v hKe.1
    (hKe.2.trans coframeChart_subset_GL) (hcl n)]
  exact hn v

/-- **`prop:reduced-continuity`, complete action** (gravity + Standard Model, the latter with
Yang–Mills, Higgs and the complete Dirac–Yukawa contribution including the metric–spin-connection
chain): under the reduced convergence on the slab box and convergence of the Yukawa coefficients,
`D𝒮_{θ_h}(z_h) → D𝒮_θ(z)` in the dual norm of `𝒱_K^r` (`r ≥ 1`). -/
theorem actionVariation_dual_tendsto {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T)
    {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {r : ℕ} (hr : 1 ≤ r)
    {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    {L : LimitFields FC.C}
    (hRC : ReducedConvergence (slabChart t₀ t₁ h0 h01 h1 (T := T)) z θ L θ₀)
    (hyL : Tendsto (fun n => yukL FC (θ n)) atTop (𝓝 (yukL FC θ₀)))
    (hy0 : Tendsto (fun n => FC.yukawa (θ n) 0) atTop (𝓝 (FC.yukawa θ₀ 0)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest left r K,
      |(firstVariation T FC (θ n) .gravity (z n).z v.val +
          firstVariation T FC (θ n) .standardModel (z n).z v.val) -
        (gravLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v +
          smLimitVariation FC θ₀ (slabChart t₀ t₁ h0 h01 h1 (T := T)) L v)| ≤ ε * ‖v‖ := by
  filter_upwards [gravVariation_dual_tendsto FC h0 h01 h1 hK hr hRC (half_pos hε),
    smVariation_dual_tendsto FC h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) hr hRC
      hyL hy0 (half_pos hε)] with n hg hs v
  have e : ∀ a b c d : ℝ, (a + c) - (b + d) = (a - b) + (c - d) := fun _ _ _ _ => by ring
  rw [e]
  exact (abs_add_le _ _).trans ((add_le_add (hg v) (hs v)).trans_eq (by ring))

/-- **Non-vacuity**: the flat regulator satisfies the hypotheses of the complete statement. -/
example {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T}
    (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : CrTest (trivialCarrier Unit).left r K,
      |(firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .gravity
            ((flatRegulator T).fields n).z v.val +
          firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) .standardModel
            ((flatRegulator T).fields n).z v.val) -
        (gravLimitVariation (trivialCarrier Unit) physicalBank
            (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v +
          smLimitVariation (trivialCarrier Unit) physicalBank
            (slabChart t₀ t₁ h0 h01 h1 (T := T)) flatLimit v)| ≤ ε * ‖v‖ :=
  actionVariation_dual_tendsto (trivialCarrier Unit) h0 h01 h1 hK hr
    (flatRegulator_reducedActionConvergence T _) tendsto_const_nhds tendsto_const_nhds hε

end GravityMain

end EinsteinSM
end RenewalGeometry
