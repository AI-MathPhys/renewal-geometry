/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalGaugeEstimates
import RenewalGeometry.Continuum.EinsteinSMFirstVariationContinuity

/-!
# Critical-energy quotient compactness in Coulomb charts, conditional on Uhlenbeck's gauge
  (`thm:critical-quotient-defect`, compactness part of `eq:critical-quotient-convergence`;
  Einstein–Standard-Model action-closure manuscript)

Box rendering of `CriticalGaugeEstimates.lean` (chart `K = box a b ⊂ ℝ⁴`, smooth unitary
connections `A_h` of a rank-`m` Hermitian bundle with matrix entries, the gauge transformations of
`UhlenbeckSmallEnergyGauge m`).  This file composes the named Uhlenbeck small-energy gauge theorem
with the proved positive graph estimates and the Rellich/weak compactness on boxes into the
**quotient compactness** of the connection and of the matter fields:

* `uhlenbeck_ball_cover` — the small-energy ball cover of `prop:critical-uhlenbeck` with the
  gauges `R_{h,j}` (unitary and smooth on the balls) and the inner cubes of half-side `r/4`, whose
  closures lie in the balls;
* `transported_memW12` / `transported_w12_bound` — a smooth section `u` in the defining
  representation, transported to the Coulomb chart (`ũ = R u`), lies in `W^{1,2}` of the cube with
  `‖ũ‖_{W^{1,2}} ≤ C_B(1 + η) m (‖u‖_2 + ‖∇^{A}u‖_2)`: the classical derivative is
  `∂ũ = R ∇^A u - Ã ũ` (gauge covariance `covDerV_gauge`) and `critical_positive_graph`
  applies with the small Coulomb `L⁴` norm; the gauge-invariant bound is exactly (Q3)/(Q4);
* `critical_quotient_compactness_of_gauge` (**main theorem**): under `UhlenbeckSmallEnergyGauge m`,
  (Q2) for the connections and the gauge-invariant bounds (Q3)/(Q4) for a finite family of smooth
  matter sections (Higgs components, spinors, dual spinors written in the defining
  representation), for every compact `K' ⊂ K` there are a finite cover by cubes, cutoff-dependent
  local gauges, and one subsequence along which on every cube: `Ã_h ⇀ A` in `W^{1,2}`,
  `Ã_h → A` in every `L^q`, `q < 4`, `F_{Ã_h} → F_A` against bounded weights; the transported
  matter `ũ_h ⇀ ũ` in `W^{1,2}`, `ũ_h → ũ` in every `L^q`, `q < 4`; and the covariant
  derivatives `∇^{Ã_h}ũ_h → ∇^{A}ũ` against bounded weights (`D_{A_h}H_h ⇀ D_AH`).

This is the compactness half of `eq:critical-quotient-convergence` (connection, curvature, Higgs,
covariant Higgs gradient, spinor and dual spinor in `H¹`), conditional on the named gap
`UhlenbeckSmallEnergyGauge`.  Not composed here: the coframe part (Q1) (a separate precompactness
extraction), the passage of the Euler rows with the equivariant budgets (Q5), and the metric
equation `eq:critical-quotient-einstein` with the defects; see the ledger note.

Rendering: matter sections in the defining representation of `U(m)` (the gauges produced by the
rank-`m` Uhlenbeck theorem are `U(m)`-valued), with zero reference connection; sections smooth on
`ℝ⁴` (the reconstructed fields).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CriticalQuotient

open SobolevOpen CriticalGauge

set_option linter.unusedSectionVars false

/-! ### The Uhlenbeck ball cover -/

/-- The inner cube of half-side `r/4` about `c`. -/
def innerCube (c : Fin 4 → ℝ) (r : ℝ) : Set (Fin 4 → ℝ) :=
  box (fun i => c i - r / 4) (fun i => c i + r / 4)

theorem closure_innerCube_subset_eBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    closure (innerCube c r) ⊆ eBall c r := by
  have hcl : closure (innerCube c r) ⊆ Set.pi univ fun i => Icc (c i - r / 4) (c i + r / 4) :=
    closure_minimal (Set.pi_mono fun i _ => Ioo_subset_Icc_self)
      (isClosed_set_pi fun i _ => isClosed_Icc)
  intro x hx
  have hx' := hcl hx
  show ∑ i, (x i - c i) ^ 2 < r ^ 2
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (x i - c i) ^ 2 ≤ (r / 4) ^ 2 := by
    intro i _
    have h1 := hx' i (mem_univ i)
    exact sq_le_sq' (by linarith [h1.1]) (by linarith [h1.2])
  calc ∑ i, (x i - c i) ^ 2 ≤ ∑ _i : Fin 4, (r / 4) ^ 2 := Finset.sum_le_sum h
    _ < r ^ 2 := by simp; nlinarith

theorem innerCube_subset_eBall (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    innerCube c r ⊆ eBall c r :=
  subset_closure.trans (closure_innerCube_subset_eBall c hr)

theorem isCompact_closure_innerCube (c : Fin 4 → ℝ) (r : ℝ) :
    IsCompact (closure (innerCube c r)) := by
  refine (isCompact_univ_pi fun i => isCompact_Icc (a := c i - r / 4) (b := c i + r / 4)).of_isClosed_subset
    isClosed_closure ?_
  exact closure_minimal (Set.pi_mono fun i _ => Ioo_subset_Icc_self)
    (isClosed_set_pi fun i _ => isClosed_Icc)

/-- **The small-energy ball cover with Uhlenbeck gauges** (from `UhlenbeckSmallEnergyGauge`):
for every compact `K' ⊂ K = box a b` and `η > 0` there are finitely many balls `B_r(c_j) ⊂ K`
whose inner cubes cover `K'`, and gauges `R_{h,j}`, unitary and smooth on `B_r(c_j)`, with
`Ã_{h,j} = R_{h,j}·A_h` Coulomb on the ball, uniformly bounded in `W^{1,2}(B_r(c_j))` and with
`‖Ã_{h,j}‖_{L⁴(B_r(c_j))} ≤ η`. -/
theorem uhlenbeck_ball_cover {m : ℕ} (hU : UhlenbeckSmallEnergyGauge m)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧ (∀ j, eBall (ctr j) r ⊆ box a b) ∧
      K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ x ∈ eBall (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (eBall (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (eBall (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (eBall (ctr j) r)) ≤ η) := by
  obtain ⟨εU, hεU, CU, hU'⟩ := hU
  set εs : ℝ≥0 := min εU ((η / (CU + 1)) ^ 2)
  have hεs : 0 < εs := lt_min hεU (by positivity)
  obtain ⟨δ, hδ, hUIδ⟩ := (criticalCurvatureUI_iff _ _ _).mp hUI εs (by exact_mod_cast hεs)
  obtain ⟨r0, hr0, hthick⟩ := hK'.exists_thickening_subset_open (isOpen_box a b) hK'Q
  set r : ℝ := min (r0 / 2) (min 1 δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by have := lt_min one_pos hδ; positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hvol : (2 * r) ^ Fintype.card (Fin 4) ≤ δ := by
    have h2r : 2 * r ≤ min 1 δ := by
      have := min_le_right (r0 / 2) (min 1 δ / 2); linarith
    have h0 : 0 ≤ 2 * r := by linarith
    have h1 : 2 * r ≤ 1 := h2r.trans (min_le_left _ _)
    simp only [Fintype.card_fin]
    calc (2 * r) ^ 4 ≤ (2 * r) ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = 2 * r := pow_one _
      _ ≤ δ := h2r.trans (min_le_right _ _)
  have hball : ∀ c ∈ K', eBall c r ⊆ box a b := by
    intro c hc x hx
    refine hthick (Metric.mem_thickening_iff.mpr ⟨c, hc, ?_⟩)
    exact (Metric.mem_ball.mp (eBall_subset_ball c hr hx)).trans hrr0
  have hballvol : ∀ c, volume (eBall c r) ≤ ENNReal.ofReal δ := fun c =>
    (measure_mono (eBall_subset_ball c hr)).trans (by
      rw [Real.volume_pi_ball c hr]; exact ENNReal.ofReal_le_ofReal hvol)
  have henergy : ∀ h, ∀ c ∈ K', curvEnergy (A h) (eBall c r) ≤ εs := fun h c hc =>
    hUIδ h (eBall c r) (isOpen_eBall c r).measurableSet (hball c hc) (hballvol c)
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : K' => innerCube c.1 r)
    (fun c => isOpen_box _ _) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by
      rw [innerCube, mem_box]; intro i; constructor <;> simp <;> linarith⟩)
  set N := t.card
  set ctr : Fin N → Fin 4 → ℝ := fun j => (t.equivFin.symm j : K').1
  have hctr : ∀ j, ctr j ∈ K' := fun j => (t.equivFin.symm j : K').2
  refine ⟨N, ctr, r, hr, fun j => hball _ (hctr j), ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (ht hx)
    refine mem_iUnion.mpr ⟨t.equivFin ⟨c, hct⟩, ?_⟩
    simpa [ctr] using hxc
  choose Cr hCr using fun j => hU' (ctr j) r hr
  have hsmall : ∀ h j, curvEnergy (A h) (eBall (ctr j) r) ≤ εU := fun h j =>
    (henergy h _ (hctr j)).trans (by exact_mod_cast min_le_left _ _)
  choose R hRu hRs hRdiv hRW hRw12 hR4 using fun h j => hCr j (A h) (hA h) (hsmall h j)
  refine ⟨R, hRu, hRs, hRdiv, ⟨∑ j, (Cr j : ℝ≥0∞) * (εU : ℝ≥0∞) ^ (1 / 2 : ℝ), ?_,
    fun h j ν c e => ⟨hRW h j ν c e, ?_⟩⟩, fun h j ν c e => ?_⟩
  · exact ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
  · refine (hRw12 h j ν c e).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Cr j : ℝ≥0∞) *
      (εU : ℝ≥0∞) ^ (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_univ j))
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (hsmall h j) (by norm_num)) _
  · exact (hR4 h j ν c e).trans (mul_rpow_half_le (min_le_right _ _) (henergy h _ (hctr j)))

/-! ### Matter sections transported to a Coulomb chart -/

section Transport

variable {m : ℕ}

theorem pd_congr' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : (Fin 4 → ℝ) → F}
    {x : Fin 4 → ℝ} (h : f =ᶠ[𝓝 x] g) (i : Fin 4) : pd f i x = pd g i x := by
  unfold pd; rw [h.fderiv_eq]

/-- Local form of `pdM_unitary`: on an open set where `R` is unitary,
`∂R R^* + R (∂R)^* = 0`. -/
theorem pdM_unitary_on {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {U : Set (Fin 4 → ℝ)}
    (hU : IsOpen U) (hRu : ∀ y ∈ U, R y ∈ unitaryGroup (Fin m) ℂ) {x : Fin 4 → ℝ} (hx : x ∈ U)
    (hR : MDiffAt R x) (μ : Fin 4) :
    pdM R μ x * star (R x) + R x * star (pdM R μ x) = 0 := by
  have h1 : (fun y => R y * star (R y)) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Matrix.mem_unitaryGroup_iff.mp (hRu y hy)
  have h2 := pdM_mul hR hR.star μ
  rw [pdM_star hR] at h2
  rw [← h2]
  ext c e
  simp only [pdM, Matrix.of_apply, Matrix.zero_apply]
  rw [pd_congr' (f := fun y => (R y * star (R y)) c e) (g := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ) c e)
    (h1.mono fun y hy => by simpa using congrFun (congrFun hy c) e) μ]
  exact pd_const_complex _ μ x

/-- Pointwise form of `covDerV_gauge`: `∇^{R·𝒜}(R η)(x) = R(x) ∇^𝒜 η(x)` whenever `R(x)` is
unitary. -/
theorem covDerV_gauge_at {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hRu : R x ∈ unitaryGroup (Fin m) ℂ) (𝒜 : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    {η : (Fin 4 → ℝ) → Fin m → ℂ} (hR : MDiffAt R x) (hη : VDiffAt η x) (μ : Fin 4) :
    covDerV (gaugeConn R 𝒜) (fun y => R y *ᵥ η y) μ x = R x *ᵥ covDerV 𝒜 η μ x := by
  have hu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp hRu
  have e : (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) * R x =
      R x * 𝒜 μ x - pdM R μ x := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc (pdM R μ x), hu, Matrix.mul_one,
      Matrix.mul_one]
  rw [covDerV, covDerV, gaugeConn, pdV_mulVec hR hη, Matrix.mulVec_mulVec, e, Matrix.sub_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

/-- The transported matter section `ũ = R u`, componentwise. -/
def transp (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (u : (Fin 4 → ℝ) → Fin m → ℂ) :
    Fin m → (Fin 4 → ℝ) → ℂ :=
  fun c y => (R y *ᵥ u y) c

/-- Its classical partial derivatives. -/
def tgrad (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (u : (Fin 4 → ℝ) → Fin m → ℂ) :
    Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ :=
  fun c μ y => pd (transp R u c) μ y

open Classical in
/-- A connection cut off outside an open set `U`, in entry form. -/
def cutConn (U : Set (Fin 4 → ℝ)) (𝒜 : MConn m) : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ :=
  fun μ c e x => if x ∈ U then 𝒜 μ x c e else 0

/-- The gauge-transformed connection is unitary (skew-Hermitian) wherever the gauge is unitary
(on an open set). -/
theorem cutConn_gauge_skew {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {U : Set (Fin 4 → ℝ)}
    (hU : IsOpen U) (hRu : ∀ y ∈ U, R y ∈ unitaryGroup (Fin m) ℂ)
    (hRd : ∀ y ∈ U, MDiffAt R y) {A : MConn m} (hA : ∀ μ y, star (A μ y) = -A μ y) :
    IsSkewHermitianConn (cutConn U (gaugeConn R A)) := by
  intro μ c e x
  unfold cutConn
  split_ifs with hx
  · have hd := pdM_unitary_on hU hRu hx (hRd x hx) μ
    have hstar : star (gaugeConn R A μ x) = -gaugeConn R A μ x := by
      simp only [gaugeConn, star_sub, star_mul, star_star, hA μ x]
      have : R x * star (pdM R μ x) = -(pdM R μ x * star (R x)) := eq_neg_of_add_eq_zero_right hd
      rw [Matrix.mul_assoc, this]
      noncomm_ring
    have := congrFun (congrFun hstar c) e
    simp only [Matrix.star_apply, Matrix.neg_apply] at this
    have h2 := congrArg star this
    rw [star_star, star_neg] at h2
    exact h2
  · simp

end Transport

/-! ### `W^{1,2}` bounds for transported matter -/

section TransportBound

variable {m : ℕ}

theorem innerCube_eq_box (c0 : Fin 4 → ℝ) (r : ℝ) :
    innerCube c0 r = box (fun i => c0 i - r / 4) (fun i => c0 i + r / 4) := rfl

theorem norm_mulVec_unitary_le {R : Matrix (Fin m) (Fin m) ℂ} (hR : R ∈ unitaryGroup (Fin m) ℂ)
    (v : Fin m → ℂ) (e : Fin m) : ‖(R *ᵥ v) e‖ ≤ ∑ c, ‖v c‖ :=
  (norm_le_fibreNorm _ e).trans ((fibreNorm_mulVec_unitary hR v).le.trans (fibreNorm_le_sum v))

/-- `L²` norms of a unitarily rotated vector field are bounded by the sum of the component norms. -/
theorem eLpNorm_rot_le {Q : Set (Fin 4 → ℝ)} (hQ : MeasurableSet Q)
    {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} (hRu : ∀ y ∈ Q, R y ∈ unitaryGroup (Fin m) ℂ)
    {v : (Fin 4 → ℝ) → Fin m → ℂ} (hv : ∀ c, AEStronglyMeasurable (fun y => v y c)
      (volume.restrict Q))
    {F : (Fin 4 → ℝ) → ℂ} (hF : ∀ y ∈ Q, F y = (R y *ᵥ v y) e) :
    eLpNorm F 2 (volume.restrict Q) ≤ ∑ c, eLpNorm (fun y => v y c) 2 (volume.restrict Q) := by
  calc eLpNorm F 2 (volume.restrict Q) ≤ eLpNorm (fun y => ∑ c, ‖v y c‖) 2 (volume.restrict Q) := by
        refine eLpNorm_mono_ae ?_
        filter_upwards [ae_restrict_mem hQ] with y hy
        rw [hF y hy, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact norm_mulVec_unitary_le (hRu y hy) _ e
    _ ≤ ∑ c, eLpNorm (fun y => ‖v y c‖) 2 (volume.restrict Q) := by
        have := eLpNorm_sum_le (f := fun c y => ‖v y c‖) (s := Finset.univ) (p := 2)
          (μ := volume.restrict Q) (fun c _ => (hv c).norm) (by norm_num)
        have heq : (∑ c, fun y => ‖v y c‖) = fun y => ∑ c, ‖v y c‖ := by
          funext y; simp [Finset.sum_apply]
        rwa [heq] at this
    _ = _ := by simp only [eLpNorm_norm]

/-- **Transported matter is `W^{1,2}` on the Coulomb cube, with the gauge-invariant bound.**
On the inner cube `Q` of a ball `U = B_r(c₀)` on which the gauge `R` is unitary and smooth, a
smooth section `u` of the defining representation transported to `ũ = R u` lies in `W^{1,2}(Q)`
(classical derivatives), and if `‖Ã‖_{L⁴(U)} ≤ η` for `Ã = R·A` then
`‖ũ_c‖_{W^{1,2}(Q)} ≤ C (1 + η) m (Σ_e ‖u_e‖_{L²(Q)} + Σ_{e,μ} ‖(∇^A_μ u)_e‖_{L²(Q)})`, with `C`
depending only on the cube and the rank (`critical_positive_graph`). -/
theorem transported_bound (c0 : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ C : ℝ≥0, ∀ (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ),
      (∀ y ∈ eBall c0 r, R y ∈ unitaryGroup (Fin m) ℂ) →
      (∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) (eBall c0 r)) →
      ∀ (A : MConn m), IsSmoothUnitaryConn A →
      ∀ (u : (Fin 4 → ℝ) → Fin m → ℂ), ContDiff ℝ ∞ u → ∀ η : ℝ≥0,
      (∀ ν c e, eLpNorm (entries (gaugeConn R A) ν c e) 4
        (volume.restrict (eBall c0 r)) ≤ η) →
      (∀ c, MemW12 (innerCube c0 r) (transp R u c) (tgrad R u c)) ∧
      ∀ c, w12Norm (innerCube c0 r) (transp R u c) (tgrad R u c) ≤
        C * (1 + η) * (m * ∑ e, eLpNorm (fun y => u y e) 2 (volume.restrict (innerCube c0 r)) +
          m * ∑ e, ∑ μ, eLpNorm (fun y => covDerV A u μ y e) 2
            (volume.restrict (innerCube c0 r))) := by
  have hab : ∀ i, c0 i - r / 4 < c0 i + r / 4 := fun i => by linarith
  obtain ⟨C, hC⟩ := critical_positive_graph hab m 0
  refine ⟨C, fun R hRu hRs A hA u hu η hη4 => ?_⟩
  set U := eBall c0 r
  set Q := innerCube c0 r
  have hUo : IsOpen U := isOpen_eBall c0 r
  have hQo : IsOpen Q := isOpen_box _ _
  have hQU : Q ⊆ U := innerCube_subset_eBall c0 hr
  have hRd : ∀ y ∈ U, MDiffAt R y := fun y hy c e =>
    ((hRs c e).contDiffAt (hUo.mem_nhds hy)).differentiableAt (by simp)
  have hue : ∀ e, ContDiff ℝ ∞ fun y => u y e := fun e => (contDiff_apply ℝ ℂ e).comp hu
  -- `W^{1,2}` membership
  have hmem : ∀ c, MemW12 Q (transp R u c) (tgrad R u c) := by
    intro c
    have hcd : ContDiffOn ℝ 1 (transp R u c) U := by
      have : ContDiffOn ℝ ∞ (transp R u c) U := by
        show ContDiffOn ℝ ∞ (fun y => ∑ e, R y c e * u y e) U
        exact ContDiffOn.sum fun e _ => (hRs c e).mul (hue e).contDiffOn
      exact this.of_le (by simp)
    exact EinsteinSM.memW12_of_contDiffOn hQo hUo (isCompact_closure_innerCube c0 r)
      (closure_innerCube_subset_eBall c0 hr) hcd
  refine ⟨hmem, fun c => ?_⟩
  -- the positive graph estimate with the cut Coulomb connection
  set A' := cutConn U (gaugeConn R A)
  have hskew : IsSkewHermitianConn A' := cutConn_gauge_skew hUo hRu hRd hA.skew
  have hΓ : IsSkewHermitianConn (fun (_ : Fin 4) (_ _ : Fin m) (_ : Fin 4 → ℝ) => (0 : ℂ)) :=
    fun _ _ _ _ => by simp
  have hpdR : ∀ μ c e, ContinuousOn (fun y => pd (fun y => R y c e) μ y) U := fun μ c e =>
    ((hRs c e).continuousOn_fderiv_of_isOpen hUo (by simp)).clm_apply continuousOn_const
  have hgcont : ∀ μ c e, ContinuousOn (fun y => gaugeConn R A μ y c e) U := by
    intro μ c e
    have hRc : ∀ c e, ContinuousOn (fun y => R y c e) U := fun c e => (hRs c e).continuousOn
    have hAc : ∀ c e, Continuous fun y => A μ y c e := fun c e => (hA.smooth μ c e).continuous
    simp only [gaugeConn, Matrix.sub_apply, Matrix.mul_apply, Matrix.star_apply, pdM,
      Matrix.of_apply]
    refine ContinuousOn.sub (continuousOn_finset_sum _ fun k _ => ContinuousOn.mul
      (continuousOn_finset_sum _ fun l _ => (hRc c l).mul (hAc l k).continuousOn) ?_)
      (continuousOn_finset_sum _ fun k _ => (hpdR μ c k).mul ?_)
    · exact (Complex.continuous_conj.comp_continuousOn (hRc e k))
    · exact (Complex.continuous_conj.comp_continuousOn (hRc e k))
  have hA'Q : ∀ μ c e, ∀ y ∈ Q, A' μ c e y = gaugeConn R A μ y c e := fun μ c e y hy => by
    simp [A', cutConn, hQU hy]
  have hA'm : ∀ μ c e, AEStronglyMeasurable (A' μ c e) (volume.restrict Q) := fun μ c e =>
    (((hgcont μ c e).mono hQU).congr fun y hy => hA'Q μ c e y hy).aestronglyMeasurable
      hQo.measurableSet
  have hA'4 : ∀ μ c e, eLpNorm (A' μ c e) 4 (volume.restrict Q) ≤ η := by
    intro μ c e
    calc eLpNorm (A' μ c e) 4 (volume.restrict Q) =
          eLpNorm (entries (gaugeConn R A) μ c e) 4 (volume.restrict Q) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [ae_restrict_mem hQo.measurableSet] with y hy
          exact hA'Q μ c e y hy
      _ ≤ eLpNorm (entries (gaugeConn R A) μ c e) 4 (volume.restrict U) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hQU le_rfl)
      _ ≤ η := hη4 μ c e
  have hgraph := ((hC η _ A' hΓ hskew (fun _ _ _ => aestronglyMeasurable_const)
    (fun _ _ _ _ => by simp) hA'm hA'4).1 (transp R u) (tgrad R u) hmem c).2
  refine hgraph.trans ?_
  refine mul_le_mul_right (add_le_add ?_ ?_) _
  · -- zeroth-order terms
    have hb : ∀ e, eLpNorm (transp R u e) 2 (volume.restrict Q) ≤
        ∑ c', eLpNorm (fun y => u y c') 2 (volume.restrict Q) := fun e =>
      eLpNorm_rot_le hQo.measurableSet (fun y hy => hRu y (hQU hy))
        (fun c' => (hue c').continuous.aestronglyMeasurable) (fun y _ => rfl)
    calc ∑ e, eLpNorm (transp R u e) 2 (volume.restrict Q) ≤
          ∑ _e : Fin m, ∑ c', eLpNorm (fun y => u y c') 2 (volume.restrict Q) :=
          Finset.sum_le_sum fun e _ => hb e
      _ = m * ∑ c', eLpNorm (fun y => u y c') 2 (volume.restrict Q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- covariant terms
    have hcov : ∀ e μ, ∀ y ∈ Q,
        covD (tgrad R u) (fun μ c e x => (fun (_ : Fin 4) (_ _ : Fin m) (_ : Fin 4 → ℝ) =>
          (0 : ℂ)) μ c e x + A' μ c e x) (transp R u) e μ y =
          (R y *ᵥ covDerV A u μ y) e := by
      intro e μ y hy
      have hcv := covDerV_gauge_at (hRu y (hQU hy)) A (hRd y (hQU hy))
        (fun c => (hue c).differentiable (by simp) y) μ
      rw [← hcv]
      simp only [covD, zero_add, hA'Q _ _ _ y hy, covDerV, Pi.add_apply, pdV, tgrad, transp,
        Matrix.mulVec, dotProduct]
      rfl
    have hcm : ∀ μ c', AEStronglyMeasurable (fun y => covDerV A u μ y c')
        (volume.restrict Q) := by
      intro μ c'
      refine Continuous.aestronglyMeasurable ?_
      simp only [covDerV, Pi.add_apply, pdV, Matrix.mulVec, dotProduct]
      refine Continuous.add ?_ (continuous_finset_sum _ fun k _ =>
        (hA.smooth μ c' k).continuous.mul (hue k).continuous)
      unfold pd
      exact ((hue c').continuous_fderiv (by simp)).clm_apply continuous_const
    calc ∑ e, ∑ μ, eLpNorm (covD (tgrad R u) (fun μ c e x =>
            (fun (_ : Fin 4) (_ _ : Fin m) (_ : Fin 4 → ℝ) => (0 : ℂ)) μ c e x + A' μ c e x)
            (transp R u) e μ) 2 (volume.restrict Q) ≤
          ∑ _e : Fin m, ∑ μ, ∑ c', eLpNorm (fun y => covDerV A u μ y c') 2
            (volume.restrict Q) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
            eLpNorm_rot_le hQo.measurableSet (fun y hy => hRu y (hQU hy)) (hcm μ)
              (hcov e μ)
      _ = m * ∑ e, ∑ μ, eLpNorm (fun y => covDerV A u μ y e) 2 (volume.restrict Q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_comm]

end TransportBound

/-! ### Weak identification of the covariant derivative -/

section CovLimit

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsFiniteMeasure ρ] {m : ℕ}

/-- **Weak identification of `∇^{A_k} u_k`**: if `∂u_k ⇀ g₀` weakly in `L²` and `A_k → A₀`,
`u_k → u₀` strongly in `L²`, then `∂u_k + A_k u_k → g₀ + A₀ u₀` against every bounded weight
(`D_{A_h}H_h ⇀ D_AH`). -/
theorem tendsto_integral_covDer {A : ℕ → Fin m → X → ℂ} {A₀ : Fin m → X → ℂ}
    {u : ℕ → Fin m → X → ℂ} {u₀ : Fin m → X → ℂ} {g : ℕ → X → ℂ} {g₀ : X → ℂ}
    (hA : ∀ e, LpTendsto ρ 2 (fun k => A k e) (A₀ e))
    (hu : ∀ e, LpTendsto ρ 2 (fun k => u k e) (u₀ e))
    (hg : ∀ k, MemLp (g k) 2 ρ) (hg₀ : MemLp g₀ 2 ρ)
    (hgw : ∀ w : X → ℝ, MemLp w 2 ρ →
      Tendsto (fun k => ∫ x, w x • g k x ∂ρ) atTop (𝓝 (∫ x, w x • g₀ x ∂ρ)))
    {w : X → ℝ} (hw : MemLp w ⊤ ρ) :
    Tendsto (fun k => ∫ x, w x • (g k x + ∑ e, A k e x * u k e x) ∂ρ) atTop
      (𝓝 (∫ x, w x • (g₀ x + ∑ e, A₀ e x * u₀ e x) ∂ρ)) := by
  have hprod : ∀ e, LpTendsto ρ 1 (fun k x => ContinuousLinearMap.mul ℝ ℂ (A k e x) (u k e x))
      (fun x => ContinuousLinearMap.mul ℝ ℂ (A₀ e x) (u₀ e x)) := fun e =>
    LpTendsto.bilin (p := 2) (q := 2) (r := 1) (ContinuousLinearMap.mul ℝ ℂ) (hA e) (hu e)
  have hsplit : ∀ (G : X → ℂ) (Ae ue : Fin m → X → ℂ), MemLp G 2 ρ →
      (∀ e, MemLp (fun x => ContinuousLinearMap.mul ℝ ℂ (Ae e x) (ue e x)) 1 ρ) →
      ∫ x, w x • (G x + ∑ e, Ae e x * ue e x) ∂ρ =
        ∫ x, w x • G x ∂ρ + ∑ e, ∫ x, w x • (Ae e x * ue e x) ∂ρ := by
    intro G Ae ue hG hP
    have hi : ∀ e, Integrable (fun x => w x • (Ae e x * ue e x)) ρ := fun e =>
      integrable_smul_of_memLp_one hw (by simpa using hP e)
    simp only [smul_add, Finset.smul_sum]
    rw [integral_add (integrable_smul_of_memLp_two hw hG) (integrable_finset_sum _ fun e _ => hi e),
      integral_finset_sum _ fun e _ => hi e]
  have hw2 : MemLp w 2 ρ := hw.mono_exponent le_top
  rw [hsplit _ _ _ hg₀ fun e => (hprod e).memLp_lim]
  refine ((hgw w hw2).add (tendsto_finset_sum _ fun e _ =>
    tendsto_integral_bdd_mul_mul (hA e) (hu e) hw)).congr fun k => ?_
  rw [hsplit _ _ _ (hg k) fun e => (hprod e).memLp k]

end CovLimit

/-! ### `thm:critical-quotient-defect`: quotient compactness in Coulomb charts -/

/-- The limit properties on one Coulomb cube `Q` along a subsequence `φ`: connection limit
`A_∞ ∈ W^{1,2}(Q)` (strong `L^q`, `q < 4`, weak gradients, weak curvature) and matter limits
`ũ_∞ ∈ W^{1,2}(Q)` (strong `L^q`, `q < 4`, weak gradients, weak covariant derivatives). -/
def QuotientLimit {m : ℕ} {S : Type} [Fintype S] (Q : Set (Fin 4 → ℝ)) (C : ℕ → MConn m)
    (uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ) (gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (φ : ℕ → ℕ) : Prop :=
  ∃ (Ainf : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (GA : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ)
    (uinf : S → Fin m → (Fin 4 → ℝ) → ℂ) (Gu : S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
    (∀ ν c e, MemW12 Q (Ainf ν c e) (GA ν c e)) ∧
    (∀ ν c e (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun k => eLpNorm
      (entries (C (φ k)) ν c e - Ainf ν c e) q (volume.restrict Q)) atTop (𝓝 0)) ∧
    (∀ ν c e μ (w : (Fin 4 → ℝ) → ℝ), MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • entryGrad (C (φ k)) ν c e μ x ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • GA ν c e μ x ∂(volume.restrict Q)))) ∧
    (∀ μ ν c e (w : (Fin 4 → ℝ) → ℝ), MemLp w ⊤ (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • curvatureW (entries (C (φ k))) (entryGrad (C (φ k))) μ ν c e x
        ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict Q)))) ∧
    (∀ s c, MemW12 Q (uinf s c) (Gu s c)) ∧
    (∀ s c (q : ℝ≥0∞), 1 ≤ q → q < 4 → Tendsto (fun k => eLpNorm
      (uT (φ k) s c - uinf s c) q (volume.restrict Q)) atTop (𝓝 0)) ∧
    (∀ s c μ (w : (Fin 4 → ℝ) → ℝ), MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • gT (φ k) s c μ x ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict Q)))) ∧
    (∀ s c μ (w : (Fin 4 → ℝ) → ℝ), MemLp w ⊤ (volume.restrict Q) →
      Tendsto (fun k => ∫ x, w x • (gT (φ k) s c μ x +
          ∑ e, entries (C (φ k)) μ c e x * uT (φ k) s e x) ∂(volume.restrict Q)) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x) ∂(volume.restrict Q))))

theorem QuotientLimit.comp {m : ℕ} {S : Type} [Fintype S] {Q : Set (Fin 4 → ℝ)}
    {C : ℕ → MConn m} {uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ}
    {gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} {φ ψ : ℕ → ℕ}
    (h : QuotientLimit Q C uT gT φ) (hψ : StrictMono ψ) : QuotientLimit Q C uT gT (φ ∘ ψ) := by
  obtain ⟨Ainf, GA, uinf, Gu, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have ht := hψ.tendsto_atTop
  exact ⟨Ainf, GA, uinf, Gu, h1, fun ν c e q hq hq4 => (h2 ν c e q hq hq4).comp ht,
    fun ν c e μ w hw => (h3 ν c e μ w hw).comp ht, fun μ ν c e w hw => (h4 μ ν c e w hw).comp ht,
    h5, fun s c q hq hq4 => (h6 s c q hq hq4).comp ht, fun s c μ w hw => (h7 s c μ w hw).comp ht,
    fun s c μ w hw => (h8 s c μ w hw).comp ht⟩

/-- Extraction on one cube: a family bounded in `W^{1,2}(Q)` has a `QuotientLimit` subsequence. -/
theorem exists_quotientLimit {m : ℕ} {S : Type} [Fintype S] {lo hi : Fin 4 → ℝ}
    (hlh : ∀ i, lo i < hi i) {C : ℕ → MConn m} {uT : ℕ → S → Fin m → (Fin 4 → ℝ) → ℂ}
    {gT : ℕ → S → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hWA : ∀ k ν c e, MemW12 (box lo hi) (entries (C k) ν c e) (entryGrad (C k) ν c e))
    (hWu : ∀ k s c, MemW12 (box lo hi) (uT k s c) (gT k s c)) {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hBA : ∀ k ν c e, w12Norm (box lo hi) (entries (C k) ν c e) (entryGrad (C k) ν c e) ≤ B)
    (hBu : ∀ k s c, w12Norm (box lo hi) (uT k s c) (gT k s c) ≤ B) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ QuotientLimit (box lo hi) C uT gT (φ ∘ ψ) := by
  set ρ := volume.restrict (box lo hi)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  set P := (Fin 4 × Fin m × Fin m) ⊕ (S × Fin m)
  set U : ℕ → P → (Fin 4 → ℝ) → ℂ := fun k p => match p with
    | .inl q => entries (C (φ k)) q.1 q.2.1 q.2.2
    | .inr q => uT (φ k) q.1 q.2 with hU
  set G : ℕ → P → Fin 4 → (Fin 4 → ℝ) → ℂ := fun k p => match p with
    | .inl q => entryGrad (C (φ k)) q.1 q.2.1 q.2.2
    | .inr q => gT (φ k) q.1 q.2 with hG
  have hW : ∀ k p, MemW12 (box lo hi) (U k p) (G k p) := by
    intro k p; rcases p with q | q
    · exact hWA _ _ _ _
    · exact hWu _ _ _
  have hB : ∀ k p, w12Norm (box lo hi) (U k p) (G k p) ≤ B := by
    intro k p; rcases p with q | q
    · exact hBA _ _ _ _
    · exact hBu _ _ _
  have hd : Fintype.card (Fin 4) = 4 := by simp
  obtain ⟨ψ, hψ, v, Gv, hvW, hLq, hweak⟩ := w12_compactness_box hd hlh U G hW hBt hB
  have hL2 : ∀ p, LpTendsto ρ 2 (fun k => U (ψ k) p) (v p) := fun p =>
    ⟨fun k => (hW _ p).memLp, (hvW p).memLp, hLq p 2 one_le_two (by norm_num)⟩
  refine ⟨ψ, hψ, fun ν c e => v (.inl (ν, c, e)), fun ν c e => Gv (.inl (ν, c, e)),
    fun s c => v (.inr (s, c)), fun s c => Gv (.inr (s, c)), fun ν c e => hvW _,
    fun ν c e q hq1 hq4 => hLq (.inl (ν, c, e)) q hq1 hq4,
    fun ν c e μ w hw => hweak (.inl (ν, c, e)) μ w hw, ?_, fun s c => hvW _,
    fun s c q hq1 hq4 => hLq (.inr (s, c)) q hq1 hq4,
    fun s c μ w hw => hweak (.inr (s, c)) μ w hw, ?_⟩
  · intro μ ν c e w hw
    exact tendsto_integral_curvatureW (ρ := ρ) (A := fun k ν c e => U (ψ k) (.inl (ν, c, e)))
      (dA := fun k ν c e => G (ψ k) (.inl (ν, c, e)))
      (A₀ := fun ν c e => v (.inl (ν, c, e))) (dA₀ := fun ν c e => Gv (.inl (ν, c, e)))
      (fun ν c e => hL2 (.inl (ν, c, e)))
      (fun k ν c e μ => (hW (ψ k) (.inl (ν, c, e))).memLp_grad μ)
      (fun ν c e μ => (hvW (.inl (ν, c, e))).memLp_grad μ)
      (fun ν c e μ w hw => hweak (.inl (ν, c, e)) μ w hw) hw μ ν c e
  · intro s c μ w hw
    exact tendsto_integral_covDer (A := fun k e => U (ψ k) (.inl (μ, c, e)))
      (A₀ := fun e => v (.inl (μ, c, e))) (u := fun k e => U (ψ k) (.inr (s, e)))
      (u₀ := fun e => v (.inr (s, e))) (g := fun k => G (ψ k) (.inr (s, c)) μ)
      (g₀ := Gv (.inr (s, c)) μ) (fun e => hL2 (.inl (μ, c, e))) (fun e => hL2 (.inr (s, e)))
      (fun k => (hW (ψ k) (.inr (s, c))).memLp_grad μ) ((hvW (.inr (s, c))).memLp_grad μ)
      (fun w hw => hweak (.inr (s, c)) μ w hw) hw

/-- **`thm:critical-quotient-defect`, quotient compactness (`eq:critical-quotient-convergence`),
conditional on the named Uhlenbeck gap `UhlenbeckSmallEnergyGauge`.**  Box rendering: chart
`K = box a b`, smooth unitary connections `A_h` (rank `m`) with bounded curvature energy and
uniformly integrable critical curvature energy (Q2); a finite family of smooth matter sections
`u_{h,s}` (Higgs, spinor and dual-spinor components in the defining representation) with the
gauge-invariant bounds `sup_h (‖u_{h,s}‖_{L²(K)} + ‖∇^{A_h} u_{h,s}‖_{L²(K)}) < ∞` (Q3)/(Q4).
Then for every compact `K' ⊂ K` and `η > 0` there are a finite cover of `K'` by cubes
`Q_j ⊂ K`, cutoff-dependent local gauges `R_{h,j}` (unitary on `Q_j`) in which
`Ã_{h,j} = R_{h,j}·A_h` is Coulomb on `Q_j` with `‖Ã_{h,j}‖_{L⁴(Q_j)} ≤ η`, and one subsequence
along which on every cube (`QuotientLimit`): `Ã ⇀ A_j` in `W^{1,2}`, `Ã → A_j` in `L^q` for
`1 ≤ q < 4`, `F_Ã → F_{A_j}` against bounded weights; the transported matter `R_{h,j}u_{h,s}`
converges weakly in `W^{1,2}` and strongly in every `L^q`, `q < 4`, and its covariant derivatives
`∇^{Ã}(R u)` (`= R ∇^{A}u`, `transported_covDer`) converge against bounded weights to the covariant
derivatives of the limits. -/
theorem critical_quotient_compactness_of_gauge {m : ℕ} (hU : UhlenbeckSmallEnergyGauge m)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
          QuotientLimit (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ := by
  obtain ⟨N, ctr, r, hr, hball, hcover, R, hRu, hRs, hdiv, ⟨BA, hBAt, hAW⟩, hA4⟩ :=
    uhlenbeck_ball_cover hU A hA hUI hK' hK'Q hη
  obtain ⟨B, hBt, hB⟩ := hQ3
  choose C hC using fun j => transported_bound (ctr j) hr m
  have hT := fun h j s => hC j (R h j) (hRu h j) (hRs h j) (A h) (hA h) (u h s) (hu h s) η (hA4 h j)
  have hQK : ∀ j, innerCube (ctr j) r ⊆ box a b := fun j =>
    (innerCube_subset_eBall (ctr j) hr).trans (hball j)
  refine ⟨N, ctr, r, hr, hQK, hcover, R, fun h j y hy => hRu h j y (innerCube_subset_eBall _ hr hy),
    fun h j x hx => hdiv h j x (innerCube_subset_eBall _ hr hx), fun h j ν c e =>
      (eLpNorm_mono_measure _ (Measure.restrict_mono (innerCube_subset_eBall _ hr) le_rfl)).trans
        (hA4 h j ν c e), ?_⟩
  -- uniform `W^{1,2}` bounds on every cube
  set Bj : Fin N → ℝ≥0∞ := fun j => BA + (C j : ℝ≥0∞) * (1 + (η : ℝ≥0∞)) * (m * B + m * B)
  have hBjt : ∀ j, Bj j ≠ ⊤ := fun j => ENNReal.add_ne_top.mpr ⟨hBAt, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp)) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) hBt, ENNReal.mul_ne_top (by simp) hBt⟩)⟩
  have hsum1 : ∀ j h s, ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (innerCube (ctr j) r))
      ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => eLpNorm_mono_measure _ (Measure.restrict_mono (hQK j) le_rfl)).trans
      (le_add_right le_rfl |>.trans (hB h s))
  have hsum2 : ∀ j h s, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2
      (volume.restrict (innerCube (ctr j) r)) ≤ B := fun j h s =>
    (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun μ _ =>
      eLpNorm_mono_measure _ (Measure.restrict_mono (hQK j) le_rfl)).trans
      (le_add_left le_rfl |>.trans (hB h s))
  have hBu : ∀ j h s c, w12Norm (innerCube (ctr j) r) (transp (R h j) (u h s) c)
      (tgrad (R h j) (u h s) c) ≤ Bj j := by
    intro j h s c
    refine ((hT h j s).2 c).trans (le_add_left ?_)
    gcongr
    · exact hsum1 j h s
    · exact hsum2 j h s
  have hBA : ∀ j h ν c e, w12Norm (innerCube (ctr j) r) (entries (gaugeConn (R h j) (A h)) ν c e)
      (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ Bj j := fun j h ν c e =>
    (w12Norm_mono (innerCube_subset_eBall _ hr) _ _).trans ((hAW h j ν c e).2.trans le_self_add)
  -- the common extraction
  refine exists_common_subseq (fun j φ => QuotientLimit (innerCube (ctr j) r)
    (fun h => gaugeConn (R h j) (A h)) (fun h s => transp (R h j) (u h s))
    (fun h s => tgrad (R h j) (u h s)) φ) (fun j φ _ => ?_) (fun j φ ψ hψ hP => hP.comp hψ)
  exact exists_quotientLimit (fun i => by linarith)
    (fun h ν c e => (hAW h j ν c e).1.mono (innerCube_subset_eBall _ hr))
    (fun h s c => (hT h j s).1 c) (hBjt j) (fun h ν c e => hBA j h ν c e)
    (fun h s c => hBu j h s c) φ

/-- In the Coulomb chart the transported covariant derivative is the rotated original one:
`∂(R u)_c + Σ_e Ã_{μ,ce} (R u)_e = (R ∇^A_μ u)_c` (gauge covariance), so the `QuotientLimit`
covariant-derivative clause is the weak limit of `R_{h,j} ∇^{A_h} u_{h,s}`. -/
theorem transported_covDer {m : ℕ} {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ} {x : Fin 4 → ℝ}
    (hRu : R x ∈ unitaryGroup (Fin m) ℂ) (hR : MDiffAt R x) (A : MConn m)
    {u : (Fin 4 → ℝ) → Fin m → ℂ} (hu : VDiffAt u x) (μ : Fin 4) (c : Fin m) :
    tgrad R u c μ x + ∑ e, entries (gaugeConn R A) μ c e x * transp R u e x =
      (R x *ᵥ covDerV A u μ x) c := by
  rw [← covDerV_gauge_at hRu A hR hu μ]
  simp only [covDerV, Pi.add_apply, pdV, tgrad, transp, entries, Matrix.mulVec, dotProduct]
  rfl

/-- **Non-vacuity**: the hypothesis packet of `critical_quotient_compactness_of_gauge` (apart from
the named Uhlenbeck theorem) is satisfiable: zero connection, zero matter sections. -/
example : IsSmoothUnitaryConn (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) ∧
    (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (_h : ℕ) (_s : Unit),
      ∑ e, eLpNorm (fun y => (fun (_ : Fin 4 → ℝ) (_ : Fin 1) => (0 : ℂ)) y e) 2
          (volume.restrict (box (0 : Fin 4 → ℝ) 1)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
          (fun (_ : Fin 4 → ℝ) (_ : Fin 1) => (0 : ℂ)) μ y e) 2
          (volume.restrict (box (0 : Fin 4 → ℝ) 1)) ≤ B) := by
  refine ⟨⟨fun _ _ _ => contDiff_const, fun _ _ => by simp⟩, 0, by simp, fun _ _ => ?_⟩
  have h0 : ∀ μ y, covDerV (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun (_ : Fin 4 → ℝ) (_ : Fin 1) => (0 : ℂ)) μ y = 0 := by
    intro μ y
    funext e
    simp [covDerV, pdV, pd_const_complex]
  simp [h0]

end RenewalGeometry.CriticalQuotient
