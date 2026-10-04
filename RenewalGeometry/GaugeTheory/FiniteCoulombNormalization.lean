/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.ODEAprioriContinuation
import RenewalGeometry.GaugeTheory.CoulombHomotopyAlgebra

/-!
# Finite critical Coulomb normalization (`thm:finite-Coulomb-normalization`, Einstein–SM
  action closure)

Setting (disclosed rendering of the paper's).  The periodic grid `(ℤ/n)^ι`, `card ι = 4`, mesh
`h > 0`, fixed side `L = n h` (the paper's comparison box has `L = 2π`; all constants below depend
only on `L`, the group and the metric, never on `n` or `h`).  The gauge group is the unitary group
of a finite-dimensional C*-algebra `𝔸` (`U(N)`: `N × N` matrices with the operator norm;
`U(3) × U(2)`: block matrices), with Lie algebra the skew-adjoint elements; the invariant
Lie-algebra metric is a real inner product space `E` with a linear identification
`toE : 𝔸 ≃L[ℝ] E` that is invariant under unitary conjugation
(`‖toE (U X U^*)‖ = ‖toE X‖`) and infinitesimally invariant (`⟪toE a, toE [a, u]⟫ = 0` for
skew-adjoint `a`); for matrices this is the Frobenius metric `Re tr(X^* Y)`.  The logarithm is the
analytic branch near the identity (`SeriesLogChart.logChart`), a conjugation-invariant chart.

For a logarithmic seed `B` (skew-adjoint) and a site gauge `q`, the auxiliary homotopy of the
paper's proof is `A_s = h⁻¹ Log(q_x e^{shB_μ(x)} q_{x+μ}^*)` (`linkA`), driven by the vector field
`q̇_x = ξ_x q_x`, `ξ = M_{A_s}⁻¹ δ_h R_s`, `R_s = 𝒥(h ad_{A_s})⁻¹ Ad_q B`
(`eq:native-Coulomb-homotopy-ODE`; `field`).

This file proves:
* `field_contDiffOn`: the vector field is `C¹` (indeed `C^∞`) on the open set `domO` where the
  logarithms are defined and `‖A_μ‖_{4,h}` is below the Faddeev–Popov threshold;
* `isCompact_setK`: the a priori set (unitary gauges, strict chart and transverse margins) is
  compact;
* the a priori analysis along any solution (`apriori_of_solution`): the gauges stay unitary, the
  Coulomb condition `δ_h A_s = 0` is preserved, `‖A_s‖_{2,h} ≤ s ‖B‖_{2,h}` (the physical `L²_h`
  estimate), `‖𝔽_h(A_s)‖_{2,h} = ‖𝔽_h(sB)‖_{2,h} ≤ ‖𝔽_h(B)‖_{2,h} + C‖B‖²_{4,h}`, and the
  first-exit bound `‖A_s‖_{4,h} ≤ (4/3) C₀ b` from `a ≤ C₀ b + C₁ a²`;
* **`finite_coulomb_normalization`** (`thm:finite-Coulomb-normalization`): there are `ε_c, C_c`
  (depending on `L`, the group, the metric and on a prescribed `ε_* > 0`, not on `n`, `h`) such
  that every seed with `‖B‖_{4,h} + ‖𝔽_h(B)‖_{2,h} ≤ ε_c` admits a unitary site gauge `q` with
  `A_μ(x) = h⁻¹ Log(q_x e^{hB_μ(x)} q_{x+μ}^*)`, `δ_h A = 0`,
  `‖A‖_{1,h} + ‖A‖_{4,h} ≤ C_c(‖B‖_{2,h} + ‖𝔽_h(B)‖_{2,h} + ‖B‖²_{4,h})` and `‖A‖_{4,h} ≤ ε_*`.
-/

open NormedSpace Filter Topology Finset Set

namespace RenewalGeometry.FiniteCoulomb

open OperatorHalfCoth MatrixExpDerivative SeriesLogChart GridSobolev LogGaugeDifferential
  CoulombHomotopy CoulombApriori CurvatureSplit

noncomputable section

variable {𝔸 : Type*} [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E]
variable (toE : 𝔸 ≃L[ℝ] E)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {n : ℕ} [NeZero n]

/-! ### The homotopy data -/

/-- The gauged auxiliary link `q_x e^{shB_μ(x)} q_{x+μ}^*`. -/
def linkP (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) : 𝔸 :=
  q x * exp (s • (h • B μ x)) * star (q (x + gridStep μ))

/-- The logarithmic link coordinates `A_s = h⁻¹ Log(q_x e^{shB} q_{x+μ}^*)`. -/
def linkA (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) :
    ι → (ι → ZMod n) → 𝔸 :=
  fun μ x => h⁻¹ • logChart (linkP h B s q μ x)

/-- `R_s = 𝒥(h ad_{A_s})⁻¹ Ad_q B`. -/
def linkR (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) :
    ι → (ι → ZMod n) → 𝔸 :=
  fun μ x => Ring.inverse (dexpJ (h • adOp (linkA h B s q μ x))) (q x * B μ x * star (q x))

/-- The `E`-valued transverse solution `M_{A_s}⁻¹ δ_h R_s` (via the invertible extension
`N_A` of `lem:native-FP-inverse`). -/
def solveFP (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) :
    (ι → ZMod n) → E :=
  Ring.inverse (FaddeevPopov.nCLM (brE toE) h (fun μ y => toE (linkA h B s q μ y)))
    (periodicHodgeCodiff h gridStep (fun μ y => toE (linkR h B s q μ y)))

/-- The skew-adjoint part `½(X - X^*)`. -/
def skewPart (X : 𝔸) : 𝔸 := (1 / 2 : ℝ) • (X - star X)

theorem star_skewPart (X : 𝔸) : star (skewPart X) = -skewPart X := by
  simp only [skewPart, star_smul, star_sub, star_star, star_trivial]
  rw [← smul_neg, neg_sub]

theorem skewPart_of_skew {X : 𝔸} (hX : star X = -X) : skewPart X = X := by
  rw [skewPart, hX, sub_neg_eq_add, ← two_smul ℝ X, smul_smul]; norm_num

/-- The generator `ξ_s` (`eq:native-Coulomb-homotopy-ODE`), projected to the Lie algebra. -/
def genXi (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) :
    (ι → ZMod n) → 𝔸 :=
  fun x => skewPart (toE.symm (solveFP toE h B s q x))

/-- The vector field `q ↦ (ξ_x q_x)_x` of the Coulomb homotopy. -/
def field (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ) (q : (ι → ZMod n) → 𝔸) :
    (ι → ZMod n) → 𝔸 :=
  fun x => genXi toE h B s q x * q x

/-- The open domain of the ODE: logarithms defined, scaled links in the small chart, and the
transverse threshold `‖A_μ‖_{4,h} < r_FP`. -/
def domO (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : Set (ℝ × ((ι → ZMod n) → 𝔸)) :=
  {p | (∀ μ x, ‖linkP h B p.1 p.2 μ x - 1‖ < 1) ∧
    (∀ μ x, ‖logChart (linkP h B p.1 p.2 μ x)‖ < 1 / 64) ∧
    ∀ μ, gridL4Norm h (fun y => toE (linkA h B p.1 p.2 μ y)) < FaddeevPopov.rFP (brE toE)}

/-- The compact a priori set. -/
def setK (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : Set (ℝ × ((ι → ZMod n) → 𝔸)) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ (∀ x, p.2 x ∈ unitary 𝔸) ∧
    (∀ μ x, ‖linkP h B p.1 p.2 μ x - 1‖ ≤ 1 / 2) ∧
    (∀ μ x, ‖logChart (linkP h B p.1 p.2 μ x)‖ ≤ 1 / 128) ∧
    ∀ μ, gridL4Norm h (fun y => toE (linkA h B p.1 p.2 μ y)) ≤ FaddeevPopov.rFP (brE toE) / 2}

theorem setK_subset_domO (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : setK toE h B ⊆ domO toE h B := by
  rintro p ⟨-, -, h1, h2, h3⟩
  refine ⟨fun μ x => (h1 μ x).trans_lt (by norm_num), fun μ x => (h2 μ x).trans_lt (by norm_num),
    fun μ => (h3 μ).trans_lt ?_⟩
  have := FaddeevPopov.rFP_pos (brE toE)
  linarith

/-! ### Regularity of the vector field -/

theorem contDiffAt_linkP {k : WithTop ℕ∞} (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) (p : ℝ × ((ι → ZMod n) → 𝔸)) :
    ContDiffAt ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkP h B p.1 p.2 μ x) p := by
  have hq : ∀ y, ContDiffAt ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => p.2 y) p := fun y =>
    ((contDiff_apply ℝ 𝔸 y).comp contDiff_snd).contDiffAt
  have hexp : ContDiffAt ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => exp (p.1 • (h • B μ x))) p := by
    have h1 : ContDiff ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => p.1 • (h • B μ x)) :=
      contDiff_fst.smul contDiff_const
    exact (exp_analytic (𝕂 := ℝ) _).contDiffAt.comp p h1.contDiffAt
  have hstar : ContDiffAt ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => star (p.2 (x + gridStep μ))) p :=
    ((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸).contDiff.contDiffAt.comp p (hq _)
  exact ((hq x).mul hexp).mul hstar

theorem continuous_linkP (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n) :
    Continuous (fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkP h B p.1 p.2 μ x) :=
  continuous_iff_continuousAt.2 fun p => (contDiffAt_linkP (k := 0) h B μ x p).continuousAt

theorem contDiffAt_linkA {k : WithTop ℕ∞} (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) {p : ℝ × ((ι → ZMod n) → 𝔸)} (hp : ‖linkP h B p.1 p.2 μ x - 1‖ < 1) :
    ContDiffAt ℝ k (fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkA h B p.1 p.2 μ x) p :=
  ((contDiffAt_logChart hp).comp p (contDiffAt_linkP h B μ x p)).const_smul _

/-- The chart domain `D₁ = {‖linkP - 1‖ < 1}`. -/
def domChart (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : Set (ℝ × ((ι → ZMod n) → 𝔸)) :=
  {p | ∀ μ x, ‖linkP h B p.1 p.2 μ x - 1‖ < 1}

theorem isOpen_domChart (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : IsOpen (domChart h B) := by
  have : domChart h B = ⋂ μ, ⋂ x, (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      linkP h B p.1 p.2 μ x) ⁻¹' {P | ‖P - 1‖ < 1} := by
    ext p; simp [domChart]
  rw [this]
  exact isOpen_iInter_of_finite fun μ => isOpen_iInter_of_finite fun x =>
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).preimage
      (continuous_linkP h B μ x)

theorem continuousOn_linkA (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n) :
    ContinuousOn (fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkA h B p.1 p.2 μ x) (domChart h B) :=
  fun p hp => (contDiffAt_linkA (k := 0) h B μ x (hp μ x)).continuousAt.continuousWithinAt

theorem continuous_gridL4Norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (h : ℝ) :
    Continuous (fun u : (ι → ZMod n) → F => gridL4Norm h u) := by
  unfold gridL4Norm
  refine Continuous.rpow_const ?_ fun _ => Or.inr (by norm_num)
  fun_prop

theorem continuousOn_L4 (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι) :
    ContinuousOn (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      gridL4Norm h (fun y => toE (linkA h B p.1 p.2 μ y))) (domChart h B) := by
  refine (continuous_gridL4Norm h).comp_continuousOn ?_
  exact continuousOn_pi.2 fun y => toE.continuous.comp_continuousOn (continuousOn_linkA h B μ y)

theorem domO_eq (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) :
    domO toE h B = domChart h B ∩
      ((⋂ μ, ⋂ x, (domChart h B ∩ (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        ‖logChart (linkP h B p.1 p.2 μ x)‖) ⁻¹' Iio (1 / 64))) ∩
      ⋂ μ, (domChart h B ∩ (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        gridL4Norm h (fun y => toE (linkA h B p.1 p.2 μ y))) ⁻¹'
          Iio (FaddeevPopov.rFP (brE toE)))) := by
  ext p
  simp only [domO, domChart, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, Set.mem_preimage,
    Set.mem_Iio]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun μ x => ⟨h1, h2 μ x⟩, fun μ => ⟨h1, h3 μ⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun μ x => (h2 μ x).2, fun μ => (h3 μ).2⟩

theorem continuousOn_logChart_linkP (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) :
    ContinuousOn (fun p : ℝ × ((ι → ZMod n) → 𝔸) => logChart (linkP h B p.1 p.2 μ x))
      (domChart h B) := by
  intro p hp
  have hc : ContDiffAt ℝ 0 (logChart ∘ fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkP h B p.1 p.2 μ x)
      p := (contDiffAt_logChart (hp μ x)).comp p (contDiffAt_linkP h B μ x p)
  exact hc.continuousAt.continuousWithinAt

theorem isOpen_domO (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : IsOpen (domO toE h B) := by
  rw [domO_eq]
  have hD := isOpen_domChart h B
  refine hD.inter (IsOpen.inter ?_ ?_)
  · exact isOpen_iInter_of_finite fun μ => isOpen_iInter_of_finite fun x =>
      ContinuousOn.isOpen_inter_preimage (continuousOn_logChart_linkP h B μ x).norm hD isOpen_Iio
  · exact isOpen_iInter_of_finite fun μ =>
      ContinuousOn.isOpen_inter_preimage (continuousOn_L4 toE h B μ) hD isOpen_Iio

theorem h_smul_linkA {h : ℝ} (hh : h ≠ 0) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ)
    (q : (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n) :
    h • linkA h B s q μ x = logChart (linkP h B s q μ x) := by
  simp only [linkA, smul_smul, mul_inv_cancel₀ hh, one_smul]

theorem isUnit_dexpJ_linkA {h : ℝ} (hh : h ≠ 0) (B : ι → (ι → ZMod n) → 𝔸) (s : ℝ)
    (q : (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n)
    (hL : ‖logChart (linkP h B s q μ x)‖ ≤ 1 / 8) :
    IsUnit (dexpJ (h • adOp (linkA h B s q μ x))) := by
  have := isUnit_dexpJ_adOp_of_norm_le (h • linkA h B s q μ x)
    (by rw [h_smul_linkA hh]; exact hL)
  rwa [adOp_smul] at this

theorem isOpen_fpSet (h : ℝ) (r : ℝ) :
    IsOpen {A : ι → (ι → ZMod n) → E | ∀ μ, gridL4Norm h (A μ) < r} := by
  rw [setOf_forall]
  exact isOpen_iInter_of_finite fun μ =>
    isOpen_lt ((continuous_gridL4Norm h).comp (continuous_apply μ)) continuous_const

/-- **The vector field of the Coulomb homotopy is smooth on its open domain.** -/
theorem contDiffAt_field (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (B : ι → (ι → ZMod n) → 𝔸) {p : ℝ × ((ι → ZMod n) → 𝔸)} (hp : p ∈ domO toE h B) :
    ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) => field toE h B p.1 p.2) p := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hA : ∀ μ x, ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) => linkA h B p.1 p.2 μ x) p :=
    fun μ x => contDiffAt_linkA h B μ x (hp1 μ x)
  have hAbar : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      (fun μ y => toE (linkA h B p.1 p.2 μ y))) p :=
    contDiffAt_pi.2 fun μ => contDiffAt_pi.2 fun y =>
      (toE : 𝔸 →L[ℝ] E).contDiff.contDiffAt.comp p (hA μ y)
  have hR : ∀ μ x, ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      linkR h B p.1 p.2 μ x) p := by
    intro μ x
    have hU := isUnit_dexpJ_linkA hh.ne' B p.1 p.2 μ x ((hp2 μ x).le.trans (by norm_num))
    obtain ⟨u, hu⟩ := hU
    have h1 : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        dexpJ (h • adOp (linkA h B p.1 p.2 μ x))) p := by
      have hZ : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
          (h • adL : 𝔸 →L[ℝ] (𝔸 →L[ℝ] 𝔸)) (linkA h B p.1 p.2 μ x)) p :=
        (h • adL : 𝔸 →L[ℝ] (𝔸 →L[ℝ] 𝔸)).contDiff.contDiffAt.comp p (hA μ x)
      have hZ' : (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
          (h • adL : 𝔸 →L[ℝ] (𝔸 →L[ℝ] 𝔸)) (linkA h B p.1 p.2 μ x)) =
          fun p => h • adOp (linkA h B p.1 p.2 μ x) := by
        funext p; rw [ContinuousLinearMap.smul_apply, adL_apply]
      rw [hZ'] at hZ
      exact (contDiff_dexpJ (k := 1)).contDiffAt.comp p hZ
    have h2 : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        Ring.inverse (dexpJ (h • adOp (linkA h B p.1 p.2 μ x)))) p := by
      have hi := contDiffAt_ringInverse ℝ (n := 1) u
      rw [hu] at hi
      exact hi.comp p h1
    have hq : ∀ y, ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) => p.2 y) p := fun y =>
      ((contDiff_apply ℝ 𝔸 y).comp contDiff_snd).contDiffAt
    have h3 : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        p.2 x * B μ x * star (p.2 x)) p :=
      ((hq x).mul contDiffAt_const).mul
        (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸).contDiff.contDiffAt.comp p (hq x))
    exact h2.clm_apply h3
  have hRbar : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      periodicHodgeCodiff h gridStep (fun μ y => toE (linkR h B p.1 p.2 μ y))) p := by
    refine contDiffAt_pi.2 fun x => ?_
    simp only [periodicHodgeCodiff, periodicHodgeBwd]
    refine ContDiffAt.neg (ContDiffAt.sum fun μ _ => ContDiffAt.const_smul _ (ContDiffAt.sub ?_ ?_))
    · exact (toE : 𝔸 →L[ℝ] E).contDiff.contDiffAt.comp p (hR μ x)
    · exact (toE : 𝔸 →L[ℝ] E).contDiff.contDiffAt.comp p (hR μ _)
  have hinv : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
      Ring.inverse (FaddeevPopov.nCLM (brE toE) h (fun μ y => toE (linkA h B p.1 p.2 μ y)))) p := by
    have hU := (FaddeevPopov.fp_inverse_contDiffOn (k := 1) (n := n) hι (brE toE) hh).1
    have hmem : (fun μ y => toE (linkA h B p.1 p.2 μ y)) ∈
        {A : ι → (ι → ZMod n) → E | ∀ μ, gridL4Norm h (A μ) < FaddeevPopov.rFP (brE toE)} := hp3
    exact (hU.contDiffAt ((isOpen_fpSet h _).mem_nhds hmem)).comp p hAbar
  have hsol : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) => solveFP toE h B p.1 p.2) p :=
    hinv.clm_apply hRbar
  refine contDiffAt_pi.2 fun x => ?_
  have hξ : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) => genXi toE h B p.1 p.2 x) p := by
    have h1 : ContDiffAt ℝ 1 (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        toE.symm (solveFP toE h B p.1 p.2 x)) p :=
      (toE.symm : E →L[ℝ] 𝔸).contDiff.contDiffAt.comp p (contDiffAt_pi.1 hsol x)
    have h2 := ((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸).contDiff.contDiffAt.comp p h1
    exact (h1.sub h2).const_smul (1 / 2 : ℝ)
  exact hξ.mul (((contDiff_apply ℝ 𝔸 x).comp contDiff_snd).contDiffAt)

theorem field_contDiffOn (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (B : ι → (ι → ZMod n) → 𝔸) :
    ContDiffOn ℝ 1 (Function.uncurry (field toE h B)) (domO toE h B) :=
  fun _ hp => (contDiffAt_field toE hι hh B hp).contDiffWithinAt

/-! ### Compactness of the a priori set -/

theorem isCompact_setK (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : IsCompact (setK toE h B) := by
  set D := {p : ℝ × ((ι → ZMod n) → 𝔸) | ∀ μ x, ‖linkP h B p.1 p.2 μ x - 1‖ ≤ 1 / 2} with hDdef
  have hDc : IsClosed D := by
    have : D = ⋂ μ, ⋂ x, (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
        linkP h B p.1 p.2 μ x) ⁻¹' {P | ‖P - 1‖ ≤ 1 / 2} := by
      ext p; simp [D]
    rw [this]
    exact isClosed_iInter fun μ => isClosed_iInter fun x =>
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).preimage
        (continuous_linkP h B μ x)
  have hDsub : D ⊆ domChart h B := fun p hp μ x => (hp μ x).trans_lt (by norm_num)
  have hK : setK toE h B = {p : ℝ × ((ι → ZMod n) → 𝔸) | p.1 ∈ Icc (0 : ℝ) 1} ∩
      {p | ∀ x, p.2 x ∈ unitary 𝔸} ∩ (D ∩ ((⋂ μ, ⋂ x, (D ∩
        (fun p : ℝ × ((ι → ZMod n) → 𝔸) => ‖logChart (linkP h B p.1 p.2 μ x)‖) ⁻¹' Iic (1 / 128)))
        ∩ ⋂ μ, (D ∩ (fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
          gridL4Norm h (fun y => toE (linkA h B p.1 p.2 μ y))) ⁻¹'
            Iic (FaddeevPopov.rFP (brE toE) / 2)))) := by
    ext p
    simp only [setK, D, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h0, h1, h2, h3, h4⟩
      exact ⟨⟨h0, h1⟩, h2, fun μ x => ⟨h2, h3 μ x⟩, fun μ => ⟨h2, h4 μ⟩⟩
    · rintro ⟨⟨h0, h1⟩, h2, h3, h4⟩
      exact ⟨h0, h1, h2, fun μ x => (h3 μ x).2, fun μ => (h4 μ).2⟩
  have hclosed : IsClosed (setK toE h B) := by
    rw [hK]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (hDc.inter (IsClosed.inter ?_ ?_))
    · exact isClosed_Icc.preimage continuous_fst
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_unitary.preimage
        ((continuous_apply x).comp continuous_snd)
    · exact isClosed_iInter fun μ => isClosed_iInter fun x =>
        ContinuousOn.preimage_isClosed_of_isClosed
          ((continuousOn_logChart_linkP h B μ x).norm.mono hDsub) hDc isClosed_Iic
    · exact isClosed_iInter fun μ =>
        ContinuousOn.preimage_isClosed_of_isClosed
          ((continuousOn_L4 toE h B μ).mono hDsub) hDc isClosed_Iic
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ((ι → ZMod n) → 𝔸))) (r := 1)).subset ?_
  rintro p ⟨h0, h1, -⟩
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg h0.1]; exact h0.2
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun x =>
      (CStarRing.norm_of_mem_unitary (h1 x)).le

/-! ### Unitary gauges, unitary links and skewness -/

omit [Nontrivial 𝔸] in
/-- In a finite-dimensional algebra a left inverse is a right inverse. -/
theorem mul_star_of_star_mul {u : 𝔸} (h : star u * u = 1) : u * star u = 1 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℝ u) := by
    intro a b hab
    have hab' : u * a = u * b := hab
    calc a = star u * u * a := by rw [h, one_mul]
      _ = star u * (u * a) := mul_assoc _ _ _
      _ = star u * (u * b) := by rw [hab']
      _ = b := by rw [← mul_assoc, h, one_mul]
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have hv' : u * v = 1 := hv
  have : star u = v := by
    calc star u = star u * (u * v) := by rw [hv', mul_one]
      _ = v := by rw [← mul_assoc, h, one_mul]
  rw [this, hv']

/-- A unitary as a unit. -/
def unitUnit {u : 𝔸} (hu : u ∈ unitary 𝔸) : 𝔸ˣ :=
  ⟨u, star u, Unitary.mul_star_self_of_mem hu, Unitary.star_mul_self_of_mem hu⟩

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] in
theorem exp_skew_unitary {X : 𝔸} (hX : star X = -X) : exp X ∈ unitary 𝔸 := by
  rw [Unitary.mem_iff, star_exp, hX]
  exact ⟨exp_neg_mul_exp X, exp_mul_exp_neg X⟩

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] in
theorem star_mul_cancel_left' {u : 𝔸} (hu : u ∈ unitary 𝔸) (X : 𝔸) : star u * (u * X) = X := by
  rw [← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]

omit [FiniteDimensional ℝ 𝔸] in
theorem linkP_unitary {h s : ℝ} {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (μ : ι) (x : ι → ZMod n) :
    linkP h B s q μ x ∈ unitary 𝔸 := by
  have he : exp (s • (h • B μ x)) ∈ unitary 𝔸 :=
    exp_skew_unitary (by rw [star_smul, star_smul, hB, star_trivial, star_trivial, smul_neg,
      smul_neg])
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hq x) he) (Unitary.star_mem (hq _))

omit [FiniteDimensional ℝ 𝔸] in
theorem logChart_skew' {P : 𝔸} (hP : P ∈ unitary 𝔸) (h1 : ‖P - 1‖ < 1)
    (hL : ‖logChart P‖ ≤ 1 / 32) : star (logChart P) = -logChart P := by
  have hstar : ‖star P - 1‖ < 1 := by
    rw [show star P - 1 = star (P - 1) by rw [star_sub, star_one], norm_star]; exact h1
  have e1 : star P = exp (-logChart P) := by
    have hm : exp (-logChart P) * P = 1 := by
      have := exp_neg_mul_exp (logChart P)
      rwa [exp_logChart h1] at this
    calc star P = exp (-logChart P) * P * star P := by rw [hm, one_mul]
      _ = exp (-logChart P) := by rw [mul_assoc, Unitary.mul_star_self_of_mem hP, mul_one]
  have := logChart_star h1 hstar
  rw [e1, logChart_exp (by rwa [norm_neg])] at this
  exact this.symm

omit [FiniteDimensional ℝ 𝔸] in
theorem linkA_skew {h s : ℝ} {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B)
    (μ : ι) (x : ι → ZMod n) : star (linkA h B s q μ x) = -linkA h B s q μ x := by
  have := logChart_skew' (linkP_unitary hB hq μ x) (hp.1 μ x) ((hp.2.1 μ x).le.trans (by norm_num))
  simp only [linkA, star_smul, star_trivial, this, smul_neg]

theorem linkR_skew {h s : ℝ} (hh : h ≠ 0) {B : ι → (ι → ZMod n) → 𝔸}
    (hB : ∀ μ x, star (B μ x) = -B μ x) {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸)
    (hp : (s, q) ∈ domO toE h B) (μ : ι) (x : ι → ZMod n) :
    star (linkR h B s q μ x) = -linkR h B s q μ x := by
  have hA := linkA_skew toE hB hq hp μ x
  have hsm : ‖h • linkA h B s q μ x‖ ≤ 1 / 8 := by
    rw [h_smul_linkA hh]; exact (hp.2.1 μ x).le.trans (by norm_num)
  refine ringInverse_dexpJ_skew hA hsm ?_
  rw [star_mul, star_mul, star_star, hB]
  noncomm_ring

/-! ### The transverse solution along unitary gauges -/

omit [Nontrivial E] [FiniteDimensional ℝ E] [LinearOrder ι] in
theorem codiff_sub (h : ℝ) (f g : ι → (ι → ZMod n) → E) :
    periodicHodgeCodiff h gridStep (fun μ y => f μ y - g μ y) =
      periodicHodgeCodiff h gridStep f - periodicHodgeCodiff h gridStep g := by
  funext x
  simp only [periodicHodgeCodiff, periodicHodgeBwd, Pi.sub_apply, smul_sub, sum_sub_distrib]
  abel

theorem solveFP_spec (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (B : ι → (ι → ZMod n) → 𝔸) {s : ℝ} {q : (ι → ZMod n) → 𝔸} (hp : (s, q) ∈ domO toE h B) :
    ∑ x, solveFP toE h B s q x = 0 ∧
      FaddeevPopov.fpOp (brE toE) h (fun μ y => toE (linkA h B s q μ y)) (solveFP toE h B s q) =
        periodicHodgeCodiff h gridStep (fun μ y => toE (linkR h B s q μ y)) :=
  (FaddeevPopov.fp_inverse_contDiffOn (k := 1) (n := n) hι (brE toE) hh).2 _ hp.2.2 _
    (FaddeevPopov.sum_codiff h _)

theorem toE_genXi (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸}
    (hB : ∀ μ x, star (B μ x) = -B μ x) {s : ℝ} {q : (ι → ZMod n) → 𝔸}
    (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B) (y : ι → ZMod n) :
    toE (genXi toE h B s q y) = solveFP toE h B s q y := by
  obtain ⟨h1, h2⟩ := solveFP_spec toE hι hh B hp
  have hskew := fp_solution_skew toE hι hh (linkA h B s q) (linkR h B s q)
    (linkA_skew toE hB hq hp) (linkR_skew toE hh.ne' hB hq hp) hp.2.2 _ h1 h2 y
  rw [genXi, skewPart_of_skew hskew, ContinuousLinearEquiv.apply_symm_apply]

/-- At a unitary point of the domain, the derivative `Ȧ = R - (𝒦 D^+ξ + [A, mξ])` of the homotopy
is divergence free: `δ_h Ȧ = δ_h R - M_A ξ = 0`. -/
theorem codiff_derivative_eq_zero (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x) {s : ℝ}
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B) :
    periodicHodgeCodiff h gridStep (fun μ y => toE (linkR h B s q μ y -
      gaugeFlux h (linkA h B s q) (genXi toE h B s q) μ y)) = 0 := by
  have hflux : ∀ μ y, toE (gaugeFlux h (linkA h B s q) (genXi toE h B s q) μ y) =
      FaddeevPopov.fpFlux (brE toE) h (fun ν z => toE (linkA h B s q ν z))
        (solveFP toE h B s q) μ y := by
    intro μ y
    rw [toE_gaugeFlux toE (linkA h B s q) _ μ y
      (by rw [h_smul_linkA hh.ne']; exact (hp.2.1 μ y).le.trans (by norm_num))]
    congr 1
    funext z
    exact toE_genXi toE hι hh hB hq hp z
  have e : (fun μ y => toE (linkR h B s q μ y -
      gaugeFlux h (linkA h B s q) (genXi toE h B s q) μ y)) =
      fun μ y => toE (linkR h B s q μ y) - FaddeevPopov.fpFlux (brE toE) h
        (fun ν z => toE (linkA h B s q ν z)) (solveFP toE h B s q) μ y := by
    funext μ y; rw [map_sub, hflux]
  rw [e]
  have h2 := (solveFP_spec toE hι hh B hp).2
  unfold FaddeevPopov.fpOp at h2
  funext x
  have hsub := codiff_sub (n := n) h (fun μ y => toE (linkR h B s q μ y))
    (FaddeevPopov.fpFlux (brE toE) h (fun ν z => toE (linkA h B s q ν z)) (solveFP toE h B s q))
  have hsub' := congrFun hsub x
  simp only [Pi.sub_apply] at hsub'
  rw [hsub', h2, sub_self]; rfl

/-! ### Along a solution of the homotopy ODE: unitarity and the Coulomb condition -/

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [LinearOrder ι] [NeZero n] in
theorem hasDerivWithinAt_Ici_of_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → F} {f' : F} {T t : ℝ} (hd : HasDerivWithinAt γ f' (Icc 0 T) t)
    (ht : t ∈ Ico 0 T) : HasDerivWithinAt γ f' (Ici t) t :=
  hd.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl))

/-- **The gauges stay unitary** along any solution starting at `q ≡ 1`. -/
theorem unitary_of_solution {h : ℝ} (B : ι → (ι → ZMod n) → 𝔸) {T : ℝ}
    {γ : ℝ → (ι → ZMod n) → 𝔸} (hγ0 : γ 0 = fun _ => 1)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ y, γ t y ∈ unitary 𝔸 := by
  intro t ht y
  have hcont : ContinuousOn γ (Icc 0 T) := fun s hs => (hd s hs).continuousWithinAt
  have hy : ContinuousOn (fun s => γ s y) (Icc 0 T) := (continuous_apply y).comp_continuousOn hcont
  set f : ℝ → 𝔸 := fun s => star (γ s y) * γ s y with hf
  have hfc : ContinuousOn f (Icc 0 T) := (continuous_star.comp_continuousOn hy).mul hy
  have hder : ∀ s ∈ Ico 0 T, HasDerivWithinAt f 0 (Ici s) s := by
    intro s hs
    have h1 := hasDerivWithinAt_pi.1 (hasDerivWithinAt_Ici_of_Icc (hd s (Ico_subset_Icc_self hs))
      hs) y
    have h2 := h1.star.mul h1
    have hξ : star (genXi toE h B s (γ s) y) = -genXi toE h B s (γ s) y := star_skewPart _
    refine h2.congr_deriv ?_
    change star (genXi toE h B s (γ s) y * γ s y) * γ s y +
      star (γ s y) * (genXi toE h B s (γ s) y * γ s y) = 0
    rw [star_mul, hξ]
    noncomm_ring
  have hc := constant_of_has_deriv_right_zero hfc hder t ht
  have h0 : f 0 = 1 := by simp [hf, hγ0]
  rw [h0] at hc
  exact Unitary.mem_iff.2 ⟨hc, mul_star_of_star_mul hc⟩

/-- The exact chain rule along a solution: `Ȧ_s = R_s - (𝒦 D^+ξ_s + [A_s, m ξ_s])`. -/
theorem hasDerivWithinAt_linkA_of_solution {h : ℝ} (hh : h ≠ 0) (B : ι → (ι → ZMod n) → 𝔸)
    {T : ℝ} {γ : ℝ → (ι → ZMod n) → 𝔸} (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t)
    (hu : ∀ t ∈ Icc 0 T, ∀ y, γ t y ∈ unitary 𝔸) {t : ℝ} (ht : t ∈ Ico 0 T) (μ : ι)
    (x : ι → ZMod n) :
    HasDerivWithinAt (fun s => linkA h B s (γ s) μ x)
      (linkR h B t (γ t) μ x - gaugeFlux h (linkA h B t (γ t)) (genXi toE h B t (γ t)) μ x)
      (Ici t) t := by
  have ht' := Ico_subset_Icc_self ht
  have hp := hO t ht'
  have hq : ∀ y, HasDerivWithinAt (fun s => γ s y) (genXi toE h B t (γ t) y * γ t y) (Ici t) t :=
    fun y => hasDerivWithinAt_pi.1 (hasDerivWithinAt_Ici_of_Icc (hd t ht') ht) y
  have hA : γ t x * exp (t • (h • B μ x)) * star (γ t (x + gridStep μ)) =
      exp (h • linkA h B t (γ t) μ x) := by
    rw [h_smul_linkA hh, exp_logChart (hp.1 μ x)]; rfl
  have hLog : ∀ᶠ Y in 𝓝 (h • linkA h B t (γ t) μ x), logChart (exp Y) = Y :=
    eventually_logChart_exp (by rw [h_smul_linkA hh]; exact (hp.2.1 μ x).trans (by norm_num))
  have hJ := isUnit_dexpJ_linkA hh B t (γ t) μ x ((hp.2.1 μ x).le.trans (by norm_num))
  exact homotopy_derivative_star logChart hh B γ (genXi toE h B t (γ t)) t (linkA h B t (γ t)) μ x
    hq (fun y => star_skewPart _) (hu t ht') hA hLog hJ

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E]
  [FiniteDimensional ℝ E] [LinearOrder ι] in
theorem hasDerivWithinAt_codiff (h : ℝ) {S : Set ℝ} {t : ℝ} {a : ℝ → ι → (ι → ZMod n) → E}
    {a' : ι → (ι → ZMod n) → E} (ha : ∀ μ y, HasDerivWithinAt (fun s => a s μ y) (a' μ y) S t) :
    HasDerivWithinAt (fun s => periodicHodgeCodiff h gridStep (a s))
      (periodicHodgeCodiff h gridStep a') S t := by
  refine hasDerivWithinAt_pi.2 fun x => ?_
  simp only [periodicHodgeCodiff, periodicHodgeBwd]
  exact (HasDerivWithinAt.fun_sum fun μ _ => ((ha μ x).sub (ha μ _)).const_smul h⁻¹).neg

theorem continuousOn_linkA_sol {h : ℝ} (B : ι → (ι → ZMod n) → 𝔸) {T : ℝ}
    {γ : ℝ → (ι → ZMod n) → 𝔸} (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) (μ : ι)
    (x : ι → ZMod n) : ContinuousOn (fun s => linkA h B s (γ s) μ x) (Icc 0 T) := by
  intro s hs
  have hγc : ContinuousWithinAt (fun s => ((s, γ s) : ℝ × ((ι → ZMod n) → 𝔸))) (Icc 0 T) s :=
    continuousWithinAt_id.prodMk (hd s hs).continuousWithinAt
  have hA := (contDiffAt_linkA (k := 0) h B μ x ((hO s hs).1 μ x)).continuousAt
  exact ContinuousAt.comp_continuousWithinAt (g := fun p : ℝ × ((ι → ZMod n) → 𝔸) =>
    linkA h B p.1 p.2 μ x) (f := fun s => ((s, γ s) : ℝ × ((ι → ZMod n) → 𝔸))) hA hγc

theorem linkA_one (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (μ : ι) (x : ι → ZMod n) :
    linkA h B 0 (fun _ => (1 : 𝔸)) μ x = 0 := by
  simp [linkA, linkP, logChart_one]

/-- **The Coulomb condition is preserved**: `δ_h A_s = 0` along any solution. -/
theorem coulomb_of_solution (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x) {T : ℝ}
    {γ : ℝ → (ι → ZMod n) → 𝔸} (hγ0 : γ 0 = fun _ => 1)
    (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, periodicHodgeCodiff h gridStep (fun μ y => toE (linkA h B t (γ t) μ y)) = 0 := by
  have hu := unitary_of_solution toE B hγ0 hd
  set c : ℝ → (ι → ZMod n) → E :=
    fun s => periodicHodgeCodiff h gridStep (fun μ y => toE (linkA h B s (γ s) μ y)) with hc
  have hcont : ContinuousOn c (Icc 0 T) := by
    refine continuousOn_pi.2 fun x => ?_
    simp only [hc, periodicHodgeCodiff, periodicHodgeBwd]
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun μ _ => ContinuousOn.const_smul
      (ContinuousOn.sub ?_ ?_) _)
    · exact toE.continuous.comp_continuousOn (continuousOn_linkA_sol toE B hO hd μ x)
    · exact toE.continuous.comp_continuousOn (continuousOn_linkA_sol toE B hO hd μ _)
  have hder : ∀ s ∈ Ico 0 T, HasDerivWithinAt c 0 (Ici s) s := by
    intro s hs
    have h1 := hasDerivWithinAt_codiff (n := n) h (S := Ici s) (t := s)
      (a := fun s μ y => toE (linkA h B s (γ s) μ y))
      (a' := fun μ y => toE (linkR h B s (γ s) μ y -
        gaugeFlux h (linkA h B s (γ s)) (genXi toE h B s (γ s)) μ y))
      fun μ y => (toE : 𝔸 →L[ℝ] E).hasFDerivAt.comp_hasDerivWithinAt s
        (hasDerivWithinAt_linkA_of_solution toE hh.ne' B hO hd hu hs μ y)
    rwa [codiff_derivative_eq_zero toE hι hh hB (hu s (Ico_subset_Icc_self hs))
      (hO s (Ico_subset_Icc_self hs))] at h1
  intro t ht
  have := constant_of_has_deriv_right_zero hcont hder t ht
  change c t = 0
  rw [this]
  simp only [hc, hγ0, linkA_one, map_zero]
  funext x
  simp [periodicHodgeCodiff, periodicHodgeBwd]

/-! ### The physical `L²_h` estimate `‖A_s‖_{2,h} ≤ s ‖B‖_{2,h}` -/

/-- The bilinear form `⟨X, Y⟩ = ⟪toE X, toE Y⟫` on `𝔸`. -/
def bf : 𝔸 →L[ℝ] 𝔸 →L[ℝ] ℝ :=
  (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (toE : 𝔸 →L[ℝ] E) (toE : 𝔸 →L[ℝ] E)

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E] in
theorem bf_apply (X Y : 𝔸) : bf toE X Y = inner ℝ (toE X) (toE Y) := by simp [bf]

/-- The adjoint of `𝒥(h ad_a)⁻¹` fixes `a` (`a` skew-adjoint, invariant metric). -/
theorem inner_ringInverse_dexpJ (hM2 : ∀ a : 𝔸, star a = -a → ∀ u,
      inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ} {a : 𝔸} (ha : star a = -a)
    (hJ : IsUnit (dexpJ (h • adOp a))) (w : 𝔸) :
    inner ℝ (toE a) (toE (Ring.inverse (dexpJ (h • adOp a)) w)) = inner ℝ (toE a) (toE w) := by
  have hZ : ∀ u, bf toE a ((h • adOp a) u) = 0 := by
    intro u
    rw [ContinuousLinearMap.smul_apply, map_smul, bf_apply, adOp_apply, hM2 a ha u, smul_zero]
  have h1 := (LogGaugeDifferential.pairing_series_eq (bf toE) a (h • adOp a) hZ
    (Ring.inverse (dexpJ (h • adOp a)) w)).1
  have h2 : dexpJ (h • adOp a) (Ring.inverse (dexpJ (h • adOp a)) w) = w := by
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hJ]; rfl
  rw [h2, bf_apply, bf_apply] at h1
  exact h1.symm

/-- The gauge flux pairs with `A` like `D^+ξ` (`𝒦(h ad_A)^* A = A`, `⟨A, [A, ·]⟩ = 0`). -/
theorem inner_gaugeFlux (hM2 : ∀ a : 𝔸, star a = -a → ∀ u,
      inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ} (A : ι → (ι → ZMod n) → 𝔸)
    (ξ : (ι → ZMod n) → 𝔸) (μ : ι) (y : ι → ZMod n) (ha : star (A μ y) = -A μ y)
    (hJ : IsUnit (dexpJ (h • adOp (A μ y)))) :
    inner ℝ (toE (A μ y)) (toE (gaugeFlux h A ξ μ y)) =
      inner ℝ (toE (A μ y)) (toE (gridFwd h μ ξ y)) := by
  have hB' : ∀ u, bf toE (A μ y) (A μ y * u - u * A μ y) = 0 := fun u => by
    rw [bf_apply]; exact hM2 _ ha u
  have h1 := LogGaugeDifferential.pairing_halfCoth (bf toE) h (A μ y) hB' hJ (gridFwd h μ ξ y)
  rw [gaugeFlux, map_add, inner_add_right, ← bf_apply, h1, bf_apply, adOp_apply,
    hM2 _ ha, add_zero]

/-- **Pairing of the homotopy derivative with `A`**: at a unitary point of the domain where
`δ_h A = 0`, `Σ ⟨A, Ȧ⟩ = Σ ⟨A, Ad_q B⟩ ≤ (Σ‖A‖²)^{1/2} (Σ‖B‖²)^{1/2}` (the gauge tangent
contributes `-⟨δ_h A, ξ⟩ = 0`). -/
theorem sum_inner_derivative_le (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ}
    (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x) {s : ℝ}
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B)
    (hcod : periodicHodgeCodiff h gridStep (fun μ y => toE (linkA h B s q μ y)) = 0) :
    ∑ μ, ∑ y, inner ℝ (toE (linkA h B s q μ y)) (toE (linkR h B s q μ y -
        gaugeFlux h (linkA h B s q) (genXi toE h B s q) μ y)) ≤
      √(∑ μ, ∑ y, ‖toE (linkA h B s q μ y)‖ ^ 2) * √(∑ μ, ∑ y, ‖toE (B μ y)‖ ^ 2) := by
  set A := linkA h B s q
  set ξ := genXi toE h B s q
  have hA : ∀ μ y, star (A μ y) = -A μ y := linkA_skew toE hB hq hp
  have hJ : ∀ μ y, IsUnit (dexpJ (h • adOp (A μ y))) := fun μ y =>
    isUnit_dexpJ_linkA hh.ne' B s q μ y ((hp.2.1 μ y).le.trans (by norm_num))
  -- the gauge tangent contributes nothing
  have hflux : ∑ μ, ∑ y, inner ℝ (toE (A μ y)) (toE (gaugeFlux h A ξ μ y)) = 0 := by
    have e1 : ∀ μ y, inner ℝ (toE (A μ y)) (toE (gaugeFlux h A ξ μ y)) =
        inner ℝ (toE (A μ y)) (gridFwd h μ (fun z => toE (ξ z)) y) := by
      intro μ y
      rw [inner_gaugeFlux toE hM2 A ξ μ y (hA μ y) (hJ μ y), toE_gridFwd]
    simp only [e1]
    rw [← FaddeevPopov.sum_inner_codiff h (fun μ y => toE (A μ y)) (fun z => toE (ξ z))]
    have : periodicHodgeCodiff h gridStep (fun μ y => toE (A μ y)) = 0 := hcod
    simp [this]
  -- the `R` part
  have hR : ∀ μ y, inner ℝ (toE (A μ y)) (toE (linkR h B s q μ y)) ≤
      ‖toE (A μ y)‖ * ‖toE (B μ y)‖ := by
    intro μ y
    rw [linkR, inner_ringInverse_dexpJ toE hM2 (hA μ y) (hJ μ y)]
    refine (real_inner_le_norm _ _).trans (le_of_eq ?_)
    rw [hM1 _ (hq y)]
  have hsplit : ∑ μ, ∑ y, inner ℝ (toE (A μ y)) (toE (linkR h B s q μ y - gaugeFlux h A ξ μ y)) =
      ∑ μ, ∑ y, inner ℝ (toE (A μ y)) (toE (linkR h B s q μ y)) -
        ∑ μ, ∑ y, inner ℝ (toE (A μ y)) (toE (gaugeFlux h A ξ μ y)) := by
    simp only [map_sub, inner_sub_right, sum_sub_distrib]
  rw [hsplit, hflux, sub_zero]
  calc ∑ μ, ∑ y, inner ℝ (toE (A μ y)) (toE (linkR h B s q μ y))
      ≤ ∑ μ, ∑ y, ‖toE (A μ y)‖ * ‖toE (B μ y)‖ := sum_le_sum fun μ _ => sum_le_sum fun y _ => hR μ y
    _ ≤ _ := by
        have := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (ι × (ι → ZMod n)))
          (fun p => ‖toE (A p.1 p.2)‖) (fun p => ‖toE (B p.1 p.2)‖)
        simp only [← Finset.univ_product_univ, Finset.sum_product] at this
        exact this

theorem oneL2_sq_eq (h : ℝ) (A : ι → (ι → ZMod n) → 𝔸) :
    (∑ μ, periodicHodgeNormSq ι h (bar (toE : 𝔸 →L[ℝ] E) A μ)) =
      h ^ Fintype.card ι * ∑ μ, ∑ y, ‖toE (A μ y)‖ ^ 2 := by
  simp only [periodicHodgeNormSq, bar, mul_sum]
  rfl

/-- **The physical `L²_h` estimate** (`‖A_s‖_{2,h} ≤ s ‖B‖_{2,h}`) along any solution. -/
theorem oneL2_le_of_solution (hι : Fintype.card ι = 4)
    (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ}
    (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x) {T : ℝ}
    {γ : ℝ → (ι → ZMod n) → 𝔸} (hγ0 : γ 0 = fun _ => 1)
    (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) ≤
      t * oneL2 h (toE : 𝔸 →L[ℝ] E) B := by
  have hu := unitary_of_solution toE B hγ0 hd
  have hcod := coulomb_of_solution toE hι hh hB hγ0 hO hd
  set w : ℝ := h ^ Fintype.card ι with hw
  have hw0 : 0 ≤ w := by positivity
  set e : ℝ → ℝ := fun s => w * ∑ μ, ∑ y, ‖toE (linkA h B s (γ s) μ y)‖ ^ 2 with he
  set Y : ℝ := ∑ μ, ∑ y, ‖toE (B μ y)‖ ^ 2 with hY
  have hY0 : 0 ≤ Y := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  set β : ℝ := √w * √Y with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβeq : oneL2 h (toE : 𝔸 →L[ℝ] E) B = β := by
    rw [oneL2, oneL2_sq_eq, Real.sqrt_mul hw0]
  have hAeq : ∀ s, oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B s (γ s)) = √(e s) := by
    intro s; rw [oneL2, oneL2_sq_eq]
  have he0 : ∀ s, 0 ≤ e s := fun s => by
    simp only [he]; exact mul_nonneg hw0 (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
  -- derivative of the energy
  set e' : ℝ → ℝ := fun s => w * ∑ μ, ∑ y, 2 * inner ℝ (toE (linkA h B s (γ s) μ y))
    (toE (linkR h B s (γ s) μ y - gaugeFlux h (linkA h B s (γ s)) (genXi toE h B s (γ s)) μ y))
    with he'
  have hder : ∀ s ∈ Ico 0 T, HasDerivWithinAt e (e' s) (Ici s) s := by
    intro s hs
    refine HasDerivWithinAt.const_mul w (HasDerivWithinAt.fun_sum fun μ _ =>
      HasDerivWithinAt.fun_sum fun y _ => ?_)
    exact ((toE : 𝔸 →L[ℝ] E).hasFDerivAt.comp_hasDerivWithinAt s
      (hasDerivWithinAt_linkA_of_solution toE hh.ne' B hO hd hu hs μ y)).norm_sq
  have hbound : ∀ s ∈ Ico 0 T, e' s ≤ 2 * √(e s) * β := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have h1 := sum_inner_derivative_le toE hM1 hM2 hh hB (hu s hs') (hO s hs') (hcod s hs')
    have e1 : e' s = 2 * w * ∑ μ, ∑ y, inner ℝ (toE (linkA h B s (γ s) μ y))
        (toE (linkR h B s (γ s) μ y - gaugeFlux h (linkA h B s (γ s))
          (genXi toE h B s (γ s)) μ y)) := by
      simp only [he', mul_sum]; ring_nf
    have e2 : √(e s) = √w * √(∑ μ, ∑ y, ‖toE (linkA h B s (γ s) μ y)‖ ^ 2) := by
      simp only [he]; rw [Real.sqrt_mul hw0]
    rw [e1, e2, hβ]
    have hw' : √w * √w = w := Real.mul_self_sqrt hw0
    calc 2 * w * _ ≤ 2 * w * (√(∑ μ, ∑ y, ‖toE (linkA h B s (γ s) μ y)‖ ^ 2) * √Y) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by
          rw [show 2 * (√w * √(∑ μ, ∑ y, ‖toE (linkA h B s (γ s) μ y)‖ ^ 2)) * (√w * √Y) =
            2 * (√w * √w) * (√(∑ μ, ∑ y, ‖toE (linkA h B s (γ s) μ y)‖ ^ 2) * √Y) by ring, hw']
  -- continuity
  have hcont : ContinuousOn e (Icc 0 T) := by
    simp only [he]
    refine continuousOn_const.mul (continuousOn_finsetSum _ fun μ _ =>
      continuousOn_finsetSum _ fun y _ => ?_)
    exact ((toE.continuous.comp_continuousOn (continuousOn_linkA_sol toE B hO hd μ y)).norm).pow 2
  have he_zero : e 0 = 0 := by simp [he, hγ0, linkA_one]
  intro t ht
  rw [hAeq, hβeq]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set F : ℝ → ℝ := fun s => √(e s + ε ^ 2) with hF
  have hpos : ∀ s, 0 < e s + ε ^ 2 := fun s => by have := he0 s; positivity
  have hFd : ∀ s ∈ Ico 0 T, HasDerivWithinAt F (e' s / (2 * √(e s + ε ^ 2))) (Ici s) s :=
    fun s hs => ((hder s hs).add_const (ε ^ 2)).sqrt (hpos s).ne'
  have hFc : ContinuousOn F (Icc 0 T) :=
    (hcont.add continuousOn_const).sqrt
  have hFb : ∀ s ∈ Ico 0 T, e' s / (2 * √(e s + ε ^ 2)) ≤ β := by
    intro s hs
    have hsq : 0 < √(e s + ε ^ 2) := Real.sqrt_pos.2 (hpos s)
    rw [div_le_iff₀ (by positivity)]
    have h1 : √(e s) ≤ √(e s + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    calc e' s ≤ 2 * √(e s) * β := hbound s hs
      _ ≤ 2 * √(e s + ε ^ 2) * β := by gcongr
      _ = β * (2 * √(e s + ε ^ 2)) := by ring
  have hmain := image_le_of_deriv_right_le_deriv_boundary hFc hFd
    (B := fun s => ε + s * β) (B' := fun _ => β)
    (by simp only [hF, he_zero, zero_add, zero_mul, add_zero]; rw [Real.sqrt_sq hε.le])
    (by fun_prop)
    (fun s _ => by
      have := ((hasDerivAt_id s).mul_const β).const_add ε
      simpa using this.hasDerivWithinAt)
    hFb ht
  have h1 : √(e t) ≤ F t := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have := h1.trans hmain
  linarith

/-! ### The curvature along the homotopy -/

/-- **Conjugation covariance of the plaquette logarithm**: `F_h(A_s) = Ad_{q_x} F_h(sB)`. -/
theorem curvature_linkA {h : ℝ} (hh : h ≠ 0) {B : ι → (ι → ZMod n) → 𝔸} {s : ℝ}
    {q : (ι → ZMod n) → 𝔸} (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B)
    (hpl : ∀ μ ν x, ‖plaquette h (fun μ y => s • B μ y) μ ν x - 1‖ < 1) (μ ν : ι)
    (x : ι → ZMod n) :
    curvature h (linkA h B s q) μ ν x =
      q x * curvature h (fun μ y => s • B μ y) μ ν x * star (q x) := by
  have e1 : ∀ μ y, exp (h • linkA h B s q μ y) =
      q y * exp (s • (h • B μ y)) * star (q (y + gridStep μ)) := by
    intro μ y; rw [h_smul_linkA hh, exp_logChart (hp.1 μ y)]; rfl
  have e2 : ∀ μ y, exp (-(h • linkA h B s q μ y)) =
      q (y + gridStep μ) * exp (-(s • (h • B μ y))) * star (q y) := by
    intro μ y
    set Q := q (y + gridStep μ) * exp (-(s • (h • B μ y))) * star (q y)
    have hP : exp (h • linkA h B s q μ y) * Q = 1 := by
      rw [e1]
      simp only [Q, mul_assoc]
      rw [star_mul_cancel_left' (hq _), ← mul_assoc (exp (s • (h • B μ y))),
        exp_mul_exp_neg, one_mul, Unitary.mul_star_self_of_mem (hq y)]
    calc exp (-(h • linkA h B s q μ y))
        = exp (-(h • linkA h B s q μ y)) * (exp (h • linkA h B s q μ y) * Q) := by rw [hP, mul_one]
      _ = Q := by rw [← mul_assoc, exp_neg_mul_exp, one_mul]
  set M := plaquette h (fun μ y => s • B μ y) μ ν x
  have hplaq : plaquette h (linkA h B s q) μ ν x = q x * M * star (q x) := by
    simp only [plaquette, M]
    rw [e1, e1, e2, e2, add_right_comm x (gridStep ν) (gridStep μ)]
    simp only [mul_assoc, smul_comm h s]
    rw [star_mul_cancel_left' (hq _), star_mul_cancel_left' (hq _), star_mul_cancel_left' (hq _)]
  have hM : ‖M - 1‖ < 1 := hpl μ ν x
  have hM' : ‖((unitUnit (hq x) : 𝔸ˣ) : 𝔸) * (M - 1) * ↑(unitUnit (hq x))⁻¹‖ < 1 := by
    change ‖q x * (M - 1) * star (q x)‖ < 1
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (hq x)),
      CStarRing.norm_mem_unitary_mul _ (hq x)]
    exact hM
  have hlog := logChart_conj (unitUnit (hq x)) hM hM'
  change logChart (q x * M * star (q x)) = q x * logChart M * star (q x) at hlog
  rw [curvature, hplaq, hlog, curvature, mul_smul_comm, smul_mul_assoc]

/-! ### Norm bookkeeping -/

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E]
  [LinearOrder ι] in
theorem gridL2Norm_add_le' {h : ℝ} (hh : 0 < h) (f g : (ι → ZMod n) → E) :
    gridL2Norm h (f + g) ≤ gridL2Norm h f + gridL2Norm h g := by
  have := gridL2Norm_sub_le hh f (-g)
  have hn : gridL2Norm h (-g) = gridL2Norm h g := by
    simp [gridL2Norm, periodicHodgeNormSq]
  rwa [sub_neg_eq_add, hn] at this

theorem gridL2Norm_smul' (h c : ℝ) (f : (ι → ZMod n) → E) :
    gridL2Norm h (c • f) = |c| * gridL2Norm h f := by
  simp only [gridL2Norm, periodicHodgeNormSq, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, ← mul_sum]
  rw [mul_left_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E]
  [LinearOrder ι] in
theorem gridL4Norm_smul' {h : ℝ} (hh : 0 ≤ h) (c : ℝ) (f : (ι → ZMod n) → E) :
    gridL4Norm h (c • f) = |c| * gridL4Norm h f := by
  have h1 := gridL4Norm_pow_four hh (c • f)
  have h2 := gridL4Norm_pow_four hh f
  have e : gridL4Norm h (c • f) ^ 4 = (|c| * gridL4Norm h f) ^ 4 := by
    rw [h1, mul_pow, h2]
    simp only [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, ← mul_sum]
    rw [show |c| ^ 4 = c ^ 4 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]]
    ring
  exact (pow_left_inj₀ (gridL4Norm_nonneg hh _) (mul_nonneg (abs_nonneg c)
    (gridL4Norm_nonneg hh _)) four_ne_zero).1 e

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E]
  [LinearOrder ι] in
/-- Hölder on the fixed-volume box: `‖u‖_{2,h} ≤ L ‖u‖_{4,h}`, `L = n h`, in four dimensions. -/
theorem gridL2Norm_le_L_mul_gridL4Norm (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (u : (ι → ZMod n) → E) : gridL2Norm h u ≤ (n * h) * gridL4Norm h u := by
  have hcard : (Fintype.card (ι → ZMod n) : ℝ) = (n : ℝ) ^ 4 := by
    rw [Fintype.card_fun, ZMod.card, hι]; push_cast; ring
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) (fun x => ‖u x‖ ^ 2)
  simp only [one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at hcs
  rw [hcard] at hcs
  have hL4 := gridL4Norm_pow_four hh.le u
  rw [hι] at hL4
  have h0 : 0 ≤ (n * h) * gridL4Norm h u := mul_nonneg (by positivity) (gridL4Norm_nonneg hh.le _)
  rw [gridL2Norm, periodicHodgeNormSq, hι, Real.sqrt_le_left h0]
  have hsq : (h ^ 4 * ∑ x, ‖u x‖ ^ 2) ^ 2 ≤ ((n * h) * gridL4Norm h u) ^ 2 ^ 2 := by
    have e1 : ((n * h) * gridL4Norm h u) ^ 2 ^ 2 = (n * h) ^ 4 * (h ^ 4 * ∑ x, ‖u x‖ ^ 4) := by
      rw [← hL4]; ring
    rw [e1]
    have e2 : (h ^ 4 * ∑ x, ‖u x‖ ^ 2) ^ 2 = h ^ 8 * (∑ x, ‖u x‖ ^ 2) ^ 2 := by ring
    rw [e2]
    have e3 : ∀ x, (‖u x‖ ^ 2) ^ 2 = ‖u x‖ ^ 4 := fun x => by ring
    simp only [e3] at hcs
    calc h ^ 8 * (∑ x, ‖u x‖ ^ 2) ^ 2 ≤ h ^ 8 * ((n : ℝ) ^ 4 * ∑ x, ‖u x‖ ^ 4) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (n * h) ^ 4 * (h ^ 4 * ∑ x, ‖u x‖ ^ 4) := by ring
  have hpos : 0 ≤ h ^ 4 * ∑ x, ‖u x‖ ^ 2 := by positivity
  have e4 : ((n * h) * gridL4Norm h u) ^ 2 ^ 2 = (((n * h) * gridL4Norm h u) ^ 2) ^ 2 := by ring
  rw [e4] at hsq
  exact (pow_le_pow_iff_left₀ hpos (sq_nonneg _) two_ne_zero).1 hsq

/-- `‖A‖_{2,h} ≤ L ‖A‖_{4,h}` for one-forms. -/
theorem oneL2_le (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) (T : 𝔸 →L[ℝ] E)
    (A : ι → (ι → ZMod n) → 𝔸) : oneL2 h T A ≤ (n * h) * oneL4 h T A := by
  unfold oneL2 oneL4
  have h1 : √(∑ μ, periodicHodgeNormSq ι h (bar T A μ)) ≤ ∑ μ, gridL2Norm h (bar T A μ) := by
    have := sqrt_sum_sq_le_sum univ (fun μ => gridL2Norm h (bar T A μ))
      (fun _ _ => gridL2Norm_nonneg _ _)
    simpa only [gridL2Norm_sq' hh.le] using this
  refine h1.trans ?_
  rw [mul_sum]
  exact sum_le_sum fun μ _ => gridL2Norm_le_L_mul_gridL4Norm hι hh _

/-- **Curvature of the rescaled seed**: `‖𝔽_h(sB)‖ ≤ ‖𝔽_h(B)‖ + 2·192 K ‖B‖²_{4,h}` for
`0 ≤ s ≤ 1` (exact split `F_h(sB) = sF_h(B) - s𝒩_h(B) + 𝒩_h(sB)`). -/
theorem curvL2_smul_le (hι : Fintype.card ι = 4) (T : 𝔸 →L[ℝ] E) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ X, ‖X‖ ≤ c * ‖T X‖) {h : ℝ} (hh : 0 < h) (B : ι → (ι → ZMod n) → 𝔸)
    (hs : ∀ μ ν x, h * slotNorm B μ ν x ≤ 1 / 8) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    curvL2 h T (fun μ y => s • B μ y) ≤
      curvL2 h T B + 2 * (192 * (21 * ‖T‖ * c ^ 2) * oneL4 h T B ^ 2) := by
  set sB : ι → (ι → ZMod n) → 𝔸 := fun μ y => s • B μ y with hsB
  have hslot : ∀ μ ν x, h * slotNorm sB μ ν x ≤ 1 / 8 := by
    intro μ ν x
    have : slotNorm sB μ ν x = s * slotNorm B μ ν x := by
      simp only [slotNorm, hsB, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]; ring
    rw [this]
    have h0 : 0 ≤ slotNorm B μ ν x := by unfold slotNorm; positivity
    nlinarith [hs μ ν x]
  have hL4s : oneL4 h T sB = s * oneL4 h T B := by
    unfold oneL4
    rw [mul_sum]
    refine sum_congr rfl fun μ _ => ?_
    have : bar T sB μ = s • bar T B μ := by funext y; simp [bar, hsB, map_smul]
    rw [this, gridL4Norm_smul' hh.le, abs_of_nonneg hs0]
  have hL4B := oneL4_nonneg hh.le T B
  have hNB := sum_pairs_curvRem_le hι T hc0 hc hh B hs
  have hNsB := sum_pairs_curvRem_le hι T hc0 hc hh sB hslot
  set K := 21 * ‖T‖ * c ^ 2
  have hK : 0 ≤ K := by positivity
  -- pointwise identity of the split
  have hsplit : ∀ μ ν, (fun x => T (curvature h sB μ ν x)) =
      s • (fun x => T (curvature h B μ ν x)) + ((-s) • (fun x => T (curvRem h B μ ν x)) +
        (fun x => T (curvRem h sB μ ν x))) := by
    intro μ ν
    funext x
    have e1 := curvature_eq_split h sB μ ν x
    have e2 := curvature_eq_split h B μ ν x
    have e3 : extD h sB μ ν x = s • extD h B μ ν x := by
      simp only [extD, gridFwd, hsB, ← smul_sub, smul_comm s]
    rw [e1, e3, show extD h B μ ν x = curvature h B μ ν x - curvRem h B μ ν x by
      rw [e2]; abel]
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, map_sub, smul_sub]
    rw [neg_smul]; abel
  set f : ι × ι → ℝ := fun p => gridL2Norm h (fun x => T (curvature h B p.1 p.2 x))
  set g : ι × ι → ℝ := fun p => gridL2Norm h (fun x => T (curvRem h B p.1 p.2 x)) +
    gridL2Norm h (fun x => T (curvRem h sB p.1 p.2 x))
  have hp : ∀ p : ι × ι, gridL2Norm h (fun x => T (curvature h sB p.1 p.2 x)) ≤ f p + g p := by
    intro p
    rw [hsplit]
    refine (gridL2Norm_add_le' hh _ _).trans ?_
    refine add_le_add ?_ ((gridL2Norm_add_le' hh _ _).trans ?_)
    · rw [gridL2Norm_smul', abs_of_nonneg hs0]
      exact mul_le_of_le_one_left (gridL2Norm_nonneg _ _) hs1
    · rw [gridL2Norm_smul', abs_neg, abs_of_nonneg hs0]
      exact add_le_add (mul_le_of_le_one_left (gridL2Norm_nonneg _ _) hs1) le_rfl
  unfold curvL2 packetL2
  calc √(∑ p ∈ pairs ι, gridL2Norm h (fun x => T (curvature h sB p.1 p.2 x)) ^ 2)
      ≤ √(∑ p ∈ pairs ι, (f p + g p) ^ 2) := by
        refine Real.sqrt_le_sqrt (sum_le_sum fun p _ => ?_)
        exact pow_le_pow_left₀ (gridL2Norm_nonneg _ _) (hp p) 2
    _ ≤ √(∑ p ∈ pairs ι, f p ^ 2) + √(∑ p ∈ pairs ι, g p ^ 2) := sqrt_sum_add_sq_le _ _ _
    _ ≤ √(∑ p ∈ pairs ι, f p ^ 2) + ∑ p ∈ pairs ι, g p := by
        gcongr
        exact sqrt_sum_sq_le_sum _ _ fun p _ => add_nonneg (gridL2Norm_nonneg _ _)
          (gridL2Norm_nonneg _ _)
    _ ≤ _ := by
        have hsum : ∑ p ∈ pairs ι, g p ≤ 192 * K * oneL4 h T B ^ 2 + 192 * K * oneL4 h T sB ^ 2 := by
          simp only [g, sum_add_distrib]
          exact add_le_add hNB hNsB
        have hsB2 : oneL4 h T sB ^ 2 ≤ oneL4 h T B ^ 2 := by
          rw [hL4s]
          have : s * oneL4 h T B ≤ oneL4 h T B := mul_le_of_le_one_left hL4B hs1
          exact pow_le_pow_left₀ (mul_nonneg hs0 hL4B) this 2
        have : 192 * K * oneL4 h T sB ^ 2 ≤ 192 * K * oneL4 h T B ^ 2 :=
          mul_le_mul_of_nonneg_left hsB2 (by positivity)
        linarith

/-- `‖𝔽_h(A_s)‖_{2,h} = ‖𝔽_h(sB)‖_{2,h}` on unitary gauges (invariant metric). -/
theorem curvL2_linkA_eq (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖) {h : ℝ}
    (hh : h ≠ 0) {B : ι → (ι → ZMod n) → 𝔸} {s : ℝ} {q : (ι → ZMod n) → 𝔸}
    (hq : ∀ y, q y ∈ unitary 𝔸) (hp : (s, q) ∈ domO toE h B)
    (hpl : ∀ μ ν x, ‖plaquette h (fun μ y => s • B μ y) μ ν x - 1‖ < 1) :
    curvL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B s q) =
      curvL2 h (toE : 𝔸 →L[ℝ] E) (fun μ y => s • B μ y) := by
  unfold curvL2 packetL2
  congr 1
  refine sum_congr rfl fun p _ => ?_
  congr 1
  simp only [gridL2Norm, periodicHodgeNormSq]
  congr 2
  refine sum_congr rfl fun x _ => ?_
  rw [curvature_linkA toE hh hq hp hpl]
  change ‖toE (q x * _ * star (q x))‖ ^ 2 = _
  rw [hM1 _ (hq x)]
  rfl

/-! ### The first-exit argument -/

/-- The envelope constant `K = 21 ‖toE‖ ‖toE⁻¹‖²`. -/
def Kc : ℝ := 21 * ‖(toE : 𝔸 →L[ℝ] E)‖ * ‖(toE.symm : E →L[ℝ] 𝔸)‖ ^ 2

/-- The seed size `b = 12(‖𝔽_h(B)‖_{2,h} + 384 K ‖B‖²_{4,h}) + (8/L) ‖B‖_{2,h}`. -/
def bSeed (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) : ℝ :=
  12 * (curvL2 h (toE : 𝔸 →L[ℝ] E) B + 384 * Kc toE * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2) +
    8 / (n * h) * oneL2 h (toE : 𝔸 →L[ℝ] E) B

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E] in
theorem norm_le_symm (X : 𝔸) : ‖X‖ ≤ ‖(toE.symm : E →L[ℝ] 𝔸)‖ * ‖toE X‖ := by
  have := (toE.symm : E →L[ℝ] 𝔸).le_opNorm (toE X)
  simpa using this

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E] in
theorem Kc_nonneg : 0 ≤ Kc toE := by unfold Kc; positivity

theorem curvL2_nonneg (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : 0 ≤ curvL2 h T A :=
  Real.sqrt_nonneg _

theorem oneL2_nonneg (h : ℝ) (T : 𝔸 →L[ℝ] E) (A : ι → (ι → ZMod n) → 𝔸) : 0 ≤ oneL2 h T A :=
  Real.sqrt_nonneg _

theorem bSeed_nonneg {h : ℝ} (hh : 0 < h) (B : ι → (ι → ZMod n) → 𝔸) : 0 ≤ bSeed toE h B := by
  have := Kc_nonneg toE
  have h1 := curvL2_nonneg h (toE : 𝔸 →L[ℝ] E) B
  have h2 := oneL2_nonneg h (toE : 𝔸 →L[ℝ] E) B
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold bSeed; positivity

theorem slot_scale {h : ℝ} (hh : 0 < h) (B : ι → (ι → ZMod n) → 𝔸)
    (hseed : ∀ μ ν x, h * slotNorm B μ ν x ≤ 1 / 8) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (μ ν : ι) (x : ι → ZMod n) : h * slotNorm (fun μ y => s • B μ y) μ ν x ≤ 1 / 8 := by
  have e : slotNorm (fun μ y => s • B μ y) μ ν x = s * slotNorm B μ ν x := by
    simp only [slotNorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]; ring
  rw [e]
  have h0 : 0 ≤ slotNorm B μ ν x := by unfold slotNorm; positivity
  have := hseed μ ν x
  calc h * (s * slotNorm B μ ν x) = s * (h * slotNorm B μ ν x) := by ring
    _ ≤ 1 * (h * slotNorm B μ ν x) := by gcongr
    _ ≤ 1 / 8 := by linarith

/-- **A priori analysis and first exit** (`eq:native-Coulomb-first-exit`): along any solution
of the Coulomb homotopy on `[0, T]`, `T ≤ 1`, starting at `q ≡ 1` inside the domain, the
estimate `a_s ≤ b + C₁ a_s²` holds, hence (first exit) `a_s ≤ (4/3) b ≤ r/2`, and the path stays
in the compact a priori set. -/
theorem apriori_of_solution (hι : Fintype.card ι = 4)
    (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ}
    (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    (hseed : ∀ μ ν x, h * slotNorm B μ ν x ≤ 1 / 8) {r : ℝ} (hr0 : 0 < r)
    (hrC : 12 * 192 * Kc toE * r ≤ 1 / 4) (hrFP : r ≤ FaddeevPopov.rFP (brE toE))
    (hrc : ‖(toE.symm : E →L[ℝ] 𝔸)‖ * r ≤ 1 / 64) (hb : bSeed toE h B ≤ 3 / 8 * r)
    {T : ℝ} (hT : T ≤ 1) {γ : ℝ → (ι → ZMod n) → 𝔸} (hγ0 : γ 0 = fun _ => 1)
    (hO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ domO toE h B)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, (t, γ t) ∈ setK toE h B ∧
      oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) ≤ 4 / 3 * bSeed toE h B := by
  set c := ‖(toE.symm : E →L[ℝ] 𝔸)‖ with hcdef
  set K := Kc toE with hKdef
  set b := bSeed toE h B with hbdef
  have hc0 : 0 ≤ c := norm_nonneg _
  have hc : ∀ X, ‖X‖ ≤ c * ‖toE X‖ := norm_le_symm toE
  have hu := unitary_of_solution toE B hγ0 hd
  have hcod := coulomb_of_solution toE hι hh hB hγ0 hO hd
  have hL2 := oneL2_le_of_solution toE hι hM1 hM2 hh hB hγ0 hO hd
  have hK0 : 0 ≤ K := Kc_nonneg toE
  have hb0 : 0 ≤ b := bSeed_nonneg toE hh B
  set a : ℝ → ℝ := fun t => oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) with ha
  have ha0 : ∀ t, 0 ≤ a t := fun t => oneL4_nonneg hh.le _ _
  -- the plaquettes of the rescaled seeds are in the chart
  have hpl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ μ ν x,
      ‖plaquette h (fun μ y => s • B μ y) μ ν x - 1‖ < 1 := by
    intro s hs μ ν x
    have hsl := slot_scale hh B hseed hs.1 hs.2 μ ν x
    have := (norm_curvRem_le hh _ μ ν x hsl).2
    linarith
  -- the a priori inequality `a ≤ b + C₁ a²`
  have hineq : ∀ t ∈ Icc 0 T, a t ≤ b + 12 * 192 * K * a t ^ 2 := by
    intro t ht
    have hp := hO t ht
    have hs : ∀ μ ν x, h * slotNorm (linkA h B t (γ t)) μ ν x ≤ 1 / 8 := by
      intro μ ν x
      have e : ∀ μ y, h * ‖linkA h B t (γ t) μ y‖ ≤ 1 / 64 := by
        intro μ y
        have := (hp.2.1 μ y).le
        rwa [← h_smul_linkA hh.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hh] at this
      have := e μ x; have := e ν (x + gridStep μ); have := e μ (x + gridStep ν); have := e ν x
      unfold slotNorm
      linarith
    have hap := (coulomb_apriori hι (toE : 𝔸 →L[ℝ] E) hc0 hc hh _ (hcod t ht) hs).1
    have hcurv : curvL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) ≤
        curvL2 h (toE : 𝔸 →L[ℝ] E) B + 2 * (192 * K * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2) := by
      rw [curvL2_linkA_eq toE hM1 hh.ne' (hu t ht) hp (hpl t ⟨ht.1, ht.2.trans hT⟩)]
      exact curvL2_smul_le hι _ hc0 hc hh B hseed ht.1 (ht.2.trans hT)
    have hl2 : oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) ≤ oneL2 h (toE : 𝔸 →L[ℝ] E) B :=
      (hL2 t ht).trans (mul_le_of_le_one_left (oneL2_nonneg _ _ _) (ht.2.trans hT))
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have hL : 0 ≤ 8 / (n * h) := by positivity
    have hK' : 21 * ‖(toE : 𝔸 →L[ℝ] E)‖ * c ^ 2 = K := rfl
    rw [hK'] at hap
    calc a t ≤ 12 * curvL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) +
          8 / (n * h) * oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) +
          12 * 192 * K * a t ^ 2 := hap
      _ ≤ 12 * (curvL2 h (toE : 𝔸 →L[ℝ] E) B + 2 * (192 * K * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2)) +
          8 / (n * h) * oneL2 h (toE : 𝔸 →L[ℝ] E) B + 12 * 192 * K * a t ^ 2 := by gcongr
      _ = b + 12 * 192 * K * a t ^ 2 := by rw [hbdef, bSeed]; ring
  -- continuity of `a`
  have hcontA : ContinuousOn a (Icc 0 T) := by
    simp only [ha, oneL4]
    refine continuousOn_finsetSum _ fun μ _ => ?_
    refine (continuous_gridL4Norm h).comp_continuousOn ?_
    exact continuousOn_pi.2 fun y => toE.continuous.comp_continuousOn
      (continuousOn_linkA_sol toE B hO hd μ y)
  have ha_zero : a 0 = 0 := by
    have hz : bar (toE : 𝔸 →L[ℝ] E) (linkA h B 0 (γ 0)) = 0 := by
      funext μ y
      rw [hγ0]
      simp only [bar, linkA_one, map_zero, Pi.zero_apply]
    simp only [ha, oneL4, hz, Pi.zero_apply]
    simp [gridL4Norm]
  -- first exit
  have key : ∀ t ∈ Icc 0 T, a t ≤ r → a t ≤ 4 / 3 * b := by
    intro t ht har
    have h1 := hineq t ht
    have h2 : 12 * 192 * K * a t ^ 2 ≤ a t / 4 := by
      calc 12 * 192 * K * a t ^ 2 = (12 * 192 * K * a t) * a t := by ring
        _ ≤ (12 * 192 * K * r) * a t := by
            have : 12 * 192 * K * a t ≤ 12 * 192 * K * r :=
              mul_le_mul_of_nonneg_left har (by positivity)
            exact mul_le_mul_of_nonneg_right this (ha0 t)
        _ ≤ 1 / 4 * a t := mul_le_mul_of_nonneg_right hrC (ha0 t)
        _ = a t / 4 := by ring
    linarith
  have hfinal : ∀ t ∈ Icc 0 T, a t ≤ 4 / 3 * b := by
    intro t ht
    by_contra hcon
    by_cases har : a t ≤ r
    · exact hcon (key t ht har)
    · have hart : r ≤ a t := le_of_lt (lt_of_not_ge har)
      obtain ⟨t', ht', hat'⟩ := intermediate_value_Icc ht.1
        (hcontA.mono (Icc_subset_Icc le_rfl ht.2)) ⟨by rw [ha_zero]; exact hr0.le, hart⟩
      have := key t' ⟨ht'.1, ht'.2.trans ht.2⟩ hat'.le
      rw [hat'] at this
      linarith
  intro t ht
  have hat : a t ≤ r / 2 := (hfinal t ht).trans (by linarith)
  have hp := hO t ht
  have hLog : ∀ μ x, ‖logChart (linkP h B t (γ t) μ x)‖ ≤ 1 / 128 := by
    intro μ x
    rw [← h_smul_linkA hh.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have h1 := FaddeevPopov.mul_norm_le_gridL4Norm hι hh
      (fun y => toE (linkA h B t (γ t) μ y)) x
    have h2 := gridL4_le_oneL4 hh.le (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) μ
    have h3 : gridL4Norm h (bar (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) μ) ≤ a t := h2
    calc h * ‖linkA h B t (γ t) μ x‖ ≤ h * (c * ‖toE (linkA h B t (γ t) μ x)‖) :=
          mul_le_mul_of_nonneg_left (hc _) hh.le
      _ = c * (h * ‖toE (linkA h B t (γ t) μ x)‖) := by ring
      _ ≤ c * (r / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          exact h1.trans (h3.trans hat)
      _ ≤ 1 / 128 := by linarith
  refine ⟨⟨⟨ht.1, ht.2.trans hT⟩, hu t ht, fun μ x => ?_, hLog, fun μ => ?_⟩, hfinal t ht⟩
  · rw [← exp_logChart (hp.1 μ x)]
    exact (norm_exp_sub_one_le ((hLog μ x).trans (by norm_num))).trans
      (by linarith [hLog μ x])
  · have h2 := gridL4_le_oneL4 hh.le (toE : 𝔸 →L[ℝ] E) (linkA h B t (γ t)) μ
    have h3 : gridL4Norm h (fun y => toE (linkA h B t (γ t) μ y)) ≤ a t := h2
    linarith

/-! ### The theorem -/

theorem initial_mem_setK {h : ℝ} (hh : 0 < h) (B : ι → (ι → ZMod n) → 𝔸) :
    ((0 : ℝ), fun _ => (1 : 𝔸)) ∈ setK toE h B := by
  have hP : ∀ μ x, linkP h B 0 (fun _ => (1 : 𝔸)) μ x = 1 := fun μ x => by simp [linkP]
  refine ⟨⟨le_rfl, zero_le_one⟩, fun _ => one_mem _, fun μ x => ?_, fun μ x => ?_, fun μ => ?_⟩
  · rw [hP, sub_self, norm_zero]; norm_num
  · rw [hP, logChart_one, norm_zero]; norm_num
  · have : (fun y => toE (linkA h B 0 (fun _ => (1 : 𝔸)) μ y)) = 0 := by
      funext y; simp [linkA_one]
    rw [this]
    have h0 : gridL4Norm h (0 : (ι → ZMod n) → E) = 0 := by simp [gridL4Norm]
    rw [h0]
    exact (half_pos (FaddeevPopov.rFP_pos (brE toE))).le

omit [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E] [FiniteDimensional ℝ E] [Fintype ι]
  [LinearOrder ι] [NeZero n] in
theorem linkA_at_one (h : ℝ) (B : ι → (ι → ZMod n) → 𝔸) (q : (ι → ZMod n) → 𝔸) (μ : ι)
    (x : ι → ZMod n) :
    linkA h B 1 q μ x = h⁻¹ • logChart (q x * exp (h • B μ x) * star (q (x + gridStep μ))) := by
  simp only [linkA, linkP, one_smul]

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [NeZero n] in
theorem div_succ_le_one {x : ℝ} (hx : 0 ≤ x) : x / (x + 1) ≤ 1 := by
  rw [div_le_one (by linarith)]; linarith

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [NeZero n] in
/-- Choice of the a priori radius `r`. -/
theorem exists_radius {K c ρ ε : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 12 * 192 * K * r ≤ 1 / 4 ∧ r ≤ ρ ∧ c * r ≤ 1 / 64 ∧ r ≤ ε ∧ r ≤ 1 := by
  refine ⟨min (min (1 / (4 * (12 * 192) * (K + 1))) ρ) (min (1 / (64 * (c + 1))) (min ε 1)),
    lt_min (lt_min (by positivity) hρ) (lt_min (by positivity) (lt_min hε one_pos)), ?_,
    (min_le_left _ _).trans (min_le_right _ _), ?_,
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  · have h1 := (min_le_left _ (min (1 / (64 * (c + 1))) (min ε 1))).trans
      (min_le_left (1 / (4 * (12 * 192) * (K + 1))) ρ)
    calc 12 * 192 * K * _ ≤ 12 * 192 * K * (1 / (4 * (12 * 192) * (K + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 4 * (K / (K + 1)) := by field_simp
      _ ≤ 1 / 4 * 1 := mul_le_mul_of_nonneg_left (div_succ_le_one hK) (by norm_num)
      _ = 1 / 4 := mul_one _
  · have h1 := (min_le_right (min (1 / (4 * (12 * 192) * (K + 1))) ρ) _).trans
      (min_le_left (1 / (64 * (c + 1))) (min ε 1))
    calc c * _ ≤ c * (1 / (64 * (c + 1))) := mul_le_mul_of_nonneg_left h1 hc
      _ = 1 / 64 * (c / (c + 1)) := by field_simp
      _ ≤ 1 / 64 * 1 := mul_le_mul_of_nonneg_left (div_succ_le_one hc) (by norm_num)
      _ = 1 / 64 := mul_one _

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [NeZero n] in
/-- Choice of the seed threshold `ε_c`. -/
theorem exists_threshold {K c r : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ c * ε ≤ 1 / 32 ∧ (20 + 4608 * K) * ε ≤ 3 / 8 * r := by
  refine ⟨min (min 1 (1 / (32 * (c + 1)))) (r / (64 * (1 + 4608 * K))),
    lt_min (lt_min one_pos (by positivity)) (by positivity),
    (min_le_left _ _).trans (min_le_left _ _), ?_, ?_⟩
  · have h1 := (min_le_left _ (r / (64 * (1 + 4608 * K)))).trans
      (min_le_right 1 (1 / (32 * (c + 1))))
    calc c * _ ≤ c * (1 / (32 * (c + 1))) := mul_le_mul_of_nonneg_left h1 hc
      _ = 1 / 32 * (c / (c + 1)) := by field_simp
      _ ≤ 1 / 32 * 1 := mul_le_mul_of_nonneg_left (div_succ_le_one hc) (by norm_num)
      _ = 1 / 32 := mul_one _
  · have h1 := min_le_right (min 1 (1 / (32 * (c + 1)))) (r / (64 * (1 + 4608 * K)))
    have h2 : (20 + 4608 * K) / (64 * (1 + 4608 * K)) ≤ 3 / 8 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc (20 + 4608 * K) * _ ≤ (20 + 4608 * K) * (r / (64 * (1 + 4608 * K))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = r * ((20 + 4608 * K) / (64 * (1 + 4608 * K))) := by ring
      _ ≤ r * (3 / 8) := mul_le_mul_of_nonneg_left h2 hr.le
      _ = 3 / 8 * r := by ring

omit [CStarAlgebra 𝔸] [Nontrivial 𝔸] [FiniteDimensional ℝ 𝔸] [Nontrivial E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [LinearOrder ι] [NeZero n] in
/-- The final arithmetic of `eq:native-Coulomb-estimate`. -/
theorem final_bound {H a PA FA P F X K L b : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hP : 0 ≤ P) (hF : 0 ≤ F) (hX : 0 ≤ X)
    (hH : H ≤ PA + FA + 192 * K * a ^ 2) (hPA : PA ≤ P) (hFA : FA ≤ F + 2 * (192 * K * X))
    (hab : a ≤ 4 / 3 * b) (hb : b ≤ (12 + 4608 * K + 8 / L) * (P + F + X)) :
    H + a ≤ (1 + 384 * K + 4 / 3 * (1 + 192 * K) * (12 + 4608 * K + 8 / L)) * (P + F + X) := by
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have h1 : 192 * K * a ^ 2 ≤ 192 * K * a := mul_le_mul_of_nonneg_left ha2 (by positivity)
  have h2 : (1 + 192 * K) * a ≤ (1 + 192 * K) * (4 / 3 * ((12 + 4608 * K + 8 / L) * (P + F + X))) :=
    mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
      (by positivity)
  have hS : 0 ≤ P + F + X := by positivity
  have h3 : P + F + 384 * K * X ≤ (1 + 384 * K) * (P + F + X) := by nlinarith [mul_nonneg hK hS]
  nlinarith

/-- The construction for one seed (all hypotheses explicit). -/
theorem coulomb_of_seed (hι : Fintype.card ι = 4)
    (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0) {h : ℝ}
    (hh : 0 < h) {B : ι → (ι → ZMod n) → 𝔸} (hB : ∀ μ x, star (B μ x) = -B μ x)
    (hseed : ∀ μ ν x, h * slotNorm B μ ν x ≤ 1 / 8) {r : ℝ} (hr0 : 0 < r)
    (hrC : 12 * 192 * Kc toE * r ≤ 1 / 4) (hrFP : r ≤ FaddeevPopov.rFP (brE toE))
    (hrc : ‖(toE.symm : E →L[ℝ] 𝔸)‖ * r ≤ 1 / 64) (hr1 : r ≤ 1)
    (hb : bSeed toE h B ≤ 3 / 8 * r) :
    ∃ q : (ι → ZMod n) → 𝔸, (∀ x, q x ∈ unitary 𝔸) ∧
      (∀ μ x, star (linkA h B 1 q μ x) = -linkA h B 1 q μ x) ∧
      periodicHodgeCodiff h gridStep (bar (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q)) = 0 ∧
      oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤ 4 / 3 * bSeed toE h B ∧
      oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤ oneL2 h (toE : 𝔸 →L[ℝ] E) B ∧
      curvL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤
        curvL2 h (toE : 𝔸 →L[ℝ] E) B + 2 * (192 * Kc toE * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2) ∧
      oneH1 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤ oneL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) +
        curvL2 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) +
          192 * Kc toE * oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ^ 2 ∧
      ∃ γ : ℝ → (ι → ZMod n) → 𝔸, γ 0 = (fun _ => 1) ∧ γ 1 = q ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (t, γ t) ∈ domO toE h B) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 1) t := by
  have hc0 : 0 ≤ ‖(toE.symm : E →L[ℝ] 𝔸)‖ := norm_nonneg _
  obtain ⟨γ, hγ0, hγ⟩ := ODEContinuation.exists_solution_of_apriori (f := field toE h B)
    (isOpen_domO toE h B) (field_contDiffOn toE hι hh B) (isCompact_setK toE h B)
    (setK_subset_domO toE h B) (initial_mem_setK toE hh B) zero_le_one
    (fun T hT γ hγ0 hO hd t ht => (apriori_of_solution toE hι hM1 hM2 hh hB hseed hr0 hrC hrFP
      hrc hb hT.2 hγ0 hO hd t ht).1)
  have hO1 : ∀ t ∈ Icc (0 : ℝ) 1, (t, γ t) ∈ domO toE h B := fun t ht =>
    setK_subset_domO toE h B (hγ t ht).2
  have hd1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 1) t :=
    fun t ht => (hγ t ht).1
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hap1 := apriori_of_solution toE hι hM1 hM2 hh hB hseed hr0 hrC hrFP hrc hb le_rfl hγ0 hO1
    hd1 1 h1mem
  have hcod1 := coulomb_of_solution toE hι hh hB hγ0 hO1 hd1 1 h1mem
  have hu1 := unitary_of_solution toE B hγ0 hd1 1 h1mem
  have hL21 := oneL2_le_of_solution toE hι hM1 hM2 hh hB hγ0 hO1 hd1 1 h1mem
  have hp1 := hO1 1 h1mem
  refine ⟨γ 1, hu1, linkA_skew toE hB hu1 hp1, hcod1, hap1.2, by simpa using hL21, ?_, ?_,
    γ, hγ0, rfl, hO1, hd1⟩
  · have hpl : ∀ μ ν x, ‖plaquette h (fun μ y => (1 : ℝ) • B μ y) μ ν x - 1‖ < 1 := by
      intro μ ν x
      have hsl := slot_scale hh B hseed zero_le_one le_rfl μ ν x
      have := (norm_curvRem_le hh _ μ ν x hsl).2
      linarith
    rw [curvL2_linkA_eq toE hM1 hh.ne' hu1 hp1 hpl]
    exact curvL2_smul_le hι _ hc0 (norm_le_symm toE) hh B hseed zero_le_one le_rfl
  · have hs : ∀ μ ν x, h * slotNorm (linkA h B 1 (γ 1)) μ ν x ≤ 1 / 8 := by
      intro μ ν x
      have e : ∀ μ y, h * ‖linkA h B 1 (γ 1) μ y‖ ≤ 1 / 64 := by
        intro μ y
        have := (hp1.2.1 μ y).le
        rwa [← h_smul_linkA hh.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hh] at this
      have := e μ x; have := e ν (x + gridStep μ); have := e μ (x + gridStep ν); have := e ν x
      unfold slotNorm
      linarith
    exact (coulomb_apriori hι (toE : 𝔸 →L[ℝ] E) hc0 (norm_le_symm toE) hh _ hcod1 hs).2

/-- **`thm:finite-Coulomb-normalization`** (finite critical Coulomb normalization).

Let the gauge group be the unitary group of a finite-dimensional C*-algebra `𝔸` with an
invariant Lie-algebra metric `toE` (hypotheses `hM1`, `hM2`), on the four-dimensional periodic
grid of fixed side `L = m h`.  For every prescribed `ε_* > 0` there are `ε_c, C_c > 0`,
independent of `m` and `h`, such that every skew-adjoint logarithmic seed `B` with
`‖B‖_{4,h} + ‖𝔽_h(B)‖_{2,h} ≤ ε_c` (`eq:native-critical-seed`) admits a unitary site gauge `q`
with `A_μ(x) = h⁻¹ Log(q_x e^{hB_μ(x)} q_{x+μ}^*)` skew-adjoint, `δ_h A = 0`
(`eq:native-constructed-Coulomb`),
`‖A‖_{1,h} + ‖A‖_{4,h} ≤ C_c(‖B‖_{2,h} + ‖𝔽_h(B)‖_{2,h} + ‖B‖²_{4,h})`
(`eq:native-Coulomb-estimate`) and `‖A‖_{4,h} ≤ ε_*`.  No bound on `δ_h B` or on the first
differences of `B` is assumed. -/
theorem finite_coulomb_normalization (hι : Fintype.card ι = 4)
    (hM1 : ∀ U ∈ unitary 𝔸, ∀ X, ‖toE (U * X * star U)‖ = ‖toE X‖)
    (hM2 : ∀ a : 𝔸, star a = -a → ∀ u, inner ℝ (toE a) (toE (a * u - u * a)) = 0)
    {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (m : ℕ) [NeZero m] (h : ℝ), 0 < h → (m : ℝ) * h = L →
      ∀ B : ι → (ι → ZMod m) → 𝔸, (∀ μ x, star (B μ x) = -B μ x) →
      oneL4 h (toE : 𝔸 →L[ℝ] E) B + curvL2 h (toE : 𝔸 →L[ℝ] E) B ≤ εc →
      ∃ q : (ι → ZMod m) → 𝔸, (∀ x, q x ∈ unitary 𝔸) ∧
        (∀ μ x, linkA h B 1 q μ x =
          h⁻¹ • logChart (q x * exp (h • B μ x) * star (q (x + gridStep μ)))) ∧
        (∀ μ x, star (linkA h B 1 q μ x) = -linkA h B 1 q μ x) ∧
        periodicHodgeCodiff h gridStep (bar (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q)) = 0 ∧
        oneH1 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) + oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤
          Cc * (oneL2 h (toE : 𝔸 →L[ℝ] E) B + curvL2 h (toE : 𝔸 →L[ℝ] E) B +
            oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2) ∧
        oneL4 h (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q) ≤ εstar ∧
        ∃ γ : ℝ → (ι → ZMod m) → 𝔸, γ 0 = (fun _ => 1) ∧ γ 1 = q ∧
          (∀ t ∈ Icc (0 : ℝ) 1, (t, γ t) ∈ domO toE h B) ∧
          ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (field toE h B t (γ t)) (Icc 0 1) t := by
  have hc0 : 0 ≤ ‖(toE.symm : E →L[ℝ] 𝔸)‖ := norm_nonneg _
  have hK0 := Kc_nonneg toE
  obtain ⟨r, hr0, hrC, hrFP, hrc, hrε, hr1⟩ :=
    exists_radius hK0 hc0 (FaddeevPopov.rFP_pos (brE toE)) hεstar
  obtain ⟨εc, hεc0, hεc1, hεcc, hεcr⟩ := exists_threshold (K := Kc toE) hK0 hc0 hr0
  refine ⟨εc, 1 + 384 * Kc toE + 4 / 3 * (1 + 192 * Kc toE) * (12 + 4608 * Kc toE + 8 / L),
    hεc0, by positivity, fun m _ h hh hmh B hB hBsmall => ?_⟩
  have hB4 : oneL4 h (toE : 𝔸 →L[ℝ] E) B ≤ εc :=
    (le_add_of_nonneg_right (curvL2_nonneg _ _ _)).trans hBsmall
  have hBF : curvL2 h (toE : 𝔸 →L[ℝ] E) B ≤ εc :=
    (le_add_of_nonneg_left (oneL4_nonneg hh.le _ _)).trans hBsmall
  have hB40 := oneL4_nonneg hh.le (toE : 𝔸 →L[ℝ] E) B
  -- the seed is in the scaled chart
  have hseed : ∀ μ ν x, h * slotNorm B μ ν x ≤ 1 / 8 := by
    have e : ∀ μ y, h * ‖B μ y‖ ≤ 1 / 32 := by
      intro μ y
      have h1 := FaddeevPopov.mul_norm_le_gridL4Norm hι hh (fun z => toE (B μ z)) y
      have h2 := gridL4_le_oneL4 hh.le (toE : 𝔸 →L[ℝ] E) B μ
      have h3 : gridL4Norm h (fun z => toE (B μ z)) ≤ εc := h2.trans hB4
      calc h * ‖B μ y‖ ≤ h * (‖(toE.symm : E →L[ℝ] 𝔸)‖ * ‖toE (B μ y)‖) :=
            mul_le_mul_of_nonneg_left (norm_le_symm toE _) hh.le
        _ = ‖(toE.symm : E →L[ℝ] 𝔸)‖ * (h * ‖toE (B μ y)‖) := by ring
        _ ≤ ‖(toE.symm : E →L[ℝ] 𝔸)‖ * εc := mul_le_mul_of_nonneg_left (h1.trans h3) hc0
        _ ≤ 1 / 32 := hεcc
    intro μ ν x
    have := e μ x; have := e ν (x + gridStep μ); have := e μ (x + gridStep ν); have := e ν x
    unfold slotNorm
    linarith
  -- the seed size
  have hL2B : oneL2 h (toE : 𝔸 →L[ℝ] E) B ≤ L * εc := by
    have := oneL2_le hι hh (toE : 𝔸 →L[ℝ] E) B
    rw [hmh] at this
    exact this.trans (mul_le_mul_of_nonneg_left hB4 hL.le)
  have hbsplit : bSeed toE h B = 12 * curvL2 h (toE : 𝔸 →L[ℝ] E) B +
      4608 * Kc toE * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2 + 8 / L * oneL2 h (toE : 𝔸 →L[ℝ] E) B := by
    rw [bSeed, hmh]; ring
  have hb : bSeed toE h B ≤ 3 / 8 * r := by
    rw [hbsplit]
    have h1 : oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2 ≤ εc := by
      calc oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2 ≤ εc ^ 2 := pow_le_pow_left₀ hB40 hB4 2
        _ ≤ εc * 1 := by rw [sq]; exact mul_le_mul_of_nonneg_left hεc1 hεc0.le
        _ = εc := mul_one _
    have h2 : 8 / L * oneL2 h (toE : 𝔸 →L[ℝ] E) B ≤ 8 * εc := by
      calc 8 / L * oneL2 h (toE : 𝔸 →L[ℝ] E) B ≤ 8 / L * (L * εc) :=
            mul_le_mul_of_nonneg_left hL2B (by positivity)
        _ = 8 * εc := by field_simp
    have h3 : 4608 * Kc toE * oneL4 h (toE : 𝔸 →L[ℝ] E) B ^ 2 ≤ 4608 * Kc toE * εc :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  obtain ⟨q, hu, hskew, hcod, ha, hl2, hcurv, hH1, hpath⟩ :=
    coulomb_of_seed toE hι hM1 hM2 hh hB hseed hr0 hrC hrFP hrc hr1 hb
  have ha0 := oneL4_nonneg hh.le (toE : 𝔸 →L[ℝ] E) (linkA h B 1 q)
  have hb0 := bSeed_nonneg toE hh B
  refine ⟨q, hu, linkA_at_one h B q, hskew, hcod, ?_, by linarith, hpath⟩
  refine final_bound hK0 hL ha0 (by linarith) (oneL2_nonneg _ _ _) (curvL2_nonneg _ _ _)
    (sq_nonneg _) hH1 hl2 hcurv ha ?_
  rw [hbsplit]
  have h8 : 0 ≤ 8 / L := by positivity
  have hP := oneL2_nonneg h (toE : 𝔸 →L[ℝ] E) B
  have hF := curvL2_nonneg h (toE : 𝔸 →L[ℝ] E) B
  have hX := sq_nonneg (oneL4 h (toE : 𝔸 →L[ℝ] E) B)
  nlinarith [mul_nonneg hK0 hP, mul_nonneg hK0 hF, mul_nonneg h8 hF, mul_nonneg h8 hX]

end

end RenewalGeometry.FiniteCoulomb
