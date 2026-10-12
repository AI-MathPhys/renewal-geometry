/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.EinsteinSMReducedTopology
import MathPhys.FieldTheory.Continuum.EinsteinSMChartBoxTools

/-!
# The strong-packet distance `d_K` on smooth fields and coupling constants

Triangle inequalities for `L^p` and `H¹` norms on chart boxes, measurability and `H¹` membership
of smooth fields on chart boxes, and the strong-packet distance `dK` (componentwise `dKComp`, the
coupling-constant coordinates `bankVec`) with its triangle inequality and symmetry.

Split out of `MathPhys.Continuum.EinsteinSMCofinalTransport` (which re-exports it); names
are unchanged.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace MathPhys
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Triangle inequalities -/

section Triangle

variable {T : ℝ} {ι' : Type} [Fintype ι']

theorem eLpNorm_sub_le_add {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f g h : E4 → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    eLpNorm (f - h) p μ ≤ eLpNorm (f - g) p μ + eLpNorm (g - h) p μ := by
  have e : f - h = (f - g) + (g - h) := by abel
  rw [e]
  exact eLpNorm_add_le (hf.sub hg) (hg.sub hh) hp

theorem eLpNorm_top_sub_le_add {F : Type*} [NormedAddCommGroup F] {μ : Measure E4}
    {f g h : E4 → F} : eLpNorm (f - h) ⊤ μ ≤ eLpNorm (f - g) ⊤ μ + eLpNorm (g - h) ⊤ μ := by
  have e : f - h = (f - g) + (g - h) := by abel
  rw [e, eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNorm_exponent_top]
  exact eLpNormEssSup_add_le

theorem h1Norm_sub_le_add {Q : ChartBox T} {u₁ u₂ u₃ : E4 → ι' → ℂ}
    {g₁ g₂ g₃ : E4 → Fin 4 → ι' → ℂ} (hu₁ : AEStronglyMeasurable u₁ Q.μ)
    (hu₂ : AEStronglyMeasurable u₂ Q.μ) (hu₃ : AEStronglyMeasurable u₃ Q.μ)
    (hg₁ : AEStronglyMeasurable g₁ Q.μ) (hg₂ : AEStronglyMeasurable g₂ Q.μ)
    (hg₃ : AEStronglyMeasurable g₃ Q.μ) :
    h1Norm Q (u₁ - u₃) (g₁ - g₃) ≤ h1Norm Q (u₁ - u₂) (g₁ - g₂) + h1Norm Q (u₂ - u₃) (g₂ - g₃) := by
  unfold h1Norm
  calc eLpNorm (u₁ - u₃) 2 Q.μ + eLpNorm (g₁ - g₃) 2 Q.μ
      ≤ (eLpNorm (u₁ - u₂) 2 Q.μ + eLpNorm (u₂ - u₃) 2 Q.μ) +
          (eLpNorm (g₁ - g₂) 2 Q.μ + eLpNorm (g₂ - g₃) 2 Q.μ) :=
        add_le_add (eLpNorm_sub_le_add (by norm_num) hu₁ hu₂ hu₃)
          (eLpNorm_sub_le_add (by norm_num) hg₁ hg₂ hg₃)
    _ = _ := by ring

theorem h1Norm_comm {Q : ChartBox T} (u₁ u₂ : E4 → ι' → ℂ) (g₁ g₂ : E4 → Fin 4 → ι' → ℂ) :
    h1Norm Q (u₁ - u₂) (g₁ - g₂) = h1Norm Q (u₂ - u₁) (g₂ - g₁) := by
  unfold h1Norm
  rw [eLpNorm_sub_comm u₁, eLpNorm_sub_comm g₁]

/-- `a_n ≤ c_n + b_n` with `c_n, b_n → 0` forces `a_n → 0`. -/
theorem tendsto_zero_of_le_add {a b c : ℕ → ℝ≥0∞} (hle : ∀ n, a n ≤ c n + b n)
    (hc : Tendsto c atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hc.add hb)
    (fun _ => zero_le) hle

end Triangle

/-! ### Measurability of smooth fields on chart boxes -/

section Meas

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} (Q : ChartBox T)
  (z : SmoothFields T left)

theorem SmoothFields.aesm_e : AEStronglyMeasurable z.z.e Q.μ :=
  (memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
    (z.smooth_e.continuousOn.mono Q.closure_subset_cylSlab) 1).1

theorem SmoothFields.aesm_A : AEStronglyMeasurable z.z.A Q.μ :=
  (memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
    (z.smooth_A.continuousOn.mono Q.closure_subset_cylSlab) 1).1

theorem SmoothFields.aesm_H : AEStronglyMeasurable z.z.H Q.μ :=
  (memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
    (z.smooth_H.continuousOn.mono Q.closure_subset_cylSlab) 1).1

theorem SmoothFields.aesm_F : AEStronglyMeasurable (curvatureF z.z.A) Q.μ :=
  (memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
    ((continuousOn_curvatureF z.smooth_A).mono Q.closure_subset_cylSlab) 1).1

theorem SmoothFields.aesm_K : AEStronglyMeasurable (covDerivHiggs z.z.A z.z.H) Q.μ :=
  (memLp_of_continuousOn_closure Q.isOpen Q.isCompact_closure
    ((continuousOn_covDerivHiggs z.smooth_A z.smooth_H).mono Q.closure_subset_cylSlab) 1).1

variable {ι' : Type} [Fintype ι']

theorem MemH1.aesm {u : E4 → ι' → ℂ} {g : E4 → Fin 4 → ι' → ℂ} (h : MemH1 Q u g) :
    AEStronglyMeasurable u Q.μ := (memLp_pi_iff.mpr fun c => (h c).memLp).1

theorem MemH1.aesm_grad {u : E4 → ι' → ℂ} {g : E4 → Fin 4 → ι' → ℂ} (h : MemH1 Q u g) :
    AEStronglyMeasurable g Q.μ :=
  (memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (h c).memLp_grad i).1

theorem SmoothFields.memH1_e : MemH1 Q (coframeC z.z.e) (coframeGrad z.z.e) :=
  memH1_coframe_of_smooth Q Q.isCompact_closure Q.closure_subset_cylSlab z.smooth_e

theorem SmoothFields.memH1_Ψ : MemH1 Q (spinorC z.z.Ψ) (spinorGrad z.z.Ψ) :=
  memH1_spinor_of_smooth Q z.smooth_Ψ

theorem SmoothFields.memH1_Ψb : MemH1 Q (spinorC z.z.Ψb) (spinorGrad z.z.Ψb) :=
  memH1_spinor_of_smooth Q z.smooth_Ψb

end Meas

/-! ### The strong-packet distance `d_K` -/

section DK

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- The difference norms of `eq:strong-geometry`–`eq:strong-spinors` on a chart box. -/
def dKComp (Q : ChartBox T) (z₁ z₂ : SmoothFields T left) : Fin 8 → ℝ≥0∞ :=
  ![eLpNorm (z₁.z.e - z₂.z.e) ⊤ Q.μ,
    h1Norm Q (coframeC z₁.z.e - coframeC z₂.z.e) (coframeGrad z₁.z.e - coframeGrad z₂.z.e),
    eLpNorm (z₁.z.A - z₂.z.A) 4 Q.μ,
    eLpNorm (curvatureF z₁.z.A - curvatureF z₂.z.A) 2 Q.μ,
    eLpNorm (z₁.z.H - z₂.z.H) 4 Q.μ,
    eLpNorm (covDerivHiggs z₁.z.A z₁.z.H - covDerivHiggs z₂.z.A z₂.z.H) 2 Q.μ,
    h1Norm Q (spinorC z₁.z.Ψ - spinorC z₂.z.Ψ) (spinorGrad z₁.z.Ψ - spinorGrad z₂.z.Ψ),
    h1Norm Q (spinorC z₁.z.Ψb - spinorC z₂.z.Ψb) (spinorGrad z₁.z.Ψb - spinorGrad z₂.z.Ψb)]

/-- The bank coordinates as an element of a product of `Pi` types (extended metric space). -/
def bankVec (θ : CoefficientBank Ysec) : (Fin 7 → ℝ) × (Ysec → Fin 3 → Fin 3 → ℂ) :=
  ((bankCoords θ).1, fun y i j => (bankCoords θ).2 y i j)

theorem bankTendsto_iff_vec {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec} :
    BankTendsto θ θ₀ ↔ Tendsto (fun n => bankVec (θ n)) atTop (𝓝 (bankVec θ₀)) := Iff.rfl

/-- **The strong-packet distance `d_K`** of two reconstructed cutoffs on a chart box: the sum of
the difference norms of `eq:strong-geometry`–`eq:strong-spinors` and `|θ₁ - θ₂|`. -/
def dK (Q : ChartBox T) (z₁ : SmoothFields T left) (θ₁ : CoefficientBank Ysec)
    (z₂ : SmoothFields T left) (θ₂ : CoefficientBank Ysec) : ℝ≥0∞ :=
  ∑ i, dKComp Q z₁ z₂ i + edist (bankVec θ₁) (bankVec θ₂)

theorem dKComp_le_dK (Q : ChartBox T) (z₁ : SmoothFields T left) (θ₁ : CoefficientBank Ysec)
    (z₂ : SmoothFields T left) (θ₂ : CoefficientBank Ysec) (i : Fin 8) :
    dKComp Q z₁ z₂ i ≤ dK Q z₁ θ₁ z₂ θ₂ :=
  (Finset.single_le_sum (f := dKComp Q z₁ z₂) (fun _ _ => zero_le) (Finset.mem_univ i)).trans
    le_self_add

theorem edist_bank_le_dK (Q : ChartBox T) (z₁ : SmoothFields T left)
    (θ₁ : CoefficientBank Ysec) (z₂ : SmoothFields T left) (θ₂ : CoefficientBank Ysec) :
    edist (bankVec θ₁) (bankVec θ₂) ≤ dK Q z₁ θ₁ z₂ θ₂ := le_add_self

theorem dKComp_triangle (Q : ChartBox T) (z₁ z₂ z₃ : SmoothFields T left) (i : Fin 8) :
    dKComp Q z₁ z₃ i ≤ dKComp Q z₁ z₂ i + dKComp Q z₂ z₃ i := by
  fin_cases i
  · exact eLpNorm_top_sub_le_add
  · exact h1Norm_sub_le_add ((z₁.memH1_e Q).aesm Q) ((z₂.memH1_e Q).aesm Q) ((z₃.memH1_e Q).aesm Q)
      ((z₁.memH1_e Q).aesm_grad Q) ((z₂.memH1_e Q).aesm_grad Q) ((z₃.memH1_e Q).aesm_grad Q)
  · exact eLpNorm_sub_le_add (by norm_num) (z₁.aesm_A Q) (z₂.aesm_A Q) (z₃.aesm_A Q)
  · exact eLpNorm_sub_le_add (by norm_num) (z₁.aesm_F Q) (z₂.aesm_F Q) (z₃.aesm_F Q)
  · exact eLpNorm_sub_le_add (by norm_num) (z₁.aesm_H Q) (z₂.aesm_H Q) (z₃.aesm_H Q)
  · exact eLpNorm_sub_le_add (by norm_num) (z₁.aesm_K Q) (z₂.aesm_K Q) (z₃.aesm_K Q)
  · exact h1Norm_sub_le_add ((z₁.memH1_Ψ Q).aesm Q) ((z₂.memH1_Ψ Q).aesm Q)
      ((z₃.memH1_Ψ Q).aesm Q) ((z₁.memH1_Ψ Q).aesm_grad Q) ((z₂.memH1_Ψ Q).aesm_grad Q)
      ((z₃.memH1_Ψ Q).aesm_grad Q)
  · exact h1Norm_sub_le_add ((z₁.memH1_Ψb Q).aesm Q) ((z₂.memH1_Ψb Q).aesm Q)
      ((z₃.memH1_Ψb Q).aesm Q) ((z₁.memH1_Ψb Q).aesm_grad Q) ((z₂.memH1_Ψb Q).aesm_grad Q)
      ((z₃.memH1_Ψb Q).aesm_grad Q)

/-- The triangle inequality for `d_K`. -/
theorem dK_triangle (Q : ChartBox T) (z₁ z₂ z₃ : SmoothFields T left)
    (θ₁ θ₂ θ₃ : CoefficientBank Ysec) :
    dK Q z₁ θ₁ z₃ θ₃ ≤ dK Q z₁ θ₁ z₂ θ₂ + dK Q z₂ θ₂ z₃ θ₃ := by
  unfold dK
  calc ∑ i, dKComp Q z₁ z₃ i + edist (bankVec θ₁) (bankVec θ₃)
      ≤ ∑ i, (dKComp Q z₁ z₂ i + dKComp Q z₂ z₃ i) +
          (edist (bankVec θ₁) (bankVec θ₂) + edist (bankVec θ₂) (bankVec θ₃)) :=
        add_le_add (Finset.sum_le_sum fun i _ => dKComp_triangle Q z₁ z₂ z₃ i)
          (edist_triangle _ _ _)
    _ = _ := by rw [Finset.sum_add_distrib]; ring

theorem dKComp_comm (Q : ChartBox T) (z₁ z₂ : SmoothFields T left) (i : Fin 8) :
    dKComp Q z₁ z₂ i = dKComp Q z₂ z₁ i := by
  fin_cases i
  · exact eLpNorm_sub_comm (z₁.z.e) (z₂.z.e) ⊤ Q.μ
  · exact h1Norm_comm _ _ _ _
  · exact eLpNorm_sub_comm (z₁.z.A) (z₂.z.A) 4 Q.μ
  · exact eLpNorm_sub_comm (curvatureF z₁.z.A) (curvatureF z₂.z.A) 2 Q.μ
  · exact eLpNorm_sub_comm (z₁.z.H) (z₂.z.H) 4 Q.μ
  · exact eLpNorm_sub_comm (covDerivHiggs z₁.z.A z₁.z.H) (covDerivHiggs z₂.z.A z₂.z.H) 2 Q.μ
  · exact h1Norm_comm _ _ _ _
  · exact h1Norm_comm _ _ _ _

theorem dK_comm (Q : ChartBox T) (z₁ : SmoothFields T left) (θ₁ : CoefficientBank Ysec)
    (z₂ : SmoothFields T left) (θ₂ : CoefficientBank Ysec) :
    dK Q z₁ θ₁ z₂ θ₂ = dK Q z₂ θ₂ z₁ θ₁ := by
  unfold dK
  rw [edist_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => dKComp_comm Q z₁ z₂ i

theorem dK_self (Q : ChartBox T) (z : SmoothFields T left) (θ : CoefficientBank Ysec) :
    dK Q z θ z θ = 0 := by
  have h : ∀ i, dKComp Q z z i = 0 := by
    intro i
    fin_cases i <;> simp [dKComp, h1Norm]
  simp [dK, h]

/-- **Summable cofinal transport** on a chart box: `d_K(z_{n+1}, z_n) ≤ η_n` with `Σ η_n < ∞`
(`eq:cofinal-transport`). -/
def SummableTransport (Q : ChartBox T) (z : ℕ → SmoothFields T left)
    (θ : ℕ → CoefficientBank Ysec) : Prop :=
  ∃ η : ℕ → ℝ≥0∞, (∑' n, η n) ≠ ⊤ ∧ ∀ n, dK Q (z (n + 1)) (θ (n + 1)) (z n) (θ n) ≤ η n

/-- The telescoped bound `d_K(z_m, z_n) ≤ Σ_{n ≤ j < m} η_j`. -/
theorem dK_le_sum_Ico (Q : ChartBox T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} {η : ℕ → ℝ≥0∞}
    (hη : ∀ n, dK Q (z (n + 1)) (θ (n + 1)) (z n) (θ n) ≤ η n) {n m : ℕ} (hnm : n ≤ m) :
    dK Q (z m) (θ m) (z n) (θ n) ≤ ∑ j ∈ Finset.Ico n m, η j := by
  induction m, hnm using Nat.le_induction with
  | base => simp [dK_self]
  | succ m hnm ih =>
    calc dK Q (z (m + 1)) (θ (m + 1)) (z n) (θ n)
        ≤ dK Q (z (m + 1)) (θ (m + 1)) (z m) (θ m) + dK Q (z m) (θ m) (z n) (θ n) :=
          dK_triangle Q _ _ _ _ _ _
      _ ≤ η m + ∑ j ∈ Finset.Ico n m, η j := add_le_add (hη m) ih
      _ = ∑ j ∈ Finset.Ico n (m + 1), η j := by rw [Finset.sum_Ico_succ_top hnm]; ring

/-- **Summable transport makes the sequence Cauchy in `d_K`.** -/
theorem dK_cauchy (Q : ChartBox T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (h : SummableTransport Q z θ) :
    ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N, dK Q (z m) (θ m) (z n) (θ n) ≤ ε := by
  obtain ⟨η, hsum, hη⟩ := h
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_sum_nat_add η hsum).eventually (ge_mem_nhds hε))
  have key : ∀ m n, N ≤ n → n ≤ m → dK Q (z m) (θ m) (z n) (θ n) ≤ ε := by
    intro m n hNn hnm
    refine (dK_le_sum_Ico Q hη hnm).trans ?_
    refine le_trans (Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left hNn)) ?_
    refine le_trans ?_ (hN N le_rfl)
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (m - N)))
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
  refine ⟨N, fun m hm n hn => ?_⟩
  rcases le_total n m with hnm | hmn
  · exact key m n hn hnm
  · rw [dK_comm]; exact key n m hm hmn

end DK

end EinsteinSM
end MathPhys
