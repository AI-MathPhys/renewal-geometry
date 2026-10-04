/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMainLimit

/-!
# Summable cofinal transport, cofinal uniqueness and a realized random branch
  (`prop:cofinal-transport`, `cor:cofinal-unique`, `cor:random-realization`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMCertificatePacket.lean` and `EinsteinSMMainLimit.lean`.

## The strong-packet distance

`dK Q z₁ θ₁ z₂ θ₂` is the paper's `d_K` (`app:sectorwise-variation`): the sum of the difference
norms of `eq:strong-geometry`–`eq:strong-spinors` on the chart box `Q`
(`‖e₁ - e₂‖_{L^∞} + ‖e₁ - e₂‖_{H¹} + ‖A₁ - A₂‖_{L⁴} + ‖F_{A₁} - F_{A₂}‖_{L²} + ‖H₁ - H₂‖_{L⁴}
+ ‖D_{A₁}H₁ - D_{A₂}H₂‖_{L²} + ‖Ψ₁ - Ψ₂‖_{H¹} + ‖Ψ̄₁ - Ψ̄₂‖_{H¹}`) plus the bank distance
`|θ₁ - θ₂|` (the extended distance of `bankCoords`).  It is valued in `ℝ≥0∞`; `dK_triangle`,
`dK_comm`, `dK_self`.

## Contents

* `dK_le_sum_Ico`, `dK_cauchy`: summable adjacent transport `d_K(z_{n+1}, z_n) ≤ η_n`,
  `Σ η_n < ∞`, makes the sequence Cauchy in `d_K`, hence in each norm entering `d_K`;
* `StrongPacketOn.of_close`, `StrongPacket.of_close`: sequences `d_K`-close to a strong-packet
  convergent sequence converge to the same strong-packet limit;
* `StrongPacket.unique`, `StrongPacket.comp`: uniqueness of strong-packet limits and passage to
  subsequences;
* **`cofinal_transport`** (`prop:cofinal-transport`): Cauchy in each norm, a unique local
  strong-packet limit of the **whole** sequence; **`cofinal_route_independence`** (route
  independence under vanishing direct comparisons); **`cofinal_subseq_limit_eq`** (no subsequence
  choice remains);
* **`cofinal_unique`** (`cor:cofinal-unique`);
* **`random_realization`** (`cor:random-realization`): Tonelli (`ae_tsum_sq_ne_top`), pathwise
  vanishing of `L_h√R_h + e_h`, `cofinal_unique` on each path of a full-measure event;
* the last sentence of `cor:random-realization` (hypotheses on a dense test core):
  `testJet_sub`, `continuous_cov_functional`, `continuous_firstVariation` (the reconstructed first
  variation of smooth fields is continuous in the test), `coreConsistencyDefect`,
  `SourceBoundsOn`, `closure_on_core` (the limit functional vanishes on the core and is continuous
  as a locally uniform limit, hence vanishes), **`random_realization_core`**;
* non-vacuity for the flat regulator (all main theorems).

The spinor `H¹` compactness on route (C4b) is *not* needed here: the summable transport itself
makes the spinors Cauchy in `H¹` on every chart box, so the strong packet is produced through the
proved `certificate_packet_of_spinorStrong` without `prop:dirac-stability`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
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

/-! ### Closeness in `d_K` preserves strong-packet limits -/

section Close

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

theorem tendsto_dKComp {Q : ChartBox T} {z w : ℕ → SmoothFields T left}
    {θ θw : ℕ → CoefficientBank Ysec}
    (h : Tendsto (fun n => dK Q (z n) (θ n) (w n) (θw n)) atTop (𝓝 0)) (i : Fin 8) :
    Tendsto (fun n => dKComp Q (z n) (w n) i) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => dKComp_le_dK Q _ _ _ _ i

/-- **A sequence `d_K`-close to a strong-packet convergent sequence converges to the same
strong-packet limit** on the chart box (given its own coframe bound). -/
theorem StrongPacketOn.of_close {Q : ChartBox T} {w z : ℕ → SmoothFields T left}
    {θw θ : ℕ → CoefficientBank Ysec} {L : LimitFields C} (h : StrongPacketOn Q w L)
    (hclose : Tendsto (fun n => dK Q (z n) (θ n) (w n) (θw n)) atTop (𝓝 0))
    (hbound : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
      eLpNorm (z n).z.e ⊤ Q.μ + eLpNorm (fun x => coframeInv ((z n).z.e x)) ⊤ Q.μ ≤ B) :
    StrongPacketOn Q z L := by
  have c := tendsto_dKComp hclose
  have mLe := (h.coframe_mem).aesm Q
  have mLde := (h.coframe_mem).aesm_grad Q
  have mLΨ := (h.spinor_mem).aesm Q
  have mLdΨ := (h.spinor_mem).aesm_grad Q
  have mLΨb := (h.cospinor_mem).aesm Q
  have mLdΨb := (h.cospinor_mem).aesm_grad Q
  exact
    { coframe_Linfty := tendsto_zero_of_le_add (fun n => eLpNorm_top_sub_le_add) (c 0)
        h.coframe_Linfty
      coframe_mem := h.coframe_mem
      coframe_H1 := tendsto_zero_of_le_add (fun n => h1Norm_sub_le_add
        (((z n).memH1_e Q).aesm Q) (((w n).memH1_e Q).aesm Q) mLe
        (((z n).memH1_e Q).aesm_grad Q) (((w n).memH1_e Q).aesm_grad Q) mLde) (c 1)
        h.coframe_H1
      coframe_bound := hbound
      limit_chart := h.limit_chart
      conn_lie := h.conn_lie
      conn_mem := h.conn_mem
      conn_tendsto := tendsto_zero_of_le_add (fun n => eLpNorm_sub_le_add (by norm_num)
        ((z n).aesm_A Q) ((w n).aesm_A Q) h.conn_mem.1) (c 2) h.conn_tendsto
      curv_mem := h.curv_mem
      curv_weak := h.curv_weak
      curv_tendsto := tendsto_zero_of_le_add (fun n => eLpNorm_sub_le_add (by norm_num)
        ((z n).aesm_F Q) ((w n).aesm_F Q) h.curv_mem.1) (c 3) h.curv_tendsto
      higgs_mem := h.higgs_mem
      higgs_tendsto := tendsto_zero_of_le_add (fun n => eLpNorm_sub_le_add (by norm_num)
        ((z n).aesm_H Q) ((w n).aesm_H Q) h.higgs_mem.1) (c 4) h.higgs_tendsto
      covgrad_mem := h.covgrad_mem
      covgrad_weak := h.covgrad_weak
      covgrad_tendsto := tendsto_zero_of_le_add (fun n => eLpNorm_sub_le_add (by norm_num)
        ((z n).aesm_K Q) ((w n).aesm_K Q) h.covgrad_mem.1) (c 5) h.covgrad_tendsto
      spinor_mem := h.spinor_mem
      spinor_tendsto := tendsto_zero_of_le_add (fun n => h1Norm_sub_le_add
        (((z n).memH1_Ψ Q).aesm Q) (((w n).memH1_Ψ Q).aesm Q) mLΨ
        (((z n).memH1_Ψ Q).aesm_grad Q) (((w n).memH1_Ψ Q).aesm_grad Q) mLdΨ) (c 6)
        h.spinor_tendsto
      cospinor_mem := h.cospinor_mem
      cospinor_tendsto := tendsto_zero_of_le_add (fun n => h1Norm_sub_le_add
        (((z n).memH1_Ψb Q).aesm Q) (((w n).memH1_Ψb Q).aesm Q) mLΨb
        (((z n).memH1_Ψb Q).aesm_grad Q) (((w n).memH1_Ψb Q).aesm_grad Q) mLdΨb) (c 7)
        h.cospinor_tendsto }

/-- Bank convergence transfers along vanishing `d_K`. -/
theorem bankTendsto_of_close {Q : ChartBox T} {w z : ℕ → SmoothFields T left}
    {θw θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec} (h : BankTendsto θw θ₀)
    (hclose : Tendsto (fun n => dK Q (z n) (θ n) (w n) (θw n)) atTop (𝓝 0)) :
    BankTendsto θ θ₀ := by
  rw [bankTendsto_iff_vec] at h ⊢
  rw [tendsto_iff_edist_tendsto_0] at h ⊢
  exact tendsto_zero_of_le_add (fun n => edist_triangle _ (bankVec (θw n)) _)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hclose (fun _ => zero_le)
      fun n => edist_bank_le_dK Q _ _ _ _) h

/-- **Uniqueness of strong-packet limits** (a.e. on every chart box, banks equal), under the
coframe chart condition and compact banks. -/
theorem StrongPacket.unique {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    {L L' : LimitFields C} {θ₀ θ₀' : CoefficientBank Ysec}
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P) (h : StrongPacket z θ L θ₀)
    (h' : StrongPacket z θ L' θ₀') :
    (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' :=
  ⟨fun Q => ((h.local_conv Q).toReduced (hch Q) hbank h.bank_tendsto).unique
    ((h'.local_conv Q).toReduced (hch Q) hbank h'.bank_tendsto),
    tendsto_nhds_unique h.bank_tendsto h'.bank_tendsto⟩

end Close

/-! ### `prop:cofinal-transport` -/

section Transport

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {Ysec : Type} [Fintype Ysec]

/-- Strong-packet convergence on a chart box passes to subsequences. -/
theorem StrongPacketOn.comp {Q : ChartBox T} {z : ℕ → SmoothFields T left} {L : LimitFields C}
    (h : StrongPacketOn Q z L) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    StrongPacketOn Q (fun k => z (ψ k)) L :=
  { h with
    coframe_Linfty := h.coframe_Linfty.comp hψ
    coframe_H1 := h.coframe_H1.comp hψ
    coframe_bound := by
      obtain ⟨B, hB, hBn⟩ := h.coframe_bound
      exact ⟨B, hB, fun k => hBn _⟩
    conn_tendsto := h.conn_tendsto.comp hψ
    curv_tendsto := h.curv_tendsto.comp hψ
    higgs_tendsto := h.higgs_tendsto.comp hψ
    covgrad_tendsto := h.covgrad_tendsto.comp hψ
    spinor_tendsto := h.spinor_tendsto.comp hψ
    cospinor_tendsto := h.cospinor_tendsto.comp hψ }

/-- The classical strong packet passes to subsequences. -/
theorem StrongPacket.comp {z : ℕ → SmoothFields T left} {θ : ℕ → CoefficientBank Ysec}
    {L : LimitFields C} {θ₀ : CoefficientBank Ysec} (h : StrongPacket z θ L θ₀) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) : StrongPacket (fun k => z (ψ k)) (fun k => θ (ψ k)) L θ₀ := by
  obtain ⟨c, hc, hcθ⟩ := h.bank_pos
  exact ⟨fun Q => (h.local_conv Q).comp hψ, h.bank_tendsto.comp hψ, c, hc, fun k => hcθ _⟩

/-- Summable transport makes the spinors Cauchy in `H¹` on every chart box. -/
theorem SummableTransport.spinorH1Cauchy {Q : ChartBox T} {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (h : SummableTransport Q z θ) : SpinorH1Cauchy Q z := by
  have hC := dK_cauchy Q h
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · obtain ⟨N, hN⟩ := hC (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    exact ⟨N, fun m hm n hn => (dKComp_le_dK Q (z m) (θ m) (z n) (θ n) 6).trans (hN m hm n hn)⟩
  · obtain ⟨N, hN⟩ := hC (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    exact ⟨N, fun m hm n hn => (dKComp_le_dK Q (z m) (θ m) (z n) (θ n) 7).trans (hN m hm n hn)⟩

/-- **`prop:cofinal-transport` (summable cofinal transport).**  Let a cofinal sequence of smooth
reconstructed fields satisfy the classical compactness certificate (either spinor route) and the
coframe chart condition on every chart box, and the summable transport
`d_K(z_{h_{n+1}}, z_{h_n}) ≤ η_{n,K}`, `Σ_n η_{n,K} < ∞`, on every chart box.  Then the sequence is
Cauchy in each norm entering `d_K`, and it converges (the **whole** sequence, no extraction) to a
local strong-packet limit `(z, θ)` (`StrongPacket`: the curvature and covariant Higgs derivative of
the limit are identified with the limit connection), which is unique (a.e. on every chart box,
bank equal).  The `H¹` compactness of the spinors is supplied by the transport itself, so route
(C4b) does not require `prop:dirac-stability` here. -/
theorem cofinal_transport (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (htr : ∀ Q : ChartBox T, SummableTransport Q z θ) :
    (∀ Q : ChartBox T, ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      (∀ i, dKComp Q (z m) (z n) i ≤ ε) ∧ edist (bankVec (θ m)) (bankVec (θ n)) ≤ ε) ∧
    ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec), StrongPacket z θ L θ₀ ∧
      (∀ Q : ChartBox T, ReducedConvergence Q z θ L θ₀) ∧
      ∀ (L' : LimitFields C) (θ₀' : CoefficientBank Ysec), StrongPacket z θ L' θ₀' →
        (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' := by
  have hC := fun Q => dK_cauchy Q (htr Q)
  have hsp : ∀ Q : ChartBox T, SpinorStrongRoute Q z := fun Q =>
    (htr Q).spinorH1Cauchy.spinorStrongRoute
  obtain ⟨ψ, hψ, L, θ₀, hSP, -⟩ :=
    certificate_packet_of_spinorStrong hT hcert hch hsp id strictMono_id
  have hclose : ∀ Q : ChartBox T,
      Tendsto (fun n => dK Q (z n) (θ n) (z (ψ n)) (θ (ψ n))) atTop (𝓝 0) := by
    intro Q
    refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC Q ε hε
    exact eventually_atTop.mpr ⟨N, fun n hn => hN n hn (ψ n) (hn.trans (hψ.id_le n))⟩
  obtain ⟨P, hP, hθP⟩ := (hcert (midChart hT)).bank_compact
  have hbank : ∃ P, IsCompactBankSet P ∧ ∀ n, θ n ∈ P := ⟨P, hP, hθP⟩
  obtain ⟨c, hc, hcθ⟩ := exists_bank_lower hP hθP
  have hSPz : StrongPacket z θ L θ₀ := by
    refine ⟨fun Q => ?_, bankTendsto_of_close hSP.bank_tendsto (hclose (midChart hT)), c, hc, hcθ⟩
    obtain ⟨Ke, hKe, hKn⟩ := hch Q
    exact (hSP.local_conv Q).of_close (hclose Q) (coframe_bound_of_chart hKe hKn)
  refine ⟨fun Q ε hε => ?_, L, θ₀, hSPz, fun Q => (hSPz.local_conv Q).toReduced (hch Q) hbank
    hSPz.bank_tendsto, fun L' θ₀' h' => StrongPacket.unique hch hbank hSPz h'⟩
  obtain ⟨N, hN⟩ := hC Q ε hε
  exact ⟨N, fun m hm n hn => ⟨fun i => (dKComp_le_dK Q _ _ _ _ i).trans (hN m hm n hn),
    (edist_bank_le_dK Q _ _ _ _).trans (hN m hm n hn)⟩⟩

/-- **Route independence** (`prop:cofinal-transport`, second assertion): if two cofinal routes
converge in the strong packet and admit direct comparisons whose `d_K` error tends to zero once
both cutoffs pass a common scale, their limits agree (a.e. on every chart box, banks equal). -/
theorem cofinal_route_independence (hT : 0 < T) {z z' : ℕ → SmoothFields T left}
    {θ θ' : ℕ → CoefficientBank Ysec} (hch' : ∀ Q : ChartBox T, CoframeChartCondition Q z')
    (hbank' : ∃ P, IsCompactBankSet P ∧ ∀ n, θ' n ∈ P)
    (hcmp : ∀ Q : ChartBox T, ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      dK Q (z m) (θ m) (z' n) (θ' n) ≤ ε)
    {L L' : LimitFields C} {θ₀ θ₀' : CoefficientBank Ysec} (h : StrongPacket z θ L θ₀)
    (h' : StrongPacket z' θ' L' θ₀') :
    (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' := by
  have hclose : ∀ Q : ChartBox T,
      Tendsto (fun n => dK Q (z' n) (θ' n) (z n) (θ n)) atTop (𝓝 0) := by
    intro Q
    refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hcmp Q ε hε
    exact eventually_atTop.mpr ⟨N, fun n hn => by rw [dK_comm]; exact hN n hn n hn⟩
  have hz' : StrongPacket z' θ' L θ₀ := by
    refine ⟨fun Q => ?_, bankTendsto_of_close h.bank_tendsto (hclose (midChart hT)),
      h'.bank_pos⟩
    obtain ⟨Ke, hKe, hKn⟩ := hch' Q
    exact (h.local_conv Q).of_close (hclose Q) (coframe_bound_of_chart hKe hKn)
  exact StrongPacket.unique hch' hbank' hz' h'

/-- **No subsequence choice remains** (`prop:cofinal-transport`, "in particular"): under the
hypotheses of `cofinal_transport`, the whole sequence has a strong-packet limit and every
subsequential strong-packet limit (as supplied by `thm:certificate-packet`) coincides with it. -/
theorem cofinal_subseq_limit_eq (hT : 0 < T) {z : ℕ → SmoothFields T left}
    {θ : ℕ → CoefficientBank Ysec} (hcert : ∀ Q : ChartBox T, CompactnessCertificate Q z θ)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q z)
    (htr : ∀ Q : ChartBox T, SummableTransport Q z θ) :
    ∃ (L : LimitFields C) (θ₀ : CoefficientBank Ysec), StrongPacket z θ L θ₀ ∧
      ∀ (σ : ℕ → ℕ), StrictMono σ → ∀ (L' : LimitFields C) (θ₀' : CoefficientBank Ysec),
        StrongPacket (fun k => z (σ k)) (fun k => θ (σ k)) L' θ₀' →
          (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' := by
  obtain ⟨-, L, θ₀, h, -, -⟩ := cofinal_transport hT hcert hch htr
  obtain ⟨P, hP, hθP⟩ := (hcert (midChart hT)).bank_compact
  refine ⟨L, θ₀, h, fun σ hσ L' θ₀' h' => ?_⟩
  refine StrongPacket.unique (z := fun k => z (σ k)) (fun Q => ?_) ⟨P, hP, fun k => hθP _⟩
    (h.comp hσ.tendsto_atTop) h'
  obtain ⟨Ke, hKe, hKn⟩ := hch Q
  exact ⟨Ke, hKe, fun k => hKn _⟩

end Transport

/-! ### `cor:cofinal-unique` -/

section CofinalUnique

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **Cofinal uniqueness, core form** (stationarity `ε_h(K) → 0` as hypothesis). -/
theorem cofinal_unique_of_stationary (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous)
    (htr : ∀ Q : ChartBox T, SummableTransport Q reg.fields reg.bank) :
    ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec), θ₀ ∈ physicalBanks ∧
      StrongPacket reg.fields reg.bank L θ₀ ∧
      FirstVariationsConverge FC reg.r0 reg.fields reg.bank L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      ∀ (L' : LimitFields FC.C) (θ₀' : CoefficientBank Ysec),
        StrongPacket reg.fields reg.bank L' θ₀' →
          (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' := by
  obtain ⟨-, L, θ₀, hSP, hRC, huniq⟩ := cofinal_transport hT hcert hch htr
  have hcl := closure_along reg (σ := id) tendsto_id
    (fun t₀ t₁ h0 h01 h1 => hRC (slabChart t₀ t₁ h0 h01 h1)) hcons hstat hyuk
  exact ⟨L, θ₀, hSP.limit_bank_physical, hSP, hcl.1, hcl.2.1, hcl.2.2, huniq⟩

/-- **`cor:cofinal-unique` (cofinal uniqueness and route independence).**  Under the hypotheses of
`thm:main-limit` (compactness certificate with either spinor route and the coframe chart condition
on every chart box, `c_h(K) → 0`, the source bounds of `prop:source-bound` with
`L_h√R_h + e_h(K) → 0`, continuity of the Yukawa map), let the cofinal sequence additionally
satisfy the summable transport estimate on every chart box.  Then the **entire** cofinal sequence
converges in the strong-packet topology to a single limit `(z, θ)`, which is a classical
Einstein–Standard-Model solution (first variations converge, all Euler rows vanish,
`eq:Einstein-SM`); the limit is unique; and any second admissible route `reg'` whose direct
comparisons with `reg` have vanishing `d_K` error has the same limit. -/
theorem cofinal_unique (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesCompactnessCertificate Q)
    (hch : ∀ Q : ChartBox T, CoframeChartCondition Q reg.fields)
    (hcons : reg.FirstVariationConsistent) {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ}
    {e : CylRegion T → ℕ → ℝ} {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBounds reg W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0))
    (hyuk : FC.YukawaContinuous)
    (htr : ∀ Q : ChartBox T, SummableTransport Q reg.fields reg.bank) :
    ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec), θ₀ ∈ physicalBanks ∧
      StrongPacket reg.fields reg.bank L θ₀ ∧
      FirstVariationsConverge FC reg.r0 reg.fields reg.bank L θ₀ ∧
      IsDistributionalSolution (T := T) FC reg.r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC reg.r0 L θ₀ ∧
      (∀ (L' : LimitFields FC.C) (θ₀' : CoefficientBank Ysec),
        StrongPacket reg.fields reg.bank L' θ₀' →
          (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀') ∧
      ∀ (reg' : RegulatorSequence T FC),
        (∀ Q : ChartBox T, CoframeChartCondition Q reg'.fields) →
        (∃ P, IsCompactBankSet P ∧ ∀ n, reg'.bank n ∈ P) →
        (∀ Q : ChartBox T, ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          dK Q (reg.fields m) (reg.bank m) (reg'.fields n) (reg'.bank n) ≤ ε) →
        ∀ (L' : LimitFields FC.C) (θ₀' : CoefficientBank Ysec),
          StrongPacket reg'.fields reg'.bank L' θ₀' →
            (∀ Q : ChartBox T, LimitFields.AEEqOn Q L L') ∧ bankCoords θ₀ = bankCoords θ₀' := by
  obtain ⟨L, θ₀, h1, h2, h3, h4, h5, h6⟩ := cofinal_unique_of_stationary hT reg hcert hch hcons
    (physicallyStationary_of_source hsrc hvan) hyuk htr
  exact ⟨L, θ₀, h1, h2, h3, h4, h5, h6, fun reg' hch' hbank' hcmp L' θ₀' h' =>
    cofinal_route_independence hT hch' hbank' hcmp h2 h'⟩

end CofinalUnique

/-! ### `cor:random-realization` -/

section Random

/-- **Tonelli step**: `Σ_h L_h² 𝔼 X_h² < ∞` gives `Σ_h L_h² X_h² < ∞` almost surely
(`lintegral_tsum`, no independence). -/
theorem ae_tsum_sq_ne_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (Lc : ℕ → ℝ)
    (hsum : ∑' n, ENNReal.ofReal (Lc n ^ 2) * ∫⁻ ξ, ENNReal.ofReal (X n ξ ^ 2) ∂P ≠ ⊤) :
    ∀ᵐ ξ ∂P, ∑' n, ENNReal.ofReal ((Lc n * X n ξ) ^ 2) ≠ ⊤ := by
  have hm : ∀ n, AEMeasurable (fun ξ => ENNReal.ofReal ((Lc n * X n ξ) ^ 2)) P := fun n =>
    (((hX n).const_mul (Lc n)).pow_const 2).ennreal_ofReal
  have e : ∑' n, ∫⁻ ξ, ENNReal.ofReal ((Lc n * X n ξ) ^ 2) ∂P =
      ∑' n, ENNReal.ofReal (Lc n ^ 2) * ∫⁻ ξ, ENNReal.ofReal (X n ξ ^ 2) ∂P := by
    congr 1
    funext n
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext ξ
    rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have hint : ∫⁻ ξ, ∑' n, ENNReal.ofReal ((Lc n * X n ξ) ^ 2) ∂P ≠ ⊤ := by
    rw [lintegral_tsum hm, e]
    exact hsum
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) hint] with ξ hξ
  exact hξ.ne

/-- A real sequence with `Σ y_n² < ∞` tends to zero. -/
theorem tendsto_zero_of_tsum_sq_ne_top {y : ℕ → ℝ} (h : ∑' n, ENNReal.ofReal (y n ^ 2) ≠ ⊤) :
    Tendsto y atTop (𝓝 0) := by
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
  have h2 : Tendsto (fun n => y n ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun n => Real.sqrt (y n ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Real.sqrt_sq_eq_abs] at h3
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h3)

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **`cor:random-realization` (a realized random branch).**  On a common probability space let
the reconstructed fields satisfy, almost surely, the compactness and consistency hypotheses of
`thm:main-limit` (compactness certificate with either spinor route and the coframe chart condition
on every chart box, `c_h(K) → 0`) and the cofinal-transport hypothesis of `cor:cofinal-unique`
(summable transport on every chart box).  Let the source estimate of `prop:source-bound` hold
pathwise, with random covectors `a_h(ξ)` (`R_h(ξ) = ‖a_h(ξ)‖²_{G_h^{-1}}`), random source lifts,
deterministic `L_h` and deterministic `e_h(K) → 0`, and assume
`Σ_h L_h² 𝔼‖a_h‖²_{G_h^{-1}} < ∞`.  Then almost surely the whole cofinal sequence converges in the
strong packet to a limit `z(ξ)` which satisfies all matter Euler equations and `eq:Einstein-SM`.
No independence is used. -/
theorem random_realization (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (reg : Ω → RegulatorSequence T FC)
    (hyp : ∀ᵐ ξ ∂P, (∀ Q : ChartBox T, (reg ξ).SatisfiesCompactnessCertificate Q) ∧
      (∀ Q : ChartBox T, CoframeChartCondition Q (reg ξ).fields) ∧
      (reg ξ).FirstVariationConsistent ∧
      ∀ Q : ChartBox T, SummableTransport Q (reg ξ).fields (reg ξ).bank)
    {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)]
    (a : Ω → ∀ n, W n →L[ℝ] ℝ) (Lc : ℕ → ℝ) (e : CylRegion T → ℕ → ℝ)
    (he : ∀ K, Tendsto (e K) atTop (𝓝 0))
    (vh : ∀ ξ n (K : CylRegion T), CrTest FC.left (reg ξ).r0 K → W n)
    (hsrc : ∀ᵐ ξ ∂P, SourceBounds (reg ξ) W (a ξ) (fun n => ‖a ξ n‖ ^ 2) Lc e (vh ξ))
    (hmeas : ∀ n, AEMeasurable (fun ξ => ‖a ξ n‖) P)
    (hsum : ∑' n, ENNReal.ofReal (Lc n ^ 2) * ∫⁻ ξ, ENNReal.ofReal (‖a ξ n‖ ^ 2) ∂P ≠ ⊤)
    (hyuk : FC.YukawaContinuous) :
    ∀ᵐ ξ ∂P, ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (reg ξ).fields (reg ξ).bank L θ₀ ∧
      IsDistributionalSolution (T := T) FC (reg ξ).r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC (reg ξ).r0 L θ₀ := by
  filter_upwards [hyp, hsrc, ae_tsum_sq_ne_top (X := fun n ξ => ‖a ξ n‖) hmeas Lc hsum] with
    ξ ⟨hc, hch, hcons, htr⟩ hs hξ
  have hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (‖a ξ n‖ ^ 2) + e K n) atTop (𝓝 0) := by
    intro K
    have hy := tendsto_zero_of_tsum_sq_ne_top (y := fun n => Lc n * ‖a ξ n‖) hξ
    simpa [Real.sqrt_sq (norm_nonneg _)] using hy.add (he K)
  obtain ⟨L, θ₀, -, hSP, -, h4, h5, -⟩ := cofinal_unique hT (reg ξ) hc hch hcons hs hvan hyuk htr
  exact ⟨L, θ₀, hSP, h4, h5⟩

end Random

/-! ### Non-vacuity: the flat regulator -/

section FlatNonVacuity

variable {T : ℝ}

/-- The flat regulator satisfies the summable transport on every chart box (`d_K = 0`). -/
theorem flatRegulator_summableTransport (Q : ChartBox T) :
    SummableTransport Q (flatRegulator T).fields (flatRegulator T).bank := by
  refine ⟨fun _ => 0, by simp, fun n => ?_⟩
  have h1 : (flatRegulator T).fields (n + 1) = (flatRegulator T).fields n := rfl
  have h2 : (flatRegulator T).bank (n + 1) = (flatRegulator T).bank n := rfl
  rw [h1, h2, dK_self]

/-- **Non-vacuity of `prop:cofinal-transport`.** -/
example (hT : 0 < T) :=
  cofinal_transport hT (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) flatRegulator_summableTransport

/-- **Non-vacuity of `cor:cofinal-unique`.** -/
example (hT : 0 < T) :=
  cofinal_unique hT (flatRegulator T) (fun Q => flatRegulator_compactnessCertificate T Q)
    (flatRegulator_coframeChart T) (flatRegulator_consistent hT) flatRegulator_sourceBounds
    (fun K => by simp) (trivialCarrier_yukawaContinuous Unit) flatRegulator_summableTransport

/-- **Non-vacuity of `cor:random-realization`**: the constant random flat regulator on a
one-point probability space satisfies every hypothesis. -/
example (hT : 0 < T) :=
  random_realization (P := Measure.dirac ()) hT (fun _ : Unit => flatRegulator T)
    (ae_of_all _ fun _ => ⟨fun Q => flatRegulator_compactnessCertificate T Q,
      flatRegulator_coframeChart T, flatRegulator_consistent hT, flatRegulator_summableTransport⟩)
    (W := fun _ => ℝ) (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => tendsto_const_nhds)
    (fun _ _ _ _ => 0)
    (ae_of_all _ fun _ => ⟨fun n => le_rfl, fun n K v => by simp, fun n K v => by
      have h0 : (flatRegulator T).lift n K v = 0 := rfl
      rw [h0]; simp⟩)
    (fun _ => aemeasurable_const) (by simp) (trivialCarrier_yukawaContinuous Unit)

end FlatNonVacuity

/-! ### Continuity of the first variation of smooth fields in the test -/

section TestContinuity

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {r : ℕ} {K : CylRegion T}

theorem pd_sub_field {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F}
    {x : E4} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (f - g) i x = pd f i x - pd g i x := by
  unfold pd
  rw [fderiv_sub hf hg]
  rfl

/-- The test jet is additive: `testJet(v - w) = testJet v - testJet w`. -/
theorem testJet_sub (v w : CrTest left r K) (x : E4) :
    testJet (v - w).val x = testJet v.val x - testJet w.val x := by
  have d : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      IsCylTest K f → DifferentiableAt ℝ f x := fun hf =>
    (hf.smooth.differentiable (by simp)) x
  have he := pd_sub_field (d (isCylTest_e v)) (d (isCylTest_e w))
  have hA := pd_sub_field (d (isCylTest_A v)) (d (isCylTest_A w))
  have hH := pd_sub_field (d (isCylTest_H v)) (d (isCylTest_H w))
  have hΨ := pd_sub_field (d (isCylTest_Ψ v)) (d (isCylTest_Ψ w))
  have hΨb := pd_sub_field (d (isCylTest_Ψb v)) (d (isCylTest_Ψb w))
  have hv : (v - w).val = v.val - w.val := rfl
  rw [hv]
  change RJet.mk ((v.val.e - w.val.e) x) (fun i => pd (v.val.e - w.val.e) i x)
    ((v.val.A - w.val.A) x) (fun i => pd (v.val.A - w.val.A) i x) ((v.val.H - w.val.H) x)
    (fun i => pd (v.val.H - w.val.H) i x) ((v.val.Ψ - w.val.Ψ) x)
    (fun i => pd (v.val.Ψ - w.val.Ψ) i x) ((v.val.Ψb - w.val.Ψb) x)
    (fun i => pd (v.val.Ψb - w.val.Ψb) i x) = _
  simp only [he, hA, hH, hΨ, hΨb, Pi.sub_apply]
  rfl

/-- **The covector functional of smooth fields is Lipschitz in the test.**  If `Cov R T' =
DG(R)[redVar R T']` for a `C¹` density `G` on the nondegenerate jet chart and the jet `J` is
continuous on the closure of a chart box with values in the chart, then
`v ↦ ∫_Q Cov(J x)(testJet v x)` is continuous on `𝒱_K^r` (`r ≥ 1`). -/
theorem continuous_cov_functional (hr : 1 ≤ r) (Q : ChartBox T) {J : E4 → RJet C}
    (hJ : ContinuousOn J (closure Q.set)) (hJGL : ∀ x ∈ closure Q.set, J x ∈ jetGL C)
    {G : RJet C → ℝ} (hG : ContDiffOn ℝ 1 G (jetGL C)) {Cov : RJet C → RJet C →L[ℝ] ℝ}
    (hCov : ∀ R ∈ jetGL C, ∀ T', fderiv ℝ G R (redVar R T') = Cov R T') :
    Continuous (fun v : CrTest left r K => ∫ x in Q.set, Cov (J x) (testJet v.val x)) := by
  set Φ : RJet C × RJet C → ℝ := fun p => fderiv ℝ G p.1 (redVar p.1 p.2) with hΦ
  have hdG : ContinuousOn (fun R => fderiv ℝ G R) (jetGL C) :=
    hG.continuousOn_fderiv_of_isOpen isOpen_jetGL le_rfl
  have hΦc : ContinuousOn Φ (jetGL C ×ˢ univ) := by
    refine ContinuousOn.clm_apply (hdG.comp continuousOn_fst fun p hp => hp.1) ?_
    exact continuous_redVar.continuousOn
  have hKc : IsCompact (J '' closure Q.set) := Q.isCompact_closure.image_of_continuousOn hJ
  obtain ⟨M₀, hM₀⟩ := (hKc.prod (isCompact_closedBall (0 : RJet C) 1)).exists_bound_of_continuousOn
    (hΦc.mono fun p hp => ⟨by obtain ⟨x, hx, hxp⟩ := hp.1; rw [← hxp]; exact hJGL x hx,
      mem_univ _⟩)
  set M := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  -- the operator bound on the chart image
  have hbound : ∀ x ∈ closure Q.set, ∀ T' : RJet C, |Cov (J x) T'| ≤ M * ‖T'‖ := by
    intro x hx T'
    rcases eq_or_ne T' 0 with h0 | h0
    · simp [h0]
    · have hn : 0 < ‖T'‖ := norm_pos_iff.mpr h0
      set T'' := ‖T'‖⁻¹ • T'
      have hT'' : ‖T''‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 : |Cov (J x) T''| ≤ M := by
        rw [← hCov _ (hJGL x hx)]
        have := hM₀ (J x, T'') ⟨mem_image_of_mem J hx, by simp [hT'']⟩
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      have e : Cov (J x) T' = ‖T'‖ * Cov (J x) T'' := by
        simp only [T'', map_smul, smul_eq_mul]
        field_simp
      rw [e, abs_mul, abs_norm, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 hn.le
  -- the integrands
  set f : CrTest left r K → E4 → ℝ := fun v x => Cov (J x) (testJet v.val x) with hf
  have hfΦ : ∀ v, ∀ x ∈ closure Q.set, f v x = Φ (J x, testJet v.val x) := fun v x hx =>
    (hCov _ (hJGL x hx) _).symm
  have hfc : ∀ v, ContinuousOn (f v) Q.set := by
    intro v
    refine (ContinuousOn.congr (f := fun x => Φ (J x, testJet v.val x)) ?_ fun x hx =>
      hfΦ v x (subset_closure hx))
    refine hΦc.comp ((hJ.mono subset_closure).prodMk (continuous_testJet v).continuousOn)
      fun x hx => ⟨hJGL x (subset_closure hx), mem_univ _⟩
  have hfint : ∀ v, Integrable (f v) Q.μ := by
    intro v
    refine Integrable.mono' (integrable_const (M * ‖v‖))
      ((hfc v).aestronglyMeasurable Q.isOpen.measurableSet) ?_
    filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    exact (hbound x (subset_closure hx) _).trans
      (mul_le_mul_of_nonneg_left (norm_testJet_le hr v x) hM0)
  have hvol : volume Q.set < ⊤ := Q.volume_ne_top.lt_top
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (M * volume.real Q.set))
    fun v w => ?_).continuous
  rw [Real.dist_eq, ← integral_sub (hfint v) (hfint w), dist_eq_norm,
    Real.coe_toNNReal _ (mul_nonneg hM0 measureReal_nonneg)]
  have hle : ∀ x ∈ Q.set, ‖f v x - f w x‖ ≤ M * ‖v - w‖ := by
    intro x hx
    simp only [hf]
    rw [← map_sub, ← testJet_sub, Real.norm_eq_abs]
    exact (hbound x (subset_closure hx) _).trans
      (mul_le_mul_of_nonneg_left (norm_testJet_le hr (v - w) x) hM0)
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol hle
  rw [← Real.norm_eq_abs]
  calc ‖∫ x in Q.set, (f v x - f w x)‖ ≤ M * ‖v - w‖ * volume.real Q.set := this
    _ = M * volume.real Q.set * ‖v - w‖ := by ring

end TestContinuity

/-! ### Hypotheses on a dense test core (`cor:random-realization`, last sentence) -/

section Core

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- **Continuity of the reconstructed first variation in the test.**  For smooth reconstructed
fields whose coframe takes values a.e. in a compact subset of the coframe chart on a slab chart
containing the time support of `K`, the complete first variation `v ↦ D𝒮_θ(z)[v]` is continuous
on `𝒱_K^r` (`r ≥ 1`). -/
theorem continuous_firstVariation (θ : CoefficientBank Ysec) {t₀ t₁ : ℝ} (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h1 : t₁ < T) {K : CylRegion T} (hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁)
    {r : ℕ} (hr : 1 ≤ r) (z : SmoothFields T FC.left) {Ke : Set CoframeFibre}
    (hKe : IsCompactCoframeSet Ke)
    (hzK : ∀ᵐ x ∂(slabChart t₀ t₁ h0 h01 h1 (T := T)).μ, z.z.e x ∈ Ke) :
    Continuous (fun v : CrTest FC.left r K => firstVariation T FC θ .gravity z.z v.val +
      firstVariation T FC θ .standardModel z.z v.val) := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
  have hcl : closure Q.set ⊆ cylSlab T := Q.closure_subset_cylSlab
  have hzK' : ∀ x ∈ closure Q.set, z.z.e x ∈ Ke :=
    forall_mem_of_ae_mem Q.isOpen (z.smooth_e.continuousOn.mono hcl) hKe.1.isClosed hzK
  have hGL : Ke ⊆ coframeGL := fun e he => coframeChart_subset_GL (hKe.2 he)
  have hJ : ContinuousOn (redJet z.z) (closure Q.set) := (continuousOn_redJet z).mono hcl
  have hJGL : ∀ x ∈ closure Q.set, redJet z.z x ∈ jetGL FC.C := fun x hx => hGL (hzK' x hx)
  have hg := continuous_cov_functional (K := K) (left := FC.left) hr Q hJ hJGL
    (contDiffOn_gravPt θ) (fun R hR T' => fderiv_gravPt_redVar θ hR T')
  have hs := continuous_cov_functional (K := K) (left := FC.left) hr Q hJ hJGL
    (G := smPt FC θ) (Cov := fun R => bosonCov θ R + diracCov FC θ R)
    ((contDiffOn_bosonPt θ).add (contDiffOn_diracPt FC θ)) (fun R hR T' => by
      have hb := hasFDerivAt_bosonPt θ hR
      have hd := hasFDerivAt_diracPt FC θ hR
      rw [show smPt FC θ = fun R => bosonPt θ R + diracPt FC θ R from rfl,
        fderiv_fun_add hb.1 hd.1, ContinuousLinearMap.add_apply, hb.2, ← bosonCov_apply,
        fderiv_diracPt_redVar FC θ hR, ContinuousLinearMap.add_apply])
  refine (hg.add hs).congr fun v => ?_
  rw [gravVariation_eq_cov FC θ h0 h01 h1 hK z v hKe.1 hGL hzK',
    smVariation_eq_cov FC θ h0 h01 h1 (fun p hp => Ioo_subset_Icc_self (hK p hp)) z v hKe.1 hGL
      hzK']
  rfl

/-- The first-variation consistency defect `c_h(K)` with the supremum restricted to a test core
`S K ⊆ 𝒱_K`. -/
def coreConsistencyDefect (reg : RegulatorSequence T FC)
    (S : ∀ K : CylRegion T, Set (CrTest FC.left reg.r0 K)) (n : ℕ) (K : CylRegion T) : ℝ≥0∞ :=
  ∑ b : Sector, ⨆ (v : CrTest FC.left reg.r0 K) (_ : v ∈ S K) (_ : ‖v‖ ≤ 1),
    ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
      firstVariation T FC (reg.bank n) b (reg.fields n).z v.val|

/-- The hypotheses of `prop:source-bound` formulated on a test core `S K ⊆ 𝒱_K`. -/
def SourceBoundsOn (reg : RegulatorSequence T FC)
    (S : ∀ K : CylRegion T, Set (CrTest FC.left reg.r0 K)) (W : ℕ → Type)
    [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)] (a : ∀ n, W n →L[ℝ] ℝ)
    (R Lc : ℕ → ℝ) (e : CylRegion T → ℕ → ℝ)
    (vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n) : Prop :=
  (∀ n, ‖a n‖ ^ 2 ≤ R n) ∧ (∀ n K, ∀ v ∈ S K, ‖vh n K v‖ ≤ Lc n * ‖v‖) ∧
    ∀ n K, ∀ v ∈ S K,
      |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v) - a n (vh n K v)| ≤
        e K n * ‖v‖

/-- The consistency bound for a single core test of norm `≤ 1`. -/
theorem core_defect_bound (reg : RegulatorSequence T FC)
    (S : ∀ K : CylRegion T, Set (CrTest FC.left reg.r0 K)) (n : ℕ) (K : CylRegion T)
    (v : CrTest FC.left reg.r0 K) (hvS : v ∈ S K) (hv : ‖v‖ ≤ 1) :
    ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
        firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) -
      fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
        coreConsistencyDefect reg S n K := by
  have hb : ∀ b : Sector, ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K v) -
      firstVariation T FC (reg.bank n) b (reg.fields n).z v.val| ≤
      ⨆ (w : CrTest FC.left reg.r0 K) (_ : w ∈ S K) (_ : ‖w‖ ≤ 1),
        ENNReal.ofReal |reg.finiteSectorVariation n b (reg.lift n K w) -
          firstVariation T FC (reg.bank n) b (reg.fields n).z w.val| := fun b =>
    le_iSup_of_le v (le_iSup_of_le hvS (le_iSup_of_le hv le_rfl))
  rw [reg.fderiv_action_eq_sum]
  calc ENNReal.ofReal |(firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val +
          firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val) -
        (reg.finiteSectorVariation n .gravity (reg.lift n K v) +
          reg.finiteSectorVariation n .standardModel (reg.lift n K v))|
      ≤ ENNReal.ofReal (|reg.finiteSectorVariation n .gravity (reg.lift n K v) -
            firstVariation T FC (reg.bank n) .gravity (reg.fields n).z v.val| +
          |reg.finiteSectorVariation n .standardModel (reg.lift n K v) -
            firstVariation T FC (reg.bank n) .standardModel (reg.fields n).z v.val|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_sub_comm (reg.finiteSectorVariation n .gravity _),
          abs_sub_comm (reg.finiteSectorVariation n .standardModel _)]
        refine le_trans (le_of_eq ?_) (abs_add_le _ _)
        congr 1; ring
    _ ≤ _ := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        unfold coreConsistencyDefect
        have : (Finset.univ : Finset Sector) = {Sector.gravity, Sector.standardModel} := rfl
        rw [this, Finset.sum_pair (by decide)]
        exact add_le_add (hb .gravity) (hb .standardModel)

/-- The pointwise source bound on the core. -/
theorem core_source_bound {reg : RegulatorSequence T FC}
    {S : ∀ K : CylRegion T, Set (CrTest FC.left reg.r0 K)} {W : ℕ → Type}
    [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)] {a : ∀ n, W n →L[ℝ] ℝ}
    {R Lc : ℕ → ℝ} {e : CylRegion T → ℕ → ℝ}
    {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBoundsOn reg S W a R Lc e vh) (n : ℕ) (K : CylRegion T)
    (v : CrTest FC.left reg.r0 K) (hvS : v ∈ S K) :
    |fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)| ≤
      (Lc n * Real.sqrt (R n) + e K n) * ‖v‖ := by
  have hRnn : 0 ≤ R n := le_trans (sq_nonneg _) (hsrc.1 n)
  have hnorm : ‖a n‖ ≤ Real.sqrt (R n) := (Real.le_sqrt (norm_nonneg _) hRnn).2 (hsrc.1 n)
  have hcs : |a n (vh n K v)| ≤ ‖a n‖ * ‖vh n K v‖ := by
    rw [← Real.norm_eq_abs]
    exact (a n).le_opNorm _
  have h1 := hsrc.2.2 n K v hvS
  have h2 := hsrc.2.1 n K v hvS
  set Φ := fderiv ℝ (reg.iface n).action (reg.config n) (reg.lift n K v)
  calc |Φ| = |(Φ - a n (vh n K v)) + a n (vh n K v)| := by rw [sub_add_cancel]
    _ ≤ |Φ - a n (vh n K v)| + |a n (vh n K v)| := abs_add_le _ _
    _ ≤ e K n * ‖v‖ + Real.sqrt (R n) * (Lc n * ‖v‖) :=
        add_le_add h1 (hcs.trans (mul_le_mul hnorm h2 (norm_nonneg _) (Real.sqrt_nonneg _)))
    _ = (Lc n * Real.sqrt (R n) + e K n) * ‖v‖ := by ring

/-- **Closure with hypotheses on a dense test core.**  Along a subsequence with reduced convergence
on every slab chart, if the consistency defect restricted to a dense test core `S K` tends to zero
and the source bounds of `prop:source-bound` hold on the core with `L_h√R_h + e_h(K) → 0`, the
limit is a distributional solution of all Euler equations (the limit first variation vanishes on
the core, and it is continuous on `𝒱_K^{r₀}` as a locally uniform limit of the continuous
reconstructed first variations). -/
theorem closure_on_core (reg : RegulatorSequence T FC) {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    {L : LimitFields FC.C} {θ₀ : CoefficientBank Ysec}
    (hRC : ∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (σ k))
        (fun k => reg.bank (σ k)) L θ₀)
    (hyuk : FC.YukawaContinuous) (S : ∀ K : CylRegion T, Set (CrTest FC.left reg.r0 K))
    (hS : ∀ K, Dense (S K))
    (hcons : ∀ K, Tendsto (fun n => coreConsistencyDefect reg S n K) atTop (𝓝 0))
    {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)]
    {a : ∀ n, W n →L[ℝ] ℝ} {R Lc : ℕ → ℝ} {e : CylRegion T → ℕ → ℝ}
    {vh : ∀ n (K : CylRegion T), CrTest FC.left reg.r0 K → W n}
    (hsrc : SourceBoundsOn reg S W a R Lc e vh)
    (hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (R n) + e K n) atTop (𝓝 0)) :
    IsDistributionalSolution (T := T) FC reg.r0 L θ₀ := by
  intro K t₀ t₁ h0 h01 h1 hK
  have hr : 1 ≤ reg.r0 := le_trans (by norm_num) reg.four_le_r0
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQ
  set ℓ : CrTest FC.left reg.r0 K → ℝ := fun v =>
    gravLimitVariation FC θ₀ Q L v + smLimitVariation FC θ₀ Q L v with hℓ
  set ℓk : ℕ → CrTest FC.left reg.r0 K → ℝ := fun k v =>
    firstVariation T FC (reg.bank (σ k)) .gravity (reg.fields (σ k)).z v.val +
      firstVariation T FC (reg.bank (σ k)) .standardModel (reg.fields (σ k)).z v.val with hℓk
  obtain ⟨hyL, hy0⟩ := hyuk _ _ (hRC t₀ t₁ h0 h01 h1).bank_tendsto
  have hdual : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ v, |ℓk k v - ℓ v| ≤ ε * ‖v‖ := fun ε hε =>
    actionVariation_dual_tendsto FC h0 h01 h1 hK hr (hRC t₀ t₁ h0 h01 h1) hyL hy0 hε
  -- (A) the limit functional vanishes on the core
  have hA : ∀ v ∈ S K, ‖v‖ ≤ 1 → ℓ v = 0 := by
    intro v hvS hv
    refine abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (abs_nonneg _))
    have hδ3 : 0 < δ / 3 := by positivity
    have hc := ((hcons K).comp hσ).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ3))
    have hs := ((hvan K).comp hσ).eventually (Metric.ball_mem_nhds 0 hδ3)
    obtain ⟨k, hk1, hk2, hk3⟩ := ((hdual (δ / 3) hδ3).and (hc.and hs)).exists
    set Φ := fderiv ℝ (reg.iface (σ k)).action (reg.config (σ k)) (reg.lift (σ k) K v)
    have e1 : |ℓk k v - Φ| < δ / 3 :=
      (ENNReal.ofReal_lt_ofReal_iff hδ3).mp
        ((core_defect_bound reg S (σ k) K v hvS hv).trans_lt hk2)
    have hk3' : |Lc (σ k) * Real.sqrt (R (σ k)) + e K (σ k)| < δ / 3 := by
      simpa [Real.dist_eq] using hk3
    have e2 : |Φ| < δ / 3 := by
      refine (core_source_bound hsrc (σ k) K v hvS).trans_lt (lt_of_le_of_lt ?_ hk3')
      calc (Lc (σ k) * Real.sqrt (R (σ k)) + e K (σ k)) * ‖v‖
          ≤ |Lc (σ k) * Real.sqrt (R (σ k)) + e K (σ k)| * ‖v‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ |Lc (σ k) * Real.sqrt (R (σ k)) + e K (σ k)| :=
            mul_le_of_le_one_right (abs_nonneg _) hv
    have e3 := (hk1 v).trans (mul_le_of_le_one_right hδ3.le hv)
    have t1 := abs_sub_le (ℓ v) (ℓk k v) 0
    have t2 := abs_sub_le (ℓk k v) Φ 0
    rw [abs_sub_comm] at e3
    simp only [sub_zero] at t1 t2
    linarith
  -- (B) the limit functional is continuous
  have hcont : Continuous ℓ := by
    obtain ⟨Ke, hKe, hzKe, -⟩ := (hRC t₀ t₁ h0 h01 h1).coframe_chart
    refine TendstoLocallyUniformly.continuous (F := ℓk) (p := atTop) ?_
      (Frequently.of_forall (f := atTop) fun k =>
      continuous_firstVariation (reg.bank (σ k)) h0 h01 h1 hK hr (reg.fields (σ k)) hKe
        (hzKe k))
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε v₀
    refine ⟨Metric.ball v₀ 1, Metric.ball_mem_nhds v₀ one_pos, ?_⟩
    have hpos : 0 < ε / (‖v₀‖ + 2) := by positivity
    filter_upwards [hdual _ hpos] with k hk w hw
    rw [Real.dist_eq, abs_sub_comm]
    have hw' : ‖w‖ < ‖v₀‖ + 1 := by
      have h1 := norm_sub_norm_le w v₀
      have h2 : ‖w - v₀‖ < 1 := by rw [← dist_eq_norm]; exact hw
      linarith
    calc |ℓk k w - ℓ w| ≤ ε / (‖v₀‖ + 2) * ‖w‖ := hk w
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v₀, norm_nonneg w]
  -- (C) density and continuity
  have hclosed : IsClosed {v | ℓ v = 0} := isClosed_eq hcont continuous_const
  have hball : ∀ v ∈ Metric.ball (0 : CrTest FC.left reg.r0 K) 1, ℓ v = 0 := by
    intro v hv
    have hsub := (hS K).open_subset_closure_inter Metric.isOpen_ball hv
    refine closure_minimal (fun w hw => ?_) hclosed hsub
    exact hA w hw.2 (le_of_lt (mem_ball_zero_iff.mp hw.1))
  have hunit : ∀ v : CrTest FC.left reg.r0 K, ‖v‖ ≤ 1 → ℓ v = 0 := by
    intro v hv
    have hmem : v ∈ closure (Metric.ball (0 : CrTest FC.left reg.r0 K) 1) := by
      rw [closure_ball (0 : CrTest FC.left reg.r0 K) one_ne_zero]
      exact mem_closedBall_zero_iff.mpr hv
    exact closure_minimal hball hclosed hmem
  exact eq_zero_of_unit_of_homogeneous FC ℓ (fun c v => by
    simp only [hℓ, gravLimitVariation_smul, smLimitVariation_smul]; ring) hunit

/-- **`cor:random-realization`, hypotheses on a test core** ("it is enough to formulate the
hypotheses on a countable dense test core with the displayed uniform bounds"): as
`random_realization`, but with the first-variation consistency and the source bounds of
`prop:source-bound` required only for the tests of a dense core `S(ξ, K) ⊆ 𝒱_K` (in particular a
countable one), with the displayed uniform bounds `L_h‖v‖`, `e_h‖v‖`. -/
theorem random_realization_core (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (reg : Ω → RegulatorSequence T FC)
    (S : ∀ ξ (K : CylRegion T), Set (CrTest FC.left (reg ξ).r0 K)) (hS : ∀ ξ K, Dense (S ξ K))
    (hyp : ∀ᵐ ξ ∂P, (∀ Q : ChartBox T, (reg ξ).SatisfiesCompactnessCertificate Q) ∧
      (∀ Q : ChartBox T, CoframeChartCondition Q (reg ξ).fields) ∧
      (∀ K, Tendsto (fun n => coreConsistencyDefect (reg ξ) (S ξ) n K) atTop (𝓝 0)) ∧
      ∀ Q : ChartBox T, SummableTransport Q (reg ξ).fields (reg ξ).bank)
    {W : ℕ → Type} [∀ n, NormedAddCommGroup (W n)] [∀ n, InnerProductSpace ℝ (W n)]
    (a : Ω → ∀ n, W n →L[ℝ] ℝ) (Lc : ℕ → ℝ) (e : CylRegion T → ℕ → ℝ)
    (he : ∀ K, Tendsto (e K) atTop (𝓝 0))
    (vh : ∀ ξ n (K : CylRegion T), CrTest FC.left (reg ξ).r0 K → W n)
    (hsrc : ∀ᵐ ξ ∂P, SourceBoundsOn (reg ξ) (S ξ) W (a ξ) (fun n => ‖a ξ n‖ ^ 2) Lc e (vh ξ))
    (hmeas : ∀ n, AEMeasurable (fun ξ => ‖a ξ n‖) P)
    (hsum : ∑' n, ENNReal.ofReal (Lc n ^ 2) * ∫⁻ ξ, ENNReal.ofReal (‖a ξ n‖ ^ 2) ∂P ≠ ⊤)
    (hyuk : FC.YukawaContinuous) :
    ∀ᵐ ξ ∂P, ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      StrongPacket (reg ξ).fields (reg ξ).bank L θ₀ ∧
      IsDistributionalSolution (T := T) FC (reg ξ).r0 L θ₀ ∧
      SatisfiesEinsteinSM (T := T) FC (reg ξ).r0 L θ₀ := by
  filter_upwards [hyp, hsrc, ae_tsum_sq_ne_top (X := fun n ξ => ‖a ξ n‖) hmeas Lc hsum] with
    ξ ⟨hc, hch, hcons, htr⟩ hs hξ
  have hvan : ∀ K, Tendsto (fun n => Lc n * Real.sqrt (‖a ξ n‖ ^ 2) + e K n) atTop (𝓝 0) := by
    intro K
    have hy := tendsto_zero_of_tsum_sq_ne_top (y := fun n => Lc n * ‖a ξ n‖) hξ
    simpa [Real.sqrt_sq (norm_nonneg _)] using hy.add (he K)
  obtain ⟨-, L, θ₀, hSP, hRC, -⟩ := cofinal_transport hT hc hch htr
  have hsol := closure_on_core (reg ξ) (σ := id) tendsto_id
    (fun t₀ t₁ h0 h01 h1 => hRC (slabChart t₀ t₁ h0 h01 h1)) hyuk (S ξ) (hS ξ) hcons hs hvan
  exact ⟨L, θ₀, hSP, hsol, hsol.einstein⟩

end Core

/-! ### Non-vacuity of the core version -/

section CoreFlat

variable {T : ℝ}

/-- The flat regulator is consistent on every test core. -/
theorem flatRegulator_coreConsistent (hT : 0 < T)
    (S : ∀ K : CylRegion T, Set (CrTest (trivialCarrier Unit).left (flatRegulator T).r0 K))
    (K : CylRegion T) :
    Tendsto (fun n => coreConsistencyDefect (flatRegulator T) S n K) atTop (𝓝 0) := by
  have h : ∀ n, coreConsistencyDefect (flatRegulator T) S n K = 0 := by
    intro n
    simp only [coreConsistencyDefect]
    refine Finset.sum_eq_zero fun b _ => le_antisymm
      (iSup_le fun v => iSup_le fun _ => iSup_le fun _ => ?_) zero_le
    have h0 : (flatRegulator T).lift n K v = 0 := rfl
    have hfv : firstVariation T (trivialCarrier Unit) ((flatRegulator T).bank n) b
        ((flatRegulator T).fields n).z v.val = 0 := firstVariation_flat hT b n K v
    rw [hfv, h0]
    cases b <;> simp [RegulatorSequence.finiteSectorVariation]
  simp only [h]
  exact tendsto_const_nhds

/-- **Non-vacuity of `random_realization_core`** (the core is the whole test space). -/
example (hT : 0 < T) :=
  random_realization_core (P := Measure.dirac ()) hT (fun _ : Unit => flatRegulator T)
    (fun _ _ => univ) (fun _ _ => dense_univ)
    (ae_of_all _ fun _ => ⟨fun Q => flatRegulator_compactnessCertificate T Q,
      flatRegulator_coframeChart T, flatRegulator_coreConsistent hT _,
      flatRegulator_summableTransport⟩)
    (W := fun _ => ℝ) (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => tendsto_const_nhds)
    (fun _ _ _ _ => 0)
    (ae_of_all _ fun _ => ⟨fun n => le_rfl, fun n K v _ => by simp, fun n K v _ => by
      have h0 : (flatRegulator T).lift n K v = 0 := rfl
      rw [h0]; simp⟩)
    (fun _ => aemeasurable_const) (by simp) (trivialCarrier_yukawaContinuous Unit)

end CoreFlat

end EinsteinSM
end RenewalGeometry
