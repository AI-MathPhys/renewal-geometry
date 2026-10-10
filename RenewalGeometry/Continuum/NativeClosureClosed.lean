/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeSourceCompareMain
import RenewalGeometry.Continuum.NativeClosureTuple

/-!
# `thm:native-closure` and `cor:native-rate` for native records

Einstein–Standard-Model action-closure manuscript, `thm:native-closure` (`eq:native-total`,
`eq:native-geometry`) and `cor:native-rate`, for the native grid records themselves.

A native record `u_h` (odd `n`, `h = 2π/n`) is mapped to the actual field tuple
`z_h = recTuple u_h` of its trigonometric reconstruction dilated to unit spatial period
(`dilField t₀`, time shift `t₀`; the slab `[t₀, t₁] × 𝕋³_{2π}` becomes `[0, T] × 𝕋³`,
`T = (t₁ - t₀)/2π`), with the slab theory data `SlabData.toSMData M δ` of the native model.  The
source estimate `𝒴_k(z_h) ≤ C₁F_{h,k}` (`RecordTuple.native_source_tuple`, from
`thm:native-source`) is composed with `prop:coupled-bootstrap` (`native_closure_tuple`).

* **`native_closure`** — `eq:native-geometry`: there are `C` and `τ_*` such that along any filter,
  for records satisfying the hypotheses of `thm:native-source` (`RecordHyp`) and the tuple
  hypotheses (adapted Lorentz gauge etc., part of `RecordHyp`), with `hK_h → 0`,
  `τ_{h,k+2}(K_h) ≤ τ_*` and `D^full_{h,k} = i_{h,k} + γ_{h,k} + F_{h,k} → 0`, eventually
  `‖𝒰_h - 𝒰_*‖_{C_tH^k} + ‖Riem‖_{L²H^{k-1}} + ‖T^{SM}‖_{L²H^k} ≤ C D^full_{h,k}`.
* **`native_rate`** — `cor:native-rate` (state/curvature/stress clause): under `σ_h = O(h)`,
  `1 ≤ K_h ≤ c₂h^{-β}`, `β < 1/(k+4)`, `eq:native-tail-rate` and
  `i_{h,k} + γ_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the distance is
  `O(h^{1-β(k+4)}(1+|log h|)^{k+1})`; the resolution and tail-threshold conditions of
  `thm:native-source` are derived from the rate hypotheses.

Gauge sector in `𝔤` (corrected encoding): the finite-action budget `σ_h` and the forcing budget
`F_{h,k}` read only the physical rows (gauge rows tested in the gauge Lie algebra `𝔤 = gSub` of
the slab model through the orthogonal projection `πg`), and the slab Yang–Mills current is the
`𝔤`-component of the native current (`SlabData.Jcur`).

Disclosed renderings: `Σ = 𝕋³`; the records are in the adapted Lorentz gauge (upper-triangular
coframe with positive diagonal), temporal internal gauge, with physical (`ℂ`-linear) co-spinors;
the slab data use a smoothed frame with margin `δ` (`Margin`), equal to the exact frame on the
records (`TupleHyp.margin`); the symmetric-hyperbolic coordinate condition `hAsym` of
`prop:coupled-bootstrap` is a hypothesis on the coordinates `eX`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped Real ContDiff Nat

namespace RenewalGeometry.RecordTuple

open DiscreteEulerConsistency (R4)
open NativeScaling (Mat)
open ShiftedJetAction (Grid)
open NativeDensity DiscreteEulerConsistency NativeModel SlabData ActualJetState
  ActualJetCompleteForcing ActualJetBridge CoupledBootstrap ActualJetSmooth
open TrigInterp (recon reconLow tau)
open NativeRate (eps0 forcingBudget)

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]
variable {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m)

/-- The actual-tuple type of the slab data of a native model. -/
abbrev STuple := Tuple m (HSp M) 𝓢 (CoSpinor 𝓢)

open Classical in
/-- **The actual field tuple of a native record**: the dilated reconstruction `dilField t₀
(recon n u)` as an actual tuple when it satisfies the tuple hypotheses, and the fallback `z₀`
otherwise (only eventual statements are made, under the tuple hypotheses). -/
def recTuple {δ : ℝ} (hδ : 0 < δ) (t₀ : ℝ) (n : ℕ) [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢)
    (z₀ : STuple M) : STuple M :=
  if h : TupleHyp M δ (dilField t₀ (recon n u)) then toTuple hδ h else z₀

theorem recTuple_eq {δ : ℝ} (hδ : 0 < δ) (t₀ : ℝ) {n : ℕ} [NeZero n]
    {u : Grid n → Field 𝔄 𝓗 𝓢} (z₀ : STuple M) (h : TupleHyp M δ (dilField t₀ (recon n u))) :
    recTuple M hδ t₀ n u z₀ = toTuple hδ h := by
  unfold recTuple; rw [dif_pos h]

open Classical in
/-- **The hypotheses of `thm:native-source` on one record** (the resolution `hK ≤ c_res` and the
tail threshold `τ_{h,k+2} ≤ τ_*` are stated separately), together with the tuple hypotheses of the
dilated reconstruction.  The finite-action budget `σ` bounds the raw Euler rows on the **physical**
directions (`physF πg`: coframe, gauge directions in the gauge Lie algebra `𝔤`, Higgs, spinor and
co-spinor directions), as in the manuscript, whose gauge field and test directions live in `𝔤`. -/
structure RecordHyp (δ : ℝ) (Ke : Set Mat) (A t₀ t₁ b : ℝ) (n : ℕ) [NeZero n]
    (u : Grid n → Field 𝔄 𝓗 𝓢) (K σ : ℝ) : Prop where
  odd : Odd n
  one_le : 1 ≤ K
  low_chart : ∀ x, (reconLow n K u x).1 ∈ Ke
  low_amp : ∀ x, ‖reconLow n K u x‖ ≤ A
  chart : ∀ x, (recon n u x).1 ∈ Ke
  amp : ∀ x, ‖recon n u x‖ ≤ A
  sigma_nonneg : 0 ≤ σ
  sigma : (2 * π / n) ^ 4 * ∑ x ∈ Finset.univ.filter
      (fun x : Grid n => pos (2 * π / n) x ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b)),
      ‖(eulerRow (localAction M.toData (2 * π / n)) (2 * π / n) u x).comp
        (NativeTail.physF M.πg)‖ ^ 2 ≤ σ ^ 2
  tuple : TupleHyp M δ (dilField t₀ (recon n u))

/-- The slab time of `[t₀, t₁]` in unit-period coordinates. -/
def slabT (t₀ t₁ : ℝ) : ℝ := (t₁ - t₀) / (2 * π)

theorem slabT_pos {t₀ t₁ : ℝ} (h : t₀ < t₁) : 0 < slabT t₀ t₁ :=
  div_pos (by linarith) (by positivity)

/-- **`thm:native-closure`** (`eq:native-geometry`) for native records. -/
theorem native_closure {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ C τs : ℝ, 0 ≤ C ∧ 0 < τs ∧ ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i)) →
      Tendsto (fun i => 2 * π / N i * K i) l (𝓝 0) →
      (∀ᶠ i in l, tau (N i) (K i) (k + 2) (u i) ≤ τs) →
      Tendsto (fun i =>
        ‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs) +
        forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) l (𝓝 0) →
      ∀ᶠ i in l, dist ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs) ≤
        C * (‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs) +
        forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
          (tau (N i) (K i) (k + 2) (u i))) := by
  obtain ⟨C₁, cr, τs, hC₁, hcr, hτs, hsrc⟩ :=
    native_source_tuple M hδ eY eYD hKe hdet A k (by omega) hCk hb h0 h1 h01.le
  obtain ⟨Cst, hCst, hcl⟩ := CoupledBootstrap.NativeTuple.native_closure_tuple.{0}
    (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) hAsym hk (slabT_pos h01) hKr hKO hR₁
  refine ⟨Cst * max 1 C₁, τs, mul_nonneg hCst (le_trans zero_le_one (le_max_left _ _)), hτs,
    fun {ι} l N _ u K σ zs hzs hrec hhK hτ hD => ?_⟩
  have hF0 : ∀ᶠ i in l, 0 ≤ forcingBudget k Ck (σ i) (2 * π / N i) (K i)
      (tau (N i) (K i) 2 (u i)) (tau (N i) (K i) (k + 2) (u i)) := by
    filter_upwards [hrec] with i hr
    have hK0 : 0 < K i := by linarith [hr.one_le]
    have hn0 : (0 : ℝ) < N i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (N i))
    exact SourceCompare.forcingBudget_nonneg k hCk.le hr.sigma_nonneg (by positivity) hr.one_le
      (TrigInterp.tau_nonneg _ hK0 _ _) (TrigInterp.tau_nonneg _ hK0 _ _)
  have hY : ∀ᶠ i in l,
      (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).resB (recTuple M hδ t₀ (N i) (u i) zs) +
      (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).resD (recTuple M hδ t₀ (N i) (u i) zs) ≤
      C₁ * forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
        (tau (N i) (K i) (k + 2) (u i)) := by
    filter_upwards [hrec, hhK.eventually (ge_mem_nhds hcr), hτ] with i hr hc ht
    rw [recTuple_eq M hδ t₀ zs hr.tuple]
    exact hsrc (N i) hr.odd (u i) (K i) (σ i) hr.one_le hc ht hr.low_chart hr.low_amp hr.chart
      hr.amp hr.sigma_nonneg hr.sigma hr.tuple
  exact hcl l (fun i => recTuple M hδ t₀ (N i) (u i) zs) zs hzs _ C₁ hF0 hD hY

/-- `h K ≤ c₂ h^{1-β}` from `K ≤ c₂ h^{-β}`. -/
theorem mul_le_rpow_of_le {h K c₂ β : ℝ} (hh : 0 < h) (hK : K ≤ c₂ * h ^ (-β)) :
    h * K ≤ c₂ * h ^ (1 - β) := by
  have e : h ^ (1 - β) = h * h ^ (-β) := by
    rw [sub_eq_add_neg, Real.rpow_add hh, Real.rpow_one]
  rw [e]
  calc h * K ≤ h * (c₂ * h ^ (-β)) := mul_le_mul_of_nonneg_left hK hh.le
    _ = c₂ * (h * h ^ (-β)) := by ring

/-- `h K² ≤ c₂² h^{1-2β}` from `0 ≤ K ≤ c₂ h^{-β}`. -/
theorem mul_sq_le_rpow_of_le {h K c₂ β : ℝ} (hh : 0 < h) (hK0 : 0 ≤ K)
    (hK : K ≤ c₂ * h ^ (-β)) : h * K ^ 2 ≤ c₂ ^ 2 * h ^ (1 - 2 * β) := by
  have e : h ^ (1 - 2 * β) = h * (h ^ (-β)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, sub_eq_add_neg, Real.rpow_add hh,
      Real.rpow_one]
    congr 2; push_cast; ring
  rw [e]
  have h2 : K ^ 2 ≤ (c₂ * h ^ (-β)) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  calc h * K ^ 2 ≤ h * (c₂ * h ^ (-β)) ^ 2 := mul_le_mul_of_nonneg_left h2 hh.le
    _ = c₂ ^ 2 * (h * (h ^ (-β)) ^ 2) := by ring

theorem tendsto_rpow_of_nhdsGT {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝[>] 0)) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun i => h i ^ p) l (𝓝 0) := by
  have h0 : Tendsto h l (𝓝 0) := (tendsto_nhdsWithin_iff.1 hh).1
  have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).comp h0
  rwa [Real.zero_rpow hp.ne'] at this

/-- **`cor:native-rate`** for native records (state, curvature and stress rate): with
`h = 2π/n → 0⁺`, `σ_h ≤ C_σh`, `1 ≤ K_h ≤ c₂h^{-β}`, `0 ≤ β < 1/(k+4)`, `eq:native-tail-rate`
`τ_{h,2} ≤ C_τhK_h`, `τ_{h,k+2} ≤ C_τhK_h²`, the hypotheses of `thm:native-source` on the records
and `i_{h,k} + γ_{h,k} = O(h^{1-β(k+4)}(1+|log h|)^{k+1})`, the state, curvature and Standard-Model
stress distances are `O(h^{1-β(k+4)}(1+|log h|)^{k+1})`.  The resolution `hK_h ≤ c_res` and the tail
threshold `τ_{h,k+2} ≤ τ_*` of `thm:native-source` are consequences of the rate hypotheses. -/
theorem native_rate {δ : ℝ} (hδ : 0 < δ) {nX na nb : ℕ}
    (eX : (Fin nX → ℝ) ≃L[ℝ] StateP m (HSp M) 𝓢 (CoSpinor 𝓢))
    (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M)) (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢)
    (hAsym : ∀ j a b v, Aco (toSMData M δ) eX j a b v = Aco (toSMData M δ) eX j b a v)
    {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A : ℝ) {k : ℕ}
    (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {t₀ t₁ b : ℝ} (hb : 0 < b) (h0 : b < t₀)
    (h1 : t₁ + b ≤ 2 * π) (h01 : t₀ < t₁) {Kr : Set (Fin nX → ℝ)} (hKr : IsCompact Kr)
    (hKO : Kr ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) {β c₂ Cσ Cτ : ℝ} (hβ : 0 ≤ β)
    (hβk : β < 1 / (k + 4)) (hCσ : 0 ≤ Cσ) :
    ∀ {ι : Type} (l : Filter ι) (N : ι → ℕ) [∀ i, NeZero (N i)]
      (u : ∀ i, Grid (N i) → Field 𝔄 𝓗 𝓢) (K σ : ι → ℝ),
      ∀ zs ∈ refSet (toSMData M δ) eX k (slabT t₀ t₁) Kr R₁,
      Tendsto (fun i => 2 * π / N i) l (𝓝[>] 0) →
      (∀ᶠ i in l, RecordHyp M δ Ke A t₀ t₁ b (N i) (u i) (K i) (σ i) ∧
        K i ≤ c₂ * (2 * π / N i) ^ (-β) ∧ σ i ≤ Cσ * (2 * π / N i) ∧
        tau (N i) (K i) 2 (u i) ≤ Cτ * (2 * π / N i * K i) ∧
        tau (N i) (K i) (k + 2) (u i) ≤ Cτ * (2 * π / N i * K i ^ 2)) →
      (fun i =>
        ‖(slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init (recTuple M hδ t₀ (N i) (u i) zs) -
          (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).init zs‖ +
        (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).harm (recTuple M hδ t₀ (N i) (u i) zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N i)|) ^ (k + 1)) →
      (fun i => dist ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k
            (slabT t₀ t₁) (slabT_pos h01)).obs (recTuple M hδ t₀ (N i) (u i) zs))
          ((slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
            (slabT_pos h01)).obs zs)) =O[l]
        (fun i => (2 * π / N i) ^ (1 - β * (k + 4)) *
          (1 + |Real.log (2 * π / N i)|) ^ (k + 1)) := by
  obtain ⟨C₁, cr, τs, hC₁, hcr, hτs, hsrc⟩ :=
    native_source_tuple M hδ eY eYD hKe hdet A k (by omega) hCk hb h0 h1 h01.le
  obtain ⟨Cst, hCst, hrt⟩ := CoupledBootstrap.NativeTuple.native_rate_tuple.{0}
    (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) hAsym hk (slabT_pos h01) hKr hKO hR₁
  intro ι l N _ u K σ zs hzs hh hev hig
  set hN : ι → ℝ := fun i => 2 * π / N i with hN_def
  have hpos : ∀ i, 0 < hN i := fun i => by
    have : (0 : ℝ) < N i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (N i))
    positivity
  have hk4 : (0 : ℝ) < k + 4 := by positivity
  have hβ1 : β * (k + 4) < 1 := by rwa [lt_div_iff₀ hk4] at hβk
  have hk4' : (8 : ℝ) ≤ k + 4 := by
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hβ2 : 2 * β < 1 := by nlinarith
  -- `hK → 0` and `τ_{k+2} → 0`
  have hr1 := tendsto_rpow_of_nhdsGT hh (show 0 < 1 - β by linarith)
  have hr2 := tendsto_rpow_of_nhdsGT hh (show 0 < 1 - 2 * β by linarith)
  have hhK : Tendsto (fun i => 2 * π / N i * K i) l (𝓝 0) := by
    have hup : Tendsto (fun i => c₂ * hN i ^ (1 - β)) l (𝓝 0) := by
      simpa using hr1.const_mul c₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with i hi
      exact mul_nonneg (hpos i).le (by linarith [hi.1.one_le])
    · filter_upwards [hev] with i hi
      exact mul_le_rpow_of_le (hpos i) hi.2.1
  have hτ0 : Tendsto (fun i => tau (N i) (K i) (k + 2) (u i)) l (𝓝 0) := by
    have hup : Tendsto (fun i => |Cτ| * (c₂ ^ 2 * hN i ^ (1 - 2 * β))) l (𝓝 0) := by
      simpa using (hr2.const_mul (c₂ ^ 2)).const_mul |Cτ|
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with i hi
      exact TrigInterp.tau_nonneg _ (by linarith [hi.1.one_le]) _ _
    · filter_upwards [hev] with i hi
      refine hi.2.2.2.2.trans ?_
      have hm : 0 ≤ 2 * π / N i * K i ^ 2 := by
        have := hpos i
        positivity
      calc Cτ * (2 * π / N i * K i ^ 2) ≤ |Cτ| * (2 * π / N i * K i ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hm
        _ ≤ |Cτ| * (c₂ ^ 2 * hN i ^ (1 - 2 * β)) :=
            mul_le_mul_of_nonneg_left
              (mul_sq_le_rpow_of_le (hpos i) (by linarith [hi.1.one_le]) hi.2.1) (abs_nonneg _)
  have hY : ∀ᶠ i in l,
      (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).resB (recTuple M hδ t₀ (N i) (u i) zs) +
      (slabModel (toSMData M δ) eX eY eYD (toSMData_smooth M hδ) k (slabT t₀ t₁)
        (slabT_pos h01)).resD (recTuple M hδ t₀ (N i) (u i) zs) ≤
      C₁ * forcingBudget k Ck (σ i) (2 * π / N i) (K i) (tau (N i) (K i) 2 (u i))
        (tau (N i) (K i) (k + 2) (u i)) := by
    filter_upwards [hev, hhK.eventually (ge_mem_nhds hcr), hτ0.eventually (ge_mem_nhds hτs)]
      with i hi hc ht
    have hr := hi.1
    rw [recTuple_eq M hδ t₀ zs hr.tuple]
    exact hsrc (N i) hr.odd (u i) (K i) (σ i) hr.one_le hc ht hr.low_chart hr.low_amp hr.chart
      hr.amp hr.sigma_nonneg hr.sigma hr.tuple
  have hh1 : ∀ᶠ i in l, hN i ≤ 1 :=
    (tendsto_nhdsWithin_iff.1 hh).1.eventually (ge_mem_nhds one_pos)
  refine hrt l (fun i => recTuple M hδ t₀ (N i) (u i) zs) zs hzs hN K σ
    (fun i => tau (N i) (K i) 2 (u i)) (fun i => tau (N i) (K i) (k + 2) (u i))
    (Ck := Ck) (C₁ := C₁) (Cτ := Cτ) (c₂ := c₂) hCk.le hβ hβk hCσ hh ?_ hY hig
  filter_upwards [hev, hh1] with i hi hi1
  have hK0 : 0 < K i := by linarith [hi.1.one_le]
  exact ⟨hpos i, hi1, hi.1.one_le, hi.2.1, hi.1.sigma_nonneg, hi.2.2.1,
    TrigInterp.tau_nonneg _ hK0 _ _, hi.2.2.2.1, TrigInterp.tau_nonneg _ hK0 _ _, hi.2.2.2.2⟩

end

end RenewalGeometry.RecordTuple
