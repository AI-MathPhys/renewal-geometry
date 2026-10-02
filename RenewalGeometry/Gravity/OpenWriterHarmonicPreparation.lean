/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterVacuumLimit

/-!
# The harmonic preparation of `D_s(ε)` data and its Moser bound
  (`eq:supp-open-harmonic-initial`, `eq:main-open-data-class`, `thm:supp-open-einstein`)

Slice data are encoded as record fields with vanishing time row: `Q₀ = g⁰ - η` (spatial block
`γ - I`) and `Kr` (spatial block `K`), with classical spatial derivative fields.

* `prepFun` — the harmonic preparation `V₀ = (2 tr_γ K, γ^{jk}(∂_jγ_{ki} - ½∂ᵢγ_{jk}), -2K)` of
  `eq:supp-open-harmonic-initial`, `γ^{ij}` the spatial block of `(η + Q₀)⁻¹`;
* `prep_moser` — **Moser bound of the preparation map**: for small data,
  `V₀ ∈ H^s` and `Σ‖V₀‖_{H^s} ≤ C (Σ‖γ - I‖_{H^{s+1}} + Σ‖K‖_{H^s})` (from `cont_moser` for the
  inverse-metric entries and the product algebra `memH_mul`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterLimitRegularity

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum HarmonicGaugePropagation ContractedBianchiJet
  PeriodicGridSobolev.Composition OpenWriterGridBridge RootParityConnector HarmonicWriter
  HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Bound bookkeeping -/

/-- `f ∈ H^s` with `‖f‖_{H^s} ≤ a`. -/
def HB (s : ℕ) (f : CT) (a : ℝ) : Prop := MemH s ⇑f ∧ sn s ⇑f ≤ a

theorem HB.add {s : ℕ} {f g : CT} {a b : ℝ} (hf : HB s f a) (hg : HB s g b) : HB s (f + g) (a + b) :=
  ⟨memH_add hf.1 hg.1, (sn_add_le' hf.1 hg.1).trans (add_le_add hf.2 hg.2)⟩

theorem HB.sub {s : ℕ} {f g : CT} {a b : ℝ} (hf : HB s f a) (hg : HB s g b) : HB s (f - g) (a + b) :=
  ⟨memH_sub hf.1 hg.1, (sn_sub_le' hf.1 hg.1).trans (add_le_add hf.2 hg.2)⟩

theorem HB.smul {s : ℕ} {f : CT} {a : ℝ} (c : ℂ) (hf : HB s f a) : HB s (c • f) (‖c‖ * a) :=
  ⟨memH_smul c hf.1, by rw [sn_smul]; exact
    mul_le_mul_of_nonneg_left hf.2 (norm_nonneg _)⟩

theorem HB.mono {s : ℕ} {f : CT} {a b : ℝ} (hf : HB s f a) (h : a ≤ b) : HB s f b := ⟨hf.1, hf.2.trans h⟩

theorem HB.sum {s : ℕ} {ι : Type*} (t : Finset ι) {f : ι → CT} {a : ι → ℝ}
    (hf : ∀ i, HB s (f i) (a i)) : HB s (∑ i ∈ t, f i) (∑ i ∈ t, a i) := by
  obtain ⟨h1, h2⟩ := sn_sum_le' t (fun i => (hf i).1)
  exact ⟨h1, h2.trans (Finset.sum_le_sum fun i _ => (hf i).2)⟩

/-! ### The harmonic preparation -/

/-- `γ^{ij}`: the spatial block of the inverse space-time metric `(η + Q₀)⁻¹`. -/
def prepGinv (Q₀ : T3 → MetricRec) (x : T3) (i j : Fin 3) : ℝ :=
  (Matrix.of (minkowski + Q₀ x))⁻¹ i.succ j.succ

/-- **The harmonic preparation** `eq:supp-open-harmonic-initial`:
`V₀ = (2 tr_γ K, γ^{jk}(∂_jγ_{ki} - ½∂ᵢγ_{jk}), -2K)` (unit lapse, zero shift). -/
def prepFun (Q₀ Kr : T3 → MetricRec) (Qd : Fin 3 → T3 → MetricRec) (x : T3) : MetricRec :=
  fun μ ν => sliceMat (2 * ∑ i, ∑ j, prepGinv Q₀ x i j * Kr x i.succ j.succ)
    (fun i => ∑ j, ∑ k, prepGinv Q₀ x j k * (Qd j x k.succ i.succ - (1 / 2) * Qd i x j.succ k.succ))
    (Matrix.of fun i j => -2 * Kr x i.succ j.succ) μ ν

/-- The inverse-metric entry as a function of the record. -/
def invEntry (i j : Fin 3) (q : MetricRec) : ℝ := (Matrix.of (minkowski + q))⁻¹ i.succ j.succ

theorem analyticAt_invEntry (i j : Fin 3) : AnalyticAt ℝ (invEntry i j) 0 := by
  have h := analyticAt_inv_entry minkowski det_minkowski_ne i.succ j.succ
  have hg : AnalyticAt ℝ (fun q : MetricRec => minkowski + q) 0 := by fun_prop
  exact h.comp_of_eq hg (by simp)

theorem invEntry_zero (i j : Fin 3) : invEntry i j 0 = minkowski i.succ j.succ := by
  simp only [invEntry, add_zero, minkowski_inv]; rfl

theorem norm_minkowski_le (i j : Fin 3) : ‖((minkowski i.succ j.succ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [minkowski_succ_succ]; split_ifs <;> simp

set_option maxHeartbeats 1000000 in
/-- **Moser bound of the harmonic preparation**: for `s ≥ 2` there are `δ > 0`, `C ≥ 0` such that
for data `Q₀ ∈ H^{s+1}`, `Kr ∈ H^s` with classical derivative fields `∂ᵢQ₀` and
`Σ‖Q₀‖_{H^{s+1}} ≤ δ`, the prepared velocity `V₀ = prepFun` is a continuous record field with
components in `H^s` and `Σ‖V₀‖_{H^s} ≤ C (Σ‖Q₀‖_{H^{s+1}} + Σ‖Kr‖_{H^s})`. -/
theorem prep_moser (s : ℕ) (hs : 2 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (Q₀ Kr : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec)),
      (∀ i, IsLineDeriv i ⇑Q₀ ⇑(Qd i)) → (∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)) →
      (∀ k, MemH s ⇑(ccoord bM Kr k)) → ccoordSum (s + 1) bM Q₀ ≤ δ →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
        (∀ k, MemH s ⇑(ccoord bM V₀ k)) ∧
        ccoordSum s bM V₀ ≤ C * (ccoordSum (s + 1) bM Q₀ + ccoordSum s bM Kr) := by
  -- Moser for the nine inverse-metric entries
  have hM : ∀ e : Fin 3 × Fin 3, ∃ δ > 0, ∃ C ≥ 0, ∀ Q : C(T3, MetricRec),
      (∀ k, MemH s ⇑(ccoord bM Q k)) → ccoordSum s bM Q ≤ δ →
      ∃ F : CT, (∀ x, F x = ((invEntry e.1 e.2 (Q x) - invEntry e.1 e.2 0 : ℝ) : ℂ)) ∧
        MemH s ⇑F ∧ sn s ⇑F ≤ C * ccoordSum s bM Q := by
    intro e
    obtain ⟨p, R, hp⟩ := analyticAt_invEntry e.1 e.2
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser s hs bM hp
    refine ⟨δ, hδ, C, hC, fun Q hQ hQδ => ?_⟩
    obtain ⟨-, F, hF, hFm, hFs⟩ := hm Q hQ hQδ
    exact ⟨F, fun x => by rw [hF x, zero_add], hFm, hFs⟩
  choose δM hδM CM hCM hMm using hM
  set δ0 : ℝ := (univ : Finset (Fin 3 × Fin 3)).inf' univ_nonempty δM
  have hδ0 : 0 < δ0 := by rw [Finset.lt_inf'_iff]; intro e _; exact hδM e
  have hδ0le : ∀ e, δ0 ≤ δM e := fun e => Finset.inf'_le _ (mem_univ e)
  set C0 : ℝ := ∑ e, CM e
  have hC0 : ∀ e, CM e ≤ C0 := fun e => single_le_sum (f := CM) (fun e _ => hCM e) (mem_univ e)
  have hC0n : 0 ≤ C0 := sum_nonneg fun e _ => hCM e
  obtain ⟨Km, hKm, hmul⟩ := memH_mul s hs
  set Cc : ℝ := 18 * (1 + Km * C0) + 2
  have hCc : 0 ≤ Cc := by positivity
  refine ⟨min δ0 1, lt_min hδ0 one_pos, 16 * Cc, by positivity,
    fun Q₀ Kr Qd hdQ hQ hK hsmall => ?_⟩
  set A := ccoordSum (s + 1) bM Q₀
  set B := ccoordSum s bM Kr
  have hA0 : 0 ≤ A := ccoordSum_nonneg _ _ _
  have hB0 : 0 ≤ B := ccoordSum_nonneg _ _ _
  have hA1 : A ≤ 1 := hsmall.trans (min_le_right _ _)
  have hQs : ∀ k, MemH s ⇑(ccoord bM Q₀ k) := fun k => memH_mono (by omega) (hQ k)
  have hAs : ccoordSum s bM Q₀ ≤ A := ccoordSum_mono (by omega) hQ
  -- the inverse entries
  have hF : ∀ i j : Fin 3, ∃ F : CT, (∀ x, F x = ((prepGinv ⇑Q₀ x i j -
      minkowski i.succ j.succ : ℝ) : ℂ)) ∧ HB s F (C0 * A) := by
    intro i j
    obtain ⟨F, hFx, hFm, hFs⟩ := hMm (i, j) Q₀ hQs ((hAs.trans hsmall).trans
      ((min_le_left _ _).trans (hδ0le _)))
    refine ⟨F, fun x => by rw [hFx x, invEntry_zero]; rfl, hFm, hFs.trans ?_⟩
    exact mul_le_mul (hC0 _) hAs (ccoordSum_nonneg _ _ _) hC0n
  choose F hFx hFb using hF
  -- the data components
  have hkc : ∀ i j : Fin 3, HB s (cmp Kr i.succ j.succ) B := fun i j =>
    ⟨memH_cmp hK _ _, sn_cmp_le_ccoordSum _ _ _ _⟩
  have hdq : ∀ (j : Fin 3) (a b : Fin 4), HB s (cmp (Qd j) a b) A := fun j a b => by
    have h := memH_of_isLineDeriv (isLineDeriv_cmp (hdQ j) a b) (memH_cmp hQ a b)
    exact ⟨h.1, h.2.trans (sn_cmp_le_ccoordSum _ _ _ _)⟩
  -- the three blocks as continuous functions
  set C : Fin 3 → Fin 3 → CT := fun i j => (((minkowski i.succ j.succ : ℝ) : ℂ)) • (1 : CT)
  set D : Fin 3 → Fin 3 → Fin 3 → CT := fun i j k =>
    cmp (Qd j) k.succ i.succ - ((1 / 2 : ℝ) : ℂ) • cmp (Qd i) j.succ k.succ
  set E00 : CT := (2 : ℂ) • ∑ i, ∑ j, (((minkowski i.succ j.succ : ℝ) : ℂ) • cmp Kr i.succ j.succ +
    F i j * cmp Kr i.succ j.succ)
  set E0 : Fin 3 → CT := fun i => ∑ j, ∑ k, (((minkowski j.succ k.succ : ℝ) : ℂ) • D i j k +
    F j k * D i j k)
  set Esp : Fin 3 → Fin 3 → CT := fun i j => (-2 : ℂ) • cmp Kr i.succ j.succ
  have hFKb : ∀ i j, HB s (F i j * cmp Kr i.succ j.succ) (Km * (C0 * A) * B) := fun i j =>
    ⟨(hmul _ _ (hFb i j).1 (hkc i j).1).1, (hmul _ _ (hFb i j).1 (hkc i j).1).2.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hFb i j).2 hKm) (hkc i j).2 (sn_nonneg _ _)
        (by positivity))⟩
  have hDb : ∀ i j k, HB s (D i j k) (2 * A) := fun i j k =>
    ((hdq j k.succ i.succ).sub ((hdq i j.succ k.succ).smul _)).mono (by
      simp only [Complex.norm_real, Real.norm_eq_abs]; norm_num; linarith)
  have hE00 : HB s E00 (Cc * (A + B)) := by
    have h := (HB.sum univ fun i => HB.sum univ fun j =>
      (((hkc i j).smul _).mono (mul_le_of_le_one_left hB0 (norm_minkowski_le i j))).add
        (hFKb i j)).smul (2 : ℂ)
    refine h.mono ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Complex.norm_ofNat]
    have : Km * (C0 * A) * B ≤ Km * C0 * B := by
      have := mul_le_mul_of_nonneg_left hA1 (mul_nonneg hKm hC0n)
      nlinarith
    simp only [Cc]; push_cast; nlinarith
  have hE0 : ∀ i, HB s (E0 i) (Cc * (A + B)) := by
    intro i
    have h := HB.sum univ fun j => HB.sum univ fun k =>
      (((hDb i j k).smul _).mono (mul_le_of_le_one_left (by positivity)
        (norm_minkowski_le j k))).add
      (⟨(hmul _ _ (hFb j k).1 (hDb i j k).1).1, (hmul _ _ (hFb j k).1 (hDb i j k).1).2.trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hFb j k).2 hKm) (hDb i j k).2 (sn_nonneg _ _)
          (by positivity))⟩ : HB s (F j k * D i j k) (Km * (C0 * A) * (2 * A)))
    refine h.mono ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : Km * (C0 * A) * (2 * A) ≤ Km * C0 * (2 * A) := by
      have := mul_le_mul_of_nonneg_left hA1 (mul_nonneg hKm hC0n)
      nlinarith
    simp only [Cc]; push_cast; nlinarith
  have hEsp : ∀ i j, HB s (Esp i j) (Cc * (A + B)) := fun i j =>
    ((hkc i j).smul _).mono (by
      have h1 := mul_nonneg hKm hC0n
      have h2 : 2 * B ≤ Cc * (A + B) := by simp only [Cc]; nlinarith
      simpa using h2)
  -- pointwise identities
  have hg : ∀ x i j, prepGinv ⇑Q₀ x i j = (F i j x).re + minkowski i.succ j.succ := by
    intro x i j; rw [hFx]; simp
  have hgc : ∀ i j, Continuous fun x => prepGinv ⇑Q₀ x i j := fun i j => by
    have : (fun x => prepGinv ⇑Q₀ x i j) = fun x => (F i j x).re + minkowski i.succ j.succ :=
      funext fun x => hg x i j
    rw [this]; fun_prop
  have hcont : Continuous (prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i))) := by
    have hK' : ∀ μ ν, Continuous fun x => Kr x μ ν := fun μ ν =>
      (continuous_apply ν).comp ((continuous_apply μ).comp Kr.continuous)
    have hQd' : ∀ i μ ν, Continuous fun x => Qd i x μ ν := fun i μ ν =>
      (continuous_apply ν).comp ((continuous_apply μ).comp (Qd i).continuous)
    refine continuous_pi fun μ => continuous_pi fun ν => ?_
    refine Fin.cases ?_ (fun a => ?_) μ <;> refine Fin.cases ?_ (fun b => ?_) ν <;>
      simp only [prepFun, sliceMat_zero_zero, sliceMat_zero_succ, sliceMat_succ_zero,
        sliceMat_succ_succ, Matrix.of_apply]
    · exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => (hgc i j).mul (hK' _ _))
    · exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        (hgc j k).mul ((hQd' _ _ _).sub (continuous_const.mul (hQd' _ _ _)))
    · exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        (hgc j k).mul ((hQd' _ _ _).sub (continuous_const.mul (hQd' _ _ _)))
    · exact continuous_const.mul (hK' _ _)
  set V₀ : C(T3, MetricRec) := ⟨_, hcont⟩
  have e00 : cmp V₀ 0 0 = E00 := by
    ext x
    simp only [cmp_apply, V₀, ContinuousMap.coe_mk, prepFun, sliceMat_zero_zero, E00,
      ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, smul_eq_mul, hFx]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e0 : ∀ i, cmp V₀ 0 i.succ = E0 i ∧ cmp V₀ i.succ 0 = E0 i := by
    intro i
    refine ⟨?_, ?_⟩ <;> ext x <;>
    simp only [cmp_apply, V₀, ContinuousMap.coe_mk, prepFun, sliceMat_zero_succ,
      sliceMat_succ_zero, E0, D, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      hFx] <;>
    push_cast <;>
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have esp : ∀ i j, cmp V₀ i.succ j.succ = Esp i j := by
    intro i j
    ext x
    simp only [cmp_apply, V₀, ContinuousMap.coe_mk, prepFun, sliceMat_succ_succ, Matrix.of_apply,
      Esp, ContinuousMap.smul_apply, smul_eq_mul]
    push_cast; ring
  have hcomp : ∀ μ ν, HB s (cmp V₀ μ ν) (Cc * (A + B)) := by
    intro μ ν
    refine Fin.cases ?_ (fun a => ?_) μ <;> refine Fin.cases ?_ (fun b => ?_) ν
    · rw [e00]; exact hE00
    · rw [(e0 b).1]; exact hE0 b
    · rw [(e0 a).2]; exact hE0 a
    · rw [esp]; exact hEsp a b
  refine ⟨V₀, rfl, fun k => by rw [ccoord_bM]; exact (hcomp k.1 k.2).1, ?_⟩
  unfold ccoordSum
  calc ∑ k, sn s ⇑(ccoord bM V₀ k) ≤ ∑ _k : Σ _ : Fin 4, Fin 4, Cc * (A + B) :=
        Finset.sum_le_sum fun k _ => by rw [ccoord_bM]; exact (hcomp k.1 k.2).2
    _ = 16 * Cc * (A + B) := by simp; ring


/-! ### Slice data of `D_s(ε)` -/

/-- The unit-lapse zero-shift slice data at `x` of record-encoded `(γ, K)` data:
`γ = I + Q₀|_{space}`, `γ⁻¹` the spatial block of `(η + Q₀)⁻¹`, `∂γ`, `∂∂γ`, `K`, `∂K` from the
classical derivative fields, `(v₀₀, v₀ᵢ)` the harmonic preparation; the free time derivatives of
the second jet and the acceleration are set to `0`. -/
def dataSlice (Q₀ Kr : T3 → MetricRec) (Qd Kd : Fin 3 → T3 → MetricRec)
    (Qdd : Fin 3 → Fin 3 → T3 → MetricRec) (x : T3) : SliceData where
  γ := Matrix.of fun i j => (minkowski + Q₀ x) i.succ j.succ
  γi := Matrix.of fun i j => prepGinv Q₀ x i j
  dγ := fun k => Matrix.of fun i j => Qd k x i.succ j.succ
  ddγ := fun k l => Matrix.of fun i j => Qdd k l x i.succ j.succ
  K := Matrix.of fun i j => Kr x i.succ j.succ
  dK := fun k => Matrix.of fun i j => Kd k x i.succ j.succ
  v00 := prepFun Q₀ Kr Qd x 0 0
  v0 := fun i => prepFun Q₀ Kr Qd x 0 i.succ
  dv00 := fun _ => 0
  dv0 := fun _ _ => 0
  w := 0

/-- **The data class `D_s(ε)`** (`eq:main-open-data-class`), record-encoded: `Q₀ = g⁰ - η` with
spatial block `γ - I` and `Kr` with spatial block `K` (vanishing time rows, symmetric), with
classical spatial derivative fields `∂Q₀`, `∂∂Q₀`, `∂Kr`, `γ - I ∈ H^{s+1}`, `K ∈ H^s`, and the
vacuum constraints `R(γ) + (tr_γK)² - |K|²_γ = 0`, `∇_γ^jK_{ji} - ∂ᵢtr_γK = 0` at every point. -/
structure DsData (s : ℕ) (Q₀ Kr : C(T3, MetricRec)) (Qd Kd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) : Prop where
  symQ : ∀ x μ ν, Q₀ x μ ν = Q₀ x ν μ
  symK : ∀ x μ ν, Kr x μ ν = Kr x ν μ
  timeQ : ∀ x μ, Q₀ x 0 μ = 0
  timeK : ∀ x μ, Kr x 0 μ = 0
  dQ : ∀ i, IsLineDeriv i ⇑Q₀ ⇑(Qd i)
  dQd : ∀ i j, IsLineDeriv i ⇑(Qd j) ⇑(Qdd i j)
  dK : ∀ i, IsLineDeriv i ⇑Kr ⇑(Kd i)
  regQ : ∀ k, MemH (s + 1) ⇑(ccoord bM Q₀ k)
  regK : ∀ k, MemH s ⇑(ccoord bM Kr k)
  ham : ∀ x, (dataSlice ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) (fun i => ⇑(Kd i))
    (fun i j => ⇑(Qdd i j)) x).hamC = 0
  mom : ∀ x i, (dataSlice ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) (fun i => ⇑(Kd i))
    (fun i j => ⇑(Qdd i j)) x).momC i = 0

/-- The size `‖γ - I‖_{H^{s+1}} + ‖K‖_{H^s}` of `eq:main-open-data-class` (component sums). -/
def dataSize (s : ℕ) (Q₀ Kr : C(T3, MetricRec)) : ℝ := ccoordSum (s + 1) bM Q₀ + ccoordSum s bM Kr

/-- Block structure of the inverse of a unit-lapse zero-shift record. -/
theorem inv_block {g : MetricRec} (h00 : g 0 0 = -1) (h0i : ∀ i : Fin 3, g 0 i.succ = 0)
    (hi0 : ∀ i : Fin 3, g i.succ 0 = 0) (hdet : (Matrix.of g).det ≠ 0) :
    (Matrix.of g)⁻¹ = sliceMat (-1) 0 (Matrix.of fun i j => (Matrix.of g)⁻¹ i.succ j.succ) ∧
    (Matrix.of fun i j : Fin 3 => g i.succ j.succ) *
      (Matrix.of fun i j => (Matrix.of g)⁻¹ i.succ j.succ) = 1 := by
  set N := (Matrix.of g)⁻¹
  have hNM : N * Matrix.of g = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  have hMN : Matrix.of g * N = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hdet)
  have e1 := congrFun (congrFun hNM 0) 0
  have e2 : ∀ i : Fin 3, (N * Matrix.of g) i.succ 0 = 0 := fun i => by
    rw [hNM]; simp [Matrix.one_apply, Fin.succ_ne_zero]
  have e3 : ∀ j : Fin 3, (Matrix.of g * N) 0 j.succ = 0 := fun j => by
    rw [hMN]; simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm]
  have e4 : ∀ i j : Fin 3, (Matrix.of g * N) i.succ j.succ = if i = j then 1 else 0 := fun i j => by
    rw [hMN]; simp [Matrix.one_apply, Fin.succ_inj]
  simp only [Matrix.mul_apply, Fin.sum_univ_succ (n := 3), Matrix.of_apply, h00, h0i, hi0,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at e1 e2 e3 e4
  have n00 : N 0 0 = -1 := by linarith
  have ni0 : ∀ i : Fin 3, N i.succ 0 = 0 := fun i => by have := e2 i; linarith
  have n0j : ∀ j : Fin 3, N 0 j.succ = 0 := fun j => by have := e3 j; linarith
  refine ⟨?_, ?_⟩
  · ext μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [n00, ni0, n0j]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    have := e4 i j
    simpa using this

theorem isLineDeriv_entry {i : Fin 3} {F F' : T3 → MetricRec} (h : IsLineDeriv i F F')
    (μ ν : Fin 4) : IsLineDeriv i (fun x => F x μ ν) (fun x => F' x μ ν) := fun x =>
  hasDerivAt_pi.mp (hasDerivAt_pi.mp (h x) μ) ν

theorem fin_zero_ne_succ (i : Fin 3) : (0 : Fin 4) ≠ i.succ := (Fin.succ_ne_zero i).symm

theorem isLineDeriv_comp_unique {i : Fin 3} {F F' : T3 → MetricRec} (h : IsLineDeriv i F F')
    {a b : Fin 4} {f f' : T3 → ℝ} (hf : IsLineDeriv i f f') (e : ∀ x, F x a b = f x) (x : T3) :
    F' x a b = f' x := by
  have h1 := hasDerivAt_pi.mp (hasDerivAt_pi.mp (h x) a) b
  have h2 := hf x
  simp only [e] at h1
  exact h1.unique h2


set_option maxHeartbeats 8000000 in
/-- **`thm:supp-open-einstein`** (whole-sequence nonsymmetric vacuum limit) with the paper's
hypotheses, for `s ≥ 6`: there are `ε_s, T_s > 0` and constants `K, C, C_ε` such that for every
`(γ, K) ∈ D_s(ε)` (`DsData`, `dataSize ≤ ε ≤ ε_s`) the harmonic preparation `V₀ = prepFun`
(`eq:supp-open-harmonic-initial`) is defined, for every mesh `h = 1/(n + 1)` the open writer has a
unique solution on `[0, T_s]` from the samples of `(Q₀, V₀)` (`open_writer_lifespan`), and the whole
sequence of interpolated solutions converges to a classical solution of the harmonic reduced
equation with the metric rate `eq:supp-open-metric-rate` and the curvature rate
`eq:supp-open-curvature-rate` (`O(h ε)`), whose Einstein tensor vanishes on `[0, T_s] × 𝕋³`. -/
theorem supp_open_einstein (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ TL > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∃ Cε ≥ 0, ∀ (Q₀ Kr : C(T3, MetricRec))
      (Qd Kd : Fin 3 → C(T3, MetricRec)) (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
        (∀ n, IsWriterSolution TL (q n) (v n) ∧ q n 0 = sampleRec (n + 1) ⇑Q₀ ∧
          v n 0 = sampleRec (n + 1) ⇑V₀) ∧
        (∀ n (q' v' : ℝ → Grid (n + 1) → MetricRec), q' 0 = sampleRec (n + 1) ⇑Q₀ →
          v' 0 = sampleRec (n + 1) ⇑V₀ → IsWriterSolution TL q' v' →
          ∀ t ∈ Set.Icc 0 TL, q' t = q n t ∧ v' t = v n t) ∧
          ∃ (Q V A : ℝ → C(T3, MetricRec)) (Qd' Vd' : ℝ → Fin 3 → C(T3, MetricRec))
            (Qdd' : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)), Q 0 = Q₀ ∧ V 0 = V₀ ∧
            ∀ t ∈ Set.Icc 0 TL,
              (Tendsto (fun n => interpRec (q n t)) atTop (𝓝 (Q t)) ∧
              Tendsto (fun n => interpRec (v n t)) atTop (𝓝 (V t)) ∧
              Tendsto (fun n => interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t)))) atTop
                (𝓝 (A t)) ∧ (∀ y μ ν, A t y μ ν = A t y ν μ) ∧
              (∀ i, Tendsto (fun n => interpD (q n t) i) atTop (𝓝 (Qd' t i))) ∧
              (∀ i, Tendsto (fun n => interpD (v n t) i) atTop (𝓝 (Vd' t i))) ∧
              (∀ i j, Tendsto (fun n => interpDD (q n t) i j) atTop (𝓝 (Qdd' t i j))) ∧
              IsContJet (Q t) (V t) (Qd' t) (Vd' t) (Qdd' t) ∧
              (∀ y (κ : Upper), normalRow (Q t y) (V t y) (A t y) (fun i => Qd' t i y)
                (fun i => Vd' t i y) (fun i j => Qdd' t i j y) κ.1.1 κ.1.2 = 0) ∧
              (t ∈ Set.Ioo 0 TL → ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t ∧
                HasDerivAt (fun τ => V τ y) (A t y) t) ∧
              (∀ n (κ : Upper),
                sn (s - 1) ⇑(cmp (interpRec (q n t)) κ.1.1 κ.1.2 - cmp (Q t) κ.1.1 κ.1.2) ≤
                  C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 2) ⇑(cmp (interpRec (v n t)) κ.1.1 κ.1.2 - cmp (V t) κ.1.1 κ.1.2) ≤
                  C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹ ∧
                sn (s - 3) ⇑(cmp (interpRec (harmonicWriterAcceleration (q n t) (v n t))) κ.1.1 κ.1.2 -
                  cmp (A t) κ.1.1 κ.1.2) ≤ C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹) ∧
              ∀ n (a b c d : Fin 4), ∃ F : CT,
                (∀ y, F y = ((riemOf (pjetField (interpRec (q n t)) (interpRec (v n t))
                    (interpRec (symRec (harmonicWriterAcceleration (q n t) (v n t))))
                    (interpD (q n t)) (interpD (v n t)) (interpDD (q n t)) y) a b c d -
                  riemOf (pjetField (Q t) (V t) (A t) (Qd' t) (Vd' t) (Qdd' t) y) a b c d : ℝ) : ℂ)) ∧
                MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * Real.exp (K * t) * (1 + t) * (Cε * ε) * ((n : ℝ) + 1)⁻¹) ∧
              ∀ y μ ν, einstein (minkowski + Q t y) (recInv (minkowski + Q t y))
                (metricJet (V t y, fun i => Qd' t i y))
                (ddArr (A t y) (fun i => Vd' t i y) (fun i j => Qdd' t i j y)) μ ν = 0 := by
  obtain ⟨δ1, hδ1, h1⟩ := writer_limit_hyp s hs
  obtain ⟨δ2, hδ2, K, hK, C, hC, h2⟩ := writer_limit_curvature_rate_sym s (by omega)
  obtain ⟨δM, hδM, CM, hCM, hprep⟩ := prep_moser s (by omega)
  obtain ⟨εL, hεL, TL, hTL, CL, hCL, hlife⟩ := open_writer_lifespan s (by omega)
  obtain ⟨CS, hCS, hsamp⟩ := Xnorm_sample_le s (by omega)
  set Cp : ℝ := 1 + CM
  have hCp : 0 ≤ Cp := by positivity
  set Cε : ℝ := (1 + CL * CS) * Cp
  have hCε : 0 ≤ Cε := by positivity
  have hCpε : Cp ≤ Cε := by
    have : 0 ≤ CL * CS * Cp := by positivity
    simp only [Cε]; nlinarith
  refine ⟨min (min δM (εL / (CS * Cp + 1))) (min (δ1 / (Cε + 1)) (δ2 / (Cε + 1))),
    by positivity, TL, hTL, K, hK, C, hC, Cε, hCε,
    fun Q₀ Kr Qd Kd Qdd ε hD hsz hεs => ?_⟩
  have hεM : ε ≤ δM := hεs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεL' : ε ≤ εL / (CS * Cp + 1) := hεs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ δ1 / (Cε + 1) := hεs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : ε ≤ δ2 / (Cε + 1) := hεs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA0 : 0 ≤ ccoordSum (s + 1) bM Q₀ := ccoordSum_nonneg _ _ _
  have hB0 : 0 ≤ ccoordSum s bM Kr := ccoordSum_nonneg _ _ _
  have hε0 : 0 ≤ ε := (add_nonneg hA0 hB0).trans hsz
  have hA : ccoordSum (s + 1) bM Q₀ ≤ ε := by unfold dataSize at hsz; linarith
  obtain ⟨V₀, hV₀, hVreg, hVb⟩ := hprep Q₀ Kr Qd hD.dQ hD.regQ hD.regK (hA.trans hεM)
  -- the prepared data
  have hVsym : ∀ y μ ν, V₀ y μ ν = V₀ y ν μ := by
    intro y μ ν
    rw [hV₀]
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp only [prepFun, sliceMat_zero_zero, sliceMat_zero_succ, sliceMat_succ_zero,
        sliceMat_succ_succ, Matrix.of_apply]
    rw [hD.symK y i.succ j.succ]
  have hcT : contTop s Q₀ V₀ ≤ Cp * ε := by
    unfold contTop
    have := mul_le_mul_of_nonneg_left hsz hCM
    unfold dataSize at this
    simp only [Cp]; nlinarith
  have hX0 : ∀ N [NeZero N], Xnorm s (sampleRec N ⇑Q₀) (sampleRec N ⇑V₀) ≤ CS * (Cp * ε) :=
    fun N _ => (hsamp N Q₀ V₀ hD.regQ hVreg).trans (mul_le_mul_of_nonneg_left hcT hCS)
  have hXL : CS * (Cp * ε) ≤ εL := by
    have h := hεL'
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hex : ∀ n : ℕ, ∃ qv : (ℝ → Grid (n + 1) → MetricRec) × (ℝ → Grid (n + 1) → MetricRec),
      qv.1 0 = sampleRec (n + 1) ⇑Q₀ ∧ qv.2 0 = sampleRec (n + 1) ⇑V₀ ∧
      IsWriterSolution TL qv.1 qv.2 ∧ ∀ t ∈ Set.Icc 0 TL, Xnorm s (qv.1 t) (qv.2 t) ≤
        CL * Xnorm s (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀) := by
    intro n
    obtain ⟨q, v, h1, h2, h3, h4⟩ := (hlife (n + 1) (sampleRec (n + 1) ⇑Q₀)
      (sampleRec (n + 1) ⇑V₀) (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym)
      ((hX0 (n + 1)).trans hXL)).1
    exact ⟨(q, v), h1, h2, h3, h4⟩
  choose qv hq0 hv0 hsol hXqv using hex
  set q : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec := fun n => (qv n).1
  set v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec := fun n => (qv n).2
  have hW : WriterData s TL q v Q₀ V₀ (Cε * ε) := by
    refine ⟨hsol, hq0, hv0, hD.symQ, hVsym, hD.regQ, hVreg, hcT.trans
      (mul_le_mul_of_nonneg_right hCpε hε0), fun n t ht => (hXqv n t ht).trans ?_⟩
    have := mul_le_mul_of_nonneg_left (hX0 (n + 1)) hCL
    have h' : CL * (CS * (Cp * ε)) ≤ Cε * ε := by
      simp only [Cε]
      have : 0 ≤ Cp * ε := by positivity
      nlinarith
    linarith
  have hεδ1 : Cε * ε ≤ δ1 := by
    rw [le_div_iff₀ (by positivity)] at hε1; nlinarith
  have hεδ2 : Cε * ε ≤ δ2 := by
    rw [le_div_iff₀ (by positivity)] at hε2; nlinarith
  refine ⟨V₀, hV₀, q, v, fun n => ⟨hsol n, hq0 n, hv0 n⟩, fun n q' v' h1 h2 h3 t ht =>
    (hlife (n + 1) (sampleRec (n + 1) ⇑Q₀) (sampleRec (n + 1) ⇑V₀)
      (isSymRec_sampleRec hD.symQ) (isSymRec_sampleRec hVsym) ((hX0 (n + 1)).trans hXL)).2
      q' v' (q n) (v n) h1 h2 (hq0 n) (hv0 n) h3 (hsol n) t ht, ?_⟩
  -- the limit
  have hW' := hW
  obtain ⟨-, -, -, hQs, -, hQ, hV, hX0', hXq⟩ := hW'
  obtain ⟨Q, V, A, Qd', Vd', Qdd', hQ0, hV0, hcr⟩ := h2 TL q v Q₀ V₀ (Cε * ε) hsol hq0 hv0 hQs
    hVsym hQ hV hX0' hXq hεδ2
  obtain ⟨hF, hlim⟩ := h1 TL q v Q₀ V₀ (Cε * ε) hW hεδ1 hTL.le
  refine ⟨Q, V, A, Qd', Vd', Qdd', hQ0, hV0, fun t ht => ⟨hcr t ht, ?_⟩⟩
  have eQ : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).Q τ = ⇑(Q τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).1 (hcr τ hτ).1
    show ⇑(limF (famQ q []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eV : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).V τ = ⇑(V τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.1 (hcr τ hτ).2.1
    show ⇑(limF (famV v []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eA : ∀ τ ∈ Set.Icc 0 TL, (limField q v TL).A τ = ⇑(A τ) := fun τ hτ => by
    have e := tendsto_nhds_unique (hlim τ hτ).2.2 (hcr τ hτ).2.2.1
    show ⇑(limF (famA q v []) (clampT TL τ)) = _
    rw [clampT_of_mem hτ, e]
  have eQd : ∀ τ ∈ Set.Icc 0 TL, ∀ i, (limField q v TL).Qd τ i = ⇑(Qd' τ i) := fun τ hτ i => by
    have h' := hF.xQ τ hτ i
    rw [eQ τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dQ i)
  have eQdd : ∀ τ ∈ Set.Icc 0 TL, ∀ i j, (limField q v TL).Qdd τ i j = ⇑(Qdd' τ i j) :=
    fun τ hτ i j => by
      have h' := hF.xQd τ hτ i j
      rw [eQd τ hτ j] at h'
      exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dQd i j)
  have eVd : ∀ τ ∈ Set.Icc 0 TL, ∀ i, (limField q v TL).Vd τ i = ⇑(Vd' τ i) := fun τ hτ i => by
    have h' := hF.xV τ hτ i
    rw [eV τ hτ] at h'
    exact isLineDeriv_unique h' ((hcr τ hτ).2.2.2.2.2.2.2.1.dV i)
  -- the initial slice from the data
  have h0 : (0 : ℝ) ∈ Set.Icc 0 TL := ⟨le_rfl, hTL.le⟩
  set F := limField q v TL
  have fQ : F.Q 0 = ⇑Q₀ := by rw [eQ 0 h0, hQ0]
  have fV : F.V 0 = ⇑V₀ := by rw [eV 0 h0, hV0]
  have fQd : ∀ k, F.Qd 0 k = ⇑(Qd k) := fun k => by
    have h' := hF.xQ 0 h0 k
    rw [fQ] at h'
    exact isLineDeriv_unique h' (hD.dQ k)
  have fQdd : ∀ k l, F.Qdd 0 k l = ⇑(Qdd k l) := fun k l => by
    have h' := hF.xQd 0 h0 k l
    rw [fQd l] at h'
    exact isLineDeriv_unique h' (hD.dQd k l)
  have qt : ∀ y μ, Q₀ y μ 0 = 0 := fun y μ => by rw [hD.symQ]; exact hD.timeQ y μ
  have qdt : ∀ k y μ, Qd k y 0 μ = 0 ∧ Qd k y μ 0 = 0 := fun k y μ =>
    ⟨isLineDeriv_comp_unique (hD.dQ k) (isLineDeriv_zero k) (fun x => hD.timeQ x μ) y,
     isLineDeriv_comp_unique (hD.dQ k) (isLineDeriv_zero k) (fun x => qt x μ) y⟩
  have qddt : ∀ k l y μ, Qdd k l y 0 μ = 0 ∧ Qdd k l y μ 0 = 0 := fun k l y μ =>
    ⟨isLineDeriv_comp_unique (hD.dQd k l) (isLineDeriv_zero k) (fun x => (qdt l x μ).1) y,
     isLineDeriv_comp_unique (hD.dQd k l) (isLineDeriv_zero k) (fun x => (qdt l x μ).2) y⟩
  have hI : F.InitData := by
    intro x
    have hdet : (Matrix.of (minkowski + Q₀ x)).det ≠ 0 := by
      have := hF.det_ne h0 x; rwa [fQ] at this
    obtain ⟨hblk, hγγ⟩ := inv_block (g := minkowski + Q₀ x)
      (by simp [minkowski, hD.timeQ]) (fun i => by simp [minkowski, hD.timeQ, fin_zero_ne_succ])
      (fun i => by simp [minkowski, qt, Fin.succ_ne_zero]) hdet
    set S0 := dataSlice ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) (fun i => ⇑(Kd i)) (fun i j => ⇑(Qdd i j)) x
    set S : SliceData := { S0 with
      dv00 := (fun k => F.Vd 0 k x 0 0)
      dv0 := (fun k i => F.Vd 0 k x 0 i.succ)
      w := Matrix.of (F.A 0 x) }
    have hSv : S.Valid := by
      refine ⟨hγγ, ?_, ?_, fun k => ?_, fun k l => ?_, fun k l => ?_, ?_, fun k => ?_, ?_⟩
      · ext i j; simp [S, S0, dataSlice, hD.symQ x, minkowski_symm]
      · ext i j
        exact recInv_symm (fun μ ν => by simp only [Pi.add_apply, hD.symQ x μ ν, minkowski_symm μ ν])
          j.succ i.succ
      · ext i j
        have := hF.sQd 0 k x j.succ i.succ
        rw [fQd] at this
        exact this
      · ext i j
        have := hF.sQdd 0 k l x j.succ i.succ
        rw [fQdd] at this
        exact this
      · ext i j
        have := congrFun (congrFun (hF.iQdd 0 k l) x) i.succ
        rw [fQdd, fQdd] at this
        exact congrFun this j.succ
      · ext i j; simp [S, S0, dataSlice, hD.symK x]
      · ext i j
        have h := isLineDeriv_comp_unique (hD.dK k) (isLineDeriv_entry (hD.dK k) j.succ i.succ)
          (fun y => hD.symK y i.succ j.succ) x
        first | exact h | exact h.symm
      · ext μ ν; exact hF.sA 0 x ν μ
    refine ⟨S, hSv, ⟨rfl, fun l => rfl⟩, hD.ham x, hD.mom x, ?_, ?_, ?_, ?_⟩
    · show Matrix.of (minkowski + F.Q 0 x) = sliceMat (-1) 0 S0.γ
      rw [fQ]
      ext μ ν
      refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
        simp [S0, dataSlice, minkowski, hD.timeQ, qt, Fin.succ_ne_zero, fin_zero_ne_succ]
    · show (Matrix.of (minkowski + F.Q 0 x))⁻¹ = sliceMat (-1) 0 S0.γi
      rw [fQ]; exact hblk
    · funext a
      refine Fin.cases ?_ (fun k => ?_) a
      · show Matrix.of (F.V 0 x) = sliceMat S0.v00 S0.v0 ((-2 : ℝ) • S0.K)
        rw [fV, hV₀]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, prepFun]
      · show Matrix.of (F.Qd 0 k x) = sliceMat 0 0 (S0.dγ k)
        rw [fQd]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, (qdt k x _).1, (qdt k x _).2]
    · have hVdsp : ∀ (l i j : Fin 3), F.Vd 0 l x i.succ j.succ = -2 * Kd l x i.succ j.succ := by
        intro l i j
        refine isLineDeriv_comp_unique (hF.xV 0 h0 l) (f := fun y => -2 * Kr y i.succ j.succ)
          (f' := fun y => -2 * Kd l y i.succ j.succ)
          (fun y => ((isLineDeriv_entry (hD.dK l) i.succ j.succ) y).const_mul (-2)) (fun y => ?_) x
        rw [fV, hV₀]; simp [prepFun]
      have hdtk : ∀ l, Matrix.of (F.Vd 0 l x) = S.dtk l := by
        intro l
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
        · rfl
        · rfl
        · show F.Vd 0 l x i.succ 0 = F.Vd 0 l x 0 i.succ
          exact hF.sVd 0 l x _ _
        · show F.Vd 0 l x i.succ j.succ = ((-2 : ℝ) • S0.dK l) i j
          rw [hVdsp]; simp [S0, dataSlice]
      funext a b
      refine Fin.cases ?_ (fun k => ?_) a <;> refine Fin.cases ?_ (fun l => ?_) b
      · rfl
      · exact hdtk l
      · exact hdtk k
      · show Matrix.of (F.Qdd 0 k l x) = sliceMat 0 0 (S0.ddγ k l)
        rw [fQdd]
        ext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
          simp [S0, dataSlice, (qddt k l x _).1, (qddt k l x _).2]
  intro y μ ν
  have hE := hF.einstein_eq_zero hTL hI t ht y μ ν
  have r1 := congrFun (eQ t ht) y
  have r2 := congrFun (eV t ht) y
  have r3 := congrFun (eA t ht) y
  have r4 : (fun i => F.Qd t i y) = fun i => Qd' t i y := funext fun i => congrFun (eQd t ht i) y
  have r5 : (fun i => F.Vd t i y) = fun i => Vd' t i y := funext fun i => congrFun (eVd t ht i) y
  have r6 : (fun i j => F.Qdd t i j y) = fun i j => Qdd' t i j y :=
    funext fun i => funext fun j => congrFun (eQdd t ht i j) y
  rw [r1, r2, r3, r4, r5, r6] at hE
  exact hE


/-- Non-vacuity: the flat data `γ = I`, `K = 0` belong to `D_s(ε)` for every `s`. -/
theorem dsData_zero (s : ℕ) : DsData s 0 0 (fun _ => 0) (fun _ => 0) (fun _ _ => 0) where
  symQ := fun _ _ _ => rfl
  symK := fun _ _ _ => rfl
  timeQ := fun _ _ => rfl
  timeK := fun _ _ => rfl
  dQ := fun i => isLineDeriv_zero i
  dQd := fun i _ => isLineDeriv_zero i
  dK := fun i => isLineDeriv_zero i
  regQ := fun k => by rw [ccoord_zero]; exact memH_zero _
  regK := fun k => by rw [ccoord_zero]; exact memH_zero _
  ham := fun x => by
    simp [SliceData.hamC, SliceData.trK, SliceData.normK2, dataSlice, Jet3.scal,
      Jet3.ricM, Jet3.riem, Jet3.dchr, Jet3.chr, Jet3.low, Jet3.dlow, SliceData.spatial,
      Matrix.trace, Matrix.diag, Matrix.mul_apply]
  mom := fun x i => by
    simp [SliceData.momC, SliceData.divK, SliceData.dtrK, dataSlice, Jet3.chr,
      Jet3.low, Jet3.dG, SliceData.spatial]

end

end RenewalGeometry.OpenWriterLimitRegularity
