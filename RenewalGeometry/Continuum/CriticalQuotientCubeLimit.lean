/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientSections

/-!
# The limit packet on a Coulomb cube and the convergence of the rows
  (`thm:critical-quotient-defect`, `app:critical-quotient-proof`; Einstein–Standard-Model
  action-closure manuscript)

On one Coulomb cube `Q`, from the quotient limits of the chart extraction (`QuotientLimit`: the
connection entries `Ã → A_∞` in `L^q`, `q < 4`, weak gradients, weak curvature; the transported
matter `R u → u_∞` in `L^q`, `q < 4`, weak gradients and weak covariant derivatives) and the
coframe limit, this file builds the limit packet `limitOf …` (a `LimitFields`: coframe, its
gradient, connection, curvature `F_{A_∞}`, Higgs doublet, `D_{A_∞}H_∞`, spinor and dual spinor with
their gradients) and verifies, for the jets `J_n = j(R_n·z_n)` of the gauge-transformed fields, all
the hypotheses of `cube_rows_tendsto`:

* `coframe_cube`: coframe convergence in measure inside the compact chart set and `∂e_n → ∂e` in
  `L²(Q)`;
* `strong_fields_cube`: `A, H, Ψ, Ψ̄` converge in `L²(Q)`; `L⁴` bounds of `H, Ψ, Ψ̄` from the
  `W^{1,2}` bounds (critical Sobolev);
* `weak_F_cube`, `weak_K_cube`, `weak_D_cube`: weak `L²(Q)` convergence with uniform bounds of the
  curvature, of `D_{A}H` and of the spinor gradients (upgraded from bounded to `L²` weights by the
  uniform `L²` bounds).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure
  BallAnalysis.SMGaugeStructure SMGaugeLie EinsteinSM SMGaugeJet CurvatureCovariance
  FirstVariationCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### The limit packet -/

/-- **The limit packet on a Coulomb cube** built from the coframe limit `(e₀, de₀)` and the
quotient limits `(A_∞, ∂A_∞, u_∞, ∂u_∞)` of the transported sections (`matterSec` indexing). -/
def limitOf (e₀ : E4 → CoframeFibre) (de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ)
    (Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ) (GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ)
    (uinf : MIdx → Fin 5 → E4 → ℂ) (Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ) :
    LimitFields (Fin 5) where
  e := e₀
  de := fun x i p => ((de₀ p.1 p.2 i x : ℝ) : ℂ)
  A := fun x μ c e => Ainf μ c e x
  F := fun x μ ν c e => curvatureW Ainf GA μ ν c e x
  H := fun x i => uinf none (Fin.natAdd 3 i) x
  K := fun x μ i => Gu none (Fin.natAdd 3 i) μ x + ∑ e, Ainf μ (Fin.natAdd 3 i) e x * uinf none e x
  Ψ := fun x s c => uinf (some (Sum.inl s)) c x
  dΨ := fun x i p => Gu (some (Sum.inl p.1)) p.2 i x
  Ψb := fun x s c => star (uinf (some (Sum.inr s)) c x)
  dΨb := fun x i p => star (Gu (some (Sum.inr p.1)) p.2 i x)

/-! ### Coframes on a cube -/

section Coframe

variable {a b lo hi : E4}

theorem eLpNorm_restrict_mono_set {F : Type*} [NormedAddCommGroup F] {f : E4 → F} {p : ℝ≥0∞}
    {S T : Set E4} (h : S ⊆ T) : eLpNorm f p (volume.restrict S) ≤ eLpNorm f p (volume.restrict T) :=
  eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl)

theorem tendsto_restrict_mono {F : Type*} [NormedAddCommGroup F] {f : ℕ → E4 → F} {p : ℝ≥0∞}
    {S T : Set E4} (h : S ⊆ T) (ht : Tendsto (fun n => eLpNorm (f n) p (volume.restrict T)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p (volume.restrict S)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    fun _ => eLpNorm_restrict_mono_set h

theorem isCompact_closure_box (lo hi : E4) : IsCompact (closure (box lo hi)) := by
  refine (isCompact_univ_pi fun i => isCompact_Icc (a := lo i) (b := hi i)).of_isClosed_subset
    isClosed_closure ?_
  exact closure_minimal (Set.pi_mono fun i _ => Ioo_subset_Icc_self)
    (isClosed_set_pi fun i _ => isClosed_Icc)

/-- Continuous functions are in every `L^p` of a box. -/
theorem memLp_box_of_continuous {F : Type*} [NormedAddCommGroup F] {f : E4 → F}
    (hf : Continuous f) (lo hi : E4) (p : ℝ≥0∞) : MemLp f p (volume.restrict (box lo hi)) :=
  memLp_of_continuousOn_closure (isOpen_box lo hi) (isCompact_closure_box lo hi)
    hf.continuousOn p

/-- **The coframe hypotheses of `cube_rows_tendsto` on a cube** from the coframe limit on the
chart and the uniform nondegeneracy (values in a compact subset of the chart). -/
theorem coframe_cube (hQK : box lo hi ⊆ box a b) {e : ℕ → E4 → CoframeFibre}
    (he : ∀ n, ContDiff ℝ ∞ (e n)) {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hKeGL : Ke ⊆ coframeGL) (heK : ∀ n, ∀ x ∈ box a b, e n x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
    (hL2 : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => e k y i ν - e₀ y i ν) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hd : ∀ i ν μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => e k y i ν) μ y - de₀ i ν μ y) 2
      (volume.restrict (box a b))) atTop (𝓝 0)) :
    CoframeConv (volume.restrict (box lo hi)) Ke (fun n x => e n x) e₀ ∧
      RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2 (fun n x => fun i => pd (e n) i x)
        (fun x => fun i a ν => de₀ a ν i x) := by
  set μ := volume.restrict (box lo hi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  have hle : μ ≤ volume.restrict (box a b) := Measure.restrict_mono hQK le_rfl
  have hecont : ∀ n, Continuous (e n) := fun n => (he n).continuous
  have he2 : RenewalGeometry.LpTendsto μ 2 (fun n x => e n x) e₀ := by
    refine lpTendsto_pi (by norm_num) fun i => lpTendsto_pi (by norm_num) fun ν =>
      ⟨fun n => memLp_box_of_continuous
        ((continuous_apply ν).comp ((continuous_apply i).comp (hecont n))) lo hi 2,
        ((he₀ i ν).mono_measure hle).mono_exponent le_top, tendsto_restrict_mono hQK (hL2 i ν)⟩
  have hTM : TendstoInMeasure μ (fun n x => e n x) atTop e₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun n => (he2.memLp n).1) he2.memLp_lim.1
      he2.tendsto
  refine ⟨⟨hKe, hKeGL, fun n => (hecont n).aemeasurable, fun n =>
    (ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx => heK n x (hQK hx)), ?_, hTM⟩, ?_⟩
  · obtain ⟨ns, -, hns⟩ := hTM.exists_seq_tendsto_ae
    filter_upwards [hns, (ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx => hx)]
      with x hx hxQ
    exact hKe.isClosed.mem_of_tendsto hx (Eventually.of_forall fun k => heK _ x (hQK hxQ))
  · refine lpTendsto_pi (by norm_num) fun i => lpTendsto_pi (by norm_num) fun a' =>
      lpTendsto_pi (by norm_num) fun ν => ⟨fun n => ?_, (hde₀ a' ν i).mono_measure hle, ?_⟩
    · have hc : Continuous fun x => pd (fun y => e n y a' ν) i x :=
        (((contDiff_apply ℝ ℝ ν).comp ((contDiff_apply ℝ _ a').comp (he n))).continuous_fderiv
          (by simp)).clm_apply continuous_const
      have e1 : (fun x => pd (e n) i x a' ν) = fun x => pd (fun y => e n y a' ν) i x := by
        funext x
        have hdx : DifferentiableAt ℝ (e n) x := ((he n).differentiable (by simp)) x
        rw [pd_apply_gen (differentiableAt_apply_gen hdx a') i ν, pd_apply_gen hdx i a']
      show MemLp (fun x => pd (e n) i x a' ν) 2 μ
      rw [e1]
      exact memLp_box_of_continuous hc lo hi 2
    · have e1 : ∀ n, (fun x => pd (e n) i x a' ν) = fun x => pd (fun y => e n y a' ν) i x := by
        intro n
        funext x
        have hdx : DifferentiableAt ℝ (e n) x := ((he n).differentiable (by simp)) x
        rw [pd_apply_gen (differentiableAt_apply_gen hdx a') i ν, pd_apply_gen hdx i a']
      have := tendsto_restrict_mono hQK (hd a' ν i)
      refine this.congr fun n => ?_
      congr 1
      funext x
      simp only [Pi.sub_apply]
      rw [← congrFun (e1 n) x]

end Coframe


/-! ### Strong convergence of the fields on a cube -/

section Strong

variable {lo hi : E4}

theorem lpTendsto_of_quot {f : ℕ → E4 → ℂ} {f₀ : E4 → ℂ} {g : ℕ → Fin 4 → E4 → ℂ}
    {g₀ : Fin 4 → E4 → ℂ} (hW : ∀ n, MemW12 (box lo hi) (f n) (g n))
    (hW₀ : MemW12 (box lo hi) f₀ g₀)
    (h : Tendsto (fun n => eLpNorm (f n - f₀) 2 (volume.restrict (box lo hi))) atTop (𝓝 0)) :
    RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2 f f₀ :=
  ⟨fun n => (hW n).memLp, hW₀.memLp, h⟩

theorem aesm_pi {X ι F : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    [NormedAddCommGroup F] {f : X → ι → F}
    (h : ∀ i, AEStronglyMeasurable (fun x => f x i) μ) : AEStronglyMeasurable f μ := by
  classical
  have e : f = ∑ i, (Pi.single i) ∘ (fun x => f x i) := by ext x j; simp
  rw [e]
  exact Finset.aestronglyMeasurable_sum _ fun i _ =>
    (Isometry.single (E := fun _ : ι => F) i).continuous.comp_aestronglyMeasurable (h i)

theorem lpTendsto_star {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℂ}
    {f₀ : X → ℂ} {p : ℝ≥0∞} (h : RenewalGeometry.LpTendsto μ p f f₀) :
    RenewalGeometry.LpTendsto μ p (fun n x => star (f n x)) (fun x => star (f₀ x)) := by
  have hs : ∀ {g : X → ℂ}, MemLp g p μ → MemLp (fun x => star (g x)) p μ := fun {g} hg =>
    ⟨(Complex.continuous_conj.comp_aestronglyMeasurable hg.1), by
      rw [eLpNorm_congr_norm_ae (g := g) (Eventually.of_forall fun x => norm_star (g x))]
      exact hg.2⟩
  refine ⟨fun n => hs (h.memLp n), hs h.memLp_lim, ?_⟩
  have e : ∀ n, eLpNorm ((fun x => star (f n x)) - fun x => star (f₀ x)) p μ =
      eLpNorm (f n - f₀) p μ := fun n =>
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, ← star_sub, norm_star])
  simpa only [e] using h.tendsto

/-- **Strong `L²` convergence of `A, H, Ψ, Ψ̄` on a Coulomb cube and uniform `L⁴` bounds of
`H, Ψ, Ψ̄`.** -/
theorem strong_fields_cube (hlh : ∀ i, lo i < hi i) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e, Tendsto (fun n => eLpNorm (entries (gaugeConn (R n) (connM (z n).A)) ν c e -
      Ainf ν c e) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0)) :
    RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2
        (fun n x => (redJet (gaugeTuple (R n) (z n)) x).A) (fun x μ c e => Ainf μ c e x) ∧
      RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2
        (fun n x => (redJet (gaugeTuple (R n) (z n)) x).H)
        (fun x i => uinf none (Fin.natAdd 3 i) x) ∧
      RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2
        (fun n x => (redJet (gaugeTuple (R n) (z n)) x).Ψ)
        (fun x s c => uinf (some (Sum.inl s)) c x) ∧
      RenewalGeometry.LpTendsto (volume.restrict (box lo hi)) 2
        (fun n x => (redJet (gaugeTuple (R n) (z n)) x).Ψb)
        (fun x s c => star (uinf (some (Sum.inr s)) c x)) ∧
      ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n,
        eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).H) 4 (volume.restrict (box lo hi))
          ≤ M ∧
        eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψ) 4 (volume.restrict (box lo hi))
          ≤ M ∧
        eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb) 4
          (volume.restrict (box lo hi)) ≤ M := by
  set μ := volume.restrict (box lo hi)
  have hH : ∀ n x i, (redJet (gaugeTuple (R n) (z n)) x).H i =
      transp (R n) (matterSec (z n) none) (Fin.natAdd 3 i) x := fun n x i => by
    show (gaugeTuple (R n) (z n)).H x i = _
    rw [gaugeTuple_H_eq]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lpTendsto_pi (by norm_num) fun μ' => lpTendsto_pi (by norm_num) fun c =>
      lpTendsto_pi (by norm_num) fun e => lpTendsto_of_quot (fun n => hWA n μ' c e) (q1 μ' c e)
        (q2 μ' c e)
  · refine lpTendsto_pi (by norm_num) fun i => ?_
    have := lpTendsto_of_quot (fun n => hWu n none (Fin.natAdd 3 i)) (q5 none (Fin.natAdd 3 i))
      (q6 none (Fin.natAdd 3 i))
    exact this.congr (fun n => Eventually.of_forall fun x => (hH n x i).symm)
      (Eventually.of_forall fun x => rfl)
  · exact lpTendsto_pi (by norm_num) fun s => lpTendsto_pi (by norm_num) fun c =>
      lpTendsto_of_quot (fun n => hWu n (some (Sum.inl s)) c) (q5 (some (Sum.inl s)) c)
        (q6 (some (Sum.inl s)) c)
  · refine lpTendsto_pi (by norm_num) fun s => lpTendsto_pi (by norm_num) fun c => ?_
    have := lpTendsto_star (lpTendsto_of_quot (fun n => hWu n (some (Sum.inr s)) c)
      (q5 (some (Sum.inr s)) c) (q6 (some (Sum.inr s)) c))
    exact this.congr (fun n => Eventually.of_forall fun x =>
      (gaugeTuple_Ψb_eq (R := R n) (z := z n) x s c).symm) (Eventually.of_forall fun x => rfl)
  · obtain ⟨CS, hCS⟩ := exists_sobolev_L4_box (ι := Fin 4) (by simp) hlh
    have h4 : ∀ n s c, eLpNorm (transp (R n) (matterSec (z n) s) c) 4 μ ≤ CS * Bu := fun n s c =>
      (hCS _ _ (hWu n s c)).trans (mul_le_mul_of_nonneg_left (hBu' n s c) bot_le)
    have hm : ∀ n s c, AEStronglyMeasurable (transp (R n) (matterSec (z n) s) c) μ :=
      fun n s c => (hWu n s c).memLp.1
    refine ⟨40 * (CS * Bu), ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.coe_ne_top
      hBu), fun n => ⟨?_, ?_, ?_⟩⟩
    · calc _ ≤ ∑ i, eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).H i) 4 μ :=
            eLpNorm_pi_le (fun i => (hm n none (Fin.natAdd 3 i)).congr
              (Eventually.of_forall fun x => (hH n x i).symm)) (by norm_num)
        _ ≤ ∑ _i : Fin 2, CS * Bu := Finset.sum_le_sum fun i _ => by
            rw [show (fun x => (redJet (gaugeTuple (R n) (z n)) x).H i) =
              transp (R n) (matterSec (z n) none) (Fin.natAdd 3 i) from funext fun x => hH n x i]
            exact h4 n none _
        _ ≤ 40 * (CS * Bu) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            gcongr; norm_num
    · calc _ ≤ ∑ s, eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψ s) 4 μ :=
            eLpNorm_pi_le (fun s => aesm_pi fun c =>
              hm n (some (Sum.inl s)) c) (by norm_num)
        _ ≤ ∑ _s : Fin 4, ∑ _c : Fin 5, CS * Bu := Finset.sum_le_sum fun s _ =>
            (eLpNorm_pi_le (fun c => hm n (some (Sum.inl s)) c) (by norm_num)).trans
              (Finset.sum_le_sum fun c _ => h4 n _ c)
        _ ≤ 40 * (CS * Bu) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← mul_assoc]; gcongr; norm_num
    · have hb : ∀ s c, eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s c) 4 μ ≤
          CS * Bu := fun s c => by
        rw [show (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s c) =
            fun x => star (transp (R n) (matterSec (z n) (some (Sum.inr s))) c x) from
          funext fun x => gaugeTuple_Ψb_eq (R := R n) (z := z n) x s c]
        rw [eLpNorm_congr_norm_ae (g := transp (R n) (matterSec (z n) (some (Sum.inr s))) c)
          (Eventually.of_forall fun x => norm_star _)]
        exact h4 n _ c
      have hmb : ∀ s c, AEStronglyMeasurable
          (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s c) μ := fun s c =>
        (Complex.continuous_conj.comp_aestronglyMeasurable (hm n (some (Sum.inr s)) c)).congr
          (Eventually.of_forall fun x => (gaugeTuple_Ψb_eq (R := R n) (z := z n) x s c).symm)
      calc _ ≤ ∑ s, eLpNorm (fun x => (redJet (gaugeTuple (R n) (z n)) x).Ψb s) 4 μ :=
            eLpNorm_pi_le (fun s => aesm_pi fun c => hmb s c)
              (by norm_num)
        _ ≤ ∑ _s : Fin 4, ∑ _c : Fin 5, CS * Bu := Finset.sum_le_sum fun s _ =>
            (eLpNorm_pi_le (fun c => hmb s c) (by norm_num)).trans
              (Finset.sum_le_sum fun c _ => hb s c)
        _ ≤ 40 * (CS * Bu) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← mul_assoc]; gcongr; norm_num

end Strong


/-! ### Weak convergence of the curvature, `D_AH` and the spinor gradients -/

section Weak

variable {lo hi : E4}

theorem WeakL2Data.congr_ae {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W W' : ℕ → E4 → V} {W₀ W₀' : E4 → V} (h : WeakL2Data lo hi W W₀)
    (hW : ∀ n, W n =ᵐ[volume.restrict (box lo hi)] W' n)
    (hW₀ : W₀ =ᵐ[volume.restrict (box lo hi)] W₀') : WeakL2Data lo hi W' W₀' := by
  obtain ⟨h1, h2, ⟨B, hB⟩, h4⟩ := h
  refine ⟨fun n => (h1 n).ae_eq (hW n), h2.ae_eq hW₀, ⟨B, fun n => by
    rw [← eLpNorm_congr_ae (hW n)]; exact hB n⟩, fun ℓ g hg => ?_⟩
  have e : ∀ (U U' : E4 → V), U =ᵐ[volume.restrict (box lo hi)] U' →
      ∫ x, g x * ℓ (U x) ∂(volume.restrict (box lo hi)) =
        ∫ x, g x * ℓ (U' x) ∂(volume.restrict (box lo hi)) := fun U U' hU =>
    integral_congr_ae (hU.mono fun x hx => by simp only [hx])
  simp only [← e _ _ (hW _), ← e _ _ hW₀]
  exact h4 ℓ g hg

theorem eLpNorm_component_le {X ι F : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    [NormedAddCommGroup F] (f : X → ι → F) (i : ι) (p : ℝ≥0∞) :
    eLpNorm (fun x => f x i) p μ ≤ eLpNorm f p μ :=
  eLpNorm_mono fun x => norm_le_pi_norm (f x) i

theorem toReal_bound_of_le {a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  ENNReal.toReal_mono hb h

/-- Scalar weak data from convergence against bounded weights and a uniform `L²` bound. -/
theorem weakL2Data_scalar {W : ℕ → E4 → ℂ} {W₀ : E4 → ℂ}
    (hW : ∀ n, MemLp (W n) 2 (volume.restrict (box lo hi)))
    (hW₀ : MemLp W₀ 2 (volume.restrict (box lo hi))) {B : ℝ}
    (hB : ∀ n, (eLpNorm (W n) 2 (volume.restrict (box lo hi))).toReal ≤ B)
    (h : ∀ w : E4 → ℝ, MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • W n x ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • W₀ x ∂(volume.restrict (box lo hi))))) :
    WeakL2Data lo hi W W₀ := by
  have : IsFiniteMeasure (volume.restrict (box lo hi)) :=
    isFiniteMeasure_restrict.mpr (volume_box_ne_top lo hi)
  exact ⟨hW, hW₀, ⟨B, hB⟩, weakL2_of_real_weights hW hW₀ fun w hw =>
    tendsto_L2_weights hW hW₀ hB h hw⟩

/-- Weak data of `Π`-valued maps from that of the components. -/
theorem weakL2Data_pi {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : ℕ → E4 → ι → V} {W₀ : E4 → ι → V} (h : ∀ i, WeakL2Data lo hi (fun n x => W n x i)
      (fun x => W₀ x i)) : WeakL2Data lo hi W W₀ := by
  choose h1 h2 hB h4 using h
  choose B hB using hB
  refine ⟨fun n => memLp_pi_iff.mpr fun i => h1 i n, memLp_pi_iff.mpr h2,
    ⟨∑ i, B i, fun n => ?_⟩, weakL2_pi (fun n => memLp_pi_iff.mpr fun i => h1 i n)
      (memLp_pi_iff.mpr h2) h4⟩
  have hle := eLpNorm_pi_le (μ := volume.restrict (box lo hi)) (f := W n)
    (fun i => (h1 i n).1) (p := 2) (by norm_num)
  calc (eLpNorm (W n) 2 (volume.restrict (box lo hi))).toReal ≤
        (∑ i, eLpNorm (fun x => W n x i) 2 (volume.restrict (box lo hi))).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => (h1 i n).eLpNorm_ne_top) hle
    _ = ∑ i, (eLpNorm (fun x => W n x i) 2 (volume.restrict (box lo hi))).toReal :=
        ENNReal.toReal_sum fun i _ => (h1 i n).eLpNorm_ne_top
    _ ≤ ∑ i, B i := Finset.sum_le_sum fun i _ => hB i n

theorem weakL2Data_prod {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] {W : ℕ → E4 → V} {W₀ : E4 → V}
    {W' : ℕ → E4 → V'} {W'₀ : E4 → V'} (h : WeakL2Data lo hi W W₀)
    (h' : WeakL2Data lo hi W' W'₀) :
    WeakL2Data lo hi (fun n x => (W n x, W' n x)) (fun x => (W₀ x, W'₀ x)) := by
  obtain ⟨h1, h2, ⟨B, hB⟩, h4⟩ := h
  obtain ⟨h1', h2', ⟨B', hB'⟩, h4'⟩ := h'
  refine ⟨fun n => memLp_prodMk (h1 n) (h1' n), memLp_prodMk h2 h2', ⟨B + B', fun n => ?_⟩,
    weakL2_prod h1 h2 h1' h2' h4 h4'⟩
  have hle : eLpNorm (fun x => (W n x, W' n x)) 2 (volume.restrict (box lo hi)) ≤
      eLpNorm (W n) 2 (volume.restrict (box lo hi)) +
        eLpNorm (W' n) 2 (volume.restrict (box lo hi)) := by
    calc _ ≤ eLpNorm (fun x => ‖W n x‖ + ‖W' n x‖) 2 (volume.restrict (box lo hi)) :=
          eLpNorm_mono_real fun x => norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
            le_add_of_nonneg_left (norm_nonneg _)⟩
      _ ≤ _ := (eLpNorm_add_le (h1 n).1.norm (h1' n).1.norm (by norm_num)).trans
          (by rw [eLpNorm_norm, eLpNorm_norm])
  calc _ ≤ (eLpNorm (W n) 2 (volume.restrict (box lo hi)) +
        eLpNorm (W' n) 2 (volume.restrict (box lo hi))).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(h1 n).eLpNorm_ne_top,
          (h1' n).eLpNorm_ne_top⟩) hle
    _ = _ := ENNReal.toReal_add (h1 n).eLpNorm_ne_top (h1' n).eLpNorm_ne_top
    _ ≤ B + B' := add_le_add (hB n) (hB' n)

end Weak


section WeakFields

variable {lo hi : E4}

theorem memLp_two_mul_of_W12 (hlh : ∀ i, lo i < hi i) {f g : E4 → ℂ} {df dg : Fin 4 → E4 → ℂ}
    (hf : MemW12 (box lo hi) f df) (hg : MemW12 (box lo hi) g dg) :
    MemLp (fun x => f x * g x) 2 (volume.restrict (box lo hi)) := by
  have h4f := memLp_four_of_memW12_box hlh hf
  have h4g := memLp_four_of_memW12_box hlh hg
  have : ENNReal.HolderTriple 4 4 2 := FirstVariationCalculus.holderTriple_four_four_two
  exact h4g.mul h4f

/-- **Weak `L²` data of the spinor gradients** on a Coulomb cube. -/
theorem weak_D_cube {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}
    (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x) (hz : ∀ n x, DiffAt (z n) x)
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q7 : ∀ s c μ (w : E4 → ℝ), MemLp w 2 (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • tgrad (R n) (matterSec (z n) s) c μ x
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict (box lo hi))))) :
    WeakL2Data lo hi (fun n x => ((redJet (gaugeTuple (R n) (z n)) x).dΨ,
        (redJet (gaugeTuple (R n) (z n)) x).dΨb))
      (fun x => ((fun i s c => Gu (some (Sum.inl s)) c i x),
        (fun i s c => star (Gu (some (Sum.inr s)) c i x)))) := by
  set μQ := volume.restrict (box lo hi)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  have hgrad : ∀ n s c i, (eLpNorm (tgrad (R n) (matterSec (z n) s) c i) 2 μQ).toReal ≤
      Bu.toReal := fun n s c i => ENNReal.toReal_mono hBu ((Finset.single_le_sum
        (f := fun i => eLpNorm (tgrad (R n) (matterSec (z n) s) c i) 2 μQ)
        (fun _ _ => zero_le) (Finset.mem_univ i)).trans (le_add_self.trans (hBu' n s c)))
  have hstarM : ∀ {f : E4 → ℂ}, MemLp f 2 μQ → MemLp (fun x => star (f x)) 2 μQ := fun {f} hf =>
    ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, by
      rw [eLpNorm_congr_norm_ae (g := f) (Eventually.of_forall fun x => norm_star _)]
      exact hf.2⟩
  -- the clean sequences
  have h1 : WeakL2Data lo hi (fun n x => fun i s c => tgrad (R n) (matterSec (z n)
      (some (Sum.inl s))) c i x) (fun x i s c => Gu (some (Sum.inl s)) c i x) := by
    refine weakL2Data_pi fun i => weakL2Data_pi fun s => weakL2Data_pi fun c => ?_
    exact ⟨fun n => (hWu n _ c).memLp_grad i, (q5 _ c).memLp_grad i, ⟨Bu.toReal, fun n =>
      hgrad n _ c i⟩, weakL2_of_real_weights (fun n => (hWu n _ c).memLp_grad i)
        ((q5 _ c).memLp_grad i) fun w hw => q7 _ c i w hw⟩
  have h2 : WeakL2Data lo hi (fun n x => fun i s c => star (tgrad (R n) (matterSec (z n)
      (some (Sum.inr s))) c i x)) (fun x i s c => star (Gu (some (Sum.inr s)) c i x)) := by
    refine weakL2Data_pi fun i => weakL2Data_pi fun s => weakL2Data_pi fun c => ?_
    refine ⟨fun n => hstarM ((hWu n _ c).memLp_grad i), hstarM ((q5 _ c).memLp_grad i),
      ⟨Bu.toReal, fun n => ?_⟩, weakL2_of_real_weights (fun n => hstarM ((hWu n _ c).memLp_grad i))
        (hstarM ((q5 _ c).memLp_grad i)) fun w hw => ?_⟩
    · rw [eLpNorm_congr_norm_ae (g := tgrad (R n) (matterSec (z n) (some (Sum.inr s))) c i)
        (Eventually.of_forall fun x => norm_star _)]
      exact hgrad n _ c i
    · have e : ∀ f : E4 → ℂ, ∫ x, w x • star (f x) ∂μQ = star (∫ x, w x • f x ∂μQ) := by
        intro f
        show _ = (starRingEnd ℂ) (∫ x, w x • f x ∂μQ)
        rw [← integral_conj]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show w x • star (f x) = (starRingEnd ℂ) (w x • f x)
        rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
        rfl
      have h7 := (Complex.continuous_conj.tendsto _).comp (q7 (some (Sum.inr s)) c i w hw)
      rw [e]
      exact h7.congr fun n => (e _).symm
  refine (weakL2Data_prod h1 h2).congr_ae (fun n => ?_) (Eventually.of_forall fun x => rfl)
  refine (ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx => ?_)
  refine Prod.ext ?_ ?_
  · funext i s c
    exact (redJet_gaugeTuple_dΨ (hR n x hx) (hz n x).Ψ i s c).symm
  · funext i s c
    exact (redJet_gaugeTuple_dΨb (hR n x hx) (hz n x).Ψb i s c).symm

end WeakFields


section WeakFieldsKF

variable {lo hi : E4}

theorem continuous_covDerV_entry {𝒜 : MConn 5} (h𝒜 : ∀ μ c e, Continuous fun y => 𝒜 μ y c e)
    {η : E4 → Fin 5 → ℂ} (hη : ContDiff ℝ ∞ η) (μ : Fin 4) (e : Fin 5) :
    Continuous fun x => covDerV 𝒜 η μ x e := by
  have hc : ∀ c, ContDiff ℝ ∞ (fun y => η y c) := fun c => (contDiff_apply ℝ ℂ c).comp hη
  simp only [covDerV, Pi.add_apply, pdV, mulVec, dotProduct]
  refine Continuous.add ?_ (continuous_finset_sum _ fun k _ => (h𝒜 μ e k).mul
    ((continuous_apply k).comp hη.continuous))
  exact ((hc e).continuous_fderiv (by simp)).clm_apply continuous_const

theorem norm_higgsG_apply_le {g : M5} (hg : g ∈ unitaryGroup (Fin 5) ℂ) (v : HiggsFibre)
    (i : Fin 2) : ‖higgsG g v i‖ ≤ ∑ j, ‖v j‖ := by
  simp only [higgsG, mulVec, dotProduct, wk, submatrix_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_entry_le_one hg _ _)

/-- **Weak `L²` data of the covariant Higgs gradient** on a Coulomb cube. -/
theorem weak_K_cube (hlh : ∀ i, lo i < hi i) {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}
    (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x) (hz : ∀ n x, DiffAt (z n) x)
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie)
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B) :
    WeakL2Data lo hi (fun n x => (redJet (gaugeTuple (R n) (z n)) x).K)
      (fun x μ i => Gu none (Fin.natAdd 3 i) μ x +
        ∑ e, Ainf μ (Fin.natAdd 3 i) e x * uinf none e x) := by
  set μQ := volume.restrict (box lo hi)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  -- the clean sequence
  set W : ℕ → E4 → Fin 4 → HiggsFibre := fun n x μ i =>
    tgrad (R n) (matterSec (z n) none) (Fin.natAdd 3 i) μ x +
      ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ (Fin.natAdd 3 i) e x *
        transp (R n) (matterSec (z n) none) e x
  have hpt : ∀ n, ∀ x ∈ box lo hi, ∀ μ i, ‖W n x μ i‖ ≤
      ∑ e, ‖covDerV (connM (z n).A) (matterSec (z n) none) μ x e‖ := by
    intro n x hx μ i
    have hK := redJet_gaugeTuple_K (z := z n) (hR n x hx) (hz n x).H μ i
    have hK2 : (redJet (gaugeTuple (R n) (z n)) x).K μ =
        higgsG (R n x) (covDerivHiggs (z n).A (z n).H x μ) :=
      covDerivHiggs_gaugeTuple (hR n x hx) (hz n x).H μ
    have hproj : covDerivHiggs (z n).A (z n).H x μ =
        projH (covDerV (connM (z n).A) (matterSec (z n) none) μ x) := by
      rw [covDerV_matterSec_higgs (hlie n x) (hz n x).H, projH_embH]
    show ‖W n x μ i‖ ≤ _
    rw [show W n x μ i = (redJet (gaugeTuple (R n) (z n)) x).K μ i from hK.symm, hK2, hproj]
    refine (norm_higgsG_apply_le (hR n x hx).unitary.self_of_nhds _ i).trans ?_
    simp only [projH]
    rw [sum_fin5 (fun e => ‖covDerV (connM (z n).A) (matterSec (z n) none) μ x e‖)]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hscalar : ∀ μ i, WeakL2Data lo hi (fun n x => W n x μ i)
      (fun x => Gu none (Fin.natAdd 3 i) μ x + ∑ e, Ainf μ (Fin.natAdd 3 i) e x * uinf none e x) := by
    intro μ i
    have hmem : ∀ n, MemLp (fun x => W n x μ i) 2 μQ := fun n =>
      ((hWu n none _).memLp_grad μ).add (memLp_finset_sum _ fun e _ =>
        memLp_two_mul_of_W12 hlh (hWA n μ _ e) (hWu n none e))
    refine weakL2Data_scalar hmem (((q5 none _).memLp_grad μ).add (memLp_finset_sum _ fun e _ =>
      memLp_two_mul_of_W12 hlh (q1 μ _ e) (q5 none e))) (B := B.toReal) (fun n => ?_)
      (q8 none _ μ)
    refine ENNReal.toReal_mono hB ?_
    calc eLpNorm (fun x => W n x μ i) 2 μQ ≤
          eLpNorm (fun x => ∑ e, ‖covDerV (connM (z n).A) (matterSec (z n) none) μ x e‖) 2 μQ :=
          eLpNorm_mono_ae_real ((ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx =>
            hpt n x hx μ i))
      _ = eLpNorm (∑ e, fun x => ‖covDerV (connM (z n).A) (matterSec (z n) none) μ x e‖) 2 μQ := by
          congr 1
      _ ≤ ∑ e, eLpNorm (fun x => ‖covDerV (connM (z n).A) (matterSec (z n) none) μ x e‖) 2 μQ :=
          eLpNorm_sum_le (fun e _ => ?_) (by norm_num)
      _ = ∑ e, eLpNorm (fun x => covDerV (connM (z n).A) (matterSec (z n) none) μ x e) 2 μQ := by
          simp only [eLpNorm_norm]
      _ ≤ ∑ e, ∑ μ', eLpNorm (fun x => covDerV (connM (z n).A) (matterSec (z n) none) μ' x e) 2
            μQ := Finset.sum_le_sum fun e _ => Finset.single_le_sum
              (f := fun μ' => eLpNorm (fun x => covDerV (connM (z n).A) (matterSec (z n) none) μ' x e)
                2 μQ) (fun _ _ => zero_le) (Finset.mem_univ μ)
      _ ≤ B := hQ3c n
    · -- measurability of the covariant-derivative components
      have hdiff : Continuous fun x => covDerV (connM (z n).A) (matterSec (z n) none) μ x e :=
        continuous_covDerV_entry (fun μ c e =>
            ((continuous_apply e).comp ((continuous_apply c).comp ((continuous_apply μ).comp
              (hzA n).continuous))))
          (embHL.contDiff.comp (hzH n)) μ e
      exact hdiff.norm.aestronglyMeasurable
  refine (weakL2Data_pi fun μ => weakL2Data_pi fun i => hscalar μ i).congr_ae (fun n => ?_)
    (Eventually.of_forall fun x => rfl)
  refine (ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx => ?_)
  funext μ i
  exact (redJet_gaugeTuple_K (z := z n) (hR n x hx) (hz n x).H μ i).symm

end WeakFieldsKF


section WeakCurv

variable {lo hi : E4}

theorem eLpNorm_curvVec_eq {A : MConn 5} {S : Set E4} :
    eLpNorm (fun x => curvVec A x) 2 (volume.restrict S) = curvEnergy A S ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, curvEnergy]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

theorem memLp_curvatureW_lim (hlh : ∀ i, lo i < hi i) {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ}
    {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e)) (μ ν : Fin 4) (c e : Fin 5) :
    MemLp (curvatureW Ainf GA μ ν c e) 2 (volume.restrict (box lo hi)) := by
  have h := (((q1 ν c e).memLp_grad μ).sub ((q1 μ c e).memLp_grad ν)).add
    (memLp_finset_sum Finset.univ fun k _ =>
      (memLp_two_mul_of_W12 hlh (q1 μ c k) (q1 ν k e)).sub
        (memLp_two_mul_of_W12 hlh (q1 ν c k) (q1 μ k e)))
  convert h using 1
  funext x
  simp [curvatureW]

/-- **Weak `L²` data of the curvature** on a Coulomb cube: the uniform `L²` bound is the
gauge-invariant curvature energy. -/
theorem weak_F_cube (hlh : ∀ i, lo i < hi i) {z : ℕ → FieldTuple (Fin 5)} {R : ℕ → E4 → M5}
    (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x) (hzA : ∀ n x, DifferentiableAt ℝ (z n).A x)
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF) :
    WeakL2Data lo hi (fun n x => (redJet (gaugeTuple (R n) (z n)) x).F)
      (fun x μ ν c e => curvatureW Ainf GA μ ν c e x) := by
  set μQ := volume.restrict (box lo hi)
  have hQm : MeasurableSet (box lo hi) := (isOpen_box lo hi).measurableSet
  have hcv : ∀ n, eLpNorm (fun x => curvVec (gaugeConn (R n) (connM (z n).A)) x) 2 μQ ≤
      MF ^ (1 / 2 : ℝ) := fun n => by
    rw [eLpNorm_curvVec_eq]; exact ENNReal.rpow_le_rpow (hE n) (by norm_num)
  have hfin : MF ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMF
  have hscalar : ∀ μ ν c e, WeakL2Data lo hi (fun n x => curvatureW
      (entries (gaugeConn (R n) (connM (z n).A))) (entryGrad (gaugeConn (R n) (connM (z n).A)))
        μ ν c e x) (fun x => curvatureW Ainf GA μ ν c e x) := by
    intro μ ν c e
    have hle : ∀ n, eLpNorm (fun x => curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x) 2 μQ ≤ MF ^ (1 / 2 : ℝ) :=
      fun n => (eLpNorm_mono fun x => by
        have := PiLp.norm_apply_le (curvVec (gaugeConn (R n) (connM (z n).A)) x) (μ, ν, c, e)
        simpa [curvVec] using this).trans (hcv n)
    have hmem : ∀ n, MemLp (fun x => curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x) 2 μQ := fun n =>
      ⟨aestronglyMeasurable_curvatureW (fun ν c e => (hWA n ν c e).memLp.1)
        (fun ν c e μ => ((hWA n ν c e).memLp_grad μ).1) μ ν c e,
        (hle n).trans_lt hfin.lt_top⟩
    exact weakL2Data_scalar hmem (memLp_curvatureW_lim hlh q1 μ ν c e)
      (B := (MF ^ (1 / 2 : ℝ)).toReal) (fun n => ENNReal.toReal_mono hfin (hle n)) (q4 μ ν c e)
  refine (weakL2Data_pi fun μ => weakL2Data_pi fun ν => weakL2Data_pi fun c =>
    weakL2Data_pi fun e => hscalar μ ν c e).congr_ae (fun n => ?_)
    (Eventually.of_forall fun x => rfl)
  refine (ae_restrict_iff' hQm).mpr (Eventually.of_forall fun x hx => ?_)
  funext μ ν c e
  exact (redJet_gaugeTuple_F (z := z n) (hR n x hx) (hzA n x) μ ν c e).symm

end WeakCurv


/-! ### Convergence of the rows on a Coulomb cube -/

/-- **The complete first-variation rows converge on a Coulomb cube** (critical convergences of
`app:critical-quotient-proof`): for the jets of the gauge-transformed fields and every bounded
Lipschitz test jet `τ`, `∫_Q (fullCov - quadMet)_n(τ)` converges to the same expression at the
limit packet `limitOf …`. -/
theorem cube_limit_tendsto {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) {lo hi a b : E4}
    (hlh : ∀ i, lo i < hi i) (hQK : box lo hi ⊆ box a b) {z : ℕ → FieldTuple (Fin 5)}
    {R : ℕ → E4 → M5}
    (hzA : ∀ n, ContDiff ℝ ∞ (z n).A) (hzH : ∀ n, ContDiff ℝ ∞ (z n).H)
    (hze : ∀ n, ContDiff ℝ ∞ (z n).e) (hz : ∀ n x, DiffAt (z n) x)
    (hlie : ∀ n x μ, (z n).A x μ ∈ smLie) (hR : ∀ n, ∀ x ∈ box lo hi, GaugeAt (R n) x)
    {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (heK : ∀ n, ∀ x ∈ box a b, (z n).e x ∈ Ke)
    {e₀ : E4 → CoframeFibre} {de₀ : Fin 4 → Fin 4 → Fin 4 → E4 → ℝ}
    (he₀ : ∀ i ν, MemLp (fun y => e₀ y i ν) ⊤ (volume.restrict (box a b)))
    (hde₀ : ∀ i ν μ, MemLp (de₀ i ν μ) 2 (volume.restrict (box a b)))
    (hL2 : ∀ i ν, Tendsto (fun k => eLpNorm (fun y => (z k).e y i ν - e₀ y i ν) 2
      (volume.restrict (box a b))) atTop (𝓝 0))
    (hd : ∀ i ν μ, Tendsto (fun k => eLpNorm (fun y => pd (fun y => (z k).e y i ν) μ y -
      de₀ i ν μ y) 2 (volume.restrict (box a b))) atTop (𝓝 0))
    (hWA : ∀ n ν c e, MemW12 (box lo hi) (entries (gaugeConn (R n) (connM (z n).A)) ν c e)
      (entryGrad (gaugeConn (R n) (connM (z n).A)) ν c e))
    (hWu : ∀ n s c, MemW12 (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c))
    {Bu : ℝ≥0∞} (hBu : Bu ≠ ⊤)
    (hBu' : ∀ n s c, w12Norm (box lo hi) (transp (R n) (matterSec (z n) s) c)
      (tgrad (R n) (matterSec (z n) s) c) ≤ Bu)
    {Ainf : Fin 4 → Fin 5 → Fin 5 → E4 → ℂ} {GA : Fin 4 → Fin 5 → Fin 5 → Fin 4 → E4 → ℂ}
    {uinf : MIdx → Fin 5 → E4 → ℂ} {Gu : MIdx → Fin 5 → Fin 4 → E4 → ℂ}
    (q1 : ∀ ν c e, MemW12 (box lo hi) (Ainf ν c e) (GA ν c e))
    (q2 : ∀ ν c e, Tendsto (fun n => eLpNorm (entries (gaugeConn (R n) (connM (z n).A)) ν c e -
      Ainf ν c e) 2 (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q4 : ∀ μ ν c e (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • curvatureW (entries (gaugeConn (R n) (connM (z n).A)))
        (entryGrad (gaugeConn (R n) (connM (z n).A))) μ ν c e x ∂(volume.restrict (box lo hi)))
        atTop (𝓝 (∫ x, w x • curvatureW Ainf GA μ ν c e x ∂(volume.restrict (box lo hi)))))
    (q5 : ∀ s c, MemW12 (box lo hi) (uinf s c) (Gu s c))
    (q6 : ∀ s c, Tendsto (fun n => eLpNorm (transp (R n) (matterSec (z n) s) c - uinf s c) 2
      (volume.restrict (box lo hi))) atTop (𝓝 0))
    (q7 : ∀ s c μ (w : E4 → ℝ), MemLp w 2 (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • tgrad (R n) (matterSec (z n) s) c μ x
        ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • Gu s c μ x ∂(volume.restrict (box lo hi)))))
    (q8 : ∀ s c μ (w : E4 → ℝ), MemLp w ⊤ (volume.restrict (box lo hi)) →
      Tendsto (fun n => ∫ x, w x • (tgrad (R n) (matterSec (z n) s) c μ x +
          ∑ e, entries (gaugeConn (R n) (connM (z n).A)) μ c e x *
            transp (R n) (matterSec (z n) s) e x) ∂(volume.restrict (box lo hi))) atTop
        (𝓝 (∫ x, w x • (Gu s c μ x + ∑ e, Ainf μ c e x * uinf s e x)
          ∂(volume.restrict (box lo hi)))))
    {MF : ℝ≥0∞} (hMF : MF ≠ ⊤)
    (hE : ∀ n, curvEnergy (gaugeConn (R n) (connM (z n).A)) (box lo hi) ≤ MF)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hQ3c : ∀ n, ∑ e, ∑ μ, eLpNorm (fun y => covDerV (connM (z n).A) (matterSec (z n) none) μ y e)
      2 (volume.restrict (box lo hi)) ≤ B)
    {θ : ℕ → CoefficientBank Ysec} {θ₀ : CoefficientBank Ysec}
    (hs : ∀ j, Tendsto (fun n => gaugeScalars (θ n) j) atTop (𝓝 (gaugeScalars θ₀ j)))
    (hl : Tendsto (fun n => (θ n).lambdaH) atTop (𝓝 θ₀.lambdaH))
    (hv : Tendsto (fun n => (θ n).vH) atTop (𝓝 θ₀.vH))
    (hk : Tendsto (fun n => (2 * (θ n).kappa)⁻¹) atTop (𝓝 (2 * θ₀.kappa)⁻¹))
    (hΛ : Tendsto (fun n => -(2 * (θ n).Lambda)) atTop (𝓝 (-(2 * θ₀.Lambda))))
    (hm : Tendsto (fun n => mY (θ n)) atTop (𝓝 (mY θ₀)))
    {τ : E4 → RJet (Fin 5)} (hτc : Continuous τ) {C L : ℝ} (hC : ∀ x, ‖τ x‖ ≤ C)
    (hL : ∀ x y, ‖τ x - τ y‖ ≤ L * ‖x - y‖) :
    (∀ n, Integrable (fun x => fullCov mY (θ n) (redJet (gaugeTuple (R n) (z n)) x) (τ x) -
        quadMet (θ n) (redJet (gaugeTuple (R n) (z n)) x) (τ x)) (volume.restrict (box lo hi))) ∧
    Integrable (fun x => fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) (τ x) -
        quadMet θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) (τ x))
        (volume.restrict (box lo hi)) ∧
    Tendsto (fun n => ∫ x, (fullCov mY (θ n) (redJet (gaugeTuple (R n) (z n)) x) (τ x) -
        quadMet (θ n) (redJet (gaugeTuple (R n) (z n)) x) (τ x)) ∂(volume.restrict (box lo hi)))
      atTop (𝓝 (∫ x, (fullCov mY θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) (τ x) -
        quadMet θ₀ (limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) (τ x))
          ∂(volume.restrict (box lo hi)))) := by
  obtain ⟨hcf, hde⟩ := coframe_cube hQK hze hKe hKeGL heK he₀ hde₀ hL2 hd
  obtain ⟨hA, hH, hΨ, hΨb, M, hM, hM4⟩ := strong_fields_cube hlh hWA hWu hBu hBu' q1 q2 q5 q6
  have hF := weak_F_cube hlh hR (fun n x => (hz n x).A) hWA q1 q4 hMF hE
  have hK := weak_K_cube hlh hR hz hzA hzH hlie hWA hWu q1 q5 q8 hB hQ3c
  have hD := weak_D_cube hR hz hWu hBu hBu' q5 q7
  exact cube_rows_tendsto mY (Jn := fun n x => redJet (gaugeTuple (R n) (z n)) x)
    (J₀ := fun x => limitJet (limitOf e₀ de₀ Ainf GA uinf Gu) x) hcf hde hA hH hΨ hΨb hM
    (fun n => (hM4 n).1) (fun n => (hM4 n).2.1) (fun n => (hM4 n).2.2) hF hK hD hs hl hv hk hΛ hm
    hτc hC hL

end RenewalGeometry.CriticalQuotientRows
