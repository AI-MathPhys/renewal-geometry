/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHarmonicPropagation

/-!
# Uniqueness for coupled wave / first-order symmetric systems

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`): with back-reacting spinors the constraint (subsidiary) system of the
actual-jet system couples the harmonic gauge covector `c` (second order, Lorentzian principal
part) with first-order symmetric blocks (the spinor defining-jet defects and the normal
prolongation defect).  This file proves the generic uniqueness theorem for such coupled systems
with **zero-order couplings**:

* **`coupled_unique`** — let `u` be `C²` (`k` components) and `w` be `C¹` (`n` components) on
  `(a, b) × ℝ³`, spatially periodic, with a `C¹` adapted frame `e` (`g⁻¹ = -e₀⊗e₀ + Σ_a e_a⊗e_a`)
  and continuous coframe `θ`, and symmetric `C¹` periodic matrices `M^j`.  If on `[t₀, t₁] × 𝕋³`
  `|g^{μβ}∂_μ∂_βu_i| ≤ K(‖u‖ + Σ_γ‖∂_γu‖ + ‖w‖)` and
  `‖∂_tw + Σ_jM^j∂_jw‖ ≤ K(‖u‖ + Σ_γ‖∂_γu‖ + ‖w‖)`, and `u = ∂_tu = 0`, `w = 0` at `t₀`, then
  `u = 0` and `w = 0` on `[t₀, t₁] × 𝕋³`.

The proof stacks the first-order frame reduction `(u, e₀u, e_au)` of the wave block
(`GenHarmonic.frameState`, `frameCoeff`) with `e₀{}^0·w`, giving one symmetric hyperbolic system
with block-diagonal principal part (the symmetriser is the identity in these coordinates), and
applies `GenHarmonic.sym_unique`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.GenCpl

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk GenHarmonic GenGauss ActualJetBridge

set_option linter.unusedSectionVars false

/-- The coefficients of the first-order block: `M^0 = 1`, `M^{j+1} = M^j`. -/
def Mfull {n : ℕ} (M : Fin 3 → ST 3 → Fin n → Fin n → ℝ) (μ : Fin 4) (x : ST 3) :
    Fin n → Fin n → ℝ :=
  Fin.cases (fun i l => if i = l then 1 else 0) (fun j => M j x) μ

/-- The stacked state `(u, e₀u, e_au; w)`. -/
def stackState {k n : ℕ} (u : ST 3 → Fin k → ℝ) (w : ST 3 → Fin n → ℝ)
    (e : ST 3 → Fin 4 → Fin 4 → ℝ) (x : ST 3) : (Fin k × Fin 5) ⊕ Fin n → ℝ :=
  Sum.elim (frameState u e x) (w x)

/-- The stacked principal coefficients (block diagonal). -/
def stackCoeff {k n : ℕ} (M : Fin 3 → ST 3 → Fin n → Fin n → ℝ)
    (e : ST 3 → Fin 4 → Fin 4 → ℝ) (μ : Fin 4) (x : ST 3) :
    (Fin k × Fin 5) ⊕ Fin n → (Fin k × Fin 5) ⊕ Fin n → ℝ :=
  Sum.elim (fun p => Sum.elim (fun q => frameCoeff e μ x p q) (fun _ => 0))
    (fun i => Sum.elim (fun _ => 0) (fun l => e x 0 0 * Mfull M μ x i l))

theorem norm_inl_le {k n : ℕ} (v : (Fin k × Fin 5) ⊕ Fin n → ℝ) :
    ‖(fun p => v (Sum.inl p))‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => norm_le_pi_norm v (Sum.inl p)

theorem norm_inr_le {k n : ℕ} (v : (Fin k × Fin 5) ⊕ Fin n → ℝ) :
    ‖(fun i => v (Sum.inr i))‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v (Sum.inr i)

/-- **Uniqueness for coupled wave / first-order symmetric systems with zero-order couplings**
(generic). -/
theorem coupled_unique {k n : ℕ} {u : ST 3 → Fin k → ℝ} {w : ST 3 → Fin n → ℝ}
    {e gi θ : ST 3 → Fin 4 → Fin 4 → ℝ} {M : Fin 3 → ST 3 → Fin n → Fin n → ℝ}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hu : ContDiffOn ℝ 2 u (openSlab a b)) (hup : IsSPeriodic u)
    (hw : ContDiffOn ℝ 1 w (openSlab a b)) (hwp : IsSPeriodic w)
    (he : ContDiffOn ℝ 1 e (openSlab a b)) (hep : IsSPeriodic e)
    (he0 : ∀ x (c : Fin 3), e x c.succ 0 = 0) (he00 : ∀ x, 0 < e x 0 0)
    (hadapt : ∀ x μ ν, gi x μ ν = -(e x 0 μ * e x 0 ν) + ∑ c : Fin 3, e x c.succ μ * e x c.succ ν)
    (hθ : ContinuousOn θ (openSlab a b)) (hθp : IsSPeriodic θ)
    (hcof : ∀ x ∈ openSlab a b, ∀ (v : Fin 4 → ℝ) γ, v γ = ∑ B, θ x B γ * ∑ β, e x B β * v β)
    (hM : ∀ j, ContDiffOn ℝ 1 (M j) (openSlab a b)) (hMp : ∀ j, IsSPeriodic (M j))
    (hMs : ∀ j x i l, M j x i l = M j x l i)
    {K : ℝ} (hK : 0 ≤ K)
    (hequ : ∀ x ∈ slab t₀ t₁, ∀ i, |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i| ≤
      K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖))
    (heqw : ∀ x ∈ slab t₀ t₁, ‖(fun i => pd w 0 x i + ∑ j : Fin 3, ∑ l, M j x i l *
      pd w j.succ x l)‖ ≤ K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖))
    (h0 : ∀ y : Fin 3 → ℝ, u (Fin.cons t₀ y) = 0)
    (h0t : ∀ y : Fin 3 → ℝ, pd u 0 (Fin.cons t₀ y) = 0)
    (hw0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, u x = 0 ∧ w x = 0 := by
  set U := openSlab (d := 3) a b with hUdef
  have hU : IsOpen U := isOpen_openSlab a b
  have hsub : slab (d := 3) t₀ t₁ ⊆ U := slab_subset_openSlab ha hb
  -- regularity
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hpdu : ∀ β, ContDiffOn ℝ 1 (pd u β) U := fun β => contDiffOn_pd hU (n := 1) hu β
  have hec : ∀ A μ, ContDiffOn ℝ 1 (fun x => e x A μ) U := fun A μ =>
    contDiffOn_pi.1 (contDiffOn_pi.1 he A) μ
  have hpdui : ∀ β i, ContDiffOn ℝ 1 (fun x => pd u β x i) U := fun β i =>
    contDiffOn_pi.1 (hpdu β) i
  have hui : ∀ i, ContDiffOn ℝ 1 (fun x => u x i) U := fun i => contDiffOn_pi.1 hu1 i
  have hwi : ∀ i, ContDiffOn ℝ 1 (fun x => w x i) U := fun i => contDiffOn_pi.1 hw i
  have hMc : ∀ j i l, ContDiffOn ℝ 1 (fun x => M j x i l) U := fun j i l =>
    contDiffOn_pi.1 (contDiffOn_pi.1 (hM j) i) l
  -- the frame state
  set FS := frameState u e with hFSdef
  have hFS : ContDiffOn ℝ 1 FS U := by
    refine contDiffOn_pi.2 fun p => ?_
    rcases p with ⟨i, r⟩
    induction r using Fin.cases with
    | zero => exact hui i
    | succ B =>
      show ContDiffOn ℝ 1 (fun x => ∑ β, e x B β * pd u β x i) U
      exact ContDiffOn.sum fun β _ => (hec B β).mul (hpdui β i)
  have hpdp : ∀ β, IsSPeriodic (pd u β) := fun β k' x => by
    unfold SobolevOpen.pd
    have : (fun z => u (z + sshift k')) = u := funext fun z => hup k' z
    rw [← fderiv_comp_add_right, this]
  -- the stacked state
  set Wb := stackState u w e with hWbdef
  have hWb : ContDiffOn ℝ 1 Wb U := by
    refine contDiffOn_pi.2 fun p => ?_
    rcases p with p | i
    · exact contDiffOn_pi.1 hFS p
    · exact hwi i
  have hWbp : IsSPeriodic Wb := fun k' x => by
    funext p
    rcases p with ⟨i, r⟩ | i
    · simp only [hWbdef, stackState, Sum.elim_inl, frameState, fc, hup k' x, hep k' x]
      induction r using Fin.cases with
      | zero => rfl
      | succ B => simp only [Fin.cases_succ, hpdp _ k' x]
    · simp only [hWbdef, stackState, Sum.elim_inr, hwp k' x]
  -- derivatives of the stacked state
  have hdWb_inl : ∀ x ∈ U, ∀ μ p, pd Wb μ x (Sum.inl p) = pd FS μ x p := by
    intro x hx μ p
    rw [← pd_apply (diffAt_of_contDiffOn hU hWb one_ne_zero hx) μ (Sum.inl p),
      ← pd_apply (diffAt_of_contDiffOn hU hFS one_ne_zero hx) μ p]
    rfl
  have hdWb_inr : ∀ x ∈ U, ∀ μ i, pd Wb μ x (Sum.inr i) = pd w μ x i := by
    intro x hx μ i
    rw [← pd_apply (diffAt_of_contDiffOn hU hWb one_ne_zero hx) μ (Sum.inr i),
      ← pd_apply (diffAt_of_contDiffOn hU hw one_ne_zero hx) μ i]
    rfl
  have hdW0 : ∀ x ∈ U, ∀ μ i, pd FS μ x (i, 0) = pd u μ x i := by
    intro x hx μ i
    rw [← pd_apply (diffAt_of_contDiffOn hU hFS one_ne_zero hx) μ (i, 0),
      ← pd_apply (diffAt_of_contDiffOn hU hu1 one_ne_zero hx) μ i]
    rfl
  have hdWB : ∀ x ∈ U, ∀ μ i (B : Fin 4), pd FS μ x (i, B.succ) =
      dfc (e x) (fun μ' A β => pd e μ' x A β) (fun β => pd u β x i)
        (fun μ' β => pd (pd u β) μ' x i) μ B := by
    intro x hx μ i B
    rw [← pd_apply (diffAt_of_contDiffOn hU hFS one_ne_zero hx) μ (i, B.succ)]
    have hfun : (fun y => FS y (i, B.succ)) = fun y => ∑ β, e y B β * pd u β y i := rfl
    rw [hfun]
    refine pd_eq_of_line ?_ ?_
    · exact diffAt_of_contDiffOn hU (ContDiffOn.sum fun β _ => (hec B β).mul (hpdui β i))
        one_ne_zero hx
    · refine HasDerivAt.fun_sum fun β _ => ?_
      have h1 := hasDerivAt_line0 (diffAt_of_contDiffOn hU (hec B β) one_ne_zero hx) μ
      have h2 := hasDerivAt_line0 (diffAt_of_contDiffOn hU (hpdui β i) one_ne_zero hx) μ
      have h3 := h1.mul h2
      simp only [zero_smul, add_zero] at h3
      rw [pd_apply (diffAt_of_contDiffOn hU (hpdu β) one_ne_zero hx) μ i,
        pd_apply (diffAt_of_contDiffOn hU (contDiffOn_pi.1 he B) one_ne_zero hx) μ β,
        pd_apply (diffAt_of_contDiffOn hU he one_ne_zero hx) μ B] at h3
      exact h3
  -- the coefficients
  set c : Fin 4 → ST 3 → (Fin k × Fin 5) ⊕ Fin n → (Fin k × Fin 5) ⊕ Fin n → ℝ :=
    fun μ => stackCoeff M e μ with hc
  have hMf : ∀ μ i l, ContDiffOn ℝ 1 (fun x => Mfull M μ x i l) U := by
    intro μ i l
    induction μ using Fin.cases with
    | zero => exact contDiffOn_const
    | succ j => exact hMc j i l
  have hfc : ∀ μ (p p' : Fin k × Fin 5), ContDiffOn ℝ 1 (fun x => frameCoeff e μ x p p') U := by
    intro μ p p'
    show ContDiffOn ℝ 1 (fun x => if p.1 = p'.1 then blk (e x) μ p.2 p'.2 else 0) U
    by_cases hp : p.1 = p'.1
    · simp only [hp, if_true]
      unfold blk
      refine ContDiffOn.sub ?_ (ContDiffOn.sum fun a' _ => ?_)
      · by_cases hr : p.2 = p'.2
        · simp only [hr, if_true]; exact hec 0 μ
        · simp only [hr, if_false]; exact contDiffOn_const
      · split_ifs
        · exact hec _ μ
        · exact contDiffOn_const
    · simp only [hp, if_false]; exact contDiffOn_const
  have hcs : ∀ μ, ContDiffOn ℝ 1 (c μ) U := by
    intro μ
    refine contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => ?_
    rcases p with p | i <;> rcases q with q | l
    · exact hfc μ p q
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact (hec 0 0).mul (hMf μ i l)
  have hcp : ∀ μ, IsSPeriodic (c μ) := fun μ k' x => by
    funext p q
    rcases p with p | i <;> rcases q with q | l
    · show frameCoeff e μ (x + sshift k') p q = frameCoeff e μ x p q
      unfold frameCoeff
      rw [hep k' x]
    · rfl
    · rfl
    · show e (x + sshift k') 0 0 * Mfull M μ (x + sshift k') i l = e x 0 0 * Mfull M μ x i l
      rw [hep k' x]
      induction μ using Fin.cases with
      | zero => rfl
      | succ j => simp only [Mfull, Fin.cases_succ, hMp j k' x]
  have hcsym : ∀ μ x p q, c μ x p q = c μ x q p := by
    intro μ x p q
    rcases p with p | i <;> rcases q with q | l
    · show frameCoeff e μ x p q = frameCoeff e μ x q p
      simp only [frameCoeff]
      by_cases hp : p.1 = q.1
      · rw [if_pos hp, if_pos hp.symm, blk_symm]
      · rw [if_neg hp, if_neg (Ne.symm hp)]
    · rfl
    · rfl
    · show e x 0 0 * Mfull M μ x i l = e x 0 0 * Mfull M μ x l i
      induction μ using Fin.cases with
      | zero =>
        simp only [Mfull, Fin.cases_zero]
        by_cases h : i = l
        · rw [h]
        · rw [if_neg h, if_neg (Ne.symm h)]
      | succ j => simp only [Mfull, Fin.cases_succ, hMs j x i l]
  have hc0 : ∀ x p q, c 0 x p q = if p = q then e x 0 0 else 0 := by
    intro x p q
    rcases p with p | i <;> rcases q with q | l
    · show frameCoeff e 0 x p q = _
      simp only [frameCoeff, blk_zero_time (e x) (he0 x)]
      rcases p with ⟨i, r⟩
      rcases q with ⟨i', r'⟩
      by_cases hi : i = i' <;> by_cases hr : r = r' <;> simp [hi, hr]
    · simp [hc, stackCoeff]
    · simp [hc, stackCoeff]
    · show e x 0 0 * Mfull M 0 x i l = _
      simp only [Mfull, Fin.cases_zero, Sum.inr.injEq]
      by_cases h : i = l <;> simp [h]
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower_slab (hec 0 0).continuousOn
    (fun k' x => by simp only [hep k' x]) he00 ha hb
  -- coefficient bounds
  have hpe : IsSPeriodic (fderiv ℝ e) := KatoGalerkin.isSPeriodic_fderiv hep
  obtain ⟨Cde, hCde⟩ := KatoGalerkin.exists_bound_slab
    (he.continuousOn_fderiv_of_isOpen hU le_rfl) hpe ha hb
  obtain ⟨Ce, hCe⟩ := KatoGalerkin.exists_bound_slab he.continuousOn hep ha hb
  obtain ⟨Cθ, hCθ⟩ := KatoGalerkin.exists_bound_slab hθ hθp ha hb
  have hCe0 : 0 ≤ Ce := by
    have := hCe (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have hCde0 : 0 ≤ Cde := by
    have := hCde (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have hCθ0 : 0 ≤ Cθ := by
    have := hCθ (Fin.cons t₀ 0) (cons_mem_slab 0 |>.2 ⟨le_rfl, h01.le⟩)
    exact (norm_nonneg _).trans this
  have be : ∀ x ∈ slab t₀ t₁, ∀ A μ, |e x A μ| ≤ Ce := fun x hx A μ =>
    ((norm_le_pi_norm (e x A) μ).trans (norm_le_pi_norm (e x) A)).trans (hCe x hx)
  have bde : ∀ x ∈ slab t₀ t₁, ∀ μ A β, |pd e μ x A β| ≤ Cde := by
    intro x hx μ A β
    have h1 : ‖pd e μ x‖ ≤ Cde := by
      unfold SobolevOpen.pd
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [Pi.norm_single, norm_one, mul_one]
      exact hCde x hx
    exact ((norm_le_pi_norm (pd e μ x A) β).trans (norm_le_pi_norm (pd e μ x) A)).trans h1
  have bθ : ∀ x ∈ slab t₀ t₁, ∀ B γ, |θ x B γ| ≤ Cθ := fun x hx B γ =>
    ((norm_le_pi_norm (θ x B) γ).trans (norm_le_pi_norm (θ x) B)).trans (hCθ x hx)
  -- the frame state is controlled by the stacked state
  have bFS : ∀ x, ‖FS x‖ ≤ ‖Wb x‖ := fun x => norm_inl_le (Wb x)
  have bw : ∀ x, ‖w x‖ ≤ ‖Wb x‖ := fun x => norm_inr_le (Wb x)
  -- the first jets are controlled by the frame components
  have bdu : ∀ x ∈ slab t₀ t₁, ∀ γ i, |pd u γ x i| ≤ 4 * Cθ * ‖Wb x‖ := by
    intro x hx γ i
    rw [hcof x (hsub hx) (fun β => pd u β x i) γ]
    have hWB : ∀ B, |∑ β, e x B β * pd u β x i| ≤ ‖Wb x‖ := fun B =>
      ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (FS x) (i, B.succ))).trans (bFS x)
    refine (abs_sum_mul_le (fun B => θ x B γ) _ hWB).trans ?_
    have : ∑ B, |θ x B γ| ≤ 4 * Cθ := by
      calc ∑ B, |θ x B γ| ≤ ∑ _B : Fin 4, Cθ := Finset.sum_le_sum fun B _ => bθ x hx B γ
        _ = 4 * Cθ := by simp
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have bu : ∀ x, ∀ i, |u x i| ≤ ‖Wb x‖ := fun x i =>
    ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (FS x) (i, 0))).trans (bFS x)
  have bnu : ∀ x, ‖u x‖ ≤ ‖Wb x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (Real.norm_eq_abs _).le.trans (bu x i)
  have bnpdu : ∀ x ∈ slab t₀ t₁, ∀ γ, ‖pd u γ x‖ ≤ 4 * Cθ * ‖Wb x‖ := fun x hx γ =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
      (Real.norm_eq_abs _).le.trans (bdu x hx γ i)
  have bR : ∀ x ∈ slab t₀ t₁, ‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖ ≤ (2 + 16 * Cθ) * ‖Wb x‖ := by
    intro x hx
    have : ∑ γ, ‖pd u γ x‖ ≤ 16 * Cθ * ‖Wb x‖ := by
      calc ∑ γ, ‖pd u γ x‖ ≤ ∑ _γ : Fin 4, 4 * Cθ * ‖Wb x‖ :=
            Finset.sum_le_sum fun γ _ => bnpdu x hx γ
        _ = 16 * Cθ * ‖Wb x‖ := by simp; ring
    linarith [bnu x, bw x]
  -- the constant
  set K' : ℝ := 1 + K * (2 + 16 * Cθ) + 64 * Ce * Cde * (4 * Cθ) + Ce * K * (2 + 16 * Cθ)
    with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hsol := sym_unique (N := (Fin k × Fin 5) ⊕ Fin n) (W := Wb) (c := c)
    (a0 := fun x => e x 0 0) ha h01 hb hWb hWbp hcs hcp hcsym hc0 hκ hκle hK'0 ?_ ?_
  · intro x hx
    have hz := hsol x hx
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun hz (Sum.inl (i, 0))
      exact this
    · have := congrFun hz (Sum.inr i)
      exact this
  · -- the principal part is controlled
    intro x hx
    have hxU := hsub hx
    have hWnn := norm_nonneg (Wb x)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    rw [Real.norm_eq_abs]
    rcases p with ⟨i, r⟩ | i
    · -- the wave block
      have hcoll : ∑ μ, ∑ q, c μ x (Sum.inl (i, r)) q * pd Wb μ x q =
          ∑ μ, ∑ r', blk (e x) μ r r' * pd FS μ x (i, r') := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Fintype.sum_sum_type]
        simp only [hc, stackCoeff, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
          add_zero]
        rw [Fintype.sum_prod_type]
        simp only [frameCoeff, ite_mul, zero_mul, hdWb_inl x hxU]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      rw [hcoll]
      set du : Fin 4 → ℝ := fun β => pd u β x i with hdu
      set ddu : Fin 4 → Fin 4 → ℝ := fun μ β => pd (pd u β) μ x i with hddu
      set de : Fin 4 → Fin 4 → Fin 4 → ℝ := fun μ A β => pd e μ x A β with hde
      have bdu' : ∀ β, |du β| ≤ 4 * Cθ * ‖Wb x‖ := fun β => bdu x hx β i
      have blow : ∀ L : Fin 4 → ℝ, (∀ β, |L β| ≤ 16 * Ce * Cde) →
          |∑ β, L β * du β| ≤ 64 * Ce * Cde * (4 * Cθ) * ‖Wb x‖ := by
        intro L hL
        refine (abs_sum_mul_le L du bdu').trans ?_
        have : ∑ β, |L β| ≤ 64 * Ce * Cde := by
          calc ∑ β, |L β| ≤ ∑ _β : Fin 4, 16 * Ce * Cde := Finset.sum_le_sum fun β _ => hL β
            _ = 64 * Ce * Cde := by simp; ring
        calc (∑ β, |L β|) * (4 * Cθ * ‖Wb x‖) ≤ 64 * Ce * Cde * (4 * Cθ * ‖Wb x‖) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring
      have bprod : ∀ A A' μ β, |e x A μ * de μ A' β| ≤ Ce * Cde := fun A A' μ β => by
        rw [abs_mul]
        exact mul_le_mul (be x hx A μ) (bde x hx μ A' β) (abs_nonneg _) hCe0
      have hextra : 0 ≤ Ce * K * (2 + 16 * Cθ) * ‖Wb x‖ := by positivity
      induction r using Fin.cases with
      | zero =>
        have : ∑ μ, ∑ r', blk (e x) μ 0 r' * pd FS μ x (i, r') = FS x (i, 1) := by
          simp only [blk_row0]
          rw [Finset.sum_congr rfl fun μ _ => by rw [hdW0 x hxU μ i]]
          rfl
        rw [this]
        calc |FS x (i, 1)| ≤ ‖Wb x‖ :=
              ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ _)).trans (bFS x)
          _ ≤ K' * ‖Wb x‖ := le_mul_of_one_le_left hWnn (by
              have : 0 ≤ K * (2 + 16 * Cθ) := by positivity
              have : 0 ≤ 64 * Ce * Cde * (4 * Cθ) := by positivity
              have : 0 ≤ Ce * K * (2 + 16 * Cθ) := by positivity
              rw [hK']; linarith)
      | succ r1 =>
        induction r1 using Fin.cases with
        | zero =>
          have hrow : ∑ μ, ∑ r', blk (e x) μ (Fin.succ 0) r' * pd FS μ x (i, r') =
              ∑ μ, e x 0 μ * dfc (e x) de du ddu μ 0 -
                ∑ c : Fin 3, ∑ μ, e x c.succ μ * dfc (e x) de du ddu μ c.succ := by
            rw [show (Fin.succ 0 : Fin 5) = 1 from rfl]
            simp only [blk_row1, Finset.sum_sub_distrib]
            congr 1
            · exact Finset.sum_congr rfl fun μ _ => congrArg (e x 0 μ * ·) (hdWB x hxU μ i 0)
            · rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun μ _ => by
                rw [hdWB x hxU μ i c.succ]
          rw [hrow, rowP (gi x) (e x) (hadapt x) de du ddu]
          have h1 := hequ x hx i
          have h2 := blow (fun β => ∑ μ, e x 0 μ * de μ 0 β -
            ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) (fun β => by
              refine (abs_sub _ _).trans ?_
              refine le_trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
                (Finset.abs_sum_le_sum_abs _ _)) ?_
              have e1 : ∑ μ, |e x 0 μ * de μ 0 β| ≤ 4 * (Ce * Cde) := by
                calc ∑ μ, |e x 0 μ * de μ 0 β| ≤ ∑ _μ : Fin 4, Ce * Cde :=
                      Finset.sum_le_sum fun μ _ => bprod 0 0 μ β
                  _ = 4 * (Ce * Cde) := by simp
              have e2 : ∑ c : Fin 3, |∑ μ, e x c.succ μ * de μ c.succ β| ≤ 12 * (Ce * Cde) := by
                calc ∑ c : Fin 3, |∑ μ, e x c.succ μ * de μ c.succ β| ≤
                      ∑ _c : Fin 3, 4 * (Ce * Cde) := Finset.sum_le_sum fun c _ =>
                      (Finset.abs_sum_le_sum_abs _ _).trans (by
                        calc ∑ μ, |e x c.succ μ * de μ c.succ β| ≤ ∑ _μ : Fin 4, Ce * Cde :=
                              Finset.sum_le_sum fun μ _ => bprod _ _ μ β
                          _ = 4 * (Ce * Cde) := by simp)
                  _ = 12 * (Ce * Cde) := by simp; ring
              linarith)
          have h3 := bR x hx
          calc |-(∑ μ, ∑ β, gi x μ β * ddu μ β) + ∑ β, (∑ μ, e x 0 μ * de μ 0 β -
                ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) * du β|
              ≤ |∑ μ, ∑ β, gi x μ β * ddu μ β| + |∑ β, (∑ μ, e x 0 μ * de μ 0 β -
                ∑ c : Fin 3, ∑ μ, e x c.succ μ * de μ c.succ β) * du β| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_neg]
            _ ≤ K * ((2 + 16 * Cθ) * ‖Wb x‖) + 64 * Ce * Cde * (4 * Cθ) * ‖Wb x‖ :=
                add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3 hK)) h2
            _ ≤ K' * ‖Wb x‖ := by rw [hK']; nlinarith
        | succ s =>
          have hrow : ∑ μ, ∑ r', blk (e x) μ s.succ.succ r' * pd FS μ x (i, r') =
              ∑ μ, e x 0 μ * dfc (e x) de du ddu μ s.succ -
                ∑ μ, e x s.succ μ * dfc (e x) de du ddu μ 0 := by
            simp only [blk_rowQ, Finset.sum_sub_distrib]
            congr 1
            · exact Finset.sum_congr rfl fun μ _ => by rw [hdWB x hxU μ i s.succ]
            · exact Finset.sum_congr rfl fun μ _ =>
                congrArg (e x s.succ μ * ·) (hdWB x hxU μ i 0)
          have hs : ∀ μ β, ddu μ β = ddu β μ := fun μ β => by
            simp only [hddu]
            rw [pd_pd_symm_at hU hu hxU β μ]
          rw [hrow, rowQ (e x) de du ddu hs s]
          refine (blow _ fun β => ?_).trans ?_
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ μ, |e x 0 μ * de μ s.succ β - e x s.succ μ * de μ 0 β| ≤
                  ∑ _μ : Fin 4, 2 * (Ce * Cde) := Finset.sum_le_sum fun μ _ =>
                    (abs_sub _ _).trans (by linarith [bprod 0 s.succ μ β, bprod s.succ 0 μ β])
              _ ≤ 16 * Ce * Cde := by simp; nlinarith [mul_nonneg hCe0 hCde0]
          · rw [hK']
            nlinarith [mul_nonneg (mul_nonneg hK (by positivity : (0:ℝ) ≤ 2 + 16 * Cθ)) hWnn]
    · -- the first-order block
      have hcoll : ∑ μ, ∑ q, c μ x (Sum.inr i) q * pd Wb μ x q =
          e x 0 0 * (pd w 0 x i + ∑ j : Fin 3, ∑ l, M j x i l * pd w j.succ x l) := by
        have e1 : ∀ μ, ∑ q, c μ x (Sum.inr i) q * pd Wb μ x q =
            e x 0 0 * ∑ l, Mfull M μ x i l * pd w μ x l := by
          intro μ
          rw [Fintype.sum_sum_type]
          simp only [hc, stackCoeff, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
            zero_add, hdWb_inr x hxU, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_congr rfl fun μ _ => e1 μ, ← Finset.mul_sum, Fin.sum_univ_succ]
        congr 1
        simp only [Mfull, Fin.cases_zero, Fin.cases_succ, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hcoll, abs_mul]
      have h1 : |pd w 0 x i + ∑ j : Fin 3, ∑ l, M j x i l * pd w j.succ x l| ≤
          K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖) :=
        ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm (fun i => pd w 0 x i +
          ∑ j : Fin 3, ∑ l, M j x i l * pd w j.succ x l) i)).trans (heqw x hx)
      have h2 : |e x 0 0| ≤ Ce := be x hx 0 0
      have h3 := bR x hx
      calc |e x 0 0| * |pd w 0 x i + ∑ j : Fin 3, ∑ l, M j x i l * pd w j.succ x l|
          ≤ Ce * (K * ((2 + 16 * Cθ) * ‖Wb x‖)) :=
            mul_le_mul h2 (h1.trans (mul_le_mul_of_nonneg_left h3 hK)) (abs_nonneg _) hCe0
        _ ≤ K' * ‖Wb x‖ := by
            rw [hK']
            have : 0 ≤ K * (2 + 16 * Cθ) * ‖Wb x‖ := by positivity
            have : 0 ≤ 64 * Ce * Cde * (4 * Cθ) * ‖Wb x‖ := by positivity
            nlinarith
  · -- vanishing initial stacked state
    intro y
    funext p
    have hy : (Fin.cons t₀ y : ST 3) ∈ U := ⟨ha, h01.trans hb⟩
    rcases p with ⟨i, r⟩ | i
    · induction r using Fin.cases with
      | zero => simp [hWbdef, stackState, frameState, h0 y]
      | succ B =>
        show fc (e (Fin.cons t₀ y)) (fun β => pd u β (Fin.cons t₀ y) i) B = 0
        have hdu0 : ∀ β, pd u β (Fin.cons t₀ y) = 0 := by
          intro β
          induction β using Fin.cases with
          | zero => exact h0t y
          | succ j =>
            refine pd_eq_of_line (diffAt_of_contDiffOn hU hu1 one_ne_zero hy) ?_
            have : (fun s : ℝ => u ((Fin.cons t₀ y : ST 3) + s • ev j.succ)) = fun _ => 0 := by
              funext s
              have : (Fin.cons t₀ y : ST 3) + s • ev j.succ =
                  Fin.cons t₀ (y + s • Pi.single j 1) := by
                funext q
                induction q using Fin.cases with
                | zero => simp [ev]
                | succ q => simp [ev, Pi.single_apply, Fin.succ_inj]
              rw [this, h0]
            rw [this]
            exact hasDerivAt_const _ _
        simp [fc, hdu0]
    · simp [hWbdef, stackState, hw0 y]

end RenewalGeometry.GenCpl
