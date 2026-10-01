/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawFamily

/-!
# The lower-order difference estimate for the law family `B`
  (infrastructure for `lem:supp-law-cost-control`)

Two forced histories of one member `B` of the law family `eq:supp-law-family`,
`q_t = v`, `v_t = V_{B,h}(q, v) + f` and `p_t = w`, `w_t = V_{B,h}(p, w) + f̃`, both in the top
chart `‖·‖_{X^s_h} ≤ δ` on `[0, T]`, satisfy for `3 ≤ r ≤ s - 1`
`‖X(t) - Y(t)‖_{X^r_h} ≤ 3 e^{K t} (3 ‖X(0) - Y(0)‖_{X^r_h} + K ∫_0^t ‖f - f̃‖_{r,h})`,
uniformly in the mesh and the mark.

The difference row contains the top-order term `-h² B Λ_h² δq`, which is **not** bounded by
`‖δX‖_{X^r_h}` at order `r`; as in `thm:supp-law-stability` it is cancelled through the energy
`𝓔^δ = 𝓔_r(δq, δv; coefficients of q) + (h²/2) Σ_{|α| ≤ r} ⟨Λ_h δq_α, B Λ_h δq_α⟩_h`
(`lawGenEnergy`), not estimated.

* `bForceAt`, `commTermAt`, `forcingTerm_bForceAt`: the cancellation identity for the stencil
  applied to arbitrary data with the mass coefficient of a fixed record;
* `lawForce_sub`: `lawForce B q - lawForce B p = -a(q)⁻¹ h² B Λ_h²(q - p) + (a(p)⁻¹ - a(q)⁻¹) h² B Λ_h² p`;
* `diffRate_force`: the difference rate is affine in the force difference;
* `lawGenEnergy_bounds`: `⅛ ‖(Q, V)‖² ≤ 𝓔^δ ≤ 9 ‖(Q, V)‖²` on the chart;
* `law_diff_static_bound`, `law_difference` (the estimate);
* `dAcc_bound`, `sobNorm_lawForceRem_le`, `lawAccel_diff_bound`: the writer and law-family
  accelerations are Lipschitz one order down, `‖V_{B,h}(X) - V_{B,h}(Y)‖_{r-1,h} ≤ K ‖X - Y‖_{X^r_h}`.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Elementary norm facts -/

theorem lawDiff_Xnorm_mono {r r' : ℕ} (h : r ≤ r') (Q V : Grid N → MetricRec) :
    Xnorm r Q V ≤ Xnorm r' Q V := by
  refine Real.sqrt_le_sqrt (sum_le_sum fun κ _ => add_le_add ?_ ?_)
  · exact PeriodicGridSobolev.sobSq_mono (by omega) _
  · exact PeriodicGridSobolev.sobSq_mono h _

theorem lawDiff_Xnorm_sub_comm (r : ℕ) (q p v w : Grid N → MetricRec) :
    Xnorm r (p - q) (w - v) = Xnorm r (q - p) (v - w) := by
  have hneg : ∀ (r' : ℕ) (u u' : Grid N → MetricRec) (κ : Upper),
      PeriodicGridSobolev.sobSq r' (cx (comp (u' - u) κ.1.1 κ.1.2)) =
        PeriodicGridSobolev.sobSq r' (cx (comp (u - u') κ.1.1 κ.1.2)) := by
    intro r' u u' κ
    have e : cx (comp (u' - u) κ.1.1 κ.1.2) = -cx (comp (u - u') κ.1.1 κ.1.2) := by
      funext x; simp [comp, cx]
    rw [e, ← PeriodicGridSobolev.sobNorm_sq, ← PeriodicGridSobolev.sobNorm_sq,
      PeriodicGridSobolev.Moser.sobNorm_neg]
  unfold Xnorm Xsq
  congr 1
  exact sum_congr rfl fun κ _ => by rw [hneg (r + 1) q p κ, hneg r v w κ]

theorem lawDiff_Fnorm_zero (r : ℕ) : Fnorm r (0 : Grid N → MetricRec) = 0 := by
  unfold Fnorm
  have e : ∀ κ : Upper, cx (comp (0 : Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := fun κ => by
    funext x; simp [comp, cx]
  simp only [e]
  simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]

/-- `‖F‖_{r,h} ≤ 16 M` when every upper component is bounded by `M` in `H^r_h`. -/
theorem lawDiff_Fnorm_le_of_comp_le (r : ℕ) (F : Grid N → MetricRec) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ κ : Upper, PeriodicGridSobolev.sobNorm r (cx (comp F κ.1.1 κ.1.2)) ≤ M) :
    Fnorm r F ≤ 16 * M := by
  have hc : (Fintype.card Upper : ℝ) ≤ 16 := by
    have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
    have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
    exact_mod_cast h1.trans h2.le
  unfold Fnorm
  rw [Real.sqrt_le_left (by positivity)]
  calc ∑ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp F κ.1.1 κ.1.2)) ≤ ∑ _κ : Upper, M ^ 2 :=
        sum_le_sum fun κ _ => by
          rw [← PeriodicGridSobolev.sobNorm_sq]
          exact pow_le_pow_left₀ (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (h κ) 2
    _ = (Fintype.card Upper : ℝ) * M ^ 2 := by simp
    _ ≤ 16 * M ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (16 * M) ^ 2 := by nlinarith [sq_nonneg M]

theorem lawDiff_Fnorm_mono {r r' : ℕ} (h : r ≤ r') (F : Grid N → MetricRec) :
    Fnorm r F ≤ Fnorm r' F :=
  Real.sqrt_le_sqrt (sum_le_sum fun _ _ => PeriodicGridSobolev.sobSq_mono h _)

/-! ### The stencil with a frozen mass coefficient -/

/-- The added force `-a⁻¹ h² B Λ_h² u` with a given mass coefficient array `a`. -/
def bForceAt (a : Grid N → ℝ) (B : Upper → Upper → ℝ) (u : Grid N → MetricRec) :
    Grid N → MetricRec :=
  fun x μ ν => -((a x)⁻¹ * bTerm B u x μ ν)

/-- The commutator term `Σ_α ⟨V_α, a_α 𝒞_α(a⁻¹, h² B Λ_h² u)⟩_h` with a given mass coefficient. -/
def commTermAt (B : Upper → Upper → ℝ) (s : ℕ) (a : Grid N → ℝ) (u V : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ k : Upper, ((N : ℝ) ^ 3)⁻¹ * ∑ x,
    DαR α (comp V k.1.1 k.1.2) x * (SαR α a x *
      commR α (fun y => (a y)⁻¹) (comp (bTerm B u) k.1.1 k.1.2) x)

/-- **The cancellation with a frozen coefficient**: the forcing contribution of
`-a(q)⁻¹ h² B Λ_h² u` paired with `V` is `-Σ_α ⟨V_α, h² B Λ_h² u_α⟩` up to the commutator. -/
theorem forcingTerm_bForceAt (B : Upper → Upper → ℝ) (s : ℕ) (q u V : Grid N → MetricRec)
    (ha : ∀ x, aArr q x ≠ 0) :
    forcingTerm s q V (bForceAt (aArr q) B u) =
      -lawExtraRate B s u V - commTermAt B s (aArr q) u V := by
  unfold forcingTerm lawExtraRate commTermAt
  rw [← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [← sum_neg_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hpt : ∀ x, SαR α (aArr q) x * DαR α (comp (bForceAt (aArr q) B u) k.1.1 k.1.2) x =
      -DαR α (comp (bTerm B u) k.1.1 k.1.2) x -
      SαR α (aArr q) x * commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B u) k.1.1 k.1.2) x := by
    intro x
    have e1 : comp (bForceAt (aArr q) B u) k.1.1 k.1.2 =
        -(fun y => (aArr q y)⁻¹ * comp (bTerm B u) k.1.1 k.1.2 y) := by
      funext y; simp [comp, bForceAt]
    rw [e1, DαR_neg]
    have e2 : DαR α (fun y => (aArr q y)⁻¹ * comp (bTerm B u) k.1.1 k.1.2 y) x =
        SαR α (fun y => (aArr q y)⁻¹) x * DαR α (comp (bTerm B u) k.1.1 k.1.2) x +
          commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B u) k.1.1 k.1.2) x := by
      simp only [commR]; ring
    have e3 : SαR α (aArr q) x * SαR α (fun y => (aArr q y)⁻¹) x = 1 := by
      simp only [SαR]; exact mul_inv_cancel₀ (ha _)
    rw [Pi.neg_apply, e2, mul_neg, mul_add, ← mul_assoc, e3, one_mul]
    ring
  rw [← mul_neg, ← mul_sub, ← sum_neg_distrib, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [hpt]
  ring

theorem lawDiff_bTerm_sub (B : Upper → Upper → ℝ) (q p : Grid N → MetricRec) :
    bTerm B q - bTerm B p = bTerm B (q - p) := by
  funext x μ ν
  simp only [bTerm, Pi.sub_apply]
  have e : ∀ l : Upper, comp (q - p) l.1.1 l.1.2 = comp q l.1.1 l.1.2 - comp p l.1.1 l.1.2 :=
    fun l => rfl
  simp only [e]
  have hl : ∀ u w : Grid N → ℝ, lapR (lapR (u - w)) = lapR (lapR u) - lapR (lapR w) := by
    intro u w
    rw [show lapR (u - w) = lapR u - lapR w from lapRLin.map_sub u w]
    exact lapRLin.map_sub _ _
  simp only [hl, Pi.sub_apply, mul_sub, sum_sub_distrib]

/-- The coefficient remainder `(a(p)⁻¹ - a(q)⁻¹) h² B Λ_h² p` of the force difference. -/
def lawForceRem (B : Upper → Upper → ℝ) (q p : Grid N → MetricRec) : Grid N → MetricRec :=
  fun x μ ν => ((aArr p x)⁻¹ - (aArr q x)⁻¹) * bTerm B p x μ ν

/-- `lawForce B q - lawForce B p = -a(q)⁻¹ h² B Λ_h² (q - p) + (a(p)⁻¹ - a(q)⁻¹) h² B Λ_h² p`. -/
theorem lawForce_sub (B : Upper → Upper → ℝ) (q p : Grid N → MetricRec) :
    lawForce B q - lawForce B p = bForceAt (aArr q) B (q - p) + lawForceRem B q p := by
  funext x μ ν
  have h := congrFun (congrFun (congrFun (lawDiff_bTerm_sub B q p) x) μ) ν
  simp only [Pi.sub_apply] at h
  simp only [lawForce, bForceAt, lawForceRem, Pi.sub_apply, Pi.add_apply, ← h]
  ring

/-! ### The difference rate is affine in the force difference -/

theorem diffRate_force (r : ℕ) (q p v w f g : Grid N → MetricRec) :
    diffRate r q p v w f g = diffRate r q p v w 0 0 + forcingTerm r q (v - w) (f - g) := by
  have hd : ∀ α (μ ν : Fin 4), DαR α (comp (dAcc q p v w f g) μ ν) =
      DαR α (comp (dAcc q p v w 0 0) μ ν) + DαR α (comp (f - g) μ ν) := by
    intro α μ ν
    rw [← DαR_add]
    congr 1
    funext y
    simp only [comp, dAcc, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    ring
  unfold diffRate forcingTerm Rdiff
  simp only [hd, Pi.add_apply]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, ← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun κ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  ring

/-! ### The difference energy and its equivalence -/

/-- **The difference energy of the law family**: the quadratic energy of the data `(Q, V)` with
the shifted coefficients `a, c` plus the added stencil energy of `Q`. -/
def lawGenEnergy (B : Upper → Upper → ℝ) (r : ℕ) (a : Grid N → ℝ)
    (c : Fin 3 → Fin 3 → Grid N → ℝ) (Q V : Grid N → MetricRec) : ℝ :=
  genEnergy r a c Q V + lawExtra B r Q

/-- **Energy equivalence for the difference energy**: on the pointwise chart and for every mark
with `‖B‖_op ≤ b ≤ 1/48`, `⅛ ‖(Q, V)‖²_{X^r_h} ≤ 𝓔^δ ≤ 9 ‖(Q, V)‖²_{X^r_h}` for all data. -/
theorem lawGenEnergy_bounds (r : ℕ) {b : ℝ} {B : Upper → Upper → ℝ} (hB : IsMark b B)
    (hb : b ≤ 1 / 48) (a : Grid N → ℝ) (c : Fin 3 → Fin 3 → Grid N → ℝ)
    (ha : ∀ x, 1 / 2 ≤ a x ∧ a x ≤ 3 / 2)
    (hc : ∀ x i j, |c i j x - (if i = j then 1 else 0)| ≤ 1 / 18) (Q V : Grid N → MetricRec) :
    Xsq r Q V / 8 ≤ lawGenEnergy B r a c Q V ∧ lawGenEnergy B r a c Q V ≤ 9 * Xsq r Q V := by
  have hb0 := hB.nonneg
  set Dg : (Fin 3 → ℕ) → ℝ := fun α => ∑ κ : Upper, ∑ i, PeriodicGridSobolev.gridNormSq
    (PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2))))
  have hDgG : ∀ α, Dg α ≤ ∑ κ : Upper, levelG α Q V κ := by
    intro α
    refine sum_le_sum fun κ _ => ?_
    unfold levelG
    have := PeriodicGridSobolev.gridNormSq_nonneg
      (PeriodicGridSobolev.Dα α (cx (comp V κ.1.1 κ.1.2)))
    have := PeriodicGridSobolev.gridNormSq_nonneg
      (PeriodicGridSobolev.Dα α (cx (comp Q κ.1.1 κ.1.2)))
    linarith
  have hext := fun α => abs_lawExtra_level_le hB α Q
  unfold lawGenEnergy
  rw [lawExtra_eq_sum]
  unfold genEnergy
  rw [← sum_add_distrib]
  constructor
  · calc Xsq r Q V / 8 ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices r,
          (1 / 8) * ∑ κ : Upper, levelG α Q V κ := by
          rw [← mul_sum, div_eq_mul_inv, mul_comm]
          have := Xsq_le_sum_levelG r Q V
          linarith
      _ ≤ _ := by
          refine sum_le_sum fun α _ => ?_
          have h1 := energy_level_lower α a c ha hc Q V
          have h2 := neg_abs_le (((N : ℝ) ^ 2)⁻¹ / 2 * ∑ k : Upper, ∑ l : Upper, B k l *
            (((N : ℝ) ^ 3)⁻¹ * ∑ x, lapR (DαR α (comp Q k.1.1 k.1.2)) x *
              lapR (DαR α (comp Q l.1.1 l.1.2)) x))
          have h3 := hext α
          have h4 := hDgG α
          have h5 : 6 * b * Dg α ≤ 1 / 8 * ∑ κ : Upper, levelG α Q V κ := by
            have : 0 ≤ Dg α := sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
              PeriodicGridSobolev.gridNormSq_nonneg _
            nlinarith
          simp only [Dg] at h4 h5
          linarith
  · have hup := (genEnergy_bounds r a c ha hc Q V).2
    have hgr := sum_grad_le r Q V
    calc _ ≤ ∑ α ∈ PeriodicGridSobolev.multiIndices r, (energy (SαR α a)
          (fun i j => SαR α (c i j)) (fun κ : Upper => DαR α (comp Q κ.1.1 κ.1.2))
          (fun κ : Upper => DαR α (comp V κ.1.1 κ.1.2)) + 6 * b * Dg α) :=
          sum_le_sum fun α _ => add_le_add le_rfl ((le_abs_self _).trans (hext α))
      _ = genEnergy r a c Q V + 6 * b *
          ∑ α ∈ PeriodicGridSobolev.multiIndices r, Dg α := by
          rw [sum_add_distrib, ← mul_sum]; rfl
      _ ≤ 8 * Xsq r Q V + 6 * b * (3 * Xsq r Q V) := by
          gcongr
      _ ≤ 9 * Xsq r Q V := by
          have := Xsq_nonneg r Q V
          nlinarith

/-- **Exact identity for the difference energy of the law family.**  Along two forced law-family
histories, `d𝓔^δ/dt = diffRate(0, 0) - commTermAt + ⟨δv, a (a(p)⁻¹ - a(q)⁻¹) h² B Λ_h² p⟩
 + ⟨δv, a (f - f̃)⟩` (all at order `r`); the stencil `-h² B Λ_h² δq` has cancelled. -/
theorem hasDerivAt_lawDiffEnergy (B : Upper → Upper → ℝ) (hB : ∀ k l, B k l = B l k) (r : ℕ)
    (q p v w f g : ℝ → Grid N → MetricRec) (t : ℝ) (hsym : IsSymRec (q t))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hp : ∀ x, HasDerivAt (fun τ => p τ x) (w t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (lawAccel B (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t)
    (hw : ∀ x (κ : Upper), HasDerivAt (fun τ => w τ x κ.1.1 κ.1.2)
      (lawAccel B (p t) (w t) x κ.1.1 κ.1.2 + g t x κ.1.1 κ.1.2) t)
    (hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q t x))
    (hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t x))
    (haq : ∀ x, aArr (q t) x ≠ 0) :
    HasDerivAt (fun τ => lawGenEnergy B r (aArr (q τ)) (cArr (q τ)) (q τ - p τ) (v τ - w τ))
      (diffRate r (q t) (p t) (v t) (w t) 0 0 - commTermAt B r (aArr (q t)) (q t - p t) (v t - w t) +
        forcingTerm r (q t) (v t - w t) (lawForceRem B (q t) (p t)) +
        forcingTerm r (q t) (v t - w t) (f t - g t)) t := by
  have h1 := hasDerivAt_diffEnergy r q p v w (fun τ => lawForce B (q τ) + f τ)
    (fun τ => lawForce B (p τ) + g τ) t hsym hq hp
    (fun x κ => by
      have := hv x κ
      simp only [lawAccel, Pi.add_apply] at this ⊢
      rw [← add_assoc]; exact this)
    (fun x κ => by
      have := hw x κ
      simp only [lawAccel, Pi.add_apply] at this ⊢
      rw [← add_assoc]; exact this) hdA hdC
  have h2 := hasDerivAt_lawExtra B hB r (fun τ => q τ - p τ) (fun τ => v τ - w τ) t
    (fun x => (hq x).sub (hp x))
  refine (h1.add h2).congr_deriv ?_
  have e : lawForce B (q t) + f t - (lawForce B (p t) + g t) =
      bForceAt (aArr (q t)) B (q t - p t) + lawForceRem B (q t) (p t) + (f t - g t) := by
    rw [← lawForce_sub]; abel
  rw [diffRate_force, e, forcingTerm_add, forcingTerm_add,
    forcingTerm_bForceAt B r (q t) (q t - p t) (v t - w t) haq]
  ring

/-! ### The static bound -/

/-- The forcing pairing is bounded by `(3/2) #α #κ ‖(Q, V)‖_{X^r_h} ‖F‖_{r,h}` when `|a| ≤ 3/2`. -/
theorem forcingTerm_le_chart (r : ℕ) (q Q V F : Grid N → MetricRec) (hV : IsSymRec V)
    (ha : ∀ y, |aArr q y| ≤ 3 / 2) :
    forcingTerm r q V F ≤ 3 / 2 * ((PeriodicGridSobolev.multiIndices r).card : ℝ) *
      (Fintype.card Upper : ℝ) * Xnorm r Q V * Fnorm r F := by
  unfold forcingTerm
  have hX0 := Xnorm_nonneg r Q V
  have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices r, ∀ κ : Upper,
      ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp V κ.1.1 κ.1.2) x *
        (SαR α (aArr q) x * DαR α (comp F κ.1.1 κ.1.2) x) ≤ Xnorm r Q V * (3 / 2 * Fnorm r F) := by
    intro α hα κ
    have hdeg := PeriodicGridSobolev.mem_multiIndices.mp hα
    refine (le_abs_self _).trans ((abs_inner_le _ _).trans ?_)
    refine mul_le_mul ?_ ?_ (PeriodicGridSobolev.gridNorm_nonneg _) hX0
    · exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le r Q hV _ _ le_rfl)
    · refine (gridNorm_cx_mul_le (by norm_num) (fun x => ha (x + svec α))).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_le_Fnorm r F κ)
  calc _ ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices r, ∑ _κ : Upper,
        Xnorm r Q V * (3 / 2 * Fnorm r F) := sum_le_sum fun α hα => sum_le_sum fun κ _ => hper α hα κ
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **The frozen-coefficient commutator is quadratic in the difference**: if `|a(q)| ≤ 3/2` and
`‖a(q)⁻¹ - 1‖_{r,h} ≤ 1`, then `|commTermAt B r (a(q)) Q V| ≤ K ‖(Q, V)‖²_{X^r_h}`. -/
theorem abs_commTermAt_le (r : ℕ) (hr : 3 ≤ r) :
    ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q Q V : Grid N → MetricRec) (b : ℝ)
      (B : Upper → Upper → ℝ), IsMark b B → b ≤ 1 / 48 → IsSymRec Q → IsSymRec V →
      (∀ y, |aArr q y| ≤ 3 / 2) →
      PeriodicGridSobolev.sobNorm r (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 →
      |commTermAt B r (aArr q) Q V| ≤ K * Xnorm r Q V ^ 2 := by
  obtain ⟨Cc, hCc, hcalc⟩ := PeriodicGridSobolev.uniform_sobolev_calculus r hr
  refine ⟨((PeriodicGridSobolev.multiIndices r).card : ℝ) * (Fintype.card Upper : ℝ) *
    (3 / 2 * (Cc * 12)), by positivity, fun N _ q Q V b B hB hb hQ hV ha hainv => ?_⟩
  have hb0 := hB.nonneg
  set X := Xnorm r Q V
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  obtain ⟨-, hcomm⟩ := hcalc N
  have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices r, ∀ k : Upper,
      |((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp V k.1.1 k.1.2) x * (SαR α (aArr q) x *
        commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B Q) k.1.1 k.1.2) x)| ≤
      3 / 2 * (Cc * 12) * X ^ 2 := by
    intro α hα k
    have hdeg := PeriodicGridSobolev.mem_multiIndices.mp hα
    refine (abs_inner_le _ _).trans ?_
    have h1 : PeriodicGridSobolev.gridNorm (cx (DαR α (comp V k.1.1 k.1.2))) ≤ X :=
      (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le r Q hV _ _ le_rfl)
    have h2 : PeriodicGridSobolev.gridNorm (cx (fun x => SαR α (aArr q) x *
        commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B Q) k.1.1 k.1.2) x)) ≤
        3 / 2 * PeriodicGridSobolev.gridNorm
          (cx (commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B Q) k.1.1 k.1.2))) :=
      gridNorm_cx_mul_le (by norm_num) (fun x => ha (x + svec α))
    have h3 : PeriodicGridSobolev.gridNorm
        (cx (commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B Q) k.1.1 k.1.2))) ≤
        Cc * 1 * (12 * X) := by
      rw [cx_commR]
      refine ((hcomm α hdeg _ _ 1 0).1).trans ?_
      have hw := sobNorm_bTerm_le r (by omega) hB hQ V k
      have hw' : PeriodicGridSobolev.sobNorm (r - 1) (cx (comp (bTerm B Q) k.1.1 k.1.2)) ≤
          12 * X := hw.trans (by nlinarith)
      gcongr
      exact PeriodicGridSobolev.Moser.sobNorm_nonneg _ _
    calc PeriodicGridSobolev.gridNorm (cx (DαR α (comp V k.1.1 k.1.2))) *
          PeriodicGridSobolev.gridNorm (cx (fun x => SαR α (aArr q) x *
            commR α (fun y => (aArr q y)⁻¹) (comp (bTerm B Q) k.1.1 k.1.2) x))
        ≤ X * (3 / 2 * (Cc * 1 * (12 * X))) := by
          refine mul_le_mul h1 (h2.trans ?_) (PeriodicGridSobolev.gridNorm_nonneg _) hX0
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 3 / 2 * (Cc * 12) * X ^ 2 := by ring
  unfold commTermAt
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices r, ∑ _k : Upper,
        3 / 2 * (Cc * 12) * X ^ 2 :=
        sum_le_sum fun α hα => (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun k _ => hper α hα k)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

/-- **Static bound of the law-family difference rate**: for `3 ≤ r`, `r + 1 ≤ s` there are
`δ > 0`, `K ≥ 0`, independent of the mesh and of the mark (`‖B‖_op ≤ 1/48`), such that for two
symmetric records in the top chart and arbitrary forces `f, f̃`, the rate of
`hasDerivAt_lawDiffEnergy` is `≤ K ‖δX‖²_{X^r_h} + K ‖δX‖_{X^r_h} ‖f - f̃‖_{r,h}`. -/
theorem law_diff_static_bound (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ)
      (q p v w f g : Grid N → MetricRec), IsMark (1 / 48) B →
      IsSymRec q → IsSymRec p → IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ → Xnorm s p w ≤ δ →
      diffRate r q p v w 0 0 - commTermAt B r (aArr q) (q - p) (v - w) +
        forcingTerm r q (v - w) (lawForceRem B q p) + forcingTerm r q (v - w) (f - g) ≤
        K * Xsq r (q - p) (v - w) + K * Xnorm r (q - p) (v - w) * Fnorm r (f - g) := by
  obtain ⟨δd, hδd, Kd, hKd, hstat⟩ := diff_static_bound s r hr hrs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s (by omega)
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients r (by omega)
  obtain ⟨Kc, hKc, hcomm⟩ := abs_commTermAt_le r hr
  obtain ⟨pser, R, hpser⟩ := analyticAt_harmA_inv
  obtain ⟨δL, hδL, CL, hCL, hLip⟩ :=
    PeriodicGridSobolev.Moser.moser_lipschitz r (by omega) bM hpser
  set cF : ℝ := 3 / 2 * ((PeriodicGridSobolev.multiIndices r).card : ℝ) *
    (Fintype.card Upper : ℝ)
  have hcF : 0 ≤ cF := by positivity
  set Ar := PeriodicGridSobolev.Moser.algConst r
  have hAr := PeriodicGridSobolev.Moser.algConst_pos r
  set CRm : ℝ := 16 * (Ar * (CL * 16) * 12)
  have hCRm : 0 ≤ CRm := by positivity
  set δ : ℝ := min δd (min δ0 (min 1 (min (δa / 16) (min (δL / 16) (1 / (16 * (Ca + 1)))))))
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, Kd + Kc + cF * CRm + cF, by positivity,
    fun N _ B q p v w f g hB hq hp hv hw hXq hXp => ?_⟩
  have hδd' : δ ≤ δd := min_le_left _ _
  have hδ0' : δ ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδa' : δ ≤ δa / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδL' : δ ≤ δL / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδC : δ ≤ 1 / (16 * (Ca + 1)) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  set D := Xnorm r (q - p) (v - w)
  set F := Fnorm r (f - g)
  have hD0 : 0 ≤ D := Xnorm_nonneg _ _ _
  have hF0 : 0 ≤ F := Fnorm_nonneg _ _
  have hD2 : Xsq r (q - p) (v - w) = D ^ 2 := (Xnorm_sq _ _ _).symm
  obtain ⟨ha, -, -, -, -, -⟩ := hpc N q v hq hv (hXq.trans hδ0')
  have ha' : ∀ y, |aArr q y| ≤ 3 / 2 := fun y => by
    rw [abs_le]; constructor <;> linarith [(ha y).1, (ha y).2]
  have hcsq : PeriodicGridSobolev.Moser.coordSum r bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hcsp : PeriodicGridSobolev.Moser.coordSum r bM p ≤ 16 * Xnorm s p w :=
    coordSum_bM_q_le s hp w (by omega)
  have hainv : PeriodicGridSobolev.sobNorm r
      (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := by
    have hM := hma N q (hcsq.trans (by linarith [hXq.trans hδa']))
    refine hM.2.1.trans ?_
    have h1 : X ≤ 1 / (16 * (Ca + 1)) := hXq.trans hδC
    rw [le_div_iff₀ (by positivity)] at h1
    calc Ca * PeriodicGridSobolev.Moser.coordSum r bM q ≤ Ca * (16 * X) :=
          mul_le_mul_of_nonneg_left hcsq hCa
      _ ≤ 1 := by nlinarith
  have hqd := isSymRec_sub hq hp
  have hvd := isSymRec_sub hv hw
  -- the four pieces
  have t1 : diffRate r q p v w 0 0 ≤ Kd * D ^ 2 := by
    have := hstat N q p v w 0 0 hq hp hv hw (hXq.trans hδd') (hXp.trans hδd')
    rw [sub_self, lawDiff_Fnorm_zero, mul_zero, add_zero, hD2] at this
    exact this
  have t2 : -commTermAt B r (aArr q) (q - p) (v - w) ≤ Kc * D ^ 2 :=
    (neg_le_abs _).trans (hcomm N q (q - p) (v - w) (1 / 48) B hB le_rfl hqd hvd ha' hainv)
  have hRem : Fnorm r (lawForceRem B q p) ≤ CRm * D := by
    have hM : 0 ≤ Ar * (CL * 16 * D) * 12 := by positivity
    refine (lawDiff_Fnorm_le_of_comp_le r _ hM fun κ => ?_).trans (le_of_eq (by simp only [CRm]; ring))
    have e : cx (comp (lawForceRem B q p) κ.1.1 κ.1.2) =
        (cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹)) *
          cx (comp (bTerm B p) κ.1.1 κ.1.2) := by
      funext x; simp [comp, cx, lawForceRem]
    rw [e]
    refine (PeriodicGridSobolev.Moser.sobNorm_mul_le r (by omega) _ _).trans ?_
    have hL := hLip N p q (hcsp.trans (by linarith [hXp.trans hδL']))
      (hcsq.trans (by linarith [hXq.trans hδL']))
    have hL' : PeriodicGridSobolev.sobNorm r
        (cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹)) ≤ CL * 16 * D := by
      have e2 : cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹) =
          fun x => (((harmA (minkowski + p x))⁻¹ - (harmA (minkowski + q x))⁻¹ : ℝ) : ℂ) := by
        funext x; simp [cx, aArr]
      rw [e2]
      refine hL.trans ?_
      have hc := coordSum_bM_q_le r (isSymRec_sub hp hq) (w - v) (show r ≤ r + 1 by omega)
      rw [lawDiff_Xnorm_sub_comm] at hc
      calc CL * PeriodicGridSobolev.Moser.coordSum r bM (p - q) ≤ CL * (16 * D) :=
            mul_le_mul_of_nonneg_left hc hCL
        _ = CL * 16 * D := by ring
    have hbT : PeriodicGridSobolev.sobNorm r (cx (comp (bTerm B p) κ.1.1 κ.1.2)) ≤ 12 := by
      have h1 := sobNorm_bTerm_le (r + 1) (by omega) hB hp w κ
      rw [show r + 1 - 1 = r by omega] at h1
      have h2 : Xnorm (r + 1) p w ≤ 1 := (lawDiff_Xnorm_mono hrs p w).trans (hXp.trans hδ1)
      have h3 : 0 ≤ Xnorm (r + 1) p w := Xnorm_nonneg _ _ _
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL' hAr.le) hbT
      (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (by positivity)
  have t3 : forcingTerm r q (v - w) (lawForceRem B q p) ≤ cF * D * (CRm * D) := by
    refine (forcingTerm_le_chart r q (q - p) (v - w) _ hvd ha').trans ?_
    exact mul_le_mul_of_nonneg_left hRem (mul_nonneg hcF hD0)
  have t4 : forcingTerm r q (v - w) (f - g) ≤ cF * D * F :=
    forcingTerm_le_chart r q (q - p) (v - w) _ hvd ha'
  rw [hD2]
  have e : (Kd + Kc + cF * CRm + cF) * D ^ 2 + (Kd + Kc + cF * CRm + cF) * D * F =
      Kd * D ^ 2 + Kc * D ^ 2 + cF * D * (CRm * D) + cF * D * F +
        (cF * D ^ 2 + (Kd + Kc + cF * CRm) * D * F) := by ring
  have h6 : 0 ≤ Kd + Kc + cF * CRm := by nlinarith [mul_nonneg hcF hCRm]
  have h5 : 0 ≤ cF * D ^ 2 + (Kd + Kc + cF * CRm) * D * F :=
    add_nonneg (mul_nonneg hcF (sq_nonneg D)) (mul_nonneg (mul_nonneg h6 hD0) hF0)
  linarith

/-- A pair of forced histories of the law-family member `B` on `[0, T]`, both in the top chart
`‖·‖_{X^s_h} ≤ δ`: `q_t = v`, `v_t = V_{B,h}(q, v) + f`, `p_t = w`, `w_t = V_{B,h}(p, w) + f̃`
(ten-component equations, two-sided derivatives, symmetric records). -/
def IsLawForcedPair (B : Upper → Upper → ℝ) (s : ℕ) (δ T : ℝ)
    (q p v w f g : ℝ → Grid N → MetricRec) : Prop :=
  ∀ t ∈ Icc 0 T, IsSymRec (q t) ∧ IsSymRec (v t) ∧ IsSymRec (p t) ∧ IsSymRec (w t) ∧
    (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) ∧
    (∀ x, HasDerivAt (fun τ => p τ x) (w t x) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (lawAccel B (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t) ∧
    (∀ x (κ : Upper), HasDerivAt (fun τ => w τ x κ.1.1 κ.1.2)
      (lawAccel B (p t) (w t) x κ.1.1 κ.1.2 + g t x κ.1.1 κ.1.2) t) ∧
    Xnorm s (q t) (v t) ≤ δ ∧ Xnorm s (p t) (w t) ≤ δ

/-- **The lower-order difference estimate for the law family** (`eq:supp-open-difference` for
every member `B` of `eq:supp-law-family`; the fourth-order stencil is cancelled through the
difference energy `lawGenEnergy`).  For `3 ≤ r ≤ s - 1` there are a top-chart radius `δ > 0` and
`K ≥ 0`, independent of the mesh and of the mark (`B = Bᵀ`, `‖B‖_op ≤ 1/48`), such that for every
`T ≥ 0` and every two top-bounded forced law histories with forces `f, f̃` continuous on `[0, T]`,
`‖X(t) - Y(t)‖_{X^r_h} ≤ 3 e^{K t} (3 ‖X(0) - Y(0)‖_{X^r_h} + K ∫_0^t ‖f - f̃‖_{r,h})`. -/
theorem law_difference (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (T : ℝ)
      (q p v w f g : ℝ → Grid N → MetricRec), IsMark (1 / 48) B →
      IsLawForcedPair B s δ T q p v w f g → ContinuousOn f (Icc 0 T) → ContinuousOn g (Icc 0 T) →
      ∀ t ∈ Icc 0 T, Xnorm r (q t - p t) (v t - w t) ≤
        3 * Real.exp (K * t) * (3 * Xnorm r (q 0 - p 0) (v 0 - w 0) +
          K * ∫ τ in (0)..t, Fnorm r (f τ - g τ)) := by
  have hs : 3 ≤ s := by omega
  obtain ⟨δ1, hδ1, Ks, hKs, hstat⟩ := law_diff_static_bound s r hr hrs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  set δ := min δ1 δ0
  have hδ : 0 < δ := lt_min hδ1 hδ0
  refine ⟨δ, hδ, 8 * Ks, by positivity, fun N _ B T q p v w f g hB hpair hf hg => ?_⟩
  set E : ℝ → ℝ := fun τ =>
    lawGenEnergy B r (aArr (q τ)) (cArr (q τ)) (q τ - p τ) (v τ - w τ)
  set Fn : ℝ → ℝ := fun τ => Fnorm r (f τ - g τ)
  set Dn : ℝ → ℝ := fun τ => Xnorm r (q τ - p τ) (v τ - w τ)
  have hbd : ∀ τ ∈ Icc 0 T, Xsq r (q τ - p τ) (v τ - w τ) / 8 ≤ E τ ∧
      E τ ≤ 9 * Xsq r (q τ - p τ) (v τ - w τ) := by
    intro τ hτ
    obtain ⟨hqs, hvs, -, -, -, -, -, -, hXq, -⟩ := hpair τ hτ
    obtain ⟨ha, hc, -⟩ := hpc N (q τ) (v τ) hqs hvs (hXq.trans (min_le_right _ _))
    exact lawGenEnergy_bounds r hB le_rfl _ _ ha hc _ _
  have hE0 : ∀ τ ∈ Icc 0 T, 0 ≤ E τ := fun τ hτ =>
    le_trans (by have := Xsq_nonneg r (q τ - p τ) (v τ - w τ); linarith) (hbd τ hτ).1
  have hDs : ∀ τ ∈ Icc 0 T, Dn τ ≤ 3 * Real.sqrt (E τ) := by
    intro τ hτ
    have h1 : Dn τ ^ 2 ≤ 9 * E τ := by
      have := (hbd τ hτ).1
      rw [show Dn τ ^ 2 = Xsq r (q τ - p τ) (v τ - w τ) from Xnorm_sq _ _ _]
      linarith [hE0 τ hτ]
    have hD0 : 0 ≤ Dn τ := Xnorm_nonneg _ _ _
    have hs3 : (3 * Real.sqrt (E τ)) ^ 2 = 9 * E τ := by
      rw [mul_pow, Real.sq_sqrt (hE0 τ hτ)]; norm_num
    nlinarith [Real.sqrt_nonneg (E τ)]
  have hderiv : ∀ τ ∈ Icc 0 T, ∃ e', HasDerivAt E e' τ ∧
      e' ≤ 8 * Ks * E τ + 8 * Ks * Real.sqrt (E τ) * Fn τ := by
    intro τ hτ
    obtain ⟨hqs, hvs, hps, hws, hq, hp, hv, hw, hXq, hXp⟩ := hpair τ hτ
    obtain ⟨ha, -, -, -, hdA, hdC⟩ := hpc N (q τ) (v τ) hqs hvs (hXq.trans (min_le_right _ _))
    have haq : ∀ x, aArr (q τ) x ≠ 0 := fun x => by have := (ha x).1; positivity
    refine ⟨_, hasDerivAt_lawDiffEnergy B hB.1 r q p v w f g τ hqs hq hp hv hw hdA hdC haq, ?_⟩
    have h1 := hstat N B (q τ) (p τ) (v τ) (w τ) (f τ) (g τ) hB hqs hps hvs hws
      (hXq.trans (min_le_left _ _)) (hXp.trans (min_le_left _ _))
    have h2 : Xsq r (q τ - p τ) (v τ - w τ) ≤ 8 * E τ := by linarith [(hbd τ hτ).1]
    have h3 : Dn τ * Fn τ ≤ 3 * Real.sqrt (E τ) * Fn τ :=
      mul_le_mul_of_nonneg_right (hDs τ hτ) (Fnorm_nonneg _ _)
    have h4 : Ks * Xsq r (q τ - p τ) (v τ - w τ) ≤ Ks * (8 * E τ) :=
      mul_le_mul_of_nonneg_left h2 hKs
    have h5 : Ks * (Dn τ * Fn τ) ≤ Ks * (3 * Real.sqrt (E τ) * Fn τ) :=
      mul_le_mul_of_nonneg_left h3 hKs
    have h6 : 0 ≤ Ks * (Real.sqrt (E τ) * Fn τ) := by
      have := Fnorm_nonneg r (f τ - g τ)
      have := Real.sqrt_nonneg (E τ)
      positivity
    have e1 : Ks * Xnorm r (q τ - p τ) (v τ - w τ) * Fnorm r (f τ - g τ) =
        Ks * (Dn τ * Fn τ) := by
      simp only [Dn, Fn]; ring
    rw [e1] at h1
    nlinarith
  have hFc : ContinuousOn Fn (Icc 0 T) := (continuous_Fnorm r).comp_continuousOn (hf.sub hg)
  intro t ht
  have hgr := ODECutoff.sqrt_le_of_forced_deriv (by positivity) hderiv hE0 hFc
    (fun τ _ => Fnorm_nonneg _ _) t ht
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsE0 : Real.sqrt (E 0) ≤ 3 * Dn 0 := by
    have h1 := (hbd 0 hT).2
    have hD0 : 0 ≤ Dn 0 := Xnorm_nonneg _ _ _
    rw [show Xsq r (q 0 - p 0) (v 0 - w 0) = Dn 0 ^ 2 from (Xnorm_sq _ _ _).symm] at h1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hint : 0 ≤ ∫ τ in (0)..t, Fn τ :=
    intervalIntegral.integral_nonneg ht.1 fun τ _ => Fnorm_nonneg _ _
  have hex := Real.exp_pos (8 * Ks * t)
  calc Dn t ≤ 3 * Real.sqrt (E t) := hDs t ht
    _ ≤ 3 * (Real.exp (8 * Ks * t) * (Real.sqrt (E 0) + 8 * Ks * ∫ τ in (0)..t, Fn τ)) := by
        gcongr
    _ ≤ 3 * Real.exp (8 * Ks * t) * (3 * Dn 0 + 8 * Ks * ∫ τ in (0)..t, Fn τ) := by
        rw [← mul_assoc]
        gcongr

set_option maxHeartbeats 4000000 in
/-- **Lipschitz bound of the writer acceleration one order down** (the bound `hδvt` inside
`diff_static_bound`, exported): for `3 ≤ r`, `r + 1 ≤ s` there are `δ > 0`, `K ≥ 0`,
independent of the mesh, such that for two symmetric records in the top chart and forces
`f, f̃`, `‖(V_{0,h}(q,v) + f) - (V_{0,h}(p,w) + f̃)‖_{r-1,h} ≤ K (‖δX‖_{X^r_h} + ‖f - f̃‖_{r,h})`
componentwise. -/
theorem dAcc_bound (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q p v w f g : Grid N → MetricRec),
      IsSymRec q → IsSymRec p → IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ → Xnorm s p w ≤ δ →
      ∀ κ : Upper, PeriodicGridSobolev.sobNorm (r - 1) (cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) ≤
        K * (Xnorm r (q - p) (v - w) + Fnorm r (f - g)) := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  have hs : 3 ≤ s := by omega
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s hs
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients r (by omega)
  obtain ⟨δa1, hδa1, Ca1, hCa1, hma1⟩ := moser_coefficients (r - 1) (by omega)
  obtain ⟨δc, hδc, Cc, hCc, hmc⟩ := moser_coefficients (r + 1) (by omega)
  obtain ⟨δl, hδl, Cl, hCl, hml⟩ := moser_lipschitz_coefficients r (by omega)
  obtain ⟨δl1, hδl1, Cl1, hCl1, hml1⟩ := moser_lipschitz_coefficients (r + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hmG⟩ := moser_lipschitz_compensator r (by omega)
  set Cs : ℝ := Ca + Ca1 + Cc + 1
  have hCs : 0 < Cs := by positivity
  set δ : ℝ := min (min (min δ0 δA) (min 1 (1 / (16 * Cs))))
    (min (min (δa / 16) (δa1 / 16)) (min (min (δc / 16) (δl / 16)) (min (δl1 / 16) (δG / 80))))
  have hδ : 0 < δ := by positivity
  set Ar := algConst r
  set Ar1 := algConst (r - 1)
  set Ar2 := algConst (r + 1)
  have hAr := algConst_pos r
  have hAr1 := algConst_pos (r - 1)
  have hAr2 := algConst_pos (r + 1)
  set CGt : ℝ := CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
    3 * ((Ar + Ar2) * (Cl1 * 16)) + (Ar + 1)
  have hCGt : 0 ≤ CGt := by positivity
  set CV : ℝ := (Ar1 + 1) * (9 * (Ar + 1) + 3 * Ar1 + 3 * Ar + CGt)
  have hCV : 0 ≤ CV := by positivity
  refine ⟨δ, hδ, CV, hCV, fun N _ q p v w f g hq hp hv hw hXq hXp => ?_⟩
  -- bookkeeping of the radii
  set Xq := Xnorm s q v
  set Xp := Xnorm s p w
  have hXq0 : 0 ≤ Xq := Xnorm_nonneg _ _ _
  have hXp0 : 0 ≤ Xp := Xnorm_nonneg _ _ _
  have hδ0' : δ ≤ δ0 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδA' : δ ≤ δA := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / (16 * Cs) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδa' : δ ≤ δa / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδa1' : δ ≤ δa1 / 16 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc' : δ ≤ δc / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _)))
  have hδl' : δ ≤ δl / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _)))
  have hδl1' : δ ≤ δl1 / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδG' : δ ≤ δG / 80 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hXq1 : Xq ≤ 1 := hXq.trans hδ1
  have hXp1 : Xp ≤ 1 := hXp.trans hδ1
  have hsmall : 16 * Cs * Xq ≤ 1 := by
    have := hXq.trans hδCs
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hCsX : ∀ C', 0 ≤ C' → C' ≤ Cs → C' * (16 * Xq) ≤ 1 := fun C' _ hC' =>
    calc C' * (16 * Xq) ≤ Cs * (16 * Xq) := mul_le_mul_of_nonneg_right hC' (by positivity)
      _ = 16 * Cs * Xq := by ring
      _ ≤ 1 := hsmall
  have hCaX : Ca * (16 * Xq) ≤ 1 := hCsX Ca hCa (by simp only [Cs]; linarith)
  have hCa1X : Ca1 * (16 * Xq) ≤ 1 := hCsX Ca1 hCa1 (by simp only [Cs]; linarith)
  have hCcX : Cc * (16 * Xq) ≤ 1 := hCsX Cc hCc (by simp only [Cs]; linarith)
  -- the pointwise chart of `q` and `p`
  obtain ⟨ha, hc, hadot, hcdot, -, -⟩ := hpc N q v hq hv (hXq.trans hδ0')
  obtain ⟨hap, -, -, -, -, -⟩ := hpc N p w hp hw (hXp.trans hδ0')
  have haq_ne : ∀ x, aArr q x ≠ 0 := fun x => by have := (ha x).1; positivity
  have hap_ne : ∀ x, aArr p x ≠ 0 := fun x => by have := (hap x).1; positivity
  -- coefficient bounds for `q`
  have hcsq_r : coordSum r bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hcsq_r1 : coordSum (r - 1) bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hcsq_r2 : coordSum (r + 1) bM q ≤ 16 * Xq := coordSum_bM_q_le s hq v (by omega)
  have hMa := hma N q (hcsq_r.trans (by linarith [hXq.trans hδa']))
  have hMa1 := hma1 N q (hcsq_r1.trans (by linarith [hXq.trans hδa1']))
  have hMc := hmc N q (hcsq_r2.trans (by linarith [hXq.trans hδc']))
  have ha_r : sobNorm r (cx (aArr q) - fun _ => (1 : ℂ)) ≤ 1 :=
    hMa.1.trans ((mul_le_mul_of_nonneg_left hcsq_r hCa).trans hCaX)
  have hainv : sobNorm (r - 1) (cx (fun x => (harmA (minkowski + q x))⁻¹) -
      fun _ => (1 : ℂ)) ≤ 1 :=
    hMa1.2.1.trans ((mul_le_mul_of_nonneg_left hcsq_r1 hCa1).trans hCa1X)
  have hc_r2 : ∀ i j, sobNorm (r + 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 := fun i j =>
    (hMc.2.2.1 i j).trans ((mul_le_mul_of_nonneg_left hcsq_r2 hCc).trans hCcX)
  have hb_r2 : ∀ i, sobNorm (r + 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := fun i =>
    (hMc.2.2.2 i).trans ((mul_le_mul_of_nonneg_left hcsq_r2 hCc).trans hCcX)
  -- the difference norms
  set D := Xnorm r (q - p) (v - w)
  set F := Fnorm r (f - g)
  have hD0 : 0 ≤ D := Xnorm_nonneg _ _ _
  have hF0 : 0 ≤ F := Fnorm_nonneg _ _
  have hqd := isSymRec_sub hq hp
  have hvd := isSymRec_sub hv hw
  have hDcs : coordSum r bM (q - p) ≤ 16 * D := coordSum_bM_q_le r hqd (v - w) (by omega)
  have hDcs1 : coordSum (r + 1) bM (q - p) ≤ 16 * D := coordSum_bM_q_le r hqd (v - w) le_rfl
  have hDcJ : coordSum r bJ (jetArr (q - p) (v - w)) ≤ 80 * D := coordSum_bJ_le r hqd hvd
  -- Lipschitz bounds
  have hL := hml N q p (hcsq_r.trans (by linarith [hXq.trans hδl']))
    ((coordSum_bM_q_le s hp w (by omega)).trans (by linarith [hXp.trans hδl']))
  have hL1 := hml1 N q p (hcsq_r2.trans (by linarith [hXq.trans hδl1']))
    ((coordSum_bM_q_le s hp w (by omega)).trans (by linarith [hXp.trans hδl1']))
  have hLG := hmG N (jetArr q v) (jetArr p w)
    (((coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le s hq hv)).trans
      (by linarith [hXq.trans hδG']))
    (((coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le s hp hw)).trans
      (by linarith [hXp.trans hδG']))
  rw [jetArr_sub] at hLG
  have hΔa : sobNorm r (cx (aArr q) - cx (aArr p)) ≤ Cl * 16 * D := by
    refine hL.1.trans ?_
    calc Cl * coordSum r bM (q - p) ≤ Cl * (16 * D) := mul_le_mul_of_nonneg_left hDcs hCl
      _ = Cl * 16 * D := by ring
  have hΔc : ∀ i j, sobNorm (r + 1) (cx (cArr q i j) - cx (cArr p i j)) ≤ Cl1 * 16 * D := by
    intro i j
    refine (hL1.2.1 i j).trans ?_
    calc Cl1 * coordSum (r + 1) bM (q - p) ≤ Cl1 * (16 * D) :=
          mul_le_mul_of_nonneg_left hDcs1 hCl1
      _ = Cl1 * 16 * D := by ring
  have hΔb : ∀ i, sobNorm (r + 1) (cx (bArr q i) - cx (bArr p i)) ≤ Cl1 * 16 * D := by
    intro i
    refine (hL1.2.2 i).trans ?_
    calc Cl1 * coordSum (r + 1) bM (q - p) ≤ Cl1 * (16 * D) :=
          mul_le_mul_of_nonneg_left hDcs1 hCl1
      _ = Cl1 * 16 * D := by ring
  -- the source bound
  have hGsrc : ∀ κ : Upper, sobNorm r (diffSource q p v w f g κ.1.1 κ.1.2) ≤ CGt * (D + F) := by
    intro κ
    rw [diffSource_eq q p v w f g κ.1.1 κ.1.2 haq_ne hap_ne]
    have t1 : sobNorm r (cx (comp (Garr q v) κ.1.1 κ.1.2) - cx (comp (Garr p w) κ.1.1 κ.1.2)) ≤
        CG * 80 * D := by
      have := hLG κ.1.1 κ.1.2
      calc _ = sobNorm r (cx (fun x => compensatorMap (jetArr q v x) κ.1.1 κ.1.2) -
              cx (fun x => compensatorMap (jetArr p w x) κ.1.1 κ.1.2)) := rfl
        _ ≤ CG * coordSum r bJ (jetArr (q - p) (v - w)) := this
        _ ≤ CG * (80 * D) := mul_le_mul_of_nonneg_left hDcJ hCG
        _ = CG * 80 * D := by ring
    have t2 : sobNorm r ((cx (aArr q) - cx (aArr p)) *
        cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2)) ≤ Ar * (Cl * 16) * KA * D := by
      refine (sobNorm_mul_le r (by omega) _ _).trans ?_
      have hAp : sobNorm r (cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2)) ≤ KA :=
        (sobNorm_mono (by omega) _).trans ((hacc N p w hp hw (hXp.trans hδA') _ _).trans
          (mul_le_of_le_one_right hKA hXp1))
      calc Ar * sobNorm r (cx (aArr q) - cx (aArr p)) *
            sobNorm r (cx (comp (harmonicWriterAcceleration p w) κ.1.1 κ.1.2))
          ≤ Ar * (Cl * 16 * D) * KA := by
            gcongr
            exact sobNorm_nonneg _ _
        _ = Ar * (Cl * 16) * KA * D := by ring
    have t3 : sobNorm r (cDiv (fun i j => cx (cArr q i j) - cx (cArr p i j))
        (cx (comp p κ.1.1 κ.1.2))) ≤ 9 * (Ar2 * (Cl1 * 16)) * D := by
      unfold cDiv
      have hij : ∀ i j, sobNorm r (Dm i ((cx (cArr q i j) - cx (cArr p i j)) *
          Dp j (cx (comp p κ.1.1 κ.1.2)))) ≤ Ar2 * (Cl1 * 16) * D := by
        intro i j
        refine (sobNorm_Dm_le r i _).trans ((sobNorm_mul_le (r + 1) (by omega) _ _).trans ?_)
        have hp2 : sobNorm (r + 1) (Dp j (cx (comp p κ.1.1 κ.1.2))) ≤ 1 :=
          (sobNorm_Dp_le (r + 1) j _).trans ((sobNorm_q_le s hp w _ _ (by omega)).trans hXp1)
        calc Ar2 * sobNorm (r + 1) (cx (cArr q i j) - cx (cArr p i j)) *
              sobNorm (r + 1) (Dp j (cx (comp p κ.1.1 κ.1.2))) ≤ Ar2 * (Cl1 * 16 * D) * 1 := by
              gcongr
              · exact sobNorm_nonneg _ _
              · exact hΔc i j
          _ = Ar2 * (Cl1 * 16) * D := by ring
      calc _ ≤ ∑ i, sobNorm r (∑ j, Dm i ((cx (cArr q i j) - cx (cArr p i j)) *
            Dp j (cx (comp p κ.1.1 κ.1.2)))) := sobNorm_sum_le _ _ _
        _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, Ar2 * (Cl1 * 16) * D :=
            sum_le_sum fun i _ => (sobNorm_sum_le _ _ _).trans (sum_le_sum fun j _ => hij i j)
        _ = 9 * (Ar2 * (Cl1 * 16)) * D := by simp; ring
    have t4 : sobNorm r (cSkew (fun i => cx (bArr q i) - cx (bArr p i))
        (cx (comp w κ.1.1 κ.1.2))) ≤ 3 * ((Ar + Ar2) * (Cl1 * 16)) * D := by
      unfold cSkew
      have hw1 : sobNorm (r + 1) (cx (comp w κ.1.1 κ.1.2)) ≤ 1 :=
        (sobNorm_v_le s p hw _ _ (by omega)).trans hXp1
      have hi : ∀ i, sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
          D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) ≤
          (Ar + Ar2) * (Cl1 * 16) * D := by
        intro i
        refine (sobNorm_add_le _ _ _).trans ?_
        have h1 : sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2))) ≤
            Ar * (Cl1 * 16 * D) * 1 := by
          refine (sobNorm_mul_le r (by omega) _ _).trans ?_
          gcongr
          · exact sobNorm_nonneg _ _
          · exact (sobNorm_mono (by omega) _).trans (hΔb i)
          · exact (sobNorm_D0_le r i _).trans hw1
        have h2 : sobNorm r (D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) ≤
            Ar2 * (Cl1 * 16 * D) * 1 := by
          refine (sobNorm_D0_le r i _).trans ((sobNorm_mul_le (r + 1) (by omega) _ _).trans ?_)
          gcongr
          · exact sobNorm_nonneg _ _
          · exact hΔb i
        calc _ ≤ Ar * (Cl1 * 16 * D) * 1 + Ar2 * (Cl1 * 16 * D) * 1 := add_le_add h1 h2
          _ = (Ar + Ar2) * (Cl1 * 16) * D := by ring
      calc _ ≤ ∑ i, sobNorm r ((cx (bArr q i) - cx (bArr p i)) * D0 i (cx (comp w κ.1.1 κ.1.2)) +
            D0 i ((cx (bArr q i) - cx (bArr p i)) * cx (comp w κ.1.1 κ.1.2))) :=
            sobNorm_sum_le _ _ _
        _ ≤ ∑ _i : Fin 3, (Ar + Ar2) * (Cl1 * 16) * D := sum_le_sum fun i _ => hi i
        _ = 3 * ((Ar + Ar2) * (Cl1 * 16)) * D := by simp; ring
    have t5 : sobNorm r (cx (aArr q) * (cx (comp f κ.1.1 κ.1.2) - cx (comp g κ.1.1 κ.1.2))) ≤
        (Ar + 1) * F := by
      refine (sobNorm_coef_mul_le r (by omega) _ _ 1 (by simp) ha_r).trans ?_
      rw [← cx_comp_sub]
      exact mul_le_mul_of_nonneg_left (sobNorm_le_Fnorm r (f - g) κ) (by positivity)
    calc _ ≤ CG * 80 * D + Ar * (Cl * 16) * KA * D + 9 * (Ar2 * (Cl1 * 16)) * D +
          3 * ((Ar + Ar2) * (Cl1 * 16)) * D + (Ar + 1) * F := by
          refine (sobNorm_add_le _ _ _).trans (add_le_add ?_ t5)
          refine (sobNorm_sub_le _ _ _).trans (add_le_add ?_ t4)
          refine (sobNorm_add_le _ _ _).trans (add_le_add ?_ t3)
          exact (sobNorm_sub_le _ _ _).trans (add_le_add t1 t2)
      _ ≤ CGt * (D + F) := by
          have h1 : 0 ≤ (CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
              3 * ((Ar + Ar2) * (Cl1 * 16))) * F := by positivity
          have h2 : 0 ≤ (Ar + 1) * D := by positivity
          have e : CGt * (D + F) = CG * 80 * D + Ar * (Cl * 16) * KA * D +
              9 * (Ar2 * (Cl1 * 16)) * D + 3 * ((Ar + Ar2) * (Cl1 * 16)) * D + (Ar + 1) * F +
              ((CG * 80 + Ar * (Cl * 16) * KA + 9 * (Ar2 * (Cl1 * 16)) +
                3 * ((Ar + Ar2) * (Cl1 * 16))) * F + (Ar + 1) * D) := by
            simp only [CGt]; ring
          linarith
  -- the acceleration difference in `H^{r-1}_h`
  have hδvt : ∀ κ : Upper, sobNorm (r - 1) (cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) ≤
      CV * (D + F) := by
    intro κ
    have e : cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2) =
        cx (fun x => (harmA (minkowski + q x))⁻¹) *
          (cx (aArr q) * cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2)) := by
      funext x
      simp only [Pi.mul_apply, cx_apply]
      rw [← mul_assoc, ← Complex.ofReal_mul, show (harmA (minkowski + q x))⁻¹ * aArr q x = 1 from
        inv_mul_cancel₀ (haq_ne x), Complex.ofReal_one, one_mul]
    have hrw : cx (aArr q) * cx (comp (dAcc q p v w f g) κ.1.1 κ.1.2) =
        ∑ i, ∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp (q - p) κ.1.1 κ.1.2))) -
        ∑ i, (cx (bArr q i) * D0 i (cx (comp (v - w) κ.1.1 κ.1.2)) +
          D0 i (cx (bArr q i) * cx (comp (v - w) κ.1.1 κ.1.2))) +
        diffSource q p v w f g κ.1.1 κ.1.2 := by
      unfold diffSource cDiv cSkew; abel
    rw [e, hrw]
    refine (sobNorm_coef_mul_le (r - 1) (by omega) _ _ 1 (by simp) hainv).trans ?_
    have hR := rhs_bound r hr (cx (comp (q - p) κ.1.1 κ.1.2)) (cx (comp (v - w) κ.1.1 κ.1.2))
      (diffSource q p v w f g κ.1.1 κ.1.2) (fun i j => cx (cArr q i j)) (fun i => cx (bArr q i))
      (fun i j => ((if i = j then 1 else 0 : ℝ) : ℂ)) (fun i j => by split_ifs <;> simp)
      (D + F) CGt
      (fun i j => (sobNorm_mono (by omega) _).trans (hc_r2 i j))
      (fun i => (sobNorm_mono (by omega) _).trans (hb_r2 i))
      (fun j => (sobNorm_Dp_le r j _).trans ((sobNorm_q_le r hqd (v - w) _ _ le_rfl).trans
        (by linarith)))
      ((sobNorm_v_le r (q - p) hvd _ _ le_rfl).trans (by linarith)) (hGsrc κ)
    calc (Ar1 + 1) * sobNorm (r - 1) _ ≤ (Ar1 + 1) *
          ((9 * (Ar + 1) + 3 * Ar1 + 3 * Ar + CGt) * (D + F)) := by gcongr
      _ = CV * (D + F) := by simp only [CV]; ring
  exact hδvt

/-- **The coefficient remainder of the force difference is Lipschitz**: for `r ≥ 2` there are
`δ > 0`, `C ≥ 0`, independent of the mesh and of the mark, such that on the chart
`‖(q, v)‖_{X^{r+1}_h}, ‖(p, w)‖_{X^{r+1}_h} ≤ δ`,
`‖(a(p)⁻¹ - a(q)⁻¹) h² B Λ_h² p‖_{r,h} ≤ C ‖(q - p, v - w)‖_{X^r_h}` componentwise. -/
theorem sobNorm_lawForceRem_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ)
      (q p v w : Grid N → MetricRec), IsMark (1 / 48) B → IsSymRec q → IsSymRec p →
      Xnorm (r + 1) q v ≤ δ → Xnorm (r + 1) p w ≤ δ → ∀ κ : Upper,
      PeriodicGridSobolev.sobNorm r (cx (comp (lawForceRem B q p) κ.1.1 κ.1.2)) ≤
        C * Xnorm r (q - p) (v - w) := by
  obtain ⟨pser, R, hpser⟩ := analyticAt_harmA_inv
  obtain ⟨δL, hδL, CL, hCL, hLip⟩ :=
    PeriodicGridSobolev.Moser.moser_lipschitz r hr bM hpser
  set Ar := PeriodicGridSobolev.Moser.algConst r
  have hAr := PeriodicGridSobolev.Moser.algConst_pos r
  refine ⟨min 1 (δL / 16), by positivity, Ar * (CL * 16) * 12, by positivity,
    fun N _ B q p v w hB hq hp hXq hXp κ => ?_⟩
  set D := Xnorm r (q - p) (v - w)
  have hD0 : 0 ≤ D := Xnorm_nonneg _ _ _
  have hcsq : PeriodicGridSobolev.Moser.coordSum r bM q ≤ 16 * Xnorm (r + 1) q v :=
    coordSum_bM_q_le (r + 1) hq v (by omega)
  have hcsp : PeriodicGridSobolev.Moser.coordSum r bM p ≤ 16 * Xnorm (r + 1) p w :=
    coordSum_bM_q_le (r + 1) hp w (by omega)
  have e : cx (comp (lawForceRem B q p) κ.1.1 κ.1.2) =
      (cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹)) *
        cx (comp (bTerm B p) κ.1.1 κ.1.2) := by
    funext x; simp [comp, cx, lawForceRem]
  rw [e]
  refine (PeriodicGridSobolev.Moser.sobNorm_mul_le r hr _ _).trans ?_
  have hL := hLip N p q (hcsp.trans (by linarith [hXp.trans (min_le_right _ _)]))
    (hcsq.trans (by linarith [hXq.trans (min_le_right _ _)]))
  have hL' : PeriodicGridSobolev.sobNorm r
      (cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹)) ≤ CL * 16 * D := by
    have e2 : cx (fun x => (aArr p x)⁻¹) - cx (fun x => (aArr q x)⁻¹) =
        fun x => (((harmA (minkowski + p x))⁻¹ - (harmA (minkowski + q x))⁻¹ : ℝ) : ℂ) := by
      funext x; simp [cx, aArr]
    rw [e2]
    refine hL.trans ?_
    have hc := coordSum_bM_q_le r (isSymRec_sub hp hq) (w - v) (show r ≤ r + 1 by omega)
    rw [lawDiff_Xnorm_sub_comm] at hc
    calc CL * PeriodicGridSobolev.Moser.coordSum r bM (p - q) ≤ CL * (16 * D) :=
          mul_le_mul_of_nonneg_left hc hCL
      _ = CL * 16 * D := by ring
  have hbT : PeriodicGridSobolev.sobNorm r (cx (comp (bTerm B p) κ.1.1 κ.1.2)) ≤ 12 := by
    have h1 := sobNorm_bTerm_le (r + 1) (by omega) hB hp w κ
    rw [show r + 1 - 1 = r by omega] at h1
    have h2 : Xnorm (r + 1) p w ≤ 1 := hXp.trans (min_le_left _ _)
    have h3 : 0 ≤ Xnorm (r + 1) p w := Xnorm_nonneg _ _ _
    linarith
  have := mul_le_mul (mul_le_mul_of_nonneg_left hL' hAr.le) hbT
    (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _) (by positivity)
  linarith

/-- **Lipschitz bound of the law-family acceleration one order down**: for `3 ≤ r`, `r + 1 ≤ s`
there are `δ > 0`, `K ≥ 0`, independent of the mesh and of the mark, such that for two symmetric
records in the top chart,
`‖V_{B,h}(q, v) - V_{B,h}(p, w)‖_{r-1,h} ≤ K ‖(q - p, v - w)‖_{X^r_h}` componentwise. -/
theorem lawAccel_diff_bound (s r : ℕ) (hr : 3 ≤ r) (hrs : r + 1 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ)
      (q p v w : Grid N → MetricRec), IsMark (1 / 48) B →
      IsSymRec q → IsSymRec p → IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ → Xnorm s p w ≤ δ →
      ∀ κ : Upper, PeriodicGridSobolev.sobNorm (r - 1)
        (cx (comp (lawAccel B q v - lawAccel B p w) κ.1.1 κ.1.2)) ≤
        K * Xnorm r (q - p) (v - w) := by
  obtain ⟨δ1, hδ1, K1, hK1, hd⟩ := dAcc_bound s r hr hrs
  obtain ⟨δ2, hδ2, C2, hC2, hrem⟩ := sobNorm_lawForceRem_le r (by omega)
  obtain ⟨δa, hδa, Ca, hCa, hma⟩ := moser_coefficients (r - 1) (by omega)
  set A1 := PeriodicGridSobolev.Moser.algConst (r - 1)
  have hA1 := PeriodicGridSobolev.Moser.algConst_pos (r - 1)
  refine ⟨min δ1 (min δ2 (min (δa / 16) (1 / (16 * (Ca + 1))))), by positivity,
    K1 + (A1 + 1) * 12 + C2, by positivity, fun N _ B q p v w hB hq hp hv hw hXq hXp κ => ?_⟩
  set D := Xnorm r (q - p) (v - w)
  have hD0 : 0 ≤ D := Xnorm_nonneg _ _ _
  have hqd := isSymRec_sub hq hp
  have hvd := isSymRec_sub hv hw
  have hXq2 : Xnorm (r + 1) q v ≤ δ2 :=
    (lawDiff_Xnorm_mono hrs q v).trans (hXq.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hXp2 : Xnorm (r + 1) p w ≤ δ2 :=
    (lawDiff_Xnorm_mono hrs p w).trans (hXp.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcsq : PeriodicGridSobolev.Moser.coordSum (r - 1) bM q ≤ 16 * Xnorm s q v :=
    coordSum_bM_q_le s hq v (by omega)
  have hainv : PeriodicGridSobolev.sobNorm (r - 1)
      (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := by
    have hM := hma N q (hcsq.trans (by
      linarith [hXq.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))]))
    refine hM.2.1.trans ?_
    have h1 : Xnorm s q v ≤ 1 / (16 * (Ca + 1)) :=
      hXq.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    have := Xnorm_nonneg s q v
    calc Ca * PeriodicGridSobolev.Moser.coordSum (r - 1) bM q ≤ Ca * (16 * Xnorm s q v) :=
          mul_le_mul_of_nonneg_left hcsq hCa
      _ ≤ 1 := by nlinarith
  have e : lawAccel B q v - lawAccel B p w =
      dAcc q p v w 0 0 + (bForceAt (aArr q) B (q - p) + lawForceRem B q p) := by
    rw [← lawForce_sub]
    funext x μ ν
    simp only [lawAccel, dAcc, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    ring
  rw [e, cx_comp_add, cx_comp_add]
  refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
  have t1 : PeriodicGridSobolev.sobNorm (r - 1) (cx (comp (dAcc q p v w 0 0) κ.1.1 κ.1.2)) ≤
      K1 * D := by
    have := hd N q p v w 0 0 hq hp hv hw (hXq.trans (min_le_left _ _))
      (hXp.trans (min_le_left _ _)) κ
    rwa [sub_self, lawDiff_Fnorm_zero, add_zero] at this
  have t2 : PeriodicGridSobolev.sobNorm (r - 1)
      (cx (comp (bForceAt (aArr q) B (q - p)) κ.1.1 κ.1.2)) ≤ (A1 + 1) * (12 * D) := by
    have e2 : cx (comp (bForceAt (aArr q) B (q - p)) κ.1.1 κ.1.2) =
        -(cx (fun x => (aArr q x)⁻¹) * cx (comp (bTerm B (q - p)) κ.1.1 κ.1.2)) := by
      funext x; simp [comp, cx, bForceAt]
    rw [e2, PeriodicGridSobolev.Moser.sobNorm_neg]
    refine (sobNorm_coef_mul_le (r - 1) (by omega) _ _ 1 (by simp) hainv).trans ?_
    have h3 := sobNorm_bTerm_le r (by omega) hB hqd (v - w) κ
    exact mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
  have t3 : PeriodicGridSobolev.sobNorm (r - 1) (cx (comp (lawForceRem B q p) κ.1.1 κ.1.2)) ≤
      C2 * D :=
    (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans
      (hrem N B q p v w hB hq hp hXq2 hXp2 κ)
  have t23 := (PeriodicGridSobolev.Moser.sobNorm_add_le (r - 1) _ _).trans (add_le_add t2 t3)
  nlinarith

end

end RenewalGeometry.OpenWriterLifespan
