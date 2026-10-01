/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.IteratedDerivBounds
import RenewalGeometry.Analysis.TwoPointHermiteInterpolation

/-!
# The complete Taylor–Hermite residual of a second-order writer with inverse-mesh bounds
  (`lem:supp-open-hermite-residual`, `eq:supp-open-local-taylor`,
  `eq:supp-open-taylor-remainder`, `eq:supp-open-hermite-correction`,
  `eq:supp-open-hermite-local-defect`; emergent-spacetime manuscript)

Abstract setting (`Writer`): a position space `Eq` and a velocity space `Ev` (real Banach
spaces), mutually inverse continuous linear maps `ι : Eq → Ev` (norm `≤ 1`) and
`u : Ev → Eq` (norm `≤ A h⁻¹`; for the grid writer these are the identity of arrays between
`H^{s+1}_h` and `H^s_h`), an acceleration `V : Eq × Ev → Ev` and the field
`𝓕(q, v) = (u v, V(q, v))`.  We assume the inverse-mesh bounds of
`eq:supp-open-local-vector-bounds`: `𝓕` is smooth on a ball `‖X‖ < δ` with
`‖D^j 𝓕‖ ≤ A h⁻¹` (`j ≤ 9`) and `‖𝓕(X)‖ ≤ A h⁻¹ ‖X‖`.

* `Writer.qj j X = (J_j X)_q`: the position jets of the writer at the source (`J_j` the vector
  jets of `IteratedDerivBounds.vfJet`); `taylorC X` the degree-seven Taylor coefficients
  `q⁽ʲ⁾(0)/j!` and `T_X = polyCurve (taylorC X)` (`eq:supp-open-local-taylor`);
  `endpoint X τ = X₁ = (T_X(τ), T_X'(τ))`.
* `hermiteC X τ`: the endpoint-corrected polynomial `Q_X = T_X + τ²δ₂H₂(t/τ) + τ³δ₃H₃(t/τ)`
  with `δ₂ = V(X₁) − T_X''(τ)`, `δ₃ = J(X₁) − T_X'''(τ)` (`eq:supp-open-hermite-correction`);
  `hermiteC_jets`: its value, velocity, acceleration and jerk are `(q, v, V(X), J(X))` at `0`
  and `(X₁, V(X₁), J(X₁))` at `τ`; `hermiteC_unique`: it is the only polynomial of degree
  `≤ 7` with these jets.
* `exists_local_solution`: the exact local solution from the source (Picard–Lindelöf), on a
  time interval of length `h/(2A)`, inside the ball of radius `ε` around the source.
* `hermite_residual` (**`lem:supp-open-hermite-residual`**): for `c₋h² ≤ τ ≤ c₊h²`, `h ≤ h₀`
  and `‖X‖ ≤ ε ≤ δ/4`, the polynomial `Q_X` stays in the chart and its actual defect
  `f_X = Q_X'' − V(Q_X, Q_X')` satisfies `‖f_X(t)‖ ≤ C ε h⁵` and `‖∂_t f_X(t)‖ ≤ C ε h³` on the
  whole interval `[0, τ]`, with `h₀, C` depending only on `A, c₋, c₊`.
-/

open Set Metric Filter Topology Function
open scoped ContDiff BigOperators NNReal

namespace RenewalGeometry.TaylorHermiteResidual

open IteratedDerivBounds TwoPointHermite

noncomputable section

/-! ### Polynomial curves at the origin -/

section Poly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyCurveDeriv_at_zero {n : ℕ} (c : Fin n → E) (j : Fin n) :
    polyCurveDeriv j c 0 = ((j : ℕ).factorial : ℝ) • c j := by
  unfold polyCurveDeriv
  rw [Finset.sum_eq_single j]
  · simp [Nat.descFactorial_self]
  · intro i _ hij
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hij) with h | h
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp
    · have : (i : ℕ) - j ≠ 0 := by omega
      simp [zero_pow this]
  · simp

end Poly

/-! ### Second-order writers -/

/-- **A second-order writer**: position and velocity spaces with mutually inverse
identifications `ι`, `u` and an acceleration `V`; the field is `𝓕(q, v) = (u v, V(q, v))`. -/
structure Writer (Eq Ev : Type*) [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
    [NormedAddCommGroup Ev] [NormedSpace ℝ Ev] where
  ι : Eq →L[ℝ] Ev
  u : Ev →L[ℝ] Eq
  V : Eq × Ev → Ev
  ι_u : ∀ y, ι (u y) = y
  u_ι : ∀ x, u (ι x) = x

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [NormedAddCommGroup Ev]
  [NormedSpace ℝ Ev] (W : Writer Eq Ev)

/-- The differential writer `𝓕(q, v) = (u v, V(q, v))`. -/
def field (X : Eq × Ev) : Eq × Ev := (W.u X.2, W.V X)

/-- The position jets `(J_j X)_q` of the writer. -/
def qj (j : ℕ) (X : Eq × Ev) : Eq := (vfJet W.field j X).1

/-- Degree-seven Taylor coefficients `(J_i X)_q / i!` (`eq:supp-open-local-taylor`). -/
def taylorC (X : Eq × Ev) : Fin 8 → Eq := fun i => (((i : ℕ).factorial : ℝ))⁻¹ • W.qj i X

/-- The phase point `(P(t), P'(t))` of a polynomial position curve. -/
def phase (c : Fin 8 → Eq) (t : ℝ) : Eq × Ev :=
  (polyCurve c t, W.ι (polyCurveDeriv 1 c t))

/-- The actual defect `P'' − V(P, P')` of a polynomial position curve. -/
def defect (c : Fin 8 → Eq) (t : ℝ) : Ev :=
  W.ι (polyCurveDeriv 2 c t) - W.V (W.phase c t)

/-- The Taylor endpoint `X₁ = (T_X(τ), T_X'(τ))`. -/
def endpoint (X : Eq × Ev) (τ : ℝ) : Eq × Ev := W.phase (W.taylorC X) τ

/-- `δ₂ = V(X₁) − T_X''(τ)` (as a position-space element). -/
def corr2 (X : Eq × Ev) (τ : ℝ) : Eq :=
  W.qj 2 (W.endpoint X τ) - polyCurveDeriv 2 (W.taylorC X) τ

/-- `δ₃ = J(X₁) − T_X'''(τ)`. -/
def corr3 (X : Eq × Ev) (τ : ℝ) : Eq :=
  W.qj 3 (W.endpoint X τ) - polyCurveDeriv 3 (W.taylorC X) τ

/-- **The endpoint-corrected polynomial** `Q_X = T_X + τ²δ₂H₂(t/τ) + τ³δ₃H₃(t/τ)`. -/
def hermiteC (X : Eq × Ev) (τ : ℝ) : Fin 8 → Eq :=
  W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)

theorem qj_zero (X : Eq × Ev) : W.qj 0 X = X.1 := rfl

theorem qj_one (X : Eq × Ev) : W.qj 1 X = W.u X.2 := by
  simp [qj, vfJet_one, field]

theorem polyCurveDeriv_taylorC_zero (X : Eq × Ev) (j : Fin 8) :
    polyCurveDeriv j (W.taylorC X) 0 = W.qj j X := by
  rw [polyCurveDeriv_at_zero, taylorC, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

theorem polyCurveDeriv_add {n : ℕ} (j : ℕ) (c c' : Fin n → Eq) (t : ℝ) :
    polyCurveDeriv j (c + c') t = polyCurveDeriv j c t + polyCurveDeriv j c' t := by
  simp only [polyCurveDeriv, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- **The jets of `Q_X`** (definition of `Q_X` after `eq:supp-open-local-taylor`): value,
velocity, acceleration and jerk are `(J_i X)_q` at `0` and `(J_i X₁)_q` at `τ`, `i ≤ 3`; i.e.
`(q, v, V(X), J(X))` and `(X₁, V(X₁), J(X₁))`. -/
theorem hermiteC_jets (X : Eq × Ev) {τ : ℝ} (hτ : τ ≠ 0) (i : Fin 4) :
    polyCurveDeriv i (W.hermiteC X τ) 0 = W.qj i X ∧
      polyCurveDeriv i (W.hermiteC X τ) τ = W.qj i (W.endpoint X τ) := by
  obtain ⟨h0, h10, h11, h12, h13⟩ := hermiteCorrection_jets hτ (W.corr2 X τ) (W.corr3 X τ)
  simp only [iteratedDeriv_polyCurve] at h0 h11 h12 h13
  rw [← polyCurveDeriv_zero] at h10
  refine ⟨?_, ?_⟩
  · rw [hermiteC, polyCurveDeriv_add, h0 i, add_zero]
    exact W.polyCurveDeriv_taylorC_zero X ⟨i, by omega⟩
  · rw [hermiteC, polyCurveDeriv_add]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.val_zero]
      rw [h10, add_zero, qj_zero, polyCurveDeriv_zero]; rfl
    · simp only [Fin.mk_one, Fin.val_one]
      rw [h11, add_zero, qj_one]
      simp [endpoint, phase, W.u_ι]
    · simp only [Fin.reduceFinMk, Fin.val_two]
      rw [h12, corr2]; abel
    · show polyCurveDeriv 3 (W.taylorC X) τ + polyCurveDeriv 3 (hermiteCorrection τ (W.corr2 X τ)
        (W.corr3 X τ)) τ = W.qj 3 (W.endpoint X τ)
      rw [h13, corr3]; abel

/-- **Uniqueness of `Q_X`**: a polynomial curve of degree `≤ 7` with the same jets through order
three at `0` and `τ` is `Q_X`. -/
theorem hermiteC_unique (X : Eq × Ev) {τ : ℝ} (hτ : τ ≠ 0) (c : Fin 8 → Eq)
    (h0 : ∀ i : Fin 4, polyCurveDeriv i c 0 = W.qj i X)
    (hτc : ∀ i : Fin 4, polyCurveDeriv i c τ = W.qj i (W.endpoint X τ)) :
    c = W.hermiteC X τ := by
  have hs : scaleCoeffs τ c = scaleCoeffs τ (W.hermiteC X τ) := by
    refine eq_of_jets_eq (k := 3) (funext fun r => ?_)
    simp only [jets]
    rw [polyCurveDeriv_scaleCoeffs, polyCurveDeriv_scaleCoeffs]
    congr 1
    obtain ⟨e, i⟩ := r
    fin_cases e
    · simp only [Fin.zero_eta, Fin.val_zero, Nat.cast_zero, mul_zero]
      rw [h0 i, (W.hermiteC_jets X hτ i).1]
    · simp only [Fin.mk_one, Fin.val_one, Nat.cast_one, mul_one]
      rw [hτc i, (W.hermiteC_jets X hτ i).2]
  funext i
  have := congrFun hs i
  simp only [scaleCoeffs] at this
  exact smul_right_injective Eq (pow_ne_zero _ hτ) this

end Writer

/-! ### Exact local solutions -/

section Solution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

open ODE in
/-- **Picard–Lindelöf with containment**: a field bounded by `L` and `K`-Lipschitz on
`closedBall X a` has a solution through `X` on `(-σ, σ)` staying in that ball when `L σ ≤ a`. -/
theorem exists_solution_mem_closedBall {F : E → E} {X : E} {a L K : ℝ≥0} {σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ x ∈ closedBall X a, ‖F x‖ ≤ L) (hl : LipschitzOnWith K F (closedBall X a))
    (hm : (L : ℝ) * σ ≤ a) :
    ∃ Y : ℝ → E, Y 0 = X ∧ ∀ t ∈ Ioo (-σ) σ, HasDerivAt Y (F (Y t)) t ∧ Y t ∈ closedBall X a := by
  have ht0 : (0 : ℝ) ∈ Icc (-σ) σ := ⟨by linarith, hσ⟩
  have hf : IsPicardLindelof (fun _ => F) (tmin := -σ) (tmax := σ) ⟨0, ht0⟩ X a 0 L K := by
    refine IsPicardLindelof.of_time_independent hb hl ?_
    simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_zero]
    exact hm
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf (mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, fun t ht => ⟨?_, α.compProj_mem_closedBall hf.mul_max_le⟩⟩
  · show α.compProj ((⟨0, ht0⟩ : Icc (-σ) σ) : ℝ) = X
    rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · have htI : t ∈ Icc (-σ) σ := Ioo_subset_Icc_self ht
    have hd : HasDerivWithinAt α.compProj (F (α.compProj t)) (Icc (-σ) σ) t := by
      apply hasDerivWithinAt_picard_Icc ht0 hf.continuousOn_uncurry
        α.continuous_compProj.continuousOn (fun _ _ ↦ α.compProj_mem_closedBall hf.mul_max_le)
        X htI |>.congr_of_mem _ htI
      intro t' ht'
      nth_rw 1 [← hα]
      rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
/-- Solutions of a smooth autonomous field are smooth. -/
theorem contDiffOn_of_solution {F : E → E} {U : Set E} (hF : ContDiffOn ℝ ∞ F U) {S : Set ℝ}
    (hS : IsOpen S) {Y : ℝ → E} (hYU : ∀ t ∈ S, Y t ∈ U)
    (hY : ∀ t ∈ S, HasDerivAt Y (F (Y t)) t) : ContDiffOn ℝ ∞ Y S := by
  have hmaps : MapsTo Y S U := fun t ht => hYU t ht
  have key : ∀ n : ℕ, ContDiffOn ℝ n Y S := by
    intro n
    induction n with
    | zero =>
      exact contDiffOn_zero.mpr fun t ht => (hY t ht).continuousAt.continuousWithinAt
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_deriv_of_isOpen hS]
      refine ⟨fun t ht => (hY t ht).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
      · exact absurd h (by simp)
      · have h1 : ContDiffOn ℝ n (fun t => F (Y t)) S :=
          (hF.of_le (by exact_mod_cast le_top)).comp ih hmaps
        exact h1.congr fun t ht => (hY t ht).deriv
  exact contDiffOn_infty.mpr key

omit [CompleteSpace E] in
/-- Local Taylor bound on `[0, t]` inside an open set of smoothness. -/
theorem norm_sub_taylor_le {g : ℝ → E} {S : Set ℝ} (hS : IsOpen S) (hg : ContDiffOn ℝ ∞ g S)
    {t : ℝ} (ht : 0 ≤ t) (hIcc : Icc 0 t ⊆ S) (n : ℕ) {C : ℝ}
    (hC : ∀ y ∈ Icc 0 t, ‖iteratedDeriv (n + 1) g y‖ ≤ C) :
    ‖g t - ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k g 0‖ ≤
      C * t ^ (n + 1) / n.factorial := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Finset.sum_range_succ']
    simp
  have hU : UniqueDiffOn ℝ (Icc 0 t) := uniqueDiffOn_Icc hpos
  have hgI : ContDiffOn ℝ (n + 1) g (Icc 0 t) := (hg.of_le (by exact_mod_cast le_top)).mono hIcc
  have hca : ∀ y ∈ Icc 0 t, ContDiffAt ℝ (n + 1) g y := fun y hy =>
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt (hS.mem_nhds (hIcc hy)))
  have h := taylor_mean_remainder_bound (f := g) (n := n) (C := C) ht hgI (right_mem_Icc.2 ht)
    (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hU (hca y hy) hy]
      exact hC y hy)
  rw [taylor_within_apply] at h
  have e : ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (t - 0) ^ k) •
      iteratedDerivWithin k g (Icc 0 t) 0 =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * t ^ k) • iteratedDeriv k g 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [sub_zero, iteratedDerivWithin_eq_iteratedDeriv hU _ (left_mem_Icc.2 ht)]
    exact (hca 0 (left_mem_Icc.2 ht)).of_le (by
      have := Finset.mem_range.mp hk
      exact_mod_cast this.le)
  rw [e, sub_zero] at h
  exact h

end Solution

/-! ### Inverse-mesh bounds and the analytic core -/

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [NormedAddCommGroup Ev]
  [NormedSpace ℝ Ev] (W : Writer Eq Ev)

/-- **Inverse-mesh bounds** (`eq:supp-open-local-vector-bounds`) for a writer on the ball
`‖X‖ < δ`, mesh `h` and constant `A`. -/
structure Bounds (h A δ : ℝ) : Prop where
  h_pos : 0 < h
  h_le_one : h ≤ 1
  one_le_A : 1 ≤ A
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  norm_ι : ‖W.ι‖ ≤ 1
  norm_u : ‖W.u‖ ≤ A * h⁻¹
  deriv : DerivBound W.field (ball 0 δ) 9 (A * h⁻¹)
  field_le : ∀ Z ∈ ball (0 : Eq × Ev) δ, ‖W.field Z‖ ≤ A * h⁻¹ * ‖Z‖

/-- The velocity of the phase curve, `(P'(t), P''(t))`. -/
def phaseVel (c : Fin 8 → Eq) (t : ℝ) : Eq × Ev :=
  (polyCurveDeriv 1 c t, W.ι (polyCurveDeriv 2 c t))

/-- The time derivative of the defect, `P''' − D V(P, P')[(P', P'')]`. -/
def defectDeriv (c : Fin 8 → Eq) (t : ℝ) : Ev :=
  W.ι (polyCurveDeriv 3 c t) - (fderiv ℝ W.field (W.phase c t) (W.phaseVel c t)).2

theorem V_eq (Z : Eq × Ev) : W.V Z = (W.field Z).2 := rfl

theorem hasDerivAt_phase (c : Fin 8 → Eq) (t : ℝ) :
    HasDerivAt (W.phase c) (W.phaseVel c t) t := by
  have h0 := hasDerivAt_polyCurveDeriv 0 c t
  rw [polyCurveDeriv_zero] at h0
  have h1 := W.ι.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_polyCurveDeriv 1 c t)
  exact h0.prodMk h1

theorem hasDerivAt_defect {c : Fin 8 → Eq} {t δ : ℝ} (hF : ContDiffOn ℝ ∞ W.field (ball 0 δ))
    (ht : W.phase c t ∈ ball 0 δ) :
    HasDerivAt (W.defect c) (W.defectDeriv c t) t := by
  have hd : DifferentiableAt ℝ W.field (W.phase c t) :=
    (hF.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)
  have h1 := W.ι.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_polyCurveDeriv 2 c t)
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t (W.hasDerivAt_phase c t)
  have h3 := (ContinuousLinearMap.snd ℝ Eq Ev).hasFDerivAt.comp_hasDerivAt t h2
  exact h1.sub h3

theorem ι_polyCurveDeriv {n : ℕ} (j : ℕ) (c : Fin n → Eq) (t : ℝ) :
    W.ι (polyCurveDeriv j c t) = polyCurveDeriv j (fun i => W.ι (c i)) t := by
  simp only [polyCurveDeriv, map_sum, map_smul]

end Writer

/-! ### The analytic core -/

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [CompleteSpace Eq]
  [NormedAddCommGroup Ev] [NormedSpace ℝ Ev] [CompleteSpace Ev] {W : Writer Eq Ev}
  {h A δ : ℝ}

theorem Bounds.M_pos (hB : W.Bounds h A δ) : 0 < A * h⁻¹ :=
  mul_pos (by linarith [hB.one_le_A]) (inv_pos.mpr hB.h_pos)

theorem Bounds.lip_field (hB : W.Bounds h A δ) {a b : Eq × Ev} (ha : a ∈ ball 0 δ)
    (hb : b ∈ ball 0 δ) : ‖W.field a - W.field b‖ ≤ A * h⁻¹ * ‖a - b‖ :=
  (convex_ball (0 : Eq × Ev) δ).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hB.deriv.contDiffAt isOpen_ball hz).differentiableAt (by simp))
    (fun z hz => hB.deriv.norm_fderiv_le (by norm_num) hz) hb ha

theorem Bounds.lip_fderiv (hB : W.Bounds h A δ) {a b : Eq × Ev} (ha : a ∈ ball 0 δ)
    (hb : b ∈ ball 0 δ) :
    ‖fderiv ℝ W.field a - fderiv ℝ W.field b‖ ≤ A * h⁻¹ * ‖a - b‖ := by
  have hd : DerivBound (fderiv ℝ W.field) (ball 0 δ) 8 (A * h⁻¹) := hB.deriv.fderiv isOpen_ball
  exact (convex_ball (0 : Eq × Ev) δ).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hd.contDiffAt isOpen_ball hz).differentiableAt (by simp))
    (fun z hz => hd.norm_fderiv_le (by norm_num) hz) hb ha

theorem Bounds.norm_fderiv (hB : W.Bounds h A δ) {a : Eq × Ev} (ha : a ∈ ball 0 δ) :
    ‖fderiv ℝ W.field a‖ ≤ A * h⁻¹ :=
  hB.deriv.norm_fderiv_le (by norm_num) ha

/-- The exact local solution from a source of size `≤ ε`, on `(-h/(2A), h/(2A))`. -/
theorem Bounds.exists_exact (hB : W.Bounds h A δ) {X : Eq × Ev} {ε : ℝ} (hX : ‖X‖ ≤ ε)
    (hεδ : 4 * ε ≤ δ) :
    ∃ Y : ℝ → Eq × Ev, Y 0 = X ∧ ∀ t ∈ Ioo (-(h / (2 * A))) (h / (2 * A)),
      HasDerivAt Y (W.field (Y t)) t ∧ ‖Y t - X‖ ≤ ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hX
  have hA := hB.one_le_A
  have hh := hB.h_pos
  have hM := hB.M_pos
  have hsub : closedBall X ε ⊆ ball (0 : Eq × Ev) δ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball_zero_iff]
    have : ‖z‖ ≤ ‖X‖ + ‖z - X‖ := by
      calc ‖z‖ = ‖X + (z - X)‖ := by congr 1; abel
        _ ≤ ‖X‖ + ‖z - X‖ := norm_add_le _ _
    linarith [hB.δ_pos]
  have hzle : ∀ z ∈ closedBall X ε, ‖z‖ ≤ 2 * ε := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖X + (z - X)‖ := by congr 1; abel
      _ ≤ ‖X‖ + ‖z - X‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith
  set a : ℝ≥0 := ⟨ε, hε0⟩
  set L : ℝ≥0 := ⟨A * h⁻¹ * (2 * ε), by positivity⟩
  set K : ℝ≥0 := ⟨A * h⁻¹, hM.le⟩
  have hb : ∀ z ∈ closedBall X a, ‖W.field z‖ ≤ L := by
    intro z hz
    show ‖W.field z‖ ≤ A * h⁻¹ * (2 * ε)
    exact (hB.field_le z (hsub hz)).trans (mul_le_mul_of_nonneg_left (hzle z hz) hM.le)
  have hl : LipschitzOnWith K W.field (closedBall X a) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hB.deriv.contDiffAt isOpen_ball (hsub hz)).differentiableAt (by simp))
      (fun z hz => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact hB.norm_fderiv (hsub hz)) (convex_closedBall X ε)
  have hσ : 0 ≤ h / (2 * A) := by positivity
  have hm : (L : ℝ) * (h / (2 * A)) ≤ a := by
    show A * h⁻¹ * (2 * ε) * (h / (2 * A)) ≤ ε
    have : A * h⁻¹ * (2 * ε) * (h / (2 * A)) = ε := by field_simp
    rw [this]
  obtain ⟨Y, hY0, hY⟩ := exists_solution_mem_closedBall hσ hb hl hm
  refine ⟨Y, hY0, fun t ht => ⟨(hY t ht).1, ?_⟩⟩
  have := (hY t ht).2
  rwa [mem_closedBall, dist_eq_norm] at this

/-- `h^{-7} τ^m ≤ c^8 h^n` for `τ ≤ c h²`, `2m = n + 7`, `m ≤ 8`. -/
theorem pow_scale {h c τ : ℝ} (hh : 0 < h) (hc : 1 ≤ c) (hτ0 : 0 ≤ τ) (hτ : τ ≤ c * h ^ 2)
    {m n : ℕ} (hm : m ≤ 8) (hmn : 2 * m = n + 7) :
    h⁻¹ ^ 7 * τ ^ m ≤ c ^ 8 * h ^ n := by
  have h1 : τ ^ m ≤ (c * h ^ 2) ^ m := pow_le_pow_left₀ hτ0 hτ m
  have h2 : (c * h ^ 2) ^ m = c ^ m * h ^ (2 * m) := by rw [mul_pow, ← pow_mul]
  have h3 : c ^ m ≤ c ^ 8 := pow_le_pow_right₀ hc hm
  have h4 : h⁻¹ ^ 7 * h ^ (2 * m) = h ^ n := by
    rw [hmn, pow_add, ← mul_assoc, mul_comm (h⁻¹ ^ 7), mul_assoc, ← mul_pow, inv_mul_cancel₀ hh.ne',
      one_pow, mul_one]
  calc h⁻¹ ^ 7 * τ ^ m ≤ h⁻¹ ^ 7 * (c ^ 8 * h ^ (2 * m)) := by
        gcongr
        calc τ ^ m ≤ c ^ m * h ^ (2 * m) := h1.trans h2.le
          _ ≤ c ^ 8 * h ^ (2 * m) := by gcongr
    _ = c ^ 8 * h ^ n := by rw [mul_left_comm, h4]

/-- The constant `B₈ = 2 · 2^{54} A⁷` bounding `‖q⁽⁸⁾‖ ≤ B₈ ε h^{-7}` along the exact solution. -/
def B8 (A : ℝ) : ℝ := 2 * 2 ^ 54 * A ^ 7

set_option maxHeartbeats 4000000 in
/-- **Taylor estimates along the exact solution and the defect of `T_X`.**  For a source with
`‖X‖ ≤ ε ≤ δ/4`, `0 < τ ≤ c h²` with `τ < h/(2A)`, and `t ∈ [0, τ]`, with
`E₀ = B₈ c⁸`, `Ph = A E₀`: the Taylor phase stays within `Ph ε h⁷` of the exact solution (so in
the ball of radius `2ε + Ph ε h⁷`), the defect of `T_X` is `≤ (E₀ + A Ph) ε h⁵`, its time
derivative is `≤ (E₀ + (2A² + A) Ph) ε h³`, and the phase velocity is `≤ (2A + Ph) h^{-1} ε`. -/
theorem Bounds.taylor_defect (hB : W.Bounds h A δ) {X : Eq × Ev} {ε τ c : ℝ} (hX : ‖X‖ ≤ ε)
    (hεδ : 4 * ε ≤ δ) (hc : 1 ≤ c) (hτ0 : 0 < τ) (hτc : τ ≤ c * h ^ 2) (hτσ : τ < h / (2 * A))
    (hsmall : A * (B8 A * c ^ 8) * h ^ 7 ≤ 1 / 2) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖W.phase (W.taylorC X) t‖ ≤ 2 * ε + A * (B8 A * c ^ 8) * ε * h ^ 7 ∧
    ‖W.defect (W.taylorC X) t‖ ≤ (B8 A * c ^ 8 + A * (A * (B8 A * c ^ 8))) * ε * h ^ 5 ∧
    ‖W.defectDeriv (W.taylorC X) t‖ ≤
      (B8 A * c ^ 8 + (2 * A ^ 2 + A) * (A * (B8 A * c ^ 8))) * ε * h ^ 3 ∧
    ‖W.phaseVel (W.taylorC X) t‖ ≤ (2 * A + A * (B8 A * c ^ 8)) * h⁻¹ * ε := by
  -- constants
  have hA := hB.one_le_A
  have hh := hB.h_pos
  have hh1 := hB.h_le_one
  have hM := hB.M_pos
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hX
  have hε1 : ε ≤ 1 := by linarith [hB.δ_le_one]
  set E0 := B8 A * c ^ 8 with hE0
  set Ph := A * E0 with hPh
  have hB8 : 0 ≤ B8 A := by unfold B8; positivity
  have hE00 : 0 ≤ E0 := by positivity
  have hPh0 : 0 ≤ Ph := by positivity
  set F := W.field
  set U : Set (Eq × Ev) := ball 0 δ
  have hU : IsOpen U := isOpen_ball
  have hFc : ContDiffOn ℝ ∞ F U := hB.deriv.contDiffOn
  -- the exact solution
  obtain ⟨Y, hY0, hY⟩ := hB.exists_exact hX hεδ
  set σ := h / (2 * A)
  set S := Ioo (-σ) σ
  have hS : IsOpen S := isOpen_Ioo
  have hYn : ∀ s ∈ S, ‖Y s‖ ≤ 2 * ε := by
    intro s hs
    calc ‖Y s‖ = ‖X + (Y s - X)‖ := by congr 1; abel
      _ ≤ ‖X‖ + ‖Y s - X‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith [(hY s hs).2]
  have hYU : ∀ s ∈ S, Y s ∈ U := fun s hs => mem_ball_zero_iff.mpr (by
    linarith [hYn s hs, hB.δ_pos])
  have hYd : ∀ s ∈ S, HasDerivAt Y (F (Y s)) s := fun s hs => (hY s hs).1
  have hσ : 0 < σ := by positivity
  have h0S : (0 : ℝ) ∈ S := ⟨by linarith, hσ⟩
  have hIcc : Icc 0 τ ⊆ S := fun s hs => ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hτσ⟩
  have htS : t ∈ S := hIcc ht
  have ht0 : 0 ≤ t := ht.1
  -- jets along the solution
  set Pq : Eq × Ev →L[ℝ] Ev := W.ι.comp (ContinuousLinearMap.fst ℝ Eq Ev)
  have hPQ : ∀ Z ∈ U, Pq (F Z) = (ContinuousLinearMap.snd ℝ Eq Ev) Z := by
    intro Z _; show W.ι (W.u Z.2) = Z.2; exact W.ι_u _
  have hproj : ∀ j, ∀ Z ∈ U, W.ι (vfJet F (j + 1) Z).1 = (vfJet F j Z).2 :=
    fun j Z hZ => vfJet_proj hFc hU Pq (ContinuousLinearMap.snd ℝ Eq Ev) hPQ j Z hZ
  have hjet : ∀ j k, ∀ s ∈ S, iteratedDeriv k (fun τ => Pq (vfJet F j (Y τ))) s =
      Pq (vfJet F (j + k) (Y s)) :=
    fun j k s hs => iteratedDeriv_clm_vfJet_eq hFc hU hS hYU hYd Pq j k s hs
  have hjetq : ∀ k, iteratedDeriv k (fun τ => (vfJet F 0 (Y τ)).1) 0 = W.qj k X := by
    intro k
    have := iteratedDeriv_clm_vfJet_eq hFc hU hS hYU hYd (ContinuousLinearMap.fst ℝ Eq Ev) 0 k
      0 h0S
    simpa [hY0, qj] using this
  -- the bound on the eighth jet
  have hp8 : ∀ s ∈ S, ‖(vfJet F 7 (Y s)).2‖ ≤ B8 A * ε * h⁻¹ ^ 7 := by
    intro s hs
    have h1 := vfJet_norm_le hB.deriv hU hM.le (hYU s hs) 7 (by norm_num) (by norm_num)
    have h2 := hB.field_le (Y s) (hYU s hs)
    calc ‖(vfJet F 7 (Y s)).2‖ ≤ ‖vfJet F 7 (Y s)‖ := norm_snd_le _
      _ ≤ (2 ^ 9 * (A * h⁻¹)) ^ (7 - 1) * ‖F (Y s)‖ := h1
      _ ≤ (2 ^ 9 * (A * h⁻¹)) ^ 6 * (A * h⁻¹ * (2 * ε)) := by
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left (hYn s hs) hM.le
      _ = B8 A * ε * h⁻¹ ^ 7 := by unfold B8; ring
  -- Taylor remainders for orders `j ≤ 3`
  have htaylor : ∀ j : ℕ, j ≤ 3 → ‖Pq (vfJet F j (Y t)) - W.ι (polyCurveDeriv j (W.taylorC X) t)‖
      ≤ B8 A * ε * h⁻¹ ^ 7 * τ ^ (8 - j) := by
    intro j hj
    set g : ℝ → Ev := fun τ => Pq (vfJet F j (Y τ))
    have hgc : ContDiffOn ℝ ∞ g S := by
      have h1 := (vfJet_contDiffOn hFc hU j).comp (contDiffOn_of_solution hFc hS hYU hYd)
        (fun s hs => hYU s hs)
      exact Pq.contDiff.comp_contDiffOn h1
    have hrem := norm_sub_taylor_le hS hgc ht0 (fun s hs => hIcc ⟨hs.1, hs.2.trans ht.2⟩)
      (7 - j) (C := B8 A * ε * h⁻¹ ^ 7) (fun y hy => by
        rw [hjet j (7 - j + 1) y (hIcc ⟨hy.1, hy.2.trans ht.2⟩),
          show j + (7 - j + 1) = 7 + 1 by omega]
        show ‖W.ι (vfJet F (7 + 1) (Y y)).1‖ ≤ _
        rw [hproj 7 (Y y) (hYU y (hIcc ⟨hy.1, hy.2.trans ht.2⟩))]
        exact hp8 y (hIcc ⟨hy.1, hy.2.trans ht.2⟩))
    -- the Taylor sum is the image of `T_X^{(j)}`
    have hsum : ∑ k ∈ Finset.range (7 - j + 1), ((k.factorial : ℝ)⁻¹ * t ^ k) •
        iteratedDeriv k g 0 = W.ι (polyCurveDeriv j (W.taylorC X) t) := by
      have htc : W.taylorC X = taylorCoeffs (fun τ => (vfJet F 0 (Y τ)).1) 8 := by
        funext i; simp only [taylorC, taylorCoeffs, hjetq]
      rw [htc, polyCurveDeriv_taylorCoeffs _ (by omega : j < 8)]
      simp only [VectorLineTaylor.taylorSum, map_sum, map_smul, iteratedDeriv_iteratedDeriv_eq,
        show 8 - 1 - j = 7 - j by omega]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      rw [hjet j k 0 h0S, hjetq, add_comm k j, hY0]
      rfl
    rw [hsum] at hrem
    refine hrem.trans ?_
    have hf : (1 : ℝ) ≤ ((7 - j).factorial : ℝ) := by
      have : 1 ≤ (7 - j).factorial := Nat.factorial_pos _
      exact_mod_cast this
    have hC0 : 0 ≤ B8 A * ε * h⁻¹ ^ 7 := by positivity
    have htτ : t ^ (7 - j + 1) ≤ τ ^ (8 - j) := by
      rw [show 7 - j + 1 = 8 - j by omega]; exact pow_le_pow_left₀ ht0 ht.2 _
    calc B8 A * ε * h⁻¹ ^ 7 * t ^ (7 - j + 1) / ((7 - j).factorial : ℝ)
        ≤ B8 A * ε * h⁻¹ ^ 7 * t ^ (7 - j + 1) :=
          div_le_self (by positivity) hf
      _ ≤ B8 A * ε * h⁻¹ ^ 7 * τ ^ (8 - j) := mul_le_mul_of_nonneg_left htτ hC0
  -- scaled Taylor errors `e_j ≤ E₀ ε h^{9-2j}`
  have hτ0' : 0 ≤ τ := hτ0.le
  have he : ∀ j : ℕ, ∀ n : ℕ, j ≤ 3 → 2 * (8 - j) = n + 7 →
      ‖Pq (vfJet F j (Y t)) - W.ι (polyCurveDeriv j (W.taylorC X) t)‖ ≤ E0 * ε * h ^ n := by
    intro j n hj hn
    refine (htaylor j hj).trans ?_
    have := pow_scale hh hc hτ0' hτc (m := 8 - j) (n := n) (by omega) hn
    calc B8 A * ε * h⁻¹ ^ 7 * τ ^ (8 - j) = B8 A * ε * (h⁻¹ ^ 7 * τ ^ (8 - j)) := by ring
      _ ≤ B8 A * ε * (c ^ 8 * h ^ n) := by gcongr
      _ = E0 * ε * h ^ n := by rw [hE0]; ring
  have he0 := he 0 9 (by norm_num) (by norm_num)
  have he1 := he 1 7 (by norm_num) (by norm_num)
  have he2 := he 2 5 (by norm_num) (by norm_num)
  have he3 := he 3 3 (by norm_num) (by norm_num)
  -- identification of the exact jets
  have hYt := hYU t htS
  have hg0 : Pq (vfJet F 0 (Y t)) = W.ι (Y t).1 := rfl
  have hg1 : Pq (vfJet F 1 (Y t)) = (Y t).2 := by
    show W.ι (vfJet F (0 + 1) (Y t)).1 = _; rw [hproj 0 _ hYt]; rfl
  have hg2 : Pq (vfJet F 2 (Y t)) = W.V (Y t) := by
    show W.ι (vfJet F (1 + 1) (Y t)).1 = _; rw [hproj 1 _ hYt, vfJet_one]; rfl
  have hg3 : Pq (vfJet F 3 (Y t)) = (fderiv ℝ F (Y t) (F (Y t))).2 := by
    show W.ι (vfJet F (2 + 1) (Y t)).1 = _; rw [hproj 2 _ hYt, vfJet_succ, vfJet_one]
  rw [hg0] at he0; rw [hg1] at he1; rw [hg2] at he2; rw [hg3] at he3
  -- powers of `h`
  have hp : ∀ n m : ℕ, n ≤ m → h ^ m ≤ h ^ n := fun n m hnm => pow_le_pow_of_le_one hh.le hh1 hnm
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have hu := hB.norm_u
  -- the phase error
  set T := W.taylorC X
  have hphase : ‖W.phase T t - Y t‖ ≤ Ph * ε * h ^ 7 := by
    have h1 : (W.phase T t - Y t).1 = W.u (W.ι (polyCurve T t) - W.ι (Y t).1) := by
      show polyCurve T t - (Y t).1 = _
      rw [map_sub, W.u_ι, W.u_ι]
    have h2 : (W.phase T t - Y t).2 = W.ι (polyCurveDeriv 1 T t) - (Y t).2 := rfl
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · rw [h1]
      refine (W.u.le_opNorm _).trans ?_
      rw [norm_sub_rev, ← polyCurveDeriv_zero]
      calc ‖W.u‖ * ‖W.ι (Y t).1 - W.ι (polyCurveDeriv 0 T t)‖ ≤ A * h⁻¹ * (E0 * ε * h ^ 9) :=
            mul_le_mul hu he0 (norm_nonneg _) hM.le
        _ = A * E0 * ε * h ^ 7 * (h⁻¹ * h) * h := by ring
        _ ≤ Ph * ε * h ^ 7 := by
            rw [hinv, mul_one, hPh]
            have : 0 ≤ A * E0 * ε * h ^ 7 := by positivity
            nlinarith
    · rw [h2, norm_sub_rev]
      refine he1.trans ?_
      have : E0 ≤ Ph := by rw [hPh]; nlinarith
      have : 0 ≤ ε * h ^ 7 := by positivity
      nlinarith
  -- the velocity error `‖𝓕(Y) − Φ_T'‖ ≤ Ph ε h⁵`
  have hvel : ‖F (Y t) - W.phaseVel T t‖ ≤ Ph * ε * h ^ 5 := by
    have h1 : (F (Y t) - W.phaseVel T t).1 = W.u ((Y t).2 - W.ι (polyCurveDeriv 1 T t)) := by
      show W.u (Y t).2 - polyCurveDeriv 1 T t = _
      rw [map_sub, W.u_ι]
    have h2 : (F (Y t) - W.phaseVel T t).2 = W.V (Y t) - W.ι (polyCurveDeriv 2 T t) := rfl
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · rw [h1]
      refine (W.u.le_opNorm _).trans ?_
      calc ‖W.u‖ * ‖(Y t).2 - W.ι (polyCurveDeriv 1 T t)‖ ≤ A * h⁻¹ * (E0 * ε * h ^ 7) :=
            mul_le_mul hu he1 (norm_nonneg _) hM.le
        _ = A * E0 * ε * h ^ 5 * (h⁻¹ * h) * h := by ring
        _ ≤ Ph * ε * h ^ 5 := by
            rw [hinv, mul_one, hPh]
            have : 0 ≤ A * E0 * ε * h ^ 5 := by positivity
            nlinarith
    · rw [h2]
      refine he2.trans ?_
      have : E0 ≤ Ph := by rw [hPh]; nlinarith
      have : 0 ≤ ε * h ^ 5 := by positivity
      nlinarith
  -- chart
  have hYtn := hYn t htS
  have hphn : ‖W.phase T t‖ ≤ 2 * ε + Ph * ε * h ^ 7 := by
    calc ‖W.phase T t‖ = ‖Y t + (W.phase T t - Y t)‖ := by congr 1; abel
      _ ≤ ‖Y t‖ + ‖W.phase T t - Y t‖ := norm_add_le _ _
      _ ≤ 2 * ε + Ph * ε * h ^ 7 := add_le_add hYtn hphase
  have hPhU : W.phase T t ∈ U := by
    refine mem_ball_zero_iff.mpr (lt_of_le_of_lt hphn ?_)
    have : Ph * ε * h ^ 7 ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_right hsmall hε0
      nlinarith
    linarith [hB.δ_pos]
  refine ⟨hphn, ?_, ?_, ?_⟩
  · -- the defect of `T_X`
    have hdef : W.defect T t = (W.ι (polyCurveDeriv 2 T t) - W.V (Y t)) +
        (W.V (Y t) - W.V (W.phase T t)) := by
      unfold defect; abel
    rw [hdef]
    refine (norm_add_le _ _).trans ?_
    have hV : ‖W.V (Y t) - W.V (W.phase T t)‖ ≤ A * h⁻¹ * (Ph * ε * h ^ 7) := by
      have : W.V (Y t) - W.V (W.phase T t) = (F (Y t) - F (W.phase T t)).2 := rfl
      rw [this]
      refine (norm_snd_le _).trans ((hB.lip_field hYt hPhU).trans ?_)
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_left hphase hM.le
    have e1 : A * h⁻¹ * (Ph * ε * h ^ 7) = A * Ph * ε * h ^ 5 * (h⁻¹ * h) * h := by ring
    rw [e1, hinv, mul_one] at hV
    rw [norm_sub_rev] at he2
    have : A * Ph * ε * h ^ 5 * h ≤ A * Ph * ε * h ^ 5 := by
      have : 0 ≤ A * Ph * ε * h ^ 5 := by positivity
      nlinarith
    nlinarith
  · -- the time derivative of the defect
    have hderiv : W.defectDeriv T t =
        (W.ι (polyCurveDeriv 3 T t) - (fderiv ℝ F (Y t) (F (Y t))).2) +
        ((fderiv ℝ F (Y t) - fderiv ℝ F (W.phase T t)) (F (Y t))).2 +
        (fderiv ℝ F (W.phase T t) (F (Y t) - W.phaseVel T t)).2 := by
      simp only [defectDeriv, ContinuousLinearMap.sub_apply, map_sub, Prod.snd_sub]
      abel
    rw [hderiv]
    have b1 : ‖W.ι (polyCurveDeriv 3 T t) - (fderiv ℝ F (Y t) (F (Y t))).2‖ ≤ E0 * ε * h ^ 3 := by
      rw [norm_sub_rev]; exact he3
    have b2 : ‖((fderiv ℝ F (Y t) - fderiv ℝ F (W.phase T t)) (F (Y t))).2‖ ≤
        (A * h⁻¹ * (Ph * ε * h ^ 7)) * (A * h⁻¹ * (2 * ε)) := by
      refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      refine mul_le_mul ?_ ((hB.field_le _ hYt).trans
        (mul_le_mul_of_nonneg_left hYtn hM.le)) (norm_nonneg _) (by positivity)
      exact (hB.lip_fderiv hYt hPhU).trans (mul_le_mul_of_nonneg_left (by
        rw [norm_sub_rev]; exact hphase) hM.le)
    have b3 : ‖(fderiv ℝ F (W.phase T t) (F (Y t) - W.phaseVel T t)).2‖ ≤
        A * h⁻¹ * (Ph * ε * h ^ 5) := by
      refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      exact mul_le_mul (hB.norm_fderiv hPhU) hvel (norm_nonneg _) hM.le
    refine (norm_add₃_le).trans ?_
    have e1 : A * h⁻¹ * (Ph * ε * h ^ 7) * (A * h⁻¹ * (2 * ε)) =
        2 * A ^ 2 * Ph * ε * ε * h ^ 3 * (h⁻¹ * h) ^ 2 * h ^ 2 := by ring
    have e2 : A * h⁻¹ * (Ph * ε * h ^ 5) = A * Ph * ε * h ^ 3 * (h⁻¹ * h) * h := by ring
    rw [e1, hinv, one_pow, mul_one] at b2
    rw [e2, hinv, mul_one] at b3
    have k2 : 2 * A ^ 2 * Ph * ε * ε * h ^ 3 * h ^ 2 ≤ 2 * A ^ 2 * Ph * ε * h ^ 3 := by
      have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ hh.le hh1
      have : ε * h ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ 2 * A ^ 2 * Ph * ε * h ^ 3 := by positivity
      nlinarith
    have k3 : A * Ph * ε * h ^ 3 * h ≤ A * Ph * ε * h ^ 3 := by
      have : 0 ≤ A * Ph * ε * h ^ 3 := by positivity
      nlinarith
    nlinarith
  · -- the phase velocity
    have h1 : ‖W.phaseVel T t‖ ≤ ‖F (Y t)‖ + ‖F (Y t) - W.phaseVel T t‖ := by
      calc ‖W.phaseVel T t‖ = ‖F (Y t) - (F (Y t) - W.phaseVel T t)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖F (Y t)‖ ≤ A * h⁻¹ * (2 * ε) :=
      (hB.field_le _ hYt).trans (mul_le_mul_of_nonneg_left hYtn hM.le)
    have h3 : Ph * ε * h ^ 5 ≤ Ph * h⁻¹ * ε := by
      have : h ^ 5 ≤ h⁻¹ := (pow_le_one₀ hh.le hh1).trans (one_le_inv₀ hh |>.mpr hh1)
      have : 0 ≤ Ph * ε := by positivity
      nlinarith
    nlinarith

end Writer

/-! ### The endpoint correction and the complete residual -/

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [CompleteSpace Eq]
  [NormedAddCommGroup Ev] [NormedSpace ℝ Ev] [CompleteSpace Ev] {W : Writer Eq Ev}
  {h A δ : ℝ}

/-- `ι δ₂ = −f_T(τ)` and `ι δ₃ = DV(X₁)[(0, −f_T(τ))] − ∂_t f_T(τ)`. -/
theorem Bounds.corr_norms (hB : W.Bounds h A δ) {X : Eq × Ev} {τ : ℝ}
    (hX1 : W.endpoint X τ ∈ ball 0 δ) :
    ‖W.ι (W.corr2 X τ)‖ ≤ ‖W.defect (W.taylorC X) τ‖ ∧
    ‖W.ι (W.corr3 X τ)‖ ≤ A * h⁻¹ * ‖W.defect (W.taylorC X) τ‖ +
      ‖W.defectDeriv (W.taylorC X) τ‖ := by
  set F := W.field
  have hU : IsOpen (ball (0 : Eq × Ev) δ) := isOpen_ball
  have hFc : ContDiffOn ℝ ∞ F (ball 0 δ) := hB.deriv.contDiffOn
  set Pq : Eq × Ev →L[ℝ] Ev := W.ι.comp (ContinuousLinearMap.fst ℝ Eq Ev)
  have hPQ : ∀ Z ∈ ball (0 : Eq × Ev) δ, Pq (F Z) = (ContinuousLinearMap.snd ℝ Eq Ev) Z := by
    intro Z _; show W.ι (W.u Z.2) = Z.2; exact W.ι_u _
  have hproj : ∀ j, ∀ Z ∈ ball (0 : Eq × Ev) δ, W.ι (vfJet F (j + 1) Z).1 = (vfJet F j Z).2 :=
    fun j Z hZ => vfJet_proj hFc hU Pq (ContinuousLinearMap.snd ℝ Eq Ev) hPQ j Z hZ
  set T := W.taylorC X
  set X1 := W.endpoint X τ
  have hX1p : X1 = W.phase T τ := rfl
  have h2 : W.ι (W.corr2 X τ) = -W.defect T τ := by
    have : W.ι (W.qj 2 X1) = W.V X1 := by
      show W.ι (vfJet F (1 + 1) X1).1 = _
      rw [hproj 1 X1 hX1, vfJet_one]; rfl
    rw [corr2, map_sub, this, defect, ← hX1p]; abel
  have hvel : F X1 - W.phaseVel T τ = (0, -W.defect T τ) := by
    refine Prod.ext ?_ ?_
    · show W.u (W.ι (polyCurveDeriv 1 T τ)) - polyCurveDeriv 1 T τ = 0
      rw [W.u_ι, sub_self]
    · show W.V X1 - W.ι (polyCurveDeriv 2 T τ) = -(W.ι (polyCurveDeriv 2 T τ) - W.V X1)
      abel
  have h3 : W.ι (W.corr3 X τ) = (fderiv ℝ F X1 (F X1 - W.phaseVel T τ)).2 - W.defectDeriv T τ := by
    have : W.ι (W.qj 3 X1) = (fderiv ℝ F X1 (F X1)).2 := by
      show W.ι (vfJet F (2 + 1) X1).1 = _
      rw [hproj 2 X1 hX1, vfJet_succ, vfJet_one]
    rw [corr3, map_sub, this, defectDeriv, ← hX1p, map_sub, Prod.snd_sub]; abel
  refine ⟨by rw [h2, norm_neg], ?_⟩
  rw [h3]
  refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
  refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
  rw [hvel]
  refine mul_le_mul (hB.norm_fderiv hX1) ?_ (norm_nonneg _) hB.M_pos.le
  rw [Prod.norm_def, norm_zero, norm_neg]
  exact max_le (norm_nonneg _) le_rfl

/-- Derivative bounds for the image of the endpoint correction. -/
theorem norm_ι_corr_le (W : Writer Eq Ev) {τ : ℝ} (hτ : 0 < τ) (δ₂ δ₃ : Eq) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 τ) :
    ‖W.ι (polyCurveDeriv j (hermiteCorrection τ δ₂ δ₃) t)‖ ≤
      hermiteConst 3 j * (τ ^ 2 * ‖W.ι δ₂‖ + τ ^ 3 * ‖W.ι δ₃‖) / τ ^ j := by
  obtain ⟨h0, h10, h11, h12, h13⟩ := hermiteCorrection_jets hτ.ne' δ₂ δ₃
  simp only [iteratedDeriv_polyCurve] at h0 h11 h12 h13
  rw [← polyCurveDeriv_zero] at h10
  rw [W.ι_polyCurveDeriv]
  refine norm_polyCurveDeriv_le_scaled (k := 3) _ hτ (fun e i => ?_) j ht
  have hb0 : 0 ≤ τ ^ 2 * ‖W.ι δ₂‖ + τ ^ 3 * ‖W.ι δ₃‖ := by positivity
  rw [← W.ι_polyCurveDeriv]
  fin_cases e
  · simp only [Fin.zero_eta, Fin.val_zero, Nat.cast_zero, zero_mul]
    rw [h0 i, map_zero, norm_zero, mul_zero]; exact hb0
  · simp only [Fin.mk_one, Fin.val_one, Nat.cast_one, one_mul]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.val_zero, pow_zero, one_mul]
      rw [h10, map_zero, norm_zero]; exact hb0
    · simp only [Fin.mk_one, Fin.val_one, pow_one]
      rw [h11, map_zero, norm_zero, mul_zero]; exact hb0
    · show τ ^ 2 * ‖W.ι (polyCurveDeriv 2 (hermiteCorrection τ δ₂ δ₃) τ)‖ ≤ _
      rw [h12]
      have : 0 ≤ τ ^ 3 * ‖W.ι δ₃‖ := by positivity
      linarith
    · show τ ^ 3 * ‖W.ι (polyCurveDeriv 3 (hermiteCorrection τ δ₂ δ₃) τ)‖ ≤ _
      rw [h13]
      have : 0 ≤ τ ^ 2 * ‖W.ι δ₂‖ := by positivity
      linarith

end Writer

namespace Writer

variable {Eq Ev : Type*} [NormedAddCommGroup Eq] [NormedSpace ℝ Eq] [CompleteSpace Eq]
  [NormedAddCommGroup Ev] [NormedSpace ℝ Ev] [CompleteSpace Ev] {W : Writer Eq Ev}
  {h A δ : ℝ}

theorem Bounds.phase_corr_le (hB : W.Bounds h A δ) {T Cc : Fin 8 → Eq} {t ε Kc : ℝ}
    (hε0 : 0 ≤ ε) (hKc0 : 0 ≤ Kc)
    (hc0 : ‖W.ι (polyCurveDeriv 0 Cc t)‖ ≤ Kc * ε * h ^ 9)
    (hc1 : ‖W.ι (polyCurveDeriv 1 Cc t)‖ ≤ Kc * ε * h ^ 7) :
    ‖W.phase (T + Cc) t - W.phase T t‖ ≤ A * Kc * ε * h ^ 7 := by
  have hh := hB.h_pos
  have hA := hB.one_le_A
  have hM := hB.M_pos
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have e : W.phase (T + Cc) t - W.phase T t = (polyCurve Cc t, W.ι (polyCurveDeriv 1 Cc t)) := by
    have hQ0 : polyCurve (T + Cc) t = polyCurve T t + polyCurve Cc t := by
      rw [← polyCurveDeriv_zero, polyCurveDeriv_add, polyCurveDeriv_zero, polyCurveDeriv_zero]
    show (polyCurve (T + Cc) t, W.ι (polyCurveDeriv 1 (T + Cc) t)) -
      (polyCurve T t, W.ι (polyCurveDeriv 1 T t)) = _
    rw [hQ0, polyCurveDeriv_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp
  rw [e]
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · rw [← W.u_ι (polyCurve Cc t), ← polyCurveDeriv_zero]
    refine (W.u.le_opNorm _).trans ?_
    calc ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 Cc t)‖ ≤ A * h⁻¹ * (Kc * ε * h ^ 9) :=
          mul_le_mul hB.norm_u hc0 (norm_nonneg _) hM.le
      _ = A * Kc * ε * h ^ 7 * (h⁻¹ * h) * h := by ring
      _ ≤ A * Kc * ε * h ^ 7 := by
          rw [hinv, mul_one]
          have : 0 ≤ A * Kc * ε * h ^ 7 := by positivity
          nlinarith [hB.h_le_one]
  · refine hc1.trans ?_
    have : 0 ≤ Kc * ε * h ^ 7 := by positivity
    nlinarith

theorem Bounds.phaseVel_corr_le (hB : W.Bounds h A δ) {T Cc : Fin 8 → Eq} {t ε Kc : ℝ}
    (hε0 : 0 ≤ ε) (hKc0 : 0 ≤ Kc)
    (hc1 : ‖W.ι (polyCurveDeriv 1 Cc t)‖ ≤ Kc * ε * h ^ 7)
    (hc2 : ‖W.ι (polyCurveDeriv 2 Cc t)‖ ≤ Kc * ε * h ^ 5) :
    ‖W.phaseVel (T + Cc) t - W.phaseVel T t‖ ≤ A * Kc * ε * h ^ 5 := by
  have hh := hB.h_pos
  have hA := hB.one_le_A
  have hM := hB.M_pos
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have e : W.phaseVel (T + Cc) t - W.phaseVel T t =
      (polyCurveDeriv 1 Cc t, W.ι (polyCurveDeriv 2 Cc t)) := by
    show (polyCurveDeriv 1 (T + Cc) t, W.ι (polyCurveDeriv 2 (T + Cc) t)) -
      (polyCurveDeriv 1 T t, W.ι (polyCurveDeriv 2 T t)) = _
    rw [polyCurveDeriv_add, polyCurveDeriv_add, map_add]
    refine Prod.ext ?_ ?_ <;> simp
  rw [e]
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · rw [← W.u_ι (polyCurveDeriv 1 Cc t)]
    refine (W.u.le_opNorm _).trans ?_
    calc ‖W.u‖ * ‖W.ι (polyCurveDeriv 1 Cc t)‖ ≤ A * h⁻¹ * (Kc * ε * h ^ 7) :=
          mul_le_mul hB.norm_u hc1 (norm_nonneg _) hM.le
      _ = A * Kc * ε * h ^ 5 * (h⁻¹ * h) * h := by ring
      _ ≤ A * Kc * ε * h ^ 5 := by
          rw [hinv, mul_one]
          have : 0 ≤ A * Kc * ε * h ^ 5 := by positivity
          nlinarith [hB.h_le_one]
  · refine hc2.trans ?_
    have : 0 ≤ Kc * ε * h ^ 5 := by positivity
    nlinarith

theorem Bounds.defect_corr_le (hB : W.Bounds h A δ) {T Cc : Fin 8 → Eq} {t ε Kc G0 : ℝ}
    (hε0 : 0 ≤ ε) (hKc0 : 0 ≤ Kc) (hTU : W.phase T t ∈ ball 0 δ)
    (hQU : W.phase (T + Cc) t ∈ ball 0 δ) (hdT : ‖W.defect T t‖ ≤ G0 * ε * h ^ 5)
    (hc2 : ‖W.ι (polyCurveDeriv 2 Cc t)‖ ≤ Kc * ε * h ^ 5)
    (hph : ‖W.phase (T + Cc) t - W.phase T t‖ ≤ A * Kc * ε * h ^ 7) :
    ‖W.defect (T + Cc) t‖ ≤ (G0 + Kc + A ^ 2 * Kc) * ε * h ^ 5 := by
  have hh := hB.h_pos
  have hA := hB.one_le_A
  have hM := hB.M_pos
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have e : W.defect (T + Cc) t = W.defect T t + W.ι (polyCurveDeriv 2 Cc t) +
      (W.V (W.phase T t) - W.V (W.phase (T + Cc) t)) := by
    simp only [defect]; rw [polyCurveDeriv_add, map_add]; abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  have hV : ‖W.V (W.phase T t) - W.V (W.phase (T + Cc) t)‖ ≤
      A * h⁻¹ * (A * Kc * ε * h ^ 7) := by
    have : W.V (W.phase T t) - W.V (W.phase (T + Cc) t) =
        (W.field (W.phase T t) - W.field (W.phase (T + Cc) t)).2 := rfl
    rw [this]
    refine (norm_snd_le _).trans ((hB.lip_field hTU hQU).trans ?_)
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_left hph hM.le
  have e1 : A * h⁻¹ * (A * Kc * ε * h ^ 7) = A ^ 2 * Kc * ε * h ^ 5 * (h⁻¹ * h) * h := by ring
  rw [e1, hinv, mul_one] at hV
  have k : A ^ 2 * Kc * ε * h ^ 5 * h ≤ A ^ 2 * Kc * ε * h ^ 5 := by
    have : 0 ≤ A ^ 2 * Kc * ε * h ^ 5 := by positivity
    nlinarith [hB.h_le_one]
  calc ‖W.defect T t‖ + ‖W.ι (polyCurveDeriv 2 Cc t)‖ +
        ‖W.V (W.phase T t) - W.V (W.phase (T + Cc) t)‖
      ≤ G0 * ε * h ^ 5 + Kc * ε * h ^ 5 + A ^ 2 * Kc * ε * h ^ 5 := by linarith
    _ = (G0 + Kc + A ^ 2 * Kc) * ε * h ^ 5 := by ring

theorem Bounds.defectDeriv_corr_le (hB : W.Bounds h A δ) {T Cc : Fin 8 → Eq}
    {t ε Kc G1 Ph : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hKc0 : 0 ≤ Kc) (hPh0 : 0 ≤ Ph)
    (hTU : W.phase T t ∈ ball 0 δ)
    (hQU : W.phase (T + Cc) t ∈ ball 0 δ) (hddT : ‖W.defectDeriv T t‖ ≤ G1 * ε * h ^ 3)
    (hvT : ‖W.phaseVel T t‖ ≤ (2 * A + Ph) * h⁻¹ * ε)
    (hc3 : ‖W.ι (polyCurveDeriv 3 Cc t)‖ ≤ Kc * ε * h ^ 3)
    (hph : ‖W.phase (T + Cc) t - W.phase T t‖ ≤ A * Kc * ε * h ^ 7)
    (hvel : ‖W.phaseVel (T + Cc) t - W.phaseVel T t‖ ≤ A * Kc * ε * h ^ 5) :
    ‖W.defectDeriv (T + Cc) t‖ ≤
      (G1 + Kc + A ^ 2 * Kc * (2 * A + Ph) + A ^ 2 * Kc) * ε * h ^ 3 := by
  have hh := hB.h_pos
  have hh1 := hB.h_le_one
  have hA := hB.one_le_A
  have hM := hB.M_pos
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  set F := W.field
  have e : W.defectDeriv (T + Cc) t = W.defectDeriv T t + W.ι (polyCurveDeriv 3 Cc t) +
      ((fderiv ℝ F (W.phase T t) - fderiv ℝ F (W.phase (T + Cc) t)) (W.phaseVel T t)).2 -
      (fderiv ℝ F (W.phase (T + Cc) t) (W.phaseVel (T + Cc) t - W.phaseVel T t)).2 := by
    simp only [defectDeriv, ContinuousLinearMap.sub_apply, map_sub, Prod.snd_sub]
    rw [polyCurveDeriv_add, map_add]; abel
  rw [e]
  have b3 : ‖((fderiv ℝ F (W.phase T t) - fderiv ℝ F (W.phase (T + Cc) t))
      (W.phaseVel T t)).2‖ ≤ A * h⁻¹ * (A * Kc * ε * h ^ 7) * ((2 * A + Ph) * h⁻¹ * ε) := by
    refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    refine mul_le_mul ?_ hvT (norm_nonneg _) (by positivity)
    refine (hB.lip_fderiv hTU hQU).trans (mul_le_mul_of_nonneg_left ?_ hM.le)
    rw [norm_sub_rev]; exact hph
  have b4 : ‖(fderiv ℝ F (W.phase (T + Cc) t) (W.phaseVel (T + Cc) t - W.phaseVel T t)).2‖ ≤
      A * h⁻¹ * (A * Kc * ε * h ^ 5) := by
    refine (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    exact mul_le_mul (hB.norm_fderiv hQU) hvel (norm_nonneg _) hM.le
  refine (norm_sub_le _ _).trans ((add_le_add norm_add₃_le le_rfl).trans ?_)
  have e3 : A * h⁻¹ * (A * Kc * ε * h ^ 7) * ((2 * A + Ph) * h⁻¹ * ε) =
      A ^ 2 * Kc * (2 * A + Ph) * ε * ε * h ^ 3 * (h⁻¹ * h) ^ 2 * h ^ 2 := by ring
  have e4 : A * h⁻¹ * (A * Kc * ε * h ^ 5) = A ^ 2 * Kc * ε * h ^ 3 * (h⁻¹ * h) * h := by ring
  rw [e3, hinv, one_pow, mul_one] at b3
  rw [e4, hinv, mul_one] at b4
  have k3 : A ^ 2 * Kc * (2 * A + Ph) * ε * ε * h ^ 3 * h ^ 2 ≤
      A ^ 2 * Kc * (2 * A + Ph) * ε * h ^ 3 := by
    have hh2 : h ^ 2 ≤ 1 := pow_le_one₀ hh.le hh1
    have heh : ε * h ^ 2 ≤ 1 := by nlinarith
    have hpos : 0 ≤ A ^ 2 * Kc * (2 * A + Ph) * ε * h ^ 3 := by positivity
    calc A ^ 2 * Kc * (2 * A + Ph) * ε * ε * h ^ 3 * h ^ 2
        = (A ^ 2 * Kc * (2 * A + Ph) * ε * h ^ 3) * (ε * h ^ 2) := by ring
      _ ≤ (A ^ 2 * Kc * (2 * A + Ph) * ε * h ^ 3) * 1 := mul_le_mul_of_nonneg_left heh hpos
      _ = _ := mul_one _
  have k4 : A ^ 2 * Kc * ε * h ^ 3 * h ≤ A ^ 2 * Kc * ε * h ^ 3 := by
    have : 0 ≤ A ^ 2 * Kc * ε * h ^ 3 := by positivity
    calc A ^ 2 * Kc * ε * h ^ 3 * h ≤ A ^ 2 * Kc * ε * h ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hh1 this
      _ = _ := mul_one _
  calc ‖W.defectDeriv T t‖ + ‖W.ι (polyCurveDeriv 3 Cc t)‖ +
        ‖((fderiv ℝ F (W.phase T t) - fderiv ℝ F (W.phase (T + Cc) t)) (W.phaseVel T t)).2‖ +
        ‖(fderiv ℝ F (W.phase (T + Cc) t) (W.phaseVel (T + Cc) t - W.phaseVel T t)).2‖
      ≤ G1 * ε * h ^ 3 + Kc * ε * h ^ 3 + A ^ 2 * Kc * (2 * A + Ph) * ε * h ^ 3 +
          A ^ 2 * Kc * ε * h ^ 3 := by linarith
    _ = _ := by ring

/-- The amplitude `b = τ²‖δ₂‖ + τ³‖δ₃‖` of the endpoint correction is `O(ε h⁹)`. -/
theorem amp_le {h A ε τ c G0 G1 d2 d3 : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hA : 1 ≤ A) (hε0 : 0 ≤ ε)
    (hc1 : 1 ≤ c) (hτ0 : 0 ≤ τ) (hτc : τ ≤ c * h ^ 2) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1)
    (hd20 : 0 ≤ d2) (hd30 : 0 ≤ d3)
    (hd2 : d2 ≤ G0 * ε * h ^ 5) (hd3 : d3 ≤ A * h⁻¹ * (G0 * ε * h ^ 5) + G1 * ε * h ^ 3) :
    τ ^ 2 * d2 + τ ^ 3 * d3 ≤ c ^ 3 * (G0 + A * G0 + G1) * ε * h ^ 9 := by
  have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have hd3' : d3 ≤ (A * G0 + G1) * ε * h ^ 3 := by
    have e1 : A * h⁻¹ * (G0 * ε * h ^ 5) = A * G0 * ε * h ^ 3 * (h⁻¹ * h) * h := by ring
    rw [e1, hinv, mul_one] at hd3
    have : A * G0 * ε * h ^ 3 * h ≤ A * G0 * ε * h ^ 3 * 1 :=
      mul_le_mul_of_nonneg_left hh1 (by positivity)
    nlinarith
  have t2 : τ ^ 2 ≤ c ^ 3 * h ^ 4 := by
    calc τ ^ 2 ≤ (c * h ^ 2) ^ 2 := pow_le_pow_left₀ hτ0 hτc 2
      _ = c ^ 2 * h ^ 4 := by ring
      _ ≤ c ^ 3 * h ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by positivity)
  have t3 : τ ^ 3 ≤ c ^ 3 * h ^ 6 := by
    calc τ ^ 3 ≤ (c * h ^ 2) ^ 3 := pow_le_pow_left₀ hτ0 hτc 3
      _ = c ^ 3 * h ^ 6 := by ring
  have k1 : τ ^ 2 * d2 ≤ c ^ 3 * h ^ 4 * (G0 * ε * h ^ 5) :=
    mul_le_mul t2 hd2 hd20 (by positivity)
  have k2 : τ ^ 3 * d3 ≤ c ^ 3 * h ^ 6 * ((A * G0 + G1) * ε * h ^ 3) :=
    mul_le_mul t3 hd3' hd30 (by positivity)
  calc τ ^ 2 * d2 + τ ^ 3 * d3 ≤ c ^ 3 * h ^ 4 * (G0 * ε * h ^ 5) +
        c ^ 3 * h ^ 6 * ((A * G0 + G1) * ε * h ^ 3) := add_le_add k1 k2
    _ = c ^ 3 * (G0 + A * G0 + G1) * ε * h ^ 9 := by ring

/-- Derivative bounds of the correction from its amplitude: for `j ≤ 3`, `n + 2j = 9` and
`τ ≥ c₋h²`, `‖ι C⁽ʲ⁾‖ ≤ (K_H B / c₋³) ε hⁿ` on `[0, τ]`. -/
theorem corr_le (W : Writer Eq Ev) {h τ cmm KH Bc ε : ℝ} (hh : 0 < h) (hcmm0 : 0 < cmm)
    (hcmm1 : cmm ≤ 1) (hτm : cmm * h ^ 2 ≤ τ) (hKH : ∀ j < 4, hermiteConst 3 j ≤ KH)
    (hKH0 : 0 ≤ KH) (δ₂ δ₃ : Eq)
    (hb : τ ^ 2 * ‖W.ι δ₂‖ + τ ^ 3 * ‖W.ι δ₃‖ ≤ Bc * ε * h ^ 9) (hBc : 0 ≤ Bc) (hε : 0 ≤ ε)
    (j n : ℕ) (hj : j ≤ 3) (hn : n + 2 * j = 9) {s : ℝ} (hs : s ∈ Icc 0 τ) :
    ‖W.ι (polyCurveDeriv j (hermiteCorrection τ δ₂ δ₃) s)‖ ≤ KH * Bc / cmm ^ 3 * ε * h ^ n := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτm
  refine (W.norm_ι_corr_le hτ0 δ₂ δ₃ j hs).trans ?_
  have hτj : cmm ^ 3 * h ^ (2 * j) ≤ τ ^ j := by
    calc cmm ^ 3 * h ^ (2 * j) ≤ cmm ^ j * h ^ (2 * j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hcmm0.le hcmm1 hj) (by positivity)
      _ = (cmm * h ^ 2) ^ j := by rw [mul_pow, ← pow_mul]
      _ ≤ τ ^ j := pow_le_pow_left₀ (by positivity) hτm j
  have hpos : 0 < cmm ^ 3 * h ^ (2 * j) := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hτj)]
  have hb0 : 0 ≤ τ ^ 2 * ‖W.ι δ₂‖ + τ ^ 3 * ‖W.ι δ₃‖ := by positivity
  calc hermiteConst 3 j * (τ ^ 2 * ‖W.ι δ₂‖ + τ ^ 3 * ‖W.ι δ₃‖) ≤ KH * (Bc * ε * h ^ 9) :=
        mul_le_mul (hKH j (by omega)) hb hb0 hKH0
    _ = KH * Bc / cmm ^ 3 * ε * h ^ n * (cmm ^ 3 * h ^ (2 * j)) := by
        rw [← hn, pow_add]; field_simp
    _ ≤ KH * Bc / cmm ^ 3 * ε * h ^ n * τ ^ j := by
        refine mul_le_mul_of_nonneg_left hτj ?_
        have : 0 ≤ KH * Bc / cmm ^ 3 * ε :=
          mul_nonneg (div_nonneg (mul_nonneg hKH0 hBc) (by positivity)) hε
        have : 0 ≤ h ^ n := by positivity
        positivity

end Writer

universe uq uv

set_option maxHeartbeats 4000000 in
/-- Extended form of `hermite_residual`: additionally `‖(Q_X, Q_X')‖ ≤ 3ε` and
`‖(Q_X', Q_X'')‖ ≤ C h^{-1} ε` on `[0, τ]` (used for perturbations). -/
theorem hermite_residual_full (A cm cp : ℝ) (hA : 1 ≤ A) (hcm : 0 < cm) (hcp : 0 < cp) :
    ∃ h₀ > 0, ∃ C ≥ 0, ∀ {Eq : Type uq} {Ev : Type uv} [NormedAddCommGroup Eq]
      [NormedSpace ℝ Eq] [CompleteSpace Eq] [NormedAddCommGroup Ev] [NormedSpace ℝ Ev]
      [CompleteSpace Ev] (W : Writer Eq Ev) (h δ : ℝ), W.Bounds h A δ → h ≤ h₀ →
      ∀ (X : Eq × Ev) (ε τ : ℝ), ‖X‖ ≤ ε → 4 * ε ≤ δ → cm * h ^ 2 ≤ τ → τ ≤ cp * h ^ 2 →
      ∀ t ∈ Icc 0 τ, W.phase (W.hermiteC X τ) t ∈ ball 0 δ ∧
        ‖W.defect (W.hermiteC X τ) t‖ ≤ C * ε * h ^ 5 ∧
        HasDerivAt (W.defect (W.hermiteC X τ)) (W.defectDeriv (W.hermiteC X τ) t) t ∧
        ‖W.defectDeriv (W.hermiteC X τ) t‖ ≤ C * ε * h ^ 3 ∧
        ‖W.phase (W.hermiteC X τ) t‖ ≤ 3 * ε ∧
        ‖W.phaseVel (W.hermiteC X τ) t‖ ≤ C * h⁻¹ * ε := by
  set c := max cp 1 with hcdef
  have hc1 : 1 ≤ c := le_max_right _ _
  have hcp' : cp ≤ c := le_max_left _ _
  set cmm := min cm 1 with hcmmdef
  have hcmm0 : 0 < cmm := lt_min hcm one_pos
  have hcmm1 : cmm ≤ 1 := min_le_right _ _
  have hcmm : cmm ≤ cm := min_le_left _ _
  set E0 := Writer.B8 A * c ^ 8 with hE0
  have hB8 : 0 ≤ Writer.B8 A := by unfold Writer.B8; positivity
  have hE00 : 0 ≤ E0 := by positivity
  set Ph := A * E0 with hPh
  have hPh0 : 0 ≤ Ph := by positivity
  set G0 := E0 + A * Ph with hG0
  set G1 := E0 + (2 * A ^ 2 + A) * Ph with hG1
  have hG00 : 0 ≤ G0 := by positivity
  have hG10 : 0 ≤ G1 := by positivity
  set KH := ∑ j ∈ Finset.range 4, hermiteConst 3 j with hKH
  have hKH0 : 0 ≤ KH := Finset.sum_nonneg fun j _ => hermiteConst_nonneg 3 j
  have hKHj : ∀ j < 4, hermiteConst 3 j ≤ KH := fun j hj =>
    Finset.single_le_sum (f := fun j => hermiteConst 3 j) (fun j _ => hermiteConst_nonneg 3 j)
      (Finset.mem_range.mpr hj)
  set Bc := c ^ 3 * (G0 + A * G0 + G1) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set Kc := KH * Bc / cmm ^ 3 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set C1 := G0 + Kc + A ^ 2 * Kc
  set C2 := G1 + Kc + A ^ 2 * Kc * (2 * A + Ph) + A ^ 2 * Kc
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  set C3 := 2 * A + Ph + A * Kc
  have hC30 : 0 ≤ C3 := by positivity
  refine ⟨min (1 / (4 * A * c)) (1 / (2 * (Ph + A * Kc) + 1)), lt_min (by positivity)
    (by positivity), C1 + C2 + C3, by positivity, ?_⟩
  intro Eq Ev _ _ _ _ _ _ W h δ hB hh0 X ε τ hX hεδ hτm hτp t ht
  have hh := hB.h_pos
  have hh1 := hB.h_le_one
  have hM := hB.M_pos
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hX
  have hε1 : ε ≤ 1 := by linarith [hB.δ_le_one]
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτm
  have hτc : τ ≤ c * h ^ 2 := hτp.trans (mul_le_mul_of_nonneg_right hcp' (by positivity))
  have hh0a : h ≤ 1 / (4 * A * c) := hh0.trans (min_le_left _ _)
  have hh0b : h ≤ 1 / (2 * (Ph + A * Kc) + 1) := hh0.trans (min_le_right _ _)
  have hτσ : τ < h / (2 * A) := by
    have h0 : h * (4 * A * c) ≤ 1 := (le_div_iff₀ (by positivity)).mp hh0a
    have h2 : c * h ^ 2 * (4 * A) ≤ h := by nlinarith
    have h3 : c * h ^ 2 ≤ h / (4 * A) := (le_div_iff₀ (by positivity)).mpr h2
    have h4 : h / (4 * A) < h / (2 * A) := div_lt_div_of_pos_left hh (by positivity) (by linarith)
    linarith
  have hh7 : h ^ 7 ≤ h := by
    calc h ^ 7 = h * h ^ 6 := by ring
      _ ≤ h * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hh.le hh1) hh.le
      _ = h := mul_one h
  have hsm : (Ph + A * Kc) * h ^ 7 ≤ 1 / 2 := by
    have h0 : h * (2 * (Ph + A * Kc) + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp hh0b
    have : 0 ≤ Ph + A * Kc := by positivity
    have h1 : (Ph + A * Kc) * h ≤ 1 / 2 := by nlinarith
    calc (Ph + A * Kc) * h ^ 7 ≤ (Ph + A * Kc) * h := mul_le_mul_of_nonneg_left hh7 this
      _ ≤ 1 / 2 := h1
  have hsmall : A * (Writer.B8 A * c ^ 8) * h ^ 7 ≤ 1 / 2 := by
    have : 0 ≤ A * Kc * h ^ 7 := by positivity
    rw [← hE0, ← hPh]; nlinarith
  -- Taylor estimates at `t` and at `τ`
  obtain ⟨hphT, hdT, hddT, hvT⟩ := hB.taylor_defect hX hεδ hc1 hτ0 hτc hτσ hsmall ht
  obtain ⟨hphTτ, hdTτ, hddTτ, -⟩ :=
    hB.taylor_defect hX hεδ hc1 hτ0 hτc hτσ hsmall (right_mem_Icc.mpr hτ0.le)
  rw [← hE0, ← hPh] at hphT hdT hddT hvT hphTτ hdTτ hddTτ
  have hUδ : ∀ Z : Eq × Ev, ‖Z‖ ≤ 2 * ε + Ph * ε * h ^ 7 + A * Kc * ε * h ^ 7 →
      Z ∈ ball 0 δ := by
    intro Z hZ
    refine mem_ball_zero_iff.mpr (lt_of_le_of_lt hZ ?_)
    have : (Ph + A * Kc) * h ^ 7 * ε ≤ 1 / 2 * ε := mul_le_mul_of_nonneg_right hsm hε0
    linarith [hB.δ_pos]
  have hAKc : 0 ≤ A * Kc * ε * h ^ 7 := by positivity
  have hX1 : W.endpoint X τ ∈ ball 0 δ := hUδ _ (by
    show ‖W.phase (W.taylorC X) τ‖ ≤ _
    linarith)
  -- the correction amplitudes
  obtain ⟨hδ2, hδ3⟩ := hB.corr_norms hX1
  have hb := Writer.amp_le hh hh1 hA hε0 hc1 hτ0.le hτc hG00 hG10 (norm_nonneg _) (norm_nonneg _)
    (hδ2.trans hdTτ)
    (hδ3.trans (add_le_add (mul_le_mul_of_nonneg_left hdTτ hM.le) hddTτ))
  rw [← hBc] at hb
  have hcorr := fun j n hj hn => Writer.corr_le W hh hcmm0 hcmm1
    ((mul_le_mul_of_nonneg_right hcmm (by positivity)).trans hτm) hKHj hKH0
    (W.corr2 X τ) (W.corr3 X τ) hb hBc0 hε0 j n hj hn ht
  rw [← hKc] at hcorr
  have hc0 := hcorr 0 9 (by norm_num) (by norm_num)
  have hc1' := hcorr 1 7 (by norm_num) (by norm_num)
  have hc2 := hcorr 2 5 (by norm_num) (by norm_num)
  have hc3 := hcorr 3 3 (by norm_num) (by norm_num)
  -- assembly with `Q_X = T_X + correction`
  have hQ : W.hermiteC X τ = W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ) := rfl
  rw [hQ]
  have hph := hB.phase_corr_le (T := W.taylorC X) hε0 hKc0 hc0 hc1'
  have hvel := hB.phaseVel_corr_le (T := W.taylorC X) hε0 hKc0 hc1' hc2
  have hTU : W.phase (W.taylorC X) t ∈ ball 0 δ := hUδ _ (by linarith)
  have hQU : W.phase (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t ∈
      ball 0 δ := by
    refine hUδ _ ?_
    calc ‖W.phase (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t‖
        = ‖W.phase (W.taylorC X) t + (W.phase (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phase (W.taylorC X) t)‖ := by
          congr 1; abel
      _ ≤ ‖W.phase (W.taylorC X) t‖ + ‖W.phase (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phase (W.taylorC X) t‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith
  have hD := hB.defect_corr_le hε0 hKc0 hTU hQU hdT hc2 hph
  have hDD := hB.defectDeriv_corr_le hε0 hε1 hKc0 hPh0 hTU hQU hddT hvT hc3 hph hvel
  have hQn : ‖W.phase (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t‖ ≤
      3 * ε := by
    calc ‖W.phase (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t‖
        = ‖W.phase (W.taylorC X) t + (W.phase (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phase (W.taylorC X) t)‖ := by
          congr 1; abel
      _ ≤ ‖W.phase (W.taylorC X) t‖ + ‖W.phase (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phase (W.taylorC X) t‖ :=
          norm_add_le _ _
      _ ≤ 3 * ε := by
          have : (Ph + A * Kc) * h ^ 7 * ε ≤ 1 / 2 * ε := mul_le_mul_of_nonneg_right hsm hε0
          nlinarith
  have hQv : ‖W.phaseVel (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t‖ ≤
      C3 * h⁻¹ * ε := by
    have h5 : h ^ 5 ≤ h⁻¹ := (pow_le_one₀ hh.le hh1).trans (one_le_inv₀ hh |>.mpr hh1)
    calc ‖W.phaseVel (W.taylorC X + hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t‖
        = ‖W.phaseVel (W.taylorC X) t + (W.phaseVel (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phaseVel (W.taylorC X) t)‖ := by
          congr 1; abel
      _ ≤ ‖W.phaseVel (W.taylorC X) t‖ + ‖W.phaseVel (W.taylorC X +
            hermiteCorrection τ (W.corr2 X τ) (W.corr3 X τ)) t - W.phaseVel (W.taylorC X) t‖ :=
          norm_add_le _ _
      _ ≤ (2 * A + Ph) * h⁻¹ * ε + A * Kc * ε * h ^ 5 := add_le_add hvT hvel
      _ ≤ C3 * h⁻¹ * ε := by
          have : A * Kc * ε * h ^ 5 ≤ A * Kc * ε * h⁻¹ :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
          nlinarith
  refine ⟨hQU, hD.trans ?_, W.hasDerivAt_defect hB.deriv.contDiffOn hQU, hDD.trans ?_, hQn,
    hQv.trans ?_⟩
  · have : 0 ≤ ε * h ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_right (show C1 ≤ C1 + C2 + C3 by linarith) this
    linarith [show C1 * ε * h ^ 5 = C1 * (ε * h ^ 5) by ring,
      show (C1 + C2 + C3) * ε * h ^ 5 = (C1 + C2 + C3) * (ε * h ^ 5) by ring]
  · have : 0 ≤ ε * h ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right (show C2 ≤ C1 + C2 + C3 by linarith) this
    linarith [show C2 * ε * h ^ 3 = C2 * (ε * h ^ 3) by ring,
      show (C1 + C2 + C3) * ε * h ^ 3 = (C1 + C2 + C3) * (ε * h ^ 3) by ring]
  · have : 0 ≤ h⁻¹ * ε := by positivity
    have := mul_le_mul_of_nonneg_right (show C3 ≤ C1 + C2 + C3 by linarith) this
    linarith [show C3 * h⁻¹ * ε = C3 * (h⁻¹ * ε) by ring,
      show (C1 + C2 + C3) * h⁻¹ * ε = (C1 + C2 + C3) * (h⁻¹ * ε) by ring]

/-- **`lem:supp-open-hermite-residual`** (complete Taylor–Hermite residual), abstract form.
Fix `A ≥ 1` and `0 < c₋, c₊`.  There are `h₀ > 0` and `C`, depending only on `(A, c₋, c₊)`,
such that for every second-order writer with the inverse-mesh bounds `W.Bounds h A δ`
(`eq:supp-open-local-vector-bounds` with constant `A`, mesh `h ≤ h₀`), every source `X` with
`‖X‖ ≤ ε ≤ δ/4` and every step `c₋h² ≤ τ ≤ c₊h²`, the endpoint-corrected Taylor–Hermite
polynomial `Q_X` (`hermiteC X τ`) satisfies on the complete interval `[0, τ]`:
`Q_X` stays in the chart (`(Q_X, Q_X') ∈ ball 0 δ`), its actual defect
`f_X = Q_X'' − V(Q_X, Q_X')` obeys `‖f_X(t)‖ ≤ C ε h⁵`, it is differentiable with
`∂_t f_X = Q_X⁽³⁾ − DV(Q_X, Q_X')[(Q_X', Q_X'')]` and `‖∂_t f_X(t)‖ ≤ C ε h³`
(`eq:supp-open-hermite-local-defect`; the bound holds in the velocity norm itself, the
manuscript retains a weaker norm for the derivative). -/
theorem hermite_residual (A cm cp : ℝ) (hA : 1 ≤ A) (hcm : 0 < cm) (hcp : 0 < cp) :
    ∃ h₀ > 0, ∃ C ≥ 0, ∀ {Eq : Type uq} {Ev : Type uv} [NormedAddCommGroup Eq]
      [NormedSpace ℝ Eq] [CompleteSpace Eq] [NormedAddCommGroup Ev] [NormedSpace ℝ Ev]
      [CompleteSpace Ev] (W : Writer Eq Ev) (h δ : ℝ), W.Bounds h A δ → h ≤ h₀ →
      ∀ (X : Eq × Ev) (ε τ : ℝ), ‖X‖ ≤ ε → 4 * ε ≤ δ → cm * h ^ 2 ≤ τ → τ ≤ cp * h ^ 2 →
      ∀ t ∈ Icc 0 τ, W.phase (W.hermiteC X τ) t ∈ ball 0 δ ∧
        ‖W.defect (W.hermiteC X τ) t‖ ≤ C * ε * h ^ 5 ∧
        HasDerivAt (W.defect (W.hermiteC X τ)) (W.defectDeriv (W.hermiteC X τ) t) t ∧
        ‖W.defectDeriv (W.hermiteC X τ) t‖ ≤ C * ε * h ^ 3 := by
  obtain ⟨h₀, hh₀, C, hC, hres⟩ := hermite_residual_full.{uq, uv} A cm cp hA hcm hcp
  exact ⟨h₀, hh₀, C, hC, fun W h δ hB hh X ε τ hX hεδ hτm hτp t ht =>
    let H := hres W h δ hB hh X ε τ hX hεδ hτm hτp t ht
    ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩⟩

end

end RenewalGeometry.TaylorHermiteResidual
