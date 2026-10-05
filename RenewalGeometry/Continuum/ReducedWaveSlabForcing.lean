/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabDifference

/-!
# The `H^{s-2}` forcing bound for the difference of two reduced-wave solutions

For two metrics with the hypotheses of `thm:hyperbolic` (`MetricHyp`, common constants, order
`s = k + 2`, `k ≥ 3`), the forcing `F_{h,j}` of the difference system
(`ReducedWaveSlabDifference.lean`) satisfies, at every time of the slab (`forcing_Q_le`),

`Q_k(F_c) ≤ c₁ W (1 + Q_k(𝒮ⱼ,c)) + c₂ Q_k(𝒮ₕ,c - 𝒮ⱼ,c)`,
`W = Σ_c (Q_{k+1}(g_h,c - g_j,c) + Q_k(∂ₜg_h,c - ∂ₜg_j,c))`

(the squared `H^{s-1} × H^{s-2}` difference norm), with `c₁, c₂` depending only on the common
constants — "at one derivative below the a priori bound `H^{s-2}` is an algebra … the forcing,
apart from `𝒮_h - 𝒮_j`, has `H^{s-2}` norm bounded by `a_{h,j}(‖w‖_{H^{s-1}} + ‖∂ₜw‖_{H^{s-2}})`".

* `exists_Vbound` — uniform `H^k` bounds of the variables `(q, g⁻¹, g, ∂g, θ)`;
* `Q_gi_diff_le`, `Q_q_diff_le`, `DV_le` — the variable differences are controlled by `W`
  (`g_h⁻¹ - g_j⁻¹ = g_h⁻¹(g_j - g_h)g_j⁻¹`, `q_h - q_j = q_h q_j (g_j^{00} - g_h^{00})`);
* `forcing_Q_le` — the forcing bound.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]
variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {T a0 lam Λ K0 : ℝ}

/-- The squared `H^{s-1} × H^{s-2}` norm of the difference (`k = s - 2`). -/
def Wn (k : ℕ) (g g' : Idx → X → ℝ) (t : ℝ) : ℝ :=
  ∑ c, (Q (k + 1) (wdiff g g' c) t + Q k (pd (wdiff g g' c) 0) t)

theorem Wn_nonneg (k : ℕ) (g g' : Idx → X → ℝ) (t : ℝ) : 0 ≤ Wn k g g' t :=
  Finset.sum_nonneg fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _)

theorem Q_w_le_Wn (k : ℕ) (g g' : Idx → X → ℝ) (t : ℝ) (c : Idx) :
    Q (k + 1) (wdiff g g' c) t ≤ Wn k g g' t :=
  (le_add_of_nonneg_right (Q_nonneg _ _ _)).trans
    (Finset.single_le_sum (f := fun c => Q (k + 1) (wdiff g g' c) t +
      Q k (pd (wdiff g g' c) 0) t) (fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _))
      (Finset.mem_univ c))

theorem Q_wt_le_Wn (k : ℕ) (g g' : Idx → X → ℝ) (t : ℝ) (c : Idx) :
    Q k (pd (wdiff g g' c) 0) t ≤ Wn k g g' t :=
  (le_add_of_nonneg_left (Q_nonneg _ _ _)).trans
    (Finset.single_le_sum (f := fun c => Q (k + 1) (wdiff g g' c) t +
      Q k (pd (wdiff g g' c) 0) t) (fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _))
      (Finset.mem_univ c))

theorem Wn_comm {k : ℕ} {g g' : Idx → X → ℝ} (hg : ∀ c, ContDiff ℝ ∞ (g c))
    (hg' : ∀ c, ContDiff ℝ ∞ (g' c)) {t : ℝ} : Wn k g' g t = Wn k g g' t := by
  unfold Wn
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : Q (k + 1) (wdiff g' g c) t = Q (k + 1) (wdiff g g' c) t :=
    Q_sub_comm _ (hg' c) (hg c) t
  have e2 : Q k (pd (wdiff g' g c) 0) t = Q k (pd (wdiff g g' c) 0) t := by
    rw [pd_wdiff hg' hg, pd_wdiff hg hg']
    exact Q_sub_comm _ (contDiff_pd_top (hg' c) 0) (contDiff_pd_top (hg c) 0) t
  rw [e1, e2]

namespace MetricHyp

variable {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}

theorem hst' (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) {t : ℝ} (ht : t ∈ Icc 0 T)
    (c : Idx) : Q (k + 1) (pd (g c) 0) t ≤ K0 := by
  have := h.hst t ht c
  simpa using this

theorem K0_nonneg (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) (hT : 0 ≤ T) : 0 ≤ K0 :=
  (Q_nonneg _ _ _).trans (h.hsg 0 ⟨le_rfl, hT⟩ (0, 0))

end MetricHyp

/-! ### Uniform bounds of the variables -/

/-- The background fields are uniformly bounded in `H^k` on `[0, T]`. -/
theorem exists_Btheta (k : ℕ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) :
    ∃ Bθ : ℝ, 0 ≤ Bθ ∧ ∀ t ∈ Icc 0 T, ∀ j, Q k (θ j) t ≤ Bθ := by
  have : ∀ j, ∃ C, ∀ t ∈ Icc 0 T, ‖Q k (θ j) t‖ ≤ C := fun j =>
    isCompact_Icc.exists_bound_of_continuousOn (continuous_Q k (hθ j)).continuousOn
  choose C hC using this
  refine ⟨∑ j, |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht j => ?_⟩
  have h1 := hC j t ht
  rw [Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))))

/-- The uniform `H^k` bound of the variables. -/
def BV (k : ℕ) (CS K0 Λ a0 Bθ : ℝ) : ℝ :=
  (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2 +
    (wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2 + K0 + Bθ

theorem BV_nonneg (k : ℕ) {CS K0 Λ a0 Bθ : ℝ} (hK : 0 ≤ K0) (hB : 0 ≤ Bθ) :
    0 ≤ BV k CS K0 Λ a0 Bθ := by
  unfold BV; positivity

theorem MetricHyp.Q_q_le {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Q k (lapseInv a0 gi) t ≤ (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2 := by
  have hΛ : 0 ≤ Λ := le_trans ha.le (h.Λ_pos ha hT.le)
  have := h.derivBound_q ha hCS hsup (by omega) hΛ
  simp only [Nat.add_sub_cancel] at this
  exact Q_le_of_bound (h.sq ha) (slice_bound_of_derivBound this ht)

theorem MetricHyp.Q_gi_le {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {t : ℝ} (ht : t ∈ Icc 0 T) (a b : Fin 4) :
    Q k (gi a b) t ≤ (wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2 := by
  have hΛ : 0 ≤ Λ := le_trans ha.le (h.Λ_pos ha hT.le)
  have := h.derivBound_gi hCS hsup (by omega) hΛ a b
  simp only [Nat.add_sub_cancel] at this
  exact Q_le_of_bound (h.sgi a b) (slice_bound_of_derivBound this ht)

theorem MetricHyp.Vbound {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {Bθ : ℝ} (hBθ0 : 0 ≤ Bθ)
    (hBθ : ∀ t ∈ Icc 0 T, ∀ j, Q k (θ j) t ≤ Bθ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ v, Q k (Vfam a0 θ g gi v) t ≤ BV k CS K0 Λ a0 Bθ := by
  have hK := h.K0_nonneg hT.le
  have h1 := h.Q_q_le hT ha hCS hsup ht
  have h2 := fun a b => h.Q_gi_le hT ha hCS hsup ht a b
  have hq0 : 0 ≤ (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2 := by positivity
  have hg0 : 0 ≤ (wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2 := by positivity
  unfold BV
  intro v
  rcases v with _ | ab | c | cμ | j
  · show Q k (lapseInv a0 gi) t ≤ _; linarith
  · show Q k (gi ab.1 ab.2) t ≤ _; linarith [h2 ab.1 ab.2]
  · show Q k (g c) t ≤ _
    have := (Q_mono (k := k) (k' := k + 2) (by omega) (g c) t).trans (h.hsg t ht c); linarith
  · show Q k (pd (g cμ.1) cμ.2) t ≤ _
    obtain ⟨c, μ⟩ := cμ
    induction μ using Fin.cases with
    | zero =>
      have := (Q_mono (k := k) (k' := k + 1) (by omega) _ t).trans (h.hst' ht c); linarith
    | succ i =>
      have := (Q_pd_le (k := k) i (g c) t).trans ((Q_mono (k := k + 1) (k' := k + 2) (by omega)
        (g c) t).trans (h.hsg t ht c))
      linarith
  · show Q k (θ j) t ≤ _; linarith [hBθ t ht j]

/-! ### Differences of the variables -/

/-- `H - H' = H (G' - G) H'` for inverse matrices. -/
theorem inv_sub_inv_eq {n : ℕ} {G G' H H' : Matrix (Fin n) (Fin n) ℝ} (h1 : G * H = 1)
    (h2 : G' * H' = 1) : H - H' = H * (G' - G) * H' := by
  have h3 : H * G = 1 := mul_eq_one_comm.mp h1
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc H G' H', h2, Matrix.mul_one, h3,
    Matrix.one_mul]

theorem gi_sub_eq {k : ℕ} {g g' : Idx → X → ℝ} {gi gi' : Fin 4 → Fin 4 → X → ℝ}
    {S S' : Idx → X → ℝ} (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S)
    (h' : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S') {x : X} (hx : x 0 ∈ Icc 0 T)
    (a b : Fin 4) :
    gi a b x - gi' a b x =
      ∑ c, ∑ e, gi a c x * (g' (c, e) x - g (c, e) x) * gi' e b x := by
  have e := inv_sub_inv_eq (G := Matrix.of fun a c => g (a, c) x)
    (H := Matrix.of fun a b => gi a b x) (G' := Matrix.of fun a c => g' (a, c) x)
    (H' := Matrix.of fun a b => gi' a b x)
    (by ext a b; simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]; exact h.inv x hx a b)
    (by ext a b; simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]; exact h'.inv x hx a b)
  have := congrFun (congrFun e a) b
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply] at this
  rw [this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]

/-- The constant of `Q_gi_diff_le`. -/
def cgi (k : ℕ) (CS K0 Λ : ℝ) : ℝ :=
  256 * (algC 3 k CS * (algC 3 k CS * ((wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2)) *
    ((wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2))

theorem Q_gi_diff_le {k : ℕ} (hk : 3 ≤ k) {g g' : Idx → X → ℝ}
    {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S)
    (h' : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S') (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {t : ℝ} (ht : t ∈ Icc 0 T) (a b : Fin 4) :
    Q k (fun x => gi a b x - gi' a b x) t ≤ cgi k CS K0 Λ * Wn k g g' t := by
  set Ca := algC 3 k CS
  have hCa : 0 ≤ Ca := algC_nonneg k hCS
  set Bg := (wordsLE 3 k).card * MetricHyp.Cgi (k + 2) CS K0 Λ ^ 2
  have hBg : 0 ≤ Bg := by positivity
  have hk2 : 2 * 2 ≤ k + 1 := by omega
  -- smoothness / periodicity of the terms
  have sterm : ∀ c e, ContDiff ℝ ∞ (fun x => gi a c x * (g' (c, e) x - g (c, e) x) * gi' e b x) :=
    fun c e => ((h.sgi a c).mul ((h'.sg _).sub (h.sg _))).mul (h'.sgi e b)
  rw [Q_congr_slab ((h.sgi a b).sub (h'.sgi a b))
    (ContDiff.sum fun c _ => ContDiff.sum fun e _ => sterm c e)
    (fun x hx => gi_sub_eq h h' hx a b) k ht]
  refine (Q_sum_le k Finset.univ (fun c => ContDiff.sum fun e _ => sterm c e) t).trans ?_
  have hterm : ∀ c e, Q k (fun x => gi a c x * (g' (c, e) x - g (c, e) x) * gi' e b x) t ≤
      Ca * (Ca * Bg) * Bg * Wn k g g' t := by
    intro c e
    have pw : IsSPeriodic fun x => g' (c, e) x - g (c, e) x := fun k' x => by
      show g' (c, e) _ - g (c, e) _ = _
      rw [h.pg (c, e) k' x, h'.pg (c, e) k' x]
    have m1 := Q_mul_le hk2 hCS hsup ((h.sgi a c).mul ((h'.sg (c, e)).sub (h.sg (c, e))))
      (h'.sgi e b) (isSPeriodic_mul (h.pgi a c) pw) (h'.pgi e b) t
    have m2 := Q_mul_le hk2 hCS hsup (h.sgi a c) ((h'.sg (c, e)).sub (h.sg (c, e))) (h.pgi a c)
      pw t
    have hw : Q k (fun x => g' (c, e) x - g (c, e) x) t ≤ Wn k g g' t := by
      rw [Q_sub_comm k (h'.sg _) (h.sg _)]
      exact (Q_mono (Nat.le_succ k) _ t).trans (Q_w_le_Wn k g g' t (c, e))
    have q1 := h.Q_gi_le hT ha hCS hsup ht a c
    have q2 := h'.Q_gi_le hT ha hCS hsup ht e b
    have n1 := Q_nonneg k (gi a c) t
    have n2 := Q_nonneg k (fun x => g' (c, e) x - g (c, e) x) t
    have n3 := Q_nonneg k (gi' e b) t
    have n4 := Q_nonneg k (fun x => gi a c x * (g' (c, e) x - g (c, e) x)) t
    calc _ ≤ Ca * Q k (fun x => gi a c x * (g' (c, e) x - g (c, e) x)) t * Q k (gi' e b) t := m1
      _ ≤ Ca * (Ca * Q k (gi a c) t * Q k (fun x => g' (c, e) x - g (c, e) x) t) * Bg := by
          gcongr
      _ ≤ Ca * (Ca * Bg * Wn k g g' t) * Bg := by gcongr
      _ = Ca * (Ca * Bg) * Bg * Wn k g g' t := by ring
  have hW := Wn_nonneg k g g' t
  calc (Finset.univ : Finset (Fin 4)).card * ∑ c, Q k (fun x => ∑ e, gi a c x *
        (g' (c, e) x - g (c, e) x) * gi' e b x) t ≤
      4 * ∑ _c : Fin 4, 4 * ∑ _e : Fin 4, Ca * (Ca * Bg) * Bg * Wn k g g' t := by
        rw [Finset.card_univ, Fintype.card_fin]
        push_cast
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by norm_num)
        refine (Q_sum_le k Finset.univ (fun e => sterm c e) t).trans ?_
        rw [Finset.card_univ, Fintype.card_fin]
        push_cast
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hterm c e) (by norm_num)
    _ = cgi k CS K0 Λ * Wn k g g' t := by
        rw [show cgi k CS K0 Λ = 256 * (Ca * (Ca * Bg) * Bg) from rfl]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        ring

/-- The constant of `Q_q_diff_le`. -/
def cq (k : ℕ) (CS K0 Λ a0 : ℝ) : ℝ :=
  algC 3 k CS * ((wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2) *
    (algC 3 k CS * ((wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2) * cgi k CS K0 Λ)

theorem Q_q_diff_le {k : ℕ} (hk : 3 ≤ k) {g g' : Idx → X → ℝ}
    {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S)
    (h' : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S') (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Q k (fun x => lapseInv a0 gi x - lapseInv a0 gi' x) t ≤ cq k CS K0 Λ a0 * Wn k g g' t := by
  set Ca := algC 3 k CS
  have hCa : 0 ≤ Ca := algC_nonneg k hCS
  set Bq := (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2
  have hk2 : 2 * 2 ≤ k + 1 := by omega
  have sd' : ContDiff ℝ ∞ fun x => gi' 0 0 x - gi 0 0 x := (h'.sgi 0 0).sub (h.sgi 0 0)
  have pd' : IsSPeriodic fun x => gi' 0 0 x - gi 0 0 x := fun k' x => by
    simp only [h.pgi 0 0 k' x, h'.pgi 0 0 k' x]
  have e : ∀ x : X, x 0 ∈ Icc 0 T → lapseInv a0 gi x - lapseInv a0 gi' x =
      lapseInv a0 gi x * (lapseInv a0 gi' x * (gi' 0 0 x - gi 0 0 x)) := fun x hx => by
    have h1 := h.q_mul ha hx; have h2 := h'.q_mul ha hx
    linear_combination lapseInv a0 gi' x * h1 - lapseInv a0 gi x * h2
  rw [Q_congr_slab ((h.sq ha).sub (h'.sq ha)) ((h.sq ha).mul ((h'.sq ha).mul sd')) e k ht]
  have m1 := Q_mul_le hk2 hCS hsup (h.sq ha) ((h'.sq ha).mul sd') h.pq
    (fun k' x => by simp only [h'.pq k' x, pd' k' x]) t
  have m2 := Q_mul_le hk2 hCS hsup (h'.sq ha) sd' h'.pq pd' t
  have hd : Q k (fun x => gi' 0 0 x - gi 0 0 x) t ≤ cgi k CS K0 Λ * Wn k g' g t :=
    Q_gi_diff_le hk h' h hT ha hCS hsup ht 0 0
  have hWs : Wn k g' g t = Wn k g g' t := Wn_comm h.sg h'.sg
  rw [hWs] at hd
  have q1 := h.Q_q_le hT ha hCS hsup ht
  have q2 := h'.Q_q_le hT ha hCS hsup ht
  have n1 := Q_nonneg k (lapseInv a0 gi) t
  have n2 := Q_nonneg k (lapseInv a0 gi') t
  have n3 := Q_nonneg k (fun x => gi' 0 0 x - gi 0 0 x) t
  have n4 := Q_nonneg k (fun x => lapseInv a0 gi' x * (gi' 0 0 x - gi 0 0 x)) t
  have hW := Wn_nonneg k g g' t
  have hBq : 0 ≤ Bq := by positivity
  calc _ ≤ Ca * Q k (lapseInv a0 gi) t * Q k (fun x => lapseInv a0 gi' x *
        (gi' 0 0 x - gi 0 0 x)) t := m1
    _ ≤ Ca * Bq * (Ca * Q k (lapseInv a0 gi') t * Q k (fun x => gi' 0 0 x - gi 0 0 x) t) := by
        gcongr
    _ ≤ Ca * Bq * (Ca * Bq * (cgi k CS K0 Λ * Wn k g g' t)) := by gcongr
    _ = cq k CS K0 Λ a0 * Wn k g g' t := by unfold cq; ring

/-- The constant of `DV_le`. -/
def cD (κ : Type) [Fintype κ] (k : ℕ) (CS K0 Λ a0 : ℝ) : ℝ :=
  Fintype.card (Option (NV κ)) * (cq k CS K0 Λ a0 + cgi k CS K0 Λ + 1)

theorem cgi_nonneg (k : ℕ) {CS K0 Λ : ℝ} (hCS : 0 ≤ CS) : 0 ≤ cgi k CS K0 Λ := by
  unfold cgi; have := algC_nonneg (d := 3) k hCS; positivity

theorem cq_nonneg (k : ℕ) {CS K0 Λ a0 : ℝ} (hCS : 0 ≤ CS) : 0 ≤ cq k CS K0 Λ a0 := by
  unfold cq; have := algC_nonneg (d := 3) k hCS; have := cgi_nonneg k (K0 := K0) (Λ := Λ) hCS
  positivity

/-- **The differences of the variables are controlled by `W`**:
`Σ_v Q_k(V_h,v - V_j,v) ≤ c_D W`. -/
theorem DV_le {k : ℕ} (hk : 3 ≤ k) {g g' : Idx → X → ℝ}
    {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S)
    (h' : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S') (hT : 0 < T) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∑ v, Q k (fun x => Vfam a0 θ g gi v x - Vfam a0 θ g' gi' v x) t ≤
      cD κ k CS K0 Λ a0 * Wn k g g' t := by
  have hW := Wn_nonneg k g g' t
  have h1 := cq_nonneg k (K0 := K0) (Λ := Λ) (a0 := a0) hCS
  have h2 := cgi_nonneg k (K0 := K0) (Λ := Λ) hCS
  have hv : ∀ v, Q k (fun x => Vfam a0 θ g gi v x - Vfam a0 θ g' gi' v x) t ≤
      (cq k CS K0 Λ a0 + cgi k CS K0 Λ + 1) * Wn k g g' t := by
    intro v
    rcases v with _ | ab | c | cμ | j
    · have := Q_q_diff_le hk h h' hT ha hCS hsup ht
      exact this.trans (by nlinarith)
    · have := Q_gi_diff_le hk h h' hT ha hCS hsup ht ab.1 ab.2
      exact this.trans (by nlinarith)
    · have := (Q_mono (Nat.le_succ k) _ t).trans (Q_w_le_Wn k g g' t c)
      exact this.trans (by nlinarith)
    · obtain ⟨c, μ⟩ := cμ
      show Q k (fun x => pd (g c) μ x - pd (g' c) μ x) t ≤ _
      rw [← pd_wdiff h.sg h'.sg c μ]
      have : Q k (pd (wdiff g g' c) μ) t ≤ Wn k g g' t := by
        induction μ using Fin.cases with
        | zero => exact Q_wt_le_Wn k g g' t c
        | succ i => exact (Q_pd_le i _ t).trans (Q_w_le_Wn k g g' t c)
      exact this.trans (by nlinarith)
    · show Q k (fun x => θ j x - θ j x) t ≤ _
      have e0 : Q k (fun x => θ j x - θ j x) t = 0 := by simp [Q_const]
      rw [e0]; positivity
  calc ∑ v, Q k (fun x => Vfam a0 θ g gi v x - Vfam a0 θ g' gi' v x) t ≤
      ∑ _v : Option (NV κ), (cq k CS K0 Λ a0 + cgi k CS K0 Λ + 1) * Wn k g g' t :=
        Finset.sum_le_sum fun v _ => hv v
    _ = cD κ k CS K0 Λ a0 * Wn k g g' t := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cD]; ring

theorem MetricHyp.Q_U_le {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) {t : ℝ}
    (ht : t ∈ Icc 0 T) (c : Idx) (i : Fin 3) :
    Q k (pd (pd (g c) 0) i.succ) t ≤ K0 :=
  (Q_pd_le i _ t).trans (h.hst' ht c)

theorem MetricHyp.Q_V_le {k : ℕ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S) {t : ℝ}
    (ht : t ∈ Icc 0 T) (c : Idx) (i j : Fin 3) :
    Q k (pd (pd (g c) j.succ) i.succ) t ≤ K0 :=
  (Q_pd_le i _ t).trans ((Q_pd_le j _ t).trans (h.hsg t ht c))

/-- **The `H^{s-2}` forcing bound** (`thm:hyperbolic`, proof): there are constants `c₁, c₂`,
depending only on the common constants, such that for any two metrics with the hypotheses,
`Q_k(F_c) ≤ c₁ W (1 + Q_k(𝒮ⱼ,c)) + c₂ Q_k(𝒮ₕ,c - 𝒮ⱼ,c)` on `[0, T]`. -/
theorem forcing_Q_le {k : ℕ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 ≤ lam)
    (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S →
      MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T, ∀ c,
      Q k (fdiff a0 gi g g' c) t ≤
        c₁ * Wn k g g' t * (1 + Q k (S' c) t) + c₂ * Q k (fun x => S c x - S' c x) t := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  obtain ⟨Bθ, hBθ0, hBθ⟩ := exists_Btheta (T := T) k hθ
  have hk2 : 2 * 2 ≤ k + 1 := by omega
  set B := BV k CS K0 Λ a0 Bθ
  have hB : 0 ≤ B := BV_nonneg k hK0 hBθ0
  have lipβ := fun i : Fin 3 => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup (betaP i) hB
  have lipγ := fun ij : Fin 3 × Fin 3 => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup
    (gammaP ij.1 ij.2) hB
  have lipψ := fun c : Idx => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup (psiP Np c) hB
  choose Bβ Lβ hBβ hLβ lβ using lipβ
  choose Bγ Lγ hBγ hLγ lγ using lipγ
  choose Bψ Lψ hBψ hLψ lψ using lipψ
  set Ca := algC 3 k CS
  have hCa : 0 ≤ Ca := algC_nonneg k hCS
  set LB := ∑ i, Lβ i
  set LG := ∑ ij, Lγ ij
  set LP := ∑ c, Lψ c
  have hLB : 0 ≤ LB := Finset.sum_nonneg fun i _ => hLβ i
  have hLG : 0 ≤ LG := Finset.sum_nonneg fun i _ => hLγ i
  have hLP : 0 ≤ LP := Finset.sum_nonneg fun i _ => hLψ i
  set cd := cD κ k CS K0 Λ a0
  have hcd : 0 ≤ cd := by
    simp only [cd, cD]
    have := cq_nonneg k (K0 := K0) (Λ := Λ) (a0 := a0) hCS
    have := cgi_nonneg k (K0 := K0) (Λ := Λ) hCS
    positivity
  set Bq := (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2
  have hBq : 0 ≤ Bq := by positivity
  set cqq := cq k CS K0 Λ a0
  have hcqq : 0 ≤ cqq := cq_nonneg k hCS
  refine ⟨8 * (36 * Ca * LB * cd * K0) + 8 * (81 * Ca * LG * cd * K0) + 4 * (LP * cd) +
      2 * (2 * Ca * cqq), 2 * (2 * Ca * Bq), by positivity, by positivity,
    fun g g' gi gi' S S' h h' t ht c => ?_⟩
  -- the inputs of the Lipschitz estimates
  set V := Vfam a0 θ g gi
  set V' := Vfam a0 θ g' gi'
  set D := ∑ v, Q k (fun x => V v x - V' v x) t
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun v _ => Q_nonneg _ _ _
  have hDv : ∀ v, Q k (fun x => V v x - V' v x) t ≤ D := fun v =>
    Finset.single_le_sum (f := fun v => Q k (fun x => V v x - V' v x) t)
      (fun v _ => Q_nonneg _ _ _) (Finset.mem_univ v)
  have hDW : D ≤ cd * Wn k g g' t := DV_le hk h h' hT ha hCS hsup ht
  have bV := h.Vbound hT ha hCS hsup hBθ0 hBθ ht
  have bV' := h'.Vbound hT ha hCS hsup hBθ0 hBθ ht
  have hW := Wn_nonneg k g g' t
  -- the four parts of the forcing
  have sβ := h.sbeta ha
  have sβ' := h'.sbeta ha
  have sγ := h.sgamma ha
  have sγ' := h'.sgamma ha
  have sU : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (pd (g' c) 0) i.succ) := fun i =>
    contDiff_pd_top (contDiff_pd_top (h'.sg c) 0) _
  have sVV : ∀ i j : Fin 3, ContDiff ℝ ∞ (pd (pd (g' c) j.succ) i.succ) := fun i j =>
    contDiff_pd_top (contDiff_pd_top (h'.sg c) _) _
  have pU : ∀ i : Fin 3, IsSPeriodic (pd (pd (g' c) 0) i.succ) := fun i =>
    isSPeriodic_pd (isSPeriodic_pd (h'.pg c) 0) _
  have pVV : ∀ i j : Fin 3, IsSPeriodic (pd (pd (g' c) j.succ) i.succ) := fun i j =>
    isSPeriodic_pd (isSPeriodic_pd (h'.pg c) _) _
  set A : X → ℝ := fun x => 2 * ∑ i : Fin 3, (betaF (lapseInv a0 gi) gi i x -
    betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x
  set Bf : X → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, (gammaF (lapseInv a0 gi) gi i j x -
    gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x
  set C : X → ℝ := fun x => psiF a0 Np θ g gi c x - psiF a0 Np θ g' gi' c x
  set Df : X → ℝ := fun x => lapseInv a0 gi x * S c x - lapseInv a0 gi' x * S' c x
  have sAi : ∀ i : Fin 3, ContDiff ℝ ∞ fun x => (betaF (lapseInv a0 gi) gi i x -
      betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x := fun i =>
    ((sβ i).sub (sβ' i)).mul (sU i)
  have sBij : ∀ i j : Fin 3, ContDiff ℝ ∞ fun x => (gammaF (lapseInv a0 gi) gi i j x -
      gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x := fun i j =>
    ((sγ i j).sub (sγ' i j)).mul (sVV i j)
  have sA : ContDiff ℝ ∞ A := contDiff_const.mul (ContDiff.sum fun i _ => sAi i)
  have sB : ContDiff ℝ ∞ Bf := ContDiff.sum fun i _ => ContDiff.sum fun j _ => sBij i j
  have sC : ContDiff ℝ ∞ C := (h.spsi ha c).sub (h'.spsi ha c)
  have sD : ContDiff ℝ ∞ Df := ((h.sq ha).mul (h.sS c)).sub ((h'.sq ha).mul (h'.sS c))
  -- the forcing equals `A + B + C + D` on the slab
  have hF : Q k (fdiff a0 gi g g' c) t = Q k (fun x => A x + Bf x + C x + Df x) t := by
    have sF := (diffSys_hyp h h' (by omega) hT ha hlam hCS hsup).sF c
    exact Q_congr_slab sF (((sA.add sB).add sC).add sD) (fun x hx => fdiff_eq h h' ha hx c) k ht
  rw [hF]
  have e1 := Q_add_le k ((sA.add sB).add sC) sD t
  have e2 := Q_add_le k (sA.add sB) sC t
  have e3 := Q_add_le k sA sB t
  -- part A
  have hA : Q k A t ≤ 36 * Ca * LB * cd * K0 * Wn k g g' t := by
    have : Q k A t = 2 ^ 2 * Q k (fun x => ∑ i : Fin 3, (betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x) t :=
      Q_const_mul k (ContDiff.sum fun i _ => sAi i) 2 t
    rw [this]
    have hs := Q_sum_le k Finset.univ sAi t
    rw [Finset.card_univ, Fintype.card_fin] at hs
    have hterm : ∀ i : Fin 3, Q k (fun x => (betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x) t ≤
        Ca * (LB * cd * Wn k g g' t) * K0 := by
      intro i
      have pβd : IsSPeriodic fun x => betaF (lapseInv a0 gi) gi i x -
          betaF (lapseInv a0 gi') gi' i x := fun k' x => by
        show betaF _ gi i _ - betaF _ gi' i _ = _
        rw [h.pbeta i k' x, h'.pbeta i k' x]
      have m := Q_mul_le hk2 hCS hsup ((sβ i).sub (sβ' i)) (sU i) pβd (pU i) t
      have hl := (lβ i V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
      rw [evalF_betaP, evalF_betaP] at hl
      have hLi : Lβ i ≤ LB := Finset.single_le_sum (f := Lβ) (fun i _ => hLβ i)
        (Finset.mem_univ i)
      have h1 : Q k (fun x => betaF (lapseInv a0 gi) gi i x - betaF (lapseInv a0 gi') gi' i x) t
          ≤ LB * cd * Wn k g g' t := by
        refine hl.trans ?_
        calc Lβ i * D ≤ LB * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLB
          _ = _ := by ring
      have h2 := h'.Q_U_le ht c i
      have n1 := Q_nonneg k (fun x => betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) t
      have n2 := Q_nonneg k (pd (pd (g' c) 0) i.succ) t
      calc _ ≤ Ca * Q k (fun x => betaF (lapseInv a0 gi) gi i x -
            betaF (lapseInv a0 gi') gi' i x) t * Q k (pd (pd (g' c) 0) i.succ) t := m
        _ ≤ Ca * (LB * cd * Wn k g g' t) * K0 := by gcongr
    calc _ ≤ 2 ^ 2 * (3 * ∑ i : Fin 3, Ca * (LB * cd * Wn k g g' t) * K0) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
          push_cast
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)
      _ = 36 * Ca * LB * cd * K0 * Wn k g g' t := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- part B
  have hBb : Q k Bf t ≤ 81 * Ca * LG * cd * K0 * Wn k g g' t := by
    have hterm : ∀ i j : Fin 3, Q k (fun x => (gammaF (lapseInv a0 gi) gi i j x -
        gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x) t ≤
        Ca * (LG * cd * Wn k g g' t) * K0 := by
      intro i j
      have pγd : IsSPeriodic fun x => gammaF (lapseInv a0 gi) gi i j x -
          gammaF (lapseInv a0 gi') gi' i j x := fun k' x => by
        show gammaF _ gi i j _ - gammaF _ gi' i j _ = _
        rw [h.pgamma i j k' x, h'.pgamma i j k' x]
      have m := Q_mul_le hk2 hCS hsup ((sγ i j).sub (sγ' i j)) (sVV i j) pγd (pVV i j) t
      have hl := (lγ (i, j) V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
      rw [evalF_gammaP, evalF_gammaP] at hl
      have hLi : Lγ (i, j) ≤ LG := Finset.single_le_sum (f := Lγ) (fun i _ => hLγ i)
        (Finset.mem_univ (i, j))
      have h1 : Q k (fun x => gammaF (lapseInv a0 gi) gi i j x -
          gammaF (lapseInv a0 gi') gi' i j x) t ≤ LG * cd * Wn k g g' t := by
        refine hl.trans ?_
        calc Lγ (i, j) * D ≤ LG * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLG
          _ = _ := by ring
      have h2 := h'.Q_V_le ht c i j
      have n1 := Q_nonneg k (fun x => gammaF (lapseInv a0 gi) gi i j x -
        gammaF (lapseInv a0 gi') gi' i j x) t
      have n2 := Q_nonneg k (pd (pd (g' c) j.succ) i.succ) t
      calc _ ≤ Ca * Q k (fun x => gammaF (lapseInv a0 gi) gi i j x -
            gammaF (lapseInv a0 gi') gi' i j x) t * Q k (pd (pd (g' c) j.succ) i.succ) t := m
        _ ≤ Ca * (LG * cd * Wn k g g' t) * K0 := by gcongr
    have hs := Q_sum_le k Finset.univ (fun i => ContDiff.sum (s := Finset.univ) fun j _ => sBij i j) t
    rw [Finset.card_univ, Fintype.card_fin] at hs
    calc Q k Bf t ≤ 3 * ∑ i : Fin 3, (3 * ∑ j : Fin 3, Ca * (LG * cd * Wn k g g' t) * K0) := by
          refine hs.trans ?_
          push_cast
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
          have hs2 := Q_sum_le k Finset.univ (fun j => sBij i j) t
          rw [Finset.card_univ, Fintype.card_fin] at hs2
          refine hs2.trans ?_
          push_cast
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm i j) (by norm_num)
      _ = 81 * Ca * LG * cd * K0 * Wn k g g' t := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- part C
  have hC : Q k C t ≤ LP * cd * Wn k g g' t := by
    have hl := (lψ c V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
    rw [evalF_psiP, evalF_psiP] at hl
    have hLi : Lψ c ≤ LP := Finset.single_le_sum (f := Lψ) (fun i _ => hLψ i) (Finset.mem_univ c)
    refine hl.trans ?_
    calc Lψ c * D ≤ LP * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLP
      _ = _ := by ring
  -- part D
  have hDd : Q k Df t ≤ 2 * Ca * Bq * Q k (fun x => S c x - S' c x) t +
      2 * Ca * cqq * Wn k g g' t * Q k (S' c) t := by
    have e : Df = fun x => lapseInv a0 gi x * (S c x - S' c x) +
        (lapseInv a0 gi x - lapseInv a0 gi' x) * S' c x := by
      funext x; simp only [Df]; ring
    rw [e]
    have sΔ : ContDiff ℝ ∞ fun x => S c x - S' c x := (h.sS c).sub (h'.sS c)
    have pΔ : IsSPeriodic fun x => S c x - S' c x := fun k' x => by
      show S c _ - S' c _ = _; rw [h.pS c k' x, h'.pS c k' x]
    have sqd : ContDiff ℝ ∞ fun x => lapseInv a0 gi x - lapseInv a0 gi' x :=
      (h.sq ha).sub (h'.sq ha)
    have pqd : IsSPeriodic fun x => lapseInv a0 gi x - lapseInv a0 gi' x := fun k' x => by
      show lapseInv a0 gi _ - lapseInv a0 gi' _ = _; rw [h.pq k' x, h'.pq k' x]
    refine (Q_add_le k ((h.sq ha).mul sΔ) (sqd.mul (h'.sS c)) t).trans ?_
    have m1 := Q_mul_le hk2 hCS hsup (h.sq ha) sΔ h.pq pΔ t
    have m2 := Q_mul_le hk2 hCS hsup sqd (h'.sS c) pqd (h'.pS c) t
    have q1 := h.Q_q_le hT ha hCS hsup ht
    have q2 := Q_q_diff_le hk h h' hT ha hCS hsup ht
    have n1 := Q_nonneg k (fun x => S c x - S' c x) t
    have n2 := Q_nonneg k (S' c) t
    have n3 := Q_nonneg k (lapseInv a0 gi) t
    have n4 := Q_nonneg k (fun x => lapseInv a0 gi x - lapseInv a0 gi' x) t
    have b1 : Ca * Q k (lapseInv a0 gi) t * Q k (fun x => S c x - S' c x) t ≤
        Ca * Bq * Q k (fun x => S c x - S' c x) t := by gcongr
    have b2 : Ca * Q k (fun x => lapseInv a0 gi x - lapseInv a0 gi' x) t * Q k (S' c) t ≤
        Ca * (cqq * Wn k g g' t) * Q k (S' c) t := by gcongr
    nlinarith
  have nA := Q_nonneg k A t
  have nB := Q_nonneg k Bf t
  have nC := Q_nonneg k C t
  have nD := Q_nonneg k Df t
  have nS := Q_nonneg k (S' c) t
  have nΔ := Q_nonneg k (fun x => S c x - S' c x) t
  have hWS : 0 ≤ Wn k g g' t * Q k (S' c) t := mul_nonneg hW nS
  calc Q k (fun x => A x + Bf x + C x + Df x) t ≤
      8 * Q k A t + 8 * Q k Bf t + 4 * Q k C t + 2 * Q k Df t := by linarith
    _ ≤ 8 * (36 * Ca * LB * cd * K0 * Wn k g g' t) + 8 * (81 * Ca * LG * cd * K0 * Wn k g g' t) +
        4 * (LP * cd * Wn k g g' t) + 2 * (2 * Ca * Bq * Q k (fun x => S c x - S' c x) t +
          2 * Ca * cqq * Wn k g g' t * Q k (S' c) t) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ 8 * (36 * Ca * LB * cd * K0) + 8 * (81 * Ca * LG * cd * K0) + 4 * (LP * cd) :=
          by positivity
        nlinarith [mul_nonneg this hWS, mul_nonneg (mul_nonneg hCa hcqq) hW]

end ReducedWaveStab

end RenewalGeometry
