/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CubicalInterfaceLifting
import RenewalGeometry.Continuum.DistributionalCurvatureCompactness

/-!
# The jump formula for cellwise `C¹` fields on a cubical mesh
  (`eq:supp-connection-jumps`; emergent-spacetime manuscript, supplement)

Gauss–Green on the uniform cubical mesh of side `h > 0` in `ℝ^{n+1}`: for a field `u` that is
`C¹` on each closed-open cell (`u x = P_{κ(x)}(x)`, `κ(x) = ⌊x/h⌋` the cell label, each `P_k`
globally `C¹`, `P_k = 0` off a finite set of cells), the distributional partial derivative is the
broken (cellwise) derivative plus the face measures of the jumps:
`-∫ ∂_a ψ u = ∫ ψ ∂_a^b u + Σ_{faces f ⊥ e_a} ∫_f ψ [u]_f`, `[u]_f = P_k - P_{k - e_a}` on the face
`f = (a, k)` (the cell `k` lies on the positive side).

* `integral_deriv_smul_floor`: the one-dimensional formula (integration by parts on each
  interval `[m h, (m+1) h]` and summation by parts);
* `cellIndex`, `cellwise`, `brokenPDeriv`, `faceJump`: the cellwise field, its broken partial
  derivative and its face jumps;
* `partial_jump_formula`: the `(n+1)`-dimensional formula (Fubini in normal coordinates);
* `connection_jump_formula`: **`eq:supp-connection-jumps`** for a cellwise `C¹` connection
  `ω = Σ_b ω_b dx^b`: `d_dist ω = d_b ω + Σ_f J_f δ_f` with `J_f = n_f^♭ ∧ [ω]_f`.
-/

open MeasureTheory Filter Topology ENNReal Set
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.CubicalJump

set_option linter.unusedSectionVars false

/-! ### The one-dimensional jump formula -/

section OneDim

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

theorem floor_div_eq_of_mem {h : ℝ} (hh : 0 < h) {m : ℤ} {t : ℝ} (h1 : (m : ℝ) * h ≤ t)
    (h2 : t < ((m : ℝ) + 1) * h) : ⌊t / h⌋ = m := by
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hh]; exact h1
  · rw [div_lt_iff₀ hh]; exact h2

/-- Integration by parts on one interval for a scalar times a vector-valued `C¹` function. -/
theorem integral_deriv_smul_eq {ψ ψ' : ℝ → ℝ} (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ'c : Continuous ψ') {Q Q' : ℝ → A} (hQ : ∀ t, HasDerivAt Q (Q' t) t)
    (hQ'c : Continuous Q') (a b : ℝ) :
    ∫ t in a..b, ψ' t • Q t = ψ b • Q b - ψ a • Q a - ∫ t in a..b, ψ t • Q' t := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  have i1 : IntervalIntegrable (fun t => ψ t • Q' t) volume a b :=
    (hψc.smul hQ'c).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => ψ' t • Q t) volume a b :=
    (hψ'c.smul hQc).intervalIntegrable _ _
  have h1 : ∫ t in a..b, (ψ t • Q' t + ψ' t • Q t) = ψ b • Q b - ψ a • Q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hψ t).smul (hQ t)) (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2] at h1
  rw [← h1]; abel

/-- **One-dimensional jump formula.**  Let `ψ` be `C¹`, vanishing (with its derivative) outside
`(m₀ h, (m₀ + N) h)`, and let `u(t) = Q_{⌊t/h⌋}(t)` with every `Q_m` of class `C¹`.  Then
`-∫ ψ' u = ∫ ψ u'_b + Σ_{j < N} ψ(x_j) (Q_{m₀+j}(x_j) - Q_{m₀+j-1}(x_j))`, `x_j = (m₀ + j) h`. -/
theorem integral_deriv_smul_floor {h : ℝ} (hh : 0 < h) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ'c : Continuous ψ') {Q Q' : ℤ → ℝ → A}
    (hQ : ∀ m t, HasDerivAt (Q m) (Q' m t) t) (hQ'c : ∀ m, Continuous (Q' m)) (m₀ : ℤ) (N : ℕ)
    (hsupp : ∀ t, t ∉ Ioo ((m₀ : ℝ) * h) (((m₀ : ℝ) + N) * h) → ψ t = 0 ∧ ψ' t = 0) :
    -(∫ t, ψ' t • Q ⌊t / h⌋ t) = (∫ t, ψ t • Q' ⌊t / h⌋ t) +
      ∑ j ∈ Finset.range N, ψ (((m₀ : ℝ) + j) * h) •
        (Q (m₀ + j) (((m₀ : ℝ) + j) * h) - Q (m₀ + j - 1) (((m₀ : ℝ) + j) * h)) := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hQc : ∀ m, Continuous (Q m) := fun m =>
    continuous_iff_continuousAt.2 fun t => (hQ m t).continuousAt
  set x : ℕ → ℝ := fun k => ((m₀ : ℝ) + k) * h with hx
  have hxmono : ∀ k, x k ≤ x (k + 1) := fun k => by
    simp only [hx]; push_cast; nlinarith
  -- reduction of a whole-line integral to the adjacent intervals
  have hsplit : ∀ g : ℝ → A, (∀ t, t ∉ Ioo (x 0) (x N) → g t = 0) →
      (∀ k < N, IntervalIntegrable g volume (x k) (x (k + 1))) →
      ∫ t, g t = ∑ k ∈ Finset.range N, ∫ t in x k..x (k + 1), g t := by
    intro g hg hint
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    have hle : x 0 ≤ x N := by
      simp only [hx]; push_cast; nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    rw [intervalIntegral.integral_of_le hle]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hg t fun h' => ?_).symm
    exact ht ⟨h'.1, h'.2.le⟩
  -- on each piece the floor is constant almost everywhere
  have hpiece : ∀ (k : ℕ) (G : ℤ → ℝ → A),
      ∫ t in x k..x (k + 1), G ⌊t / h⌋ t = ∫ t in x k..x (k + 1), G (m₀ + k) t := by
    intro k G
    refine intervalIntegral.integral_congr_ae' ?_ ?_
    · filter_upwards [Measure.ae_ne volume (x (k + 1))] with t hne ht
      have : ⌊t / h⌋ = m₀ + k := by
        apply floor_div_eq_of_mem hh
        · push_cast; exact ht.1.le
        · push_cast
          have := lt_of_le_of_ne ht.2 hne
          simp only [hx] at this; push_cast at this; linarith
      rw [this]
    · exact Eventually.of_forall fun t ht => absurd ht (by
        rw [Set.Ioc_eq_empty (not_lt.2 (hxmono k))]; exact Set.notMem_empty t)
  have hsupp' : ∀ t, t ∉ Ioo (x 0) (x N) → ψ t = 0 ∧ ψ' t = 0 := fun t ht => hsupp t (by
    simpa [hx] using ht)
  -- interval integrability of the two integrands on each piece
  have hint1 : ∀ k < N, IntervalIntegrable (fun t => ψ' t • Q ⌊t / h⌋ t) volume (x k) (x (k + 1)) := by
    intro k _
    have hc : IntervalIntegrable (fun t => ψ' t • Q (m₀ + k) t) volume (x k) (x (k + 1)) :=
      (hψ'c.smul (hQc _)).intervalIntegrable _ _
    refine hc.congr_ae ?_
    rw [Set.uIoc_of_le (hxmono k)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume (x (k + 1)))] with t ht hne
    have : ⌊t / h⌋ = m₀ + k := by
      apply floor_div_eq_of_mem hh
      · push_cast; exact ht.1.le
      · push_cast
        have := lt_of_le_of_ne ht.2 hne
        simp only [hx] at this; push_cast at this; linarith
    simp [this]
  have hint2 : ∀ k < N, IntervalIntegrable (fun t => ψ t • Q' ⌊t / h⌋ t) volume (x k) (x (k + 1)) := by
    intro k _
    have hc : IntervalIntegrable (fun t => ψ t • Q' (m₀ + k) t) volume (x k) (x (k + 1)) :=
      (hψc.smul (hQ'c _)).intervalIntegrable _ _
    refine hc.congr_ae ?_
    rw [Set.uIoc_of_le (hxmono k)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume (x (k + 1)))] with t ht hne
    have : ⌊t / h⌋ = m₀ + k := by
      apply floor_div_eq_of_mem hh
      · push_cast; exact ht.1.le
      · push_cast
        have := lt_of_le_of_ne ht.2 hne
        simp only [hx] at this; push_cast at this; linarith
    simp [this]
  rw [hsplit _ (fun t ht => by simp [(hsupp' t ht).2]) hint1,
    hsplit _ (fun t ht => by simp [(hsupp' t ht).1]) hint2]
  simp only [hpiece _ (fun m t => ψ' t • Q m t), hpiece _ (fun m t => ψ t • Q' m t)]
  have hibp : ∀ k : ℕ, ∫ t in x k..x (k + 1), ψ' t • Q (m₀ + k) t =
      ψ (x (k + 1)) • Q (m₀ + k) (x (k + 1)) - ψ (x k) • Q (m₀ + k) (x k) -
        ∫ t in x k..x (k + 1), ψ t • Q' (m₀ + k) t := fun k =>
    integral_deriv_smul_eq hψ hψ'c (hQ _) (hQ'c _) _ _
  simp only [hibp, Finset.sum_sub_distrib]
  -- summation by parts
  set B : ℕ → A := fun j => ψ (x j) • Q (m₀ + j - 1) (x j) with hB
  have hB0 : B 0 = 0 := by
    simp only [hB, (hsupp' (x 0) fun h' => (lt_irrefl _ h'.1)).1, zero_smul]
  have hBN : B N = 0 := by
    simp only [hB, (hsupp' (x N) fun h' => (lt_irrefl _ h'.2)).1, zero_smul]
  have hshift : ∑ k ∈ Finset.range N, ψ (x (k + 1)) • Q (m₀ + k) (x (k + 1)) =
      ∑ j ∈ Finset.range N, B j := by
    have : ∀ k : ℕ, ψ (x (k + 1)) • Q (m₀ + k) (x (k + 1)) = B (k + 1) := fun k => by
      simp only [hB]; congr 2; push_cast; ring
    simp only [this]
    have h3 := Finset.sum_range_succ' B N
    rw [hB0, add_zero, Finset.sum_range_succ, hBN, add_zero] at h3
    exact h3.symm
  rw [hshift]
  have hx' : ∀ j : ℕ, ((m₀ : ℝ) + j) * h = x j := fun j => rfl
  simp only [hx', smul_sub, Finset.sum_sub_distrib, hB]
  abel

end OneDim

/-! ### Cellwise fields on the cubical mesh -/

section Mesh

open InterfaceLifting

variable {n : ℕ}
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

/-- The label `κ(x) = ⌊x/h⌋` of the closed-open cell containing `x`. -/
def cellIndex (h : ℝ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℤ := fun m => ⌊x m / h⌋

/-- A cellwise field `u(x) = P_{κ(x)}(x)`. -/
def cellwise (h : ℝ) (P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A) (x : Fin (n + 1) → ℝ) : A :=
  P (cellIndex h x) x

/-- The broken (cellwise) partial derivative `∂_a^b u(x) = ∂_a P_{κ(x)}(x)`. -/
def brokenPDeriv (h : ℝ) (P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A) (a : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : A :=
  fderiv ℝ (P (cellIndex h x)) x (Pi.single a 1)

/-- The jump `[u]_f = P_k - P_{k - e_i}` across the face `f = (i, k)` (cell `k` on the positive
side of the normal `e_i`), as a function of the tangential coordinates. -/
def faceJump (h : ℝ) (P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A) (f : Face n)
    (y : Fin n → ℝ) : A :=
  P f.2 (facePoint h f y) - P (f.2 - Pi.single f.1 1) (facePoint h f y)

/-- A cellwise `C¹` family: every piece is globally `C¹` and only finitely many pieces are
nonzero (the cells of a compact chart region). -/
structure IsCellwiseC1 (P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A)
    (S : Finset (Fin (n + 1) → ℤ)) : Prop where
  contDiff : ∀ k, ContDiff ℝ 1 (P k)
  eq_zero : ∀ k ∉ S, P k = 0

theorem mem_cell_iff {h : ℝ} (hh : 0 < h) {k : Fin (n + 1) → ℤ} {x : Fin (n + 1) → ℝ} :
    x ∈ cell h k ↔ cellIndex h x = k := by
  simp only [cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, cellIndex]
  constructor
  · intro hx; funext m
    exact InterfaceLifting.int_eq_of_mem_Ico hh
      ⟨by rw [← le_div_iff₀ hh]; exact Int.floor_le _,
        by rw [← div_lt_iff₀ hh]; exact Int.lt_floor_add_one _⟩ (hx m)
  · rintro rfl m
    exact ⟨by rw [← le_div_iff₀ hh]; exact Int.floor_le _,
      by rw [← div_lt_iff₀ hh]; exact Int.lt_floor_add_one _⟩

/-- A field given cellwise by a finite family is a finite sum of cell indicators. -/
theorem cellwise_eq_sum (h : ℝ) (hh : 0 < h) (G : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A)
    (S : Finset (Fin (n + 1) → ℤ)) (hG : ∀ k ∉ S, ∀ x, G k x = 0) (x : Fin (n + 1) → ℝ) :
    G (cellIndex h x) x = ∑ k ∈ S, (cell h k).indicator (G k) x := by
  classical
  have : ∀ k ∈ S, (cell h k).indicator (G k) x = if cellIndex h x = k then G k x else 0 :=
    fun k _ => by
      by_cases hk : cellIndex h x = k
      · rw [if_pos hk, Set.indicator_of_mem ((mem_cell_iff hh).2 hk)]
      · rw [if_neg hk, Set.indicator_of_notMem (fun h' => hk ((mem_cell_iff hh).1 h'))]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with hS
  · rfl
  · exact hG _ hS x

theorem cell_subset_Icc (h : ℝ) (hh : 0 < h) (k : Fin (n + 1) → ℤ) :
    cell h k ⊆ univ.pi fun m => Icc ((k m : ℝ) * h) (((k m : ℝ) + 1) * h) :=
  Set.pi_mono fun _ _ => Ico_subset_Icc_self

/-- A continuous function restricted to a cell is integrable. -/
theorem integrable_indicator_cell {G : (Fin (n + 1) → ℝ) → A} (hG : Continuous G) {h : ℝ}
    (hh : 0 < h) (k : Fin (n + 1) → ℤ) : Integrable ((cell h k).indicator G) := by
  refine IntegrableOn.integrable_indicator ?_ (measurableSet_cell h k)
  exact (hG.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (cell_subset_Icc h hh k)

theorem integrable_smul_sum_indicator {φ : (Fin (n + 1) → ℝ) → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (S : Finset (Fin (n + 1) → ℤ))
    {G : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A} (hG : ∀ k, Continuous (G k)) :
    Integrable fun x => φ x • ∑ k ∈ S, (cell h k).indicator (G k) x := by
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hsum : Integrable fun x => ∑ k ∈ S, (cell h k).indicator (G k) x :=
    integrable_finsetSum S fun k _ => integrable_indicator_cell (hG k) hh k
  exact hsum.smul_of_top_right (φ := φ) (memLp_top_of_bound hφ.aestronglyMeasurable M
    (Eventually.of_forall hM))

/-! #### Lines in a coordinate direction -/

/-- The point `insertNth a t y`. -/
abbrev ins (a : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) a t y

theorem ins_eq_update (a : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    ins a t y = Function.update (ins a 0 y) a t := by
  funext m
  rcases Fin.eq_self_or_eq_succAbove a m with rfl | ⟨j, rfl⟩
  · simp
  · simp [Function.update, Fin.succAbove_ne]

theorem hasDerivAt_ins (a : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun s => ins a s y) (Pi.single a 1) t := by
  classical
  have : (fun s => ins a s y) = Function.update (ins a 0 y) a := funext fun s => ins_eq_update a s y
  rw [this]
  exact hasDerivAt_update _ _ _

theorem continuous_ins (a : Fin (n + 1)) (y : Fin n → ℝ) : Continuous fun s => ins a s y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ins a t y).continuousAt

theorem continuous_ins_right (a : Fin (n + 1)) (t : ℝ) :
    Continuous fun y : Fin n → ℝ => ins a t y := by
  refine continuous_pi fun m => ?_
  rcases Fin.eq_self_or_eq_succAbove a m with rfl | ⟨j, rfl⟩
  · simp only [ins, Fin.insertNth_apply_same]; exact continuous_const
  · simp only [ins, Fin.insertNth_apply_succAbove]; exact continuous_apply j

/-- The cell label along a line: `κ(insertNth a t y) = insertNth a ⌊t/h⌋ ⌊y/h⌋`. -/
def lineLabel (h : ℝ) (a : Fin (n + 1)) (y : Fin n → ℝ) (m : ℤ) : Fin (n + 1) → ℤ :=
  Fin.insertNth (α := fun _ => ℤ) a m fun j => ⌊y j / h⌋

theorem cellIndex_ins (h : ℝ) (a : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    cellIndex h (ins a t y) = lineLabel h a y ⌊t / h⌋ := by
  funext m
  rcases Fin.eq_self_or_eq_succAbove a m with rfl | ⟨j, rfl⟩
  · simp [cellIndex, lineLabel]
  · simp [cellIndex, lineLabel]

theorem lineLabel_sub_single (h : ℝ) (a : Fin (n + 1)) (y : Fin n → ℝ) (m : ℤ) :
    lineLabel h a y m - Pi.single a 1 = lineLabel h a y (m - 1) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove a i with rfl | ⟨j, rfl⟩
  · simp [lineLabel]
  · simp [lineLabel, Fin.succAbove_ne]

end Mesh

/-! ### The `(n+1)`-dimensional jump formula -/

section JumpFormula

open InterfaceLifting

variable {n : ℕ}
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

theorem piFinSuccAbove_symm_eq_ins (a : Fin (n + 1)) (p : ℝ × (Fin n → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) a).symm p = ins a p.1 p.2 := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- Fubini in the normal coordinate `a`: `∫ G = ∫_y ∫_t G(insertNth a t y)`. -/
theorem integral_eq_integral_ins (a : Fin (n + 1)) {G : (Fin (n + 1) → ℝ) → A}
    (hG : Integrable G) :
    ∫ x, G x = ∫ y, ∫ t, G (ins a t y) ∧ Integrable fun y => ∫ t, G (ins a t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) a
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n + 1) → ℝ)) :=
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) a).symm _
  have hGp : Integrable (fun p : ℝ × (Fin n → ℝ) => G (ins a p.1 p.2))
      ((volume : Measure ℝ).prod volume) := by
    have := (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hG
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, e]
    rw [piFinSuccAbove_symm_eq_ins]
  refine ⟨?_, hGp.integral_prod_right⟩
  rw [← hmp.integral_comp' (g := G)]
  simp only [e, piFinSuccAbove_symm_eq_ins]
  exact integral_prod_symm _ hGp

theorem mem_faceBox_lineLabel (h : ℝ) (hh : 0 < h) (a : Fin (n + 1)) (y : Fin n → ℝ) (m : ℤ) :
    y ∈ faceBox h (a, lineLabel h a y m) := by
  intro j _
  simp only [lineLabel, Fin.insertNth_apply_succAbove]
  exact ⟨by rw [← le_div_iff₀ hh]; exact Int.floor_le _,
    by rw [← div_lt_iff₀ hh]; exact Int.lt_floor_add_one _⟩

theorem facePoint_lineLabel (h : ℝ) (a : Fin (n + 1)) (y : Fin n → ℝ) (m : ℤ) :
    facePoint h (a, lineLabel h a y m) y = ins a ((m : ℝ) * h) y := by
  simp [facePoint, faceLevel, lineLabel]

theorem eq_lineLabel_of_mem_faceBox {h : ℝ} (hh : 0 < h) {a : Fin (n + 1)}
    {k : Fin (n + 1) → ℤ} {y : Fin n → ℝ} (hy : y ∈ faceBox h (a, k)) :
    k = lineLabel h a y (k a) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove a i with rfl | ⟨j, rfl⟩
  · simp [lineLabel]
  · simp only [lineLabel, Fin.insertNth_apply_succAbove]
    have := hy j (mem_univ _)
    simp only at this
    exact (floor_div_eq_of_mem hh this.1 this.2).symm

theorem norm_ins_ge (a : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) : |t| ≤ ‖ins a t y‖ := by
  have := norm_le_pi_norm (ins a t y) a
  simpa [Real.norm_eq_abs] using this

/-- **Jump formula for one partial derivative** (Gauss–Green on the cubical mesh).  For a
cellwise `C¹` field `u = cellwise h P`, a `C¹` compactly supported `ψ`, and a finite face family
`F` containing every face `⊥ e_a` on which `ψ` does not vanish identically,
`-∫ ∂_a ψ u = ∫ ψ ∂_a^b u + Σ_{f ∈ F, f ⊥ e_a} ∫_f ψ [u]_f`. -/
theorem partial_jump_formula {h : ℝ} (hh : 0 < h) {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : IsCellwiseC1 P S) (a : Fin (n + 1))
    {ψ : (Fin (n + 1) → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (F : Finset (Face n))
    (hF : ∀ k : Fin (n + 1) → ℤ, ∀ y ∈ faceBox h (a, k), ψ (facePoint h (a, k) y) ≠ 0 →
      (a, k) ∈ F) :
    -(∫ x, DistributionalCurvature.pderiv a ψ x • cellwise h P x) =
      (∫ x, ψ x • brokenPDeriv h P a x) +
        ∑ f ∈ F.filter (fun f => f.1 = a),
          ∫ y in faceBox h f, ψ (facePoint h f y) • faceJump h P f y := by
  classical
  -- regularity
  have hPd : ∀ k, Differentiable ℝ (P k) := fun k => (hP.contDiff k).differentiable one_ne_zero
  have hPc : ∀ k, Continuous (P k) := fun k => (hP.contDiff k).continuous
  have hPdc : ∀ k, Continuous fun x => fderiv ℝ (P k) x (Pi.single a 1) := fun k =>
    ((hP.contDiff k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hψdc : Continuous (DistributionalCurvature.pderiv a ψ) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfz : ∀ x, x ∉ tsupport ψ → ψ x = 0 ∧ fderiv ℝ ψ x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport fun h' => hx (tsupport_fderiv_subset ℝ h')⟩
  have hpdcs : HasCompactSupport (DistributionalCurvature.pderiv a ψ) :=
    HasCompactSupport.intro hψc fun x hx => by
      simp [DistributionalCurvature.pderiv, (hfz x hx).2]
  -- integrands as finite sums of cell indicators
  have hu : ∀ x, cellwise h P x = ∑ k ∈ S, (cell h k).indicator (P k) x := fun x =>
    cellwise_eq_sum h hh P S (fun k hk x => by rw [hP.eq_zero k hk]; rfl) x
  have hb : ∀ x, brokenPDeriv h P a x =
      ∑ k ∈ S, (cell h k).indicator (fun x => fderiv ℝ (P k) x (Pi.single a 1)) x := fun x =>
    cellwise_eq_sum h hh (fun k x => fderiv ℝ (P k) x (Pi.single a 1)) S
      (fun k hk x => by rw [hP.eq_zero k hk]; simp) x
  have I1 : Integrable fun x => DistributionalCurvature.pderiv a ψ x • cellwise h P x := by
    simp_rw [hu]; exact integrable_smul_sum_indicator hψdc hpdcs hh S hPc
  have I2 : Integrable fun x => ψ x • brokenPDeriv h P a x := by
    simp_rw [hb]; exact integrable_smul_sum_indicator hψ.continuous hψc hh S hPdc
  obtain ⟨e1, -⟩ := integral_eq_integral_ins a I1
  obtain ⟨e2, J2⟩ := integral_eq_integral_ins a I2
  -- a radius for the support
  obtain ⟨R, hR⟩ := hψc.isCompact.isBounded.exists_norm_le
  set N0 : ℕ := ⌈R / h⌉₊ + 1 with hN0
  have hRN : R < (N0 : ℝ) * h := by
    have h1 : R / h ≤ ⌈R / h⌉₊ := Nat.le_ceil _
    have h2 : R ≤ (⌈R / h⌉₊ : ℝ) * h := by rwa [div_le_iff₀ hh] at h1
    simp only [hN0]; push_cast; nlinarith
  have hfar : ∀ x : Fin (n + 1) → ℝ, (N0 : ℝ) * h ≤ ‖x‖ → ψ x = 0 ∧ fderiv ℝ ψ x = 0 :=
    fun x hx => hfz x fun hmem => by linarith [hR x hmem]
  -- the face side, pointwise in `y`
  set g : Face n → (Fin n → ℝ) → A := fun f y => ψ (facePoint h f y) • faceJump h P f y with hg
  have hgc : ∀ f, Continuous (g f) := fun f => by
    simp only [hg, faceJump, facePoint]
    exact (hψ.continuous.comp (continuous_ins_right _ _)).smul
      (((hPc _).comp (continuous_ins_right _ _)).sub ((hPc _).comp (continuous_ins_right _ _)))
  have hgi : ∀ f, Integrable ((faceBox h f).indicator (g f)) := fun f =>
    IntegrableOn.integrable_indicator ((hgc f).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc) |>.mono_set
        (Set.pi_mono fun _ _ => Ico_subset_Icc_self)) (measurableSet_faceBox h f)
  set T : (Fin n → ℝ) → A := fun y => ∑ f ∈ F.filter (fun f => f.1 = a),
    (faceBox h f).indicator (g f) y with hT
  have hTi : Integrable T := integrable_finsetSum _ fun f _ => hgi f
  have hTint : ∫ y, T y = ∑ f ∈ F.filter (fun f => f.1 = a),
      ∫ y in faceBox h f, ψ (facePoint h f y) • faceJump h P f y := by
    rw [integral_finsetSum _ fun f _ => hgi f]
    exact Finset.sum_congr rfl fun f _ => integral_indicator (measurableSet_faceBox h f)
  -- the one-dimensional formula on every line
  have key : ∀ y, -(∫ t, DistributionalCurvature.pderiv a ψ (ins a t y) • cellwise h P (ins a t y)) =
      (∫ t, ψ (ins a t y) • brokenPDeriv h P a (ins a t y)) + T y := by
    intro y
    have hsupp : ∀ t, t ∉ Ioo (((-N0 : ℤ) : ℝ) * h) ((((-N0 : ℤ) : ℝ) + ((2 * N0 : ℕ) : ℝ)) * h) →
        ψ (ins a t y) = 0 ∧ DistributionalCurvature.pderiv a ψ (ins a t y) = 0 := by
      intro t ht
      have hle : (N0 : ℝ) * h ≤ |t| := by
        by_contra hlt
        push Not at hlt
        apply ht
        rw [abs_lt] at hlt
        constructor <;> push_cast <;> linarith
      have := hfar _ (hle.trans (norm_ins_ge a t y))
      exact ⟨this.1, by simp [DistributionalCurvature.pderiv, this.2]⟩
    have h1 := integral_deriv_smul_floor hh (ψ := fun t => ψ (ins a t y))
      (ψ' := fun t => DistributionalCurvature.pderiv a ψ (ins a t y))
      (fun t => (hψd _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ins a t y))
      (hψdc.comp (continuous_ins a y))
      (Q := fun m t => P (lineLabel h a y m) (ins a t y))
      (Q' := fun m t => fderiv ℝ (P (lineLabel h a y m)) (ins a t y) (Pi.single a 1))
      (fun m t => (hPd _ _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ins a t y))
      (fun m => (hPdc _).comp (continuous_ins a y)) (-N0) (2 * N0) hsupp
    have hc1 : ∀ t, cellwise h P (ins a t y) = P (lineLabel h a y ⌊t / h⌋) (ins a t y) :=
      fun t => by simp only [cellwise, cellIndex_ins]
    have hc2 : ∀ t, brokenPDeriv h P a (ins a t y) =
        fderiv ℝ (P (lineLabel h a y ⌊t / h⌋)) (ins a t y) (Pi.single a 1) :=
      fun t => by simp only [brokenPDeriv, cellIndex_ins]
    simp only [hc1, hc2]
    rw [h1]
    congr 1
    -- matching the line sum with the face sum
    simp only [hT]
    refine Finset.sum_bij_ne_zero (fun j _ _ => (a, lineLabel h a y (-N0 + j))) ?_ ?_ ?_ ?_
    · intro j _ hj
      refine Finset.mem_filter.2 ⟨hF _ y (mem_faceBox_lineLabel h hh a y _) ?_, rfl⟩
      rw [facePoint_lineLabel]
      intro h0
      apply hj
      push_cast at h0 ⊢
      rw [h0, zero_smul]
    · intro j1 _ _ j2 _ _ heq
      have := congrFun (congrArg Prod.snd heq) a
      simp only [lineLabel, Fin.insertNth_apply_same] at this
      omega
    · intro f hf hne
      obtain ⟨hfF, hfa⟩ := Finset.mem_filter.1 hf
      obtain ⟨i, k⟩ := f
      simp only at hfa
      subst hfa
      have hy : y ∈ faceBox h (i, k) := by
        by_contra hy
        exact hne (Set.indicator_of_notMem hy _)
      have hk := eq_lineLabel_of_mem_faceBox hh hy
      have hψne : ψ (ins i ((k i : ℝ) * h) y) ≠ 0 := by
        intro h0
        apply hne
        rw [Set.indicator_of_mem hy]
        simp only [hg]
        rw [hk, facePoint_lineLabel, ← hk, h0, zero_smul]
      have hlt : |(k i : ℝ) * h| < (N0 : ℝ) * h := by
        by_contra hge
        push Not at hge
        exact hψne (hfar _ (hge.trans (norm_ins_ge i _ y))).1
      rw [abs_lt] at hlt
      have hk1 : -(N0 : ℝ) < k i := by
        by_contra hc; push Not at hc; nlinarith
      have hk2 : (k i : ℝ) < N0 := by
        by_contra hc; push Not at hc; nlinarith
      have hk1' : -(N0 : ℤ) < k i := by exact_mod_cast hk1
      have hk2' : k i < (N0 : ℤ) := by exact_mod_cast hk2
      refine ⟨(k i + N0).toNat, Finset.mem_range.2 (by omega), ?_, ?_⟩
      · have hcast : (-(N0 : ℤ) + ((k i + N0).toNat : ℤ)) = k i := by omega
        intro h0
        apply hne
        rw [Set.indicator_of_mem hy]
        simp only [hg, faceJump]
        rw [← h0]
        simp only [hcast]
        push_cast
        have hreal : -(N0 : ℝ) + (((k i + N0).toNat : ℕ) : ℝ) = (k i : ℝ) := by
          have := congrArg (Int.cast : ℤ → ℝ) hcast
          push_cast at this
          exact this
        rw [hreal, ← lineLabel_sub_single, ← facePoint_lineLabel h i y (k i), ← hk]
      · have hcast : (-(N0 : ℤ) + ((k i + N0).toNat : ℤ)) = k i := by omega
        simp only [hcast]
        rw [← hk]
    · intro j _ _
      rw [Set.indicator_of_mem (mem_faceBox_lineLabel h hh a y _)]
      simp only [hg, faceJump, facePoint_lineLabel, lineLabel_sub_single]
      push_cast
      rfl
  calc -(∫ x, DistributionalCurvature.pderiv a ψ x • cellwise h P x)
      = -(∫ y, ∫ t, DistributionalCurvature.pderiv a ψ (ins a t y) • cellwise h P (ins a t y)) := by
        rw [e1]
    _ = ∫ y, -(∫ t, DistributionalCurvature.pderiv a ψ (ins a t y) • cellwise h P (ins a t y)) :=
        (integral_neg _).symm
    _ = ∫ y, ((∫ t, ψ (ins a t y) • brokenPDeriv h P a (ins a t y)) + T y) := by
        congr 1; funext y; exact key y
    _ = (∫ y, ∫ t, ψ (ins a t y) • brokenPDeriv h P a (ins a t y)) + ∫ y, T y :=
        integral_add J2 hTi
    _ = _ := by rw [← e2, hTint]

end JumpFormula

/-! ### Regularity of cellwise fields -/

section Regularity

open InterfaceLifting

variable {n : ℕ}
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

theorem cellwise_eq_sum' {h : ℝ} (hh : 0 < h) {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : IsCellwiseC1 P S) :
    cellwise h P = fun x => ∑ k ∈ S, (cell h k).indicator (P k) x :=
  funext fun x => cellwise_eq_sum h hh P S (fun k hk x => by rw [hP.eq_zero k hk]; rfl) x

theorem brokenPDeriv_eq_sum {h : ℝ} (hh : 0 < h) {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : IsCellwiseC1 P S) (a : Fin (n + 1)) :
    brokenPDeriv h P a = fun x =>
      ∑ k ∈ S, (cell h k).indicator (fun x => fderiv ℝ (P k) x (Pi.single a 1)) x :=
  funext fun x => cellwise_eq_sum h hh (fun k x => fderiv ℝ (P k) x (Pi.single a 1)) S
    (fun k hk x => by rw [hP.eq_zero k hk]; simp) x

theorem aestronglyMeasurable_cellwise {h : ℝ} (hh : 0 < h)
    {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A} {S : Finset (Fin (n + 1) → ℤ)}
    (hP : IsCellwiseC1 P S) (μ : Measure (Fin (n + 1) → ℝ)) :
    AEStronglyMeasurable (cellwise h P) μ := by
  rw [cellwise_eq_sum' hh hP]
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    ((hP.contDiff k).continuous.aestronglyMeasurable).indicator (measurableSet_cell h k)

theorem aestronglyMeasurable_brokenPDeriv {h : ℝ} (hh : 0 < h)
    {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A} {S : Finset (Fin (n + 1) → ℤ)}
    (hP : IsCellwiseC1 P S) (a : Fin (n + 1)) (μ : Measure (Fin (n + 1) → ℝ)) :
    AEStronglyMeasurable (brokenPDeriv h P a) μ := by
  rw [brokenPDeriv_eq_sum hh hP a]
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    ((((hP.contDiff k).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).aestronglyMeasurable).indicator (measurableSet_cell h k)

theorem integrable_smul_brokenPDeriv {h : ℝ} (hh : 0 < h)
    {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A} {S : Finset (Fin (n + 1) → ℤ)}
    (hP : IsCellwiseC1 P S) (a : Fin (n + 1)) {φ : (Fin (n + 1) → ℝ) → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Integrable fun x => φ x • brokenPDeriv h P a x := by
  rw [brokenPDeriv_eq_sum hh hP a]
  exact integrable_smul_sum_indicator hφ hφc hh S fun k =>
    ((hP.contDiff k).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_faceJump {h : ℝ} {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A}
    {S : Finset (Fin (n + 1) → ℤ)} (hP : IsCellwiseC1 P S) (f : Face n) :
    Continuous (faceJump h P f) := by
  have : faceJump h P f = fun y => P f.2 (ins f.1 (faceLevel h f) y) -
      P (f.2 - Pi.single f.1 1) (ins f.1 (faceLevel h f) y) := rfl
  rw [this]
  exact ((hP.contDiff _).continuous.comp (continuous_ins_right _ _)).sub
    ((hP.contDiff _).continuous.comp (continuous_ins_right _ _))

/-- A continuous function is in every `Lᵖ` of a face box. -/
theorem memLp_faceBox_of_continuous {h : ℝ} (hh : 0 < h) {g : (Fin n → ℝ) → A}
    (hg : Continuous g) (f : Face n) (p : ℝ≥0∞) : MemLp g p (volume.restrict (faceBox h f)) := by
  have hK : IsCompact (univ.pi fun j : Fin n =>
      Icc ((f.2 (f.1.succAbove j) : ℝ) * h) (((f.2 (f.1.succAbove j) : ℝ) + 1) * h)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have : IsFiniteMeasure (volume.restrict (faceBox h f)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_faceBox hh.le]; exact ENNReal.ofReal_lt_top⟩
  refine MemLp.of_bound hg.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem (measurableSet_faceBox h f)] with y hy
  exact hM y (Set.pi_mono (fun _ _ => Ico_subset_Icc_self) hy)

theorem integrableOn_smul_faceJump {h : ℝ} (hh : 0 < h)
    {P : (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℝ) → A} {S : Finset (Fin (n + 1) → ℤ)}
    (hP : IsCellwiseC1 P S) {ψ : (Fin (n + 1) → ℝ) → ℝ} (hψ : Continuous ψ) (f : Face n) :
    IntegrableOn (fun y => ψ (facePoint h f y) • faceJump h P f y) (faceBox h f) := by
  have : IsFiniteMeasure (volume.restrict (faceBox h f)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_faceBox hh.le]; exact ENNReal.ofReal_lt_top⟩
  have hc : Continuous fun y => ψ (facePoint h f y) • faceJump h P f y :=
    (hψ.comp (continuous_ins_right _ _)).smul (continuous_faceJump hP f)
  exact (memLp_faceBox_of_continuous hh hc f 1).integrable le_rfl

end Regularity

end RenewalGeometry.CubicalJump
