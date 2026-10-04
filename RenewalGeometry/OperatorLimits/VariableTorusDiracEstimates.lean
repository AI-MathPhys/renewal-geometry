/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.VariableTorusDirac
import RenewalGeometry.Analysis.TorusSquarePartitionOfUnity
import RenewalGeometry.DiscreteAnalysis.ExactSpinTransportLinks

/-!
# Uniform discrete estimates for the variable covariant Wilson operator on the periodic box

Paper `predictive_spectral_geometry`, `thm:supp-compact-spin-resolvent`, clause
`eq:supp-local-norm-resolvent`; the hypotheses (A2) and (A3) of
`VariableTorusDirac.Coeffs.covariantDiscretizationOfGarding` for genuinely variable continuous
periodic coefficients with exact spin parallel transport links.

* Elementary tools: entrywise matrix bounds in the Euclidean norm
  (`euclNormSq_mulVec_le_of_entry`), translation of grid points (`samplePt_add_single`),
  distances on the torus, uniform continuity and boundedness of continuous coefficient fields,
  and the first-order Taylor expansion of `c^j` along `e_j` (`Coeffs.norm_entry_taylor_le`).
* `Coeffs.IsTransportLinks`: exact inverse spin parallel transport links of `Ω` at mesh `1/m`
  (`eq:supp-covariant-differences`), `transport_comm` (a matrix commuting with `Ω` commutes with
  the transport), `norm_transport_sub_le_of_osc` (`U = I + hΩ + o(h)` for a merely continuous
  connection).
* `Coeffs.exists_uniform_garding`: **(A2)**, the squared Gårding estimate
  `‖u‖²_{1,h} ≤ G (‖D̃^W u‖²_h + ‖u‖²_h)` at every mesh `h = 1/(n+1)` with ONE constant `G`,
  obtained from `CovariantWilsonGarding.covariant_garding` with the sampled square partition of
  unity of `TorusPartition` (fixed patch size chosen from the modulus of continuity of `c`),
  frozen ellipticity from the uniform Clifford/ellipticity hypothesis, the Lipschitz bound from
  `∂_j c^j`, and the link bound from the transport.
-/

open MeasureTheory Set Finset ComplexConjugate UnitAddTorus Filter Topology Matrix
open scoped BigOperators Real ENNReal InnerProductSpace lp

noncomputable section

namespace RenewalGeometry.VariableTorusDirac

open FlatTorusSpinAtlas CovariantWilsonGarding VariableWilsonGarding FrozenWilsonGarding
  LatticeTorusPlancherel TorusCellEmbedding

set_option linter.unusedSectionVars false

variable {d K : ℕ}

/-! ### Entrywise matrix bounds -/

/-- An entrywise bound `|A_{ab}| ≤ ε` gives `‖A w‖² ≤ (N ε)² ‖w‖²`. -/
theorem euclNormSq_mulVec_le_of_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ a b, ‖A a b‖ ≤ ε) (w : Fin N → ℂ) :
    euclNormSq (A *ᵥ w) ≤ (N * ε) ^ 2 * euclNormSq w := by
  have hrow : ∀ a, ‖(A *ᵥ w) a‖ ^ 2 ≤ ε ^ 2 * (N * euclNormSq w) := by
    intro a
    have h1 : ‖(A *ᵥ w) a‖ ≤ ε * ∑ b, ‖w b‖ := by
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h a b) (norm_nonneg _)
    have h2 : (∑ b, ‖w b‖) ^ 2 ≤ N * euclNormSq w := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun b => ‖w b‖)
      simpa [euclNormSq] using this
    calc ‖(A *ᵥ w) a‖ ^ 2 ≤ (ε * ∑ b, ‖w b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ε ^ 2 * (∑ b, ‖w b‖) ^ 2 := by ring
      _ ≤ ε ^ 2 * (N * euclNormSq w) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  unfold euclNormSq
  calc ∑ a, ‖(A *ᵥ w) a‖ ^ 2 ≤ ∑ _a : Fin N, ε ^ 2 * (N * ∑ i, ‖w i‖ ^ 2) :=
        Finset.sum_le_sum fun a _ => hrow a
    _ = (N * ε) ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Grid points on the torus -/

section grid

variable {m : ℕ} [NeZero m]

theorem lineVec_eq_partition (j : Fin d) (t : ℝ) : lineVec j t = TorusPartition.lineVec j t := rfl

theorem coe_val_add_one (a : ZMod m) :
    ((((a + 1).val : ℝ) / m : ℝ) : UnitAddCircle) =
      (((a.val : ℝ) / m : ℝ) : UnitAddCircle) + (((m : ℝ)⁻¹ : ℝ) : UnitAddCircle) := by
  have hm : (0 : ℝ) < m := TorusCellEmbedding.n_pos
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  set q := (a.val + 1) / m with hqdef
  have hq := Nat.mod_add_div (a.val + 1) m
  rw [← hqdef] at hq
  have hr : (((a.val + 1) % m : ℕ) : ℝ) = (a.val : ℝ) + 1 - m * (q : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at this
    linarith
  have e : (((a.val + 1) % m : ℕ) : ℝ) / m =
      ((a.val : ℝ) / m + (m : ℝ)⁻¹) - ((q : ℤ) : ℝ) := by
    rw [hr, Int.cast_natCast]; field_simp
  rw [e, AddCircle.coe_sub, TorusPartition.coe_intCast_unitAddCircle, sub_zero, AddCircle.coe_add]

/-- `x ↦ x/m` intertwines the lattice shift with the translation by `e_j/m`. -/
theorem samplePt_add_single (x : Grid d m) (j : Fin d) :
    samplePt (x + Pi.single j 1) = samplePt x + lineVec j ((m : ℝ)⁻¹) := by
  funext i
  simp only [samplePt, Pi.add_apply, lineVec]
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same]
    exact coe_val_add_one (x i)
  · simp [Pi.single_eq_of_ne hij]

theorem samplePt_sub_single (x : Grid d m) (j : Fin d) :
    samplePt (x - Pi.single j 1) = samplePt x + lineVec j (-(m : ℝ)⁻¹) := by
  have h := samplePt_add_single (x - Pi.single j 1) j
  rw [sub_add_cancel] at h
  rw [h, add_assoc, ← lineVec_add, add_neg_cancel]
  simp [lineVec]

theorem norm_coe_le_abs (t : ℝ) : ‖(t : UnitAddCircle)‖ ≤ |t| := by
  rw [UnitAddCircle.norm_eq]; simpa using round_le t 0

/-- `dist` on the torus from coordinate bounds. -/
theorem dist_le_of_coord {y y' : UnitAddTorus (Fin d)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ‖y i - y' i‖ ≤ r) : dist y y' ≤ r :=
  (dist_pi_le_iff hr).2 fun i => by rw [dist_eq_norm]; exact h i

theorem norm_lineVec_apply_le (j i : Fin d) (t : ℝ) : ‖lineVec j t i‖ ≤ |t| := by
  by_cases hij : i = j
  · subst hij; simp only [lineVec, Pi.single_eq_same]; exact norm_coe_le_abs t
  · simp [lineVec, Pi.single_eq_of_ne hij]

theorem dist_add_lineVec_le (y : UnitAddTorus (Fin d)) (j : Fin d) (t : ℝ) :
    dist (y + lineVec j t) y ≤ |t| :=
  dist_le_of_coord (abs_nonneg t) fun i => by
    simp only [Pi.add_apply, add_sub_cancel_left]; exact norm_lineVec_apply_le j i t

/-- Every point is within `1/m` (coordinatewise) of the lattice point of its cell. -/
theorem norm_sub_samplePt_index_le (y : UnitAddTorus (Fin d)) (i : Fin d) :
    ‖y i - samplePt (index m y) i‖ ≤ (m : ℝ)⁻¹ := by
  have hm : (0 : ℝ) < m := TorusCellEmbedding.n_pos
  have hy := TorusPiecewiseConstant.mem_cell1_index1 (N := m) (y i)
  simp only [TorusPiecewiseConstant.cell1, Set.mem_preimage, Set.mem_Ioc] at hy
  set r := TorusPiecewiseConstant.rep (y i) with hr
  set v := ((TorusPiecewiseConstant.index1 m (y i)).val : ℝ) with hv
  have e1 : y i = ((r : ℝ) : UnitAddCircle) := (TorusPiecewiseConstant.coe_rep (y i)).symm
  have e2 : samplePt (index m y) i = ((v / m : ℝ) : UnitAddCircle) := rfl
  rw [e2, e1, ← AddCircle.coe_sub]
  refine (norm_coe_le_abs _).trans ?_
  have h1 : v / m < r := hy.1
  have h2 : r ≤ (v + 1) / m := hy.2
  rw [add_div, one_div] at h2
  have h0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem dist_samplePt_index_le (y : UnitAddTorus (Fin d)) :
    dist y (samplePt (index m y)) ≤ (m : ℝ)⁻¹ :=
  dist_le_of_coord (by positivity) fun i => norm_sub_samplePt_index_le y i

end grid

/-! ### Uniform continuity and bounds of continuous coefficient fields -/

section fields

variable {ι : Type*} [Fintype ι]

/-- Uniform continuity of a finite family of continuous matrix fields on the torus, entrywise. -/
theorem exists_delta_entries (F : ι → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ))
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ y y' : UnitAddTorus (Fin d), dist y y' < δ →
      ∀ j a b, ‖F j y a b - F j y' a b‖ < ε := by
  set G : UnitAddTorus (Fin d) → (ι → Fin K → Fin K → ℂ) := fun y j a b => F j y a b
  have hG : Continuous G := continuous_pi fun j => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply b).comp ((continuous_apply a).comp (F j).continuous)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hG) ε hε
  refine ⟨δ, hδ, fun y y' hyy j a b => ?_⟩
  have h := hδ' hyy
  rw [← dist_eq_norm]
  calc dist (G y j a b) (G y' j a b) ≤ dist (G y j a) (G y' j a) := dist_le_pi_dist _ _ b
    _ ≤ dist (G y j) (G y' j) := dist_le_pi_dist _ _ a
    _ ≤ dist (G y) (G y') := dist_le_pi_dist _ _ j
    _ < ε := h

/-- A finite family of continuous matrix fields on the torus is entrywise bounded. -/
theorem exists_bound_entries (F : ι → C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)) :
    ∃ B, 0 ≤ B ∧ ∀ j y a b, ‖F j y a b‖ ≤ B := by
  set G : UnitAddTorus (Fin d) → (ι → Fin K → Fin K → ℂ) := fun y j a b => F j y a b
  have hG : Continuous G := continuous_pi fun j => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply b).comp ((continuous_apply a).comp (F j).continuous)
  obtain ⟨B, hB⟩ := (isCompact_univ.image hG).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun j y a b => ?_⟩
  have h := hB (G y) ⟨y, mem_univ _, rfl⟩
  calc ‖F j y a b‖ = ‖G y j a b‖ := rfl
    _ ≤ ‖G y j a‖ := norm_le_pi_norm _ b
    _ ≤ ‖G y j‖ := norm_le_pi_norm _ a
    _ ≤ ‖G y‖ := norm_le_pi_norm _ j
    _ ≤ max B 0 := h.trans (le_max_left _ _)

end fields

/-! ### Taylor expansion of the coefficients along the coordinate lines -/

namespace Coeffs

variable (C : Coeffs d K)

theorem hasDerivAt_entry_line (j : Fin d) (y : UnitAddTorus (Fin d)) (a b : Fin K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => C.c j (y + lineVec j s) a b) (C.dc j (y + lineVec j t) a b) t := by
  have h := C.hasDerivAt_entry j (y + lineVec j t) a b
  have h' : HasDerivAt (fun s : ℝ => C.c j (y + lineVec j t + lineVec j s) a b)
      (C.dc j (y + lineVec j t) a b) (t - t) := by rwa [sub_self]
  have h2 := h'.comp_sub_const t t
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only
  rw [add_assoc, ← lineVec_add, add_sub_cancel]

/-- Mean value bound: `|c^j_{ab}(y + t e_j) - c^j_{ab}(y)| ≤ D |t|` when `|∂_j c^j_{ab}| ≤ D`. -/
theorem norm_entry_line_sub_le (j : Fin d) (y : UnitAddTorus (Fin d)) (a b : Fin K) {D : ℝ}
    (hD : ∀ z, ‖C.dc j z a b‖ ≤ D) (t : ℝ) :
    ‖C.c j (y + lineVec j t) a b - C.c j y a b‖ ≤ D * |t| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => C.c j (y + lineVec j s) a b)
    (f' := fun s => C.dc j (y + lineVec j s) a b) (s := univ)
    (fun s _ => (C.hasDerivAt_entry_line j y a b s).hasDerivWithinAt) (fun s _ => hD _)
    convex_univ (mem_univ 0) (mem_univ t)
  have h0 : y + lineVec j (0 : ℝ) = y := by simp [lineVec]
  simpa [h0, Real.norm_eq_abs] using this

/-- **First-order Taylor expansion along `e_j` with a uniform remainder**: if the entries of
`∂_j c^j` oscillate by less than `ε` within distance `δ`, then
`|c^j_{ab}(y + t e_j) - c^j_{ab}(y) - t ∂_j c^j_{ab}(y)| ≤ ε |t|` for `|t| < δ`. -/
theorem norm_entry_taylor_le (j : Fin d) (a b : Fin K) {ε δ : ℝ}
    (hosc : ∀ y y' : UnitAddTorus (Fin d), dist y y' < δ → ‖C.dc j y a b - C.dc j y' a b‖ < ε)
    (y : UnitAddTorus (Fin d)) (t : ℝ) (ht : |t| < δ) :
    ‖C.c j (y + lineVec j t) a b - C.c j y a b - t * C.dc j y a b‖ ≤ ε * |t| := by
  have hder : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivWithinAt
      (fun s : ℝ => C.c j (y + lineVec j s) a b - (s : ℂ) * C.dc j y a b)
      (C.dc j (y + lineVec j s) a b - C.dc j y a b) (Set.uIcc 0 t) s := by
    intro s _
    have h1 := C.hasDerivAt_entry_line j y a b s
    have h2 := (hasDerivAt_id s).ofReal_comp.mul_const (C.dc j y a b)
    simp only [id, Complex.ofReal_one, one_mul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ‖C.dc j (y + lineVec j s) a b - C.dc j y a b‖ ≤ ε := by
    intro s hs
    refine (hosc _ _ ?_).le
    refine (dist_add_lineVec_le y j s).trans_lt (lt_of_le_of_lt ?_ ht)
    rw [Set.mem_uIcc] at hs
    rcases hs with hs | hs
    · rw [abs_of_nonneg hs.1, abs_of_nonneg (hs.1.trans hs.2)]; exact hs.2
    · rw [abs_of_nonpos hs.2, abs_of_nonpos (hs.1.trans hs.2)]; linarith [hs.1]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_uIcc 0 t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have h0 : y + lineVec j (0 : ℝ) = y := by simp [lineVec]
  rw [h0, sub_zero, Real.norm_eq_abs] at this
  refine le_of_eq_of_le ?_ this
  congr 1
  push_cast
  ring

end Coeffs

/-! ### Linear transport with a continuous coefficient -/

section transport

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- **First-order expansion of linear transport with a merely continuous coefficient**:
if `U' = U Ω`, `U(0) = 1`, `‖Ω‖ ≤ B` and `‖Ω(t) - Ω(0)‖ ≤ ε` on `[0, h]`, then
`‖U(h) - 1 - h Ω(0)‖ ≤ (B² ‖1‖ e^{Bh} h + ε) h`. -/
theorem norm_transport_sub_le_of_osc {Ω U : ℝ → A} {h B ε : ℝ} (hh : 0 ≤ h) (hB : 0 ≤ B)
    (hΩB : ∀ t ∈ Icc 0 h, ‖Ω t‖ ≤ B) (hΩε : ∀ t ∈ Icc 0 h, ‖Ω t - Ω 0‖ ≤ ε)
    (hU0 : U 0 = 1) (hU : ∀ t, HasDerivAt U (U t * Ω t) t) :
    ‖U h - 1 - h • Ω 0‖ ≤ (B ^ 2 * ‖(1 : A)‖ * Real.exp (B * h) * h + ε) * h := by
  set g : ℝ → A := fun t => U t - 1 - t • Ω 0
  have hg : ∀ t, HasDerivAt g (U t * Ω t - Ω 0) t := by
    intro t
    have h1 := ((hU t).sub_const 1).sub ((hasDerivAt_id t).smul_const (Ω 0))
    rw [one_smul] at h1
    exact h1
  have hbound : ∀ s ∈ Ico 0 h,
      ‖U s * Ω s - Ω 0‖ ≤ B ^ 2 * ‖(1 : A)‖ * Real.exp (B * h) * h + ε := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have e : U s * Ω s - Ω 0 = (U s - 1) * Ω s + (Ω s - Ω 0) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hΩε s hs'))
    have h1 := LinearTransport.norm_transport_sub_one_le hB hΩB hU0 hU s hs'
    have hs0 : 0 ≤ s := hs'.1
    calc ‖(U s - 1) * Ω s‖ ≤ (B * ‖(1 : A)‖ * Real.exp (B * h) * s) * B :=
          (norm_mul_le _ _).trans (mul_le_mul h1 (hΩB s hs') (norm_nonneg _) (by positivity))
      _ = (B ^ 2 * ‖(1 : A)‖ * Real.exp (B * h)) * s := by ring
      _ ≤ (B ^ 2 * ‖(1 : A)‖ * Real.exp (B * h)) * h :=
          mul_le_mul_of_nonneg_left hs'.2 (by positivity)
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := fun s => U s * Ω s - Ω 0)
    (fun s _ => (hg s).hasDerivWithinAt) hbound h ⟨hh, le_rfl⟩
  have hg0 : g 0 = 0 := by simp [g, hU0]
  rw [hg0, sub_zero, sub_zero] at this
  exact this

/-- **A matrix commuting with the connection commutes with its transport** (uniqueness for the
linear transport equation, by Grönwall). -/
theorem transport_comm {Ω U : ℝ → A} {h B : ℝ} (hh : 0 ≤ h)
    (hΩB : ∀ t ∈ Icc 0 h, ‖Ω t‖ ≤ B) (hU0 : U 0 = 1) (hU : ∀ t, HasDerivAt U (U t * Ω t) t)
    (G : A) (hG : ∀ t, G * Ω t = Ω t * G) : G * U h = U h * G := by
  set D : ℝ → A := fun t => G * U t - U t * G
  have hD : ∀ t, HasDerivAt D (D t * Ω t) t := by
    intro t
    have h1 : HasDerivAt D (G * (U t * Ω t) - U t * Ω t * G) t :=
      ((hU t).const_mul G).fun_sub ((hU t).mul_const G)
    have e : G * (U t * Ω t) - U t * Ω t * G = D t * Ω t := by
      show _ = (G * U t - U t * G) * Ω t
      rw [sub_mul, mul_assoc (U t) (Ω t) G, ← hG t, mul_assoc G, mul_assoc (U t) G]
    rwa [e] at h1
  have hcont : ContinuousOn D (Icc 0 h) := fun s _ => (hD s).continuousAt.continuousWithinAt
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := D) (f' := fun s => D s * Ω s)
    (δ := 0) (K := B) (ε := 0) hcont (fun s _ => (hD s).hasDerivWithinAt)
    (by simp [D, hU0]) (fun s hs => by
      rw [add_zero, mul_comm B]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hΩB s (Ico_subset_Icc_self hs)) (norm_nonneg _))) h
    ⟨hh, le_rfl⟩
  rw [gronwallBound_ε0, zero_mul] at key
  exact sub_eq_zero.mp (norm_le_zero_iff.mp key)

end transport

/-! ### Exact transport links on the periodic box -/

section links

open scoped Matrix.Norms.Operator

/-- An entrywise bound gives a bound of the `ℓ^∞` operator norm. -/
theorem linfty_norm_le_of_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a b, ‖A a b‖ ≤ ε) : ‖A‖ ≤ N * ε := by
  refine ExactSpinTransport.norm_le_of_mulVec_le A (by positivity) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖A a b * v b‖ ≤ ∑ _b : Fin N, ε * ‖v‖ := Finset.sum_le_sum fun b _ => by
        rw [norm_mul]; exact mul_le_mul (h a b) (norm_le_pi_norm v b) (norm_nonneg _) hε
    _ = N * ε * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- An `ℓ^∞` operator norm bound gives the Euclidean bound `‖A w‖² ≤ (N ‖A‖)² ‖w‖²`. -/
theorem euclNormSq_mulVec_le_of_linfty {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    euclNormSq (A *ᵥ w) ≤ (N * ‖A‖) ^ 2 * euclNormSq w :=
  euclNormSq_mulVec_le_of_entry A (norm_nonneg _) (ExactSpinTransport.norm_entry_le A) w

/-- **Exact inverse spin parallel transport links** of the connection `C.Ω` at mesh `h = 1/m`
(`eq:supp-covariant-differences`): `U_j(x) = Φ(h)` where `Φ' = Φ Ω_j(x/m + t e_j)`, `Φ(0) = I`. -/
def Coeffs.IsTransportLinks (C : Coeffs d K) (m : ℕ) [NeZero m] (U : TorusLinks d m K) : Prop :=
  ∀ (j : Fin d) (x : Grid d m), ∃ Φ : ℝ → Matrix (Fin K) (Fin K) ℂ, Φ 0 = 1 ∧
    (∀ t, HasDerivAt Φ (Φ t * C.Ω j (samplePt x + lineVec j t)) t) ∧ U j x = Φ (m : ℝ)⁻¹

variable {m : ℕ} [NeZero m]

theorem inv_mesh_le_one : (m : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m))

/-- The link bound `‖U_j(x) - I‖ ≤ C_U h` (`LinkBound`) for exact transport links, with
`C_U = K B_Ω ‖I‖ e^{B_Ω}` from an operator bound `B_Ω` of the connection. -/
theorem Coeffs.linkBound_of_isTransportLinks (C : Coeffs d K) {U : TorusLinks d m K}
    (hU : C.IsTransportLinks m U) {BΩ : ℝ} (hBΩ : 0 ≤ BΩ) (hΩ : ∀ j y, ‖C.Ω j y‖ ≤ BΩ) :
    LinkBound (m : ℝ)⁻¹ U (K * (BΩ * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ)) := by
  intro j x w
  obtain ⟨Φ, hΦ0, hΦ, hUx⟩ := hU j x
  have hh : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have h1 := LinearTransport.norm_transport_sub_one_le (h := (m : ℝ)⁻¹) hBΩ
    (fun t _ => hΩ j _) hΦ0 hΦ (m : ℝ)⁻¹ ⟨hh, le_rfl⟩
  have hexp : Real.exp (BΩ * (m : ℝ)⁻¹) ≤ Real.exp BΩ :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right hBΩ inv_mesh_le_one)
  have h2 : ‖U j x - 1‖ ≤ BΩ * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ * (m : ℝ)⁻¹ := by
    rw [hUx]
    refine h1.trans ?_
    gcongr
  refine (euclNormSq_mulVec_le_of_linfty _ w).trans
    (mul_le_mul_of_nonneg_right ?_ (euclNormSq_nonneg w))
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  calc (K : ℝ) * ‖U j x - 1‖ ≤ K * (BΩ * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ *
        (m : ℝ)⁻¹) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = _ := by ring

/-- `Γ_⊥` commutes with exact transport links when it commutes with the connection. -/
theorem Coeffs.comm_of_isTransportLinks (C : Coeffs d K) {U : TorusLinks d m K}
    (hU : C.IsTransportLinks m U) (Γ : Matrix (Fin K) (Fin K) ℂ)
    (hΓΩ : ∀ j y, Γ * C.Ω j y = C.Ω j y * Γ) : ∀ j x, Γ * U j x = U j x * Γ := by
  intro j x
  obtain ⟨Φ, hΦ0, hΦ, hUx⟩ := hU j x
  obtain ⟨B, _, hB⟩ := exists_bound_entries C.Ω
  rw [hUx]
  exact transport_comm (h := (m : ℝ)⁻¹) (B := K * B) (by positivity)
    (fun t _ => linfty_norm_le_of_entry _ (by assumption) fun a b => hB j _ a b) hΦ0 hΦ Γ
    fun t => hΓΩ j _

/-- An operator bound for the connection, from compactness. -/
theorem Coeffs.exists_connection_bound (C : Coeffs d K) :
    ∃ BΩ, 0 ≤ BΩ ∧ ∀ j y, ‖C.Ω j y‖ ≤ BΩ := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_entries C.Ω
  exact ⟨K * B, by positivity, fun j y => linfty_norm_le_of_entry _ hB0 fun a b => hB j y a b⟩

end links

/-! ### (A2): the uniform Gårding estimate -/

section garding

open scoped Matrix.Norms.Operator

/-- At a fixed mesh the discrete `H¹` norm is trivially controlled:
`‖u‖²_{1,h} ≤ (1 + 4d/h²) ‖u‖²_h`. -/
theorem h1NormSq_le_coarse {m N : ℕ} [NeZero m] (h : ℝ) (hh : 0 < h) (u : TorusSection d m N) :
    h1NormSq h u ≤ (1 + 4 * d / h ^ 2) * gridNormSq h u := by
  have hfd : ∀ j, gridNormSq h (forwardDifference h j u) ≤ 4 / h ^ 2 * gridNormSq h u := by
    intro j
    have e : forwardDifference h j u = (h : ℂ)⁻¹ • (shift j u - u) := by
      funext x; simp [forwardDifference]
    rw [e, gridNormSq_smul, gridNormSq_eq_norm_eucl_sq, gridNormSq_eq_norm_eucl_sq, eucl_sub]
    have h1 : ‖eucl (shift j u) - eucl u‖ ≤ 2 * ‖eucl u‖ := by
      refine (norm_sub_le _ _).trans ?_; rw [norm_eucl_shift]; linarith
    have h2 : ‖eucl (shift j u) - eucl u‖ ^ 2 ≤ 4 * ‖eucl u‖ ^ 2 := by
      nlinarith [norm_nonneg (eucl (shift j u) - eucl u)]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    have hhd : 0 ≤ h ^ d := by positivity
    calc h⁻¹ ^ 2 * (h ^ d * ‖eucl (shift j u) - eucl u‖ ^ 2)
        ≤ h⁻¹ ^ 2 * (h ^ d * (4 * ‖eucl u‖ ^ 2)) := by gcongr
      _ = 4 / h ^ 2 * (h ^ d * ‖eucl u‖ ^ 2) := by field_simp
  unfold h1NormSq
  calc gridNormSq h u + ∑ j, gridNormSq h (forwardDifference h j u)
      ≤ gridNormSq h u + ∑ _j : Fin d, 4 / h ^ 2 * gridNormSq h u := by
        gcongr with j; exact hfd j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **(A2) for the variable covariant Wilson operator, uniformly in the mesh**
(`eq:supp-general-Garding`, `thm:supp-general-Wilson-ellipticity`): let `C` be continuous periodic
coefficients (Hermitian `ĉ^j`, `∂_j ĉ^j` continuous, continuous connection) whose doubled Clifford
data `(ĉ^j(y), Γ_⊥)` are uniformly elliptic with constants `0 < λ ≤ Λ` at every point, `Γ_⊥`
Hermitian, `ϖ ≠ 0`.  Then there is ONE constant `G` such that for every mesh `h = 1/(n+1)`,
every family of exact transport links `U` and every lattice section `u`,
`‖u‖²_{1,h} ≤ G (‖D̃^W_{g,h} u‖²_h + ‖u‖²_h)`.

Proof: `covariant_garding` with the sampled square partition of unity `TorusPartition.bump` of a
fixed patch size `1/M` (chosen once from the modulus of continuity of `c`, so that the freezing
error is absorbed), frozen points the lattice points nearest to the patch centres, the Lipschitz
bound from `∂_j c^j`, the link bound of exact transport; the finitely many coarse meshes are
handled by `h1NormSq_le_coarse`. -/
theorem Coeffs.exists_uniform_garding (C : Coeffs d K) (Γ : Matrix (Fin K) (Fin K) ℂ)
    (hΓ : Γᴴ = Γ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hell : ∀ y, UniformlyElliptic (fun j => C.c j y) Γ lam Lam) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (n : ℕ) (U : TorusLinks d (n + 1) K), C.IsTransportLinks (n + 1) U →
      ∀ u : TorusSection d (n + 1) K, h1NormSq ((n + 1 : ℕ) : ℝ)⁻¹ u ≤
        G * (gridNormSq ((n + 1 : ℕ) : ℝ)⁻¹
            (covVarWilson ((n + 1 : ℕ) : ℝ)⁻¹ ϖ (C.sampled (n + 1)) U Γ u) +
          gridNormSq ((n + 1 : ℕ) : ℝ)⁻¹ u) := by
  classical
  -- the absorption threshold
  set F := frozenConstant lam ϖ with hF
  have hF0 : 0 ≤ F := frozenConstant_nonneg lam ϖ
  set ω : ℝ := (Real.sqrt (4 * d * F) + 1)⁻¹ with hωdef
  have hω0 : 0 < ω := by positivity
  have habs : 4 * d * ω ^ 2 * F ≤ 1 := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * d * F)
    have hs0 := Real.sqrt_nonneg (4 * d * F)
    have key : 4 * d * F ≤ (Real.sqrt (4 * d * F) + 1) ^ 2 := by nlinarith
    calc 4 * d * ω ^ 2 * F = (4 * d * F) * ω ^ 2 := by ring
      _ ≤ (Real.sqrt (4 * d * F) + 1) ^ 2 * ω ^ 2 := mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = 1 := by rw [hωdef, inv_pow, mul_inv_cancel₀ (by positivity)]
  set ε : ℝ := ω / (K + 1) with hεdef
  have hε0 : 0 < ε := by positivity
  have hKε : ((K : ℝ) * ε) ^ 2 ≤ ω ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [hεdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  -- the modulus of continuity of `c` and the fixed patch size
  obtain ⟨δ, hδ, hosc⟩ := exists_delta_entries C.c hε0
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (2 / δ)
  set M : ℕ := M₁ + 2 with hMdef
  have hM2 : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by positivity
  have hMδ : (M : ℝ)⁻¹ < δ / 2 := by
    have h1 : 2 / δ < M := by
      have : (M₁ : ℝ) ≤ M := by rw [hMdef]; push_cast; linarith
      linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [inv_lt_iff_one_lt_mul₀ hMpos]
    linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 / δ)
  have hm₀pos : (0 : ℝ) < m₀ := lt_trans (by positivity) hm₀
  -- coefficient bounds
  obtain ⟨Bc, hBc0, hBc⟩ := exists_bound_entries C.c
  obtain ⟨Dc, hDc0, hDc⟩ := exists_bound_entries C.dc
  obtain ⟨BΩ, hBΩ0, hBΩ⟩ := C.exists_connection_bound
  obtain ⟨Gm, hGm0, hGm'⟩ := exists_bound_entries (d := d)
    (fun _ : Fin 1 => (ContinuousMap.const _ Γ : C(UnitAddTorus (Fin d), Matrix (Fin K) (Fin K) ℂ)))
  have hGm : ∀ a b, ‖Γ a b‖ ≤ Gm := fun a b => hGm' 0 0 a b
  -- the constants
  set Mc := Fintype.card (Fin d → Fin M)
  set Kg : ℝ := π / 2 * M
  set CU : ℝ := K * (BΩ * ‖(1 : Matrix (Fin K) (Fin K) ℂ)‖ * Real.exp BΩ)
  set G₁ := covariantGardingConstant d Mc lam ϖ Kg (K * Dc) (K * Bc) (K * Gm) CU
  set G₀ : ℝ := 1 + 4 * d * (m₀ : ℝ) ^ 2
  have hG₀ : 1 ≤ G₀ := by
    have : 0 ≤ 4 * (d : ℝ) * (m₀ : ℝ) ^ 2 := by positivity
    linarith
  refine ⟨max G₁ G₀, (zero_le_one.trans hG₀).trans (le_max_right _ _), fun n U hU u => ?_⟩
  set h : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹ with hhdef
  have hh : 0 < h := by positivity
  have hsum0 : 0 ≤ gridNormSq h (covVarWilson h ϖ (C.sampled (n + 1)) U Γ u) + gridNormSq h u :=
    add_nonneg (gridNormSq_nonneg' _ hh.le _) (gridNormSq_nonneg' _ hh.le _)
  by_cases hn : m₀ ≤ n + 1
  · -- fine meshes: the localised Gårding estimate
    have hh4 : h < δ / 4 := by
      have h1 : h ≤ (m₀ : ℝ)⁻¹ := by
        rw [hhdef]; exact inv_anti₀ hm₀pos (by exact_mod_cast hn)
      have h2 : (m₀ : ℝ)⁻¹ < δ / 4 := by
        rw [inv_lt_iff_one_lt_mul₀ hm₀pos]
        rw [div_lt_iff₀ hδ] at hm₀
        linarith
      linarith
    set e := Fintype.equivFin (Fin d → Fin M)
    set χ : Fin Mc → Grid d (n + 1) → ℝ :=
      fun β x => TorusPartition.bump M (e.symm β) (samplePt x) with hχ
    set x₀ : Fin Mc → Grid d (n + 1) :=
      fun β => index (n + 1) (TorusPartition.centre M (e.symm β)) with hx₀
    have hpart : ∀ x, ∑ β, χ β x ^ 2 = 1 := by
      intro x
      rw [hχ]
      simp only
      rw [e.symm.sum_comp (fun α => TorusPartition.bump M α (samplePt x) ^ 2)]
      exact TorusPartition.sum_sq_bump M hM2 _
    have hell' : ∀ β, UniformlyElliptic (C.sampled (n + 1) (x₀ β)) Γ lam Lam :=
      fun β => hell _
    have hgrad : ∀ β (j : Fin d) x, |χ β (x + Pi.single j 1) - χ β x| ≤ h * Kg := by
      intro β j x
      simp only [hχ]
      rw [samplePt_add_single, lineVec_eq_partition]
      refine (TorusPartition.abs_bump_add_lineVec_sub_le _ _ _ _ _).trans (le_of_eq ?_)
      rw [abs_of_pos hh]
      ring
    have hc : ∀ x j w, euclNormSq (C.sampled (n + 1) x j *ᵥ w) ≤ (K * Bc) ^ 2 * euclNormSq w :=
      fun x j w => euclNormSq_mulVec_le_of_entry _ hBc0 (fun a b => hBc j _ a b) w
    have hΓb : ∀ w, euclNormSq (Γ *ᵥ w) ≤ (K * Gm) ^ 2 * euclNormSq w :=
      fun w => euclNormSq_mulVec_le_of_entry _ hGm0 hGm w
    have hcoord : ∀ β (j : Fin d) x, NearSupport (χ β) j x → ∀ i,
        ‖samplePt x i - samplePt (x₀ β) i‖ ≤ (M : ℝ)⁻¹ + 2 * h := by
      intro β j x hx i
      set c0 := TorusPartition.centre M (e.symm β)
      have hnear : ∀ t : ℝ, |t| = h →
          TorusPartition.bump M (e.symm β) (samplePt x + lineVec j t) ≠ 0 →
            ‖samplePt x i - c0 i‖ ≤ (M : ℝ)⁻¹ + h := by
        intro t ht hb
        have hb' := TorusPartition.bump_ne_zero hb i
        have hlt : ‖(samplePt x + lineVec j t) i - c0 i‖ < (M : ℝ)⁻¹ := by
          rw [← one_div, lt_div_iff₀ hMpos, mul_comm]; exact hb'
        have e1 : samplePt x i - c0 i =
            ((samplePt x + lineVec j t) i - c0 i) - lineVec j t i := by
          simp only [Pi.add_apply]; abel
        rw [e1]
        refine (norm_sub_le _ _).trans (add_le_add hlt.le ?_)
        exact (norm_lineVec_apply_le j i t).trans ht.le
      have h1 : ‖samplePt x i - c0 i‖ ≤ (M : ℝ)⁻¹ + h := by
        rcases hx with hx | hx
        · refine hnear h (abs_of_pos hh) ?_
          have := hx
          simp only [hχ] at this
          rwa [samplePt_add_single] at this
        · refine hnear (-h) (by rw [abs_neg, abs_of_pos hh]) ?_
          have := hx
          simp only [hχ] at this
          rwa [samplePt_sub_single] at this
      have h2 : ‖c0 i - samplePt (x₀ β) i‖ ≤ h := norm_sub_samplePt_index_le c0 i
      have e2 : samplePt x i - samplePt (x₀ β) i =
          (samplePt x i - c0 i) + (c0 i - samplePt (x₀ β) i) := by abel
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hfreeze : ∀ β (j : Fin d) x, NearSupport (χ β) j x → ∀ w,
        euclNormSq ((C.sampled (n + 1) x j - C.sampled (n + 1) (x₀ β) j) *ᵥ w) ≤
          ω ^ 2 * euclNormSq w := by
      intro β j x hx w
      have hdist : dist (samplePt x) (samplePt (x₀ β)) < δ := by
        refine (dist_le_of_coord (by positivity) (hcoord β j x hx)).trans_lt ?_
        linarith
      have hent : ∀ a b, ‖(C.sampled (n + 1) x j - C.sampled (n + 1) (x₀ β) j) a b‖ ≤ ε :=
        fun a b => (hosc _ _ hdist j a b).le
      exact (euclNormSq_mulVec_le_of_entry _ hε0.le hent w).trans
        (mul_le_mul_of_nonneg_right hKε (euclNormSq_nonneg w))
    have hLip : ∀ (j : Fin d) x w, euclNormSq ((C.sampled (n + 1) (x + Pi.single j 1) j -
        C.sampled (n + 1) x j) *ᵥ w) ≤ (h * (K * Dc)) ^ 2 * euclNormSq w := by
      intro j x w
      have hent : ∀ a b, ‖(C.sampled (n + 1) (x + Pi.single j 1) j -
          C.sampled (n + 1) x j) a b‖ ≤ Dc * h := by
        intro a b
        simp only [Coeffs.sampled, Matrix.sub_apply]
        rw [samplePt_add_single]
        have := C.norm_entry_line_sub_le j (samplePt x) a b (fun z => hDc j z a b) h
        rwa [abs_of_pos hh] at this
      refine (euclNormSq_mulVec_le_of_entry _ (by positivity) hent w).trans (le_of_eq ?_)
      ring
    have hlink := C.linkBound_of_isTransportLinks hU hBΩ0 hBΩ
    have key := covariant_garding h ϖ lam Lam hh hlam hϖ hLam (C.sampled (n + 1)) U Γ hΓ χ hpart
      x₀ hell' hω0.le (by positivity : (0 : ℝ) ≤ Kg) (by positivity : (0 : ℝ) ≤ K * Dc)
      (by positivity : (0 : ℝ) ≤ K * Bc) (by positivity : (0 : ℝ) ≤ K * Gm)
      (by positivity : (0 : ℝ) ≤ CU) hgrad hc hΓb hfreeze hLip habs hlink u
    exact key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0)
  · -- coarse meshes
    push Not at hn
    have hc := h1NormSq_le_coarse h hh u
    have hbd : 1 + 4 * d / h ^ 2 ≤ G₀ := by
      rw [hhdef, inv_pow, div_inv_eq_mul]
      have : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (m₀ : ℝ) ^ 2 := by
        have : ((n + 1 : ℕ) : ℝ) ≤ m₀ := by exact_mod_cast hn.le
        exact pow_le_pow_left₀ (by positivity) this 2
      have hd0 : (0 : ℝ) ≤ 4 * d := by positivity
      nlinarith
    have hg0 := gridNormSq_nonneg' h hh.le u
    have hX := gridNormSq_nonneg' h hh.le (covVarWilson h ϖ (C.sampled (n + 1)) U Γ u)
    calc h1NormSq h u ≤ (1 + 4 * d / h ^ 2) * gridNormSq h u := hc
      _ ≤ G₀ * gridNormSq h u := mul_le_mul_of_nonneg_right hbd hg0
      _ ≤ max G₁ G₀ * (gridNormSq h (covVarWilson h ϖ (C.sampled (n + 1)) U Γ u) +
          gridNormSq h u) := by
        refine mul_le_mul (le_max_right _ _) (by linarith) hg0 ?_
        exact (zero_le_one.trans hG₀).trans (le_max_right _ _)

end garding

end RenewalGeometry.VariableTorusDirac
