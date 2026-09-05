/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.TransverseStep

/-!
# Optimal transverse-pulse theorem
  (`thm:optimal-transverse-pulse-master`, flagship manuscript)

For `U ∈ SU(2)` and the Fubini–Study displacement
`χ(U) = arcsin|U₂₁|`, with pulse alphabet `Z(·)` (longitudinal)
and `N_θ(·)` (transverse, `0 < θ ≤ π/2`):

* the boxed count `k_*(U,θ) = ⌈χ(U)/θ⌉`: every pulse word
  implementing `U` contains at least `k_*` transverse pulses
  (`optimal_transverse_pulse`, lower clause), by the
  Fubini–Study triangle inequality `χ(UV) ≤ χ(U) + χ(V)`
  (`chiFS_mul_le`), `χ(Z) = 0`, and `χ(N_θ) ≤ θ`;
* if `χ(U) = 0`, one `Z` pulse implements `U`;
* otherwise there is an explicit exact word with exactly `k_*`
  transverse pulses and total length `≤ 2k_* + 1` — the boxed
  bound `L_*(U,θ) ≤ 2k_* + 1` — built from the Euler
  decomposition `U = Z(α)Y(2χ)Z(γ)` (`euler_decomposition`) and
  the proved exact small transverse step
  (`small_transverse_step`).
-/

open Matrix Real

namespace NCG

noncomputable section

/-- The Fubini–Study displacement `χ(U) = arcsin|U₂₁|`. -/
def chiFS (U : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.arcsin ‖U 1 0‖

lemma chiFS_nonneg (U : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ chiFS U :=
  Real.arcsin_nonneg.mpr (norm_nonneg _)

/-- Row normalization of a unitary. -/
lemma unitary_row_norm (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U 1 0‖ ^ 2 + ‖U 1 1‖ ^ 2 = 1 := by
  have h2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h3 := congrFun (congrFun h2 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_apply, Matrix.one_apply_eq,
    Complex.star_def] at h3
  have h4 : ((‖U 1 0‖ ^ 2 + ‖U 1 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj']
    exact h3
  exact_mod_cast h4

/-- Column normalization of a unitary. -/
lemma unitary_col_norm (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = 1 := by
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h3 := congrFun (congrFun h2 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_apply, Matrix.one_apply_eq,
    Complex.star_def] at h3
  have h4 : ((‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj',
      mul_comm (U 0 0), mul_comm (U 1 0)]
    exact h3
  exact_mod_cast h4

lemma norm_entry_le_one (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖U 1 0‖ ≤ 1 := by
  have h := unitary_row_norm U hU
  nlinarith [norm_nonneg (U 1 0), norm_nonneg (U 1 1)]

/-- The Fubini–Study triangle inequality
`χ(UV) ≤ χ(U) + χ(V)`. -/
lemma chiFS_mul_le (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    chiFS (U * V) ≤ chiFS U + chiFS V := by
  have hrow := unitary_row_norm U hU
  have hcol := unitary_col_norm V hV
  have hx1 : ‖U 1 0‖ ≤ 1 := norm_entry_le_one U hU
  have hy1 : ‖V 1 0‖ ≤ 1 := by
    nlinarith [norm_nonneg (V 0 0), norm_nonneg (V 1 0)]
  have hb : ‖(U * V) 1 0‖
      ≤ ‖U 1 0‖ * ‖V 0 0‖ + ‖U 1 1‖ * ‖V 1 0‖ := by
    have h1 : (U * V) 1 0 = U 1 0 * V 0 0 + U 1 1 * V 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h1]
    calc ‖U 1 0 * V 0 0 + U 1 1 * V 1 0‖
        ≤ ‖U 1 0 * V 0 0‖ + ‖U 1 1 * V 1 0‖ := norm_add_le _ _
      _ = ‖U 1 0‖ * ‖V 0 0‖ + ‖U 1 1‖ * ‖V 1 0‖ := by
          rw [norm_mul, norm_mul]
  have hsin : ‖U 1 0‖ * ‖V 0 0‖ + ‖U 1 1‖ * ‖V 1 0‖
      = Real.sin (chiFS U + chiFS V) := by
    rw [Real.sin_add, chiFS, chiFS,
      Real.sin_arcsin (by linarith [norm_nonneg (U 1 0)]) hx1,
      Real.sin_arcsin (by linarith [norm_nonneg (V 1 0)]) hy1,
      Real.cos_arcsin, Real.cos_arcsin,
      show (1 : ℝ) - ‖U 1 0‖ ^ 2 = ‖U 1 1‖ ^ 2 from by
        linarith,
      show (1 : ℝ) - ‖V 1 0‖ ^ 2 = ‖V 0 0‖ ^ 2 from by
        linarith,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rcases le_or_gt (chiFS U + chiFS V) (Real.pi / 2) with hc | hc
  · calc chiFS (U * V)
        ≤ Real.arcsin (Real.sin (chiFS U + chiFS V)) :=
          Real.monotone_arcsin (hb.trans_eq hsin)
      _ = chiFS U + chiFS V := by
          refine Real.arcsin_sin ?_ hc
          have := chiFS_nonneg U
          have := chiFS_nonneg V
          have := Real.pi_pos
          linarith
  · calc chiFS (U * V) ≤ Real.pi / 2 :=
        Real.arcsin_le_pi_div_two _
      _ ≤ chiFS U + chiFS V := hc.le

lemma chiFS_pulseZ (φ : ℝ) : chiFS (pulseZ φ) = 0 := by
  simp [chiFS, pulseZ]

lemma chiFS_pulseN_le (θ β : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.pi / 2) : chiFS (pulseN θ β) ≤ θ := by
  have hsθ : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0
      (by linarith [Real.pi_pos])
  have h1 : ‖pulseN θ β 1 0‖
      = Real.sin θ * |Real.sin (β / 2)| := by
    simp only [pulseN]
    rw [show (!![(Real.cos (β / 2) : ℝ)
        - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I,
       -(((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I);
       -(((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I),
       (Real.cos (β / 2) : ℝ)
        + ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I]
        : Matrix (Fin 2) (Fin 2) ℂ) 1 0
      = -(((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I)
      from by simp]
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hsθ]
  rw [chiFS, h1]
  calc Real.arcsin (Real.sin θ * |Real.sin (β / 2)|)
      ≤ Real.arcsin (Real.sin θ) := by
        refine Real.monotone_arcsin ?_
        calc Real.sin θ * |Real.sin (β / 2)|
            ≤ Real.sin θ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hsθ
              exact Real.abs_sin_le_one _
          _ = Real.sin θ := mul_one _
    _ = θ := Real.arcsin_sin (by linarith [Real.pi_pos]) hθ

/-- `Z` pulses at time zero. -/
lemma pulseZ_zero : pulseZ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pulseZ]

/-- Additivity of `Z` pulses. -/
lemma pulseZ_add (a b : ℝ) :
    pulseZ a * pulseZ b = pulseZ (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pulseZ, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.mk_zero, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_zero,
      zero_mul, add_zero, zero_add]
  all_goals rw [← Complex.exp_add]
  all_goals congr 1
  all_goals push_cast
  all_goals ring

/-- Conjugate-transpose of a `Z` pulse. -/
lemma pulseZ_star (φ : ℝ) : star (pulseZ φ) = pulseZ (-φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pulseZ, Matrix.star_apply, Fin.mk_zero,
      Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, star_zero,
      Complex.star_def]
  all_goals rw [← Complex.exp_conj]
  all_goals congr 1
  all_goals simp only [map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  all_goals push_cast
  all_goals ring

/-- `Z` pulses are unitary. -/
lemma pulseZ_mem (φ : ℝ) :
    pulseZ φ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, pulseZ_star, pulseZ_add,
    add_neg_cancel, pulseZ_zero]

/-- Conjugate-transpose of an `N_θ` pulse. -/
lemma pulseN_star (θ β : ℝ) : star (pulseN θ β)
    = !![(Real.cos (β / 2) : ℝ)
        + ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I,
       (((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I);
       (((Real.sin θ * Real.sin (β / 2) : ℝ)) * Complex.I),
       (Real.cos (β / 2) : ℝ)
        - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I]
    := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pulseN, Matrix.star_apply, Fin.mk_zero,
      Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one,
      Complex.star_def, map_sub, map_add, map_mul, map_neg,
      Complex.conj_ofReal, Complex.conj_I]
  all_goals push_cast
  all_goals ring

/-- `N_θ` pulses are unitary. -/
lemma pulseN_mem (θ β : ℝ) :
    pulseN θ β ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, pulseN_star, pulseN,
    Matrix.mul_fin_two,
    show (1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 1] from by
      ext i j
      fin_cases i <;> fin_cases j <;> simp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · push_cast
    ring_nf
    simp only [Complex.I_sq]
    linear_combination
      Complex.sin_sq_add_cos_sq ((β : ℂ) * (1 / 2))
      + Complex.sin ((β : ℂ) * (1 / 2)) ^ 2
        * Complex.sin_sq_add_cos_sq (θ : ℂ)
  · push_cast
    ring
  · push_cast
    ring
  · push_cast
    ring_nf
    simp only [Complex.I_sq]
    linear_combination
      Complex.sin_sq_add_cos_sq ((β : ℂ) * (1 / 2))
      + Complex.sin ((β : ℂ) * (1 / 2)) ^ 2
        * Complex.sin_sq_add_cos_sq (θ : ℂ)

/-- Pulse words: `inl φ` is a longitudinal pulse, `inr β` a
transverse pulse. -/
def pulseWord (θ : ℝ) : List (ℝ ⊕ ℝ) → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | (Sum.inl φ) :: w => pulseZ φ * pulseWord θ w
  | (Sum.inr β) :: w => pulseN θ β * pulseWord θ w

/-- The transverse-pulse count of a word. -/
def transverseCount : List (ℝ ⊕ ℝ) → ℕ
  | [] => 0
  | (Sum.inl _) :: w => transverseCount w
  | (Sum.inr _) :: w => transverseCount w + 1

lemma pulseWord_mem (θ : ℝ) (w : List (ℝ ⊕ ℝ)) :
    pulseWord θ w ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  induction w with
  | nil => exact one_mem _
  | cons p w ih =>
      cases p with
      | inl φ => exact mul_mem (pulseZ_mem φ) ih
      | inr β => exact mul_mem (pulseN_mem θ β) ih

lemma pulseWord_append (θ : ℝ) (w₁ w₂ : List (ℝ ⊕ ℝ)) :
    pulseWord θ (w₁ ++ w₂)
      = pulseWord θ w₁ * pulseWord θ w₂ := by
  induction w₁ with
  | nil => simp [pulseWord]
  | cons p w ih =>
      cases p with
      | inl φ => simp [pulseWord, ih, Matrix.mul_assoc]
      | inr β => simp [pulseWord, ih, Matrix.mul_assoc]

/-- Lower bound: a word with `k` transverse pulses moves the
anchor by at most `kθ`. -/
lemma chiFS_word_le (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.pi / 2) (w : List (ℝ ⊕ ℝ)) :
    chiFS (pulseWord θ w) ≤ transverseCount w * θ := by
  induction w with
  | nil =>
      simp [pulseWord, transverseCount, chiFS]
  | cons p w ih =>
      cases p with
      | inl φ =>
          calc chiFS (pulseZ φ * pulseWord θ w)
              ≤ chiFS (pulseZ φ) + chiFS (pulseWord θ w) :=
                chiFS_mul_le _ _ (pulseZ_mem φ)
                  (pulseWord_mem θ w)
            _ ≤ transverseCount (Sum.inl φ :: w) * θ := by
                rw [chiFS_pulseZ, zero_add]
                exact ih
      | inr β =>
          calc chiFS (pulseN θ β * pulseWord θ w)
              ≤ chiFS (pulseN θ β) + chiFS (pulseWord θ w) :=
                chiFS_mul_le _ _ (pulseN_mem θ β)
                  (pulseWord_mem θ w)
            _ ≤ θ + transverseCount w * θ := by
                have := chiFS_pulseN_le θ β hθ0 hθ
                linarith
            _ = transverseCount (Sum.inr β :: w) * θ := by
                simp only [transverseCount]
                push_cast
                ring

/-- SU(2) entry relations. -/
lemma su2_entries (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : U.det = 1) :
    U 1 1 = starRingEnd ℂ (U 0 0)
      ∧ U 0 1 = -starRingEnd ℂ (U 1 0) := by
  have hadj : U.adjugate = star U := by
    have h1 : U * U.adjugate = 1 := by
      rw [Matrix.mul_adjugate, hdet, one_smul]
    have h2 : star U * U = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hU
    calc U.adjugate = 1 * U.adjugate := (one_mul _).symm
      _ = star U * U * U.adjugate := by rw [h2]
      _ = star U * (U * U.adjugate) := by
          rw [Matrix.mul_assoc]
      _ = star U := by rw [h1, Matrix.mul_one]
  rw [Matrix.adjugate_fin_two] at hadj
  constructor
  · have h3 := congrFun (congrFun hadj 0) 0
    simpa [Matrix.star_apply] using h3
  · have h3 := congrFun (congrFun hadj 0) 1
    simp only [Matrix.star_apply] at h3
    rw [show (!![U 1 1, -U 0 1; -U 1 0, U 0 0]
        : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -U 0 1 from by simp]
      at h3
    rw [show star (U 1 0) = starRingEnd ℂ (U 1 0) from rfl]
      at h3
    linear_combination -h3

/-- The `ZYZ` sandwich in closed form. -/
lemma ZYZ_entries (p q c : ℝ) :
    pulseZ p * pulseY c * pulseZ q
    = !![Complex.exp (((-(p / 2) + -(q / 2) : ℝ)) * Complex.I)
          * (Real.cos (c / 2) : ℝ),
        -(Complex.exp (((-(p / 2) + q / 2 : ℝ)) * Complex.I)
          * (Real.sin (c / 2) : ℝ));
        Complex.exp (((p / 2 + -(q / 2) : ℝ)) * Complex.I)
          * (Real.sin (c / 2) : ℝ),
        Complex.exp (((p / 2 + q / 2 : ℝ)) * Complex.I)
          * (Real.cos (c / 2) : ℝ)] := by
  have hdiag : ∀ d1 d2 a b c' d : ℂ,
      !![d1, 0; 0, d2] * !![a, b; c', d]
        = !![d1 * a, d1 * b; d2 * c', d2 * d] := by
    intro _ _ _ _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag' : ∀ a b c' d e1 e2 : ℂ,
      !![a, b; c', d] * !![e1, 0; 0, e2]
        = !![a * e1, b * e2; c' * e1, d * e2] := by
    intro _ _ _ _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [pulseZ, pulseZ, pulseY, hdiag, hdiag']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · rw [show Complex.exp ((-(p / 2) : ℝ) * Complex.I)
        * (Real.cos (c / 2) : ℝ)
        * Complex.exp ((-(q / 2) : ℝ) * Complex.I)
      = Complex.exp ((-(p / 2) : ℝ) * Complex.I)
        * Complex.exp ((-(q / 2) : ℝ) * Complex.I)
        * (Real.cos (c / 2) : ℝ) from by ring,
      ← Complex.exp_add,
      show ((-(p / 2) : ℝ) : ℂ) * Complex.I
          + ((-(q / 2) : ℝ) : ℂ) * Complex.I
        = ((-(p / 2) + -(q / 2) : ℝ)) * Complex.I from by
        push_cast; ring]
  · rw [show Complex.exp ((-(p / 2) : ℝ) * Complex.I)
        * (-((Real.sin (c / 2) : ℝ)))
        * Complex.exp (((q / 2) : ℝ) * Complex.I)
      = -(Complex.exp ((-(p / 2) : ℝ) * Complex.I)
        * Complex.exp (((q / 2) : ℝ) * Complex.I)
        * (Real.sin (c / 2) : ℝ)) from by ring,
      ← Complex.exp_add,
      show ((-(p / 2) : ℝ) : ℂ) * Complex.I
          + (((q / 2) : ℝ) : ℂ) * Complex.I
        = ((-(p / 2) + q / 2 : ℝ)) * Complex.I from by
        push_cast; ring]
  · rw [show Complex.exp (((p / 2) : ℝ) * Complex.I)
        * ((Real.sin (c / 2) : ℝ))
        * Complex.exp ((-(q / 2) : ℝ) * Complex.I)
      = Complex.exp (((p / 2) : ℝ) * Complex.I)
        * Complex.exp ((-(q / 2) : ℝ) * Complex.I)
        * (Real.sin (c / 2) : ℝ) from by ring,
      ← Complex.exp_add,
      show (((p / 2) : ℝ) : ℂ) * Complex.I
          + ((-(q / 2) : ℝ) : ℂ) * Complex.I
        = ((p / 2 + -(q / 2) : ℝ)) * Complex.I from by
        push_cast; ring]
  · rw [show Complex.exp (((p / 2) : ℝ) * Complex.I)
        * ((Real.cos (c / 2) : ℝ))
        * Complex.exp (((q / 2) : ℝ) * Complex.I)
      = Complex.exp (((p / 2) : ℝ) * Complex.I)
        * Complex.exp (((q / 2) : ℝ) * Complex.I)
        * (Real.cos (c / 2) : ℝ) from by ring,
      ← Complex.exp_add,
      show (((p / 2) : ℝ) : ℂ) * Complex.I
          + (((q / 2) : ℝ) : ℂ) * Complex.I
        = ((p / 2 + q / 2 : ℝ)) * Complex.I from by
        push_cast; ring]

/-- Euler decomposition: `U = Z(α) Y(2χ(U)) Z(γ)`. -/
lemma euler_decomposition (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : U.det = 1) :
    ∃ α γ : ℝ,
      U = pulseZ α * pulseY (2 * chiFS U) * pulseZ γ := by
  obtain ⟨h11, h01⟩ := su2_entries U hU hdet
  set ξ := (U 0 0).arg with hξ
  set ψ := (U 1 0).arg with hψ
  refine ⟨ψ - ξ, -ψ - ξ, ?_⟩
  have hcol := unitary_col_norm U hU
  have hx1 : ‖U 1 0‖ ≤ 1 := norm_entry_le_one U hU
  have hcosχ : Real.cos (chiFS U) = ‖U 0 0‖ := by
    rw [chiFS, Real.cos_arcsin,
      show (1 : ℝ) - ‖U 1 0‖ ^ 2 = ‖U 0 0‖ ^ 2 from by
        linarith, Real.sqrt_sq (norm_nonneg _)]
  have hsinχ : Real.sin (chiFS U) = ‖U 1 0‖ := by
    rw [chiFS, Real.sin_arcsin
      (by linarith [norm_nonneg (U 1 0)]) hx1]
  have ha : U 0 0 = (‖U 0 0‖ : ℂ)
      * Complex.exp ((ξ : ℝ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hb : U 1 0 = (‖U 1 0‖ : ℂ)
      * Complex.exp ((ψ : ℝ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  rw [ZYZ_entries,
    show (2 * chiFS U) / 2 = chiFS U from by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  · rw [ha, ← hcosχ,
      show (-((ψ - ξ) / 2) + -((-ψ - ξ) / 2)) = ξ from by ring]
    ring
  · rw [h01, hb, ← hsinχ,
      show (-((ψ - ξ) / 2) + (-ψ - ξ) / 2) = -ψ from by ring,
      map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show ((ψ : ℝ) : ℂ) * -Complex.I
        = ((-ψ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    ring
  · rw [hb, ← hsinχ,
      show ((ψ - ξ) / 2 + -((-ψ - ξ) / 2)) = ψ from by ring]
    ring
  · rw [h11, ha,
      show ((ψ - ξ) / 2 + (-ψ - ξ) / 2) = -ξ from by ring,
      map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show ((ξ : ℝ) : ℂ) * -Complex.I
        = ((-ξ : ℝ) : ℂ) * Complex.I from by push_cast; ring,
      ← hcosχ]
    ring

/-- Additivity of `Y` rotations. -/
lemma pulseY_add (a b : ℝ) :
    pulseY a * pulseY b = pulseY (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [pulseY, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.mk_zero, Fin.mk_one, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [show (a + b) / 2 = a / 2 + b / 2 from by ring]
      simp only [Real.cos_add, Real.sin_add]
      push_cast
      ring

lemma pulseY_zero : pulseY 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pulseY]

lemma pulseY_pow (η : ℝ) (k : ℕ) :
    pulseY η ^ k = pulseY (k * η) := by
  induction k with
  | zero => simp [pulseY_zero]
  | succ n ih =>
      rw [pow_succ, ih, pulseY_add]
      congr 1
      push_cast
      ring

/-- The repeated middle block as an explicit word. -/
lemma word_repeat (θ β zc : ℝ) (k : ℕ) :
    ∃ w : List (ℝ ⊕ ℝ),
      pulseWord θ w = (pulseN θ β * pulseZ zc) ^ k
        ∧ transverseCount w = k ∧ w.length = 2 * k := by
  induction k with
  | zero => exact ⟨[], by simp [pulseWord], rfl, rfl⟩
  | succ n ih =>
      obtain ⟨w, hw, hc, hl⟩ := ih
      refine ⟨Sum.inr β :: Sum.inl zc :: w, ?_, ?_, ?_⟩
      · simp only [pulseWord]
        rw [hw, pow_succ', Matrix.mul_assoc]
      · simp only [transverseCount]
        rw [hc]
      · simp only [List.length_cons]
        omega

/-- Sandwich power rearrangement. -/
lemma sandwich_pow (A B C : Matrix (Fin 2) (Fin 2) ℂ)
    (k : ℕ) :
    (A * B * C) ^ (k + 1)
      = A * ((B * (C * A)) ^ k * (B * C)) := by
  induction k with
  | zero => simp [Matrix.mul_assoc]
  | succ n ih =>
      rw [pow_succ', ih, pow_succ']
      simp only [Matrix.mul_assoc]

/-- `thm:optimal-transverse-pulse-master`: the boxed count
`k_* = ⌈χ(U)/θ⌉` is a lower bound for every implementing word;
`χ(U) = 0` needs one `Z` pulse; otherwise an explicit exact word
achieves `k_*` transverse pulses within the boxed total
`L_* ≤ 2k_* + 1`. -/
theorem optimal_transverse_pulse (θ : ℝ) (hθ0 : 0 < θ)
    (hθπ : θ ≤ Real.pi / 2) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : U.det = 1) :
    (∀ w : List (ℝ ⊕ ℝ), pulseWord θ w = U →
      ⌈chiFS U / θ⌉₊ ≤ transverseCount w)
    ∧ (chiFS U = 0 → ∃ φ : ℝ, U = pulseZ φ)
    ∧ (chiFS U ≠ 0 → ∃ w : List (ℝ ⊕ ℝ),
        pulseWord θ w = U
          ∧ transverseCount w = ⌈chiFS U / θ⌉₊
          ∧ w.length = 2 * ⌈chiFS U / θ⌉₊ + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have h1 := chiFS_word_le θ hθ0.le hθπ w
    rw [hw] at h1
    rw [Nat.ceil_le, div_le_iff₀ hθ0]
    exact h1
  · intro hchi
    have hb0 : ‖U 1 0‖ = 0 := Real.arcsin_eq_zero_iff.mp hchi
    have hb : U 1 0 = 0 := norm_eq_zero.mp hb0
    obtain ⟨h11, h01⟩ := su2_entries U hU hdet
    have hcol := unitary_col_norm U hU
    have ha1 : ‖U 0 0‖ = 1 := by
      rw [hb0] at hcol
      nlinarith [norm_nonneg (U 0 0)]
    refine ⟨-2 * (U 0 0).arg, ?_⟩
    have ha : U 0 0 = Complex.exp
        (((U 0 0).arg : ℝ) * Complex.I) := by
      have h5 := (Complex.norm_mul_exp_arg_mul_I (U 0 0)).symm
      rwa [ha1, Complex.ofReal_one, one_mul] at h5
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [pulseZ, Fin.mk_zero, Fin.mk_one, Fin.isValue,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
    · rw [show (-(-2 * (U 0 0).arg / 2) : ℝ) = (U 0 0).arg
        from by ring]
      exact ha
    · rw [h01, hb, map_zero, neg_zero]
    · rw [hb]
    · rw [show (-2 * (U 0 0).arg / 2 : ℝ) = -(U 0 0).arg from by
          ring]
      conv_lhs => rw [h11, ha, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      rw [show ((U 0 0).arg : ℂ) * -Complex.I
          = ((-(U 0 0).arg : ℝ) : ℂ) * Complex.I from by
          push_cast; ring]
  · intro hchi
    have hχ0 : 0 < chiFS U := (chiFS_nonneg U).lt_of_ne' hchi
    set k : ℕ := ⌈chiFS U / θ⌉₊ with hk
    have hk1 : 1 ≤ k := by
      rw [hk, Nat.one_le_ceil_iff]
      positivity
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk1
    set η : ℝ := 2 * chiFS U / k with hη
    have hη0 : 0 ≤ η := by positivity
    have hχk : chiFS U ≤ k * θ := by
      have h1 := Nat.le_ceil (chiFS U / θ)
      rw [← hk] at h1
      calc chiFS U = chiFS U / θ * θ := by
            field_simp
        _ ≤ k * θ :=
            mul_le_mul_of_nonneg_right h1 hθ0.le
    have hη2θ : η ≤ 2 * θ := by
      rw [hη, div_le_iff₀ hkr]
      nlinarith
    obtain ⟨α, γ, hEuler⟩ := euler_decomposition U hU hdet
    set s : ℝ := Real.sin (η / 2) / Real.sin θ with hs
    set β : ℝ := 2 * Real.arcsin s with hβ
    set z : ℂ := (Real.cos (β / 2) : ℝ)
      - ((Real.cos θ * Real.sin (β / 2) : ℝ)) * Complex.I
      with hz
    set φ : ℝ := z.arg with hφ
    have hstep := small_transverse_step θ η s β z φ hθ0 hθπ
      hη0 hη2θ hs hβ hz hφ
    have hYk : pulseY (2 * chiFS U) = pulseY η ^ k := by
      rw [pulseY_pow, hη]
      congr 1
      field_simp
    obtain ⟨k1, hk1'⟩ := Nat.exists_eq_add_of_le hk1
    obtain ⟨w1, hw1p, hw1c, hw1l⟩ := word_repeat θ β
      ((φ - Real.pi / 2) + (φ + Real.pi / 2)) k1
    refine ⟨Sum.inl (α + (φ + Real.pi / 2)) :: w1
        ++ [Sum.inr β, Sum.inl ((φ - Real.pi / 2) + γ)],
      ?_, ?_, ?_⟩
    · rw [pulseWord_append,
        show pulseWord θ (Sum.inl (α + (φ + Real.pi / 2)) :: w1)
          = pulseZ (α + (φ + Real.pi / 2)) * pulseWord θ w1
          from rfl,
        hw1p,
        show pulseWord θ [Sum.inr β,
            Sum.inl ((φ - Real.pi / 2) + γ)]
          = pulseN θ β * (pulseZ ((φ - Real.pi / 2) + γ)
            * 1) from rfl,
        Matrix.mul_one, hEuler, hYk, hk1', add_comm 1 k1,
        ← hstep, sandwich_pow, pulseZ_add,
        ← pulseZ_add α (φ + Real.pi / 2),
        ← pulseZ_add (φ - Real.pi / 2) γ]
      simp only [Matrix.mul_assoc]
    · have hcount : ∀ (v₁ v₂ : List (ℝ ⊕ ℝ)),
          transverseCount (v₁ ++ v₂)
            = transverseCount v₁ + transverseCount v₂ := by
        intro v₁ v₂
        induction v₁ with
        | nil => simp [transverseCount]
        | cons p v ih =>
            cases p with
            | inl _ =>
                simp only [List.cons_append, transverseCount]
                rw [ih]
            | inr _ =>
                simp only [List.cons_append, transverseCount]
                rw [ih]
                omega
      simp only [List.cons_append, transverseCount]
      rw [hcount, hw1c]
      simp only [transverseCount]
      omega
    · simp only [List.length_cons, List.length_append, hw1l,
        List.length_nil]
      omega

end

end NCG
