/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Old root alphabet, independent fast scheduler, and
  complete ADM frame (`thm:relational-scheduler-ADM`,
  Gran-Tensor manuscript)

* `relational_scheduler_ADM`, with the six unoriented
  `A₃` root classes RC.9 in the anchored integral basis
  (`e₁, e₂, e₃, e₂-e₁, e₃-e₁, e₃-e₂`):
  (A1) the six rank-one matrices `r_a r_aᵀ` form a basis
       of `Sym₃` — every symmetric matrix has exactly one
       expansion;
  (A2) the directed-difference map `κ ↦ Σ κ_a r_a` is
       surjective onto `ℝ³` and its kernel is exactly the
       three-dimensional tetrahedral circulation space
       (spanned by the three face-cycle vectors);
  (A3) the exponential-race score frame is faithful: with
       `s_b = 1_{A=b} - k_b T`, direct integration of the
       race law `ℙ(A=a, T∈dt) = k_a e^{-Kt} dt` gives
       `𝔼[s_b s_c] = δ_{bc} k_b / K` (the boxed faithful
       covariance), while winner probabilities alone are
       invariant under a common rate rescaling — they
       lose the common scale;
  (A4) the boxed RC.11 reconstruction
       `g = ϱ^{2/3}(det 𝓑)^{1/3}𝓑⁻¹`,
       `N = ϱ^{1/3}(det 𝓑)^{1/6}` inverts by
       `√(det g) = ϱ` and `N² g⁻¹ = 𝓑` — an analytic
       bijection on the positive cone;
  (A5) an `h`-mesh bracket `𝓑_h ⪰ cI₃` forces total fast
       rate `Σ_a k_a ≥ 3c/(2h²)` (each root has
       `‖r_a‖² ≤ 2`; stated as `3c ≤ 2h² Σ_a k_a`).

The identification of the winning-root observation
process with the abstract Store scheduler `Γ_{X,n}` and
the collapse statement for `O(h⁻¹)` clocks (substituting
the clock scaling into (A5)) are the manuscript's
port-monograph layer.
-/

open Matrix Finset MeasureTheory Set Module

namespace NCG

/-- The six unoriented `A₃` root classes RC.9. -/
def a3SchedulerRoot : Fin 6 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]

/-- The directed-difference (shift) map RC.10. -/
noncomputable def a3ShiftMap :
    (Fin 6 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Matrix.of fun i a => a3SchedulerRoot a i).mulVecLin

/-- The three tetrahedral face-cycle vectors. -/
def a3Cycle : Fin 3 → Fin 6 → ℝ :=
  ![![1, -1, 0, 1, 0, 0],
    ![1, 0, -1, 0, 1, 0],
    ![0, 1, -1, 0, 0, 1]]

/-- Exponential moments of the race clock:
`∫₀^∞ tⁿ e^{-Kt} dt = n! / K^{n+1}`. -/
private lemma exp_moment (K : ℝ) (hK : 0 < K) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(K * t))
      = n.factorial / K ^ (n + 1) := by
  have hsub := integral_comp_mul_left_Ioi
    (fun x => x ^ n * Real.exp (-x)) 0 hK
  simp only [mul_zero] at hsub
  have hL : (∫ x in Ioi (0 : ℝ),
      (K * x) ^ n * Real.exp (-(K * x)))
      = K ^ n * ∫ x in Ioi (0 : ℝ),
        x ^ n * Real.exp (-(K * x)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi
    intro x _
    simp only [mul_pow]
    ring
  have hG : (∫ x in Ioi (0 : ℝ),
      x ^ n * Real.exp (-x)) = n.factorial := by
    have h1 := Real.Gamma_eq_integral
      (s := (n : ℝ) + 1) (by positivity)
    have h2 := Real.Gamma_nat_eq_factorial n
    rw [h1] at h2
    rw [← h2]
    apply MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  rw [hL, hG] at hsub
  have hKne : K ≠ 0 := ne_of_gt hK
  rw [smul_eq_mul] at hsub
  rw [pow_succ]
  field_simp at hsub ⊢
  nlinarith [hsub]

/-- Integrability of the race-moment integrands. -/
private lemma exp_moment_integrable (K : ℝ) (hK : 0 < K)
    (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-(K * t)))
      (Ioi 0) := by
  have h0 := Real.GammaIntegral_convergent
    (s := (n : ℝ) + 1) (by positivity)
  have h1 : IntegrableOn
      (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
    apply h0.congr_fun _ measurableSet_Ioi
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  have h2 := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x ^ n * Real.exp (-x)) 0 hK).mpr
    (by simpa using h1)
  have h3 : IntegrableOn
      (fun x : ℝ => (K ^ n)⁻¹
        * ((K * x) ^ n * Real.exp (-(K * x))))
      (Ioi 0) := h2.const_mul _
  apply h3.congr_fun _ measurableSet_Ioi
  intro x _
  have hKpne : (K : ℝ) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt hK)
  simp only [mul_pow]
  field_simp

/-- `thm:relational-scheduler-ADM` (A1–A5). -/
theorem relational_scheduler_ADM :
    -- (A1) the six rank-one root matrices are a basis
    -- of `Sym₃`
    (∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.IsSymm →
      ∃! c : Fin 6 → ℝ,
        (∑ a, c a • vecMulVec (a3SchedulerRoot a)
          (a3SchedulerRoot a)) = S)
    -- (A2) rank three onto the shift, with kernel the
    -- tetrahedral circulation space
    ∧ (LinearMap.range a3ShiftMap = ⊤
        ∧ LinearMap.ker a3ShiftMap
          = Submodule.span ℝ (Set.range a3Cycle)
        ∧ finrank ℝ (LinearMap.ker a3ShiftMap) = 3)
    -- (A3) the exponential-race score frame is faithful …
    ∧ (∀ k : Fin 6 → ℝ, (∀ a, 0 < k a) →
        ∀ b c : Fin 6,
        (∑ a, ∫ t in Ioi (0 : ℝ),
          ((if a = b then (1 : ℝ) else 0) - k b * t)
          * ((if a = c then (1 : ℝ) else 0) - k c * t)
          * (k a * Real.exp (-((∑ j, k j) * t))))
        = if b = c then k b / (∑ j, k j) else 0)
    -- … while winner probabilities lose the common scale
    ∧ (∀ (k : Fin 6 → ℝ) (lam : ℝ), 0 < lam →
        (∀ a, 0 < k a) → ∀ b,
        (lam * k b) / (∑ j, lam * k j)
          = k b / (∑ j, k j))
    -- (A4) the boxed RC.11 reconstruction inverts
    ∧ (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ),
        0 < ϱ → 0 < B.det →
        (Real.sqrt (((ϱ ^ ((2 : ℝ)/3)
            * B.det ^ ((1 : ℝ)/3)) • B⁻¹).det) = ϱ
        ∧ ((ϱ ^ ((1 : ℝ)/3) * B.det ^ ((1 : ℝ)/6)) ^ 2)
            • ((ϱ ^ ((2 : ℝ)/3)
              * B.det ^ ((1 : ℝ)/3)) • B⁻¹)⁻¹ = B))
    -- (A5) the `h⁻²` scheduler bound
    ∧ (∀ (h c : ℝ) (k : Fin 6 → ℝ), 0 < h →
        (∀ a, 0 ≤ k a) →
        (∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2)
          ≤ v ⬝ᵥ (((h ^ 2) •
            ∑ a, k a • vecMulVec (a3SchedulerRoot a)
              (a3SchedulerRoot a)) *ᵥ v)) →
        3 * c ≤ 2 * h ^ 2 * ∑ a, k a) := by
  -- entry formula for root-matrix expansions
  have hkey : ∀ (c : Fin 6 → ℝ) (i j : Fin 3),
      (∑ a, c a • vecMulVec (a3SchedulerRoot a)
        (a3SchedulerRoot a)) i j
      = ∑ a, c a * (a3SchedulerRoot a i
        * a3SchedulerRoot a j) := by
    intro c i j
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply,
        smul_eq_mul]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- (A1)
    intro S hS
    have hsym : ∀ i j, S i j = S j i := by
      intro i j
      have := congrFun (congrFun hS j) i
      rw [Matrix.transpose_apply] at this
      exact this
    refine ⟨![S 0 0 + S 0 1 + S 0 2,
      S 1 1 + S 0 1 + S 1 2,
      S 2 2 + S 0 2 + S 1 2,
      -S 0 1, -S 0 2, -S 1 2], ?_, ?_⟩
    · ext i j
      rw [hkey]
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) j with rfl | rfl | rfl <;>
        (rw [Fin.sum_univ_six]
         simp only [a3SchedulerRoot, Matrix.cons_val,
           Matrix.cons_val_zero, Matrix.cons_val_one]
         norm_num
         all_goals linarith [hsym 0 1, hsym 0 2, hsym 1 2])
    · intro c' hc'
      have hentry : ∀ i j : Fin 3,
          (∑ a, c' a * (a3SchedulerRoot a i
            * a3SchedulerRoot a j)) = S i j := by
        intro i j
        rw [← hkey, hc']
      have e00 := hentry 0 0
      have e11 := hentry 1 1
      have e22 := hentry 2 2
      have e01 := hentry 0 1
      have e02 := hentry 0 2
      have e12 := hentry 1 2
      rw [Fin.sum_univ_six] at e00 e11 e22 e01 e02 e12
      simp only [a3SchedulerRoot, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one]
        at e00 e11 e22 e01 e02 e12
      norm_num at e00 e11 e22 e01 e02 e12
      funext a
      rcases (by decide : ∀ x : Fin 6, x = 0 ∨ x = 1
          ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5) a
        with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Matrix.cons_val, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;>
        linarith
  · -- (A2) surjectivity
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨![v 0, v 1, v 2, 0, 0, 0], ?_⟩
    funext i
    simp only [a3ShiftMap, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Fin.sum_univ_six]
    rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
        ∨ x = 2) i with rfl | rfl | rfl <;>
      simp [a3SchedulerRoot, Matrix.cons_val]
  · -- (A2) kernel = circulation space
    have hle : Submodule.span ℝ (Set.range a3Cycle)
        ≤ LinearMap.ker a3ShiftMap := by
      rw [Submodule.span_le]
      rintro x ⟨w, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      simp only [a3ShiftMap, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.zero_apply]
      rw [Fin.sum_univ_six]
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) w with rfl | rfl | rfl <;>
        rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        (simp only [a3SchedulerRoot, a3Cycle,
           Matrix.cons_val, Matrix.cons_val_zero,
           Matrix.cons_val_one]
         norm_num)
    have hrange : LinearMap.range a3ShiftMap = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      refine ⟨![v 0, v 1, v 2, 0, 0, 0], ?_⟩
      funext i
      simp only [a3ShiftMap, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [Fin.sum_univ_six]
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        simp [a3SchedulerRoot, Matrix.cons_val]
    have hkerdim : finrank ℝ
        (LinearMap.ker a3ShiftMap) = 3 := by
      have := LinearMap.finrank_range_add_finrank_ker
        a3ShiftMap
      rw [hrange] at this
      rw [finrank_top] at this
      simp only [finrank_pi, Fintype.card_fin] at this
      omega
    have hli : LinearIndependent ℝ a3Cycle := by
      rw [Fintype.linearIndependent_iff]
      intro x hx i
      have h3 := congrFun hx (3 : Fin 6)
      have h4 := congrFun hx (4 : Fin 6)
      have h5 := congrFun hx (5 : Fin 6)
      rw [Fin.sum_univ_three] at h3 h4 h5
      simp only [a3Cycle, Pi.add_apply, Pi.smul_apply,
        Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one,
        smul_eq_mul, Pi.zero_apply] at h3 h4 h5
      norm_num at h3 h4 h5
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        linarith
    have hspandim : finrank ℝ
        (Submodule.span ℝ (Set.range a3Cycle)) = 3 := by
      rw [finrank_span_eq_card hli]
      simp
    exact (Submodule.eq_of_le_of_finrank_le hle
      (by rw [hkerdim, hspandim])).symm
  · -- (A2) kernel dimension
    have hrange : LinearMap.range a3ShiftMap = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      refine ⟨![v 0, v 1, v 2, 0, 0, 0], ?_⟩
      funext i
      simp only [a3ShiftMap, Matrix.mulVecLin_apply,
        Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [Fin.sum_univ_six]
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1
          ∨ x = 2) i with rfl | rfl | rfl <;>
        simp [a3SchedulerRoot, Matrix.cons_val]
    have := LinearMap.finrank_range_add_finrank_ker
      a3ShiftMap
    rw [hrange, finrank_top] at this
    simp only [finrank_pi, Fintype.card_fin] at this
    omega
  · -- (A3) the boxed faithful score covariance
    intro k hk b c
    set K : ℝ := ∑ j, k j with hKdef
    have hK : 0 < K := by
      rw [hKdef]
      exact Finset.sum_pos (fun a _ => hk a)
        Finset.univ_nonempty
    have hKne : K ≠ 0 := ne_of_gt hK
    have hI0 := exp_moment K hK 0
    have hI1 := exp_moment K hK 1
    have hI2 := exp_moment K hK 2
    have hJ0 := exp_moment_integrable K hK 0
    have hJ1 := exp_moment_integrable K hK 1
    have hJ2 := exp_moment_integrable K hK 2
    -- each per-winner integral in closed form
    have hint : ∀ a : Fin 6,
        (∫ t in Ioi (0 : ℝ),
          ((if a = b then (1 : ℝ) else 0) - k b * t)
          * ((if a = c then (1 : ℝ) else 0) - k c * t)
          * (k a * Real.exp (-(K * t))))
        = (k a * ((if a = b then (1 : ℝ) else 0)
            * (if a = c then (1 : ℝ) else 0))) * K⁻¹
          - (k a * ((if a = b then (1 : ℝ) else 0) * k c
            + (if a = c then (1 : ℝ) else 0) * k b))
            * (K ^ 2)⁻¹
          + k a * (k b * (k c * (2 * (K ^ 3)⁻¹))) := by
      intro a
      have hfun : Set.EqOn
          (fun t : ℝ =>
            ((if a = b then (1 : ℝ) else 0) - k b * t)
            * ((if a = c then (1 : ℝ) else 0) - k c * t)
            * (k a * Real.exp (-(K * t))))
          (fun t : ℝ =>
            (k a * ((if a = b then (1 : ℝ) else 0)
              * (if a = c then (1 : ℝ) else 0)))
              * (t ^ 0 * Real.exp (-(K * t)))
            + (-(k a * ((if a = b then (1 : ℝ) else 0)
                * k c
              + (if a = c then (1 : ℝ) else 0) * k b)))
              * (t ^ 1 * Real.exp (-(K * t)))
            + (k a * (k b * k c))
              * (t ^ 2 * Real.exp (-(K * t))))
          (Ioi 0) := by
        intro t _
        simp only
        ring
      rw [MeasureTheory.setIntegral_congr_fun
        measurableSet_Ioi hfun]
      have hA : IntegrableOn (fun t : ℝ =>
          (k a * ((if a = b then (1 : ℝ) else 0)
            * (if a = c then (1 : ℝ) else 0)))
            * (t ^ 0 * Real.exp (-(K * t)))
          + (-(k a * ((if a = b then (1 : ℝ) else 0)
              * k c
            + (if a = c then (1 : ℝ) else 0) * k b)))
            * (t ^ 1 * Real.exp (-(K * t))))
          (Ioi 0) :=
        (hJ0.const_mul _).add (hJ1.const_mul _)
      rw [MeasureTheory.integral_add hA
        (hJ2.const_mul _)]
      rw [MeasureTheory.integral_add
        (hJ0.const_mul _) (hJ1.const_mul _)]
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      rw [hI0, hI1, hI2]
      simp only [Nat.factorial]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl fun a _ => hint a]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul,
      ← Finset.sum_mul]
    have hs1 : (∑ a, k a
        * ((if a = b then (1 : ℝ) else 0)
          * (if a = c then (1 : ℝ) else 0)))
        = if b = c then k b else 0 := by
      rw [Finset.sum_eq_single b]
      · by_cases hbc : b = c <;> simp [hbc]
      · intro a _ ha
        simp [ha]
      · intro h
        exact absurd (Finset.mem_univ b) h
    have hs2 : (∑ a, k a
        * ((if a = b then (1 : ℝ) else 0) * k c
          + (if a = c then (1 : ℝ) else 0) * k b))
        = k b * k c + k c * k b := by
      have hsplit : ∀ a : Fin 6, k a
          * ((if a = b then (1 : ℝ) else 0) * k c
            + (if a = c then (1 : ℝ) else 0) * k b)
          = k a * ((if a = b then (1 : ℝ) else 0) * k c)
            + k a * ((if a = c then (1 : ℝ) else 0)
              * k b) := fun a => by ring
      rw [Finset.sum_congr rfl fun a _ => hsplit a,
        Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_eq_single b]
        · simp
        · intro a _ ha
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · rw [Finset.sum_eq_single c]
        · simp [mul_comm]
        · intro a _ ha
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ c) h
    rw [hs1, hs2]
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl, if_pos rfl]
      field_simp
      ring
    · rw [if_neg hbc, if_neg hbc]
      field_simp
      ring
  · -- (A3') winner probabilities lose the common scale
    intro k lam hlam hk b
    have hKpos : 0 < ∑ j, k j :=
      Finset.sum_pos (fun a _ => hk a)
        Finset.univ_nonempty
    rw [← Finset.mul_sum]
    rw [mul_div_mul_left _ _ (ne_of_gt hlam)]
  · -- (A4) the RC.11 reconstruction inverts
    intro B ϱ hϱ hdet
    have hdet' : IsUnit B.det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hdet)
    set c1 : ℝ := ϱ ^ ((2 : ℝ)/3)
      * B.det ^ ((1 : ℝ)/3) with hc1
    have hc1pos : 0 < c1 := by
      rw [hc1]
      positivity
    have hcube : c1 ^ 3 = ϱ ^ 2 * B.det := by
      have ha : ((2 : ℝ)/3) * ((3 : ℕ) : ℝ)
          = ((2 : ℕ) : ℝ) := by norm_num
      have hb : ((1 : ℝ)/3) * ((3 : ℕ) : ℝ)
          = ((1 : ℕ) : ℝ) := by norm_num
      rw [hc1, mul_pow,
        ← Real.rpow_natCast (ϱ ^ ((2 : ℝ)/3)) 3,
        ← Real.rpow_natCast (B.det ^ ((1 : ℝ)/3)) 3,
        ← Real.rpow_mul (le_of_lt hϱ),
        ← Real.rpow_mul (le_of_lt hdet), ha, hb,
        Real.rpow_natCast, Real.rpow_natCast]
      norm_num
    constructor
    · rw [Matrix.det_smul, Matrix.det_nonsing_inv]
      simp only [Fintype.card_fin]
      rw [hcube, Ring.inverse_eq_inv]
      have hcancel : ϱ ^ 2 * B.det * B.det⁻¹
          = ϱ ^ 2 := by
        field_simp
      rw [hcancel, Real.sqrt_sq (le_of_lt hϱ)]
    · have hN2 : (ϱ ^ ((1 : ℝ)/3)
          * B.det ^ ((1 : ℝ)/6)) ^ 2 = c1 := by
        have ha : ((1 : ℝ)/3) * ((2 : ℕ) : ℝ)
            = (2 : ℝ)/3 := by norm_num
        have hb : ((1 : ℝ)/6) * ((2 : ℕ) : ℝ)
            = (1 : ℝ)/3 := by norm_num
        rw [mul_pow,
          ← Real.rpow_natCast (ϱ ^ ((1 : ℝ)/3)) 2,
          ← Real.rpow_natCast (B.det ^ ((1 : ℝ)/6)) 2,
          ← Real.rpow_mul (le_of_lt hϱ),
          ← Real.rpow_mul (le_of_lt hdet), ha, hb, hc1]
      have hginv : ((c1 • B⁻¹)⁻¹ :
          Matrix (Fin 3) (Fin 3) ℝ) = c1⁻¹ • B := by
        apply Matrix.inv_eq_right_inv
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hc1pos),
          Matrix.nonsing_inv_mul B hdet', one_smul]
      rw [hN2, hginv, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hc1pos), one_smul]
  · -- (A5) the scheduler bound
    intro h c k hh hk hpsd
    have hsingle : ∀ (i : Fin 3) (w : Fin 3 → ℝ),
        Pi.single i (1 : ℝ) ⬝ᵥ w = w i := by
      intro i w
      rw [dotProduct, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hdiag : ∀ i : Fin 3, c ≤ h ^ 2
        * ∑ a, k a * (a3SchedulerRoot a i) ^ 2 := by
      intro i
      have hp := hpsd (Pi.single i 1)
      have hLHS : (∑ j,
          (Pi.single i (1 : ℝ) : Fin 3 → ℝ) j ^ 2)
          = 1 := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hLHS, mul_one, hsingle] at hp
      have hMv : (((h ^ 2) • ∑ a, k a
          • vecMulVec (a3SchedulerRoot a)
            (a3SchedulerRoot a)) *ᵥ
          Pi.single i (1 : ℝ)) i
          = ((h ^ 2) • ∑ a, k a
            • vecMulVec (a3SchedulerRoot a)
              (a3SchedulerRoot a)) i i := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same, mul_one]
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj, mul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hMv] at hp
      have hentry : ((h ^ 2) • ∑ a, k a
          • vecMulVec (a3SchedulerRoot a)
            (a3SchedulerRoot a)) i i
          = h ^ 2 * ∑ a, k a
            * (a3SchedulerRoot a i) ^ 2 := by
        rw [Matrix.smul_apply, hkey k i i, smul_eq_mul]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by
          rw [sq]
      rw [hentry] at hp
      exact hp
    have h0 := hdiag 0
    have h1 := hdiag 1
    have h2 := hdiag 2
    rw [Fin.sum_univ_six] at h0 h1 h2
    simp only [a3SchedulerRoot, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one]
      at h0 h1 h2
    norm_num at h0 h1 h2
    rw [Fin.sum_univ_six]
    nlinarith [mul_nonneg (sq_nonneg h) (hk 0),
      mul_nonneg (sq_nonneg h) (hk 1),
      mul_nonneg (sq_nonneg h) (hk 2),
      mul_nonneg (sq_nonneg h) (hk 3),
      mul_nonneg (sq_nonneg h) (hk 4),
      mul_nonneg (sq_nonneg h) (hk 5)]

end NCG
