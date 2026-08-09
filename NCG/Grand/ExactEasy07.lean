/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PhaseAxisMoment
import NCG.Grand.DelayedWard

/-!
# Exact EASY batch 07: phase axis and delayed Ward Read
-/

namespace NCG

/-- The complete permutation-fixed subspace in the centred
head/tail coefficient space is the one-dimensional phase axis.
The unnormalised axis vector is `(n,-1,…,-1)`. -/
theorem phase_fixed_subspace (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (n + 1) → ℝ) (hv : ∑ j, v j = 0) :
    (∀ π : Equiv.Perm (Fin n), ∀ i : Fin n,
        v i.succ = v (π i).succ)
      ↔ ∃ t : ℝ, v 0 = n * t ∧ ∀ i : Fin n, v i.succ = -t := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hvsplit : v 0 + ∑ i : Fin n, v i.succ = 0 := by
    rw [← Fin.sum_univ_succ]
    exact hv
  constructor
  · intro hfix
    have htail : ∀ i : Fin n, v i.succ = v i₀.succ := by
      intro i
      have h := hfix (Equiv.swap i₀ i) i₀
      simpa [i₀] using h.symm
    refine ⟨-v i₀.succ, ?_, ?_⟩
    · have hsum : ∑ i : Fin n, v i.succ = n * v i₀.succ := by
        calc
          ∑ i : Fin n, v i.succ = ∑ _i : Fin n, v i₀.succ := by
            apply Finset.sum_congr rfl
            intro i _
            exact htail i
          _ = n * v i₀.succ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
      rw [hsum] at hvsplit
      linarith
    · intro i
      rw [htail i]
      ring
  · rintro ⟨t, _hhead, htail⟩ π i
    rw [htail i, htail (π i)]

/-- The internally regular phase law with a head mass `a` and
uniform tail mass `(1-a)/n`. -/
noncomputable def phaseUniformLaw (n : ℕ) (a : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases a (fun _ => (1 - a) / n)

/-- Uniformity of the regular phase law is equivalent to the
vanishing Ward coordinate and hence to the canonical head mass. -/
theorem phase_uniform_ward (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    (phaseUniformLaw n a = fun _ => 1 / (n + 1 : ℝ))
      ↔ a - (1 - a) / n = 0 := by
  have hward := (ward_coordinate n hn a).1
  rw [hward]
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [phaseUniformLaw] using h0
  · intro ha
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [phaseUniformLaw] using ha
    · simp only [phaseUniformLaw, Fin.cases_succ]
      rw [ha]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- `thm:phase-invariant-axis`, including the previously omitted
complete symmetric-group fixed-space clause. -/
theorem phase_invariant_axis_exact (n : ℕ) (hn : 1 ≤ n) :
    (∀ v : Fin (n + 1) → ℝ, ∑ j, v j = 0 →
      ((∀ π : Equiv.Perm (Fin n), ∀ i : Fin n,
          v i.succ = v (π i).succ)
        ↔ ∃ t : ℝ, v 0 = n * t ∧ ∀ i : Fin n, v i.succ = -t))
    ∧ (∀ a : ℝ,
        (phaseUniformLaw n a = fun _ => 1 / (n + 1 : ℝ))
          ↔ a - (1 - a) / n = 0)
    ∧ (∀ a : ℝ,
        (a - (1 - a) / n = 0 ↔ a = 1 / (n + 1))
        ∧ |a - 1 / (n + 1)| =
          n / (n + 1) * |a - (1 - a) / n|) := by
  refine ⟨?_, ?_, ward_coordinate n hn⟩
  · intro v hv
    exact phase_fixed_subspace n hn v hv
  · exact phase_uniform_ward n hn

/-! ## Delayed binary Read -/

/-- At every positive delay and positive exchange rate, equality
of the two binary Reads is equivalent to zero Ward current and to
the canonical mass. -/
theorem delayed_binary_fixed_read (n : ℕ) (r a t : ℝ)
    (hn : 1 ≤ n) (hr : 0 < r) (ht : 0 < t) :
    let h := fun τ : ℝ => 1 / ((n : ℝ) + 1)
      + (a - 1 / ((n : ℝ) + 1))
        * Real.exp (-((n : ℝ) + 1) * r * τ)
    (h t = h 0 ↔ r * (((n : ℝ) + 1) * a - 1) = 0)
      ∧ (r * (((n : ℝ) + 1) * a - 1) = 0
        ↔ a = 1 / ((n : ℝ) + 1)) := by
  dsimp
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hexp : Real.exp (-((n : ℝ) + 1) * r * t) ≠ 1 := by
    have hprod : 0 < ((n : ℝ) + 1) * r * t :=
      mul_pos (mul_pos hk hr) ht
    have hneg : -((n : ℝ) + 1) * r * t < 0 := by linarith
    exact ne_of_lt (Real.exp_lt_one_iff.mpr hneg)
  have hdelay :
      (1 / ((n : ℝ) + 1)
          + (a - 1 / ((n : ℝ) + 1))
            * Real.exp (-((n : ℝ) + 1) * r * t)
        = 1 / ((n : ℝ) + 1)
          + (a - 1 / ((n : ℝ) + 1))
            * Real.exp (-((n : ℝ) + 1) * r * 0))
      ↔ a = 1 / ((n : ℝ) + 1) := by
    simp only [mul_zero, Real.exp_zero, mul_one]
    constructor
    · intro h
      have hmul : (a - 1 / ((n : ℝ) + 1))
          * Real.exp (-((n : ℝ) + 1) * r * t)
          = (a - 1 / ((n : ℝ) + 1)) * 1 := by linarith
      by_contra hne
      have hc : a - 1 / ((n : ℝ) + 1) ≠ 0 := sub_ne_zero.mpr hne
      exact hexp (mul_left_cancel₀ hc hmul)
    · intro ha
      rw [ha]
      ring
  have hcurrent :
      (r * (((n : ℝ) + 1) * a - 1) = 0
        ↔ a = 1 / ((n : ℝ) + 1)) := by
    constructor
    · intro h
      have hz : ((n : ℝ) + 1) * a - 1 = 0 :=
        (mul_eq_zero.mp h).resolve_left hr.ne'
      rw [eq_div_iff hk.ne']
      linarith
    · intro ha
      rw [ha]
      field_simp
      ring
  exact ⟨hdelay.trans hcurrent.symm, hcurrent⟩

/-- `thm:delayed-binary-Ward`, with the fixed-positive-delay
equivalence appended to the existing ODE/current theorem. -/
theorem delayed_binary_ward_exact (n : ℕ) (r a t : ℝ)
    (hn : 1 ≤ n) (hr : 0 < r) (ht : 0 < t) :
    let h := fun τ : ℝ => 1 / ((n : ℝ) + 1)
      + (a - 1 / ((n : ℝ) + 1))
        * Real.exp (-((n : ℝ) + 1) * r * τ)
    (HasDerivAt h (r * (1 - ((n : ℝ) + 1) * h t)) t)
      ∧ h 0 = a
      ∧ (-((a - 1 / ((n : ℝ) + 1)) * (-((n : ℝ) + 1) * r))
          = r * (((n : ℝ) + 1) * a - 1))
      ∧ (r * (((n : ℝ) + 1) * a - 1)
          = r * n * (a - (1 - a) / n))
      ∧ (h t = h 0 ↔ r * (((n : ℝ) + 1) * a - 1) = 0)
      ∧ (r * (((n : ℝ) + 1) * a - 1) = 0
          ↔ a = 1 / ((n : ℝ) + 1)) := by
  dsimp
  have hbase := delayed_binary_ward n r a t hn
  have hfixed := delayed_binary_fixed_read n r a t hn hr ht
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2,
    hfixed.1, hfixed.2⟩

end NCG
