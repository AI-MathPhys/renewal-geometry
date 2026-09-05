/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mass–prefix identity and the Fourier boundary identity
  (`thm:mass-prefix`, `lem:fourier-boundary`, arithmetic monograph)

For Hilbert-valued discrepancy coefficients `d₀, …, d_N` with total
mass `M = Σ d_c` and prefixes `q_c = Σ_{r ≤ c} d_r`:

* `mass_prefix_bilinear` — the exact Abel resummation
  `Σ_c B(d_c, F_c) = B(M, F_N) + Σ_{c<N} B(q_c, F_c − F_{c+1})`
  for any bilinear pairing `B`;
* `mass_prefix` — the manuscript display, with `B` the tensor
  product: `𝒞_F(d) = M ⊗ T_{s_N}F + Σ q_c ⊗ (T_{s_c}F − T_{s_{c+1}}F)`
  (the translated ports `T_{s_c}F` enter only through their values,
  so the statement is for an arbitrary family `F c` of vectors);
* `stepPrefix` — the step prefix field `J_d(s) = q_c` on
  `[s_c, s_{c+1})`, vanishing outside `[s_0, s_N)`;
* `fourier_boundary` — `Σ_c e^{its_c} d_c = e^{its_N} M
  − it ∫ e^{its} J_d(s) ds`, valid for all real `t`;
* `fourier_boundary_unitary` — the boxed display with the unitary
  transform `Ĵ_d(t) = (2π)^{−1/2} ∫ e^{its} J_d(s) ds` (defined
  in-file as `unitaryHat`), so the boundary term is `it√(2π)·Ĵ_d(t)`.
-/

open Finset MeasureTheory Set Complex

namespace NCG

section Algebraic

variable {H E G : Type*} [AddCommGroup H] [Module ℂ H]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup G] [Module ℂ G]

/-- Total mass `M(d) = Σ_{c=0}^N d_c`. -/
def totalMass (d : ℕ → H) (N : ℕ) : H := ∑ c ∈ Finset.range (N + 1), d c

/-- Prefix mass `q_c(d) = Σ_{r=0}^c d_r`. -/
def prefixMass (d : ℕ → H) (c : ℕ) : H := ∑ r ∈ Finset.range (c + 1), d r

omit [Module ℂ E] in
/-- Telescoping tail: `Σ_{c=r}^{N-1} (F_c − F_{c+1}) = F_r − F_N`. -/
private lemma telescope_Ico (F : ℕ → E) {r N : ℕ} (hr : r ≤ N) :
    (∑ c ∈ Finset.Ico r N, (F c - F (c + 1))) = F r - F N := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := Finset.sum_range_sub' (fun i => F (r + i)) (N - r)
  simp only [← Nat.add_assoc] at h
  rw [h, Nat.add_sub_cancel' hr, Nat.add_zero]

/-- `thm:mass-prefix` in bilinear form: for any bilinear pairing `B`,
`Σ_c B(d_c, F_c) = B(M, F_N) + Σ_{c<N} B(q_c, F_c − F_{c+1})`. -/
theorem mass_prefix_bilinear (B : H →ₗ[ℂ] E →ₗ[ℂ] G)
    (d : ℕ → H) (F : ℕ → E) (N : ℕ) :
    (∑ c ∈ Finset.range (N + 1), B (d c) (F c))
      = B (totalMass d N) (F N)
        + ∑ c ∈ Finset.range N, B (prefixMass d c) (F c - F (c + 1)) := by
  have hswap : (∑ c ∈ Finset.range N, ∑ r ∈ Finset.range (c + 1),
        B (d r) (F c - F (c + 1)))
      = ∑ r ∈ Finset.range N, B (d r) (F r - F N) := by
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_Ico_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [← map_sum, telescope_Ico F (Finset.mem_Ico.mp hr).2.le]
  simp only [prefixMass, totalMass, map_sum, LinearMap.sum_apply]
  rw [hswap]
  simp only [map_sub, Finset.sum_sub_distrib, Finset.sum_range_succ]
  abel

open TensorProduct in
/-- `thm:mass-prefix` (manuscript display): the correlation packet
`𝒞_F(d) = Σ_c d_c ⊗ F_c` resums as
`M(d) ⊗ F_N + Σ_{c<N} q_c(d) ⊗ (F_c − F_{c+1})`. -/
theorem mass_prefix (d : ℕ → H) (F : ℕ → E) (N : ℕ) :
    (∑ c ∈ Finset.range (N + 1), d c ⊗ₜ[ℂ] F c)
      = totalMass d N ⊗ₜ[ℂ] F N
        + ∑ c ∈ Finset.range N, prefixMass d c ⊗ₜ[ℂ] (F c - F (c + 1)) := by
  simpa using mass_prefix_bilinear (TensorProduct.mk ℂ H E) d F N

/-- `thm:mass-prefix` in scalar-coefficient form:
`Σ_c z_c • d_c = z_N • M + Σ_{c<N} (z_c − z_{c+1}) • q_c`. -/
theorem mass_prefix_smul (d : ℕ → H) (z : ℕ → ℂ) (N : ℕ) :
    (∑ c ∈ Finset.range (N + 1), z c • d c)
      = z N • totalMass d N
        + ∑ c ∈ Finset.range N, (z c - z (c + 1)) • prefixMass d c := by
  simpa using mass_prefix_bilinear ((LinearMap.lsmul ℂ H).flip) d z N

end Algebraic

section Analytic

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [CompleteSpace H]

/-- The step prefix field `J_d(s) = q_c(d)` on `[s_c, s_{c+1})`,
vanishing outside `[s_0, s_N)`. -/
noncomputable def stepPrefix (d : ℕ → H) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) : H :=
  ∑ c ∈ Finset.range N,
    (Set.Ico (s c) (s (c + 1))).indicator (fun _ => prefixMass d c) u

/-- `lem:fourier-boundary` (integral form): for every real `t`,
`Σ_c e^{its_c} d_c = e^{its_N} M(d) − it ∫ e^{its} J_d(s) ds`. -/
theorem fourier_boundary (d : ℕ → H) (s : ℕ → ℝ) (N : ℕ)
    (hs : Monotone s) (t : ℝ) :
    (∑ c ∈ Finset.range (N + 1),
        Complex.exp ((t : ℂ) * s c * Complex.I) • d c)
      = Complex.exp ((t : ℂ) * s N * Complex.I) • totalMass d N
        - (Complex.I * t) •
            ∫ u : ℝ, Complex.exp ((t : ℂ) * u * Complex.I) •
              stepPrefix d s N u := by
  by_cases ht : t = 0
  · subst ht
    simp [totalMass]
  -- the frequency `it` is nonzero
  have hit : Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)
  -- pointwise: pull the scalar inside each indicator
  have hpt : ∀ u : ℝ,
      Complex.exp ((t : ℂ) * u * Complex.I) • stepPrefix d s N u
        = ∑ c ∈ Finset.range N,
            (Set.Ico (s c) (s (c + 1))).indicator
              (fun x => Complex.exp ((t : ℂ) * x * Complex.I) •
                prefixMass d c) u := by
    intro u
    rw [stepPrefix, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hu : u ∈ Set.Ico (s c) (s (c + 1))
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu,
        smul_zero]
  -- each piece is integrable
  have hint : ∀ c : ℕ, Integrable
      ((Set.Ico (s c) (s (c + 1))).indicator
        (fun x => Complex.exp ((t : ℂ) * x * Complex.I) •
          prefixMass d c)) := by
    intro c
    refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ico)
    have hcont : Continuous fun x : ℝ =>
        Complex.exp ((t : ℂ) * x * Complex.I) • prefixMass d c := by
      fun_prop
    exact hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  -- evaluate the integral piecewise
  have hInt : (∫ u : ℝ, Complex.exp ((t : ℂ) * u * Complex.I) •
        stepPrefix d s N u)
      = ∑ c ∈ Finset.range N,
          ((Complex.exp ((t : ℂ) * s (c + 1) * Complex.I)
              - Complex.exp ((t : ℂ) * s c * Complex.I))
            / (Complex.I * t)) • prefixMass d c := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_finsetSum _ fun c _ => hint c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MeasureTheory.integral_indicator measurableSet_Ico,
      MeasureTheory.integral_Ico_eq_integral_Ioc,
      integral_smul_const,
      ← intervalIntegral.integral_of_le (hs (Nat.le_add_right c 1))]
    congr 1
    have hform : ∀ u : ℝ, Complex.exp ((t : ℂ) * u * Complex.I)
        = Complex.exp ((Complex.I * t) * u) := by
      intro u
      ring_nf
    rw [intervalIntegral.integral_congr fun u _ => hform u,
      integral_exp_mul_complex hit]
    congr 1
    congr 1 <;> · congr 1; ring
  rw [hInt, Finset.smul_sum]
  -- cancel `it` against the divided exponential differences
  have hcancel : ∀ c : ℕ,
      (Complex.I * (t : ℂ)) •
        (((Complex.exp ((t : ℂ) * s (c + 1) * Complex.I)
            - Complex.exp ((t : ℂ) * s c * Complex.I))
          / (Complex.I * t)) • prefixMass d c)
        = (Complex.exp ((t : ℂ) * s (c + 1) * Complex.I)
            - Complex.exp ((t : ℂ) * s c * Complex.I)) •
              prefixMass d c := by
    intro c
    rw [smul_smul, mul_comm, div_mul_cancel₀ _ hit]
  rw [Finset.sum_congr rfl fun c _ => hcancel c]
  -- conclude by the scalar mass–prefix identity
  have habel := mass_prefix_smul d
    (fun c => Complex.exp ((t : ℂ) * s c * Complex.I)) N
  rw [habel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← neg_smul, neg_sub]

/-- The unitary Fourier transform used in the manuscript display:
`Ĵ(t) = (2π)^{−1/2} ∫ e^{its} J(s) ds`. -/
noncomputable def unitaryHat (J : ℝ → H) (t : ℝ) : H :=
  ((Real.sqrt (2 * Real.pi) : ℂ))⁻¹ •
    ∫ u : ℝ, Complex.exp ((t : ℂ) * u * Complex.I) • J u

/-- `lem:fourier-boundary` (boxed display): with the unitary Fourier
transform, `Σ_c e^{its_c} d_c = e^{its_N} M(d) − it√(2π)·Ĵ_d(t)`. -/
theorem fourier_boundary_unitary (d : ℕ → H) (s : ℕ → ℝ) (N : ℕ)
    (hs : Monotone s) (t : ℝ) :
    (∑ c ∈ Finset.range (N + 1),
        Complex.exp ((t : ℂ) * s c * Complex.I) • d c)
      = Complex.exp ((t : ℂ) * s N * Complex.I) • totalMass d N
        - (Complex.I * t * (Real.sqrt (2 * Real.pi) : ℂ)) •
            unitaryHat (stepPrefix d s N) t := by
  have hsqrt : ((Real.sqrt (2 * Real.pi) : ℂ)) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr ?_
    positivity
  rw [fourier_boundary d s N hs t]
  congr 1
  rw [unitaryHat, smul_smul, mul_assoc,
    mul_inv_cancel₀ hsqrt, mul_one]

end Analytic

end NCG
