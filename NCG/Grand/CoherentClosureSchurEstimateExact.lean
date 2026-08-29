/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CoherentClosureQuantitativeEnvelope
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Exact Loewner and Schur estimates for coherent source closure

This file supplies the order-theoretic estimate in
`thm:SMST-reducing-coherent-closure`.  The point is that the Gram
`a⋆a` commutes with every entire function of a normal generator `a`.
Consequently a norm estimate on the coherent writer is also an estimate
relative to the source Gram, including on a Gram with a nontrivial kernel.
-/

open NormedSpace Filter Topology

namespace NCG
namespace CoherentClosureSchurEstimateExact

/-- A positive Gram commuting with a multiplier absorbs the usual C⋆ norm
bound relative to itself.  This is the abstract Loewner step used by the
coherent-source estimate. -/
theorem commuting_gram_conjugate_le_norm_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (c d : A) (hc : 0 ≤ c) (hcd : Commute c d) :
    star d * c * d ≤ ‖d‖ ^ 2 • c := by
  have hcstar : star c = c := hc.isSelfAdjoint.star_eq
  have hcdstar : Commute c (star d) := by
    change c * star d = star d * c
    have h := congrArg star hcd.eq
    simpa only [star_mul, star_star, hcstar] using h.symm
  have hcq : Commute c (star d * d) := hcdstar.mul_right hcd
  have hq : star d * d ≤ algebraMap ℝ A (‖d‖ ^ 2) :=
    CStarAlgebra.star_mul_le_algebraMap_norm_sq
  rw [← sub_nonneg]
  have hdiff : 0 ≤ algebraMap ℝ A (‖d‖ ^ 2) - star d * d :=
    sub_nonneg.mpr hq
  have hcalg : Commute c (algebraMap ℝ A (‖d‖ ^ 2)) := by
    change c * algebraMap ℝ A (‖d‖ ^ 2) =
      algebraMap ℝ A (‖d‖ ^ 2) * c
    exact (Algebra.commutes _ _).symm
  have hcommdiff : Commute c
      (algebraMap ℝ A (‖d‖ ^ 2) - star d * d) :=
    hcalg.sub_right hcq
  have hprod := hcommdiff.mul_nonneg hc hdiff
  convert hprod using 1
  calc
    ‖d‖ ^ 2 • c - star d * c * d =
        c * algebraMap ℝ A (‖d‖ ^ 2) - c * (star d * d) := by
      congr 1
      · rw [Algebra.smul_def]
        exact Algebra.commutes _ _
      · rw [hcdstar.eq.symm, mul_assoc]
    _ = c * (algebraMap ℝ A (‖d‖ ^ 2) - star d * d) := by
      rw [mul_sub]

/-- If the multiplier norm is bounded by `K`, the relative Gram estimate has
coefficient `K²`. -/
theorem commuting_gram_conjugate_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (c d : A) (K : ℝ) (hc : 0 ≤ c) (hcd : Commute c d)
    (hK : ‖d‖ ≤ K) :
    star d * c * d ≤ K ^ 2 • c := by
  refine (commuting_gram_conjugate_le_norm_sq c d hc hcd).trans ?_
  have hK0 : 0 ≤ K := (norm_nonneg d).trans hK
  exact smul_le_smul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg d) hK0).2 hK) hc

/-- For a normal generator, its source Gram commutes with the coherent writer
defined by the odd-factorial entire series. -/
theorem coherentWriter_commutes_sourceGram
    {A : Type*} [CStarAlgebra A]
    (a W : A) (t : ℝ) (ha : IsStarNormal a)
    (hW : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
        a ^ (2 * k)) W) :
    Commute (star a * a) W := by
  have hca : Commute (star a * a) a := by
    change (star a * a) * a = a * (star a * a)
    calc
      star a * a * a = (a * star a) * a := by rw [ha.star_comm_self.eq]
      _ = a * (star a * a) := by rw [mul_assoc]
  have hterm : ∀ k : ℕ, Commute (star a * a)
      ((t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
        a ^ (2 * k)) := fun k =>
    (hca.pow_right (2 * k)).smul_right _
  have hl := hW.mul_left (star a * a)
  have hr := hW.mul_right (star a * a)
  exact hl.unique (hr.congr_fun fun k => (hterm k).eq)

/-- The manuscript's assembled coherent-writer Loewner estimate. -/
theorem coherentWriter_sourceGram_loewner
    {A : Type*} [CStarAlgebra A] [NormOneClass A]
    [PartialOrder A] [StarOrderedRing A]
    (a W : A) (t M : ℝ) (ht : 0 ≤ t) (haNorm : ‖a‖ ≤ M)
    (ha : IsStarNormal a)
    (hW : HasSum (fun k : ℕ =>
      (t ^ (2 * k) / (((2 * k + 1).factorial : ℝ))) •
        a ^ (2 * k)) W) :
    star (W - 1) * (star a * a) * (W - 1) ≤
      (t ^ 4 * M ^ 4 * Real.exp (2 * t * M) / 36) •
        (star a * a) := by
  have hc : 0 ≤ star a * a := star_mul_self_nonneg a
  have hcommW := coherentWriter_commutes_sourceGram a W t ha hW
  have hcomm : Commute (star a * a) (W - 1) :=
    hcommW.sub_right (Commute.one_right _)
  have hnorm :=
    CoherentClosureQuantitativeEnvelope.coherentWriter_sub_one_norm_le
      a W t M ht haNorm hW
  have h := commuting_gram_conjugate_le (star a * a) (W - 1)
    (t ^ 2 * M ^ 2 * Real.exp (t * M) / 6) hc hcomm hnorm
  convert h using 1
  ring_nf
  rw [show t * M * 2 = t * M + t * M by ring, Real.exp_add, pow_two]

/-- A residual factored through the regularity square root satisfies the
corresponding Schur-form estimate.  Splitting the factored residual into its
source-core and polarization parts gives precisely the square of the sum of
the two error bounds. -/
theorem factored_residual_schur_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (Zcore Zpol s E : A) (Kcore Kpol : ℝ)
    (hE : E = (Zcore + Zpol) * s)
    (hcore : ‖Zcore‖ ≤ Kcore) (hpol : ‖Zpol‖ ≤ Kpol) :
    star E * E ≤ (Kcore + Kpol) ^ 2 • (star s * s) := by
  have hnorm : ‖Zcore + Zpol‖ ≤ Kcore + Kpol :=
    (norm_add_le _ _).trans (add_le_add hcore hpol)
  have hconj := CStarAlgebra.star_left_conjugate_le_norm_smul
    (a := s) (b := star (Zcore + Zpol) * (Zcore + Zpol))
    (IsSelfAdjoint.star_mul_self _)
  have hnormGram : ‖star (Zcore + Zpol) * (Zcore + Zpol)‖ =
      ‖Zcore + Zpol‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self, pow_two]
  rw [hnormGram] at hconj
  calc
    star E * E = star s *
        (star (Zcore + Zpol) * (Zcore + Zpol)) * s := by
      rw [hE, star_mul]
      simp only [mul_assoc]
    _ ≤ ‖Zcore + Zpol‖ ^ 2 • (star s * s) := hconj
    _ ≤ (Kcore + Kpol) ^ 2 • (star s * s) := by
      have hK0 : 0 ≤ Kcore + Kpol := (norm_nonneg _).trans hnorm
      exact smul_le_smul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hK0).2 hnorm) (star_mul_self_nonneg s)

/-! ## The local principal logarithm -/

/-- The principal logarithm on the norm ball `‖W-1‖ < 1`, represented by
its convergent Mercator series.  Only this local branch is needed as the
physical step tends to zero. -/
noncomputable def localPrincipalLog
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (W : A) : A :=
  ∑' n : ℕ, (((-1 : ℝ) ^ n) / (n + 1 : ℝ)) • (W - 1) ^ (n + 1)

set_option maxHeartbeats 500000 in
/-- On the half-unit ball the local principal logarithm is Lipschitz with
constant two. -/
theorem norm_localPrincipalLog_le_two
    {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (W : A) (hW : ‖W - 1‖ ≤ 1 / 2) :
    ‖localPrincipalLog W‖ ≤ 2 * ‖W - 1‖ := by
  let r : ℝ := ‖W - 1‖
  let f : ℕ → A := fun n =>
    (((-1 : ℝ) ^ n) / (n + 1 : ℝ)) • (W - 1) ^ (n + 1)
  let g : ℕ → ℝ := fun n => 2 * r * (1 / 2 : ℝ) ^ (n + 1)
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr : r ≤ 1 / 2 := hW
  have hg : Summable g := by
    have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [pow_succ'] using
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2 : ℝ)
    exact hs.mul_left (2 * r)
  have hterm (n : ℕ) : ‖f n‖ ≤ g n := by
    have hcoeff : |((-1 : ℝ) ^ n) / (n + 1 : ℝ)| ≤ 1 := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow : r ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
      pow_le_pow_left₀ hr0 hr _
    calc
      ‖f n‖ = |((-1 : ℝ) ^ n) / (n + 1 : ℝ)| *
          ‖(W - 1) ^ (n + 1)‖ := by
        simp only [f, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * r ^ (n + 1) := by
        gcongr
        exact norm_pow_le _ _
      _ ≤ 2 * r * (1 / 2 : ℝ) ^ (n + 1) := by
        have hr2 : r ^ (n + 1) ≤
            2 * r * (1 / 2 : ℝ) ^ (n + 1) := by
          calc
            r ^ (n + 1) = r * r ^ n := by rw [pow_succ']
            _ ≤ r * (1 / 2 : ℝ) ^ n := by gcongr
            _ = 2 * r * (1 / 2 : ℝ) ^ (n + 1) := by
              rw [pow_succ']
              ring
        simpa using hr2
      _ = g n := rfl
  have hf : Summable f := hg.of_norm_bounded hterm
  have hfnorm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hg
  calc
    ‖localPrincipalLog W‖ = ‖∑' n, f n‖ := by rfl
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hfnorm
    _ ≤ ∑' n, g n := hfnorm.tsum_le_tsum hterm hg
    _ = 2 * r := by
      simp only [g]
      rw [tsum_mul_left]
      have hs := hasSum_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
      rw [show (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1)) = 1 by
        rw [show (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) =
            fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n by
          funext n; rw [pow_succ']]
        rw [tsum_mul_left, hs.tsum_eq]
        norm_num]
      ring
    _ = 2 * ‖W - 1‖ := rfl

/-- A quadratic approach to the identity makes the physical-step logarithm
vanish.  Here `localPrincipalLog` is the principal branch because the
hypotheses eventually place `W(t)` in the half-unit ball around `1`. -/
theorem localPrincipalLog_div_physicalStep_tendsto_zero
    {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A]
    (W : ℝ → A) (K : ℝ) (hK : 0 ≤ K)
    (hquad : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      ‖W t - 1‖ ≤ K * t ^ 2)
    (hhalf : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      ‖W t - 1‖ ≤ 1 / 2) :
    Tendsto (fun t : ℝ => (2 * t)⁻¹ • localPrincipalLog (W t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto (fun t : ℝ => K * t)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => K * t) :=
      continuous_const.mul continuous_id
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
  filter_upwards [hquad, hhalf, self_mem_nhdsWithin] with t htquad hthalf htpos
  have ht : 0 < t := htpos
  have hlog := norm_localPrincipalLog_le_two (W t) hthalf
  calc
    ‖(2 * t)⁻¹ • localPrincipalLog (W t)‖ =
        (2 * t)⁻¹ * ‖localPrincipalLog (W t)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) ht))]
    _ ≤ (2 * t)⁻¹ * (2 * ‖W t - 1‖) := by gcongr
    _ ≤ (2 * t)⁻¹ * (2 * (K * t ^ 2)) := by gcongr
    _ = K * t := by field_simp

end CoherentClosureSchurEstimateExact
end NCG
