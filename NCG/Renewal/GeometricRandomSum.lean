/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Geometric random sums of discrete waiting times

This module supplies the probability-law layer used by accepted-response
renewal.  A base waiting-time `PMF` is convolved independently a prescribed
number of times, and then mixed by the geometric law for the number of
failures before the first accepted opportunity.
-/

namespace NCG

open scoped ENNReal

/-- Convolution of two natural-valued probability mass functions, implemented
by independent monadic sampling followed by addition. -/
noncomputable def natPMFConvolution (p q : PMF ℕ) : PMF ℕ :=
  p.bind fun a => q.map fun b => a + b

/-- Sum of `n` iid samples from a natural-valued probability law. -/
noncomputable def iidNatSum (p : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 => natPMFConvolution p (iidNatSum p n)

/-- The number of completed opportunities through the first acceptance is
one plus a geometric number of failures. -/
noncomputable def geometricOpportunityCount (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) : PMF ℕ :=
  (ProbabilityTheory.geometricPMF hθ hθ1).map Nat.succ

/-- Actual accepted-response waiting law: sample a geometric opportunity
count and, independently at each opportunity, a fresh base waiting time. -/
noncomputable def geometricRandomSumLaw (p : PMF ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) : PMF ℕ :=
  (ProbabilityTheory.geometricPMF hθ hθ1).bind fun k =>
    iidNatSum p (k + 1)

/-- Real probability mass associated with a `PMF`. -/
noncomputable def pmfRealMass (p : PMF ℕ) (n : ℕ) : ℝ :=
  (p n).toReal

theorem pmfRealMass_nonneg (p : PMF ℕ) (n : ℕ) :
    0 ≤ pmfRealMass p n := ENNReal.toReal_nonneg

theorem pmfRealMass_summable (p : PMF ℕ) :
    Summable (pmfRealMass p) := by
  exact ENNReal.summable_toReal p.tsum_coe_ne_top

theorem pmfRealMass_tsum (p : PMF ℕ) :
    ∑' n, pmfRealMass p n = 1 := by
  unfold pmfRealMass
  rw [← ENNReal.tsum_toReal_eq (fun n => p.apply_ne_top n), p.tsum_coe]
  norm_num

/-- Probability-generating function of a natural-valued `PMF`. -/
noncomputable def pmfPgf (p : PMF ℕ) (z : ℝ) : ℝ :=
  ∑' n, pmfRealMass p n * z ^ n

theorem pmfPgf_summable (p : PMF ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    Summable fun n => pmfRealMass p n * z ^ n := by
  apply Summable.of_norm_bounded (pmfRealMass_summable p)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pmfRealMass_nonneg p n),
    abs_pow]
  have hzpow : |z| ^ n ≤ 1 := by
    exact pow_le_one₀ (abs_nonneg z) hz
  exact mul_le_of_le_one_right (pmfRealMass_nonneg p n) hzpow

theorem pmfPgf_one (p : PMF ℕ) : pmfPgf p 1 = 1 := by
  simpa [pmfPgf] using pmfRealMass_tsum p

theorem pmfPgf_nonneg (p : PMF ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ pmfPgf p z := by
  exact tsum_nonneg fun n => mul_nonneg (pmfRealMass_nonneg p n)
    (pow_nonneg hz n)

theorem pmfPgf_le_one (p : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : pmfPgf p z ≤ 1 := by
  rw [← pmfRealMass_tsum p]
  unfold pmfPgf
  exact Summable.tsum_le_tsum (fun n => by
    have hpow : z ^ n ≤ 1 := pow_le_one₀ hz0 hz1
    exact mul_le_of_le_one_right (pmfRealMass_nonneg p n) hpow)
    (pmfPgf_summable p (by rw [abs_of_nonneg hz0]; exact hz1))
    (pmfRealMass_summable p)

theorem pmfRealMass_bind (p : PMF ℕ) (f : ℕ → PMF ℕ) (b : ℕ) :
    pmfRealMass (p.bind f) b =
      ∑' a, pmfRealMass p a * pmfRealMass (f a) b := by
  unfold pmfRealMass
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    rw [ENNReal.toReal_mul]
  · intro a
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top b)

theorem pmfPgf_pure (a : ℕ) (z : ℝ) :
    pmfPgf (PMF.pure a) z = z ^ a := by
  unfold pmfPgf pmfRealMass
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [PMF.pure_apply_of_ne _ _ hba]

set_option maxHeartbeats 800000 in
-- The nonnegative Tonelli exchange requires extra elaboration time.
/-- Total expectation under a PMF bind is the iterated expectation.  At
`0 ≤ z ≤ 1` all terms are nonnegative and Tonelli is justified by total
probability one. -/
theorem pmfPgf_bind (p : PMF ℕ) (f : ℕ → PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf (p.bind f) z =
      ∑' a, pmfRealMass p a * pmfPgf (f a) z := by
  let term : ℕ × ℕ → ℝ := fun ab =>
    pmfRealMass p ab.1 * pmfRealMass (f ab.1) ab.2 * z ^ ab.2
  have hterm : ∀ ab, 0 ≤ term ab := by
    intro ab
    exact mul_nonneg
      (mul_nonneg (pmfRealMass_nonneg p ab.1)
        (pmfRealMass_nonneg (f ab.1) ab.2))
      (pow_nonneg hz0 ab.2)
  have hrow : ∀ a, Summable fun b => term (a, b) := by
    intro a
    refine ((pmfPgf_summable (f a) (by
      rw [abs_of_nonneg hz0]
      exact hz1)).mul_left (pmfRealMass p a)).congr ?_
    intro b
    simp only [term]
    ring
  have hrowSum : ∀ a, (∑' b, term (a, b)) =
      pmfRealMass p a * pmfPgf (f a) z := by
    intro a
    calc
      (∑' b, term (a, b)) =
          ∑' b, pmfRealMass p a *
            (pmfRealMass (f a) b * z ^ b) := by
              apply tsum_congr
              intro b
              simp only [term]
              ring
      _ = pmfRealMass p a *
          ∑' b, pmfRealMass (f a) b * z ^ b := by
            rw [(pmfPgf_summable (f a) (by
              rw [abs_of_nonneg hz0]
              exact hz1)).tsum_mul_left]
      _ = pmfRealMass p a * pmfPgf (f a) z := rfl
  have hout : Summable fun a =>
      pmfRealMass p a * pmfPgf (f a) z := by
    apply Summable.of_norm_bounded (pmfRealMass_summable p)
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pmfRealMass_nonneg p a) (pmfPgf_nonneg (f a) hz0))]
    exact mul_le_of_le_one_right (pmfRealMass_nonneg p a)
      (pmfPgf_le_one (f a) hz0 hz1)
  have hdouble : Summable term := by
    rw [summable_prod_of_nonneg hterm]
    exact ⟨hrow, by simpa only [hrowSum] using hout⟩
  calc
    pmfPgf (p.bind f) z
        = ∑' b, ∑' a, term (a, b) := by
            unfold pmfPgf
            apply tsum_congr
            intro b
            rw [pmfRealMass_bind]
            have hcol : Summable fun a =>
                pmfRealMass p a * pmfRealMass (f a) b := by
              apply Summable.of_norm_bounded (pmfRealMass_summable p)
              intro a
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
                (pmfRealMass_nonneg p a)
                (pmfRealMass_nonneg (f a) b))]
              have hmassOne : pmfRealMass (f a) b ≤ 1 := by
                unfold pmfRealMass
                simpa using ENNReal.toReal_mono ENNReal.one_ne_top
                  ((f a).coe_le_one b)
              exact mul_le_of_le_one_right (pmfRealMass_nonneg p a)
                hmassOne
            rw [← hcol.tsum_mul_right]
    _ = ∑' a, ∑' b, term (a, b) := by
          exact (Summable.tsum_comm
            (f := fun a b => term (a, b)) hdouble)
    _ = ∑' a, pmfRealMass p a * pmfPgf (f a) z := by
          apply tsum_congr
          exact hrowSum

set_option maxHeartbeats 800000 in
-- This Tonelli proof supports points outside the unit disk when explicit
-- summability witnesses replace the automatic probability-one bound.
/-- General PMF-bind PGF theorem under explicit absolute convergence. -/
theorem pmfPgf_bind_summable_and_eq (p : PMF ℕ) (f : ℕ → PMF ℕ)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hf : ∀ a, Summable fun b => pmfRealMass (f a) b * z ^ b)
    (hout : Summable fun a => pmfRealMass p a * pmfPgf (f a) z) :
    (Summable fun b => pmfRealMass (p.bind f) b * z ^ b) ∧
      pmfPgf (p.bind f) z =
        ∑' a, pmfRealMass p a * pmfPgf (f a) z := by
  let term : ℕ × ℕ → ℝ := fun ab =>
    pmfRealMass p ab.1 * pmfRealMass (f ab.1) ab.2 * z ^ ab.2
  have hterm : ∀ ab, 0 ≤ term ab := by
    intro ab
    positivity [pmfRealMass_nonneg p ab.1,
      pmfRealMass_nonneg (f ab.1) ab.2, pow_nonneg hz0 ab.2]
  have hrow : ∀ a, Summable fun b => term (a, b) := by
    intro a
    refine ((hf a).mul_left (pmfRealMass p a)).congr ?_
    intro b
    simp only [term]
    ring
  have hrowSum : ∀ a, (∑' b, term (a, b)) =
      pmfRealMass p a * pmfPgf (f a) z := by
    intro a
    unfold pmfPgf
    calc
      (∑' b, term (a, b)) =
          ∑' b, pmfRealMass p a *
            (pmfRealMass (f a) b * z ^ b) := by
              apply tsum_congr
              intro b
              simp only [term]
              ring
      _ = pmfRealMass p a *
          ∑' b, pmfRealMass (f a) b * z ^ b := by
            rw [(hf a).tsum_mul_left]
  have hdouble : Summable term := by
    rw [summable_prod_of_nonneg hterm]
    exact ⟨hrow, by simpa only [hrowSum] using hout⟩
  have hcolumns : Summable fun b => ∑' a, term (a, b) := by
    simpa only [Prod.swap_prod_mk] using hdouble.prod_symm.prod
  have hresult : Summable fun b =>
      pmfRealMass (p.bind f) b * z ^ b := by
    refine hcolumns.congr ?_
    intro b
    rw [pmfRealMass_bind]
    have hcol : Summable fun a =>
        pmfRealMass p a * pmfRealMass (f a) b := by
      apply Summable.of_norm_bounded (pmfRealMass_summable p)
      intro a
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (pmfRealMass_nonneg p a) (pmfRealMass_nonneg (f a) b))]
      have hmassOne : pmfRealMass (f a) b ≤ 1 := by
        unfold pmfRealMass
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top
          ((f a).coe_le_one b)
      exact mul_le_of_le_one_right (pmfRealMass_nonneg p a) hmassOne
    rw [← hcol.tsum_mul_right]
  refine ⟨hresult, ?_⟩
  calc
    pmfPgf (p.bind f) z = ∑' b, ∑' a, term (a, b) := by
      unfold pmfPgf
      apply tsum_congr
      intro b
      rw [pmfRealMass_bind]
      have hcol : Summable fun a =>
          pmfRealMass p a * pmfRealMass (f a) b := by
        apply Summable.of_norm_bounded (pmfRealMass_summable p)
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (pmfRealMass_nonneg p a) (pmfRealMass_nonneg (f a) b))]
        have hmassOne : pmfRealMass (f a) b ≤ 1 := by
          unfold pmfRealMass
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top
            ((f a).coe_le_one b)
        exact mul_le_of_le_one_right (pmfRealMass_nonneg p a) hmassOne
      rw [← hcol.tsum_mul_right]
    _ = ∑' a, ∑' b, term (a, b) :=
      Summable.tsum_comm (f := fun a b => term (a, b)) hdouble
    _ = ∑' a, pmfRealMass p a * pmfPgf (f a) z := by
      apply tsum_congr
      exact hrowSum

theorem pmfPgf_pure_summable (a : ℕ) (z : ℝ) :
    Summable fun b => pmfRealMass (PMF.pure a) b * z ^ b := by
  refine (hasSum_single a ?_).summable
  intro b hba
  simp [pmfRealMass, PMF.pure_apply_of_ne _ _ hba]

/-- General mapped-PMF PGF formula with an explicit convergence witness. -/
theorem pmfPgf_map_summable_and_eq (p : PMF ℕ) (g : ℕ → ℕ)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hg : Summable fun a => pmfRealMass p a * z ^ (g a)) :
    (Summable fun b => pmfRealMass (p.map g) b * z ^ b) ∧
      pmfPgf (p.map g) z =
        ∑' a, pmfRealMass p a * z ^ (g a) := by
  rw [← PMF.bind_pure_comp]
  simpa [Function.comp_def, pmfPgf_pure] using
    pmfPgf_bind_summable_and_eq p (PMF.pure ∘ g) hz0
      (fun a => pmfPgf_pure_summable (g a) z)
      (by simpa [Function.comp_def, pmfPgf_pure] using hg)

/-- Shifting a convergent natural-valued PGF multiplies it by `z^a`. -/
theorem pmfPgf_map_add_left_summable_and_eq (p : PMF ℕ) (a : ℕ)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hp : Summable fun b => pmfRealMass p b * z ^ b) :
    (Summable fun n =>
        pmfRealMass (p.map fun b => a + b) n * z ^ n) ∧
      pmfPgf (p.map fun b => a + b) z = z ^ a * pmfPgf p z := by
  have hg : Summable fun b =>
      pmfRealMass p b * z ^ (a + b) := by
    refine (hp.mul_left (z ^ a)).congr ?_
    intro b
    rw [pow_add]
    ring
  refine ⟨(pmfPgf_map_summable_and_eq p (fun b => a + b) hz0 hg).1, ?_⟩
  rw [(pmfPgf_map_summable_and_eq p (fun b => a + b) hz0 hg).2]
  unfold pmfPgf
  rw [← hp.tsum_mul_left]
  apply tsum_congr
  intro b
  rw [pow_add]
  ring

/-- General convolution PGF product under explicit convergence. -/
theorem pmfPgf_convolution_summable_and_eq (p q : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z)
    (hp : Summable fun a => pmfRealMass p a * z ^ a)
    (hq : Summable fun b => pmfRealMass q b * z ^ b) :
    (Summable fun n => pmfRealMass (natPMFConvolution p q) n * z ^ n) ∧
      pmfPgf (natPMFConvolution p q) z = pmfPgf p z * pmfPgf q z := by
  have hf : ∀ a, Summable fun n =>
      pmfRealMass (q.map fun b => a + b) n * z ^ n := fun a =>
    (pmfPgf_map_add_left_summable_and_eq q a hz0 hq).1
  have hout : Summable fun a => pmfRealMass p a *
      pmfPgf (q.map fun b => a + b) z := by
    refine (hp.mul_right (pmfPgf q z)).congr ?_
    intro a
    rw [(pmfPgf_map_add_left_summable_and_eq q a hz0 hq).2]
    ring
  unfold natPMFConvolution
  refine ⟨(pmfPgf_bind_summable_and_eq p
    (fun a => q.map fun b => a + b) hz0 hf hout).1, ?_⟩
  rw [(pmfPgf_bind_summable_and_eq p
    (fun a => q.map fun b => a + b) hz0 hf hout).2]
  simp_rw [(pmfPgf_map_add_left_summable_and_eq q _ hz0 hq).2]
  unfold pmfPgf
  rw [← hp.tsum_mul_right]
  apply tsum_congr
  intro a
  ring

/-- Convergence and value of the PGF of every finite iid sum. -/
theorem pmfPgf_iidNatSum_summable_and_eq (p : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hp : Summable fun a => pmfRealMass p a * z ^ a) :
    ∀ n,
      (Summable fun k => pmfRealMass (iidNatSum p n) k * z ^ k) ∧
        pmfPgf (iidNatSum p n) z = (pmfPgf p z) ^ n
  | 0 => by
      simp [iidNatSum, pmfPgf_pure_summable, pmfPgf_pure]
  | n + 1 => by
      rw [iidNatSum]
      have hi := pmfPgf_iidNatSum_summable_and_eq p hz0 hp n
      have hc := pmfPgf_convolution_summable_and_eq p (iidNatSum p n)
        hz0 hp hi.1
      refine ⟨hc.1, ?_⟩
      rw [hc.2, hi.2, pow_succ]
      ring

theorem pmfPgf_map (p : PMF ℕ) (g : ℕ → ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf (p.map g) z = ∑' a, pmfRealMass p a * z ^ (g a) := by
  rw [← PMF.bind_pure_comp]
  rw [pmfPgf_bind p (PMF.pure ∘ g) hz0 hz1]
  apply tsum_congr
  intro a
  rw [show (PMF.pure ∘ g) a = PMF.pure (g a) from rfl,
    pmfPgf_pure]

theorem pmfPgf_map_add_left (p : PMF ℕ) (a : ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf (p.map fun b => a + b) z = z ^ a * pmfPgf p z := by
  rw [pmfPgf_map p (fun b => a + b) hz0 hz1]
  unfold pmfPgf
  have hs := pmfPgf_summable p (by
    rw [abs_of_nonneg hz0]
    exact hz1)
  calc
    (∑' b, pmfRealMass p b * z ^ (a + b)) =
        ∑' b, z ^ a * (pmfRealMass p b * z ^ b) := by
          apply tsum_congr
          intro b
          rw [pow_add]
          ring
    _ = z ^ a * ∑' b, pmfRealMass p b * z ^ b :=
          hs.tsum_mul_left (z ^ a)

theorem pmfPgf_convolution (p q : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf (natPMFConvolution p q) z = pmfPgf p z * pmfPgf q z := by
  rw [natPMFConvolution, pmfPgf_bind p
    (fun a => q.map fun b => a + b) hz0 hz1]
  simp_rw [pmfPgf_map_add_left q _ hz0 hz1]
  unfold pmfPgf
  have hs := pmfPgf_summable p (by
    rw [abs_of_nonneg hz0]
    exact hz1)
  calc
    (∑' a, pmfRealMass p a * (z ^ a * pmfPgf q z)) =
        ∑' a, (pmfRealMass p a * z ^ a) * pmfPgf q z := by
          apply tsum_congr
          intro a
          ring
    _ = (∑' a, pmfRealMass p a * z ^ a) * pmfPgf q z :=
          hs.tsum_mul_right (pmfPgf q z)

theorem pmfPgf_iidNatSum (p : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ n, pmfPgf (iidNatSum p n) z = (pmfPgf p z) ^ n
  | 0 => by simp [iidNatSum, pmfPgf_pure]
  | n + 1 => by
      rw [iidNatSum, pmfPgf_convolution p (iidNatSum p n) hz0 hz1,
        pmfPgf_iidNatSum p hz0 hz1 n, pow_succ]
      ring

theorem geometricPMF_realMass (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (k : ℕ) :
    pmfRealMass (ProbabilityTheory.geometricPMF hθ hθ1) k =
      θ * (1 - θ) ^ k := by
  unfold pmfRealMass
  change (ENNReal.ofReal ((1 - θ) ^ k * θ)).toReal =
    θ * (1 - θ) ^ k
  rw [ENNReal.toReal_ofReal]
  · ring
  · exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hθ1) k) hθ.le

/-! ## Algebraic geometric-random-sum transform -/

/-- The transform dictated by a geometric number of iid base waits.  The term
with index `k` corresponds to `k` rejected opportunities followed by one
accepted opportunity. -/
noncomputable def geometricRandomSumTransform
    (θ F : ℝ) : ℝ :=
  ∑' k : ℕ, θ * (1 - θ) ^ k * F ^ (k + 1)

/-- Convergence and exact transform of an actual geometric random sum at any
nonnegative point satisfying the geometric contraction condition. -/
theorem pmfPgf_geometricRandomSumLaw_summable_and_eq (p : PMF ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ} (hz0 : 0 ≤ z)
    (hp : Summable fun a => pmfRealMass p a * z ^ a)
    (hcontract : |(1 - θ) * pmfPgf p z| < 1) :
    (Summable fun n =>
        pmfRealMass (geometricRandomSumLaw p θ hθ hθ1) n * z ^ n) ∧
      pmfPgf (geometricRandomSumLaw p θ hθ hθ1) z =
        geometricRandomSumTransform θ (pmfPgf p z) := by
  have hi : ∀ k, Summable fun n =>
      pmfRealMass (iidNatSum p (k + 1)) n * z ^ n := fun k =>
    (pmfPgf_iidNatSum_summable_and_eq p hz0 hp (k + 1)).1
  have hgeom : Summable fun k : ℕ =>
      ((1 - θ) * pmfPgf p z) ^ k :=
    summable_geometric_of_abs_lt_one hcontract
  have hout : Summable fun k =>
      pmfRealMass (ProbabilityTheory.geometricPMF hθ hθ1) k *
        pmfPgf (iidNatSum p (k + 1)) z := by
    refine (hgeom.mul_left (θ * pmfPgf p z)).congr ?_
    intro k
    rw [geometricPMF_realMass θ hθ hθ1,
      (pmfPgf_iidNatSum_summable_and_eq p hz0 hp (k + 1)).2,
      pow_succ, mul_pow]
    ring
  unfold geometricRandomSumLaw
  have hb := pmfPgf_bind_summable_and_eq
    (ProbabilityTheory.geometricPMF hθ hθ1)
    (fun k => iidNatSum p (k + 1)) hz0 hi hout
  refine ⟨hb.1, ?_⟩
  rw [hb.2]
  unfold geometricRandomSumTransform
  apply tsum_congr
  intro k
  rw [geometricPMF_realMass θ hθ hθ1,
    (pmfPgf_iidNatSum_summable_and_eq p hz0 hp (k + 1)).2]

/-- A family of laws has a regulator-uniform positive exponential moment when
one common point above one works at every cutoff. -/
def HasUniformPositiveExponentialMoment {ι : Type*} (p : ι → PMF ℕ) : Prop :=
  ∃ z : ℝ, 1 < z ∧ ∀ X,
    Summable fun n => pmfRealMass (p X) n * z ^ n

/-- Explicit uniform hypotheses required to promote fixed-source geometric
renewal control to regulator-uniform control. -/
structure UniformGeometricRenewalBounds (ι : Type*) where
  baseLaw : ι → PMF ℕ
  acceptance : ι → ℝ
  acceptance_pos : ∀ X, 0 < acceptance X
  acceptance_le_one : ∀ X, acceptance X ≤ 1
  momentPoint : ℝ
  one_lt_momentPoint : 1 < momentPoint
  basePgf_summable : ∀ X, Summable fun n =>
    pmfRealMass (baseLaw X) n * momentPoint ^ n
  contraction : ∀ X,
    |(1 - acceptance X) * pmfPgf (baseLaw X) momentPoint| < 1

/-- Common cutoff bounds give one common exponential-moment point for the
whole family of accepted-response laws. -/
theorem uniformGeometricRandomSum_hasUniformPositiveExponentialMoment
    {ι : Type*} (b : UniformGeometricRenewalBounds ι) :
    HasUniformPositiveExponentialMoment (fun X =>
      geometricRandomSumLaw (b.baseLaw X) (b.acceptance X)
        (b.acceptance_pos X) (b.acceptance_le_one X)) := by
  refine ⟨b.momentPoint, b.one_lt_momentPoint, ?_⟩
  intro X
  exact (pmfPgf_geometricRandomSumLaw_summable_and_eq
    (b.baseLaw X) (b.acceptance X) (b.acceptance_pos X)
    (b.acceptance_le_one X) (le_trans (by norm_num) b.one_lt_momentPoint.le)
    (b.basePgf_summable X) (b.contraction X)).1

/-- The PGF of the actual PMF-valued geometric random sum is the geometric
series of powers of the base PGF. -/
theorem pmfPgf_geometricRandomSumLaw (p : PMF ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf (geometricRandomSumLaw p θ hθ hθ1) z =
      geometricRandomSumTransform θ (pmfPgf p z) := by
  rw [geometricRandomSumLaw, pmfPgf_bind _ _ hz0 hz1]
  unfold geometricRandomSumTransform
  apply tsum_congr
  intro k
  rw [geometricPMF_realMass θ hθ hθ1 k,
    pmfPgf_iidNatSum p hz0 hz1 (k + 1)]

/-! ## First moments -/

/-- First moment of a natural-valued PMF. -/
noncomputable def pmfFirstMoment (p : PMF ℕ) : ℝ :=
  ∑' n, pmfRealMass p n * (n : ℝ)

def HasFiniteFirstMoment (p : PMF ℕ) : Prop :=
  Summable fun n => pmfRealMass p n * (n : ℝ)

theorem pmfFirstMoment_pure (a : ℕ) :
    pmfFirstMoment (PMF.pure a) = a := by
  unfold pmfFirstMoment pmfRealMass
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    simp [PMF.pure_apply_of_ne _ _ hba]

theorem hasFiniteFirstMoment_pure (a : ℕ) :
    HasFiniteFirstMoment (PMF.pure a) := by
  unfold HasFiniteFirstMoment pmfRealMass
  refine (hasSum_single a ?_).summable
  intro b hba
  simp [PMF.pure_apply_of_ne _ _ hba]

set_option maxHeartbeats 800000 in
-- The proof is a nonnegative Tonelli exchange analogous to `pmfPgf_bind`.
theorem pmfFirstMoment_bind (p : PMF ℕ) (f : ℕ → PMF ℕ)
    (hf : ∀ a, HasFiniteFirstMoment (f a))
    (hout : Summable fun a =>
      pmfRealMass p a * pmfFirstMoment (f a)) :
    pmfFirstMoment (p.bind f) =
      ∑' a, pmfRealMass p a * pmfFirstMoment (f a) := by
  let term : ℕ × ℕ → ℝ := fun ab =>
    pmfRealMass p ab.1 * pmfRealMass (f ab.1) ab.2 * (ab.2 : ℝ)
  have hterm : ∀ ab, 0 ≤ term ab := by
    intro ab
    positivity [pmfRealMass_nonneg p ab.1,
      pmfRealMass_nonneg (f ab.1) ab.2]
  have hrow : ∀ a, Summable fun b => term (a, b) := by
    intro a
    refine ((hf a).mul_left (pmfRealMass p a)).congr ?_
    intro b
    simp only [HasFiniteFirstMoment, term] at *
    ring
  have hrowSum : ∀ a, (∑' b, term (a, b)) =
      pmfRealMass p a * pmfFirstMoment (f a) := by
    intro a
    unfold pmfFirstMoment
    calc
      (∑' b, term (a, b)) =
          ∑' b, pmfRealMass p a *
            (pmfRealMass (f a) b * (b : ℝ)) := by
              apply tsum_congr
              intro b
              simp only [term]
              ring
      _ = pmfRealMass p a *
          ∑' b, pmfRealMass (f a) b * (b : ℝ) := by
            rw [(hf a).tsum_mul_left]
  have hdouble : Summable term := by
    rw [summable_prod_of_nonneg hterm]
    exact ⟨hrow, by simpa only [hrowSum] using hout⟩
  calc
    pmfFirstMoment (p.bind f) =
        ∑' b, ∑' a, term (a, b) := by
          unfold pmfFirstMoment
          apply tsum_congr
          intro b
          rw [pmfRealMass_bind]
          have hcol : Summable fun a =>
              pmfRealMass p a * pmfRealMass (f a) b := by
            apply Summable.of_norm_bounded (pmfRealMass_summable p)
            intro a
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
              (pmfRealMass_nonneg p a)
              (pmfRealMass_nonneg (f a) b))]
            have hmassOne : pmfRealMass (f a) b ≤ 1 := by
              unfold pmfRealMass
              simpa using ENNReal.toReal_mono ENNReal.one_ne_top
                ((f a).coe_le_one b)
            exact mul_le_of_le_one_right (pmfRealMass_nonneg p a)
              hmassOne
          rw [← hcol.tsum_mul_right]
    _ = ∑' a, ∑' b, term (a, b) :=
      Summable.tsum_comm (f := fun a b => term (a, b)) hdouble
    _ = ∑' a, pmfRealMass p a * pmfFirstMoment (f a) := by
      apply tsum_congr
      exact hrowSum

set_option maxHeartbeats 800000 in
-- The finite-moment Tonelli exchange requires extra elaboration time.
/-- A PMF bind has finite first moment when every conditional law does and
the outer average of the conditional first moments is summable. -/
theorem hasFiniteFirstMoment_bind (p : PMF ℕ) (f : ℕ → PMF ℕ)
    (hf : ∀ a, HasFiniteFirstMoment (f a))
    (hout : Summable fun a =>
      pmfRealMass p a * pmfFirstMoment (f a)) :
    HasFiniteFirstMoment (p.bind f) := by
  let term : ℕ × ℕ → ℝ := fun ab =>
    pmfRealMass p ab.1 * pmfRealMass (f ab.1) ab.2 * (ab.2 : ℝ)
  have hterm : ∀ ab, 0 ≤ term ab := by
    intro ab
    positivity [pmfRealMass_nonneg p ab.1,
      pmfRealMass_nonneg (f ab.1) ab.2]
  have hrow : ∀ a, Summable fun b => term (a, b) := by
    intro a
    refine ((hf a).mul_left (pmfRealMass p a)).congr ?_
    intro b
    simp only [HasFiniteFirstMoment, term] at *
    ring
  have hrowSum : ∀ a, (∑' b, term (a, b)) =
      pmfRealMass p a * pmfFirstMoment (f a) := by
    intro a
    unfold pmfFirstMoment
    calc
      (∑' b, term (a, b)) =
          ∑' b, pmfRealMass p a *
            (pmfRealMass (f a) b * (b : ℝ)) := by
              apply tsum_congr
              intro b
              simp only [term]
              ring
      _ = pmfRealMass p a *
          ∑' b, pmfRealMass (f a) b * (b : ℝ) := by
            rw [(hf a).tsum_mul_left]
  have hdouble : Summable term := by
    rw [summable_prod_of_nonneg hterm]
    exact ⟨hrow, by simpa only [hrowSum] using hout⟩
  have hcolumns : Summable fun b => ∑' a, term (a, b) := by
    simpa only [Prod.swap_prod_mk] using hdouble.prod_symm.prod
  unfold HasFiniteFirstMoment
  refine hcolumns.congr ?_
  intro b
  rw [pmfRealMass_bind]
  have hcol : Summable fun a =>
      pmfRealMass p a * pmfRealMass (f a) b := by
    apply Summable.of_norm_bounded (pmfRealMass_summable p)
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pmfRealMass_nonneg p a) (pmfRealMass_nonneg (f a) b))]
    have hmassOne : pmfRealMass (f a) b ≤ 1 := by
      unfold pmfRealMass
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        ((f a).coe_le_one b)
    exact mul_le_of_le_one_right (pmfRealMass_nonneg p a) hmassOne
  rw [← hcol.tsum_mul_right]

theorem pmfFirstMoment_map (p : PMF ℕ) (g : ℕ → ℕ)
    (hg : Summable fun a => pmfRealMass p a * (g a : ℝ)) :
    pmfFirstMoment (p.map g) =
      ∑' a, pmfRealMass p a * (g a : ℝ) := by
  rw [← PMF.bind_pure_comp]
  have hbind := pmfFirstMoment_bind p (PMF.pure ∘ g)
    (fun a => hasFiniteFirstMoment_pure (g a))
    (by simpa [Function.comp_def, pmfFirstMoment_pure] using hg)
  simpa [Function.comp_def, pmfFirstMoment_pure] using hbind

theorem hasFiniteFirstMoment_map (p : PMF ℕ) (g : ℕ → ℕ)
    (hg : Summable fun a => pmfRealMass p a * (g a : ℝ)) :
    HasFiniteFirstMoment (p.map g) := by
  rw [← PMF.bind_pure_comp]
  apply hasFiniteFirstMoment_bind p (PMF.pure ∘ g)
    (fun a => hasFiniteFirstMoment_pure (g a))
  simpa [Function.comp_def, pmfFirstMoment_pure] using hg

theorem pmfFirstMoment_map_add_left (p : PMF ℕ) (a : ℕ)
    (hp : HasFiniteFirstMoment p) :
    pmfFirstMoment (p.map fun b => a + b) =
      a + pmfFirstMoment p := by
  have hs : Summable fun b =>
      pmfRealMass p b * ((a + b : ℕ) : ℝ) := by
    have ha := (pmfRealMass_summable p).mul_left (a : ℝ)
    have hb : Summable fun b => pmfRealMass p b * (b : ℝ) := hp
    exact (ha.add hb).congr fun b => by
      push_cast
      ring
  rw [pmfFirstMoment_map p (fun b => a + b) hs]
  have ha := pmfRealMass_summable p
  have hp' : Summable fun b => pmfRealMass p b * (b : ℝ) := hp
  calc
    (∑' b, pmfRealMass p b * ((a + b : ℕ) : ℝ)) =
        ∑' b, ((a : ℝ) * pmfRealMass p b +
          pmfRealMass p b * (b : ℝ)) := by
            apply tsum_congr
            intro b
            push_cast
            ring
    _ = (∑' b, (a : ℝ) * pmfRealMass p b) +
          (∑' b, pmfRealMass p b * (b : ℝ)) := by
            exact (ha.mul_left (a : ℝ)).tsum_add hp'
    _ = a + pmfFirstMoment p := by
          rw [ha.tsum_mul_left, pmfRealMass_tsum]
          simp [pmfFirstMoment]

theorem hasFiniteFirstMoment_map_add_left (p : PMF ℕ) (a : ℕ)
    (hp : HasFiniteFirstMoment p) :
    HasFiniteFirstMoment (p.map fun b => a + b) := by
  apply hasFiniteFirstMoment_map
  have ha := (pmfRealMass_summable p).mul_left (a : ℝ)
  have hp' : Summable fun b => pmfRealMass p b * (b : ℝ) := hp
  exact (ha.add hp').congr fun b => by
    push_cast
    ring

/-- Independent convolution preserves finiteness of the first moment. -/
theorem hasFiniteFirstMoment_convolution (p q : PMF ℕ)
    (hp : HasFiniteFirstMoment p) (hq : HasFiniteFirstMoment q) :
    HasFiniteFirstMoment (natPMFConvolution p q) := by
  unfold natPMFConvolution
  apply hasFiniteFirstMoment_bind p (fun a => q.map fun b => a + b)
    (fun a => hasFiniteFirstMoment_map_add_left q a hq)
  have hp' : Summable fun a => pmfRealMass p a * (a : ℝ) := hp
  have hq' := (pmfRealMass_summable p).mul_right (pmfFirstMoment q)
  refine (hp'.add hq').congr ?_
  intro a
  rw [pmfFirstMoment_map_add_left q a hq]
  ring

/-- The first moment of an independent convolution is the sum of the first
moments. -/
theorem pmfFirstMoment_convolution (p q : PMF ℕ)
    (hp : HasFiniteFirstMoment p) (hq : HasFiniteFirstMoment q) :
    pmfFirstMoment (natPMFConvolution p q) =
      pmfFirstMoment p + pmfFirstMoment q := by
  unfold natPMFConvolution
  have hout : Summable fun a => pmfRealMass p a *
      pmfFirstMoment (q.map fun b => a + b) := by
    have hp' : Summable fun a => pmfRealMass p a * (a : ℝ) := hp
    have hq' := (pmfRealMass_summable p).mul_right (pmfFirstMoment q)
    refine (hp'.add hq').congr ?_
    intro a
    rw [pmfFirstMoment_map_add_left q a hq]
    ring
  rw [pmfFirstMoment_bind p (fun a => q.map fun b => a + b)
    (fun a => hasFiniteFirstMoment_map_add_left q a hq) hout]
  simp_rw [pmfFirstMoment_map_add_left q _ hq]
  have hp' : Summable fun a => pmfRealMass p a * (a : ℝ) := hp
  have hq' := (pmfRealMass_summable p).mul_right (pmfFirstMoment q)
  calc
    (∑' a, pmfRealMass p a * (↑a + pmfFirstMoment q)) =
        ∑' a, (pmfRealMass p a * (a : ℝ) +
          pmfRealMass p a * pmfFirstMoment q) := by
            apply tsum_congr
            intro a
            ring
    _ = (∑' a, pmfRealMass p a * (a : ℝ)) +
        (∑' a, pmfRealMass p a * pmfFirstMoment q) :=
          hp'.tsum_add hq'
    _ = pmfFirstMoment p + pmfFirstMoment q := by
          rw [pmfRealMass_summable p |>.tsum_mul_right,
            pmfRealMass_tsum]
          simp [pmfFirstMoment]

/-- Every finite iid sum has a finite first moment. -/
theorem hasFiniteFirstMoment_iidNatSum (p : PMF ℕ)
    (hp : HasFiniteFirstMoment p) :
    ∀ n, HasFiniteFirstMoment (iidNatSum p n)
  | 0 => by simp [iidNatSum, hasFiniteFirstMoment_pure]
  | n + 1 => by
      rw [iidNatSum]
      exact hasFiniteFirstMoment_convolution p (iidNatSum p n) hp
        (hasFiniteFirstMoment_iidNatSum p hp n)

/-- The mean of a sum of `n` iid natural-valued samples is `n` times the
base mean. -/
theorem pmfFirstMoment_iidNatSum (p : PMF ℕ)
    (hp : HasFiniteFirstMoment p) :
    ∀ n, pmfFirstMoment (iidNatSum p n) = n * pmfFirstMoment p
  | 0 => by simp [iidNatSum, pmfFirstMoment_pure]
  | n + 1 => by
      rw [iidNatSum, pmfFirstMoment_convolution p (iidNatSum p n) hp
        (hasFiniteFirstMoment_iidNatSum p hp n),
        pmfFirstMoment_iidNatSum p hp n]
      push_cast
      ring

/-- The geometric random sum has a finite first moment whenever the base
waiting law does. -/
theorem hasFiniteFirstMoment_geometricRandomSumLaw (p : PMF ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : HasFiniteFirstMoment p) :
    HasFiniteFirstMoment (geometricRandomSumLaw p θ hθ hθ1) := by
  have hnorm : ‖1 - θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hshift : Summable fun k : ℕ =>
      ((k + 1 : ℕ) : ℝ) * (1 - θ) ^ k := by
    simpa using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm)
  unfold geometricRandomSumLaw
  apply hasFiniteFirstMoment_bind
    (ProbabilityTheory.geometricPMF hθ hθ1)
    (fun k => iidNatSum p (k + 1))
    (fun k => hasFiniteFirstMoment_iidNatSum p hp (k + 1))
  refine (hshift.mul_left (θ * pmfFirstMoment p)).congr ?_
  intro k
  rw [geometricPMF_realMass θ hθ hθ1,
    pmfFirstMoment_iidNatSum p hp (k + 1)]
  ring

/-- Wald's formula for the actual PMF-valued geometric random sum. -/
theorem pmfFirstMoment_geometricRandomSumLaw (p : PMF ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : HasFiniteFirstMoment p) :
    pmfFirstMoment (geometricRandomSumLaw p θ hθ hθ1) =
      pmfFirstMoment p / θ := by
  have hnorm : ‖1 - θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hshift : Summable fun k : ℕ =>
      ((k + 1 : ℕ) : ℝ) * (1 - θ) ^ k := by
    simpa using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm)
  have hshiftSum : (∑' k : ℕ,
      ((k + 1 : ℕ) : ℝ) * (1 - θ) ^ k) =
      1 / (1 - (1 - θ)) ^ 2 := by
    simpa using
      (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm)
  unfold geometricRandomSumLaw
  have hout : Summable fun k =>
      pmfRealMass (ProbabilityTheory.geometricPMF hθ hθ1) k *
        pmfFirstMoment (iidNatSum p (k + 1)) := by
    refine (hshift.mul_left (θ * pmfFirstMoment p)).congr ?_
    intro k
    rw [geometricPMF_realMass θ hθ hθ1,
      pmfFirstMoment_iidNatSum p hp (k + 1)]
    ring
  rw [pmfFirstMoment_bind
    (ProbabilityTheory.geometricPMF hθ hθ1)
    (fun k => iidNatSum p (k + 1))
    (fun k => hasFiniteFirstMoment_iidNatSum p hp (k + 1)) hout]
  simp_rw [geometricPMF_realMass θ hθ hθ1,
    pmfFirstMoment_iidNatSum p hp]
  calc
    (∑' k : ℕ, θ * (1 - θ) ^ k *
        ((k + 1 : ℕ) * pmfFirstMoment p)) =
        (θ * pmfFirstMoment p) *
          ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (1 - θ) ^ k := by
            rw [← hshift.tsum_mul_left]
            apply tsum_congr
            intro k
            push_cast
            ring
    _ = (θ * pmfFirstMoment p) *
        (1 / (1 - (1 - θ)) ^ 2) := by rw [hshiftSum]
    _ = pmfFirstMoment p / θ := by
          field_simp [ne_of_gt hθ]
          ring

theorem geometricRandomSumTransform_eq (θ F : ℝ)
    (hcontract : |(1 - θ) * F| < 1) :
    geometricRandomSumTransform θ F =
      θ * F / (1 - (1 - θ) * F) := by
  have hsum : Summable fun k : ℕ => ((1 - θ) * F) ^ k :=
    summable_geometric_of_abs_lt_one hcontract
  calc
    geometricRandomSumTransform θ F
        = ∑' k : ℕ, (θ * F) * (((1 - θ) * F) ^ k) := by
            apply tsum_congr
            intro k
            rw [pow_succ, mul_pow]
            ring
    _ = (θ * F) * ∑' k : ℕ, ((1 - θ) * F) ^ k :=
          hsum.tsum_mul_left (θ * F)
    _ = θ * F / (1 - (1 - θ) * F) := by
          rw [tsum_geometric_of_abs_lt_one hcontract]
          field_simp

/-- Tail-sum mean of the geometric opportunity count. -/
noncomputable def geometricOpportunityMean (θ : ℝ) : ℝ :=
  ∑' k : ℕ, (1 - θ) ^ k

theorem geometricOpportunityMean_eq_inv (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    geometricOpportunityMean θ = θ⁻¹ := by
  have habs : |1 - θ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [geometricOpportunityMean,
    tsum_geometric_of_abs_lt_one habs]
  congr 1
  ring

/-- Wald factor for an independent geometric number of iid waits. -/
noncomputable def geometricRandomSumMean (θ baseMean : ℝ) : ℝ :=
  geometricOpportunityMean θ * baseMean

theorem geometricRandomSumMean_eq (θ baseMean : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    geometricRandomSumMean θ baseMean = baseMean / θ := by
  rw [geometricRandomSumMean, geometricOpportunityMean_eq_inv θ hθ hθ1]
  field_simp

end NCG
