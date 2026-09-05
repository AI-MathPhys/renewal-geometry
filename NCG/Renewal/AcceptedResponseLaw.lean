/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Renewal.GeometricRandomSum
import NCG.Grand.AcceptedResponse

/-!
# The accepted-response waiting law

The completed-private inter-opportunity law is realized as an actual PMF.
Independent copies are summed until the first success of an independent
Bernoulli opportunity mark, using `geometricRandomSumLaw`.
-/

namespace NCG

/-- Mass of the completed-private waiting time after removing its deterministic
two-tick offset. -/
noncomputable def completedPrivateOffsetMass (k : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (1 / 3 : ℝ) ^ k -
    (4 / 5 : ℝ) * (1 / 5 : ℝ) ^ k

theorem completedPrivateOffsetMass_nonneg (k : ℕ) :
    0 ≤ completedPrivateOffsetMass k := by
  have hp : (1 / 5 : ℝ) ^ k ≤ (1 / 3 : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h5 : 0 ≤ (1 / 5 : ℝ) ^ k := pow_nonneg (by norm_num) k
  unfold completedPrivateOffsetMass
  nlinarith

theorem completedPrivateOffsetMass_summable :
    Summable completedPrivateOffsetMass := by
  exact ((summable_geometric_of_abs_lt_one (r := (1 / 3 : ℝ))
      (by norm_num)).mul_left (4 / 3)).sub
    ((summable_geometric_of_abs_lt_one (r := (1 / 5 : ℝ))
      (by norm_num)).mul_left (4 / 5))

theorem completedPrivateOffsetMass_tsum :
    ∑' k, completedPrivateOffsetMass k = 1 := by
  unfold completedPrivateOffsetMass
  rw [Summable.tsum_sub
    ((summable_geometric_of_abs_lt_one (r := (1 / 3 : ℝ))
      (by norm_num)).mul_left (4 / 3))
    ((summable_geometric_of_abs_lt_one (r := (1 / 5 : ℝ))
      (by norm_num)).mul_left (4 / 5)),
    tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one (show |(1 / 3 : ℝ)| < 1 by norm_num),
    tsum_geometric_of_abs_lt_one (show |(1 / 5 : ℝ)| < 1 by norm_num)]
  norm_num

/-- The probability law of the completed-private waiting time with the fixed
two-tick offset removed. -/
noncomputable def completedPrivateOffsetPMF : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (completedPrivateOffsetMass k), by
    apply ENNReal.hasSum_coe.mpr
    rw [← ENNReal.toNNReal_one]
    have hsum : HasSum completedPrivateOffsetMass 1 := by
      rw [← completedPrivateOffsetMass_tsum]
      exact completedPrivateOffsetMass_summable.hasSum
    convert hsum.toNNReal completedPrivateOffsetMass_nonneg using 1 <;>
      norm_num⟩

theorem completedPrivateOffsetPMF_realMass (k : ℕ) :
    pmfRealMass completedPrivateOffsetPMF k =
      completedPrivateOffsetMass k := by
  change (ENNReal.ofReal (completedPrivateOffsetMass k)).toReal =
    completedPrivateOffsetMass k
  exact ENNReal.toReal_ofReal (completedPrivateOffsetMass_nonneg k)

theorem completedPrivateOffsetPMF_hasFiniteFirstMoment :
    HasFiniteFirstMoment completedPrivateOffsetPMF := by
  have h3 : Summable fun k : ℕ =>
      (k : ℝ) * (1 / 3 : ℝ) ^ k :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)).summable
  have h5 : Summable fun k : ℕ =>
      (k : ℝ) * (1 / 5 : ℝ) ^ k :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 5 : ℝ)‖ < 1 by norm_num)).summable
  unfold HasFiniteFirstMoment
  simp_rw [completedPrivateOffsetPMF_realMass,
    completedPrivateOffsetMass]
  refine ((h3.mul_left (4 / 3)).sub
    (h5.mul_left (4 / 5))).congr ?_
  intro k
  ring

theorem completedPrivateOffsetPMF_firstMoment :
    pmfFirstMoment completedPrivateOffsetPMF = 3 / 4 := by
  have h3 : Summable fun k : ℕ =>
      (k : ℝ) * (1 / 3 : ℝ) ^ k :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)).summable
  have h5 : Summable fun k : ℕ =>
      (k : ℝ) * (1 / 5 : ℝ) ^ k :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 5 : ℝ)‖ < 1 by norm_num)).summable
  unfold pmfFirstMoment
  simp_rw [completedPrivateOffsetPMF_realMass,
    completedPrivateOffsetMass]
  rw [show (fun k : ℕ =>
      ((4 / 3 : ℝ) * (1 / 3 : ℝ) ^ k -
        (4 / 5 : ℝ) * (1 / 5 : ℝ) ^ k) * (k : ℝ)) =
      (fun k : ℕ => (4 / 3 : ℝ) * ((k : ℝ) * (1 / 3 : ℝ) ^ k) -
        (4 / 5 : ℝ) * ((k : ℝ) * (1 / 5 : ℝ) ^ k)) by
        funext k
        ring]
  rw [Summable.tsum_sub (h3.mul_left (4 / 3))
      (h5.mul_left (4 / 5)),
    tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num),
    tsum_coe_mul_geometric_of_norm_lt_one
      (show ‖(1 / 5 : ℝ)‖ < 1 by norm_num)]
  norm_num

/-- Actual completed-private waiting-time law, supported on times `2,3,…`. -/
noncomputable def completedPrivateWaitingPMF : PMF ℕ :=
  completedPrivateOffsetPMF.map fun k => 2 + k

theorem completedPrivateWaitingPMF_hasFiniteFirstMoment :
    HasFiniteFirstMoment completedPrivateWaitingPMF := by
  rw [completedPrivateWaitingPMF]
  exact hasFiniteFirstMoment_map_add_left completedPrivateOffsetPMF 2
    completedPrivateOffsetPMF_hasFiniteFirstMoment

theorem completedPrivateWaitingPMF_firstMoment :
    pmfFirstMoment completedPrivateWaitingPMF = 11 / 4 := by
  rw [completedPrivateWaitingPMF,
    pmfFirstMoment_map_add_left completedPrivateOffsetPMF 2
      completedPrivateOffsetPMF_hasFiniteFirstMoment,
    completedPrivateOffsetPMF_firstMoment]
  norm_num

/-- The completed-private waiting PGF converges on the positive interval
`[0,3)` and has the same rational form there. -/
theorem completedPrivateWaitingPMF_pgf_summable_and_eq_of_lt_three {z : ℝ}
    (hz0 : 0 ≤ z) (hz3 : z < 3) :
    (Summable fun n => pmfRealMass completedPrivateWaitingPMF n * z ^ n) ∧
      pmfPgf completedPrivateWaitingPMF z =
        8 * z ^ 2 / ((5 - z) * (3 - z)) := by
  have h3 : Summable fun k : ℕ => (z / 3) ^ k :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith)
  have h5 : Summable fun k : ℕ => (z / 5) ^ k :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith)
  have hoffset : Summable fun k =>
      pmfRealMass completedPrivateOffsetPMF k * z ^ k := by
    simp_rw [completedPrivateOffsetPMF_realMass,
      completedPrivateOffsetMass]
    refine ((h3.mul_left (4 / 3)).sub
      (h5.mul_left (4 / 5))).congr ?_
    intro k
    simp only [div_eq_mul_inv, mul_pow]
    ring
  have hmap := pmfPgf_map_add_left_summable_and_eq
    completedPrivateOffsetPMF 2 hz0 hoffset
  rw [completedPrivateWaitingPMF]
  refine ⟨hmap.1, ?_⟩
  rw [hmap.2]
  unfold pmfPgf
  simp_rw [completedPrivateOffsetPMF_realMass,
    completedPrivateOffsetMass]
  rw [show (fun k : ℕ =>
      ((4 / 3 : ℝ) * (1 / 3 : ℝ) ^ k -
        (4 / 5 : ℝ) * (1 / 5 : ℝ) ^ k) * z ^ k) =
      (fun k => (4 / 3 : ℝ) * (z / 3) ^ k -
        (4 / 5 : ℝ) * (z / 5) ^ k) by
        funext k
        simp only [div_eq_mul_inv, mul_pow]
        ring]
  rw [Summable.tsum_sub (h3.mul_left (4 / 3))
      (h5.mul_left (4 / 5)),
    tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith : |z / 3| < 1),
    tsum_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith : |z / 5| < 1)]
  have h3z : 3 - z ≠ 0 := by linarith
  have h5z : 5 - z ≠ 0 := by linarith
  field_simp
  ring

/-- The base waiting law has exactly the manuscript's rational PGF. -/
theorem completedPrivateWaitingPMF_pgf {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    pmfPgf completedPrivateWaitingPMF z =
      8 * z ^ 2 / ((5 - z) * (3 - z)) := by
  rw [completedPrivateWaitingPMF,
    pmfPgf_map_add_left completedPrivateOffsetPMF 2 hz0 hz1]
  unfold pmfPgf
  simp_rw [completedPrivateOffsetPMF_realMass,
    completedPrivateOffsetMass]
  have h3 : Summable fun k : ℕ => (z / 3) ^ k :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith)
  have h5 : Summable fun k : ℕ => (z / 5) ^ k :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith)
  rw [show (fun k : ℕ =>
      ((4 / 3 : ℝ) * (1 / 3 : ℝ) ^ k -
        (4 / 5 : ℝ) * (1 / 5 : ℝ) ^ k) * z ^ k) =
      (fun k => (4 / 3 : ℝ) * (z / 3) ^ k -
        (4 / 5 : ℝ) * (z / 5) ^ k) by
        funext k
        simp only [div_eq_mul_inv, mul_pow]
        ring]
  rw [Summable.tsum_sub (h3.mul_left (4 / 3))
      (h5.mul_left (4 / 5)),
    tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith : |z / 3| < 1),
    tsum_geometric_of_abs_lt_one (by
      rw [abs_div, abs_of_nonneg hz0]
      norm_num
      linarith : |z / 5| < 1)]
  have h3z : 3 - z ≠ 0 := by linarith
  have h5z : 5 - z ≠ 0 := by linarith
  field_simp
  ring

/-- The actual accepted-response interarrival law.  Its construction samples
fresh iid completed-private waits and an independent geometric acceptance
count. -/
noncomputable def acceptedResponseWaitingPMF (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) : PMF ℕ :=
  geometricRandomSumLaw completedPrivateWaitingPMF θ hθ hθ1

theorem acceptedResponseWaitingPMF_hasFiniteFirstMoment (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    HasFiniteFirstMoment (acceptedResponseWaitingPMF θ hθ hθ1) := by
  rw [acceptedResponseWaitingPMF]
  exact hasFiniteFirstMoment_geometricRandomSumLaw
    completedPrivateWaitingPMF θ hθ hθ1
    completedPrivateWaitingPMF_hasFiniteFirstMoment

/-- Exact expectation of the accepted-response waiting time. -/
theorem acceptedResponseWaitingPMF_firstMoment (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    pmfFirstMoment (acceptedResponseWaitingPMF θ hθ hθ1) =
      11 / (4 * θ) := by
  rw [acceptedResponseWaitingPMF,
    pmfFirstMoment_geometricRandomSumLaw completedPrivateWaitingPMF θ hθ hθ1
      completedPrivateWaitingPMF_hasFiniteFirstMoment,
    completedPrivateWaitingPMF_firstMoment]
  field_simp [ne_of_gt hθ]

/-- Reciprocal mean, i.e. the long-run response rate supplied by the renewal
law. -/
theorem acceptedResponseWaitingPMF_rate (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (pmfFirstMoment (acceptedResponseWaitingPMF θ hθ hθ1))⁻¹ =
      (4 / 11 : ℝ) * θ := by
  rw [acceptedResponseWaitingPMF_firstMoment θ hθ hθ1]
  field_simp [ne_of_gt hθ]

/-- Acceptance probability fixed by the manuscript's locked opportunity
instrument. -/
noncomputable def manuscriptAcceptanceProbability : ℝ :=
  576851 / 417942208512

theorem manuscriptAcceptanceProbability_pos :
    0 < manuscriptAcceptanceProbability := by
  norm_num [manuscriptAcceptanceProbability]

theorem manuscriptAcceptanceProbability_le_one :
    manuscriptAcceptanceProbability ≤ 1 := by
  norm_num [manuscriptAcceptanceProbability]

/-- Exact source-native response rate appearing in the manuscript. -/
theorem manuscriptAcceptedResponseRate :
    (4 / 11 : ℝ) * manuscriptAcceptanceProbability =
      52441 / 104485552128 := by
  norm_num [manuscriptAcceptanceProbability]

/-- Exact accepted-response PGF, derived from the PMF construction. -/
theorem acceptedResponseWaitingPMF_pgf (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hzContract : z < 1) :
    pmfPgf (acceptedResponseWaitingPMF θ hθ hθ1) z =
      8 * θ * z ^ 2 /
        (15 - 8 * z + (8 * θ - 7) * z ^ 2) := by
  rw [acceptedResponseWaitingPMF,
    pmfPgf_geometricRandomSumLaw completedPrivateWaitingPMF θ hθ hθ1
      hz0 hz1,
    completedPrivateWaitingPMF_pgf hz0 hz1]
  have hF0 : 0 ≤ 8 * z ^ 2 / ((5 - z) * (3 - z)) := by
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg z))
      (mul_nonneg (by linarith) (by linarith))
  have hFlt : 8 * z ^ 2 / ((5 - z) * (3 - z)) < 1 := by
    rw [div_lt_one (mul_pos (by linarith) (by linarith))]
    nlinarith [sq_nonneg (z - 1)]
  have hθrange : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hcontract : |(1 - θ) *
      (8 * z ^ 2 / ((5 - z) * (3 - z)))| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hθrange hF0)]
    calc
      (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z)))
          ≤ 1 * (8 * z ^ 2 / ((5 - z) * (3 - z))) := by
            gcongr
            linarith
      _ < 1 := by simpa using hFlt
  rw [geometricRandomSumTransform_eq _ _ hcontract]
  have hD : (5 - z) * (3 - z) ≠ 0 :=
    mul_ne_zero (by linarith) (by linarith)
  have hE : 15 - 8 * z + (8 * θ - 7) * z ^ 2 ≠ 0 := by
    have hpos : 0 < 15 - 8 * z + (8 * θ - 7) * z ^ 2 := by
      nlinarith [sq_nonneg (z - 1), mul_nonneg hθ.le (sq_nonneg z)]
    exact ne_of_gt hpos
  exact accepted_response_renewal.1 θ z hD hE

/-- Exact accepted-response PGF beyond the unit interval whenever the base
series and the geometric thinning series converge. -/
theorem acceptedResponseWaitingPMF_pgf_of_lt_three (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ}
    (hz0 : 0 ≤ z) (hz3 : z < 3)
    (hcontract : |(1 - θ) *
      (8 * z ^ 2 / ((5 - z) * (3 - z)))| < 1) :
    pmfPgf (acceptedResponseWaitingPMF θ hθ hθ1) z =
      8 * θ * z ^ 2 /
        (15 - 8 * z + (8 * θ - 7) * z ^ 2) := by
  have hb := completedPrivateWaitingPMF_pgf_summable_and_eq_of_lt_three
    hz0 hz3
  rw [acceptedResponseWaitingPMF]
  rw [(pmfPgf_geometricRandomSumLaw_summable_and_eq
    completedPrivateWaitingPMF θ hθ hθ1 hz0 hb.1 (by
      rw [hb.2]
      exact hcontract)).2,
    hb.2]
  rw [geometricRandomSumTransform_eq _ _ hcontract]
  have hD : (5 - z) * (3 - z) ≠ 0 :=
    mul_ne_zero (by linarith) (by linarith)
  have hE : 15 - 8 * z + (8 * θ - 7) * z ^ 2 ≠ 0 := by
    intro hzero
    have hgeomDen :
        1 - (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z))) ≠ 0 := by
      intro h
      have habsOne : |(1 - θ) *
          (8 * z ^ 2 / ((5 - z) * (3 - z)))| = 1 := by
        have hv : (1 - θ) *
            (8 * z ^ 2 / ((5 - z) * (3 - z))) = 1 := by linarith
        rw [hv, abs_one]
      linarith
    apply hgeomDen
    rw [show 1 - (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z))) =
        (15 - 8 * z + (8 * θ - 7) * z ^ 2) /
          ((5 - z) * (3 - z)) by
      rw [eq_div_iff hD]
      rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hD]
      ring,
      hzero]
    simp
  exact accepted_response_renewal.1 θ z hD hE

/-- Survivor transform canonically associated with a PMF.  Below it is also
identified with the generating series of the strict tail probabilities. -/
noncomputable def pmfSurvivorTransform (p : PMF ℕ) (z : ℝ) : ℝ :=
  (1 - pmfPgf p z) / (1 - z)

/-- Exact survivor transform of the accepted-response waiting law. -/
theorem acceptedResponseWaitingPMF_survivorTransform (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    pmfSurvivorTransform (acceptedResponseWaitingPMF θ hθ hθ1) z =
      (15 + 7 * z) /
        (15 - 8 * z + (8 * θ - 7) * z ^ 2) := by
  unfold pmfSurvivorTransform
  rw [acceptedResponseWaitingPMF_pgf θ hθ hθ1 hz0 hz1.le hz1]
  have hE : 15 - 8 * z + (8 * θ - 7) * z ^ 2 ≠ 0 := by
    have hpos : 0 < 15 - 8 * z + (8 * θ - 7) * z ^ 2 := by
      nlinarith [sq_nonneg (z - 1), mul_nonneg hθ.le (sq_nonneg z)]
    exact ne_of_gt hpos
  exact accepted_response_renewal.2.1 θ z hE (ne_of_lt hz1)

/-- Strict-tail probability `Pr(T > n)` of a natural-valued PMF. -/
noncomputable def pmfStrictTail (p : PMF ℕ) (n : ℕ) : ℝ :=
  ∑' m, if n < m then pmfRealMass p m else 0

theorem pmfStrictTail_nonneg (p : PMF ℕ) (n : ℕ) :
    0 ≤ pmfStrictTail p n := by
  exact tsum_nonneg fun m => by
    split <;> positivity [pmfRealMass_nonneg p m]

theorem pmfStrictTail_le_one (p : PMF ℕ) (n : ℕ) :
    pmfStrictTail p n ≤ 1 := by
  rw [← pmfRealMass_tsum p]
  unfold pmfStrictTail
  have hs : Summable fun m =>
      if n < m then pmfRealMass p m else 0 := by
    apply Summable.of_norm_bounded (pmfRealMass_summable p)
    intro m
    split
    · exact le_of_eq (abs_of_nonneg (pmfRealMass_nonneg p m))
    · simp [pmfRealMass_nonneg]
  exact hs.tsum_le_tsum (fun m => by
    split <;> simp [pmfRealMass_nonneg]) (pmfRealMass_summable p)

/-- Generating series of the strict-tail probabilities. -/
noncomputable def pmfSurvivorGeneratingFunction (p : PMF ℕ) (z : ℝ) : ℝ :=
  ∑' n, pmfStrictTail p n * z ^ n

theorem pmfSurvivorGeneratingFunction_summable (p : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable fun n => pmfStrictTail p n * z ^ n := by
  have hgeom : Summable fun n : ℕ => z ^ n :=
    summable_geometric_of_abs_lt_one (by
      rw [abs_of_nonneg hz0]
      exact hz1)
  apply Summable.of_norm_bounded hgeom
  intro n
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pmfStrictTail_nonneg p n), abs_pow,
    abs_of_nonneg hz0]
  exact mul_le_of_le_one_left (pow_nonneg hz0 n)
    (pmfStrictTail_le_one p n)

set_option maxHeartbeats 800000 in
-- The proof uses a nonnegative Tonelli exchange over tail index and outcome.
/-- The strict-tail series is the standard survivor transform
`(1 - F(z)) / (1 - z)`. -/
theorem pmfSurvivorGeneratingFunction_eq_transform (p : PMF ℕ) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    pmfSurvivorGeneratingFunction p z = pmfSurvivorTransform p z := by
  let term : ℕ × ℕ → ℝ := fun nm =>
    if nm.1 < nm.2 then pmfRealMass p nm.2 * z ^ nm.1 else 0
  have hterm : ∀ nm, 0 ≤ term nm := by
    intro nm
    simp only [term]
    split <;> positivity [pmfRealMass_nonneg p nm.2, pow_nonneg hz0 nm.1]
  have hrow : ∀ n, Summable fun m => term (n, m) := by
    intro n
    apply Summable.of_norm_bounded (pmfRealMass_summable p)
    intro m
    by_cases hnm : n < m
    · rw [show term (n, m) = pmfRealMass p m * z ^ n by
          simp [term, hnm],
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pmfRealMass_nonneg p m), abs_pow,
        abs_of_nonneg hz0]
      exact mul_le_of_le_one_right (pmfRealMass_nonneg p m)
        (pow_le_one₀ hz0 hz1.le)
    · simp [term, hnm, pmfRealMass_nonneg]
  have hrowSum : ∀ n, (∑' m, term (n, m)) =
      pmfStrictTail p n * z ^ n := by
    intro n
    unfold pmfStrictTail
    have hi : Summable fun m =>
        if n < m then pmfRealMass p m else 0 := by
      apply Summable.of_norm_bounded (pmfRealMass_summable p)
      intro m
      by_cases hnm : n < m
      · simp [hnm, abs_of_nonneg (pmfRealMass_nonneg p m)]
      · simp [hnm, pmfRealMass_nonneg]
    rw [← hi.tsum_mul_right]
    apply tsum_congr
    intro m
    by_cases hnm : n < m
    · simp [term, hnm]
    · simp [term, hnm]
  have houter : Summable fun n => ∑' m, term (n, m) := by
    simpa only [hrowSum] using
      pmfSurvivorGeneratingFunction_summable p hz0 hz1
  have hdouble : Summable term := by
    rw [summable_prod_of_nonneg hterm]
    exact ⟨hrow, houter⟩
  have hcolumnSum : ∀ m, (∑' n, term (n, m)) =
      pmfRealMass p m * ∑ n ∈ Finset.range m, z ^ n := by
    intro m
    rw [tsum_eq_sum (s := Finset.range m) (fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      simp [term, hn])]
    calc
      (∑ n ∈ Finset.range m, term (n, m)) =
          ∑ n ∈ Finset.range m, pmfRealMass p m * z ^ n := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [term, Finset.mem_range.mp hn]
      _ = pmfRealMass p m * ∑ n ∈ Finset.range m, z ^ n := by
            rw [Finset.mul_sum]
  have hcolumns : Summable fun m => ∑' n, term (n, m) := by
    simpa only [Prod.swap_prod_mk] using hdouble.prod_symm.prod
  have hfiniteColumns : Summable fun m =>
      pmfRealMass p m * ∑ n ∈ Finset.range m, z ^ n := by
    exact hcolumns.congr hcolumnSum
  have hswap : pmfSurvivorGeneratingFunction p z =
      ∑' m, pmfRealMass p m * ∑ n ∈ Finset.range m, z ^ n := by
    unfold pmfSurvivorGeneratingFunction
    calc
      (∑' n, pmfStrictTail p n * z ^ n) =
          ∑' n, ∑' m, term (n, m) := by
            apply tsum_congr
            intro n
            exact (hrowSum n).symm
      _ = ∑' m, ∑' n, term (n, m) :=
        (Summable.tsum_comm (f := fun n m => term (n, m)) hdouble).symm
      _ = ∑' m, pmfRealMass p m *
          ∑ n ∈ Finset.range m, z ^ n := by
            apply tsum_congr
            exact hcolumnSum
  have hzne : 1 - z ≠ 0 := by linarith
  unfold pmfSurvivorTransform
  rw [eq_div_iff hzne]
  rw [hswap, ← hfiniteColumns.tsum_mul_right]
  calc
    (∑' m, (pmfRealMass p m * ∑ n ∈ Finset.range m, z ^ n) *
        (1 - z)) =
        ∑' m, (pmfRealMass p m - pmfRealMass p m * z ^ m) := by
          apply tsum_congr
          intro m
          rw [mul_assoc, geom_sum_mul_neg]
          ring
    _ = (∑' m, pmfRealMass p m) -
        ∑' m, pmfRealMass p m * z ^ m := by
          rw [Summable.tsum_sub (pmfRealMass_summable p)
            (pmfPgf_summable p (by
              rw [abs_of_nonneg hz0]
              exact hz1.le))]
    _ = 1 - pmfPgf p z := by
          rw [pmfRealMass_tsum]
          rfl

/-- The displayed survivor rational function is the generating series of the
actual strict-tail probabilities. -/
theorem acceptedResponseWaitingPMF_survivorGeneratingFunction (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    pmfSurvivorGeneratingFunction
        (acceptedResponseWaitingPMF θ hθ hθ1) z =
      (15 + 7 * z) /
        (15 - 8 * z + (8 * θ - 7) * z ^ 2) := by
  rw [pmfSurvivorGeneratingFunction_eq_transform _ hz0 hz1,
    acceptedResponseWaitingPMF_survivorTransform θ hθ hθ1 hz0 hz1]

/-- A natural-valued law has a positive response-tail exponent when its PGF
converges at some real point strictly larger than one.  This is the standard
exponential-moment certificate for exponential tail decay. -/
def HasPositiveResponseTailExponent (p : PMF ℕ) : Prop :=
  ∃ z : ℝ, 1 < z ∧
    Summable fun n => pmfRealMass p n * z ^ n

/-- For every fixed positive acceptance probability, the accepted-response
law has a genuine positive exponential moment, hence a positive fixed-source
response-tail exponent. -/
theorem acceptedResponseWaitingPMF_hasPositiveTailExponent (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    HasPositiveResponseTailExponent
      (acceptedResponseWaitingPMF θ hθ hθ1) := by
  let z : ℝ := 1 + θ / 100
  have hz1 : 1 < z := by
    dsimp [z]
    linarith
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz1.le
  have hz3 : z < 3 := by
    dsimp [z]
    linarith
  have hb := completedPrivateWaitingPMF_pgf_summable_and_eq_of_lt_three
    hz0 hz3
  have hden : 0 < (5 - z) * (3 - z) :=
    mul_pos (by linarith) (by linarith)
  have hF0 : 0 ≤ pmfPgf completedPrivateWaitingPMF z := by
    rw [hb.2]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg z)) hden.le
  have hcontract : |(1 - θ) * pmfPgf completedPrivateWaitingPMF z| < 1 := by
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) hF0), hb.2]
    rw [show (1 - θ) * (8 * z ^ 2 / ((5 - z) * (3 - z))) =
        ((1 - θ) * 8 * z ^ 2) / ((5 - z) * (3 - z)) by ring,
      div_lt_one hden]
    dsimp [z]
    nlinarith [sq_nonneg θ,
      mul_nonneg hθ.le (sq_nonneg θ)]
  refine ⟨z, hz1, ?_⟩
  rw [acceptedResponseWaitingPMF]
  exact (pmfPgf_geometricRandomSumLaw_summable_and_eq
    completedPrivateWaitingPMF θ hθ hθ1 hz0 hb.1 hcontract).1

/-- The opportunity-count channel with rejection acting as the identity. -/
noncomputable def acceptedOpportunityChannel {n : Type*} [Fintype n]
    [DecidableEq n] (R : Matrix n n ℝ) (θ : ℝ) : Matrix n n ℝ :=
  R + (1 - θ) • ((1 : Matrix n n ℝ) - R)

theorem acceptedOpportunityChannel_power {n : Type*} [Fintype n]
    [DecidableEq n] (R : Matrix n n ℝ) (hR : R * R = R)
    (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (acceptedOpportunityChannel R θ) ^ N =
      R + (1 - θ) ^ N • ((1 : Matrix n n ℝ) - R) := by
  exact accepted_channel_power R hR (1 - θ) N hN

/-- Raw-time channel obtained by conditioning on whether an accepted response
has occurred by time `n`. -/
noncomputable def acceptedRawTimeChannel {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : Matrix ι ι ℝ) (p : PMF ℕ) (n : ℕ) :
    Matrix ι ι ℝ :=
  R + pmfStrictTail p n • ((1 : Matrix ι ι ℝ) - R)

theorem acceptedResponseRawTimeChannel {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    acceptedRawTimeChannel R (acceptedResponseWaitingPMF θ hθ hθ1) n =
      R + pmfStrictTail (acceptedResponseWaitingPMF θ hθ hθ1) n •
        ((1 : Matrix ι ι ℝ) - R) := rfl

end NCG
