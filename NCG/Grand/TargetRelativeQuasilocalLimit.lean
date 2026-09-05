import Mathlib
import NCG.Grand.CountableWeightedSchurKernel

/-!
# Target-relative quasilocal limits

Strong convergence of contractive collar projections is upgraded to convergence
on a varying, norm-convergent selected response.  Uniform target-tail
tightness then passes to the limit.  A uniform exponential weighted estimate
is recorded as a sufficient, but unnecessary, source of the tightness modulus.
-/

open Filter

noncomputable section

namespace NCG
namespace TargetRelativeQuasilocalLimit

universe u

variable {B : Type u} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

/-- Strongly convergent contractions may be evaluated on a norm-convergent
varying vector. -/
theorem strongly_convergent_contractions_apply
    (Pstage : ℕ → B →L[ℂ] B) (Plimit : B →L[ℂ] B)
    (xstage : ℕ → B) (x : B)
    (hcontract : ∀ n, ‖Pstage n‖ ≤ 1)
    (hP : ∀ y, Tendsto (fun n => Pstage n y) atTop (nhds (Plimit y)))
    (hx : Tendsto xstage atTop (nhds x)) :
    Tendsto (fun n => Pstage n (xstage n)) atTop (nhds (Plimit x)) := by
  have hdiff : Tendsto (fun n => xstage n - x) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => x) atTop (nhds x) :=
      tendsto_const_nhds
    simpa using hx.sub hconst
  have hnormdiff : Tendsto (fun n => ‖xstage n - x‖) atTop (nhds 0) := by
    simpa using hdiff.norm
  have hsmallNorm :
      Tendsto (fun n => ‖Pstage n (xstage n - x)‖) atTop (nhds 0) := by
    refine squeeze_zero'
      (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n => ?_) hnormdiff
    calc
      ‖Pstage n (xstage n - x)‖
          ≤ ‖Pstage n‖ * ‖xstage n - x‖ := (Pstage n).le_opNorm _
      _ ≤ 1 * ‖xstage n - x‖ := by
        gcongr
        exact hcontract n
      _ = ‖xstage n - x‖ := one_mul _
  have hsmall : Tendsto (fun n => Pstage n (xstage n - x))
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsmallNorm
  have hadd := hsmall.add (hP x)
  convert hadd using 1
  · funext n
    rw [map_sub]
    abel
  · simp

/-- At each fixed radius, transported stage tails converge to the limiting
physical collar tail. -/
theorem transported_tail_at_fixed_radius
    (Pstage : ℕ → ℕ → B →L[ℂ] B) (Plimit : ℕ → B →L[ℂ] B)
    (xstage : ℕ → B) (x : B)
    (hcontract : ∀ n R, ‖Pstage n R‖ ≤ 1)
    (hP : ∀ R y,
      Tendsto (fun n => Pstage n R y) atTop (nhds (Plimit R y)))
    (hx : Tendsto xstage atTop (nhds x)) (R : ℕ) :
    Tendsto (fun n => xstage n - Pstage n R (xstage n))
      atTop (nhds (x - Plimit R x)) := by
  exact hx.sub (strongly_convergent_contractions_apply
    (fun n => Pstage n R) (Plimit R) xstage x
    (fun n => hcontract n R) (hP R) hx)

/-- Uniform target-tail tightness passes to the selected continuum response. -/
theorem target_relative_quasilocal_limit
    (Pstage : ℕ → ℕ → B →L[ℂ] B) (Plimit : ℕ → B →L[ℂ] B)
    (xstage : ℕ → B) (x : B) (tail : ℕ → ℝ)
    (hcontract : ∀ n R, ‖Pstage n R‖ ≤ 1)
    (hP : ∀ R y,
      Tendsto (fun n => Pstage n R y) atTop (nhds (Plimit R y)))
    (hx : Tendsto xstage atTop (nhds x))
    (htail : ∀ R n, ‖xstage n - Pstage n R (xstage n)‖ ≤ tail R)
    (htailZero : Tendsto tail atTop (nhds 0)) :
    Tendsto (fun R => ‖x - Plimit R x‖) atTop (nhds 0) := by
  have hlimitBound : ∀ R, ‖x - Plimit R x‖ ≤ tail R := by
    intro R
    have hconv := (transported_tail_at_fixed_radius
      Pstage Plimit xstage x hcontract hP hx R).norm
    exact le_of_tendsto hconv (Eventually.of_forall fun n => htail R n)
  exact squeeze_zero'
    (Eventually.of_forall fun R => norm_nonneg _)
    (Eventually.of_forall hlimitBound) htailZero

/-- A uniform exponential weighted estimate supplies a valid target-tail
tightness modulus. -/
theorem exponential_bound_implies_tail_tightness
    (tail : ℕ → ℝ) (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha : 0 < alpha)
    (htail : ∀ R, 0 ≤ tail R ∧
      tail R ≤ C * Real.exp (-alpha * (R : ℝ))) :
    Tendsto tail atTop (nhds 0) := by
  have hmul : Tendsto (fun R : ℕ => alpha * (R : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop halpha
  have hexp : Tendsto (fun R : ℕ => Real.exp (-(alpha * (R : ℝ))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hmajor : Tendsto
      (fun R : ℕ => C * Real.exp (-(alpha * (R : ℝ))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  exact squeeze_zero'
    (Eventually.of_forall fun R => (htail R).1)
    (Eventually.of_forall fun R => (htail R).2)
    (by simpa only [neg_mul] using hmajor)

end TargetRelativeQuasilocalLimit
end NCG
