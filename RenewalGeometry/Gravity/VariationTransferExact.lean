/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Transfer of a classified variational representative
  (`lem:supp-variation-transfer`, `eq:main-action-variation-remainder`,
  `eq:main-first-variation-reduction`; emergent-spacetime manuscript)

The complete first variation of the physical action on a represented determining test
is written as its classified representative plus a remainder
(`eq:main-action-variation-remainder`)

  `δ𝒜_X[v] = α_X δS_{H,X}[v] + β_X δS_{P,X}[v] + λ_X δV_X[v] + 𝔯_X[v]`.

* `classifiedVariationRemainder` — the remainder `𝔯_X[v]` of
  `eq:main-action-variation-remainder`.
* `tendsto_completeVariation_of_classified` — `lem:supp-variation-transfer`, first
  clause: on any index filter (the cutoff sequence, or a realized subsequence) if the three
  classified variations converge on the test, the calibrated coefficients converge, and the
  remainder tends to zero (`eq:main-first-variation-reduction`), then the complete variation
  converges to the limiting classified variation `α δS_H + β δS_P + λ δV`.
* `classifiedVariation_limit_eq_zero_of_complete` — second clause: if moreover the complete
  variation tends to zero, the limiting classified variation vanishes.
* `ae_tendsto_completeVariation_of_classified_subseq`,
  `ae_classifiedVariation_limit_eq_zero_of_complete_subseq` — the stochastic clause: on
  one probability space carrying all cutoff records, along one common realized subsequence
  `φ` of cutoffs on which, almost surely, the hypotheses hold for every determining test,
  the same conclusions hold almost surely for every test.  The argument is applied
  pointwise after the common almost-sure subsequence has been selected; no independent
  subsequences are combined.
-/

open Filter Topology MeasureTheory

namespace RenewalGeometry

/-- `eq:main-action-variation-remainder`: the remainder
`𝔯_X[v] = δ𝒜_X[v] - α_X δS_{H,X}[v] - β_X δS_{P,X}[v] - λ_X δV_X[v]` of the complete action
variation against its classified representative, at the index `n`. -/
def classifiedVariationRemainder {ι : Type*} (δA δH δP δV : ι → ℝ) (α β lam : ι → ℝ)
    (n : ι) : ℝ :=
  δA n - α n * δH n - β n * δP n - lam n * δV n

/-- The complete variation is the classified representative plus the remainder. -/
theorem completeVariation_eq_classified_add_remainder {ι : Type*}
    (δA δH δP δV : ι → ℝ) (α β lam : ι → ℝ) (n : ι) :
    δA n = α n * δH n + β n * δP n + lam n * δV n
      + classifiedVariationRemainder δA δH δP δV α β lam n := by
  unfold classifiedVariationRemainder
  ring

/-- `lem:supp-variation-transfer`, first clause (deterministic form, on an arbitrary
index filter `l` — the cutoff sequence or any realized subsequence): if the classified
Holst, Palatini and volume variations converge on the test, the three calibrated
coefficients converge, and the remainder satisfies
`eq:main-first-variation-reduction` (`𝔯_X → 0`), then the complete action variation
converges to the limiting classified variation `a·L_H + b·L_P + c·L_V`. -/
theorem tendsto_completeVariation_of_classified {ι : Type*} {l : Filter ι}
    (δA δH δP δV : ι → ℝ) (α β lam : ι → ℝ) {a b c LH LP LV : ℝ}
    (hα : Tendsto α l (𝓝 a)) (hβ : Tendsto β l (𝓝 b)) (hlam : Tendsto lam l (𝓝 c))
    (hH : Tendsto δH l (𝓝 LH)) (hP : Tendsto δP l (𝓝 LP)) (hV : Tendsto δV l (𝓝 LV))
    (hr : Tendsto (classifiedVariationRemainder δA δH δP δV α β lam) l (𝓝 0)) :
    Tendsto δA l (𝓝 (a * LH + b * LP + c * LV)) := by
  have h : Tendsto (fun n => α n * δH n + β n * δP n + lam n * δV n
      + classifiedVariationRemainder δA δH δP δV α β lam n) l
      (𝓝 (a * LH + b * LP + c * LV + 0)) :=
    (((hα.mul hH).add (hβ.mul hP)).add (hlam.mul hV)).add hr
  rw [add_zero] at h
  refine h.congr fun n => ?_
  exact (completeVariation_eq_classified_add_remainder δA δH δP δV α β lam n).symm

/-- `lem:supp-variation-transfer`, second clause: under the same hypotheses, if the
complete action variation tends to zero on the test, the limiting classified variation
vanishes. -/
theorem classifiedVariation_limit_eq_zero_of_complete {ι : Type*} {l : Filter ι} [l.NeBot]
    (δA δH δP δV : ι → ℝ) (α β lam : ι → ℝ) {a b c LH LP LV : ℝ}
    (hα : Tendsto α l (𝓝 a)) (hβ : Tendsto β l (𝓝 b)) (hlam : Tendsto lam l (𝓝 c))
    (hH : Tendsto δH l (𝓝 LH)) (hP : Tendsto δP l (𝓝 LP)) (hV : Tendsto δV l (𝓝 LV))
    (hr : Tendsto (classifiedVariationRemainder δA δH δP δV α β lam) l (𝓝 0))
    (hA : Tendsto δA l (𝓝 0)) :
    a * LH + b * LP + c * LV = 0 :=
  tendsto_nhds_unique
    (tendsto_completeVariation_of_classified δA δH δP δV α β lam hα hβ hlam hH hP hV hr) hA

/-- `lem:supp-variation-transfer`, stochastic clause (first part): on one probability
space `(Ω, μ)` carrying the stochastic records of every cutoff `X : ℕ` and every
determining test `k`, along one common realized subsequence `φ` of cutoffs on which,
almost surely, the classified variations converge on every test and the remainder tends
to zero, the complete variation converges almost surely on every test to the limiting
classified variation.  The deterministic transfer is applied pointwise on the selected
subsequence. -/
theorem ae_tendsto_completeVariation_of_classified_subseq {Ω κ : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (δA δH δP δV : ℕ → κ → Ω → ℝ) (α β lam : ℕ → ℝ) {a b c : ℝ}
    (LH LP LV : κ → Ω → ℝ)
    (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hlam : Tendsto lam atTop (𝓝 c))
    (hH : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δH (φ j) k ω) atTop (𝓝 (LH k ω)))
    (hP : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δP (φ j) k ω) atTop (𝓝 (LP k ω)))
    (hV : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δV (φ j) k ω) atTop (𝓝 (LV k ω)))
    (hr : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j =>
      classifiedVariationRemainder (fun X => δA X k ω) (fun X => δH X k ω)
        (fun X => δP X k ω) (fun X => δV X k ω) α β lam (φ j)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δA (φ j) k ω) atTop
      (𝓝 (a * LH k ω + b * LP k ω + c * LV k ω)) := by
  filter_upwards [hH, hP, hV, hr] with ω hHω hPω hVω hrω
  intro k
  have hα' : Tendsto (fun j => α (φ j)) atTop (𝓝 a) := hα.comp hφ.tendsto_atTop
  have hβ' : Tendsto (fun j => β (φ j)) atTop (𝓝 b) := hβ.comp hφ.tendsto_atTop
  have hlam' : Tendsto (fun j => lam (φ j)) atTop (𝓝 c) := hlam.comp hφ.tendsto_atTop
  exact tendsto_completeVariation_of_classified (fun j => δA (φ j) k ω)
    (fun j => δH (φ j) k ω) (fun j => δP (φ j) k ω) (fun j => δV (φ j) k ω)
    (fun j => α (φ j)) (fun j => β (φ j)) (fun j => lam (φ j))
    hα' hβ' hlam' (hHω k) (hPω k) (hVω k) (hrω k)

/-- `lem:supp-variation-transfer`, stochastic clause (second part): if along the same
common realized subsequence the complete variation tends to zero almost surely on every
test, the limiting classified variation vanishes almost surely on every test. -/
theorem ae_classifiedVariation_limit_eq_zero_of_complete_subseq {Ω κ : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (δA δH δP δV : ℕ → κ → Ω → ℝ) (α β lam : ℕ → ℝ) {a b c : ℝ}
    (LH LP LV : κ → Ω → ℝ)
    (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hlam : Tendsto lam atTop (𝓝 c))
    (hH : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δH (φ j) k ω) atTop (𝓝 (LH k ω)))
    (hP : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δP (φ j) k ω) atTop (𝓝 (LP k ω)))
    (hV : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δV (φ j) k ω) atTop (𝓝 (LV k ω)))
    (hr : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j =>
      classifiedVariationRemainder (fun X => δA X k ω) (fun X => δH X k ω)
        (fun X => δP X k ω) (fun X => δV X k ω) α β lam (φ j)) atTop (𝓝 0))
    (hA : ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun j => δA (φ j) k ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ k, a * LH k ω + b * LP k ω + c * LV k ω = 0 := by
  filter_upwards [ae_tendsto_completeVariation_of_classified_subseq μ φ hφ δA δH δP δV
    α β lam LH LP LV hα hβ hlam hH hP hV hr, hA] with ω hlim hAω
  intro k
  exact tendsto_nhds_unique (hlim k) (hAω k)

end RenewalGeometry
