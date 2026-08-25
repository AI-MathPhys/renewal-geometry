/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The universal physical continuum: the record-local passage glue

Record-local machinery for `thm:universal-physical-continuum`, whose twelve
proof anchors are all proved records (`thm:global-cylinder-descent`,
`thm:AF-limit-state`, `thm:summable-state-correction`,
`thm:projective-state-alternative`, `thm:quasilocal-completion`,
`thm:GNS-observable-limit`, `thm:GT-Mosco`,
`thm:field-tightness-alternative`, `thm:joint-source-inductive-limit`,
`thm:metric-profile-alternative`, `thm:feedback-limit-classification`,
`def:GT-continuum-realization`).  The three passage steps the proof performs
in place are formalized exactly:

* `posSemidef_of_entrywise_tendsto`: entrywise limits of positive Gram
  matrices remain positive;
* `dense_coercivity_extension`: the common coercive bound extends from the
  finite source vectors to the limiting selected sector by saturation and
  continuity;
* `not_scalar_of_centered_positive`: a centered observable with positive
  limiting norm excludes a scalar or zero realization — the cyclic vector
  and the centered observable vector are never proportional.
-/

open Filter Topology Matrix
open scoped ComplexOrder

namespace NCG
namespace UniversalContinuum

/-! ### Entrywise limits of positive Gram matrices remain positive -/

variable {ι : Type*} [Finite ι]

theorem posSemidef_of_entrywise_tendsto {M : ℕ → Matrix ι ι ℂ}
    {Mlim : Matrix ι ι ℂ} (hpsd : ∀ k, (M k).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 (Mlim i j))) :
    Mlim.PosSemidef := by
  haveI := Fintype.ofFinite ι
  have hquad : ∀ x : ι → ℂ,
      Tendsto (fun k => star x ⬝ᵥ ((M k) *ᵥ x)) atTop
        (𝓝 (star x ⬝ᵥ (Mlim *ᵥ x))) := by
    intro x
    simp only [dotProduct, Matrix.mulVec]
    exact tendsto_finsetSum _ fun i _ =>
      Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ =>
        Tendsto.mul_const _ (hlim i j))
  have hherm : Mlim.IsHermitian := by
    ext i j
    have hstar : Tendsto (fun k => star ((M k) j i)) atTop
        (𝓝 (star (Mlim j i))) := (continuous_star.tendsto _).comp (hlim j i)
    have heq : (fun k => star ((M k) j i)) = fun k => (M k) i j := by
      funext k
      calc star ((M k) j i) = ((M k)ᴴ) i j :=
            (Matrix.conjTranspose_apply _ _ _).symm
        _ = (M k) i j := by rw [(hpsd k).1]
    rw [heq] at hstar
    have huniq := tendsto_nhds_unique hstar (hlim i j)
    exact (Matrix.conjTranspose_apply _ _ _).trans huniq
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  have hterms : ∀ k, (0 : ℂ) ≤ star x ⬝ᵥ ((M k) *ᵥ x) := fun k =>
    (hpsd k).dotProduct_mulVec_nonneg x
  have hre := (Complex.continuous_re.tendsto _).comp (hquad x)
  have him := (Complex.continuous_im.tendsto _).comp (hquad x)
  rw [Complex.le_def]
  constructor
  · have hre0 : ∀ k, (0 : ℝ) ≤ (star x ⬝ᵥ ((M k) *ᵥ x)).re := fun k => by
      have h := (Complex.le_def.mp (hterms k)).1
      simpa using h
    have := ge_of_tendsto hre (Filter.Eventually.of_forall hre0)
    simpa using this
  · have him0 : (fun k => (star x ⬝ᵥ ((M k) *ᵥ x)).im) = fun _ => (0 : ℝ) := by
      funext k
      have h := (Complex.le_def.mp (hterms k)).2
      simpa using h.symm
    rw [Function.comp_def] at him
    rw [him0] at him
    have := tendsto_nhds_unique him tendsto_const_nhds
    simpa using this.symm

/-! ### The coercive bound extends to the limiting selected sector -/

/-- **Saturation and continuity extend the common coercive bound** from the
finite source vectors to the limiting selected sector. -/
theorem dense_coercivity_extension {E : Type*} [NormedAddCommGroup E]
    (q : E → ℝ) (hq : Continuous q) (c : ℝ) (D : Set E) (hD : Dense D)
    (hbound : ∀ x ∈ D, c * ‖x‖ ^ 2 ≤ q x) (x : E) : c * ‖x‖ ^ 2 ≤ q x := by
  have hclosed : IsClosed {y : E | c * ‖y‖ ^ 2 ≤ q y} :=
    isClosed_le (by fun_prop) hq
  exact hclosed.closure_subset_iff.mpr hbound (hD x)

/-! ### Nondegeneracy: no scalar or zero realization -/

/-- **A centered observable with positive limiting norm excludes a scalar or
zero realization**: the centered observable vector is never a scalar multiple
of the cyclic vector. -/
theorem not_scalar_of_centered_positive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Ω a : H} (ha : a ≠ 0)
    (horth : inner ℂ Ω a = 0) (c : ℂ) : a ≠ c • Ω := by
  intro hc
  rcases eq_or_ne Ω 0 with hΩ | hΩ
  · rw [hΩ, smul_zero] at hc
    exact ha hc
  · rw [hc, inner_smul_right] at horth
    have hΩ2 : inner ℂ Ω Ω ≠ 0 := inner_self_ne_zero.mpr hΩ
    rcases mul_eq_zero.mp horth with h | h
    · rw [h, zero_smul] at hc
      exact ha hc
    · exact hΩ2 h

end UniversalContinuum
end NCG
