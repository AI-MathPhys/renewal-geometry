/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact02
import NCG.Grand.MediumProved01
import NCG.Grand.CommonActionApproximateWardBounds

/-!
# Medium exact records, batch 03 (Gran-Tensor manuscript, RPESM cluster)

Exact formalizations of the following manuscript records:

* `prop:RPESM-mixed-short-transport` — adjacent-cutoff stability and
  four-cutoff transport of the mixed short (RTH.M7–RTH.M10): the
  pseudoinverse resolvent identity on a common primitive support, the exact
  adjacent difference of Schur residuals, the operator-norm stability bound
  with the `s_*` floor, the exact three-step transport rectangle, and the
  witness that transporting the diagonal Grams alone conceals a change from
  follower to orthogonal occurrence.
* `thm:RPESM-quantum-source-metric` — quantum-state-first score (RTH.17)
  for a positive scalar unquenched reweighting of a finite bosonic law, the
  complete mixed metric block decomposition (RTH.18) with its exact
  cancellation witness, and the final source short (RTH.19) through the
  entrance and semigroup-cyclic projections.
* `thm:RPESM-H4-conditioned-thread` — the protected-source bound, the
  normalizer and density windows (RH.5), exact projectivity and the
  identically-one source cocycle (RH.6), the master-law interface, and
  reflection positivity of the conditioned family.
* `thm:RPESM-H4-source-floors` — the safe window `η⋆^safe` (RH.7) and the
  explicit conditioned variance/norm/reflected-Gram floors (RH.8) through
  the sharp `tanh η` oscillation total-variation bound.
* `prop:RPESM-H4-action-no-reprice` — the intrinsic source action (RH.9):
  closed form, actual derivative `η·Var`, strict positivity, exact cutoff
  independence, and the repeated-counting identity.
* `thm:RPESM-source-conditioned-projectivity` — the relational source
  bounds, exact transport, windows (RS.3), projectivity (RS.4), unit source
  cocycle, and reflection positivity.
* `thm:RPESM-local-orbit-full-rank` — the uniform local orbit floor
  `Q ⪰ e^{-21/64} a_χ I₂`, eigenvalue floor, exact cutoff constancy of the
  normalizer, mean, and orbit Gram, and rank two at every cutoff (RS.6).
* `cth:RPESM-local-source-no-rank-one` — the liminf second-eigenvalue floor
  `liminf λ₂ ≥ e^{-21/64} a_χ > 0` along arbitrary ultraviolet refinements.
* `thm:RPESM-subextensive-fixed-source` — the exact product-law average
  orbit identity (RS.8), the transverse eigenvalue, the rank-one limit, and
  the oscillation-tilted concentration bounds.
* `cth:RPESM-bounded-source-removal` — the bounded-source quasi-average
  bound `‖lim_M Q‖ ≤ ρ⋆²η²` (RS.9), rank one at fixed positive source, and
  the vanishing source-removed orbit.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder Matrix.Norms.L2Operator

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### `prop:RPESM-mixed-short-transport`

Rendering (RTH.M7–RTH.M10): after Kato alignment the adjacent complete
block Grams `(Sᵢ, Tᵢ, Rᵢ)` live on fixed finite coefficient carriers
`E_B`, `E_Q`; the aligned common primitive support is a single projection
`P` equal to both spectral support projections `1_{(0,∞)}(Sᵢ)`, and the
floor (RTH.M7) is the Loewner bound `Sᵢ ⪰ s_* P`.  `S†` is the spectral
Moore–Penrose inverse `pinv` and `‖·‖` is the `ℓ²` operator norm
(`Matrix.Norms.L2Operator`).  The Schur residual is
`R⊥ = R - T* S† T` (`rperp`), the resolvent identity
`S₂† - S₁† = -S₂† (ΔS) S₁†` is proved on the common support, and RTH.M8,
RTH.M9, RTH.M10 are the manuscript displays verbatim.  The concluding
clause — transport of the diagonal Grams alone can conceal a change from
follower to orthogonal occurrence — is the explicit one-dimensional
witness with `S, R` transported identically while `R⊥` jumps `0 → 1`. -/

section MixedShortTransportSection

namespace MixedShortTransport

variable {eb eQ : Type*} [Fintype eb] [Fintype eQ] [DecidableEq eb]

/-- The compressed Schur residual `R⊥ = R - T* S† T` of one complete block
Gram `(S, T, R)`. -/
noncomputable def rperp {S : Matrix eb eb ℂ} (hS : S.IsHermitian)
    (T : Matrix eb eQ ℂ) (R : Matrix eQ eQ ℂ) : Matrix eQ eQ ℂ :=
  R - Tᴴ * pinv hS * T

/-- The spectral support projection absorbs the pseudoinverse on the left. -/
theorem supportProj_mul_pinv {S : Matrix eb eb ℂ} (hS : S.IsHermitian) :
    supportProj hS * pinv hS = pinv hS := by
  unfold supportProj pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hS fun i => ?_
  split_ifs <;> norm_num

/-- The spectral support projection absorbs the pseudoinverse on the right. -/
theorem pinv_mul_supportProj {S : Matrix eb eb ℂ} (hS : S.IsHermitian) :
    pinv hS * supportProj hS = pinv hS := by
  unfold supportProj pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hS fun i => ?_
  split_ifs <;> norm_num

/-- **The pseudoinverse resolvent identity on a common support**: if `S₁`
and `S₂` share the support projection `P`, then
`S₂† (S₂ - S₁) S₁† = S₁† - S₂†`. -/
theorem pinv_resolvent {S₁ S₂ : Matrix eb eb ℂ} (hS₁ : S₁.IsHermitian)
    (hS₂ : S₂.IsHermitian) {P : Matrix eb eb ℂ}
    (hP₁ : supportProj hS₁ = P) (hP₂ : supportProj hS₂ = P) :
    pinv hS₂ * (S₂ - S₁) * pinv hS₁ = pinv hS₁ - pinv hS₂ := by
  have h₂ : pinv hS₂ * S₂ = P := by
    have h := congrArg conjTranspose (mul_pinv_eq_supportProj hS₂)
    rwa [conjTranspose_mul, (pinv_isHermitian hS₂).eq, hS₂.eq,
      (supportProj_posSemidef hS₂).1.eq, hP₂] at h
  have h₁ : S₁ * pinv hS₁ = P := by rw [mul_pinv_eq_supportProj hS₁, hP₁]
  calc pinv hS₂ * (S₂ - S₁) * pinv hS₁
      = pinv hS₂ * S₂ * pinv hS₁ - pinv hS₂ * (S₁ * pinv hS₁) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
    _ = P * pinv hS₁ - pinv hS₂ * P := by rw [h₂, h₁]
    _ = supportProj hS₁ * pinv hS₁ - pinv hS₂ * supportProj hS₂ := by
        rw [hP₁, hP₂]
    _ = pinv hS₁ - pinv hS₂ := by
        rw [supportProj_mul_pinv, pinv_mul_supportProj]

omit [Fintype eQ] in
/-- **(RTH.M8)**: the exact adjacent difference of mixed Schur residuals
`R⊥,₂ - R⊥,₁ = ΔR - (ΔT)* S₂† T₂ - T₁* S₁† ΔT + T₁* S₂† (ΔS) S₁† T₂`. -/
theorem rperp_adjacent_transport {S₁ S₂ : Matrix eb eb ℂ}
    (hS₁ : S₁.IsHermitian) (hS₂ : S₂.IsHermitian) {P : Matrix eb eb ℂ}
    (hP₁ : supportProj hS₁ = P) (hP₂ : supportProj hS₂ = P)
    (T₁ T₂ : Matrix eb eQ ℂ) (R₁ R₂ : Matrix eQ eQ ℂ) :
    rperp hS₂ T₂ R₂ - rperp hS₁ T₁ R₁
      = (R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂ * T₂ - T₁ᴴ * pinv hS₁ * (T₂ - T₁)
        + T₁ᴴ * pinv hS₂ * (S₂ - S₁) * pinv hS₁ * T₂ := by
    have hres : T₁ᴴ * (pinv hS₂ * (S₂ - S₁) * pinv hS₁) * T₂
        = T₁ᴴ * pinv hS₁ * T₂ - T₁ᴴ * pinv hS₂ * T₂ := by
      rw [pinv_resolvent hS₁ hS₂ hP₁ hP₂, Matrix.mul_sub, Matrix.sub_mul]
    unfold rperp
    have hres' : T₁ᴴ * pinv hS₂ * (S₂ - S₁) * pinv hS₁ * T₂
        = T₁ᴴ * pinv hS₁ * T₂ - T₁ᴴ * pinv hS₂ * T₂ := by
      rw [← hres]
      simp only [Matrix.mul_assoc]
    rw [hres']
    simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel

/-- Every positive eigenvalue of a Gram with the Loewner support floor
`S ⪰ s P` is at least `s`. -/
theorem eigenvalues_ge_of_support_floor {S : Matrix eb eb ℂ}
    (hS : S.PosSemidef) {s : ℝ}
    (hfl : (S - (s : ℂ) • supportProj hS.1).PosSemidef) (i : eb)
    (hi : 0 < hS.1.eigenvalues i) : s ≤ hS.1.eigenvalues i := by
  have hform := re_form_nonneg hfl ⇑(hS.1.eigenvectorBasis i)
  have hPv : supportProj hS.1 *ᵥ ⇑(hS.1.eigenvectorBasis i)
      = ((1 : ℝ) : ℂ) • ⇑(hS.1.eigenvectorBasis i) := by
    unfold supportProj
    rw [CrossSign.spectralFunction_mulVec_eigenvectorBasis hS.1 _ i]
    have hval : (if 0 < hS.1.eigenvalues i then (1 : ℝ) else 0) = 1 := by
      simp [hi]
    rw [hval]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, hPv] at hform
  rw [form_eigenvectorBasis hS.1 i] at hform
  have hone : star ⇑(hS.1.eigenvectorBasis i) ⬝ᵥ
      ((s : ℂ) • (((1 : ℝ) : ℂ) • ⇑(hS.1.eigenvectorBasis i))) = (s : ℂ) := by
    rw [dotProduct_smul, dotProduct_smul, star_dot_self_eigenvectorBasis hS.1 i]
    simp
  rw [hone] at hform
  have hsub : (0 : ℝ) ≤ hS.1.eigenvalues i - s := by simpa using hform
  linarith

/-- **(RTH.M7 ⟹ pseudoinverse ceiling)**: the Loewner floor `S ⪰ s_* P` on
the support gives the operator-norm bound `‖S†‖ ≤ s_*⁻¹`. -/
theorem pinv_l2_opNorm_le {S : Matrix eb eb ℂ} (hS : S.PosSemidef) {s : ℝ}
    (hs : 0 < s) (hfl : (S - (s : ℂ) • supportProj hS.1).PosSemidef) :
    ‖pinv hS.1‖ ≤ s⁻¹ := by
  refine l2_opNorm_le_of_conjTranspose_mul_self_le_scalar _ _ (by positivity) ?_
  rw [(pinv_isHermitian hS.1).eq]
  have hsq : pinv hS.1 * pinv hS.1
      = spectralFunction hS.1
          (fun l => (if 0 < l then l⁻¹ else 0) * (if 0 < l then l⁻¹ else 0)) := by
    unfold pinv
    rw [spectralFunction_mul]
  have hone : ((s⁻¹ ^ 2 : ℝ) : ℂ) • (1 : Matrix eb eb ℂ)
      = spectralFunction hS.1 (fun _ => s⁻¹ ^ 2) :=
    (spectralFunction_const hS.1 _).symm
  rw [hsq, hone, ← spectralFunction_sub]
  refine spectralFunction_posSemidef hS.1 _ fun i => ?_
  split_ifs with hpos
  · have hge := eigenvalues_ge_of_support_floor hS hfl i hpos
    have h1 : (hS.1.eigenvalues i)⁻¹ ≤ s⁻¹ := inv_anti₀ hs hge
    have h2 : (0 : ℝ) ≤ (hS.1.eigenvalues i)⁻¹ := by positivity
    nlinarith
  · nlinarith [sq_nonneg s⁻¹]

/-- **(RTH.M9)**: the operator-norm stability of the mixed Schur residual
under adjacent-cutoff transport with the `s_*` floor:
`‖R⊥,₂ - R⊥,₁‖ ≤ ‖ΔR‖ + s_*⁻¹(‖ΔT‖‖T₂‖ + ‖T₁‖‖ΔT‖) + s_*⁻²‖T₁‖‖T₂‖‖ΔS‖`. -/
theorem rperp_adjacent_stability [DecidableEq eQ] {S₁ S₂ : Matrix eb eb ℂ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) {P : Matrix eb eb ℂ}
    (hP₁ : supportProj hS₁.1 = P) (hP₂ : supportProj hS₂.1 = P) {s : ℝ}
    (hs : 0 < s) (hfl₁ : (S₁ - (s : ℂ) • P).PosSemidef)
    (hfl₂ : (S₂ - (s : ℂ) • P).PosSemidef)
    (T₁ T₂ : Matrix eb eQ ℂ) (R₁ R₂ : Matrix eQ eQ ℂ) :
    ‖rperp hS₂.1 T₂ R₂ - rperp hS₁.1 T₁ R₁‖
      ≤ ‖R₂ - R₁‖ + s⁻¹ * (‖T₂ - T₁‖ * ‖T₂‖ + ‖T₁‖ * ‖T₂ - T₁‖)
        + s⁻¹ ^ 2 * (‖T₁‖ * ‖T₂‖ * ‖S₂ - S₁‖) := by
  have hp₁ : ‖pinv hS₁.1‖ ≤ s⁻¹ := pinv_l2_opNorm_le hS₁ hs (hP₁ ▸ hfl₁)
  have hp₂ : ‖pinv hS₂.1‖ ≤ s⁻¹ := pinv_l2_opNorm_le hS₂ hs (hP₂ ▸ hfl₂)
  have hsinv : (0 : ℝ) ≤ s⁻¹ := by positivity
  rw [rperp_adjacent_transport hS₁.1 hS₂.1 hP₁ hP₂ T₁ T₂ R₁ R₂]
  -- triangle inequality on the four-term identity
  have htri : ‖(R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂.1 * T₂
        - T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)
        + T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖
      ≤ ‖R₂ - R₁‖ + ‖(T₂ - T₁)ᴴ * pinv hS₂.1 * T₂‖
        + ‖T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖
        + ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖ := by
    calc ‖(R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂.1 * T₂
          - T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)
          + T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖
        ≤ ‖(R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂.1 * T₂
            - T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖
          + ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖ := norm_add_le _ _
      _ ≤ ‖(R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂.1 * T₂‖
          + ‖T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖
          + ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖ := by
          have := norm_sub_le ((R₂ - R₁) - (T₂ - T₁)ᴴ * pinv hS₂.1 * T₂)
            (T₁ᴴ * pinv hS₁.1 * (T₂ - T₁))
          linarith
      _ ≤ ‖R₂ - R₁‖ + ‖(T₂ - T₁)ᴴ * pinv hS₂.1 * T₂‖
          + ‖T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖
          + ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖ := by
          have := norm_sub_le (R₂ - R₁) ((T₂ - T₁)ᴴ * pinv hS₂.1 * T₂)
          linarith
  refine htri.trans ?_
  have hb₁ : ‖(T₂ - T₁)ᴴ * pinv hS₂.1 * T₂‖ ≤ ‖T₂ - T₁‖ * (s⁻¹ * ‖T₂‖) := by
    calc ‖(T₂ - T₁)ᴴ * pinv hS₂.1 * T₂‖
        ≤ ‖(T₂ - T₁)ᴴ * pinv hS₂.1‖ * ‖T₂‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖(T₂ - T₁)ᴴ‖ * ‖pinv hS₂.1‖ * ‖T₂‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖T₂ - T₁‖ * ‖pinv hS₂.1‖ * ‖T₂‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖T₂ - T₁‖ * s⁻¹ * ‖T₂‖ := by
          have := mul_le_mul_of_nonneg_left hp₂ (norm_nonneg (T₂ - T₁))
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖T₂ - T₁‖ * (s⁻¹ * ‖T₂‖) := by ring
  have hb₂ : ‖T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖ ≤ ‖T₁‖ * (s⁻¹ * ‖T₂ - T₁‖) := by
    calc ‖T₁ᴴ * pinv hS₁.1 * (T₂ - T₁)‖
        ≤ ‖T₁ᴴ * pinv hS₁.1‖ * ‖T₂ - T₁‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖T₁ᴴ‖ * ‖pinv hS₁.1‖ * ‖T₂ - T₁‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖T₁‖ * ‖pinv hS₁.1‖ * ‖T₂ - T₁‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ ‖T₁‖ * s⁻¹ * ‖T₂ - T₁‖ := by
          have := mul_le_mul_of_nonneg_left hp₁ (norm_nonneg T₁)
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖T₁‖ * (s⁻¹ * ‖T₂ - T₁‖) := by ring
  have hb₃ : ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1 * T₂‖
      ≤ ‖T₁‖ * s⁻¹ * ‖S₂ - S₁‖ * s⁻¹ * ‖T₂‖ := by
    have n₁ : ‖T₁ᴴ * pinv hS₂.1‖ ≤ ‖T₁‖ * s⁻¹ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_left hp₂ (norm_nonneg T₁)
    have n₂ : ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁)‖ ≤ ‖T₁‖ * s⁻¹ * ‖S₂ - S₁‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right n₁ (norm_nonneg _))
    have n₃ : ‖T₁ᴴ * pinv hS₂.1 * (S₂ - S₁) * pinv hS₁.1‖
        ≤ ‖T₁‖ * s⁻¹ * ‖S₂ - S₁‖ * s⁻¹ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      exact mul_le_mul n₂ hp₁ (norm_nonneg _) (by positivity)
    exact (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right n₃ (norm_nonneg _))
  nlinarith [norm_nonneg (R₂ - R₁)]

/-- **(RTH.M10)**: three adjacent quantum-coefficient transports obey the
exact rectangle
`U₃₁* R⊥,₄ U₃₁ - R⊥,₁ = D₁⊥ + U₁* D₂⊥ U₁ + U₂₁* D₃⊥ U₂₁`. -/
theorem rperp_transport_rectangle {S₁ S₂ S₃ S₄ : Matrix eb eb ℂ}
    (hS₁ : S₁.IsHermitian) (hS₂ : S₂.IsHermitian) (hS₃ : S₃.IsHermitian)
    (hS₄ : S₄.IsHermitian) (T₁ T₂ T₃ T₄ : Matrix eb eQ ℂ)
    (R₁ R₂ R₃ R₄ : Matrix eQ eQ ℂ) (U₁ U₂ U₃ : Matrix eQ eQ ℂ) :
    (U₃ * U₂ * U₁)ᴴ * rperp hS₄ T₄ R₄ * (U₃ * U₂ * U₁) - rperp hS₁ T₁ R₁
      = (U₁ᴴ * rperp hS₂ T₂ R₂ * U₁ - rperp hS₁ T₁ R₁)
        + U₁ᴴ * (U₂ᴴ * rperp hS₃ T₃ R₃ * U₂ - rperp hS₂ T₂ R₂) * U₁
        + (U₂ * U₁)ᴴ * (U₃ᴴ * rperp hS₄ T₄ R₄ * U₃ - rperp hS₃ T₃ R₃)
          * (U₂ * U₁) := by
  simp only [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- Transport of the diagonal Grams alone conceals ancestry: the adjacent
one-dimensional data `(S, T, R) = (1, 1, 1) → (1, 0, 1)` transport `S` and
`R` identically, yet the Schur residual jumps from the follower value
`R⊥ = 0` to the orthogonal occurrence `R⊥ = 1`. -/
theorem diagonal_transport_conceals_ancestry :
    ∃ (S₁ S₂ T₁ T₂ R₁ R₂ : Matrix (Fin 1) (Fin 1) ℂ)
      (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef),
      S₁ = S₂ ∧ R₁ = R₂ ∧ rperp hS₁.1 T₁ R₁ = 0 ∧ rperp hS₂.1 T₂ R₂ = 1 := by
  refine ⟨1, 1, 1, 0, 1, 1, Matrix.PosSemidef.one, Matrix.PosSemidef.one,
    rfl, rfl, ?_, ?_⟩
  · unfold rperp
    rw [pinv_one, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, sub_self]
  · unfold rperp
    rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul, sub_zero]

end MixedShortTransport

end MixedShortTransportSection

/-! ### `thm:RPESM-quantum-source-metric`

Rendering (RTH.16–RTH.19): the sector-patched packet at one conditioning
point is a finite carrier `Ω` with a positive bosonic weight family
`p t : Ω → ℝ` along one variation direction and a positive scalar
unquenched factor `z t : Ω → ℝ` (RTH.16 is the normalized law
`ν = z·p/Z`).  Scores are rendered in the energy sign convention
`F = E[∂ log ρ] − ∂ log ρ` (mean-centered negative log-derivative), under
which the manuscript display (RTH.17) is verbatim; the raw quantum score
is certified as the actual derivative of the normalized quantum
log-density (`rawScoreQ_hasDerivAt`), so nothing is encoded by
definition.  (RTH.18) is the complete mixed metric on the direction bank:
`𝒢 = (B+X)* ℒ† (B+X)` splits exactly into the four blocks, the diagonal
blocks are PSD for a PSD generator, `B + X` is exactly the quantum score
(`score_split`), and the one-dimensional hidden carrier `B = g`, `X = -g`
witnesses exact cross-term cancellation.  (RTH.19) is proved on the
finite-dimensional Hilbert carrier of `thm:GT-dynamic-source-ancestry`
(`NCG/Grand/MediumProved01.lean`): with `S₀ = B₀*B₀`, `T_Q = B₀*Y_Q`,
`R_Q = Y_Q*Y_Q` and the closed-range Moore–Penrose `S₀†`, the complete
entrance short equals `Y_Q*(I−P_{B₀})Y_Q`, which splits exactly into the
clock-generated promotion `Y_Q*(P_{H_Q}^{B₀}−P_{B₀})Y_Q` and the
dynamically new source `Y_Q*(I−P_{H_Q}^{B₀})Y_Q`, both positive, with
`P_{H_Q}^{B₀}` the genuine semigroup-cyclic projection; the delayed
orthogonality of the residual kernel to every primitive follower is the
re-exported `cyc_short_delay_orthogonality`. -/

section QuantumSourceMetricSection

namespace QuantumSourceMetric

variable {Ω : Type*} [Fintype Ω]

/-- The unquenched normalizer `Z = ∑ z·p` (RTH.16). -/
noncomputable def qnorm (w zw : Ω → ℝ) : ℝ := ∑ x, zw x * w x

/-- The positive scalar unquenched law `ν = z·p/Z` (RTH.16). -/
noncomputable def nuQ (w zw : Ω → ℝ) : Ω → ℝ := fun x => zw x * w x / qnorm w zw

/-- The raw bosonic score `∂ log p`. -/
noncomputable def rawScoreB (w dp : Ω → ℝ) : Ω → ℝ := fun x => dp x / w x

/-- The centered bosonic score `F^B` (energy sign convention). -/
noncomputable def scoreB (w dp : Ω → ℝ) : Ω → ℝ :=
  fun x => (∑ y, w y * rawScoreB w dp y) - rawScoreB w dp x

/-- The fermionic tilt derivative `ℓ^F = ∂ log z`. -/
noncomputable def ellF (zw dz : Ω → ℝ) : Ω → ℝ := fun x => dz x / zw x

/-- The raw quantum score `∂ log(z·p/Z)`. -/
noncomputable def rawScoreQ (w zw dp dz : Ω → ℝ) : Ω → ℝ := fun x =>
  ellF zw dz x + rawScoreB w dp x
    - (∑ y, (dz y * w y + zw y * dp y)) / qnorm w zw

/-- The quantum-state-first score `F^Q` (energy sign convention, centered
in the unquenched state `ν`). -/
noncomputable def scoreQ (w zw dp dz : Ω → ℝ) : Ω → ℝ := fun x =>
  (∑ y, nuQ w zw y * rawScoreQ w zw dp dz y) - rawScoreQ w zw dp dz x

variable [Nonempty Ω]

/-- The unquenched normalizer is positive. -/
theorem qnorm_pos {w zw : Ω → ℝ} (hw : ∀ x, 0 < w x) (hzw : ∀ x, 0 < zw x) :
    0 < qnorm w zw :=
  Finset.sum_pos (fun x _ => mul_pos (hzw x) (hw x)) Finset.univ_nonempty

/-- The unquenched law is a probability law. -/
theorem nuQ_sum_one {w zw : Ω → ℝ} (hw : ∀ x, 0 < w x) (hzw : ∀ x, 0 < zw x) :
    ∑ y, nuQ w zw y = 1 := by
  unfold nuQ
  rw [← Finset.sum_div]
  exact div_self (qnorm_pos hw hzw).ne'

omit [Fintype Ω] [Nonempty Ω] in
/-- The raw bosonic score is the actual derivative of the bosonic
log-likelihood. -/
theorem rawScoreB_hasDerivAt (p : ℝ → Ω → ℝ) (dp : Ω → ℝ)
    (hp : ∀ t x, 0 < p t x)
    (hdp : ∀ x, HasDerivAt (fun t => p t x) (dp x) 0) (x : Ω) :
    HasDerivAt (fun t => Real.log (p t x)) (rawScoreB (p 0) dp x) 0 :=
  (hdp x).log (hp 0 x).ne'

/-- **The raw quantum score is the actual derivative of the normalized
quantum log-density** `∂ log(z·p/Z)` — the score of (RTH.16). -/
theorem rawScoreQ_hasDerivAt (p z : ℝ → Ω → ℝ) (dp dz : Ω → ℝ)
    (hp : ∀ t x, 0 < p t x) (hz : ∀ t x, 0 < z t x)
    (hdp : ∀ x, HasDerivAt (fun t => p t x) (dp x) 0)
    (hdz : ∀ x, HasDerivAt (fun t => z t x) (dz x) 0) (x : Ω) :
    HasDerivAt (fun t => Real.log (z t x * p t x / qnorm (p t) (z t)))
      (rawScoreQ (p 0) (z 0) dp dz x) 0 := by
  have hZ0 : 0 < qnorm (p 0) (z 0) := qnorm_pos (hp 0) (hz 0)
  have hnum : HasDerivAt (fun t => z t x * p t x)
      (dz x * p 0 x + z 0 x * dp x) 0 := (hdz x).mul (hdp x)
  have hZ : HasDerivAt (fun t => qnorm (p t) (z t))
      (∑ y, (dz y * p 0 y + z 0 y * dp y)) 0 := by
    unfold qnorm
    exact HasDerivAt.fun_sum fun y _ => (hdz y).mul (hdp y)
  have hfrac := hnum.div hZ hZ0.ne'
  have hval : z 0 x * p 0 x / qnorm (p 0) (z 0) ≠ 0 := by
    have := mul_pos (hz 0 x) (hp 0 x)
    positivity
  have hlog := hfrac.log hval
  have heq : ((dz x * p 0 x + z 0 x * dp x) * qnorm (p 0) (z 0)
        - z 0 x * p 0 x * ∑ y, (dz y * p 0 y + z 0 y * dp y))
        / qnorm (p 0) (z 0) ^ 2 / (z 0 x * p 0 x / qnorm (p 0) (z 0))
      = rawScoreQ (p 0) (z 0) dp dz x := by
    unfold rawScoreQ ellF rawScoreB
    have h₁ : z 0 x ≠ 0 := (hz 0 x).ne'
    have h₂ : p 0 x ≠ 0 := (hp 0 x).ne'
    field_simp
  simp only [Pi.div_apply] at hlog
  rwa [heq] at hlog

/-- **(RTH.17)**: the quantum-state-first score decomposition
`F^Q = F^B − ℓ^F − ν(F^B − ℓ^F)`. -/
theorem quantum_state_first_score (w zw dp dz : Ω → ℝ)
    (hw : ∀ x, 0 < w x) (hzw : ∀ x, 0 < zw x) :
    scoreQ w zw dp dz = fun x =>
      scoreB w dp x - ellF zw dz x
        - ∑ y, nuQ w zw y * (scoreB w dp y - ellF zw dz y) := by
  funext x
  have hν1 := nuQ_sum_one hw hzw
  set c := (∑ y, (dz y * w y + zw y * dp y)) / qnorm w zw with hc
  set m := ∑ y, w y * rawScoreB w dp y with hm
  have hexpQ : ∀ y, nuQ w zw y * rawScoreQ w zw dp dz y
      = nuQ w zw y * ellF zw dz y + nuQ w zw y * rawScoreB w dp y
        - nuQ w zw y * c := by
    intro y
    unfold rawScoreQ
    rw [← hc]
    ring
  have hsumQ : ∑ y, nuQ w zw y * rawScoreQ w zw dp dz y
      = (∑ y, nuQ w zw y * ellF zw dz y)
        + (∑ y, nuQ w zw y * rawScoreB w dp y) - c := by
    rw [Finset.sum_congr rfl fun y _ => hexpQ y, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, hν1, one_mul]
  have hexpR : ∀ y, nuQ w zw y * (scoreB w dp y - ellF zw dz y)
      = nuQ w zw y * m - nuQ w zw y * rawScoreB w dp y
        - nuQ w zw y * ellF zw dz y := by
    intro y
    unfold scoreB
    rw [← hm]
    ring
  have hsumR : ∑ y, nuQ w zw y * (scoreB w dp y - ellF zw dz y)
      = m - (∑ y, nuQ w zw y * rawScoreB w dp y)
        - (∑ y, nuQ w zw y * ellF zw dz y) := by
    rw [Finset.sum_congr rfl fun y _ => hexpR y, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hν1, one_mul]
  have hQx : rawScoreQ w zw dp dz x
      = ellF zw dz x + rawScoreB w dp x - c := by
    unfold rawScoreQ
    rw [← hc]
  have hBx : scoreB w dp x = m - rawScoreB w dp x := by
    unfold scoreB
    rw [← hm]
  unfold scoreQ
  rw [hsumQ, hQx, hsumR, hBx]
  ring

/-- The centered bosonic and reflected-tilt writers reassemble the
quantum score: `B + X = F^Q` with `B = F^B − ν(F^B)` and
`X = −ℓ^F + ν(ℓ^F)`. -/
theorem score_split (w zw dp dz : Ω → ℝ)
    (hw : ∀ x, 0 < w x) (hzw : ∀ x, 0 < zw x) :
    (fun x => (scoreB w dp x - ∑ y, nuQ w zw y * scoreB w dp y)
        + (-ellF zw dz x + ∑ y, nuQ w zw y * ellF zw dz y))
      = scoreQ w zw dp dz := by
  funext x
  rw [quantum_state_first_score w zw dp dz hw hzw]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end QuantumSourceMetric

end QuantumSourceMetricSection

section QuantumSourceMetricMatrixSection

namespace QuantumSourceMetric

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]

/-- **(RTH.18)**: the complete mixed metric
`𝒢 = (B+X)* ℒ† (B+X)` splits exactly into
`𝒢^{BB} + 𝒢^{XX} + 𝒢^{BX} + (𝒢^{BX})*`, and the diagonal blocks are
positive for a positive generator. -/
theorem complete_mixed_metric {L : Matrix Ω Ω ℂ} (hL : L.PosSemidef)
    (B X : Matrix Ω ι ℂ) :
    (B + X)ᴴ * pinv hL.1 * (B + X)
        = Bᴴ * pinv hL.1 * B + Xᴴ * pinv hL.1 * X + Bᴴ * pinv hL.1 * X
          + (Bᴴ * pinv hL.1 * X)ᴴ
      ∧ (Bᴴ * pinv hL.1 * B).PosSemidef ∧ (Xᴴ * pinv hL.1 * X).PosSemidef := by
  refine ⟨?_, (pinv_posSemidef hL.1).conjTranspose_mul_mul_same B,
    (pinv_posSemidef hL.1).conjTranspose_mul_mul_same X⟩
  have hadj : (Bᴴ * pinv hL.1 * X)ᴴ = Xᴴ * pinv hL.1 * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (pinv_isHermitian hL.1).eq, Matrix.mul_assoc]
  rw [hadj, conjTranspose_add]
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

/-- The positive diagonal blocks do not bound the complete metric: on the
one-dimensional hidden carrier with `B = g`, `X = −g`, the cross terms
cancel the diagonal exactly (`𝒢 = 0` while `𝒢^{BB} = 𝒢^{XX} = 1`). -/
theorem cross_terms_cancel_exactly :
    ∃ (L B X : Matrix (Fin 1) (Fin 1) ℂ) (hL : L.PosSemidef),
      (B + X)ᴴ * pinv hL.1 * (B + X) = 0
        ∧ Bᴴ * pinv hL.1 * B = 1 ∧ Xᴴ * pinv hL.1 * X = 1 := by
  refine ⟨1, 1, -1, Matrix.PosSemidef.one, ?_, ?_, ?_⟩
  · rw [add_neg_cancel, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  · rw [pinv_one, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [pinv_one, conjTranspose_neg, conjTranspose_one, Matrix.mul_one,
      Matrix.neg_mul, Matrix.one_mul, neg_neg]

end QuantumSourceMetric

end QuantumSourceMetricMatrixSection

section QuantumSourceShortSection

namespace QuantumSourceMetric

open ContinuousLinearMap Submodule ClosedRangeMoorePenrose
open scoped InnerProduct ComplexInnerProductSpace

variable {V E E' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']

/-- Orthogonal star-projections compose idempotently. -/
theorem starProjection_comp_self (K : Submodule ℂ V) :
    K.starProjection ∘L K.starProjection = K.starProjection :=
  K.isIdempotentElem_starProjection

/-- The synthesis conjugate of the Gram pseudoinverse is the source-range
projection: `B₀ S₀† B₀* = P_{B₀}`. -/
theorem comp_gramPinv_comp_adjoint (B0 : E →L[ℂ] V)
    (hclosed : IsClosed (B0.range : Set V)) :
    B0 ∘L gramPinv B0 hclosed ∘L (B0†) = B0.range.starProjection := by
  have h3 : ((pinv B0 hclosed)†) ∘L (B0†) = B0.range.starProjection := by
    calc ((pinv B0 hclosed)†) ∘L (B0†)
        = (B0 ∘L pinv B0 hclosed)† := (adjoint_comp B0 (pinv B0 hclosed)).symm
      _ = B0.range.starProjection† := by rw [comp_pinv]
      _ = B0.range.starProjection :=
          isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection B0.range)
  calc B0 ∘L gramPinv B0 hclosed ∘L (B0†)
      = B0 ∘L pinv B0 hclosed ∘L (((pinv B0 hclosed)†) ∘L (B0†)) := by
        simp only [gramPinv, comp_assoc]
    _ = B0 ∘L pinv B0 hclosed ∘L B0.range.starProjection := by rw [h3]
    _ = B0 ∘L pinv B0 hclosed := by rw [pinv_comp_rangeProjection]
    _ = B0.range.starProjection := comp_pinv B0 hclosed

/-- **(RTH.19)**: the final source short.  With `S₀ = B₀*B₀`,
`T_Q = B₀*Y_Q`, `R_Q = Y_Q*Y_Q` on the completed carrier of `H_Q`, the
complete entrance short equals `Y_Q*(I−P_{B₀})Y_Q` and splits exactly into
the clock-generated promotion `Y_Q*(P_{H_Q}^{B₀}−P_{B₀})Y_Q` and the
dynamically new quantum source `Y_Q*(I−P_{H_Q}^{B₀})Y_Q`, both positive. -/
theorem final_source_short (H : V →L[ℂ] V) (B0 : E →L[ℂ] V)
    (YQ : E' →L[ℂ] V) (hclosed : IsClosed (B0.range : Set V)) :
    (YQ†) ∘L YQ - (((B0†) ∘L YQ)†) ∘L gramPinv B0 hclosed ∘L ((B0†) ∘L YQ)
        = dynRent B0 YQ
      ∧ dynRent B0 YQ = dynRprom H B0 YQ + dynRdyn H B0 YQ
      ∧ (dynRprom H B0 YQ).IsPositive ∧ (dynRdyn H B0 YQ).IsPositive := by
  obtain ⟨hsplit, hprom, hdyn⟩ := dynamic_source_ancestry_split H B0 YQ
  refine ⟨?_, hsplit, hprom, hdyn⟩
  have hadj : (((B0†) ∘L YQ)†) = (YQ†) ∘L B0 := by
    rw [adjoint_comp, adjoint_adjoint]
  have hmid : (((B0†) ∘L YQ)†) ∘L gramPinv B0 hclosed ∘L ((B0†) ∘L YQ)
      = (YQ†) ∘L B0.range.starProjection ∘L YQ := by
    rw [hadj]
    have h1 : ((YQ†) ∘L B0) ∘L gramPinv B0 hclosed ∘L ((B0†) ∘L YQ)
        = (YQ†) ∘L (B0 ∘L gramPinv B0 hclosed ∘L (B0†)) ∘L YQ := by
      simp only [comp_assoc]
    rw [comp_assoc] at h1 ⊢
    rw [h1, comp_gramPinv_comp_adjoint B0 hclosed]
  rw [hmid, dynRent, rangeProj, compress_sub]
  have hone : (YQ†) ∘L (1 : V →L[ℂ] V) ∘L YQ = (YQ†) ∘L YQ := by
    rw [one_def, id_comp]
  rw [hone]

/-- The delayed clauses of (RTH.19): after the complete cyclic short, the
kernel of the dynamically new source is delayed-orthogonal to the
primitive synthesis and to every primitive follower, at every delay
(re-export of `thm:GT-dynamic-source-ancestry`, LT.30). -/
theorem final_source_short_delayed_orthogonality {H : V →L[ℂ] V}
    (hH : IsSelfAdjoint H) (B0 : E →L[ℂ] V) (YQ : E' →L[ℂ] V) (t : ℝ) :
    (B0†) ∘L expH H t ∘L ((1 - cycProj H B0) ∘L YQ) = 0
      ∧ ((cycProj H B0 ∘L YQ)†) ∘L expH H t ∘L ((1 - cycProj H B0) ∘L YQ) = 0 :=
  cyc_short_delay_orthogonality hH B0 YQ t

end QuantumSourceMetric

end QuantumSourceShortSection

/-! ### Shared finite bounded-tilt library

The finite conditioned path card at cutoff `N` is a finite carrier with
strictly positive probability weights; the protected source insertion
(RH.3–RH.4) and the relational source (RS.1–RS.2) are exponential tilts
`e^{ηB}/Z` by bounded reflected writers `B = b + b∘Θ`.  This section
provides the tilt normalizer, tilted weights, normalizer and density
windows, exact pushforward projectivity against every writer, the sourced
reflection-positivity transfer, and the sharp oscillation total-variation
bound `‖P_η − P‖_TV ≤ tanh η` used by the conditioned floors. -/

section TiltThreadSection

namespace TiltThread

variable {Ω : Type*} [Fintype Ω]

/-- The tilt normalizer `Z_η = E[e^{ηB}]` (RH.4/RS.2). -/
noncomputable def zNorm (w B : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ x, w x * Real.exp (η * B x)

/-- The tilted (conditioned) weights `dP_η = e^{ηB}/Z_η dP` (RH.4/RS.2). -/
noncomputable def tilt (w B : Ω → ℝ) (η : ℝ) : Ω → ℝ :=
  fun x => w x * Real.exp (η * B x) / zNorm w B η

/-- Total-variation distance between two finite weight systems. -/
noncomputable def tvDist (v w : Ω → ℝ) : ℝ := (∑ x, |v x - w x|) / 2

variable [Nonempty Ω]

/-- The normalizer is strictly positive. -/
theorem zNorm_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ) (η : ℝ) :
    0 < zNorm w B η :=
  Finset.sum_pos (fun x _ => mul_pos (hw x) (Real.exp_pos _)) Finset.univ_nonempty

/-- The tilted weights are strictly positive. -/
theorem tilt_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ) (η : ℝ) (x : Ω) :
    0 < tilt w B η x :=
  div_pos (mul_pos (hw x) (Real.exp_pos _)) (zNorm_pos hw B η)

/-- The tilted weights are a probability system. -/
theorem tilt_sum_one {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ) (η : ℝ) :
    ∑ x, tilt w B η x = 1 := by
  unfold tilt
  rw [← Finset.sum_div]
  exact div_self (zNorm_pos hw B η).ne'

omit [Nonempty Ω] in
/-- **Normalizer window**: `e^{-cη} ≤ Z_η ≤ e^{cη}` for a writer bounded
by `c` (the `|B| ≤ 2` instance is RH.5/RS.3). -/
theorem zNorm_window {w B : Ω → ℝ} {c η : ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (hB : ∀ x, |B x| ≤ c) (hη : 0 ≤ η) :
    Real.exp (-(c * η)) ≤ zNorm w B η ∧ zNorm w B η ≤ Real.exp (c * η) := by
  constructor
  · calc Real.exp (-(c * η)) = ∑ x, w x * Real.exp (-(c * η)) := by
          rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ zNorm w B η := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw x)
          have := (abs_le.mp (hB x)).1
          nlinarith
  · calc zNorm w B η ≤ ∑ x, w x * Real.exp (c * η) := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw x)
          have := (abs_le.mp (hB x)).2
          nlinarith
    _ = Real.exp (c * η) := by rw [← Finset.sum_mul, hw1, one_mul]

omit [Nonempty Ω] in
/-- **Density window**: `e^{-2cη} ≤ e^{ηB}/Z_η ≤ e^{2cη}` for a writer
bounded by `c` (the `|B| ≤ 2` instance is RH.5/RS.3). -/
theorem density_window {w B : Ω → ℝ} {c η : ℝ} (hw : ∀ x, 0 ≤ w x)
    (hw1 : ∑ x, w x = 1) (hB : ∀ x, |B x| ≤ c) (hη : 0 ≤ η) (x : Ω) :
    Real.exp (-(2 * c * η)) ≤ Real.exp (η * B x) / zNorm w B η
      ∧ Real.exp (η * B x) / zNorm w B η ≤ Real.exp (2 * c * η) := by
  obtain ⟨hZlo, hZhi⟩ := zNorm_window hw hw1 hB hη
  have hZpos : 0 < zNorm w B η := lt_of_lt_of_le (Real.exp_pos _) hZlo
  have hBlo := (abs_le.mp (hB x)).1
  have hBhi := (abs_le.mp (hB x)).2
  constructor
  · rw [le_div_iff₀ hZpos]
    calc Real.exp (-(2 * c * η)) * zNorm w B η
        ≤ Real.exp (-(2 * c * η)) * Real.exp (c * η) :=
          mul_le_mul_of_nonneg_left hZhi (Real.exp_pos _).le
      _ = Real.exp (-(2 * c * η) + c * η) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (η * B x) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
  · rw [div_le_iff₀ hZpos]
    calc Real.exp (η * B x) ≤ Real.exp (c * η) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
      _ = Real.exp (2 * c * η) * Real.exp (-(c * η)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (2 * c * η) * zNorm w B η :=
          mul_le_mul_of_nonneg_left hZlo (Real.exp_pos _).le

variable {Ω' : Type*} [Fintype Ω']

omit [Nonempty Ω] in
/-- **Exact normalizer transport** `Z_{N+1,η} = Z_{N,η}` (RH.6/RS.4): the
tilt normalizer of the exactly pulled-back writer under a projective base
law equals the coarse normalizer. -/
theorem zNorm_pullback {w : Ω → ℝ} {w' : Ω' → ℝ} {π : Ω' → Ω}
    (hpush : ∀ f : Ω → ℝ, ∑ x', w' x' * f (π x') = ∑ x, w x * f x)
    (B : Ω → ℝ) (η : ℝ) :
    zNorm w' (fun x' => B (π x')) η = zNorm w B η :=
  hpush fun x => Real.exp (η * B x)

omit [Nonempty Ω] in
/-- **Exact tilted-law transport** `(π_{N+1/N})_* P_{N+1,η} = P_{N,η}`
(RH.6/RS.4): the tilted fine law integrates every pulled-back writer as the
tilted coarse law. -/
theorem tilt_pullback {w : Ω → ℝ} {w' : Ω' → ℝ} {π : Ω' → Ω}
    (hpush : ∀ f : Ω → ℝ, ∑ x', w' x' * f (π x') = ∑ x, w x * f x)
    (B : Ω → ℝ) (η : ℝ) (f : Ω → ℝ) :
    ∑ x', tilt w' (fun x' => B (π x')) η x' * f (π x')
      = ∑ x, tilt w B η x * f x := by
  unfold tilt
  rw [zNorm_pullback hpush B η]
  have hstep := hpush fun x => Real.exp (η * B x) / zNorm w B η * f x
  calc ∑ x', w' x' * Real.exp (η * B (π x')) / zNorm w B η * f (π x')
      = ∑ x', w' x' * (Real.exp (η * B (π x')) / zNorm w B η * f (π x')) := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        ring
    _ = ∑ x, w x * (Real.exp (η * B x) / zNorm w B η * f x) := hstep
    _ = ∑ x, w x * Real.exp (η * B x) / zNorm w B η * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

omit [Nonempty Ω] in
/-- Bounded-writer perturbation of expectations by total variation:
`|E_v[f] − E_w[f]| ≤ 2c‖v−w‖_TV` for `|f| ≤ c`. -/
theorem abs_expect_sub_le_tv {v w f : Ω → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) :
    |∑ x, v x * f x - ∑ x, w x * f x| ≤ 2 * c * tvDist v w := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ x, (v x * f x - w x * f x)| ≤ ∑ x, |v x * f x - w x * f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |v x - w x| * |f x| := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ ∑ x, |v x - w x| * c := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = 2 * c * tvDist v w := by
        rw [← Finset.sum_mul]
        unfold tvDist
        ring

omit [Nonempty Ω] in
/-- Complex bounded-writer perturbation by total variation:
`‖E_v[F] − E_w[F]‖ ≤ 2c‖v−w‖_TV` for `‖F‖ ≤ c`. -/
theorem norm_expectC_sub_le_tv {v w : Ω → ℝ} {F : Ω → ℂ} {c : ℝ}
    (hF : ∀ x, ‖F x‖ ≤ c) :
    ‖(∑ x, (v x : ℂ) * F x) - ∑ x, (w x : ℂ) * F x‖ ≤ 2 * c * tvDist v w := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ x, ((v x : ℂ) * F x - (w x : ℂ) * F x)‖
      ≤ ∑ x, ‖(v x : ℂ) * F x - (w x : ℂ) * F x‖ := norm_sum_le _ _
    _ = ∑ x, |v x - w x| * ‖F x‖ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← sub_mul, norm_mul]
        congr 1
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ x, |v x - w x| * c := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = 2 * c * tvDist v w := by
        rw [← Finset.sum_mul]
        unfold tvDist
        ring

/-- `tanh` in exponential-square form. -/
theorem tanh_eq_exp_two_mul (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq]
  have h1 : 0 < Real.exp x + Real.exp (-x) := by positivity
  have h2 : 0 < Real.exp (2 * x) + 1 := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne']
  have hxx : Real.exp x * Real.exp x = Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hxm : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- `tanh` is monotone. -/
theorem tanh_le_tanh {x y : ℝ} (hxy : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  by_contra hlt
  push Not at hlt
  have := Real.artanh_lt_artanh (Real.neg_one_lt_tanh y) (Real.tanh_lt_one x) hlt
  rw [Real.artanh_tanh, Real.artanh_tanh] at this
  linarith

/-- **The sharp oscillation total-variation bound** (RH floors): a source
writer with `|B| ≤ 2` tilts the finite path law by at most `tanh η` in
total variation. -/
theorem tilt_tv_le_tanh {w B : Ω → ℝ} {η : ℝ} (hw : ∀ x, 0 < w x)
    (hw1 : ∑ x, w x = 1) (hB : ∀ x, |B x| ≤ 2) (hη : 0 ≤ η) :
    tvDist (tilt w B η) w ≤ Real.tanh η := by
  rcases eq_or_lt_of_le hη with hη0 | hηpos
  · -- at `η = 0` the tilt is the base law
    have hzero : tilt w B 0 = w := by
      funext x
      unfold tilt zNorm
      simp only [zero_mul, Real.exp_zero, mul_one]
      rw [hw1, div_one]
    rw [← hη0, hzero]
    unfold tvDist
    simp [Real.tanh_zero]
  · -- density and window data
    set Z := zNorm w B η with hZdef
    have hZpos : 0 < Z := zNorm_pos hw B η
    set d : Ω → ℝ := fun x => Real.exp (η * B x) / Z with hd
    set a : ℝ := Real.exp (-(2 * η)) / Z with ha
    set b : ℝ := Real.exp (2 * η) / Z with hb
    have hapos : 0 < a := by rw [ha]; positivity
    have hdlo : ∀ x, a ≤ d x := by
      intro x
      rw [ha, hd]
      have hBx := (abs_le.mp (hB x)).1
      have hexp : Real.exp (-(2 * η)) ≤ Real.exp (η * B x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact (div_le_div_iff_of_pos_right hZpos).mpr hexp
    have hdhi : ∀ x, d x ≤ b := by
      intro x
      rw [hb, hd]
      have hBx := (abs_le.mp (hB x)).2
      have hexp : Real.exp (η * B x) ≤ Real.exp (2 * η) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact (div_le_div_iff_of_pos_right hZpos).mpr hexp
    have hmean : ∑ x, w x * d x = 1 := by
      have hterm : ∀ x, w x * d x = tilt w B η x := by
        intro x
        rw [hd]
        unfold tilt
        rw [← hZdef, mul_div_assoc]
      rw [Finset.sum_congr rfl fun x _ => hterm x]
      exact tilt_sum_one hw B η
    have ha1 : a ≤ 1 := by
      have h := Finset.sum_le_sum
        (fun x (_ : x ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hdlo x) (hw x).le)
      rw [← Finset.sum_mul, hw1, one_mul, hmean] at h
      exact h
    have hb1 : 1 ≤ b := by
      have h := Finset.sum_le_sum
        (fun x (_ : x ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hdhi x) (hw x).le)
      rw [← Finset.sum_mul, hw1, one_mul, hmean] at h
      exact h
    set t : ℝ := Real.exp (2 * η) with htdef
    have ht : 1 < t := by
      rw [htdef, show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hab : b = a * t ^ 2 := by
      rw [ha, hb, htdef, sq, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    have hablt : a < b := by
      rw [hab]
      nlinarith
    -- the total variation is the positive-part mass of the density defect
    have htv : tvDist (tilt w B η) w = ∑ x, w x * max (d x - 1) 0 := by
      unfold tvDist
      have h1 : ∀ x, |tilt w B η x - w x| = w x * |d x - 1| := by
        intro x
        have : tilt w B η x - w x = w x * (d x - 1) := by
          unfold tilt
          rw [hd, ← hZdef]
          ring
        rw [this, abs_mul, abs_of_pos (hw x)]
      have h2 : ∀ x, |d x - 1| = 2 * max (d x - 1) 0 - (d x - 1) := by
        intro x
        rcases le_or_gt (d x) 1 with hle | hlt
        · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
          ring
        · rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
          ring
      rw [Finset.sum_congr rfl fun x _ => by rw [h1 x, h2 x]]
      have hsplit : ∑ x, w x * (2 * max (d x - 1) 0 - (d x - 1))
          = 2 * (∑ x, w x * max (d x - 1) 0) - ((∑ x, w x * d x) - ∑ x, w x) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [hsplit, hmean, hw1]
      ring
    -- pointwise chord bound above the hinge
    have hchord : ∀ x, (b - a) * max (d x - 1) 0 ≤ (b - 1) * (d x - a) := by
      intro x
      rcases le_or_gt (d x) 1 with hle | hlt
      · rw [max_eq_right (by linarith)]
        have := hdlo x
        nlinarith
      · rw [max_eq_left (by linarith)]
        have h1 := hdhi x
        nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr (hdhi x))]
    -- summed chord bound
    have hsum : (b - a) * tvDist (tilt w B η) w ≤ (b - 1) * (1 - a) := by
      rw [htv, Finset.mul_sum]
      have h := Finset.sum_le_sum
        (fun x (_ : x ∈ Finset.univ) =>
          mul_le_mul_of_nonneg_left (hchord x) (hw x).le)
      calc ∑ x, (b - a) * (w x * max (d x - 1) 0)
          = ∑ x, w x * ((b - a) * max (d x - 1) 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
        _ ≤ ∑ x, w x * ((b - 1) * (d x - a)) := h
        _ = (b - 1) * ((∑ x, w x * d x) - a * ∑ x, w x) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              ring
        _ = (b - 1) * (1 - a) := by rw [hmean, hw1, mul_one]
    -- the sharp constant
    have htanh : Real.tanh η = (t - 1) / (t + 1) := by
      rw [tanh_eq_exp_two_mul, htdef]
    have hkey : (b - 1) * (1 - a) * (t + 1) ≤ (t - 1) * (b - a) := by
      rw [hab]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t + 1) (sq_nonneg (a * t - 1))]
    rw [htanh, le_div_iff₀ (by linarith : (0 : ℝ) < t + 1)]
    have hchain : tvDist (tilt w B η) w * (t + 1) * (b - a)
        ≤ (t - 1) * (b - a) := by
      calc tvDist (tilt w B η) w * (t + 1) * (b - a)
          = ((b - a) * tvDist (tilt w B η) w) * (t + 1) := by ring
        _ ≤ (b - 1) * (1 - a) * (t + 1) := by
            have := hsum
            nlinarith
        _ ≤ (t - 1) * (b - a) := hkey
    have hba : (0 : ℝ) < b - a := by linarith
    exact le_of_mul_le_mul_right hchain hba

omit [Nonempty Ω] in
/-- At `η = 0` the tilt is the base law. -/
theorem tilt_zero {w : Ω → ℝ} (hw1 : ∑ x, w x = 1) (B : Ω → ℝ) :
    tilt w B 0 = w := by
  funext x
  unfold tilt zNorm
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [hw1, div_one]

/-- **Sourced reflection positivity**: the tilted reflected Gram of every
positive-time writer is nonnegative, because
`e^{ηB}Θ(F̄)F = conj((e^{ηb}F)∘Θ)·(e^{ηb}F)` for the reflected source
`B = b + b∘Θ` and the base reflected form is positive on the tilted
positive-time writer `e^{ηb}F`. -/
theorem tilt_reflection_positive {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (Θ : Ω → Ω) (b : Ω → ℝ) (η : ℝ) (PT : (Ω → ℂ) → Prop)
    (hRP : ∀ F, PT F →
      0 ≤ (∑ x, (w x : ℂ) * ((starRingEnd ℂ) (F (Θ x)) * F x)).re)
    (hclosed : ∀ F, PT F → PT fun x => (Real.exp (η * b x) : ℂ) * F x)
    (F : Ω → ℂ) (hF : PT F) :
    0 ≤ (∑ x, ((tilt w (fun y => b y + b (Θ y)) η x : ℝ) : ℂ)
        * ((starRingEnd ℂ) (F (Θ x)) * F x)).re := by
  have hbase := hRP (fun x => (Real.exp (η * b x) : ℂ) * F x) (hclosed F hF)
  have hZpos : 0 < zNorm w (fun y => b y + b (Θ y)) η := zNorm_pos hw _ η
  have hterm : ∀ x, ((tilt w (fun y => b y + b (Θ y)) η x : ℝ) : ℂ)
      * ((starRingEnd ℂ) (F (Θ x)) * F x)
      = (((zNorm w (fun y => b y + b (Θ y)) η)⁻¹ : ℝ) : ℂ)
        * ((w x : ℂ)
          * ((starRingEnd ℂ) ((Real.exp (η * b (Θ x)) : ℂ) * F (Θ x))
            * ((Real.exp (η * b x) : ℂ) * F x))) := by
    intro x
    unfold tilt
    have hsplit : Real.exp (η * (b x + b (Θ x)))
        = Real.exp (η * b x) * Real.exp (η * b (Θ x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [map_mul, Complex.conj_ofReal]
    push_cast [hsplit]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum,
    Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) hbase

end TiltThread

end TiltThreadSection

/-! ### `thm:RPESM-H4-conditioned-thread`

Rendering (RH.3–RH.6): the finite path card at cutoff `N` is a finite
carrier with strictly positive probability weights `w`; the level-zero
Higgs-norm writer `W⋆ = exp(i‖H‖⁴/256)` is rendered as an arbitrary
unit-modulus writer `Wr` (only unit modulus enters), the two-sided
reflection is a carrier map `Θ`, and the protected insertion is
`B⋆ = Re Wr + (Re Wr)∘Θ` (`bStar`).  The adjacent cutoff is any finite
carrier `Ω'` with a projection `π` pushing its base law to the coarse law
against every writer, with `Wr` pulled back exactly and `Θ` intertwined.
The bundle proves `|B⋆| ≤ 2`, the normalizer window `e^{-2η} ≤ Z ≤ e^{2η}`,
the density window `e^{-4η} ≤ dP_η/dP ≤ e^{4η}` (RH.5), the exact writer
pullback, `Z_{N+1,η} = Z_{N,η}`, the exact tilted-law pushforward (RH.6),
the identically-one adjacent exponential source cocycle (hence zero
source-cocycle and cofinal debit), and the `N`-independent normalized
density.  The master clause is proved on a projective-tower interface: a
master carrier with compatible projections and a base master expectation
having the `w N` as marginals carries one bounded mean-one `N`-independent
density whose conditioned expectations have all the tilted finite-cutoff
laws as marginals.  Reflection positivity of every conditioned reflected
Gram is `protected_source_reflection_positive`. -/

section H4ConditionedThreadSection

namespace H4Thread

open TiltThread

variable {Ω : Type*} [Fintype Ω]

/-- The protected reflected source insertion `B⋆ = b⋆ + Θb⋆` (RH.3), with
`b⋆ = Re W⋆` the real part of the unit-modulus protected writer. -/
noncomputable def bStar (Wr : Ω → ℂ) (Θ : Ω → Ω) : Ω → ℝ :=
  fun x => (Wr x).re + (Wr (Θ x)).re

omit [Fintype Ω] in
/-- The protected source is bounded by two (RH.5). -/
theorem abs_bStar_le_two {Wr : Ω → ℂ} (hWr : ∀ x, ‖Wr x‖ = 1) (Θ : Ω → Ω)
    (x : Ω) : |bStar Wr Θ x| ≤ 2 := by
  have h1 : |(Wr x).re| ≤ 1 := by
    calc |(Wr x).re| ≤ ‖Wr x‖ := Complex.abs_re_le_norm _
      _ = 1 := hWr x
  have h2 : |(Wr (Θ x)).re| ≤ 1 := by
    calc |(Wr (Θ x)).re| ≤ ‖Wr (Θ x)‖ := Complex.abs_re_le_norm _
      _ = 1 := hWr (Θ x)
  calc |bStar Wr Θ x| ≤ |(Wr x).re| + |(Wr (Θ x)).re| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- **`thm:RPESM-H4-conditioned-thread`, adjacent clauses (RH.5–RH.6)**:
the protected-source bound, the normalizer and density windows, the exact
writer pullback, normalizer equality, tilted-law pushforward, the
identically-one adjacent exponential source cocycle (zero source-cocycle
debit), and the `N`-independent normalized conditioned density. -/
theorem protected_source_thread
    {Ω' : Type*} [Fintype Ω']
    (w : Ω → ℝ) (w' : Ω' → ℝ) (π : Ω' → Ω) (Θ : Ω → Ω) (Θ' : Ω' → Ω')
    (Wr : Ω → ℂ) (Wr' : Ω' → ℂ) (η : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hWr : ∀ x, ‖Wr x‖ = 1)
    (hpush : ∀ f : Ω → ℝ, ∑ x', w' x' * f (π x') = ∑ x, w x * f x)
    (hWpull : ∀ x', Wr' x' = Wr (π x'))
    (hΘcomm : ∀ x', π (Θ' x') = Θ (π x'))
    (hη : 0 ≤ η) :
    (∀ x, |bStar Wr Θ x| ≤ 2)
    ∧ (Real.exp (-(2 * η)) ≤ zNorm w (bStar Wr Θ) η
        ∧ zNorm w (bStar Wr Θ) η ≤ Real.exp (2 * η))
    ∧ (∀ x, Real.exp (-(4 * η))
          ≤ Real.exp (η * bStar Wr Θ x) / zNorm w (bStar Wr Θ) η
        ∧ Real.exp (η * bStar Wr Θ x) / zNorm w (bStar Wr Θ) η
          ≤ Real.exp (4 * η))
    ∧ (∀ x', bStar Wr' Θ' x' = bStar Wr Θ (π x'))
    ∧ zNorm w' (bStar Wr' Θ') η = zNorm w (bStar Wr Θ) η
    ∧ (∀ f : Ω → ℝ, ∑ x', tilt w' (bStar Wr' Θ') η x' * f (π x')
        = ∑ x, tilt w (bStar Wr Θ) η x * f x)
    ∧ (∀ x', Real.exp (η * bStar Wr' Θ' x')
        / Real.exp (η * bStar Wr Θ (π x')) = 1)
    ∧ (∀ x', Real.exp (η * bStar Wr' Θ' x') / zNorm w' (bStar Wr' Θ') η
        = Real.exp (η * bStar Wr Θ (π x')) / zNorm w (bStar Wr Θ) η) := by
  have hb2 : ∀ x, |bStar Wr Θ x| ≤ 2 := abs_bStar_le_two hWr Θ
  have hBpull : ∀ x', bStar Wr' Θ' x' = bStar Wr Θ (π x') := by
    intro x'
    unfold bStar
    rw [hWpull x', hWpull (Θ' x'), hΘcomm x']
  have hBfun : bStar Wr' Θ' = fun x' => bStar Wr Θ (π x') := funext hBpull
  have hZeq : zNorm w' (bStar Wr' Θ') η = zNorm w (bStar Wr Θ) η := by
    rw [hBfun]
    exact zNorm_pullback hpush _ η
  have h4 : (2 : ℝ) * 2 * η = 4 * η := by ring
  refine ⟨hb2, zNorm_window hw hw1 hb2 hη, fun x => ?_, hBpull, hZeq,
    fun f => ?_, fun x' => ?_, fun x' => ?_⟩
  · have := density_window hw hw1 hb2 hη x
    rwa [h4] at this
  · rw [hBfun]
    exact tilt_pullback hpush _ η f
  · rw [hBpull x']
    exact div_self (Real.exp_pos _).ne'
  · rw [hBpull x', hZeq]

/-- **`thm:RPESM-H4-conditioned-thread`, master clauses (RH.6)**: along
the projective tower with exactly pulled-back protected sources, the
conditioned density pulled to the master path is one bounded function
independent of `N`, it has mean one under the base master law, and the
conditioned master expectations have the conditioned finite laws
`P_{N,η}` as all finite-cutoff marginals. -/
theorem protected_source_master
    {Ω : ℕ → Type*} [∀ N, Fintype (Ω N)]
    (w : ∀ N, Ω N → ℝ) (π : ∀ N, Ω (N + 1) → Ω N) (B : ∀ N, Ω N → ℝ)
    {M : Type*} (ρ : ∀ N, M → Ω N) (Einf : (M → ℝ) → ℝ) (η : ℝ)
    (hw : ∀ x, 0 ≤ w 0 x) (hw1 : ∑ x, w 0 x = 1)
    (hpush : ∀ N (f : Ω N → ℝ),
      ∑ x', w (N + 1) x' * f (π N x') = ∑ x, w N x * f x)
    (hB : ∀ N x', B (N + 1) x' = B N (π N x'))
    (hBb : ∀ x, |B 0 x| ≤ 2)
    (hρ : ∀ N m, ρ N m = π N (ρ (N + 1) m))
    (hmarg : ∀ N (f : Ω N → ℝ), Einf (fun m => f (ρ N m)) = ∑ x, w N x * f x)
    (hη : 0 ≤ η) :
    (∀ N m, Real.exp (η * B N (ρ N m)) / zNorm (w N) (B N) η
        = Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η)
    ∧ (∀ m, Real.exp (-(4 * η))
          ≤ Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η
        ∧ Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η
          ≤ Real.exp (4 * η))
    ∧ Einf (fun m => Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η) = 1
    ∧ ∀ N (f : Ω N → ℝ),
        Einf (fun m =>
            Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η * f (ρ N m))
          = ∑ x, tilt (w N) (B N) η x * f x := by
  have hBcomp : ∀ N m, B N (ρ N m) = B 0 (ρ 0 m) := by
    intro N
    induction N with
    | zero => intro m; rfl
    | succ N ih =>
        intro m
        rw [hB N (ρ (N + 1) m), ← hρ N m]
        exact ih m
  have hZeq : ∀ N, zNorm (w N) (B N) η = zNorm (w 0) (B 0) η := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih =>
        rw [← ih]
        have hBfun : B (N + 1) = fun x' => B N (π N x') := funext (hB N)
        rw [hBfun]
        exact zNorm_pullback (hpush N) _ η
  have hZ0pos : 0 < zNorm (w 0) (B 0) η :=
    lt_of_lt_of_le (Real.exp_pos _) (zNorm_window hw hw1 hBb hη).1
  refine ⟨fun N m => by rw [hBcomp N m, hZeq N], fun m => ?_, ?_, ?_⟩
  · have := density_window hw hw1 hBb hη (ρ 0 m)
    rwa [show (2 : ℝ) * 2 * η = 4 * η by ring] at this
  · have h := hmarg 0 fun x => Real.exp (η * B 0 x) / zNorm (w 0) (B 0) η
    have hsum : ∑ x, w 0 x * (Real.exp (η * B 0 x) / zNorm (w 0) (B 0) η)
        = 1 := by
      calc ∑ x, w 0 x * (Real.exp (η * B 0 x) / zNorm (w 0) (B 0) η)
          = (∑ x, w 0 x * Real.exp (η * B 0 x)) / zNorm (w 0) (B 0) η := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = 1 := div_self hZ0pos.ne'
    exact h.trans hsum
  · intro N f
    have hfun : (fun m =>
          Real.exp (η * B 0 (ρ 0 m)) / zNorm (w 0) (B 0) η * f (ρ N m))
        = fun m => (fun x =>
            Real.exp (η * B N x) / zNorm (w N) (B N) η * f x) (ρ N m) := by
      funext m
      rw [← hBcomp N m, hZeq N]
    rw [hfun,
      hmarg N fun x => Real.exp (η * B N x) / zNorm (w N) (B N) η * f x]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold tilt
    ring

/-- **`thm:RPESM-H4-conditioned-thread`, reflection clause**: every
conditioned reflected Gram of a positive-time writer remains nonnegative
under the protected-source tilt. -/
theorem protected_source_reflection_positive {w : Ω → ℝ} [Nonempty Ω]
    (hw : ∀ x, 0 < w x) (Θ : Ω → Ω) (Wr : Ω → ℂ) (η : ℝ)
    (PT : (Ω → ℂ) → Prop)
    (hRP : ∀ F, PT F →
      0 ≤ (∑ x, (w x : ℂ) * ((starRingEnd ℂ) (F (Θ x)) * F x)).re)
    (hclosed : ∀ F, PT F →
      PT fun x => (Real.exp (η * (Wr x).re) : ℂ) * F x)
    (F : Ω → ℂ) (hF : PT F) :
    0 ≤ (∑ x, ((tilt w (bStar Wr Θ) η x : ℝ) : ℂ)
        * ((starRingEnd ℂ) (F (Θ x)) * F x)).re :=
  tilt_reflection_positive hw Θ (fun x => (Wr x).re) η PT hRP hclosed F hF

end H4Thread

end H4ConditionedThreadSection

/-! ### `thm:RPESM-H4-source-floors`

Rendering (RH.7–RH.8): the evaluated-card constants are
`a⋆ = 89/483840` and `Γ̲⋆ = e^{-a⋆}/65537` (RH.2, an upstream display of
the evaluated finite card, entering here through the base-value
hypotheses), and the safe window is `η⋆^safe = arctanh(e^{-2}Γ̲⋆/16) > 0`
(RH.7).  The conditioned static source variance is the genuine tilted
variance `Γ⋆,η = Var_{P_η}(W⋆)` of the unit-modulus protected writer; the
positive-time norm and separation-two reflected Gram are conditioned
expectations of modulus-≤4 writers whose base values dominate `Γ⋆`
(positive-time norm) resp. equal `e^{-2}Γ⋆` (the selected global-refresh
branch), exactly as in the manuscript proof.  The floors (RH.8) follow
from the sharp oscillation bound `‖P_η − P‖_TV ≤ tanh η`
(`TiltThread.tilt_tv_le_tanh`).  Uniformity in `N` is by quantification:
the statement holds for every finite conditioned card with the same
explicit constants, and the conditioned data transport exactly by
`thm:RPESM-H4-conditioned-thread`. -/

section H4SourceFloorsSection

namespace H4Floors

open TiltThread

/-- The evaluated-card exponent `a⋆ = 89/483840` (RH.2). -/
noncomputable def aStar : ℝ := 89 / 483840

/-- The evaluated-card static variance floor `Γ̲⋆ = e^{-a⋆}/65537`
(RH.2). -/
noncomputable def gammaLow : ℝ := Real.exp (-aStar) / 65537

/-- **(RH.7)**: the safe source window
`η⋆^safe = arctanh(e^{-2}Γ̲⋆/16)`. -/
noncomputable def etaSafe : ℝ := Real.artanh (Real.exp (-2) * gammaLow / 16)

/-- The variance floor is positive. -/
theorem gammaLow_pos : 0 < gammaLow := by
  unfold gammaLow
  positivity

/-- The variance floor is below one. -/
theorem gammaLow_lt_one : gammaLow < 1 := by
  unfold gammaLow
  have h1 : Real.exp (-aStar) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    refine Real.exp_le_exp.mpr ?_
    unfold aStar
    norm_num
  nlinarith [Real.exp_pos (-aStar)]

/-- The threshold argument lies in the open unit interval. -/
theorem etaSafe_arg_mem :
    Real.exp (-2) * gammaLow / 16 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · have := gammaLow_pos
    positivity
  · have h1 : Real.exp (-2 : ℝ) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by norm_num)
    have h2 := gammaLow_lt_one
    have h3 := gammaLow_pos
    nlinarith [Real.exp_pos (-2 : ℝ)]

/-- **(RH.7)**: the safe window is strictly positive. -/
theorem etaSafe_pos : 0 < etaSafe :=
  Real.artanh_pos etaSafe_arg_mem

/-- Inside the safe window the sharp oscillation constant is at most
`e^{-2}Γ̲⋆/16`. -/
theorem tanh_le_of_le_etaSafe {η : ℝ} (hη : η ≤ etaSafe) :
    Real.tanh η ≤ Real.exp (-2) * gammaLow / 16 := by
  calc Real.tanh η ≤ Real.tanh etaSafe := tanh_le_tanh hη
    _ = Real.exp (-2) * gammaLow / 16 := by
        unfold etaSafe
        exact Real.tanh_artanh
          ⟨by linarith [etaSafe_arg_mem.1], etaSafe_arg_mem.2⟩

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The variance of a complex writer under a finite weight system. -/
noncomputable def cvar (v : Ω → ℝ) (W : Ω → ℂ) : ℝ :=
  (∑ x, v x * ‖W x‖ ^ 2) - ‖∑ x, (v x : ℂ) * W x‖ ^ 2

omit [Nonempty Ω] in
/-- For a unit-modulus writer under a probability system the variance is
`1 − ‖mean‖²`. -/
theorem cvar_eq_one_sub {v : Ω → ℝ} {W : Ω → ℂ} (hv1 : ∑ x, v x = 1)
    (hW : ∀ x, ‖W x‖ = 1) :
    cvar v W = 1 - ‖∑ x, (v x : ℂ) * W x‖ ^ 2 := by
  unfold cvar
  congr 1
  calc ∑ x, v x * ‖W x‖ ^ 2 = ∑ x, v x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hW x]
        ring
    _ = 1 := hv1

omit [Nonempty Ω] in
/-- The mean of a unit-modulus writer under a nonnegative probability
system has norm at most one. -/
theorem norm_mean_le_one {v : Ω → ℝ} {W : Ω → ℂ} (hv : ∀ x, 0 ≤ v x)
    (hv1 : ∑ x, v x = 1) (hW : ∀ x, ‖W x‖ = 1) :
    ‖∑ x, (v x : ℂ) * W x‖ ≤ 1 := by
  calc ‖∑ x, (v x : ℂ) * W x‖ ≤ ∑ x, ‖(v x : ℂ) * W x‖ := norm_sum_le _ _
    _ = ∑ x, v x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, hW x, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hv x)]
    _ = 1 := hv1

/-- **`thm:RPESM-H4-source-floors` (RH.7–RH.8)**: in the safe window
`0 ≤ η ≤ η⋆^safe`, the conditioned static source variance, positive-time
norm, and separation-two reflected Gram of the protected source satisfy
the explicit floors `Γ⋆,η ≥ (3/4)Γ̲⋆`, `n⋆,η ≥ (1/2)Γ̲⋆`,
`q⋆,η ≥ (1/2)e^{-2}Γ̲⋆ > 0`, with all constants independent of the
cutoff. -/
theorem conditioned_source_floors
    (w : Ω → ℝ) (W : Ω → ℂ) (Gn Gq B : Ω → ℝ) (η : ℝ)
    (hw : ∀ x, 0 < w x) (hw1 : ∑ x, w x = 1) (hW : ∀ x, ‖W x‖ = 1)
    (hB : ∀ x, |B x| ≤ 2)
    (hGn : ∀ x, |Gn x| ≤ 4) (hGq : ∀ x, |Gq x| ≤ 4)
    (hΓ : gammaLow ≤ cvar w W)
    (hn : cvar w W ≤ ∑ x, w x * Gn x)
    (hq : ∑ x, w x * Gq x = Real.exp (-2) * cvar w W)
    (hη0 : 0 ≤ η) (hηs : η ≤ etaSafe) :
    0 < etaSafe
    ∧ 3 / 4 * gammaLow ≤ cvar (tilt w B η) W
    ∧ 1 / 2 * gammaLow ≤ ∑ x, tilt w B η x * Gn x
    ∧ 1 / 2 * Real.exp (-2) * gammaLow ≤ ∑ x, tilt w B η x * Gq x
    ∧ 0 < 1 / 2 * Real.exp (-2) * gammaLow := by
  have hδtv := tilt_tv_le_tanh hw hw1 hB hη0
  have hδsafe := tanh_le_of_le_etaSafe hηs
  have hδnn : 0 ≤ Real.tanh η := by
    rw [show (0 : ℝ) = Real.tanh 0 by rw [Real.tanh_zero]]
    exact tanh_le_tanh hη0
  have htw : ∀ x, 0 ≤ tilt w B η x := fun x => (tilt_pos hw B η x).le
  have htw1 : ∑ x, tilt w B η x = 1 := tilt_sum_one hw B η
  have hexp2 : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
  have hexp2le : Real.exp (-2 : ℝ) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hγ := gammaLow_pos
  -- variance floor
  have hΓfloor : cvar w W - 4 * Real.tanh η ≤ cvar (tilt w B η) W := by
    have hmw := norm_mean_le_one (fun x => (hw x).le) hw1 hW
    have hmt := norm_mean_le_one htw htw1 hW
    have hdiff : ‖(∑ x, ((tilt w B η x : ℝ) : ℂ) * W x)
        - ∑ x, (w x : ℂ) * W x‖ ≤ 2 * Real.tanh η := by
      calc ‖(∑ x, ((tilt w B η x : ℝ) : ℂ) * W x) - ∑ x, (w x : ℂ) * W x‖
          ≤ 2 * 1 * tvDist (tilt w B η) w :=
            norm_expectC_sub_le_tv fun x => le_of_eq (hW x)
        _ ≤ 2 * Real.tanh η := by nlinarith
    have hnorm : ‖∑ x, ((tilt w B η x : ℝ) : ℂ) * W x‖
        - ‖∑ x, (w x : ℂ) * W x‖ ≤ 2 * Real.tanh η := by
      have h1 := norm_sub_norm_le (∑ x, ((tilt w B η x : ℝ) : ℂ) * W x)
        (∑ x, (w x : ℂ) * W x)
      linarith
    rw [cvar_eq_one_sub hw1 hW, cvar_eq_one_sub htw1 hW]
    have hmwnn : 0 ≤ ‖∑ x, (w x : ℂ) * W x‖ := norm_nonneg _
    have hmtnn : 0 ≤ ‖∑ x, ((tilt w B η x : ℝ) : ℂ) * W x‖ := norm_nonneg _
    have hkey : ‖∑ x, ((tilt w B η x : ℝ) : ℂ) * W x‖ ^ 2
        - ‖∑ x, (w x : ℂ) * W x‖ ^ 2 ≤ 4 * Real.tanh η := by
      rcases le_or_gt ‖∑ x, ((tilt w B η x : ℝ) : ℂ) * W x‖
          ‖∑ x, (w x : ℂ) * W x‖ with hle | hgt
      · nlinarith [mul_le_mul hle hle hmtnn (hmtnn.trans hle)]
      · nlinarith [mul_le_mul hnorm
          (show ‖∑ x, ((tilt w B η x : ℝ) : ℂ) * W x‖
              + ‖∑ x, (w x : ℂ) * W x‖ ≤ 2 by linarith)
          (by linarith) (by linarith)]
    linarith
  -- positive-time and reflected floors
  have hnfloor : (∑ x, w x * Gn x) - 8 * Real.tanh η
      ≤ ∑ x, tilt w B η x * Gn x := by
    have h1 := abs_expect_sub_le_tv (v := tilt w B η) (w := w) (f := Gn) hGn
    have habs := abs_le.mp h1
    nlinarith [habs.1]
  have hqfloor : (∑ x, w x * Gq x) - 8 * Real.tanh η
      ≤ ∑ x, tilt w B η x * Gq x := by
    have h1 := abs_expect_sub_le_tv (v := tilt w B η) (w := w) (f := Gq) hGq
    have habs := abs_le.mp h1
    nlinarith [habs.1]
  refine ⟨etaSafe_pos, ?_, ?_, ?_, by positivity⟩
  · nlinarith
  · nlinarith
  · have hcv : cvar w W ≤ 1 := by
      rw [cvar_eq_one_sub hw1 hW]
      nlinarith [sq_nonneg ‖∑ x, (w x : ℂ) * W x‖]
    nlinarith

end H4Floors

end H4SourceFloorsSection

/-! ### `prop:RPESM-H4-action-no-reprice`

Rendering (RH.9): the intrinsic source action is the exact finite
relative entropy `𝒜⋆(η) = D_KL(P_{N,η}⋆‖P_N^path)` of the conditioned
finite path card.  We prove: the closed form
`𝒜⋆(η) = η ∂_η log Z_η − log Z_η` with `∂_η log Z_η` certified as the
actual derivative (`hasDerivAt_log_zNorm`); the actual derivative
`𝒜⋆'(η) = η·Var_{P_η}(B⋆) ≥ 0` (`source_action_hasDerivAt`); strict
positivity for `η > 0` under source nonconstancy
(`source_action_pos`); exact independence of the cutoff under the
projective pullback of `thm:RPESM-H4-conditioned-thread`
(`source_action_pullback`, the zero adjacent transport novelty); and the
repeated-counting identity for the cutoff sum
(`summing_recounts_source`). -/

section H4ActionSection

namespace H4Action

open TiltThread

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The intrinsic source action
`𝒜⋆(η) = D_KL(P_{N,η}⋆ ‖ P_N^path)` (RH.9). -/
noncomputable def sourceAction (w B : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ x, tilt w B η x * Real.log (tilt w B η x / w x)

/-- The conditioned source mean `E_{P_η}[B⋆]`. -/
noncomputable def tiltMean (w B : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ x, tilt w B η x * B x

/-- The conditioned source variance `Var_{P_η}(B⋆)`. -/
noncomputable def tiltVar (w B : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ x, tilt w B η x * (B x - tiltMean w B η) ^ 2

omit [Nonempty Ω] in
/-- The conditioned mean in normalizer-quotient form. -/
theorem tiltMean_eq (w B : Ω → ℝ) (η : ℝ) :
    tiltMean w B η
      = (∑ x, w x * B x * Real.exp (η * B x)) / zNorm w B η := by
  unfold tiltMean tilt
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Nonempty Ω] in
/-- The normalizer has the conditioned unnormalized mean as its actual
derivative. -/
theorem hasDerivAt_zNorm (w B : Ω → ℝ) (η : ℝ) :
    HasDerivAt (fun t => zNorm w B t)
      (∑ x, w x * B x * Real.exp (η * B x)) η := by
  refine HasDerivAt.fun_sum fun x _ => ?_
  have h1 := ((hasDerivAt_mul_const (B x)).exp.const_mul (w x) :
    HasDerivAt (fun t : ℝ => w x * Real.exp (t * B x))
      (w x * (Real.exp (η * B x) * B x)) η)
  rw [show w x * B x * Real.exp (η * B x)
      = w x * (Real.exp (η * B x) * B x) from by ring]
  exact h1

omit [Nonempty Ω] in
/-- The unnormalized conditioned mean has the unnormalized second moment
as its actual derivative. -/
theorem hasDerivAt_zMean (w B : Ω → ℝ) (η : ℝ) :
    HasDerivAt (fun t => ∑ x, w x * B x * Real.exp (t * B x))
      (∑ x, w x * B x ^ 2 * Real.exp (η * B x)) η := by
  refine HasDerivAt.fun_sum fun x _ => ?_
  have h1 := ((hasDerivAt_mul_const (B x)).exp.const_mul (w x * B x) :
    HasDerivAt (fun t : ℝ => w x * B x * Real.exp (t * B x))
      (w x * B x * (Real.exp (η * B x) * B x)) η)
  rw [show w x * B x ^ 2 * Real.exp (η * B x)
      = w x * B x * (Real.exp (η * B x) * B x) from by ring]
  exact h1

/-- `log Z_η` has the conditioned source mean as its actual derivative:
`∂_η log Z_η = E_{P_η}[B⋆]`. -/
theorem hasDerivAt_log_zNorm {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ)
    (η : ℝ) :
    HasDerivAt (fun t => Real.log (zNorm w B t)) (tiltMean w B η) η := by
  have hZpos := zNorm_pos hw B η
  have h := (hasDerivAt_zNorm w B η).log hZpos.ne'
  rwa [← tiltMean_eq] at h

/-- **(RH.9, closed form)**: the intrinsic source action is
`𝒜⋆(η) = η ∂_η log Z_η − log Z_η` with the conditioned mean as the
derivative of `log Z`. -/
theorem source_action_eq {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ)
    (η : ℝ) :
    sourceAction w B η = η * tiltMean w B η - Real.log (zNorm w B η) := by
  have hZpos := zNorm_pos hw B η
  have hterm : ∀ x, tilt w B η x * Real.log (tilt w B η x / w x)
      = η * (tilt w B η x * B x)
        - Real.log (zNorm w B η) * tilt w B η x := by
    intro x
    have hwx : w x ≠ 0 := (hw x).ne'
    have hratio : tilt w B η x / w x = Real.exp (η * B x) / zNorm w B η := by
      unfold tilt
      field_simp
    rw [hratio, Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
    ring
  unfold sourceAction
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, tilt_sum_one hw B η, mul_one]
  rfl

/-- The conditioned variance in second-moment form. -/
theorem tiltVar_eq {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ) (η : ℝ) :
    tiltVar w B η
      = (∑ x, w x * B x ^ 2 * Real.exp (η * B x)) / zNorm w B η
        - tiltMean w B η ^ 2 := by
  have hterm : ∀ x, tilt w B η x * (B x - tiltMean w B η) ^ 2
      = tilt w B η x * B x ^ 2
        - 2 * tiltMean w B η * (tilt w B η x * B x)
        + tiltMean w B η ^ 2 * tilt w B η x := by
    intro x
    ring
  unfold tiltVar
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    tilt_sum_one hw B η, mul_one]
  have hmom : ∑ x, tilt w B η x * B x ^ 2
      = (∑ x, w x * B x ^ 2 * Real.exp (η * B x)) / zNorm w B η := by
    unfold tilt
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hmom]
  unfold tiltMean
  ring

/-- The conditioned variance is nonnegative. -/
theorem tiltVar_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (B : Ω → ℝ)
    (η : ℝ) : 0 ≤ tiltVar w B η :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (tilt_pos hw B η x).le (sq_nonneg _)

/-- Source nonconstancy makes the conditioned variance strictly
positive at every tilt. -/
theorem tiltVar_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {B : Ω → ℝ}
    (hnc : ∃ x y, B x ≠ B y) (η : ℝ) : 0 < tiltVar w B η := by
  obtain ⟨x, y, hxy⟩ := hnc
  have hone : B x ≠ tiltMean w B η ∨ B y ≠ tiltMean w B η := by
    by_contra hcon
    push Not at hcon
    exact hxy (hcon.1.trans hcon.2.symm)
  have hwit : ∃ z, B z ≠ tiltMean w B η := by
    rcases hone with h | h
    · exact ⟨x, h⟩
    · exact ⟨y, h⟩
  obtain ⟨z, hz⟩ := hwit
  refine Finset.sum_pos' (fun u _ =>
    mul_nonneg (tilt_pos hw B η u).le (sq_nonneg _)) ⟨z, Finset.mem_univ z, ?_⟩
  exact mul_pos (tilt_pos hw B η z)
    (by positivity)

/-- **(RH.9, derivative)**: the intrinsic source action has the actual
derivative `𝒜⋆'(η) = η · Var_{P_η}(B⋆)`, nonnegative for `η ≥ 0`. -/
theorem source_action_hasDerivAt {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (B : Ω → ℝ) (η : ℝ) :
    HasDerivAt (fun t => sourceAction w B t) (η * tiltVar w B η) η := by
  have hZpos := zNorm_pos hw B η
  have hfun : (fun t => sourceAction w B t)
      = fun t => t * ((∑ x, w x * B x * Real.exp (t * B x)) / zNorm w B t)
          - Real.log (zNorm w B t) := by
    funext t
    rw [source_action_eq hw B t, tiltMean_eq]
  have hZ := hasDerivAt_zNorm w B η
  have hZd := hasDerivAt_zMean w B η
  have hdiv := hZd.div hZ hZpos.ne'
  have hmul := (hasDerivAt_id η).mul hdiv
  have hlog := hZ.log hZpos.ne'
  have htotal := hmul.sub hlog
  have hval : 1 * ((∑ x, w x * B x * Real.exp (η * B x)) / zNorm w B η)
        + η * (((∑ x, w x * B x ^ 2 * Real.exp (η * B x)) * zNorm w B η
            - (∑ x, w x * B x * Real.exp (η * B x))
              * ∑ x, w x * B x * Real.exp (η * B x))
          / zNorm w B η ^ 2)
        - (∑ x, w x * B x * Real.exp (η * B x)) / zNorm w B η
      = η * tiltVar w B η := by
    rw [tiltVar_eq hw B η, tiltMean_eq]
    set Z := zNorm w B η with hZ0
    set S1 := ∑ x, w x * B x * Real.exp (η * B x) with hS1
    set S2 := ∑ x, w x * B x ^ 2 * Real.exp (η * B x) with hS2
    field_simp
    ring
  rw [hfun, ← hval]
  refine HasDerivAt.congr_of_eventuallyEq htotal
    (Filter.Eventually.of_forall fun t => ?_)
  rfl

omit [Nonempty Ω] in
/-- The intrinsic action vanishes at zero source. -/
theorem source_action_zero {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (hw1 : ∑ x, w x = 1) (B : Ω → ℝ) : sourceAction w B 0 = 0 := by
  unfold sourceAction
  rw [tilt_zero hw1]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [div_self (hw x).ne', Real.log_one, mul_zero]

/-- **(RH.9, strict positivity)**: the intrinsic source action is
strictly positive at every positive source strength for a nonconstant
source. -/
theorem source_action_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x)
    (hw1 : ∑ x, w x = 1) {B : Ω → ℝ} (hnc : ∃ x y, B x ≠ B y) {η : ℝ}
    (hη : 0 < η) : 0 < sourceAction w B η := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s => sourceAction w B s)
      (t * tiltVar w B t) t := fun t => source_action_hasDerivAt hw B t
  have hmono : StrictMonoOn (fun t => sourceAction w B t)
      (Set.Icc 0 η) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 η) ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t =>
        (hd t).continuousAt).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      exact mul_pos ht.1 (tiltVar_pos hw hnc t)
  have := hmono (Set.left_mem_Icc.mpr hη.le)
    (Set.right_mem_Icc.mpr hη.le) hη
  have h0 := source_action_zero hw hw1 B
  simpa [h0] using this

variable {Ω' : Type*} [Fintype Ω']

omit [Nonempty Ω] in
/-- **(RH.9, cutoff independence)**: the intrinsic source action of the
exactly pulled-back source under a projective base law is that of the
coarse cutoff — every adjacent transport novelty is zero. -/
theorem source_action_pullback {w : Ω → ℝ} {w' : Ω' → ℝ} {π : Ω' → Ω}
    (hw : ∀ x, 0 < w x) (hw' : ∀ x', 0 < w' x')
    (hpush : ∀ f : Ω → ℝ, ∑ x', w' x' * f (π x') = ∑ x, w x * f x)
    (B : Ω → ℝ) (η : ℝ) :
    sourceAction w' (fun x' => B (π x')) η = sourceAction w B η := by
  have hZeq := zNorm_pullback hpush B η
  have hratio' : ∀ x', tilt w' (fun y => B (π y)) η x' / w' x'
      = Real.exp (η * B (π x')) / zNorm w B η := by
    intro x'
    have hwx : w' x' ≠ 0 := (hw' x').ne'
    unfold tilt
    rw [hZeq]
    beta_reduce
    field_simp
  have hratio : ∀ x, tilt w B η x / w x
      = Real.exp (η * B x) / zNorm w B η := by
    intro x
    have hwx : w x ≠ 0 := (hw x).ne'
    unfold tilt
    field_simp
  unfold sourceAction
  calc ∑ x', tilt w' (fun y => B (π y)) η x'
        * Real.log (tilt w' (fun y => B (π y)) η x' / w' x')
      = ∑ x', tilt w' (fun y => B (π y)) η x'
          * ((fun x => Real.log (Real.exp (η * B x) / zNorm w B η)) (π x')) := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [hratio' x']
    _ = ∑ x, tilt w B η x
          * Real.log (Real.exp (η * B x) / zNorm w B η) :=
        tilt_pullback hpush B η
          fun x => Real.log (Real.exp (η * B x) / zNorm w B η)
    _ = ∑ x, tilt w B η x * Real.log (tilt w B η x / w x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hratio x]

omit [Fintype Ω] [Nonempty Ω] in
/-- Summing the same cutoff-independent relative entropy over cutoffs
counts the one occurring source `K` times. -/
theorem summing_recounts_source (A : ℕ → ℝ) (hA : ∀ N, A N = A 0)
    (K : ℕ) : ∑ N ∈ Finset.range K, A N = K * A 0 := by
  rw [Finset.sum_congr rfl fun N _ => hA N, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

end H4Action

end H4ActionSection

/-! ### `thm:RPESM-source-conditioned-projectivity`

Rendering (RS.1–RS.4): the relational neutral-Higgs source is built from
the frame-coordinate saturation read: `χ_H(h) = h/√(1+‖h‖²)` on the
doublet carrier `W_H = ℂ²` (`EuclideanSpace ℂ (Fin 2)`), the covariant
frame enters through the unit vector `b = f⁺ζ₀`, and the positive-time
writer is `B⁺ = Re⟨b, χ_H(H)⟩` with reflected source `B = B⁺ + ΘB⁺`
(RS.1).  Exact root/frame/Higgs-coordinate transport is the hypothesis
`H_{N+1} = H_N ∘ π` with the frame vector fixed; the base path laws are a
projective finite family.  The bundle proves `|B⁺| ≤ 1`, `|B| ≤ 2`, the
exact source transport `B_{N+1} = B_N ∘ π`, the windows (RS.3), the exact
normalizer and conditioned-law transport (RS.4), the identically-one
source cocycle (vanishing source-coordinate mismatch, old-source debit,
and fresh shell-source birth), and the `N`-independent conditioned
density (the conditioned state and every descendant conditioned
expectation of a pulled-back writer are deterministic consequences of the
one source occurrence).  Reflection positivity of the conditioned family
is `relational_source_reflection_positive`. -/

section SourceConditionedProjectivitySection

namespace RelationalSource

open TiltThread
open scoped InnerProduct ComplexInnerProductSpace

/-- The Higgs saturation map `χ_H(h) = h/√(1+‖h‖²)` on the doublet
carrier. -/
noncomputable def chiH (h : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt (1 + ‖h‖ ^ 2))⁻¹ : ℝ) • h

/-- The saturation map lands strictly inside the unit ball. -/
theorem norm_chiH_lt_one (h : EuclideanSpace ℂ (Fin 2)) : ‖chiH h‖ < 1 := by
  unfold chiH
  have hs : 0 < Real.sqrt (1 + ‖h‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs),
    inv_mul_eq_div, div_lt_one hs, Real.lt_sqrt (norm_nonneg h)]
  linarith

variable {Ω : Type*} [Fintype Ω]

/-- The positive-time relational writer `B⁺ = Re⟨b, χ_H(H)⟩` (RS.1). -/
noncomputable def bPlus (b : EuclideanSpace ℂ (Fin 2))
    (Hread : Ω → EuclideanSpace ℂ (Fin 2)) : Ω → ℝ :=
  fun x => (⟪b, chiH (Hread x)⟫).re

/-- The reflected relational source `B = B⁺ + ΘB⁺` (RS.1). -/
noncomputable def bRefl (b : EuclideanSpace ℂ (Fin 2))
    (Hread : Ω → EuclideanSpace ℂ (Fin 2)) (Θ : Ω → Ω) : Ω → ℝ :=
  fun x => bPlus b Hread x + bPlus b Hread (Θ x)

omit [Fintype Ω] in
/-- The positive-time relational writer is bounded by one. -/
theorem abs_bPlus_le_one {b : EuclideanSpace ℂ (Fin 2)} (hb : ‖b‖ = 1)
    (Hread : Ω → EuclideanSpace ℂ (Fin 2)) (x : Ω) :
    |bPlus b Hread x| ≤ 1 := by
  unfold bPlus
  calc |(⟪b, chiH (Hread x)⟫).re| ≤ ‖⟪b, chiH (Hread x)⟫‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖b‖ * ‖chiH (Hread x)‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by
        rw [hb, one_mul]
        exact (norm_chiH_lt_one _).le

omit [Fintype Ω] in
/-- The reflected relational source is bounded by two. -/
theorem abs_bRefl_le_two {b : EuclideanSpace ℂ (Fin 2)} (hb : ‖b‖ = 1)
    (Hread : Ω → EuclideanSpace ℂ (Fin 2)) (Θ : Ω → Ω) (x : Ω) :
    |bRefl b Hread Θ x| ≤ 2 := by
  unfold bRefl
  calc |bPlus b Hread x + bPlus b Hread (Θ x)|
      ≤ |bPlus b Hread x| + |bPlus b Hread (Θ x)| := abs_add_le _ _
    _ ≤ 2 := by
        have h1 := abs_bPlus_le_one hb Hread x
        have h2 := abs_bPlus_le_one hb Hread (Θ x)
        linarith

/-- **`thm:RPESM-source-conditioned-projectivity` (RS.1–RS.4)**: the
source bounds `|B⁺| ≤ 1`, `|B| ≤ 2`, the exact source transport
`B_{N+1} = B_N ∘ π`, the normalizer and density windows (RS.3), the
exact normalizer equality and conditioned-law pushforward (RS.4), the
identically-one adjacent source cocycle (zero source-coordinate
mismatch, old-source debit, and shell-source birth), and the
`N`-independent conditioned density. -/
theorem source_conditioned_projectivity
    {Ω' : Type*} [Fintype Ω']
    (w : Ω → ℝ) (w' : Ω' → ℝ) (π : Ω' → Ω) (Θ : Ω → Ω) (Θ' : Ω' → Ω')
    (b : EuclideanSpace ℂ (Fin 2))
    (Hread : Ω → EuclideanSpace ℂ (Fin 2))
    (Hread' : Ω' → EuclideanSpace ℂ (Fin 2)) (η : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1) (hb : ‖b‖ = 1)
    (hpush : ∀ f : Ω → ℝ, ∑ x', w' x' * f (π x') = ∑ x, w x * f x)
    (hHpull : ∀ x', Hread' x' = Hread (π x'))
    (hΘcomm : ∀ x', π (Θ' x') = Θ (π x'))
    (hη : 0 ≤ η) (_hηstar : η ≤ 1 / 64) :
    (∀ x, |bPlus b Hread x| ≤ 1)
    ∧ (∀ x, |bRefl b Hread Θ x| ≤ 2)
    ∧ (∀ x', bRefl b Hread' Θ' x' = bRefl b Hread Θ (π x'))
    ∧ (Real.exp (-(2 * η)) ≤ zNorm w (bRefl b Hread Θ) η
        ∧ zNorm w (bRefl b Hread Θ) η ≤ Real.exp (2 * η))
    ∧ (∀ x, Real.exp (-(4 * η))
          ≤ Real.exp (η * bRefl b Hread Θ x) / zNorm w (bRefl b Hread Θ) η
        ∧ Real.exp (η * bRefl b Hread Θ x) / zNorm w (bRefl b Hread Θ) η
          ≤ Real.exp (4 * η))
    ∧ zNorm w' (bRefl b Hread' Θ') η = zNorm w (bRefl b Hread Θ) η
    ∧ (∀ f : Ω → ℝ, ∑ x', tilt w' (bRefl b Hread' Θ') η x' * f (π x')
        = ∑ x, tilt w (bRefl b Hread Θ) η x * f x)
    ∧ (∀ x', Real.exp (η * bRefl b Hread' Θ' x')
        / Real.exp (η * bRefl b Hread Θ (π x')) = 1)
    ∧ (∀ x', Real.exp (η * bRefl b Hread' Θ' x')
          / zNorm w' (bRefl b Hread' Θ') η
        = Real.exp (η * bRefl b Hread Θ (π x'))
          / zNorm w (bRefl b Hread Θ) η) := by
  have hb2 := abs_bRefl_le_two hb Hread Θ
  have hBpull : ∀ x', bRefl b Hread' Θ' x' = bRefl b Hread Θ (π x') := by
    intro x'
    unfold bRefl bPlus
    rw [hHpull x', hHpull (Θ' x'), hΘcomm x']
  have hBfun : bRefl b Hread' Θ' = fun x' => bRefl b Hread Θ (π x') :=
    funext hBpull
  have hZeq : zNorm w' (bRefl b Hread' Θ') η
      = zNorm w (bRefl b Hread Θ) η := by
    rw [hBfun]
    exact zNorm_pullback hpush _ η
  refine ⟨abs_bPlus_le_one hb Hread, hb2, hBpull,
    zNorm_window hw hw1 hb2 hη, fun x => ?_, hZeq, fun f => ?_,
    fun x' => ?_, fun x' => ?_⟩
  · have := density_window hw hw1 hb2 hη x
    rwa [show (2 : ℝ) * 2 * η = 4 * η by ring] at this
  · rw [hBfun]
    exact tilt_pullback hpush _ η f
  · rw [hBpull x']
    exact div_self (Real.exp_pos _).ne'
  · rw [hBpull x', hZeq]

/-- **`thm:RPESM-source-conditioned-projectivity`, reflection clause**:
the conditioned relational family is reflection positive on every
positive-time writer. -/
theorem relational_source_reflection_positive [Nonempty Ω] {w : Ω → ℝ}
    (hw : ∀ x, 0 < w x) (Θ : Ω → Ω) (b : EuclideanSpace ℂ (Fin 2))
    (Hread : Ω → EuclideanSpace ℂ (Fin 2)) (η : ℝ)
    (PT : (Ω → ℂ) → Prop)
    (hRP : ∀ F, PT F →
      0 ≤ (∑ x, (w x : ℂ) * ((starRingEnd ℂ) (F (Θ x)) * F x)).re)
    (hclosed : ∀ F, PT F →
      PT fun x => (Real.exp (η * bPlus b Hread x) : ℂ) * F x)
    (F : Ω → ℂ) (hF : PT F) :
    0 ≤ (∑ x, ((tilt w (bRefl b Hread Θ) η x : ℝ) : ℂ)
        * ((starRingEnd ℂ) (F (Θ x)) * F x)).re :=
  tilt_reflection_positive hw Θ (bPlus b Hread) η PT hRP hclosed F hF

end RelationalSource

end SourceConditionedProjectivitySection

/-! ### Shared expectation-functional library

The occurring one-site and orbit laws of the RS records are rendered — as
in the repo's isotropy layer (`NCG/Gravity/IsotropicMoments.lean`) — by
their expectation functionals: a map `Ef : (α → ℝ) → ℝ` that is additive,
real-homogeneous, monotone, and normalized (`IsExpectation`).  Every
genuine probability law induces such a functional; conversely all record
content (Gibbs reweighting windows, product-law moments, concentration,
orbit floors) is derived from these four properties, so nothing about the
laws beyond their occurring structural facts is assumed.  `gibbs Ef V` is
the normalized exponential reweighting `f ↦ E[e^V f]/E[e^V]`, again an
expectation functional, with the two-sided oscillation comparison
`e^{lo−hi} E[f] ≤ E_V[f] ≤ e^{hi−lo} E[f]` for `f ≥ 0`. -/

section ExpFunSection

namespace ExpFun

variable {α : Type*}

/-- An expectation functional: additive, real-homogeneous, monotone, and
normalized. -/
structure IsExpectation (Ef : (α → ℝ) → ℝ) : Prop where
  add : ∀ f g : α → ℝ, Ef (fun h => f h + g h) = Ef f + Ef g
  smul : ∀ (c : ℝ) (f : α → ℝ), Ef (fun h => c * f h) = c * Ef f
  mono : ∀ f g : α → ℝ, (∀ h, f h ≤ g h) → Ef f ≤ Ef g
  one : Ef (fun _ => 1) = 1

namespace IsExpectation

variable {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)

include hE

/-- Expectation of a constant. -/
theorem const (c : ℝ) : Ef (fun _ => c) = c := by
  have h := hE.smul c fun _ => 1
  rw [hE.one, mul_one] at h
  simpa using h

/-- Expectation of zero. -/
theorem zero : Ef (fun _ => 0) = 0 := by
  have h := hE.const 0
  exact h

/-- Expectation of a negation. -/
theorem neg (f : α → ℝ) : Ef (fun h => -f h) = -Ef f := by
  have h := hE.smul (-1) f
  simpa using h

/-- Expectation of a difference. -/
theorem sub (f g : α → ℝ) : Ef (fun h => f h - g h) = Ef f - Ef g := by
  have h := hE.add f fun h => -g h
  rw [hE.neg g] at h
  rw [show (fun h => f h - g h) = fun h => f h + -g h from
    funext fun h => by ring, h]
  ring

/-- Expectation of a nonnegative writer is nonnegative. -/
theorem nonneg {f : α → ℝ} (hf : ∀ h, 0 ≤ f h) : 0 ≤ Ef f := by
  have h := hE.mono (fun _ => 0) f fun h => hf h
  rwa [hE.zero] at h

/-- Expectation of a finite sum of writers. -/
theorem sum {ι : Type*} (s : Finset ι) (F : ι → α → ℝ) :
    Ef (fun h => ∑ k ∈ s, F k h) = ∑ k ∈ s, Ef (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hE.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha,
        show (fun h => ∑ k ∈ insert a s, F k h)
          = fun h => F a h + ∑ k ∈ s, F k h from
          funext fun h => by rw [Finset.sum_insert ha],
        hE.add, ih]

/-- A two-sided bound transfers to the expectation. -/
theorem abs_le {f : α → ℝ} {c : ℝ} (hf : ∀ h, |f h| ≤ c) : |Ef f| ≤ c := by
  have h₁ := hE.mono f (fun _ => c) fun h => (_root_.abs_le.mp (hf h)).2
  have h₂ := hE.mono (fun _ => -c) f fun h => (_root_.abs_le.mp (hf h)).1
  rw [hE.const] at h₁
  rw [hE.const] at h₂
  exact _root_.abs_le.mpr ⟨h₂, h₁⟩

end IsExpectation

variable {Ef : (α → ℝ) → ℝ}

/-- The complex expectation induced by a real expectation functional. -/
noncomputable def cExp (Ef : (α → ℝ) → ℝ) (F : α → ℂ) : ℂ :=
  ⟨Ef fun h => (F h).re, Ef fun h => (F h).im⟩

/-- Additivity of the complex expectation. -/
theorem cExp_add (hE : IsExpectation Ef) (F G : α → ℂ) :
    cExp Ef (fun h => F h + G h) = cExp Ef F + cExp Ef G := by
  refine Complex.ext ?_ ?_
  · show Ef (fun h => (F h + G h).re)
      = Ef (fun h => (F h).re) + Ef fun h => (G h).re
    rw [show (fun h => (F h + G h).re) = fun h => (F h).re + (G h).re from
      funext fun h => Complex.add_re _ _]
    exact hE.add _ _
  · show Ef (fun h => (F h + G h).im)
      = Ef (fun h => (F h).im) + Ef fun h => (G h).im
    rw [show (fun h => (F h + G h).im) = fun h => (F h).im + (G h).im from
      funext fun h => Complex.add_im _ _]
    exact hE.add _ _

/-- Complex homogeneity of the complex expectation. -/
theorem cExp_smul (hE : IsExpectation Ef) (a : ℂ) (F : α → ℂ) :
    cExp Ef (fun h => a * F h) = a * cExp Ef F := by
  refine Complex.ext ?_ ?_
  · show Ef (fun h => (a * F h).re)
      = a.re * Ef (fun h => (F h).re) - a.im * Ef fun h => (F h).im
    rw [show (fun h => (a * F h).re)
        = fun h => a.re * (F h).re - a.im * (F h).im from
        funext fun h => Complex.mul_re _ _]
    rw [hE.sub, hE.smul, hE.smul]
  · show Ef (fun h => (a * F h).im)
      = a.re * Ef (fun h => (F h).im) + a.im * Ef fun h => (F h).re
    rw [show (fun h => (a * F h).im)
        = fun h => a.re * (F h).im + a.im * (F h).re from
        funext fun h => Complex.mul_im _ _]
    rw [hE.add, hE.smul, hE.smul]

/-- The complex expectation of the zero writer. -/
theorem cExp_zero (hE : IsExpectation Ef) :
    cExp Ef (fun _ => 0) = 0 := by
  refine Complex.ext ?_ ?_
  · show Ef (fun _ => (0 : ℂ).re) = (0 : ℝ)
    simpa using hE.zero
  · show Ef (fun _ => (0 : ℂ).im) = (0 : ℝ)
    simpa using hE.zero

/-- The complex expectation of a finite sum of writers. -/
theorem cExp_sum (hE : IsExpectation Ef) {ι : Type*} (s : Finset ι)
    (F : ι → α → ℂ) :
    cExp Ef (fun h => ∑ k ∈ s, F k h) = ∑ k ∈ s, cExp Ef (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cExp_zero hE
  | insert a s ha ih =>
      rw [Finset.sum_insert ha,
        show (fun h => ∑ k ∈ insert a s, F k h)
          = fun h => F a h + ∑ k ∈ s, F k h from
          funext fun h => by rw [Finset.sum_insert ha],
        cExp_add hE, ih]

/-- The complex expectation of a real writer is the real expectation. -/
theorem cExp_ofReal (hE : IsExpectation Ef) (f : α → ℝ) :
    cExp Ef (fun h => ((f h : ℝ) : ℂ)) = ((Ef f : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · show Ef (fun h => ((f h : ℝ) : ℂ).re) = Ef f
    rw [show (fun h => ((f h : ℝ) : ℂ).re) = f from
      funext fun h => Complex.ofReal_re _]
  · show Ef (fun h => ((f h : ℝ) : ℂ).im) = (0 : ℝ)
    rw [show (fun h => ((f h : ℝ) : ℂ).im) = fun _ => (0 : ℝ) from
      funext fun h => Complex.ofReal_im _]
    exact hE.zero


/-- The complex expectation of a conjugated writer. -/
theorem cExp_conj (hE : IsExpectation Ef) (F : α → ℂ) :
    cExp Ef (fun h => (starRingEnd ℂ) (F h)) = (starRingEnd ℂ) (cExp Ef F) := by
  refine Complex.ext ?_ ?_
  · show Ef (fun h => ((starRingEnd ℂ) (F h)).re) = Ef fun h => (F h).re
    rw [show (fun h => ((starRingEnd ℂ) (F h)).re) = fun h => (F h).re from
      funext fun h => Complex.conj_re _]
  · show Ef (fun h => ((starRingEnd ℂ) (F h)).im) = -Ef fun h => (F h).im
    rw [show (fun h => ((starRingEnd ℂ) (F h)).im) = fun h => -(F h).im from
      funext fun h => Complex.conj_im _]
    exact hE.neg _

/-- The Cauchy–Schwarz mean bound `E[|f|] ≤ √(E[f²])`. -/
theorem IsExpectation.abs_mean_le_sqrt (hE : IsExpectation Ef) (f : α → ℝ) :
    Ef (fun h => |f h|) ≤ Real.sqrt (Ef fun h => f h ^ 2) := by
  set a := Ef fun h => |f h| with ha
  set b := Ef fun h => f h ^ 2 with hb
  have hano : 0 ≤ a := hE.nonneg fun h => abs_nonneg _
  have hbno : 0 ≤ b := hE.nonneg fun h => sq_nonneg _
  have hkey : 0 ≤ b - 2 * a * a + a ^ 2 := by
    have hexp : Ef (fun h => (|f h| - a) ^ 2) = b - 2 * a * a + a ^ 2 := by
      rw [show (fun h => (|f h| - a) ^ 2)
          = fun h => f h ^ 2 + (-(2 * a) * |f h| + a ^ 2 * 1) from
          funext fun h => by rw [sub_sq, sq_abs]; ring]
      rw [hE.add, hE.add, hE.smul, hE.smul, hE.one, ← ha, ← hb]
      ring
    have := hE.nonneg (f := fun h => (|f h| - a) ^ 2) fun h => sq_nonneg _
    rw [hexp] at this
    linarith
  have hsq : a ^ 2 ≤ b := by nlinarith
  calc a = Real.sqrt (a ^ 2) := by rw [Real.sqrt_sq hano]
    _ ≤ Real.sqrt b := Real.sqrt_le_sqrt hsq

/-- The Gibbs (exponentially tilted, normalized) functional
`f ↦ E[e^V f]/E[e^V]`. -/
noncomputable def gibbs (Ef : (α → ℝ) → ℝ) (V : α → ℝ) :
    (α → ℝ) → ℝ :=
  fun f => Ef (fun h => Real.exp (V h) * f h) / Ef fun h => Real.exp (V h)

/-- Window for the Gibbs normalizer. -/
theorem gibbs_normalizer_window {Ef : (α → ℝ) → ℝ}
    (hE : IsExpectation Ef) {V : α → ℝ} {lo hi : ℝ}
    (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi) :
    Real.exp lo ≤ Ef (fun h => Real.exp (V h))
      ∧ Ef (fun h => Real.exp (V h)) ≤ Real.exp hi := by
  constructor
  · have h := hE.mono (fun _ => Real.exp lo) (fun h => Real.exp (V h))
      fun h => Real.exp_le_exp.mpr (hV h).1
    rwa [hE.const] at h
  · have h := hE.mono (fun h => Real.exp (V h)) (fun _ => Real.exp hi)
      fun h => Real.exp_le_exp.mpr (hV h).2
    rwa [hE.const] at h

/-- The Gibbs functional of an expectation is an expectation. -/
theorem gibbs_isExpectation {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    {V : α → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi) :
    IsExpectation (gibbs Ef V) := by
  have hZpos : 0 < Ef (fun h => Real.exp (V h)) :=
    lt_of_lt_of_le (Real.exp_pos lo) (gibbs_normalizer_window hE hV).1
  refine ⟨fun f g => ?_, fun c f => ?_, fun f g hfg => ?_, ?_⟩
  · unfold gibbs
    rw [show (fun h => Real.exp (V h) * (f h + g h))
        = fun h => Real.exp (V h) * f h + Real.exp (V h) * g h from
        funext fun h => by ring, hE.add, add_div]
  · unfold gibbs
    rw [show (fun h => Real.exp (V h) * (c * f h))
        = fun h => c * (Real.exp (V h) * f h) from
        funext fun h => by ring, hE.smul, mul_div_assoc]
  · unfold gibbs
    refine (div_le_div_iff_of_pos_right hZpos).mpr ?_
    exact hE.mono _ _ fun h =>
      mul_le_mul_of_nonneg_left (hfg h) (Real.exp_pos _).le
  · unfold gibbs
    rw [show (fun h => Real.exp (V h) * 1) = fun h => Real.exp (V h) from
      funext fun h => by ring]
    exact div_self hZpos.ne'

/-- **Two-sided oscillation comparison**: the Gibbs reweighting of a
nonnegative writer is at least `e^{lo−hi}` times its base expectation. -/
theorem gibbs_ge {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    {V : α → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi)
    {f : α → ℝ} (hf : ∀ h, 0 ≤ f h) :
    Real.exp (lo - hi) * Ef f ≤ gibbs Ef V f := by
  obtain ⟨hZlo, hZhi⟩ := gibbs_normalizer_window hE hV
  have hZpos : 0 < Ef (fun h => Real.exp (V h)) :=
    lt_of_lt_of_le (Real.exp_pos lo) hZlo
  have hnum : Real.exp lo * Ef f ≤ Ef (fun h => Real.exp (V h) * f h) := by
    have h := hE.mono (fun h => Real.exp lo * f h)
      (fun h => Real.exp (V h) * f h) fun h =>
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hV h).1) (hf h)
    rwa [hE.smul] at h
  have hEf : 0 ≤ Ef f := hE.nonneg hf
  calc Real.exp (lo - hi) * Ef f
      = Real.exp lo * Ef f / Real.exp hi := by
        rw [Real.exp_sub]
        ring
    _ ≤ Ef (fun h => Real.exp (V h) * f h) / Real.exp hi := by
        exact (div_le_div_iff_of_pos_right (Real.exp_pos hi)).mpr hnum
    _ ≤ Ef (fun h => Real.exp (V h) * f h) / Ef (fun h => Real.exp (V h)) := by
        refine div_le_div_of_nonneg_left ?_ hZpos hZhi
        exact hE.nonneg fun h => mul_nonneg (Real.exp_pos _).le (hf h)
    _ = gibbs Ef V f := rfl

/-- **Two-sided oscillation comparison, upper side**: the Gibbs
reweighting of a nonnegative writer is at most `e^{hi−lo}` times its base
expectation. -/
theorem gibbs_le {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    {V : α → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi)
    {f : α → ℝ} (hf : ∀ h, 0 ≤ f h) :
    gibbs Ef V f ≤ Real.exp (hi - lo) * Ef f := by
  obtain ⟨hZlo, hZhi⟩ := gibbs_normalizer_window hE hV
  have hZpos : 0 < Ef (fun h => Real.exp (V h)) :=
    lt_of_lt_of_le (Real.exp_pos lo) hZlo
  have hnum : Ef (fun h => Real.exp (V h) * f h) ≤ Real.exp hi * Ef f := by
    have h := hE.mono (fun h => Real.exp (V h) * f h)
      (fun h => Real.exp hi * f h) fun h =>
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hV h).2) (hf h)
    rwa [hE.smul] at h
  have hEf : 0 ≤ Ef f := hE.nonneg hf
  calc gibbs Ef V f
      ≤ Ef (fun h => Real.exp (V h) * f h) / Real.exp lo := by
        refine div_le_div_of_nonneg_left ?_ (Real.exp_pos lo) hZlo
        exact hE.nonneg fun h => mul_nonneg (Real.exp_pos _).le (hf h)
    _ ≤ Real.exp hi * Ef f / Real.exp lo :=
        (div_le_div_iff_of_pos_right (Real.exp_pos lo)).mpr hnum
    _ = Real.exp (hi - lo) * Ef f := by
        rw [Real.exp_sub]
        ring

end ExpFun

end ExpFunSection

/-! ### `cth:RPESM-local-source-no-rank-one` and the uniform orbit floor

Rendering (RS.5–RS.6 layer): the local frame-coordinate read at the
transported old root is the saturation `v = χ_H(h)` of the Higgs
coordinate `h ∈ W_H = ℂ²`.  The product quartic proposal `q_H` enters
through its expectation functional `Ef` (`ExpFun.IsExpectation`) together
with its two occurring structural facts: rotational invariance
(`Ef (f∘U) = Ef f` for every unitary `U` of the doublet) and
non-concentration at the origin (`0 < Ef (min ‖h‖² 1)`); the constant
`a_χ` is rendered as the frame-coordinate saturation second moment
`a_χ = Ef ‖⟨ζ₀, χ_H(·)⟩‖²`, proved equal to the same moment of every unit
direction (`aChi_isotropy`, the manuscript's rotational-invariance step,
via an explicitly constructed unitary carrying `ζ₀` to the given
direction).  The interacting law at cutoff `N` has normalized density
`e^{g_N}` against the proposal with oscillation window `17/64`, and
source conditioning multiplies by `e^{ηB_N}` with `|B_N| ≤ 2`,
`0 ≤ η ≤ 1/64`; the conditioned orbit Gram is the `2×2` matrix of
conditioned second moments of the read.  We prove the uniform Loewner
floor `Q ⪰ e^{-21/64} a_χ I₂` (`orbitGram_floor`), the induced
eigenvalue floor, and the countertheorem: along arbitrary `N_j → ∞`,
`0 ≤ η_j ≤ 1/64`, the second orbit eigenvalue satisfies
`liminf_j λ₂(Q_j) ≥ e^{-21/64} a_χ > 0` — ultraviolet refinement of the
one-root source is not a thermodynamic rank-one phase.  (The 10-digit
numeric evaluation of `a_χ` in RS.6 is not formalized; the countertheorem
uses only the exact floor `e^{-21/64} a_χ > 0`.) -/

section LocalOrbitSection

namespace LocalOrbit

open ExpFun RelationalSource Filter
open scoped InnerProduct ComplexInnerProductSpace

/-- The Higgs doublet carrier `W_H = ℂ²`. -/
abbrev WH : Type := EuclideanSpace ℂ (Fin 2)

/-- The neutral direction `ζ₀ = (0,1)ᵀ` (RS.1). -/
noncomputable def zeta0 : WH := EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

/-- The neutral direction is a unit vector. -/
theorem norm_zeta0 : ‖zeta0‖ = 1 := by
  unfold zeta0
  rw [PiLp.norm_single]
  norm_num

variable {Ef : (WH → ℝ) → ℝ}

/-- The conditioned local orbit Gram
`Q = E[χ_H(h) χ_H(h)^*]` of the frame-coordinate read. -/
noncomputable def orbitGram (Ef : (WH → ℝ) → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cExp Ef fun h => chiH h i * (starRingEnd ℂ) (chiH h j)

/-- The orbit Gram is Hermitian. -/
theorem orbitGram_isHermitian (hE : IsExpectation Ef) :
    (orbitGram Ef).IsHermitian := by
  show (orbitGram Ef)ᴴ = orbitGram Ef
  ext i j
  rw [Matrix.conjTranspose_apply]
  have hre : ∀ h : WH, (chiH h j * (starRingEnd ℂ) (chiH h i)).re
      = (chiH h i * (starRingEnd ℂ) (chiH h j)).re := by
    intro h
    rw [Complex.mul_re, Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  have him : ∀ h : WH, (chiH h j * (starRingEnd ℂ) (chiH h i)).im
      = -(chiH h i * (starRingEnd ℂ) (chiH h j)).im := by
    intro h
    rw [Complex.mul_im, Complex.mul_im]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  refine Complex.ext ?_ ?_
  · show Ef (fun h => (chiH h j * (starRingEnd ℂ) (chiH h i)).re)
      = Ef fun h => (chiH h i * (starRingEnd ℂ) (chiH h j)).re
    rw [show (fun h => (chiH h j * (starRingEnd ℂ) (chiH h i)).re)
        = fun h => (chiH h i * (starRingEnd ℂ) (chiH h j)).re from
        funext hre]
  · show -Ef (fun h => (chiH h j * (starRingEnd ℂ) (chiH h i)).im)
      = Ef fun h => (chiH h i * (starRingEnd ℂ) (chiH h j)).im
    rw [show (fun h => (chiH h j * (starRingEnd ℂ) (chiH h i)).im)
        = fun h => -(chiH h i * (starRingEnd ℂ) (chiH h j)).im from
        funext him]
    rw [hE.neg, neg_neg]

/-- **The orbit quadratic form** is the conditioned second moment of the
directional saturation read:
`c* Q c = E[ ‖∑ᵢ c̄ᵢ χ_H(h)ᵢ‖² ]`. -/
theorem orbitGram_form (hE : IsExpectation Ef) (c : Fin 2 → ℂ) :
    star c ⬝ᵥ (orbitGram Ef *ᵥ c)
      = ((Ef (fun h =>
          ‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2) : ℝ) : ℂ) := by
  have hlhs : star c ⬝ᵥ (orbitGram Ef *ᵥ c)
      = ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j) * orbitGram Ef i j := by
    unfold dotProduct Matrix.mulVec dotProduct
    rw [Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, Complex.star_def]
    ring
  rw [hlhs]
  have hterm : ∀ i j, ((starRingEnd ℂ) (c i) * c j) * orbitGram Ef i j
      = cExp Ef fun h => ((starRingEnd ℂ) (c i) * c j)
          * (chiH h i * (starRingEnd ℂ) (chiH h j)) := by
    intro i j
    rw [cExp_smul hE]
    rfl
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  rw [Finset.sum_congr rfl fun i _ => (cExp_sum hE Finset.univ _).symm,
    (cExp_sum hE Finset.univ _).symm]
  have hpt : ∀ h : WH,
      (∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
        * (chiH h i * (starRingEnd ℂ) (chiH h j)))
      = ((‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2 : ℝ) : ℂ) := by
    intro h
    have hz : (∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
          * (chiH h i * (starRingEnd ℂ) (chiH h j)))
        = (∑ i, (starRingEnd ℂ) (c i) * chiH h i)
          * (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (c j) * chiH h j) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hz, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show (fun h => ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
      * (chiH h i * (starRingEnd ℂ) (chiH h j)))
      = fun h => ((‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2 : ℝ) : ℂ)
      from funext hpt]
  exact cExp_ofReal hE _

/-- The saturation read is equivariant under doublet unitaries. -/
theorem chiH_equivariant (U : WH ≃ₗᵢ[ℂ] WH) (h : WH) :
    chiH (U h) = U (chiH h) := by
  unfold chiH
  rw [U.norm_map]
  exact (LinearMapClass.map_smul_of_tower U _ h).symm

/-- The squared saturation norm. -/
theorem norm_chiH_sq (h : WH) : ‖chiH h‖ ^ 2 = ‖h‖ ^ 2 / (1 + ‖h‖ ^ 2) := by
  unfold chiH
  have hpos : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖h‖ ^ 2) := Real.sqrt_pos.mpr hpos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow,
    inv_pow, Real.sq_sqrt hpos.le]
  ring

/-- `a_χ`: the frame-coordinate saturation second moment of the
proposal (RS.5, rendered as the occurring frame integral). -/
noncomputable def aChi (Ef : (WH → ℝ) → ℝ) : ℝ :=
  Ef fun h => ‖(⟪zeta0, chiH h⟫ : ℂ)‖ ^ 2

/-- Every unit direction of the doublet carries a unitary frame taking
`ζ₀` to it. -/
theorem exists_isometry_zeta0 {c : WH} (hc : ‖c‖ = 1) :
    ∃ U : WH ≃ₗᵢ[ℂ] WH, U zeta0 = c := by
  have hcard : Module.finrank ℂ WH = Fintype.card (Fin 2) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  have horth : Orthonormal ℂ
      (({(1 : Fin 2)} : Set (Fin 2)).domRestrict fun _ => c) := by
    constructor
    · rintro ⟨i, hi⟩
      exact hc
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hne
      exfalso
      apply hne
      apply Subtype.ext
      rw [Set.mem_singleton_iff] at hi hj
      exact hi.trans hj.symm
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨(EuclideanSpace.basisFun (Fin 2) ℂ).equiv b (Equiv.refl _), ?_⟩
  have h1 : zeta0 = EuclideanSpace.basisFun (Fin 2) ℂ 1 := by
    rw [EuclideanSpace.basisFun_apply]
    rfl
  rw [h1, OrthonormalBasis.equiv_apply_basis]
  exact hb 1 (Set.mem_singleton _)

/-- **Isotropy of the proposal** (the manuscript's rotational-invariance
step): every unit direction has the same saturation second moment
`a_χ`. -/
theorem aChi_isotropy (_hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    {c : WH} (hc : ‖c‖ = 1) :
    Ef (fun h => ‖(⟪c, chiH h⟫ : ℂ)‖ ^ 2) = aChi Ef := by
  obtain ⟨U, hU⟩ := exists_isometry_zeta0 hc
  have h1 := hInv U fun h => ‖(⟪c, chiH h⟫ : ℂ)‖ ^ 2
  have hpt : ∀ h : WH, ‖(⟪c, chiH (U h)⟫ : ℂ)‖ ^ 2
      = ‖(⟪zeta0, chiH h⟫ : ℂ)‖ ^ 2 := by
    intro h
    have hmap := U.toLinearIsometry.inner_map_map zeta0 (chiH h)
    rw [LinearIsometryEquiv.coe_toLinearIsometry] at hmap
    rw [chiH_equivariant U h, ← hU, hmap]
  rw [show (fun h => ‖(⟪c, chiH (U h)⟫ : ℂ)‖ ^ 2)
      = fun h => ‖(⟪zeta0, chiH h⟫ : ℂ)‖ ^ 2 from funext hpt] at h1
  rw [← h1]
  rfl

/-- `a_χ` is nonnegative. -/
theorem aChi_nonneg (hE : IsExpectation Ef) : 0 ≤ aChi Ef :=
  hE.nonneg fun h => by positivity

/-- **Positivity of `a_χ`** from non-concentration of the proposal at the
origin, through isotropy and the exact saturation profile. -/
theorem aChi_pos (hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (hnondeg : 0 < Ef fun h => min (‖h‖ ^ 2) 1) : 0 < aChi Ef := by
  have he : ∀ i : Fin 2,
      Ef (fun h =>
        ‖(⟪(EuclideanSpace.single i (1 : ℂ) : WH), chiH h⟫ : ℂ)‖ ^ 2)
        = aChi Ef := by
    intro i
    refine aChi_isotropy hE hInv ?_
    rw [PiLp.norm_single]
    norm_num
  have hsplit : ∀ h : WH, ‖chiH h‖ ^ 2
      = ‖(⟪(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : WH), chiH h⟫ : ℂ)‖ ^ 2
        + ‖(⟪(EuclideanSpace.single (1 : Fin 2) (1 : ℂ) : WH),
            chiH h⟫ : ℂ)‖ ^ 2 := by
    intro h
    rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    rw [EuclideanSpace.norm_sq_eq (chiH h), Fin.sum_univ_two]
  have htwo : Ef (fun h => ‖chiH h‖ ^ 2) = 2 * aChi Ef := by
    rw [show (fun h => ‖chiH h‖ ^ 2) = fun h =>
        ‖(⟪(EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : WH), chiH h⟫ : ℂ)‖ ^ 2
          + ‖(⟪(EuclideanSpace.single (1 : Fin 2) (1 : ℂ) : WH),
              chiH h⟫ : ℂ)‖ ^ 2
        from funext hsplit, hE.add, he 0, he 1]
    ring
  have hdom : ∀ h : WH, min (‖h‖ ^ 2) 1 / 2 ≤ ‖chiH h‖ ^ 2 := by
    intro h
    rw [norm_chiH_sq]
    have hn : (0 : ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
    rcases le_or_gt (‖h‖ ^ 2) 1 with hle | hgt
    · rw [min_eq_left hle, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    · rw [min_eq_right hgt.le, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
  have hmono := hE.mono _ _ hdom
  have hhalf : Ef (fun h => min (‖h‖ ^ 2) 1 / 2)
      = Ef (fun h => min (‖h‖ ^ 2) 1) / 2 := by
    rw [show (fun h => min (‖h‖ ^ 2) 1 / 2)
        = fun h => (2 : ℝ)⁻¹ * min (‖h‖ ^ 2) 1 from funext fun h => by ring,
      hE.smul]
    ring
  rw [hhalf, htwo] at hmono
  linarith

/-- The directional saturation moment scales with the squared length of
the direction. -/
theorem directional_moment (hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (c : Fin 2 → ℂ) :
    Ef (fun h => ‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2)
      = (∑ i, ‖c i‖ ^ 2) * aChi Ef := by
  set u : WH := WithLp.toLp 2 c with hu
  have hinner : ∀ h : WH, (⟪u, chiH h⟫ : ℂ)
      = ∑ i, (starRingEnd ℂ) (c i) * chiH h i := by
    intro h
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply']
  have hnorm : ‖u‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  by_cases hzero : c = 0
  · subst hzero
    have h0 : ∀ h : WH, ‖∑ i, (starRingEnd ℂ) ((0 : Fin 2 → ℂ) i)
        * chiH h i‖ ^ 2 = 0 := by
      intro h
      simp
    rw [show (fun h => ‖∑ i, (starRingEnd ℂ) ((0 : Fin 2 → ℂ) i)
        * chiH h i‖ ^ 2) = fun _ => (0 : ℝ) from funext h0, hE.zero]
    simp
  · have hupos : 0 < ‖u‖ := by
      rw [norm_pos_iff]
      intro hu0
      apply hzero
      funext i
      have hcoord := congrArg (fun v : WH => v i) hu0
      simpa using hcoord
    set cunit : WH := ‖u‖⁻¹ • u with hcu
    have hcnorm : ‖cunit‖ = 1 := by
      rw [hcu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hupos),
        inv_mul_cancel₀ hupos.ne']
    have hdir : ∀ h : WH, ‖(⟪u, chiH h⟫ : ℂ)‖ ^ 2
        = ‖u‖ ^ 2 * ‖(⟪cunit, chiH h⟫ : ℂ)‖ ^ 2 := by
      intro h
      have hue : u = ‖u‖ • cunit := by
        rw [hcu, smul_smul, mul_inv_cancel₀ hupos.ne', one_smul]
      have hcast : ((‖u‖ : ℝ) : ℂ) • cunit = (‖u‖ : ℝ) • cunit := by
        rw [← Complex.coe_algebraMap, algebraMap_smul]
      calc ‖(⟪u, chiH h⟫ : ℂ)‖ ^ 2
          = ‖(⟪((‖u‖ : ℝ) : ℂ) • cunit, chiH h⟫ : ℂ)‖ ^ 2 := by
            rw [hcast, ← hue]
        _ = ‖(starRingEnd ℂ) ((‖u‖ : ℝ) : ℂ) * (⟪cunit, chiH h⟫ : ℂ)‖ ^ 2 := by
            rw [inner_smul_left]
        _ = ‖u‖ ^ 2 * ‖(⟪cunit, chiH h⟫ : ℂ)‖ ^ 2 := by
            rw [norm_mul, Complex.conj_ofReal, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hupos]
            ring
    calc Ef (fun h => ‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2)
        = Ef (fun h => ‖u‖ ^ 2 * ‖(⟪cunit, chiH h⟫ : ℂ)‖ ^ 2) := by
          congr 1
          funext h
          rw [← hinner h, hdir h]
      _ = ‖u‖ ^ 2 * Ef (fun h => ‖(⟪cunit, chiH h⟫ : ℂ)‖ ^ 2) := hE.smul _ _
      _ = (∑ i, ‖c i‖ ^ 2) * aChi Ef := by
          rw [aChi_isotropy hE hInv hcnorm, hnorm]

/-- **The uniform local orbit floor (RS.6, Loewner form)**: for every
Gibbs conditioning with oscillation window `[lo, hi]`, the conditioned
orbit Gram satisfies `Q ⪰ e^{lo−hi} a_χ I₂`. -/
theorem orbitGram_floor (hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    {V : WH → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi) :
    (orbitGram (gibbs Ef V)
      - ((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ) • 1).PosSemidef := by
  have hG := gibbs_isExpectation hE hV
  have hsmulH : (((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ)
      • (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
    show _ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  refine posSemidef_of_re_form ((orbitGram_isHermitian hG).sub hsmulH)
    fun x => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, orbitGram_form hG,
    star_dot_self_eq_sum_sq]
  have hfloor : Real.exp (lo - hi) * ((∑ i, ‖x i‖ ^ 2) * aChi Ef)
      ≤ gibbs Ef V fun h => ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2 := by
    have h1 := gibbs_ge hE hV
      (f := fun h => ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2)
      fun h => by positivity
    rwa [directional_moment hE hInv x] at h1
  have hre : (((gibbs Ef V fun h =>
        ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2 : ℝ) : ℂ)
      - ((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ)
        * ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)).re
      = (gibbs Ef V fun h => ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2)
        - Real.exp (lo - hi) * aChi Ef * ∑ i, ‖x i‖ ^ 2 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [smul_eq_mul, hre]
  nlinarith [hfloor]

/-- **The uniform orbit ceiling**: the conditioned orbit Gram satisfies
`Q ⪯ I₂` (the saturation read lies in the unit ball). -/
theorem orbitGram_ceiling (hE : IsExpectation Ef)
    {V : WH → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi) :
    (((1 : ℝ) : ℂ) • 1 - orbitGram (gibbs Ef V)).PosSemidef := by
  have hG := gibbs_isExpectation hE hV
  have hsmulH : (((1 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
    show _ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  refine posSemidef_of_re_form (hsmulH.sub (orbitGram_isHermitian hG))
    fun x => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, orbitGram_form hG,
    star_dot_self_eq_sum_sq]
  have hbound : (gibbs Ef V fun h =>
      ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2) ≤ ∑ i, ‖x i‖ ^ 2 := by
    have hpt : ∀ h : WH, ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2
        ≤ ∑ i, ‖x i‖ ^ 2 := by
      intro h
      set u : WH := WithLp.toLp 2 x with hu
      have hinner : (⟪u, chiH h⟫ : ℂ)
          = ∑ i, (starRingEnd ℂ) (x i) * chiH h i := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.inner_apply']
      rw [← hinner]
      have hchi2 : ‖chiH h‖ ^ 2 ≤ 1 := by
        have h1 := norm_chiH_lt_one h
        have h2 := norm_nonneg (chiH h)
        nlinarith
      calc ‖(⟪u, chiH h⟫ : ℂ)‖ ^ 2 ≤ (‖u‖ * ‖chiH h‖) ^ 2 := by
            have hle := norm_inner_le_norm (𝕜 := ℂ) u (chiH h)
            exact pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = ‖u‖ ^ 2 * ‖chiH h‖ ^ 2 := by ring
        _ ≤ ‖u‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hchi2 (sq_nonneg _)
        _ = ‖u‖ ^ 2 := by ring
        _ = ∑ i, ‖x i‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
    have h1 := hG.mono _ _ hpt
    rwa [hG.const] at h1
  have hre : ((((1 : ℝ) : ℂ) * ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ))
      - ((gibbs Ef V fun h =>
        ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2 : ℝ) : ℂ)).re
      = (∑ i, ‖x i‖ ^ 2)
        - gibbs Ef V fun h => ‖∑ i, (starRingEnd ℂ) (x i) * chiH h i‖ ^ 2 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  rw [smul_eq_mul, hre]
  linarith

/-- The second (least) orbit eigenvalue, as a total function of the
`2×2` Gram. -/
noncomputable def lam2 (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  letI := Classical.dec M.IsHermitian
  if h : M.IsHermitian then hermLamMin h else 0

/-- `lam2` of a Hermitian Gram is its least eigenvalue. -/
theorem lam2_eq {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.IsHermitian) :
    lam2 M = hermLamMin h := by
  unfold lam2
  split
  · rfl
  · exact absurd h ‹¬M.IsHermitian›

/-- **The uniform eigenvalue floor and ceiling** for the conditioned
orbit Gram. -/
theorem lam2_orbit_bounds (hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    {V : WH → ℝ} {lo hi : ℝ} (hV : ∀ h, lo ≤ V h ∧ V h ≤ hi) :
    Real.exp (lo - hi) * aChi Ef ≤ lam2 (orbitGram (gibbs Ef V))
      ∧ lam2 (orbitGram (gibbs Ef V)) ≤ 1 := by
  have hG := gibbs_isExpectation hE hV
  have hherm := orbitGram_isHermitian hG
  rw [lam2_eq hherm]
  constructor
  · exact le_hermLamMin_of_loewner hherm (orbitGram_floor hE hInv hV)
  · have hup := eigenvalues_le_of_loewner hherm (orbitGram_ceiling hE hV) 0
    exact le_trans (hermLamMin_le hherm 0) hup

/-- **`cth:RPESM-local-source-no-rank-one`**: along arbitrary
ultraviolet-refining cutoffs `N_j → ∞` and source strengths
`0 ≤ η_j ≤ 1/64`, the second eigenvalue of the conditioned local orbit
Gram obeys `liminf_j λ₂(Q_{N_j,η_j}) ≥ e^{-21/64} a_χ > 0`: ultraviolet
refinement of the one-root source cannot be relabelled as a
thermodynamic rank-one phase. -/
theorem local_source_no_rank_one (hE : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (hnondeg : 0 < Ef fun h => min (‖h‖ ^ 2) 1)
    (Nseq : ℕ → ℕ) (_hNseq : Filter.Tendsto Nseq Filter.atTop Filter.atTop)
    (ηseq : ℕ → ℝ) (hηseq : ∀ j, 0 ≤ ηseq j ∧ ηseq j ≤ 1 / 64)
    (g : ℕ → WH → ℝ) (lo : ℕ → ℝ)
    (hg : ∀ N h, lo N ≤ g N h ∧ g N h ≤ lo N + 17 / 64)
    (B : ℕ → WH → ℝ) (hB : ∀ N h, |B N h| ≤ 2) :
    0 < Real.exp (-(21 / 64)) * aChi Ef
    ∧ Real.exp (-(21 / 64)) * aChi Ef
      ≤ Filter.liminf (fun j => lam2 (orbitGram
          (gibbs Ef fun h => g (Nseq j) h + ηseq j * B (Nseq j) h)))
        Filter.atTop := by
  have hapos := aChi_pos hE hInv hnondeg
  have hwindow : ∀ j h,
      lo (Nseq j) - 2 * ηseq j ≤ g (Nseq j) h + ηseq j * B (Nseq j) h
      ∧ g (Nseq j) h + ηseq j * B (Nseq j) h
        ≤ lo (Nseq j) + 17 / 64 + 2 * ηseq j := by
    intro j h
    have h1 := (hg (Nseq j) h).1
    have h2 := (hg (Nseq j) h).2
    have h3 := abs_le.mp (hB (Nseq j) h)
    have h4 := (hηseq j).1
    constructor
    · nlinarith [h3.1]
    · nlinarith [h3.2]
  have hterm : ∀ j, Real.exp (-(21 / 64)) * aChi Ef
      ≤ lam2 (orbitGram
        (gibbs Ef fun h => g (Nseq j) h + ηseq j * B (Nseq j) h)) := by
    intro j
    have hlb := (lam2_orbit_bounds hE hInv (hwindow j)).1
    refine le_trans ?_ hlb
    refine mul_le_mul_of_nonneg_right ?_ (aChi_nonneg hE)
    refine Real.exp_le_exp.mpr ?_
    have h4 := (hηseq j).2
    nlinarith [(hηseq j).1]
  refine ⟨mul_pos (Real.exp_pos _) hapos, ?_⟩
  refine Filter.le_liminf_of_le ?_ (Filter.Eventually.of_forall hterm)
  refine Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop
    (x := 1) (Filter.Eventually.of_forall fun j => ?_)
  exact (lam2_orbit_bounds hE hInv (hwindow j)).2

end LocalOrbit

end LocalOrbitSection

/-! ### `thm:RPESM-subextensive-fixed-source`

Rendering (RS.8): the coherently sourced one-site law of the
frame-coordinate Higgs read enters through its expectation functional
`E1` with the saturation bound `‖V‖ ≤ 1` and the RS.7-layer structural
facts: sourced mean `E[V] = m ζ₀` (componentwise, `0 < m ≤ 1` for a
positive one-site source) and diagonal second-moment structure
`C(s) = q∥ P_{ζ₀} + q⊥ P_{ζ₀}^⊥`.  The product law over `M` sites is the
product-expectation interface `IsProductLaw`: every product writer
integrates to the product of one-site expectations — the defining
property of the product measure.  We prove the exact average-orbit
identity (RS.8), the transverse eigenvalue `q⊥/M` on `ζ₀^⊥`, convergence
of the orbit to the nonzero rank-one matrix `m² P_{ζ₀}`, the
oscillation-tilted concentration bounds
`E‖V̄−mζ₀‖² ≤ e^{Δ⋆}M⁻¹` and `λ₂ ≤ 2e^{Δ⋆/2}M^{-1/2}`, and the
subextensive (`osc B_M = o(M)`) limit and concentration through an
exponential Chernoff bound derived from the product interface. -/

section SubextensiveSection

namespace Subextensive

open ExpFun LocalOrbit Filter

variable {S : Type*} (E1 : (S → ℝ) → ℝ)

/-- The product-law interface: the `M`-site functional integrates every
product writer as the product of one-site expectations. -/
def IsProductLaw (EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ) : Prop :=
  (∀ M, IsExpectation (EM M))
  ∧ ∀ (M : ℕ) (f : Fin M → S → ℝ),
      EM M (fun x => ∏ j, f j (x j)) = ∏ j, E1 (f j)

variable {E1}

/-- A one-coordinate writer integrates by the one-site law. -/
theorem prod_single (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {M : ℕ} (k : Fin M) (f : S → ℝ) :
    EM M (fun x => f (x k)) = E1 f := by
  classical
  have h1 := hPL.2 M
    (Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f)
  have hL : (fun x : Fin M → S => ∏ j,
      Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f j (x j))
      = fun x => f (x k) := by
    funext x
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      Function.update_self]
    have hrest : ∏ j ∈ Finset.univ.erase k,
        Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f j (x j)
        = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrest, mul_one]
  have hR : (∏ j, E1
      (Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f j))
      = E1 f := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      Function.update_self]
    have hrest : ∏ j ∈ Finset.univ.erase k,
        E1 (Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f j)
        = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      exact hE1.one
    rw [hrest, mul_one]
  rw [hL] at h1
  rw [h1, hR]

/-- Two distinct-coordinate writers integrate independently. -/
theorem prod_pair (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {M : ℕ} {k l : Fin M} (hkl : k ≠ l) (f g : S → ℝ) :
    EM M (fun x => f (x k) * g (x l)) = E1 f * E1 g := by
  classical
  set F := Function.update
    (Function.update (fun _ : Fin M => fun _ : S => (1 : ℝ)) k f) l g
    with hF
  have hFk : F k = f := by
    rw [hF, Function.update_of_ne hkl, Function.update_self]
  have hFl : F l = g := by
    rw [hF, Function.update_self]
  have hFother : ∀ j, j ≠ k → j ≠ l → F j = fun _ => (1 : ℝ) := by
    intro j hjk hjl
    rw [hF, Function.update_of_ne hjl, Function.update_of_ne hjk]
  have hlk : l ∈ Finset.univ.erase k :=
    Finset.mem_erase.mpr ⟨(Ne.symm hkl), Finset.mem_univ l⟩
  have h1 := hPL.2 M F
  have hL : (fun x : Fin M → S => ∏ j, F j (x j))
      = fun x => f (x k) * g (x l) := by
    funext x
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hFk,
      ← Finset.mul_prod_erase _ _ hlk, hFl]
    have hrest : ∏ j ∈ (Finset.univ.erase k).erase l, F j (x j) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hjl := Finset.ne_of_mem_erase hj
      have hjk := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      rw [hFother j hjk hjl]
    rw [hrest, mul_one]
  have hR : (∏ j, E1 (F j)) = E1 f * E1 g := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hFk,
      ← Finset.mul_prod_erase _ _ hlk, hFl]
    have hrest : ∏ j ∈ (Finset.univ.erase k).erase l, E1 (F j) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hjl := Finset.ne_of_mem_erase hj
      have hjk := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      rw [hFother j hjk hjl]
      exact hE1.one
    rw [hrest, mul_one]
  rw [hL] at h1
  rw [h1, hR]

/-- Complex one-coordinate writers integrate by the one-site law. -/
theorem cExp_single (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {M : ℕ} (k : Fin M) (F : S → ℂ) :
    cExp (EM M) (fun x => F (x k)) = cExp E1 F := by
  refine Complex.ext ?_ ?_
  · show EM M (fun x => (F (x k)).re) = E1 fun ω => (F ω).re
    exact prod_single hE1 hPL k fun ω => (F ω).re
  · show EM M (fun x => (F (x k)).im) = E1 fun ω => (F ω).im
    exact prod_single hE1 hPL k fun ω => (F ω).im

/-- Complex distinct-coordinate writers integrate independently. -/
theorem cExp_pair (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {M : ℕ} {k l : Fin M} (hkl : k ≠ l) (F G : S → ℂ) :
    cExp (EM M) (fun x => F (x k) * G (x l)) = cExp E1 F * cExp E1 G := by
  have hEM := hPL.1 M
  refine Complex.ext ?_ ?_
  · show EM M (fun x => (F (x k) * G (x l)).re)
      = (cExp E1 F * cExp E1 G).re
    calc EM M (fun x => (F (x k) * G (x l)).re)
        = EM M (fun x => (F (x k)).re * (G (x l)).re
            - (F (x k)).im * (G (x l)).im) := by
          rw [show (fun x : Fin M → S => (F (x k) * G (x l)).re)
              = fun x => (F (x k)).re * (G (x l)).re
                - (F (x k)).im * (G (x l)).im from
              funext fun x => Complex.mul_re _ _]
      _ = E1 (fun ω => (F ω).re) * E1 (fun ω => (G ω).re)
          - E1 (fun ω => (F ω).im) * E1 (fun ω => (G ω).im) := by
          rw [hEM.sub,
            prod_pair hE1 hPL hkl (fun ω => (F ω).re) fun ω => (G ω).re,
            prod_pair hE1 hPL hkl (fun ω => (F ω).im) fun ω => (G ω).im]
      _ = (cExp E1 F * cExp E1 G).re :=
          (Complex.mul_re (cExp E1 F) (cExp E1 G)).symm
  · show EM M (fun x => (F (x k) * G (x l)).im)
      = (cExp E1 F * cExp E1 G).im
    calc EM M (fun x => (F (x k) * G (x l)).im)
        = EM M (fun x => (F (x k)).re * (G (x l)).im
            + (F (x k)).im * (G (x l)).re) := by
          rw [show (fun x : Fin M → S => (F (x k) * G (x l)).im)
              = fun x => (F (x k)).re * (G (x l)).im
                + (F (x k)).im * (G (x l)).re from
              funext fun x => Complex.mul_im _ _]
      _ = E1 (fun ω => (F ω).re) * E1 (fun ω => (G ω).im)
          + E1 (fun ω => (F ω).im) * E1 (fun ω => (G ω).re) := by
          rw [hEM.add,
            prod_pair hE1 hPL hkl (fun ω => (F ω).re) fun ω => (G ω).im,
            prod_pair hE1 hPL hkl (fun ω => (F ω).im) fun ω => (G ω).re]
      _ = (cExp E1 F * cExp E1 G).im :=
          (Complex.mul_im (cExp E1 F) (cExp E1 G)).symm

variable {α : Type*}

/-- The orbit Gram of an arbitrary doublet-coordinate read under an
expectation functional. -/
noncomputable def gram2 (Ef : (α → ℝ) → ℝ) (w : α → Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cExp Ef fun a => w a i * (starRingEnd ℂ) (w a j)

/-- The read Gram is Hermitian. -/
theorem gram2_isHermitian {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    (w : α → Fin 2 → ℂ) : (gram2 Ef w).IsHermitian := by
  show (gram2 Ef w)ᴴ = gram2 Ef w
  ext i j
  rw [Matrix.conjTranspose_apply]
  have hre : ∀ a : α, (w a j * (starRingEnd ℂ) (w a i)).re
      = (w a i * (starRingEnd ℂ) (w a j)).re := by
    intro a
    rw [Complex.mul_re, Complex.mul_re]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  have him : ∀ a : α, (w a j * (starRingEnd ℂ) (w a i)).im
      = -(w a i * (starRingEnd ℂ) (w a j)).im := by
    intro a
    rw [Complex.mul_im, Complex.mul_im]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  refine Complex.ext ?_ ?_
  · show Ef (fun a => (w a j * (starRingEnd ℂ) (w a i)).re)
      = Ef fun a => (w a i * (starRingEnd ℂ) (w a j)).re
    rw [show (fun a => (w a j * (starRingEnd ℂ) (w a i)).re)
        = fun a => (w a i * (starRingEnd ℂ) (w a j)).re from funext hre]
  · show -Ef (fun a => (w a j * (starRingEnd ℂ) (w a i)).im)
      = Ef fun a => (w a i * (starRingEnd ℂ) (w a j)).im
    rw [show (fun a => (w a j * (starRingEnd ℂ) (w a i)).im)
        = fun a => -(w a i * (starRingEnd ℂ) (w a j)).im from funext him]
    rw [hE.neg, neg_neg]

/-- The quadratic form of a read Gram is the expected squared directional
read. -/
theorem gram2_form {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    (w : α → Fin 2 → ℂ) (c : Fin 2 → ℂ) :
    star c ⬝ᵥ (gram2 Ef w *ᵥ c)
      = ((Ef (fun a => ‖∑ i, (starRingEnd ℂ) (c i) * w a i‖ ^ 2) : ℝ) : ℂ) := by
  have hlhs : star c ⬝ᵥ (gram2 Ef w *ᵥ c)
      = ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j) * gram2 Ef w i j := by
    unfold dotProduct Matrix.mulVec dotProduct
    rw [Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, Complex.star_def]
    ring
  rw [hlhs]
  have hterm : ∀ i j, ((starRingEnd ℂ) (c i) * c j) * gram2 Ef w i j
      = cExp Ef fun a => ((starRingEnd ℂ) (c i) * c j)
          * (w a i * (starRingEnd ℂ) (w a j)) := by
    intro i j
    rw [cExp_smul hE]
    rfl
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  rw [Finset.sum_congr rfl fun i _ => (cExp_sum hE Finset.univ _).symm,
    (cExp_sum hE Finset.univ _).symm]
  have hpt : ∀ a : α,
      (∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
        * (w a i * (starRingEnd ℂ) (w a j)))
      = ((‖∑ i, (starRingEnd ℂ) (c i) * w a i‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    have hz : (∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
          * (w a i * (starRingEnd ℂ) (w a j)))
        = (∑ i, (starRingEnd ℂ) (c i) * w a i)
          * (starRingEnd ℂ) (∑ j, (starRingEnd ℂ) (c j) * w a j) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_conj]
      ring
    rw [hz, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show (fun a => ∑ i, ∑ j, ((starRingEnd ℂ) (c i) * c j)
      * (w a i * (starRingEnd ℂ) (w a j)))
      = fun a => ((‖∑ i, (starRingEnd ℂ) (c i) * w a i‖ ^ 2 : ℝ) : ℂ)
      from funext hpt]
  exact cExp_ofReal hE _

/-- Rayleigh upper bound: the least eigenvalue is below the quadratic
form of any unit direction. -/
theorem hermLamMin_le_re_form {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.IsHermitian) (x : Fin 2 → ℂ) (hx : ∑ i, ‖x i‖ ^ 2 = 1) :
    hermLamMin hM ≤ (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hfl := hermLamMin_floor hM
  have hform := re_form_nonneg hfl x
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, star_dot_self_eq_sum_sq, hx] at hform
  have hre : ((hermLamMin hM : ℂ) • ((1 : ℝ) : ℂ)).re = hermLamMin hM := by
    rw [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re, mul_one]
  rw [Complex.sub_re, hre] at hform
  linarith

/-- The `M`-site average of the doublet read, in coordinates. -/
noncomputable def vbar (V : S → WH) (M : ℕ) (x : Fin M → S) :
    Fin 2 → ℂ :=
  fun i => (M : ℂ)⁻¹ * ∑ k, V (x k) i

/-- The one-site second-moment matrix `C(s)` of the sourced read. -/
noncomputable def siteC (E1 : (S → ℝ) → ℝ) (V : S → WH) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cExp E1 fun ω => V ω i * (starRingEnd ℂ) (V ω j)

/-- The neutral-ray projector `P_{ζ₀} = ζ₀ ζ₀^*`. -/
noncomputable def pz : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => zeta0 i * (starRingEnd ℂ) (zeta0 j)

/-- The transverse projector `P_{ζ₀}^⊥ = e₀ e₀^*`. -/
noncomputable def pzPerp : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : WH) i
    * (starRingEnd ℂ) ((EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : WH) j)

/-- Coordinates of the neutral direction. -/
theorem zeta0_coord (i : Fin 2) :
    (zeta0 : WH) i = if i = 1 then 1 else 0 := by
  unfold zeta0
  rw [PiLp.single_apply]

/-- Entries of the neutral-ray projector. -/
theorem pz_entries : pz 0 0 = 0 ∧ pz 0 1 = 0 ∧ pz 1 0 = 0 ∧ pz 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold pz
      simp [zeta0_coord]

/-- Coordinates of the transverse direction. -/
theorem e0_coord (i : Fin 2) :
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) : WH) i
      = if i = 0 then 1 else 0 := by
  rw [PiLp.single_apply]

/-- **The exact average second-moment identity** behind (RS.8): for the
product law over `M ≥ 1` sites,
`E[V̄ᵢ V̄ⱼ*] = μᵢ μⱼ* + M⁻¹ (Cᵢⱼ − μᵢ μⱼ*)`. -/
theorem avg_second_moment (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (V : S → WH) {M : ℕ} (hM : 1 ≤ M) (i j : Fin 2) :
    gram2 (EM M) (vbar V M) i j
      = cExp E1 (fun ω => V ω i)
          * (starRingEnd ℂ) (cExp E1 fun ω => V ω j)
        + (M : ℂ)⁻¹ * (siteC E1 V i j
          - cExp E1 (fun ω => V ω i)
            * (starRingEnd ℂ) (cExp E1 fun ω => V ω j)) := by
  classical
  have hEM := hPL.1 M
  have hMne : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
  set μi := cExp E1 fun ω => V ω i with hμi
  set μj := cExp E1 fun ω => V ω j with hμj
  have hpt : ∀ x : Fin M → S,
      vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
      = ((M : ℂ)⁻¹ * (M : ℂ)⁻¹)
        * ∑ k, ∑ l, V (x k) i * (starRingEnd ℂ) (V (x l) j) := by
    intro x
    unfold vbar
    rw [map_mul, map_inv₀, map_natCast, map_sum,
      show ((M : ℂ)⁻¹ * ∑ k, V (x k) i)
          * ((M : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (V (x l) j))
        = ((M : ℂ)⁻¹ * (M : ℂ)⁻¹) * ((∑ k, V (x k) i)
          * ∑ l, (starRingEnd ℂ) (V (x l) j)) from by ring,
      Finset.sum_mul_sum]
  have hcexp : gram2 (EM M) (vbar V M) i j
      = ((M : ℂ)⁻¹ * (M : ℂ)⁻¹) * ∑ k, ∑ l,
          cExp (EM M) fun x => V (x k) i * (starRingEnd ℂ) (V (x l) j) := by
    unfold gram2
    rw [show (fun x => vbar V M x i * (starRingEnd ℂ) (vbar V M x j))
        = fun x => ((M : ℂ)⁻¹ * (M : ℂ)⁻¹)
          * ∑ k, ∑ l, V (x k) i * (starRingEnd ℂ) (V (x l) j) from
        funext hpt, cExp_smul hEM]
    congr 1
    rw [show (fun x : Fin M → S =>
        ∑ k, ∑ l, V (x k) i * (starRingEnd ℂ) (V (x l) j))
        = fun x => ∑ k, (fun x' : Fin M → S =>
          ∑ l, V (x' k) i * (starRingEnd ℂ) (V (x' l) j)) x from rfl,
      cExp_sum hEM]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cExp_sum hEM]
  have hpair : ∀ (k l : Fin M), k ≠ l →
      cExp (EM M) (fun x => V (x k) i * (starRingEnd ℂ) (V (x l) j))
        = μi * (starRingEnd ℂ) μj := by
    intro k l hkl
    have h := cExp_pair hE1 hPL hkl (fun ω => V ω i)
      fun ω => (starRingEnd ℂ) (V ω j)
    rw [cExp_conj hE1] at h
    exact h
  have hdiag : ∀ k : Fin M,
      cExp (EM M) (fun x => V (x k) i * (starRingEnd ℂ) (V (x k) j))
        = siteC E1 V i j := by
    intro k
    exact cExp_single hE1 hPL k fun ω => V ω i * (starRingEnd ℂ) (V ω j)
  have hinner : ∀ k : Fin M,
      (∑ l, cExp (EM M) fun x => V (x k) i * (starRingEnd ℂ) (V (x l) j))
        = siteC E1 V i j + ((M : ℂ) - 1) * (μi * (starRingEnd ℂ) μj) := by
    intro k
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), hdiag k]
    congr 1
    rw [Finset.sum_congr rfl fun l hl =>
      hpair k l (Ne.symm (Finset.ne_of_mem_erase hl)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [Nat.cast_sub hM, Nat.cast_one]
  rw [hcexp, Finset.sum_congr rfl fun k _ => hinner k, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The complex expectation of a constant writer. -/
theorem cExp_const {α : Type*} {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    (z : ℂ) : cExp Ef (fun _ => z) = z := by
  refine Complex.ext ?_ ?_
  · show Ef (fun _ => z.re) = z.re
    exact hE.const _
  · show Ef (fun _ => z.im) = z.im
    exact hE.const _

/-- The complex expectation of a difference. -/
theorem cExp_sub {α : Type*} {Ef : (α → ℝ) → ℝ} (hE : IsExpectation Ef)
    (F G : α → ℂ) :
    cExp Ef (fun a => F a - G a) = cExp Ef F - cExp Ef G := by
  have h1 := cExp_add hE F fun a => -G a
  have h2 : cExp Ef (fun a => -G a) = -cExp Ef G := by
    have h3 := cExp_smul hE (-1) G
    simpa using h3
  rw [h2] at h1
  rw [show (fun a => F a - G a) = fun a => F a + -G a from
    funext fun a => by ring, h1]
  ring

/-- A coordinate of a doublet vector is dominated by its norm. -/
theorem coord_le_norm (w : WH) (i : Fin 2) : ‖w i‖ ≤ ‖w‖ := by
  have h1 : ‖w i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (w i), norm_nonneg w]

/-- Coordinates of a finite sum of doublet vectors. -/
theorem wh_coord_sum {ι : Type*} (s : Finset ι) (w : ι → WH) (i : Fin 2) :
    (∑ k ∈ s, w k) i = ∑ k ∈ s, w k i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl

/-- The average read is bounded by the saturation bound. -/
theorem norm_vbar_le {V : S → WH} (hVb : ∀ ω, ‖V ω‖ ≤ 1) {M : ℕ}
    (hM : 1 ≤ M) (x : Fin M → S) (i : Fin 2) : ‖vbar V M x i‖ ≤ 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  unfold vbar
  rw [norm_mul]
  have h1 : ‖((M : ℂ))⁻¹‖ = (M : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have h2 : ‖∑ k, V (x k) i‖ ≤ (M : ℝ) := by
    calc ‖∑ k : Fin M, V (x k) i‖ ≤ ∑ k : Fin M, ‖V (x k) i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k : Fin M, 1 := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact le_trans (coord_le_norm (V (x k)) i) (hVb (x k))
      _ = (M : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
  rw [h1]
  calc (M : ℝ)⁻¹ * ‖∑ k, V (x k) i‖ ≤ (M : ℝ)⁻¹ * (M : ℝ) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := inv_mul_cancel₀ hMpos.ne'

variable {V : S → WH} {m qpar qperp : ℝ}

/-- Entries of the transverse projector. -/
theorem pzPerp_entries : pzPerp 0 0 = 1 ∧ pzPerp 0 1 = 0
    ∧ pzPerp 1 0 = 0 ∧ pzPerp 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold pzPerp
      simp

/-- **(RS.8)**: the exact product-law average orbit identity
`E[V̄ V̄*] = m² P_{ζ₀} + M⁻¹ (C(s) − m² P_{ζ₀})`. -/
theorem fixed_source_orbit_identity (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) :
    gram2 (EM M) (vbar V M)
      = ((m ^ 2 : ℝ) : ℂ) • pz
        + (M : ℂ)⁻¹ • (siteC E1 V - ((m ^ 2 : ℝ) : ℂ) • pz) := by
  have hmu : ∀ i j : Fin 2,
      cExp E1 (fun ω => V ω i) * (starRingEnd ℂ) (cExp E1 fun ω => V ω j)
        = ((m ^ 2 : ℝ) : ℂ) * pz i j := by
    intro i j
    unfold pz
    fin_cases i <;> fin_cases j
    · show cExp E1 (fun ω => V ω 0) * (starRingEnd ℂ)
          (cExp E1 fun ω => V ω 0)
        = ((m ^ 2 : ℝ) : ℂ) * (zeta0 0 * (starRingEnd ℂ) (zeta0 0))
      rw [hmean0, zeta0_coord]
      simp
    · show cExp E1 (fun ω => V ω 0) * (starRingEnd ℂ)
          (cExp E1 fun ω => V ω 1)
        = ((m ^ 2 : ℝ) : ℂ) * (zeta0 0 * (starRingEnd ℂ) (zeta0 1))
      rw [hmean0, zeta0_coord]
      simp
    · show cExp E1 (fun ω => V ω 1) * (starRingEnd ℂ)
          (cExp E1 fun ω => V ω 0)
        = ((m ^ 2 : ℝ) : ℂ) * (zeta0 1 * (starRingEnd ℂ) (zeta0 0))
      rw [hmean1, hmean0, zeta0_coord 0]
      simp
    · show cExp E1 (fun ω => V ω 1) * (starRingEnd ℂ)
          (cExp E1 fun ω => V ω 1)
        = ((m ^ 2 : ℝ) : ℂ) * (zeta0 1 * (starRingEnd ℂ) (zeta0 1))
      rw [hmean1, zeta0_coord]
      simp [Complex.conj_ofReal]
      ring
  ext i j
  rw [avg_second_moment hE1 hPL V hM i j, hmu i j]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]

/-- **(RS.8, transverse eigenvalue)**: the transverse direction `e₀` is an
eigenvector of the average orbit with eigenvalue `q⊥(s)/M`. -/
theorem transverse_eigenvalue (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    (hC : siteC E1 V
      = ((qpar : ℝ) : ℂ) • pz + ((qperp : ℝ) : ℂ) • pzPerp)
    {M : ℕ} (hM : 1 ≤ M) :
    gram2 (EM M) (vbar V M) *ᵥ Pi.single (0 : Fin 2) (1 : ℂ)
      = ((M : ℂ)⁻¹ * ((qperp : ℝ) : ℂ)) • Pi.single (0 : Fin 2) 1 := by
  have hQ := fixed_source_orbit_identity hE1 hPL hmean0 hmean1 hM
  have hentry : ∀ i : Fin 2, gram2 (EM M) (vbar V M) i 0
      = ((m ^ 2 : ℝ) : ℂ) * pz i 0
        + (M : ℂ)⁻¹ * (((qpar : ℝ) : ℂ) * pz i 0
          + ((qperp : ℝ) : ℂ) * pzPerp i 0 - ((m ^ 2 : ℝ) : ℂ) * pz i 0) := by
    intro i
    have h := congrFun (congrFun hQ i) 0
    rw [hC] at h
    simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul] using h
  have hL0 : (gram2 (EM M) (vbar V M) *ᵥ Pi.single (0 : Fin 2) (1 : ℂ)) 0
      = (M : ℂ)⁻¹ * ((qperp : ℝ) : ℂ) := by
    show gram2 (EM M) (vbar V M) 0 ⬝ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = _
    rw [dotProduct_single, mul_one, hentry 0, pz_entries.1,
      pzPerp_entries.1]
    ring
  have hL1 : (gram2 (EM M) (vbar V M) *ᵥ Pi.single (0 : Fin 2) (1 : ℂ)) 1
      = 0 := by
    show gram2 (EM M) (vbar V M) 1 ⬝ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = _
    rw [dotProduct_single, mul_one, hentry 1, pz_entries.2.2.1,
      pzPerp_entries.2.2.1]
    ring
  have hR0 : (((M : ℂ)⁻¹ * ((qperp : ℝ) : ℂ))
      • Pi.single (0 : Fin 2) (1 : ℂ)) 0
      = (M : ℂ)⁻¹ * ((qperp : ℝ) : ℂ) := by
    simp
  have hR1 : (((M : ℂ)⁻¹ * ((qperp : ℝ) : ℂ))
      • Pi.single (0 : Fin 2) (1 : ℂ)) 1 = 0 := by
    simp
  funext i
  fin_cases i
  · exact hL0.trans hR0.symm
  · exact hL1.trans hR1.symm

/-- **(RS.8, thermodynamic limit)**: the average orbit converges to the
nonzero rank-one matrix `m² P_{ζ₀}`. -/
theorem fixed_source_orbit_limit (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ)) (hm : 0 < m) :
    Filter.Tendsto (fun M => gram2 (EM M) (vbar V M)) Filter.atTop
        (nhds (((m ^ 2 : ℝ) : ℂ) • pz))
      ∧ ((m ^ 2 : ℝ) : ℂ) • pz ≠ 0
      ∧ (((m ^ 2 : ℝ) : ℂ) • pz).rank = 1 := by
  classical
  have hm2 : ((m ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr (by positivity)
  have hdiag : ((m ^ 2 : ℝ) : ℂ) • pz
      = Matrix.diagonal fun i : Fin 2 =>
          if i = 1 then ((m ^ 2 : ℝ) : ℂ) else 0 := by
    have hd : ∀ i j : Fin 2, (((m ^ 2 : ℝ) : ℂ) • pz) i j
        = Matrix.diagonal (fun i : Fin 2 =>
            if i = 1 then ((m ^ 2 : ℝ) : ℂ) else 0) i j := by
      intro i j
      rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
      have hi : i = 0 ∨ i = 1 := by omega
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;>
        subst hj
      · rw [pz_entries.1]
        simp
      · rw [pz_entries.2.1]
        simp
      · rw [pz_entries.2.2.1]
        simp
      · rw [pz_entries.2.2.2]
        simp
    ext i j
    exact hd i j
  refine ⟨?_, ?_, ?_⟩
  · -- entrywise convergence via the exact identity
    rw [show (nhds (((m ^ 2 : ℝ) : ℂ) • pz))
        = nhds (fun i j => (((m ^ 2 : ℝ) : ℂ) • pz) i j) from rfl]
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have hinv : Filter.Tendsto (fun M : ℕ => ((M : ℂ))⁻¹)
        Filter.atTop (nhds 0) := tendsto_inv_atTop_nhds_zero_nat
    have hev : ∀ᶠ M : ℕ in Filter.atTop,
        gram2 (EM M) (vbar V M) i j
          = (((m ^ 2 : ℝ) : ℂ) • pz) i j
            + (M : ℂ)⁻¹ * (siteC E1 V i j
              - (((m ^ 2 : ℝ) : ℂ) • pz) i j) := by
      refine Filter.eventually_atTop.mpr ⟨1, fun M hM => ?_⟩
      rw [fixed_source_orbit_identity hE1 hPL hmean0 hmean1 hM]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul]
    have hlim : Filter.Tendsto (fun M : ℕ =>
        (((m ^ 2 : ℝ) : ℂ) • pz) i j
          + (M : ℂ)⁻¹ * (siteC E1 V i j - (((m ^ 2 : ℝ) : ℂ) • pz) i j))
        Filter.atTop (nhds ((((m ^ 2 : ℝ) : ℂ) • pz) i j)) := by
      have h2 := tendsto_const_nhds
        (x := (((m ^ 2 : ℝ) : ℂ) • pz) i j) (f := Filter.atTop (α := ℕ))
      have h3 := hinv.mul_const
        (siteC E1 V i j - (((m ^ 2 : ℝ) : ℂ) • pz) i j)
      rw [zero_mul] at h3
      simpa using h2.add h3
    exact hlim.congr' (hev.mono fun M hM => hM.symm)
  · rw [hdiag]
    intro hzero
    have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hzero
    simp [Matrix.diagonal] at h1
    exact hm.ne' h1
  · rw [hdiag, Matrix.rank_diagonal]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, by simp [hm.ne']⟩, ?_⟩
    rintro ⟨i, hi⟩
    apply Subtype.ext
    fin_cases i
    · simp at hi
    · rfl

/-- Diagonal entries of a read Gram are expected squared moduli. -/
theorem gram2_diag_re {α : Type*} (Eg : (α → ℝ) → ℝ) (w : α → Fin 2 → ℂ)
    (i : Fin 2) :
    (gram2 Eg w i i).re = Eg fun a => Complex.normSq (w a i) := by
  show Eg (fun a => (w a i * (starRingEnd ℂ) (w a i)).re) = _
  rw [show (fun a => (w a i * (starRingEnd ℂ) (w a i)).re)
      = fun a => Complex.normSq (w a i) from funext fun a => by
        rw [Complex.mul_conj]
        exact Complex.ofReal_re _]

/-- The neutral coordinates. -/
theorem zeta0_zero : (zeta0 : WH) 0 = 0 := by
  simp [zeta0_coord]

/-- The neutral coordinates. -/
theorem zeta0_one : (zeta0 : WH) 1 = 1 := by
  simp [zeta0_coord]

/-- Coordinates of the centered read. -/
theorem vc_coord (V : S → WH) (m : ℝ) (ω : S) (i : Fin 2) :
    ((V ω - (m : ℝ) • zeta0 : WH)) i = V ω i - (m : ℂ) * zeta0 i := by
  have h1 : ((V ω - (m : ℝ) • zeta0 : WH)) i
      = V ω i - ((m : ℝ) • zeta0 : WH) i := rfl
  have h2 : ((m : ℝ) • zeta0 : WH) i = (m : ℝ) • (zeta0 i : ℂ) := rfl
  rw [h1, h2, Complex.real_smul]

/-- The average of the centered read is the centered average. -/
theorem vbar_centered (V : S → WH) (m : ℝ) {M : ℕ} (hM : 1 ≤ M)
    (x : Fin M → S) (i : Fin 2) :
    vbar (fun ω => V ω - (m : ℝ) • zeta0) M x i
      = vbar V M x i - (m : ℂ) * zeta0 i := by
  have hMne : (M : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
  unfold vbar
  rw [Finset.sum_congr rfl fun k _ => vc_coord V m (x k) i,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hMne, one_mul]

variable {V : S → WH} {m : ℝ}

/-- The centered one-site means vanish. -/
theorem centered_mean_zero (hE1 : IsExpectation E1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ)) (i : Fin 2) :
    cExp E1 (fun ω => (V ω - (m : ℝ) • zeta0 : WH) i) = 0 := by
  rw [show (fun ω => (V ω - (m : ℝ) • zeta0 : WH) i)
      = fun ω => V ω i - (m : ℂ) * zeta0 i from
      funext fun ω => vc_coord V m ω i,
    cExp_sub hE1, cExp_const hE1]
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi | hi <;> subst hi
  · rw [hmean0, zeta0_zero]
    ring
  · rw [hmean1, zeta0_one]
    ring

/-- **Product-law deviation moment**: the expected squared deviation of
the average read from its rank-one mean is at most `M⁻¹`. -/
theorem prod_dev_moment (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) :
    EM M (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i)) ≤ (M : ℝ)⁻¹ := by
  have hEM := hPL.1 M
  set Vc : S → WH := fun ω => V ω - (m : ℝ) • zeta0 with hVc
  have hfun : (fun x : Fin M → S => ∑ i,
      Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      = fun x => ∑ i, Complex.normSq (vbar Vc M x i) := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hVc, vbar_centered V m hM x i]
  rw [hfun,
    show (fun x : Fin M → S => ∑ i, Complex.normSq (vbar Vc M x i))
      = fun x => ∑ i, (fun x' : Fin M → S =>
        Complex.normSq (vbar Vc M x' i)) x from rfl,
    hEM.sum]
  have hdiag : ∀ i : Fin 2, EM M (fun x => Complex.normSq (vbar Vc M x i))
      = (M : ℝ)⁻¹ * E1 fun ω => Complex.normSq (Vc ω i) := by
    intro i
    have h1 := gram2_diag_re (EM M) (vbar Vc M) i
    have h2 := avg_second_moment hE1 hPL Vc hM i i
    have hc0 : cExp E1 (fun ω => Vc ω i) = 0 := by
      rw [hVc]
      exact centered_mean_zero hE1 hmean0 hmean1 i
    rw [hc0] at h2
    have h3 : gram2 (EM M) (vbar Vc M) i i
        = (M : ℂ)⁻¹ * siteC E1 Vc i i := by
      rw [h2]
      ring
    have h4 : ((M : ℂ)⁻¹ * siteC E1 Vc i i).re
        = (M : ℝ)⁻¹ * (siteC E1 Vc i i).re := by
      rw [show ((M : ℂ))⁻¹ = (((M : ℝ)⁻¹ : ℝ) : ℂ) from by push_cast; rfl,
        Complex.re_ofReal_mul]
    have h5 : (siteC E1 Vc i i).re = E1 fun ω => Complex.normSq (Vc ω i) :=
      gram2_diag_re E1 (fun ω => (Vc ω : Fin 2 → ℂ)) i
    rw [← h1, h3, h4, h5]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, ← Finset.mul_sum, ← hE1.sum]
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
  refine mul_le_of_le_one_right hMinv ?_
  -- the one-site centered second moment is at most one
  have hexp : ∀ ω, (∑ i, (fun i => fun ω' : S =>
      Complex.normSq (Vc ω' i)) i ω)
      = (∑ i, Complex.normSq (V ω i))
        + (-(2 * m) * (V ω 1).re + m ^ 2 * 1) := by
    intro ω
    rw [show (∑ i, (fun i => fun ω' : S =>
        Complex.normSq (Vc ω' i)) i ω) = ∑ i, Complex.normSq (Vc ω i)
        from rfl]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, hVc, vc_coord, vc_coord,
      zeta0_zero, zeta0_one, mul_zero, sub_zero, mul_one]
    rw [show Complex.normSq (V ω 1 - (m : ℂ))
        = Complex.normSq (V ω 1) - 2 * m * (V ω 1).re + m ^ 2 from by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring]
    ring
  have hsplit : E1 (fun ω => ∑ i, (fun i => fun ω' : S =>
      Complex.normSq (Vc ω' i)) i ω)
      = E1 (fun ω => ∑ i, Complex.normSq (V ω i))
        + (-(2 * m) * E1 (fun ω => (V ω 1).re) + m ^ 2 * 1) := by
    rw [show (fun ω => ∑ i, (fun i => fun ω' : S =>
        Complex.normSq (Vc ω' i)) i ω)
        = fun ω => (∑ i, Complex.normSq (V ω i))
          + (-(2 * m) * (V ω 1).re + m ^ 2 * 1) from funext hexp,
      hE1.add, hE1.add, hE1.smul, hE1.smul, hE1.one]
  have hEm : E1 (fun ω => (V ω 1).re) = m := by
    have h6 : E1 (fun ω => (V ω 1).re)
        = (cExp E1 fun ω => V ω 1).re := rfl
    rw [h6, hmean1, Complex.ofReal_re]
  have hV2 : E1 (fun ω => ∑ i, Complex.normSq (V ω i)) ≤ 1 := by
    have hpt : ∀ ω, (∑ i, Complex.normSq (V ω i)) ≤ 1 := by
      intro ω
      have h7 : (∑ i, Complex.normSq (V ω i)) = ‖V ω‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _
      rw [h7]
      nlinarith [hVb ω, norm_nonneg (V ω)]
    have h8 := hE1.mono _ (fun _ => 1) hpt
    rwa [hE1.one] at h8
  rw [hsplit, hEm]
  nlinarith [sq_nonneg m]

/-- **`thm:RPESM-subextensive-fixed-source`, bounded-oscillation tilt**:
under any interaction tilt of oscillation at most `Δ⋆`, the conditioned
squared deviation obeys `E‖V̄ − mζ₀‖² ≤ e^{Δ⋆} M⁻¹`. -/
theorem tilted_dev_moment (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) {Bt : (Fin M → S) → ℝ} {lo Δ : ℝ}
    (hBt : ∀ x, lo ≤ Bt x ∧ Bt x ≤ lo + Δ) :
    gibbs (EM M) Bt (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ Real.exp Δ * (M : ℝ)⁻¹ := by
  have h1 := gibbs_le (hPL.1 M) hBt
    (f := fun x => ∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
    fun x => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 := prod_dev_moment hE1 hPL hVb hmean0 hmean1 hM
  calc gibbs (EM M) Bt (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ Real.exp (lo + Δ - lo) * EM M (fun x => ∑ i,
          Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i)) := h1
    _ = Real.exp Δ * EM M (fun x => ∑ i,
          Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i)) := by
        rw [show lo + Δ - lo = Δ by ring]
    _ ≤ Real.exp Δ * (M : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos Δ).le

/-- **`thm:RPESM-subextensive-fixed-source`, tilted second eigenvalue**:
under any interaction tilt of oscillation at most `Δ⋆`, the second orbit
eigenvalue is at most `2 e^{Δ⋆/2} M^{-1/2}`. -/
theorem tilted_lam2_bound (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) {Bt : (Fin M → S) → ℝ} {lo Δ : ℝ}
    (hBt : ∀ x, lo ≤ Bt x ∧ Bt x ≤ lo + Δ) :
    lam2 (gram2 (gibbs (EM M) Bt) (vbar V M))
      ≤ 2 * Real.exp (Δ / 2) / Real.sqrt M := by
  have hG := gibbs_isExpectation (hPL.1 M) hBt
  have hherm := gram2_isHermitian hG (vbar V M)
  rw [lam2_eq hherm]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hsq : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hMs : Real.sqrt M * Real.sqrt M = (M : ℝ) :=
    Real.mul_self_sqrt hMpos.le
  -- the Rayleigh value in the transverse direction
  set e0v : Fin 2 → ℂ := Pi.single (0 : Fin 2) (1 : ℂ) with he0v
  have hunit : ∑ i, ‖e0v i‖ ^ 2 = 1 := by
    rw [he0v, Fin.sum_univ_two]
    simp
  have hray := hermLamMin_le_re_form hherm e0v hunit
  have hsum0 : ∀ x : Fin M → S,
      (∑ i, (starRingEnd ℂ) (e0v i) * vbar V M x i) = vbar V M x 0 := by
    intro x
    rw [he0v, Fin.sum_univ_two]
    simp
  have hformval : (star e0v
      ⬝ᵥ (gram2 (gibbs (EM M) Bt) (vbar V M) *ᵥ e0v)).re
      = gibbs (EM M) Bt fun x => ‖vbar V M x 0‖ ^ 2 := by
    rw [gram2_form hG (vbar V M) e0v,
      show (fun x => ‖∑ i, (starRingEnd ℂ) (e0v i) * vbar V M x i‖ ^ 2)
        = fun x => ‖vbar V M x 0‖ ^ 2 from
        funext fun x => by rw [hsum0 x]]
    exact Complex.ofReal_re _
  rw [hformval] at hray
  -- the Rayleigh value is dominated by the tilted deviation moment
  have hdom : gibbs (EM M) Bt (fun x => ‖vbar V M x 0‖ ^ 2)
      ≤ Real.exp Δ * (M : ℝ)⁻¹ := by
    have hmono := hG.mono (fun x => ‖vbar V M x 0‖ ^ 2)
      (fun x => ∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      fun x => by
        have h1 : ‖vbar V M x 0‖ ^ 2
            = Complex.normSq (vbar V M x 0 - (m : ℂ) * zeta0 0) := by
          rw [zeta0_zero, mul_zero, sub_zero, Complex.normSq_eq_norm_sq]
        rw [h1]
        exact Finset.single_le_sum
          (f := fun i => Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
          (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ (0 : Fin 2))
    exact hmono.trans (tilted_dev_moment hE1 hPL hVb hmean0 hmean1 hM hBt)
  have hone : gibbs (EM M) Bt (fun x => ‖vbar V M x 0‖ ^ 2) ≤ 1 := by
    have hmono := hG.mono (fun x => ‖vbar V M x 0‖ ^ 2) (fun _ => 1)
      fun x => by
        have h1 := norm_vbar_le hVb hM x 0
        nlinarith [norm_nonneg (vbar V M x 0)]
    rwa [hG.one] at hmono
  set lam := hermLamMin hherm with hlam
  set E := Real.exp (Δ / 2) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hexpsq : E * E = Real.exp Δ := by
    rw [hEdef, ← Real.exp_add]
    congr 1
    ring
  rcases le_or_gt E (2 * Real.sqrt M) with hle | hgt
  · have hlamM : lam * (M : ℝ) ≤ E * E := by
      have h2 : lam ≤ Real.exp Δ * (M : ℝ)⁻¹ := le_trans hray hdom
      have h3 := mul_le_mul_of_nonneg_right h2 hMpos.le
      rw [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one, ← hexpsq] at h3
      exact h3
    rw [le_div_iff₀ hsq]
    have h9 : 0 ≤ (2 * E - lam * Real.sqrt M) * Real.sqrt M := by
      nlinarith
    nlinarith [h9]
  · rw [le_div_iff₀ hsq]
    have hlam1 : lam ≤ 1 := le_trans hray hone
    nlinarith

/-- Quadratic upper bound on the exponential in the unit window. -/
theorem exp_le_one_add_add_sq {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t ≤ 1 + t + t ^ 2 := by
  have h := Real.exp_bound ht (by norm_num : 0 < 2)
  have hsum : (∑ i ∈ Finset.range 2, t ^ i / (Nat.factorial i)) = 1 + t := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at h
  have h2 := (abs_le.mp h).2
  have h3 : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [h3] at h2
  norm_num [Nat.factorial] at h2
  nlinarith [sq_nonneg t]

/-- One-site moment-generating bound for a centered read bounded by two. -/
theorem site_mgf_bound (hE1 : IsExpectation E1) {Y : S → ℝ}
    (hYb : ∀ ω, |Y ω| ≤ 2) (hY0 : E1 Y = 0) {l : ℝ} (hl : |l| ≤ 1 / 2) :
    E1 (fun ω => Real.exp (l * Y ω)) ≤ Real.exp (4 * l ^ 2) := by
  have hpt : ∀ ω, Real.exp (l * Y ω)
      ≤ (1 + 4 * l ^ 2) * 1 + l * Y ω := by
    intro ω
    have h1 : |l * Y ω| ≤ 1 := by
      rw [abs_mul]
      calc |l| * |Y ω| ≤ (1 / 2) * 2 :=
            mul_le_mul hl (hYb ω) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h2 := exp_le_one_add_add_sq h1
    have h3 : (l * Y ω) ^ 2 ≤ 4 * l ^ 2 := by
      have h4 := hYb ω
      have h5 := abs_nonneg (Y ω)
      have h6 : (Y ω) ^ 2 ≤ 4 := by
        have := sq_abs (Y ω)
        nlinarith
      nlinarith [sq_nonneg l]
    nlinarith
  have hmono := hE1.mono _ _ hpt
  have hlin : E1 (fun ω => (1 + 4 * l ^ 2) * 1 + l * Y ω)
      = 1 + 4 * l ^ 2 := by
    rw [show (fun ω => (1 + 4 * l ^ 2) * 1 + l * Y ω)
        = fun ω => (1 + 4 * l ^ 2) * 1 + l * Y ω from rfl, hE1.add,
      hE1.smul, hE1.smul, hE1.one, hY0]
    ring
  rw [hlin] at hmono
  calc E1 (fun ω => Real.exp (l * Y ω)) ≤ 1 + 4 * l ^ 2 := hmono
    _ ≤ Real.exp (4 * l ^ 2) := by
        have := Real.add_one_le_exp (4 * l ^ 2)
        linarith

/-- Product moment-generating factorization over the sites. -/
theorem prod_mgf (_hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {M : ℕ} (Y : S → ℝ) (l : ℝ) :
    EM M (fun x => Real.exp (l * ∑ k, Y (x k)))
      = (E1 fun ω => Real.exp (l * Y ω)) ^ M := by
  have h1 := hPL.2 M fun _ => fun ω => Real.exp (l * Y ω)
  have hL : (fun x : Fin M → S =>
      ∏ j, (fun _ : Fin M => fun ω => Real.exp (l * Y ω)) j (x j))
      = fun x => Real.exp (l * ∑ k, Y (x k)) := by
    funext x
    rw [Finset.mul_sum, Real.exp_sum]
  have hR : (∏ _j : Fin M, E1 fun ω => Real.exp (l * Y ω))
      = (E1 fun ω => Real.exp (l * Y ω)) ^ M := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hL] at h1
  rw [h1, hR]

/-- **Chernoff tail bound** for the product law: a one-sided
site-sum indicator has exponentially small expectation. -/
theorem chernoff_indicator (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    {Y : S → ℝ} (hYb : ∀ ω, |Y ω| ≤ 2) (hY0 : E1 Y = 0)
    {M : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε4 : ε ≤ 4) :
    EM M (fun x => if (M : ℝ) * ε ≤ ∑ k, Y (x k) then (1 : ℝ) else 0)
      ≤ Real.exp (-((M : ℝ) * ε ^ 2 / 16)) := by
  classical
  have hEM := hPL.1 M
  set l : ℝ := ε / 8 with hldef
  have hl : |l| ≤ 1 / 2 := by
    rw [hldef, abs_of_pos (by positivity)]
    linarith
  have hpt : ∀ x : Fin M → S,
      (if (M : ℝ) * ε ≤ ∑ k, Y (x k) then (1 : ℝ) else 0)
        ≤ Real.exp (-(l * ((M : ℝ) * ε))) * Real.exp (l * ∑ k, Y (x k)) := by
    intro x
    rw [← Real.exp_add]
    split_ifs with hc
    · have h1 : 0 ≤ -(l * ((M : ℝ) * ε)) + l * ∑ k, Y (x k) := by
        have h2 : l * ((M : ℝ) * ε) ≤ l * ∑ k, Y (x k) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        linarith
      have := Real.add_one_le_exp (-(l * ((M : ℝ) * ε)) + l * ∑ k, Y (x k))
      linarith
    · exact (Real.exp_pos _).le
  have hmono := hEM.mono _ _ hpt
  have hsplit : EM M (fun x => Real.exp (-(l * ((M : ℝ) * ε)))
      * Real.exp (l * ∑ k, Y (x k)))
      = Real.exp (-(l * ((M : ℝ) * ε)))
        * (E1 fun ω => Real.exp (l * Y ω)) ^ M := by
    rw [hEM.smul, prod_mgf hE1 hPL Y l]
  rw [hsplit] at hmono
  have hmgf := site_mgf_bound hE1 hYb hY0 hl
  have hmgfnn : 0 ≤ E1 fun ω => Real.exp (l * Y ω) :=
    hE1.nonneg fun ω => (Real.exp_pos _).le
  have hpow : (E1 fun ω => Real.exp (l * Y ω)) ^ M
      ≤ Real.exp (4 * l ^ 2) ^ M := pow_le_pow_left₀ hmgfnn hmgf M
  have hexp : Real.exp (-(l * ((M : ℝ) * ε))) * Real.exp (4 * l ^ 2) ^ M
      = Real.exp (-((M : ℝ) * ε ^ 2 / 16)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hldef]
    ring
  calc EM M (fun x => if (M : ℝ) * ε ≤ ∑ k, Y (x k) then (1 : ℝ) else 0)
      ≤ Real.exp (-(l * ((M : ℝ) * ε)))
        * (E1 fun ω => Real.exp (l * Y ω)) ^ M := hmono
    _ ≤ Real.exp (-(l * ((M : ℝ) * ε))) * Real.exp (4 * l ^ 2) ^ M :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-((M : ℝ) * ε ^ 2 / 16)) := hexp

/-- The absolute mean bound `|E[f]| ≤ E[|f|]`. -/
theorem abs_expect_le {α : Type*} {Ef : (α → ℝ) → ℝ}
    (hE : IsExpectation Ef) (f : α → ℝ) :
    |Ef f| ≤ Ef fun a => |f a| := by
  have h1 := hE.mono f (fun a => |f a|) fun a => le_abs_self _
  have h2 := hE.mono (fun a => -|f a|) f fun a => neg_abs_le _
  have h3 := hE.neg fun a => |f a|
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- The complex expectation is dominated by twice the expected modulus. -/
theorem cExp_norm_le {α : Type*} {Ef : (α → ℝ) → ℝ}
    (hE : IsExpectation Ef) (F : α → ℂ) :
    ‖cExp Ef F‖ ≤ 2 * Ef fun a => ‖F a‖ := by
  have hre : |Ef fun a => (F a).re| ≤ Ef fun a => ‖F a‖ := by
    refine le_trans (abs_expect_le hE _) (hE.mono _ _ fun a => ?_)
    exact Complex.abs_re_le_norm _
  have him : |Ef fun a => (F a).im| ≤ Ef fun a => ‖F a‖ := by
    refine le_trans (abs_expect_le hE _) (hE.mono _ _ fun a => ?_)
    exact Complex.abs_im_le_norm _
  have hEnn : 0 ≤ Ef fun a => ‖F a‖ := hE.nonneg fun a => norm_nonneg _
  have hsq : ‖cExp Ef F‖ ^ 2
      = (Ef fun a => (F a).re) ^ 2 + (Ef fun a => (F a).im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    show Complex.normSq ⟨_, _⟩ = _
    rw [Complex.normSq_mk]
    ring
  nlinarith [norm_nonneg (cExp Ef F), sq_abs (Ef fun a => (F a).re),
    sq_abs (Ef fun a => (F a).im),
    mul_self_le_mul_self (abs_nonneg (Ef fun a => (F a).re)) hre,
    mul_self_le_mul_self (abs_nonneg (Ef fun a => (F a).im)) him]

/-- The sourced mean amplitude is bounded by one. -/
theorem abs_mean_le_one (hE1 : IsExpectation E1) (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ)) : |m| ≤ 1 := by
  have hm : E1 (fun ω => (V ω 1).re) = m := by
    have h6 : E1 (fun ω => (V ω 1).re) = (cExp E1 fun ω => V ω 1).re := rfl
    rw [h6, hmean1, Complex.ofReal_re]
  rw [← hm]
  refine hE1.abs_le fun ω => ?_
  calc |(V ω 1).re| ≤ ‖V ω 1‖ := Complex.abs_re_le_norm _
    _ ≤ ‖V ω‖ := coord_le_norm _ _
    _ ≤ 1 := hVb ω

/-- The four real component reads of the centered doublet read. -/
noncomputable def yComp (V : S → WH) (m : ℝ) (i : Fin 2) (b : Bool) :
    S → ℝ :=
  fun ω => if b then ((V ω - (m : ℝ) • zeta0 : WH) i).re
    else ((V ω - (m : ℝ) • zeta0 : WH) i).im

/-- The component reads are centered. -/
theorem yComp_mean_zero (hE1 : IsExpectation E1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ)) (i : Fin 2) (b : Bool) :
    E1 (yComp V m i b) = 0 := by
  have hc := centered_mean_zero hE1 hmean0 hmean1 i
  cases b
  · show E1 (fun ω => ((V ω - (m : ℝ) • zeta0 : WH) i).im) = 0
    have h1 : E1 (fun ω => ((V ω - (m : ℝ) • zeta0 : WH) i).im)
        = (cExp E1 fun ω => (V ω - (m : ℝ) • zeta0 : WH) i).im := rfl
    rw [h1, hc]
    rfl
  · show E1 (fun ω => ((V ω - (m : ℝ) • zeta0 : WH) i).re) = 0
    have h1 : E1 (fun ω => ((V ω - (m : ℝ) • zeta0 : WH) i).re)
        = (cExp E1 fun ω => (V ω - (m : ℝ) • zeta0 : WH) i).re := rfl
    rw [h1, hc]
    rfl

/-- The component reads are bounded by two. -/
theorem yComp_abs_le (hVb : ∀ ω, ‖V ω‖ ≤ 1) (hmabs : |m| ≤ 1)
    (i : Fin 2) (b : Bool) (ω : S) : |yComp V m i b ω| ≤ 2 := by
  have hvc : ‖(V ω - (m : ℝ) • zeta0 : WH)‖ ≤ 2 := by
    calc ‖(V ω - (m : ℝ) • zeta0 : WH)‖
        ≤ ‖V ω‖ + ‖((m : ℝ) • zeta0 : WH)‖ := norm_sub_le _ _
      _ ≤ 1 + |m| * 1 := by
          rw [norm_smul, Real.norm_eq_abs, norm_zeta0]
          exact add_le_add (hVb ω) le_rfl
      _ ≤ 2 := by linarith
  have hcoord := coord_le_norm (V ω - (m : ℝ) • zeta0 : WH) i
  unfold yComp
  cases b
  · show |((V ω - (m : ℝ) • zeta0 : WH) i).im| ≤ 2
    calc |((V ω - (m : ℝ) • zeta0 : WH) i).im|
        ≤ ‖(V ω - (m : ℝ) • zeta0 : WH) i‖ := Complex.abs_im_le_norm _
      _ ≤ 2 := le_trans hcoord hvc
  · show |((V ω - (m : ℝ) • zeta0 : WH) i).re| ≤ 2
    calc |((V ω - (m : ℝ) • zeta0 : WH) i).re|
        ≤ ‖(V ω - (m : ℝ) • zeta0 : WH) i‖ := Complex.abs_re_le_norm _
      _ ≤ 2 := le_trans hcoord hvc

/-- The deviation components are site averages of the component reads. -/
theorem dev_component (V : S → WH) (m : ℝ) {M : ℕ} (hM : 1 ≤ M)
    (x : Fin M → S) (i : Fin 2) :
    (vbar V M x i - (m : ℂ) * zeta0 i).re
        = (M : ℝ)⁻¹ * ∑ k, yComp V m i true (x k)
      ∧ (vbar V M x i - (m : ℂ) * zeta0 i).im
        = (M : ℝ)⁻¹ * ∑ k, yComp V m i false (x k) := by
  have h1 : vbar V M x i - (m : ℂ) * zeta0 i
      = (M : ℂ)⁻¹ * ∑ k, (V (x k) - (m : ℝ) • zeta0 : WH) i := by
    rw [← vbar_centered V m hM x i]
    rfl
  have hcast : ((M : ℂ))⁻¹ = (((M : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  constructor
  · rw [h1, hcast, Complex.re_ofReal_mul, Complex.re_sum]
    rfl
  · rw [h1, hcast, Complex.im_ofReal_mul, Complex.im_sum]
    rfl

/-- The squared deviation is the sum of the four squared component
averages. -/
theorem fdev_component_split (V : S → WH) (m : ℝ) {M : ℕ} (hM : 1 ≤ M)
    (x : Fin M → S) :
    (∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      = ∑ p : Fin 2 × Bool,
          ((M : ℝ)⁻¹ * ∑ k, yComp V m p.1 p.2 (x k)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, ← (dev_component V m hM x i).1,
    ← (dev_component V m hM x i).2, Complex.normSq_apply]
  ring

/-- The squared deviation is bounded by four. -/
theorem fdev_le_four (hVb : ∀ ω, ‖V ω‖ ≤ 1) (hmabs : |m| ≤ 1) {M : ℕ}
    (hM : 1 ≤ M) (x : Fin M → S) :
    (∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i)) ≤ 4 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  set wavg : WH := (M : ℝ)⁻¹ • ∑ k, V (x k) with hwavg
  set dv : WH := wavg - (m : ℝ) • zeta0 with hdv
  have hwcoord : ∀ i, (wavg : WH) i = vbar V M x i := by
    intro i
    have h1 : (wavg : WH) i = (M : ℝ)⁻¹ • ((∑ k, V (x k) : WH) i) := rfl
    rw [h1, Complex.real_smul, wh_coord_sum]
    unfold vbar
    push_cast
    rfl
  have hcoord : ∀ i, (dv : WH) i = vbar V M x i - (m : ℂ) * zeta0 i := by
    intro i
    have h1 : (dv : WH) i = wavg i - ((m : ℝ) • zeta0 : WH) i := rfl
    have h2 : ((m : ℝ) • zeta0 : WH) i = (m : ℝ) • (zeta0 i : ℂ) := rfl
    rw [h1, h2, Complex.real_smul, hwcoord i]
  have hsum : (∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      = ‖dv‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcoord i, Complex.normSq_eq_norm_sq]
  have hwnorm : ‖wavg‖ ≤ 1 := by
    rw [hwavg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos)]
    have h3 : ‖∑ k, V (x k)‖ ≤ (M : ℝ) := by
      calc ‖∑ k : Fin M, V (x k)‖ ≤ ∑ k : Fin M, ‖V (x k)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k : Fin M, 1 := Finset.sum_le_sum fun k _ => hVb (x k)
        _ = (M : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
    calc (M : ℝ)⁻¹ * ‖∑ k, V (x k)‖ ≤ (M : ℝ)⁻¹ * (M : ℝ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 := inv_mul_cancel₀ hMpos.ne'
  have hdev : ‖dv‖ ≤ 2 := by
    have hz : ‖((m : ℝ) • zeta0 : WH)‖ = |m| := by
      rw [norm_smul, Real.norm_eq_abs, norm_zeta0, mul_one]
    calc ‖dv‖ ≤ ‖wavg‖ + ‖((m : ℝ) • zeta0 : WH)‖ := norm_sub_le _ _
      _ ≤ 2 := by
          rw [hz]
          linarith
  rw [hsum]
  nlinarith [norm_nonneg dv]

/-- **The pointwise indicator decomposition** of the squared deviation:
either the deviation is below the threshold or one of the eight
one-sided component tail events occurs. -/
theorem fdev_indicator_bound (hVb : ∀ ω, ‖V ω‖ ≤ 1) (hmabs : |m| ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) (x : Fin M → S) :
    (∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ ε ^ 2 + 4 * ∑ p : Fin 2 × Bool,
          ((if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
              then (1 : ℝ) else 0)
            + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
              then (1 : ℝ) else 0)) := by
  classical
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hpairnn : ∀ p : Fin 2 × Bool, (0 : ℝ)
      ≤ (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)
        + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0) := by
    intro p
    have h1 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
        ≤ ∑ k, yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
        ≤ ∑ k, -yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    linarith
  have hsumnn : (0 : ℝ) ≤ ∑ p : Fin 2 × Bool,
      ((if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)
        + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)) :=
    Finset.sum_nonneg fun p _ => hpairnn p
  rcases le_or_gt (∑ i, Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      (ε ^ 2) with hle | hgt
  · linarith
  · have hsplit := fdev_component_split V m hM x
    have hex : ∃ p : Fin 2 × Bool, (ε / 2) ^ 2
        < ((M : ℝ)⁻¹ * ∑ k, yComp V m p.1 p.2 (x k)) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hall := Finset.sum_le_sum
        (fun (p : Fin 2 × Bool) (_ : p ∈ Finset.univ) => hcon p)
      rw [Finset.sum_const, Finset.card_univ,
        show Fintype.card (Fin 2 × Bool) = 4 from rfl, nsmul_eq_mul] at hall
      rw [hsplit] at hgt
      nlinarith
    obtain ⟨p, hp⟩ := hex
    set T := ∑ k, yComp V m p.1 p.2 (x k) with hT
    have habs : (M : ℝ) * (ε / 2) < |T| := by
      have h4 : ε / 2 < |(M : ℝ)⁻¹ * T| := by
        by_contra hcon2
        push Not at hcon2
        nlinarith [sq_abs ((M : ℝ)⁻¹ * T), abs_nonneg ((M : ℝ)⁻¹ * T)]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hMpos)] at h4
      have h5 := mul_lt_mul_of_pos_left h4 hMpos
      rwa [← mul_assoc, mul_inv_cancel₀ hMpos.ne', one_mul] at h5
    have hone : (1 : ℝ)
        ≤ (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0)
          + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0) := by
      have hTneg : (∑ k, -yComp V m p.1 p.2 (x k)) = -T := by
        rw [hT, ← Finset.sum_neg_distrib]
      rcases lt_abs.mp habs with h6 | h6
      · have hc1 : (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k) := by
          rw [← hT]
          exact h6.le
        have h7 : (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0) = 1 := by simp [hc1]
        have h8 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
            ≤ ∑ k, -yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        rw [h7]
        linarith
      · have h7 : (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0) = 1 := by
          rw [hTneg]
          simp [h6.le]
        have h8 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
            ≤ ∑ k, yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        rw [h7]
        linarith
    have hD4 := fdev_le_four hVb hmabs hM x
    have hsumge := Finset.single_le_sum (fun p' _ => hpairnn p')
      (Finset.mem_univ p)
    nlinarith [sq_nonneg ε]

/-- **Subextensive tilted deviation bound**: under an interaction tilt of
oscillation `Δ`, for every threshold `0 < ε ≤ 2` the conditioned squared
deviation obeys `E‖V̄−mζ₀‖² ≤ ε² + 32 e^{Δ − M(ε/2)²/16}`. -/
theorem subextensive_dev_bound (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) {Bt : (Fin M → S) → ℝ} {lo Δ : ℝ}
    (hBt : ∀ x, lo ≤ Bt x ∧ Bt x ≤ lo + Δ)
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 2) :
    gibbs (EM M) Bt (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ ε ^ 2 + 32 * Real.exp (Δ - (M : ℝ) * (ε / 2) ^ 2 / 16) := by
  classical
  have hEM := hPL.1 M
  have hG := gibbs_isExpectation hEM hBt
  have hmabs := abs_mean_le_one hE1 hVb hmean1
  set Gsum : (Fin M → S) → ℝ := fun x => ∑ p : Fin 2 × Bool,
      ((if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)
        + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)) with hGsum
  have hGnn : ∀ x, 0 ≤ Gsum x := by
    intro x
    refine Finset.sum_nonneg fun p _ => ?_
    have h1 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
        ≤ ∑ k, yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if (M : ℝ) * (ε / 2)
        ≤ ∑ k, -yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    linarith
  have hmono := hG.mono _ (fun x => ε ^ 2 + 4 * Gsum x)
    fun x => fdev_indicator_bound hVb hmabs hM hε0 x
  have hlin : gibbs (EM M) Bt (fun x => ε ^ 2 + 4 * Gsum x)
      = ε ^ 2 + 4 * gibbs (EM M) Bt Gsum := by
    have h1 := hG.add (fun _ => ε ^ 2) fun x => 4 * Gsum x
    have h2 := hG.smul 4 Gsum
    have h3 := hG.const (ε ^ 2)
    rw [h3, h2] at h1
    exact h1
  have hEsum : EM M Gsum ≤ 8 * Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) := by
    have hper : ∀ p : Fin 2 × Bool,
        EM M (fun x =>
          (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0)
          + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0))
        ≤ 2 * Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) := by
      intro p
      have hadd := hEM.add
        (fun x => if (M : ℝ) * (ε / 2)
          ≤ ∑ k, yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0)
        (fun x => if (M : ℝ) * (ε / 2)
          ≤ ∑ k, -yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0)
      have hc1 : EM M (fun x => if (M : ℝ) * (ε / 2)
          ≤ ∑ k, yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0)
          ≤ Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) := by
        have h4 := chernoff_indicator hE1 hPL
          (Y := yComp V m p.1 p.2) (yComp_abs_le hVb hmabs p.1 p.2)
          (yComp_mean_zero hE1 hmean0 hmean1 p.1 p.2)
          (M := M) (ε := ε / 2) (by positivity) (by linarith)
        exact h4
      have hc2 : EM M (fun x => if (M : ℝ) * (ε / 2)
          ≤ ∑ k, -yComp V m p.1 p.2 (x k) then (1 : ℝ) else 0)
          ≤ Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) := by
        have hYb' : ∀ ω, |(fun ω' => -yComp V m p.1 p.2 ω') ω| ≤ 2 := by
          intro ω
          rw [abs_neg]
          exact yComp_abs_le hVb hmabs p.1 p.2 ω
        have hY0' : E1 (fun ω => -yComp V m p.1 p.2 ω) = 0 := by
          rw [hE1.neg, yComp_mean_zero hE1 hmean0 hmean1 p.1 p.2, neg_zero]
        have h4 := chernoff_indicator hE1 hPL
          (Y := fun ω => -yComp V m p.1 p.2 ω) hYb' hY0'
          (M := M) (ε := ε / 2) (by positivity) (by linarith)
        exact h4
      rw [hadd]
      linarith
    have hsum := hEM.sum Finset.univ fun p : Fin 2 × Bool =>
      fun x =>
        (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)
        + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
          then (1 : ℝ) else 0)
    rw [hGsum]
    rw [show Gsum = fun x => ∑ p : Fin 2 × Bool,
        ((if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0)
          + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0)) from hGsum] at *
    rw [hsum]
    calc (∑ p : Fin 2 × Bool, EM M fun x =>
          (if (M : ℝ) * (ε / 2) ≤ ∑ k, yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0)
          + (if (M : ℝ) * (ε / 2) ≤ ∑ k, -yComp V m p.1 p.2 (x k)
            then (1 : ℝ) else 0))
        ≤ ∑ _p : Fin 2 × Bool,
            2 * Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) :=
          Finset.sum_le_sum fun p _ => hper p
      _ = 8 * Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)) := by
          rw [Finset.sum_const, Finset.card_univ,
            show Fintype.card (Fin 2 × Bool) = 4 from rfl, nsmul_eq_mul]
          ring
  have hup := gibbs_le hEM hBt (f := Gsum) hGnn
  calc gibbs (EM M) Bt (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ gibbs (EM M) Bt (fun x => ε ^ 2 + 4 * Gsum x) := hmono
    _ = ε ^ 2 + 4 * gibbs (EM M) Bt Gsum := hlin
    _ ≤ ε ^ 2 + 4 * (Real.exp (lo + Δ - lo) * EM M Gsum) := by
        have h5 := hup
        have h6 : 0 ≤ Real.exp (lo + Δ - lo) := (Real.exp_pos _).le
        nlinarith [hEM.nonneg hGnn, Real.exp_pos (lo + Δ - lo)]
    _ ≤ ε ^ 2 + 4 * (Real.exp Δ
          * (8 * Real.exp (-((M : ℝ) * (ε / 2) ^ 2 / 16)))) := by
        rw [show lo + Δ - lo = Δ by ring]
        have h7 := mul_le_mul_of_nonneg_left hEsum (Real.exp_pos Δ).le
        linarith
    _ = ε ^ 2 + 32 * Real.exp (Δ - (M : ℝ) * (ε / 2) ^ 2 / 16) := by
        rw [show Δ - (M : ℝ) * (ε / 2) ^ 2 / 16
            = Δ + -((M : ℝ) * (ε / 2) ^ 2 / 16) by ring, Real.exp_add]
        ring

/-- Norm of the neutral coordinates. -/
theorem norm_zeta0_coord_le (i : Fin 2) : ‖(zeta0 : WH) i‖ ≤ 1 := by
  rw [zeta0_coord]
  split_ifs <;> norm_num

/-- **Entry deviation of the tilted orbit Gram** from the rank-one mean:
every entry lies within `4√(E‖V̄−mζ₀‖²)` of `m² P_{ζ₀}`. -/
theorem tilted_entry_dev (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    {M : ℕ} (hM : 1 ≤ M) {Bt : (Fin M → S) → ℝ} {lo Δ : ℝ}
    (hBt : ∀ x, lo ≤ Bt x ∧ Bt x ≤ lo + Δ) (i j : Fin 2) :
    ‖gram2 (gibbs (EM M) Bt) (vbar V M) i j - ((m ^ 2 : ℝ) : ℂ) * pz i j‖
      ≤ 4 * Real.sqrt (gibbs (EM M) Bt fun x => ∑ i',
          Complex.normSq (vbar V M x i' - (m : ℂ) * zeta0 i')) := by
  have hEM := hPL.1 M
  have hG := gibbs_isExpectation hEM hBt
  have hmabs := abs_mean_le_one hE1 hVb hmean1
  have htarget : ((m ^ 2 : ℝ) : ℂ) * pz i j
      = ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j) := by
    unfold pz
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hdiff : gram2 (gibbs (EM M) Bt) (vbar V M) i j
        - ((m ^ 2 : ℝ) : ℂ) * pz i j
      = cExp (gibbs (EM M) Bt) fun x =>
          vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
            - ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j) := by
    rw [htarget, cExp_sub hG, cExp_const hG]
    rfl
  have hpt : ∀ x : Fin M → S,
      ‖vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
        - ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j)‖
      ≤ ‖vbar V M x i - (m : ℂ) * zeta0 i‖
        + ‖vbar V M x j - (m : ℂ) * zeta0 j‖ := by
    intro x
    have hexp : vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
        - ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j)
        = (vbar V M x i - (m : ℂ) * zeta0 i)
            * (starRingEnd ℂ) (vbar V M x j)
          + ((m : ℂ) * zeta0 i) * (starRingEnd ℂ)
            (vbar V M x j - (m : ℂ) * zeta0 j) := by
      rw [map_sub]
      ring
    rw [hexp]
    have hvb : ‖(starRingEnd ℂ) (vbar V M x j)‖ ≤ 1 := by
      rw [RCLike.norm_conj]
      exact norm_vbar_le hVb hM x j
    have hmz : ‖(m : ℂ) * zeta0 i‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |m| * ‖(zeta0 : WH) i‖ ≤ 1 * 1 :=
            mul_le_mul hmabs (norm_zeta0_coord_le i) (norm_nonneg _)
              (by norm_num)
        _ = 1 := by norm_num
    calc ‖(vbar V M x i - (m : ℂ) * zeta0 i)
          * (starRingEnd ℂ) (vbar V M x j)
        + ((m : ℂ) * zeta0 i) * (starRingEnd ℂ)
            (vbar V M x j - (m : ℂ) * zeta0 j)‖
        ≤ ‖(vbar V M x i - (m : ℂ) * zeta0 i)
            * (starRingEnd ℂ) (vbar V M x j)‖
          + ‖((m : ℂ) * zeta0 i) * (starRingEnd ℂ)
              (vbar V M x j - (m : ℂ) * zeta0 j)‖ := norm_add_le _ _
      _ ≤ ‖vbar V M x i - (m : ℂ) * zeta0 i‖ * 1
          + 1 * ‖vbar V M x j - (m : ℂ) * zeta0 j‖ := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (norm_vbar_le hVb hM x j)
              (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hmz (norm_nonneg _))
      _ = ‖vbar V M x i - (m : ℂ) * zeta0 i‖
          + ‖vbar V M x j - (m : ℂ) * zeta0 j‖ := by ring
  have hnormle := cExp_norm_le hG fun x =>
      vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
        - ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j)
  have hmono := hG.mono _ _ hpt
  have hsplitE : gibbs (EM M) Bt (fun x =>
        ‖vbar V M x i - (m : ℂ) * zeta0 i‖
          + ‖vbar V M x j - (m : ℂ) * zeta0 j‖)
      = gibbs (EM M) Bt (fun x => ‖vbar V M x i - (m : ℂ) * zeta0 i‖)
        + gibbs (EM M) Bt (fun x =>
            ‖vbar V M x j - (m : ℂ) * zeta0 j‖) :=
    hG.add _ _
  have hdevcoord : ∀ i' : Fin 2,
      gibbs (EM M) Bt (fun x => ‖vbar V M x i' - (m : ℂ) * zeta0 i'‖)
        ≤ Real.sqrt (gibbs (EM M) Bt fun x => ∑ i'',
            Complex.normSq (vbar V M x i'' - (m : ℂ) * zeta0 i'')) := by
    intro i'
    have h1 := hG.abs_mean_le_sqrt
      fun x => ‖vbar V M x i' - (m : ℂ) * zeta0 i'‖
    have h2 : (fun x => |‖vbar V M x i' - (m : ℂ) * zeta0 i'‖|)
        = fun x => ‖vbar V M x i' - (m : ℂ) * zeta0 i'‖ := by
      funext x
      exact abs_norm _
    rw [h2] at h1
    refine le_trans h1 (Real.sqrt_le_sqrt ?_)
    refine hG.mono _ _ fun x => ?_
    rw [show ‖vbar V M x i' - (m : ℂ) * zeta0 i'‖ ^ 2
        = Complex.normSq (vbar V M x i' - (m : ℂ) * zeta0 i') from
        (Complex.normSq_eq_norm_sq _).symm]
    exact Finset.single_le_sum
      (f := fun i'' => Complex.normSq (vbar V M x i'' - (m : ℂ) * zeta0 i''))
      (fun i'' _ => Complex.normSq_nonneg _) (Finset.mem_univ i')
  rw [hdiff]
  calc ‖cExp (gibbs (EM M) Bt) fun x =>
        vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
          - ((m : ℂ) * zeta0 i) * (starRingEnd ℂ) ((m : ℂ) * zeta0 j)‖
      ≤ 2 * gibbs (EM M) Bt (fun x =>
          ‖vbar V M x i * (starRingEnd ℂ) (vbar V M x j)
            - ((m : ℂ) * zeta0 i)
              * (starRingEnd ℂ) ((m : ℂ) * zeta0 j)‖) := hnormle
    _ ≤ 2 * gibbs (EM M) Bt (fun x =>
          ‖vbar V M x i - (m : ℂ) * zeta0 i‖
            + ‖vbar V M x j - (m : ℂ) * zeta0 j‖) := by
        linarith [hmono]
    _ ≤ 4 * Real.sqrt (gibbs (EM M) Bt fun x => ∑ i',
          Complex.normSq (vbar V M x i' - (m : ℂ) * zeta0 i')) := by
        rw [hsplitE]
        have h3 := hdevcoord i
        have h4 := hdevcoord j
        linarith

/-- **`thm:RPESM-subextensive-fixed-source`, subextensive concentration**:
with `osc B_M = o(M)` the conditioned squared deviation vanishes in the
thermodynamic limit. -/
theorem subextensive_dev_limit (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    (Bt : ∀ M : ℕ, (Fin M → S) → ℝ) (lo Δ : ℕ → ℝ)
    (hBt : ∀ M x, lo M ≤ Bt M x ∧ Bt M x ≤ lo M + Δ M)
    (hsub : Filter.Tendsto (fun M : ℕ => Δ M / M) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun M => gibbs (EM M) (Bt M) fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      Filter.atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε' hε'
  set ε := min (Real.sqrt (ε' / 2)) 2 with hεdef
  have hε0 : 0 < ε :=
    lt_min (Real.sqrt_pos.mpr (by linarith)) (by norm_num)
  have hε2 : ε ≤ 2 := min_le_right _ _
  have hεsq : ε ^ 2 ≤ ε' / 2 := by
    have h1 : ε ≤ Real.sqrt (ε' / 2) := min_le_left _ _
    have h2 : ε ^ 2 ≤ Real.sqrt (ε' / 2) ^ 2 := pow_le_pow_left₀ hε0.le h1 2
    rwa [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ ε' / 2)] at h2
  set c := (ε / 2) ^ 2 / 16 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    positivity
  have hev1 : ∀ᶠ M : ℕ in Filter.atTop, Δ M / M < c / 2 :=
    hsub.eventually_lt_const (by linarith)
  have hexp0 : Filter.Tendsto
      (fun M : ℕ => 32 * Real.exp (-((M : ℝ) * (c / 2))))
      Filter.atTop (nhds 0) := by
    have h4 : Filter.Tendsto (fun M : ℕ => (M : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have h5 := h4.atTop_mul_const (by positivity : (0 : ℝ) < c / 2)
    have h6 : Filter.Tendsto (fun M : ℕ => -((M : ℝ) * (c / 2)))
        Filter.atTop Filter.atBot := tendsto_neg_atTop_atBot.comp h5
    have h7 := (Real.tendsto_exp_atBot.comp h6).const_mul (32 : ℝ)
    simpa using h7
  have hev2 : ∀ᶠ M : ℕ in Filter.atTop,
      32 * Real.exp (-((M : ℝ) * (c / 2))) < ε' / 2 :=
    hexp0.eventually_lt_const (by linarith)
  have hev3 : ∀ᶠ M : ℕ in Filter.atTop, 1 ≤ M :=
    Filter.eventually_ge_atTop 1
  filter_upwards [hev1, hev2, hev3] with M h1 h2 h3
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hbound := subextensive_dev_bound hE1 hPL hVb hmean0 hmean1 h3
    (hBt M) hε0 hε2
  have hexpo : Δ M - (M : ℝ) * (ε / 2) ^ 2 / 16 ≤ -((M : ℝ) * (c / 2)) := by
    have h8 : Δ M < (M : ℝ) * (c / 2) := by
      have h9 := (div_lt_iff₀ hMpos).mp h1
      linarith
    have h10 : (M : ℝ) * (ε / 2) ^ 2 / 16 = (M : ℝ) * c := by
      rw [hcdef]
      ring
    linarith
  have hmono2 : 32 * Real.exp (Δ M - (M : ℝ) * (ε / 2) ^ 2 / 16)
      ≤ 32 * Real.exp (-((M : ℝ) * (c / 2))) := by
    have h11 := Real.exp_le_exp.mpr hexpo
    linarith
  have hnn : 0 ≤ gibbs (EM M) (Bt M) fun x => ∑ i,
      Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i) :=
    (gibbs_isExpectation (hPL.1 M) (hBt M)).nonneg fun x =>
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc gibbs (EM M) (Bt M) (fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i))
      ≤ ε ^ 2 + 32 * Real.exp (Δ M - (M : ℝ) * (ε / 2) ^ 2 / 16) := hbound
    _ < ε' := by linarith

/-- **`thm:RPESM-subextensive-fixed-source`, subextensive limit**: with
`osc B_M = o(M)` the tilted orbit still converges to the rank-one matrix
`m² P_{ζ₀}`. -/
theorem subextensive_orbit_limit (hE1 : IsExpectation E1)
    {EM : ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ} (hPL : IsProductLaw E1 EM)
    (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hmean0 : cExp E1 (fun ω => V ω 0) = 0)
    (hmean1 : cExp E1 (fun ω => V ω 1) = (m : ℂ))
    (Bt : ∀ M : ℕ, (Fin M → S) → ℝ) (lo Δ : ℕ → ℝ)
    (hBt : ∀ M x, lo M ≤ Bt M x ∧ Bt M x ≤ lo M + Δ M)
    (hsub : Filter.Tendsto (fun M : ℕ => Δ M / M) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun M => gram2 (gibbs (EM M) (Bt M)) (vbar V M))
      Filter.atTop (nhds (((m ^ 2 : ℝ) : ℂ) • pz)) := by
  have hdev := subextensive_dev_limit hE1 hPL hVb hmean0 hmean1 Bt lo Δ
    hBt hsub
  have hg : Filter.Tendsto (fun M => 4 * Real.sqrt
      (gibbs (EM M) (Bt M) fun x => ∑ i,
        Complex.normSq (vbar V M x i - (m : ℂ) * zeta0 i)))
      Filter.atTop (nhds 0) := by
    have h1 := (Real.continuous_sqrt.tendsto 0).comp hdev
    rw [Real.sqrt_zero] at h1
    simpa using h1.const_mul (4 : ℝ)
  rw [show (nhds (((m ^ 2 : ℝ) : ℂ) • pz))
      = nhds (fun i j => (((m ^ 2 : ℝ) : ℂ) • pz) i j) from rfl]
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hb : ∀ᶠ M : ℕ in Filter.atTop,
      ‖gram2 (gibbs (EM M) (Bt M)) (vbar V M) i j
        - (((m ^ 2 : ℝ) : ℂ) • pz) i j‖
      ≤ 4 * Real.sqrt (gibbs (EM M) (Bt M) fun x => ∑ i',
          Complex.normSq (vbar V M x i' - (m : ℂ) * zeta0 i')) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    have h2 := tilted_entry_dev hE1 hPL hVb hmean1 hM (hBt M) i j
    have h3 : (((m ^ 2 : ℝ) : ℂ) • pz) i j
        = ((m ^ 2 : ℝ) : ℂ) * pz i j := by
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [h3]
    exact h2
  have h4 := squeeze_zero_norm' hb hg
  exact tendsto_sub_nhds_zero_iff.mp h4

end Subextensive

end SubextensiveSection

/-! ### `thm:RPESM-local-orbit-full-rank`

Rendering (RS.6): the cutoff-`N` path carrier is an abstract carrier `Ω N`
with base expectation functional `EΩ N` (`ExpFun.IsExpectation`), projective
against `π N : Ω (N+1) → Ω N`; the transported old-root Higgs coordinate is
`Hc N : Ω N → W_H` with `Hc (N+1) = Hc N ∘ π N`, and its base marginal at
the root cutoff is the rotation-invariant, non-concentrated quartic proposal
`Ef` (the same interface as `cth:RPESM-local-source-no-rank-one`).  The
normalized interacting density is `e^{g_N}` with oscillation window `17/64`,
exactly transported, and the source is `η B_N` with `|B_N| ≤ 2`,
`0 ≤ η ≤ 1/64`, exactly transported; the conditioned law is the Gibbs
functional of `g_N + η B_N` and `Q_{N,η}` is its Gram of the saturation
read `χ_H(Hc)`.  The bundle `local_orbit_full_rank` proves: the uniform
Loewner floor `Q_{N,η} ⪰ e^{-21/64} a_χ I₂` with the eigenvalue floor
`λ_min(Q_{N,η}) ≥ e^{-21/64} a_χ > 0` (RS.6); the exact `N`-independence of
the source normalizer, conditioned source mean, and local orbit Gram; and
rank two at every cutoff and every source strength in the window (hence
along every source-removal sequence).  The decimal evaluation
`λ_min ≥ 0.1576726006` of the very same constant `e^{-21/64} a_χ` for the
explicit quartic integral `a_χ ≈ 0.2189067271` of (RS.5) is a numerical
evaluation not formalized here; the exact floor `e^{-21/64} a_χ` is proved,
with `a_χ > 0` derived from non-concentration. -/

section LocalOrbitFullRankSection

namespace LocalOrbitFullRank

open ExpFun RelationalSource LocalOrbit Subextensive

/-- The transported local frame-coordinate saturation read on a path
carrier. -/
noncomputable def pathRead {Ω : Type*} (Hc : Ω → WH) : Ω → Fin 2 → ℂ :=
  fun ω i => chiH (Hc ω) i

/-- The Gibbs functional in explicit quotient form. -/
theorem gibbs_eq_div {α : Type*} (Ef : (α → ℝ) → ℝ) (V f : α → ℝ) :
    gibbs Ef V f
      = Ef (fun a => Real.exp (V a) * f a) / Ef fun a => Real.exp (V a) :=
  rfl

/-- A scalar Loewner floor weakens to every smaller scalar. -/
theorem loewner_floor_mono {Q : Matrix (Fin 2) (Fin 2) ℂ} {c₁ c₂ : ℝ}
    (h : (Q - ((c₁ : ℝ) : ℂ) • 1).PosSemidef) (hc : c₂ ≤ c₁) :
    (Q - ((c₂ : ℝ) : ℂ) • 1).PosSemidef := by
  have h2 : (((c₁ - c₂ : ℝ) : ℂ)
      • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef :=
    posSemidef_real_smul Matrix.PosSemidef.one (by linarith)
  have h3 := h.add h2
  convert h3 using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub]
  ring

variable {Ω : Type*} {EΩ : (Ω → ℝ) → ℝ} {Ef : (WH → ℝ) → ℝ}

/-- The path marginal identity transports the directional saturation
moment of the proposal. -/
theorem path_directional_moment (hEf : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    {Hc : Ω → WH} (hmarg : ∀ f : WH → ℝ, EΩ (fun ω => f (Hc ω)) = Ef f)
    (c : Fin 2 → ℂ) :
    EΩ (fun ω => ‖∑ i, (starRingEnd ℂ) (c i) * pathRead Hc ω i‖ ^ 2)
      = (∑ i, ‖c i‖ ^ 2) * aChi Ef :=
  (hmarg fun h => ‖∑ i, (starRingEnd ℂ) (c i) * chiH h i‖ ^ 2).trans
    (directional_moment hEf hInv c)

/-- **(RS.6, Loewner window form)**: the conditioned local orbit Gram of the
transported saturation read has the uniform floor `Q ⪰ e^{lo−hi} a_χ I₂`
for every conditioning with oscillation window `[lo, hi]`. -/
theorem path_orbitGram_floor (hEf : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (hEΩ : IsExpectation EΩ) {Hc : Ω → WH}
    (hmarg : ∀ f : WH → ℝ, EΩ (fun ω => f (Hc ω)) = Ef f)
    {V : Ω → ℝ} {lo hi : ℝ} (hV : ∀ ω, lo ≤ V ω ∧ V ω ≤ hi) :
    (gram2 (gibbs EΩ V) (pathRead Hc)
      - ((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ) • 1).PosSemidef := by
  have hG := gibbs_isExpectation hEΩ hV
  have hsmulH : (((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ)
      • (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
    show _ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal]
  refine posSemidef_of_re_form
    ((gram2_isHermitian hG (pathRead Hc)).sub hsmulH) fun x => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, gram2_form hG (pathRead Hc),
    star_dot_self_eq_sum_sq]
  have hfloor : Real.exp (lo - hi) * ((∑ i, ‖x i‖ ^ 2) * aChi Ef)
      ≤ gibbs EΩ V fun ω =>
        ‖∑ i, (starRingEnd ℂ) (x i) * pathRead Hc ω i‖ ^ 2 := by
    have h1 := gibbs_ge hEΩ hV
      (f := fun ω => ‖∑ i, (starRingEnd ℂ) (x i) * pathRead Hc ω i‖ ^ 2)
      fun ω => by positivity
    rwa [path_directional_moment hEf hInv hmarg x] at h1
  have hre : (((gibbs EΩ V fun ω =>
        ‖∑ i, (starRingEnd ℂ) (x i) * pathRead Hc ω i‖ ^ 2 : ℝ) : ℂ)
      - ((Real.exp (lo - hi) * aChi Ef : ℝ) : ℂ)
        * ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)).re
      = (gibbs EΩ V fun ω =>
          ‖∑ i, (starRingEnd ℂ) (x i) * pathRead Hc ω i‖ ^ 2)
        - Real.exp (lo - hi) * aChi Ef * ∑ i, ‖x i‖ ^ 2 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  rw [smul_eq_mul, hre]
  nlinarith [hfloor]

/-- **(RS.6, full rank)**: the conditioned local orbit has rank two. -/
theorem path_orbitGram_rank_two (hEf : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (hnondeg : 0 < Ef fun h => min (‖h‖ ^ 2) 1)
    (hEΩ : IsExpectation EΩ) {Hc : Ω → WH}
    (hmarg : ∀ f : WH → ℝ, EΩ (fun ω => f (Hc ω)) = Ef f)
    {V : Ω → ℝ} {lo hi : ℝ} (hV : ∀ ω, lo ≤ V ω ∧ V ω ≤ hi) :
    (gram2 (gibbs EΩ V) (pathRead Hc)).rank = 2 := by
  have hG := gibbs_isExpectation hEΩ hV
  have hherm := gram2_isHermitian hG (pathRead Hc)
  have hκ : 0 < Real.exp (lo - hi) * aChi Ef :=
    mul_pos (Real.exp_pos _) (aChi_pos hEf hInv hnondeg)
  have hpd := posDef_of_kappa_floor hherm hκ
    (path_orbitGram_floor hEf hInv hEΩ hmarg hV)
  rw [Matrix.rank_of_isUnit _ hpd.isUnit]
  exact Fintype.card_fin 2

/-- Exact transport of the conditioned functional through a projective
step: the Gibbs expectation of an exactly pulled-back writer under the
pulled-back tilt equals the coarse Gibbs expectation. -/
theorem gibbs_pullback {Ω' : Type*} {EΩ' : (Ω' → ℝ) → ℝ} {π : Ω' → Ω}
    (hpull : ∀ f : Ω → ℝ, EΩ' (fun ω' => f (π ω')) = EΩ f)
    (V f : Ω → ℝ) :
    gibbs EΩ' (fun ω' => V (π ω')) (fun ω' => f (π ω')) = gibbs EΩ V f := by
  have h1 : EΩ' (fun ω' => Real.exp (V (π ω')) * f (π ω'))
      = EΩ fun ω => Real.exp (V ω) * f ω :=
    hpull fun ω => Real.exp (V ω) * f ω
  have h2 : EΩ' (fun ω' => Real.exp (V (π ω'))) = EΩ fun ω => Real.exp (V ω) :=
    hpull fun ω => Real.exp (V ω)
  rw [gibbs_eq_div, gibbs_eq_div, h1, h2]

/-- Exact transport of the conditioned orbit Gram through a projective
step. -/
theorem gram2_gibbs_pullback {Ω' : Type*} {EΩ' : (Ω' → ℝ) → ℝ} {π : Ω' → Ω}
    (hpull : ∀ f : Ω → ℝ, EΩ' (fun ω' => f (π ω')) = EΩ f)
    (V : Ω → ℝ) (w : Ω → Fin 2 → ℂ) :
    gram2 (gibbs EΩ' fun ω' => V (π ω')) (fun ω' => w (π ω'))
      = gram2 (gibbs EΩ V) w := by
  ext i j
  refine Complex.ext ?_ ?_
  · show gibbs EΩ' (fun ω' => V (π ω'))
        (fun ω' => (w (π ω') i * (starRingEnd ℂ) (w (π ω') j)).re)
      = gibbs EΩ V fun ω => (w ω i * (starRingEnd ℂ) (w ω j)).re
    exact gibbs_pullback hpull V fun ω => (w ω i * (starRingEnd ℂ) (w ω j)).re
  · show gibbs EΩ' (fun ω' => V (π ω'))
        (fun ω' => (w (π ω') i * (starRingEnd ℂ) (w (π ω') j)).im)
      = gibbs EΩ V fun ω => (w ω i * (starRingEnd ℂ) (w ω j)).im
    exact gibbs_pullback hpull V fun ω => (w ω i * (starRingEnd ℂ) (w ω j)).im

/-- **`thm:RPESM-local-orbit-full-rank` (RS.6)**: along the projective
thread with exactly transported root coordinate, interacting density
(oscillation window `17/64`), and source (`|B| ≤ 2`, `0 ≤ η ≤ 1/64`), the
conditioned local orbit Gram of the saturation read satisfies the uniform
Loewner floor `Q_{N,η} ⪰ e^{-21/64} a_χ I₂` and eigenvalue floor
`λ_min ≥ e^{-21/64} a_χ > 0`; the source normalizer, conditioned source
mean, and local orbit Gram are exactly independent of `N`; and the local
orbit has rank two at every cutoff and every source strength in the
window. -/
theorem local_orbit_full_rank
    {Ω : ℕ → Type*} (EΩ : ∀ N, (Ω N → ℝ) → ℝ)
    (π : ∀ N, Ω (N + 1) → Ω N) {Ef : (WH → ℝ) → ℝ}
    (hEf : IsExpectation Ef)
    (hInv : ∀ (U : WH ≃ₗᵢ[ℂ] WH) (f : WH → ℝ), Ef (fun h => f (U h)) = Ef f)
    (hnondeg : 0 < Ef fun h => min (‖h‖ ^ 2) 1)
    (hEΩ : ∀ N, IsExpectation (EΩ N))
    (hpull : ∀ N (f : Ω N → ℝ), EΩ (N + 1) (fun ω' => f (π N ω')) = EΩ N f)
    (Hc : ∀ N, Ω N → WH) (hHc : ∀ N ω', Hc (N + 1) ω' = Hc N (π N ω'))
    (hmarg0 : ∀ f : WH → ℝ, EΩ 0 (fun ω => f (Hc 0 ω)) = Ef f)
    (g : ∀ N, Ω N → ℝ) (lo : ℕ → ℝ)
    (hg : ∀ N ω, lo N ≤ g N ω ∧ g N ω ≤ lo N + 17 / 64)
    (hgpull : ∀ N ω', g (N + 1) ω' = g N (π N ω'))
    (B : ∀ N, Ω N → ℝ) (hB : ∀ N ω, |B N ω| ≤ 2)
    (hBpull : ∀ N ω', B (N + 1) ω' = B N (π N ω'))
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64) :
    0 < Real.exp (-(21 / 64)) * aChi Ef
    ∧ (∀ N, (gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω)
          (pathRead (Hc N))
        - ((Real.exp (-(21 / 64)) * aChi Ef : ℝ) : ℂ) • 1).PosSemidef)
    ∧ (∀ N, Real.exp (-(21 / 64)) * aChi Ef
        ≤ lam2 (gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω)
            (pathRead (Hc N))))
    ∧ (∀ N, EΩ N (fun ω => Real.exp (g N ω + η * B N ω))
        = EΩ 0 fun ω => Real.exp (g 0 ω + η * B 0 ω))
    ∧ (∀ N, gibbs (EΩ N) (fun ω => g N ω + η * B N ω) (B N)
        = gibbs (EΩ 0) (fun ω => g 0 ω + η * B 0 ω) (B 0))
    ∧ (∀ N, gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω)
          (pathRead (Hc N))
        = gram2 (gibbs (EΩ 0) fun ω => g 0 ω + η * B 0 ω)
          (pathRead (Hc 0)))
    ∧ (∀ N, (gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω)
        (pathRead (Hc N))).rank = 2) := by
  have hmargN : ∀ N (f : WH → ℝ), EΩ N (fun ω => f (Hc N ω)) = Ef f := by
    intro N
    induction N with
    | zero => exact hmarg0
    | succ N ih =>
        intro f
        have h1 : (fun ω' => f (Hc (N + 1) ω'))
            = fun ω' => f (Hc N (π N ω')) := by
          funext ω'
          rw [hHc N ω']
        rw [h1]
        exact (hpull N fun ω => f (Hc N ω)).trans (ih f)
  have hwin : ∀ N (ω : Ω N),
      lo N - 2 * η ≤ g N ω + η * B N ω
        ∧ g N ω + η * B N ω ≤ lo N + 17 / 64 + 2 * η := by
    intro N ω
    have h1 := (hg N ω).1
    have h2 := (hg N ω).2
    have h3 := abs_le.mp (hB N ω)
    constructor
    · nlinarith [h3.1]
    · nlinarith [h3.2]
  have hexp : ∀ N : ℕ, Real.exp (-(21 / 64))
      ≤ Real.exp ((lo N - 2 * η) - (lo N + 17 / 64 + 2 * η)) := by
    intro N
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hfloorN : ∀ N,
      (gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω) (pathRead (Hc N))
        - ((Real.exp (-(21 / 64)) * aChi Ef : ℝ) : ℂ) • 1).PosSemidef := by
    intro N
    refine loewner_floor_mono
      (path_orbitGram_floor hEf hInv (hEΩ N) (hmargN N) (hwin N)) ?_
    exact mul_le_mul_of_nonneg_right (hexp N) (aChi_nonneg hEf)
  have hVfun : ∀ N, (fun ω' => g (N + 1) ω' + η * B (N + 1) ω')
      = fun ω' => (fun ω => g N ω + η * B N ω) (π N ω') := by
    intro N
    funext ω'
    rw [hgpull N ω', hBpull N ω']
  have hreadfun : ∀ N, pathRead (Hc (N + 1))
      = fun ω' => pathRead (Hc N) (π N ω') := by
    intro N
    funext ω' i
    unfold pathRead
    rw [hHc N ω']
  have hZstep : ∀ N, EΩ (N + 1)
        (fun ω' => Real.exp (g (N + 1) ω' + η * B (N + 1) ω'))
      = EΩ N fun ω => Real.exp (g N ω + η * B N ω) := by
    intro N
    have h1 : (fun ω' => Real.exp (g (N + 1) ω' + η * B (N + 1) ω'))
        = fun ω' => Real.exp (g N (π N ω') + η * B N (π N ω')) := by
      funext ω'
      rw [hgpull N ω', hBpull N ω']
    rw [h1]
    exact hpull N fun ω => Real.exp (g N ω + η * B N ω)
  have hmeanstep : ∀ N,
      gibbs (EΩ (N + 1)) (fun ω' => g (N + 1) ω' + η * B (N + 1) ω')
          (B (N + 1))
        = gibbs (EΩ N) (fun ω => g N ω + η * B N ω) (B N) := by
    intro N
    have hBfun : B (N + 1) = fun ω' => B N (π N ω') := funext (hBpull N)
    rw [hVfun N, hBfun]
    exact gibbs_pullback (hpull N) (fun ω => g N ω + η * B N ω) (B N)
  have hgramstep : ∀ N,
      gram2 (gibbs (EΩ (N + 1)) fun ω' => g (N + 1) ω' + η * B (N + 1) ω')
          (pathRead (Hc (N + 1)))
        = gram2 (gibbs (EΩ N) fun ω => g N ω + η * B N ω)
            (pathRead (Hc N)) := by
    intro N
    rw [hVfun N, hreadfun N]
    exact gram2_gibbs_pullback (hpull N) (fun ω => g N ω + η * B N ω)
      (pathRead (Hc N))
  refine ⟨mul_pos (Real.exp_pos _) (aChi_pos hEf hInv hnondeg), hfloorN,
    fun N => ?_, fun N => ?_, fun N => ?_, fun N => ?_, fun N => ?_⟩
  · have hG := gibbs_isExpectation (hEΩ N) (hwin N)
    have hherm := gram2_isHermitian hG (pathRead (Hc N))
    rw [lam2_eq hherm]
    exact le_hermLamMin_of_loewner hherm (hfloorN N)
  · induction N with
    | zero => rfl
    | succ N ih => rw [hZstep N, ih]
  · induction N with
    | zero => rfl
    | succ N ih => rw [hmeanstep N, ih]
  · induction N with
    | zero => rfl
    | succ N ih => rw [hgramstep N, ih]
  · exact path_orbitGram_rank_two hEf hInv hnondeg (hEΩ N) (hmargN N) (hwin N)

end LocalOrbitFullRank

end LocalOrbitFullRankSection

/-! ### `cth:RPESM-bounded-source-removal`

Rendering (RS.9): the coherently sourced one-site law at per-site source
`s_N = η ρ_N` is the exponential tilt `gibbs E1 (s_N X)` of the base
one-site law `E1` by the neutral source read `X = Re⟨ζ₀, V⟩ = Re(V·1)` of
the saturated frame-coordinate read `V` (`‖V‖ ≤ 1`, so `|X| ≤ 1`); the
base law is symmetric in `X` (the isotropy of the quartic proposal), which
gives the exact chord window `0 ≤ m(s) ≤ s` of (RS.7, upper branch) via the
pointwise bound `x·sinh(s x) ≤ s·cosh(s x)` and `E[cosh] ≥ 1`.  For each
cutoff the thermodynamic orbit is the subextensive-interaction limit of
`thm:RPESM-subextensive-fixed-source`, equal to `m(s_N)² P_{ζ₀}`, so with
`0 < ρ_N ≤ ρ⋆` every such orbit has `ℓ²` operator norm at most `ρ⋆²η²`
uniformly in `N` (RS.9; `sup_N` is rendered as `∀ N`).  At every fixed
positive source with non-degenerate read the orbit is a nonzero rank-one
matrix (`m(s) ≥ s·E[X²]/E[cosh] > 0`), and the source-removed orbit is
zero: the amplitude tends to `0` as `η ↓ 0`
(`source_removed_orbit_zero`).  The RPESM specialization enters through
`rpesm_bounded_osc_subextensive`: the volume-normalized interaction with
total oscillation `17/64` is subextensive (`osc/M → 0`), so the bundle
applies to it; the aside on analyticity of its one-site pressure is
commentary not formalized here. -/

section BoundedSourceRemovalSection

namespace BoundedSourceRemoval

open ExpFun LocalOrbit Subextensive LocalOrbitFullRank Filter

/-- The chord bound `sinh t ≤ t·cosh t` for `t ≥ 0` (i.e. `tanh t ≤ t`). -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.cosh t := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y => y * Real.cosh y - Real.sinh y)
      (x * Real.sinh x) x := by
    intro x
    have h1 : HasDerivAt (fun y => y * Real.cosh y)
        (1 * Real.cosh x + x * Real.sinh x) x :=
      (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
    have h2 : HasDerivAt (fun y => y * Real.cosh y - Real.sinh y)
        (1 * Real.cosh x + x * Real.sinh x - Real.cosh x) x :=
      h1.sub (Real.hasDerivAt_sinh x)
    have h3 : 1 * Real.cosh x + x * Real.sinh x - Real.cosh x
        = x * Real.sinh x := by ring
    rwa [h3] at h2
  have hmono : MonotoneOn (fun y => y * Real.cosh y - Real.sinh y)
      (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun x =>
        (hd x).continuousAt).continuousOn
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hd x).deriv]
      exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le)
  have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h0
  linarith

/-- The pointwise chord window of the sourced read:
`s x² ≤ x·sinh(s x) ≤ s·cosh(s x)` for `|x| ≤ 1` and `s ≥ 0`. -/
theorem mul_sinh_window {x s : ℝ} (hx : |x| ≤ 1) (hs : 0 ≤ s) :
    s * x ^ 2 ≤ x * Real.sinh (s * x)
      ∧ x * Real.sinh (s * x) ≤ s * Real.cosh (s * x) := by
  have habs : x * Real.sinh (s * x) = |x| * Real.sinh (s * |x|) := by
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
    · rw [abs_of_neg hx0, show s * -x = -(s * x) by ring, Real.sinh_neg]
      ring
  have hcosh : Real.cosh (s * x) = Real.cosh (s * |x|) := by
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
    · rw [abs_of_neg hx0, show s * -x = -(s * x) by ring, Real.cosh_neg]
  have hax : 0 ≤ |x| := abs_nonneg x
  have hsx : 0 ≤ s * |x| := mul_nonneg hs hax
  constructor
  · have h1 : s * |x| ≤ Real.sinh (s * |x|) := Real.self_le_sinh_iff.mpr hsx
    have h2 : |x| * (s * |x|) ≤ |x| * Real.sinh (s * |x|) :=
      mul_le_mul_of_nonneg_left h1 hax
    have h3 : |x| * (s * |x|) = s * x ^ 2 := by
      rw [sq, ← abs_mul_abs_self x]
      ring
    rw [habs]
    linarith
  · have h1 : Real.sinh (s * |x|) ≤ (s * |x|) * Real.cosh (s * |x|) :=
      sinh_le_mul_cosh hsx
    have h2 : |x| * Real.sinh (s * |x|)
        ≤ |x| * ((s * |x|) * Real.cosh (s * |x|)) :=
      mul_le_mul_of_nonneg_left h1 hax
    have hcpos : 0 < Real.cosh (s * |x|) := Real.cosh_pos _
    have h4 : |x| * |x| ≤ 1 := by
      nlinarith [abs_nonneg x]
    have h3 : |x| * ((s * |x|) * Real.cosh (s * |x|))
        ≤ s * Real.cosh (s * |x|) := by
      nlinarith [mul_nonneg (mul_nonneg hs hcpos.le) (sub_nonneg.mpr h4)]
    rw [habs, hcosh]
    linarith

variable {S : Type*} {E1 : (S → ℝ) → ℝ}

/-- Under source-read symmetry the tilt numerator is the `sinh` moment. -/
theorem tilt_numerator_eq_sinh (hE1 : IsExpectation E1) {X : S → ℝ}
    (hsym : ∀ g : ℝ → ℝ, E1 (fun ω => g (X ω)) = E1 fun ω => g (-X ω))
    (s : ℝ) :
    E1 (fun ω => Real.exp (s * X ω) * X ω)
      = E1 fun ω => X ω * Real.sinh (s * X ω) := by
  have hA := hsym fun t => Real.exp (s * t) * t
  have hneg : (fun ω => Real.exp (s * -X ω) * -X ω)
      = fun ω => -1 * (Real.exp (-(s * X ω)) * X ω) := by
    funext ω
    rw [show s * -X ω = -(s * X ω) by ring]
    ring
  have hsm := hE1.smul (-1) fun ω => Real.exp (-(s * X ω)) * X ω
  rw [hneg, hsm] at hA
  have hsplit : (fun ω => X ω * Real.sinh (s * X ω))
      = fun ω => (2⁻¹ : ℝ) * (Real.exp (s * X ω) * X ω)
          - (2⁻¹ : ℝ) * (Real.exp (-(s * X ω)) * X ω) := by
    funext ω
    rw [Real.sinh_eq]
    ring
  have h2 := hE1.sub (fun ω => (2⁻¹ : ℝ) * (Real.exp (s * X ω) * X ω))
    fun ω => (2⁻¹ : ℝ) * (Real.exp (-(s * X ω)) * X ω)
  have hs1 := hE1.smul (2⁻¹ : ℝ) fun ω => Real.exp (s * X ω) * X ω
  have hs2 := hE1.smul (2⁻¹ : ℝ) fun ω => Real.exp (-(s * X ω)) * X ω
  rw [hsplit, h2, hs1, hs2]
  linarith [hA]

/-- Under source-read symmetry the tilt normalizer is the `cosh` moment. -/
theorem tilt_denominator_eq_cosh (hE1 : IsExpectation E1) {X : S → ℝ}
    (hsym : ∀ g : ℝ → ℝ, E1 (fun ω => g (X ω)) = E1 fun ω => g (-X ω))
    (s : ℝ) :
    E1 (fun ω => Real.exp (s * X ω)) = E1 fun ω => Real.cosh (s * X ω) := by
  have hC := hsym fun t => Real.exp (s * t)
  have hneg : (fun ω => Real.exp (s * -X ω))
      = fun ω => Real.exp (-(s * X ω)) := by
    funext ω
    rw [show s * -X ω = -(s * X ω) by ring]
  rw [hneg] at hC
  have hsplit : (fun ω => Real.cosh (s * X ω))
      = fun ω => (2⁻¹ : ℝ) * Real.exp (s * X ω)
          + (2⁻¹ : ℝ) * Real.exp (-(s * X ω)) := by
    funext ω
    rw [Real.cosh_eq]
    ring
  have h2 := hE1.add (fun ω => (2⁻¹ : ℝ) * Real.exp (s * X ω))
    fun ω => (2⁻¹ : ℝ) * Real.exp (-(s * X ω))
  have hs1 := hE1.smul (2⁻¹ : ℝ) fun ω => Real.exp (s * X ω)
  have hs2 := hE1.smul (2⁻¹ : ℝ) fun ω => Real.exp (-(s * X ω))
  rw [hsplit, h2, hs1, hs2]
  linarith [hC]

/-- **(RS.7, upper branch)**: the sourced one-site mean of a symmetric read
bounded by one obeys the exact chord window `0 ≤ m(s) ≤ s`. -/
theorem tilted_mean_window (hE1 : IsExpectation E1) {X : S → ℝ}
    (hX : ∀ ω, |X ω| ≤ 1)
    (hsym : ∀ g : ℝ → ℝ, E1 (fun ω => g (X ω)) = E1 fun ω => g (-X ω))
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ gibbs E1 (fun ω => s * X ω) X ∧ gibbs E1 (fun ω => s * X ω) X ≤ s := by
  have hnum := tilt_numerator_eq_sinh hE1 hsym s
  have hden := tilt_denominator_eq_cosh hE1 hsym s
  have hden1 : 1 ≤ E1 fun ω => Real.cosh (s * X ω) := by
    have h := hE1.mono (fun _ => 1) (fun ω => Real.cosh (s * X ω))
      fun ω => Real.one_le_cosh _
    rwa [hE1.one] at h
  have hnum0 : 0 ≤ E1 fun ω => X ω * Real.sinh (s * X ω) := by
    refine hE1.nonneg fun ω => ?_
    have h1 := (mul_sinh_window (hX ω) hs).1
    have h2 : 0 ≤ s * X ω ^ 2 := mul_nonneg hs (sq_nonneg _)
    linarith
  have hnumle : E1 (fun ω => X ω * Real.sinh (s * X ω))
      ≤ s * E1 fun ω => Real.cosh (s * X ω) := by
    have h := hE1.mono (fun ω => X ω * Real.sinh (s * X ω))
      (fun ω => s * Real.cosh (s * X ω))
      fun ω => (mul_sinh_window (hX ω) hs).2
    rwa [hE1.smul] at h
  rw [gibbs_eq_div, hnum, hden]
  constructor
  · exact div_nonneg hnum0 (by linarith)
  · rw [div_le_iff₀ (by linarith : (0 : ℝ) < E1 fun ω => Real.cosh (s * X ω))]
    exact hnumle

/-- **(RS.7, lower branch)**: at strictly positive source the sourced mean
of a non-degenerate symmetric read is strictly positive. -/
theorem tilted_mean_pos (hE1 : IsExpectation E1) {X : S → ℝ}
    (hX : ∀ ω, |X ω| ≤ 1)
    (hsym : ∀ g : ℝ → ℝ, E1 (fun ω => g (X ω)) = E1 fun ω => g (-X ω))
    {s : ℝ} (hs : 0 < s) (hX2 : 0 < E1 fun ω => X ω ^ 2) :
    0 < gibbs E1 (fun ω => s * X ω) X := by
  have hnum := tilt_numerator_eq_sinh hE1 hsym s
  have hden := tilt_denominator_eq_cosh hE1 hsym s
  have hden1 : 1 ≤ E1 fun ω => Real.cosh (s * X ω) := by
    have h := hE1.mono (fun _ => 1) (fun ω => Real.cosh (s * X ω))
      fun ω => Real.one_le_cosh _
    rwa [hE1.one] at h
  have hnumge : s * E1 (fun ω => X ω ^ 2)
      ≤ E1 fun ω => X ω * Real.sinh (s * X ω) := by
    have h := hE1.mono (fun ω => s * X ω ^ 2)
      (fun ω => X ω * Real.sinh (s * X ω))
      fun ω => (mul_sinh_window (hX ω) hs.le).1
    rwa [hE1.smul] at h
  rw [gibbs_eq_div, hnum, hden]
  exact div_pos (lt_of_lt_of_le (mul_pos hs hX2) hnumge) (by linarith)

/-- The neutral-ray projector is Hermitian. -/
theorem pz_conjTranspose : pzᴴ = pz := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold pz
  rw [Complex.star_def, map_mul, Complex.conj_conj]
  ring

/-- The neutral-ray projector is idempotent. -/
theorem pz_mul_pz : pz * pz = pz := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨h00, h01, h10, h11⟩ := pz_entries
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;>
    subst hj <;> simp only [h00, h01, h10, h11] <;> ring

/-- The complement of the neutral-ray projector is positive. -/
theorem one_sub_pz_posSemidef :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - pz).PosSemidef := by
  have hherm : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - pz).IsHermitian := by
    show _ᴴ = _
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, pz_conjTranspose]
  refine posSemidef_of_re_form hherm fun x => ?_
  have hL : star x ⬝ᵥ (pz *ᵥ x) = (starRingEnd ℂ) (x 1) * x 1 := by
    unfold dotProduct Matrix.mulVec dotProduct
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Pi.star_apply, Complex.star_def]
    obtain ⟨h00, h01, h10, h11⟩ := pz_entries
    rw [h00, h01, h10, h11]
    ring
  have hI : star x ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x)
      = (starRingEnd ℂ) (x 0) * x 0 + (starRingEnd ℂ) (x 1) * x 1 := by
    rw [Matrix.one_mulVec]
    unfold dotProduct
    rw [Fin.sum_univ_two]
    simp only [Pi.star_apply, Complex.star_def]
  rw [Matrix.sub_mulVec, dotProduct_sub, hL, hI]
  have hcancel : (starRingEnd ℂ) (x 0) * x 0 + (starRingEnd ℂ) (x 1) * x 1
      - (starRingEnd ℂ) (x 1) * x 1 = (starRingEnd ℂ) (x 0) * x 0 := by
    ring
  rw [hcancel, show (starRingEnd ℂ) (x 0) * x 0
      = ((Complex.normSq (x 0) : ℝ) : ℂ) from by
    rw [mul_comm, Complex.mul_conj], Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The nonnegative real dilations of the neutral-ray projector have
`ℓ²` operator norm at most the dilation. -/
theorem l2_opNorm_smul_pz_le {c : ℝ} (hc : 0 ≤ c) :
    ‖((c : ℝ) : ℂ) • pz‖ ≤ c := by
  refine l2_opNorm_le_of_conjTranspose_mul_self_le_scalar _ c hc ?_
  have h1 : (((c : ℝ) : ℂ) • pz)ᴴ * (((c : ℝ) : ℂ) • pz)
      = ((c ^ 2 : ℝ) : ℂ) • pz := by
    rw [Matrix.conjTranspose_smul, pz_conjTranspose, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, pz_mul_pz,
      smul_smul]
    congr 1
    push_cast
    ring
  rw [h1, show ((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - ((c ^ 2 : ℝ) : ℂ) • pz
      = ((c ^ 2 : ℝ) : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - pz) from
    (smul_sub _ _ _).symm]
  exact posSemidef_real_smul one_sub_pz_posSemidef (by positivity)

/-- A positive real dilation of the neutral-ray projector is a nonzero
rank-one matrix. -/
theorem pz_smul_rank_one {c : ℝ} (hc : 0 < c) :
    (((c : ℝ) : ℂ) • pz ≠ 0) ∧ (((c : ℝ) : ℂ) • pz).rank = 1 := by
  classical
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hdiag : ((c : ℝ) : ℂ) • pz
      = Matrix.diagonal fun i : Fin 2 =>
          if i = 1 then ((c : ℝ) : ℂ) else 0 := by
    ext i j
    rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    obtain ⟨h00, h01, h10, h11⟩ := pz_entries
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;>
      subst hj
    · rw [h00]
      simp
    · rw [h01]
      simp
    · rw [h10]
      simp
    · rw [h11]
      simp
  constructor
  · intro hzero
    have h1 : (((c : ℝ) : ℂ) • pz) 1 1 = 0 := by
      rw [hzero]
      rfl
    rw [Matrix.smul_apply, pz_entries.2.2.2, smul_eq_mul, mul_one] at h1
    exact hcne h1
  · rw [hdiag, Matrix.rank_diagonal, Fintype.card_eq_one_iff]
    refine ⟨⟨1, by simp [hcne]⟩, ?_⟩
    rintro ⟨i, hi⟩
    apply Subtype.ext
    fin_cases i
    · simp at hi
    · rfl

/-- **`cth:RPESM-bounded-source-removal` (RS.9)**: with per-site source
`s_N = η ρ_N`, `0 < ρ_N ≤ ρ⋆`, every subextensive-interaction thermodynamic
orbit of the sourced frame-coordinate read exists and equals
`m(s_N)² P_{ζ₀}`, its operator norm is at most `ρ⋆²η²` uniformly in `N`
(`sup_N ‖lim_M Q_{N,M,η}‖ ≤ ρ⋆²η²`), and at fixed positive source with
non-degenerate read the orbit is a nonzero rank-one matrix whose amplitude
is source-controlled. -/
theorem bounded_source_removal (hE1 : IsExpectation E1)
    {V : S → WH} (hVb : ∀ ω, ‖V ω‖ ≤ 1)
    (hsym : ∀ g : ℝ → ℝ,
      E1 (fun ω => g ((V ω 1).re)) = E1 fun ω => g (-(V ω 1).re))
    (ρ : ℕ → ℝ) {ρs : ℝ} (hρ : ∀ N, 0 < ρ N ∧ ρ N ≤ ρs)
    {η : ℝ} (hη : 0 ≤ η) (mN : ℕ → ℝ)
    (hmean0 : ∀ N, cExp (gibbs E1 fun ω => η * ρ N * (V ω 1).re)
        (fun ω => V ω 0) = 0)
    (hmean1 : ∀ N, cExp (gibbs E1 fun ω => η * ρ N * (V ω 1).re)
        (fun ω => V ω 1) = ((mN N : ℝ) : ℂ))
    (EM : ℕ → ∀ M : ℕ, ((Fin M → S) → ℝ) → ℝ)
    (hPL : ∀ N, IsProductLaw (gibbs E1 fun ω => η * ρ N * (V ω 1).re) (EM N))
    (Bt : ℕ → ∀ M : ℕ, (Fin M → S) → ℝ) (lo Δ : ℕ → ℕ → ℝ)
    (hBt : ∀ N M x, lo N M ≤ Bt N M x ∧ Bt N M x ≤ lo N M + Δ N M)
    (hsub : ∀ N, Tendsto (fun M : ℕ => Δ N M / M) atTop (nhds 0)) :
    (∀ N, Tendsto (fun M => gram2 (gibbs (EM N M) (Bt N M)) (vbar V M))
        atTop (nhds (((mN N ^ 2 : ℝ) : ℂ) • pz)))
    ∧ (∀ N, ‖((mN N ^ 2 : ℝ) : ℂ) • pz‖ ≤ ρs ^ 2 * η ^ 2)
    ∧ (0 < η → (0 < E1 fun ω => (V ω 1).re ^ 2) →
        ∀ N, (((mN N ^ 2 : ℝ) : ℂ) • pz ≠ 0)
          ∧ (((mN N ^ 2 : ℝ) : ℂ) • pz).rank = 1) := by
  have hX1 : ∀ ω, |(V ω 1).re| ≤ 1 := fun ω =>
    le_trans (Complex.abs_re_le_norm _)
      (le_trans (coord_le_norm (V ω) 1) (hVb ω))
  have hs : ∀ N, 0 ≤ η * ρ N := fun N => mul_nonneg hη (hρ N).1.le
  have hwin : ∀ N ω, -(η * ρ N) ≤ η * ρ N * (V ω 1).re
      ∧ η * ρ N * (V ω 1).re ≤ η * ρ N := by
    intro N ω
    have h1 := abs_le.mp (hX1 ω)
    have h2 := hs N
    constructor <;> nlinarith [h1.1, h1.2]
  have hEt : ∀ N, IsExpectation (gibbs E1 fun ω => η * ρ N * (V ω 1).re) :=
    fun N => gibbs_isExpectation hE1 (hwin N)
  have hmval : ∀ N, gibbs E1 (fun ω => η * ρ N * (V ω 1).re)
      (fun ω => (V ω 1).re) = mN N := by
    intro N
    have h1 := congrArg Complex.re (hmean1 N)
    rw [Complex.ofReal_re] at h1
    exact h1
  have hmwin : ∀ N, 0 ≤ mN N ∧ mN N ≤ η * ρ N := by
    intro N
    have h1 := tilted_mean_window hE1 hX1 hsym (hs N)
    constructor
    · calc (0 : ℝ) ≤ gibbs E1 (fun ω => η * ρ N * (V ω 1).re)
            (fun ω => (V ω 1).re) := h1.1
        _ = mN N := hmval N
    · calc mN N = gibbs E1 (fun ω => η * ρ N * (V ω 1).re)
            (fun ω => (V ω 1).re) := (hmval N).symm
        _ ≤ η * ρ N := h1.2
  refine ⟨fun N => ?_, fun N => ?_, fun hηpos hX2 N => ?_⟩
  · exact subextensive_orbit_limit (hEt N) (hPL N) hVb (hmean0 N)
      (hmean1 N) (Bt N) (lo N) (Δ N) (hBt N) (hsub N)
  · have h1 : ‖((mN N ^ 2 : ℝ) : ℂ) • pz‖ ≤ mN N ^ 2 :=
      l2_opNorm_smul_pz_le (sq_nonneg _)
    have h2 := (hmwin N).1
    have h3 := (hmwin N).2
    have h4 := (hρ N).2
    have h6 : mN N ≤ ρs * η := by nlinarith
    have h7 : 0 ≤ (ρs * η - mN N) * (ρs * η + mN N) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h7]
  · have hmpos : 0 < mN N := by
      have h1 := tilted_mean_pos hE1 hX1 hsym
        (mul_pos hηpos (hρ N).1) hX2
      have h2 : gibbs E1 (fun ω => η * ρ N * (V ω 1).re)
          (fun ω => (V ω 1).re) = mN N := hmval N
      rw [← h2]
      exact h1
    exact pz_smul_rank_one (by positivity)

/-- **(RS.9, source removal)**: the thermodynamic orbit amplitude vanishes
as `η ↓ 0` — the quasi-average of every bounded source normalization is
zero. -/
theorem source_removed_orbit_zero {morb : ℝ → ℝ} {ρs : ℝ}
    (hm : ∀ η : ℝ, 0 ≤ η → 0 ≤ morb η ∧ morb η ≤ ρs * η) :
    Tendsto (fun η : ℝ => ((morb η ^ 2 : ℝ) : ℂ) • pz)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  have hb : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ici 0),
      ‖((morb η ^ 2 : ℝ) : ℂ) • pz‖ ≤ ρs ^ 2 * η ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have h1 := hm η hη
    have h2 : ‖((morb η ^ 2 : ℝ) : ℂ) • pz‖ ≤ morb η ^ 2 :=
      l2_opNorm_smul_pz_le (sq_nonneg _)
    have h3 : 0 ≤ (ρs * η - morb η) * (ρs * η + morb η) :=
      mul_nonneg (by linarith [h1.1, h1.2]) (by linarith [h1.1, h1.2])
    nlinarith [h3]
  have hg : Tendsto (fun η : ℝ => ρs ^ 2 * η ^ 2)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    have h1 : Tendsto (fun η : ℝ => ρs ^ 2 * η ^ 2) (nhds 0)
        (nhds (ρs ^ 2 * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    rw [show ρs ^ 2 * (0 : ℝ) ^ 2 = 0 by ring] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm' hb hg

/-- The volume-normalized RPESM interaction, with total oscillation bounded
by `17/64`, is subextensive: its per-volume oscillation vanishes, so the
fixed-source bundle applies to it. -/
theorem rpesm_bounded_osc_subextensive :
    Tendsto (fun M : ℕ => (17 / 64 : ℝ) / M) atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

end BoundedSourceRemoval

end BoundedSourceRemovalSection

end NCG
