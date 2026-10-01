/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowBranchData
import RenewalGeometry.Gravity.ExactSlowGateExact
import RenewalGeometry.Analysis.QuadraticNewtonCertificate

/-!
# Canonical rank-two factorization of the slope gate and the cokernel obstruction
  (`thm:supp-exact-rank-two-factorization`, `eq:supp-exact-rank-two-factorization`,
  `eq:supp-exact-rank-two-bound`, `cor:supp-exact-slope-cokernel`,
  `eq:supp-exact-cokernel-constant`, `eq:supp-exact-cokernel-no-root`;
  emergent-spacetime manuscript)

All objects are the abstract encodings of `Gravity/ExactSlowBranchData.lean`, with the
hypotheses of `ExactSlowGate.original_slope_jets` (`prop:supp-exact-original-slope-jets`):
`Ξ(r, y) = 𝖤 r + J_g γ(r, y) + J_H y` with `γ` of class `C²`, `γ(0) = 0`, `𝔠_g ∘ Ξ = 0`
near `0`, `𝔠_g, 𝔠_H` of class `C²`, `f` differentiable at `0`, `D𝔠_g(0) J_H = 0`, and a left
inverse `𝒜_g⁻¹` of `𝒜_g = D𝔠_g(0) J_g`; `𝒞_g = D𝔠_H(0) J_g`, `𝒞 = 𝒞_g 𝒜_g⁻¹`,
`ℛ(c) = 2 𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)`, and `𝒬_can(c)` is the slope polynomial of
the reduced functions, `q_{0,can} = 𝒬_can(0)` (`slopeCan`).

**Ward input.** The paper's proof removes the harmonic-row Hessian contribution
`2 D²𝔠_H(0)[b_*, J_H c] + D²𝔠_H(0)[J_H c, J_H c]` by
`thm:supp-exact-harmonic-q4-zero` (base-uniform harmonic quartic annihilation: the
constant-shift row has no coefficient in a pure harmonic direction `J_H c` at any small
second-record base, hence also no base derivative).  That theorem rests on the explicit
finite action and is not formalised; it enters here as the hypothesis
`HarmonicAnnihilation`: `D𝔠_H(Ξ(q))[J_H c] = 0` for all bases `Ξ(q)` near `0` on the
elimination graph.  (`harmonicAnnihilation_sndDeriv` differentiates it in the base
direction, giving `D²𝔠_H(0)[DΞ(0) u, J_H c] = 0`, in particular for `u` giving `b_*` and
`J_H c'`.)

Results:
* `slopeCan_rank_two_factorization_of_hessian`, `slopeCan_rank_two_factorization`:
  `𝒬_can(c) = q_{0,can} - 𝒞 ℛ(c)` (`eq:supp-exact-rank-two-factorization`);
* `slopeCan_hasFDerivAt`, `slopeCan_rank_le`, `slopeCan_rank_le_two`:
  `D𝒬_can(c) = -𝒞 Dℛ(c)` and `rank D𝒬_can(c) ≤ rank 𝒞_g ≤ dim 𝒵_g = 2`
  (`eq:supp-exact-rank-two-bound`);
* `slopeCan_cokernel_constant`, `slopeCan_no_root`: the two clauses of
  `cor:supp-exact-slope-cokernel` (covector `λ` with `λ ∘ 𝒞_g = 0`, i.e. `λ ∈ ker 𝒞_gᵀ`);
* `slopeCan_floor`: for an inner-product harmonic output space,
  `‖𝒬_can(c)‖ ≥ ‖q_{0,can} - P_{Ran 𝒞_g} q_{0,can}‖` (abstract form of
  `eq:supp-finite-range-floor`; the coordinate form is `Algebra/FiniteRangeTestExact.lean`).
-/

namespace RenewalGeometry
namespace ExactSlowRankTwo

open ExactSlowBranch ExactSlowGate Filter Topology Module

variable {R Y Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- The canonical slope polynomial `𝒬_can(c)` of the reduced functions
`𝓕 = L_X f ∘ Ξ`, `𝓗 = 𝔠_H ∘ Ξ` (`eq:supp-exact-slope-polynomial`, physical row
convention), with `v = 𝓕(0, 0)` passed as a parameter. -/
noncomputable def slopeCan (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cH : V → Ho) (f : V → Xs) (LX : Xs →L[ℝ] R) (v : R) (c : Y) : Ho :=
  slopePolynomial (reducedDrift LX f (reducedChart E Jg JH γ))
    (reducedHarmonic cH (reducedChart E Jg JH γ)) v c

/-- The Ward input of `thm:supp-exact-rank-two-factorization`, i.e. the conclusion of
`thm:supp-exact-harmonic-q4-zero` in the encoding: at every second-record base `Ξ(q)`
near `0` on the elimination graph, the harmonic row has no derivative in a pure harmonic
weak direction `J_H c`. -/
def HarmonicAnnihilation (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cH : V → Ho) : Prop :=
  ∀ c : Y, ∀ᶠ q in 𝓝 (0 : R × Y), fderiv ℝ cH (reducedChart E Jg JH γ q) (JH c) = 0

/-- Base derivative of the harmonic annihilation: `D²𝔠_H(0)[DΞ(0) u, J_H c] = 0`
("its derivative with respect to any admissible second-record base direction also
vanishes"). -/
theorem harmonicAnnihilation_sndDeriv (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cH : V → Ho) (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcH : ContDiffAt ℝ 2 cH 0) (hW : HarmonicAnnihilation E Jg JH γ cH) (u : R × Y) (c : Y) :
    sndDeriv cH 0 (fderiv ℝ (reducedChart E Jg JH γ) 0 u) (JH c) = 0 := by
  set Ξ := reducedChart E Jg JH γ
  have hΞ0 : Ξ 0 = 0 := by simp [Ξ, reducedChart, hγ0]
  have hΞd : DifferentiableAt ℝ Ξ 0 :=
    (reducedChart_contDiffAt E Jg JH hγ).differentiableAt two_ne_zero
  have hD2 : HasFDerivAt (fderiv ℝ cH) (fderiv ℝ (fderiv ℝ cH) 0) (Ξ 0) := by
    rw [hΞ0]
    exact ((hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hd : HasFDerivAt (fun q => fderiv ℝ cH (Ξ q) (JH c))
      ((ContinuousLinearMap.apply ℝ Ho (JH c)).comp
        ((fderiv ℝ (fderiv ℝ cH) 0).comp (fderiv ℝ Ξ 0))) 0 :=
    (ContinuousLinearMap.apply ℝ Ho (JH c)).hasFDerivAt.comp 0 (hD2.comp 0 hΞd.hasFDerivAt)
  have hz : fderiv ℝ (fun q => fderiv ℝ cH (Ξ q) (JH c)) 0 = 0 :=
    fderiv_of_eventually_zero _ 0 (hW c)
  rw [hd.fderiv] at hz
  have := congrArg (fun T => T u) hz
  simpa [sndDeriv] using this

/-- First derivative of the reduced chart along the elimination graph:
`DΞ(0)(r, y) = Ê r + J_H y`. -/
theorem reducedChart_fderiv_zero (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V) (JH : Y →L[ℝ] V)
    (γ : R × Y → Zg) (cg : V → Zg) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0) (hcg : ContDiffAt ℝ 2 cg 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z) (r : R) (y : Y) :
    fderiv ℝ (reducedChart E Jg JH γ) 0 (r, y) = hatE E Jg AgInv (fderiv ℝ cg 0) r + JH y := by
  set Ξ := reducedChart E Jg JH γ
  have hΞ0 : Ξ 0 = 0 := by simp [Ξ, reducedChart, hγ0]
  have hΞd : DifferentiableAt ℝ Ξ 0 :=
    (reducedChart_contDiffAt E Jg JH hγ).differentiableAt two_ne_zero
  have hγd : DifferentiableAt ℝ γ 0 := hγ.differentiableAt two_ne_zero
  have hcg2 : DifferentiableAt ℝ cg (Ξ 0) := hΞ0 ▸ hcg.differentiableAt two_ne_zero
  have hDΞ : ∀ q : R × Y, fderiv ℝ Ξ 0 q = E q.1 + Jg (fderiv ℝ γ 0 q) + JH q.2 := by
    intro q
    rw [(reducedChart_hasFDerivAt E Jg JH hγd.hasFDerivAt).fderiv]
    simp
  have hfirst : ∀ q, fderiv ℝ cg 0 (fderiv ℝ Ξ 0 q) = 0 := by
    intro q
    have h := fderiv_of_eventually_zero (cg ∘ Ξ) 0 himp
    rw [fderiv_comp 0 hcg2 hΞd, hΞ0] at h
    simpa using congrArg (fun T => T q) h
  have h := hfirst (r, y)
  rw [hDΞ, map_add, map_add, hJH, add_zero] at h
  have hγ1 : fderiv ℝ γ 0 (r, y) = -AgInv (fderiv ℝ cg 0 (E r)) := by
    rw [← hAg (fderiv ℝ γ 0 (r, y)), eq_neg_of_add_eq_zero_right h, map_neg]
  rw [hDΞ, hγ1]
  simp [hatE, sub_eq_add_neg]

/-- **`eq:supp-exact-rank-two-factorization` from the second-order Ward identities.**
Under the hypotheses of `original_slope_jets`, if the harmonic row Hessian vanishes on
`(b_*, J_H c)` and on `(J_H c, J_H c')`, then `𝒬_can(c) = q_{0,can} - 𝒞 ℛ(c)`. -/
theorem slopeCan_rank_two_factorization_of_hessian (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z) (v : R)
    (hWb : ∀ c, sndDeriv cH 0 (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) (JH c) = 0)
    (hWH : ∀ c c', sndDeriv cH 0 (JH c) (JH c') = 0) (c : Y) :
    slopeCan E Jg JH γ cH f LX v c
      = slopeCan E Jg JH γ cH f LX v 0
        - scriptC ((fderiv ℝ cH 0).comp Jg) AgInv
            (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c) := by
  unfold slopeCan
  rw [original_slope_jets E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg v c,
    original_slope_jets E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg v 0]
  have hsH : ∀ a b, sndDeriv cH 0 a b = sndDeriv cH 0 b a :=
    fun a b => hcH.isSymmSndFDerivAt (by simp) a b
  have hsg : ∀ a b, sndDeriv cg 0 a b = sndDeriv cg 0 b a :=
    fun a b => hcg.isSymmSndFDerivAt (by simp) a b
  simp only [slopeDirection, scriptC, scriptR, gTwo, map_zero, add_zero,
    ContinuousLinearMap.comp_apply]
  set bs := slopeBase E Jg AgInv (fderiv ℝ cg 0) v
  set h := JH c
  have e1 := hsH h bs
  have e2 := hsg h bs
  have w1 := hWb c
  have w2 := hWH c c
  unfold sndDeriv at e1 e2 w1 w2 ⊢
  simp only [map_add, add_apply]
  rw [e1, e2, w1, w2]
  simp only [map_smul]
  module

/-- **`thm:supp-exact-rank-two-factorization`, `eq:supp-exact-rank-two-factorization`.**
On the branch (hypotheses of `original_slope_jets`) with the harmonic annihilation of
`thm:supp-exact-harmonic-q4-zero` (`HarmonicAnnihilation`),
`𝒬_can(c) = q_{0,can} - 𝒞 ℛ(c)` with `𝒞 = 𝒞_g 𝒜_g⁻¹`, `𝒞_g = D𝔠_H(0) J_g`,
`ℛ(c) = 2 𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)`, `b_* = Ê v`. -/
theorem slopeCan_rank_two_factorization (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R) (c : Y) :
    slopeCan E Jg JH γ cH f LX v c
      = slopeCan E Jg JH γ cH f LX v 0
        - scriptC ((fderiv ℝ cH 0).comp Jg) AgInv
            (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c) := by
  have hD := reducedChart_fderiv_zero E Jg JH γ cg AgInv hγ hγ0 hcg himp hJH hAg
  refine slopeCan_rank_two_factorization_of_hessian E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg
    hcH hf himp hJH hAg v (fun c => ?_) (fun c c' => ?_) c
  · have h := harmonicAnnihilation_sndDeriv E Jg JH γ cH hγ hγ0 hcH hW (v, 0) c
    rwa [hD, map_zero, add_zero] at h
  · have h := harmonicAnnihilation_sndDeriv E Jg JH γ cH hγ hγ0 hcH hW (0, c) c'
    rwa [hD, map_zero, zero_add] at h

/-- **`eq:supp-exact-rank-two-bound`, derivative.** Under the factorization,
`D𝒬_can(c) = -𝒞 Dℛ(c)`. -/
theorem slopeCan_hasFDerivAt (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R) (c : Y) :
    HasFDerivAt (slopeCan E Jg JH γ cH f LX v)
      (-(scriptC ((fderiv ℝ cH 0).comp Jg) AgInv).comp
        (fderiv ℝ (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v)) c)) c := by
  set Rm := scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v)
  set S := scriptC ((fderiv ℝ cH 0).comp Jg) AgInv
  have hfun : slopeCan E Jg JH γ cH f LX v = fun c => slopeCan E Jg JH γ cH f LX v 0 - S (Rm c) :=
    funext fun c => slopeCan_rank_two_factorization E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH
      hf himp hJH hAg hW v c
  have hR : HasFDerivAt Rm (fderiv ℝ Rm c) c :=
    ((QuadraticNewton.scriptR_contDiff cg JH _ (n := 1)).differentiable one_ne_zero c).hasFDerivAt
  rw [hfun]
  have := (S.hasFDerivAt.comp c hR).const_sub (slopeCan E Jg JH γ cH f LX v 0)
  convert this using 1
  ext; simp

/-- **`eq:supp-exact-rank-two-bound`, rank.** `rank D𝒬_can(c) ≤ rank 𝒞_g`. -/
theorem slopeCan_rank_le (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R) (c : Y) :
    LinearMap.rank (fderiv ℝ (slopeCan E Jg JH γ cH f LX v) c : Y →ₗ[ℝ] Ho)
      ≤ LinearMap.rank (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho) := by
  rw [(slopeCan_hasFDerivAt E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg hW
    v c).fderiv]
  set D := fderiv ℝ (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v)) c
  set Cg := (fderiv ℝ cH 0).comp Jg
  have e : (-(scriptC Cg AgInv).comp D : Y →L[ℝ] Ho)
      = Cg.comp (AgInv.comp (-D)) := by
    ext y; simp [scriptC]
  rw [e]
  exact LinearMap.rank_comp_le_left _ _

/-- **`eq:supp-exact-rank-two-bound`, `rank 𝒞_g ≤ 2`.** With `dim 𝒵_g = 2`,
`rank D𝒬_can(c) ≤ rank 𝒞_g ≤ 2`. -/
theorem slopeCan_rank_le_two [FiniteDimensional ℝ Zg] (h2 : finrank ℝ Zg = 2)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R) (c : Y) :
    LinearMap.rank (fderiv ℝ (slopeCan E Jg JH γ cH f LX v) c : Y →ₗ[ℝ] Ho)
        ≤ LinearMap.rank (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho) ∧
      LinearMap.rank (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho) ≤ 2 := by
  refine ⟨slopeCan_rank_le E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH hAg hW v c,
    ?_⟩
  set Cg : Zg →ₗ[ℝ] Ho := (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho)
  calc LinearMap.rank Cg = (finrank ℝ (LinearMap.range Cg) : Cardinal) :=
        (finrank_eq_rank _ _).symm
    _ ≤ (finrank ℝ Zg : Cardinal) := Nat.cast_le.mpr (LinearMap.finrank_range_le _)
    _ = 2 := by rw [h2]; rfl

/-- **`cor:supp-exact-slope-cokernel`, `eq:supp-exact-cokernel-constant`.** For every
covector `λ` with `λ ∘ 𝒞_g = 0` (`λ ∈ ker 𝒞_gᵀ`), `λ(𝒬_can(c)) = λ(q_{0,can})` for all
`c`. -/
theorem slopeCan_cokernel_constant (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R)
    (lam : Ho →ₗ[ℝ] ℝ) (hlam : ∀ z, lam (fderiv ℝ cH 0 (Jg z)) = 0) (c : Y) :
    lam (slopeCan E Jg JH γ cH f LX v c) = lam (slopeCan E Jg JH γ cH f LX v 0) := by
  rw [slopeCan_rank_two_factorization E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp hJH
    hAg hW v c, map_sub]
  simp [scriptC, hlam]

/-- **`cor:supp-exact-slope-cokernel`, `eq:supp-exact-cokernel-no-root`.** If
`q_{0,can} ∉ Ran 𝒞_g` then `𝒬_can(c) ≠ 0` for every `c`. -/
theorem slopeCan_no_root (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R)
    (hq0 : slopeCan E Jg JH γ cH f LX v 0 ∉
      LinearMap.range (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho)) (c : Y) :
    slopeCan E Jg JH γ cH f LX v c ≠ 0 := by
  intro h0
  apply hq0
  have h := slopeCan_rank_two_factorization E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf himp
    hJH hAg hW v c
  rw [h0, eq_comm, sub_eq_zero] at h
  exact ⟨AgInv (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c), by
    rw [h]; rfl⟩

section Floor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Floor (abstract form of `eq:supp-finite-range-floor`).** For an inner-product
harmonic output space and finite-dimensional `𝒵_g`, the factorization gives
`‖𝒬_can(c)‖ ≥ ‖q_{0,can} - P q_{0,can}‖ = ‖e_*‖`, `P` the orthogonal projection onto
`Ran 𝒞_g`. -/
theorem slopeCan_floor [FiniteDimensional ℝ Zg] (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → H) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R) (c : Y) :
    ‖slopeCan E Jg JH γ cH f LX v 0
        - (LinearMap.range (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] H) : Zg →ₗ[ℝ] H)).starProjection
          (slopeCan E Jg JH γ cH f LX v 0)‖
      ≤ ‖slopeCan E Jg JH γ cH f LX v c‖ := by
  set K := LinearMap.range (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] H) : Zg →ₗ[ℝ] H)
  set q0 := slopeCan E Jg JH γ cH f LX v 0
  rw [Submodule.starProjection_minimal, slopeCan_rank_two_factorization E Jg JH γ cg cH f LX
    AgInv hγ hγ0 hcg hcH hf himp hJH hAg hW v c]
  have hw : scriptC ((fderiv ℝ cH 0).comp Jg) AgInv
      (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c) ∈ K :=
    ⟨AgInv (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c), rfl⟩
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨_, hw⟩ : K)

end Floor

end ExactSlowRankTwo
end RenewalGeometry
