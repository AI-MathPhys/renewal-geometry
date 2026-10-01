/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowRankTwoExact
import RenewalGeometry.Analysis.QuadraticNewtonCertificate

/-!
# Two-equation physical slope reduction
  (`thm:supp-exact-two-equation-slope`, `eq:supp-exact-rank-two-membership`,
  `eq:supp-exact-two-equation-slope`; emergent-spacetime manuscript)

Setting of `Gravity/ExactSlowRankTwoExact.lean`: the canonical slope polynomial
`𝒬_can = slopeCan`, `𝒞 = 𝒞_g 𝒜_g⁻¹` (`scriptC`), `𝒞_g = D𝔠_H(0) J_g`, and the two-row quadratic
map `ℛ(c) = 2 𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)` (`scriptR`).

* `scriptC_injective`: under `eq:supp-exact-rank-two-membership` (`rank 𝒞_g = 2 = dim 𝒵_g`),
  `𝒞` is injective (`𝒜_g⁻¹` is a left, hence two-sided, inverse on the finite-dimensional
  `𝒵_g`), so `y₀` with `𝒞 y₀ = q_{0,can}` exists (`q_{0,can} ∈ Ran 𝒞_g`) and is unique
  (`exists_unique_y0`).
* `two_equation_slope_iff_of_factorization`: from the factorization
  `𝒬_can(c) = q_{0,can} - 𝒞 ℛ(c)` alone, `𝒬_can(c) = 0 ↔ ℛ(c) = y₀`.
* `regular_level_curve`: a general regular-level-set statement in the analytic class: for an
  analytic `F : Y → Z`, `dim Y = 3`, `dim Z = 2`, at a point `c₀` of `{F = y₀}` where
  `DF(c₀)` has rank two there are linear coordinates `c = c₀ + E y + s n`
  (`(s, y) ↦ s n + E y` a linear isomorphism `ℝ × Z ≃ Y`) and an analytic `ψ`, `ψ(0) = 0`,
  such that near `c₀` the level set is exactly the graph `y = ψ(s)`: a one-dimensional
  real-analytic submanifold.
* `two_equation_slope`: **`thm:supp-exact-two-equation-slope`** on the branch of
  `slopeCan_rank_two_factorization` (hypotheses of `ExactSlowGate.original_slope_jets` plus
  `HarmonicAnnihilation`, the encoded conclusion of `thm:supp-exact-harmonic-q4-zero`):
  both the equivalence and the local one-dimensional analytic structure of the zero set of
  `𝒬_can` at every root where `Dℛ` has rank two.

Status: the factorization input is `HarmonicAnnihilation`, i.e. the still-open
`thm:supp-exact-harmonic-q4-zero`; under the strict corollary policy the record stays
conditional on that theorem.
-/

open Filter Topology Module
open scoped ContDiff

namespace RenewalGeometry
namespace ExactTwoEquationSlope

open ExactSlowBranch ExactSlowGate ExactSlowRankTwo QuadraticNewton

/-! ## Linear algebra of the membership condition -/

section Membership

variable {Zg Ho : Type*} [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- A left inverse of an endomorphism of a finite-dimensional space is injective. -/
theorem leftInverse_injective [FiniteDimensional ℝ Zg] (A AgInv : Zg →L[ℝ] Zg)
    (hAg : ∀ z, AgInv (A z) = z) : Function.Injective AgInv := by
  have hs : Function.Surjective (AgInv : Zg →ₗ[ℝ] Zg) := fun z => ⟨A z, hAg z⟩
  exact LinearMap.injective_iff_surjective.mpr hs

/-- `rank 𝒞_g = dim 𝒵_g` makes `𝒞_g` injective. -/
theorem injective_of_finrank_range_eq [FiniteDimensional ℝ Zg] (Cg : Zg →L[ℝ] Ho)
    (hrank : finrank ℝ (LinearMap.range (Cg : Zg →ₗ[ℝ] Ho)) = finrank ℝ Zg) :
    Function.Injective Cg := by
  have h := (Cg : Zg →ₗ[ℝ] Ho).finrank_range_add_finrank_ker
  rw [hrank] at h
  have hk : finrank ℝ (LinearMap.ker (Cg : Zg →ₗ[ℝ] Ho)) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hk
  exact LinearMap.ker_eq_bot.mp hk

/-- **`𝒞` is an isomorphism onto its range** under `eq:supp-exact-rank-two-membership`. -/
theorem scriptC_injective [FiniteDimensional ℝ Zg] (Cg : Zg →L[ℝ] Ho) (A AgInv : Zg →L[ℝ] Zg)
    (hAg : ∀ z, AgInv (A z) = z)
    (hrank : finrank ℝ (LinearMap.range (Cg : Zg →ₗ[ℝ] Ho)) = finrank ℝ Zg) :
    Function.Injective (scriptC Cg AgInv) :=
  (injective_of_finrank_range_eq Cg hrank).comp (leftInverse_injective A AgInv hAg)

/-- **Definition of `y₀`.** If `q₀ ∈ Ran 𝒞_g` and `rank 𝒞_g = dim 𝒵_g`, there is a unique
`y₀ ∈ 𝒵_g` with `𝒞 y₀ = q₀`. -/
theorem exists_unique_y0 [FiniteDimensional ℝ Zg] (Cg : Zg →L[ℝ] Ho) (A AgInv : Zg →L[ℝ] Zg)
    (hAg : ∀ z, AgInv (A z) = z)
    (hrank : finrank ℝ (LinearMap.range (Cg : Zg →ₗ[ℝ] Ho)) = finrank ℝ Zg) (q₀ : Ho)
    (hq₀ : q₀ ∈ LinearMap.range (Cg : Zg →ₗ[ℝ] Ho)) :
    ∃! y₀ : Zg, scriptC Cg AgInv y₀ = q₀ := by
  have hinj := leftInverse_injective A AgInv hAg
  have hsurj : Function.Surjective (AgInv : Zg →ₗ[ℝ] Zg) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨z, hz⟩ := hq₀
  obtain ⟨y₀, hy₀⟩ := hsurj z
  refine ⟨y₀, ?_, fun y hy => scriptC_injective Cg A AgInv hAg hrank ?_⟩
  · simp only [scriptC, ContinuousLinearMap.comp_apply]
    rw [show AgInv y₀ = z from hy₀]
    exact hz
  · rw [hy]
    simp only [scriptC, ContinuousLinearMap.comp_apply]
    rw [show AgInv y₀ = z from hy₀]
    exact hz.symm

/-- **`eq:supp-exact-two-equation-slope` from the factorization.**  If
`Q(c) = q₀ - 𝒞 ℛ(c)` with `𝒞` injective and `𝒞 y₀ = q₀`, then `Q(c) = 0 ↔ ℛ(c) = y₀`. -/
theorem two_equation_slope_iff_of_factorization {Y : Type*} (Q : Y → Ho) (Rm : Y → Zg)
    (C : Zg →L[ℝ] Ho) (hC : Function.Injective C) (q₀ : Ho) (y₀ : Zg) (hy₀ : C y₀ = q₀)
    (hfact : ∀ c, Q c = q₀ - C (Rm c)) (c : Y) :
    Q c = 0 ↔ Rm c = y₀ := by
  rw [hfact, sub_eq_zero, ← hy₀]
  exact ⟨fun h => (hC h).symm, fun h => by rw [h]⟩

end Membership

/-! ## Regular level sets of analytic maps `ℝ³ → ℝ²` -/

section LevelCurve

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- **Regular level curve.** Let `F : Y → Z` be analytic (`C^ω`) with `dim Y = 3`,
`dim Z = 2`, `F c₀ = y₀`, and `rank DF(c₀) = 2`.  Then there are `E : Z →L Y` and `n : Y`
such that `(s, y) ↦ s n + E y` is a linear isomorphism `ℝ × Z → Y`, `DF(c₀) E = id`,
`DF(c₀) n = 0`, and an analytic `ψ : ℝ → Z` with `ψ 0 = 0` such that, near `(0, 0)`,
`F (c₀ + E y + s n) = y₀ ↔ ψ s = y`: the level set is locally a one-dimensional
real-analytic submanifold (the graph of `ψ` in these linear coordinates). -/
theorem regular_level_curve (F : Y → Z) (hF : ContDiff ℝ ω F) (hY : finrank ℝ Y = 3)
    (hZ : finrank ℝ Z = 2) (c₀ : Y) (y₀ : Z) (hc₀ : F c₀ = y₀)
    (hrank : finrank ℝ (LinearMap.range (fderiv ℝ F c₀ : Y →ₗ[ℝ] Z)) = 2) :
    ∃ (Esl : Z →L[ℝ] Y) (n : Y),
      Function.Bijective (fun p : ℝ × Z => p.1 • n + Esl p.2) ∧
      (∀ y, fderiv ℝ F c₀ (Esl y) = y) ∧ fderiv ℝ F c₀ n = 0 ∧
      ∃ ψ : ℝ → Z, ψ 0 = 0 ∧ (∀ᶠ s in 𝓝 (0 : ℝ), AnalyticAt ℝ ψ s) ∧
        ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : Z)), F (c₀ + Esl p.2 + p.1 • n) = y₀ ↔ ψ p.1 = p.2 := by
  set D := fderiv ℝ F c₀ with hDdef
  -- `D` is onto and its kernel is a line
  have hrange : LinearMap.range (D : Y →ₗ[ℝ] Z) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, hZ])
  have hker : finrank ℝ (LinearMap.ker (D : Y →ₗ[ℝ] Z)) = 1 := by
    have := (D : Y →ₗ[ℝ] Z).finrank_range_add_finrank_ker
    omega
  obtain ⟨n, hnK, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := LinearMap.ker (D : Y →ₗ[ℝ] Z)) (by
      intro h
      rw [h, finrank_bot] at hker
      exact absurd hker (by norm_num))
  have hDn : D n = 0 := hnK
  -- a complement `C` of the kernel, on which `D` is an isomorphism
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (D : Y →ₗ[ℝ] Z))
  have hCdim : finrank ℝ C = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    omega
  set DC : C →ₗ[ℝ] Z := (D : Y →ₗ[ℝ] Z).comp C.subtype
  have hDCinj : Function.Injective DC := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxK : (x : Y) ∈ LinearMap.ker (D : Y →ₗ[ℝ] Z) := hx
    have : (x : Y) ∈ LinearMap.ker (D : Y →ₗ[ℝ] Z) ⊓ C := ⟨hxK, x.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hDCbij : Function.Bijective DC :=
    ⟨hDCinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hCdim, hZ])).mp hDCinj⟩
  set e : C ≃ₗ[ℝ] Z := LinearEquiv.ofBijective DC hDCbij
  set Esl : Z →L[ℝ] Y := LinearMap.toContinuousLinearMap (C.subtype.comp e.symm.toLinearMap)
  have hDE : ∀ y, D (Esl y) = y := by
    intro y
    have h1 : D (Esl y) = DC (e.symm y) := rfl
    rw [h1]
    exact e.apply_symm_apply y
  -- the coordinate map `(s, y) ↦ s n + E y` is a linear isomorphism
  set Lc : ℝ × Z →ₗ[ℝ] Y :=
    ((LinearMap.lsmul ℝ Y).flip n).comp (LinearMap.fst ℝ ℝ Z)
      + (Esl : Z →ₗ[ℝ] Y).comp (LinearMap.snd ℝ ℝ Z)
  have hLc : ∀ p : ℝ × Z, Lc p = p.1 • n + Esl p.2 := fun p => rfl
  have hLinj : Function.Injective Lc := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, y⟩ h
    rw [hLc] at h
    have hy : y = 0 := by
      have := congrArg D h
      rwa [map_add, map_smul, hDn, smul_zero, zero_add, hDE, map_zero] at this
    subst hy
    simp only [map_zero, add_zero, smul_eq_zero, hn0, or_false] at h
    simp [h]
  have hLbij : Function.Bijective Lc :=
    ⟨hLinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_prod, finrank_self, hZ, hY])).mp hLinj⟩
  refine ⟨Esl, n, ?_, hDE, hDn, ?_⟩
  · have hfun : (fun p : ℝ × Z => p.1 • n + Esl p.2) = Lc := funext fun p => (hLc p).symm
    rw [hfun]
    exact hLbij
  -- the analytic root curve
  set G : ℝ × Z → Z := fun p => F (c₀ + Esl p.2 + p.1 • n) - y₀
  have hA : ContDiff ℝ ω fun p : ℝ × Z => c₀ + Esl p.2 + p.1 • n :=
    (contDiff_const.add (Esl.contDiff.comp contDiff_snd)).add (contDiff_fst.smul contDiff_const)
  have hG : ContDiff ℝ ω G := (hF.comp hA).sub contDiff_const
  have hroot : G (0, 0) = 0 := by simp [G, hc₀]
  -- `∂_y G (0, 0) = D E = id`
  have hAd : HasFDerivAt (fun p : ℝ × Z => c₀ + Esl p.2 + p.1 • n)
      (Esl.comp (ContinuousLinearMap.snd ℝ ℝ Z)
        + (ContinuousLinearMap.fst ℝ ℝ Z).smulRight n) ((0 : ℝ), (0 : Z)) := by
    have h1 : HasFDerivAt (fun p : ℝ × Z => Esl p.2) (Esl.comp (ContinuousLinearMap.snd ℝ ℝ Z))
        ((0 : ℝ), (0 : Z)) := (Esl.comp (ContinuousLinearMap.snd ℝ ℝ Z)).hasFDerivAt
    have h2 : HasFDerivAt (fun p : ℝ × Z => p.1 • n)
        ((ContinuousLinearMap.fst ℝ ℝ Z).smulRight n) ((0 : ℝ), (0 : Z)) :=
      ((ContinuousLinearMap.fst ℝ ℝ Z).smulRight n).hasFDerivAt
    exact (h1.const_add c₀).add h2
  have hFd : HasFDerivAt F D (c₀ + Esl (0 : Z) + (0 : ℝ) • n) := by
    simp only [map_zero, add_zero, zero_smul]
    exact ((hF.differentiable (by simp)) c₀).hasFDerivAt
  have hGd : HasFDerivAt G (D.comp (Esl.comp (ContinuousLinearMap.snd ℝ ℝ Z)
        + (ContinuousLinearMap.fst ℝ ℝ Z).smulRight n)) ((0 : ℝ), (0 : Z)) :=
    (hFd.comp ((0 : ℝ), (0 : Z)) hAd).sub_const y₀
  have hinv : ((fderiv ℝ G ((0 : ℝ), (0 : Z))).comp
      (ContinuousLinearMap.inr ℝ ℝ Z)).IsInvertible := by
    rw [hGd.fderiv]
    have hid : (D.comp (Esl.comp (ContinuousLinearMap.snd ℝ ℝ Z)
        + (ContinuousLinearMap.fst ℝ ℝ Z).smulRight n)).comp
          (ContinuousLinearMap.inr ℝ ℝ Z) = ContinuousLinearMap.id ℝ Z := by
      ext y
      simp [hDE]
    rw [hid]
    exact ⟨ContinuousLinearEquiv.refl ℝ Z, rfl⟩
  obtain ⟨ψ, hψ0, hψan, -, hψiff⟩ :=
    analytic_root_continuation G 0 0 hG.contDiffAt hroot hinv
  refine ⟨ψ, hψ0, hψan, ?_⟩
  filter_upwards [hψiff] with p hp
  rw [← hp]
  simp only [G, sub_eq_zero]

end LevelCurve

/-! ## `thm:supp-exact-two-equation-slope` on the rank-two branch -/

section Slope

variable {R Y Zg V Xs Ho : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- **`thm:supp-exact-two-equation-slope`, `eq:supp-exact-two-equation-slope`.**
On the branch of `slopeCan_rank_two_factorization` (hypotheses of `original_slope_jets` and
`HarmonicAnnihilation`), assume `eq:supp-exact-rank-two-membership`: `dim 𝒵_g = 2`,
`rank 𝒞_g = 2`, and let `y₀` satisfy `𝒞 y₀ = q_{0,can}` (it exists and is unique when
`q_{0,can} ∈ Ran 𝒞_g`, `exists_unique_y0`).  Then
1. `𝒬_can(c) = 0 ↔ ℛ(c) = y₀` for every `c`;
2. if `dim Y = 3` (the harmonic slope space `ℝ³`), at every root `c₀` of `𝒬_can` where
   `Dℛ(c₀)` has rank two, the zero set of `𝒬_can` is locally a one-dimensional real-analytic
   submanifold: in linear coordinates `c = c₀ + E y + s n` (`(s, y) ↦ s n + E y` a linear
   isomorphism `ℝ × 𝒵_g ≃ Y`) it is near `c₀` the graph `y = ψ(s)` of an analytic `ψ` with
   `ψ(0) = 0`. -/
theorem two_equation_slope [FiniteDimensional ℝ Zg] (hZg : finrank ℝ Zg = 2)
    (E : R →L[ℝ] V) (Jg : Zg →L[ℝ] V)
    (JH : Y →L[ℝ] V) (γ : R × Y → Zg) (cg : V → Zg) (cH : V → Ho) (f : V → Xs)
    (LX : Xs →L[ℝ] R) (AgInv : Zg →L[ℝ] Zg)
    (hγ : ContDiffAt ℝ 2 γ 0) (hγ0 : γ 0 = 0)
    (hcg : ContDiffAt ℝ 2 cg 0) (hcH : ContDiffAt ℝ 2 cH 0) (hf : DifferentiableAt ℝ f 0)
    (himp : ∀ᶠ q in 𝓝 (0 : R × Y), cg (reducedChart E Jg JH γ q) = 0)
    (hJH : ∀ y, fderiv ℝ cg 0 (JH y) = 0)
    (hAg : ∀ z, AgInv (fderiv ℝ cg 0 (Jg z)) = z)
    (hW : HarmonicAnnihilation E Jg JH γ cH) (v : R)
    (hrankC : finrank ℝ (LinearMap.range
      (((fderiv ℝ cH 0).comp Jg : Zg →L[ℝ] Ho) : Zg →ₗ[ℝ] Ho)) = 2)
    (y₀ : Zg) (hy₀ : scriptC ((fderiv ℝ cH 0).comp Jg) AgInv y₀ = slopeCan E Jg JH γ cH f LX v 0) :
    (∀ c, slopeCan E Jg JH γ cH f LX v c = 0 ↔
        scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c = y₀) ∧
      ∀ [FiniteDimensional ℝ Y], finrank ℝ Y = 3 → ∀ c₀ : Y,
        slopeCan E Jg JH γ cH f LX v c₀ = 0 →
        finrank ℝ (LinearMap.range (fderiv ℝ
          (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v)) c₀ : Y →ₗ[ℝ] Zg)) = 2 →
        ∃ (Esl : Zg →L[ℝ] Y) (n : Y),
          Function.Bijective (fun p : ℝ × Zg => p.1 • n + Esl p.2) ∧
          ∃ ψ : ℝ → Zg, ψ 0 = 0 ∧ (∀ᶠ s in 𝓝 (0 : ℝ), AnalyticAt ℝ ψ s) ∧
            ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : Zg)),
              slopeCan E Jg JH γ cH f LX v (c₀ + Esl p.2 + p.1 • n) = 0 ↔ ψ p.1 = p.2 := by
  set Cg := (fderiv ℝ cH 0).comp Jg
  have hCinj : Function.Injective (scriptC Cg AgInv) :=
    scriptC_injective Cg ((fderiv ℝ cg 0).comp Jg) AgInv (fun z => hAg z) (by rw [hrankC, hZg])
  have hiff : ∀ c, slopeCan E Jg JH γ cH f LX v c = 0 ↔
      scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v) c = y₀ :=
    two_equation_slope_iff_of_factorization _ _ (scriptC Cg AgInv) hCinj _ y₀ hy₀
      (fun c => slopeCan_rank_two_factorization E Jg JH γ cg cH f LX AgInv hγ hγ0 hcg hcH hf
        himp hJH hAg hW v c)
  refine ⟨hiff, fun hY c₀ hc₀ hrank => ?_⟩
  obtain ⟨Esl, n, hbij, -, -, ψ, hψ0, hψan, hψ⟩ :=
    regular_level_curve (scriptR cg JH (slopeBase E Jg AgInv (fderiv ℝ cg 0) v))
      (scriptR_contDiff cg JH _) hY hZg c₀ y₀ ((hiff c₀).mp hc₀) hrank
  refine ⟨Esl, n, hbij, ψ, hψ0, hψan, ?_⟩
  filter_upwards [hψ] with p hp
  rw [hiff]
  exact hp

end Slope

end ExactTwoEquationSlope
end RenewalGeometry
