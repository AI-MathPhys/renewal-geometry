/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeScalingBlocksExact
import RenewalGeometry.DiscreteAnalysis.ShiftedPlaquetteLogarithmUniformExact

/-!
# Amplitude-preserving scaling: the ν-normalised plaquette is uniformly regular
  (`lem:native-scaling`, gauge sector regularity clause)

`lem:native-scaling` substitutes `ρ = hK`, `ν = K⁻¹` and evaluates the plaquette map of
`lem:native-plaquette` at the arguments `νA`.  The explicit removable quotient
`Q(ρ; X, Y, a, b)` of `ShiftedPlaquetteLogarithmUniformExact` satisfies the exact
factorisation
`Q(ρ; νX, νY, νa, νb) = ν · Q̂(ρ, ν; X, Y, a, b)`  (`quotientPoly_smul`)
with `Q̂` a polynomial in `ρ, ν, X, Y, a, b` and the entire function `E`, hence jointly
analytic in `(ρ, ν, X, Y, a, b)` (`analyticAt_jointNuQuotient`).  Consequently the
normalised field strength
`F̃(ρ, ν; X, Y, a, b) = Q̂ · L(ρ² ν Q̂)`  (`jointNuLogPlaquette`)
satisfies `Φ(ρ; νX, νY, νa, νb) = ν F̃(ρ, ν; X, Y, a, b)` for every `ρ, ν`
(`logPlaquette_smul_eq`), is jointly analytic wherever `‖ρ² ν Q̂‖ < 1`, in particular on a
neighbourhood of `{ρ = 0}` for *all* `ν` (`analyticAt_jointNuLogPlaquette`), and all its
fixed-order derivatives are bounded uniformly for `|ρ| ≤ ρ₀`, `ν ∈ [0, 1]` and parameters in a
compact set (`exists_uniform_nu_iteratedFDeriv_bound`): this is the "uniformly regular for
small `ρ` and `0 ≤ ν ≤ 1`" clause of `lem:native-scaling` for the gauge plaquette, with the
removable factor `ν⁻¹` handled exactly.  On the grid, `F^h[A] = K F̃(ρ, ν; jet of A)`
(`fieldStrength_eq_nu_normalised`), i.e. the Yang–Mills density carries exactly the factor
`K²`.

Scoped hypotheses: `𝔄` a real Banach algebra with `‖1‖ = 1`, as in the companion files.
Not covered (disclosed): the assembly of the four densities of `eq:native-densities`, and the
regularity of the Higgs/Dirac links in `(ρ, ν)`, which need representation-theoretic structure
(`ρ_H`, `ρ_S`, `σ` analytic) not present in `NativeScalingBlocksExact`.
-/

open NormedSpace Filter Topology

namespace RenewalGeometry
namespace ShiftedPlaquette

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- `w(ρ, ν v) = ν w(ρν, v)`. -/
theorem linkExp_smul (ρ ν : ℝ) (v : 𝔄) : linkExp ρ (ν • v) = ν • linkExp (ρ * ν) v := by
  simp only [linkExp, smul_add, smul_smul, smul_pow, smul_mul_assoc]
  module

/-- The ν-normalised explicit quotient `Q̂(ρ, ν; X, Y, a, b)`, with
`Q(ρ; νX, νY, νa, νb) = ν Q̂`: writing `v̂ = (X, Y + ρa, -(X + ρb), -Y)` and
`ŵ_i = w(ρν, v̂_i)`,
`Q̂ = (a - b) + ν Σ_i v̂_i² E(ρν v̂_i) + ν Σ_{i<j} ŵ_i ŵ_j + ρν² Σ_{i<j<k} ŵ_iŵ_jŵ_k + ρ²ν³ ŵ₁ŵ₂ŵ₃ŵ₄`. -/
noncomputable def nuQuotientPoly (ρ ν : ℝ) (X Y a b : 𝔄) : 𝔄 :=
  (a - b) +
    ν • (X ^ 2 * expRemainder ((ρ * ν) • X) +
      (Y + ρ • a) ^ 2 * expRemainder ((ρ * ν) • (Y + ρ • a)) +
      (-(X + ρ • b)) ^ 2 * expRemainder ((ρ * ν) • -(X + ρ • b)) +
      (-Y) ^ 2 * expRemainder ((ρ * ν) • -Y)) +
    ν • (linkExp (ρ * ν) X * linkExp (ρ * ν) (Y + ρ • a) +
      linkExp (ρ * ν) X * linkExp (ρ * ν) (-(X + ρ • b)) +
      linkExp (ρ * ν) X * linkExp (ρ * ν) (-Y) +
      linkExp (ρ * ν) (Y + ρ • a) * linkExp (ρ * ν) (-(X + ρ • b)) +
      linkExp (ρ * ν) (Y + ρ • a) * linkExp (ρ * ν) (-Y) +
      linkExp (ρ * ν) (-(X + ρ • b)) * linkExp (ρ * ν) (-Y)) +
    (ρ * ν ^ 2) • (linkExp (ρ * ν) X * linkExp (ρ * ν) (Y + ρ • a) * linkExp (ρ * ν) (-(X + ρ • b)) +
      linkExp (ρ * ν) X * linkExp (ρ * ν) (Y + ρ • a) * linkExp (ρ * ν) (-Y) +
      linkExp (ρ * ν) X * linkExp (ρ * ν) (-(X + ρ • b)) * linkExp (ρ * ν) (-Y) +
      linkExp (ρ * ν) (Y + ρ • a) * linkExp (ρ * ν) (-(X + ρ • b)) * linkExp (ρ * ν) (-Y)) +
    (ρ ^ 2 * ν ^ 3) • (linkExp (ρ * ν) X * linkExp (ρ * ν) (Y + ρ • a) *
      linkExp (ρ * ν) (-(X + ρ • b)) * linkExp (ρ * ν) (-Y))

/-- **Exact removable factor `ν`:** `Q(ρ; νX, νY, νa, νb) = ν Q̂(ρ, ν; X, Y, a, b)`. -/
theorem quotientPoly_smul (ρ ν : ℝ) (X Y a b : 𝔄) :
    quotientPoly ρ (ν • X) (ν • Y) (ν • a) (ν • b) = ν • nuQuotientPoly ρ ν X Y a b := by
  have h2 : ν • Y + ρ • ν • a = ν • (Y + ρ • a) := by
    rw [smul_add, smul_smul, smul_smul, mul_comm]
  have h3 : -(ν • X + ρ • ν • b) = ν • -(X + ρ • b) := by
    rw [smul_neg, smul_add, smul_smul, smul_smul, mul_comm]
  have h4 : -(ν • Y) = ν • -Y := (smul_neg ν Y).symm
  unfold quotientPoly nuQuotientPoly
  rw [h2, h3, h4]
  simp only [linkExp_smul, smul_pow, smul_smul, smul_mul_assoc, mul_smul_comm]
  module

/-- The normalised quotient as a function of the joint variable `(ρ, ν, X, Y, a, b)`. -/
noncomputable def jointNuQuotient (p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  nuQuotientPoly p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2

/-- The normalised field strength `F̃(ρ, ν; X, Y, a, b) = Q̂ · L(ρ² ν Q̂)`. -/
noncomputable def jointNuLogPlaquette (p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  jointNuQuotient p * logQuotient ((p.1 ^ 2 * p.2.1) • jointNuQuotient p)

/-- `Φ(ρ; νX, νY, νa, νb) = ν F̃(ρ, ν; X, Y, a, b)` for all `ρ, ν`: the removable factor `ν`
of `lem:native-scaling` ("use `lem:native-plaquette` with arguments `νA`; the removable
quotient shows `F^h = K F̃_{ρ,ν}`"). -/
theorem logPlaquette_smul_eq (ρ ν : ℝ) (X Y a b : 𝔄) :
    logPlaquette (ν • X) (ν • Y) (ν • a) (ν • b) ρ = ν • jointNuLogPlaquette (ρ, ν, X, Y, a, b) := by
  simp only [logPlaquette, jointNuLogPlaquette, jointNuQuotient, quotient_eq_quotientPoly,
    quotientPoly_smul, smul_smul, smul_mul_assoc]

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- `Q̂` is jointly analytic in `(ρ, ν, X, Y, a, b)`. -/
theorem analyticAt_jointNuQuotient (p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) :
    AnalyticAt ℝ jointNuQuotient p := by
  unfold jointNuQuotient nuQuotientPoly linkExp
  fun_prop

theorem continuous_jointNuQuotient : Continuous (jointNuQuotient (𝔄 := 𝔄)) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_jointNuQuotient p).continuousAt

/-- `F̃` is jointly analytic wherever `‖ρ² ν Q̂‖ < 1`, in particular at every point with
`ρ = 0` (any `ν`). -/
theorem analyticAt_jointNuLogPlaquette {p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄}
    (hp : ‖(p.1 ^ 2 * p.2.1) • jointNuQuotient p‖ < 1) :
    AnalyticAt ℝ jointNuLogPlaquette p := by
  have hQ := analyticAt_jointNuQuotient p
  have hin : AnalyticAt ℝ (fun q : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      (q.1 ^ 2 * q.2.1) • jointNuQuotient q) p := by
    have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1 ^ 2 * q.2.1) p := by
      fun_prop
    exact h1.smul hQ
  have hL : AnalyticAt ℝ logQuotient ((p.1 ^ 2 * p.2.1) • jointNuQuotient p) :=
    analyticAt_logQuotient hp
  have hcomp : AnalyticAt ℝ (logQuotient ∘ fun q : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      (q.1 ^ 2 * q.2.1) • jointNuQuotient q) p :=
    AnalyticAt.comp (g := logQuotient) (f := fun q : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      (q.1 ^ 2 * q.2.1) • jointNuQuotient q) (x := p) hL hin
  exact hQ.mul hcomp

theorem isOpen_jointNuDomain :
    IsOpen {p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 | ‖(p.1 ^ 2 * p.2.1) • jointNuQuotient p‖ < 1} :=
  isOpen_lt (((continuous_fst.pow 2).mul (continuous_fst.comp continuous_snd)).smul
    continuous_jointNuQuotient).norm continuous_const

/-- **`lem:native-scaling`, regularity clause for the gauge plaquette.**  For every order `k`
and every compact set `K` of parameters `(X, Y, a, b)` there are `ρ₀ > 0` and `C` such that all
`k`-th Fréchet derivatives of the normalised field strength `F̃` in `(ρ, ν, X, Y, a, b)` are
bounded by `C` for `|ρ| ≤ ρ₀`, `ν ∈ [0, 1]` and `(X, Y, a, b) ∈ K`. -/
theorem exists_uniform_nu_iteratedFDeriv_bound (k : ℕ) {K : Set (𝔄 × 𝔄 × 𝔄 × 𝔄)}
    (hK : IsCompact K) :
    ∃ ρ₀ > 0, ∃ C : ℝ, ∀ ρ : ℝ, |ρ| ≤ ρ₀ → ∀ ν ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ k jointNuLogPlaquette (ρ, ν, q)‖ ≤ C := by
  set U := {p : ℝ × ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 | ‖(p.1 ^ 2 * p.2.1) • jointNuQuotient p‖ < 1} with hU
  have hUo : IsOpen U := isOpen_jointNuDomain
  have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ K) ⊆ U := by
    rintro ⟨ρ, ν, q⟩ ⟨hρ, _⟩
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    simp [hU]
  have hKc : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨u, v, huo, -, hu0, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hKc hUo hsub
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp huo 0 (hu0 rfl)
  refine ⟨ρ₀ / 2, by positivity, ?_⟩
  have hSc : IsCompact (Metric.closedBall (0 : ℝ) (ρ₀ / 2) ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ K)) :=
    (isCompact_closedBall _ _).prod hKc
  have hSU : Metric.closedBall (0 : ℝ) (ρ₀ / 2) ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ K) ⊆ U := fun p hp =>
    huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hρ₀) hp.1), hKv hp.2⟩
  have hcd : ContDiffOn ℝ (k : WithTop ℕ∞) jointNuLogPlaquette U := fun p hp =>
    (analyticAt_jointNuLogPlaquette hp).contDiffAt.contDiffWithinAt
  have hcont : ContinuousOn (iteratedFDeriv ℝ k jointNuLogPlaquette) U :=
    (hcd.continuousOn_iteratedFDerivWithin le_rfl hUo.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen k hUo).symm
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hcont.mono hSU)
  refine ⟨C, fun ρ hρ ν hν q hq => hC (ρ, ν, q) ⟨?_, hν, hq⟩⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact hρ

end ShiftedPlaquette

namespace NativeScaling

open ShiftedJetAction (Grid unitVec)

variable {n : ℕ} [NeZero n]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- **`lem:native-scaling`, gauge sector with the removable factor made explicit:**
`F^h[A](x) = K · F̃(hK, K⁻¹; A_μ(x), A_ν(x), δ⁺_{hK} A_ν(x), δ⁺_{hK} A_μ(x))`, so the
Yang–Mills density `⟨F^h, F^h⟩` carries exactly the factor `K²` in front of a uniformly regular
normalised density. -/
theorem fieldStrength_eq_nu_normalised {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0)
    (A : Fin 4 → Grid n → 𝔄) (x : Grid n) (μ ν : Fin 4) :
    fieldStrength h A x μ ν = K • ShiftedPlaquette.jointNuLogPlaquette
      (h * K, K⁻¹, A μ x, A ν x, ShiftedJetAction.fwdDiff (h * K) μ (A ν) x,
        ShiftedJetAction.fwdDiff (h * K) ν (A μ) x) := by
  have hhK : h * K ≠ 0 := mul_ne_zero hh hK
  rw [fieldStrength_scale hK, fieldStrength_eq_logPlaquette hhK]
  have h1 : ∀ (B : Grid n → 𝔄) (lam : Fin 4),
      ShiftedJetAction.fwdDiff (h * K) lam (K⁻¹ • B) x = K⁻¹ • ShiftedJetAction.fwdDiff (h * K) lam B x := by
    intro B lam
    unfold ShiftedJetAction.fwdDiff
    simp only [Pi.smul_apply, smul_sub, smul_smul, mul_comm]
  simp only [Pi.smul_apply]
  rw [h1, h1, ShiftedPlaquette.logPlaquette_smul_eq, smul_smul]
  congr 1
  field_simp

end NativeScaling
end RenewalGeometry
