/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticImplicitFunction
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# Exact two-row elimination: linear critical coordinates and the analytic graph `γ`
  (`lem:supp-exact-two-row-elimination`; emergent-spacetime manuscript)

Abstract data as in `RenewalGeometry/Gravity/ExactSlowBranchData.lean` (`Φ₀ = C_red ⊕ B`, the
weak decomposition `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ`, `ker B = 𝒵_g ⊕ ℋ`, the setup coupling test
`p_H C_red = 0`), an isomorphism `X : R → 𝒳 = ker (p_g C_red)` and a right inverse `B^#` of `B`
on `Ran B`.

* `linearCriticalCoordinates` is `Ξ₀(r, z_g, y) = 𝖤 r + J_g z_g + J_H y` with
  `𝖤 r = (X r, -B^# C_red X r)` (`eq:supp-exact-linear-critical-coordinates`);
* `linearCriticalCoordinates_injective`, `mem_ker_leadingConstraint_iff`: `Ξ₀` is injective with
  range exactly `𝒦₀ = ker Φ₀` (the linear statement of the lemma);
* `two_row_elimination_graph`: for an analytic `𝔠_g` with `𝔠_g(0) = 0` and invertible
  `𝒜_g = D𝔠_g(0) J_g`, there is a unique local analytic `γ(r, y) ∈ 𝒵_g`, `γ(0,0) = 0`, with
  `𝔠_g(Ξ(r, y)) = 0` for `Ξ = 𝖤 r + J_g γ + J_H y` (`eq:supp-exact-Xi-reduced`), by the analytic
  implicit function theorem of `RenewalGeometry/Analysis/AnalyticImplicitFunction.lean`; and if
  moreover `D𝔠_g(0) J_H = 0` then `γ_y(0, 0) = 0`.

Status note: the hypotheses `𝒜_g ∈ GL₂` and `D𝔠_g(0) J_H = 0` are the literal source identities
`eq:supp-exact-slope-entrance`; the harmonic one is derived in the paper from
`thm:supp-exact-harmonic-q4-zero`, which is not yet formalised.
-/

open Filter
open scoped Topology

namespace RenewalGeometry

namespace ExactTwoRowElimination

open ExactSlowBranch

variable {Xs W Zg Hs R : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- `𝖤 r = (X r, -B^# C_red X r)`. -/
def criticalE (Cred : Xs →L[ℝ] W) (Bsh : W →L[ℝ] W) (X : R →L[ℝ] Xs) : R →L[ℝ] Xs × W :=
  X.prod (-(Bsh ∘L Cred ∘L X))

/-- `Ξ₀(r, z_g, y) = 𝖤 r + J_g z_g + J_H y` (`eq:supp-exact-linear-critical-coordinates`), with
the weak insertions `(0, J_g ·)`, `(0, J_H ·)`. -/
def linearCriticalCoordinates (Cred : Xs →L[ℝ] W) (Bsh : W →L[ℝ] W) (X : R →L[ℝ] Xs)
    (Jg : Zg →L[ℝ] W) (JH : Hs →L[ℝ] W) (t : R × Zg × Hs) : Xs × W :=
  criticalE Cred Bsh X t.1 + (0, Jg t.2.1) + (0, JH t.2.2)

section Linear

variable {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs} {Bsh : W →L[ℝ] W} {X : R →L[ℝ] Xs}

/-- `Ξ₀` maps into `𝒦₀ = ker Φ₀` and every element of `𝒦₀` is in its range. -/
theorem mem_ker_leadingConstraint_iff (hD : WeakDecomposition B Jg JH pg pH)
    (hK : KernelSplit B Jg JH) (hHC : ∀ x, pH (Cred x) = 0)
    (hBsh : ∀ z, B (Bsh (B z)) = B z) (hX1 : ∀ r, pg (Cred (X r)) = 0)
    (hX2 : ∀ x, pg (Cred x) = 0 → ∃ r, X r = x) (ξ : Xs × W) :
    leadingConstraint Cred B ξ = 0 ↔
      ∃ t : R × Zg × Hs, linearCriticalCoordinates Cred Bsh X Jg JH t = ξ := by
  have hrange : ∀ r, B (Bsh (Cred (X r))) = Cred (X r) := by
    intro r
    obtain ⟨z, hz⟩ := hD.mem_range_of_proj_zero (hX1 r) (hHC (X r))
    rw [← hz, hBsh]
  constructor
  · intro h
    obtain ⟨x, w⟩ := ξ
    simp only [leadingConstraint_apply] at h
    have hpg : pg (Cred x) = 0 := by
      have := congrArg pg h
      rwa [map_add, hD.pg_B, add_zero, map_zero] at this
    obtain ⟨r, rfl⟩ := hX2 x hpg
    have hker : B (w + Bsh (Cred (X r))) = 0 := by
      rw [map_add, hrange]
      rw [add_comm] at h
      exact h
    obtain ⟨z, y, hzy⟩ := hK.ker_le _ hker
    refine ⟨(r, z, y), ?_⟩
    simp only [linearCriticalCoordinates, criticalE, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, Prod.mk_add_mk, add_zero,
      Prod.mk.injEq, true_and]
    rw [add_assoc, ← hzy]
    abel
  · rintro ⟨⟨r, z, y⟩, rfl⟩
    simp only [linearCriticalCoordinates, criticalE, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, Prod.mk_add_mk, add_zero,
      leadingConstraint_apply, map_add, map_neg, hK.B_Jg, hK.B_JH, hrange]
    abel

/-- `Ξ₀` is injective. -/
theorem linearCriticalCoordinates_injective (hD : WeakDecomposition B Jg JH pg pH)
    (hXinj : Function.Injective X) :
    Function.Injective (linearCriticalCoordinates Cred Bsh X Jg JH) := by
  rintro ⟨r, z, y⟩ ⟨r', z', y'⟩ h
  simp only [linearCriticalCoordinates, criticalE, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, Prod.mk_add_mk, add_zero,
    Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hr : r = r' := hXinj h1
  subst hr
  have h2' : Jg z + JH y = Jg z' + JH y' := by
    have := h2
    rw [add_assoc, add_assoc] at this
    exact add_left_cancel this
  have hz : z = z' := by
    have := congrArg pg h2'
    simpa [hD.pg_Jg, hD.pg_JH] using this
  have hy : y = y' := by
    have := congrArg pH h2'
    simpa [hD.pH_Jg, hD.pH_JH] using this
  rw [hz, hy]

end Linear

section Graph

variable [CompleteSpace Xs] [CompleteSpace W] [CompleteSpace Zg] [CompleteSpace Hs]
  [CompleteSpace R]

/-- The affine map `((r, y), z) ↦ 𝖤 r + J_g z + J_H y`, as a continuous linear map. -/
def chartLinear (E : R →L[ℝ] Xs × W) (Jg' : Zg →L[ℝ] Xs × W) (JH' : Hs →L[ℝ] Xs × W) :
    (R × Hs) × Zg →L[ℝ] Xs × W :=
  E ∘L (ContinuousLinearMap.fst ℝ R Hs ∘L ContinuousLinearMap.fst ℝ (R × Hs) Zg) +
    Jg' ∘L ContinuousLinearMap.snd ℝ (R × Hs) Zg +
    JH' ∘L (ContinuousLinearMap.snd ℝ R Hs ∘L ContinuousLinearMap.fst ℝ (R × Hs) Zg)

/-- **The analytic two-row graph** (`eq:supp-exact-Xi-reduced`).  Let `𝔠_g : Xs × W → 𝒵_g` be
analytic at `0` with `𝔠_g(0) = 0` and `𝒜_g = D𝔠_g(0) ∘ J_g'` invertible.  Then there is
`γ : R × ℋ → 𝒵_g`, analytic at `0`, with `γ(0) = 0`, `𝔠_g(𝖤 r + J_g γ(r, y) + J_H y) = 0` near
`0`, unique near `0` (any `z` near `0` solving `𝔠_g(𝖤 r + J_g z + J_H y) = 0` equals `γ(r, y)`),
and with `γ_y(0, 0) = 0` as soon as `D𝔠_g(0) ∘ J_H' = 0`. -/
theorem two_row_elimination_graph (E : R →L[ℝ] Xs × W) (Jg' : Zg →L[ℝ] Xs × W)
    (JH' : Hs →L[ℝ] Xs × W) (cg : Xs × W → Zg) (hcg : AnalyticAt ℝ cg 0) (hcg0 : cg 0 = 0)
    (Ag : Zg ≃L[ℝ] Zg) (hAg : fderiv ℝ cg 0 ∘L Jg' = (Ag : Zg →L[ℝ] Zg)) :
    ∃ γ : R × Hs → Zg, AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧
      (∀ᶠ q in 𝓝 (0 : R × Hs), cg (reducedChart E Jg' JH' γ q) = 0) ∧
      (∀ᶠ x in 𝓝 (0 : (R × Hs) × Zg),
        cg (E x.1.1 + Jg' x.2 + JH' x.1.2) = 0 ↔ γ x.1 = x.2) ∧
      (fderiv ℝ cg 0 ∘L JH' = 0 →
        fderiv ℝ γ 0 ∘L ContinuousLinearMap.inr ℝ R Hs = 0) := by
  set L := chartLinear E Jg' JH'
  have hL : ∀ x, L x = E x.1.1 + Jg' x.2 + JH' x.1.2 := fun x => by
    simp [L, chartLinear]
  set F : (R × Hs) × Zg → Zg := fun x => cg (L x)
  have hF : AnalyticAt ℝ F 0 := hcg.comp_of_eq (L.analyticAt 0) (map_zero L)
  have hFd : fderiv ℝ F 0 = fderiv ℝ cg 0 ∘L L := by
    have h1 : HasFDerivAt cg (fderiv ℝ cg 0) (L 0) := by
      rw [map_zero]; exact hcg.differentiableAt.hasFDerivAt
    exact (h1.comp (0 : (R × Hs) × Zg) L.hasFDerivAt).fderiv
  have hinvEq : fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ (R × Hs) Zg = (Ag : Zg →L[ℝ] Zg) := by
    rw [hFd, ← hAg]
    ext z
    simp [hL]
  have hinv : (fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ (R × Hs) Zg).IsInvertible :=
    ⟨Ag, hinvEq.symm⟩
  obtain ⟨γ, hγ0, hγan, hsol, huniq, hderiv⟩ :=
    AnalyticImplicit.analytic_implicit_function (u := (0 : (R × Hs) × Zg)) hF hinv
  have hF0 : F 0 = 0 := by simp [F, hcg0]
  simp only [Prod.fst_zero, Prod.snd_zero, hF0] at hγ0 hsol huniq hγan hderiv
  refine ⟨γ, hγan, hγ0, ?_, ?_, ?_⟩
  · filter_upwards [hsol] with q hq
    simpa [F, hL, reducedChart] using hq
  · filter_upwards [huniq] with x hx
    simpa [F, hL] using hx
  · intro hH
    rw [hderiv.hasFDerivAt.fderiv]
    ext y
    have h0 : fderiv ℝ F 0 ((0, y), 0) = 0 := by
      rw [hFd]
      have := congrArg (fun T => T y) hH
      simpa [hL] using this
    simp [h0]

end Graph

/-! ### Non-vacuity -/

/-- The graph hypotheses are satisfiable: `𝔠_g = p_g ∘ snd` on `ℝ × ℝ` with `J_g' = inr`. -/
example : AnalyticAt ℝ (fun ξ : ℝ × ℝ => ξ.2) 0 ∧ (fun ξ : ℝ × ℝ => ξ.2) 0 = 0 ∧
    fderiv ℝ (fun ξ : ℝ × ℝ => ξ.2) 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) := by
  refine ⟨analyticAt_snd, rfl, ?_⟩
  have : fderiv ℝ (fun ξ : ℝ × ℝ => ξ.2) 0 = ContinuousLinearMap.snd ℝ ℝ ℝ := fderiv_snd
  rw [this]
  ext
  simp

end ExactTwoRowElimination

end RenewalGeometry
