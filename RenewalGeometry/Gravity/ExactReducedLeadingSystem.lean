/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactTwoRowEliminationAnalytic

/-!
# The reduced three-constraint leading system
  (`thm:supp-exact-reduced-leading-system`, `eq:supp-exact-leading-dae`,
  `eq:supp-exact-reduced-functions`, `eq:supp-exact-reduced-dae`, `eq:supp-exact-paired-zero`;
  emergent-spacetime manuscript)

Abstract data as in `Gravity/ExactTwoRowEliminationAnalytic.lean`: `Φ₀ = C_red ⊕ B`, the weak
decomposition `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` (`WeakDecomposition`, `KernelSplit`), `p_H C_red = 0`, an
isomorphism `X : R → 𝒳 = ker(p_g C_red)` with inverse `L_X` on `𝒳`, `B^#` with `B B^# B = B`,
`𝖤 r = (X r, -B^# C_red X r)`, the insertions `J_g' = (0, J_g ·)`, `J_H' = (0, J_H ·)`, and the
two-row graph `γ` of `lem:supp-exact-two-row-elimination` (entered with the properties
`ExactTwoRowElimination.two_row_elimination_graph` proves: `γ(0) = 0`, continuity at `0`,
`𝔠_g(Ξ(r, y)) = 0` near `0`, and local uniqueness).  `𝔠_g = p_g C_red f`
(`eq:supp-exact-c-functions`); `𝓕 = L_X f ∘ Ξ`, `𝓗 = 𝔠_H ∘ Ξ` (`ExactSlowBranch.reducedDrift`,
`reducedHarmonic`).

* `reducedCoord`: the continuous linear coordinates `π(x, w) = (L_X x, p_H(w + B^# C_red X L_X x))`
  with `π ∘ Ξ = id` (`reducedCoord_reducedChart`).
* `leading_static_iff`: near `0`, `Φ₀(ξ) = 0 ∧ 𝔠_g(ξ) = 0 ⟺ ξ = Ξ(π ξ)`.
* **`reduced_leading_system`** (`thm:supp-exact-reduced-leading-system`, path statement): there
  is a neighbourhood `𝒰` of `0` such that a path `ξ` with values in `𝒰` on an open time set `I`
  solves the leading DAE `Φ₀(ξ) = 0`, `x_τ = f(ξ)`, `𝔠_g(ξ) = 0`, `𝔠_H(ξ) = 0` on `I` iff
  `ξ = Ξ(r, y)` on `I` with `r_τ = 𝓕(r, y)` and `𝓗(r, y) = 0` (`eq:supp-exact-reduced-dae`).
  The equivalence is pointwise in time (`regular_equation_iff`), so it applies verbatim at every
  time where an absolutely continuous path is differentiable, i.e. almost everywhere.
* **`paired_zero`** (`eq:supp-exact-paired-zero`): `𝓗(0,0) = 0`, `𝓕_y(0,0) = 𝓗_y(0,0) = 0`
  from `𝔠_H(0) = 0`, `Df(0)J_H = 0`, `D𝔠_H(0)J_H = 0` and `γ_y(0,0) = 0`.
* `reduced_leading_system_of_analytic`: the path statement with `γ` supplied by the analytic
  implicit-function theorem (`two_row_elimination_graph`, needs `𝒜_g = D𝔠_g(0)J_g` invertible).

The paired-zero identities use the harmonic slope-entrance identities of
`eq:supp-exact-slope-entrance`, which the manuscript derives from the constant-shift coefficient
audit (`thm:supp-exact-harmonic-q4-zero`); they are hypotheses here.
-/

open Filter Set
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace ExactReducedLeading

open ExactSlowBranch ExactTwoRowElimination

variable {Xs W Zg Hs R : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- The weak insertion `(0, J ·)` into the slow space. -/
def ins {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (J : Z →L[ℝ] W) : Z →L[ℝ] Xs × W :=
  (ContinuousLinearMap.inr ℝ Xs W).comp J

/-- The shifted weak component `w' = w + B^# C_red X L_X x` of `ξ = (x, w)`. -/
def shiftedWeak (Cred : Xs →L[ℝ] W) (Bsh : W →L[ℝ] W) (X : R →L[ℝ] Xs) (LX : Xs →L[ℝ] R) :
    Xs × W →L[ℝ] W :=
  ContinuousLinearMap.snd ℝ Xs W + Bsh ∘L Cred ∘L X ∘L LX ∘L ContinuousLinearMap.fst ℝ Xs W

/-- The reduced coordinates `π(ξ) = (L_X x, p_H w')`. -/
def reducedCoord (Cred : Xs →L[ℝ] W) (Bsh : W →L[ℝ] W) (X : R →L[ℝ] Xs) (LX : Xs →L[ℝ] R)
    (pH : W →L[ℝ] Hs) : Xs × W →L[ℝ] R × Hs :=
  (LX ∘L ContinuousLinearMap.fst ℝ Xs W).prod (pH ∘L shiftedWeak Cred Bsh X LX)

/-- The full linear coordinates `Θ(ξ) = ((L_X x, p_H w'), p_g w')`. -/
def fullCoord (Cred : Xs →L[ℝ] W) (Bsh : W →L[ℝ] W) (X : R →L[ℝ] Xs) (LX : Xs →L[ℝ] R)
    (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) : Xs × W →L[ℝ] (R × Hs) × Zg :=
  (reducedCoord Cred Bsh X LX pH).prod (pg ∘L shiftedWeak Cred Bsh X LX)

section Linear

variable {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs} {Bsh : W →L[ℝ] W} {X : R →L[ℝ] Xs} {LX : Xs →L[ℝ] R}

/-- `Ξ(q)` lies in `𝒦₀ = ker Φ₀` for every `q` and every `γ`. -/
theorem leadingConstraint_reducedChart (hD : WeakDecomposition B Jg JH pg pH)
    (hK : KernelSplit B Jg JH) (hHC : ∀ x, pH (Cred x) = 0)
    (hBsh : ∀ z, B (Bsh (B z)) = B z) (hX1 : ∀ r, pg (Cred (X r)) = 0) (γ : R × Hs → Zg)
    (q : R × Hs) :
    leadingConstraint Cred B (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ q) = 0 := by
  have hrange : ∀ r, B (Bsh (Cred (X r))) = Cred (X r) := by
    intro r
    obtain ⟨z, hz⟩ := hD.mem_range_of_proj_zero (hX1 r) (hHC (X r))
    rw [← hz, hBsh]
  simp [reducedChart, criticalE, ins, hK.B_Jg, hK.B_JH, hrange]

/-- The reduced coordinates invert the chart: `π(Ξ(q)) = q`. -/
theorem reducedCoord_reducedChart (hD : WeakDecomposition B Jg JH pg pH)
    (hLX : ∀ r, LX (X r) = r) (γ : R × Hs → Zg) (q : R × Hs) :
    reducedCoord Cred Bsh X LX pH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ q) = q := by
  obtain ⟨r, y⟩ := q
  simp [reducedCoord, shiftedWeak, reducedChart, criticalE, ins, hLX, hD.pH_Jg, hD.pH_JH]

/-- The first (regular) component of `Ξ(r, y)` is `X r`. -/
theorem reducedChart_fst (γ : R × Hs → Zg) (q : R × Hs) :
    (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ q).1 = X q.1 := by
  simp [reducedChart, criticalE, ins]

/-- Every `ξ ∈ 𝒦₀` is `𝖤 r + J_g' z + J_H' y` with `((r, y), z) = Θ(ξ)`. -/
theorem fullCoord_spec (hD : WeakDecomposition B Jg JH pg pH) (hK : KernelSplit B Jg JH)
    (hHC : ∀ x, pH (Cred x) = 0) (hBsh : ∀ z, B (Bsh (B z)) = B z)
    (hXL : ∀ x, pg (Cred x) = 0 → X (LX x) = x) {ξ : Xs × W}
    (hξ : leadingConstraint Cred B ξ = 0) :
    criticalE Cred Bsh X (fullCoord Cred Bsh X LX pg pH ξ).1.1 +
      ins Jg (fullCoord Cred Bsh X LX pg pH ξ).2 +
      ins JH (fullCoord Cred Bsh X LX pg pH ξ).1.2 = ξ := by
  obtain ⟨x, w⟩ := ξ
  simp only [leadingConstraint_apply] at hξ
  have hpg : pg (Cred x) = 0 := by
    have := congrArg pg hξ
    rwa [map_add, hD.pg_B, add_zero, map_zero] at this
  have hx : X (LX x) = x := hXL x hpg
  have hrange : B (Bsh (Cred x)) = Cred x := by
    obtain ⟨z, hz⟩ := hD.mem_range_of_proj_zero hpg (hHC x)
    rw [← hz, hBsh]
  have hker : B (w + Bsh (Cred x)) = 0 := by
    rw [map_add, hrange, add_comm]; exact hξ
  obtain ⟨z, y, hzy⟩ := hK.ker_le _ hker
  have hz : pg (w + Bsh (Cred x)) = z := by rw [hzy]; simp [hD.pg_Jg, hD.pg_JH]
  have hy : pH (w + Bsh (Cred x)) = y := by rw [hzy]; simp [hD.pH_Jg, hD.pH_JH]
  simp only [fullCoord, reducedCoord, shiftedWeak, criticalE, ins, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', neg_apply, ContinuousLinearMap.inr_apply,
    hx, hz, hy, Prod.mk_add_mk, add_zero, Prod.mk.injEq, true_and]
  rw [add_assoc, ← hzy]
  abel

end Linear

section Reduced

variable {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs} {Bsh : W →L[ℝ] W} {X : R →L[ℝ] Xs} {LX : Xs →L[ℝ] R}

/-- **Static reduction.**  Near `0`, `Φ₀(ξ) = 0 ∧ 𝔠_g(ξ) = 0` iff `ξ = Ξ(π ξ)`. -/
theorem leading_static_iff (hD : WeakDecomposition B Jg JH pg pH) (hK : KernelSplit B Jg JH)
    (hHC : ∀ x, pH (Cred x) = 0) (hBsh : ∀ z, B (Bsh (B z)) = B z)
    (hX1 : ∀ r, pg (Cred (X r)) = 0) (hXL : ∀ x, pg (Cred x) = 0 → X (LX x) = x)
    (hLX : ∀ r, LX (X r) = r) (cg : Xs × W → Zg) (γ : R × Hs → Zg)
    (hsolve : ∀ᶠ q in 𝓝 (0 : R × Hs),
      cg (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ q) = 0)
    (huniq : ∀ᶠ x in 𝓝 (0 : (R × Hs) × Zg),
      cg (criticalE Cred Bsh X x.1.1 + ins Jg x.2 + ins JH x.1.2) = 0 ↔ γ x.1 = x.2) :
    ∀ᶠ ξ in 𝓝 (0 : Xs × W),
      (leadingConstraint Cred B ξ = 0 ∧ cg ξ = 0 ↔
        ξ = reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ
          (reducedCoord Cred Bsh X LX pH ξ)) := by
  set Ξ := reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ
  set Θ := fullCoord Cred Bsh X LX pg pH
  set π := reducedCoord Cred Bsh X LX pH
  have hΘ : Tendsto Θ (𝓝 0) (𝓝 0) := by
    simpa using Θ.continuous.tendsto (0 : Xs × W)
  have hπ : Tendsto π (𝓝 0) (𝓝 0) := by
    simpa using π.continuous.tendsto (0 : Xs × W)
  filter_upwards [hΘ.eventually huniq, hπ.eventually hsolve] with ξ h1 h2
  constructor
  · rintro ⟨hξ, hc⟩
    have hspec := fullCoord_spec (LX := LX) hD hK hHC hBsh hXL hξ
    have hγ : γ (Θ ξ).1 = (Θ ξ).2 := h1.mp (by rw [hspec]; exact hc)
    calc ξ = criticalE Cred Bsh X (Θ ξ).1.1 + ins Jg (Θ ξ).2 + ins JH (Θ ξ).1.2 := hspec.symm
      _ = Ξ (π ξ) := by
          rw [← hγ]
          simp [Ξ, reducedChart, Θ, π, fullCoord]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [h]; exact leadingConstraint_reducedChart hD hK hHC hBsh hX1 γ _
    · rw [h]; exact h2

/-- **Pointwise equivalence of the regular equations.**  If `ξ = Ξ(r, y)` near `τ` with
`𝔠_g(ξ(τ)) = 0`, then `x_τ = f(ξ)` at `τ` iff `r_τ = 𝓕(r, y)` at `τ`. -/
theorem regular_equation_iff (hXL : ∀ x, pg (Cred x) = 0 → X (LX x) = x)
    (hLX : ∀ r, LX (X r) = r) (f : Xs × W → Xs) (γ : R × Hs → Zg) (ξ : ℝ → Xs × W)
    (ry : ℝ → R × Hs) {τ : ℝ}
    (hξ : ∀ᶠ s in 𝓝 τ, ξ s = reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ (ry s))
    (hcg : pg (Cred (f (ξ τ))) = 0) :
    HasDerivAt (fun s => (ξ s).1) (f (ξ τ)) τ ↔
      HasDerivAt (fun s => (ry s).1)
        (reducedDrift LX f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ) (ry τ)) τ := by
  have hfst : (fun s => (ξ s).1) =ᶠ[𝓝 τ] fun s => X (ry s).1 := by
    filter_upwards [hξ] with s hs
    rw [hs, reducedChart_fst]
  have hξτ := hξ.self_of_nhds
  have hr : (fun s => (ry s).1) =ᶠ[𝓝 τ] fun s => LX (ξ s).1 := by
    filter_upwards [hξ] with s hs
    rw [hs, reducedChart_fst, hLX]
  simp only [reducedDrift, ← hξτ]
  constructor
  · intro h
    exact ((LX.hasFDerivAt.comp_hasDerivAt τ h)).congr_of_eventuallyEq hr
  · intro h
    have h2 := (X.hasFDerivAt.comp_hasDerivAt τ h).congr_of_eventuallyEq hfst
    rwa [show X (LX (f (ξ τ))) = f (ξ τ) from hXL _ hcg] at h2

/-- **`thm:supp-exact-reduced-leading-system`** (path statement).  There is a neighbourhood `𝒰`
of `0` such that for every path `ξ` with values in `𝒰` on an open set of times `I`:
`ξ` solves the leading DAE `Φ₀(ξ) = 0`, `x_τ = f(ξ)`, `𝔠_g(ξ) = 0`, `𝔠_H(ξ) = 0` on `I` iff
`ξ = Ξ(r, y)` on `I` for a path `(r, y)` with `r_τ = 𝓕(r, y)` and `𝓗(r, y) = 0` on `I`. -/
theorem reduced_leading_system (hD : WeakDecomposition B Jg JH pg pH) (hK : KernelSplit B Jg JH)
    (hHC : ∀ x, pH (Cred x) = 0) (hBsh : ∀ z, B (Bsh (B z)) = B z)
    (hX1 : ∀ r, pg (Cred (X r)) = 0) (hXL : ∀ x, pg (Cred x) = 0 → X (LX x) = x)
    (hLX : ∀ r, LX (X r) = r) (f : Xs × W → Xs) {Ho : Type*} [NormedAddCommGroup Ho]
    [NormedSpace ℝ Ho] (cH : Xs × W → Ho) (γ : R × Hs → Zg)
    (hsolve : ∀ᶠ q in 𝓝 (0 : R × Hs),
      pg (Cred (f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ q))) = 0)
    (huniq : ∀ᶠ x in 𝓝 (0 : (R × Hs) × Zg),
      pg (Cred (f (criticalE Cred Bsh X x.1.1 + ins Jg x.2 + ins JH x.1.2))) = 0 ↔
        γ x.1 = x.2) :
    ∃ 𝒰 ∈ 𝓝 (0 : Xs × W), ∀ (ξ : ℝ → Xs × W) (I : Set ℝ), IsOpen I → (∀ τ ∈ I, ξ τ ∈ 𝒰) →
      ((∀ τ ∈ I, leadingConstraint Cred B (ξ τ) = 0 ∧ pg (Cred (f (ξ τ))) = 0 ∧ cH (ξ τ) = 0 ∧
          HasDerivAt (fun s => (ξ s).1) (f (ξ τ)) τ) ↔
        ∃ ry : ℝ → R × Hs, ∀ τ ∈ I,
          ξ τ = reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ (ry τ) ∧
          HasDerivAt (fun s => (ry s).1)
            (reducedDrift LX f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ) (ry τ))
            τ ∧
          reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ) (ry τ) = 0) := by
  set Ξ := reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ
  set π := reducedCoord Cred Bsh X LX pH
  set cg : Xs × W → Zg := fun ξ => pg (Cred (f ξ))
  have hstat := leading_static_iff (LX := LX) hD hK hHC hBsh hX1 hXL hLX cg γ hsolve huniq
  have hπ : Tendsto π (𝓝 0) (𝓝 0) := by simpa using π.continuous.tendsto (0 : Xs × W)
  refine ⟨{ξ | (leadingConstraint Cred B ξ = 0 ∧ cg ξ = 0 ↔ ξ = Ξ (π ξ)) ∧ cg (Ξ (π ξ)) = 0},
    hstat.and (hπ.eventually hsolve), ?_⟩
  intro ξ I hI hU
  constructor
  · intro h
    refine ⟨fun s => π (ξ s), fun τ hτ => ?_⟩
    obtain ⟨h0, hc, hH, hd⟩ := h τ hτ
    have hξτ : ξ τ = Ξ (π (ξ τ)) := ((hU τ hτ).1.mp ⟨h0, hc⟩)
    have hev : ∀ᶠ s in 𝓝 τ, ξ s = Ξ (π (ξ s)) := by
      filter_upwards [hI.mem_nhds hτ] with s hs
      exact (hU s hs).1.mp ⟨(h s hs).1, (h s hs).2.1⟩
    refine ⟨hξτ, (regular_equation_iff hXL hLX f γ ξ (fun s => π (ξ s)) hev hc).mp hd, ?_⟩
    simp only [reducedHarmonic]
    rw [← hξτ]; exact hH
  · rintro ⟨ry, hry⟩ τ hτ
    obtain ⟨hξ, hd, hH⟩ := hry τ hτ
    have hπξ : ∀ s ∈ I, π (ξ s) = ry s := fun s hs => by
      rw [(hry s hs).1]; exact reducedCoord_reducedChart hD hLX γ _
    have hcτ : cg (ξ τ) = 0 := by
      have := (hU τ hτ).2
      rwa [hπξ τ hτ, ← hξ] at this
    have hev : ∀ᶠ s in 𝓝 τ, ξ s = Ξ (ry s) := by
      filter_upwards [hI.mem_nhds hτ] with s hs
      exact (hry s hs).1
    refine ⟨?_, hcτ, ?_, (regular_equation_iff hXL hLX f γ ξ ry hev hcτ).mpr hd⟩
    · rw [hξ]; exact leadingConstraint_reducedChart hD hK hHC hBsh hX1 γ _
    · simp only [reducedHarmonic] at hH
      rw [hξ]; exact hH

/-- **`eq:supp-exact-paired-zero`.**  With `𝔠_H(0) = 0`, `Df(0)J_H = 0`, `D𝔠_H(0)J_H = 0` (the
harmonic slope-entrance identities) and `γ(0) = 0`, `γ_y(0,0) = 0`:
`𝓗(0,0) = 0` and `𝓕_y(0,0) = 𝓗_y(0,0) = 0`. -/
theorem paired_zero {Ho : Type*} [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]
    (f : Xs × W → Xs) (cH : Xs × W → Ho) (γ : R × Hs → Zg) (hγ0 : γ 0 = 0)
    (hγd : DifferentiableAt ℝ γ 0)
    (hγy : fderiv ℝ γ 0 ∘L ContinuousLinearMap.inr ℝ R Hs = 0)
    (hf : DifferentiableAt ℝ f 0) (hcH : DifferentiableAt ℝ cH 0) (hcH0 : cH 0 = 0)
    (hfJ : fderiv ℝ f 0 ∘L ins JH = 0) (hcHJ : fderiv ℝ cH 0 ∘L ins JH = 0) :
    reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ) 0 = 0 ∧
      fderiv ℝ (reducedDrift LX f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ)) 0 ∘L
        ContinuousLinearMap.inr ℝ R Hs = 0 ∧
      fderiv ℝ (reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ)) 0 ∘L
        ContinuousLinearMap.inr ℝ R Hs = 0 := by
  set Ξ := reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ
  have hΞ0 : Ξ 0 = 0 := by simp [Ξ, reducedChart, hγ0]
  have hΞd : HasFDerivAt Ξ ((criticalE Cred Bsh X).comp (ContinuousLinearMap.fst ℝ R Hs) +
      (ins Jg).comp (fderiv ℝ γ 0) + (ins JH).comp (ContinuousLinearMap.snd ℝ R Hs)) 0 := by
    have h1 := (criticalE Cred Bsh X).hasFDerivAt.comp (0 : R × Hs)
      (ContinuousLinearMap.fst ℝ R Hs).hasFDerivAt
    have h2 := (ins (Xs := Xs) Jg).hasFDerivAt.comp (0 : R × Hs) hγd.hasFDerivAt
    have h3 := (ins (Xs := Xs) JH).hasFDerivAt.comp (0 : R × Hs) (ContinuousLinearMap.snd ℝ R Hs).hasFDerivAt
    exact (h1.add h2).add h3
  have hΞy : ∀ y, ((criticalE Cred Bsh X).comp (ContinuousLinearMap.fst ℝ R Hs) +
      (ins (Xs := Xs) Jg).comp (fderiv ℝ γ 0) + (ins (Xs := Xs) JH).comp
        (ContinuousLinearMap.snd ℝ R Hs)) (ContinuousLinearMap.inr ℝ R Hs y) =
      ins (Xs := Xs) JH y := by
    intro y
    have h0 : fderiv ℝ γ 0 (0, y) = 0 := by
      have := congrArg (fun T => T y) hγy
      simpa using this
    simp [h0]
  refine ⟨by simp [reducedHarmonic, hΞ0, hcH0], ?_, ?_⟩
  · have hF : HasFDerivAt (reducedDrift LX f Ξ) (LX.comp ((fderiv ℝ f 0).comp
        ((criticalE Cred Bsh X).comp (ContinuousLinearMap.fst ℝ R Hs) +
          (ins Jg).comp (fderiv ℝ γ 0) + (ins JH).comp (ContinuousLinearMap.snd ℝ R Hs)))) 0 := by
      have hf' : HasFDerivAt f (fderiv ℝ f 0) (Ξ 0) := by rw [hΞ0]; exact hf.hasFDerivAt
      exact LX.hasFDerivAt.comp (0 : R × Hs) (hf'.comp (0 : R × Hs) hΞd)
    rw [hF.fderiv]
    ext1 y
    have := congrArg (fun T => T y) hfJ
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at this ⊢
    rw [hΞy, this, map_zero]
  · have hH : HasFDerivAt (reducedHarmonic cH Ξ) ((fderiv ℝ cH 0).comp
        ((criticalE Cred Bsh X).comp (ContinuousLinearMap.fst ℝ R Hs) +
          (ins Jg).comp (fderiv ℝ γ 0) + (ins JH).comp (ContinuousLinearMap.snd ℝ R Hs))) 0 := by
      have hc' : HasFDerivAt cH (fderiv ℝ cH 0) (Ξ 0) := by rw [hΞ0]; exact hcH.hasFDerivAt
      exact hc'.comp (0 : R × Hs) hΞd
    rw [hH.fderiv]
    ext1 y
    have := congrArg (fun T => T y) hcHJ
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at this ⊢
    rw [hΞy, this]

end Reduced

section Analytic

variable [CompleteSpace Xs] [CompleteSpace W] [CompleteSpace Zg] [CompleteSpace Hs]
  [CompleteSpace R]
variable {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs} {Bsh : W →L[ℝ] W} {X : R →L[ℝ] Xs} {LX : Xs →L[ℝ] R}

/-- **`thm:supp-exact-reduced-leading-system` with the analytic two-row graph.**  For analytic
`f` with `𝔠_g(0) = p_g C_red f(0) = 0` and `𝒜_g = D𝔠_g(0) J_g'` invertible, the graph `γ` of
`two_row_elimination_graph` reduces the leading DAE as in `reduced_leading_system`; if moreover
the slope-entrance identities `D𝔠_g(0)J_H = 0`, `Df(0)J_H = 0`, `𝔠_H(0) = 0`,
`D𝔠_H(0)J_H = 0` hold, the paired zero `eq:supp-exact-paired-zero` holds. -/
theorem reduced_leading_system_of_analytic (hD : WeakDecomposition B Jg JH pg pH)
    (hK : KernelSplit B Jg JH) (hHC : ∀ x, pH (Cred x) = 0) (hBsh : ∀ z, B (Bsh (B z)) = B z)
    (hX1 : ∀ r, pg (Cred (X r)) = 0) (hXL : ∀ x, pg (Cred x) = 0 → X (LX x) = x)
    (hLX : ∀ r, LX (X r) = r) (f : Xs × W → Xs) (hfa : AnalyticAt ℝ f 0)
    (hcg0 : pg (Cred (f 0)) = 0) (Ag : Zg ≃L[ℝ] Zg)
    (hAg : fderiv ℝ (fun ξ => pg (Cred (f ξ))) 0 ∘L ins Jg = (Ag : Zg →L[ℝ] Zg))
    {Ho : Type*} [NormedAddCommGroup Ho] [NormedSpace ℝ Ho] (cH : Xs × W → Ho) :
    ∃ γ : R × Hs → Zg, AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧
      (∃ 𝒰 ∈ 𝓝 (0 : Xs × W), ∀ (ξ : ℝ → Xs × W) (I : Set ℝ), IsOpen I → (∀ τ ∈ I, ξ τ ∈ 𝒰) →
        ((∀ τ ∈ I, leadingConstraint Cred B (ξ τ) = 0 ∧ pg (Cred (f (ξ τ))) = 0 ∧ cH (ξ τ) = 0 ∧
            HasDerivAt (fun s => (ξ s).1) (f (ξ τ)) τ) ↔
          ∃ ry : ℝ → R × Hs, ∀ τ ∈ I,
            ξ τ = reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ (ry τ) ∧
            HasDerivAt (fun s => (ry s).1)
              (reducedDrift LX f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ)
                (ry τ)) τ ∧
            reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ)
              (ry τ) = 0)) ∧
      (fderiv ℝ (fun ξ => pg (Cred (f ξ))) 0 ∘L ins JH = 0 → fderiv ℝ f 0 ∘L ins JH = 0 →
        DifferentiableAt ℝ cH 0 → cH 0 = 0 → fderiv ℝ cH 0 ∘L ins JH = 0 →
        reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ) 0 = 0 ∧
        fderiv ℝ (reducedDrift LX f (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ))
          0 ∘L ContinuousLinearMap.inr ℝ R Hs = 0 ∧
        fderiv ℝ (reducedHarmonic cH (reducedChart (criticalE Cred Bsh X) (ins Jg) (ins JH) γ))
          0 ∘L ContinuousLinearMap.inr ℝ R Hs = 0) := by
  have hcga : AnalyticAt ℝ (fun ξ => pg (Cred (f ξ))) 0 :=
    ((pg.comp Cred).analyticAt _).comp hfa
  obtain ⟨γ, hγa, hγ0, hsolve, huniq, hγy⟩ :=
    two_row_elimination_graph (criticalE Cred Bsh X) (ins Jg) (ins JH)
      (fun ξ => pg (Cred (f ξ))) hcga hcg0 Ag hAg
  refine ⟨γ, hγa, hγ0, reduced_leading_system hD hK hHC hBsh hX1 hXL hLX f cH γ hsolve huniq, ?_⟩
  intro hcgJ hfJ hcH hcH0 hcHJ
  exact paired_zero f cH γ hγ0 hγa.differentiableAt (hγy hcgJ) hfa.differentiableAt hcH hcH0 hfJ
    hcHJ

end Analytic

end ExactReducedLeading
end RenewalGeometry

end
