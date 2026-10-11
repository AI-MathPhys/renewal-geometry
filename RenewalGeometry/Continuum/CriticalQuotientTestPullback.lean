/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientRowConvergence

/-!
# Pulling fixed normalized tests back through `G_SM` Coulomb gauges
  (`lem:equivariant-tests`, `thm:critical-quotient-defect`; Einstein–Standard-Model
  action-closure manuscript)

"Fix now a smooth test in a normalized chart and pull it back through the cutoff-dependent
gauge" (`app:critical-quotient-proof`).  For a gauge `R`, smooth and `G_SM`-valued on an open set
`B`, and a smooth physical test `v` supported in a compact subset of `B`:

* `pullTest R v = R^*·v` (`a ↦ R^* a R`, `η_H ↦ R₂^* η_H`, `η ↦ R^* η`, `η̄ ↦ η̄ R`, `k ↦ k`) is again a
  smooth physical test supported in the same compact set, `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued
  (`isSetTest_pullTest`), and `R·(R^*·v) = v` (`gaugeTest_pullTest`);
* **`integral_pullTest`**: the complete first variation of the original fields along the pulled-back
  test equals the first variation of the gauge-transformed fields along the fixed test,
  `∫_K Cov(j z)(j¹(R^*·v)) = ∫_Q Cov(j(R·z))(j¹ v)` (pointwise gauge invariance `fullCov_gauge`,
  no derivative of the gauge enters).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient BallAnalysis.SMGaugeStructure SMGaugeLie
  EinsteinSM SMGaugeJet

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### Admissible tests -/

/-- The five components of a tuple vanish at `y`. -/
def VanishesAt (v : FieldTuple (Fin 5)) (y : E4) : Prop :=
  v.e y = 0 ∧ v.A y = 0 ∧ v.H y = 0 ∧ v.Ψ y = 0 ∧ v.Ψb y = 0

/-- **A smooth physical test on `S`**: smooth components, vanishing outside a compact subset of
`S`, gauge part valued in `𝔰(𝔲(3) ⊕ 𝔲(2))` (`def:tests`, chart rendering). -/
structure IsSetTest (S : Set E4) (v : FieldTuple (Fin 5)) : Prop where
  smooth_e : ContDiff ℝ ∞ v.e
  smooth_A : ContDiff ℝ ∞ v.A
  smooth_H : ContDiff ℝ ∞ v.H
  smooth_Ψ : ContDiff ℝ ∞ v.Ψ
  smooth_Ψb : ContDiff ℝ ∞ v.Ψb
  supp : ∃ Kc, IsCompact Kc ∧ Kc ⊆ S ∧ ∀ y ∉ Kc, VanishesAt v y
  lie : ∀ y μ, v.A y μ ∈ smLie

theorem IsSetTest.diffAt {S : Set E4} {v : FieldTuple (Fin 5)} (hv : IsSetTest S v) (x : E4) :
    DiffAt v x :=
  ⟨(hv.smooth_e.differentiable (by simp)) x, (hv.smooth_A.differentiable (by simp)) x,
    (hv.smooth_H.differentiable (by simp)) x, (hv.smooth_Ψ.differentiable (by simp)) x,
    (hv.smooth_Ψb.differentiable (by simp)) x⟩

theorem IsSetTest.mono {S S' : Set E4} {v : FieldTuple (Fin 5)} (hv : IsSetTest S v)
    (h : S ⊆ S') : IsSetTest S' v :=
  { hv with supp := let ⟨Kc, hKc, hKS, h0⟩ := hv.supp; ⟨Kc, hKc, hKS.trans h, h0⟩ }

/-- A test vanishing near `x` has zero jet at `x`. -/
theorem testJet_eq_zero {v : FieldTuple (Fin 5)} {x : E4}
    (h : ∀ᶠ y in 𝓝 x, VanishesAt v y) : testJet v x = 0 := by
  have he : v.e =ᶠ[𝓝 x] 0 := h.mono fun y hy => hy.1
  have hA : v.A =ᶠ[𝓝 x] 0 := h.mono fun y hy => hy.2.1
  have hH : v.H =ᶠ[𝓝 x] 0 := h.mono fun y hy => hy.2.2.1
  have hΨ : v.Ψ =ᶠ[𝓝 x] 0 := h.mono fun y hy => hy.2.2.2.1
  have hΨb : v.Ψb =ᶠ[𝓝 x] 0 := h.mono fun y hy => hy.2.2.2.2
  have hpd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      f =ᶠ[𝓝 x] 0 → ∀ i, pd f i x = 0 := by
    intro F _ _ f hf i
    unfold pd; rw [hf.fderiv_eq]; simp
  simp only [testJet, RJet.mk, he.self_of_nhds, hA.self_of_nhds, hH.self_of_nhds,
    hΨ.self_of_nhds, hΨb.self_of_nhds, Pi.zero_apply]
  simp only [hpd he, hpd hA, hpd hH, hpd hΨ, hpd hΨb]
  rfl

/-! ### The pulled-back test -/

/-- **The pulled-back test** `R^*·v` (linear action of the inverse gauge `R^* = R⁻¹`). -/
def pullTest (R : E4 → M5) (v : FieldTuple (Fin 5)) : FieldTuple (Fin 5) :=
  gaugeTest (fun y => star (R y)) v

theorem vanishesAt_gaugeTest {R : E4 → M5} {v : FieldTuple (Fin 5)} {y : E4}
    (h : VanishesAt v y) : VanishesAt (gaugeTest R v) y := by
  obtain ⟨he, hA, hH, hΨ, hΨb⟩ := h
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · show (fun μ => adG (R y) (v.A y μ)) = 0
    funext μ i j
    simp [hA, adG]
  · show higgsG (R y) (v.H y) = 0
    simp [hH, higgsG]
  · show spinG (R y) (v.Ψ y) = 0
    funext s; simp [hΨ, spinG]
  · show cospinG (R y) (v.Ψb y) = 0
    funext s; simp [hΨb, cospinG]

/-- **`R·(R^*·v) = v`** for a gauge with values in `G_SM` wherever `v` does not vanish. -/
theorem gaugeTest_pullTest {R : E4 → M5} {v : FieldTuple (Fin 5)}
    (h : ∀ y, R y ∈ GSM ∨ VanishesAt v y) : gaugeTest R (pullTest R v) = v := by
  have key : ∀ y, (gaugeTest R (pullTest R v)).e y = v.e y ∧
      (gaugeTest R (pullTest R v)).A y = v.A y ∧ (gaugeTest R (pullTest R v)).H y = v.H y ∧
      (gaugeTest R (pullTest R v)).Ψ y = v.Ψ y ∧ (gaugeTest R (pullTest R v)).Ψb y = v.Ψb y := by
    intro y
    rcases h y with hg | h0
    · have h1 : R y * star (R y) = 1 := mem_unitaryGroup_iff.mp hg.1
      have h2 : star (R y) * R y = 1 := mem_unitaryGroup_iff'.mp hg.1
      have hw : wk (R y) * wk (star (R y)) = 1 := by
        rw [wk_star]; exact (wk_unitary hg).1
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · funext μ i j
        show (R y * Matrix.of (fun i j => (star (R y) * Matrix.of (v.A y μ) *
          star (star (R y))) i j) * star (R y)) i j = v.A y μ i j
        have : Matrix.of (fun i j => (star (R y) * Matrix.of (v.A y μ) * star (star (R y))) i j) =
            star (R y) * Matrix.of (v.A y μ) * R y := by
          ext; simp
        rw [this]
        simp only [Matrix.mul_assoc]
        rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
        rfl
      · show wk (R y) *ᵥ (wk (star (R y)) *ᵥ v.H y) = v.H y
        rw [mulVec_mulVec, hw, one_mulVec]
      · funext s
        show R y *ᵥ (star (R y) *ᵥ v.Ψ y s) = v.Ψ y s
        rw [mulVec_mulVec, h1, one_mulVec]
      · funext s
        show (star (R y))ᵀ *ᵥ ((star (star (R y)))ᵀ *ᵥ v.Ψb y s) = v.Ψb y s
        rw [mulVec_mulVec, star_star, ← transpose_mul, h1, transpose_one, one_mulVec]
    · have h' := vanishesAt_gaugeTest (R := R) (vanishesAt_gaugeTest (R := fun y => star (R y)) h0)
      exact ⟨h'.1.trans h0.1.symm, h'.2.1.trans h0.2.1.symm, h'.2.2.1.trans h0.2.2.1.symm,
        h'.2.2.2.1.trans h0.2.2.2.1.symm, h'.2.2.2.2.trans h0.2.2.2.2.symm⟩
  refine Prod.ext (funext fun y => (key y).1) (Prod.ext (funext fun y => (key y).2.1)
    (Prod.ext (funext fun y => (key y).2.2.1) (Prod.ext (funext fun y => (key y).2.2.2.1)
      (funext fun y => (key y).2.2.2.2))))

/-! ### Smoothness of the pulled-back test -/

theorem contDiffAt_entry_star {R : E4 → M5} {x : E4}
    (hR : ∀ c e, ContDiffAt ℝ ∞ (fun y => R y c e) x) (c e : Fin 5) :
    ContDiffAt ℝ ∞ (fun y => star (R y) c e) x := by
  simp only [star_apply]
  have h := (Complex.conjCLE.contDiff (n := ∞)).contDiffAt.comp x (hR e c)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [Complex.conjCLE_apply])

theorem contDiffAt_mul_entry {R S : E4 → M5} {x : E4}
    (hR : ∀ c e, ContDiffAt ℝ ∞ (fun y => R y c e) x)
    (hS : ∀ c e, ContDiffAt ℝ ∞ (fun y => S y c e) x) (c e : Fin 5) :
    ContDiffAt ℝ ∞ (fun y => (R y * S y) c e) x := by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (hR c k).mul (hS k e)

theorem contDiffAt_mulVec_entry {R : E4 → M5} {w : E4 → Fin 5 → ℂ} {x : E4}
    (hR : ∀ c e, ContDiffAt ℝ ∞ (fun y => R y c e) x)
    (hw : ∀ c, ContDiffAt ℝ ∞ (fun y => w y c) x) (c : Fin 5) :
    ContDiffAt ℝ ∞ (fun y => (R y *ᵥ w y) c) x := by
  simp only [mulVec, dotProduct]
  exact ContDiffAt.sum fun k _ => (hR c k).mul (hw k)

theorem contDiffAt_apply₁ {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → ι → F} {x : E4} (hf : ContDiffAt ℝ ∞ f x) (i : ι) :
    ContDiffAt ℝ ∞ (fun y => f y i) x :=
  contDiffAt_pi.mp hf i

/-- The pulled-back test is smooth near every point of the open set where the gauge is
smooth. -/
theorem contDiffAt_pullTest {R : E4 → M5} {x : E4}
    (hR : ∀ c e, ContDiffAt ℝ ∞ (fun y => R y c e) x) {v : FieldTuple (Fin 5)}
    (hA : ContDiffAt ℝ ∞ v.A x) (hH : ContDiffAt ℝ ∞ v.H x) (hΨ : ContDiffAt ℝ ∞ v.Ψ x)
    (hΨb : ContDiffAt ℝ ∞ v.Ψb x) :
    ContDiffAt ℝ ∞ (pullTest R v).A x ∧ ContDiffAt ℝ ∞ (pullTest R v).H x ∧
      ContDiffAt ℝ ∞ (pullTest R v).Ψ x ∧ ContDiffAt ℝ ∞ (pullTest R v).Ψb x := by
  have hRs := contDiffAt_entry_star hR
  have hRss : ∀ c e, ContDiffAt ℝ ∞ (fun y => star (star (R y)) c e) x := by
    simpa using hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine contDiffAt_pi.mpr fun μ => contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
    show ContDiffAt ℝ ∞ (fun y => (star (R y) * Matrix.of (v.A y μ) * star (star (R y))) i j) x
    exact contDiffAt_mul_entry (contDiffAt_mul_entry hRs
      (fun c e => contDiffAt_apply₁ (contDiffAt_apply₁ (contDiffAt_apply₁ hA μ) c) e)) hRss i j
  · refine contDiffAt_pi.mpr fun i => ?_
    show ContDiffAt ℝ ∞ (fun y => (wk (star (R y)) *ᵥ v.H y) i) x
    simp only [mulVec, dotProduct, wk, submatrix_apply]
    exact ContDiffAt.sum fun k _ => (hRs _ _).mul (contDiffAt_apply₁ hH k)
  · refine contDiffAt_pi.mpr fun s => contDiffAt_pi.mpr fun c => ?_
    show ContDiffAt ℝ ∞ (fun y => (star (R y) *ᵥ v.Ψ y s) c) x
    exact contDiffAt_mulVec_entry hRs (fun c => contDiffAt_apply₁ (contDiffAt_apply₁ hΨ s) c) c
  · refine contDiffAt_pi.mpr fun s => contDiffAt_pi.mpr fun c => ?_
    show ContDiffAt ℝ ∞ (fun y => ((star (star (R y)))ᵀ *ᵥ v.Ψb y s) c) x
    simp only [mulVec, dotProduct, transpose_apply]
    exact ContDiffAt.sum fun k _ => (hRss _ _).mul
      (contDiffAt_apply₁ (contDiffAt_apply₁ hΨb s) k)

theorem eventually_vanishes_pullTest {R : E4 → M5} {v : FieldTuple (Fin 5)} {x : E4}
    (h : ∀ᶠ y in 𝓝 x, VanishesAt v y) : ∀ᶠ y in 𝓝 x, VanishesAt (pullTest R v) y :=
  h.mono fun _ hy => vanishesAt_gaugeTest hy

/-- **The pulled-back test is an admissible test** (smooth, compactly supported in the same set,
`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued). -/
theorem isSetTest_pullTest {R : E4 → M5} {B S : Set E4} (hB : IsOpen B)
    (hRs : ∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) B) (hRG : ∀ y ∈ B, R y ∈ GSM)
    {v : FieldTuple (Fin 5)} (hv : IsSetTest S v) (hSB : S ⊆ B) : IsSetTest S (pullTest R v) := by
  obtain ⟨Kc, hKc, hKS, h0⟩ := hv.supp
  have hloc : ∀ x, x ∉ Kc → ∀ᶠ y in 𝓝 x, VanishesAt v y := fun x hx =>
    Filter.mem_of_superset (hKc.isClosed.isOpen_compl.mem_nhds hx) fun y hy => h0 y hy
  have hsm : ∀ x, ContDiffAt ℝ ∞ (pullTest R v).A x ∧ ContDiffAt ℝ ∞ (pullTest R v).H x ∧
      ContDiffAt ℝ ∞ (pullTest R v).Ψ x ∧ ContDiffAt ℝ ∞ (pullTest R v).Ψb x := by
    intro x
    by_cases hx : x ∈ B
    · exact contDiffAt_pullTest (fun c e => (hRs c e).contDiffAt (hB.mem_nhds hx))
        hv.smooth_A.contDiffAt hv.smooth_H.contDiffAt hv.smooth_Ψ.contDiffAt
        hv.smooth_Ψb.contDiffAt
    · have hxK : x ∉ Kc := fun h => hx (hSB (hKS h))
      have hev := eventually_vanishes_pullTest (R := R) (hloc x hxK)
      exact ⟨contDiffAt_const.congr_of_eventuallyEq (hev.mono fun y hy => hy.2.1),
        contDiffAt_const.congr_of_eventuallyEq (hev.mono fun y hy => hy.2.2.1),
        contDiffAt_const.congr_of_eventuallyEq (hev.mono fun y hy => hy.2.2.2.1),
        contDiffAt_const.congr_of_eventuallyEq (hev.mono fun y hy => hy.2.2.2.2)⟩
  refine ⟨hv.smooth_e, contDiff_iff_contDiffAt.mpr fun x => (hsm x).1,
    contDiff_iff_contDiffAt.mpr fun x => (hsm x).2.1,
    contDiff_iff_contDiffAt.mpr fun x => (hsm x).2.2.1,
    contDiff_iff_contDiffAt.mpr fun x => (hsm x).2.2.2, ⟨Kc, hKc, hKS, fun y hy =>
      vanishesAt_gaugeTest (h0 y hy)⟩, fun y μ => ?_⟩
  by_cases hy : y ∈ B
  · have hg : star (R y) ∈ GSM := star_mem_GSM (hRG y hy)
    have hX : Matrix.of (v.A y μ) ∈ gSM := by
      have := (mem_gSM_iff (v.A y μ)).2 (hv.lie y μ); exact this
    have hm := ad_mem_gSM hg hX
    have e : (pullTest R v).A y μ = Matrix.of.symm (star (R y) * Matrix.of (v.A y μ) *
        star (star (R y))) := rfl
    rw [e, ← mem_gSM_iff, Equiv.apply_symm_apply]
    exact hm
  · have hyK : y ∉ Kc := fun h => hy (hSB (hKS h))
    have : (pullTest R v).A y = 0 := (vanishesAt_gaugeTest (h0 y hyK)).2.1
    rw [this]
    exact smLie.zero_mem

/-! ### The pulled-back first variation -/

/-- **Gauge invariance of the first variation along pulled-back tests**: for fields `z`
differentiable on `S` with nondegenerate coframe, a gauge `R` smooth and `G_SM`-valued on an open
`B`, and a test `v` supported in a compact subset of `Q ⊆ S ∩ B`,
`∫_S Cov(j z)(j¹(R^*·v)) = ∫_Q Cov(j(R·z))(j¹ v)`. -/
theorem integral_pullTest {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (θ : CoefficientBank Ysec) {R : E4 → M5} {B S Q : Set E4} (hB : IsOpen B)
    (hRs : ∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) B) (hRG : ∀ y ∈ B, R y ∈ GSM)
    {z : FieldTuple (Fin 5)} (hz : ∀ x ∈ S, DiffAt z x) (hGL : ∀ x ∈ S, z.e x ∈ coframeGL)
    {v : FieldTuple (Fin 5)} (hv : IsSetTest Q v) (hQB : Q ⊆ B) (hQS : Q ⊆ S)
    (hS : MeasurableSet S) :
    ∫ x in S, fullCov mY θ (redJet z x) (testJet (pullTest R v) x) =
      ∫ x in Q, fullCov mY θ (redJet (gaugeTuple R z) x) (testJet v x) := by
  obtain ⟨Kc, hKc, hKQ, h0⟩ := hv.supp
  have hloc : ∀ x, x ∉ Kc → ∀ᶠ y in 𝓝 x, VanishesAt v y := fun x hx =>
    Filter.mem_of_superset (hKc.isClosed.isOpen_compl.mem_nhds hx) fun y hy => h0 y hy
  have hpull := isSetTest_pullTest hB hRs hRG hv hQB
  have hgp : gaugeTest R (pullTest R v) = v := gaugeTest_pullTest fun y => by
    by_cases hy : y ∈ B
    · exact Or.inl (hRG y hy)
    · exact Or.inr (h0 y fun h => hy (hQB (hKQ h)))
  -- pointwise identity on `S`
  have hpt : ∀ x ∈ S, fullCov mY θ (redJet z x) (testJet (pullTest R v) x) =
      fullCov mY θ (redJet (gaugeTuple R z) x) (testJet v x) := by
    intro x hx
    by_cases hxK : x ∈ Kc
    · have hxB : x ∈ B := hQB (hKQ hxK)
      have hRx : GaugeAt R x :=
        ⟨fun c e => (show ContDiffAt ℝ 2 (fun y => R y c e) x from
          ((hRs c e).contDiffAt (hB.mem_nhds hxB)).of_le (WithTop.coe_le_coe.mpr le_top)),
          Filter.mem_of_superset (hB.mem_nhds hxB) fun y hy => hRG y hy⟩
      have := fullCov_gauge mY θ hRx (hz x hx) (hpull.diffAt x) (hGL x hx)
      rw [hgp] at this
      exact this.symm
    · rw [testJet_eq_zero (hloc x hxK), testJet_eq_zero
        (eventually_vanishes_pullTest (R := R) (hloc x hxK)), map_zero,
        map_zero]
  rw [setIntegral_congr_fun hS hpt]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hS hQS fun x hx => ?_
  have hxK : x ∉ Kc := fun h => hx.2 (hKQ h)
  rw [testJet_eq_zero (hloc x hxK), map_zero]

end RenewalGeometry.CriticalQuotientRows
