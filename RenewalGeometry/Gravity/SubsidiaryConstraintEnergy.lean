/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicGaugePropagation
import RenewalGeometry.Gravity.SubsidiarySourceJet
import RenewalGeometry.Continuum.TorusWaveEnergyForced

/-!
# Subsidiary equation and constraint stability with sources (`prop:subsidiary`,
  Einstein–Standard-Model action-closure manuscript)

A classical metric field `g = η + Q` on `[0, T] × 𝕋³` (a `C3Field` of
`Gravity/HarmonicGaugePropagation.lean`: candidate classical derivatives up to order three) together
with stress and residual tensor fields `T, r` with first-derivative fields, which satisfies the
reduced Einstein equation with constant parameters `Λ, κ`
`Ĝ + Λ g = κ T + r`, `Ĝ = G - ∇_{(μ}C_{ν)} + ½ g ∇^αC_α` (`eq:reduced-Einstein`, the library's
`resM`), `C = C(g)` the harmonic gauge covector.  The closed spatial slab is `Σ = 𝕋³` (disclosed).

* `SourcedHyp` — regularity of the field (as in `C3Field.Hyp`, without the vacuum row and the
  near-Minkowski chart; only nondegeneracy of `g`), the derivative relations of `T, r`, and the
  reduced equation on `[0, T] × 𝕋³`.
* **`SourcedHyp.subsidiary`** (`eq:subsidiary` at every interior point of the slab):
  `□_g C_ν + Ric_ν{}^μ C_μ = -2 𝒲_ν`, `𝒲_ν = κ ∇^μT_{μν} + ∇^μ r_{μν}` — the derivatives of the
  reduced equation along time and space paths (`Jet3.PathDeriv`) feed
  `SubsidiarySource.subsidiary_with_source`.
* `WaveCoeffs` — **uniform wave-energy coefficients and an `L¹_t L^∞_x` curvature potential**:
  `-g^{00} ≥ a₀`, `g^{ij}ξᵢξⱼ ≥ λ|ξ|²`, `|∂g^{-1}| ≤ M`, and the lower-order part of the subsidiary
  operator (Christoffel and curvature terms) has operator norm `≤ m(t)` with `m ≥ 0` continuous;
  at `t = 0`, `-g^{00} ≤ A₁`, `|g^{ij}| ≤ A₁`.
* **`constraint_bound`** (`eq:constraint-bound`): for `t ∈ [0, T]`,
  `‖(C, ∂C)(t)‖_{L²} ≤ C_T (‖(C, ∂C)(0)‖_{L²} + ∫₀ᵀ ‖𝒲‖_{L²})`, with the explicit
  `C_T = 2 c^{-1/2} max(√(3A₁+1), c^{-1/2}) exp(((16M + 2)T + 4∫₀ᵀ m)/(2c))`, `c = min(a₀, λ, 1)`,
  depending only on `a₀, λ, M, A₁, T, ∫₀ᵀ m`.
* `constraint_vanishes` — vanishing initial constraint data and Ward residual force `C ≡ 0`
  (the subsidiary energy vanishes on the slab).
-/

open Finset Matrix Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RenewalGeometry.SubsidiaryConstraint

open ContractedBianchiJet OpenWriterEnergy OpenWriterChart HarmonicDefect OpenWriterContinuum
  TorusSobolevTransfer HarmonicGaugePropagation TorusWaveEnergyForced
open ContractedBianchiJet.SubsidiarySource (divS subsidiary_with_source)

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

set_option linter.unusedSectionVars false

/-- `4 × 4` real matrices. -/
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The hypotheses of `prop:subsidiary`: the regularity of the classical metric field `F`
(continuity on the slab, symmetric records, derivative relations — as in `C3Field.Hyp`),
nondegeneracy of `g = η + Q`, the derivative relations of the stress `Ts` and residual `r` fields
(`dTs t x e`, `dr t x e` are `∂_e Ts`, `∂_e r`), and the reduced Einstein equation
`Ĝ + Λ g = κ Ts + r` on `[0, T] × 𝕋³`. -/
structure SourcedHyp (F : C3Field) (T Λ κ : ℝ) (Ts r : ℝ → T3 → Mat4)
    (dTs dr : ℝ → T3 → Fin 4 → Mat4) : Prop where
  cQ : ContinuousOn (fun p : ℝ × T3 => F.Q p.1 p.2) (Icc 0 T ×ˢ univ)
  cV : ContinuousOn (fun p : ℝ × T3 => F.V p.1 p.2) (Icc 0 T ×ˢ univ)
  cA : ContinuousOn (fun p : ℝ × T3 => F.A p.1 p.2) (Icc 0 T ×ˢ univ)
  cAt : ContinuousOn (fun p : ℝ × T3 => F.At p.1 p.2) (Icc 0 T ×ˢ univ)
  cQd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Qd p.1 i p.2) (Icc 0 T ×ˢ univ)
  cVd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Vd p.1 i p.2) (Icc 0 T ×ˢ univ)
  cAd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Ad p.1 i p.2) (Icc 0 T ×ˢ univ)
  cQdd : ∀ i j, ContinuousOn (fun p : ℝ × T3 => F.Qdd p.1 i j p.2) (Icc 0 T ×ˢ univ)
  cVdd : ∀ i j, ContinuousOn (fun p : ℝ × T3 => F.Vdd p.1 i j p.2) (Icc 0 T ×ˢ univ)
  cQddd : ∀ i j k, ContinuousOn (fun p : ℝ × T3 => F.Qddd p.1 i j k p.2) (Icc 0 T ×ˢ univ)
  sQ : ∀ t x μ ν, F.Q t x μ ν = F.Q t x ν μ
  sV : ∀ t x μ ν, F.V t x μ ν = F.V t x ν μ
  sA : ∀ t x μ ν, F.A t x μ ν = F.A t x ν μ
  sAt : ∀ t x μ ν, F.At t x μ ν = F.At t x ν μ
  sQd : ∀ t i x μ ν, F.Qd t i x μ ν = F.Qd t i x ν μ
  sVd : ∀ t i x μ ν, F.Vd t i x μ ν = F.Vd t i x ν μ
  sAd : ∀ t i x μ ν, F.Ad t i x μ ν = F.Ad t i x ν μ
  sQdd : ∀ t i j x μ ν, F.Qdd t i j x μ ν = F.Qdd t i j x ν μ
  sVdd : ∀ t i j x μ ν, F.Vdd t i j x μ ν = F.Vdd t i j x ν μ
  sQddd : ∀ t i j k x μ ν, F.Qddd t i j k x μ ν = F.Qddd t i j k x ν μ
  iQdd : ∀ t i j, F.Qdd t i j = F.Qdd t j i
  iVdd : ∀ t i j, F.Vdd t i j = F.Vdd t j i
  iQddd1 : ∀ t i j k, F.Qddd t i j k = F.Qddd t j i k
  iQddd2 : ∀ t i j k, F.Qddd t i j k = F.Qddd t i k j
  tQ : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.Q τ x) (F.V t x) t
  tV : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.V τ x) (F.A t x) t
  tA : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.A τ x) (F.At t x) t
  tQd : ∀ t ∈ Ioo 0 T, ∀ i x, HasDerivAt (fun τ => F.Qd τ i x) (F.Vd t i x) t
  tVd : ∀ t ∈ Ioo 0 T, ∀ i x, HasDerivAt (fun τ => F.Vd τ i x) (F.Ad t i x) t
  tQdd : ∀ t ∈ Ioo 0 T, ∀ i j x, HasDerivAt (fun τ => F.Qdd τ i j x) (F.Vdd t i j x) t
  xQ : ∀ t ∈ Icc 0 T, ∀ i, IsLineDeriv i (F.Q t) (F.Qd t i)
  xV : ∀ t ∈ Icc 0 T, ∀ i, IsLineDeriv i (F.V t) (F.Vd t i)
  xA : ∀ t ∈ Icc 0 T, ∀ i, IsLineDeriv i (F.A t) (F.Ad t i)
  xQd : ∀ t ∈ Icc 0 T, ∀ i j, IsLineDeriv i (F.Qd t j) (F.Qdd t i j)
  xVd : ∀ t ∈ Icc 0 T, ∀ i j, IsLineDeriv i (F.Vd t j) (F.Vdd t i j)
  xQdd : ∀ t ∈ Icc 0 T, ∀ i j k, IsLineDeriv i (F.Qdd t j k) (F.Qddd t i j k)
  nondeg : ∀ t ∈ Icc 0 T, ∀ x, (Matrix.of (minkowski + F.Q t x)).det ≠ 0
  cTs : ContinuousOn (fun p : ℝ × T3 => Ts p.1 p.2) (Icc 0 T ×ˢ univ)
  cdTs : ∀ e, ContinuousOn (fun p : ℝ × T3 => dTs p.1 p.2 e) (Icc 0 T ×ˢ univ)
  cr : ContinuousOn (fun p : ℝ × T3 => r p.1 p.2) (Icc 0 T ×ˢ univ)
  cdr : ∀ e, ContinuousOn (fun p : ℝ × T3 => dr p.1 p.2 e) (Icc 0 T ×ˢ univ)
  tTs : ∀ t ∈ Ioo 0 T, ∀ x, MHasDeriv (fun τ => Ts τ x) (dTs t x 0) t
  xTs : ∀ t ∈ Icc 0 T, ∀ (k : Fin 3) x,
    MHasDeriv (fun σ => Ts t (x + lineShift k σ)) (dTs t x k.succ) 0
  tr : ∀ t ∈ Ioo 0 T, ∀ x, MHasDeriv (fun τ => r τ x) (dr t x 0) t
  xr : ∀ t ∈ Icc 0 T, ∀ (k : Fin 3) x,
    MHasDeriv (fun σ => r t (x + lineShift k σ)) (dr t x k.succ) 0
  reduced : ∀ t ∈ Icc 0 T, ∀ x, (F.jetAt t x).resM (F.jetAt t x).gc (F.jetAt t x).dgc +
    Λ • (F.jetAt t x).g = κ • Ts t x + r t x

namespace SourcedHyp

variable {F : C3Field} {T Λ κ : ℝ} {Ts r : ℝ → T3 → Mat4} {dTs dr : ℝ → T3 → Fin 4 → Mat4}

theorem valid (h : SourcedHyp F T Λ κ Ts r dTs dr) {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) :
    (F.jetAt t x).Valid where
  gG := Matrix.mul_nonsing_inv _ (Ne.isUnit (h.nondeg t ht x))
  g_symm := by
    ext μ ν
    simp [C3Field.jetAt, Matrix.transpose_apply, h.sQ t x μ ν, C3Field.minkowski_symm μ ν]
  G_symm := by
    have hT : Matrix.transpose (Matrix.of (minkowski + F.Q t x)) =
        Matrix.of (minkowski + F.Q t x) := by
      ext μ ν; simp [Matrix.transpose_apply, h.sQ t x μ ν, C3Field.minkowski_symm μ ν]
    simp only [C3Field.jetAt]
    rw [Matrix.transpose_nonsing_inv, hT]
  dg_symm := fun a => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [C3Field.jetAt, metricJet, h.sV t x μ ν]
    · simp [C3Field.jetAt, metricJet, h.sQd t i x μ ν]
  ddg_symm := fun a b => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      simp [C3Field.jetAt, h.sA t x μ ν, h.sVd t _ x μ ν, h.sQdd t _ _ x μ ν]
  ddg_comm := fun a b => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      simp [C3Field.jetAt, h.iQdd t]
  dddg_symm := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [C3Field.jetAt, h.sAt t x μ ν, h.sAd t _ x μ ν, h.sVdd t _ _ x μ ν,
        h.sQddd t _ _ _ x μ ν]
  dddg_comm1 := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [C3Field.jetAt, h.iVdd t, h.iQddd1 t]
  dddg_comm2 := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [C3Field.jetAt, h.iVdd t, h.iQddd2 t]

/-- Time paths are consistent jet paths. -/
theorem pathDeriv_time (h : SourcedHyp F T Λ κ Ts r dTs dr) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : T3) :
    Jet3.PathDeriv (fun τ => F.jetAt τ x) 0 t where
  g := C3Field.mhasDeriv_of_rec_add minkowski (h.tQ t ht x)
  G := mhasDeriv_inv (C3Field.mhasDeriv_of_rec_add minkowski (h.tQ t ht x))
    (h.nondeg t (Ioo_subset_Icc_self ht) x)
  dg := fun a => by
    refine Fin.cases ?_ (fun i => ?_) a
    · exact C3Field.mhasDeriv_of_rec (h.tV t ht x)
    · exact C3Field.mhasDeriv_of_rec (h.tQd t ht i x)
  ddg := fun a b => by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact C3Field.mhasDeriv_of_rec (h.tA t ht x)
    · exact C3Field.mhasDeriv_of_rec (h.tVd t ht j x)
    · exact C3Field.mhasDeriv_of_rec (h.tVd t ht i x)
    · exact C3Field.mhasDeriv_of_rec (h.tQdd t ht i j x)

/-- Spatial paths are consistent jet paths. -/
theorem pathDeriv_space (h : SourcedHyp F T Λ κ Ts r dTs dr) {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3)
    (k : Fin 3) : Jet3.PathDeriv (fun σ => F.jetAt t (x + lineShift k σ)) k.succ 0 where
  g := C3Field.mhasDeriv_of_rec_add minkowski (C3Field.hasDerivAt_shift (h.xQ t ht k) x)
  G := mhasDeriv_inv (C3Field.mhasDeriv_of_rec_add minkowski
    (C3Field.hasDerivAt_shift (h.xQ t ht k) x))
    (by rw [lineShift_zero, add_zero]; exact h.nondeg t ht x)
  dg := fun a => by
    refine Fin.cases ?_ (fun i => ?_) a
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xV t ht k) x)
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xQd t ht k i) x)
  ddg := fun a b => by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xA t ht k) x)
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xVd t ht k j) x)
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xVd t ht k i) x)
    · exact C3Field.mhasDeriv_of_rec (C3Field.hasDerivAt_shift (h.xQdd t ht k i j) x)

/-- Two matrix functions agreeing near `s` with derivatives `A', B'` there have `A' = B'`. -/
theorem mhasDeriv_unique {A B : ℝ → Mat4} {A' B' : Mat4} {s : ℝ} (hA : MHasDeriv A A' s)
    (hB : MHasDeriv B B' s) (hAB : ∀ᶠ s' in 𝓝 s, A s' = B s') : A' = B' := by
  ext i j
  exact (hA i j).unique ((hB i j).congr_of_eventuallyEq (hAB.mono fun s' hs' => by
    simp only [hs']))

/-- The derivative of the reduced equation along a consistent jet path. -/
theorem deriv_reduced {J : ℝ → Jet3 (Fin 4)} {e : Fin 4} {s : ℝ} (hJ : Jet3.PathDeriv J e s)
    {S : ℝ → Mat4} {S' : Mat4} (hS : MHasDeriv S S' s)
    (hEq : ∀ᶠ s' in 𝓝 s, (J s').resM (J s').gc (J s').dgc + Λ • (J s').g = S s') :
    (J s).dresM (J s).gc (J s).dgc (J s).ddgc e + Λ • (J s).dg e = S' := by
  have h1 := hJ.resM.add (MHasDeriv.smul (hasDerivAt_const s Λ) hJ.g)
  refine mhasDeriv_unique (h1.congr ?_) hS hEq
  simp

theorem mhasDeriv_source {S R : ℝ → Mat4} {S' R' : Mat4} {s : ℝ} (hS : MHasDeriv S S' s)
    (hR : MHasDeriv R R' s) : MHasDeriv (fun s => κ • S s + R s) (κ • S' + R') s :=
  (MHasDeriv.smul (hasDerivAt_const s κ) hS).add hR |>.congr (by simp)

/-- **`eq:subsidiary`** at every interior point of the slab: the harmonic gauge covector of a
classical solution of the reduced equation with sources satisfies
`□C_b + Ric^l{}_b C_l = -2 (κ ∇^aT_{ab} + ∇^a r_{ab})`. -/
theorem subsidiary (h : SourcedHyp F T Λ κ Ts r dTs dr) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : T3)
    (b : Fin 4) :
    (F.jetAt t x).boxC (F.jetAt t x).gc (F.jetAt t x).dgc (F.jetAt t x).ddgc b +
      (F.jetAt t x).ricC (F.jetAt t x).gc b =
      -2 * (κ * divS (F.jetAt t x) (Ts t x) (dTs t x) b +
        divS (F.jetAt t x) (r t x) (dr t x) b) := by
  have htc := Ioo_subset_Icc_self ht
  have hv := h.valid htc x
  refine subsidiary_with_source hv _ _ _ (fun e a => Jet3.ddgc_swap hv e a) Λ κ (Ts t x) (r t x)
    (dTs t x) (dr t x) (h.reduced t htc x) (fun e => ?_) b
  refine Fin.cases ?_ (fun k => ?_) e
  · -- the time direction
    refine deriv_reduced (h.pathDeriv_time ht x) (mhasDeriv_source (h.tTs t ht x) (h.tr t ht x)) ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact h.reduced τ (Ioo_subset_Icc_self hτ) x
  · -- a spatial direction
    have hP := h.pathDeriv_space htc x k
    have key := deriv_reduced hP (mhasDeriv_source (h.xTs t htc k x) (h.xr t htc k x))
      (Eventually.of_forall fun σ => h.reduced t htc _)
    simpa only [C3Field.jetAt_shift_zero] using key

/-- The clamped jet family is continuous. -/
theorem jetCont (h : SourcedHyp F T Λ κ Ts r dTs dr) (hT : 0 ≤ T) :
    JetFam.JetCont (F.jc T) := by
  have cl := fun {f : ℝ → T3 → MetricRec} hf => C3Field.cont_clamp hT (f := f) hf
  have hQ := cl h.cQ
  have hg : Continuous fun p : ℝ × T3 => minkowski + F.Q (clampT T p.1) p.2 :=
    continuous_const.add hQ
  refine ⟨hg, ?_, fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun p => ?_
    have hd := h.nondeg _ (clampT_mem hT p.1) p.2
    exact ContinuousAt.comp (g := fun g : MetricRec => (Matrix.of g)⁻¹ i j)
      ((analyticAt_inv_entry _ hd i j).continuousAt) hg.continuousAt
  · refine Fin.cases ?_ (fun i => ?_) a
    · exact cl h.cV
    · exact cl (f := fun t x => F.Qd t i x) (h.cQd i)
  · refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact cl h.cA
    · exact cl (f := fun t x => F.Vd t j x) (h.cVd j)
    · exact cl (f := fun t x => F.Vd t i x) (h.cVd i)
    · exact cl (f := fun t x => F.Qdd t i j x) (h.cQdd i j)
  · refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c
    · exact cl h.cAt
    · exact cl (f := fun t x => F.Ad t k x) (h.cAd k)
    · exact cl (f := fun t x => F.Ad t j x) (h.cAd j)
    · exact cl (f := fun t x => F.Vdd t j k x) (h.cVdd j k)
    · exact cl (f := fun t x => F.Ad t i x) (h.cAd i)
    · exact cl (f := fun t x => F.Vdd t i k x) (h.cVdd i k)
    · exact cl (f := fun t x => F.Vdd t i j x) (h.cVdd i j)
    · exact cl (f := fun t x => F.Qddd t i j k x) (h.cQddd i j k)

end SourcedHyp

/-! ### The subsidiary system as a forced linear wave system -/

/-- Continuity of the covariant divergence along a continuous jet family. -/
theorem continuous_divS {X : Type*} [TopologicalSpace X] {J : X → Jet3 (Fin 4)}
    (hJ : JetFam.JetCont J) {S : X → Mat4} {dS : X → Fin 4 → Mat4} (hS : Continuous S)
    (hdS : ∀ e, Continuous fun p => dS p e) (b : Fin 4) :
    Continuous fun p => divS (J p) (S p) (dS p) b := by
  unfold divS
  refine continuous_finsetSum _ fun e _ => continuous_finsetSum _ fun a _ => ?_
  exact (hJ.G.matrix_elem e a).mul ((((hdS e).sub ((hJ.chr e).matrix_transpose.matrix_mul hS)).sub
    (hS.matrix_mul (hJ.chr e))).matrix_elem a b)

/-- The Ward source `𝒲_b = κ ∇^aT_{ab} + ∇^a r_{ab}` of the field. -/
def ward (F : C3Field) (κ : ℝ) (Ts r : ℝ → T3 → Mat4) (dTs dr : ℝ → T3 → Fin 4 → Mat4)
    (t : ℝ) (x : T3) (b : Fin 4) : ℝ :=
  κ * divS (F.jetAt t x) (Ts t x) (dTs t x) b + divS (F.jetAt t x) (r t x) (dr t x) b

/-- Its `L²(𝕋³)` norm at time `t`. -/
def wardNorm (F : C3Field) (κ : ℝ) (Ts r : ℝ → T3 → Mat4) (dTs dr : ℝ → T3 → Fin 4 → Mat4)
    (t : ℝ) : ℝ :=
  Real.sqrt (∫ x, ∑ b, ward F κ Ts r dTs dr t x b ^ 2)

/-- The pointwise subsidiary energy size `Σ_b (|∂ₜC_b|² + |∇C_b|² + C_b²)` of the harmonic gauge
covector `C = C(g)`. -/
def csize (F : C3Field) (t : ℝ) (x : T3) : ℝ :=
  ∑ b, ((F.jetAt t x).dgc 0 b ^ 2 + ∑ i : Fin 3, (F.jetAt t x).dgc i.succ b ^ 2 +
    (F.jetAt t x).gc b ^ 2)

/-- The forced wave data of the subsidiary system: the data `C3Field.waveData` of the gauge
covector with non-principal part `lowerOp + 2𝒲` (time clamped to `[0, T]`). -/
def waveDataF (F : C3Field) (T κ : ℝ) (Ts r : ℝ → T3 → Mat4)
    (dTs dr : ℝ → T3 → Fin 4 → Mat4) : TorusWaveEnergy.WaveData (Fin 4) :=
  { F.waveData T with
    L := fun t x b => JetFam.lowerOp (F.jc T (t, x)) (F.jc T (t, x)).gc
        (fun e b => (F.jc T (t, x)).dgc e b) b +
      2 * ward F κ Ts r dTs dr (clampT T t) x b }

/-- **Uniform wave-energy coefficients and an `L¹_t L^∞_x` curvature potential** on the slab:
`-g^{00} ≥ a₀`, `g^{ij}ξᵢξⱼ ≥ λ|ξ|²`, `|∂_e g^{μν}| ≤ M`; the lower-order part of the subsidiary
operator (Christoffel and curvature terms, `JetFam.lowerOp`) has operator norm at most `m(t)`, with
`m ≥ 0` continuous (its `L¹(0, T)` norm enters the constant). -/
structure WaveCoeffs (F : C3Field) (T a₀ lam M : ℝ) (m : ℝ → ℝ) : Prop where
  coer_a : ∀ t ∈ Icc 0 T, ∀ x, a₀ ≤ -(F.jetAt t x).G 0 0
  coer_γ : ∀ t ∈ Icc 0 T, ∀ x (ξ : Fin 3 → ℝ),
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (F.jetAt t x).G i.succ j.succ * ξ i * ξ j
  bnd_dG : ∀ t ∈ Icc 0 T, ∀ x e μ ν, |((F.jetAt t x).dG e) μ ν| ≤ M
  cont_m : Continuous m
  m_nonneg : ∀ t, 0 ≤ m t
  pot : ∀ t ∈ Icc 0 T, ∀ x b (c : Fin 4 → ℝ) (dc : Fin 4 → Fin 4 → ℝ),
    |JetFam.lowerOp (F.jetAt t x) c dc b| ≤ m t * ‖((c, dc) : (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ))‖

/-- The forced principal split: if `□C + Ric·C = -2𝒲` then
`-g^{00}∂ₜ²C = 2g^{0i}∂ᵢ∂ₜC + g^{ij}∂ᵢ∂ⱼC + lowerOp + 2𝒲`. -/
theorem principal_split_forced {J : Jet3 (Fin 4)} (hv : J.Valid) (b : Fin 4) (w : ℝ)
    (hsub : J.boxC J.gc J.dgc J.ddgc b + J.ricC J.gc b = -2 * w) :
    -J.G 0 0 * J.ddgc 0 0 b = 2 * ∑ i : Fin 3, J.G 0 i.succ * J.ddgc i.succ 0 b +
      ∑ i : Fin 3, ∑ j : Fin 3, J.G i.succ j.succ * J.ddgc i.succ j.succ b +
      (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b + 2 * w) := by
  have hsplit : J.boxC J.gc J.dgc J.ddgc b = ∑ e, ∑ a, J.G e a * J.ddgc e a b +
      ∑ e, ∑ a, J.G e a * J.nnc J.gc J.dgc (fun _ => 0) e a b := by
    unfold Jet3.boxC
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← JetFam.nnc_sub_ddc]
    ring
  have hlow : JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b =
      ∑ e, ∑ a, J.G e a * J.nnc J.gc J.dgc (fun _ => 0) e a b + J.ricC J.gc b := rfl
  have hGs : ∀ i : Fin 3, J.G i.succ 0 = J.G 0 i.succ := fun i => by
    have := congrFun (congrFun hv.G_symm 0) i.succ
    simpa [Matrix.transpose_apply] using this
  have hds : ∀ i : Fin 3, J.ddgc 0 i.succ b = J.ddgc i.succ 0 b := fun i =>
    congrFun (Jet3.ddgc_swap hv 0 i.succ) b
  have hpr : ∑ e, ∑ a, J.G e a * J.ddgc e a b = J.G 0 0 * J.ddgc 0 0 b +
      2 * ∑ i : Fin 3, J.G 0 i.succ * J.ddgc i.succ 0 b +
      ∑ i : Fin 3, ∑ j : Fin 3, J.G i.succ j.succ * J.ddgc i.succ j.succ b := by
    simp only [Fin.sum_univ_succ (n := 3), hGs, hds, Finset.sum_add_distrib]
    ring
  rw [hsplit, hpr] at hsub
  rw [hlow]
  linarith

theorem cont_clamp' {E : Type*} [TopologicalSpace E] {T : ℝ} (hT : 0 ≤ T) {f : ℝ → T3 → E}
    (hf : ContinuousOn (fun p : ℝ × T3 => f p.1 p.2) (Icc 0 T ×ˢ univ)) :
    Continuous fun p : ℝ × T3 => f (clampT T p.1) p.2 :=
  hf.comp_continuous (((continuous_clampT T).comp continuous_fst).prodMk continuous_snd)
    fun p => ⟨clampT_mem hT p.1, Set.mem_univ _⟩

variable {F : C3Field} {T Λ κ : ℝ} {Ts r : ℝ → T3 → Mat4} {dTs dr : ℝ → T3 → Fin 4 → Mat4}
  {a₀ lam M : ℝ} {m : ℝ → ℝ}

theorem continuous_ward (h : SourcedHyp F T Λ κ Ts r dTs dr) (hT : 0 ≤ T) (b : Fin 4) :
    Continuous fun p : ℝ × T3 => ward F κ Ts r dTs dr (clampT T p.1) p.2 b := by
  have hJ := h.jetCont hT
  unfold ward
  exact (continuous_const.mul (continuous_divS hJ (cont_clamp' hT h.cTs)
    (fun e => cont_clamp' hT (f := fun t x => dTs t x e) (h.cdTs e)) b)).add
    (continuous_divS hJ (cont_clamp' hT h.cr)
      (fun e => cont_clamp' hT (f := fun t x => dr t x e) (h.cdr e)) b)

set_option maxHeartbeats 1000000 in
/-- **The subsidiary system with sources is a forced linear wave system** with lower-order part
`lowerOp` (potential `2m(t)`) and forcing `2𝒲`. -/
theorem forcedSolves (h : SourcedHyp F T Λ κ Ts r dTs dr) (hc : WaveCoeffs F T a₀ lam M m)
    (hT : 0 ≤ T) :
    ForcedSolves (waveDataF F T κ Ts r dTs dr)
      (fun t x b => JetFam.lowerOp (F.jc T (t, x)) (F.jc T (t, x)).gc
        (fun e b => (F.jc T (t, x)).dgc e b) b)
      (fun t x b => 2 * ward F κ Ts r dTs dr (clampT T t) x b) (fun t => 2 * m t) T a₀ lam M := by
  have hJ := h.jetCont hT
  have hvalc : ∀ t x, (F.jc T (t, x)).Valid := fun t x => h.valid (clampT_mem hT t) x
  exact {
    cont_u := fun b => hJ.gc b
    cont_ut := fun b => hJ.dgc.matrix_elem 0 b
    cont_utt := fun b => (hJ.ddgc 0).matrix_elem 0 b
    cont_ux := fun i b => hJ.dgc.matrix_elem i.succ b
    cont_uxt := fun i b => (hJ.ddgc i.succ).matrix_elem 0 b
    cont_uxx := fun i j b => (hJ.ddgc i.succ).matrix_elem j.succ b
    cont_a := (hJ.G.matrix_elem 0 0).neg
    cont_at := ((hJ.dG 0).matrix_elem 0 0).neg
    cont_β := fun i => hJ.G.matrix_elem 0 i.succ
    cont_βdiv := fun i => (hJ.dG i.succ).matrix_elem 0 i.succ
    cont_γ := fun i j => hJ.G.matrix_elem i.succ j.succ
    cont_γt := fun i j => (hJ.dG 0).matrix_elem i.succ j.succ
    cont_γx := fun i j => (hJ.dG i.succ).matrix_elem i.succ j.succ
    cont_L0 := fun b => (hJ.lowerOp (continuous_pi fun b => hJ.gc b) hJ.dgc b)
    cont_W := fun b => continuous_const.mul (continuous_ward h hT b)
    cont_m := continuous_const.mul hc.cont_m
    L_eq := fun t x b => rfl
    dt_u := fun t ht x b => by
      have := (h.pathDeriv_time ht x).gc b
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq (Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((C3Field.jc_eventually (F := F) ht x).mono
        fun s hs => by simp only [hs])
    dt_ut := fun t ht x b => by
      have := (h.pathDeriv_time ht x).dgc 0 b
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq (Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((C3Field.jc_eventually (F := F) ht x).mono
        fun s hs => by simp only [hs])
    dt_ux := fun t ht i x b => by
      have := (h.pathDeriv_time ht x).dgc i.succ b
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq (Ioo_subset_Icc_self ht)]
      rw [← congrFun (Jet3.ddgc_swap (h.valid (Ioo_subset_Icc_self ht) x) 0 i.succ) b]
      exact this.congr_of_eventuallyEq ((C3Field.jc_eventually (F := F) ht x).mono
        fun s hs => by simp only [hs])
    dt_a := fun t ht x => by
      have := ((h.pathDeriv_time ht x).G 0 0).neg
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq (Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((C3Field.jc_eventually (F := F) ht x).mono
        fun s hs => by simp only [hs, Pi.neg_apply])
    dt_γ := fun t ht i j x => by
      have := (h.pathDeriv_time ht x).G i.succ j.succ
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq (Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((C3Field.jc_eventually (F := F) ht x).mono
        fun s hs => by simp only [hs])
    dx_u := fun t ht i b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).gc b
      simpa only [waveDataF, C3Field.waveData, C3Field.jc, C3Field.jetAt_shift_zero] using this
    dx_ut := fun t ht i b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).dgc 0 b
      simpa only [waveDataF, C3Field.waveData, C3Field.jc, C3Field.jetAt_shift_zero] using this
    dx_ux := fun t ht i j b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).dgc j.succ b
      simpa only [waveDataF, C3Field.waveData, C3Field.jc, C3Field.jetAt_shift_zero] using this
    dx_β := fun t ht i x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).G 0 i.succ
      simpa only [waveDataF, C3Field.waveData, C3Field.jc, C3Field.jetAt_shift_zero] using this
    dx_γ := fun t ht i j x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).G i.succ j.succ
      simpa only [waveDataF, C3Field.waveData, C3Field.jc, C3Field.jetAt_shift_zero] using this
    γ_symm := fun t i j x => by
      have := congrFun (congrFun (hvalc t x).G_symm i.succ) j.succ
      simpa [waveDataF, C3Field.waveData, Matrix.transpose_apply] using this.symm
    eqn := fun t ht x b => by
      have htc := Ioo_subset_Icc_self ht
      have hsub := h.subsidiary ht x b
      have := principal_split_forced (h.valid htc x) b (ward F κ Ts r dTs dr t x b) hsub
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq htc, clampT_of_mem htc]
      linarith
    coer_a := fun t ht x => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht]
      exact hc.coer_a t ht x
    coer_γ := fun t ht x ξ => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht]
      exact hc.coer_γ t ht x ξ
    bnd_at := fun t ht x => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht, abs_neg]
      exact hc.bnd_dG t ht x 0 0 0
    bnd_βdiv := fun t ht i x => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht]
      exact hc.bnd_dG t ht x _ _ _
    bnd_γt := fun t ht i j x => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht]
      exact hc.bnd_dG t ht x _ _ _
    bnd_γx := fun t ht i j x => by
      simp only [waveDataF, C3Field.waveData, C3Field.jc_eq ht]
      exact hc.bnd_dG t ht x _ _ _
    m_nonneg := fun t => mul_nonneg zero_le_two (hc.m_nonneg t)
    bnd_L0 := fun t ht x => by
      set J := F.jc T (t, x) with hJdef
      have hJt : J = F.jetAt t x := C3Field.jc_eq ht x
      set S := ∑ b, (J.dgc 0 b ^ 2 + ∑ i : Fin 3, J.dgc i.succ b ^ 2 + J.gc b ^ 2)
      have hS : 0 ≤ S := Finset.sum_nonneg fun b _ => by positivity
      have hn := C3Field.norm_le_sqrt_size J.gc (fun e b => J.dgc e b)
      have hLb : ∀ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2 ≤ m t ^ 2 * S := by
        intro b
        have h1 := hc.pot t ht x b J.gc (fun e b => J.dgc e b)
        rw [← hJt] at h1
        have h2 : |JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b| ≤ m t * Real.sqrt S :=
          h1.trans (mul_le_mul_of_nonneg_left hn (hc.m_nonneg t))
        have h3 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
        rw [mul_pow, Real.sq_sqrt hS] at h3
        exact h3
      have hsum : ∑ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2 ≤
          (2 * m t) ^ 2 * S := by
        calc ∑ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2
            ≤ ∑ _b : Fin 4, m t ^ 2 * S := Finset.sum_le_sum fun b _ => hLb b
          _ = (2 * m t) ^ 2 * S := by simp; ring
      exact hsum }

/-- The explicit constant of `eq:constraint-bound`. -/
def constC (T a₀ lam M A₁ : ℝ) (m : ℝ → ℝ) : ℝ :=
  2 * ((Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ *
    max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ *
    Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, 2 * m s) / (2 * ForcedSolves.cmin a₀ lam)))

theorem constC_nonneg (T a₀ lam M A₁ : ℝ) (m : ℝ → ℝ) : 0 ≤ constC T a₀ lam M A₁ m := by
  unfold constC
  have h1 : 0 ≤ (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have h2 : 0 ≤ max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  positivity

theorem wardNorm_nonneg (F : C3Field) (κ : ℝ) (Ts r : ℝ → T3 → Mat4)
    (dTs dr : ℝ → T3 → Fin 4 → Mat4) (t : ℝ) : 0 ≤ wardNorm F κ Ts r dTs dr t :=
  Real.sqrt_nonneg _

theorem csize_nonneg (F : C3Field) (t : ℝ) (x : T3) : 0 ≤ csize F t x :=
  Finset.sum_nonneg fun b _ => by positivity

/-- **`prop:subsidiary`, the constraint bound `eq:constraint-bound`**: on the closed slab
`[0, T] × 𝕋³`, for a classical solution of the reduced Einstein equation with sources and
uniform wave-energy coefficients with an `L¹_t L^∞_x` curvature potential `m`, the harmonic gauge
covector satisfies, for every `t ∈ [0, T]`,
`‖(C, ∂C)(t)‖_{L²} ≤ C_T (‖(C, ∂C)(0)‖_{L²} + ‖𝒲‖_{L¹_t L²_x})`
with `C_T = constC T a₀ λ M A₁ m` (depending only on `a₀, λ, M, A₁, T` and `∫₀ᵀ m`). -/
theorem constraint_bound (h : SourcedHyp F T Λ κ Ts r dTs dr) (hc : WaveCoeffs F T a₀ lam M m)
    (ha₀ : 0 < a₀) (hlam : 0 < lam) {A₁ : ℝ} (hA₁a : ∀ x, -(F.jetAt 0 x).G 0 0 ≤ A₁)
    (hA₁γ : ∀ (i j : Fin 3) x, |(F.jetAt 0 x).G i.succ j.succ| ≤ A₁) :
    ∀ t ∈ Icc 0 T, Real.sqrt (∫ x, csize F t x) ≤ constC T a₀ lam M A₁ m *
      (Real.sqrt (∫ x, csize F 0 x) + ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hF := forcedSolves h hc hT
  have hcl0 : clampT T 0 = 0 := clampT_of_mem h0
  have hsb := ForcedSolves.size_bound hF ha₀ hlam (A₁ := A₁)
    (fun x => by simp only [waveDataF, C3Field.waveData, C3Field.jc, hcl0]; exact hA₁a x)
    (fun i j x => by simp only [waveDataF, C3Field.waveData, C3Field.jc, hcl0]; exact hA₁γ i j x)
    t ht
  have hsz : ∀ τ ∈ Icc 0 T, (fun x => (waveDataF F T κ Ts r dTs dr).size τ x) = csize F τ := by
    intro τ hτ
    funext x
    simp only [TorusWaveEnergy.WaveData.size, waveDataF, C3Field.waveData, csize,
      C3Field.jc_eq hτ]
  have hwn : ∀ s ∈ Icc 0 T,
      ForcedSolves.wnorm (fun t x b => 2 * ward F κ Ts r dTs dr (clampT T t) x b) s =
        2 * wardNorm F κ Ts r dTs dr s := by
    intro s hs
    unfold ForcedSolves.wnorm wardNorm
    simp only [clampT_of_mem hs, mul_pow]
    simp_rw [← Finset.mul_sum]
    rw [integral_const_mul, Real.sqrt_mul (by norm_num),
      show (2 : ℝ) ^ 2 = 2 * 2 by norm_num, Real.sqrt_mul_self (by norm_num)]
  have hint : ∫ s in (0)..T,
      ForcedSolves.wnorm (fun t x b => 2 * ward F κ Ts r dTs dr (clampT T t) x b) s =
      2 * ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    exact hwn s hs
  rw [hsz t ht, hsz 0 h0, hint] at hsb
  have hK : 0 ≤ (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ *
      max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ *
      Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, 2 * m s) /
        (2 * ForcedSolves.cmin a₀ lam)) := by
    have h1 : 0 ≤ (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have h2 : 0 ≤ max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt (ForcedSolves.cmin a₀ lam))⁻¹ :=
      (Real.sqrt_nonneg _).trans (le_max_left _ _)
    positivity
  have hWi : 0 ≤ ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s :=
    intervalIntegral.integral_nonneg hT fun s _ => wardNorm_nonneg F κ Ts r dTs dr s
  have hS0 := Real.sqrt_nonneg (∫ x, csize F 0 x)
  refine hsb.trans ?_
  unfold constC
  have : Real.sqrt (∫ x, csize F 0 x) + 2 * ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s ≤
      2 * (Real.sqrt (∫ x, csize F 0 x) + ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s) := by
    linarith
  calc _ ≤ _ * (2 * (Real.sqrt (∫ x, csize F 0 x) + ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s)) :=
        mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

theorem continuous_csize (h : SourcedHyp F T Λ κ Ts r dTs dr) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous fun x => csize F t x := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hJ := h.jetCont hT
  have hc : Continuous fun p : ℝ × T3 => ∑ b, ((F.jc T p).dgc 0 b ^ 2 +
      ∑ i : Fin 3, (F.jc T p).dgc i.succ b ^ 2 + (F.jc T p).gc b ^ 2) := by
    have h1 := fun b => hJ.gc b
    have h2 := fun e b => hJ.dgc.matrix_elem e b
    fun_prop
  have := TorusWaveEnergy.WaveData.continuous_slice hc t
  refine this.congr fun x => ?_
  simp only [csize, C3Field.jc_eq ht]

/-- **Constraint propagation**: vanishing initial constraint data and vanishing Ward residual on
the slab force `C(g) ≡ 0` and `∂C(g) ≡ 0` on `[0, T] × 𝕋³`. -/
theorem constraint_vanishes (h : SourcedHyp F T Λ κ Ts r dTs dr) (hc : WaveCoeffs F T a₀ lam M m)
    (ha₀ : 0 < a₀) (hlam : 0 < lam) {A₁ : ℝ} (hA₁a : ∀ x, -(F.jetAt 0 x).G 0 0 ≤ A₁)
    (hA₁γ : ∀ (i j : Fin 3) x, |(F.jetAt 0 x).G i.succ j.succ| ≤ A₁)
    (hC0 : ∀ x, csize F 0 x = 0) (hW : ∀ t ∈ Icc 0 T, ∀ x b, ward F κ Ts r dTs dr t x b = 0) :
    ∀ t ∈ Icc 0 T, ∀ x, csize F t x = 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hb := constraint_bound h hc ha₀ hlam hA₁a hA₁γ t ht
  have hW0 : ∫ s in (0)..T, wardNorm F κ Ts r dTs dr s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · simp
    · rw [uIcc_of_le hT] at hs
      simp [wardNorm, hW s hs]
  simp only [hC0, integral_zero, Real.sqrt_zero, hW0, add_zero, mul_zero] at hb
  have hz : ∫ x, csize F t x = 0 := by
    have h1 := Real.sqrt_eq_zero'.1 (le_antisymm hb (Real.sqrt_nonneg _))
    exact le_antisymm h1 (integral_nonneg fun x => csize_nonneg F t x)
  intro x
  by_contra hne
  have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := (volume : Measure T3))
    (continuous_csize h ht) (TorusWaveEnergy.integrable_of_continuous (continuous_csize h ht))
    (fun y => csize_nonneg F t y) hne
  linarith

/-- **Uniformity** (the last sentence of `prop:subsidiary`): for a family of solutions with common
wave-energy constants `a₀, λ, M, A₁`, potentials with uniformly bounded `∫₀ᵀ m_n ≤ B`, whose initial
constraint data and Ward residuals tend to zero in `L²` and `L¹_t L²_x`, the constraint tends to
zero in `L^∞_t L²_x` (the subsidiary energy norm). -/
theorem constraint_tendsto {Fn : ℕ → C3Field} {Λn κn : ℕ → ℝ} {Tsn rn : ℕ → ℝ → T3 → Mat4}
    {dTsn drn : ℕ → ℝ → T3 → Fin 4 → Mat4} {mn : ℕ → ℝ → ℝ} {A₁ B : ℝ}
    (h : ∀ n, SourcedHyp (Fn n) T (Λn n) (κn n) (Tsn n) (rn n) (dTsn n) (drn n))
    (hc : ∀ n, WaveCoeffs (Fn n) T a₀ lam M (mn n)) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    (hT : 0 ≤ T) (hA₁a : ∀ n x, -((Fn n).jetAt 0 x).G 0 0 ≤ A₁)
    (hA₁γ : ∀ n (i j : Fin 3) x, |((Fn n).jetAt 0 x).G i.succ j.succ| ≤ A₁)
    (hB : ∀ n, ∫ s in (0)..T, mn n s ≤ B)
    (hdata : Tendsto (fun n => Real.sqrt (∫ x, csize (Fn n) 0 x) +
      ∫ s in (0)..T, wardNorm (Fn n) (κn n) (Tsn n) (rn n) (dTsn n) (drn n) s) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, Real.sqrt (∫ x, csize (Fn n) t x) ≤ ε := by
  intro ε hε
  set c := ForcedSolves.cmin a₀ lam
  set K := 2 * ((Real.sqrt c)⁻¹ * max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt c)⁻¹ *
    Real.exp (((16 * M + 2) * T + 4 * B) / (2 * c)))
  have hc0 : 0 < c := ForcedSolves.cmin_pos ha₀ hlam
  have hK : ∀ n, constC T a₀ lam M A₁ (mn n) ≤ K := by
    intro n
    unfold constC
    have h1 : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have h2 : 0 ≤ max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt c)⁻¹ :=
      (Real.sqrt_nonneg _).trans (le_max_left _ _)
    have h3 : ∫ s in (0)..T, 2 * mn n s ≤ 2 * B := by
      rw [intervalIntegral.integral_const_mul]; linarith [hB n]
    have h4 : Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, 2 * mn n s) / (2 * c)) ≤
        Real.exp (((16 * M + 2) * T + 4 * B) / (2 * c)) := by
      refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (by positivity))
      linarith
    have := mul_le_mul_of_nonneg_left h4 (mul_nonneg h1 h2)
    linarith
  have hK0 : 0 ≤ K := (constC_nonneg T a₀ lam M A₁ (mn 0)).trans (hK 0)
  have hev := (hdata.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (K + 1) by positivity)))
  filter_upwards [hev] with n hn t ht
  have hb := constraint_bound (h n) (hc n) ha₀ hlam (hA₁a n) (hA₁γ n) t ht
  have hd0 : 0 ≤ Real.sqrt (∫ x, csize (Fn n) 0 x) +
      ∫ s in (0)..T, wardNorm (Fn n) (κn n) (Tsn n) (rn n) (dTsn n) (drn n) s :=
    add_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg hT fun s _ =>
      wardNorm_nonneg _ _ _ _ _ _ s)
  calc Real.sqrt (∫ x, csize (Fn n) t x) ≤ constC T a₀ lam M A₁ (mn n) * _ := hb
    _ ≤ K * (ε / (K + 1)) := mul_le_mul (hK n) hn.le hd0 hK0
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith


/-! ### Non-vacuity: the flat metric with zero sources -/

/-- The flat field `g = η`. -/
def flatField : C3Field := ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0,
  fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩

theorem minkowski_mul_self : Matrix.of minkowski * Matrix.of minkowski = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, minkowski, Matrix.one_apply]

theorem minkowski_inv : (Matrix.of minkowski)⁻¹ = Matrix.of minkowski :=
  Matrix.inv_eq_left_inv minkowski_mul_self

theorem flat_jetAt (t : ℝ) (x : T3) : flatField.jetAt t x =
    ⟨Matrix.of minkowski, Matrix.of minkowski, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ := by
  have h0 : (minkowski + (0 : MetricRec)) = minkowski := add_zero _
  simp only [C3Field.jetAt, flatField, h0, minkowski_inv]
  congr 1
  · funext a; ext μ ν; refine Fin.cases ?_ (fun i => ?_) a <;> simp [metricJet]
  · funext a b; ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;> simp
  · funext a b c; ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;> simp


/-- The flat jet. -/
abbrev J0 : Jet3 (Fin 4) := ⟨Matrix.of minkowski, Matrix.of minkowski, fun _ => 0, fun _ _ => 0,
  fun _ _ _ => 0⟩

theorem J0_low (a : Fin 4) : J0.low a = 0 := by ext; simp [Jet3.low]
theorem J0_dlow (b a : Fin 4) : J0.dlow b a = 0 := by ext; simp [Jet3.dlow]
theorem J0_chr (a : Fin 4) : J0.chr a = 0 := by simp [Jet3.chr, J0_low]
theorem J0_dchr (b a : Fin 4) : J0.dchr b a = 0 := by simp [Jet3.dchr, J0_dlow, J0_chr]
theorem J0_riem (a b : Fin 4) : J0.riem a b = 0 := by simp [Jet3.riem, J0_chr, J0_dchr]
theorem J0_ricM : J0.ricM = 0 := by ext; simp [Jet3.ricM, J0_riem]
theorem J0_gc : J0.gc = 0 := by funext b; simp [Jet3.gc, Jet3.gcUp, J0_chr]
theorem J0_dgc : J0.dgc = 0 := by ext; simp [Jet3.dgc, Jet3.gcUp, Jet3.dgcUp, J0_chr, J0_dchr, Jet3.dG]
theorem J0_resM : J0.resM J0.gc J0.dgc = 0 := by
  have h1 : J0.nc J0.gc J0.dgc = 0 := by
    ext; simp [Jet3.nc, Jet3.chrC, J0_chr, J0_dgc]
  simp only [Jet3.resM, Jet3.einM, J0_ricM, Jet3.scal, Jet3.hM, h1, Jet3.trN]
  simp
theorem J0_dG (e : Fin 4) : J0.dG e = 0 := by simp [Jet3.dG]
theorem J0_lowerOp (c : Fin 4 → ℝ) (dc : Fin 4 → Fin 4 → ℝ) (b : Fin 4) :
    JetFam.lowerOp J0 c dc b = 0 := by
  simp [JetFam.lowerOp, Jet3.nnc, Jet3.dnc, Jet3.nc, Jet3.chrC, J0_chr, J0_dchr, Jet3.ricC, J0_ricM]

theorem flat_jetAt' (t : ℝ) (x : T3) : flatField.jetAt t x = J0 := flat_jetAt t x

theorem flat_sourced (T : ℝ) :
    SourcedHyp flatField T 0 0 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) where
  cQ := continuousOn_const
  cV := continuousOn_const
  cA := continuousOn_const
  cAt := continuousOn_const
  cQd := fun _ => continuousOn_const
  cVd := fun _ => continuousOn_const
  cAd := fun _ => continuousOn_const
  cQdd := fun _ _ => continuousOn_const
  cVdd := fun _ _ => continuousOn_const
  cQddd := fun _ _ _ => continuousOn_const
  sQ := fun _ _ _ _ => rfl
  sV := fun _ _ _ _ => rfl
  sA := fun _ _ _ _ => rfl
  sAt := fun _ _ _ _ => rfl
  sQd := fun _ _ _ _ _ => rfl
  sVd := fun _ _ _ _ _ => rfl
  sAd := fun _ _ _ _ _ => rfl
  sQdd := fun _ _ _ _ _ _ => rfl
  sVdd := fun _ _ _ _ _ _ => rfl
  sQddd := fun _ _ _ _ _ _ _ => rfl
  iQdd := fun _ _ _ => rfl
  iVdd := fun _ _ _ => rfl
  iQddd1 := fun _ _ _ _ => rfl
  iQddd2 := fun _ _ _ _ => rfl
  tQ := fun _ _ _ => hasDerivAt_const _ _
  tV := fun _ _ _ => hasDerivAt_const _ _
  tA := fun _ _ _ => hasDerivAt_const _ _
  tQd := fun _ _ _ _ => hasDerivAt_const _ _
  tVd := fun _ _ _ _ => hasDerivAt_const _ _
  tQdd := fun _ _ _ _ _ => hasDerivAt_const _ _
  xQ := fun _ _ _ _ => hasDerivAt_const _ _
  xV := fun _ _ _ _ => hasDerivAt_const _ _
  xA := fun _ _ _ _ => hasDerivAt_const _ _
  xQd := fun _ _ _ _ _ => hasDerivAt_const _ _
  xVd := fun _ _ _ _ _ => hasDerivAt_const _ _
  xQdd := fun _ _ _ _ _ _ => hasDerivAt_const _ _
  nondeg := fun _ _ _ => by
    have h := congrArg Matrix.det minkowski_mul_self
    rw [Matrix.det_mul, Matrix.det_one] at h
    simp only [flatField, add_zero]
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  cTs := continuousOn_const
  cdTs := fun _ => continuousOn_const
  cr := continuousOn_const
  cdr := fun _ => continuousOn_const
  tTs := fun _ _ _ _ _ => hasDerivAt_const _ _
  xTs := fun _ _ _ _ _ _ => hasDerivAt_const _ _
  tr := fun _ _ _ _ _ => hasDerivAt_const _ _
  xr := fun _ _ _ _ _ _ => hasDerivAt_const _ _
  reduced := fun t _ x => by rw [flat_jetAt', J0_resM]; simp

theorem flat_coeffs (T : ℝ) : WaveCoeffs flatField T 1 1 0 (fun _ => 0) where
  coer_a := fun t _ x => by rw [flat_jetAt']; simp [minkowski]
  coer_γ := fun t _ x ξ => by
    rw [flat_jetAt']
    simp only [Matrix.of_apply, HarmonicGaugePropagation.minkowski_succ_succ, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [sq]
  bnd_dG := fun t _ x e μ ν => by rw [flat_jetAt', J0_dG]; simp
  cont_m := continuous_const
  m_nonneg := fun _ => le_rfl
  pot := fun t _ x b c dc => by rw [flat_jetAt', J0_lowerOp]; simp

/-- Non-vacuity of `constraint_bound` (flat metric, zero sources, unit coefficients). -/
example (T : ℝ) := constraint_bound (flat_sourced T) (flat_coeffs T) one_pos one_pos (A₁ := 1)
  (fun x => by rw [flat_jetAt']; simp [minkowski])
  (fun i j x => by
    rw [flat_jetAt']
    simp only [Matrix.of_apply, HarmonicGaugePropagation.minkowski_succ_succ]
    split_ifs <;> simp)


end

end RenewalGeometry.SubsidiaryConstraint
