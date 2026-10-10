/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedConstraintReduction

/-!
# Slab-local smooth field tuples

Generic infrastructure for `lem:generated-physical-identification` (Einstein–Standard-Model
action-closure manuscript, `app:generated-dynamics`): the actual-jet chain
(`ActualJetBridge.Tuple`, `ActualJetState.writer_pde`, `GenConstraint`, `GenGauss`,
`GenHarmonic`) is stated for global `C^∞` tuples on `ℝ × 𝕋³`, while solutions of the symmetric
system live on slabs `(a, b) × 𝕋³`.  A slab-local smooth tuple is turned into a global one by a
**smooth reparametrisation of time** which is the identity on a smaller slab; on that slab the
global tuple agrees with the local fields on a neighbourhood of every point, hence has the same
actual jets, the same actual-jet state, residuals and harmonic defect.

* `exists_time_reparam` — for `a < c < d < b` a smooth `φ : ℝ → (a, b)` with `φ = id` on `(c, d)`
  (a `ContDiffBump` interpolation between `t` and the midpoint);
* `reparam`, `contDiff_reparam`, `reparam_mem`, `reparam_eventuallyEq` — the space-time map
  `(t, y) ↦ (φ(t), y)`;
* `LocalTuple` — metric, gauge potential, Higgs field and spinors, `C^∞` on `(a, b) × ℝ³`,
  spatially periodic, with the metric symmetric and in the Lorentzian chart and `A_0 = 0` on the
  slab;
* **`LocalTuple.ext`** — the global tuple `z ∘ (φ × id)`; **`ext_eventuallyEq`**: on `(c, d) × ℝ³`
  each field of the extension coincides with the local field near every point;
  **`jet_eq_of_eventuallyEq`**: tuples whose fields agree near `x` have the same actual jet at
  `x` — so every pointwise statement of the chain (state, writer identity, residuals, harmonic
  defect, the symmetric system) at points of the smaller slab is a statement about the local
  fields, independent of the reparametrisation (`stateF_ext_eq`, `bosF_ext_eq`, `dirF_ext_eq`,
  `CF_ext_eq`).
-/

open Filter Topology Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.SlabLocal

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation
  TwistedHalfRicci ActualJetBridge ActualJetState GenConstraint

set_option linter.unusedSectionVars false

/-! ### Smooth reparametrisation of time -/

/-- **A smooth time cut-off**: for `a < c < d < b` there is a smooth `φ : ℝ → (a, b)` with
`φ(t) = t` on `(c, d)`. -/
theorem exists_time_reparam {a c d b : ℝ} (hac : a < c) (hcd : c < d) (hdb : d < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ t, φ t ∈ Ioo a b) ∧ ∀ t ∈ Ioo c d, φ t = t := by
  set m := (c + d) / 2 with hm
  set rIn := (d - c) / 2 with hrIn
  set rOut := min (m - a) (b - m) with hrOut
  have hrIn0 : 0 < rIn := by rw [hrIn]; linarith
  have hlt : rIn < rOut := by rw [hrOut, hrIn, hm]; exact lt_min (by linarith) (by linarith)
  let χ : ContDiffBump m := ⟨rIn, rOut, hrIn0, hlt⟩
  refine ⟨fun t => χ t * t + (1 - χ t) * m, ?_, fun t => ?_, fun t ht => ?_⟩
  · exact (χ.contDiff.mul contDiff_id).add ((contDiff_const.sub χ.contDiff).mul contDiff_const)
  · have e : χ t * t + (1 - χ t) * m - m = χ t * (t - m) := by ring
    have hma : rOut ≤ m - a := min_le_left _ _
    have hmb : rOut ≤ b - m := min_le_right _ _
    by_cases hd : dist t m < rOut
    · have h1 : |χ t * t + (1 - χ t) * m - m| < rOut := by
        rw [e, abs_mul, abs_of_nonneg χ.nonneg]
        calc χ t * |t - m| ≤ 1 * |t - m| :=
              mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
          _ = dist t m := by rw [one_mul, Real.dist_eq]
          _ < rOut := hd
      rw [abs_lt] at h1
      exact ⟨by linarith, by linarith⟩
    · have h0 : χ t = 0 := χ.zero_of_le_dist (not_lt.1 hd)
      simp only [h0, zero_mul, sub_zero, one_mul, zero_add]
      exact ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  · have h1 : χ t = 1 := by
      refine χ.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      show -rIn ≤ t - m ∧ t - m ≤ rIn
      rw [hrIn, hm]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp [h1]

/-- The space-time map `(t, y) ↦ (φ(t), y)`. -/
def reparam (φ : ℝ → ℝ) (x : ST 3) : ST 3 := Fin.cons (φ (x 0)) (Fin.tail x)

theorem contDiff_reparam {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (reparam φ) := by
  refine contDiff_pi.2 fun μ => ?_
  induction μ using Fin.cases with
  | zero =>
    show ContDiff ℝ ∞ fun x : ST 3 => φ (x 0)
    exact hφ.comp (contDiff_apply ℝ ℝ 0)
  | succ j =>
    show ContDiff ℝ ∞ fun x : ST 3 => x j.succ
    exact contDiff_apply ℝ ℝ j.succ

theorem reparam_mem {φ : ℝ → ℝ} {a b : ℝ} (hφ : ∀ t, φ t ∈ Ioo a b) (x : ST 3) :
    reparam φ x ∈ openSlab a b := hφ (x 0)

theorem reparam_shift (φ : ℝ → ℝ) (k : Fin 3 → ℤ) (x : ST 3) :
    reparam φ (x + sshift k) = reparam φ x + sshift k := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [reparam, sshift]
  | succ j => simp [reparam, sshift, Fin.tail]

theorem reparam_eventuallyEq {φ : ℝ → ℝ} {c d : ℝ} (hφ : ∀ t ∈ Ioo c d, φ t = t) {x : ST 3}
    (hx : x ∈ openSlab c d) : reparam φ =ᶠ[𝓝 x] id := by
  filter_upwards [(isOpen_openSlab c d).mem_nhds hx] with y hy
  funext μ
  induction μ using Fin.cases with
  | zero => simp [reparam, hφ _ hy]
  | succ j => simp [reparam, Fin.tail]

/-! ### Slab-local tuples -/

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- **A slab-local smooth field tuple** on `(a, b) × 𝕋³`: the fields of `ActualJetBridge.Tuple`,
smooth on the open slab, with the pointwise conditions (symmetric metric in the Lorentzian chart,
exact temporal gauge) on the slab. -/
structure LocalTuple (a b : ℝ) where
  g : ST 3 → Fin 4 → Fin 4 → ℝ
  A : ST 3 → Fin 4 → MatLie m
  H : ST 3 → V
  ψ : ST 3 → S
  ψb : ST 3 → S'
  g_smooth : ContDiffOn ℝ ∞ g (openSlab a b)
  A_smooth : ContDiffOn ℝ ∞ A (openSlab a b)
  H_smooth : ContDiffOn ℝ ∞ H (openSlab a b)
  ψ_smooth : ContDiffOn ℝ ∞ ψ (openSlab a b)
  ψb_smooth : ContDiffOn ℝ ∞ ψb (openSlab a b)
  g_per : IsSPeriodic g
  A_per : IsSPeriodic A
  H_per : IsSPeriodic H
  ψ_per : IsSPeriodic ψ
  ψb_per : IsSPeriodic ψb
  g_symm : ∀ x ∈ openSlab a b, ∀ μ ν, g x μ ν = g x ν μ
  temporal : ∀ x ∈ openSlab a b, A x 0 = 0
  det_ne : ∀ x ∈ openSlab a b, (Matrix.of (g x)).det ≠ 0
  lor : ∀ x ∈ openSlab a b, IsLorChart (ginvOf (g x))

namespace LocalTuple

variable {a b : ℝ} (L : LocalTuple m V S S' a b) {φ : ℝ → ℝ}

theorem comp_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : ContDiffOn ℝ ∞ f (openSlab a b)) (hφ : ContDiff ℝ ∞ φ) (hφr : ∀ t, φ t ∈ Ioo a b) :
    ContDiff ℝ ∞ (fun x => f (reparam φ x)) :=
  hf.comp_contDiff (contDiff_reparam hφ) (reparam_mem hφr)

theorem comp_per {E : Type*} {f : ST 3 → E} (hf : IsSPeriodic f) :
    IsSPeriodic (fun x => f (reparam φ x)) := fun k x => by
  simp only [reparam_shift, hf k]

/-- **The global extension** `z ∘ (φ × id)` of a slab-local tuple (a `Tuple` on all of
`ℝ × 𝕋³`). -/
def ext (hφ : ContDiff ℝ ∞ φ) (hφr : ∀ t, φ t ∈ Ioo a b) : Tuple m V S S' where
  g x := L.g (reparam φ x)
  A x := L.A (reparam φ x)
  H x := L.H (reparam φ x)
  ψ x := L.ψ (reparam φ x)
  ψb x := L.ψb (reparam φ x)
  g_smooth := comp_smooth L.g_smooth hφ hφr
  A_smooth := comp_smooth L.A_smooth hφ hφr
  H_smooth := comp_smooth L.H_smooth hφ hφr
  ψ_smooth := comp_smooth L.ψ_smooth hφ hφr
  ψb_smooth := comp_smooth L.ψb_smooth hφ hφr
  g_per := comp_per L.g_per
  A_per := comp_per L.A_per
  H_per := comp_per L.H_per
  ψ_per := comp_per L.ψ_per
  ψb_per := comp_per L.ψb_per
  g_symm x := L.g_symm _ (reparam_mem hφr x)
  temporal x := L.temporal _ (reparam_mem hφr x)
  det_ne x := L.det_ne _ (reparam_mem hφr x)
  lor x := L.lor _ (reparam_mem hφr x)

variable {c d : ℝ}

/-- On the smaller slab the extension coincides with the local fields near every point. -/
theorem ext_eventuallyEq (hφ : ContDiff ℝ ∞ φ) (hφr : ∀ t, φ t ∈ Ioo a b)
    (hφid : ∀ t ∈ Ioo c d, φ t = t) {x : ST 3} (hx : x ∈ openSlab c d) :
    (L.ext hφ hφr).g =ᶠ[𝓝 x] L.g ∧ (L.ext hφ hφr).A =ᶠ[𝓝 x] L.A ∧
      (L.ext hφ hφr).H =ᶠ[𝓝 x] L.H ∧ (L.ext hφ hφr).ψ =ᶠ[𝓝 x] L.ψ ∧
      (L.ext hφ hφr).ψb =ᶠ[𝓝 x] L.ψb := by
  have h := reparam_eventuallyEq hφid hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · filter_upwards [h] with y hy
    show _ = _
    simp only [ext, hy, id]

end LocalTuple

/-! ### Tuples agreeing near a point have the same actual jets -/

section JetLocality

theorem pd_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ST 3 → E}
    {x : ST 3} (h : f =ᶠ[𝓝 x] f') (μ : Fin 4) : pd f μ =ᶠ[𝓝 x] pd f' μ := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ f' := h.fderiv
  filter_upwards [h1] with y hy
  unfold SobolevOpen.pd
  rw [hy]

theorem apply_eventuallyEq {ι E : Type*} {f f' : ST 3 → ι → E} {x : ST 3}
    (h : f =ᶠ[𝓝 x] f') (i : ι) : (fun y => f y i) =ᶠ[𝓝 x] fun y => f' y i := by
  filter_upwards [h] with y hy
  rw [hy]

/-- **Locality of the actual jet**: two tuples whose fields agree near `x` have the same actual
jet at `x` (all derivatives up to the orders used by the chain coincide). -/
theorem jet_eq_of_eventuallyEq {z z' : Tuple m V S S'} {x : ST 3} (hg : z.g =ᶠ[𝓝 x] z'.g)
    (hA : z.A =ᶠ[𝓝 x] z'.A) (hH : z.H =ᶠ[𝓝 x] z'.H) (hψ : z.ψ =ᶠ[𝓝 x] z'.ψ)
    (hψb : z.ψb =ᶠ[𝓝 x] z'.ψb) : z.jet x = z'.jet x := by
  have hgx : z.g x = z'.g x := hg.eq_of_nhds
  have hdg : ∀ α, pd z.g α =ᶠ[𝓝 x] pd z'.g α := fun α => pd_eventuallyEq hg α
  have hddg : ∀ β α, pd (pd z.g α) β x = pd (pd z'.g α) β x := fun β α =>
    (pd_eventuallyEq (hdg α) β).eq_of_nhds
  -- the frame-jet fields
  have hgi_ev : (fun y => z.gi y) =ᶠ[𝓝 x] fun y => z'.gi y := by
    filter_upwards [hg] with y hy
    simp only [Tuple.gi, hy]
  have hdg_ev : (fun y => z.dg y) =ᶠ[𝓝 x] fun y => z'.dg y := by
    filter_upwards [(hdg 0), (hdg 1), (hdg 2), (hdg 3)] with y h0 h1 h2 h3
    funext α
    fin_cases α
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hde_ev : (fun y => z.de y) =ᶠ[𝓝 x] fun y => z'.de y := by
    filter_upwards [hgi_ev, hdg_ev] with y h1 h2
    show z.de y = z'.de y
    unfold Tuple.de
    rw [h1, h2]
  have hdde : ∀ δ γ A μ, z.dde x δ γ A μ = z'.dde x δ γ A μ := by
    intro δ γ A μ
    exact (pd_eventuallyEq (apply_eventuallyEq (apply_eventuallyEq (apply_eventuallyEq
      hde_ev γ) A) μ) δ).eq_of_nhds
  have hFJ : z.FJ x = z'.FJ x := by
    have h1 : z.gi x = z'.gi x := hgi_ev.eq_of_nhds
    have h2 : z.dg x = z'.dg x := hdg_ev.eq_of_nhds
    have h3 : z.ddg x = z'.ddg x := by funext β α; exact hddg β α
    have h4 : z.e x = z'.e x := by
      show (fun A μ => frU (z.gi x) A μ) = fun A μ => frU (z'.gi x) A μ
      rw [h1]
    have h5 : z.de x = z'.de x := hde_ev.eq_of_nhds
    have h6 : z.dde x = z'.dde x := by funext δ γ A μ; exact hdde δ γ A μ
    unfold Tuple.FJ
    congr 1
  have hAx : z.A x = z'.A x := hA.eq_of_nhds
  have hdA : ∀ γ, pd z.A γ x = pd z'.A γ x := fun γ => (pd_eventuallyEq hA γ).eq_of_nhds
  have hddA : ∀ δ γ, pd (pd z.A γ) δ x = pd (pd z'.A γ) δ x := fun δ γ =>
    (pd_eventuallyEq (pd_eventuallyEq hA γ) δ).eq_of_nhds
  have hHx : z.H x = z'.H x := hH.eq_of_nhds
  have hdH : ∀ γ, pd z.H γ x = pd z'.H γ x := fun γ => (pd_eventuallyEq hH γ).eq_of_nhds
  have hddH : ∀ δ γ, pd (pd z.H γ) δ x = pd (pd z'.H γ) δ x := fun δ γ =>
    (pd_eventuallyEq (pd_eventuallyEq hH γ) δ).eq_of_nhds
  have hψx : z.ψ x = z'.ψ x := hψ.eq_of_nhds
  have hdψ : ∀ γ, pd z.ψ γ x = pd z'.ψ γ x := fun γ => (pd_eventuallyEq hψ γ).eq_of_nhds
  have hddψ : ∀ δ γ, pd (pd z.ψ γ) δ x = pd (pd z'.ψ γ) δ x := fun δ γ =>
    (pd_eventuallyEq (pd_eventuallyEq hψ γ) δ).eq_of_nhds
  have hψbx : z.ψb x = z'.ψb x := hψb.eq_of_nhds
  have hdψb : ∀ γ, pd z.ψb γ x = pd z'.ψb γ x := fun γ => (pd_eventuallyEq hψb γ).eq_of_nhds
  have hddψb : ∀ δ γ, pd (pd z.ψb γ) δ x = pd (pd z'.ψb γ) δ x := fun δ γ =>
    (pd_eventuallyEq (pd_eventuallyEq hψb γ) δ).eq_of_nhds
  unfold Tuple.jet
  congr 1
  · funext γ μ; rw [hdA γ]
  · funext δ γ μ; rw [hddA δ γ]
  · funext γ; rw [hdH γ]
  · funext δ γ; rw [hddH δ γ]
  · funext γ; rw [hdψ γ]
  · funext δ γ; rw [hddψ δ γ]
  · funext γ; rw [hdψb γ]
  · funext δ γ; rw [hddψb δ γ]

end JetLocality

/-! ### The chain on slab-local tuples -/

section Chain

variable (SM : SMData (MatLie m) V S S')

/-- The actual-jet state of tuples agreeing near `x` coincides at `x`. -/
theorem stateF_eq_of_jet {z z' : Tuple m V S S'} {x : ST 3} (h : z.jet x = z'.jet x) :
    stateF SM z x = stateF SM z' x := by
  unfold stateF
  rw [h]

theorem bosF_eq_of_jet {z z' : Tuple m V S S'} {x : ST 3} (h : z.jet x = z'.jet x) :
    bosF SM z x = bosF SM z' x := by
  unfold bosF
  rw [h]

theorem dirF_eq_of_jet {z z' : Tuple m V S S'} {x : ST 3} (h : z.jet x = z'.jet x) :
    dirF SM z x = dirF SM z' x := by
  unfold dirF
  rw [h]

variable {a b c d : ℝ} (L : LocalTuple m V S S' a b) {φ φ' : ℝ → ℝ}

/-- **Independence of the reparametrisation**: on `(c, d) × 𝕋³` any two extensions of a slab-local
tuple have the same actual jets; hence the actual-jet state, residuals and harmonic defect of the
extension are those of the local fields. -/
theorem jet_ext_eq (hφ : ContDiff ℝ ∞ φ) (hφr : ∀ t, φ t ∈ Ioo a b)
    (hφid : ∀ t ∈ Ioo c d, φ t = t) (hφ' : ContDiff ℝ ∞ φ') (hφr' : ∀ t, φ' t ∈ Ioo a b)
    (hφid' : ∀ t ∈ Ioo c d, φ' t = t) {x : ST 3} (hx : x ∈ openSlab c d) :
    (L.ext hφ hφr).jet x = (L.ext hφ' hφr').jet x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := L.ext_eventuallyEq hφ hφr hφid hx
  obtain ⟨h1', h2', h3', h4', h5'⟩ := L.ext_eventuallyEq hφ' hφr' hφid' hx
  exact jet_eq_of_eventuallyEq (h1.trans h1'.symm) (h2.trans h2'.symm) (h3.trans h3'.symm)
    (h4.trans h4'.symm) (h5.trans h5'.symm)

/-- Every slab-local tuple has a global extension agreeing with it near every point of a given
smaller slab. -/
theorem exists_ext {c d : ℝ} (hac : a < c) (hcd : c < d) (hdb : d < b) :
    ∃ z : Tuple m V S S', ∀ x ∈ openSlab c d, z.g =ᶠ[𝓝 x] L.g ∧ z.A =ᶠ[𝓝 x] L.A ∧
      z.H =ᶠ[𝓝 x] L.H ∧ z.ψ =ᶠ[𝓝 x] L.ψ ∧ z.ψb =ᶠ[𝓝 x] L.ψb := by
  obtain ⟨φ, hφ, hφr, hφid⟩ := exists_time_reparam hac hcd hdb
  exact ⟨L.ext hφ hφr, fun x hx => L.ext_eventuallyEq hφ hφr hφid hx⟩

end Chain

end RenewalGeometry.SlabLocal
