/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedFirstOrderAction

/-!
# The first variation of `S^{(1)}` on a slab cell

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("At the generated
record, integration by parts expresses `D S^{cmp}_{N,τ}` through the physical rows"), on one time
cell `[a, b] × 𝕋³`:

* `sint_add_on`, `sint_sub_on`, `sint_sum_on`, `intervalIntegrable_sint_on` — slice integrals of
  fields continuous near the cell;
* **`cell_grav`** — `∫_{cell} DL1EH[k] = ∫_{cell}(-√(-det g) G^{μν}k_{μν}) + [∫ (W^0 - δw^0)]_a^b`:
  the first-derivative Einstein–Hilbert density has the Einstein row and a first-jet boundary
  flux (`GenFOGrav.volScal_eq_L1EH_add_div`, `GenFOGrav.eh_field_variation`).
-/

namespace RenewalGeometry

namespace GenCellVar

open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon
  ActualJetSmooth ActualJetGauge SlabWaveHk ActualJetWriter ActualJetBridge ActualJetState
  GenMatVar GenNoether PeriodicCube GenFOGrav GenMatEuler GenFOAction GenCell KatoGalerkin
  SymHypEnergy
open SobolevOpen (pd)
open MeasureTheory Set
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Slice integrals of fields continuous near a slice -/

section SliceOn

variable {d : ℕ}

theorem integrableOn_slice_on {f : ST d → ℝ} {a' b' t : ℝ} (hf : ContinuousOn f (openSlab a' b'))
    (ht : t ∈ Ioo a' b') :
    IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y)) (Icc 0 1) :=
  integrableOn_cube_of_continuousOn (hf.comp (continuous_cons t).continuousOn
    fun y _ => cons_mem_openSlab ht y)

theorem sint_add_on {f g : ST d → ℝ} {a' b' t : ℝ} (hf : ContinuousOn f (openSlab a' b'))
    (hg : ContinuousOn g (openSlab a' b')) (ht : t ∈ Ioo a' b') :
    sint (fun x => f x + g x) t = sint f t + sint g t := by
  unfold sint
  exact integral_add (integrableOn_slice_on hf ht) (integrableOn_slice_on hg ht)

theorem sint_sub_on {f g : ST d → ℝ} {a' b' t : ℝ} (hf : ContinuousOn f (openSlab a' b'))
    (hg : ContinuousOn g (openSlab a' b')) (ht : t ∈ Ioo a' b') :
    sint (fun x => f x - g x) t = sint f t - sint g t := by
  unfold sint
  exact integral_sub (integrableOn_slice_on hf ht) (integrableOn_slice_on hg ht)

theorem sint_sum_on {ι : Type*} (s : Finset ι) {f : ι → ST d → ℝ} {a' b' t : ℝ}
    (hf : ∀ i, ContinuousOn (f i) (openSlab a' b')) (ht : t ∈ Ioo a' b') :
    sint (fun x => ∑ i ∈ s, f i x) t = ∑ i ∈ s, sint (f i) t := by
  unfold sint
  exact integral_finset_sum s fun i _ => integrableOn_slice_on (hf i) ht

theorem intervalIntegrable_sint_on {f : ST d → ℝ} {a' a b b' : ℝ}
    (hf : ContinuousOn f (openSlab a' b')) (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    IntervalIntegrable (sint f) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine continuousOn_sint_of hab (hf.mono ?_)
  rintro _ ⟨q, ⟨h1, -⟩, rfl⟩
  exact cons_mem_openSlab ⟨ha.trans_le h1.1, h1.2.trans_lt hb⟩ q.2

/-- Cell integrals of a difference of fields continuous near the cell. -/
theorem cellInt_sub_on {f g : ST d → ℝ} {a' a b b' : ℝ} (hf : ContinuousOn f (openSlab a' b'))
    (hg : ContinuousOn g (openSlab a' b')) (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    cellInt a b (fun x => f x - g x) = cellInt a b f - cellInt a b g := by
  unfold cellInt
  rw [← intervalIntegral.integral_sub (intervalIntegrable_sint_on hf ha hab hb)
    (intervalIntegrable_sint_on hg ha hab hb)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  exact sint_sub_on hf hg ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

theorem cellInt_add_on {f g : ST d → ℝ} {a' a b b' : ℝ} (hf : ContinuousOn f (openSlab a' b'))
    (hg : ContinuousOn g (openSlab a' b')) (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    cellInt a b (fun x => f x + g x) = cellInt a b f + cellInt a b g := by
  unfold cellInt
  rw [← intervalIntegral.integral_add (intervalIntegrable_sint_on hf ha hab hb)
    (intervalIntegrable_sint_on hg ha hab hb)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  exact sint_add_on hf hg ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

theorem cellInt_sum_on {ι : Type*} (s : Finset ι) {f : ι → ST d → ℝ} {a' a b b' : ℝ}
    (hf : ∀ i, ContinuousOn (f i) (openSlab a' b')) (ha : a' < a) (hab : a ≤ b) (hb : b < b') :
    cellInt a b (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cellInt a b (f i) := by
  unfold cellInt
  rw [← intervalIntegral.integral_finset_sum fun i _ => intervalIntegrable_sint_on (hf i) ha hab hb]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  exact sint_sum_on s hf ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

end SliceOn

/-! ### Jet functionals of the gravitational sector -/

section GravJets

/-- The second-derivative Einstein–Hilbert density `√(-det g) R` on metric 2-jets. -/
def vR2 (p : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met)) : ℝ :=
  volM p.1 * scal (ginvOf p.1) p.2.1 p.2.2

/-- The divergence flux `√(-det g) w^λ` on metric 1-jets. -/
def WJ (lam : Fin 4) (p : Met × (Fin 4 → Met)) : ℝ :=
  volM p.1 * fluxV (ginvOf p.1) (chr (ginvOf p.1) p.2) lam

/-- The Palatini flux `√(-det g)(g^{μν}δΓ^λ_{μν} - g^{λμ}δΓ^ν_{μν})` on pairs of metric 1-jets. -/
def PFJ (lam : Fin 4) (p q : Met × (Fin 4 → Met)) : ℝ :=
  volM p.1 * fluxV (ginvOf p.1) (chrVar (ginvOf p.1) p.2 q.1 q.2) lam

section CDHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

theorem cd_dchr {gi : E → Met} {dg : E → Fin 4 → Met} {ddg : E → Fin 4 → Fin 4 → Met}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dg y α a b) x)
    (hddg : ∀ β α a b, ContDiffAt ℝ ∞ (fun y => ddg y β α a b) x) (α l μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => dchr (gi y) (dg y) (ddg y) α l μ ν) x := by
  have h1 := cd_dginv hgi hdg
  unfold dchr dchr1 dchr2; fun_prop

theorem cd_ricciJ {Γ : E → Fin 4 → Fin 4 → Fin 4 → ℝ} {D : E → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hΓ : ∀ l a b, ContDiffAt ℝ ∞ (fun y => Γ y l a b) x)
    (hD : ∀ α l a b, ContDiffAt ℝ ∞ (fun y => D y α l a b) x) (μ ν : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => ricciJ (Γ y) (D y) μ ν) x := by
  unfold ricciJ; fun_prop

theorem cd_trG {gi X : E → Met} (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hX : ∀ a b, ContDiffAt ℝ ∞ (fun y => X y a b) x) :
    ContDiffAt ℝ ∞ (fun y => trG (gi y) (X y)) x := by
  unfold trG; fun_prop

theorem cd_fluxV {gi : E → Met} {X : E → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hX : ∀ l a b, ContDiffAt ℝ ∞ (fun y => X y l a b) x) (lam : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => fluxV (gi y) (X y) lam) x := by
  unfold fluxV; fun_prop

theorem cd_ginvVar {gi k : E → Met} (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hk : ∀ a b, ContDiffAt ℝ ∞ (fun y => k y a b) x) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => ginvVar (gi y) (k y) a b) x := by
  unfold ginvVar; fun_prop

theorem cd_chrVar {gi k : E → Met} {dg dk : E → Fin 4 → Met}
    (hgi : ∀ a b, ContDiffAt ℝ ∞ (fun y => gi y a b) x)
    (hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dg y α a b) x)
    (hk : ∀ a b, ContDiffAt ℝ ∞ (fun y => k y a b) x)
    (hdk : ∀ α a b, ContDiffAt ℝ ∞ (fun y => dk y α a b) x) (l a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => chrVar (gi y) (dg y) (k y) (dk y) l a b) x := by
  unfold chrVar
  exact (cd_chr (cd_ginvVar hgi hk) hdg l a b).add (cd_chr hgi hdk l a b)

end CDHelpers

theorem contDiffOn_vR2 : ContDiffOn ℝ ∞ vR2 {p | (Matrix.of p.1).det < 0} := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hp' : (Matrix.of p.1).det < 0 := hp
  have hg : ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) => q.1) p :=
    contDiffAt_fst
  have hv := contDiffAt_volM hg hp'
  have hgi0 := ContDiffAt.ginvOf_fun hg hp'.ne
  have hgi : ∀ a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) =>
      ginvOf q.1 a b) p := fun a b => contDiffAt_pi.1 (contDiffAt_pi.1 hgi0 a) b
  have hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) =>
      q.2.1 α a b) p := fun α a b => by fun_prop
  have hddg : ∀ β α a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) =>
      q.2.2 β α a b) p := fun β α a b => by fun_prop
  have hR : ∀ a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) =>
      ricci (ginvOf q.1) q.2.1 q.2.2 a b) p := fun a b =>
    cd_ricciJ (cd_chr hgi hdg) (cd_dchr hgi hdg hddg) a b
  have hS := cd_trG hgi hR
  unfold vR2 scal
  exact hv.mul hS

theorem contDiffOn_WJ (lam : Fin 4) :
    ContDiffOn ℝ ∞ (WJ lam) {p | (Matrix.of p.1).det < 0} := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hp' : (Matrix.of p.1).det < 0 := hp
  have hg : ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) => q.1) p := contDiffAt_fst
  have hv := contDiffAt_volM hg hp'
  have hgi0 := ContDiffAt.ginvOf_fun hg hp'.ne
  have hgi : ∀ a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) => ginvOf q.1 a b) p :=
    fun a b => contDiffAt_pi.1 (contDiffAt_pi.1 hgi0 a) b
  have hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun q : Met × (Fin 4 → Met) => q.2 α a b) p :=
    fun α a b => by fun_prop
  have hW := cd_fluxV hgi (cd_chr hgi hdg) lam
  unfold WJ
  exact hv.mul hW

theorem contDiffOn_PFJ (lam : Fin 4) :
    ContDiffOn ℝ ∞ (fun pq : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) => PFJ lam pq.1 pq.2)
      {pq | (Matrix.of pq.1.1).det < 0} := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hp' : (Matrix.of p.1.1).det < 0 := hp
  have hg : ContDiffAt ℝ ∞ (fun q : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) => q.1.1) p := by
    fun_prop
  have hv := contDiffAt_volM hg hp'
  have hgi0 := ContDiffAt.ginvOf_fun hg hp'.ne
  have hgi : ∀ a b, ContDiffAt ℝ ∞ (fun q : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) =>
      ginvOf q.1.1 a b) p := fun a b => contDiffAt_pi.1 (contDiffAt_pi.1 hgi0 a) b
  have hdg : ∀ α a b, ContDiffAt ℝ ∞ (fun q : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) =>
      q.1.2 α a b) p := fun α a b => by fun_prop
  have hk : ∀ a b, ContDiffAt ℝ ∞ (fun q : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) =>
      q.2.1 a b) p := fun a b => by fun_prop
  have hdk : ∀ α a b, ContDiffAt ℝ ∞ (fun q : (Met × (Fin 4 → Met)) × (Met × (Fin 4 → Met)) =>
      q.2.2 α a b) p := fun α a b => by fun_prop
  have hW := cd_fluxV hgi (cd_chrVar hgi hdg hk hdk) lam
  unfold PFJ
  exact hv.mul hW

theorem isOpen_det_neg {E : Type*} [TopologicalSpace E] {π : E → Met} (hπ : Continuous π) :
    IsOpen {p : E | (Matrix.of (π p)).det < 0} := by
  have hdet : Continuous fun p : E => (Matrix.of (π p)).det :=
    Continuous.matrix_det (A := fun p : E => Matrix.of (π p)) hπ
  exact isOpen_lt hdet continuous_const

end GravJets

/-! ### Margins near a closed slab -/

section Margin

/-- **Uniform margin**: if a continuous periodic field takes values in an open set on the closed
slab `[a, b] × 𝕋³`, then so does every small line perturbation on a slightly larger slab. -/
theorem exists_line_margin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j v : ST 3 → E} (hj : Continuous j) (hv : Continuous v) (hjp : IsSPeriodic j)
    (hvp : IsSPeriodic v) {U : Set E} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    (hK : ∀ x : ST 3, x 0 ∈ Icc a b → j x ∈ U) :
    ∃ r > 0, ∀ ε ∈ Icc (-r) r, ∀ x : ST 3, x 0 ∈ Icc (a - r) (b + r) → j x + ε • v x ∈ U := by
  set N : Set (ℝ × ST 3) := {p | j p.2 + p.1 • v p.2 ∈ U} with hN
  have hNo : IsOpen N :=
    hU.preimage ((hj.comp continuous_snd).add (continuous_fst.smul (hv.comp continuous_snd)))
  set Kc : Set (ℝ × ST 3) := (fun q : ℝ × (Fin 3 → ℝ) => ((0 : ℝ), (Fin.cons q.1 q.2 : ST 3))) ''
    (Icc a b ×ˢ Icc 0 1) with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_Icc.prod isCompact_Icc).image (continuous_const.prodMk continuous_cons2)
  have hKN : Kc ⊆ N := by
    rintro _ ⟨q, ⟨hq1, -⟩, rfl⟩
    show j _ + (0 : ℝ) • v _ ∈ U
    rw [zero_smul, add_zero]
    exact hK _ (by simpa using hq1)
  obtain ⟨δ, hδ, hsub⟩ := hKcc.exists_thickening_subset_open hNo hKN
  refine ⟨δ / 2, by positivity, fun ε hε x hx => ?_⟩
  set t := x 0 with ht
  set y' : Fin 3 → ℝ := fun i => Int.fract (Fin.tail x i) with hy'
  set c := max a (min t b) with hc
  have hcI : c ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have htc1 : t - c ≤ δ / 2 := by
    have h2 : min t b ≤ c := le_max_right _ _
    rcases min_choice t b with h | h <;> rw [h] at h2 <;> linarith [hx.2]
  have htc2 : c - t ≤ δ / 2 := by
    have h1 : c ≤ max a t := max_le_max le_rfl (min_le_left _ _)
    rcases max_choice a t with h | h <;> rw [h] at h1 <;> linarith [hx.1]
  have hy'I : y' ∈ Icc (0 : Fin 3 → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have hmem : ((0 : ℝ), (Fin.cons c y' : ST 3)) ∈ Kc := ⟨(c, y'), ⟨hcI, hy'I⟩, rfl⟩
  have hdist : dist (ε, (Fin.cons t y' : ST 3)) ((0 : ℝ), (Fin.cons c y' : ST 3)) < δ := by
    rw [Prod.dist_eq]
    have h1 : dist ε 0 ≤ δ / 2 := by
      rw [Real.dist_eq, sub_zero, abs_le]; exact ⟨hε.1, hε.2⟩
    have h2 : dist (Fin.cons t y' : ST 3) (Fin.cons c y') ≤ δ / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero, Real.dist_eq, abs_le]; constructor <;> linarith
      | succ i => simp only [Fin.cons_succ, dist_self]; positivity
    have : max (dist ε 0) (dist (Fin.cons t y' : ST 3) (Fin.cons c y')) ≤ δ / 2 := max_le h1 h2
    linarith
  have hin : (ε, (Fin.cons t y' : ST 3)) ∈ N :=
    hsub (Metric.mem_thickening_iff.2 ⟨_, hmem, hdist⟩)
  have hper : IsSPeriodic (fun x : ST 3 => j x + ε • v x) := fun k x => by
    simp only [hjp k x, hvp k x]
  have hfr := (hper.slice t).apply_fract (Fin.tail x)
  have hx' : (Fin.cons t (Fin.tail x) : ST 3) = x := Fin.cons_self_tail x
  have e : j x + ε • v x = j (Fin.cons t y') + ε • v (Fin.cons t y') := by
    rw [hy']
    rw [hfr, hx']
  rw [e]
  exact hin

end Margin

/-! ### The gravitational cell variation -/

section CellGrav

/-- The metric 1-jet field `(g, ∂g)`. -/
def j1M (g : ST 3 → Met) (x : ST 3) : Met × (Fin 4 → Met) := (g x, dF g x)

/-- The metric 2-jet field `(g, ∂g, ∂∂g)`. -/
def j2M (g : ST 3 → Met) (x : ST 3) : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) :=
  (g x, dF g x, ddF g x)

variable {g k : ST 3 → Met}

theorem contDiff_dF (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dF g) :=
  contDiff_pi.2 fun α => EHFieldVariation.contDiff_pd' hg α

theorem contDiff_ddF (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ddF g) :=
  contDiff_pi.2 fun β => contDiff_pi.2 fun α =>
    EHFieldVariation.contDiff_pd' (EHFieldVariation.contDiff_pd' hg α) β

theorem contDiff_j1M (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (j1M g) :=
  hg.prodMk (contDiff_dF hg)

theorem contDiff_j2M (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (j2M g) :=
  hg.prodMk ((contDiff_dF hg).prodMk (contDiff_ddF hg))

theorem isSPeriodic_dF (hgp : IsSPeriodic g) : IsSPeriodic (dF g) := fun k x => by
  funext α
  exact isSPeriodic_pd' hgp α k x

theorem isSPeriodic_j1M (hgp : IsSPeriodic g) : IsSPeriodic (j1M g) := fun k x => by
  simp only [j1M, hgp k x, isSPeriodic_dF hgp k x]

theorem pd_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (ε : ℝ) (α : Fin 4) :
    pd (fun y => g y + ε • k y) α = fun y => pd g α y + ε • pd k α y := by
  funext y
  exact pd_add_smul (hg.differentiable (by simp) y) (hk.differentiable (by simp) y) ε α

theorem dF_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (ε : ℝ) (x : ST 3) :
    dF (fun y => g y + ε • k y) x = dF g x + ε • dF k x := by
  funext α μ ν
  show pd (fun y => g y + ε • k y) α x μ ν = _
  rw [pd_line hg hk ε α]
  rfl

theorem ddF_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (ε : ℝ) (x : ST 3) :
    ddF (fun y => g y + ε • k y) x = ddF g x + ε • ddF k x := by
  funext β α μ ν
  show pd (pd (fun y => g y + ε • k y) α) β x μ ν = _
  rw [pd_line hg hk ε α, pd_line (EHFieldVariation.contDiff_pd' hg α)
    (EHFieldVariation.contDiff_pd' hk α) ε β]
  rfl

theorem j1M_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (ε : ℝ) (x : ST 3) :
    j1M (fun y => g y + ε • k y) x = j1M g x + ε • j1M k x := by
  simp only [j1M, dF_line hg hk ε x, Prod.smul_mk, Prod.mk_add_mk]

theorem j2M_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k) (ε : ℝ) (x : ST 3) :
    j2M (fun y => g y + ε • k y) x = j2M g x + ε • j2M k x := by
  simp only [j2M, dF_line hg hk ε x, ddF_line hg hk ε x, Prod.smul_mk, Prod.mk_add_mk]

theorem contDiffOn_pd_of_on {f : ST 3 → ℝ} {a' b' : ℝ} (hf : ContDiffOn ℝ ∞ f (openSlab a' b'))
    (μ : Fin 4) : ContDiffOn ℝ ∞ (pd f μ) (openSlab a' b') := by
  intro x hx
  have h := (hf.contDiffAt ((isOpen_openSlab a' b').mem_nhds hx))
  unfold SobolevOpen.pd
  exact ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

theorem continuousOn_fderiv_jet {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    {L : J → ℝ} {U : Set J} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {j v : ST 3 → J}
    (hj : Continuous j) (hv : Continuous v) {s : Set (ST 3)} (hs : ∀ x ∈ s, j x ∈ U) :
    ContinuousOn (fun x => fderiv ℝ L (j x) (v x)) s :=
  ((hL.continuousOn_fderiv_of_isOpen hU (by simp)).comp hj.continuousOn hs).clm_apply
    hv.continuousOn

theorem contDiffOn_comp_jet {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    {L : J → ℝ} {U : Set J} (hL : ContDiffOn ℝ ∞ L U) {j : ST 3 → J} (hj : ContDiff ℝ ∞ j)
    {s : Set (ST 3)} (hs : ∀ x ∈ s, j x ∈ U) : ContDiffOn ℝ ∞ (fun x => L (j x)) s :=
  hL.comp hj.contDiffOn hs

end CellGrav

section CellGrav2

variable {g k : ST 3 → Met}

theorem isOpen_U1 : IsOpen {p : Met × (Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
  isOpen_det_neg continuous_fst

theorem isOpen_U2 :
    IsOpen {p : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
  isOpen_det_neg continuous_fst

theorem contDiffOn_L1EHp : ContDiffOn ℝ ∞ L1EHp {p : Met × (Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
  fun p hp => (cd_L1EH (E := Met × (Fin 4 → Met)) (x := p) (g := fun q => q.1) (dg := fun q => q.2)
    (by fun_prop) (fun α a b => by fun_prop) hp).contDiffWithinAt

/-- **The cell identity along the metric line** `g + εk`: the first-derivative density differs from
`√(-det g)R` by the time flux `W^0` at the cell ends. -/
theorem cell_L1EH_line (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k)
    (hgs : ∀ x μ ν, g x μ ν = g x ν μ) (hks : ∀ x μ ν, k x μ ν = k x ν μ)
    (hgp : IsSPeriodic g) (hkp : IsSPeriodic k) {a' a b b' ε : ℝ} (ha : a' < a) (hab : a ≤ b)
    (hb : b < b') (hdet : ∀ x ∈ openSlab a' b', (Matrix.of (g x + ε • k x)).det < 0) :
    cellInt a b (fun x => L1EHp (j1M g x + ε • j1M k x)) =
      cellInt a b (fun x => vR2 (j2M g x + ε • j2M k x)) -
        (sint (fun x => WJ 0 (j1M g x + ε • j1M k x)) b -
          sint (fun x => WJ 0 (j1M g x + ε • j1M k x)) a) := by
  set gl : ST 3 → Met := fun y => g y + ε • k y with hgl
  have hgld : ContDiff ℝ ∞ gl := hg.add (hk.const_smul ε)
  have hgls : ∀ x μ ν, gl x μ ν = gl x ν μ := fun x μ ν => by
    simp only [hgl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hgs x μ ν, hks x μ ν]
  have hglp : IsSPeriodic gl := fun k' x => by simp only [hgl, hgp k' x, hkp k' x]
  have e1 : ∀ x, j1M g x + ε • j1M k x = j1M gl x := fun x => (j1M_line hg hk ε x).symm
  have e2 : ∀ x, j2M g x + ε • j2M k x = j2M gl x := fun x => (j2M_line hg hk ε x).symm
  simp only [e1, e2]
  have hU : ∀ x ∈ openSlab a' b', j1M gl x ∈ {p : Met × (Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
    fun x hx => hdet x hx
  have hU2 : ∀ x ∈ openSlab a' b',
      j2M gl x ∈ {p : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
    fun x hx => hdet x hx
  -- smoothness of the fluxes
  have hW : ∀ lam, ContDiffOn ℝ ∞ (wfluxF gl lam) (openSlab a' b') := fun lam =>
    contDiffOn_comp_jet (contDiffOn_WJ lam) (contDiff_j1M hgld) hU
  have hWp : ∀ lam, IsSPeriodic (wfluxF gl lam) := fun lam k' x => by
    show WJ lam (j1M gl (x + sshift k')) = WJ lam (j1M gl x)
    rw [isSPeriodic_j1M hglp k' x]
  have hpt : ∀ x ∈ openSlab a' b', L1EHp (j1M gl x) =
      vR2 (j2M gl x) - ∑ lam, pd (wfluxF gl lam) lam x := fun x hx => by
    have h := volScal_eq_L1EH_add_div hgld hgls x (hdet x hx)
    show L1EH (gl x) (dF gl x) = volM (gl x) * scal (ginvOf (gl x)) (dF gl x) (ddF gl x) - _
    linarith
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) ∈ openSlab a' b' :=
    fun t ht y => cons_mem_openSlab ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩ y
  rw [cellInt_congr (g := fun x => vR2 (j2M gl x) - ∑ lam, pd (wfluxF gl lam) lam x) hab
    (fun t ht y _ => hpt _ (hsl t ht y))]
  have hc1 : ContinuousOn (fun x => vR2 (j2M gl x)) (openSlab a' b') :=
    (contDiffOn_comp_jet contDiffOn_vR2 (contDiff_j2M hgld) hU2).continuousOn
  have hc2 : ∀ lam, ContinuousOn (pd (wfluxF gl lam) lam) (openSlab a' b') := fun lam =>
    (contDiffOn_pd_of_on (hW lam) lam).continuousOn
  have hc3 : ContinuousOn (fun x => ∑ lam, pd (wfluxF gl lam) lam x) (openSlab a' b') :=
    continuousOn_finset_sum _ fun lam _ => hc2 lam
  rw [cellInt_sub_on hc1 hc3 ha hab hb, cellInt_sum_on _ hc2 ha hab hb, Fin.sum_univ_succ,
    cellInt_pd_zero_loc (hW 0) ha hab hb]
  have hz : ∀ i : Fin 3, cellInt a b (pd (wfluxF gl i.succ) i.succ) = 0 := fun i =>
    cellInt_pd_succ_loc (hW _) (hWp _) ha hab hb i
  simp only [hz, Finset.sum_const_zero, add_zero]
  rfl

end CellGrav2

section CellGrav3

variable {g k : ST 3 → Met}

/-- The jet derivative of `√(-det g)R` along `k` is the Einstein row plus the divergence of the
Palatini flux. -/
theorem fderiv_vR2_eq (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k)
    (hgs : ∀ x μ ν, g x μ ν = g x ν μ) (hks : ∀ x μ ν, k x μ ν = k x ν μ) (x : ST 3)
    (hdet : (Matrix.of (g x)).det < 0) :
    fderiv ℝ vR2 (j2M g x) (j2M k x) =
      -(volM (g x) * ∑ μ, ∑ ν, einsteinUp (g x) (ginvOf (g x)) (dF g x) (ddF g x) μ ν * k x μ ν) +
        ∑ lam, pd (palatiniFlux g k lam) lam x := by
  have hd : DifferentiableAt ℝ vR2 (j2M g x) :=
    (contDiffOn_vR2.contDiffAt (isOpen_U2.mem_nhds hdet)).differentiableAt (by simp)
  have hl : HasDerivAt (fun ε : ℝ => j2M g x + ε • j2M k x) (j2M k x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (j2M k x)).const_add (j2M g x)
  have h1 : HasDerivAt (fun ε : ℝ => vR2 (j2M g x + ε • j2M k x))
      (fderiv ℝ vR2 (j2M g x) (j2M k x)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := eh_field_variation hg hk hgs hks x hdet
  exact h1.unique h2

/-- **The gravitational cell variation** (`app:generated-dynamics`, summation by parts on a cell):
for a smooth periodic symmetric metric field `g` and variation `k` with `det(g + εk) < 0` near the
cell, the cell integral of the first variation of the first-derivative Einstein–Hilbert density is
the Einstein row plus the time fluxes `W_{Pal}^0 - δW^0` at the cell ends. -/
theorem cell_grav (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k)
    (hgs : ∀ x μ ν, g x μ ν = g x ν μ) (hks : ∀ x μ ν, k x μ ν = k x ν μ)
    (hgp : IsSPeriodic g) (hkp : IsSPeriodic k) {a' a b b' r : ℝ} (ha : a' < a) (hab : a ≤ b)
    (hb : b < b') (hr : 0 < r)
    (hdet : ∀ ε ∈ Icc (-r) r, ∀ x ∈ openSlab a' b', (Matrix.of (g x + ε • k x)).det < 0) :
    cellInt a b (fun x => fderiv ℝ L1EHp (j1M g x) (j1M k x)) =
      cellInt a b (fun x => -(volM (g x) * ∑ μ, ∑ ν,
        einsteinUp (g x) (ginvOf (g x)) (dF g x) (ddF g x) μ ν * k x μ ν)) +
      (sint (fun x => PFJ 0 (j1M g x) (j1M k x)) b - sint (fun x => PFJ 0 (j1M g x) (j1M k x)) a) -
      (sint (fun x => fderiv ℝ (WJ 0) (j1M g x) (j1M k x)) b -
        sint (fun x => fderiv ℝ (WJ 0) (j1M g x) (j1M k x)) a) := by
  have hj1g := (contDiff_j1M hg).continuous
  have hj1k := (contDiff_j1M hk).continuous
  have hj2g := (contDiff_j2M hg).continuous
  have hj2k := (contDiff_j2M hk).continuous
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) ∈ openSlab a' b' :=
    fun t ht y => cons_mem_openSlab ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩ y
  have hK1 : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin 3 → ℝ) 1,
      j1M g (Fin.cons t y) + ε • j1M k (Fin.cons t y) ∈
        {p : Met × (Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
    fun ε hε t ht y _ => hdet ε hε _ (hsl t ht y)
  have hK2 : ∀ ε ∈ Icc (-r) r, ∀ t ∈ Icc a b, ∀ y ∈ Icc (0 : Fin 3 → ℝ) 1,
      j2M g (Fin.cons t y) + ε • j2M k (Fin.cons t y) ∈
        {p : Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met) | (Matrix.of p.1).det < 0} :=
    fun ε hε t ht y _ => hdet ε hε _ (hsl t ht y)
  have hB := cell_deriv_of_jet isOpen_U1 contDiffOn_L1EHp hj1g hj1k hr hab hK1
  have hC := cell_deriv_of_jet isOpen_U2 contDiffOn_vR2 hj2g hj2k hr hab hK2
  have hD : ∀ t ∈ Icc a b, HasDerivAt (fun ε : ℝ => sint (fun x => WJ 0 (j1M g x + ε • j1M k x)) t)
      (sint (fun x => fderiv ℝ (WJ 0) (j1M g x) (j1M k x)) t) 0 := fun t ht =>
    sint_deriv_of_jet isOpen_U1 (contDiffOn_WJ 0) hj1g hj1k hr
      (fun ε hε y _ => hdet ε hε _ (hsl t ht y))
  have hDa := hD a ⟨le_rfl, hab⟩
  have hDb := hD b ⟨hab, le_rfl⟩
  have hEq : (fun ε : ℝ => cellInt a b (fun x => L1EHp (j1M g x + ε • j1M k x))) =ᶠ[nhds 0]
      fun ε => cellInt a b (fun x => vR2 (j2M g x + ε • j2M k x)) -
        (sint (fun x => WJ 0 (j1M g x + ε • j1M k x)) b -
          sint (fun x => WJ 0 (j1M g x + ε • j1M k x)) a) := by
    filter_upwards [Icc_mem_nhds (neg_lt_zero.2 hr) hr] with ε hε
    exact cell_L1EH_line hg hk hgs hks hgp hkp ha hab hb (hdet ε hε)
  have hF := (hC.sub (hDb.sub hDa)).congr_of_eventuallyEq hEq
  rw [hB.unique hF]
  -- the second-derivative density
  have hdet0 : ∀ x ∈ openSlab a' b', (Matrix.of (g x)).det < 0 := fun x hx => by
    have := hdet 0 ⟨by linarith, hr.le⟩ x hx
    simpa using this
  have hPF : ∀ lam, ContDiffOn ℝ ∞ (palatiniFlux g k lam) (openSlab a' b') := fun lam =>
    contDiffOn_comp_jet (contDiffOn_PFJ lam) ((contDiff_j1M hg).prodMk (contDiff_j1M hk))
      (j := fun x => (j1M g x, j1M k x)) fun x hx => hdet0 x hx
  have hPFp : ∀ lam, IsSPeriodic (palatiniFlux g k lam) := fun lam k' x => by
    show PFJ lam (j1M g (x + sshift k')) (j1M k (x + sshift k')) = PFJ lam (j1M g x) (j1M k x)
    rw [isSPeriodic_j1M hgp k' x, isSPeriodic_j1M hkp k' x]
  have hc2 : ∀ lam, ContinuousOn (pd (palatiniFlux g k lam) lam) (openSlab a' b') := fun lam =>
    (contDiffOn_pd_of_on (hPF lam) lam).continuousOn
  have hc3 : ContinuousOn (fun x => ∑ lam, pd (palatiniFlux g k lam) lam x) (openSlab a' b') :=
    continuousOn_finset_sum _ fun lam _ => hc2 lam
  have hcf : ContinuousOn (fun x => fderiv ℝ vR2 (j2M g x) (j2M k x)) (openSlab a' b') :=
    continuousOn_fderiv_jet isOpen_U2 contDiffOn_vR2 hj2g hj2k fun x hx => hdet0 x hx
  have hc1 : ContinuousOn (fun x => -(volM (g x) * ∑ μ, ∑ ν,
      einsteinUp (g x) (ginvOf (g x)) (dF g x) (ddF g x) μ ν * k x μ ν)) (openSlab a' b') :=
    (hcf.sub hc3).congr fun x hx => by
      show _ = fderiv ℝ vR2 (j2M g x) (j2M k x) - ∑ lam, pd (palatiniFlux g k lam) lam x
      rw [fderiv_vR2_eq hg hk hgs hks x (hdet0 x hx)]; ring
  rw [cellInt_congr (g := fun x => -(volM (g x) * ∑ μ, ∑ ν,
      einsteinUp (g x) (ginvOf (g x)) (dF g x) (ddF g x) μ ν * k x μ ν) +
        ∑ lam, pd (palatiniFlux g k lam) lam x) hab
    (fun t ht y _ => fderiv_vR2_eq hg hk hgs hks _ (hdet0 _ (hsl t ht y))),
    cellInt_add_on hc1 hc3 ha hab hb, cellInt_sum_on _ hc2 ha hab hb, Fin.sum_univ_succ,
    cellInt_pd_zero_loc (hPF 0) ha hab hb]
  have hz : ∀ i : Fin 3, cellInt a b (pd (palatiniFlux g k i.succ) i.succ) = 0 := fun i =>
    cellInt_pd_succ_loc (hPF _) (hPFp _) ha hab hb i
  simp only [hz, Finset.sum_const_zero, add_zero]
  rfl

end CellGrav3

section CellTuple

/-- Continuity of the Einstein row near the cell. -/
theorem continuousOn_einsteinRow {g k : ST 3 → Met} (hg : ContDiff ℝ ∞ g) (hk : ContDiff ℝ ∞ k)
    (hgs : ∀ x μ ν, g x μ ν = g x ν μ) (hks : ∀ x μ ν, k x μ ν = k x ν μ)
    (hkp : IsSPeriodic k) (hgp : IsSPeriodic g) {s : Set (ST 3)} (hs : IsOpen s)
    (hdet0 : ∀ x ∈ s, (Matrix.of (g x)).det < 0) :
    ContinuousOn (fun x => -(volM (g x) * ∑ μ, ∑ ν,
      einsteinUp (g x) (ginvOf (g x)) (dF g x) (ddF g x) μ ν * k x μ ν)) s := by
  have hj1g := (contDiff_j1M hg).continuous
  have hj2g := (contDiff_j2M hg).continuous
  have hj2k := (contDiff_j2M hk).continuous
  have hPF : ∀ lam, ContDiffOn ℝ ∞ (palatiniFlux g k lam) s := fun lam =>
    contDiffOn_comp_jet (contDiffOn_PFJ lam) ((contDiff_j1M hg).prodMk (contDiff_j1M hk))
      (j := fun x => (j1M g x, j1M k x)) fun x hx => hdet0 x hx
  have hc2 : ∀ lam, ContinuousOn (pd (palatiniFlux g k lam) lam) s := fun lam => by
    intro x hx
    have h := ((hPF lam).contDiffAt (hs.mem_nhds hx))
    unfold SobolevOpen.pd
    exact ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt
      |>.continuousWithinAt
  have hc3 : ContinuousOn (fun x => ∑ lam, pd (palatiniFlux g k lam) lam x) s :=
    continuousOn_finset_sum _ fun lam _ => hc2 lam
  have hcf : ContinuousOn (fun x => fderiv ℝ vR2 (j2M g x) (j2M k x)) s :=
    continuousOn_fderiv_jet isOpen_U2 contDiffOn_vR2 hj2g hj2k fun x hx => hdet0 x hx
  exact (hcf.sub hc3).congr fun x hx => by
    show _ = fderiv ℝ vR2 (j2M g x) (j2M k x) - ∑ lam, pd (palatiniFlux g k lam) lam x
    rw [fderiv_vR2_eq hg hk hgs hks x (hdet0 x hx)]; ring

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

theorem contDiff_matFlux (z : Tuple m V S S') (SM : SMData (MatLie m) V S S')
    {X : ST 3 → Fin 4 → MatLie m} (hX : ContDiff ℝ ∞ X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η)
    (γ : Fin 4) : ContDiff ℝ ∞ (matFlux z SM X η γ) := by
  have h1 : ∀ δ, ContDiff ℝ ∞ (fun y => SM.ipG (dens z y γ δ) (X y δ)) := fun δ => by
    have : (fun y => SM.ipG (dens z y γ δ) (X y δ)) =
        fun y => bilinCLM SM.ipG (dens z y γ δ) (X y δ) := rfl
    rw [this]
    exact ((bilinCLM SM.ipG).contDiff.comp (contDiff_pi.1 (contDiff_pi.1 (contDiff_dens z) γ) δ)).clm_apply
      (contDiff_pi.1 hX δ)
  have h2 : ContDiff ℝ ∞ (fun y => 2 * SM.ipV (densH z y γ) (η y)) := by
    have : (fun y => 2 * SM.ipV (densH z y γ) (η y)) =
        fun y => 2 * bilinCLM SM.ipV (densH z y γ) (η y) := rfl
    rw [this]
    exact contDiff_const.mul (((bilinCLM SM.ipV).contDiff.comp (contDiff_densH z γ)).clm_apply hη)
  unfold matFlux
  exact (ContDiff.sum fun δ _ => h1 δ).add h2

theorem isSPeriodic_matFlux (z : Tuple m V S S') (SM : SMData (MatLie m) V S S')
    {X : ST 3 → Fin 4 → MatLie m} (hXp : IsSPeriodic X) {η : ST 3 → V} (hηp : IsSPeriodic η)
    (γ : Fin 4) : IsSPeriodic (matFlux z SM X η γ) := fun k x => by
  have hd : ∀ δ, dens z (x + sshift k) γ δ = dens z x γ δ := fun δ => by
    rw [← DnJ_eq_dens, ← DnJ_eq_dens]
    simp only [z.g_per k x, z.A_per k x, isSPeriodic_pd' z.A_per γ k x]
    congr 3
    funext γ' μ
    rw [isSPeriodic_pd' z.A_per γ' k x]
  have hdH : densH z (x + sshift k) γ = densH z x γ := by
    rw [← DhJ_eq_densH, ← DhJ_eq_densH]
    simp only [z.g_per k x, z.A_per k x, z.H_per k x]
    congr 3
    funext γ'
    rw [isSPeriodic_pd' z.H_per γ' k x]
  unfold matFlux
  simp only [hd, hdH, hXp k x, hηp k x]

end CellTuple

section CellVar

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- The Einstein row `-√(-det g) G^{μν}k_{μν}` of a tuple along a metric variation. -/
def einRow (z : Tuple m V S S') (k : ST 3 → Met) (x : ST 3) : ℝ :=
  -(volM (z.g x) * ∑ μ, ∑ ν, einsteinUp (z.g x) (ginvOf (z.g x)) (dF z.g x) (ddF z.g x) μ ν * k x μ ν)

/-- **The bulk rows of the first variation of `S^{(1)}`** at a tuple along `(k, X, η)`: Einstein
row, cosmological and matter-stress metric terms, Yang–Mills and Higgs residual rows. -/
def bulkT (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (k : ST 3 → Met)
    (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (x : ST 3) : ℝ :=
  (1 / (2 * SM.κ)) * einRow z k x - SM.Λ / SM.κ * ((1 / 2) * volM (z.g x) * trG (ginvOf (z.g x)) (k x)) +
    ((1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
        (ymStressB SM.ipG (z.g x) (ginvOf (z.g x)) (Fm (z.A x) (fun γ μ => pd z.A γ x μ))) μ ν *
          k x μ ν +
       (1 / 2) * volM (z.g x) * ∑ μ, ∑ ν, up (ginvOf (z.g x))
        (higgsStressB SM.ipV SM.lamH SM.vH (z.g x) (ginvOf (z.g x)) (z.H x)
          (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x))) μ ν * k x μ ν) +
    (∑ δ, SM.ipG (densR SM z x δ) (X x δ) + 2 * rho z x * SM.ipV ((bosF SM z x).2.2) (η x))

/-- The time flux of the first variation of `S^{(1)}` through a slice. -/
def fluxT (SM : SMData (MatLie m) V S S') (z : Tuple m V S S') (k : ST 3 → Met)
    (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (t : ℝ) : ℝ :=
  (1 / (2 * SM.κ)) * (sint (fun x => PFJ 0 (j1M z.g x) (j1M k x)) t -
    sint (fun x => fderiv ℝ (WJ 0) (j1M z.g x) (j1M k x)) t) - sint (matFlux z SM X η 0) t

set_option maxHeartbeats 1000000 in
/-- **The first variation of `S^{(1)}` on a cell** (variational data): for a smooth tuple and
smooth periodic variations `(k, X, η)` (`k` symmetric), the cell integral of the first variation
of the first-derivative action density is the cell integral of the bulk rows plus the difference
of the time fluxes at the cell ends. -/
theorem cell_variation (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    (z : Tuple m V S S') {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (hkp : IsSPeriodic k) {X : ST 3 → Fin 4 → MatLie m} (hX : ContDiff ℝ ∞ X)
    (hXp : IsSPeriodic X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η) (hηp : IsSPeriodic η)
    {a b : ℝ} (hab : a ≤ b) :
    cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z.g z.A z.H x) (j1F k X η x)) =
      cellInt a b (bulkT SM z k X η) + (fluxT SM z k X η b - fluxT SM z k X η a) := by
  -- the margin
  have hUo : IsOpen {M : Met | (Matrix.of M).det < 0} := isOpen_det_neg continuous_id
  obtain ⟨r, hr, hmar⟩ := exists_line_margin z.g_smooth.continuous hk.continuous z.g_per hkp hUo
    hab (fun x _ => GenCell.Tuple_det_neg z x)
  have ha : a - r < a := by linarith
  have hb : b < b + r := by linarith
  have hdet : ∀ ε ∈ Icc (-r) r, ∀ x ∈ openSlab (a - r) (b + r),
      (Matrix.of (z.g x + ε • k x)).det < 0 := fun ε hε x hx =>
    hmar ε hε x ⟨hx.1.le, hx.2.le⟩
  have hgs : ∀ x μ ν, z.g x μ ν = z.g x ν μ := fun x μ ν => z.g_symm x μ ν
  have hdet0 : ∀ x ∈ openSlab (a - r) (b + r), (Matrix.of (z.g x)).det < 0 :=
    fun x _ => GenCell.Tuple_det_neg z x
  set c : ℝ := 1 / (2 * SM.κ) with hc
  set F : ST 3 → ℝ := fun x => fderiv ℝ L1EHp (j1M z.g x) (j1M k x) with hF
  set D : ST 3 → ℝ := fun x => ∑ γ, pd (matFlux z SM X η γ) γ x with hD
  set R : ST 3 → ℝ := fun x => bulkT SM z k X η x - c * einRow z k x with hR
  have hpt : ∀ x, fderiv ℝ (L1SM SM) (j1F z.g z.A z.H x) (j1F k X η x) = (c * F x + R x) - D x := by
    intro x
    rw [fderiv_L1SM_eq SM hV z hk hks hX hη x,
      show (z.g x, fun α => pd z.g α x) = j1M z.g x from rfl,
      show (k x, fun α => pd k α x) = j1M k x from rfl]
    simp only [hF, hR, hD, bulkT, hc]
    ring
  simp only [hpt]
  -- continuity on the slab
  have hcL : ContinuousOn (fun x => fderiv ℝ (L1SM SM) (j1F z.g z.A z.H x) (j1F k X η x))
      (openSlab (a - r) (b + r)) :=
    continuousOn_fderiv_jet isOpen_chart1 (contDiffOn_L1SM SM)
      (continuous_j1F z.g_smooth z.A_smooth z.H_smooth) (continuous_j1F hk hX hη)
      fun x _ => GenCell.Tuple_det_neg z x
  have hcF : ContinuousOn F (openSlab (a - r) (b + r)) :=
    continuousOn_fderiv_jet isOpen_U1 contDiffOn_L1EHp (contDiff_j1M z.g_smooth).continuous
      (contDiff_j1M hk).continuous hdet0
  have hMF : ∀ γ, ContDiff ℝ ∞ (matFlux z SM X η γ) := fun γ => contDiff_matFlux z SM hX hη γ
  have hcDγ : ∀ γ, ContinuousOn (pd (matFlux z SM X η γ) γ) (openSlab (a - r) (b + r)) :=
    fun γ => (EHFieldVariation.contDiff_pd' (hMF γ) γ).continuous.continuousOn
  have hcD : ContinuousOn D (openSlab (a - r) (b + r)) :=
    continuousOn_finset_sum _ fun γ _ => hcDγ γ
  have hcE : ContinuousOn (einRow z k) (openSlab (a - r) (b + r)) :=
    continuousOn_einsteinRow z.g_smooth hk hgs hks hkp z.g_per (isOpen_openSlab _ _) hdet0
  have hcR : ContinuousOn R (openSlab (a - r) (b + r)) :=
    ((hcL.add hcD).sub (continuousOn_const.mul hcF)).congr fun x _ => by
      show R x = fderiv ℝ (L1SM SM) (j1F z.g z.A z.H x) (j1F k X η x) + D x - c * F x
      rw [hpt x]; ring
  have hcB : ContinuousOn (bulkT SM z k X η) (openSlab (a - r) (b + r)) :=
    (hcR.add (continuousOn_const.mul hcE)).congr fun x _ => by
      show bulkT SM z k X η x = R x + c * einRow z k x
      simp only [hR]; ring
  have hcFR : ContinuousOn (fun x => c * F x + R x) (openSlab (a - r) (b + r)) :=
    (continuousOn_const.mul hcF).add hcR
  rw [cellInt_sub_on hcFR hcD ha hab hb,
    cellInt_add_on (f := fun x => c * F x) (g := R) (continuousOn_const.mul hcF) hcR ha hab hb,
    cellInt_smul]
  -- the gravitational part
  have hG := cell_grav z.g_smooth hk hgs hks z.g_per hkp ha hab hb hr hdet
  -- the matter divergence
  have hDi : cellInt a b D = sint (matFlux z SM X η 0) b - sint (matFlux z SM X η 0) a := by
    rw [cellInt_sum_on _ hcDγ ha hab hb, Fin.sum_univ_succ,
      cellInt_pd_zero_loc (hMF 0).contDiffOn ha hab hb]
    have hz : ∀ i : Fin 3, cellInt a b (pd (matFlux z SM X η i.succ) i.succ) = 0 := fun i =>
      cellInt_pd_succ_loc (hMF _).contDiffOn (isSPeriodic_matFlux z SM hXp hηp _) ha hab hb i
    simp only [hz, Finset.sum_const_zero, add_zero]
  -- the bulk
  have hBk : cellInt a b (bulkT SM z k X η) = c * cellInt a b (einRow z k) + cellInt a b R := by
    have e : bulkT SM z k X η = fun x => c * einRow z k x + R x := by
      funext x; simp only [hR]; ring
    rw [e, cellInt_add_on (f := fun x => c * einRow z k x) (g := R) (continuousOn_const.mul hcE)
      hcR ha hab hb, cellInt_smul]
  rw [hDi, hBk]
  have hG' : cellInt a b F = cellInt a b (einRow z k) +
      (sint (fun x => PFJ 0 (j1M z.g x) (j1M k x)) b - sint (fun x => PFJ 0 (j1M z.g x) (j1M k x)) a) -
      (sint (fun x => fderiv ℝ (WJ 0) (j1M z.g x) (j1M k x)) b -
        sint (fun x => fderiv ℝ (WJ 0) (j1M z.g x) (j1M k x)) a) := hG
  rw [hG']
  simp only [fluxT, hc]
  ring

end CellVar

end

end GenCellVar

end RenewalGeometry
