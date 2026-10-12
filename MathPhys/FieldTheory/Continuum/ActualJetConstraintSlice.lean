/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.ActualJetSliceExtension
import MathPhys.FieldTheory.Gravity.SliceGaussCodazziJet
import MathPhys.FieldTheory.Continuum.GeneratedPhysicalIdentificationClosed

/-!
# Cauchy slice data of the actual-jet system and their completions

Einstein–Standard-Model action-closure manuscript, `prop:generated-initial`,
`ass:constrained-initial-solver`, `eq:exact-physical-initial-manifold` (the complete constraint
map `𝔆_k`: Einstein normal constraints, internal Gauss constraint, defining-jet identities and the
chosen initial gauge completion).

## Slice data

`SliceCauchy` — smooth `ℤ³`-periodic Cauchy data on the slice `t = 0` of `ℝ × 𝕋³` in the
**unit-lapse, zero-shift temporal gauge** (`g₀₀ = -1`, `g₀ᵢ = 0` on the slice; temporal internal
gauge `A₀ ≡ 0`): the spatial metric `γᵢⱼ`, the extrinsic curvature `Kᵢⱼ` (`∂_tγ = -2K`), the
spatial gauge potentials `Aᵢ` and their time derivatives `Ȧᵢ = F₀ᵢ`, the Higgs field `H` and its
time derivative `Ḣ = Π`, and both spinors `Ψ`, `Ψ̄`; the chart condition says that the slice metric
lies in the Lorentzian foliated chart.

* `met4 a b C` — the `4 × 4` block matrix; `g0 D`, `gi0 D`, `γi D` (inverse spatial metric);
* the **harmonic-gauge completion** of the lapse and shift time derivatives
  (`eq:supp-open-harmonic-initial`): `∂_tg₀₀ = 2 tr_γK` (`v00`),
  `∂_tg₀ₗ = γ^{jk}(∂_jγ_{kl} - ½∂_lγ_{jk})` (`v0`); `vt D` is the full `∂_tg` on the slice;
* `Params` — the second-order completion data `∂_t²g` (`W`), `∂_t²Aᵢ` (`Aa`), `∂_t²H` (`Ha`) and
  the normal spinor derivatives `∂_tΨ`, `∂_tΨ̄`;
* `mkTuple` — the completed smooth field tuple (second-order Taylor extensions of
  `ActualJetSliceExtension` with a small time scale `ε`), and `exists_chart_eps`: for small `ε`
  the completed metric stays in the Lorentzian chart at **all** times (compactness of the range of
  periodic fields), so the completion is an `ActualJetBridge.Tuple`.
-/

open Set Filter Topology Finset
open scoped ContDiff

noncomputable section

namespace MathPhys.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState SliceExt

set_option linter.unusedSectionVars false

/-! ### Block matrices -/

/-- The `4 × 4` block matrix with time-time entry `a`, time-space entries `b` and space-space
block `C`. -/
def met4 (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) : Met := fun μ ν =>
  Fin.cases (Fin.cases a b ν) (fun i => Fin.cases (b i) (fun j => C i j) ν) μ

@[simp] theorem met4_zero_zero (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) :
    met4 a b C 0 0 = a := rfl
@[simp] theorem met4_zero_succ (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (j : Fin 3) :
    met4 a b C 0 j.succ = b j := rfl
@[simp] theorem met4_succ_zero (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    met4 a b C i.succ 0 = b i := rfl
@[simp] theorem met4_succ_succ (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    met4 a b C i.succ j.succ = C i j := rfl

theorem of_met4 (a : ℝ) (b : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (met4 a b C) = ContractedBianchiJet.sliceMat a b (Matrix.of C) := by
  ext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;> rfl

theorem met4_symm {a : ℝ} {b : Fin 3 → ℝ} {C : Fin 3 → Fin 3 → ℝ} (hC : ∀ i j, C i j = C j i)
    (μ ν : Fin 4) : met4 a b C μ ν = met4 a b C ν μ := by
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;> simp [hC]

/-- `met4` as a continuous linear map of its blocks. -/
def met4L : (ℝ × (Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)) →L[ℝ] Met :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => met4 p.1 p.2.1 p.2.2
      map_add' := fun p q => by
        funext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;> simp
      map_smul' := fun c p => by
        funext μ ν
        refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;> simp }

theorem met4L_apply (p : ℝ × (Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)) :
    met4L p = met4 p.1 p.2.1 p.2.2 := rfl

/-- Partial derivatives commute with continuous linear maps. -/
theorem pd_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [DecidableEq ι] (L : E →L[ℝ] F)
    {f : (ι → ℝ) → E} {y : ι → ℝ} (hf : DifferentiableAt ℝ f y) (k : ι) :
    pd (fun y => L (f y)) k y = L (pd f k y) := by
  unfold SobolevOpen.pd
  rw [show (fun y => L (f y)) = L ∘ f from rfl, fderiv_comp y L.differentiableAt hf]
  simp

theorem contDiff_met4 {a : (Fin 3 → ℝ) → ℝ} {b : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {C : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hC : ContDiff ℝ ∞ C) : ContDiff ℝ ∞ (fun y => met4 (a y) (b y) (C y)) :=
  met4L.contDiff.comp (ha.prodMk (hb.prodMk hC))

theorem pd_met4 {a : (Fin 3 → ℝ) → ℝ} {b : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {C : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hC : ContDiff ℝ ∞ C) (k : Fin 3) (y : Fin 3 → ℝ) :
    pd (fun y => met4 (a y) (b y) (C y)) k y = met4 (pd a k y) (pd b k y) (pd C k y) := by
  have hd : DifferentiableAt ℝ (fun y => (a y, b y, C y)) y :=
    ((ha.prodMk (hb.prodMk hC)).differentiable (by simp)) y
  have h := pd_clm met4L hd k
  simp only [met4L_apply] at h
  rw [h]
  unfold SobolevOpen.pd
  have hda := (ha.differentiable (by simp)) y
  have hdb := (hb.differentiable (by simp)) y
  have hdC := (hC.differentiable (by simp)) y
  rw [DifferentiableAt.fderiv_prodMk hda (hdb.prodMk hdC), DifferentiableAt.fderiv_prodMk hdb hdC]
  rfl

/-! ### The Lorentzian chart -/

/-- The Lorentzian foliated chart for a metric: invertible, inverse in the chart of
`ActualJetFrame.frameOf`. -/
def GChart (g : Met) : Prop := (Matrix.of g).det ≠ 0 ∧ IsLorChart (ginvOf g)

theorem isOpen_gchart : IsOpen {g : Met | GChart g} := by
  have hdet : Continuous fun g : Met => (Matrix.of g).det :=
    Continuous.matrix_det (A := fun g : Met => Matrix.of g) continuous_id
  have h1 : IsOpen {g : Met | (Matrix.of g).det ≠ 0} := isOpen_ne_fun hdet continuous_const
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hc : ContinuousAt (fun g : Met => ginvOf g) g := by
    have : ContDiffAt ℝ ∞ (fun g : Met => ginvOf g) g :=
      ContDiffAt.ginvOf_fun contDiffAt_id hg.1
    exact this.continuousAt
  have h2 : ∀ᶠ g' in 𝓝 g, IsLorChart (ginvOf g') := eventually_chart hc hg.2
  filter_upwards [h1.mem_nhds hg.1, h2] with g' h1' h2'
  exact ⟨h1', h2'⟩

/-! ### Periodic fields: compact range and bounds -/

theorem isCompact_range_of_zperiodic {W : Type*} [TopologicalSpace W] {G : (Fin 3 → ℝ) → W}
    (hG : Continuous G) (hper : IsZPeriodic G) : IsCompact (Set.range G) := by
  set Q : Set (Fin 3 → ℝ) := Set.pi univ (fun _ => Icc 0 1)
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have e : Set.range G = G '' Q := by
    refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
    rintro _ ⟨y, rfl⟩
    refine ⟨fun i => Int.fract (y i), fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩,
      hper.apply_fract y⟩
  rw [e]
  exact hQ.image hG

theorem exists_bound_of_zperiodic {W : Type*} [NormedAddCommGroup W] {G : (Fin 3 → ℝ) → W}
    (hG : Continuous G) (hper : IsZPeriodic G) : ∃ M, 0 ≤ M ∧ ∀ y, ‖G y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_range_of_zperiodic hG hper).isBounded.exists_norm_le
  exact ⟨max M 0, le_max_right _ _, fun y => (hM _ ⟨y, rfl⟩).trans (le_max_left _ _)⟩

/-! ### Slice Cauchy data -/

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- **Smooth periodic Cauchy slice data** in the unit-lapse, zero-shift temporal gauge
(`prop:generated-initial`): spatial metric `γ`, extrinsic curvature `K` (`∂_tγ = -2K`), spatial
gauge potentials `Aᵢ` and `Ȧᵢ = ∂_tAᵢ` (`A₀ ≡ 0`), Higgs field `H` and `Ḣ = ∂_tH`, spinors `Ψ`,
`Ψ̄`; the slice metric `diag(-1, γ)` is in the Lorentzian foliated chart. -/
structure SliceCauchy where
  γ : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ
  K : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ
  A : (Fin 3 → ℝ) → Fin 3 → MatLie m
  Ad : (Fin 3 → ℝ) → Fin 3 → MatLie m
  H : (Fin 3 → ℝ) → V
  Hd : (Fin 3 → ℝ) → V
  ψ : (Fin 3 → ℝ) → S
  ψb : (Fin 3 → ℝ) → S'
  γ_smooth : ContDiff ℝ ∞ γ
  K_smooth : ContDiff ℝ ∞ K
  A_smooth : ContDiff ℝ ∞ A
  Ad_smooth : ContDiff ℝ ∞ Ad
  H_smooth : ContDiff ℝ ∞ H
  Hd_smooth : ContDiff ℝ ∞ Hd
  ψ_smooth : ContDiff ℝ ∞ ψ
  ψb_smooth : ContDiff ℝ ∞ ψb
  γ_per : IsZPeriodic γ
  K_per : IsZPeriodic K
  A_per : IsZPeriodic A
  Ad_per : IsZPeriodic Ad
  H_per : IsZPeriodic H
  Hd_per : IsZPeriodic Hd
  ψ_per : IsZPeriodic ψ
  ψb_per : IsZPeriodic ψb
  γ_symm : ∀ y i j, γ y i j = γ y j i
  K_symm : ∀ y i j, K y i j = K y j i
  chart : ∀ y, GChart (met4 (-1) 0 (γ y))

namespace SliceCauchy

variable (D : SliceCauchy m V S S')

/-- The space-time metric on the slice, `diag(-1, γ)`. -/
def g0 (y : Fin 3 → ℝ) : Met := met4 (-1) 0 (D.γ y)

/-- Its inverse. -/
def gi0 (y : Fin 3 → ℝ) : Met := ginvOf (D.g0 y)

/-- The inverse spatial metric `γ^{ij}` (the spatial block of `g⁻¹`). -/
def γi (y : Fin 3 → ℝ) (i j : Fin 3) : ℝ := D.gi0 y i.succ j.succ

theorem g0_symm (y : Fin 3 → ℝ) (μ ν : Fin 4) : D.g0 y μ ν = D.g0 y ν μ :=
  met4_symm (D.γ_symm y) μ ν

theorem gi0_eq (y : Fin 3 → ℝ) : D.gi0 y = met4 (-1) 0 (D.γi y) := by
  have hdet := (D.chart y).1
  have hinv := mul_ginvOf hdet
  have hsymm := ginvOf_symm (D.g0_symm y)
  have h00 : D.gi0 y 0 0 = -1 := by
    have := hinv 0 0
    rw [Fin.sum_univ_succ] at this
    simp only [g0, met4_zero_zero, met4_zero_succ, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, ite_true] at this
    simp only [gi0, g0]; linarith
  have h0j : ∀ j : Fin 3, D.gi0 y 0 j.succ = 0 := by
    intro j
    have := hinv 0 j.succ
    rw [Fin.sum_univ_succ] at this
    simp only [g0, met4_zero_zero, met4_zero_succ, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, (Fin.succ_ne_zero j).symm, ite_false] at this
    simp only [gi0, g0]; linarith
  funext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
  · exact h00
  · exact h0j j
  · simp only [met4_succ_zero, Pi.zero_apply]
    rw [show D.gi0 y i.succ 0 = ginvOf (D.g0 y) i.succ 0 from rfl, hsymm]
    exact h0j i
  · rfl

/-- `γ γ⁻¹ = 1`. -/
theorem γ_mul_γi (y : Fin 3 → ℝ) (i j : Fin 3) :
    ∑ k, D.γ y i k * D.γi y k j = if i = j then 1 else 0 := by
  have h := mul_ginvOf (D.chart y).1 i.succ j.succ
  rw [Fin.sum_univ_succ] at h
  simp only [met4_succ_zero, met4_succ_succ, Pi.zero_apply, zero_mul, zero_add,
    Fin.succ_inj] at h
  exact h

theorem γi_symm (y : Fin 3 → ℝ) (i j : Fin 3) : D.γi y i j = D.γi y j i :=
  ginvOf_symm (D.g0_symm y) i.succ j.succ

/-- The trace `tr_γK = γ^{ij}K_{ij}`. -/
def trK (y : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, D.γi y i j * D.K y i j

/-- **Harmonic-gauge completion of the lapse**: `∂_tg₀₀ = 2 tr_γK`. -/
def v00 (y : Fin 3 → ℝ) : ℝ := 2 * D.trK y

/-- **Harmonic-gauge completion of the shift**: `∂_tg₀ₗ = γ^{jk}(∂_jγ_{kl} - ½∂_lγ_{jk})`. -/
def v0 (y : Fin 3 → ℝ) (l : Fin 3) : ℝ :=
  ∑ j, ∑ k, D.γi y j k * (pd D.γ j y k l - (1 / 2) * pd D.γ l y j k)

/-- The time derivative `∂_tg` of the space-time metric on the slice. -/
def vt (y : Fin 3 → ℝ) : Met := met4 (D.v00 y) (D.v0 y) (fun i j => -2 * D.K y i j)

/-! #### Smoothness and periodicity of the derived slice fields -/

theorem contDiff_g0 : ContDiff ℝ ∞ D.g0 :=
  contDiff_met4 contDiff_const contDiff_const D.γ_smooth

theorem contDiff_gi0_apply (μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => D.gi0 y μ ν) :=
  contDiff_iff_contDiffAt.2 fun y =>
    ContDiffAt.ginvOf D.contDiff_g0.contDiffAt (D.chart y).1 μ ν

theorem contDiff_γi : ContDiff ℝ ∞ D.γi :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j => D.contDiff_gi0_apply i.succ j.succ

theorem contDiff_γi_apply (i j : Fin 3) : ContDiff ℝ ∞ (fun y => D.γi y i j) :=
  D.contDiff_gi0_apply i.succ j.succ

theorem contDiff_γ_apply (i j : Fin 3) : ContDiff ℝ ∞ (fun y => D.γ y i j) :=
  contDiff_pi.1 (contDiff_pi.1 D.γ_smooth i) j

theorem contDiff_K_apply (i j : Fin 3) : ContDiff ℝ ∞ (fun y => D.K y i j) :=
  contDiff_pi.1 (contDiff_pi.1 D.K_smooth i) j

theorem contDiff_pdγ_apply (k i j : Fin 3) : ContDiff ℝ ∞ (fun y => pd D.γ k y i j) :=
  contDiff_pi.1 (contDiff_pi.1 (contDiff_pd3 D.γ_smooth k) i) j

theorem contDiff_trK : ContDiff ℝ ∞ D.trK := by
  have h1 := D.contDiff_γi_apply
  have h2 := D.contDiff_K_apply
  unfold trK; fun_prop

theorem contDiff_v00 : ContDiff ℝ ∞ D.v00 := by
  unfold v00; exact contDiff_const.mul D.contDiff_trK

theorem contDiff_v0 : ContDiff ℝ ∞ D.v0 := by
  have h1 := D.contDiff_γi_apply
  have h2 := D.contDiff_pdγ_apply
  refine contDiff_pi.2 fun l => ?_
  unfold v0; fun_prop

theorem contDiff_negK : ContDiff ℝ ∞ (fun y i j => -2 * D.K y i j) := by
  have h2 := D.contDiff_K_apply
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  fun_prop

theorem contDiff_vt : ContDiff ℝ ∞ D.vt :=
  contDiff_met4 D.contDiff_v00 D.contDiff_v0 D.contDiff_negK

theorem g0_per : IsZPeriodic D.g0 := fun k y => by simp only [g0, D.γ_per k y]

theorem gi0_per : IsZPeriodic D.gi0 := fun k y => by
  show ginvOf (D.g0 (y + zvec k)) = ginvOf (D.g0 y); rw [D.g0_per k y]

theorem γi_per : IsZPeriodic D.γi := fun k y => by
  funext i j; show D.gi0 (y + zvec k) i.succ j.succ = D.gi0 y i.succ j.succ; rw [D.gi0_per k y]

theorem pdγ_per (j : Fin 3) : IsZPeriodic (pd D.γ j) := by
  intro k y
  unfold SobolevOpen.pd
  have : (fun y => D.γ (y + zvec k)) = D.γ := funext fun y => D.γ_per k y
  rw [← fderiv_comp_add_right, this]

theorem trK_per : IsZPeriodic D.trK := fun k y => by
  show ∑ i, ∑ j, D.γi (y + zvec k) i j * D.K (y + zvec k) i j = ∑ i, ∑ j, D.γi y i j * D.K y i j
  rw [D.γi_per k y, D.K_per k y]

theorem v0_per : IsZPeriodic D.v0 := fun k y => by
  funext l
  show ∑ j, ∑ i, D.γi (y + zvec k) j i * (pd D.γ j (y + zvec k) i l -
      (1 / 2) * pd D.γ l (y + zvec k) j i) =
    ∑ j, ∑ i, D.γi y j i * (pd D.γ j y i l - (1 / 2) * pd D.γ l y j i)
  simp only [D.γi_per k y, D.pdγ_per _ k y]

theorem vt_per : IsZPeriodic D.vt := fun k y => by
  show met4 (2 * D.trK (y + zvec k)) (D.v0 (y + zvec k)) (fun i j => -2 * D.K (y + zvec k) i j) =
    met4 (2 * D.trK y) (D.v0 y) (fun i j => -2 * D.K y i j)
  rw [D.trK_per k y, D.v0_per k y, D.K_per k y]

end SliceCauchy

/-! ### Second-order completion data -/

variable (m V S S') in
/-- **Second-order completion data** on the slice: `∂_t²g` (`W`, symmetric), `∂_t²Aᵢ` (`Aa`),
`∂_t²H` (`Ha`) and the normal derivatives `∂_tΨ` (`ψd`), `∂_tΨ̄` (`ψbd`). -/
structure Params where
  W : (Fin 3 → ℝ) → Met
  Aa : (Fin 3 → ℝ) → Fin 3 → MatLie m
  Ha : (Fin 3 → ℝ) → V
  ψd : (Fin 3 → ℝ) → S
  ψbd : (Fin 3 → ℝ) → S'
  W_smooth : ContDiff ℝ ∞ W
  Aa_smooth : ContDiff ℝ ∞ Aa
  Ha_smooth : ContDiff ℝ ∞ Ha
  ψd_smooth : ContDiff ℝ ∞ ψd
  ψbd_smooth : ContDiff ℝ ∞ ψbd
  W_per : IsZPeriodic W
  Aa_per : IsZPeriodic Aa
  Ha_per : IsZPeriodic Ha
  ψd_per : IsZPeriodic ψd
  ψbd_per : IsZPeriodic ψbd
  W_symm : ∀ y μ ν, W y μ ν = W y ν μ

/-- The zero completion data. -/
def Params.zero : Params m V S S' where
  W := fun _ => 0
  Aa := fun _ => 0
  Ha := fun _ => 0
  ψd := fun _ => 0
  ψbd := fun _ => 0
  W_smooth := contDiff_const
  Aa_smooth := contDiff_const
  Ha_smooth := contDiff_const
  ψd_smooth := contDiff_const
  ψbd_smooth := contDiff_const
  W_per := fun _ _ => rfl
  Aa_per := fun _ _ => rfl
  Ha_per := fun _ _ => rfl
  ψd_per := fun _ _ => rfl
  ψbd_per := fun _ _ => rfl
  W_symm := fun _ _ _ => rfl

/-- The temporal-gauge padding `(a₁, a₂, a₃) ↦ (0, a₁, a₂, a₃)`. -/
def padL : (Fin 3 → MatLie m) →L[ℝ] (Fin 4 → MatLie m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a μ => Fin.cases 0 a μ
      map_add' := fun a b => by
        funext μ; refine Fin.cases ?_ (fun i => ?_) μ <;> simp
      map_smul' := fun c a => by
        funext μ; refine Fin.cases ?_ (fun i => ?_) μ <;> simp }

@[simp] theorem padL_zero (a : Fin 3 → MatLie m) : padL a 0 = 0 := rfl
@[simp] theorem padL_succ (a : Fin 3 → MatLie m) (i : Fin 3) : padL a i.succ = a i := rfl

/-! ### The completed tuple -/

namespace SliceCauchy

variable (D : SliceCauchy m V S S') (P : Params m V S S')

/-- The completed metric field `g = g₀ + φ₁ ∂_tg + φ₂ W`. -/
def gF (ε : ℝ) : ST 3 → Met := textn ε D.g0 D.vt P.W

/-- The completed gauge potential (temporal gauge). -/
def AF (ε : ℝ) : ST 3 → Fin 4 → MatLie m :=
  textn ε (fun y => padL (D.A y)) (fun y => padL (D.Ad y)) (fun y => padL (P.Aa y))

/-- The completed Higgs field. -/
def HF (ε : ℝ) : ST 3 → V := textn ε D.H D.Hd P.Ha

/-- The completed spinor. -/
def ψF (ε : ℝ) : ST 3 → S := textn ε D.ψ P.ψd (fun _ => 0)

/-- The completed co-spinor. -/
def ψbF (ε : ℝ) : ST 3 → S' := textn ε D.ψb P.ψbd (fun _ => 0)

theorem contDiff_gF (ε : ℝ) : ContDiff ℝ ∞ (D.gF P ε) :=
  contDiff_textn ε D.contDiff_g0 D.contDiff_vt P.W_smooth

theorem contDiff_padA {a : (Fin 3 → ℝ) → Fin 3 → MatLie m} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (fun y => padL (a y)) :=
  padL.contDiff.comp ha

theorem contDiff_AF (ε : ℝ) : ContDiff ℝ ∞ (D.AF P ε) :=
  contDiff_textn ε (contDiff_padA D.A_smooth) (contDiff_padA D.Ad_smooth)
    (contDiff_padA P.Aa_smooth)

theorem contDiff_HF (ε : ℝ) : ContDiff ℝ ∞ (D.HF P ε) :=
  contDiff_textn ε D.H_smooth D.Hd_smooth P.Ha_smooth

theorem contDiff_ψF (ε : ℝ) : ContDiff ℝ ∞ (D.ψF P ε) :=
  contDiff_textn ε D.ψ_smooth P.ψd_smooth contDiff_const

theorem contDiff_ψbF (ε : ℝ) : ContDiff ℝ ∞ (D.ψbF P ε) :=
  contDiff_textn ε D.ψb_smooth P.ψbd_smooth contDiff_const

theorem padA_per {a : (Fin 3 → ℝ) → Fin 3 → MatLie m} (ha : IsZPeriodic a) :
    IsZPeriodic (fun y => padL (a y)) := fun k y => by simp only [ha k y]

theorem gF_symm (ε : ℝ) (x : ST 3) (μ ν : Fin 4) : D.gF P ε x μ ν = D.gF P ε x ν μ := by
  simp only [gF, textn_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [D.g0_symm, show D.vt (Fin.tail x) μ ν = D.vt (Fin.tail x) ν μ from
    met4_symm (fun i j => by rw [D.K_symm]) μ ν, P.W_symm]

theorem AF_temporal (ε : ℝ) (x : ST 3) : D.AF P ε x 0 = 0 := by
  simp [AF, textn_apply]

/-- **The completed smooth field tuple** (given the chart condition at all times). -/
def mkTuple (ε : ℝ) (hch : ∀ x, GChart (D.gF P ε x)) : Tuple m V S S' where
  g := D.gF P ε
  A := D.AF P ε
  H := D.HF P ε
  ψ := D.ψF P ε
  ψb := D.ψbF P ε
  g_smooth := D.contDiff_gF P ε
  A_smooth := D.contDiff_AF P ε
  H_smooth := D.contDiff_HF P ε
  ψ_smooth := D.contDiff_ψF P ε
  ψb_smooth := D.contDiff_ψbF P ε
  g_per := isSPeriodic_textn ε D.g0_per D.vt_per P.W_per
  A_per := isSPeriodic_textn ε (padA_per D.A_per) (padA_per D.Ad_per) (padA_per P.Aa_per)
  H_per := isSPeriodic_textn ε D.H_per D.Hd_per P.Ha_per
  ψ_per := isSPeriodic_textn ε D.ψ_per P.ψd_per (fun _ _ => rfl)
  ψb_per := isSPeriodic_textn ε D.ψb_per P.ψbd_per (fun _ _ => rfl)
  g_symm := D.gF_symm P ε
  temporal := D.AF_temporal P ε
  det_ne := fun x => (hch x).1
  lor := fun x => (hch x).2

/-- **For a small time scale the completed metric is Lorentzian at all times.** -/
theorem exists_chart_eps :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ x, GChart (D.gF P ε x) := by
  have hK := isCompact_range_of_zperiodic D.contDiff_g0.continuous D.g0_per
  have hsub : Set.range D.g0 ⊆ {g : Met | GChart g} := by
    rintro _ ⟨y, rfl⟩; exact D.chart y
  obtain ⟨δ, hδ, hδs⟩ := hK.exists_thickening_subset_open isOpen_gchart hsub
  obtain ⟨M1, hM1, hb1⟩ := exists_bound_of_zperiodic D.contDiff_vt.continuous D.vt_per
  obtain ⟨M2, hM2, hb2⟩ := exists_bound_of_zperiodic P.W_smooth.continuous P.W_per
  refine ⟨min 1 (δ / (2 * (M1 + 2 * M2 + 1))), lt_min one_pos (by positivity),
    fun ε hε hεle x => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hεδ : ε ≤ δ / (2 * (M1 + 2 * M2 + 1)) := hεle.trans (min_le_right _ _)
  have hdist : ‖D.gF P ε x - D.g0 (Fin.tail x)‖ < δ := by
    refine (norm_textn_sub_le hε.le x).trans_lt ?_
    have h1 : ε * ‖D.vt (Fin.tail x)‖ ≤ ε * M1 := mul_le_mul_of_nonneg_left (hb1 _) hε.le
    have h2 : 2 * ε ^ 2 * ‖P.W (Fin.tail x)‖ ≤ 2 * ε ^ 2 * M2 :=
      mul_le_mul_of_nonneg_left (hb2 _) (by positivity)
    have h3 : ε ^ 2 ≤ ε := by nlinarith
    have hpos : 0 < 2 * (M1 + 2 * M2 + 1) := by positivity
    have h4 : ε * (2 * (M1 + 2 * M2 + 1)) ≤ δ := by rwa [le_div_iff₀ hpos] at hεδ
    nlinarith
  apply hδs
  rw [Metric.mem_thickening_iff]
  exact ⟨D.g0 (Fin.tail x), ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hdist⟩

end SliceCauchy

end MathPhys.GenSlice
