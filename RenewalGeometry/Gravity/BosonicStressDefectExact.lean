/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SignedMeasureWeakCompactness
import RenewalGeometry.Analysis.QuadraticPacketDefect
import RenewalGeometry.Analysis.MollifierLpConvergence
import RenewalGeometry.Gravity.BosonicStressAlgebra
import RenewalGeometry.Gravity.DefectConservationTransportExact

/-!
# Measure-valued Yang–Mills and Higgs stress defects
  (Einstein–SM action closure: `lem:critical-cubic`, `prop:YM-defect`, `thm:higgs-defect`,
  `thm:joint-defect`, `thm:zero-defect-characterization`, `cor:independent-bosonic-certificates`)

## Setting and renderings

* The compact chart (compact domain including its boundary) is a compact metric space `K` with a
  finite Borel measure `V₀` (the positive reference volume `dx`); this covers a compact region of
  `ℝ⁴` and `𝕋⁴`.  Finite signed Radon measures on `K` are continuous linear functionals on `C(K, ℝ)`
  (Riesz identification, as in `PositivePacketDefectExact.lean` and
  `DefectConservationTransportExact.lean`); symmetric-tensor-valued measures are families
  `Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)`, and `S ⇀* Λ` means convergence against every `φ ∈ C(K)`.
* Metrics are continuous component fields `g : C(K, Fin 4 → Fin 4 → ℝ)`; "uniform convergence"
  is convergence in `C(K, ·)` (the sup topology on the compact chart).  The paper's smooth `g_h`
  enter only through their values, so continuity suffices; nondegeneracy (`det ≠ 0`) of the `g_h`
  and of the limit is assumed (it is what the uniform inverse bounds give).  The volume density is
  `vol g = √|det g|`, the inverse metric `ginv g = g⁻¹`.
* The gauge curvature is entered through its real components `F^a_{μν}` in an orthonormal basis of
  the fixed invariant inner product of each simple factor; the Lie metric of the action is then the
  diagonal weight `w_a = g_{j(a)}^{-2}` (`BosonicStress.lieIp`).  The covariant Higgs gradient
  `D_{A_h} H_h` is entered through its real components `Y_{μ a}` in an orthonormal basis of the
  realified Higgs fibre (`Re⟨·,·⟩` = Euclidean product); weak/strong `L²` convergence of these
  finite-dimensional fields is componentwise (equivalent).  The Higgs field itself takes values in a
  finite-dimensional real inner product space `E` (realified fibre, `|H| = ‖H‖`).
* The uniform `L⁴` bound on `H_h` (the four-dimensional Sobolev consequence `H¹(K) ⊂ L⁴(K)` of the
  weak `H¹` convergence in `eq:critical-Higgs`) is taken as an explicit hypothesis; weak `H¹`
  convergence enters through weak `L²` convergence of the weak derivatives `∂_μ H_h`.

## Results

* `critical_cubic` (`lem:critical-cubic`): `|H_h|²H_h ⇀ |H|²H` in `L^{4/3}` (`cubic_weak`),
  `D_{A_h}H_h ⇀ D_AH` in `L²` (`covD_weak`), and after extraction the quartic concentration
  measure `ν_H ≥ 0` with `|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H` and `ν_H = 0 ⟺ H_h → H` in `L⁴`
  (`quartic_defect`; uniform convexity of `L⁴` and the convexity bound
  `norm_pow_four_le_weighted`).
* `ym_defect` (`prop:YM-defect`): the symmetric tensor-valued Yang–Mills stress defect
  `𝔖_{YM}` (`IsYMDefect`), vanishing under strong `L²` curvature convergence.
* `higgs_defect` (`thm:higgs-defect`, `eq:H-defect`): `𝔖_H = 𝔎_H - λ g ν_H` (`IsHiggsDefect`,
  `IsKinDefect`, `potDefect`); `higgs_defect_einstein` (`eq:defect-Einstein`, composition with the
  finite metric equation); `higgs_defect_conserved` (conservation clause via
  `lem:defect-conservation-transport`).
* `zero_defect_characterization` (`thm:zero-defect-characterization`):
  `c(μ_{YM} + μ_{∇H} + ν_H) ≤ (𝔖_{YM} + 𝔖_H)(n, n) ≤ C(μ_{YM} + μ_{∇H} + ν_H)` and the equivalences
  `eq:complete-zero-defect-equivalence`; the pointwise algebra is in `BosonicStressAlgebra.lean`.
* `joint_defect_einstein` (`thm:joint-defect`, composition with the fermionic limit of
  `prop:weak-matter-equations` as an explicit hypothesis) and `independent_bosonic_certificates`
  (`cor:independent-bosonic-certificates`, composition with the conclusion of
  `prop:covariant-higgs-endpoint` as an explicit hypothesis).
* Non-vacuity: the full hypothesis packets of `zero_defect_characterization` and `ym_defect` are
  instantiated by the Minkowski metric with constant fields on a one-point chart.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace RenewalGeometry

namespace BosonicStressDefect

open BosonicStress QuadraticPacketDefect SignedMeasureWeakCompactness

/-! ## Continuous metric fields on the chart -/

section MetricFields

variable {K : Type*} [MetricSpace K] [CompactSpace K]

/-- A continuous metric field (component arrays `g_{μν}(x)`). -/
abbrev MetricField (K : Type*) [TopologicalSpace K] := C(K, Fin 4 → Fin 4 → ℝ)

/-- The component `g_{ij}` as a continuous function. -/
def entryF (g : MetricField K) (i j : Fin 4) : C(K, ℝ) :=
  ⟨fun x => g x i j, (continuous_apply j).comp ((continuous_apply i).comp g.continuous)⟩

/-- `det g` as a continuous function. -/
noncomputable def detF (g : MetricField K) : C(K, ℝ) :=
  ⟨fun x => (mat (g x)).det, continuous_det.comp g.continuous⟩

theorem continuous_adj (i j : Fin 4) :
    Continuous fun G : Fin 4 → Fin 4 → ℝ => (mat G).adjugate i j :=
  (continuous_apply j).comp ((continuous_apply i).comp
    (Continuous.matrix_adjugate (A := fun G : Fin 4 → Fin 4 → ℝ => mat G) continuous_id))

/-- The adjugate entries as continuous functions. -/
noncomputable def adjF (g : MetricField K) (i j : Fin 4) : C(K, ℝ) :=
  ⟨fun x => (mat (g x)).adjugate i j, (continuous_adj i j).comp g.continuous⟩

/-- The inverse-metric entries `g^{ij}`, computed in the Banach algebra `C(K, ℝ)`. -/
noncomputable def invF (g : MetricField K) (i j : Fin 4) : C(K, ℝ) :=
  Ring.inverse (detF g) * adjF g i j

/-- The volume density `√|det g|` as a continuous function. -/
noncomputable def volF (g : MetricField K) : C(K, ℝ) :=
  ⟨fun x => vol (g x), continuous_vol.comp g.continuous⟩

theorem volF_apply (g : MetricField K) (x : K) : volF g x = vol (g x) := rfl

theorem entryF_apply (g : MetricField K) (i j : Fin 4) (x : K) : entryF g i j x = g x i j := rfl

theorem invF_apply {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0) (i j : Fin 4) (x : K) :
    invF g i j x = ginv (g x) i j := by
  have hu : IsUnit (detF g) := (ContinuousMap.isUnit_iff_forall_ne_zero _).2 hdet
  have h1 : Ring.inverse (detF g) * detF g = 1 := Ring.inverse_mul_cancel _ hu
  have h2 : Ring.inverse (detF g) x * (mat (g x)).det = 1 := by
    have := congrArg (fun f : C(K, ℝ) => f x) h1
    simpa [detF] using this
  have h3 : Ring.inverse (detF g) x = ((mat (g x)).det)⁻¹ := eq_inv_of_mul_eq_one_left h2
  simp only [invF, ContinuousMap.mul_apply, h3, ginv, Matrix.inv_def, Matrix.smul_apply,
    smul_eq_mul, Ring.inverse_eq_inv']
  rfl

theorem tendsto_postcomp {β : Type*} [TopologicalSpace β] (Φ : C(Fin 4 → Fin 4 → ℝ, β))
    {g : ℕ → MetricField K} {g₀ : MetricField K} (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun h => Φ.comp (g h)) atTop (𝓝 (Φ.comp g₀)) :=
  ((ContinuousMap.continuous_postcomp Φ).tendsto g₀).comp hg

variable {g : ℕ → MetricField K} {g₀ : MetricField K}

theorem tendsto_entryF (hg : Tendsto g atTop (𝓝 g₀)) (i j : Fin 4) :
    Tendsto (fun h => entryF (g h) i j) atTop (𝓝 (entryF g₀ i j)) :=
  tendsto_postcomp ⟨fun G => G i j, (continuous_apply j).comp (continuous_apply i)⟩ hg

theorem tendsto_detF (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun h => detF (g h)) atTop (𝓝 (detF g₀)) :=
  tendsto_postcomp ⟨fun G => (mat G).det, continuous_det⟩ hg

theorem tendsto_adjF (hg : Tendsto g atTop (𝓝 g₀)) (i j : Fin 4) :
    Tendsto (fun h => adjF (g h) i j) atTop (𝓝 (adjF g₀ i j)) :=
  tendsto_postcomp ⟨fun G => (mat G).adjugate i j, continuous_adj i j⟩ hg

theorem tendsto_volF (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun h => volF (g h)) atTop (𝓝 (volF g₀)) :=
  tendsto_postcomp ⟨vol, continuous_vol⟩ hg

/-- Uniform convergence of the inverse metrics at a nondegenerate limit (continuity of inversion
at the unit `det g` of the Banach algebra `C(K, ℝ)`). -/
theorem tendsto_invF (hg : Tendsto g atTop (𝓝 g₀)) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (i j : Fin 4) : Tendsto (fun h => invF (g h) i j) atTop (𝓝 (invF g₀ i j)) := by
  have hu : IsUnit (detF g₀) := (ContinuousMap.isUnit_iff_forall_ne_zero _).2 hdet₀
  have hinv : Tendsto (fun h => Ring.inverse (detF (g h))) atTop (𝓝 (Ring.inverse (detF g₀))) := by
    have := NormedRing.inverse_continuousAt hu.unit
    rw [IsUnit.unit_spec] at this
    exact this.tendsto.comp (tendsto_detF hg)
  exact hinv.mul (tendsto_adjF hg i j)

/-- A nondegenerate continuous metric has volume density bounded below on the compact chart. -/
theorem exists_vol_lower (g₀ : MetricField K) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0) :
    ∃ c > 0, ∀ x, c ≤ vol (g₀ x) := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨1, one_pos, fun x => (IsEmpty.false x).elim⟩
  · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      (volF g₀).continuous.continuousOn
    exact ⟨vol (g₀ x₀), vol_pos (hdet₀ x₀), fun x => hx₀ (mem_univ x)⟩

/-- A continuous coefficient field from continuous entries. -/
def ofEntries {ι : Type*} (f : ι → ι → C(K, ℝ)) : C(K, ι → ι → ℝ) :=
  ⟨fun x i j => f i j x, continuous_pi fun i => continuous_pi fun j => (f i j).continuous⟩

theorem ofEntries_apply {ι : Type*} (f : ι → ι → C(K, ℝ)) (x : K) (i j : ι) :
    ofEntries f x i j = f i j x := rfl

theorem tendsto_ofEntries {ι : Type*} [Fintype ι] {f : ℕ → ι → ι → C(K, ℝ)}
    {f₀ : ι → ι → C(K, ℝ)} (hf : ∀ i j, Tendsto (fun h => f h i j) atTop (𝓝 (f₀ i j))) :
    Tendsto (fun h => ofEntries (f h)) atTop (𝓝 (ofEntries f₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun h => ∑ i, ∑ j, ‖f h i j - f₀ i j‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_iff_norm_sub_tendsto_zero.1 (hf i j)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => ?_) hs
  have h0 : 0 ≤ ∑ i, ∑ j, ‖f h i j - f₀ i j‖ := by positivity
  refine (ContinuousMap.norm_le _ h0).2 fun x => ?_
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  calc ‖(ofEntries (f h) - ofEntries f₀) x i j‖ = ‖(f h i j - f₀ i j) x‖ := rfl
    _ ≤ ‖f h i j - f₀ i j‖ := ContinuousMap.norm_coe_le_norm _ x
    _ ≤ ∑ j, ‖f h i j - f₀ i j‖ :=
        Finset.single_le_sum (f := fun j => ‖f h i j - f₀ i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ‖f h i j - f₀ i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖f h i j - f₀ i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem tendsto_const_field {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun h => ContinuousMap.const K (c h)) atTop (𝓝 (ContinuousMap.const K c₀)) :=
  (ContinuousMap.continuous_const'.tendsto c₀).comp hc

end MetricFields


/-! ## Stress coefficient fields -/

section Coefficients

variable {K : Type*} [MetricSpace K] [CompactSpace K]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Entries of the Yang–Mills stress coefficient field `vol_g · T^{YM}_{μν}` (as a quadratic form in
the realified curvature components). -/
noncomputable def ymEntry (g : MetricField K) (w : κ → ℝ) (μ ν : Fin 4)
    (p q : (Fin 4 × Fin 4) × κ) : C(K, ℝ) :=
  volF g * (((if p.1.1 = μ ∧ q.1.1 = ν then invF g p.1.2 q.1.2 else 0) -
    ContinuousMap.const K (1 / 4) * entryF g μ ν * (invF g p.1.1 q.1.1 * invF g p.1.2 q.1.2)) *
      ContinuousMap.const K (if p.2 = q.2 then w p.2 else 0))

/-- The Yang–Mills stress coefficient field. -/
noncomputable def ymCoefF (g : MetricField K) (w : κ → ℝ) (μ ν : Fin 4) :
    C(K, (Fin 4 × Fin 4) × κ → (Fin 4 × Fin 4) × κ → ℝ) :=
  ofEntries (ymEntry g w μ ν)

theorem ymCoefF_apply {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0) (w : κ → ℝ)
    (μ ν : Fin 4) (x : K) : ymCoefF g w μ ν x = ymCoef (g x) w (vol (g x)) μ ν := by
  funext p q
  simp only [ymCoefF, ofEntries_apply, ymEntry, ymCoef, diagCoef, ymBeta, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;>
    simp [ContinuousMap.mul_apply, ContinuousMap.sub_apply, volF_apply, entryF_apply,
      invF_apply hdet]

/-- Entries of the kinetic Higgs stress coefficient field `vol_g · T^{H,kin}_{μν}`. -/
noncomputable def kinEntry (g : MetricField K) (μ ν : Fin 4) (p q : Fin 4 × κ) : C(K, ℝ) :=
  volF g * (((if p.1 = μ ∧ q.1 = ν then ContinuousMap.const K 2 else 0) -
    entryF g μ ν * invF g p.1 q.1) * ContinuousMap.const K (if p.2 = q.2 then 1 else 0))

/-- The kinetic Higgs stress coefficient field. -/
noncomputable def kinCoefF (g : MetricField K) (μ ν : Fin 4) :
    C(K, Fin 4 × κ → Fin 4 × κ → ℝ) :=
  ofEntries (kinEntry g μ ν)

theorem kinCoefF_apply {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0) (μ ν : Fin 4)
    (x : K) : kinCoefF (κ := κ) g μ ν x = kinCoef (κ := κ) (g x) (vol (g x)) μ ν := by
  funext p q
  simp only [kinCoefF, ofEntries_apply, kinEntry, kinCoef, diagCoef, kinBeta, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;>
    simp [ContinuousMap.mul_apply, ContinuousMap.sub_apply, volF_apply, entryF_apply,
      invF_apply hdet]

variable {g : ℕ → MetricField K} {g₀ : MetricField K}

theorem tendsto_ymCoefF (hg : Tendsto g atTop (𝓝 g₀)) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {w : ℕ → κ → ℝ} {w₀ : κ → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (μ ν : Fin 4) :
    Tendsto (fun h => ymCoefF (g h) (w h) μ ν) atTop (𝓝 (ymCoefF g₀ w₀ μ ν)) := by
  refine tendsto_ofEntries fun p q => ?_
  refine (tendsto_volF hg).mul (Tendsto.mul (Tendsto.sub ?_ ?_) ?_)
  · split_ifs
    · exact tendsto_invF hg hdet₀ _ _
    · exact tendsto_const_nhds
  · exact (tendsto_const_nhds.mul (tendsto_entryF hg μ ν)).mul
      ((tendsto_invF hg hdet₀ _ _).mul (tendsto_invF hg hdet₀ _ _))
  · refine tendsto_const_field ?_
    split_ifs
    · exact hw _
    · exact tendsto_const_nhds

theorem tendsto_kinCoefF (hg : Tendsto g atTop (𝓝 g₀)) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (μ ν : Fin 4) :
    Tendsto (fun h => kinCoefF (κ := κ) (g h) μ ν) atTop (𝓝 (kinCoefF g₀ μ ν)) := by
  refine tendsto_ofEntries fun p q => ?_
  refine (tendsto_volF hg).mul (Tendsto.mul (Tendsto.sub tendsto_const_nhds ?_) tendsto_const_nhds)
  exact (tendsto_entryF hg μ ν).mul (tendsto_invF hg hdet₀ _ _)

end Coefficients

/-! ## Packets of realified fields -/

section Packets

variable {K : Type*} {κ : Type*}

/-- The realified curvature packet, indexed by `((μ, ν), a)`. -/
def Fp (F : Fin 4 → Fin 4 → κ → K → ℝ) : (Fin 4 × Fin 4) × κ → K → ℝ :=
  fun p x => F p.1.1 p.1.2 p.2 x

/-- The curvature components at a point. -/
def Fval (F : Fin 4 → Fin 4 → κ → K → ℝ) (x : K) : Fin 4 → Fin 4 → κ → ℝ :=
  fun α β a => F α β a x

/-- The realified covariant-gradient packet, indexed by `(μ, a)`. -/
def Yp (Y : Fin 4 → κ → K → ℝ) : Fin 4 × κ → K → ℝ := fun p x => Y p.1 p.2 x

/-- The covariant-gradient components at a point. -/
def Yval (Y : Fin 4 → κ → K → ℝ) (x : K) : Fin 4 → κ → ℝ := fun α a => Y α a x

theorem Fp_flat (F : Fin 4 → Fin 4 → κ → K → ℝ) (x : K) :
    (fun p => Fp F p x) = flat fun q : Fin 4 × Fin 4 => Fval F x q.1 q.2 := rfl

theorem Yp_flat (Y : Fin 4 → κ → K → ℝ) (x : K) : (fun p => Yp Y p x) = flat (Yval Y x) := rfl

end Packets

section Densities

variable {K : Type*} [MetricSpace K] [CompactSpace K]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem qf_ymCoefF {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0) (w : κ → ℝ)
    (F : Fin 4 → Fin 4 → κ → K → ℝ) (μ ν : Fin 4) (x : K) :
    qf (ymCoefF g w μ ν x) (fun p => Fp F p x) = ymStress (g x) w (Fval F x) μ ν * vol (g x) := by
  rw [ymCoefF_apply hdet, Fp_flat, qf_ymCoef, mul_comm]

theorem qf_kinCoefF {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0)
    (Y : Fin 4 → κ → K → ℝ) (μ ν : Fin 4) (x : K) :
    qf (kinCoefF g μ ν x) (fun p => Yp Y p x) = higgsKin (g x) (Yval Y x) μ ν * vol (g x) := by
  rw [kinCoefF_apply hdet, Yp_flat, qf_kinCoef, mul_comm]

theorem ginv_symm {G : Fin 4 → Fin 4 → ℝ} (hG : ∀ μ ν, G μ ν = G ν μ) (μ ν : Fin 4) :
    ginv G μ ν = ginv G ν μ := by
  have hT : Matrix.transpose (mat G) = mat G := by ext i j; simp [hG]
  have : Matrix.transpose ((mat G)⁻¹) = (mat G)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  simp only [ginv]
  conv_lhs => rw [← this]
  rfl

theorem ymStress_symm {G : Fin 4 → Fin 4 → ℝ} (hG : ∀ μ ν, G μ ν = G ν μ) (w : κ → ℝ)
    (F : Fin 4 → Fin 4 → κ → ℝ) (μ ν : Fin 4) : ymStress G w F μ ν = ymStress G w F ν μ := by
  simp only [ymStress, hG μ ν]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [ginv_symm hG]
  simp only [lieIp]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

theorem higgsKin_symm {G : Fin 4 → Fin 4 → ℝ} (hG : ∀ μ ν, G μ ν = G ν μ)
    (Y : Fin 4 → κ → ℝ) (μ ν : Fin 4) : higgsKin G Y μ ν = higgsKin G Y ν μ := by
  simp only [higgsKin, hG μ ν, mul_comm (Y μ _)]

end Densities

/-! ## `prop:YM-defect` -/

section YM

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable (V₀ : Measure K) [IsFiniteMeasure V₀]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure V₀] [DecidableEq κ] in
theorem StrongL2.comp {ι : Type*} {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ}
    (hs : StrongL2 V₀ Y Y₀) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    StrongL2 V₀ (fun h => Y (σ h)) Y₀ :=
  fun i => (hs i).comp hσ.tendsto_atTop

/-- The defect relation `T^{YM}_h dV_{g_h} ⇀* T^{YM} dV_g + 𝔖_{YM}` along `σ`. -/
def IsYMDefect (g : ℕ → MetricField K) (g₀ : MetricField K) (w : ℕ → κ → ℝ) (w₀ : κ → ℝ)
    (F : ℕ → Fin 4 → Fin 4 → κ → K → ℝ) (F₀ : Fin 4 → Fin 4 → κ → K → ℝ) (σ : ℕ → ℕ)
    (S : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) : Prop :=
  ∀ μ ν (φ : C(K, ℝ)), Tendsto (fun h => ∫ x, φ x *
      (ymStress (g (σ h) x) (w (σ h)) (Fval (F (σ h)) x) μ ν * vol (g (σ h) x)) ∂V₀) atTop
    (𝓝 (∫ x, φ x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀ + S μ ν φ))

variable {V₀}
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {w : ℕ → κ → ℝ} {w₀ : κ → ℝ}
  {F : ℕ → Fin 4 → Fin 4 → κ → K → ℝ} {F₀ : Fin 4 → Fin 4 → κ → K → ℝ}

/-- The Yang–Mills stress defect is the contraction of the curvature covariance measure with the
limiting stress coefficients: for any extraction along which the curvature packet has the matrix
defect `𝖰_F`, `𝔖_{YM,μν} = B^{μν}_{YM} : 𝖰_F`. -/
theorem isYMDefect_of_isDefect (hg : Tendsto g atTop (𝓝 g₀)) (hdet : ∀ h x, (mat (g h x)).det ≠ 0)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0) (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {Q : StrongDual ℝ C(K, (Fin 4 × Fin 4) × κ → (Fin 4 × Fin 4) × κ → ℝ)}
    (hQ : IsDefect V₀ (fun h => Fp (F (σ h))) (Fp F₀) Q) :
    IsYMDefect V₀ g g₀ w w₀ F F₀ σ fun μ ν => contract Q (ymCoefF g₀ w₀ μ ν) := by
  intro μ ν φ
  have hB : Tendsto (fun h => ymCoefF (g (σ h)) (w (σ h)) μ ν) atTop (𝓝 (ymCoefF g₀ w₀ μ ν)) :=
    (tendsto_ymCoefF hg hdet₀ hw μ ν).comp hσ.tendsto_atTop
  have := hQ.tendsto_contract (hF.comp hσ) hB φ
  simp only [qf_ymCoefF (hdet _), qf_ymCoefF hdet₀] at this
  exact this

/-- **`prop:YM-defect`**: on a compact chart, let continuous metrics `g_h → g` uniformly
(nondegenerate, symmetric), let the Lie-metric weights converge, and let the curvatures converge
weakly in `L²`, `F_{A_h} ⇀ F_A`.  After extraction there is a symmetric tensor-valued finite Radon
measure `𝔖_{YM}` with `T^{YM}_h dV_{g_h} ⇀* T^{YM} dV_g + 𝔖_{YM}` (`eq:YM-defect`), and strong `L²`
convergence of the curvatures gives `𝔖_{YM} = 0`.  No hypothesis on the connections `A_h` enters. -/
theorem ym_defect (hg : Tendsto g atTop (𝓝 g₀)) (hdet : ∀ h x, (mat (g h x)).det ≠ 0)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0) (hsym : ∀ h x μ ν, g h x μ ν = g h x ν μ)
    (hsym₀ : ∀ x μ ν, g₀ x μ ν = g₀ x ν μ)
    (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ S : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ S ∧ (∀ μ ν, S μ ν = S ν μ) ∧
      (StrongL2 V₀ (fun h => Fp (F h)) (Fp F₀) → ∀ μ ν, S μ ν = 0) := by
  obtain ⟨σ, hσ, Q, hQ⟩ := exists_isDefect hF
  have hS := isYMDefect_of_isDefect hg hdet hdet₀ hw hF hσ hQ
  refine ⟨σ, hσ, _, hS, fun μ ν => ?_, fun hs μ ν => ?_⟩
  · ext φ
    have h1 := hS μ ν φ
    have h2 := hS ν μ φ
    have e1 : (fun h => ∫ x, φ x * (ymStress (g (σ h) x) (w (σ h)) (Fval (F (σ h)) x) ν μ *
        vol (g (σ h) x)) ∂V₀) = fun h => ∫ x, φ x * (ymStress (g (σ h) x) (w (σ h))
          (Fval (F (σ h)) x) μ ν * vol (g (σ h) x)) ∂V₀ := by
      funext h; congr 1; funext x; rw [ymStress_symm (hsym _ _)]
    have e2 : ∫ x, φ x * (ymStress (g₀ x) w₀ (Fval F₀ x) ν μ * vol (g₀ x)) ∂V₀ =
        ∫ x, φ x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀ := by
      congr 1; funext x; rw [ymStress_symm (hsym₀ _)]
    rw [e1, e2] at h2
    have := tendsto_nhds_unique h1 h2
    linarith
  · have hQ0 := hQ.eq_zero_of_strongL2 (hF.comp hσ) (StrongL2.comp _ hs hσ)
    rw [hQ0]
    rfl

end YM

/-! ## `Lᵖ` helpers -/

section LpHelpers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

theorem rpow_four_eq (r : ℝ) : r ^ ((4 : ℝ≥0∞).toReal) = r ^ 4 := by
  rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem memLp_of_eLpNorm_le {p : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) {C : ℝ≥0}
    (hC : eLpNorm f p μ ≤ C) : MemLp f p μ :=
  ⟨hf, hC.trans_lt ENNReal.coe_lt_top⟩

/-- `∫ ‖f‖⁴ = ‖f‖_{L⁴}⁴`. -/
theorem integral_norm_pow_four_eq {f : α → E} (hf : MemLp f 4 μ) :
    ∫ x, ‖f x‖ ^ 4 ∂μ = (eLpNorm f 4 μ).toReal ^ 4 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ ((4 : ℝ≥0∞).toReal) ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  simp only [rpow_four_eq] at hI ⊢
  rw [show ((4 : ℝ≥0∞).toReal)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.rpow_inv_natCast_pow hI
    (by norm_num)]

/-- An `L⁴` bound `‖f‖_{L⁴} ≤ C` gives `∫ ‖f‖⁴ ≤ C⁴`. -/
theorem integral_norm_pow_four_le {f : α → E} (hf : AEStronglyMeasurable f μ) {C : ℝ≥0}
    (hC : eLpNorm f 4 μ ≤ C) : ∫ x, ‖f x‖ ^ 4 ∂μ ≤ (C : ℝ) ^ 4 := by
  rw [integral_norm_pow_four_eq (memLp_of_eLpNorm_le hf hC)]
  refine pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 4
  have := ENNReal.toReal_mono ENNReal.coe_ne_top hC
  simpa using this

theorem integrable_norm_pow_four {f : α → E} (hf : MemLp f 4 μ) :
    Integrable (fun x => ‖f x‖ ^ 4) μ :=
  hf.integrable_norm_pow (p := 4) (by norm_num)

/-- `‖ ‖f‖² ‖_{L²} = ‖f‖_{L⁴}²`-type bound: an `L⁴` bound `C` gives the `L²` bound `C²` for `‖f‖²`. -/
theorem eLpNorm_norm_sq_le {f : α → E} {C : ℝ≥0} (hC : eLpNorm f 4 μ ≤ C) :
    eLpNorm (fun x => ‖f x‖ ^ 2) 2 μ ≤ ((C ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have e : (fun x => ‖f x‖ ^ 2) = fun x => ‖f x‖ ^ (2 : ℝ) := by
    funext x; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e, eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 2)]
  have h4 : (2 : ℝ≥0∞) * ENNReal.ofReal 2 = 4 := by
    rw [ENNReal.ofReal_ofNat]; norm_num
  rw [h4]
  calc eLpNorm f 4 μ ^ (2 : ℝ) ≤ (C : ℝ≥0∞) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hC (by norm_num)
    _ = ((C ^ 2 : ℝ≥0) : ℝ≥0∞) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]; push_cast; rfl

/-- An `L⁴` bound `C` gives the `L^{4/3}` bound `C³` for the cubic `‖f‖² f`. -/
theorem eLpNorm_cubic_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E}
    {C : ℝ≥0} (hC : eLpNorm f 4 μ ≤ C) :
    eLpNorm (fun x => ‖f x‖ ^ 2 • f x) (4 / 3) μ ≤ ((C ^ 3 : ℝ≥0) : ℝ≥0∞) := by
  have e : eLpNorm (fun x => ‖f x‖ ^ 2 • f x) (4 / 3) μ =
      eLpNorm (fun x => ‖f x‖ ^ (3 : ℝ)) (4 / 3) μ := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_pow, norm_norm, Real.norm_of_nonneg (by positivity),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [e, eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 3)]
  have h4 : (4 / 3 : ℝ≥0∞) * ENNReal.ofReal 3 = 4 := by
    rw [ENNReal.ofReal_ofNat]; exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  rw [h4]
  calc eLpNorm f 4 μ ^ (3 : ℝ) ≤ (C : ℝ≥0∞) ^ (3 : ℝ) := ENNReal.rpow_le_rpow hC (by norm_num)
    _ = ((C ^ 3 : ℝ≥0) : ℝ≥0∞) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]; push_cast; rfl

theorem one_lt_four_thirds : (1 : ℝ≥0∞) < 4 / 3 := by
  rw [ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num)]; norm_num

/-- `(a + b)² ≤ (1 + δ) a² + (1 + 1/δ) b²`. -/
theorem add_sq_le_weighted (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (A + B) ^ 2 ≤ (1 + δ) * A ^ 2 + (1 + 1 / δ) * B ^ 2 := by
  have key : 2 * A * B ≤ δ * A ^ 2 + B ^ 2 / δ := by
    rw [← sub_nonneg]
    have : δ * A ^ 2 + B ^ 2 / δ - 2 * A * B = (δ * A - B) ^ 2 / δ := by
      field_simp; ring
    rw [this]; positivity
  have e1 : (1 + 1 / δ) * B ^ 2 = B ^ 2 + B ^ 2 / δ := by ring
  have e2 : (A + B) ^ 2 = A ^ 2 + 2 * A * B + B ^ 2 := by ring
  rw [e1, e2]
  linarith

/-- `‖a‖⁴ ≤ (1 + δ)³ ‖b‖⁴ + (1 + 1/δ)³ ‖a - b‖⁴`. -/
theorem norm_pow_four_le_weighted {E : Type*} [NormedAddCommGroup E] (a b : E) {δ : ℝ}
    (hδ : 0 < δ) : ‖a‖ ^ 4 ≤ (1 + δ) ^ 3 * ‖b‖ ^ 4 + (1 + 1 / δ) ^ 3 * ‖a - b‖ ^ 4 := by
  set x := ‖b‖
  set y := ‖a - b‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have htri : ‖a‖ ≤ x + y := by
    calc ‖a‖ = ‖b + (a - b)‖ := by rw [add_sub_cancel]
      _ ≤ x + y := norm_add_le _ _
  have h1 : ‖a‖ ^ 4 ≤ ((x + y) ^ 2) ^ 2 := by
    rw [← pow_mul]; exact pow_le_pow_left₀ (norm_nonneg _) htri 4
  have h2 := add_sq_le_weighted x y hδ
  have h3 : ((x + y) ^ 2) ^ 2 ≤ ((1 + δ) * x ^ 2 + (1 + 1 / δ) * y ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h2 2
  have h4 := add_sq_le_weighted ((1 + δ) * x ^ 2) ((1 + 1 / δ) * y ^ 2) hδ
  calc ‖a‖ ^ 4 ≤ ((1 + δ) * x ^ 2 + (1 + 1 / δ) * y ^ 2) ^ 2 := h1.trans h3
    _ ≤ (1 + δ) * ((1 + δ) * x ^ 2) ^ 2 + (1 + 1 / δ) * ((1 + 1 / δ) * y ^ 2) ^ 2 := h4
    _ = (1 + δ) ^ 3 * x ^ 4 + (1 + 1 / δ) ^ 3 * y ^ 4 := by ring

end LpHelpers

/-! ## `lem:critical-cubic`: cubic Euler terms and the covariant gradient -/

section Cubic

instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  have h := holderTriple_ofReal (p := 4) (q := 4) (r := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [ENNReal.ofReal_ofNat] using h

instance holderTriple_four_two : ENNReal.HolderTriple 4 2 (4 / 3) := by
  have h := holderTriple_ofReal (p := 4) (q := 2) (r := 4 / 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at h
  simpa [ENNReal.ofReal_ofNat] using h

variable {K : Type*} [MeasurableSpace K] {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`lem:critical-cubic`, cubic Euler term**: an `L⁴`-bounded, a.e. convergent Higgs sequence has
`|H_h|² H_h ⇀ |H|² H` weakly in `L^{4/3}` (tested on `L⁴`). -/
theorem cubic_weak {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) {v : K → E} (hv : MemLp v 4 V₀) :
    Tendsto (fun h => ∫ x, ⟪v x, ‖H h x‖ ^ 2 • H h x⟫ ∂V₀) atTop
      (𝓝 (∫ x, ⟪v x, ‖H₀ x‖ ^ 2 • H₀ x⟫ ∂V₀)) :=
  tendsto_integral_inner_of_ae (p := 4 / 3) (q := 4) one_lt_four_thirds
    (fun h => ((hHm h).norm.pow 2).smul (hHm h))
    (hae.mono fun x hx => (hx.norm.pow 2).smul hx) (C := C ^ 3)
    (fun h => eLpNorm_cubic_le (hL4 h)) hv

/-- The covariant derivative `D_μ H = ∂_μ H + ρ(A_μ) H` (the connection acting through operator
fields `A_μ(x) = ρ_H(A_μ(x))`). -/
def covD (dH : Fin 4 → K → E) (A : Fin 4 → K → E →L[ℝ] E) (H : K → E) (μ : Fin 4) (x : K) : E :=
  dH μ x + A μ x (H x)

theorem memLp_apply {A : K → E →L[ℝ] E} (hA : MemLp A 4 V₀) {H : K → E} (hH : MemLp H 4 V₀) :
    MemLp (fun x => A x (H x)) 2 V₀ := by
  refine ⟨Continuous.comp_aestronglyMeasurable₂ (g := fun (T : E →L[ℝ] E) (y : E) => T y)
    (continuous_fst.clm_apply continuous_snd) hA.1 hH.1, ?_⟩
  refine (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 4) (r := 2) hA.1 hH.1
    (fun T y => T y) 1 (Eventually.of_forall fun x => by
      simpa using (A x).le_opNNNorm (H x))).trans_lt ?_
  simpa using ENNReal.mul_lt_top hA.2 hH.2

theorem eLpNorm_apply_le {A : K → E →L[ℝ] E} (hA : AEStronglyMeasurable A V₀) {H : K → E}
    (hH : AEStronglyMeasurable H V₀) :
    eLpNorm (fun x => A x (H x)) 2 V₀ ≤ eLpNorm A 4 V₀ * eLpNorm H 4 V₀ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 4) (r := 2) hA hH
    (fun T y => T y) 1 (Eventually.of_forall fun x => by simpa using (A x).le_opNNNorm (H x))
  simpa using this

theorem abs_integral_le_eLpNorm_one {f : K → ℝ} (hf : AEStronglyMeasurable f V₀) :
    |∫ x, f x ∂V₀| ≤ (eLpNorm f 1 V₀).toReal := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [integral_norm_eq_lintegral_enorm hf, eLpNorm_one_eq_lintegral_enorm]

variable [FiniteDimensional ℝ E]

/-- **`lem:critical-cubic`, covariant gradient**: if `H_h ⇀ H` with `H_h → H` a.e. and bounded in
`L⁴`, the weak derivatives converge weakly in `L²`, and `A_h → A` strongly in `L⁴`, then
`D_{A_h} H_h ⇀ D_A H` weakly in `L²`:
`A_h H_h - A H = (A_h - A) H_h + A (H_h - H)`, the first term tends to zero in `L²` and the second
pairs with `A* v ∈ L^{4/3}` against the weak `L⁴` convergence of `H_h`. -/
theorem covD_weak {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {dH : ℕ → Fin 4 → K → E} {dH₀ : Fin 4 → K → E} (hdH : ∀ h μ, MemLp (dH h μ) 2 V₀)
    (hdH₀ : ∀ μ, MemLp (dH₀ μ) 2 V₀)
    (hdHw : ∀ μ (v : K → E), MemLp v 2 V₀ →
      Tendsto (fun h => ∫ x, ⟪v x, dH h μ x⟫ ∂V₀) atTop (𝓝 (∫ x, ⟪v x, dH₀ μ x⟫ ∂V₀)))
    {A : ℕ → Fin 4 → K → E →L[ℝ] E} {A₀ : Fin 4 → K → E →L[ℝ] E}
    (hA : ∀ h μ, MemLp (A h μ) 4 V₀) (hA₀ : ∀ μ, MemLp (A₀ μ) 4 V₀)
    (hAc : ∀ μ, Tendsto (fun h => eLpNorm (fun x => A h μ x - A₀ μ x) 4 V₀) atTop (𝓝 0))
    (μ : Fin 4) {v : K → E} (hv : MemLp v 2 V₀) :
    Tendsto (fun h => ∫ x, ⟪v x, covD (dH h) (A h) (H h) μ x⟫ ∂V₀) atTop
      (𝓝 (∫ x, ⟪v x, covD dH₀ A₀ H₀ μ x⟫ ∂V₀)) := by
  obtain ⟨hH₀, hH₀C⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  have hint : ∀ {w : K → E}, MemLp w 2 V₀ → Integrable (fun x => ⟪v x, w x⟫) V₀ := by
    intro w hw
    refine memLp_one_iff_integrable.1 ⟨hv.1.inner hw.1, ?_⟩
    exact (eLpNorm_inner_le (p := 2) (q := 2) hv.1 hw.1).trans_lt (ENNReal.mul_lt_top hv.2 hw.2)
  have hsplit : ∀ (dG : Fin 4 → K → E) (B : Fin 4 → K → E →L[ℝ] E) (G : K → E),
      MemLp (dG μ) 2 V₀ → MemLp (B μ) 4 V₀ → MemLp G 4 V₀ →
      ∫ x, ⟪v x, covD dG B G μ x⟫ ∂V₀ =
        ∫ x, ⟪v x, dG μ x⟫ ∂V₀ + ∫ x, ⟪v x, B μ x (G x)⟫ ∂V₀ := by
    intro dG B G h1 h2 h3
    rw [← integral_add (hint h1) (hint (memLp_apply h2 h3))]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [covD, inner_add_right])
  simp only [hsplit _ _ _ (hdH _ μ) (hA _ μ) (hH _), hsplit _ _ _ (hdH₀ μ) (hA₀ μ) hH₀]
  refine (hdHw μ v hv).add ?_
  -- the connection term
  have hd : ∀ h, MemLp (fun x => A h μ x - A₀ μ x) 4 V₀ := fun h => (hA h μ).sub (hA₀ μ)
  -- first piece: `(A_h - A) H_h → 0` in `L²`
  have hT1 : Tendsto (fun h => ∫ x, ⟪v x, (A h μ x - A₀ μ x) (H h x)⟫ ∂V₀) atTop (𝓝 0) := by
    have hbound : ∀ h, |∫ x, ⟪v x, (A h μ x - A₀ μ x) (H h x)⟫ ∂V₀| ≤
        (eLpNorm v 2 V₀ * (eLpNorm (fun x => A h μ x - A₀ μ x) 4 V₀ * C)).toReal := by
      intro h
      have hm : AEStronglyMeasurable (fun x => (A h μ x - A₀ μ x) (H h x)) V₀ :=
        (memLp_apply (hd h) (hH h)).1
      refine (abs_integral_le_eLpNorm_one (hv.1.inner hm)).trans ?_
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top hv.2.ne
        (ENNReal.mul_ne_top (hd h).2.ne ENNReal.coe_ne_top)) ?_
      refine (eLpNorm_inner_le (p := 2) (q := 2) hv.1 hm).trans ?_
      gcongr
      exact (eLpNorm_apply_le (hd h).1 (hHm h)).trans (by gcongr; exact hL4 h)
    have hlim : Tendsto (fun h => (eLpNorm v 2 V₀ *
        (eLpNorm (fun x => A h μ x - A₀ μ x) 4 V₀ * C)).toReal) atTop (𝓝 0) := by
      have h1 : Tendsto (fun h => eLpNorm v 2 V₀ *
          (eLpNorm (fun x => A h μ x - A₀ μ x) 4 V₀ * C)) atTop (𝓝 (eLpNorm v 2 V₀ * (0 * C))) :=
        ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const (hAc μ) (Or.inr ENNReal.coe_ne_top))
          (Or.inr hv.2.ne)
      rw [zero_mul, mul_zero] at h1
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    exact squeeze_zero_norm (fun h => by rw [Real.norm_eq_abs]; exact hbound h) hlim
  -- second piece: `A (H_h - H)` against `A* v ∈ L^{4/3}`
  set w : K → E := fun x => ContinuousLinearMap.adjoint (A₀ μ x) (v x)
  have hwm : AEStronglyMeasurable w V₀ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (T : E →L[ℝ] E) (y : E) =>
      ContinuousLinearMap.adjoint T y)
      ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_apply continuous_snd)
      (hA₀ μ).1 hv.1
  have hw : MemLp w (4 / 3) V₀ := by
    refine ⟨hwm, ?_⟩
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 2) (r := 4 / 3) (hA₀ μ).1 hv.1
      (fun T y => ContinuousLinearMap.adjoint T y) 1 (Eventually.of_forall fun x => by
        simpa using (ContinuousLinearMap.adjoint (A₀ μ x)).le_opNNNorm (v x))
    simp only [ENNReal.coe_one, one_mul] at this
    exact this.trans_lt (ENNReal.mul_lt_top (hA₀ μ).2 hv.2)
  have hT2 : Tendsto (fun h => ∫ x, ⟪w x, H h x⟫ ∂V₀) atTop (𝓝 (∫ x, ⟪w x, H₀ x⟫ ∂V₀)) :=
    tendsto_integral_inner_of_ae (p := 4) (q := 4 / 3) (by norm_num) hHm hae hL4 hw
  have hadj : ∀ (G : K → E) x, ⟪v x, A₀ μ x (G x)⟫ = ⟪w x, G x⟫ := fun G x =>
    (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  have hsum := hT1.add hT2
  rw [zero_add] at hsum
  have e₀ : ∫ x, ⟪w x, H₀ x⟫ ∂V₀ = ∫ x, ⟪v x, A₀ μ x (H₀ x)⟫ ∂V₀ :=
    integral_congr_ae (Eventually.of_forall fun x => (hadj H₀ x).symm)
  rw [e₀] at hsum
  refine hsum.congr fun h => ?_
  have i1 : Integrable (fun x => ⟪v x, (A h μ x - A₀ μ x) (H h x)⟫) V₀ :=
    hint (memLp_apply (hd h) (hH h))
  have i2 : Integrable (fun x => ⟪w x, H h x⟫) V₀ := by
    refine (hint (memLp_apply (hA₀ μ) (hH h))).congr (Eventually.of_forall fun x => ?_)
    exact hadj (H h) x
  rw [← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [sub_apply, inner_sub_right, ← hadj (H h) x]
  ring

end Cubic

/-! ## `lem:critical-cubic`: the quartic concentration measure -/

section Quartic

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable (V₀ : Measure K) [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quartic defect relation `|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H` (`eq:quartic-defect`) along
`σ`. -/
def IsQuarticDefect (g : ℕ → MetricField K) (g₀ : MetricField K) (H : ℕ → K → E) (H₀ : K → E)
    (σ : ℕ → ℕ) (ν : StrongDual ℝ C(K, ℝ)) : Prop :=
  ∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)) ∂V₀) atTop
    (𝓝 (∫ x, φ x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) ∂V₀ + ν φ))

variable {V₀}
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {H : ℕ → K → E} {H₀ : K → E}

theorem volF_bounded (hg : Tendsto g atTop (𝓝 g₀)) : ∃ R, ∀ h, ‖volF (g h)‖ ≤ R := by
  obtain ⟨R, hR⟩ := (tendsto_volF hg).norm.bddAbove_range
  exact ⟨R, fun h => hR ⟨h, rfl⟩⟩

theorem integrable_quartic {f : K → E} (hf : MemLp f 4 V₀) (c : C(K, ℝ)) :
    Integrable (fun x => ‖f x‖ ^ 4 * c x) V₀ := by
  have := (integrable_norm_pow_four hf).bdd_mul (c := ‖c‖) c.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => c.norm_coe_le_norm x)
  simpa [mul_comm] using this

/-- Replacement of `vol_{g_h}` by `vol_g` in the quartic densities. -/
theorem tendsto_quartic_vol (hg : Tendsto g atTop (𝓝 g₀)) (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    {C : ℝ≥0} (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, φ x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)) ∂V₀ -
      ∫ x, φ x * (‖H (σ h) x‖ ^ 4 * vol (g₀ x)) ∂V₀) atTop (𝓝 0) := by
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  have hv : Tendsto (fun h => volF (g (σ h))) atTop (𝓝 (volF g₀)) :=
    (tendsto_volF hg).comp hσ.tendsto_atTop
  have hd : Tendsto (fun h => ‖φ * (volF (g (σ h)) - volF g₀)‖) atTop (𝓝 0) := by
    have : Tendsto (fun h => φ * (volF (g (σ h)) - volF g₀)) atTop (𝓝 (φ * (volF g₀ - volF g₀))) :=
      tendsto_const_nhds.mul (hv.sub tendsto_const_nhds)
    rw [sub_self, mul_zero] at this
    simpa using this.norm
  refine squeeze_zero_norm (fun h => ?_) (by simpa using hd.mul_const ((C : ℝ) ^ 4))
  have i1 := integrable_mul_density V₀ φ (integrable_quartic (hH (σ h)) (volF (g (σ h))))
  have i2 := integrable_mul_density V₀ φ (integrable_quartic (hH (σ h)) (volF g₀))
  simp only [volF_apply] at i1 i2
  rw [← integral_sub i1 i2, Real.norm_eq_abs]
  have e : (fun x => φ x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)) -
      φ x * (‖H (σ h) x‖ ^ 4 * vol (g₀ x))) =
      fun x => (φ * (volF (g (σ h)) - volF g₀)) x * ‖H (σ h) x‖ ^ 4 := by
    funext x; simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, volF_apply]; ring
  rw [e]
  refine (abs_integral_mul_le V₀ _ (integrable_norm_pow_four (hH (σ h)))).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have : ∫ x, |‖H (σ h) x‖ ^ 4| ∂V₀ = ∫ x, ‖H (σ h) x‖ ^ 4 ∂V₀ :=
    integral_congr_ae (Eventually.of_forall fun x => abs_of_nonneg (by positivity))
  rw [this]
  exact integral_norm_pow_four_le (hHm _) (hL4 _)

/-- The weak `L⁴` test against `ψ |H|² H`. -/
theorem tendsto_quartic_cross (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) (ψ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, ψ x * (‖H₀ x‖ ^ 2 * ⟪H₀ x, H h x⟫) ∂V₀) atTop
      (𝓝 (∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀)) := by
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hv := memLp_weight_norm_sq_smul hH₀ ψ.continuous.aestronglyMeasurable (c := ‖ψ‖)
    fun x => (Real.norm_eq_abs _) ▸ ψ.norm_coe_le_norm x
  have := tendsto_integral_inner_of_ae (p := 4) (q := 4 / 3) (by norm_num) hHm hae hL4 hv
  have e : ∀ (a : E) x, ⟪ψ x • (‖H₀ x‖ ^ 2 • H₀ x), a⟫ = ψ x * (‖H₀ x‖ ^ 2 * ⟪H₀ x, a⟫) := by
    intro a x; rw [real_inner_smul_left, real_inner_smul_left]
  simp only [e] at this
  convert this using 2
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [real_inner_self_eq_norm_sq]
  ring

theorem integrable_quartic_cross {f : K → E} (hf : MemLp f 4 V₀) (hH₀ : MemLp H₀ 4 V₀)
    (ψ : C(K, ℝ)) : Integrable (fun x => ψ x * (‖H₀ x‖ ^ 2 * ⟪H₀ x, f x⟫)) V₀ := by
  have hv := memLp_weight_norm_sq_smul hH₀ ψ.continuous.aestronglyMeasurable (c := ‖ψ‖)
    fun x => (Real.norm_eq_abs _) ▸ ψ.norm_coe_le_norm x
  have hi : Integrable (fun x => ⟪ψ x • (‖H₀ x‖ ^ 2 • H₀ x), f x⟫) V₀ :=
    memLp_one_iff_integrable.1 ⟨hv.1.inner hf.1, (eLpNorm_inner_le (p := 4) (q := 4 / 3)
      hv.1 hf.1).trans_lt (ENNReal.mul_lt_top hv.2 hf.2)⟩
  refine hi.congr (Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_left]

/-- **Positivity of the quartic defect** (`ν_H ≥ 0`): weak lower semicontinuity of the `L⁴`
energy through the convexity bound `‖a‖⁴ ≥ 4 ‖b‖²⟪b, a⟫ - 3 ‖b‖⁴`. -/
theorem quartic_defect_nonneg (hg : Tendsto g atTop (𝓝 g₀))
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {ν : StrongDual ℝ C(K, ℝ)} (hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν) {φ : C(K, ℝ)}
    (hφ : ∀ x, 0 ≤ φ x) : 0 ≤ ν φ := by
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  set ψ : C(K, ℝ) := φ * volF g₀
  have hψ : ∀ x, 0 ≤ ψ x := fun x => mul_nonneg (hφ x) (vol_nonneg _)
  -- `∫ ψ |H_{σh}|⁴ → ∫ ψ |H|⁴ + ν φ`
  have h1 : Tendsto (fun h => ∫ x, ψ x * ‖H (σ h) x‖ ^ 4 ∂V₀) atTop
      (𝓝 (∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀ + ν φ)) := by
    have := (hν φ).sub (tendsto_quartic_vol hg hHm hL4 hσ φ)
    rw [sub_zero] at this
    have e0 : ∫ x, φ x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) ∂V₀ = ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀ :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [ψ, ContinuousMap.mul_apply, volF_apply]; ring)
    rw [e0] at this
    refine this.congr fun h => ?_
    simp only [sub_sub_cancel]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only [ψ, ContinuousMap.mul_apply, volF_apply]; ring)
  -- lower bound sequence
  have h2 : Tendsto (fun h => 4 * ∫ x, ψ x * (‖H₀ x‖ ^ 2 * ⟪H₀ x, H (σ h) x⟫) ∂V₀ -
      3 * ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀) atTop
      (𝓝 (4 * ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀ - 3 * ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀)) :=
    (((tendsto_quartic_cross hHm hae hL4 ψ).comp hσ.tendsto_atTop).const_mul 4).sub_const _
  have hle : ∀ h, 4 * ∫ x, ψ x * (‖H₀ x‖ ^ 2 * ⟪H₀ x, H (σ h) x⟫) ∂V₀ -
      3 * ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀ ≤ ∫ x, ψ x * ‖H (σ h) x‖ ^ 4 ∂V₀ := by
    intro h
    have i1 := integrable_quartic_cross (hH (σ h)) hH₀ ψ
    have i2 := integrable_mul_density V₀ ψ (integrable_norm_pow_four hH₀)
    have i3 := integrable_mul_density V₀ ψ (integrable_norm_pow_four (hH (σ h)))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (i1.const_mul 4)
      (i2.const_mul 3)]
    refine integral_mono ((i1.const_mul 4).sub (i2.const_mul 3)) i3 fun x => ?_
    have := mul_le_mul_of_nonneg_left (four_mul_inner_le (H (σ h) x) (H₀ x)) (hψ x)
    simp only
    nlinarith
  have := le_of_tendsto_of_tendsto' h2 h1 hle
  linarith

end Quartic

section Quartic2

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {H : ℕ → K → E} {H₀ : K → E}

/-- The quartic defect seen through the limiting volume: `∫ φ vol_g |H_{σh}|⁴ → ∫ φ vol_g |H|⁴ + ν φ`. -/
theorem IsQuarticDefect.tendsto_weighted (hg : Tendsto g atTop (𝓝 g₀))
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀) {C : ℝ≥0} (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {ν : StrongDual ℝ C(K, ℝ)}
    (hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν) (φ : C(K, ℝ)) :
    Tendsto (fun h => ∫ x, (φ * volF g₀) x * ‖H (σ h) x‖ ^ 4 ∂V₀) atTop
      (𝓝 (∫ x, (φ * volF g₀) x * ‖H₀ x‖ ^ 4 ∂V₀ + ν φ)) := by
  have := (hν φ).sub (tendsto_quartic_vol hg hHm hL4 hσ φ)
  rw [sub_zero] at this
  have e0 : ∫ x, φ x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) ∂V₀ = ∫ x, (φ * volF g₀) x * ‖H₀ x‖ ^ 4 ∂V₀ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only [ContinuousMap.mul_apply, volF_apply]; ring)
  rw [e0] at this
  refine this.congr fun h => ?_
  simp only [sub_sub_cancel]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp only [ContinuousMap.mul_apply, volF_apply]; ring)

/-- `ν_H = 0` forces strong `L⁴` convergence (Radon–Riesz / uniform convexity of `L⁴`, with the
limiting volume bounded below). -/
theorem quartic_strong_of_zero (hg : Tendsto g atTop (𝓝 g₀)) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {ν : StrongDual ℝ C(K, ℝ)} (hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν) (h0 : ν 1 = 0) :
    Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) := by
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  obtain ⟨c, hc, hvol⟩ := exists_vol_lower g₀ hdet₀
  have hnorm := hν.tendsto_weighted hg hHm hL4 hσ 1
  rw [h0, add_zero] at hnorm
  simp only [one_mul, volF_apply] at hnorm
  have hweak := (tendsto_quartic_cross hHm hae hL4 (volF g₀)).comp hσ.tendsto_atTop
  simp only [volF_apply, Function.comp_def] at hweak
  have hRR := tendsto_integral_weighted_norm_sub_pow_four (ω := fun x => vol (g₀ x)) (μ := V₀)
    (fun x => vol_nonneg _) (u := fun h => H (σ h)) (u₀ := H₀)
    (fun h => by simpa [mul_comm, volF_apply] using integrable_quartic (hH (σ h)) (volF g₀))
    (fun h => by simpa [volF_apply] using integrable_quartic_cross (hH (σ h)) hH₀ (volF g₀))
    (by simpa [mul_comm, volF_apply] using integrable_quartic hH₀ (volF g₀)) hweak hnorm
  have hbound : ∀ h, ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀ ≤
      c⁻¹ * ∫ x, vol (g₀ x) * ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀ := by
    intro h
    have hd : MemLp (fun x => H (σ h) x - H₀ x) 4 V₀ := (hH (σ h)).sub hH₀
    have hi : Integrable (fun x => vol (g₀ x) * ‖H (σ h) x - H₀ x‖ ^ 4) V₀ := by
      simpa [mul_comm, volF_apply] using integrable_quartic hd (volF g₀)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      (hi.const_mul _) (Eventually.of_forall fun x => ?_)
    have h1 : c * ‖H (σ h) x - H₀ x‖ ^ 4 ≤ vol (g₀ x) * ‖H (σ h) x - H₀ x‖ ^ 4 :=
      mul_le_mul_of_nonneg_right (hvol x) (by positivity)
    calc ‖H (σ h) x - H₀ x‖ ^ 4 = c⁻¹ * (c * ‖H (σ h) x - H₀ x‖ ^ 4) := by
          field_simp
      _ ≤ c⁻¹ * (vol (g₀ x) * ‖H (σ h) x - H₀ x‖ ^ 4) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc.le)
  refine squeeze_zero (fun h => integral_nonneg fun x => by positivity) hbound ?_
  simpa using hRR.const_mul c⁻¹

/-- Strong `L⁴` convergence kills the quartic defect (convexity bound
`‖a‖⁴ ≤ (1+δ)³‖b‖⁴ + (1+1/δ)³‖a - b‖⁴`, `δ → 0`). -/
theorem quartic_zero_of_strong (hg : Tendsto g atTop (𝓝 g₀))
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {ν : StrongDual ℝ C(K, ℝ)} (hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν)
    (hs : Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) : ν = 0 := by
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  have hpos : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → ν φ = 0 := by
    intro φ hφ
    have hν0 := quartic_defect_nonneg hg hHm hae hL4 hσ hν hφ
    set ψ : C(K, ℝ) := φ * volF g₀
    have hψ : ∀ x, 0 ≤ ψ x := fun x => mul_nonneg (hφ x) (vol_nonneg _)
    set N := ∫ x, ψ x * ‖H₀ x‖ ^ 4 ∂V₀
    have hlim := hν.tendsto_weighted hg hHm hL4 hσ φ
    have hN0 : 0 ≤ N := integral_nonneg fun x => mul_nonneg (hψ x) (by positivity)
    have hδ : ∀ δ : ℝ, 0 < δ → ν φ ≤ ((1 + δ) ^ 3 - 1) * N := by
      intro δ hδ
      have hup : ∀ h, ∫ x, ψ x * ‖H (σ h) x‖ ^ 4 ∂V₀ ≤
          (1 + δ) ^ 3 * N + (1 + 1 / δ) ^ 3 * ‖ψ‖ * ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀ := by
        intro h
        have hd : MemLp (fun x => H (σ h) x - H₀ x) 4 V₀ := (hH (σ h)).sub hH₀
        have i1 := integrable_mul_density V₀ ψ (integrable_norm_pow_four (hH (σ h)))
        have i2 := integrable_mul_density V₀ ψ (integrable_norm_pow_four hH₀)
        have i3 := integrable_norm_pow_four hd
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i2.const_mul _)
          (i3.const_mul _)]
        refine integral_mono i1 ((i2.const_mul _).add (i3.const_mul _)) fun x => ?_
        have hw := norm_pow_four_le_weighted (H (σ h) x) (H₀ x) hδ
        have hψx : ψ x ≤ ‖ψ‖ := (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ ψ.norm_coe_le_norm x)
        have h1 := mul_le_mul_of_nonneg_left hw (hψ x)
        have h2 : ψ x * ((1 + 1 / δ) ^ 3 * ‖H (σ h) x - H₀ x‖ ^ 4) ≤
            ‖ψ‖ * ((1 + 1 / δ) ^ 3 * ‖H (σ h) x - H₀ x‖ ^ 4) :=
          mul_le_mul_of_nonneg_right hψx (by positivity)
        simp only
        nlinarith
      have hR : Tendsto (fun h => (1 + δ) ^ 3 * N + (1 + 1 / δ) ^ 3 * ‖ψ‖ *
          ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 ((1 + δ) ^ 3 * N)) := by
        simpa using (hs.const_mul ((1 + 1 / δ) ^ 3 * ‖ψ‖)).const_add ((1 + δ) ^ 3 * N)
      have := le_of_tendsto_of_tendsto' hlim hR hup
      linarith
    have hT : Tendsto (fun m : ℕ => ((1 + 1 / ((m : ℝ) + 1)) ^ 3 - 1) * N) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := ((h1.const_add 1).pow 3).sub_const 1
      simp only [add_zero, one_pow, sub_self] at h2
      simpa using h2.mul_const N
    have hle : ν φ ≤ 0 := ge_of_tendsto' hT fun m => hδ _ (by positivity)
    linarith
  ext φ
  set c : C(K, ℝ) := ContinuousMap.const K ‖φ‖
  have h1 : ν (φ + c) = 0 := hpos _ fun x => by
    simp only [ContinuousMap.add_apply, c, ContinuousMap.const_apply]
    have := (Real.norm_eq_abs _) ▸ φ.norm_coe_le_norm x
    linarith [neg_abs_le (φ x)]
  have h2 : ν c = 0 := hpos _ fun x => by simp [c]
  rw [map_add, h2, add_zero] at h1
  simpa using h1

/-- **`lem:critical-cubic`, quartic concentration** (`eq:quartic-defect`): on the compact chart,
for continuous metrics `g_h → g` uniformly (nondegenerate limit) and Higgs fields `H_h → H` a.e.
bounded in `L⁴`, after extraction there is a nonnegative Radon measure `ν_H` with
`|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H`, and `ν_H = 0` iff `H_h → H` strongly in `L⁴` along the
extracted sequence. -/
theorem quartic_defect (hg : Tendsto g atTop (𝓝 g₀)) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ν : StrongDual ℝ C(K, ℝ),
      IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧ (∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) := by
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  obtain ⟨R, hR⟩ := volF_bounded hg
  have hf : ∀ h, Integrable (fun x => ‖H h x‖ ^ 4 * vol (g h x)) V₀ := fun h =>
    integrable_quartic (hH h) (volF (g h))
  have hM : ∀ h, ∫ x, |‖H h x‖ ^ 4 * vol (g h x)| ∂V₀ ≤ R * (C : ℝ) ^ 4 := by
    intro h
    have e : ∫ x, |‖H h x‖ ^ 4 * vol (g h x)| ∂V₀ = ∫ x, ‖H h x‖ ^ 4 * vol (g h x) ∂V₀ :=
      integral_congr_ae (Eventually.of_forall fun x =>
        abs_of_nonneg (mul_nonneg (by positivity) (vol_nonneg _)))
    rw [e]
    calc ∫ x, ‖H h x‖ ^ 4 * vol (g h x) ∂V₀ ≤ ∫ x, R * ‖H h x‖ ^ 4 ∂V₀ := by
          refine integral_mono (hf h) ((integrable_norm_pow_four (hH h)).const_mul R)
            fun x => ?_
          have hv : vol (g h x) ≤ R := by
            have := (volF (g h)).norm_coe_le_norm x
            rw [Real.norm_eq_abs, volF_apply, abs_of_nonneg (vol_nonneg _)] at this
            exact this.trans (hR h)
          simp only
          nlinarith [pow_nonneg (norm_nonneg (H h x)) 4]
      _ = R * ∫ x, ‖H h x‖ ^ 4 ∂V₀ := integral_const_mul _ _
      _ ≤ R * (C : ℝ) ^ 4 := by
          have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
          exact mul_le_mul_of_nonneg_left (integral_norm_pow_four_le (hHm h) (hL4 h)) hR0
  obtain ⟨σ, hσ, Λ, hΛ⟩ := exists_subseq_density_tendsto V₀ _ hf hM
  set ν := Λ - densityCLM V₀ (fun x => ‖H₀ x‖ ^ 4 * vol (g₀ x))
  have hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν := by
    intro φ
    have e : ∫ x, φ x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) ∂V₀ + ν φ = Λ φ := by
      have hi : Integrable (fun x => ‖H₀ x‖ ^ 4 * vol (g₀ x)) V₀ := by
        simpa [volF_apply] using integrable_quartic hH₀ (volF g₀)
      simp only [ν]
      rw [sub_apply, densityCLM_apply V₀ hi]
      ring
    rw [e]
    exact hΛ φ
  refine ⟨σ, hσ, ν, hν, fun φ hφ => quartic_defect_nonneg hg hHm hae hL4 hσ hν hφ,
    fun h0 => quartic_strong_of_zero hg hdet₀ hHm hae hL4 hσ hν (by rw [h0]; rfl),
    quartic_zero_of_strong hg hHm hae hL4 hσ hν⟩

end Quartic2

/-! ## `lem:critical-cubic` (bundled) and `thm:higgs-defect` -/

section Higgs

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {H : ℕ → K → E} {H₀ : K → E}

/-- **`lem:critical-cubic`**: under `eq:critical-Higgs` (here: `H_h → H` a.e., bounded in `L⁴` —
the Sobolev consequence of the weak `H¹` bound — with weakly `L²`-convergent weak derivatives),
`A_h → A` in `L⁴`, and continuous metrics `g_h → g` uniformly with nondegenerate limit:
`|H_h|² H_h ⇀ |H|² H` in `L^{4/3}`, `D_{A_h} H_h ⇀ D_A H` in `L²` (`eq:critical-weak`), and after
extraction `|H_h|⁴ dV_{g_h} ⇀* |H|⁴ dV_g + ν_H` with `ν_H ≥ 0` and
`ν_H = 0 ⟺ H_h → H` in `L⁴` along the extracted sequence (`eq:quartic-defect`). -/
theorem critical_cubic [FiniteDimensional ℝ E] (hg : Tendsto g atTop (𝓝 g₀))
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {dH : ℕ → Fin 4 → K → E} {dH₀ : Fin 4 → K → E} (hdH : ∀ h μ, MemLp (dH h μ) 2 V₀)
    (hdH₀ : ∀ μ, MemLp (dH₀ μ) 2 V₀)
    (hdHw : ∀ μ (v : K → E), MemLp v 2 V₀ →
      Tendsto (fun h => ∫ x, ⟪v x, dH h μ x⟫ ∂V₀) atTop (𝓝 (∫ x, ⟪v x, dH₀ μ x⟫ ∂V₀)))
    {A : ℕ → Fin 4 → K → E →L[ℝ] E} {A₀ : Fin 4 → K → E →L[ℝ] E}
    (hA : ∀ h μ, MemLp (A h μ) 4 V₀) (hA₀ : ∀ μ, MemLp (A₀ μ) 4 V₀)
    (hAc : ∀ μ, Tendsto (fun h => eLpNorm (fun x => A h μ x - A₀ μ x) 4 V₀) atTop (𝓝 0)) :
    (∀ v : K → E, MemLp v 4 V₀ → Tendsto (fun h => ∫ x, ⟪v x, ‖H h x‖ ^ 2 • H h x⟫ ∂V₀) atTop
      (𝓝 (∫ x, ⟪v x, ‖H₀ x‖ ^ 2 • H₀ x⟫ ∂V₀))) ∧
    (∀ μ (v : K → E), MemLp v 2 V₀ →
      Tendsto (fun h => ∫ x, ⟪v x, covD (dH h) (A h) (H h) μ x⟫ ∂V₀) atTop
        (𝓝 (∫ x, ⟪v x, covD dH₀ A₀ H₀ μ x⟫ ∂V₀))) ∧
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ν : StrongDual ℝ C(K, ℝ),
      IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧ (∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) :=
  ⟨fun v hv => cubic_weak hHm hae hL4 hv,
    fun μ v hv => covD_weak hHm hae hL4 hdH hdH₀ hdHw hA hA₀ hAc μ hv,
    quartic_defect hg hdet₀ hHm hae hL4⟩

/-- The kinetic stress defect relation `eq:kinetic-defect` along `σ`. -/
def IsKinDefect (V₀ : Measure K) {κ : Type*} (g : ℕ → MetricField K) (g₀ : MetricField K)
    (Y : ℕ → Fin 4 → κ → K → ℝ) (Y₀ : Fin 4 → κ → K → ℝ) (σ : ℕ → ℕ)
    (KH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) [Fintype κ] : Prop :=
  ∀ μ ν (φ : C(K, ℝ)), Tendsto (fun h => ∫ x, φ x *
      (higgsKin (g (σ h) x) (Yval (Y (σ h)) x) μ ν * vol (g (σ h) x)) ∂V₀) atTop
    (𝓝 (∫ x, φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν * vol (g₀ x)) ∂V₀ + KH μ ν φ))

/-- The Higgs stress defect relation `eq:H-defect` along `σ`, with
`𝔖_{H,μν} = 𝔎_{H,μν} - λ g_{μν} ν_H`. -/
def IsHiggsDefect (V₀ : Measure K) {κ : Type*} [Fintype κ] (g : ℕ → MetricField K)
    (g₀ : MetricField K) (lam vH : ℕ → ℝ) (lam₀ vH₀ : ℝ) (Y : ℕ → Fin 4 → κ → K → ℝ)
    (Y₀ : Fin 4 → κ → K → ℝ) (H : ℕ → K → E) (H₀ : K → E) (σ : ℕ → ℕ)
    (SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) : Prop :=
  ∀ μ ν (φ : C(K, ℝ)), Tendsto (fun h => ∫ x, φ x *
      (higgsStress (g (σ h) x) (lam (σ h)) (vH (σ h)) (Yval (Y (σ h)) x) (‖H (σ h) x‖ ^ 2) μ ν *
        vol (g (σ h) x)) ∂V₀) atTop
    (𝓝 (∫ x, φ x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀ +
      SH μ ν φ))

theorem memLp_two_of_continuous (ψ : C(K, ℝ)) : MemLp (fun x => ψ x) 2 V₀ :=
  MemLp.of_bound ψ.continuous.aestronglyMeasurable ‖ψ‖
    (Eventually.of_forall fun x => ψ.norm_coe_le_norm x)

theorem integral_norm_sq_le (hHm : ∀ h, AEStronglyMeasurable (H h) V₀) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C) (h : ℕ) :
    ∫ x, |‖H h x‖ ^ 2| ∂V₀ ≤ (V₀.real univ + (C : ℝ) ^ 4) / 2 := by
  have hH := memLp_of_eLpNorm_le (hHm h) (hL4 h)
  have i4 := integrable_norm_pow_four hH
  calc ∫ x, |‖H h x‖ ^ 2| ∂V₀ ≤ ∫ x, (1 + ‖H h x‖ ^ 4) / 2 ∂V₀ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          ((integrable_const 1).add i4 |>.div_const 2) (Eventually.of_forall fun x => ?_)
        simp only
        rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (‖H h x‖ ^ 2 - 1)]
    _ = (V₀.real univ + ∫ x, ‖H h x‖ ^ 4 ∂V₀) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) i4]
        simp
    _ ≤ (V₀.real univ + (C : ℝ) ^ 4) / 2 := by
        gcongr; exact integral_norm_pow_four_le (hHm h) (hL4 h)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The Higgs kinetic defect is the contraction of the gradient covariance measure with the
limiting kinetic stress coefficients. -/
theorem isKinDefect_of_isDefect (hg : Tendsto g atTop (𝓝 g₀)) (hdet : ∀ h x, (mat (g h x)).det ≠ 0)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0) {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {Q : StrongDual ℝ C(K, Fin 4 × κ → Fin 4 × κ → ℝ)}
    (hQ : IsDefect V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) Q) :
    IsKinDefect V₀ g g₀ Y Y₀ σ fun μ ν => contract Q (kinCoefF g₀ μ ν) := by
  intro μ ν φ
  have hB : Tendsto (fun h => kinCoefF (κ := κ) (g (σ h)) μ ν) atTop (𝓝 (kinCoefF g₀ μ ν)) :=
    (tendsto_kinCoefF hg hdet₀ μ ν).comp hσ.tendsto_atTop
  have := hQ.tendsto_contract (hY.comp hσ) hB φ
  simp only [qf_kinCoefF (hdet _), qf_kinCoefF hdet₀] at this
  exact this

end Higgs

section HiggsDefect

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {H : ℕ → K → E} {H₀ : K → E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem integrable_kin {G : MetricField K} (hdet : ∀ x, (mat (G x)).det ≠ 0)
    {Y : Fin 4 → κ → K → ℝ} (hY : ∀ p, MemLp (Yp Y p) 2 V₀) (φ : C(K, ℝ)) (μ ν : Fin 4) :
    Integrable (fun x => φ x * (higgsKin (G x) (Yval Y x) μ ν * vol (G x))) V₀ := by
  have := integrable_mul_density V₀ φ (integrable_qf (kinCoefF (κ := κ) G μ ν) hY)
  simpa only [qf_kinCoefF hdet] using this

/-- The scalar measure `λ g_{μν} ν_H`: `φ ↦ λ ν_H(g_{μν} φ)`. -/
noncomputable def potDefect (lam₀ : ℝ) (g₀ : MetricField K) (ν : StrongDual ℝ C(K, ℝ))
    (μ ν' : Fin 4) : StrongDual ℝ C(K, ℝ) :=
  lam₀ • ν.comp (ContinuousLinearMap.mul ℝ C(K, ℝ) (entryF g₀ μ ν'))

theorem potDefect_apply (lam₀ : ℝ) (g₀ : MetricField K) (ν : StrongDual ℝ C(K, ℝ))
    (μ ν' : Fin 4) (φ : C(K, ℝ)) : potDefect lam₀ g₀ ν μ ν' φ = lam₀ * ν (entryF g₀ μ ν' * φ) :=
  rfl

/-- **Assembly of the Higgs stress defect** (`eq:H-defect`): the kinetic defect and the quartic
concentration measure along a common subsequence give
`T^H_h dV_{g_h} ⇀* T^H dV_g + 𝔖_H`, `𝔖_{H,μν} = 𝔎_{H,μν} - λ g_{μν} ν_H`; the quadratic part of
the potential converges (weak `L²` identification) and the constant part converges with the
volume density. -/
theorem isHiggsDefect_of (hg : Tendsto g atTop (𝓝 g₀)) (hdet : ∀ h x, (mat (g h x)).det ≠ 0)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {KH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)} (hK : IsKinDefect V₀ g g₀ Y Y₀ σ KH)
    {ν : StrongDual ℝ C(K, ℝ)} (hν : IsQuarticDefect V₀ g g₀ H H₀ σ ν) :
    IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ
      (fun μ ν' => KH μ ν' - potDefect lam₀ g₀ ν μ ν') := by
  intro μ ν' φ
  obtain ⟨hH₀, -⟩ := memLp_of_ae_tendsto hHm hae hL4
  have hH : ∀ h, MemLp (H h) 4 V₀ := fun h => memLp_of_eLpNorm_le (hHm h) (hL4 h)
  have hH2 : ∀ {f : K → E}, MemLp f 4 V₀ → Integrable (fun x => ‖f x‖ ^ 2) V₀ := fun hf =>
    (hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow (p := 2) (by norm_num)
  obtain ⟨R, hR⟩ := volF_bounded hg
  have hσt := hσ.tendsto_atTop
  have hgσ : Tendsto (fun h => g (σ h)) atTop (𝓝 g₀) := hg.comp hσt
  have hlσ := hlam.comp hσt
  have hvσ := hvH.comp hσt
  -- the four coefficient sequences
  set c2 : ℕ → C(K, ℝ) := fun h => ContinuousMap.const K (lam (σ h)) * entryF (g (σ h)) μ ν'
  set c3 : ℕ → C(K, ℝ) := fun h => ContinuousMap.const K (2 * lam (σ h) * vH (σ h) ^ 2) *
    entryF (g (σ h)) μ ν' * volF (g (σ h))
  set c4 : ℕ → C(K, ℝ) := fun h => ContinuousMap.const K (lam (σ h) * vH (σ h) ^ 4) *
    entryF (g (σ h)) μ ν' * volF (g (σ h))
  set c2₀ : C(K, ℝ) := ContinuousMap.const K lam₀ * entryF g₀ μ ν'
  set c3₀ : C(K, ℝ) := ContinuousMap.const K (2 * lam₀ * vH₀ ^ 2) * entryF g₀ μ ν' * volF g₀
  set c4₀ : C(K, ℝ) := ContinuousMap.const K (lam₀ * vH₀ ^ 4) * entryF g₀ μ ν' * volF g₀
  have hc2 : Tendsto c2 atTop (𝓝 c2₀) :=
    (tendsto_const_field hlσ).mul (tendsto_entryF hgσ μ ν')
  have hc3 : Tendsto c3 atTop (𝓝 c3₀) :=
    ((tendsto_const_field (((hlσ.const_mul 2).mul (hvσ.pow 2)))).mul
      (tendsto_entryF hgσ μ ν')).mul (tendsto_volF hgσ)
  have hc4 : Tendsto c4 atTop (𝓝 c4₀) :=
    ((tendsto_const_field (hlσ.mul (hvσ.pow 4))).mul (tendsto_entryF hgσ μ ν')).mul
      (tendsto_volF hgσ)
  -- the quartic piece
  have hf2 : ∀ h, Integrable (fun x => ‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)) V₀ := fun h =>
    integrable_quartic (hH (σ h)) (volF (g (σ h)))
  have hM2 : ∀ h, ∫ x, |‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)| ∂V₀ ≤ R * (C : ℝ) ^ 4 := by
    intro h
    have e : ∫ x, |‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)| ∂V₀ =
        ∫ x, ‖H (σ h) x‖ ^ 4 * vol (g (σ h) x) ∂V₀ :=
      integral_congr_ae (Eventually.of_forall fun x =>
        abs_of_nonneg (mul_nonneg (by positivity) (vol_nonneg _)))
    rw [e]
    calc ∫ x, ‖H (σ h) x‖ ^ 4 * vol (g (σ h) x) ∂V₀ ≤ ∫ x, R * ‖H (σ h) x‖ ^ 4 ∂V₀ := by
          refine integral_mono (hf2 h) ((integrable_norm_pow_four (hH (σ h))).const_mul R)
            fun x => ?_
          have hv : vol (g (σ h) x) ≤ R := by
            have := (volF (g (σ h))).norm_coe_le_norm x
            rw [Real.norm_eq_abs, volF_apply, abs_of_nonneg (vol_nonneg _)] at this
            exact this.trans (hR _)
          simp only
          nlinarith [pow_nonneg (norm_nonneg (H (σ h) x)) 4]
      _ = R * ∫ x, ‖H (σ h) x‖ ^ 4 ∂V₀ := integral_const_mul _ _
      _ ≤ R * (C : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (integral_norm_pow_four_le (hHm _) (hL4 _))
            ((norm_nonneg _).trans (hR 0))
  have hi4₀ : Integrable (fun x => ‖H₀ x‖ ^ 4 * vol (g₀ x)) V₀ := integrable_quartic hH₀ (volF g₀)
  have hΛ2 : ∀ ψ : C(K, ℝ), Tendsto (fun h => ∫ x, ψ x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)) ∂V₀)
      atTop (𝓝 ((densityCLM V₀ (fun x => ‖H₀ x‖ ^ 4 * vol (g₀ x)) + ν) ψ)) := by
    intro ψ
    rw [add_apply, densityCLM_apply V₀ hi4₀]
    exact hν ψ
  have hT2 := tendsto_density_mul_of_tendsto V₀ hf2 hM2 hΛ2 hc2 φ
  -- the quadratic piece
  have hf3 : ∀ h, Integrable (fun x => ‖H (σ h) x‖ ^ 2) V₀ := fun h => hH2 (hH (σ h))
  have hΛ3 : ∀ ψ : C(K, ℝ), Tendsto (fun h => ∫ x, ψ x * ‖H (σ h) x‖ ^ 2 ∂V₀) atTop
      (𝓝 (densityCLM V₀ (fun x => ‖H₀ x‖ ^ 2) ψ)) := by
    intro ψ
    rw [densityCLM_apply V₀ (hH2 hH₀)]
    exact tendsto_integral_mul_of_ae (p := 2) (q := 2) (by norm_num)
      (f := fun h x => ‖H (σ h) x‖ ^ 2) (fun h => ((hHm _).norm.pow 2))
      (hae.mono fun x hx => ((hx.comp hσt).norm.pow 2)) (C := C ^ 2)
      (fun h => eLpNorm_norm_sq_le (hL4 _)) (memLp_two_of_continuous ψ)
  have hT3 := tendsto_density_mul_of_tendsto V₀ hf3
    (fun h => integral_norm_sq_le hHm hL4 (σ h)) hΛ3 hc3 φ
  -- the constant piece
  have hf4 : ∀ _ : ℕ, Integrable (fun _ : K => (1 : ℝ)) V₀ := fun _ => integrable_const 1
  have hΛ4 : ∀ ψ : C(K, ℝ), Tendsto (fun _ : ℕ => ∫ x, ψ x * (1 : ℝ) ∂V₀) atTop
      (𝓝 (densityCLM V₀ (fun _ => (1 : ℝ)) ψ)) := by
    intro ψ; rw [densityCLM_apply V₀ (integrable_const 1)]; exact tendsto_const_nhds
  have hT4 := tendsto_density_mul_of_tendsto V₀ hf4 (M := ∫ _x, |(1 : ℝ)| ∂V₀)
    (fun _ => le_rfl) hΛ4 hc4 φ
  have hT1 := hK μ ν' φ
  -- assemble
  have hsum := ((hT1.sub hT2).add hT3).sub hT4
  have hYm : ∀ h p, MemLp (Yp (Y (σ h)) p) 2 V₀ := fun h p => hY.memLp (σ h) p
  have ipt : ∀ (G : MetricField K) (l v : ℝ) (Yv : Fin 4 → κ → ℝ) (a : E) (x : K),
      φ x * (higgsStress (G x) l v Yv (‖a‖ ^ 2) μ ν' * vol (G x)) =
        φ x * (higgsKin (G x) Yv μ ν' * vol (G x)) -
        φ x * ((ContinuousMap.const K l * entryF G μ ν' : C(K, ℝ)) x * (‖a‖ ^ 4 * vol (G x))) +
        φ x * ((ContinuousMap.const K (2 * l * v ^ 2) * entryF G μ ν' * volF G : C(K, ℝ)) x *
          ‖a‖ ^ 2) -
        φ x * ((ContinuousMap.const K (l * v ^ 4) * entryF G μ ν' * volF G : C(K, ℝ)) x * 1) := by
    intro G l v Yv a x
    simp only [higgsStress, higgsPot, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      entryF_apply, volF_apply]
    ring
  have eI : ∀ h, ∫ x, φ x * (higgsStress (g (σ h) x) (lam (σ h)) (vH (σ h)) (Yval (Y (σ h)) x)
        (‖H (σ h) x‖ ^ 2) μ ν' * vol (g (σ h) x)) ∂V₀ =
      ∫ x, φ x * (higgsKin (g (σ h) x) (Yval (Y (σ h)) x) μ ν' * vol (g (σ h) x)) ∂V₀ -
        ∫ x, φ x * (c2 h x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x))) ∂V₀ +
        ∫ x, φ x * (c3 h x * ‖H (σ h) x‖ ^ 2) ∂V₀ - ∫ x, φ x * (c4 h x * 1) ∂V₀ := by
    intro h
    have iA : Integrable (fun x => φ x * (higgsKin (g (σ h) x) (Yval (Y (σ h)) x) μ ν' *
        vol (g (σ h) x))) V₀ := integrable_kin (hdet (σ h)) (hYm h) φ μ ν'
    have iB : Integrable (fun x => φ x * (c2 h x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)))) V₀ :=
      integrable_mul_density V₀ φ (integrable_mul_density V₀ (c2 h) (hf2 h))
    have iC : Integrable (fun x => φ x * (c3 h x * ‖H (σ h) x‖ ^ 2)) V₀ :=
      integrable_mul_density V₀ φ (integrable_mul_density V₀ (c3 h) (hf3 h))
    have iD : Integrable (fun x => φ x * (c4 h x * 1)) V₀ :=
      integrable_mul_density V₀ φ (integrable_mul_density V₀ (c4 h) (hf4 h))
    have iAB : Integrable (fun x => φ x * (higgsKin (g (σ h) x) (Yval (Y (σ h)) x) μ ν' *
        vol (g (σ h) x)) - φ x * (c2 h x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x)))) V₀ := iA.sub iB
    have iABC : Integrable (fun x => φ x * (higgsKin (g (σ h) x) (Yval (Y (σ h)) x) μ ν' *
        vol (g (σ h) x)) - φ x * (c2 h x * (‖H (σ h) x‖ ^ 4 * vol (g (σ h) x))) +
        φ x * (c3 h x * ‖H (σ h) x‖ ^ 2)) V₀ := iAB.add iC
    have hpt := funext fun x => ipt (g (σ h)) (lam (σ h)) (vH (σ h)) (Yval (Y (σ h)) x)
      (H (σ h) x) x
    rw [hpt, integral_sub iABC iD, integral_add iAB iC, integral_sub iA iB]
  -- the same decomposition at the limit
  have eJ : ∫ x, φ x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν' *
        vol (g₀ x)) ∂V₀ =
      ∫ x, φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x)) ∂V₀ -
        ∫ x, (φ * c2₀) x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) ∂V₀ +
        ∫ x, (φ * c3₀) x * ‖H₀ x‖ ^ 2 ∂V₀ - ∫ x, (φ * c4₀) x * 1 ∂V₀ := by
    have iA : Integrable (fun x => φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x))) V₀ :=
      integrable_kin hdet₀ hY.memLp_lim φ μ ν'
    have iB : Integrable (fun x => (φ * c2₀) x * (‖H₀ x‖ ^ 4 * vol (g₀ x))) V₀ :=
      integrable_mul_density V₀ _ hi4₀
    have iC : Integrable (fun x => (φ * c3₀) x * ‖H₀ x‖ ^ 2) V₀ :=
      integrable_mul_density V₀ _ (hH2 hH₀)
    have iD : Integrable (fun x => (φ * c4₀) x * 1) V₀ :=
      integrable_mul_density V₀ _ (integrable_const 1)
    have iAB : Integrable (fun x => φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x)) -
        (φ * c2₀) x * (‖H₀ x‖ ^ 4 * vol (g₀ x))) V₀ := iA.sub iB
    have iABC : Integrable (fun x => φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x)) -
        (φ * c2₀) x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) + (φ * c3₀) x * ‖H₀ x‖ ^ 2) V₀ := iAB.add iC
    have hpt : (fun x => φ x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν' *
        vol (g₀ x))) = fun x => φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x)) -
        (φ * c2₀) x * (‖H₀ x‖ ^ 4 * vol (g₀ x)) + (φ * c3₀) x * ‖H₀ x‖ ^ 2 -
        (φ * c4₀) x * 1 := by
      funext x
      rw [ipt g₀ lam₀ vH₀ (Yval Y₀ x) (H₀ x) x]
      simp only [c2₀, c3₀, c4₀, ContinuousMap.mul_apply]
      ring
    rw [hpt, integral_sub iABC iD, integral_add iAB iC, integral_sub iA iB]
  have eν : ν (φ * c2₀) = lam₀ * ν (entryF g₀ μ ν' * φ) := by
    have : φ * c2₀ = lam₀ • (entryF g₀ μ ν' * φ) := by
      ext x; simp [c2₀, ContinuousMap.mul_apply]; ring
    rw [this, map_smul, smul_eq_mul]
  have hlim : ∫ x, φ x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν' *
        vol (g₀ x)) ∂V₀ + (KH μ ν' - potDefect lam₀ g₀ ν μ ν') φ =
      ∫ x, φ x * (higgsKin (g₀ x) (Yval Y₀ x) μ ν' * vol (g₀ x)) ∂V₀ + KH μ ν' φ -
        (densityCLM V₀ (fun x => ‖H₀ x‖ ^ 4 * vol (g₀ x)) + ν) (φ * c2₀) +
        densityCLM V₀ (fun x => ‖H₀ x‖ ^ 2) (φ * c3₀) -
        densityCLM V₀ (fun _ => (1 : ℝ)) (φ * c4₀) := by
    rw [eJ, add_apply, densityCLM_apply V₀ hi4₀, densityCLM_apply V₀ (hH2 hH₀),
      densityCLM_apply V₀ (integrable_const 1), eν, sub_apply, potDefect_apply]
    ring
  rw [hlim]
  refine hsum.congr fun h => ?_
  rw [eI h]

end HiggsDefect

section HiggsExtraction

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : ℕ → MetricField K} {g₀ : MetricField K} {H : ℕ → K → E} {H₀ : K → E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Common extraction for the kinetic packet and the quartic densities. -/
theorem exists_higgs_extraction (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ Q : StrongDual ℝ C(K, Fin 4 × κ → Fin 4 × κ → ℝ),
      IsDefect V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) Q ∧ ∃ ν : StrongDual ℝ C(K, ℝ),
      IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧ (∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) := by
  obtain ⟨σ₁, hσ₁, Q, hQ⟩ := exists_isDefect hY
  obtain ⟨σ₂, hσ₂, ν, hν, hν0, hνiff⟩ := quartic_defect (g := fun h => g (σ₁ h))
    (H := fun h => H (σ₁ h)) (hg.comp hσ₁.tendsto_atTop) hdet₀ (fun h => hHm _)
    (hae.mono fun x hx => hx.comp hσ₁.tendsto_atTop) (fun h => hL4 _)
  exact ⟨fun h => σ₁ (σ₂ h), hσ₁.comp hσ₂, Q, fun P => (hQ P).comp hσ₂.tendsto_atTop, ν, hν, hν0,
    hνiff⟩

/-- **`thm:higgs-defect`, stress-measure clause `eq:H-defect`**: for continuous metrics `g_h → g`
uniformly (nondegenerate), Higgs fields `H_h → H` a.e. bounded in `L⁴` (`eq:critical-Higgs`), an
identified weak gradient limit `D_{A_h} H_h ⇀ D_A H` in `L²`, and convergent parameters
`λ_h → λ`, `v_h → v`: after extraction, the kinetic defect `𝔎_H` (`eq:kinetic-defect`) and the
quartic concentration measure `ν_H ≥ 0` (`eq:quartic-defect`) exist and
`T^H_h dV_{g_h} ⇀* T^H dV_g + 𝔖_H` with `𝔖_{H,μν} = 𝔎_{H,μν} - λ g_{μν} ν_H`. -/
theorem higgs_defect (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ (KH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ))
      (ν : StrongDual ℝ C(K, ℝ)),
      IsKinDefect V₀ g g₀ Y Y₀ σ KH ∧ IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧
      (∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ ν φ) ∧
      IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ
        (fun μ ν' => KH μ ν' - potDefect lam₀ g₀ ν μ ν') := by
  obtain ⟨σ, hσ, Q, hQ, ν, hν, hν0, -⟩ :=
    exists_higgs_extraction hg hdet hdet₀ hHm hae hL4 hY
  have hK := isKinDefect_of_isDefect hg hdet hdet₀ hY hσ hQ
  exact ⟨σ, hσ, _, ν, hK, hν, hν0,
    isHiggsDefect_of hg hdet hdet₀ hHm hae hL4 hY hlam hvH hσ hK hν⟩

/-- Pairing of a tensor-valued measure with a symmetric test tensor `k^{μν}`. -/
def pairT (S : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (k : Fin 4 → Fin 4 → C(K, ℝ)) : ℝ :=
  ∑ μ, ∑ ν, S μ ν (k μ ν)

/-- **`thm:higgs-defect`, Einstein clause `eq:defect-Einstein`** (composition with the finite metric
equation).  Along any extraction carrying the Higgs stress defect `𝔖_H`: if the gravitational first
variation has its intended limit (`Grav_h(k) → ⟨(Ein(g)+Λg) dV_g, k⟩`), the remaining stress
contributions have their intended (regular) limits, and the operational metric residual and
consistency error vanish (`D S(z_h)[k] = Grav_h(k)/(2κ) - ½ ⟨T^{SM}_h dV_{g_h}, k⟩ → 0`, the Hilbert
convention `eq:stress-definition`), then
`(Ein(g) + Λ g) dV_g = κ (T^{SM} dV_g + 𝔖_H)` on every test tensor. -/
theorem higgs_defect_einstein {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ}
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)}
    (hSH : IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH)
    {κE : ℝ} (hκ : 0 < κE)
    (Grav : ℕ → (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ) (Ein : (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ)
    (hGrav : ∀ k, Tendsto (fun h => Grav h k) atTop (𝓝 (Ein k)))
    (Rest : ℕ → (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ) (RestLim : (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ)
    (hRest : ∀ k, Tendsto (fun h => Rest h k) atTop (𝓝 (RestLim k)))
    (hres : ∀ k, Tendsto (fun h => Grav h k / (2 * κE) - (1 / 2) * (∑ μ, ∑ ν, ∫ x, k μ ν x *
      (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x) (‖H h x‖ ^ 2) μ ν * vol (g h x)) ∂V₀ +
        Rest h k)) atTop (𝓝 0))
    (k : Fin 4 → Fin 4 → C(K, ℝ)) :
    Ein k = κE * ((∑ μ, ∑ ν, ∫ x, k μ ν x *
      (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀) +
        RestLim k + pairT SH k) := by
  have hσt := hσ.tendsto_atTop
  have hH : Tendsto (fun h => ∑ μ, ∑ ν, ∫ x, k μ ν x *
      (higgsStress (g (σ h) x) (lam (σ h)) (vH (σ h)) (Yval (Y (σ h)) x) (‖H (σ h) x‖ ^ 2) μ ν *
        vol (g (σ h) x)) ∂V₀) atTop
      (𝓝 (∑ μ, ∑ ν, (∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
        vol (g₀ x)) ∂V₀ + SH μ ν (k μ ν)))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ => hSH μ ν (k μ ν)
  have hlim := ((hGrav k).comp hσt |>.div_const (2 * κE)).sub
    ((hH.add ((hRest k).comp hσt)).const_mul (1 / 2))
  have h0 := tendsto_nhds_unique hlim ((hres k).comp hσt)
  simp only [Finset.sum_add_distrib] at h0
  unfold pairT
  set A := ∑ μ, ∑ ν, ∫ x, k μ ν x *
    (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀
  set P := ∑ μ, ∑ ν, SH μ ν (k μ ν)
  have h1 : Ein k / (2 * κE) = 1 / 2 * (A + P + RestLim k) := by linarith
  have h2 : Ein k = 2 * κE * (Ein k / (2 * κE)) := by field_simp
  rw [h2, h1]
  ring

end HiggsExtraction

section HiggsIntegrable

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The Higgs stress density `T^H dV_g` is integrable for `L²` gradients and `L⁴` fields. -/
theorem integrable_higgsStress {G : MetricField K} (hdet : ∀ x, (mat (G x)).det ≠ 0)
    {Y : Fin 4 → κ → K → ℝ} (hY : ∀ p, MemLp (Yp Y p) 2 V₀) {H : K → E} (hH : MemLp H 4 V₀)
    (l v : ℝ) (μ ν : Fin 4) :
    Integrable (fun x => higgsStress (G x) l v (Yval Y x) (‖H x‖ ^ 2) μ ν * vol (G x)) V₀ := by
  have iA : Integrable (fun x => (1 : C(K, ℝ)) x * (higgsKin (G x) (Yval Y x) μ ν * vol (G x)))
      V₀ := integrable_kin hdet hY 1 μ ν
  have iB : Integrable (fun x => (ContinuousMap.const K l * entryF G μ ν : C(K, ℝ)) x *
      (‖H x‖ ^ 4 * vol (G x))) V₀ :=
    integrable_mul_density V₀ _ (integrable_quartic hH (volF G))
  have iC : Integrable (fun x =>
      (ContinuousMap.const K (2 * l * v ^ 2) * entryF G μ ν * volF G : C(K, ℝ)) x * ‖H x‖ ^ 2) V₀ :=
    integrable_mul_density V₀ _ ((hH.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow
      (p := 2) (by norm_num))
  have iD : Integrable (fun x =>
      (ContinuousMap.const K (l * v ^ 4) * entryF G μ ν * volF G : C(K, ℝ)) x * 1) V₀ :=
    integrable_mul_density V₀ _ (integrable_const 1)
  refine (((iA.sub iB).add iC).sub iD).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, Pi.add_apply, higgsStress, higgsPot, ContinuousMap.mul_apply,
    ContinuousMap.const_apply, ContinuousMap.one_apply, entryF_apply, volF_apply]
  ring

end HiggsIntegrable

/-! ### Conservation clause of `thm:higgs-defect` (on a chart `K ⊆ ℝ⁴`) -/

section Conservation

open DefectConservationTransport

variable {Ks : Set (Fin 4 → ℝ)} [CompactSpace Ks] {V₀ : Measure Ks} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **`thm:higgs-defect`, conservation clause**: on a compact chart `K ⊆ ℝ⁴`, let the metrics converge
in `C¹` (`g_h, g` the restrictions of `C¹` fields `gf_h → gf`), let the total reconstructed stress
`𝖳_h = T^H_h dV_{g_h} + 𝖱_h` (Higgs part plus the remaining contributions `𝖱_h`, which have their
intended regular limits `𝖱_h ⇀* 𝖱`) be uniformly bounded Radon measures, and let their covariant
divergences vanish distributionally in the limit (`eq:defect-conservation-tested` for the vector
field `X`).  Then along the extraction carrying `𝔖_H`, the limiting stress
`T^{SM} dV_g + 𝔖_H = (T^H dV_g + 𝖱) + 𝔖_H` is conserved, and if the regular limiting matter stress
satisfies its Noether identity then `∇^μ 𝔖_{H,μν} = 0` (tested on `X`). -/
theorem higgs_defect_conserved
    {g : ℕ → MetricField Ks} {g₀ : MetricField Ks}
    (gf : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (gf₀ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (hgf : ∀ h i j, ContDiff ℝ 1 fun x => gf h x i j) (hgf₀ : ∀ i j, ContDiff ℝ 1 fun x => gf₀ x i j)
    (hdetf : ∀ x ∈ Ks, (gf₀ x).det ≠ 0)
    (hC0 : ∀ i j, TendstoUniformlyOn (fun h x => gf h x i j) (fun x => gf₀ x i j) atTop Ks)
    (hC1 : ∀ k i j, TendstoUniformlyOn (fun h => pd k fun x => gf h x i j)
      (pd k fun x => gf₀ x i j) atTop Ks)
    (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {H : ℕ → Ks → E} {H₀ : Ks → E} (hH₀ : MemLp H₀ 4 V₀)
    {Y : ℕ → Fin 4 → κ → Ks → ℝ} {Y₀ : Fin 4 → κ → Ks → ℝ}
    (hY₀ : ∀ p, MemLp (Yp Y₀ p) 2 V₀)
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {SH : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)}
    (hSH : IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH)
    (R : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ)) (Rlim : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ))
    (hR : ∀ μ ν φ, Tendsto (fun h => R h μ ν φ) atTop (𝓝 (Rlim μ ν φ)))
    (T : ℕ → Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ))
    (hTdef : ∀ h μ ν φ, T h μ ν φ = ∫ x, φ x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x)
      (‖H h x‖ ^ 2) μ ν * vol (g h x)) ∂V₀ + R h μ ν φ)
    {CT : ℝ} (hT : ∀ h μ ν, ‖T h μ ν‖ ≤ CT)
    (X : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (htest : Tendsto (fun h => ∑ μ, ∑ ν, T h μ ν (covSym Ks (gf h) X μ ν)) atTop (𝓝 0)) :
    let Treg : Fin 4 → Fin 4 → StrongDual ℝ C(Ks, ℝ) := fun μ ν =>
      densityCLM V₀ (fun x => higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
        vol (g₀ x)) + Rlim μ ν
    (∑ μ, ∑ ν, (Treg μ ν + SH μ ν) (covSym Ks gf₀ X μ ν) = 0) ∧
    (∑ μ, ∑ ν, Treg μ ν (covSym Ks gf₀ X μ ν) = 0 →
      ∑ μ, ∑ ν, SH μ ν (covSym Ks gf₀ X μ ν) = 0) := by
  intro Treg
  have hσt := hσ.tendsto_atTop
  have hlim : ∀ μ ν φ, Tendsto (fun h => T (σ h) μ ν φ) atTop (𝓝 ((Treg μ ν + SH μ ν) φ)) := by
    intro μ ν φ
    have hi := integrable_higgsStress (V₀ := V₀) hdet₀ hY₀ hH₀ lam₀ vH₀ μ ν
    have := (hSH μ ν φ).add ((hR μ ν φ).comp hσt)
    refine Tendsto.congr (fun h => (hTdef (σ h) μ ν φ).symm) ?_
    convert this using 2
    · rfl
    · simp only [Treg, add_apply, densityCLM_apply V₀ hi]
      ring
  have hcons := defect_conservation_transport (K := Ks) (g := fun h => gf (σ h)) (g₀ := gf₀)
    (fun h => hgf (σ h)) hgf₀ hdetf
    (fun i j u hu => hσt.eventually (hC0 i j u hu))
    (fun k i j u hu => hσt.eventually (hC1 k i j u hu))
    (fun h => T (σ h)) (fun μ ν => Treg μ ν + SH μ ν) (fun h => hT (σ h)) hlim X (htest.comp hσt)
  refine ⟨hcons, fun hN => ?_⟩
  exact defect_conservation_split gf₀ X (fun μ ν => Treg μ ν + SH μ ν) Treg SH
    (fun μ ν => rfl) hcons hN

end Conservation

/-! ## `thm:zero-defect-characterization` -/

section ZeroDefect

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]

/-- The component `n^μ` of a continuous vector field. -/
def ncomp (n : C(K, Fin 4 → ℝ)) (μ : Fin 4) : C(K, ℝ) :=
  ⟨fun x => n x μ, (continuous_apply μ).comp n.continuous⟩

/-- The timelike contraction `𝔖(n, n) = 𝔖_{μν} n^μ n^ν` of a tensor-valued measure. -/
noncomputable def nnPair (S : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (n : C(K, Fin 4 → ℝ)) :
    StrongDual ℝ C(K, ℝ) :=
  ∑ μ, ∑ ν, (S μ ν).comp (ContinuousLinearMap.mul ℝ C(K, ℝ) (ncomp n μ * ncomp n ν))

theorem nnPair_apply (S : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (n : C(K, Fin 4 → ℝ))
    (φ : C(K, ℝ)) : nnPair S n φ = ∑ μ, ∑ ν, S μ ν (ncomp n μ * ncomp n ν * φ) := by
  simp [nnPair]

/-- A functional vanishing on nonnegative functions vanishes. -/
theorem eq_zero_of_nonneg {Λ : StrongDual ℝ C(K, ℝ)}
    (h : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → Λ φ = 0) : Λ = 0 := by
  ext φ
  set c : C(K, ℝ) := ContinuousMap.const K ‖φ‖
  have h1 : Λ (φ + c) = 0 := h _ fun x => by
    simp only [ContinuousMap.add_apply, c, ContinuousMap.const_apply]
    have := (Real.norm_eq_abs _) ▸ φ.norm_coe_le_norm x
    linarith [neg_abs_le (φ x)]
  have h2 : Λ c = 0 := h _ fun x => by simp [c]
  rw [map_add, h2, add_zero] at h1
  simpa using h1

variable {ι : Type*} [Fintype ι]

/-- The `(n, n)`-contracted coefficient field `Σ n^μ n^ν B^{μν}`. -/
noncomputable def nnField (n : C(K, Fin 4 → ℝ)) (B : Fin 4 → Fin 4 → C(K, ι → ι → ℝ)) :
    C(K, ι → ι → ℝ) :=
  ∑ μ, ∑ ν, smulCoef (ncomp n μ * ncomp n ν) (B μ ν)

theorem nnField_apply (n : C(K, Fin 4 → ℝ)) (B : Fin 4 → Fin 4 → C(K, ι → ι → ℝ)) (x : K) :
    nnField n B x = nnCoef (n x) fun μ ν => B μ ν x := by
  simp [nnField, nnCoef, ContinuousMap.coe_sum, Finset.sum_apply, smulCoef_apply, ncomp]

theorem nnPair_contract (Q : StrongDual ℝ C(K, ι → ι → ℝ)) (n : C(K, Fin 4 → ℝ))
    (B : Fin 4 → Fin 4 → C(K, ι → ι → ℝ)) (φ : C(K, ℝ)) :
    nnPair (fun μ ν => contract Q (B μ ν)) n φ = Q (smulCoef φ (nnField n B)) := by
  rw [nnPair_apply]
  simp only [contract_apply, ← map_sum]
  congr 1
  ext x i j
  simp [nnField, smulCoef_apply, ContinuousMap.coe_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

end ZeroDefect

section TwoSided

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem smulCoef_smul (φ : C(K, ℝ)) (c : ℝ) (B : C(K, ι → ι → ℝ)) :
    smulCoef φ (c • B) = c • smulCoef φ B := by
  ext x i j; simp [smulCoef_apply]; ring

/-- **Two-sided comparison with the trace defect**: pointwise bounds
`c |z|² ≤ qf (P x) z ≤ C |z|²` on the admissible directions give
`c μ_Y ≤ P : 𝖰 ≤ C μ_Y` as measures (tested on nonnegative functions). -/
theorem two_sided_of_isDefect {Y : ℕ → ι → K → ℝ} {Y₀ : ι → K → ℝ} (hY : WeakL2 V₀ Y Y₀)
    {Q : StrongDual ℝ C(K, ι → ι → ℝ)} (hQ : IsDefect V₀ Y Y₀ Q) {S : K → Set (ι → ℝ)}
    (hS : ∀ h, ∀ᵐ x ∂V₀, (fun i => Y h i x - Y₀ i x) ∈ S x) {P : C(K, ι → ι → ℝ)} {c C : ℝ}
    (hlow : ∀ x, ∀ z ∈ S x, c * ∑ i, z i ^ 2 ≤ qf (P x) z)
    (hupp : ∀ x, ∀ z ∈ S x, qf (P x) z ≤ C * ∑ i, z i ^ 2) {φ : C(K, ℝ)} (hφ : ∀ x, 0 ≤ φ x) :
    c * traceMeasure Q φ ≤ Q (smulCoef φ P) ∧ Q (smulCoef φ P) ≤ C * traceMeasure Q φ := by
  have e : ∀ a : ℝ, a * traceMeasure Q φ = Q (smulCoef φ (a • idField)) := by
    intro a
    rw [smulCoef_smul, map_smul, smul_eq_mul, traceMeasure, contract_apply]
  have hid : ∀ (a : ℝ) (x : K) (z : ι → ℝ),
      qf (smulCoef φ (a • idField) x) z = φ x * (a * ∑ i, z i ^ 2) := by
    intro a x z
    rw [smulCoef_apply, qf_smul_left, ContinuousMap.smul_apply, qf_smul_left, idField,
      ContinuousMap.const_apply, qf_idCoef]
  constructor
  · rw [e]
    refine hQ.le_of_qf_le hY hS fun x z hz => ?_
    rw [hid, smulCoef_apply, qf_smul_left]
    exact mul_le_mul_of_nonneg_left (hlow x z hz) (hφ x)
  · rw [e]
    refine hQ.le_of_qf_le hY hS fun x z hz => ?_
    rw [hid, smulCoef_apply, qf_smul_left]
    exact mul_le_mul_of_nonneg_left (hupp x z hz) (hφ x)

end TwoSided

section Uniform

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `trH(g(x), n(x))` as a continuous function (for nondegenerate `g`). -/
noncomputable def trHF (g : MetricField K) (n : C(K, Fin 4 → ℝ)) : C(K, ℝ) :=
  ∑ α, (invF g α α + ContinuousMap.const K 2 * (ncomp n α * ncomp n α))

/-- `Σ g_{μν}(x)²` as a continuous function. -/
def sqGF (g : MetricField K) : C(K, ℝ) := ∑ μ, ∑ ν, entryF g μ ν * entryF g μ ν

theorem trHF_apply {g : MetricField K} (hdet : ∀ x, (mat (g x)).det ≠ 0) (n : C(K, Fin 4 → ℝ))
    (x : K) : trHF g n x = trH (g x) (n x) := by
  simp [trHF, trH, hinv, ContinuousMap.coe_sum, Finset.sum_apply, invF_apply hdet, ncomp]

theorem sqGF_apply (g : MetricField K) (x : K) : sqGF g x = sqG (g x) := by
  simp [sqGF, sqG, ContinuousMap.coe_sum, Finset.sum_apply, entryF_apply, sq]

theorem le_norm_of_apply (f : C(K, ℝ)) (x : K) : f x ≤ ‖f‖ :=
  (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ f.norm_coe_le_norm x)

theorem exists_weight_bounds (w : κ → ℝ) (hw : ∀ a, 0 < w a) :
    ∃ cw > 0, ∃ Cw ≥ 0, ∀ a, cw ≤ w a ∧ w a ≤ Cw := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨1, one_pos, 0, le_rfl, fun a => (IsEmpty.false a).elim⟩
  · obtain ⟨a₀, -, ha₀⟩ := Finset.univ.exists_min_image w Finset.univ_nonempty
    obtain ⟨a₁, -, ha₁⟩ := Finset.univ.exists_max_image w Finset.univ_nonempty
    exact ⟨w a₀, hw a₀, w a₁, (hw a₁).le, fun a =>
      ⟨ha₀ a (Finset.mem_univ a), ha₁ a (Finset.mem_univ a)⟩⟩

/-- The antisymmetric (two-form) directions. -/
def antiSet : Set ((Fin 4 × Fin 4) × κ → ℝ) := {z | ∀ α β a, z ((β, α), a) = -z ((α, β), a)}

/-- **Uniform timelike coercivity of the Yang–Mills stress coefficient on the chart**
(`eq:YM-timelike-energy` with uniform constants on the compact chart). -/
theorem ym_uniform_bounds {g₀ : MetricField K} (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(K, Fin 4 → ℝ)} (hframe : ∀ x, ∃ E, IsTimeFrame (g₀ x) (n x) E)
    {w₀ : κ → ℝ} (hw₀ : ∀ a, 0 < w₀ a) :
    ∃ c > 0, ∃ C > 0, ∀ x, ∀ z ∈ antiSet (κ := κ),
      c * ∑ p, z p ^ 2 ≤ qf (nnField n (fun μ ν => ymCoefF g₀ w₀ μ ν) x) z ∧
      qf (nnField n (fun μ ν => ymCoefF g₀ w₀ μ ν) x) z ≤ C * ∑ p, z p ^ 2 := by
  obtain ⟨cw, hcw, Cw, hCw, hwb⟩ := exists_weight_bounds w₀ hw₀
  obtain ⟨cv, hcv, hvol⟩ := exists_vol_lower g₀ hdet₀
  set A := ‖trHF g₀ n‖
  set B := ‖sqGF g₀‖
  set Vm := ‖volF g₀‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  refine ⟨cv * cw / (4 * (A * B) ^ 2 + 1), by positivity, 4 * Cw * A ^ 2 * Vm + 1, by positivity,
    fun x z hz => ?_⟩
  obtain ⟨E, hE⟩ := hframe x
  have hP : nnField n (fun μ ν => ymCoefF g₀ w₀ μ ν) x =
      nnCoef (n x) fun μ ν => ymCoef (g₀ x) w₀ (vol (g₀ x)) μ ν := by
    rw [nnField_apply]; simp only [ymCoefF_apply hdet₀]
  rw [hP]
  have hV : 0 ≤ vol (g₀ x) := vol_nonneg _
  have hT : trH (g₀ x) (n x) ≤ A := (trHF_apply hdet₀ n x) ▸ le_norm_of_apply _ x
  have hT0 : 0 ≤ trH (g₀ x) (n x) := hE.trH_nonneg
  have hG : sqG (g₀ x) ≤ B := (sqGF_apply g₀ x) ▸ le_norm_of_apply _ x
  have hG0 := sqG_nonneg (g₀ x)
  have hVm : vol (g₀ x) ≤ Vm := (volF_apply g₀ x) ▸ le_norm_of_apply _ x
  have hlow := ym_nn_lower hE w₀ (fun a => (hwb a).1) hcw.le hV z hz
  have hupp := ym_nn_upper hE w₀ (fun a => (hwb a).2) hCw hV z hz
  have hq0 : 0 ≤ qf (nnCoef (n x) fun μ ν => ymCoef (g₀ x) w₀ (vol (g₀ x)) μ ν) z := by
    rw [qf_nn_ymCoef hE w₀ _ z hz]
    refine mul_nonneg hV (mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => ?_))
    exact Finset.sum_nonneg fun a _ => by
      rw [← sq]; exact mul_nonneg (hw₀ a).le (sq_nonneg _)
  set q := qf (nnCoef (n x) fun μ ν => ymCoef (g₀ x) w₀ (vol (g₀ x)) μ ν) z
  set Z := ∑ p, z p ^ 2
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hTG : (trH (g₀ x) (n x) * sqG (g₀ x)) ^ 2 ≤ (A * B) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hT0 hG0) (mul_le_mul hT hG hG0 hA0) 2
  constructor
  · have h1 : cv * cw * Z ≤ vol (g₀ x) * cw * Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hvol x) hcw.le) hZ0
    have h2 : 4 * (trH (g₀ x) (n x) * sqG (g₀ x)) ^ 2 * q ≤ (4 * (A * B) ^ 2 + 1) * q := by
      nlinarith
    have h3 : cv * cw * Z ≤ (4 * (A * B) ^ 2 + 1) * q := h1.trans (hlow.trans h2)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  · have h1 : 4 * Cw * trH (g₀ x) (n x) ^ 2 * vol (g₀ x) * Z ≤ 4 * Cw * A ^ 2 * Vm * Z := by
      have : trH (g₀ x) (n x) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hT0 hT 2
      have h4 : 4 * Cw * trH (g₀ x) (n x) ^ 2 * vol (g₀ x) ≤ 4 * Cw * A ^ 2 * Vm := by
        have := mul_le_mul this hVm hV (sq_nonneg _)
        nlinarith
      exact mul_le_mul_of_nonneg_right h4 hZ0
    nlinarith

/-- **Uniform timelike coercivity of the kinetic Higgs stress coefficient on the chart**
(`eq:H-timelike-energy` with uniform constants). -/
theorem kin_uniform_bounds {g₀ : MetricField K} (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(K, Fin 4 → ℝ)} (hframe : ∀ x, ∃ E, IsTimeFrame (g₀ x) (n x) E) :
    ∃ c > 0, ∃ C > 0, ∀ x, ∀ z : Fin 4 × κ → ℝ,
      c * ∑ p, z p ^ 2 ≤ qf (nnField n (fun μ ν => kinCoefF (κ := κ) g₀ μ ν) x) z ∧
      qf (nnField n (fun μ ν => kinCoefF (κ := κ) g₀ μ ν) x) z ≤ C * ∑ p, z p ^ 2 := by
  obtain ⟨cv, hcv, hvol⟩ := exists_vol_lower g₀ hdet₀
  set A := ‖trHF g₀ n‖
  set B := ‖sqGF g₀‖
  set Vm := ‖volF g₀‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  refine ⟨cv / (A * B + 1), by positivity, A * Vm + 1, by positivity, fun x z => ?_⟩
  obtain ⟨E, hE⟩ := hframe x
  have hP : nnField n (fun μ ν => kinCoefF (κ := κ) g₀ μ ν) x =
      nnCoef (n x) fun μ ν => kinCoef (κ := κ) (g₀ x) (vol (g₀ x)) μ ν := by
    rw [nnField_apply]; simp only [kinCoefF_apply hdet₀]
  rw [hP]
  have hV : 0 ≤ vol (g₀ x) := vol_nonneg _
  have hT : trH (g₀ x) (n x) ≤ A := (trHF_apply hdet₀ n x) ▸ le_norm_of_apply _ x
  have hT0 : 0 ≤ trH (g₀ x) (n x) := hE.trH_nonneg
  have hG : sqG (g₀ x) ≤ B := (sqGF_apply g₀ x) ▸ le_norm_of_apply _ x
  have hG0 := sqG_nonneg (g₀ x)
  have hVm : vol (g₀ x) ≤ Vm := (volF_apply g₀ x) ▸ le_norm_of_apply _ x
  have hlow := kin_nn_lower (κ := κ) hE hV z
  have hupp := kin_nn_upper (κ := κ) hE hV z
  have hq0 : 0 ≤ qf (nnCoef (n x) fun μ ν => kinCoef (κ := κ) (g₀ x) (vol (g₀ x)) μ ν) z := by
    rw [qf_nn_kinCoef hE _ z]
    exact mul_nonneg hV (Finset.sum_nonneg fun k _ => by
      rw [lieIp_one_self]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _)
  set q := qf (nnCoef (n x) fun μ ν => kinCoef (κ := κ) (g₀ x) (vol (g₀ x)) μ ν) z
  set Z := ∑ p, z p ^ 2
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor
  · have h1 : cv * Z ≤ vol (g₀ x) * Z := mul_le_mul_of_nonneg_right (hvol x) hZ0
    have h2 : trH (g₀ x) (n x) * sqG (g₀ x) * q ≤ (A * B + 1) * q := by
      have : trH (g₀ x) (n x) * sqG (g₀ x) ≤ A * B + 1 := by
        nlinarith [mul_le_mul hT hG hG0 hA0]
      exact mul_le_mul_of_nonneg_right this hq0
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  · have h4 : trH (g₀ x) (n x) * vol (g₀ x) ≤ A * Vm := mul_le_mul hT hVm hV hA0
    nlinarith

end Uniform

section ZeroDefectMain

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nnPair_add (S S' : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (n : C(K, Fin 4 → ℝ)) :
    nnPair (fun μ ν => S μ ν + S' μ ν) n = nnPair S n + nnPair S' n := by
  ext φ
  simp only [nnPair_apply, add_apply, Finset.sum_add_distrib]

theorem nnPair_sub (S S' : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (n : C(K, Fin 4 → ℝ)) :
    nnPair (fun μ ν => S μ ν - S' μ ν) n = nnPair S n - nnPair S' n := by
  ext φ
  simp only [nnPair_apply, sub_apply, Finset.sum_sub_distrib]

/-- The timelike contraction of the potential defect `-λ g ν_H` is `λ ν_H` (`g(n, n) = -1`). -/
theorem nnPair_potDefect {g₀ : MetricField K} {n : C(K, Fin 4 → ℝ)}
    (hframe : ∀ x, ∃ E, IsTimeFrame (g₀ x) (n x) E) (lam₀ : ℝ) (ν : StrongDual ℝ C(K, ℝ))
    (φ : C(K, ℝ)) : nnPair (fun μ ν' => potDefect lam₀ g₀ ν μ ν') n φ = -(lam₀ * ν φ) := by
  rw [nnPair_apply]
  simp only [potDefect_apply, ← Finset.mul_sum, ← map_sum]
  have : (∑ μ, ∑ ν', entryF g₀ μ ν' * (ncomp n μ * ncomp n ν' * φ)) = -φ := by
    ext x
    obtain ⟨E, hE⟩ := hframe x
    have hg := hE.gnn_eq
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply, entryF_apply,
      ncomp, ContinuousMap.coe_mk, ContinuousMap.neg_apply]
    have e : ∑ μ, ∑ ν', g₀ x μ ν' * (n x μ * n x ν' * φ x) = gnn (g₀ x) (n x) * φ x := by
      simp only [gnn, Finset.sum_mul]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν' _ => ?_
      ring
    rw [e, hg]; ring
  rw [this, map_neg]; ring

variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **`thm:zero-defect-characterization`**: under the weak Yang–Mills and Higgs hypotheses
(continuous metrics `g_h → g` uniformly, nondegenerate; curvatures `F_{A_h} ⇀ F_A` in `L²`
(antisymmetric); `H_h → H` a.e., bounded in `L⁴`; `D_{A_h}H_h ⇀ D_AH` in `L²`; convergent
parameters with positive limiting gauge coefficients `w_a > 0` and `λ_H > 0`), with Lorentzian
limit `g = Pᵀ η P` (signature `(-,+,+,+)`, `P` invertible pointwise) and a continuous unit timelike
field `n` (`g(n, n) = -1`; future-directedness is not needed), after
extraction the stress defects `𝔖_{YM}`, `𝔖_H`, the trace defects `μ_{YM}`, `μ_{∇H}` and the quartic
measure `ν_H` exist, there are `c, C > 0` with
`c(μ_{YM} + μ_{∇H} + ν_H) ≤ (𝔖_{YM} + 𝔖_H)(n, n) ≤ C(μ_{YM} + μ_{∇H} + ν_H)`
(`eq:timelike-defect-coercivity`), and the four conditions of
`eq:complete-zero-defect-equivalence` are equivalent along the extracted sequence. -/
theorem zero_defect_characterization
    {g : ℕ → MetricField K} {g₀ : MetricField K} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(K, Fin 4 → ℝ)}
    (hsig : ∀ x, ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      mat (g₀ x) = Matrix.transpose P * eta * P)
    (hunit : ∀ x, gnn (g₀ x) (n x) = -1)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hw₀ : ∀ a, 0 < w₀ a)
    {F : ℕ → Fin 4 → Fin 4 → κG → K → ℝ} {F₀ : Fin 4 → Fin 4 → κG → K → ℝ}
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀))
    (hFa : ∀ h α β a x, F h β α a x = -F h α β a x) (hFa₀ : ∀ α β a x, F₀ β α a x = -F₀ α β a x)
    {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) (hlam₀ : 0 < lam₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ (SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (μYM μH ν : StrongDual ℝ C(K, ℝ)),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM ∧
      IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH ∧
      (∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Fp (F (σ h)) p x ^ 2 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ∑ p, Fp F₀ p x ^ 2 ∂V₀ + μYM φ))) ∧
      (∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Yp (Y (σ h)) p x ^ 2 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ∑ p, Yp Y₀ p x ^ 2 ∂V₀ + μH φ))) ∧
      IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧
      (∃ c > 0, ∃ C' > 0, ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) →
        c * (μYM φ + μH φ + ν φ) ≤ nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ∧
        nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ≤ C' * (μYM φ + μH φ + ν φ)) ∧
      ((∀ μ ν', SYM μ ν' + SH μ ν' = 0) ↔ nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0) ∧
      (nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0 ↔ μYM = 0 ∧ μH = 0 ∧ ν = 0) ∧
      (μYM = 0 ∧ μH = 0 ∧ ν = 0 ↔
        StrongL2 V₀ (fun h => Fp (F (σ h))) (Fp F₀) ∧ StrongL2 V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) ∧
          Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) ∧
      (μYM = 0 ↔ StrongL2 V₀ (fun h => Fp (F (σ h))) (Fp F₀)) ∧
      (μH = 0 ↔ StrongL2 V₀ (fun h => Yp (Y (σ h))) (Yp Y₀)) ∧
      (ν = 0 ↔ Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) := by
  have hframe : ∀ x, ∃ E, IsTimeFrame (g₀ x) (n x) E := fun x => by
    obtain ⟨P, hP, hGP⟩ := hsig x
    exact exists_isTimeFrame hP hGP (hunit x)
  -- extraction
  obtain ⟨σ₁, hσ₁, QF, hQF⟩ := exists_isDefect hF
  obtain ⟨σ₂, hσ₂, QY, hQY, ν, hν, hν0, hνiff⟩ := exists_higgs_extraction
    (g := fun h => g (σ₁ h)) (H := fun h => H (σ₁ h)) (Y := fun h => Y (σ₁ h))
    (hg.comp hσ₁.tendsto_atTop) (fun h => hdet _) hdet₀ (fun h => hHm _)
    (hae.mono fun x hx => hx.comp hσ₁.tendsto_atTop) (fun h => hL4 _) (hY.comp hσ₁)
  set σ : ℕ → ℕ := fun h => σ₁ (σ₂ h)
  have hσ : StrictMono σ := hσ₁.comp hσ₂
  have hQFσ : IsDefect V₀ (fun h => Fp (F (σ h))) (Fp F₀) QF := fun P =>
    (hQF P).comp hσ₂.tendsto_atTop
  have hFσ := hF.comp hσ
  have hYσ := hY.comp hσ
  have hSYM := isYMDefect_of_isDefect hg hdet hdet₀ hw hF hσ hQFσ
  have hK := isKinDefect_of_isDefect hg hdet hdet₀ hY hσ hQY
  have hSH := isHiggsDefect_of hg hdet hdet₀ hHm hae hL4 hY hlam hvH hσ hK hν
  set SYM : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ) := fun μ ν' => contract QF (ymCoefF g₀ w₀ μ ν')
  set KH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ) := fun μ ν' => contract QY (kinCoefF g₀ μ ν')
  set SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ) := fun μ ν' => KH μ ν' - potDefect lam₀ g₀ ν μ ν'
  -- the timelike contraction
  have hnn : ∀ φ, nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ =
      QF (smulCoef φ (nnField n fun μ ν' => ymCoefF g₀ w₀ μ ν')) +
      QY (smulCoef φ (nnField n fun μ ν' => kinCoefF g₀ μ ν')) + lam₀ * ν φ := by
    intro φ
    rw [nnPair_add, add_apply]
    simp only [SH]
    rw [nnPair_sub, sub_apply, nnPair_potDefect hframe, nnPair_contract, nnPair_contract]
    ring
  -- admissibility of the curvature differences
  have hS : ∀ h, ∀ᵐ x ∂V₀, (fun p => Fp (F (σ h)) p x - Fp F₀ p x) ∈ antiSet (κ := κG) := by
    intro h
    refine Eventually.of_forall fun x α β a => ?_
    show F (σ h) β α a x - F₀ β α a x = -(F (σ h) α β a x - F₀ α β a x)
    rw [hFa, hFa₀]
    ring
  obtain ⟨c₁, hc₁, C₁, hC₁, hb₁⟩ := ym_uniform_bounds (κ := κG) hdet₀ hframe hw₀
  obtain ⟨c₂, hc₂, C₂, hC₂, hb₂⟩ := kin_uniform_bounds (κ := κ) hdet₀ hframe
  have hYM2 : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) →
      c₁ * traceMeasure QF φ ≤ QF (smulCoef φ (nnField n fun μ ν' => ymCoefF g₀ w₀ μ ν')) ∧
      QF (smulCoef φ (nnField n fun μ ν' => ymCoefF g₀ w₀ μ ν')) ≤ C₁ * traceMeasure QF φ :=
    fun φ hφ => two_sided_of_isDefect hFσ hQFσ hS (fun x z hz => (hb₁ x z hz).1)
      (fun x z hz => (hb₁ x z hz).2) hφ
  have hH2 : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) →
      c₂ * traceMeasure QY φ ≤ QY (smulCoef φ (nnField n fun μ ν' => kinCoefF g₀ μ ν')) ∧
      QY (smulCoef φ (nnField n fun μ ν' => kinCoefF g₀ μ ν')) ≤ C₂ * traceMeasure QY φ :=
    fun φ hφ => two_sided_of_isDefect hYσ hQY (S := fun _ => univ)
      (fun h => Eventually.of_forall fun x => mem_univ _) (fun x z _ => (hb₂ x z).1)
      (fun x z _ => (hb₂ x z).2) hφ
  have htrF : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ traceMeasure QF φ :=
    fun φ hφ => hQFσ.traceMeasure_nonneg hFσ hφ
  have htrY : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ traceMeasure QY φ :=
    fun φ hφ => hQY.traceMeasure_nonneg hYσ hφ
  set c := min c₁ (min c₂ lam₀)
  set C' := max C₁ (max C₂ lam₀)
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂ hlam₀)
  have hC' : 0 < C' := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hcoer : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) →
      c * (traceMeasure QF φ + traceMeasure QY φ + ν φ) ≤
        nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ∧
      nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n φ ≤
        C' * (traceMeasure QF φ + traceMeasure QY φ + ν φ) := by
    intro φ hφ
    rw [hnn]
    obtain ⟨l1, u1⟩ := hYM2 φ hφ
    obtain ⟨l2, u2⟩ := hH2 φ hφ
    have a1 := htrF φ hφ
    have a2 := htrY φ hφ
    have a3 := hν0 φ hφ
    have m1 : c ≤ c₁ := min_le_left _ _
    have m2 : c ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
    have m3 : c ≤ lam₀ := (min_le_right _ _).trans (min_le_right _ _)
    have M1 : C₁ ≤ C' := le_max_left _ _
    have M2 : C₂ ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
    have M3 : lam₀ ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right m1 a1, mul_le_mul_of_nonneg_right m2 a2,
        mul_le_mul_of_nonneg_right m3 a3]
    · nlinarith [mul_le_mul_of_nonneg_right M1 a1, mul_le_mul_of_nonneg_right M2 a2,
        mul_le_mul_of_nonneg_right M3 a3]
  -- the equivalence chain
  have hAB : (∀ μ ν', SYM μ ν' + SH μ ν' = 0) → nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0 := by
    intro hA
    ext φ
    simp [nnPair_apply, hA]
  have hBC : nnPair (fun μ ν' => SYM μ ν' + SH μ ν') n = 0 →
      traceMeasure QF = 0 ∧ traceMeasure QY = 0 ∧ ν = 0 := by
    intro hB
    have key : ∀ φ : C(K, ℝ), (∀ x, 0 ≤ φ x) →
        traceMeasure QF φ = 0 ∧ traceMeasure QY φ = 0 ∧ ν φ = 0 := by
      intro φ hφ
      have h1 := (hcoer φ hφ).1
      rw [hB, zero_apply] at h1
      have a1 := htrF φ hφ
      have a2 := htrY φ hφ
      have a3 := hν0 φ hφ
      have hsum : traceMeasure QF φ + traceMeasure QY φ + ν φ ≤ 0 := by
        by_contra hcon
        have := mul_pos hc (lt_of_not_ge hcon)
        linarith
      refine ⟨by linarith, by linarith, by linarith⟩
    exact ⟨eq_zero_of_nonneg fun φ hφ => (key φ hφ).1,
      eq_zero_of_nonneg fun φ hφ => (key φ hφ).2.1, eq_zero_of_nonneg fun φ hφ => (key φ hφ).2.2⟩
  have hCD : traceMeasure QF = 0 ∧ traceMeasure QY = 0 ∧ ν = 0 →
      StrongL2 V₀ (fun h => Fp (F (σ h))) (Fp F₀) ∧ StrongL2 V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) ∧
        Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) := by
    rintro ⟨h1, h2, h3⟩
    exact ⟨(hQFσ.traceMeasure_eq_zero_iff_strongL2 hFσ).1 h1,
      (hQY.traceMeasure_eq_zero_iff_strongL2 hYσ).1 h2, hνiff.1 h3⟩
  have hDA : StrongL2 V₀ (fun h => Fp (F (σ h))) (Fp F₀) ∧
      StrongL2 V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) ∧
        Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) →
      ∀ μ ν', SYM μ ν' + SH μ ν' = 0 := by
    rintro ⟨h1, h2, h3⟩ μ ν'
    have e1 := hQFσ.eq_zero_of_strongL2 hFσ h1
    have e2 := hQY.eq_zero_of_strongL2 hYσ h2
    have e3 := hνiff.2 h3
    ext φ
    simp only [SYM, SH, KH, add_apply, sub_apply, contract_apply, e1, e2, e3, potDefect_apply,
      zero_apply]
    ring
  refine ⟨σ, hσ, SYM, SH, traceMeasure QF, traceMeasure QY, ν, hSYM, hSH,
    fun φ => hQFσ.tendsto_trace hFσ φ, fun φ => hQY.tendsto_trace hYσ φ, hν,
    ⟨c, hc, C', hC', hcoer⟩, ⟨hAB, fun hB => hDA (hCD (hBC hB))⟩,
    ⟨hBC, fun hC => hAB (hDA (hCD hC))⟩, ⟨hCD, fun hD => hBC (hAB (hDA hD))⟩,
    hQFσ.traceMeasure_eq_zero_iff_strongL2 hFσ, hQY.traceMeasure_eq_zero_iff_strongL2 hYσ, hνiff⟩

end ZeroDefectMain

/-! ## `thm:joint-defect` and `cor:independent-bosonic-certificates` (compositions) -/

section Joint

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {V₀ : Measure K} [IsFiniteMeasure V₀]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κG : Type*} [Fintype κG] [DecidableEq κG]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **`thm:joint-defect`, composition form** (`eq:joint-defect-Einstein`): under the Yang–Mills
hypotheses of `prop:YM-defect` and the critical Higgs hypotheses of `thm:higgs-defect`, after a
common extraction the defects `𝔖_{YM}` and `𝔖_H` exist, and for every Einstein constant `κ > 0`,
gravitational first variations with their intended limit, a remaining (fermionic) stress pairing
`Ferm_h(k) → FermLim(k)` (**the conclusion of `prop:weak-matter-equations`**, an explicit hypothesis
here), and vanishing operational residual
`Grav_h(k)/(2κ) - ½ ⟨(T^{YM}_h + T^H_h) dV_{g_h}, k⟩ - ½ Ferm_h(k) → 0`, the limit identity
`(Ein(g) + Λg) dV_g = κ(T^{SM} dV_g + 𝔖_{YM} + 𝔖_H)` holds on every test tensor. -/
theorem joint_defect_einstein
    {g : ℕ → MetricField K} {g₀ : MetricField K} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    {F : ℕ → Fin 4 → Fin 4 → κG → K → ℝ} {F₀ : Fin 4 → Fin 4 → κG → K → ℝ}
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀))
    {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM ∧ IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH ∧
      ∀ (κE : ℝ) (Grav : ℕ → (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ)
        (Ein : (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ)
        (Ferm : ℕ → (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ) (FermLim : (Fin 4 → Fin 4 → C(K, ℝ)) → ℝ),
        0 < κE → (∀ k, Tendsto (fun h => Grav h k) atTop (𝓝 (Ein k))) →
        (∀ k, Tendsto (fun h => Ferm h k) atTop (𝓝 (FermLim k))) →
        (∀ k, Tendsto (fun h => Grav h k / (2 * κE) - (1 / 2) * (
          (∑ μ, ∑ ν, ∫ x, k μ ν x * (ymStress (g h x) (w h) (Fval (F h) x) μ ν *
            vol (g h x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g h x) (lam h) (vH h) (Yval (Y h) x)
            (‖H h x‖ ^ 2) μ ν * vol (g h x)) ∂V₀) + Ferm h k)) atTop (𝓝 0)) →
        ∀ k, Ein k = κE * ((∑ μ, ∑ ν, ∫ x, k μ ν x *
            (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀) +
          (∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x)
            (‖H₀ x‖ ^ 2) μ ν * vol (g₀ x)) ∂V₀) + FermLim k + pairT SYM k + pairT SH k) := by
  obtain ⟨σ₁, hσ₁, QF, hQF⟩ := exists_isDefect hF
  obtain ⟨σ₂, hσ₂, QY, hQY, νH, hν, -, -⟩ := exists_higgs_extraction
    (g := fun h => g (σ₁ h)) (H := fun h => H (σ₁ h)) (Y := fun h => Y (σ₁ h))
    (hg.comp hσ₁.tendsto_atTop) (fun h => hdet _) hdet₀ (fun h => hHm _)
    (hae.mono fun x hx => hx.comp hσ₁.tendsto_atTop) (fun h => hL4 _) (hY.comp hσ₁)
  set σ : ℕ → ℕ := fun h => σ₁ (σ₂ h)
  have hσ : StrictMono σ := hσ₁.comp hσ₂
  have hQFσ : IsDefect V₀ (fun h => Fp (F (σ h))) (Fp F₀) QF := fun P =>
    (hQF P).comp hσ₂.tendsto_atTop
  have hSYM := isYMDefect_of_isDefect hg hdet hdet₀ hw hF hσ hQFσ
  have hK := isKinDefect_of_isDefect hg hdet hdet₀ hY hσ hQY
  have hSH := isHiggsDefect_of hg hdet hdet₀ hHm hae hL4 hY hlam hvH hσ hK hν
  refine ⟨σ, hσ, _, _, hSYM, hSH, fun κE Grav Ein Ferm FermLim hκ hGrav hFerm hres k => ?_⟩
  have hσt := hσ.tendsto_atTop
  have hYM : Tendsto (fun h => ∑ μ, ∑ ν, ∫ x, k μ ν x * (ymStress (g (σ h) x) (w (σ h))
      (Fval (F (σ h)) x) μ ν * vol (g (σ h) x)) ∂V₀) atTop
      (𝓝 (∑ μ, ∑ ν, (∫ x, k μ ν x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀ +
        contract QF (ymCoefF g₀ w₀ μ ν) (k μ ν)))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ => hSYM μ ν (k μ ν)
  have hHg : Tendsto (fun h => ∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g (σ h) x) (lam (σ h))
      (vH (σ h)) (Yval (Y (σ h)) x) (‖H (σ h) x‖ ^ 2) μ ν * vol (g (σ h) x)) ∂V₀) atTop
      (𝓝 (∑ μ, ∑ ν, (∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
        vol (g₀ x)) ∂V₀ + (contract QY (kinCoefF g₀ μ ν) - potDefect lam₀ g₀ νH μ ν) (k μ ν)))) :=
    tendsto_finsetSum _ fun μ _ => tendsto_finsetSum _ fun ν _ => hSH μ ν (k μ ν)
  have hlim := ((hGrav k).comp hσt |>.div_const (2 * κE)).sub
    (((hYM.add hHg).add ((hFerm k).comp hσt)).const_mul (1 / 2))
  have h0 := tendsto_nhds_unique hlim ((hres k).comp hσt)
  simp only [Finset.sum_add_distrib] at h0
  unfold pairT
  set A := ∑ μ, ∑ ν, ∫ x, k μ ν x * (ymStress (g₀ x) w₀ (Fval F₀ x) μ ν * vol (g₀ x)) ∂V₀
  set B := ∑ μ, ∑ ν, ∫ x, k μ ν x * (higgsStress (g₀ x) lam₀ vH₀ (Yval Y₀ x) (‖H₀ x‖ ^ 2) μ ν *
    vol (g₀ x)) ∂V₀
  set P := ∑ μ, ∑ ν, contract QF (ymCoefF g₀ w₀ μ ν) (k μ ν)
  set P' := ∑ μ, ∑ ν, (contract QY (kinCoefF g₀ μ ν) - potDefect lam₀ g₀ νH μ ν) (k μ ν)
  have h1 : Ein k / (2 * κE) = 1 / 2 * (A + P + (B + P') + FermLim k) := by linarith
  have h2 : Ein k = 2 * κE * (Ein k / (2 * κE)) := by field_simp
  rw [h2, h1]
  ring

/-- **`cor:independent-bosonic-certificates`, composition form**: under the hypotheses of
`thm:zero-defect-characterization`, and given the conclusion of `prop:covariant-higgs-endpoint`
in the chart (strong `L²` convergence of the covariant gradients along a subsequence gives strong
`L⁴` convergence of the Higgs fields along it — an explicit hypothesis `hEnd` here), along the
extracted sequence `μ_{∇H} = 0` already implies `ν_H = 0`, and `μ_{YM} = μ_{∇H} = 0` is necessary
and sufficient for the zero-defect branch `𝔖_{YM} + 𝔖_H = 0`. -/
theorem independent_bosonic_certificates
    {g : ℕ → MetricField K} {g₀ : MetricField K} (hg : Tendsto g atTop (𝓝 g₀))
    (hdet : ∀ h x, (mat (g h x)).det ≠ 0) (hdet₀ : ∀ x, (mat (g₀ x)).det ≠ 0)
    {n : C(K, Fin 4 → ℝ)}
    (hsig : ∀ x, ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      mat (g₀ x) = Matrix.transpose P * eta * P)
    (hunit : ∀ x, gnn (g₀ x) (n x) = -1)
    {w : ℕ → κG → ℝ} {w₀ : κG → ℝ} (hw : ∀ a, Tendsto (fun h => w h a) atTop (𝓝 (w₀ a)))
    (hw₀ : ∀ a, 0 < w₀ a)
    {F : ℕ → Fin 4 → Fin 4 → κG → K → ℝ} {F₀ : Fin 4 → Fin 4 → κG → K → ℝ}
    (hF : WeakL2 V₀ (fun h => Fp (F h)) (Fp F₀))
    (hFa : ∀ h α β a x, F h β α a x = -F h α β a x) (hFa₀ : ∀ α β a x, F₀ β α a x = -F₀ α β a x)
    {H : ℕ → K → E} {H₀ : K → E} (hHm : ∀ h, AEStronglyMeasurable (H h) V₀)
    (hae : ∀ᵐ x ∂V₀, Tendsto (fun h => H h x) atTop (𝓝 (H₀ x))) {C : ℝ≥0}
    (hL4 : ∀ h, eLpNorm (H h) 4 V₀ ≤ C)
    {Y : ℕ → Fin 4 → κ → K → ℝ} {Y₀ : Fin 4 → κ → K → ℝ}
    (hY : WeakL2 V₀ (fun h => Yp (Y h)) (Yp Y₀))
    {lam vH : ℕ → ℝ} {lam₀ vH₀ : ℝ} (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hvH : Tendsto vH atTop (𝓝 vH₀)) (hlam₀ : 0 < lam₀)
    (hEnd : ∀ σ : ℕ → ℕ, StrictMono σ → StrongL2 V₀ (fun h => Yp (Y (σ h))) (Yp Y₀) →
      Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ (SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(K, ℝ)) (μYM μH ν : StrongDual ℝ C(K, ℝ)),
      IsYMDefect V₀ g g₀ w w₀ F F₀ σ SYM ∧
      IsHiggsDefect V₀ g g₀ lam vH lam₀ vH₀ Y Y₀ H H₀ σ SH ∧
      (∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Fp (F (σ h)) p x ^ 2 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ∑ p, Fp F₀ p x ^ 2 ∂V₀ + μYM φ))) ∧
      (∀ φ : C(K, ℝ), Tendsto (fun h => ∫ x, φ x * ∑ p, Yp (Y (σ h)) p x ^ 2 ∂V₀) atTop
        (𝓝 (∫ x, φ x * ∑ p, Yp Y₀ p x ^ 2 ∂V₀ + μH φ))) ∧
      IsQuarticDefect V₀ g g₀ H H₀ σ ν ∧
      (μH = 0 → Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) ∧ ν = 0) ∧
      (μYM = 0 ∧ μH = 0 ↔ ∀ μ ν', SYM μ ν' + SH μ ν' = 0) := by
  obtain ⟨σ, hσ, SYM, SH, μYM, μH, ν, hSYM, hSH, htrF, htrY, hν, -, hAB, hBC, hCD, -, hμH,
    hνiff⟩ := zero_defect_characterization hg hdet hdet₀ hsig hunit hw hw₀ hF hFa hFa₀ hHm hae hL4
      hY hlam hvH hlam₀
  have hcert : μH = 0 → Tendsto (fun h => ∫ x, ‖H (σ h) x - H₀ x‖ ^ 4 ∂V₀) atTop (𝓝 0) ∧
      ν = 0 := by
    intro h0
    have hL := hEnd σ hσ (hμH.1 h0)
    exact ⟨hL, hνiff.2 hL⟩
  refine ⟨σ, hσ, SYM, SH, μYM, μH, ν, hSYM, hSH, htrF, htrY, hν, hcert, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact hAB.2 (hBC.2 ⟨h1, h2, (hcert h2).2⟩)
  · intro hA
    obtain ⟨h1, h2, -⟩ := hBC.1 (hAB.1 hA)
    exact ⟨h1, h2⟩

end Joint

/-! ## Non-vacuity: the Minkowski chart with constant fields -/

section NonVacuity

/-- The Minkowski metric as a constant metric field on a one-point chart. -/
noncomputable def minkField : MetricField Unit := ContinuousMap.const Unit eta

/-- The unit time leg `e₀`. -/
def timeLeg : C(Unit, Fin 4 → ℝ) := ContinuousMap.const Unit fun μ => if μ = 0 then 1 else 0

theorem minkField_apply (x : Unit) : minkField x = eta := rfl

theorem det_eta : (mat eta).det = -1 := by
  have : mat eta = eta := rfl
  rw [this, eta, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

theorem minkField_det (x : Unit) : (mat (minkField x)).det ≠ 0 := by
  rw [minkField_apply, det_eta]; norm_num

theorem minkField_frame (x : Unit) : ∃ E, IsTimeFrame (minkField x) (timeLeg x) E := by
  refine ⟨1, ⟨?_, fun μ => ?_⟩⟩
  · rw [minkField_apply]
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · simp [timeLeg, Matrix.one_apply]

theorem minkField_sig (x : Unit) : ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
    mat (minkField x) = Matrix.transpose P * eta * P :=
  ⟨1, by simp, by rw [minkField_apply]; simp only [Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]; rfl⟩

theorem minkField_unit (x : Unit) : gnn (minkField x) (timeLeg x) = -1 := by
  obtain ⟨E, hE⟩ := minkField_frame x
  exact hE.gnn_eq

theorem memLp_unit (V₀ : Measure Unit) [IsFiniteMeasure V₀] (f : Unit → ℝ) : MemLp f 2 V₀ := by
  have : f = fun _ => f () := funext fun x => by cases x; rfl
  rw [this]
  exact memLp_const _

theorem weakL2_const {ι : Type*} (V₀ : Measure Unit) [IsFiniteMeasure V₀] (Y₀ : ι → Unit → ℝ) :
    WeakL2 V₀ (fun _ => Y₀) Y₀ :=
  ⟨fun _ i => memLp_unit V₀ _, fun i => memLp_unit V₀ _, fun _ _ _ => tendsto_const_nhds⟩

/-- **Non-vacuity of `thm:zero-defect-characterization`**: the complete hypothesis packet is
satisfied by the Minkowski metric, the time leg `e₀` (frame `E = 1`), unit Lie weights, `λ = 1`,
and constant fields on a one-point chart. -/
example : ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ (SYM SH : Fin 4 → Fin 4 → StrongDual ℝ C(Unit, ℝ)) (μYM μH ν : StrongDual ℝ C(Unit, ℝ)),
      IsYMDefect (Measure.dirac ()) (fun _ => minkField) minkField (fun _ _ => (1 : ℝ))
        (fun _ : Fin 1 => 1) (fun _ _ _ _ _ => (0 : ℝ)) (fun _ _ _ _ => 0) σ SYM ∧
      ((∀ μ ν', SYM μ ν' + SH μ ν' = 0) ↔ nnPair (fun μ ν' => SYM μ ν' + SH μ ν') timeLeg = 0) ∧
      (μYM = 0 ↔ StrongL2 (Measure.dirac ()) (fun h => Fp (fun _ _ _ _ => (0 : ℝ))) (Fp
        (fun (_ _ : Fin 4) (_ : Fin 1) (_ : Unit) => (0 : ℝ)))) := by
  have hdet : ∀ x, (mat (minkField x)).det ≠ 0 := minkField_det
  obtain ⟨σ, hσ, SYM, SH, μYM, μH, ν, hSYM, -, -, -, -, -, hAB, -, -, hμ, -, -⟩ :=
    zero_defect_characterization (V₀ := Measure.dirac ()) (E := ℝ) (κ := Fin 1)
      (g := fun _ => minkField) (g₀ := minkField) tendsto_const_nhds (fun _ => hdet) hdet
      minkField_sig minkField_unit (w := fun _ _ => (1 : ℝ)) (w₀ := fun _ : Fin 1 => 1)
      (fun _ => tendsto_const_nhds) (fun _ => one_pos)
      (weakL2_const _ (Fp fun _ _ _ _ => (0 : ℝ))) (fun _ _ _ _ _ => by simp)
      (fun _ _ _ _ => by simp) (H := fun _ _ => (1 : ℝ)) (H₀ := fun _ => 1)
      (fun _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => tendsto_const_nhds)
      (C := 1) (fun _ => by
        refine (eLpNorm_le_of_ae_bound (C := 1) (Eventually.of_forall fun _ => by simp)).trans ?_
        simp)
      (weakL2_const _ (Yp fun _ _ _ => (0 : ℝ))) (lam := fun _ => 1) (vH := fun _ => 0)
      tendsto_const_nhds tendsto_const_nhds one_pos
  exact ⟨σ, hσ, SYM, SH, μYM, μH, ν, hSYM, hAB, hμ⟩

/-- Constant sequences carry no defect: along the extraction, the Yang–Mills stress defect of a
constant (hence strongly convergent) curvature packet vanishes (`prop:YM-defect`, last clause). -/
example : ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ S : Fin 4 → Fin 4 → StrongDual ℝ C(Unit, ℝ),
    IsYMDefect (Measure.dirac ()) (fun _ => minkField) minkField (fun _ _ => (1 : ℝ))
      (fun _ : Fin 1 => 1) (fun _ _ _ _ _ => (1 : ℝ)) (fun _ _ _ _ => 1) σ S ∧ ∀ μ ν, S μ ν = 0 := by
  have hdet : ∀ x, (mat (minkField x)).det ≠ 0 := minkField_det
  have hsym : ∀ x μ ν, minkField x μ ν = minkField x ν μ := fun x μ ν => by
    rw [minkField_apply]
    show Matrix.diagonal _ μ ν = Matrix.diagonal _ ν μ
    by_cases h : μ = ν
    · subst h; rfl
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  obtain ⟨σ, hσ, S, hS, -, hzero⟩ := ym_defect (V₀ := Measure.dirac ()) (κ := Fin 1)
    (g := fun _ => minkField) tendsto_const_nhds (fun _ => hdet) hdet (fun _ => hsym) hsym
    (w := fun _ _ => (1 : ℝ)) (w₀ := fun _ => 1) (fun _ => tendsto_const_nhds)
    (weakL2_const _ (Fp fun _ _ _ _ => (1 : ℝ)))
  exact ⟨σ, hσ, S, hS, hzero fun _ => by simp⟩

end NonVacuity
end BosonicStressDefect

end RenewalGeometry
