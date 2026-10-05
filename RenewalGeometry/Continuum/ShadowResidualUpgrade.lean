/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeEulerConsistency
import RenewalGeometry.Continuum.NativeTailTransferBounds
import RenewalGeometry.DiscreteAnalysis.NodalSourceTransferExact
import RenewalGeometry.Analysis.PeriodicCubeSobolevInterpolation

/-!
# Full-record residual interpolation (`prop:shadow-residual-upgrade`)

Einstein–Standard-Model action-closure manuscript, `prop:shadow-residual-upgrade`
(`eq:shadow-zero-residual`, `eq:shadow-eta`, `eq:shadow-strong-residual`), under the regular
reader reserve `eq:shadow-reader-reserve` of `eq:shadow-regularity-indices`.

## Setting (periodic native box)

The periodic auxiliary coordinate box `𝒬 = [0, L)⁴` of period `L` in every coordinate (the paper
has `L = 2π`), the periodic grid `(ℤ/n)⁴` of mesh `h = L/n`, the unchanged local action
`S_h^{loc}` (`NativeDensity.localAction`) with raw Euler row `E_h^{raw}`
(`DiscreteEulerConsistency.eulerRow`), and a smooth `L`-periodic physical field tuple
`z = (e, A, H, Ψ, Ψ̄)` whose nodal samples are the record (for the record of the paper,
`z_h = 𝓘_h^trig u_h`, `TrigInterp.recon_gpos`).  The physical rows are the continuum Euler rows of
the Einstein–Standard-Model Lagrangian: bosonic `𝓡_B(z) = 𝓔₀(z) ∘ ι_B` (`NativeTail.RB`) and
Dirac/dual Dirac `(r_D, r̄_D)(z) = 𝓔₀(z) ∘ ι_S` (`NativeTail.RD`).

Hypotheses (as in the paper): a compact oriented coframe chart `K_e` (the calibrated
inverse-metric margin), the `L^∞` part of the reader reserve
`max_{|α| ≤ s+2} ‖∂^α z‖_∞ ≤ C_R`, and the complete finite Euler-row bound
`σ_h = ‖E_h^{raw}(𝖲_h z)‖_{0,h;Q'} ≤ s_h` on the buffered slab `Q'`.  The cylinders: `Q₁ ⊂ 𝒬`
whose mesh cells have their nodes in `Q'` (the buffer `Q₁ ⋐ Q'`), and `Q₀` on which a smooth
periodic cutoff `χ` (supported in `Q₁` within the box, `|χ| ≤ 1`) is identically `1` near `Q₀`.

## Main results

* `integral_sq_le_nodal_periodic` (generic): the periodic form of `lem:nodal-source-transfer`,
  `∫_{Q₁} |f|² ≤ 2 h⁴ Σ_{x ∈ Q'_h} |f(x)|² + 2 L⁴ (h ‖Df‖_∞)²`.
* `exists_Rfull_bounds`: the reader reserve gives cutoff-independent bounds
  `‖D^j 𝓔₀(z)‖_∞ ≤ M`, `j ≤ s` (`ContEulerBounds.norm_iteratedFDeriv_eulerOp_le` at the fixed
  scale `K = 1`: the Euler rows have differential order two, so `s + 2` derivatives suffice).
* **`shadow_zero_residual`** (`eq:shadow-zero-residual`): `‖𝓔₀(z)‖_{L²(Q₁)} ≤ C_R (s_h + h)`,
  from `prop:native-consistency` at `K = 1` (`NativeEulerConsistency.native_consistency`) and the
  nodal transfer.
* **`shadow_residual_upgrade`** (`prop:shadow-residual-upgrade`): with
  `ε_h = ‖𝓡_B(z)‖_{L²(Q₁)} + ‖(r_D, r̄_D)(z)‖_{L²(Q₁)}`,
  `ε_h ≤ C_R (s_h + h)` and
  `‖𝓡_B(z)‖_{H^k(Q₀)} + ‖(r_D, r̄_D)(z)‖_{H^{k+1}(Q₀)} ≤ C_R (ε_h^{1-k/s} + ε_h^{1-(k+1)/s})`,
  the **full space-time** Sobolev norms (all four directions, `‖f‖²_{H^k(Q₀)} =
  Σ_{j ≤ k} ∫_{Q₀} Σ_{w ∈ {0..3}^j} |∂_{w_1}⋯∂_{w_j} f|²`), by interpolation on the periodic
  box (`PeriodicSobInterp.sobA_le_rpow`) between the zero residual and the cutoff-independent
  `H^s` bound.  The last sentence (`η ≤ 2 C_R ε^{1-(k+1)/s}` for `ε ≤ 1`) is
  `NativeSourceBudget.shadow_eta_le`.

Disclosed renderings: the periodic box (`Σ = 𝕋³`, auxiliary periodic time with the seam outside
`Q'`); `ε_h` is measured on `Q₁` and the `H^k` bound holds on the smaller `Q₀` (the "common
smaller cylinder"); the `H^q` part of the reserve and `k ≥ 4` are not needed.
-/

open Finset Filter Topology Metric Set MeasureTheory
open scoped ContDiff

namespace RenewalGeometry.ShadowResidual

open DiscreteEulerConsistency (R4 evec jet1 contEuler pos samp IsPeriodic eulerRow)
open ShiftedJetAction (Grid)
open NodalSourceTransfer (cell node)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Periodic nodal transfer -/

section Nodal

variable {n : ℕ} [NeZero n]

/-- The integer index of a node. -/
def kOf (x : Grid n) : Fin 4 → ℤ := fun μ => ((x μ).val : ℤ)

theorem node_kOf (h : ℝ) (x : Grid n) : node h (kOf x) = pos h x := by
  funext μ; simp [node, kOf, pos]

theorem kOf_injective : Function.Injective (kOf (n := n)) := by
  intro x x' hx
  funext μ
  have := congrFun hx μ
  simp only [kOf, Nat.cast_inj] at this
  exact ZMod.val_injective n this

/-- The half-open periodic box `[0, L)⁴`. -/
def boxIco (L : ℝ) : Set R4 := Set.pi univ fun _ => Ico 0 L

theorem exists_cell_of_mem_box {h : ℝ} (hh : 0 < h) {y : R4} (hy : y ∈ boxIco ((n : ℝ) * h)) :
    ∃ x : Grid n, y ∈ cell h (kOf x) := by
  obtain ⟨k, hk⟩ := NodalSourceTransfer.exists_mem_cell hh y
  have hb : ∀ μ, 0 ≤ k μ ∧ k μ < n := by
    intro μ
    have h1 := hk μ (mem_univ μ)
    have h2 := hy μ (mem_univ μ)
    constructor
    · by_contra hneg
      push Not at hneg
      have : (k μ : ℝ) ≤ -1 := by exact_mod_cast (show k μ ≤ -1 by omega)
      nlinarith [h1.2, h2.1]
    · by_contra hneg
      push Not at hneg
      have : (n : ℝ) ≤ (k μ : ℝ) := by exact_mod_cast hneg
      nlinarith [h1.1, h2.2]
  refine ⟨fun μ => (((k μ).toNat : ℕ) : ZMod n), ?_⟩
  have e : kOf (fun μ => (((k μ).toNat : ℕ) : ZMod n)) = k := by
    funext μ
    simp only [kOf, ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (by have := hb μ; omega)]
    exact Int.toNat_of_nonneg (hb μ).1
  rw [e]; exact hk

theorem card_grid : (Fintype.card (Grid n) : ℝ) = (n : ℝ) ^ 4 := by
  simp only [ShiftedJetAction.Grid, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  push_cast; ring

theorem cell_subset_Icc (h : ℝ) (k : Fin 4 → ℤ) :
    cell h k ⊆ Icc (node h k) (fun i => h * k i + h) := fun y hy =>
  ⟨fun i => (hy i (mem_univ i)).1, fun i => (hy i (mem_univ i)).2.le⟩

theorem measureReal_cell {h : ℝ} (hh : 0 < h) (k : Fin 4 → ℤ) :
    volume.real (cell h k) = h ^ 4 := by
  rw [measureReal_def, NodalSourceTransfer.volume_cell hh, ENNReal.toReal_ofReal (by positivity)]

open scoped Classical in
/-- **Periodic nodal transfer** (`lem:nodal-source-transfer` on the periodic box): if `Q₁` lies in
the box `[0, nh)⁴`, every mesh cell meeting `Q₁` has its node in `Q'`, and `‖Df‖ ≤ L'`, then
`∫_{Q₁} |f|² ≤ 2 h⁴ Σ_{x : x ∈ Q'} |f(x)|² + 2 (nh)⁴ (h L')²`. -/
theorem integral_sq_le_nodal_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L' : ℝ} (hh : 0 < h) {Q₁ Q' : Set R4} (hQ₁ : Q₁ ⊆ boxIco ((n : ℝ) * h))
    (hbuf : ∀ x : Grid n, (cell h (kOf x) ∩ Q₁).Nonempty → pos h x ∈ Q')
    {f : R4 → E} (hf : Differentiable ℝ f) (hL : ∀ y, ‖fderiv ℝ f y‖ ≤ L') :
    ∫ y in Q₁, ‖f y‖ ^ 2 ≤
      2 * (h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'), ‖f (pos h x)‖ ^ 2) +
        2 * ((n : ℝ) * h) ^ 4 * (h * L') ^ 2 := by
  have hL0 : 0 ≤ L' := (norm_nonneg _).trans (hL 0)
  have hfc : Continuous f := hf.continuous
  set S := Finset.univ.filter (fun x : Grid n => (cell h (kOf x) ∩ Q₁).Nonempty) with hS
  set T := Finset.univ.filter (fun x : Grid n => pos h x ∈ Q') with hT
  have hST : S ⊆ T := fun x hx => by
    simp only [hS, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hbuf x hx
  have hcov : Q₁ ⊆ ⋃ x ∈ S, cell h (kOf x) := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_cell_of_mem_box hh (hQ₁ hy)
    exact mem_biUnion (by simp [hS]; exact ⟨y, hx, hy⟩) hx
  have hFc : Continuous fun y => ‖f y‖ ^ 2 := hfc.norm.pow 2
  have hint : ∀ x : Grid n, IntegrableOn (fun y => ‖f y‖ ^ 2) (cell h (kOf x)) :=
    fun x => (hFc.integrableOn_Icc).mono_set (cell_subset_Icc h _)
  -- pointwise bound on a cell
  have hpt : ∀ x : Grid n, ∀ y ∈ cell h (kOf x),
      ‖f y‖ ^ 2 ≤ 2 * ‖f (pos h x)‖ ^ 2 + 2 * (h * L') ^ 2 := by
    intro x y hy
    have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z)
      (fun z _ => hL z) (mem_univ (node h (kOf x))) (mem_univ y)
    have hd := NodalSourceTransfer.norm_sub_node_le hh hy
    rw [node_kOf] at hmv hd
    have h1 : ‖f y‖ ≤ ‖f (pos h x)‖ + h * L' := by
      calc ‖f y‖ = ‖f (pos h x) + (f y - f (pos h x))‖ := by congr 1; abel
        _ ≤ ‖f (pos h x)‖ + ‖f y - f (pos h x)‖ := norm_add_le _ _
        _ ≤ ‖f (pos h x)‖ + L' * ‖y - pos h x‖ := by linarith
        _ ≤ ‖f (pos h x)‖ + h * L' := by nlinarith
    have hhL : 0 ≤ h * L' := mul_nonneg hh.le hL0
    nlinarith [norm_nonneg (f y), norm_nonneg (f (pos h x)), sq_nonneg (‖f (pos h x)‖ - h * L')]
  have hcell : ∀ x : Grid n, ∫ y in cell h (kOf x), ‖f y‖ ^ 2 ≤
      h ^ 4 * (2 * ‖f (pos h x)‖ ^ 2 + 2 * (h * L') ^ 2) := by
    intro x
    calc ∫ y in cell h (kOf x), ‖f y‖ ^ 2
        ≤ ∫ _ in cell h (kOf x), (2 * ‖f (pos h x)‖ ^ 2 + 2 * (h * L') ^ 2) :=
          setIntegral_mono_on (hint x) (integrableOn_const (by
            rw [NodalSourceTransfer.volume_cell hh]; exact ENNReal.ofReal_ne_top))
            (NodalSourceTransfer.measurableSet_cell h _) (hpt x)
      _ = h ^ 4 * (2 * ‖f (pos h x)‖ ^ 2 + 2 * (h * L') ^ 2) := by
          rw [setIntegral_const, measureReal_cell hh, smul_eq_mul]
  have hdisj : Set.PairwiseDisjoint (↑S) (fun x : Grid n => cell h (kOf x)) := by
    intro x _ x' _ hxx'
    exact NodalSourceTransfer.pairwise_disjoint_cell hh (fun e => hxx' (kOf_injective e))
  calc ∫ y in Q₁, ‖f y‖ ^ 2
      ≤ ∫ y in ⋃ x ∈ S, cell h (kOf x), ‖f y‖ ^ 2 := by
        refine setIntegral_mono_set ?_ (Eventually.of_forall fun y => sq_nonneg _)
          (Eventually.of_forall hcov)
        exact (integrableOn_finset_iUnion).2 fun x _ => hint x
    _ = ∑ x ∈ S, ∫ y in cell h (kOf x), ‖f y‖ ^ 2 :=
        integral_biUnion_finset S (fun x _ => NodalSourceTransfer.measurableSet_cell h _) hdisj
          fun x _ => hint x
    _ ≤ ∑ x ∈ S, h ^ 4 * (2 * ‖f (pos h x)‖ ^ 2 + 2 * (h * L') ^ 2) :=
        Finset.sum_le_sum fun x _ => hcell x
    _ = 2 * (h ^ 4 * ∑ x ∈ S, ‖f (pos h x)‖ ^ 2) + (S.card : ℝ) * (h ^ 4 * (2 * (h * L') ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
        ring_nf
    _ ≤ 2 * (h ^ 4 * ∑ x ∈ T, ‖f (pos h x)‖ ^ 2) + (n : ℝ) ^ 4 * (h ^ 4 * (2 * (h * L') ^ 2)) := by
        have h1 : ∑ x ∈ S, ‖f (pos h x)‖ ^ 2 ≤ ∑ x ∈ T, ‖f (pos h x)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => sq_nonneg _
        have h2 : (S.card : ℝ) ≤ (n : ℝ) ^ 4 := by
          rw [← card_grid]; exact_mod_cast Finset.card_le_univ S
        have h3 : 0 ≤ h ^ 4 * (2 * (h * L') ^ 2) := by positivity
        have h4 : (0 : ℝ) ≤ h ^ 4 := by positivity
        nlinarith
    _ = _ := by ring

end Nodal

/-! ### Periodicity of the continuum Euler rows -/

section Periodic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem jet1_add_of_periodic {Y : R4 → V} {a : R4} (hY : ∀ z, Y (z + a) = Y z) (z : R4) :
    jet1 Y (z + a) = jet1 Y z := by
  have e : (fun z => Y (z + a)) = Y := funext hY
  simp only [jet1]
  rw [← fderiv_comp_add_right, e, hY]

theorem contEuler_add_of_periodic (L : V × (Fin 4 → V) → ℝ) {Y : R4 → V} {a : R4}
    (hY : ∀ z, Y (z + a) = Y z) (z : R4) : contEuler L Y (z + a) = contEuler L Y z := by
  have hj : (fun z => jet1 Y (z + a)) = jet1 Y := funext (jet1_add_of_periodic hY)
  unfold contEuler
  rw [jet1_add_of_periodic hY]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← fderiv_comp_add_right]
  congr 2
  funext z'
  simp only [jet1_add_of_periodic hY]

end Periodic

/-! ### The native residual: fixed-scale bounds and the zero residual -/

section Native

open NativeScaling (Mat)
open NativeDensity
open ContEulerBounds (JS jetP eulerOp)

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

theorem resc_one (Y : R4 → Field 𝔄 𝓗 𝓢) : NativeTail.resc 1 Y = Y := by
  funext ξ; simp [NativeTail.resc]

theorem chart_of_Ke {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hYe : ∀ z, (Y z).1 ∈ Ke) (ξ : R4) :
    (((1 : ℝ)⁻¹, jet1 (NativeTail.resc 1 Y) ξ) : ℝ × JS (Field 𝔄 𝓗 𝓢)) ∈ NativeTail.chartU := by
  rw [resc_one]
  exact (hdet _ (hYe ξ)).ne'

/-- At the fixed scale `K = 1` the continuum Euler covector is the Euler operator of the
gradient map `Gd` at `ν = 1`. -/
theorem Rfull_eq_eulerOp {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) {Y : R4 → Field 𝔄 𝓗 𝓢}
    (hYe : ∀ z, (Y z).1 ∈ Ke) : NativeTail.Rfull D Y = eulerOp (NativeTail.Gd D) 1 Y := by
  funext x
  have h := NativeTail.Rfull_scale D (one_ne_zero) Y (chart_of_Ke hdet hYe) x
  rw [h, resc_one, one_pow, one_smul, one_smul, inv_one]

/-- **Cutoff-independent derivative bounds of the Euler rows from the reader reserve**: for a
compact oriented coframe chart `K_e`, a reserve radius `C_R` and an order `s`, there is `M` such
that every smooth field with coframes in `K_e` and `‖D^j z‖ ≤ C_R` (`j ≤ s + 2`) has a smooth
continuum Euler covector with `‖D^j 𝓔₀(z)‖ ≤ M` for `j ≤ s` (the rows have differential order
two). -/
theorem exists_Rfull_bounds {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (CR : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y → (∀ z, (Y z).1 ∈ Ke) →
      (∀ j ≤ s + 2, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ CR) →
      ContDiff ℝ ∞ (NativeTail.Rfull D Y) ∧
        ∀ j ≤ s, ∀ z, ‖iteratedFDeriv ℝ j (NativeTail.Rfull D Y) z‖ ≤ M := by
  set Bp := max CR 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  set B' := max 1 (5 * Bp) with hB'
  have hB'1 : 1 ≤ B' := le_max_left _ _
  obtain ⟨δ, hδ, M, hM0, hsU, -, hbd, -⟩ :=
    NativeTail.exists_native_constants D hKe hdet Bp Bp (s + 1)
  refine ⟨∑ j ∈ Finset.range (s + 1), ContEulerBounds.cE j * M * B' ^ (j + 1),
    Finset.sum_nonneg fun j _ => by have := ContEulerBounds.cE_nonneg j; positivity, ?_⟩
  intro Y hY hYe hres
  have hres' : ∀ j ≤ s + 2, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ Bp := fun j hj z =>
    (hres j hj z).trans (le_max_left _ _)
  have hch : ∀ z, jetP (1 : ℝ) Y z ∈ NativeTail.chartU := fun z => (hdet _ (hYe z)).ne'
  have hmem : ∀ z, jetP (1 : ℝ) Y z ∈ NativeTail.jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke Bp Bp := by
    intro z
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨hYe z, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have := hres' 0 (Nat.zero_le _) z
      rwa [norm_iteratedFDeriv_zero] at this
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hBp0]
      intro μ
      have h2' := (iteratedFDeriv ℝ 1 Y z).le_opNorm (fun _ => evec μ)
      rw [iteratedFDeriv_one_apply] at h2'
      simp only [DiscreteEulerConsistency.norm_evec, Finset.prod_const_one, mul_one] at h2'
      exact h2'.trans (hres' 1 (by omega) z)
  have hR := Rfull_eq_eulerOp D hdet hYe
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact ContEulerBounds.contDiff_eulerOp (NativeTail.contDiffOn_Gd D) hY hch
  intro j hj z
  rw [hR]
  have hthick : jetP (1 : ℝ) Y z ∈ Metric.cthickening δ
      (NativeTail.jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke Bp Bp) :=
    Metric.self_subset_cthickening _ (hmem z)
  have hb := ContEulerBounds.norm_iteratedFDeriv_eulerOp_le (n := j) NativeTail.isOpen_chartU
    ((NativeTail.contDiffOn_Gd D).of_le (ContEulerBounds.natCast_le_infty _))
    (hY.of_le (ContEulerBounds.natCast_le_infty _)) hch
    (fun k hk => (hbd _ hthick k (by omega)).1) hB'1 (fun p hp1 hp2 => by
      have hJ := ContEulerBounds.norm_iteratedFDeriv_jet1_le (p := p)
        (hY.of_le (ContEulerBounds.natCast_le_infty _)) z
      have a1 := hres' p (by omega) z
      have a2 := hres' (p + 1) (by omega) z
      have : ‖iteratedFDeriv ℝ p Y z‖ + 4 * ‖iteratedFDeriv ℝ (p + 1) Y z‖ ≤ 5 * Bp := by linarith
      exact hJ.trans (this.trans (le_max_right _ _)))
  refine hb.trans ?_
  exact Finset.single_le_sum (f := fun j => ContEulerBounds.cE j * M * B' ^ (j + 1))
    (fun j _ => by have := ContEulerBounds.cE_nonneg j; positivity)
    (Finset.mem_range.2 (by omega))

theorem isPeriodic_of_isPer {V : Type*} {L : ℝ} {Y : R4 → V} (hY : PeriodicSobInterp.IsPer L Y) :
    IsPeriodic L Y := fun z μ => by
  have h := hY (Pi.single μ 1) z
  have e : L • PeriodicCube.zvec (Pi.single μ (1 : ℤ)) = (Pi.single μ L : R4) := by
    funext i
    by_cases hi : i = μ
    · subst hi; simp [PeriodicCube.zvec]
    · simp [PeriodicCube.zvec, Pi.single_apply, hi]
  rw [e] at h
  exact h

theorem isPer_Rfull {L : ℝ} {Y : R4 → Field 𝔄 𝓗 𝓢} (hY : PeriodicSobInterp.IsPer L Y) :
    PeriodicSobInterp.IsPer L (NativeTail.Rfull D Y) := fun k x =>
  contEuler_add_of_periodic _ (fun z => hY k z) x

theorem volume_boxIco {L : ℝ} (hL : 0 ≤ L) : volume.real (boxIco L) = L ^ 4 := by
  rw [measureReal_def, boxIco, Real.volume_pi_Ico]
  simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hL, ENNReal.toReal_ofReal (by positivity)]

theorem boxIco_subset_Icc (L : ℝ) : boxIco L ⊆ Icc (0 : R4) (fun _ => L) := fun y hy =>
  ⟨fun i => (hy i (mem_univ i)).1, fun i => (hy i (mem_univ i)).2.le⟩

theorem measurableSet_boxIco (L : ℝ) : MeasurableSet (boxIco L) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- `∫_Q |f|² ≤ L⁴ M²` for `Q` inside the box and `|f| ≤ M`. -/
theorem integral_sq_le_box {E : Type*} [NormedAddCommGroup E] {L M : ℝ} (hL : 0 ≤ L)
    {Q : Set R4} (hQ : Q ⊆ boxIco L) {f : R4 → E} (hf : Continuous f) (hM : ∀ y, ‖f y‖ ≤ M) :
    ∫ y in Q, ‖f y‖ ^ 2 ≤ L ^ 4 * M ^ 2 := by
  have hint : IntegrableOn (fun y => ‖f y‖ ^ 2) (boxIco L) :=
    ((hf.norm.pow 2).integrableOn_Icc).mono_set (boxIco_subset_Icc L)
  calc ∫ y in Q, ‖f y‖ ^ 2 ≤ ∫ y in boxIco L, ‖f y‖ ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun y => sq_nonneg _)
          (Eventually.of_forall hQ)
    _ ≤ ∫ _ in boxIco L, M ^ 2 := by
        refine setIntegral_mono_on hint (integrableOn_const (by
          rw [boxIco, Real.volume_pi_Ico]; simp)) (measurableSet_boxIco L) fun y _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (hM y) 2
    _ = L ^ 4 * M ^ 2 := by rw [setIntegral_const, volume_boxIco hL, smul_eq_mul]

open scoped Classical in
/-- **`eq:shadow-zero-residual`**: on the periodic box of period `L`, for a compact oriented chart
`K_e`, a reserve radius `C_R`, a cylinder `Q₁` in the box and a buffered slab `Q'`, there is `C`
such that for every grid `n`, mesh `h = L/n` and smooth `L`-periodic field `z` with coframes in
`K_e`, `‖D^j z‖ ≤ C_R` (`j ≤ 3`), every mesh cell meeting `Q₁` having its node in `Q'`, and the
complete finite Euler-row norm `σ_h = (h⁴ Σ_{x ∈ Q'_h} |E_h^{raw}(𝖲_h z)(x)|²)^{1/2} ≤ s_h`:
`‖𝓔₀(z)‖²_{L²(Q₁)} ≤ (C (s_h + h))²`.  Proof: `prop:native-consistency` at the fixed scale
`K = 1` at every node, then the periodic nodal transfer; for `h` beyond the consistency range the
bound follows from the `L^∞` bound of the rows. -/
theorem shadow_zero_residual {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (CR : ℝ) {L : ℝ} (hL : 0 < L) {Q₁ Q' : Set R4} (hQ₁ : Q₁ ⊆ boxIco L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (h : ℝ), 0 < h → (n : ℝ) * h = L →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y → PeriodicSobInterp.IsPer L Y →
        (∀ z, (Y z).1 ∈ Ke) → (∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ CR) →
        (∀ x : Grid n, (cell h (kOf x) ∩ Q₁).Nonempty → pos h x ∈ Q') →
        ∀ sh : ℝ, 0 ≤ sh →
        h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
          ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2 ≤ sh ^ 2 →
        ∫ y in Q₁, ‖NativeTail.Rfull D Y y‖ ^ 2 ≤ (C * (sh + h)) ^ 2 := by
  obtain ⟨C₁, c_res, hc, hmain⟩ := NativeEulerConsistency.native_consistency D hKe hdet CR CR
  obtain ⟨M₁, hM₁, hRb⟩ := exists_Rfull_bounds D hKe hdet CR 1
  set C := 2 + 2 * L ^ 2 * |C₁| + 2 * L ^ 2 * M₁ + L ^ 2 * M₁ / c_res with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, ?_⟩
  intro n _ h hh hnh Y hY hper hYe hres hbuf sh hsh hσ
  obtain ⟨hRs, hRd⟩ := hRb Y hY hYe hres
  have hR0 : ∀ y, ‖NativeTail.Rfull D Y y‖ ≤ M₁ := fun y => by
    have := hRd 0 (Nat.zero_le _) y; rwa [norm_iteratedFDeriv_zero] at this
  have hR1 : ∀ y, ‖fderiv ℝ (NativeTail.Rfull D Y) y‖ ≤ M₁ := fun y => by
    have := hRd 1 le_rfl y; rwa [norm_iteratedFDeriv_one] at this
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  rcases le_or_gt h c_res with hhc | hhc
  · -- the consistency range
    have hK := hmain 1 le_rfl h hh (by simpa using hhc) n Y
      (hY.of_le (ContEulerBounds.natCast_le_infty _)) (by rw [hnh]; exact isPeriodic_of_isPer hper)
      hYe (fun z => by have := hres 0 (by omega) z; rwa [norm_iteratedFDeriv_zero] at this)
      (fun z => by simpa using hres 1 (by omega) z) (fun z => by simpa using hres 2 (by omega) z)
      (fun z => by simpa using hres 3 le_rfl z)
    have hnode : ∀ x : Grid n, ‖NativeTail.Rfull D Y (pos h x)‖ ^ 2 ≤
        2 * ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2 + 2 * (|C₁| * h) ^ 2 := by
      intro x
      have h1 := hK.2.2 x
      rw [one_pow, mul_one] at h1
      have h2 : ‖NativeTail.Rfull D Y (pos h x)‖ ≤
          ‖eulerRow (localAction D h) h (samp h Y) x‖ + |C₁| * h := by
        have e : NativeTail.Rfull D Y (pos h x) = eulerRow (localAction D h) h (samp h Y) x -
            (eulerRow (localAction D h) h (samp h Y) x -
              contEuler (DiscreteEulerConsistency.limDensity (ι := Shift) (firstJetDensity D)) Y
                (pos h x)) := by
          rw [sub_sub_cancel]; rfl
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        have : C₁ * h ≤ |C₁| * h := mul_le_mul_of_nonneg_right (le_abs_self _) hh.le
        linarith
      have h3 : 0 ≤ |C₁| * h := by positivity
      nlinarith [norm_nonneg (NativeTail.Rfull D Y (pos h x)),
        norm_nonneg (eulerRow (localAction D h) h (samp h Y) x),
        sq_nonneg (‖eulerRow (localAction D h) h (samp h Y) x‖ - |C₁| * h)]
    set T := Finset.univ.filter (fun x : Grid n => pos h x ∈ Q') with hT
    have hsum : h ^ 4 * ∑ x ∈ T, ‖NativeTail.Rfull D Y (pos h x)‖ ^ 2 ≤
        2 * sh ^ 2 + 2 * L ^ 4 * (|C₁| * h) ^ 2 := by
      have hcard : (T.card : ℝ) ≤ (n : ℝ) ^ 4 := by
        rw [← card_grid]; exact_mod_cast Finset.card_le_univ T
      calc h ^ 4 * ∑ x ∈ T, ‖NativeTail.Rfull D Y (pos h x)‖ ^ 2
          ≤ h ^ 4 * ∑ x ∈ T, (2 * ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2 +
              2 * (|C₁| * h) ^ 2) := by
            gcongr with x; exact hnode x
        _ = 2 * (h ^ 4 * ∑ x ∈ T, ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2) +
              2 * (h ^ 4 * T.card) * (|C₁| * h) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]; ring
        _ ≤ 2 * sh ^ 2 + 2 * L ^ 4 * (|C₁| * h) ^ 2 := by
            have e : h ^ 4 * (n : ℝ) ^ 4 = L ^ 4 := by rw [← hnh]; ring
            have : h ^ 4 * (T.card : ℝ) ≤ L ^ 4 := by
              rw [← e]; exact mul_le_mul_of_nonneg_left hcard (by positivity)
            have h5 : 0 ≤ (|C₁| * h) ^ 2 := sq_nonneg _
            nlinarith
    have htr := integral_sq_le_nodal_periodic (n := n) hh (by rw [hnh]; exact hQ₁) hbuf
      (hRs.differentiable (by simp)) hR1
    rw [hnh] at htr
    calc ∫ y in Q₁, ‖NativeTail.Rfull D Y y‖ ^ 2
        ≤ 2 * (2 * sh ^ 2 + 2 * L ^ 4 * (|C₁| * h) ^ 2) + 2 * L ^ 4 * (h * M₁) ^ 2 := by
          refine htr.trans ?_
          gcongr
      _ ≤ (C * (sh + h)) ^ 2 := by
          have hA : 2 + 2 * L ^ 2 * |C₁| + 2 * L ^ 2 * M₁ ≤ C := by
            have : 0 ≤ L ^ 2 * M₁ / c_res := by positivity
            simp only [hCdef]; linarith
          have hA0 : 0 ≤ 2 + 2 * L ^ 2 * |C₁| + 2 * L ^ 2 * M₁ := by positivity
          have hsq : (2 + 2 * L ^ 2 * |C₁| + 2 * L ^ 2 * M₁) ^ 2 * (sh + h) ^ 2 ≤
              (C * (sh + h)) ^ 2 := by
            rw [mul_pow]; gcongr
          refine le_trans ?_ hsq
          set a := L ^ 2 * |C₁| with ha
          set b := L ^ 2 * M₁ with hb
          have ha0 : 0 ≤ a := by positivity
          have hb0 : 0 ≤ b := by positivity
          have e1 : L ^ 4 * (|C₁| * h) ^ 2 = (a * h) ^ 2 := by simp only [ha]; ring
          have e2 : L ^ 4 * (h * M₁) ^ 2 = (b * h) ^ 2 := by simp only [hb]; ring
          rw [show 2 * (2 * sh ^ 2 + 2 * L ^ 4 * (|C₁| * h) ^ 2) + 2 * L ^ 4 * (h * M₁) ^ 2 =
            4 * sh ^ 2 + 4 * (L ^ 4 * (|C₁| * h) ^ 2) + 2 * (L ^ 4 * (h * M₁) ^ 2) by ring, e1, e2]
          have hsh0 := mul_nonneg hsh hh.le
          nlinarith [mul_nonneg ha0 hb0, mul_nonneg hsh0 ha0, mul_nonneg hsh0 hb0,
            mul_nonneg (mul_nonneg hsh0 ha0) hb0, mul_nonneg (sq_nonneg h) (mul_nonneg ha0 hb0),
            mul_nonneg (sq_nonneg sh) ha0, mul_nonneg (sq_nonneg sh) hb0,
            mul_nonneg (sq_nonneg h) ha0, mul_nonneg (sq_nonneg h) hb0,
            mul_nonneg (sq_nonneg sh) (sq_nonneg a), mul_nonneg (sq_nonneg sh) (sq_nonneg b),
            mul_nonneg hsh0 (sq_nonneg a), mul_nonneg hsh0 (sq_nonneg b)]
  · -- beyond the consistency range: `L^∞` bound
    have hb := integral_sq_le_box hL.le hQ₁ hRs.continuous hR0
    refine hb.trans ?_
    have h1 : L ^ 2 * M₁ ≤ C * h := by
      have : L ^ 2 * M₁ ≤ L ^ 2 * M₁ / c_res * h := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        exact mul_le_mul_of_nonneg_left hhc.le (by positivity)
      have hle : L ^ 2 * M₁ / c_res ≤ C := by
        simp only [hCdef]
        have : 0 ≤ 2 * L ^ 2 * |C₁| := by positivity
        have : 0 ≤ 2 * L ^ 2 * M₁ := by positivity
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hle hh.le]
    have h2 : C * h ≤ C * (sh + h) := mul_le_mul_of_nonneg_left (by linarith) hC0
    have h3 : 0 ≤ L ^ 2 * M₁ := by positivity
    calc L ^ 4 * M₁ ^ 2 = (L ^ 2 * M₁) ^ 2 := by ring
      _ ≤ (C * (sh + h)) ^ 2 := pow_le_pow_left₀ h3 (h1.trans h2) 2

end Native

/-! ### Cutoff interpolation on the periodic box -/

section Cutoff

open PeriodicSobInterp (pw sobA cube IsPer)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The squared space-time Sobolev norm on a set: `‖f‖²_{H^k(Q)} = Σ_{j ≤ k} ∫_Q pw f j`
(all ordered partial derivatives of order `≤ k` in the four space-time directions). -/
def hkSq (k : ℕ) (Q : Set R4) (f : R4 → V) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∫ y in Q, pw f j y

/-- The `L²(Q)` norm. -/
def l2Q (Q : Set R4) (f : R4 → V) : ℝ := Real.sqrt (∫ y in Q, ‖f y‖ ^ 2)

theorem pw_le_norm_sq (f : R4 → V) (j : ℕ) (y : R4) :
    pw f j y ≤ 4 ^ j * ‖iteratedFDeriv ℝ j f y‖ ^ 2 := by
  unfold pw
  have hcard : (Fintype.card (Fin j → Fin 4) : ℝ) = 4 ^ j := by simp
  calc ∑ w : Fin j → Fin 4, ‖iteratedFDeriv ℝ j f y (PeriodicSobInterp.evw w)‖ ^ 2
      ≤ ∑ _w : Fin j → Fin 4, ‖iteratedFDeriv ℝ j f y‖ ^ 2 := by
        refine Finset.sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine ((iteratedFDeriv ℝ j f y).le_opNorm _).trans (le_of_eq ?_)
        simp [PeriodicSobInterp.evw, Pi.norm_single]
    _ = 4 ^ j * ‖iteratedFDeriv ℝ j f y‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

theorem volume_cube_real {L : ℝ} (hL : 0 ≤ L) : volume.real (cube (ι := Fin 4) L) = L ^ 4 := by
  rw [measureReal_def, PeriodicSobInterp.cube, Real.volume_Icc_pi]
  simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hL, ENNReal.toReal_ofReal (by positivity)]

theorem boxIco_subset_cube (L : ℝ) : boxIco L ⊆ cube (ι := Fin 4) L := boxIco_subset_Icc L

variable [FiniteDimensional ℝ V]

/-- **Cutoff interpolation on the periodic box** (generic): let `χ` be a smooth `L`-periodic
cutoff with `|χ| ≤ 1`, `χ = 0` on the box outside `Q₁`, `χ ≡ 1` near every point of `Q₀`, and
`‖D^jχ‖ ≤ B_χ` (`j ≤ s`).  For a smooth `L`-periodic `f` with `‖D^j f‖ ≤ M_f` (`j ≤ s`) and
`‖f‖²_{L²(Q₁)} ≤ ε²`, every `j ≤ s` has
`∫_{Q₀} pw f j ≤ C_j (ε^{1-j/s})²` with
`C_j = C_{V,j,s}^{1/s} M^{2j/s}`, `M² = L⁴ 4^s (2^s B_χ M_f)²` (the `H^s` bound of `χ f`). -/
theorem cutoff_interp {L : ℝ} (hL : 0 < L) {Q₀ Q₁ : Set R4} (hQ₀m : MeasurableSet Q₀)
    (hQ₁m : MeasurableSet Q₁) (hQ₀ : Q₀ ⊆ boxIco L) (hQ₁ : Q₁ ⊆ boxIco L) {s : ℕ} (hs : 0 < s)
    {χ : R4 → ℝ} (hχs : ContDiff ℝ ∞ χ) (hχp : IsPer L χ) (hχ1 : ∀ y, |χ y| ≤ 1)
    (hχ0 : ∀ y ∈ boxIco L, y ∉ Q₁ → χ y = 0) (hχQ : ∀ y ∈ Q₀, ∀ᶠ z in 𝓝 y, χ z = 1)
    {Bχ : ℝ} (hχB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ Bχ)
    {f : R4 → V} (hf : ContDiff ℝ ∞ f) (hfp : IsPer L f) {Mf : ℝ}
    (hfB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ Mf) {ε : ℝ} (hε : 0 ≤ ε)
    (hεf : ∫ y in Q₁, ‖f y‖ ^ 2 ≤ ε ^ 2) {j : ℕ} (hj : j ≤ s) :
    ∫ y in Q₀, pw f j y ≤ PeriodicSobInterp.interpConst V (Fin 4) j s ^ (1 / (s : ℝ)) *
      (L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * Mf)) ^ (2 * (j : ℝ) / s) * (ε ^ (1 - (j : ℝ) / s)) ^ 2 := by
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hχB 0 (Nat.zero_le _) 0)
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hfB 0 (Nat.zero_le _) 0)
  set g : R4 → V := fun y => χ y • f y with hg
  have hgs : ContDiff ℝ ∞ g := hχs.smul hf
  have hgp : IsPer L g := fun k x => by simp only [hg, hχp k x, hfp k x]
  -- the zero-order energy of `g`
  have h0 : sobA L g 0 ≤ ε ^ 2 := by
    unfold sobA
    simp_rw [PeriodicSobInterp.pw_zero]
    have hae : (boxIco L : Set R4) =ᵐ[volume] cube (ι := Fin 4) L := by
      unfold boxIco PeriodicSobInterp.cube
      exact Measure.univ_pi_Ico_ae_eq_Icc
    rw [← setIntegral_congr_set hae]
    have hint : IntegrableOn (fun y => ‖f y‖ ^ 2) (boxIco L) :=
      ((hf.continuous.norm.pow 2).integrableOn_Icc).mono_set (boxIco_subset_Icc L)
    calc ∫ y in boxIco L, ‖g y‖ ^ 2 ≤ ∫ y in boxIco L, Q₁.indicator (fun y => ‖f y‖ ^ 2) y := by
          refine setIntegral_mono_on ?_ (hint.indicator hQ₁m) (measurableSet_boxIco L)
            fun y hy => ?_
          · exact ((hgs.continuous.norm.pow 2).integrableOn_Icc).mono_set (boxIco_subset_Icc L)
          · by_cases hyQ : y ∈ Q₁
            · rw [Set.indicator_of_mem hyQ]
              simp only [hg, norm_smul, Real.norm_eq_abs, mul_pow]
              have : |χ y| ^ 2 ≤ 1 := by
                rw [sq_le_one_iff_abs_le_one, abs_abs]; exact hχ1 y
              nlinarith [sq_nonneg ‖f y‖]
            · rw [Set.indicator_of_notMem hyQ]
              simp only [hg]
              rw [hχ0 y hy hyQ]
              simp
      _ = ∫ y in Q₁, ‖f y‖ ^ 2 := by
          rw [setIntegral_indicator hQ₁m, Set.inter_eq_right.2 hQ₁]
      _ ≤ ε ^ 2 := hεf
  -- the order-`s` energy of `g`
  set Mg := L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * Mf) with hMg
  have hMg0 : 0 ≤ Mg := by positivity
  have hS : sobA L g s ≤ Mg ^ 2 := by
    have hpt : ∀ y, pw g s y ≤ 4 ^ s * (2 ^ s * Bχ * Mf) ^ 2 := by
      intro y
      refine (pw_le_norm_sq g s y).trans ?_
      gcongr
      refine (norm_iteratedFDeriv_smul_le hχs hf y (by exact_mod_cast le_top)).trans ?_
      calc ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
            ‖iteratedFDeriv ℝ (s - i) f y‖
          ≤ ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * Bχ * Mf := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have := hχB i hi' y
            have := hfB (s - i) (Nat.sub_le _ _) y
            gcongr
        _ = 2 ^ s * Bχ * Mf := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            congr 2
            exact_mod_cast Nat.sum_range_choose s
    unfold sobA
    calc ∫ y in cube L, pw g s y ≤ ∫ _ in cube (ι := Fin 4) L, 4 ^ s * (2 ^ s * Bχ * Mf) ^ 2 := by
          refine setIntegral_mono_on (PeriodicSobInterp.integrableOn_cube
            (PeriodicSobInterp.continuous_pw hgs s) L) (integrableOn_const (by
              rw [PeriodicSobInterp.cube, Real.volume_Icc_pi]; simp)) measurableSet_Icc
            fun y _ => hpt y
      _ = Mg ^ 2 := by
          rw [setIntegral_const, volume_cube_real hL.le, smul_eq_mul, hMg,
            show (4 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) by rw [pow_mul]; norm_num]
          ring
  have hI := PeriodicSobInterp.sobA_le_rpow hL hgs hgp hj hs hε hMg0 h0 hS
  refine le_trans ?_ hI
  -- `pw f j = pw g j` on `Q₀`
  have heq : ∀ y ∈ Q₀, pw f j y = pw g j y := by
    intro y hy
    have hfg : g =ᶠ[𝓝 y] f := (hχQ y hy).mono fun z hz => by simp [hg, hz]
    have := (hfg.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [pw, this]
  calc ∫ y in Q₀, pw f j y = ∫ y in Q₀, pw g j y := setIntegral_congr_fun hQ₀m heq
    _ ≤ sobA L g j := by
        unfold sobA
        exact setIntegral_mono_set (PeriodicSobInterp.integrableOn_cube
          (PeriodicSobInterp.continuous_pw hgs j) L)
          (Eventually.of_forall fun y => PeriodicSobInterp.pw_nonneg g j y)
          (Eventually.of_forall fun y hy => boxIco_subset_cube L (hQ₀ hy))

/-- `ε^a ≤ max(1, E) ε^b` for `0 ≤ ε ≤ E` and `0 ≤ b ≤ a ≤ 1`. -/
theorem rpow_le_max_mul_rpow {ε E a b : ℝ} (hε : 0 ≤ ε) (hεE : ε ≤ E) (hb : 0 ≤ b) (hab : b ≤ a)
    (ha : a ≤ 1) : ε ^ a ≤ max 1 E * ε ^ b := by
  rcases le_or_gt ε 1 with h1 | h1
  · calc ε ^ a ≤ ε ^ b := Real.rpow_le_rpow_of_exponent_ge' hε h1 hb hab
      _ ≤ max 1 E * ε ^ b := le_mul_of_one_le_left (Real.rpow_nonneg hε _) (le_max_left _ _)
  · calc ε ^ a ≤ ε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le ha
      _ = ε := Real.rpow_one ε
      _ ≤ max 1 E := hεE.trans (le_max_right _ _)
      _ ≤ max 1 E * ε ^ b := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow h1.le hb)

/-- **Sobolev upgrade of a residual by cutoff interpolation**: under the hypotheses of
`cutoff_interp`, with `k ≤ s` and `ε ≤ E`,
`‖f‖_{H^k(Q₀)} ≤ C ε^{1-k/s}` with `C = max(1,E) (Σ_{j ≤ k} C_j)^{1/2}`. -/
theorem hkSq_sqrt_le {L : ℝ} (hL : 0 < L) {Q₀ Q₁ : Set R4} (hQ₀m : MeasurableSet Q₀)
    (hQ₁m : MeasurableSet Q₁) (hQ₀ : Q₀ ⊆ boxIco L) (hQ₁ : Q₁ ⊆ boxIco L) {s : ℕ} (hs : 0 < s)
    {χ : R4 → ℝ} (hχs : ContDiff ℝ ∞ χ) (hχp : IsPer L χ) (hχ1 : ∀ y, |χ y| ≤ 1)
    (hχ0 : ∀ y ∈ boxIco L, y ∉ Q₁ → χ y = 0) (hχQ : ∀ y ∈ Q₀, ∀ᶠ z in 𝓝 y, χ z = 1)
    {Bχ : ℝ} (hχB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ Bχ)
    {f : R4 → V} (hf : ContDiff ℝ ∞ f) (hfp : IsPer L f) {Mf : ℝ}
    (hfB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ Mf) {ε E : ℝ} (hε : 0 ≤ ε) (hεE : ε ≤ E)
    (hεf : ∫ y in Q₁, ‖f y‖ ^ 2 ≤ ε ^ 2) {k : ℕ} (hk : k ≤ s) :
    Real.sqrt (hkSq k Q₀ f) ≤ max 1 E * Real.sqrt (∑ j ∈ Finset.range (k + 1),
      PeriodicSobInterp.interpConst V (Fin 4) j s ^ (1 / (s : ℝ)) *
        (L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * Mf)) ^ (2 * (j : ℝ) / s)) * ε ^ (1 - (k : ℝ) / s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  set c : ℕ → ℝ := fun j => PeriodicSobInterp.interpConst V (Fin 4) j s ^ (1 / (s : ℝ)) *
    (L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * Mf)) ^ (2 * (j : ℝ) / s) with hc
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hχB 0 (Nat.zero_le _) 0)
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hfB 0 (Nat.zero_le _) 0)
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    have := PeriodicSobInterp.interpConst_nonneg (V := V) (ι := Fin 4) j s
    simp only [hc]; positivity
  have hE1 : 0 ≤ max 1 E := le_trans zero_le_one (le_max_left _ _)
  have hterm : ∀ j ∈ Finset.range (k + 1), ∫ y in Q₀, pw f j y ≤
      c j * (max 1 E * ε ^ (1 - (k : ℝ) / s)) ^ 2 := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine (cutoff_interp hL hQ₀m hQ₁m hQ₀ hQ₁ hs hχs hχp hχ1 hχ0 hχQ hχB hf hfp hfB hε hεf
      (hjk.trans hk)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hc0 j)
    have hjs : (j : ℝ) / s ≤ (k : ℝ) / s := div_le_div_of_nonneg_right (by exact_mod_cast hjk) hsR.le
    have hks : (k : ℝ) / s ≤ 1 := (div_le_one hsR).2 (by exact_mod_cast hk)
    have hj0 : 0 ≤ (j : ℝ) / s := by positivity
    exact pow_le_pow_left₀ (Real.rpow_nonneg hε _)
      (rpow_le_max_mul_rpow hε hεE (by linarith) (by linarith) (by linarith)) 2
  have hsum : hkSq k Q₀ f ≤ (∑ j ∈ Finset.range (k + 1), c j) *
      (max 1 E * ε ^ (1 - (k : ℝ) / s)) ^ 2 := by
    unfold hkSq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hS0 : 0 ≤ ∑ j ∈ Finset.range (k + 1), c j := Finset.sum_nonneg fun j _ => hc0 j
  calc Real.sqrt (hkSq k Q₀ f) ≤ Real.sqrt ((∑ j ∈ Finset.range (k + 1), c j) *
        (max 1 E * ε ^ (1 - (k : ℝ) / s)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (∑ j ∈ Finset.range (k + 1), c j) * (max 1 E * ε ^ (1 - (k : ℝ) / s)) := by
        rw [Real.sqrt_mul hS0, Real.sqrt_sq (mul_nonneg hE1 (Real.rpow_nonneg hε _))]
    _ = max 1 E * Real.sqrt (∑ j ∈ Finset.range (k + 1), c j) * ε ^ (1 - (k : ℝ) / s) := by ring

end Cutoff

/-! ### `prop:shadow-residual-upgrade` -/

section Main

open NativeScaling (Mat)
open NativeDensity
open PeriodicSobInterp (IsPer)

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The residual size `ε_h = ‖𝓡_B(z)‖_{L²(Q₁)} + ‖(r_D, r̄_D)(z)‖_{L²(Q₁)}`
(`eq:shadow-zero-residual`). -/
def residualEps (Q₁ : Set R4) (Y : R4 → Field 𝔄 𝓗 𝓢) : ℝ :=
  l2Q Q₁ (NativeTail.RB D Y) + l2Q Q₁ (NativeTail.RD D Y)

/-- Bounds transported through a linear map of norm `≤ 1`. -/
theorem comp_bounds {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (P : V →L[ℝ] W) (hP : ‖P‖ ≤ 1) {F : R4 → V} (hF : ContDiff ℝ ∞ F) {L : ℝ}
    (hFp : IsPer L F) {s : ℕ} {M : ℝ} (hFB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ M) :
    ContDiff ℝ ∞ (⇑P ∘ F) ∧ IsPer L (⇑P ∘ F) ∧
      (∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j (⇑P ∘ F) y‖ ≤ M) ∧ ∀ y, ‖(⇑P ∘ F) y‖ ≤ ‖F y‖ := by
  refine ⟨P.contDiff.comp hF, hFp.comp _, fun j hj y => ?_, fun y => ?_⟩
  · refine (P.norm_iteratedFDeriv_comp_left hF.contDiffAt
      (PeriodicSobInterp.natCast_le_infty j)).trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) hP).trans (hFB j hj y)
  · exact (P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hP)

theorem RB_eq_comp (Y : R4 → Field 𝔄 𝓗 𝓢) :
    NativeTail.RB D Y = ⇑(ContEulerBounds.preL (NativeTail.ιB (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))) ∘
      NativeTail.Rfull D Y := rfl

theorem RD_eq_comp (Y : R4 → Field 𝔄 𝓗 𝓢) :
    NativeTail.RD D Y = ⇑(ContEulerBounds.preL (NativeTail.ιS (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))) ∘
      NativeTail.Rfull D Y := rfl

/-- `‖g‖_{L²(Q)} ≤ C` from `∫_Q |g|² ≤ C²`. -/
theorem l2Q_le_of_sq {V : Type*} [NormedAddCommGroup V] {Q : Set R4} {g : R4 → V} {C : ℝ}
    (hC : 0 ≤ C) (h : ∫ y in Q, ‖g y‖ ^ 2 ≤ C ^ 2) : l2Q Q g ≤ C := by
  unfold l2Q
  calc Real.sqrt (∫ y in Q, ‖g y‖ ^ 2) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

theorem l2Q_nonneg {V : Type*} [NormedAddCommGroup V] (Q : Set R4) (g : R4 → V) : 0 ≤ l2Q Q g :=
  Real.sqrt_nonneg _

theorem sq_l2Q {V : Type*} [NormedAddCommGroup V] (Q : Set R4) (g : R4 → V) :
    ∫ y in Q, ‖g y‖ ^ 2 = l2Q Q g ^ 2 := by
  unfold l2Q
  rw [Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]

open scoped Classical in
/-- **`prop:shadow-residual-upgrade`** (periodic native box of period `L`; `Σ = 𝕋³`).  Fix integers
`k`, `s` with `s > k + 1` (`eq:shadow-regularity-indices`; `k ≥ 4` and `q` are not needed), a compact
oriented coframe chart `K_e`, a reserve radius `C_R`, cylinders `Q₀`, `Q₁ ⊂ [0, L)⁴`, a buffered
slab `Q'`, and a smooth `L`-periodic cutoff `χ` with `|χ| ≤ 1`, `χ = 0` on the box outside `Q₁`,
`χ ≡ 1` near `Q₀` and `‖D^jχ‖ ≤ B_χ` (`j ≤ s`).  There is `C_R' ≥ 0` such that for every grid
`n`, mesh `h = L/n` and smooth `L`-periodic physical field `z` with coframes in `K_e` and the
`L^∞` reader reserve `max_{j ≤ s+2} ‖D^j z‖_∞ ≤ C_R` (`eq:shadow-reader-reserve`), every mesh cell
meeting `Q₁` having its node in `Q'`, and complete finite Euler-row norm `σ_h ≤ s_h`:
1. `ε_h = ‖𝓡_B(z)‖_{L²(Q₁)} + ‖(r_D, r̄_D)(z)‖_{L²(Q₁)} ≤ C_R' (s_h + h)`
   (`eq:shadow-zero-residual`);
2. `‖𝓡_B(z)‖_{H^k(Q₀)} + ‖(r_D, r̄_D)(z)‖_{H^{k+1}(Q₀)} ≤ C_R' (ε_h^{1-k/s} + ε_h^{1-(k+1)/s})
   = η_{h,k}` (`eq:shadow-eta`, `eq:shadow-strong-residual`), with the full space-time Sobolev
   norms (`hkSq`). -/
theorem shadow_residual_upgrade {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (CR : ℝ) {k s : ℕ} (hks : k + 1 < s) {L : ℝ} (hL : 0 < L) {Q₀ Q₁ Q' : Set R4}
    (hQ₀m : MeasurableSet Q₀) (hQ₁m : MeasurableSet Q₁) (hQ₀ : Q₀ ⊆ boxIco L)
    (hQ₁ : Q₁ ⊆ boxIco L) {χ : R4 → ℝ} (hχs : ContDiff ℝ ∞ χ) (hχp : IsPer L χ)
    (hχ1 : ∀ y, |χ y| ≤ 1) (hχ0 : ∀ y ∈ boxIco L, y ∉ Q₁ → χ y = 0)
    (hχQ : ∀ y ∈ Q₀, ∀ᶠ z in 𝓝 y, χ z = 1) {Bχ : ℝ}
    (hχB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ Bχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (h : ℝ), 0 < h → (n : ℝ) * h = L →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y → IsPer L Y →
        (∀ z, (Y z).1 ∈ Ke) → (∀ j ≤ s + 2, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ CR) →
        (∀ x : Grid n, (cell h (kOf x) ∩ Q₁).Nonempty → pos h x ∈ Q') →
        ∀ sh : ℝ, 0 ≤ sh →
        h ^ 4 * ∑ x ∈ Finset.univ.filter (fun x : Grid n => pos h x ∈ Q'),
          ‖eulerRow (localAction D h) h (samp h Y) x‖ ^ 2 ≤ sh ^ 2 →
        residualEps D Q₁ Y ≤ C * (sh + h) ∧
          Real.sqrt (hkSq k Q₀ (NativeTail.RB D Y)) +
              Real.sqrt (hkSq (k + 1) Q₀ (NativeTail.RD D Y)) ≤
            C * (residualEps D Q₁ Y ^ (1 - (k : ℝ) / s) +
              residualEps D Q₁ Y ^ (1 - ((k : ℝ) + 1) / s)) := by
  have hs : 0 < s := by omega
  obtain ⟨C₀, hC₀, hZ⟩ := shadow_zero_residual D hKe hdet CR hL hQ₁ (Q' := Q')
  obtain ⟨M, hM0, hRb⟩ := exists_Rfull_bounds D hKe hdet CR s
  set E := 2 * (L ^ 2 * M) with hE
  set cB := ∑ j ∈ Finset.range (k + 1),
      PeriodicSobInterp.interpConst (ContEulerBounds.NCLM (Mat × (Fin 4 → 𝔄) × 𝓗) ℝ) (Fin 4) j s ^
        (1 / (s : ℝ)) * (L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * M)) ^ (2 * (j : ℝ) / s) with hcB
  set cD := ∑ j ∈ Finset.range (k + 1 + 1),
      PeriodicSobInterp.interpConst (ContEulerBounds.NCLM (𝓢 × CoSpinor 𝓢) ℝ) (Fin 4) j s ^
        (1 / (s : ℝ)) * (L ^ 2 * (2 : ℝ) ^ s * (2 ^ s * Bχ * M)) ^ (2 * (j : ℝ) / s) with hcD
  set C := max (2 * C₀) (max (max 1 E * Real.sqrt cB) (max 1 E * Real.sqrt cD)) with hC
  have hC0 : 0 ≤ C := le_max_of_le_left (by positivity)
  refine ⟨C, hC0, ?_⟩
  intro n _ h hh hnh Y hY hper hYe hres hbuf sh hsh hσ
  obtain ⟨hRs, hRd⟩ := hRb Y hY hYe hres
  have hRp := isPer_Rfull D hper
  have hR0 : ∀ y, ‖NativeTail.Rfull D Y y‖ ≤ M := fun y => by
    have := hRd 0 (Nat.zero_le _) y; rwa [norm_iteratedFDeriv_zero] at this
  obtain ⟨hBs, hBp, hBB, hBn⟩ := comp_bounds _ (NativeTail.norm_preL_ιB_le (𝔄 := 𝔄) (𝓗 := 𝓗)
    (𝓢 := 𝓢)) hRs hRp hRd
  obtain ⟨hDs, hDp, hDB, hDn⟩ := comp_bounds _ (ContEulerBounds.norm_preL_le _
    (NativeTail.norm_ιS_le (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢))) hRs hRp hRd
  rw [← RB_eq_comp] at hBs hBp hBB hBn
  rw [← RD_eq_comp] at hDs hDp hDB hDn
  -- the zero residual
  have hZ' := hZ n h hh hnh Y hY hper hYe (fun j hj z => hres j (by omega) z) hbuf sh hsh hσ
  have hintR : IntegrableOn (fun y => ‖NativeTail.Rfull D Y y‖ ^ 2) Q₁ :=
    ((hRs.continuous.norm.pow 2).integrableOn_Icc).mono_set
      (hQ₁.trans (boxIco_subset_Icc L))
  have hsqB : ∫ y in Q₁, ‖NativeTail.RB D Y y‖ ^ 2 ≤ ∫ y in Q₁, ‖NativeTail.Rfull D Y y‖ ^ 2 :=
    setIntegral_mono_on (((hBs.continuous.norm.pow 2).integrableOn_Icc).mono_set
      (hQ₁.trans (boxIco_subset_Icc L))) hintR hQ₁m fun y _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hBn y) 2
  have hsqD : ∫ y in Q₁, ‖NativeTail.RD D Y y‖ ^ 2 ≤ ∫ y in Q₁, ‖NativeTail.Rfull D Y y‖ ^ 2 :=
    setIntegral_mono_on (((hDs.continuous.norm.pow 2).integrableOn_Icc).mono_set
      (hQ₁.trans (boxIco_subset_Icc L))) hintR hQ₁m fun y _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hDn y) 2
  have hε0 : 0 ≤ C₀ * (sh + h) := by positivity
  have hεB : l2Q Q₁ (NativeTail.RB D Y) ≤ C₀ * (sh + h) := l2Q_le_of_sq hε0 (hsqB.trans hZ')
  have hεD : l2Q Q₁ (NativeTail.RD D Y) ≤ C₀ * (sh + h) := l2Q_le_of_sq hε0 (hsqD.trans hZ')
  set ε := residualEps D Q₁ Y with hεdef
  have hεnn : 0 ≤ ε := add_nonneg (l2Q_nonneg _ _) (l2Q_nonneg _ _)
  have hpart1 : ε ≤ C * (sh + h) := by
    have : ε ≤ 2 * C₀ * (sh + h) := by simp only [hεdef, residualEps]; linarith
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  refine ⟨hpart1, ?_⟩
  -- the `L^∞` bound of `ε`
  have hLM : 0 ≤ L ^ 2 * M := by positivity
  have hεB' : l2Q Q₁ (NativeTail.RB D Y) ≤ L ^ 2 * M := by
    refine l2Q_le_of_sq hLM ((hsqB.trans (integral_sq_le_box hL.le hQ₁ hRs.continuous hR0)).trans
      (le_of_eq (by ring)))
  have hεD' : l2Q Q₁ (NativeTail.RD D Y) ≤ L ^ 2 * M := by
    refine l2Q_le_of_sq hLM ((hsqD.trans (integral_sq_le_box hL.le hQ₁ hRs.continuous hR0)).trans
      (le_of_eq (by ring)))
  have hεE : ε ≤ E := by simp only [hεdef, residualEps, hE]; linarith
  -- each component has `L²(Q₁)` norm at most `ε`
  have hB2 : ∫ y in Q₁, ‖NativeTail.RB D Y y‖ ^ 2 ≤ ε ^ 2 := by
    rw [sq_l2Q]
    have : l2Q Q₁ (NativeTail.RB D Y) ≤ ε := by
      simp only [hεdef, residualEps]; linarith [l2Q_nonneg Q₁ (NativeTail.RD D Y)]
    exact pow_le_pow_left₀ (l2Q_nonneg _ _) this 2
  have hD2 : ∫ y in Q₁, ‖NativeTail.RD D Y y‖ ^ 2 ≤ ε ^ 2 := by
    rw [sq_l2Q]
    have : l2Q Q₁ (NativeTail.RD D Y) ≤ ε := by
      simp only [hεdef, residualEps]; linarith [l2Q_nonneg Q₁ (NativeTail.RB D Y)]
    exact pow_le_pow_left₀ (l2Q_nonneg _ _) this 2
  have hIB := hkSq_sqrt_le hL hQ₀m hQ₁m hQ₀ hQ₁ hs hχs hχp hχ1 hχ0 hχQ hχB hBs hBp hBB hεnn hεE
    hB2 (k := k) (by omega)
  have hID := hkSq_sqrt_le hL hQ₀m hQ₁m hQ₀ hQ₁ hs hχs hχp hχ1 hχ0 hχQ hχB hDs hDp hDB hεnn hεE
    hD2 (k := k + 1) (by omega)
  rw [← hcB] at hIB
  rw [← hcD] at hID
  push_cast at hID
  have h1 : max 1 E * Real.sqrt cB ≤ C := le_max_of_le_right (le_max_left _ _)
  have h2 : max 1 E * Real.sqrt cD ≤ C := le_max_of_le_right (le_max_right _ _)
  have a1 : 0 ≤ ε ^ (1 - (k : ℝ) / s) := Real.rpow_nonneg hεnn _
  have a2 : 0 ≤ ε ^ (1 - ((k : ℝ) + 1) / s) := Real.rpow_nonneg hεnn _
  calc Real.sqrt (hkSq k Q₀ (NativeTail.RB D Y)) + Real.sqrt (hkSq (k + 1) Q₀ (NativeTail.RD D Y))
      ≤ max 1 E * Real.sqrt cB * ε ^ (1 - (k : ℝ) / s) +
          max 1 E * Real.sqrt cD * ε ^ (1 - ((k : ℝ) + 1) / s) := add_le_add hIB hID
    _ ≤ C * ε ^ (1 - (k : ℝ) / s) + C * ε ^ (1 - ((k : ℝ) + 1) / s) := by gcongr
    _ = C * (ε ^ (1 - (k : ℝ) / s) + ε ^ (1 - ((k : ℝ) + 1) / s)) := by ring

end Main

/-! ### The record of the paper and non-vacuity -/

section Record

open NativeScaling (Mat)
open NativeDensity
open PeriodicSobInterp (IsPer)

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Coordinatewise periodicity implies `ℤ⁴`-periodicity. -/
theorem isPer_of_isPeriodic {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {L : ℝ} {Y : R4 → V} (hY : IsPeriodic L Y) :
    IsPer L Y := by
  intro k x
  have hsum : L • PeriodicCube.zvec k = ∑ μ, (Pi.single μ ((k μ : ℝ) * L) : R4) := by
    funext i
    simp [PeriodicCube.zvec, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hsum]
  have key : ∀ S : Finset (Fin 4), Y (x + ∑ μ ∈ S, (Pi.single μ ((k μ : ℝ) * L) : R4)) = Y x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, add_comm (Pi.single a _) _, ← add_assoc]
      rw [DiscreteEulerConsistency.IsPeriodic.int_mul hY a (k a) _, ih]
  exact key Finset.univ

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

theorem isPer_recon {n : ℕ} [NeZero n] (u : Grid n → Field 𝔄 𝓗 𝓢) :
    IsPer (2 * Real.pi) (TrigInterp.recon n u) :=
  isPer_of_isPeriodic fun z μ => TrigInterp.tp_periodic _ _ z μ

theorem samp_recon {n : ℕ} [NeZero n] (hn : Odd n) (u : Grid n → Field 𝔄 𝓗 𝓢) :
    samp (2 * Real.pi / n) (TrigInterp.recon n u) = u := by
  funext x
  have e : pos (2 * Real.pi / n) x = TrigInterp.gpos n x := by
    funext μ; simp [pos, TrigInterp.gpos]
  simp only [samp, e]
  exact TrigInterp.recon_gpos n hn u x

open scoped Classical in
/-- **`prop:shadow-residual-upgrade` for the complete record** in the paper's normalization: the
periodic box of period `2π`, `n` odd, `h = 2π/n`, the record `u_h` and its trigonometric
reconstruction `z_h = 𝓘_h^trig u_h` (`TrigInterp.recon`); the finite Euler row is that of the
record itself, `E_h^{raw}(u_h)`. -/
theorem shadow_residual_upgrade_record {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (CR : ℝ) {k s : ℕ} (hks : k + 1 < s) {Q₀ Q₁ Q' : Set R4}
    (hQ₀m : MeasurableSet Q₀) (hQ₁m : MeasurableSet Q₁) (hQ₀ : Q₀ ⊆ boxIco (2 * Real.pi))
    (hQ₁ : Q₁ ⊆ boxIco (2 * Real.pi)) {χ : R4 → ℝ} (hχs : ContDiff ℝ ∞ χ)
    (hχp : IsPer (2 * Real.pi) χ) (hχ1 : ∀ y, |χ y| ≤ 1)
    (hχ0 : ∀ y ∈ boxIco (2 * Real.pi), y ∉ Q₁ → χ y = 0)
    (hχQ : ∀ y ∈ Q₀, ∀ᶠ z in 𝓝 y, χ z = 1) {Bχ : ℝ}
    (hχB : ∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ Bχ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n], Odd n → ∀ u : Grid n → Field 𝔄 𝓗 𝓢,
      (∀ z, (TrigInterp.recon n u z).1 ∈ Ke) →
      (∀ j ≤ s + 2, ∀ z, ‖iteratedFDeriv ℝ j (TrigInterp.recon n u) z‖ ≤ CR) →
      (∀ x : Grid n, (cell (2 * Real.pi / n) (kOf x) ∩ Q₁).Nonempty →
        pos (2 * Real.pi / n) x ∈ Q') →
      ∀ sh : ℝ, 0 ≤ sh →
      (2 * Real.pi / n) ^ 4 * ∑ x ∈ Finset.univ.filter
          (fun x : Grid n => pos (2 * Real.pi / n) x ∈ Q'),
        ‖eulerRow (localAction D (2 * Real.pi / n)) (2 * Real.pi / n) u x‖ ^ 2 ≤ sh ^ 2 →
      residualEps D Q₁ (TrigInterp.recon n u) ≤ C * (sh + 2 * Real.pi / n) ∧
        Real.sqrt (hkSq k Q₀ (NativeTail.RB D (TrigInterp.recon n u))) +
            Real.sqrt (hkSq (k + 1) Q₀ (NativeTail.RD D (TrigInterp.recon n u))) ≤
          C * (residualEps D Q₁ (TrigInterp.recon n u) ^ (1 - (k : ℝ) / s) +
            residualEps D Q₁ (TrigInterp.recon n u) ^ (1 - ((k : ℝ) + 1) / s)) := by
  obtain ⟨C, hC, hmain⟩ := shadow_residual_upgrade D hKe hdet CR hks Real.two_pi_pos hQ₀m hQ₁m hQ₀
    hQ₁ hχs hχp hχ1 hχ0 hχQ hχB
  refine ⟨C, hC, fun n _ hn u hYe hres hbuf sh hsh hσ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : 0 < 2 * Real.pi / n := div_pos Real.two_pi_pos hn0
  have hnh : (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi := by field_simp
  refine hmain n (2 * Real.pi / n) hh hnh _ (NativeTail.contDiff_recon u) (isPer_recon u) hYe hres
    hbuf sh hsh ?_
  rwa [samp_recon hn u]

omit [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢] in
/-- **Non-vacuity** of the hypothesis packet of `shadow_residual_upgrade`: the flat constant field
(identity coframe, zero gauge, Higgs and spinor fields) on the chart `{1}`, any period `L > 0`, the
trivial cutoff `χ ≡ 1` with `Q₀ = Q₁ = Q' = [0, L)⁴`, every grid and every order. -/
example (L : ℝ) (n : ℕ) [NeZero n] (h : ℝ) (hh : 0 < h) (hnh : (n : ℝ) * h = L) (s : ℕ) :
    let Y : R4 → Field 𝔄 𝓗 𝓢 := fun _ => ((1 : Mat), 0)
    let χ : R4 → ℝ := fun _ => 1
    ContDiff ℝ ∞ Y ∧ IsPer L Y ∧ (∀ z, (Y z).1 ∈ ({1} : Set Mat)) ∧
      (∀ j ≤ s + 2, ∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ ‖Y 0‖) ∧
      IsCompact ({1} : Set Mat) ∧ (∀ e ∈ ({1} : Set Mat), 0 < e.det) ∧
      ContDiff ℝ ∞ χ ∧ IsPer L χ ∧ (∀ y, |χ y| ≤ 1) ∧
      (∀ y ∈ boxIco L, y ∉ boxIco L → χ y = 0) ∧ (∀ y ∈ boxIco L, ∀ᶠ z in 𝓝 y, χ z = 1) ∧
      (∀ j ≤ s, ∀ y, ‖iteratedFDeriv ℝ j χ y‖ ≤ 1) ∧ MeasurableSet (boxIco L) ∧
      (∀ x : Grid n, (cell h (kOf x) ∩ boxIco L).Nonempty → pos h x ∈ boxIco L) := by
  intro Y χ
  refine ⟨contDiff_const, fun k x => rfl, fun z => rfl, fun j _ z => ?_, isCompact_singleton,
    fun e he => ?_, contDiff_const, fun k x => rfl, fun y => by simp [χ], fun y hy hy' => absurd hy hy',
    fun y _ => Eventually.of_forall fun z => rfl, fun j _ y => ?_, measurableSet_boxIco L,
    fun x _ => ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Y]
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  · rw [Set.mem_singleton_iff] at he; subst he; simp
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [χ]
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  · intro μ _
    have hv : ((x μ).val : ℝ) < n := by exact_mod_cast ZMod.val_lt (x μ)
    refine ⟨by simp only [pos]; positivity, ?_⟩
    simp only [pos]
    rw [← hnh]
    nlinarith

end Record

end

end RenewalGeometry.ShadowResidual
