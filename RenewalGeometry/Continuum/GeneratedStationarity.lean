/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedRecordNodes

/-!
# Stationarity of the composite action at the generated record

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`,
`eq:generated-stationarity`: with `S^{(1)}` the first-derivative Einstein–Yang–Mills–Higgs action
in the actual-jet variables (`GenFOAction.L1SM`), `R` the cubic-Hermite reconstruction from nodal
values and slopes (`GenRecNodes.recF`) and `S^{cmp} = S^{(1)} ∘ R` on the cells
`[jτ, (j+1)τ] ⊆ [0, Jτ]` (`Scmp`), for nodal variations `V = (v_j, v̇_j)` with fixed collar
(`v_0 = v̇_0 = v_J = v̇_J = 0`)

`|D S^{cmp}[V]| ≤ M B √(8Jτ) ‖V‖_{0,τ}`,  `‖V‖²_{0,τ} = τ Σ_{j ≤ J} (‖v_j‖² + τ²‖v̇_j‖²)`,

whenever every cell is in the Lorentzian chart with head metric in a compact set `K_g`
(`M` from `GenCellBulk.exists_hom_bound`) and the bosonic readouts satisfy
`Σ_k Q_s(e_B R_B)_k ≤ B²` on every slice (**`stationarity_of_cells`**).  Here `D S^{cmp}[V]` is a
genuine derivative (`HasDerivAt` of `ε ↦ S^{cmp}(U + εV)` at `0`).  The proof: cell variation
(`GenRecCell.record_cell`), telescoping of the time fluxes across the nodes (`recF_node`), the fixed
collar (`recF_node_zero`), the `L²` size of the reconstruction (`recF_L2`) and the discrete
Cauchy–Schwarz inequality.

* `exists_bulk_bound` — the constant `M` for a compact set of nondegenerate metrics.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenStat

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin GenRecCell SpectralGalerkin CubicHermite GenRecNodes
open MeasureTheory

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {n : ℕ} (κ : StateP m V S S' ≃ₗ[ℝ] (Fin n → ℝ))

/-! ### The composite action and the norm of nodal variations -/

/-- **The composite action** `S^{cmp}(U, P) = Σ_{j < J} ∫_{[jτ,(j+1)τ]×𝕋³} L^{(1)}(j¹ R(U, P))`:
the first-derivative Einstein–Yang–Mills–Higgs action of the cubic-Hermite reconstruction from the
nodal values `U` and nodal slopes `P`. -/
def Scmp (SM : SMData (MatLie m) V S S') {N : ℕ} (q : ℕ) (τ : ℝ) (J : ℕ)
    (U P : ℕ → GS 3 n N) : ℝ :=
  ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
    (fun x => L1SM SM (hjet1 (V := V) κ (recF q τ U P j) x))

/-- **The norm of a nodal variation** `‖V‖_{0,τ} = (τ Σ_{j ≤ J}(‖v_j‖² + τ²‖v̇_j‖²))^{1/2}`. -/
def vnorm {N : ℕ} (q : ℕ) (τ : ℝ) (J : ℕ) (v w : ℕ → GS 3 n N) : ℝ :=
  Real.sqrt (τ * ∑ j ∈ Finset.range (J + 1), (nrm2 q (v j) + τ ^ 2 * nrm2 q (w j)))

/-! ### Regularity of the head 1-jets -/

theorem continuous_hjet1 {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c)) :
    Continuous (hjet1 (V := V) κ W) := by
  have hWv : ContDiff ℝ ∞ (fun y => fun c => W c y) := contDiff_pi.2 hW
  exact continuous_j1F ((Lg κ).contDiff.comp hWv) ((LA κ).contDiff.comp hWv)
    ((LH κ).contDiff.comp hWv)

theorem isSPeriodic_hjet1 {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hWp : ∀ c, IsSPeriodic (W c)) : IsSPeriodic (hjet1 (V := V) κ W) := fun k x => by
  have h0 : ∀ c, W c (x + sshift k) = W c x := fun c => hWp c k x
  have h1 : ∀ c α, pd (W c) α (x + sshift k) = pd (W c) α x := fun c α =>
    isSPeriodic_pd' (hWp c) α k x
  unfold hjet1 j1F
  simp only [pd_famL_fun _ hW, h0, h1]

theorem det_neg_of_chart {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hWp : ∀ c, IsSPeriodic (W c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x)) {x : ST 3}
    (hx : x 0 ∈ Icc a b) : (Matrix.of (Lg κ (fun c => W c x))).det < 0 := by
  obtain ⟨z', hz'⟩ := exists_cell_ext (m := m) (V := V) (S := S) (S' := S') κ hW hWp hab hc
  rw [← (hz' x hx).1.eq_of_nhds]
  exact GenCell.Tuple_det_neg z' x

/-- **The first variation of a record cell is a genuine derivative.** -/
theorem cell_hasDerivAt (SM : SMData (MatLie m) V S S') {W Y : Fin n → ST 3 → ℝ}
    (hW : ∀ c, ContDiff ℝ ∞ (W c)) (hWp : ∀ c, IsSPeriodic (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (hYp : ∀ c, IsSPeriodic (Y c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x)) :
    HasDerivAt (fun ε : ℝ => cellInt a b (fun x => L1SM SM (hjet1 κ W x + ε • hjet1 κ Y x)))
      (cellInt a b (fun x => fderiv ℝ (L1SM SM) (hjet1 κ W x) (hjet1 κ Y x))) 0 := by
  have hK : ∀ x : ST 3, x 0 ∈ Icc a b → hjet1 (V := V) κ W x ∈ chart1 m V := fun x hx =>
    det_neg_of_chart (m := m) (V := V) (S := S) (S' := S') κ hW hWp hab hc hx
  obtain ⟨r, hr, hmar⟩ := exists_line_margin (continuous_hjet1 κ hW) (continuous_hjet1 κ hY)
    (isSPeriodic_hjet1 κ hW hWp) (isSPeriodic_hjet1 κ hY hYp) isOpen_chart1 hab hK
  refine cell_deriv_of_jet isOpen_chart1 (contDiffOn_L1SM SM) (continuous_hjet1 κ hW)
    (continuous_hjet1 κ hY) hr hab fun ε hε t ht y _ => hmar ε hε _ ?_
  simp only [Fin.cons_zero]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### The constant of the bulk rows -/

/-- **The bulk constant**: on a compact set of nondegenerate metrics the bulk rows are bounded by
`M ‖e_B R_B‖ ‖Y‖`. -/
theorem exists_bulk_bound (SM : SMData (MatLie m) V S S') {nB : ℕ}
    (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V) {Kg : Set Met} (hKg : IsCompact Kg)
    (hdet : ∀ g ∈ Kg, (Matrix.of g).det ≠ 0) :
    ∃ M ≥ 0, ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖ := by
  refine exists_hom_bound (fun g c y => bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)) hKg ?_
    (fun g _ t c y => by rw [map_smul, bulkJ_smul_left])
    (fun g _ t c y => by rw [map_smul, map_smul, map_smul, bulkJ_smul_right])
  intro p hp
  have hm : Continuous fun p : Met × (Fin nB → ℝ) × (Fin n → ℝ) =>
      (p.1, eBs p.2.1, (Lg κ p.2.2, LA κ p.2.2, LH κ p.2.2)) := by fun_prop
  have := ContinuousAt.comp (x := p)
    (g := fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      bulkJ SM q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    (f := fun p : Met × (Fin nB → ℝ) × (Fin n → ℝ) =>
      (p.1, eBs p.2.1, (Lg κ p.2.2, LA κ p.2.2, LH κ p.2.2)))
    (continuousAt_bulkJ SM (hdet p.1 hp.1)) hm.continuousAt
  exact this.continuousWithinAt

/-! ### Stationarity -/

theorem sum_adj_le {J : ℕ} (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∑ j ∈ Finset.range J, (c j + c (j + 1)) ≤ 2 * ∑ j ∈ Finset.range (J + 1), c j := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range J, c j ≤ ∑ j ∈ Finset.range (J + 1), c j := by
    rw [Finset.sum_range_succ]; linarith [hc J]
  have h2 : ∑ j ∈ Finset.range J, c (j + 1) ≤ ∑ j ∈ Finset.range (J + 1), c j := by
    rw [Finset.sum_range_succ']; linarith [hc 0]
  linarith

set_option maxHeartbeats 2000000 in
/-- **`eq:generated-stationarity` on a chart record** (variational smooth theory data,
`κ ≠ 0`): if every cell of the Hermite reconstruction `R(U, P)` on `[0, Jτ]` is in the Lorentzian
chart with head metric in `K_g` (bulk constant `M`, `exists_bulk_bound`) and the bosonic readouts
satisfy `Σ_k Q_s(e_B R_B)_k ≤ B²` on every slice, then for every nodal variation `V = (v, w)` with
fixed collar the derivative `D S^{cmp}[V]` exists and `|D S^{cmp}[V]| ≤ M B √(8Jτ) ‖V‖_{0,τ}`. -/
theorem stationarity_of_cells (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hV : GenStress.VariationalStress SM) (hκ : SM.κ ≠ 0) {N q : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {J : ℕ} {U P : ℕ → GS 3 n N}
    (hc : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      HeadChart κ (fun c => recF q τ U P j c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {Kg : Set Met} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hKg : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      Lg κ (fun c => recF q τ U P j c x) ∈ Kg)
    {s : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recF q τ U P j) x)) k) t ≤ B ^ 2)
    (v w : ℕ → GS 3 n N) (hv0 : v 0 = 0) (hw0 : w 0 = 0) (hvJ : v J = 0) (hwJ : w J = 0) :
    ∃ D : ℝ, HasDerivAt (fun ε : ℝ =>
        Scmp κ SM q τ J (fun j => U j + ε • v j) (fun j => P j + ε • w j)) D 0 ∧
      |D| ≤ M * B * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
  set W : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ U P j with hWdef
  set Y : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ v w j with hYdef
  have hWs : ∀ j c, ContDiff ℝ ∞ (W j c) := fun j c => contDiff_recF q τ U P j c
  have hWp : ∀ j c, IsSPeriodic (W j c) := fun j c => isSPeriodic_recF q τ U P j c
  have hYs : ∀ j c, ContDiff ℝ ∞ (Y j c) := fun j c => contDiff_recF q τ v w j c
  have hYp : ∀ j c, IsSPeriodic (Y j c) := fun j c => isSPeriodic_recF q τ v w j c
  have hab : ∀ j : ℕ, (j : ℝ) * τ ≤ ((j : ℝ) + 1) * τ := fun j => by nlinarith
  -- linearity of the composite action
  have hlin : ∀ (ε : ℝ) (j : ℕ) (x : ST 3),
      hjet1 (V := V) κ (recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j) x =
        hjet1 κ (W j) x + ε • hjet1 κ (Y j) x := fun ε j x => by
    have e : recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j =
        fun c y => W j c y + ε * Y j c y :=
      funext fun c => funext fun y => recF_add_smul q τ U P v w ε j c y
    rw [e]
    exact hjet1_add_smul κ (hWs j) (hYs j) ε x
  have hSe : (fun ε : ℝ => Scmp κ SM q τ J (fun j => U j + ε • v j) (fun j => P j + ε • w j)) =
      fun ε => ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => L1SM SM (hjet1 κ (W j) x + ε • hjet1 κ (Y j) x)) := by
    funext ε
    unfold Scmp
    simp only [hlin]
  have hder : HasDerivAt (fun ε : ℝ => Scmp κ SM q τ J (fun j => U j + ε • v j)
      (fun j => P j + ε • w j))
      (∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => fderiv ℝ (L1SM SM) (hjet1 κ (W j) x) (hjet1 κ (Y j) x))) 0 := by
    rw [hSe]
    exact HasDerivAt.fun_sum fun j hj => cell_hasDerivAt κ SM (hWs j) (hWp j) (hYs j) (hYp j)
      (hab j) (hc j (Finset.mem_range.1 hj))
  refine ⟨_, hder, ?_⟩
  -- the cells
  have hcell : ∀ j ∈ Finset.range J, ∃ Dj : ℝ,
      cellInt (j * τ) ((j + 1) * τ)
          (fun x => fderiv ℝ (L1SM SM) (hjet1 κ (W j) x) (hjet1 κ (Y j) x)) =
        Dj + (fluxR (V := V) κ SM (W j) (Y j) (((j : ℝ) + 1) * τ) -
          fluxR (V := V) κ SM (W j) (Y j) ((j : ℝ) * τ)) ∧
      |Dj| ≤ M * (Real.sqrt ((((j : ℝ) + 1) * τ - j * τ) * B ^ 2) *
        Real.sqrt (cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2))) := fun j hj =>
    record_cell κ SM hS hV hκ (hWs j) (hWp j) (hYs j) (hYp j) (hab j)
      (hc j (Finset.mem_range.1 hj)) eB eBs heB hM0 hM (hKg j (Finset.mem_range.1 hj))
      (hB j (Finset.mem_range.1 hj))
  choose! Dj hDj using hcell
  -- the fluxes telescope
  set G : ℕ → ℝ := fun j => fluxR (V := V) κ SM (W j) (Y j) ((j : ℝ) * τ) with hG
  have hnode : ∀ j, fluxR (V := V) κ SM (W j) (Y j) (((j : ℝ) + 1) * τ) = G (j + 1) := fun j => by
    simp only [hG]
    push_cast
    exact fluxR_congr κ SM (fun y => recF_node κ q τ hτ.ne' U P j y)
      (fun y => recF_node κ q τ hτ.ne' v w j y)
  have hG0 : G 0 = 0 := fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w 0 hv0 hw0 y
  have hGJ : G J = 0 := fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w J hvJ hwJ y
  have hsum : ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
      (fun x => fderiv ℝ (L1SM SM) (hjet1 κ (W j) x) (hjet1 κ (Y j) x)) =
      ∑ j ∈ Finset.range J, Dj j := by
    rw [Finset.sum_congr rfl fun j hj => (hDj j hj).1]
    simp only [hnode, Finset.sum_add_distrib]
    have := Finset.sum_range_sub G J
    rw [hG0, hGJ] at this
    simp only [hG] at this ⊢
    linarith
  rw [hsum]
  -- the bound
  set c : ℕ → ℝ := fun j => nrm2 q (v j) + τ ^ 2 * nrm2 q (w j) with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    add_nonneg (nrm2_nonneg q _) (mul_nonneg (sq_nonneg τ) (nrm2_nonneg q _))
  set X : ℕ → ℝ := fun j => 4 * (c j + c (j + 1)) with hX
  have hX0 : ∀ j, 0 ≤ X j := fun j => by have := hc0 j; have := hc0 (j + 1); positivity
  have hDb : ∀ j ∈ Finset.range J, |Dj j| ≤ M * B * (Real.sqrt τ * Real.sqrt (τ * X j)) := by
    intro j hj
    refine (hDj j hj).2.trans ?_
    have e1 : (((j : ℝ) + 1) * τ - j * τ) * B ^ 2 = τ * B ^ 2 := by ring
    have e2 : Real.sqrt (τ * B ^ 2) = Real.sqrt τ * B := by
      rw [Real.sqrt_mul hτ.le, Real.sqrt_sq hB0]
    have hL2 := recF_L2 q hτ v w j
    have hL2' : cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2) ≤ τ * X j := by
      refine hL2.trans (le_of_eq ?_)
      simp only [hX, hcdef]; ring
    rw [e1, e2]
    have := Real.sqrt_le_sqrt hL2'
    have hB' : 0 ≤ Real.sqrt τ * B := mul_nonneg (Real.sqrt_nonneg _) hB0
    calc M * (Real.sqrt τ * B * Real.sqrt (cellInt (j * τ) ((j + 1) * τ)
          (fun x => ∑ c, Y j c x ^ 2))) ≤ M * (Real.sqrt τ * B * Real.sqrt (τ * X j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hB') hM0
      _ = M * B * (Real.sqrt τ * Real.sqrt (τ * X j)) := by ring
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.range J) (f := fun _ => τ) (g := fun j => τ * X j)
    (fun _ => hτ.le) (fun j => mul_nonneg hτ.le (hX0 j))
  have hsumτ : ∑ _j ∈ Finset.range J, τ = J * τ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumX : ∑ j ∈ Finset.range J, τ * X j ≤ 8 * (τ * ∑ j ∈ Finset.range (J + 1), c j) := by
    rw [← Finset.mul_sum]
    have := sum_adj_le (J := J) c hc0
    have e : ∑ j ∈ Finset.range J, X j = 4 * ∑ j ∈ Finset.range J, (c j + c (j + 1)) := by
      simp only [hX, Finset.mul_sum]
    rw [e]
    nlinarith
  have hvn : vnorm q τ J v w = Real.sqrt (τ * ∑ j ∈ Finset.range (J + 1), c j) := rfl
  have hMB : 0 ≤ M * B := mul_nonneg hM0 hB0
  calc |∑ j ∈ Finset.range J, Dj j| ≤ ∑ j ∈ Finset.range J, |Dj j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range J, M * B * (Real.sqrt τ * Real.sqrt (τ * X j)) :=
        Finset.sum_le_sum hDb
    _ = M * B * ∑ j ∈ Finset.range J, Real.sqrt τ * Real.sqrt (τ * X j) := by
        rw [Finset.mul_sum]
    _ ≤ M * B * (Real.sqrt (J * τ) * Real.sqrt (8 * (τ * ∑ j ∈ Finset.range (J + 1), c j))) := by
        refine mul_le_mul_of_nonneg_left (hCS.trans ?_) hMB
        rw [hsumτ]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumX) (Real.sqrt_nonneg _)
    _ = M * B * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
        rw [hvn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
        ring

end RenewalGeometry.GenStat
