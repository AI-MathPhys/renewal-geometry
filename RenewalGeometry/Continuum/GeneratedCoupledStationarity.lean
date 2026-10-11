/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledCellDirac
import RenewalGeometry.Continuum.GeneratedStationarity

/-!
# Stationarity of the complete composite action with back-reacting spinors

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`,
`eq:generated-stationarity`, for back-reacting Dirac data (`GenDStress.CoupledDirac`): the
complete first-order density `S^{(1)} = L1SM + L1D` (`L1C`: first-derivative
Einstein–Yang–Mills–Higgs density plus the first-order Dirac density with spin connection, gauge
coupling and Yukawa term) on the extended head 1-jets of the cubic-Hermite reconstruction
(`hjet1C`, including the spinor and co-spinor heads), and the composite action
`S^{cmp} = S^{(1)} ∘ R` (`ScmpC`).

* `fderiv_L1C` — the first variation of `L1C` splits into the bosonic and Dirac parts;
* **`record_cell_cpl`** — on a record cell in the chart the first variation of `S^{(1)}` is a bulk
  term plus end fluxes (`fluxRC`: bosonic time flux minus the Dirac time flux `fluxDR`), the bulk
  being `bulkJ` of the complete bosonic residual plus `dirJ` of the Dirac residual
  (`GenCplCV.bulk_identity`) and hence bounded through the bosonic **and** Dirac readouts;
* **`stationarity_of_cells_cpl`** — `|D S^{cmp}[V]| ≤ M (B + B_D) √(8Jτ) ‖V‖_{0,τ}` for nodal
  variations with fixed collar, `B`, `B_D` bounds of the bosonic and Dirac readouts on the slices.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplSt

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin GenRecCell SpectralGalerkin CubicHermite GenRecNodes
  GenStat GenDAct GenDEul GenDFld GenDStress GenDiracCur GenCplCV GenCplCD
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

/-! ### The complete first-order density and the composite action -/

/-- **The complete first-order density** `S^{(1)} = L^{(1)}_{EYMH} + √(-det g) L_D` on the extended
head 1-jets. -/
def L1C (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) (j : HJ1C m V S S') : ℝ :=
  L1SM SM j.1 + L1D SM P j

/-- The extended head 1-jet `((g, ∂g; A, ∂A; H, ∂H), (Ψ, ∂Ψ), (Ψ̄, ∂Ψ̄))` of the head fields of a
coordinate family. -/
def hjet1C (W : Fin n → ST 3 → ℝ) (x : ST 3) : HJ1C m V S S' :=
  (hjet1 κ W x, ((Lψ κ (fun c => W c x), fun γ => Lψ κ (fun c => pd (W c) γ x)),
    (Lψb κ (fun c => W c x), fun γ => Lψb κ (fun c => pd (W c) γ x))))

/-- **The complete composite action** `S^{cmp}(U, P) = Σ_{j < J} ∫_{[jτ,(j+1)τ]×𝕋³}
S^{(1)}(j¹R(U, P))`: the complete first-order Einstein–Standard-Model action (bosonic plus Dirac)
of the cubic-Hermite reconstruction from nodal values `U` and slopes `P'`. -/
def ScmpC (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ) {N : ℕ} (q : ℕ) (τ : ℝ)
    (J : ℕ) (U P' : ℕ → GS 3 n N) : ℝ :=
  ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
    (fun x => L1C SM P (hjet1C κ (recF q τ U P' j) x))

/-- The Dirac time flux through the slice `t`, from the head values of the record `W` and of the
variation `Y` on that slice. -/
def fluxDR {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM) (W Y : Fin n → ST 3 → ℝ)
    (t : ℝ) : ℝ :=
  sint (fun x => fluxDJ hP 0 (Lg κ (fun c => W c x)) (Lψ κ (fun c => W c x))
    (Lψb κ (fun c => W c x)) (Lg κ (fun c => Y c x)) (Lψ κ (fun c => Y c x))
    (Lψb κ (fun c => Y c x))) t

/-- **The time flux of the first variation of the complete density** through the slice `t`. -/
def fluxRC {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM) (W Y : Fin n → ST 3 → ℝ)
    (t : ℝ) : ℝ :=
  fluxR (V := V) κ SM W Y t - fluxDR κ hP W Y t

theorem fluxDR_congr {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM)
    {W Y W' Y' : Fin n → ST 3 → ℝ} {t : ℝ}
    (hW : ∀ (y : Fin 3 → ℝ) c, W c (Fin.cons t y) = W' c (Fin.cons t y))
    (hY : ∀ (y : Fin 3 → ℝ) c, Y c (Fin.cons t y) = Y' c (Fin.cons t y)) :
    fluxDR κ hP W Y t = fluxDR κ hP W' Y' t := by
  have eW : ∀ y : Fin 3 → ℝ, (fun c => W c (Fin.cons t y)) = fun c => W' c (Fin.cons t y) :=
    fun y => funext (hW y)
  have eY : ∀ y : Fin 3 → ℝ, (fun c => Y c (Fin.cons t y)) = fun c => Y' c (Fin.cons t y) :=
    fun y => funext (hY y)
  unfold fluxDR sint
  simp only [eW, eY]

theorem fluxDR_zero {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM)
    {W Y : Fin n → ST 3 → ℝ} {t : ℝ} (hY : ∀ (y : Fin 3 → ℝ) c, Y c (Fin.cons t y) = 0) :
    fluxDR κ hP W Y t = 0 := by
  have eY : ∀ y : Fin 3 → ℝ, (fun c => Y c (Fin.cons t y)) = 0 := fun y => funext (hY y)
  unfold fluxDR sint
  simp only [eY, map_zero, fluxDJ_zero]
  simp

/-! ### Regularity of the extended head 1-jets -/

theorem continuous_hjet1C {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c)) :
    Continuous (hjet1C κ W) := by
  have hWv : Continuous (fun y => fun c => W c y) := continuous_pi fun c => (hW c).continuous
  have hdv : ∀ γ, Continuous (fun y => fun c => pd (W c) γ y) := fun γ =>
    continuous_pi fun c => (contDiff_pd (hW c) γ).continuous
  exact (continuous_hjet1 κ hW).prodMk ((((Lψ κ).continuous.comp hWv).prodMk
    (continuous_pi fun γ => (Lψ κ).continuous.comp (hdv γ))).prodMk
    (((Lψb κ).continuous.comp hWv).prodMk (continuous_pi fun γ => (Lψb κ).continuous.comp (hdv γ))))

theorem isSPeriodic_hjet1C {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hWp : ∀ c, IsSPeriodic (W c)) : IsSPeriodic (hjet1C κ W) := fun k x => by
  have h0 : ∀ c, W c (x + sshift k) = W c x := fun c => hWp c k x
  have h1 : ∀ c α, pd (W c) α (x + sshift k) = pd (W c) α x := fun c α =>
    isSPeriodic_pd' (hWp c) α k x
  unfold hjet1C
  rw [isSPeriodic_hjet1 κ hW hWp k x]
  simp only [h0, h1]

theorem hjet1C_mem_chart {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hWp : ∀ c, IsSPeriodic (W c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x)) {x : ST 3}
    (hx : x 0 ∈ Icc a b) : hjet1C κ W x ∈ chart1C m V S S' :=
  ⟨det_neg_of_chart κ hW hWp hab hc hx, (hc x hx).2⟩

theorem pd_add_mul {f g : ST 3 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ε : ℝ)
    (γ : Fin 4) (x : ST 3) : pd (fun y => f y + ε * g y) γ x = pd f γ x + ε * pd g γ x := by
  have df := hf.differentiable (by simp) x
  have dg := hg.differentiable (by simp) x
  unfold SobolevOpen.pd
  rw [fderiv_fun_add df (dg.const_mul ε), fderiv_const_mul dg]
  simp

theorem hjet1C_add_smul {W Y : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (ε : ℝ) (x : ST 3) :
    hjet1C κ (fun c y => W c y + ε * Y c y) x = hjet1C κ W x + ε • hjet1C κ Y x := by
  have e0 : (fun c => W c x + ε * Y c x) = (fun c => W c x) + ε • (fun c => Y c x) :=
    funext fun c => by simp
  have e1 : ∀ γ, (fun c => pd (fun y => W c y + ε * Y c y) γ x) =
      (fun c => pd (W c) γ x) + ε • (fun c => pd (Y c) γ x) := fun γ =>
    funext fun c => by simp [pd_add_mul (hW c) (hY c)]
  unfold hjet1C
  rw [hjet1_add_smul κ hW hY ε x]
  simp only [e0, e1, map_add, map_smul]
  rfl

/-! ### Nodal values of the reconstruction -/

section Nodes

variable {N : ℕ} (q : ℕ) (τ : ℝ)

theorem recF_node_val (hτ : τ ≠ 0) (U P : ℕ → GS 3 n N) (j : ℕ) (c : Fin n) (y : Fin 3 → ℝ) :
    recF q τ U P j c (Fin.cons (((j : ℝ) + 1) * τ) y) =
      recF q τ U P (j + 1) c (Fin.cons (((j : ℝ) + 1) * τ) y) := by
  have h1 : (((j : ℝ) + 1) * τ - j * τ) / τ = 1 := by field_simp; ring
  have h0 : (((j : ℝ) + 1) * τ - ((j + 1 : ℕ) : ℝ) * τ) / τ = 0 := by push_cast; simp
  refine (fldc_slice_jet q (contDiff_hc τ _ _ _ _ _) (contDiff_hc τ _ _ _ _ _)
    (hasDerivAt_hc hτ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).1
  · simp only [hc, h1, h0, hermite_one, hermite_zero]
  · simp only [hcD, h1, h0, hermiteD_one, hermiteD_zero]

theorem recF_node_val_zero (hτ : τ ≠ 0) (U P : ℕ → GS 3 n N) (j : ℕ) (hU : U j = 0)
    (hP : P j = 0) (c : Fin n) (y : Fin 3 → ℝ) :
    recF q τ U P j c (Fin.cons ((j : ℝ) * τ) y) = 0 := by
  have h0 : ((j : ℝ) * τ - j * τ) / τ = 0 := by simp
  refine (fldc_slice_zero q (contDiff_hc τ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).1
  · simp only [hc, h0, hermite_zero, hU]
  · simp only [hcD, h0, hermiteD_zero, hP]

end Nodes

/-! ### The first variation of the complete density -/

section Deriv

variable (SM : SMData (MatLie m) V S S') (P : S' →ₗ[ℝ] S →ₗ[ℝ] ℝ)

theorem hasFDerivAt_L1C {j : HJ1C m V S S'} (hj : j ∈ chart1C m V S S') :
    HasFDerivAt (L1C SM P) ((fderiv ℝ (L1SM SM) j.1).comp
      (ContinuousLinearMap.fst ℝ (HJ1 m V) ((S × (Fin 4 → S)) × (S' × (Fin 4 → S')))) +
      fderiv ℝ (L1D SM P) j) j := by
  have h1 := (differentiableAt_L1SM SM hj.1).hasFDerivAt
  have h2 := (((contDiffOn_L1D SM P).contDiffAt (isOpen_chart1C.mem_nhds hj)).differentiableAt
    (by simp)).hasFDerivAt
  exact (h1.comp j hasFDerivAt_fst).add h2

theorem fderiv_L1C {j : HJ1C m V S S'} (hj : j ∈ chart1C m V S S') (v : HJ1C m V S S') :
    fderiv ℝ (L1C SM P) j v = fderiv ℝ (L1SM SM) j.1 v.1 + fderiv ℝ (L1D SM P) j v := by
  rw [(hasFDerivAt_L1C SM P hj).fderiv]
  rfl

theorem contDiffOn_L1C : ContDiffOn ℝ ∞ (L1C SM P) (chart1C m V S S') :=
  ((contDiffOn_L1SM SM).comp contDiff_fst.contDiffOn fun _ hj => hj.1).add (contDiffOn_L1D SM P)

/-- **The first variation of a record cell of the complete action is a genuine derivative.** -/
theorem cell_hasDerivAt_C {W Y : Fin n → ST 3 → ℝ}
    (hW : ∀ c, ContDiff ℝ ∞ (W c)) (hWp : ∀ c, IsSPeriodic (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (hYp : ∀ c, IsSPeriodic (Y c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x)) :
    HasDerivAt (fun ε : ℝ => cellInt a b (fun x => L1C SM P (hjet1C κ W x + ε • hjet1C κ Y x)))
      (cellInt a b (fun x => fderiv ℝ (L1C SM P) (hjet1C κ W x) (hjet1C κ Y x))) 0 := by
  have hK : ∀ x : ST 3, x 0 ∈ Icc a b → hjet1C κ W x ∈ chart1C m V S S' := fun x hx =>
    hjet1C_mem_chart κ hW hWp hab hc hx
  obtain ⟨r, hr, hmar⟩ := exists_line_margin (continuous_hjet1C κ hW) (continuous_hjet1C κ hY)
    (isSPeriodic_hjet1C κ hW hWp) (isSPeriodic_hjet1C κ hY hYp) isOpen_chart1C hab hK
  refine cell_deriv_of_jet isOpen_chart1C (contDiffOn_L1C SM P) (continuous_hjet1C κ hW)
    (continuous_hjet1C κ hY) hr hab fun ε hε t ht y _ => hmar ε hε _ ?_
  simp only [Fin.cons_zero]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end Deriv

/-! ### Cauchy–Schwarz through a readout -/

theorem abs_cellInt_readout {F : ST 3 → ℝ} (hF : Continuous F) {Y : Fin n → ST 3 → ℝ}
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) {a b : ℝ} (hab : a ≤ b) {nR : ℕ} {R Rr : ST 3 → Fin nR → ℝ}
    (hR : Continuous R) {M : ℝ} (hM0 : 0 ≤ M)
    (hpt : ∀ x : ST 3, x 0 ∈ Icc a b → |F x| ≤ M * ‖R x‖ * ‖fun c => Y c x‖)
    (hRr : ∀ x : ST 3, x 0 ∈ Icc a b → R x = Rr x) {s : ℕ} {B : ℝ}
    (hB : ∀ t ∈ Ioo a b, ∑ k, Q s (fun x => Rr x k) t ≤ B ^ 2) :
    |cellInt a b F| ≤ M * (Real.sqrt ((b - a) * B ^ 2) *
      Real.sqrt (cellInt a b (fun x => ∑ c, Y c x ^ 2))) := by
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) 0 ∈ Icc a b := fun t ht y => by
    simpa using ht
  set f : ST 3 → ℝ := fun x => Real.sqrt (∑ k, R x k ^ 2) with hf
  set h : ST 3 → ℝ := fun x => Real.sqrt (∑ c, Y c x ^ 2) with hh
  have hfc : Continuous f := Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).comp hR).pow 2)
  have hhc : Continuous h := Real.continuous_sqrt.comp (continuous_finsetSum _ fun c _ =>
    (hY c).continuous.pow 2)
  have hpt' : ∀ x : ST 3, x 0 ∈ Icc a b → |F x| ≤ M * (f x * h x) := by
    intro x hx
    refine (hpt x hx).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_le_sqrt_sum_sq _) (norm_le_sqrt_sum_sq _)
      (norm_nonneg _) (Real.sqrt_nonneg _)) hM0
  have hmain := abs_cellInt_le hF hfc hhc hM0 hab hpt'
  have hf2 : (fun x => f x ^ 2) = fun x => ∑ k, R x k ^ 2 := by
    funext x; rw [hf]; exact Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hh2 : (fun x => h x ^ 2) = fun x => ∑ c, Y c x ^ 2 := by
    funext x; rw [hh]; exact Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)
  have hfI : cellInt a b (fun x => f x ^ 2) ≤ (b - a) * B ^ 2 := by
    rw [hf2]
    have hc2 : ∀ k, Continuous fun x => R x k ^ 2 := fun k => ((continuous_apply k).comp hR).pow 2
    refine cellInt_le_of_slices (continuous_finsetSum _ fun k _ => hc2 k) hab fun t ht => ?_
    rw [sint_sum _ hc2]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hB t ht)
    have e : sint (fun x => R x k ^ 2) t = ∫ y in Icc (0 : Fin 3 → ℝ) 1, (Rr (Fin.cons t y) k) ^ 2 := by
      unfold sint
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rw [hRr _ (hsl t ⟨ht.1.le, ht.2.le⟩ y)]
    rw [e]
    exact integral_sq_le_Q s (fun x => Rr x k) t
  rw [hh2] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hfI) (Real.sqrt_nonneg _)) hM0)

/-! ### The record cell of the complete action -/

set_option maxHeartbeats 8000000 in
/-- **The first variation of the complete first-order action on a record cell** (smooth
back-reacting Dirac data, `κ ≠ 0`): bulk plus end fluxes, the bulk being the complete bosonic rows
plus the Dirac rows, bounded through the bosonic and the Dirac readouts. -/
theorem record_cell_cpl (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hC : CoupledDirac SM) (hκ : SM.κ ≠ 0) {W Y : Fin n → ST 3 → ℝ}
    (hW : ∀ c, ContDiff ℝ ∞ (W c)) (hWp : ∀ c, IsSPeriodic (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (hYp : ∀ c, IsSPeriodic (Y c)) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ x : ST 3, x 0 ∈ Icc a b → HeadChart κ (fun c => W c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ))
    (eDs : (Fin nD → ℝ) →L[ℝ] S × S') (heD : ∀ r, eDs (eD r) = r)
    {Kg : Set Met} {Kh : Set (Met × S × S')} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hMD : ∀ h ∈ Kh, ∀ (c : Fin nD → ℝ) (y : Fin n → ℝ),
      |dirJ hC.toDiracPairing h.1 (Lg κ y) h.2.1 h.2.2 (eDs c) (Lψ κ y) (Lψb κ y)| ≤
        M * ‖c‖ * ‖y‖)
    (hKg : ∀ x : ST 3, x 0 ∈ Icc a b → Lg κ (fun c => W c x) ∈ Kg)
    (hKh : ∀ x : ST 3, x 0 ∈ Icc a b →
      (Lg κ (fun c => W c x), Lψ κ (fun c => W c x), Lψb κ (fun c => W c x)) ∈ Kh)
    {s sD : ℕ} {B BD : ℝ}
    (hB : ∀ t ∈ Ioo a b, ∑ k, Q s (fun x => eB (bosR SM (hjF κ W x)) k) t ≤ B ^ 2)
    (hBD : ∀ t ∈ Ioo a b, ∑ k, Q sD (fun x => eD (dirR SM (hjF κ W x)) k) t ≤ BD ^ 2) :
    ∃ D : ℝ, cellInt a b (fun x => fderiv ℝ (L1C SM hC.toDiracPairing.P) (hjet1C κ W x)
        (hjet1C κ Y x)) =
        D + (fluxRC κ hC.toDiracPairing W Y b - fluxRC κ hC.toDiracPairing W Y a) ∧
      |D| ≤ M * ((Real.sqrt ((b - a) * B ^ 2) + Real.sqrt ((b - a) * BD ^ 2)) *
        Real.sqrt (cellInt a b (fun x => ∑ c, Y c x ^ 2))) := by
  set hP := hC.toDiracPairing with hPdef
  set SB := GenDSN.bos0 SM hC.toVariationalDirac with hSB
  obtain ⟨z', hz'⟩ := exists_cell_ext (m := m) (V := V) (S := S) (S' := S') κ hW hWp hab hc
  have hYv : ContDiff ℝ ∞ (fun x => fun c => Y c x) := contDiff_pi.2 hY
  set kY : ST 3 → Met := fun x => Lg κ (fun c => Y c x) with hkY
  set XY : ST 3 → Fin 4 → MatLie m := fun x => LA κ (fun c => Y c x) with hXY
  set ηY : ST 3 → V := fun x => LH κ (fun c => Y c x) with hηY
  set φY : ST 3 → S := fun x => Lψ κ (fun c => Y c x) with hφY
  set φbY : ST 3 → S' := fun x => Lψb κ (fun c => Y c x) with hφbY
  have hk : ContDiff ℝ ∞ kY := (Lg κ).contDiff.comp hYv
  have hX : ContDiff ℝ ∞ XY := (LA κ).contDiff.comp hYv
  have hη : ContDiff ℝ ∞ ηY := (LH κ).contDiff.comp hYv
  have hφ : ContDiff ℝ ∞ φY := (Lψ κ).contDiff.comp hYv
  have hφb : ContDiff ℝ ∞ φbY := (Lψb κ).contDiff.comp hYv
  have hks : ∀ y μ ν, kY y μ ν = kY y ν μ := fun y μ ν => symL_symm _ μ ν
  have hkp : IsSPeriodic kY := fun k x => by simp only [hkY, hYp _ k x]
  have hXp : IsSPeriodic XY := fun k x => by simp only [hXY, hYp _ k x]
  have hηp : IsSPeriodic ηY := fun k x => by simp only [hηY, hYp _ k x]
  have hφp : IsSPeriodic φY := fun k x => by simp only [hφY, hYp _ k x]
  have hφbp : IsSPeriodic φbY := fun k x => by simp only [hφbY, hYp _ k x]
  have ha : a - 1 < a := by linarith
  have hb : b < b + 1 := by linarith
  -- the bosonic and the Dirac cell variations
  have hcv : cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x)) =
      cellInt a b (bulkT SB z' kY XY ηY) + (fluxT SB z' kY XY ηY b - fluxT SB z' kY XY ηY a) :=
    cell_variation SB (GenDSN.bos0Var hC) z' hk hks hkp hX hXp hη hηp hab
  have hcd := cell_dirac hP z' hk hks hkp hX hη hφ hφp hφb hφbp hab
  -- the jets on the closed cell
  have hsl : ∀ t ∈ Icc a b, ∀ y : Fin 3 → ℝ, (Fin.cons t y : ST 3) 0 ∈ Icc a b := fun t ht y => by
    simpa using ht
  have hj1 : ∀ x : ST 3, x 0 ∈ Icc a b → j1F z'.g z'.A z'.H x = hjet1 κ W x := fun x hx => by
    obtain ⟨h1, h2, h3, -, -⟩ := hz' x hx
    exact j1F_of_near κ h1 h2 h3
  have hjC : ∀ x : ST 3, x 0 ∈ Icc a b → jC z' x = hjet1C κ W x := fun x hx => by
    obtain ⟨-, -, -, h4, h5⟩ := hz' x hx
    have e4 : ∀ γ, pd z'.ψ γ x = Lψ κ (fun c => pd (W c) γ x) := fun γ => by
      rw [(SlabLocal.pd_eventuallyEq h4 γ).eq_of_nhds, pd_famL _ hW]
    have e5 : ∀ γ, pd z'.ψb γ x = Lψb κ (fun c => pd (W c) γ x) := fun γ => by
      rw [(SlabLocal.pd_eventuallyEq h5 γ).eq_of_nhds, pd_famL _ hW]
    unfold jC hjet1C
    rw [hj1 x hx, h4.eq_of_nhds, h5.eq_of_nhds]
    simp only [e4, e5]
  have hjW : ∀ x, jW kY XY ηY φY φbY x = hjet1C κ Y x := fun x => by
    have e4 : ∀ γ, pd φY γ x = Lψ κ (fun c => pd (Y c) γ x) := fun γ => pd_famL _ hY γ x
    have e5 : ∀ γ, pd φbY γ x = Lψb κ (fun c => pd (Y c) γ x) := fun γ => pd_famL _ hY γ x
    unfold jW hjet1C
    simp only [e4, e5]
    rfl
  have hpt : ∀ x : ST 3, x 0 ∈ Icc a b →
      fderiv ℝ (L1C SM hP.P) (hjet1C κ W x) (hjet1C κ Y x) =
        fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x) +
          fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x) := fun x hx => by
    have hm : jC z' x ∈ chart1C m V S S' := ⟨GenCell.Tuple_det_neg z' x, z'.lor x⟩
    rw [← hjC x hx, ← hjW x, fderiv_L1C SM hP.P hm]
    rfl
  have hc1 : ContinuousOn (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x))
      (openSlab (a - 1) (b + 1)) :=
    continuousOn_fderiv_jet isOpen_chart1 (contDiffOn_L1SM SM)
      (continuous_j1F z'.g_smooth z'.A_smooth z'.H_smooth) (continuous_j1F hk hX hη)
      fun x _ => GenCell.Tuple_det_neg z' x
  have hc2 : ContinuousOn (fun x => fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x))
      (openSlab (a - 1) (b + 1)) :=
    continuousOn_fderiv_jet isOpen_chart1C (contDiffOn_L1D SM hP.P) (continuous_jC z')
      (continuous_jW hk hX hη hφ hφb) fun x _ => ⟨GenCell.Tuple_det_neg z' x, z'.lor x⟩
  have hL : cellInt a b (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ W x) (hjet1C κ Y x)) =
      cellInt a b (fun x => fderiv ℝ (L1SM SM) (j1F z'.g z'.A z'.H x) (j1F kY XY ηY x)) +
        cellInt a b (fun x => fderiv ℝ (L1D SM hP.P) (jC z' x) (jW kY XY ηY φY φbY x)) := by
    rw [← cellInt_add_on hc1 hc2 ha hab hb]
    exact cellInt_congr hab fun t ht y _ => hpt _ (hsl t ht y)
  -- the fluxes
  have hfl : ∀ t ∈ Icc a b, fluxT SB z' kY XY ηY t = fluxR (V := V) κ SM W Y t := by
    intro t ht
    show fluxT SB z' kY XY ηY t = fluxR (V := V) κ SB W Y t
    unfold fluxT fluxR
    have e1 : ∀ y : Fin 3 → ℝ, PFJ 0 (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        PFJ 0 (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e2 : ∀ y : Fin 3 → ℝ, fderiv ℝ (WJ 0) (j1M z'.g (Fin.cons t y)) (j1M kY (Fin.cons t y)) =
        fderiv ℝ (WJ 0) (hjet1 κ W (Fin.cons t y)).1 (hjet1 κ Y (Fin.cons t y)).1 := fun y => by
      rw [← hj1 _ (hsl t ht y)]; rfl
    have e3 : ∀ y : Fin 3 → ℝ, matFlux z' SB XY ηY 0 (Fin.cons t y) =
        MFJ SB (hjet1 κ W (Fin.cons t y)) (hjet1 κ Y (Fin.cons t y)) := fun y => by
      rw [matFlux_eq_MFJ SB z' XY ηY kY, hj1 _ (hsl t ht y)]; rfl
    unfold sint
    simp only [e1, e2, e3]
  have hfd : ∀ t ∈ Icc a b, sint (fluxD hP z' kY φY φbY 0) t = fluxDR κ hP W Y t := by
    intro t ht
    have e : ∀ y : Fin 3 → ℝ, fluxD hP z' kY φY φbY 0 (Fin.cons t y) =
        fluxDJ hP 0 (Lg κ (fun c => W c (Fin.cons t y))) (Lψ κ (fun c => W c (Fin.cons t y)))
          (Lψb κ (fun c => W c (Fin.cons t y))) (Lg κ (fun c => Y c (Fin.cons t y)))
          (Lψ κ (fun c => Y c (Fin.cons t y))) (Lψb κ (fun c => Y c (Fin.cons t y))) := fun y => by
      obtain ⟨h1, -, -, h4, h5⟩ := hz' _ (hsl t ht y)
      rw [fluxD_eq, h1.eq_of_nhds, h4.eq_of_nhds, h5.eq_of_nhds]
    unfold fluxDR sint
    simp only [e]
  -- the bulk
  have hBI : ∀ x, bulkT SB z' kY XY ηY x + bulkD hP z' kY XY ηY φY φbY x =
      bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) +
        dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) :=
    fun x => bulk_identity z' hC hκ kY XY ηY φY φbY x
  have hbF : Continuous (bosF SM z') := (contDiff_bosF SM z' hS).continuous
  have hdF : ContDiff ℝ ∞ (dirF SM z') := contDiff_dirF SM z'
  have hJc : Continuous fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hp : Continuous fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)) :=
      z'.g_smooth.continuous.prodMk (hbF.prodMk (hk.continuous.prodMk (hX.continuous.prodMk
        hη.continuous)))
    exact ContinuousAt.comp (x := x)
      (g := fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        bulkJ SM q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (f := fun x : ST 3 => (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (continuousAt_bulkJ SM (p := (z'.g x, bosF SM z' x, (kY x, XY x, ηY x)))
      (GenCell.Tuple_det_neg z' x).ne) hp.continuousAt
  have hDc : Continuous fun x =>
      dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) :=
    continuous_iff_continuousAt.2 fun x => (contDiffAt_dirJ_comp hP z'.g_smooth.contDiffAt
      hk.contDiffAt z'.ψ_smooth.contDiffAt z'.ψb_smooth.contDiffAt hdF.contDiffAt hφ.contDiffAt
      hφb.contDiffAt (chartM_tuple z' x)).continuousAt
  have hBDc : Continuous (bulkD hP z' kY XY ηY φY φbY) :=
    continuous_bulkD hP z' hk hks hX hη hφ hφb
  have hBTc : Continuous (bulkT SB z' kY XY ηY) :=
    ((hJc.add hDc).sub hBDc).congr fun x => by
      show bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x) +
        dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x) (φbY x) -
        bulkD hP z' kY XY ηY φY φbY x = bulkT SB z' kY XY ηY x
      rw [← hBI x]; ring
  have hsum : cellInt a b (bulkT SB z' kY XY ηY) + cellInt a b (bulkD hP z' kY XY ηY φY φbY) =
      cellInt a b (fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x)) +
        cellInt a b (fun x => dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x)
          (φbY x)) := by
    rw [← cellInt_add_on hBTc.continuousOn hBDc.continuousOn ha hab hb,
      ← cellInt_add_on hJc.continuousOn hDc.continuousOn ha hab hb]
    exact cellInt_congr hab fun t _ y _ => hBI _
  refine ⟨cellInt a b (fun x => bulkJ SM (z'.g x) (bosF SM z' x) (kY x) (XY x) (ηY x)) +
    cellInt a b (fun x => dirJ hP (z'.g x) (kY x) (z'.ψ x) (z'.ψb x) (dirF SM z' x) (φY x)
      (φbY x)), ?_, ?_⟩
  · rw [hL, hcv, hcd, hfl a ⟨le_rfl, hab⟩, hfl b ⟨hab, le_rfl⟩, hfd a ⟨le_rfl, hab⟩,
      hfd b ⟨hab, le_rfl⟩, ← hsum]
    unfold fluxRC
    ring
  -- the bounds
  have hg' : ∀ x : ST 3, x 0 ∈ Icc a b → z'.g x = Lg κ (fun c => W c x) := fun x hx =>
    (hz' x hx).1.eq_of_nhds
  have hB1 := abs_cellInt_readout hJc hY hab (R := fun x => eB (bosF SM z' x))
    (Rr := fun x => eB (bosR SM (hjF κ W x))) (eB.continuous.comp hbF) hM0
    (fun x hx => by
      have := hM _ (hKg x hx) (eB (bosF SM z' x)) (fun c => Y c x)
      rw [heB, ← hg' x hx] at this
      exact this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz' x hx
      show eB (bosF SM z' x) = eB (bosR SM (hjF κ W x))
      rw [← bosR_hj2 z' x SM, hj2_of_near κ h1 h2 h3 h4 h5]) hB
  have hB2 := abs_cellInt_readout hDc hY hab (R := fun x => eD (dirF SM z' x))
    (Rr := fun x => eD (dirR SM (hjF κ W x))) (eD.continuous.comp hdF.continuous) hM0
    (fun x hx => by
      have := hMD _ (hKh x hx) (eD (dirF SM z' x)) (fun c => Y c x)
      rw [heD] at this
      obtain ⟨h1, -, -, h4, h5⟩ := hz' x hx
      rw [h1.eq_of_nhds, h4.eq_of_nhds, h5.eq_of_nhds]
      exact this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz' x hx
      show eD (dirF SM z' x) = eD (dirR SM (hjF κ W x))
      rw [← dirR_hj2 z' x SM, hj2_of_near κ h1 h2 h3 h4 h5]) hBD
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hB1 hB2
    _ = _ := by ring

/-! ### Stationarity of the complete composite action -/

set_option maxHeartbeats 4000000 in
/-- **`eq:generated-stationarity` for the complete action on a chart record** (smooth
back-reacting Dirac data, `κ ≠ 0`): if every cell of the Hermite reconstruction `R(U, P)` on
`[0, Jτ]` is in the Lorentzian chart, with head metric in `K_g` and head metric/spinor values in
`K_h` (bulk constant `M` for the bosonic rows `bulkJ` and the Dirac rows `dirJ`), and the bosonic
and Dirac readouts satisfy `Σ_k Q_s(e_B R_B)_k ≤ B²`, `Σ_k Q_{s_D}(e_D R_D)_k ≤ B_D²` on every
slice, then for every nodal variation `V = (v, w)` with fixed collar the derivative
`D S^{cmp}[V]` of the complete composite action (bosonic plus Dirac) exists and
`|D S^{cmp}[V]| ≤ M (B + B_D) √(8Jτ) ‖V‖_{0,τ}`. -/
theorem stationarity_of_cells_cpl (SM : SMData (MatLie m) V S S') (hS : SMSmooth SM)
    (hC : CoupledDirac SM) (hκ : SM.κ ≠ 0) {N q : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {J : ℕ} {U P : ℕ → GS 3 n N}
    (hc : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      HeadChart κ (fun c => recF q τ U P j c x))
    {nB : ℕ} (eB : BosP m V →L[ℝ] (Fin nB → ℝ)) (eBs : (Fin nB → ℝ) →L[ℝ] BosP m V)
    (heB : ∀ r, eBs (eB r) = r) {nD : ℕ} (eD : S × S' →L[ℝ] (Fin nD → ℝ))
    (eDs : (Fin nD → ℝ) →L[ℝ] S × S') (heD : ∀ r, eDs (eD r) = r)
    {Kg : Set Met} {Kh : Set (Met × S × S')} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ g ∈ Kg, ∀ (c : Fin nB → ℝ) (y : Fin n → ℝ),
      |bulkJ SM g (eBs c) (Lg κ y) (LA κ y) (LH κ y)| ≤ M * ‖c‖ * ‖y‖)
    (hMD : ∀ h ∈ Kh, ∀ (c : Fin nD → ℝ) (y : Fin n → ℝ),
      |dirJ hC.toDiracPairing h.1 (Lg κ y) h.2.1 h.2.2 (eDs c) (Lψ κ y) (Lψb κ y)| ≤
        M * ‖c‖ * ‖y‖)
    (hKg : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      Lg κ (fun c => recF q τ U P j c x) ∈ Kg)
    (hKh : ∀ j < J, ∀ x : ST 3, x 0 ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ) →
      (Lg κ (fun c => recF q τ U P j c x), Lψ κ (fun c => recF q τ U P j c x),
        Lψb κ (fun c => recF q τ U P j c x)) ∈ Kh)
    {s sD : ℕ} {B BD : ℝ} (hB0 : 0 ≤ B) (hBD0 : 0 ≤ BD)
    (hB : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q s (fun x => eB (bosR SM (hjF κ (recF q τ U P j) x)) k) t ≤ B ^ 2)
    (hBD : ∀ j < J, ∀ t ∈ Ioo ((j : ℝ) * τ) (((j : ℝ) + 1) * τ),
      ∑ k, Q sD (fun x => eD (dirR SM (hjF κ (recF q τ U P j) x)) k) t ≤ BD ^ 2)
    (v w : ℕ → GS 3 n N) (hv0 : v 0 = 0) (hw0 : w 0 = 0) (hvJ : v J = 0) (hwJ : w J = 0) :
    ∃ D : ℝ, HasDerivAt (fun ε : ℝ => ScmpC κ SM hC.toDiracPairing.P q τ J
        (fun j => U j + ε • v j) (fun j => P j + ε • w j)) D 0 ∧
      |D| ≤ M * (B + BD) * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
  set hP := hC.toDiracPairing with hPdef
  set W : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ U P j with hWdef
  set Y : ℕ → Fin n → ST 3 → ℝ := fun j => recF q τ v w j with hYdef
  have hWs : ∀ j c, ContDiff ℝ ∞ (W j c) := fun j c => contDiff_recF q τ U P j c
  have hWp : ∀ j c, IsSPeriodic (W j c) := fun j c => isSPeriodic_recF q τ U P j c
  have hYs : ∀ j c, ContDiff ℝ ∞ (Y j c) := fun j c => contDiff_recF q τ v w j c
  have hYp : ∀ j c, IsSPeriodic (Y j c) := fun j c => isSPeriodic_recF q τ v w j c
  have hab : ∀ j : ℕ, (j : ℝ) * τ ≤ ((j : ℝ) + 1) * τ := fun j => by nlinarith
  -- linearity of the composite action
  have hlin : ∀ (ε : ℝ) (j : ℕ) (x : ST 3),
      hjet1C κ (recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j) x =
        hjet1C κ (W j) x + ε • hjet1C κ (Y j) x := fun ε j x => by
    have e : recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j =
        fun c y => W j c y + ε * Y j c y :=
      funext fun c => funext fun y => recF_add_smul q τ U P v w ε j c y
    rw [e]
    exact hjet1C_add_smul κ (hWs j) (hYs j) ε x
  have hSe : (fun ε : ℝ => ScmpC κ SM hP.P q τ J (fun j => U j + ε • v j)
      (fun j => P j + ε • w j)) =
      fun ε => ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => L1C SM hP.P (hjet1C κ (W j) x + ε • hjet1C κ (Y j) x)) := by
    funext ε
    unfold ScmpC
    simp only [hlin]
  have hder : HasDerivAt (fun ε : ℝ => ScmpC κ SM hP.P q τ J (fun j => U j + ε • v j)
      (fun j => P j + ε • w j))
      (∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
        (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x))) 0 := by
    rw [hSe]
    exact HasDerivAt.fun_sum fun j hj => cell_hasDerivAt_C κ SM hP.P (hWs j) (hWp j) (hYs j)
      (hYp j) (hab j) (hc j (Finset.mem_range.1 hj))
  refine ⟨_, hder, ?_⟩
  -- the cells
  have hcell : ∀ j ∈ Finset.range J, ∃ Dj : ℝ,
      cellInt (j * τ) ((j + 1) * τ)
          (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x)) =
        Dj + (fluxRC κ hP (W j) (Y j) (((j : ℝ) + 1) * τ) -
          fluxRC κ hP (W j) (Y j) ((j : ℝ) * τ)) ∧
      |Dj| ≤ M * ((Real.sqrt ((((j : ℝ) + 1) * τ - j * τ) * B ^ 2) +
          Real.sqrt ((((j : ℝ) + 1) * τ - j * τ) * BD ^ 2)) *
        Real.sqrt (cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2))) := fun j hj =>
    record_cell_cpl κ SM hS hC hκ (hWs j) (hWp j) (hYs j) (hYp j) (hab j)
      (hc j (Finset.mem_range.1 hj)) eB eBs heB eD eDs heD hM0 hM hMD
      (hKg j (Finset.mem_range.1 hj)) (hKh j (Finset.mem_range.1 hj))
      (hB j (Finset.mem_range.1 hj)) (hBD j (Finset.mem_range.1 hj))
  choose! Dj hDj using hcell
  -- the fluxes telescope
  set G : ℕ → ℝ := fun j => fluxRC κ hP (W j) (Y j) ((j : ℝ) * τ) with hG
  have hnode : ∀ j, fluxRC κ hP (W j) (Y j) (((j : ℝ) + 1) * τ) = G (j + 1) := fun j => by
    simp only [hG, fluxRC]
    push_cast
    rw [fluxR_congr κ SM (fun y => recF_node κ q τ hτ.ne' U P j y)
      (fun y => recF_node κ q τ hτ.ne' v w j y),
      fluxDR_congr κ hP (fun y c => recF_node_val q τ hτ.ne' U P j c y)
      (fun y c => recF_node_val q τ hτ.ne' v w j c y)]
  have hG0 : G 0 = 0 := by
    simp only [hG, fluxRC]
    rw [fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w 0 hv0 hw0 y,
      fluxDR_zero κ hP fun y c => recF_node_val_zero q τ hτ.ne' v w 0 hv0 hw0 c y]
    simp
  have hGJ : G J = 0 := by
    simp only [hG, fluxRC]
    rw [fluxR_zero κ SM fun y => recF_node_zero κ q τ hτ.ne' v w J hvJ hwJ y,
      fluxDR_zero κ hP fun y c => recF_node_val_zero q τ hτ.ne' v w J hvJ hwJ c y]
    simp
  have hsum : ∑ j ∈ Finset.range J, cellInt (j * τ) ((j + 1) * τ)
      (fun x => fderiv ℝ (L1C SM hP.P) (hjet1C κ (W j) x) (hjet1C κ (Y j) x)) =
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
  have hBB : 0 ≤ B + BD := add_nonneg hB0 hBD0
  have hDb : ∀ j ∈ Finset.range J,
      |Dj j| ≤ M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) := by
    intro j hj
    refine (hDj j hj).2.trans ?_
    have e1 : ∀ C : ℝ, (((j : ℝ) + 1) * τ - j * τ) * C = τ * C := fun C => by ring
    have e2 : Real.sqrt (τ * B ^ 2) = Real.sqrt τ * B := by
      rw [Real.sqrt_mul hτ.le, Real.sqrt_sq hB0]
    have e3 : Real.sqrt (τ * BD ^ 2) = Real.sqrt τ * BD := by
      rw [Real.sqrt_mul hτ.le, Real.sqrt_sq hBD0]
    have hL2 := recF_L2 q hτ v w j
    have hL2' : cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, Y j c x ^ 2) ≤ τ * X j := by
      refine hL2.trans (le_of_eq ?_)
      simp only [hX, hcdef]; ring
    rw [e1, e1, e2, e3]
    have := Real.sqrt_le_sqrt hL2'
    have hB' : 0 ≤ Real.sqrt τ * B + Real.sqrt τ * BD :=
      add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB0) (mul_nonneg (Real.sqrt_nonneg _) hBD0)
    calc M * ((Real.sqrt τ * B + Real.sqrt τ * BD) * Real.sqrt (cellInt (j * τ) ((j + 1) * τ)
          (fun x => ∑ c, Y j c x ^ 2))) ≤
          M * ((Real.sqrt τ * B + Real.sqrt τ * BD) * Real.sqrt (τ * X j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hB') hM0
      _ = M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) := by ring
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
  have hMB : 0 ≤ M * (B + BD) := mul_nonneg hM0 hBB
  calc |∑ j ∈ Finset.range J, Dj j| ≤ ∑ j ∈ Finset.range J, |Dj j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range J, M * (B + BD) * (Real.sqrt τ * Real.sqrt (τ * X j)) :=
        Finset.sum_le_sum hDb
    _ = M * (B + BD) * ∑ j ∈ Finset.range J, Real.sqrt τ * Real.sqrt (τ * X j) := by
        rw [Finset.mul_sum]
    _ ≤ M * (B + BD) * (Real.sqrt (J * τ) *
          Real.sqrt (8 * (τ * ∑ j ∈ Finset.range (J + 1), c j))) := by
        refine mul_le_mul_of_nonneg_left (hCS.trans ?_) hMB
        rw [hsumτ]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumX) (Real.sqrt_nonneg _)
    _ = M * (B + BD) * Real.sqrt (8 * (J * τ)) * vnorm q τ J v w := by
        rw [hvn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
        ring

end RenewalGeometry.GenCplSt
