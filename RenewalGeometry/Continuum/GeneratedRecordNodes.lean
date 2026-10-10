/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedRecordCell

/-!
# Nodes of the Hermite record

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` (the Hermite
reconstruction `R` from nodal values and slopes and the norm `‖V‖²_{0,τ}`):

* `recF q τ U P j` — the cubic-Hermite reconstruction on the cell `[jτ, (j+1)τ]` from the nodal
  values `U j, U (j+1)` and slopes `P j, P (j+1)` (coordinate fields);
* **`recF_node`** — consecutive cells have the same head 1-jets on the common node slice (the
  reconstruction is `C¹` in time), so the time fluxes `GenRecCell.fluxR` telescope;
* **`recF_node_zero`** — a nodal value and slope `0` give a vanishing head 1-jet on the node
  slice (fixed collar);
* **`recF_L2`** — `∫_{cell} Σ_c |R(V)_c|² ≤ 4τ(‖v_j‖² + ‖v_{j+1}‖² + τ²(‖v̇_j‖² + ‖v̇_{j+1}‖²))`
  with `‖a‖² = Σ_c ∫_{𝕋³} |fld_c(a)|²` (`nrm2`);
* `recF_add_smul`, `hjet1_add_smul` — linearity of the reconstruction and of the head 1-jets.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenRecNodes

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge ActualJetBridge ActualJetState
  ActualJetCompleteForcing ActualJetRecon ActualJetKato GenHermite GenResMaps GenPhysIdFinal
  GenReadout EHJetVariation EHFieldVariation GenMatVar GenNoether GenFOGrav GenMatEuler GenFOAction
  GenCell GenCellVar GenCellBulk KatoGalerkin GenRecCell SpectralGalerkin CubicHermite
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

/-! ### Head 1-jets from coordinate 1-jets -/

section HeadJets

theorem hjet1_congr {W W' : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hW' : ∀ c, ContDiff ℝ ∞ (W' c)) {x : ST 3} (h0 : ∀ c, W c x = W' c x)
    (h1 : ∀ c α, pd (W c) α x = pd (W' c) α x) :
    hjet1 (V := V) κ W x = hjet1 κ W' x := by
  have e0 : (fun c => W c x) = fun c => W' c x := funext h0
  have e1 : ∀ α, (fun c => pd (W c) α x) = fun c => pd (W' c) α x := fun α => funext fun c => h1 c α
  unfold hjet1 j1F
  simp only [pd_famL_fun _ hW, pd_famL_fun _ hW', e0, e1]

theorem hjet1_zero {W : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c)) {x : ST 3}
    (h0 : ∀ c, W c x = 0) (h1 : ∀ c α, pd (W c) α x = 0) :
    hjet1 (V := V) κ W x = 0 := by
  have e0 : (fun c => W c x) = 0 := funext h0
  have e1 : ∀ α, (fun c => pd (W c) α x) = 0 := fun α => funext fun c => h1 c α
  unfold hjet1 j1F
  simp only [pd_famL_fun _ hW, e0, e1, map_zero]
  rfl

end HeadJets

/-! ### Jets of Galerkin-curve fields on a slice -/

section Slice

variable {N : ℕ} (q : ℕ)

theorem fldc_slice_jet {c₁ c₂ c₁' c₂' : ℝ → GS 3 n N} (hc₁ : ContDiff ℝ ∞ c₁)
    (hc₂ : ContDiff ℝ ∞ c₂) (hd₁ : ∀ t, HasDerivAt c₁ (c₁' t) t)
    (hd₂ : ∀ t, HasDerivAt c₂ (c₂' t) t) {t : ℝ} (hv : c₁ t = c₂ t) (hd : c₁' t = c₂' t)
    (b : Fin n) (y : Fin 3 → ℝ) :
    fldc q c₁ b (Fin.cons t y) = fldc q c₂ b (Fin.cons t y) ∧
      ∀ α, pd (fldc q c₁ b) α (Fin.cons t y) = pd (fldc q c₂ b) α (Fin.cons t y) := by
  have hval : ∀ y' : Fin 3 → ℝ, fldc q c₁ b (Fin.cons t y') = fldc q c₂ b (Fin.cons t y') :=
    fun y' => by simp only [fldc, Fin.cons_zero, hv]
  refine ⟨hval y, fun α => ?_⟩
  induction α using Fin.cases with
  | zero =>
    rw [pd_fldc_zero q hc₁ hd₁, pd_fldc_zero q hc₂ hd₂]
    simp only [fldc, Fin.cons_zero, hd]
  | succ i =>
    have d₁ := (contDiff_fldc q hc₁ b).differentiable (by simp) (Fin.cons t y)
    have d₂ := (contDiff_fldc q hc₂ b).differentiable (by simp) (Fin.cons t y)
    rw [← pd_slice i d₁, ← pd_slice i d₂]
    have : (fun y' => fldc q c₁ b (Fin.cons t y')) = fun y' => fldc q c₂ b (Fin.cons t y') :=
      funext hval
    rw [this]

theorem fldc_slice_zero {c c' : ℝ → GS 3 n N} (hc : ContDiff ℝ ∞ c)
    (hd : ∀ t, HasDerivAt c (c' t) t) {t : ℝ} (hv : c t = 0) (hd0 : c' t = 0) (b : Fin n)
    (y : Fin 3 → ℝ) :
    fldc q c b (Fin.cons t y) = 0 ∧ ∀ α, pd (fldc q c b) α (Fin.cons t y) = 0 := by
  have h := fldc_slice_jet q hc (contDiff_const (c := (0 : GS 3 n N))) hd
    (fun t => hasDerivAt_const t (0 : GS 3 n N)) (c₂' := fun _ => 0) hv hd0 b y
  have hz : fldc q (fun _ : ℝ => (0 : GS 3 n N)) b = fun _ => 0 := by
    funext x
    simp only [fldc, ← fldL_apply, map_zero]
  rw [hz] at h
  refine ⟨h.1, fun α => (h.2 α).trans ?_⟩
  unfold SobolevOpen.pd
  simp

end Slice

/-! ### The Hermite reconstruction on the cells -/

section Record

variable {N : ℕ} (q : ℕ) (τ : ℝ)

/-- **The cubic-Hermite reconstruction on the cell `[jτ, (j+1)τ]`** from nodal values `U` and
nodal slopes `P`. -/
def recF (U P : ℕ → GS 3 n N) (j : ℕ) : Fin n → ST 3 → ℝ :=
  recW τ (j * τ) (U j) (U (j + 1)) (P j) (P (j + 1)) q

theorem contDiff_recF (U P : ℕ → GS 3 n N) (j : ℕ) (c : Fin n) :
    ContDiff ℝ ∞ (recF q τ U P j c) := contDiff_recW τ _ _ _ _ _ c

theorem isSPeriodic_recF (U P : ℕ → GS 3 n N) (j : ℕ) (c : Fin n) :
    IsSPeriodic (recF q τ U P j c) := isSPeriodic_fldc q _ c

/-- **The reconstruction is `C¹` across the nodes**: consecutive cells have the same head 1-jets on
the common node slice. -/
theorem recF_node (hτ : τ ≠ 0) (U P : ℕ → GS 3 n N) (j : ℕ) (y : Fin 3 → ℝ) :
    hjet1 (V := V) κ (recF q τ U P j) (Fin.cons (((j : ℝ) + 1) * τ) y) =
      hjet1 κ (recF q τ U P (j + 1)) (Fin.cons (((j : ℝ) + 1) * τ) y) := by
  have h1 : (((j : ℝ) + 1) * τ - j * τ) / τ = 1 := by field_simp; ring
  have h0 : (((j : ℝ) + 1) * τ - ((j + 1 : ℕ) : ℝ) * τ) / τ = 0 := by push_cast; simp
  refine hjet1_congr κ (contDiff_recF q τ U P j) (contDiff_recF q τ U P (j + 1)) (fun c => ?_)
    (fun c α => ?_)
  · refine (fldc_slice_jet q (contDiff_hc τ _ _ _ _ _) (contDiff_hc τ _ _ _ _ _)
      (hasDerivAt_hc hτ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).1
    · simp only [hc, h1, h0, hermite_one, hermite_zero]
    · simp only [hcD, h1, h0, hermiteD_one, hermiteD_zero]
  · refine (fldc_slice_jet q (contDiff_hc τ _ _ _ _ _) (contDiff_hc τ _ _ _ _ _)
      (hasDerivAt_hc hτ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).2 α
    · simp only [hc, h1, h0, hermite_one, hermite_zero]
    · simp only [hcD, h1, h0, hermiteD_one, hermiteD_zero]

/-- **Fixed collar**: a vanishing nodal value and slope give a vanishing head 1-jet of the
reconstruction on the node slice. -/
theorem recF_node_zero (hτ : τ ≠ 0) (U P : ℕ → GS 3 n N) (j : ℕ) (hU : U j = 0) (hP : P j = 0)
    (y : Fin 3 → ℝ) : hjet1 (V := V) κ (recF q τ U P j) (Fin.cons ((j : ℝ) * τ) y) = 0 := by
  have h0 : ((j : ℝ) * τ - j * τ) / τ = 0 := by simp
  refine hjet1_zero κ (contDiff_recF q τ U P j) (fun c => ?_) (fun c α => ?_)
  · refine (fldc_slice_zero q (contDiff_hc τ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).1
    · simp only [hc, h0, hermite_zero, hU]
    · simp only [hcD, h0, hermiteD_zero, hP]
  · refine (fldc_slice_zero q (contDiff_hc τ _ _ _ _ _) (hasDerivAt_hc hτ _ _ _ _ _) ?_ ?_ c y).2 α
    · simp only [hc, h0, hermite_zero, hU]
    · simp only [hcD, h0, hermiteD_zero, hP]

end Record

/-! ### The `L²` size of the reconstruction -/

section L2

variable {N : ℕ} (q : ℕ)

/-- The squared `L²(𝕋³)` norm `Σ_c ∫_{𝕋³} |fld_c(a)|²` of the field of a Galerkin state. -/
def nrm2 (a : GS 3 n N) : ℝ := ∑ c, sint (fun x => fld q a c x ^ 2) 0

theorem nrm2_nonneg (a : GS 3 n N) : 0 ≤ nrm2 q a :=
  Finset.sum_nonneg fun c _ => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem fld_lin (a : GS 3 n N) (c : Fin n) (x : ST 3) (r : ℝ) (a' : GS 3 n N) :
    fld q (a + r • a') c x = fld q a c x + r * fld q a' c x := by
  rw [← fldL_apply, ← fldL_apply, ← fldL_apply, map_add, map_smul, smul_eq_mul]

theorem fld_smul' (a : GS 3 n N) (c : Fin n) (x : ST 3) (r : ℝ) :
    fld q (r • a) c x = r * fld q a c x := by
  rw [← fldL_apply, ← fldL_apply, map_smul, smul_eq_mul]

theorem fld_add' (a a' : GS 3 n N) (c : Fin n) (x : ST 3) :
    fld q (a + a') c x = fld q a c x + fld q a' c x := by
  rw [← fldL_apply, ← fldL_apply, ← fldL_apply, map_add]

theorem fld_slice_time (a : GS 3 n N) (c : Fin n) (t : ℝ) (y : Fin 3 → ℝ) :
    fld q a c (Fin.cons t y) = fld q a c (Fin.cons 0 y) := by
  have e : (Fin.cons t y : ST 3) = Fin.cons 0 y + t • ev (0 : Fin 4) := by
    ext i
    induction i using Fin.cases with
    | zero => simp [ev]
    | succ i => simp [ev, Pi.single_apply, Fin.succ_ne_zero]
  rw [e, fld_time_shift]

theorem sq4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- **The `L²` size of the Hermite reconstruction on a cell.** -/
theorem recF_L2 {τ : ℝ} (hτ : 0 < τ) (v w : ℕ → GS 3 n N) (j : ℕ) :
    cellInt (j * τ) ((j + 1) * τ) (fun x => ∑ c, recF q τ v w j c x ^ 2) ≤
      τ * (4 * (nrm2 q (v j) + nrm2 q (v (j + 1)) +
        τ ^ 2 * (nrm2 q (w j) + nrm2 q (w (j + 1))))) := by
  have hab : (j : ℝ) * τ ≤ (j + 1) * τ := by nlinarith
  have hcY : Continuous fun x => ∑ c, recF q τ v w j c x ^ 2 :=
    continuous_finsetSum _ fun c _ => (contDiff_recF q τ v w j c).continuous.pow 2
  set G : ST 3 → ℝ := fun x => 4 * ∑ c, (fld q (v j) c x ^ 2 + fld q (v (j + 1)) c x ^ 2 +
    τ ^ 2 * fld q (w j) c x ^ 2 + τ ^ 2 * fld q (w (j + 1)) c x ^ 2) with hG
  have hf : ∀ a : GS 3 n N, ∀ c, Continuous (fld q a c) := fun a c => (contDiff_fld q a c).continuous
  have hGc : ∀ c, Continuous fun x => fld q (v j) c x ^ 2 + fld q (v (j + 1)) c x ^ 2 +
      τ ^ 2 * fld q (w j) c x ^ 2 + τ ^ 2 * fld q (w (j + 1)) c x ^ 2 := fun c => by
    have := hf (v j) c; have := hf (v (j + 1)) c; have := hf (w j) c; have := hf (w (j + 1)) c
    fun_prop
  have hGv : ∀ t, sint G t = 4 * (nrm2 q (v j) + nrm2 q (v (j + 1)) +
      τ ^ 2 * (nrm2 q (w j) + nrm2 q (w (j + 1)))) := by
    intro t
    have e1 : sint G t = sint G 0 := by
      have hG' : ∀ y : Fin 3 → ℝ, G (Fin.cons t y) = G (Fin.cons 0 y) := fun y => by
        simp only [hG, fld_slice_time q _ _ t y]
      unfold sint
      simp only [hG']
    have hpc : ∀ c, sint (fun x => fld q (v j) c x ^ 2 + fld q (v (j + 1)) c x ^ 2 +
        τ ^ 2 * fld q (w j) c x ^ 2 + τ ^ 2 * fld q (w (j + 1)) c x ^ 2) 0 =
        sint (fun x => fld q (v j) c x ^ 2) 0 + sint (fun x => fld q (v (j + 1)) c x ^ 2) 0 +
          τ ^ 2 * (sint (fun x => fld q (w j) c x ^ 2) 0 +
            sint (fun x => fld q (w (j + 1)) c x ^ 2) 0) := fun c => by
      have h1 : Continuous fun x => fld q (v j) c x ^ 2 := (hf (v j) c).pow 2
      have h2 : Continuous fun x => fld q (v (j + 1)) c x ^ 2 := (hf (v (j + 1)) c).pow 2
      have h3' : Continuous fun x => fld q (w j) c x ^ 2 := (hf (w j) c).pow 2
      have h4' : Continuous fun x => fld q (w (j + 1)) c x ^ 2 := (hf (w (j + 1)) c).pow 2
      have h3 : Continuous fun x => τ ^ 2 * fld q (w j) c x ^ 2 := continuous_const.mul h3'
      have h4 : Continuous fun x => τ ^ 2 * fld q (w (j + 1)) c x ^ 2 := continuous_const.mul h4'
      have h12 : Continuous fun x => fld q (v j) c x ^ 2 + fld q (v (j + 1)) c x ^ 2 := h1.add h2
      have h123 : Continuous fun x => fld q (v j) c x ^ 2 + fld q (v (j + 1)) c x ^ 2 +
          τ ^ 2 * fld q (w j) c x ^ 2 := h12.add h3
      rw [sint_add h123 h4, sint_add h12 h3, sint_add h1 h2,
        sint_const_mul (τ ^ 2) (fun x => fld q (w j) c x ^ 2),
        sint_const_mul (τ ^ 2) (fun x => fld q (w (j + 1)) c x ^ 2)]
      ring
    rw [e1, hG, sint_const_mul, sint_sum _ hGc]
    unfold nrm2
    simp only [hpc, Finset.sum_add_distrib, ← Finset.mul_sum]
    try ring
  have hle : ∀ t ∈ Ioo ((j : ℝ) * τ) ((j + 1) * τ),
      sint (fun x => ∑ c, recF q τ v w j c x ^ 2) t ≤ sint G t := by
    intro t ht
    have hθ : (t - j * τ) / τ ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [ht.1]) hτ.le
      · rw [div_le_one hτ]; linarith [ht.2]
    have hH := abs_basisH_le hθ
    have hGb := abs_basisG_le hθ
    unfold sint
    refine integral_mono (integrableOn_slice hcY t)
      (integrableOn_slice (continuous_const.mul (continuous_finsetSum _ fun c _ => hGc c)) t)
      fun y => ?_
    simp only [hG]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have e : recF q τ v w j c (Fin.cons t y) =
        basisH 0 ((t - j * τ) / τ) * fld q (v j) c (Fin.cons t y) +
        basisH 1 ((t - j * τ) / τ) * fld q (v (j + 1)) c (Fin.cons t y) +
        τ * basisG 0 ((t - j * τ) / τ) * fld q (w j) c (Fin.cons t y) +
        τ * basisG 1 ((t - j * τ) / τ) * fld q (w (j + 1)) c (Fin.cons t y) := by
      simp only [recF, recW, fldc, hc, hermite, Fin.cons_zero, fld_add', fld_smul']
    rw [e]
    refine (sq4_le _ _ _ _).trans ?_
    have b1 : (basisH 0 ((t - j * τ) / τ) * fld q (v j) c (Fin.cons t y)) ^ 2 ≤
        fld q (v j) c (Fin.cons t y) ^ 2 := by
      rw [mul_pow]
      have := sq_le_one_iff_abs_le_one _ |>.2 (hH 0)
      nlinarith [sq_nonneg (fld q (v j) c (Fin.cons t y))]
    have b2 : (basisH 1 ((t - j * τ) / τ) * fld q (v (j + 1)) c (Fin.cons t y)) ^ 2 ≤
        fld q (v (j + 1)) c (Fin.cons t y) ^ 2 := by
      rw [mul_pow]
      have := sq_le_one_iff_abs_le_one _ |>.2 (hH 1)
      nlinarith [sq_nonneg (fld q (v (j + 1)) c (Fin.cons t y))]
    have b3 : (τ * basisG 0 ((t - j * τ) / τ) * fld q (w j) c (Fin.cons t y)) ^ 2 ≤
        τ ^ 2 * fld q (w j) c (Fin.cons t y) ^ 2 := by
      rw [mul_pow, mul_pow]
      have := sq_le_one_iff_abs_le_one _ |>.2 (hGb 0)
      nlinarith [sq_nonneg (fld q (w j) c (Fin.cons t y)), sq_nonneg τ,
        mul_nonneg (sq_nonneg τ) (sq_nonneg (fld q (w j) c (Fin.cons t y)))]
    have b4 : (τ * basisG 1 ((t - j * τ) / τ) * fld q (w (j + 1)) c (Fin.cons t y)) ^ 2 ≤
        τ ^ 2 * fld q (w (j + 1)) c (Fin.cons t y) ^ 2 := by
      rw [mul_pow, mul_pow]
      have := sq_le_one_iff_abs_le_one _ |>.2 (hGb 1)
      nlinarith [sq_nonneg (fld q (w (j + 1)) c (Fin.cons t y)), sq_nonneg τ,
        mul_nonneg (sq_nonneg τ) (sq_nonneg (fld q (w (j + 1)) c (Fin.cons t y)))]
    linarith
  have := cellInt_le_of_slices hcY hab (B := 4 * (nrm2 q (v j) + nrm2 q (v (j + 1)) +
      τ ^ 2 * (nrm2 q (w j) + nrm2 q (w (j + 1))))) fun t ht => (hle t ht).trans (hGv t).le
  refine this.trans (le_of_eq ?_)
  ring

end L2

/-! ### Linearity -/

section Linear

variable {N : ℕ} (q : ℕ) (τ : ℝ)

theorem hermite_add_smul (U₀ U₁ P₀ P₁ v₀ v₁ w₀ w₁ : GS 3 n N) (ε θ : ℝ) :
    hermite τ (U₀ + ε • v₀) (U₁ + ε • v₁) (P₀ + ε • w₀) (P₁ + ε • w₁) θ =
      hermite τ U₀ U₁ P₀ P₁ θ + ε • hermite τ v₀ v₁ w₀ w₁ θ := by
  simp only [hermite]
  module

theorem recF_add_smul (U P v w : ℕ → GS 3 n N) (ε : ℝ) (j : ℕ) (c : Fin n) (x : ST 3) :
    recF q τ (fun i => U i + ε • v i) (fun i => P i + ε • w i) j c x =
      recF q τ U P j c x + ε * recF q τ v w j c x := by
  simp only [recF, recW, fldc, hc, hermite_add_smul, fld_lin]

theorem hjet1_add_smul {W Y : Fin n → ST 3 → ℝ} (hW : ∀ c, ContDiff ℝ ∞ (W c))
    (hY : ∀ c, ContDiff ℝ ∞ (Y c)) (ε : ℝ) (x : ST 3) :
    hjet1 (V := V) κ (fun c y => W c y + ε * Y c y) x = hjet1 κ W x + ε • hjet1 κ Y x := by
  have hWv : ContDiff ℝ ∞ (fun y => fun c => W c y) := contDiff_pi.2 hW
  have hYv : ContDiff ℝ ∞ (fun y => fun c => Y c y) := contDiff_pi.2 hY
  have hsplit : ∀ y, (fun c => W c y + ε * Y c y) = (fun c => W c y) + ε • (fun c => Y c y) :=
    fun y => funext fun c => by simp
  have eg : (fun y => Lg κ (fun c => W c y + ε * Y c y)) =
      fun y => Lg κ (fun c => W c y) + ε • Lg κ (fun c => Y c y) := by
    funext y; rw [hsplit y, map_add, map_smul]
  have eA : (fun y => LA κ (fun c => W c y + ε * Y c y)) =
      fun y => LA κ (fun c => W c y) + ε • LA κ (fun c => Y c y) := by
    funext y; rw [hsplit y, map_add, map_smul]
  have eH : (fun y => LH κ (fun c => W c y + ε * Y c y)) =
      fun y => LH κ (fun c => W c y) + ε • LH κ (fun c => Y c y) := by
    funext y; rw [hsplit y, map_add, map_smul]
  unfold hjet1
  beta_reduce
  rw [eg, eA, eH]
  exact j1F_add_smul ((Lg κ).contDiff.comp hWv) ((Lg κ).contDiff.comp hYv)
    ((LA κ).contDiff.comp hWv) ((LA κ).contDiff.comp hYv) ((LH κ).contDiff.comp hWv)
    ((LH κ).contDiff.comp hYv) ε x

end Linear

end RenewalGeometry.GenRecNodes
