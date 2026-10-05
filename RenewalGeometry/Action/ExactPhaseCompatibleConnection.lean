/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactPhaseCompatibleNormalForm
import RenewalGeometry.DiscreteAnalysis.OddPhaseDerivativeReal

/-!
# The phase-compatible action, Lorentz coordinates and the Cartan operator
  (`eq:supp-exact-phase-compatible-derivative`, `eq:supp-exact-connection-load`,
  `eq:supp-exact-phase-action`, `eq:supp-exact-connection-normal-form`;
  emergent-spacetime manuscript)

* Lorentz coordinates: the basis `lorBasis` of `𝔰𝔬(1,3)` (three boosts `K_a`, three rotations
  `J_a`), `iota c = Σ_k c_k G_k`, `coord X k = b(G_k, X)/g_k` with Gram diagonal
  `g = (2,2,2,-2,-2,-2)` (`pairing_lorBasis`); `coord_iota`, `iota_coord` (every Lorentz
  matrix is `iota` of its coordinates), `pairing_iota` (`b(X, ι d) = Σ_k g_k coord(X)_k d_k`).
* Phase-compatible loads (`N` odd, `h = 1/N`, `δ_i = OddPhaseDerivativeReal.pd i`):
  `f°_{h,0} = Σ_i δ_iΠ_i` (`load0Ph`), `f°_{h,i} = -∂_tΠ_i - Σ_{j≠i} δ_jΣ_ji` (`loadSpPh`),
  the phase-compatible normal-form density `nfDensityPh` and the **phase-compatible action**
  `𝒫° = 𝒫^c + ∫⟨(f° - f)·A, 1⟩_h dt` (`phaseAction`, `eq:supp-exact-phase-action`);
  `phaseAction_eq_normalForm`: `𝒫° = ∫⟨-2χΛ det e + f°_h·A + q_e(A) + r_h(e,A), 1⟩_h dt`.
* Connection fields in coordinates `Conn N = Site N → Fin 4 → Fin 6 → ℝ` (`μ = 0` temporal,
  `μ = i.succ` spatial), the instantaneous phase-compatible Lagrangian `phaseLagr`.
* The Cartan operator `C(e)` (`cartanOp`): `(C A)_0 = Σ_i [A_i, Π_i]`,
  `(C A)_i = [Π_i, A_0] + Σ_j [A_j, Σ_ij]`, in coordinates; `qc_add`: the exact polarization
  `q(A + δ) = q(A) + ⟨C A, δ⟩_b + q(δ)` and `qc_eq_half`: `q(A) = ½⟨A, C A⟩_b`, i.e.
  `½ AᵀC(e)A` of `eq:supp-exact-connection-normal-form`.
-/

open Finset NormedSpace

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LogBCH PalatiniEinsteinAlgebra

/-! ### Lorentz coordinates -/

/-- The basis of `𝔰𝔬(1,3)`: boosts `K_1, K_2, K_3` (`K_a = E_{0a} + E_{a0}`) and rotations
`J_1, J_2, J_3` (`(J_a)^b{}_c = ε_{abc}`). -/
def lorBasis : Fin 6 → M4 :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0],
    !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0],
    !![0, 0, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 0]]

/-- The diagonal Gram matrix `g_k = b(G_k, G_k)` of the basis. -/
def gram : Fin 6 → ℝ := ![2, 2, 2, -2, -2, -2]

theorem gram_ne_zero (k : Fin 6) : gram k ≠ 0 := by fin_cases k <;> norm_num [gram]

set_option maxHeartbeats 1000000 in
theorem pairing_lorBasis (k l : Fin 6) :
    pairing (lorBasis k) (lorBasis l) = if k = l then gram k else 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [pairing, lorBasis, gram, Matrix.trace, Fin.sum_univ_four, Matrix.mul_apply] <;> norm_num

theorem isLorentz_lorBasis (k : Fin 6) : IsLorentz (lorBasis k) := by
  unfold IsLorentz
  fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [lorBasis, eta, minkowski, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal]

/-- `ι c = Σ_k c_k G_k`. -/
def iota (c : Fin 6 → ℝ) : M4 := ∑ k, c k • lorBasis k

/-- Coordinates `coord X k = b(G_k, X)/g_k`. -/
def coord (X : M4) (k : Fin 6) : ℝ := pairing (lorBasis k) X / gram k

theorem isLorentz_iota (c : Fin 6 → ℝ) : IsLorentz (iota c) :=
  so13.sum_mem fun k _ => so13.smul_mem (c k) (isLorentz_lorBasis k)

theorem pairing_lorBasis_iota (k : Fin 6) (c : Fin 6 → ℝ) :
    pairing (lorBasis k) (iota c) = gram k * c k := by
  unfold iota
  rw [pairing_sum_right]
  simp only [pairing_smul_right, pairing_lorBasis, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

theorem coord_iota (c : Fin 6 → ℝ) : coord (iota c) = c := by
  funext k
  rw [coord, pairing_lorBasis_iota, mul_div_cancel_left₀ (c k) (gram_ne_zero k)]

/-- `b(X, ι d) = Σ_k g_k coord(X)_k d_k` for every `X`. -/
theorem pairing_iota (X : M4) (d : Fin 6 → ℝ) :
    pairing X (iota d) = ∑ k, gram k * coord X k * d k := by
  unfold iota
  rw [pairing_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pairing_smul_right, coord, pairing_comm, mul_div_cancel₀ _ (gram_ne_zero k)]
  ring

theorem pairing_iota_iota (c d : Fin 6 → ℝ) :
    pairing (iota c) (iota d) = ∑ k, gram k * c k * d k := by
  rw [pairing_iota, coord_iota]

theorem coord_add (X Y : M4) : coord (X + Y) = coord X + coord Y := by
  funext k; simp [coord, pairing_add_right, add_div]

theorem coord_smul (c : ℝ) (X : M4) : coord (c • X) = c • coord X := by
  funext k; simp [coord, pairing_smul_right, mul_div_assoc]

theorem coord_neg (X : M4) : coord (-X) = -coord X := by
  funext k; simp [coord, pairing_neg_right, neg_div]

theorem coord_sum {ι : Type*} (s : Finset ι) (X : ι → M4) :
    coord (∑ i ∈ s, X i) = ∑ i ∈ s, coord (X i) := by
  funext k; simp [coord, pairing_sum_right, Finset.sum_div]

theorem iota_add (c d : Fin 6 → ℝ) : iota (c + d) = iota c + iota d := by
  simp [iota, add_smul, Finset.sum_add_distrib]

theorem iota_smul (a : ℝ) (c : Fin 6 → ℝ) : iota (a • c) = a • iota c := by
  simp [iota, Finset.smul_sum, smul_smul]

theorem iota_zero : iota 0 = 0 := by simp [iota]

theorem iota_neg (c : Fin 6 → ℝ) : iota (-c) = -iota c := by
  simp [iota, neg_smul, Finset.sum_neg_distrib]

set_option maxHeartbeats 1000000 in
/-- Every Lorentz matrix is `ι` of its coordinates (`ι` is onto `𝔰𝔬(1,3)`). -/
theorem iota_coord {X : M4} (hX : IsLorentz X) : iota (coord X) = X := by
  have hc : ∀ a b, (X.transpose * eta + eta * X) a b = 0 := fun a b => by rw [hX]; rfl
  have hc' : ∀ a b, X b a * eta b b + eta a a * X a b = 0 := by
    intro a b
    have := hc a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] at this
    simpa [eta, minkowski, Matrix.diagonal, Fin.sum_univ_four, Finset.sum_ite_eq'] using this
  ext a b
  have h00 := hc' 0 0; have h11 := hc' 1 1; have h22 := hc' 2 2; have h33 := hc' 3 3
  have h01 := hc' 0 1; have h02 := hc' 0 2; have h03 := hc' 0 3
  have h12 := hc' 1 2; have h13 := hc' 1 3; have h23 := hc' 2 3
  simp only [eta, minkowski, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h00 h11 h22 h33 h01 h02 h03 h12 h13 h23
  norm_num at h00 h11 h22 h33 h01 h02 h03 h12 h13 h23
  fin_cases a <;> fin_cases b <;>
    simp [iota, coord, pairing, lorBasis, gram, Matrix.trace, Fin.sum_univ_four,
      Fin.sum_univ_succ, Matrix.mul_apply] <;> linarith

/-! ### Phase-compatible loads and the phase-compatible action -/

open OddPhaseDerivativeReal in
/-- The phase-compatible temporal load `f°_{h,0} = Σ_i δ_iΠ_i` (`eq:supp-exact-connection-load`
with the spatial `D_i^-` replaced by the phase derivatives `δ_i`). -/
def load0Ph {N : ℕ} [NeZero N] (χ : ℝ) (e : Site N → M4) (x : Site N) : M4 :=
  ∑ i, pd i (fun y => piArr χ (e y) i) x

open OddPhaseDerivativeReal in
/-- The spatial part `-Σ_{j≠i} δ_jΣ_ji` of the phase-compatible load `f°_{h,i}`. -/
def loadSpPh {N : ℕ} [NeZero N] (χ : ℝ) (e : Site N → M4) (i : Fin 3) (x : Site N) : M4 :=
  -∑ j, pd j (fun y => sigmaArr χ (e y) j i) x

variable {N : ℕ} [NeZero N]

/-- The regulator spacing `h = 1/N`. -/
def hN (N : ℕ) : ℝ := (N : ℝ)⁻¹

theorem hN_ne_zero : hN N ≠ 0 := by
  unfold hN; exact inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))

theorem hN_pos : 0 < hN N := by
  unfold hN; exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- The phase-compatible normal-form density
`-2χΛ det e + f°_h(e)·A + q_e(A) + r_h(e, A)`. -/
def nfDensityPh (χ Λ h : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (A0 : Site N → M4)
    (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  -2 * χ * Λ * (e x).det + pairing (load0Ph χ e x) (A0 x) +
    (∑ i, pairing (-Pidot i x + loadSpPh χ e i x) (A i x)) + qc χ e A0 A x +
    remDensity χ h e A0 A x

/-- The load correction density `(f°_h - f_h)·A`. -/
def loadCorrection (χ h : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  pairing (load0Ph χ e x - load0 χ h e x) (A0 x) +
    ∑ i, pairing (loadSpPh χ e i x - loadSp χ h e i x) (A i x)

/-- **The phase-compatible action** `eq:supp-exact-phase-action`:
`𝒫°_{h,D} = 𝒫^c_{h,D} + ∫₀ᵀ ⟨(f°_h - f_h)·A, 1⟩_h dt` (`h = 1/N`). -/
def phaseAction (χ Λ T : ℝ) (e A0 : ℝ → Site N → M4) (A : ℝ → Fin 3 → Site N → M4) : ℝ :=
  completedAction χ Λ (hN N) T e A0 A +
    ∫ t in (0 : ℝ)..T, gridPair (hN N) (loadCorrection χ (hN N) (e t) (A0 t) (A t))

theorem nfDensityPh_eq (χ Λ h : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4)
    (A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) :
    nfDensityPh χ Λ h e Pidot A0 A x =
      nfDensity χ Λ h e Pidot A0 A x + loadCorrection χ h e A0 A x := by
  unfold nfDensityPh nfDensity loadCorrection
  simp only [pairing_sub_left, pairing_add_left, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **Normal form of the phase-compatible action**:
`𝒫° = ∫₀ᵀ ⟨-2χΛ det e + f°_h(e)·A + q_e(A) + r_h(e, A), 1⟩_h dt`. -/
theorem phaseAction_eq_normalForm (χ Λ T : ℝ)
    (e A0 : ℝ → Site N → M4) (A : ℝ → Fin 3 → Site N → M4) (Pidot : ℝ → Fin 3 → Site N → M4)
    (hA : ∀ t, HasDerivAt A (deriv A t) t)
    (hPi : ∀ t i x, HasDerivAt (fun s => piArr χ (e s x) i) (Pidot t i x) t)
    (hint : IntervalIntegrable
      (fun t => gridPair (hN N) (nfDensity χ Λ (hN N) (e t) (Pidot t) (A0 t) (A t)))
        MeasureTheory.volume 0 T)
    (hdint : IntervalIntegrable
      (fun t => gridPair (hN N) (fun x => ∑ i, (pairing (Pidot t i x) (A t i x) +
        pairing (piArr χ (e t x) i) (deriv A t i x)))) MeasureTheory.volume 0 T)
    (hcint : IntervalIntegrable
      (fun t => gridPair (hN N) (loadCorrection χ (hN N) (e t) (A0 t) (A t)))
        MeasureTheory.volume 0 T) :
    phaseAction χ Λ T e A0 A =
      ∫ t in (0 : ℝ)..T, gridPair (hN N) (nfDensityPh χ Λ (hN N) (e t) (Pidot t) (A0 t) (A t)) := by
  unfold phaseAction
  rw [completedAction_eq_normalForm hN_ne_zero χ Λ T e A0 A Pidot hA hPi hint hdint,
    ← intervalIntegral.integral_add hint hcint]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [gridPair, nfDensityPh_eq, Finset.sum_add_distrib, mul_add]

/-! ### Connection fields in Lorentz coordinates -/

/-- Connection fields in Lorentz coordinates: `A x μ k`, `μ = 0` temporal, `μ = i.succ` the
spatial direction `i`, `k` the `𝔰𝔬(1,3)` coordinate. -/
abbrev Conn (N : ℕ) := Site N → Fin 4 → Fin 6 → ℝ

/-- The temporal connection `A₀(x) = ι(A x 0)`. -/
def toA0 (A : Conn N) : Site N → M4 := fun x => iota (A x 0)

/-- The spatial connection `A_i(x) = ι(A x i.succ)`. -/
def toA (A : Conn N) : Fin 3 → Site N → M4 := fun i x => iota (A x i.succ)

/-- The instantaneous phase-compatible Lagrangian (`h = 1/N`):
`L°(e, ∂_tΠ; A) = ⟨-2χΛ det e + f°_h·A + q_e(A) + r_h(e, A), 1⟩_h`. -/
def phaseLagr (χ Λ : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (A : Conn N) : ℝ :=
  gridPair (hN N) (nfDensityPh χ Λ (hN N) e Pidot (toA0 A) (toA A))

/-! ### The Cartan operator -/

/-- Temporal component of the Cartan operator: `Σ_i [A_i, Π_i]`. -/
def cart0 (χ : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (x : Site N) : M4 :=
  ∑ i, bracket (A i x) (piArr χ (e x) i)

/-- Spatial component of the Cartan operator: `[Π_i, A₀] + Σ_j [A_j, Σ_ij]`. -/
def cartSp (χ : ℝ) (e A0 : Site N → M4) (A : Fin 3 → Site N → M4) (i : Fin 3) (x : Site N) :
    M4 :=
  bracket (piArr χ (e x) i) (A0 x) + ∑ j, bracket (A j x) (sigmaArr χ (e x) i j)

/-- The Cartan operator `C(e)` on coordinate connection fields: the `b`-gradient of the Cartan
quadratic form `q_e`. -/
def cartanOp (χ : ℝ) (e : Site N → M4) (A : Conn N) : Conn N :=
  fun x μ => Fin.cases (coord (cart0 χ e (toA0 A) (toA A) x))
    (fun i => coord (cartSp χ e (toA0 A) (toA A) i x)) μ

/-- The local coordinate pairing `⟨u, v⟩_b = Σ_μ Σ_k g_k u_{μk} v_{μk}` at a site. -/
def bdot (u v : Fin 4 → Fin 6 → ℝ) : ℝ := ∑ μ, ∑ k, gram k * u μ k * v μ k

theorem bracket_add_left (X X' Y : M4) : bracket (X + X') Y = bracket X Y + bracket X' Y := by
  simp [bracket, add_mul, mul_add]; abel

theorem bracket_add_right (X Y Y' : M4) : bracket X (Y + Y') = bracket X Y + bracket X Y' := by
  simp [bracket, add_mul, mul_add]; abel

/-- Invariance in the form used for gradients: `b(P, [X, Y]) = b([Y, P], X)`. -/
theorem pairing_bracket_left (P X Y : M4) : pairing P (bracket X Y) = pairing (bracket Y P) X := by
  unfold pairing bracket
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, ← Matrix.mul_assoc P X Y,
    ← Matrix.mul_assoc P Y X, Matrix.trace_mul_cycle P X Y]

/-- Invariance: `b(P, [X, Y]) = b([P, X], Y)`. -/
theorem pairing_bracket_right (P X Y : M4) : pairing P (bracket X Y) = pairing (bracket P X) Y :=
  pairing_bracket P X Y

theorem toA0_add (A B : Conn N) (x : Site N) : toA0 (A + B) x = toA0 A x + toA0 B x := by
  simp [toA0, ← iota_add]

theorem toA_add (A B : Conn N) (i : Fin 3) (x : Site N) :
    toA (A + B) i x = toA A i x + toA B i x := by
  simp [toA, ← iota_add]

theorem bdot_cartanOp (χ : ℝ) (e : Site N → M4) (A δ : Conn N) (x : Site N) :
    bdot (cartanOp χ e A x) (δ x) =
      pairing (cart0 χ e (toA0 A) (toA A) x) (toA0 δ x) +
        ∑ i, pairing (cartSp χ e (toA0 A) (toA A) i x) (toA δ i x) := by
  unfold bdot
  rw [Fin.sum_univ_succ]
  congr 1
  · simp only [cartanOp, Fin.cases_zero, toA0, pairing_iota]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cartanOp, Fin.cases_succ, toA, pairing_iota]

theorem bracket_neg_left (X Y : M4) : bracket (-X) Y = -bracket X Y := by
  simp [bracket]; abel

theorem bracket_neg_right (X Y : M4) : bracket X (-Y) = -bracket X Y := by
  simp [bracket]; abel

theorem bracket_zero_right (X : M4) : bracket X 0 = 0 := by simp [bracket]

theorem pairing_bracket_pi_left (χ : ℝ) (E X Y : M4) (i : Fin 3) :
    pairing (bracket X (piArr χ E i)) Y = pairing (piArr χ E i) (bracket Y X) :=
  (pairing_bracket_left _ _ _).symm

theorem pairing_bracket_pi_right (χ : ℝ) (E X Y : M4) (i : Fin 3) :
    pairing (bracket (piArr χ E i) X) Y = pairing (piArr χ E i) (bracket X Y) :=
  (pairing_bracket_right _ _ _).symm

theorem pairing_bracket_sigma_left (χ : ℝ) (E X Y : M4) (i j : Fin 3) :
    pairing (bracket X (sigmaArr χ E i j)) Y = pairing (sigmaArr χ E i j) (bracket Y X) :=
  (pairing_bracket_left _ _ _).symm

/-- **Exact polarization of the Cartan form**: `q(A + δ) = q(A) + ⟨C(e)A, δ⟩_b + q(δ)`. -/
theorem qc_add (χ : ℝ) (e : Site N → M4) (A δ : Conn N) (x : Site N) :
    qc χ e (toA0 (A + δ)) (toA (A + δ)) x =
      qc χ e (toA0 A) (toA A) x + bdot (cartanOp χ e A x) (δ x) + qc χ e (toA0 δ) (toA δ) x := by
  have hsw : ∀ i j : Fin 3, bracket (toA A i x) (toA δ j x) = -bracket (toA δ j x) (toA A i x) := by
    intro i j; simp [bracket]
  have hs10 := sigmaArr_swap χ (e x) 0 1
  have hs20 := sigmaArr_swap χ (e x) 0 2
  have hs21 := sigmaArr_swap χ (e x) 1 2
  rw [bdot_cartanOp]
  unfold qc cart0 cartSp
  simp only [toA0_add, toA_add, bracket_add_left, bracket_add_right, pairing_add_right,
    pairing_add_left, pairing_sum_left, Finset.sum_add_distrib, sumLt_eq, Fin.sum_univ_three,
    pairing_bracket_pi_left, pairing_bracket_pi_right, pairing_bracket_sigma_left, hs10, hs20,
    hs21, sigmaArr_diag, bracket_zero_right, pairing_zero_left, pairing_neg_left, hsw,
    pairing_neg_right]
  ring

theorem toA0_smul (c : ℝ) (A : Conn N) (x : Site N) : toA0 (c • A) x = c • toA0 A x := by
  simp [toA0, ← iota_smul]

theorem toA_smul (c : ℝ) (A : Conn N) (i : Fin 3) (x : Site N) :
    toA (c • A) i x = c • toA A i x := by
  simp [toA, ← iota_smul]

theorem bracket_smul_left (c : ℝ) (X Y : M4) : bracket (c • X) Y = c • bracket X Y := by
  simp [bracket, smul_sub]

theorem bracket_smul_right (c : ℝ) (X Y : M4) : bracket X (c • Y) = c • bracket X Y := by
  simp [bracket, smul_sub]

theorem qc_smul (χ : ℝ) (e : Site N → M4) (c : ℝ) (A : Conn N) (x : Site N) :
    qc χ e (toA0 (c • A)) (toA (c • A)) x = c ^ 2 * qc χ e (toA0 A) (toA A) x := by
  unfold qc
  simp only [toA0_smul, toA_smul, bracket_smul_left, bracket_smul_right, pairing_smul_right,
    sumLt_eq, Fin.sum_univ_three]
  ring

/-- `q_e(A) = ½⟨A, C(e)A⟩_b`: the Cartan form is `½ AᵀC(e)A` (`eq:supp-exact-connection-normal-form`). -/
theorem qc_eq_half (χ : ℝ) (e : Site N → M4) (A : Conn N) (x : Site N) :
    qc χ e (toA0 A) (toA A) x = (1 / 2 : ℝ) * bdot (cartanOp χ e A x) (A x) := by
  have h1 := qc_add χ e A A x
  have h2 := qc_smul χ e 2 A x
  rw [two_smul] at h2
  rw [h2] at h1
  linarith

end RenewalGeometry.ExactPhaseAction
