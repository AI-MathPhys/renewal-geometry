/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactQuadraticHamiltonian

/-!
# Constant-shift covariance of the phase-compatible action
  (`eq:supp-exact-ward-objects`, `eq:supp-exact-harmonic-mass-column`: the constant-shift structure
  behind `P_{c,1} = 0`, `P_{c,2}(U, p) = ⟨p, δ_c U⟩`; emergent-spacetime manuscript)

A constant shift `β ↦ β + c` changes the canonical ADM coframe only in its time column:
`e⁰₀ = N`, `eᵃ₀ = E_{aj}(β^j + c^j)`, i.e. `e ↦ e S_c` with `(e S_c)_μ = e_μ + δ_{μ0} c^k e_k`
(`shiftCo`, `admCoframe_add_shift`).  This file proves the exact algebra of this substitution:

* `palCoeff_shiftCo`, `piArr_shiftCo`, `sigmaArr_shiftCo`: `Π_i(e S_c) = Π_i(e)` and
  `Σ_ij(e S_c) = Σ_ij(e) + c_j Π_i(e) - c_i Π_j(e)` (permutation-symbol identities);
  `sigmaArr_lapseCo`: a lapse `N` multiplies `Σ_ij` (`palCoeff` is linear in the time column).
* `nfDensityPh_shift` (**exact**): the phase-compatible density at the shifted coframe is affine in
  the shift, `L°(e S_{tc}) = L°(e) + t · shiftDen`;
  `nfDensityPh_a0shift`: the density is affine in `A₀`, here along `A₀ ↦ A₀ - s c^jA_j`;
  `shiftDen_eq` (**the constant-shift identity**): `shiftDen = -a0Den + ⟨δ_cΠ, A⟩ + vDen`, where
  `a0Den` is the `A₀`-slope (it vanishes at a stationary connection) and `vDen` collects the two
  link-remainder terms only (`ρ^B` against `c_jΠ_i - c_iΠ_j` and `ρ^E` against `Π_i`).

The grid form (`phaseLagr_shift`, `phaseLagr_a0shift`, `shiftLagr_eq`) is used in
`ExactShiftWardEnvelope.lean` to identify the constant-shift row `P_c = ∂_λ𝓗_h[(0, c)]` of the
literal canonical Hamiltonian.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.ShiftWard

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra OddPhaseDerivativeReal QuadJet

/-! ### The shifted and lapsed coframes -/

/-- The coframe with time column `e_0 + c^k e_k` (`e S_c`, `S_c` the constant-shift matrix). -/
def shiftCo (e : M4) (c : Fin 3 → ℝ) : M4 :=
  Matrix.of fun I μ => e I μ + if μ = 0 then ∑ k, c k * e I k.succ else 0

/-- The coframe with time column `n e_0`. -/
def lapseCo (e : M4) (n : ℝ) : M4 := Matrix.of fun I μ => if μ = 0 then n * e I 0 else e I μ

/-- A constant shift of the canonical ADM coframe is the substitution `e ↦ e S_c`. -/
theorem admCoframe_add_shift (E : Fin 3 → Fin 3 → ℝ) (n : ℝ) (β c : Fin 3 → ℝ) :
    admCoframe E n (β + c) = shiftCo (admCoframe E n β) c := by
  ext I μ
  cases I using Fin.cases with
  | zero => cases μ using Fin.cases with
    | zero => simp [shiftCo]
    | succ j => simp [shiftCo]
  | succ a => cases μ using Fin.cases with
    | zero =>
      simp only [shiftCo, Matrix.of_apply, admCoframe_succ_zero, admCoframe_succ_succ,         Pi.add_apply, mul_add, Finset.sum_add_distrib, ite_true]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    | succ j => simp [shiftCo, Fin.succ_ne_zero]

/-- The unit-triad, zero-shift ADM coframe is the lapsed unit coframe. -/
theorem admCoframe_one_lapse (n : ℝ) :
    admCoframe (1 : Matrix (Fin 3) (Fin 3) ℝ) n 0 = lapseCo 1 n := by
  ext I μ
  cases I using Fin.cases with
  | zero => cases μ using Fin.cases with
    | zero => simp [lapseCo, admCoframe]
    | succ j =>
      simp [lapseCo, admCoframe, Matrix.one_apply]
      exact fun h => Fin.succ_ne_zero j h.symm
  | succ a => cases μ using Fin.cases with
    | zero => simp [lapseCo, admCoframe, Matrix.one_apply]
    | succ j => simp [lapseCo, admCoframe, Fin.succ_ne_zero, Matrix.one_apply, Fin.succ_inj]

/-! ### Permutation-symbol identities -/

/-- `T(a, b)_{ρσ} = Σ_{μν} ε^{μνρσ} a_μ b_ν`. -/
def epsT (a b : Fin 4 → ℝ) (ρ σ : Fin 4) : ℝ := ∑ μ, ∑ ν, epsR μ ν ρ σ * (a μ * b ν)

/-- The shifted vector `a_μ + δ_{μ0} c^k a_{k+1}`. -/
def shiftVec (a : Fin 4 → ℝ) (c : Fin 3 → ℝ) : Fin 4 → ℝ :=
  fun μ => a μ + if μ = 0 then ∑ k, c k * a k.succ else 0

/-- The lapsed vector `(n a_0, a_1, a_2, a_3)`. -/
def lapseVec (a : Fin 4 → ℝ) (n : ℝ) : Fin 4 → ℝ := fun μ => if μ = 0 then n * a 0 else a μ

theorem epsT_shift_spatial (c : Fin 3 → ℝ) (i j : Fin 3) (a b : Fin 4 → ℝ) :
    epsT (shiftVec a c) (shiftVec b c) i.succ j.succ =
      epsT a b i.succ j.succ + c j * epsT a b 0 i.succ - c i * epsT a b 0 j.succ := by
  fin_cases i <;> fin_cases j <;>
    simp [epsT, shiftVec, Fin.sum_univ_four, Fin.sum_univ_three, epsR, eps4] <;> ring

theorem epsT_shift_time (c : Fin 3 → ℝ) (i : Fin 3) (a b : Fin 4 → ℝ) :
    epsT (shiftVec a c) (shiftVec b c) 0 i.succ = epsT a b 0 i.succ := by
  fin_cases i <;>
    simp [epsT, shiftVec, Fin.sum_univ_four, Fin.sum_univ_three, epsR, eps4]

theorem epsT_lapse_spatial (n : ℝ) (i j : Fin 3) (a b : Fin 4 → ℝ) :
    epsT (lapseVec a n) (lapseVec b n) i.succ j.succ = n * epsT a b i.succ j.succ := by
  fin_cases i <;> fin_cases j <;>
    simp [epsT, lapseVec, Fin.sum_univ_four, epsR, eps4] <;> ring

theorem sum4_comm (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem epsT_lapse_time (n : ℝ) (i : Fin 3) (a b : Fin 4 → ℝ) :
    epsT (lapseVec a n) (lapseVec b n) 0 i.succ = epsT a b 0 i.succ := by
  fin_cases i <;> simp [epsT, lapseVec, Fin.sum_univ_four, epsR, eps4]

/-- `W_{ρσ}^{KL} = ½ Σ_{IJ} ε_{IJKL} T(e^I, e^J)_{ρσ}`. -/
theorem palCoeff_eq_epsT (e : M4) (ρ σ K L : Fin 4) :
    palCoeff e ρ σ K L = (1 / 2 : ℝ) * ∑ I, ∑ J, epsR I J K L * epsT (e I) (e J) ρ σ := by
  simp only [palCoeff, Matrix.of_apply, epsT, Finset.mul_sum]
  rw [sum4_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

theorem shiftCo_row (e : M4) (c : Fin 3 → ℝ) (I : Fin 4) : shiftCo e c I = shiftVec (e I) c := rfl

theorem lapseCo_row (e : M4) (n : ℝ) (I : Fin 4) : lapseCo e n I = lapseVec (e I) n := rfl

/-- **Shift covariance of the spatial coefficient bivectors**:
`W_{ij}(e S_c) = W_{ij}(e) + c_j W_{0i}(e) - c_i W_{0j}(e)`. -/
theorem palCoeff_shiftCo (e : M4) (c : Fin 3 → ℝ) (i j : Fin 3) :
    palCoeff (shiftCo e c) i.succ j.succ =
      palCoeff e i.succ j.succ + c j • palCoeff e 0 i.succ - c i • palCoeff e 0 j.succ := by
  ext K L
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    palCoeff_eq_epsT, shiftCo_row, epsT_shift_spatial, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring
  · refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring

/-- The time-space coefficient bivectors are shift invariant. -/
theorem palCoeff_shiftCo_time (e : M4) (c : Fin 3 → ℝ) (i : Fin 3) :
    palCoeff (shiftCo e c) 0 i.succ = palCoeff e 0 i.succ := by
  ext K L
  simp only [palCoeff_eq_epsT, shiftCo_row, epsT_shift_time]

/-- The spatial coefficient bivectors are linear in the time column. -/
theorem palCoeff_lapseCo (e : M4) (n : ℝ) (i j : Fin 3) :
    palCoeff (lapseCo e n) i.succ j.succ = n • palCoeff e i.succ j.succ := by
  ext K L
  simp only [Matrix.smul_apply, smul_eq_mul, palCoeff_eq_epsT, lapseCo_row, epsT_lapse_spatial,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring

/-- The time-space coefficient bivectors do not see the lapse. -/
theorem palCoeff_lapseCo_time (e : M4) (n : ℝ) (i : Fin 3) :
    palCoeff (lapseCo e n) 0 i.succ = palCoeff e 0 i.succ := by
  ext K L
  simp only [palCoeff_eq_epsT, lapseCo_row, epsT_lapse_time]

theorem dualCoeff_add (W W' : M4) : dualCoeff (W + W') = dualCoeff W + dualCoeff W' := by
  simp [dualCoeff, Matrix.transpose_add, Matrix.mul_add]

theorem dualCoeff_sub (W W' : M4) : dualCoeff (W - W') = dualCoeff W - dualCoeff W' := by
  simp [dualCoeff, Matrix.transpose_sub, Matrix.mul_sub]

theorem dualCoeff_smul (c : ℝ) (W : M4) : dualCoeff (c • W) = c • dualCoeff W := by
  simp [dualCoeff, Matrix.transpose_smul]

/-- `Π_i(e S_c) = Π_i(e)`. -/
theorem piArr_shiftCo (χ : ℝ) (e : M4) (c : Fin 3 → ℝ) (i : Fin 3) :
    piArr χ (shiftCo e c) i = piArr χ e i := by
  simp only [piArr, palCoeff_shiftCo_time]

/-- **`Σ_ij(e S_c) = Σ_ij(e) + c_j Π_i(e) - c_i Π_j(e)`.** -/
theorem sigmaArr_shiftCo (χ : ℝ) (e : M4) (c : Fin 3 → ℝ) (i j : Fin 3) :
    sigmaArr χ (shiftCo e c) i j = sigmaArr χ e i j + c j • piArr χ e i - c i • piArr χ e j := by
  simp only [sigmaArr, piArr, palCoeff_shiftCo, dualCoeff_add, dualCoeff_sub, dualCoeff_smul,
    smul_add, smul_sub, smul_comm χ (c _)]

/-- `Π_i(lapse n · e) = Π_i(e)`. -/
theorem piArr_lapseCo (χ : ℝ) (e : M4) (n : ℝ) (i : Fin 3) :
    piArr χ (lapseCo e n) i = piArr χ e i := by
  simp only [piArr, palCoeff_lapseCo_time]

/-- `Σ_ij(lapse n · e) = n Σ_ij(e)`. -/
theorem sigmaArr_lapseCo (χ : ℝ) (e : M4) (n : ℝ) (i j : Fin 3) :
    sigmaArr χ (lapseCo e n) i j = n • sigmaArr χ e i j := by
  simp only [sigmaArr, palCoeff_lapseCo, dualCoeff_smul, smul_comm χ n]

/-! ### The phase-compatible density under a constant shift -/

variable {N : ℕ} [NeZero N]

/-- `(δ_cΠ)_i(x) = Σ_j c_j δ_jΠ_i(x)`. -/
def dcPi (χ : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ) (i : Fin 3) (x : Site N) : M4 :=
  ∑ j, c j • pd j (fun y => piArr χ (e y) i) x

/-- `(c·A)(x) = Σ_j c_j A_j(x)`. -/
def cA (c : Fin 3 → ℝ) (A : Fin 3 → Site N → M4) (x : Site N) : M4 := ∑ j, c j • A j x

/-- The shift slope of the density: `L°(e S_{tc}) - L°(e) = t · shiftDen`. -/
def shiftDen (χ h : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ) (A : Fin 3 → Site N → M4)
    (x : Site N) : ℝ :=
  (∑ i, pairing (dcPi χ e c i x - c i • load0Ph χ e x) (A i x)) +
    sumLt fun i j => pairing (c j • piArr χ (e x) i - c i • piArr χ (e x) j)
      (bracket (A i x) (A j x) + remB h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x))

/-- The `A₀`-slope of the density along `A₀ ↦ A₀ - s c^jA_j`. -/
def a0Den (χ h : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ) (A : Fin 3 → Site N → M4)
    (x : Site N) : ℝ :=
  pairing (load0Ph χ e x) (cA c A x) +
    (∑ i, pairing (piArr χ (e x) i) (bracket (cA c A x) (A i x))) -
    ∑ i, pairing (piArr χ (e x) i) (remE h (A i x) (cA c A (x + unitVec i)))

/-- The link-remainder part of the shift slope. -/
def vDen (χ h : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ) (A : Fin 3 → Site N → M4)
    (x : Site N) : ℝ :=
  (sumLt fun i j => pairing (c j • piArr χ (e x) i - c i • piArr χ (e x) j)
      (remB h (A i x) (A j (x + unitVec i)) (A i (x + unitVec j)) (A j x))) -
    ∑ i, pairing (piArr χ (e x) i) (remE h (A i x) (cA c A (x + unitVec i)))

theorem pd_field_lin (j : Fin 3) (F G K : Site N → M4) (a b : ℝ) (x : Site N) :
    pd j (fun y => F y + a • G y - b • K y) x = pd j F x + a • pd j G x - b • pd j K x := by
  have h : (fun y => F y + a • G y - b • K y) = F + a • G - b • K := rfl
  rw [h, map_sub, map_add, map_smul, map_smul]
  rfl

theorem remE_sub_smul (h : ℝ) (a b b' : M4) (s : ℝ) :
    remE h a (b - s • b') = remE h a b - s • remE h a b' := by
  unfold remE bracket
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
    smul_smul, mul_comm h s]
  module

theorem bracket_self (X : M4) : bracket X X = 0 := by simp [bracket]

theorem bracket_swap (X Y : M4) : bracket Y X = -bracket X Y := by simp [bracket]

theorem bracket_sum_left (c : Fin 3 → ℝ) (X : Fin 3 → M4) (Y : M4) :
    bracket (∑ j, c j • X j) Y = ∑ j, c j • bracket (X j) Y := by
  simp only [bracket, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← Finset.sum_sub_distrib, smul_sub]

theorem bracket_sub_left (X X' Y : M4) : bracket (X - X') Y = bracket X Y - bracket X' Y := by
  simp only [bracket, Matrix.sub_mul, Matrix.mul_sub]; abel

theorem bracket_sub_right (X Y Y' : M4) : bracket X (Y - Y') = bracket X Y - bracket X Y' := by
  simp only [bracket, Matrix.sub_mul, Matrix.mul_sub]; abel

/-- **The density at the shifted coframe is affine in the shift** (`Λ = 0`). -/
theorem nfDensityPh_shift (χ h t : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    (A0 : Site N → M4) (A : Fin 3 → Site N → M4) (c : Fin 3 → ℝ) (x : Site N) :
    nfDensityPh χ 0 h (fun y => shiftCo (e y) (t • c)) P A0 A x =
      nfDensityPh χ 0 h e P A0 A x + t * shiftDen χ h e c A x := by
  have hl0 : load0Ph χ (fun y => shiftCo (e y) (t • c)) x = load0Ph χ e x := by
    simp only [load0Ph, piArr_shiftCo]
  have hls : ∀ i, loadSpPh χ (fun y => shiftCo (e y) (t • c)) i x =
      loadSpPh χ e i x + t • (dcPi χ e c i x - c i • load0Ph χ e x) := by
    intro i
    simp only [loadSpPh, sigmaArr_shiftCo, Pi.smul_apply, smul_eq_mul]
    simp only [pd_field_lin, dcPi, load0Ph, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.smul_sum, smul_sub, smul_smul, neg_sub]
    abel
  unfold nfDensityPh qc remDensity
  rw [hl0]
  simp only [hls, piArr_shiftCo, sigmaArr_shiftCo, Pi.smul_apply, smul_eq_mul]
  unfold shiftDen
  simp only [sumLt_eq, Fin.sum_univ_three, pairing_add_left, pairing_sub_left, pairing_smul_left,
    pairing_add_right]
  ring

/-- **The density is affine in `A₀`**: along `A₀ ↦ A₀ - s c^jA_j` its slope is `-a0Den`. -/
theorem nfDensityPh_a0shift (χ h s : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4)
    (A0 : Site N → M4) (A : Fin 3 → Site N → M4) (c : Fin 3 → ℝ) (x : Site N) :
    nfDensityPh χ 0 h e P (fun y => A0 y - s • cA c A y) A x =
      nfDensityPh χ 0 h e P A0 A x - s * a0Den χ h e c A x := by
  unfold nfDensityPh qc remDensity a0Den
  simp only [remE_sub_smul, bracket_sub_left, bracket_smul_left, pairing_sub_right,
    pairing_smul_right, Finset.sum_sub_distrib, Fin.sum_univ_three]
  ring

/-- **The constant-shift identity**: `shiftDen = -a0Den + Σ_i b(δ_cΠ_i, A_i) + vDen`. -/
theorem shiftDen_eq (χ h : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ) (A : Fin 3 → Site N → M4)
    (x : Site N) :
    shiftDen χ h e c A x = -a0Den χ h e c A x + (∑ i, pairing (dcPi χ e c i x) (A i x)) +
      vDen χ h e c A x := by
  unfold shiftDen a0Den vDen cA
  simp only [bracket_sum_left, pairing_sum_right, pairing_smul_right]
  simp only [pairing_add_right, pairing_sub_left, pairing_smul_left, sumLt_eq, Fin.sum_univ_three,
    bracket_self, pairing_zero_right]
  rw [bracket_swap (A 1 x) (A 0 x), bracket_swap (A 2 x) (A 0 x), bracket_swap (A 2 x) (A 1 x)]
  simp only [pairing_neg_right]
  ring

/-! ### Grid form -/

/-- The connection direction `A₀ ↦ (c·A)`, `A_i ↦ 0`. -/
def shiftConn (c : Fin 3 → ℝ) (A : Conn N) : Conn N :=
  fun x μ => Fin.cases (motive := fun _ => Fin 6 → ℝ) (∑ j, c j • A x j.succ) (fun _ => 0) μ

theorem toA0_sub_shiftConn (c : Fin 3 → ℝ) (A : Conn N) (s : ℝ) :
    toA0 (A - s • shiftConn c A) = fun y => toA0 A y - s • cA c (toA A) y := by
  funext y
  simp only [toA0, toA, cA, shiftConn, Pi.sub_apply, Pi.smul_apply, Fin.cases_zero]
  have h1 : iotaLin (A y 0 - s • ∑ j, c j • A y j.succ) =
      iotaLin (A y 0) - s • ∑ j, c j • iotaLin (A y j.succ) := by
    rw [map_sub, map_smul, map_sum]
    simp only [map_smul]
  exact h1

theorem toA_sub_shiftConn (c : Fin 3 → ℝ) (A : Conn N) (s : ℝ) :
    toA (A - s • shiftConn c A) = toA A := by
  funext i y
  simp [toA, shiftConn]

theorem gridPair_add' (h : ℝ) (f g : Site N → ℝ) :
    gridPair h (fun x => f x + g x) = gridPair h f + gridPair h g := by
  simp [gridPair, Finset.sum_add_distrib, mul_add]

/-- **Grid form of the shift identity.** -/
theorem phaseLagr_shift (χ t : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4) (A : Conn N)
    (c : Fin 3 → ℝ) :
    phaseLagr χ 0 (fun y => shiftCo (e y) (t • c)) P A =
      phaseLagr χ 0 e P A + t * gridPair (hN N) (shiftDen χ (hN N) e c (toA A)) := by
  unfold phaseLagr gridPair
  simp only [nfDensityPh_shift]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Grid form of the `A₀`-affinity.** -/
theorem phaseLagr_a0shift (χ s : ℝ) (e : Site N → M4) (P : Fin 3 → Site N → M4) (A : Conn N)
    (c : Fin 3 → ℝ) :
    phaseLagr χ 0 e P (A - s • shiftConn c A) =
      phaseLagr χ 0 e P A - s * gridPair (hN N) (a0Den χ (hN N) e c (toA A)) := by
  unfold phaseLagr gridPair
  rw [toA0_sub_shiftConn, toA_sub_shiftConn]
  simp only [nfDensityPh_a0shift]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Grid form of the constant-shift identity.** -/
theorem gridPair_shiftDen (χ h : ℝ) (e : Site N → M4) (c : Fin 3 → ℝ)
    (A : Fin 3 → Site N → M4) :
    gridPair h (shiftDen χ h e c A) = -gridPair h (a0Den χ h e c A) +
      gridPair h (fun x => ∑ i, pairing (dcPi χ e c i x) (A i x)) + gridPair h (vDen χ h e c A) := by
  simp only [gridPair, shiftDen_eq, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_add,
    mul_neg]

/-- **At a stationary connection the `A₀`-slope vanishes**: if the stationary row vanishes at `A`
and `L°` is differentiable there, `⟨a0Den, 1⟩_h = 0`. -/
theorem gridPair_a0Den_eq_zero {χ : ℝ} {e : Site N → M4} {P : Fin 3 → Site N → M4} {A : Conn N}
    (c : Fin 3 → ℝ) (hd : DifferentiableAt ℝ (phaseLagr χ 0 e P) A)
    (hst : statRow χ 0 e P A = 0) :
    gridPair (hN N) (a0Den χ (hN N) e c (toA A)) = 0 := by
  set v : Conn N := -shiftConn c A
  have h1 : HasDerivAt (fun s : ℝ => phaseLagr χ 0 e P (A + s • v)) (fderiv ℝ (phaseLagr χ 0 e P) A v) 0 := by
    have hl : HasDerivAt (fun s : ℝ => A + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add A
    have hd' : HasFDerivAt (phaseLagr χ 0 e P) (fderiv ℝ (phaseLagr χ 0 e P) A)
        (A + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) hl
  have hfun : (fun s : ℝ => phaseLagr χ 0 e P (A + s • v)) = fun s =>
      phaseLagr χ 0 e P A - s * gridPair (hN N) (a0Den χ (hN N) e c (toA A)) := by
    funext s
    rw [← phaseLagr_a0shift]
    congr 1
    simp [v, sub_eq_add_neg, smul_neg]
  rw [hfun] at h1
  have h2 : HasDerivAt (fun s : ℝ => phaseLagr χ 0 e P A - s * gridPair (hN N) (a0Den χ (hN N) e c (toA A)))
      (-gridPair (hN N) (a0Den χ (hN N) e c (toA A))) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (gridPair (hN N) (a0Den χ (hN N) e c (toA A)))).const_sub
      (phaseLagr χ 0 e P A)
  have h3 := h1.unique h2
  rw [QuadJet.fderiv_phaseLagr_conn, hst, map_zero] at h3
  linarith

end RenewalGeometry.ExactPhaseAction.ShiftWard
