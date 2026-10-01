/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridCommutedRow
import RenewalGeometry.Gravity.OpenWriterEnergyIdentity

/-!
# Real arrays of the open writer and the complex grid Sobolev calculus
  (bridge for `thm:supp-open-energy`; emergent-spacetime manuscript)

The open writer (`OpenWriterEnergy`) acts on real arrays of `(ℤ/N)³`; the uniform Sobolev
calculus (`PeriodicGridSobolev`) is written for complex arrays.  This file transports between them:

* `cx u = (↑) ∘ u` and `cx_Dp`, `cx_Dm`, `cx_D0`, `cx_divArr`, `cx_skewArr`: the real
  differences, divergence flux and skew transport are the complex ones on real data;
* `DαR`, `SαR`: real multi-index differences `D^α` and shifts `S^α`, with `cx_DαR`, `cx_SαR`;
  `SαR_apply` (a shift is a translation of the argument), `hasDerivAt_DαR` (time derivatives
  commute with `D^α`), `Dp_DαR`;
* `gridNormSq_cx`, `abs_inner_le`: the real grid norm and the real Cauchy–Schwarz inequality.
-/

open Finset
open scoped BigOperators

namespace RenewalGeometry.OpenWriterGridBridge

open RootParityConnector LatticeTorusPlancherel

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- Complexification of a real array. -/
def cx (u : Grid N → ℝ) : Grid N → ℂ := fun x => (u x : ℂ)

@[simp] theorem cx_apply (u : Grid N → ℝ) (x : Grid N) : cx u x = (u x : ℂ) := rfl

theorem cx_add (u w : Grid N → ℝ) : cx (u + w) = cx u + cx w := by
  funext x; simp [cx]

theorem cx_sub (u w : Grid N → ℝ) : cx (u - w) = cx u - cx w := by
  funext x; simp [cx]

theorem cx_neg (u : Grid N → ℝ) : cx (-u) = -cx u := by
  funext x; simp [cx]

theorem cx_mul (u w : Grid N → ℝ) : cx (u * w) = cx u * cx w := by
  funext x; simp [cx]

theorem cx_fun_mul (u w : Grid N → ℝ) : cx (fun x => u x * w x) = cx u * cx w := by
  funext x; simp [cx]

theorem cx_smul (r : ℝ) (u : Grid N → ℝ) : cx (r • u) = (r : ℂ) • cx u := by
  funext x; simp [cx]

theorem cx_sum {ι : Type*} (s : Finset ι) (f : ι → Grid N → ℝ) :
    cx (∑ i ∈ s, f i) = ∑ i ∈ s, cx (f i) := by
  funext x; simp [cx, Finset.sum_apply]

theorem cx_const (c : ℝ) : cx (fun _ : Grid N => c) = fun _ => (c : ℂ) := rfl

theorem cx_injective : Function.Injective (cx (N := N)) := by
  intro u w h
  funext x
  have := congrFun h x
  simp only [cx_apply] at this
  exact_mod_cast this

theorem cx_Dp (i : Fin 3) (u : Grid N → ℝ) :
    cx (OpenWriterEnergy.Dp i u) = PeriodicGridSobolev.Dp i (cx u) := by
  funext x
  rw [cx_apply, OpenWriterEnergy.Dp_apply, PeriodicGridSobolev.Dp_apply]
  push_cast; rfl

theorem cx_Dm (i : Fin 3) (u : Grid N → ℝ) :
    cx (OpenWriterEnergy.Dm i u) = PeriodicGridSobolev.Dm i (cx u) := by
  funext x
  rw [cx_apply, OpenWriterEnergy.Dm_apply, PeriodicGridSobolev.Dm_apply]
  push_cast; rfl

theorem cx_D0 (i : Fin 3) (u : Grid N → ℝ) :
    cx (OpenWriterEnergy.D0 i u) = PeriodicGridSobolev.D0 i (cx u) := by
  funext x
  rw [cx_apply, OpenWriterEnergy.D0_apply, PeriodicGridSobolev.D0_apply]
  have h1 := congrFun (cx_Dp i u) x
  have h2 := congrFun (cx_Dm i u) x
  simp only [cx_apply] at h1 h2
  push_cast
  rw [h1, h2]
  ring

theorem cx_divArr (c : Fin 3 → Fin 3 → Grid N → ℝ) (q : Grid N → ℝ) :
    cx (OpenWriterEnergy.divArr c q) = ∑ i, ∑ j,
      PeriodicGridSobolev.Dm i (cx (c i j) * PeriodicGridSobolev.Dp j (cx q)) := by
  have e : OpenWriterEnergy.divArr c q =
      ∑ i, ∑ j, OpenWriterEnergy.Dm i (fun y => c i j y * OpenWriterEnergy.Dp j q y) := by
    funext x; simp [OpenWriterEnergy.divArr, Finset.sum_apply]
  rw [e, cx_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [cx_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [cx_Dm, cx_fun_mul, cx_Dp]

theorem cx_skewArr (b : Fin 3 → Grid N → ℝ) (v : Grid N → ℝ) :
    cx (OpenWriterEnergy.skewArr b v) = ∑ i,
      (cx (b i) * PeriodicGridSobolev.D0 i (cx v) +
        PeriodicGridSobolev.D0 i (cx (b i) * cx v)) := by
  have e : OpenWriterEnergy.skewArr b v = ∑ i, (b i * OpenWriterEnergy.D0 i v +
      OpenWriterEnergy.D0 i (fun y => b i y * v y)) := by
    funext x; simp [OpenWriterEnergy.skewArr, Finset.sum_apply]
  rw [e, cx_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [cx_add, cx_mul, cx_D0, cx_D0, cx_fun_mul]

/-! ### Real multi-index differences and shifts -/

/-- Real multi-index forward difference `D^α` (the complex one on real data). -/
def DαR (α : Fin 3 → ℕ) (u : Grid N → ℝ) : Grid N → ℝ :=
  fun x => (PeriodicGridSobolev.Dα α (cx u) x).re

theorem im_Dp_eq_zero {w : Grid N → ℂ} (hw : ∀ x, (w x).im = 0) (i : Fin 3) (x : Grid N) :
    (PeriodicGridSobolev.Dp i w x).im = 0 := by
  rw [PeriodicGridSobolev.Dp_apply]
  simp [Complex.mul_im, hw]

theorem im_Dp_pow_eq_zero {w : Grid N → ℂ} (hw : ∀ x, (w x).im = 0) (i : Fin 3) (n : ℕ) :
    ∀ x, ((PeriodicGridSobolev.Dp i ^ n) w x).im = 0 := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    intro x
    rw [pow_succ', Module.End.mul_apply]
    exact im_Dp_eq_zero ih i x

theorem im_Dα_eq_zero (α : Fin 3 → ℕ) (u : Grid N → ℝ) (x : Grid N) :
    (PeriodicGridSobolev.Dα α (cx u) x).im = 0 := by
  simp only [PeriodicGridSobolev.Dα, Module.End.mul_apply]
  exact im_Dp_pow_eq_zero (im_Dp_pow_eq_zero (im_Dp_pow_eq_zero (fun x => by simp) _ _) _ _) _ _ x

theorem cx_DαR (α : Fin 3 → ℕ) (u : Grid N → ℝ) :
    cx (DαR α u) = PeriodicGridSobolev.Dα α (cx u) := by
  funext x
  apply Complex.ext
  · simp [DαR]
  · simp [DαR, im_Dα_eq_zero]

theorem DαR_add (α : Fin 3 → ℕ) (u w : Grid N → ℝ) : DαR α (u + w) = DαR α u + DαR α w := by
  apply cx_injective
  rw [cx_add, cx_DαR, cx_DαR, cx_DαR, cx_add, map_add]

theorem Dp_DαR (i : Fin 3) (α : Fin 3 → ℕ) (u : Grid N → ℝ) :
    OpenWriterEnergy.Dp i (DαR α u) = DαR (α + Pi.single i 1) u := by
  apply cx_injective
  rw [cx_Dp, cx_DαR, cx_DαR, PeriodicGridSobolev.Dp_Dα]

/-- `D^α` evaluated at a site, as a continuous linear functional of the real array. -/
def DαRL (α : Fin 3 → ℕ) (x : Grid N) : (Grid N → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => DαR α u x
      map_add' := fun u w => by rw [DαR_add]; rfl
      map_smul' := fun r u => by
        simp only [DαR, RingHom.id_apply, smul_eq_mul]
        rw [cx_smul, map_smul, Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] }

theorem DαRL_apply (α : Fin 3 → ℕ) (x : Grid N) (u : Grid N → ℝ) : DαRL α x u = DαR α u x := rfl

/-- Time derivatives commute with `D^α`. -/
theorem hasDerivAt_DαR {u : ℝ → Grid N → ℝ} {u' : Grid N → ℝ} {t : ℝ}
    (hu : ∀ x, HasDerivAt (fun τ => u τ x) (u' x) t) (α : Fin 3 → ℕ) (x : Grid N) :
    HasDerivAt (fun τ => DαR α (u τ) x) (DαR α u' x) t := by
  have h : HasDerivAt u u' t := hasDerivAt_pi.2 hu
  exact (DαRL α x).hasFDerivAt.comp_hasDerivAt t h

/-- The shift vector `Σ_i α_i e_i`. -/
def svec (α : Fin 3 → ℕ) : Grid N := fun i => ((α i : ℕ) : ZMod N)

/-- Real multi-index shift `(S^α u)(x) = u(x + α)`. -/
def SαR (α : Fin 3 → ℕ) (u : Grid N → ℝ) : Grid N → ℝ := fun x => u (x + svec α)

theorem S_pow_apply (i : Fin 3) (n : ℕ) (w : Grid N → ℂ) (x : Grid N) :
    (PeriodicGridSobolev.S i ^ n) w x = w (x + n • PeriodicGridSobolev.unit i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, PeriodicGridSobolev.S_apply, ih, succ_nsmul, add_assoc,
      add_comm (PeriodicGridSobolev.unit i)]

theorem Sα_apply (α : Fin 3 → ℕ) (w : Grid N → ℂ) (x : Grid N) :
    PeriodicGridSobolev.Sα α w x = w (x + svec α) := by
  simp only [PeriodicGridSobolev.Sα, Module.End.mul_apply, S_pow_apply]
  congr 1
  rw [add_assoc, add_assoc]
  congr 1
  funext i
  fin_cases i <;> simp [svec, PeriodicGridSobolev.unit, nsmul_eq_mul]

theorem cx_SαR (α : Fin 3 → ℕ) (u : Grid N → ℝ) :
    cx (SαR α u) = PeriodicGridSobolev.Sα α (cx u) := by
  funext x; rw [Sα_apply]; rfl

theorem SαR_fun_mul (α : Fin 3 → ℕ) (u w : Grid N → ℝ) :
    SαR α (fun x => u x * w x) = fun x => SαR α u x * SαR α w x := rfl

/-! ### Real grid norms -/

theorem gridNormSq_cx (u : Grid N → ℝ) :
    PeriodicGridSobolev.gridNormSq (cx u) = ((N : ℝ) ^ 3)⁻¹ * ∑ x, u x ^ 2 := by
  unfold PeriodicGridSobolev.gridNormSq
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [cx_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Real Cauchy–Schwarz: `|h³ Σ u w| ≤ ‖u‖_h ‖w‖_h`. -/
theorem abs_inner_le (u w : Grid N → ℝ) :
    |((N : ℝ) ^ 3)⁻¹ * ∑ x, u x * w x| ≤
      PeriodicGridSobolev.gridNorm (cx u) * PeriodicGridSobolev.gridNorm (cx w) := by
  have hN : (0 : ℝ) < ((N : ℝ) ^ 3)⁻¹ := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hcs : |∑ x, u x * w x| ≤ Real.sqrt (∑ x, u x ^ 2) * Real.sqrt (∑ x, w x ^ 2) := by
    rw [abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => -u x) w
      simp only [neg_mul, sum_neg_distrib, neg_sq] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt univ u w
  unfold PeriodicGridSobolev.gridNorm
  rw [gridNormSq_cx, gridNormSq_cx, Real.sqrt_mul hN.le, Real.sqrt_mul hN.le, abs_mul,
    abs_of_pos hN]
  calc ((N : ℝ) ^ 3)⁻¹ * |∑ x, u x * w x|
      ≤ ((N : ℝ) ^ 3)⁻¹ * (Real.sqrt (∑ x, u x ^ 2) * Real.sqrt (∑ x, w x ^ 2)) := by gcongr
    _ = Real.sqrt ((N : ℝ) ^ 3)⁻¹ * Real.sqrt (∑ x, u x ^ 2) *
        (Real.sqrt ((N : ℝ) ^ 3)⁻¹ * Real.sqrt (∑ x, w x ^ 2)) := by
        have key : ∀ k X Y : ℝ, 0 ≤ k → k * (X * Y) = Real.sqrt k * X * (Real.sqrt k * Y) := by
          intro k X Y hk
          have h := Real.mul_self_sqrt hk
          calc k * (X * Y) = (Real.sqrt k * Real.sqrt k) * (X * Y) := by rw [h]
            _ = _ := by ring
        exact key _ _ _ hN.le

end

end RenewalGeometry.OpenWriterGridBridge
