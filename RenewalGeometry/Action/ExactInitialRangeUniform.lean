/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusFinal
import RenewalGeometry.Action.ExactActionProvenance

/-!
# `lem:supp-initial-range` on the grid Sobolev spaces, with cutoff-independent radii
  (emergent-spacetime manuscript)

The real-valued version of the range inverse `R_h` of `eq:supp-initial-right-inverse` on
`𝒴^r_h = (H^r_h)^4 → 𝒫^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6`, the mean map `P₀` and the mean-zero
projection `P_⊥ = I - P₀` on `𝒴^r_h`, and the instantiation of the abstract range reduction
(`LyapunovSchmidt.RangeData`) with the actual constraint map `C_h = CHmap` of
`supp_initial_calculus` (`χ = 1`).

* `Dα_re`, `sobSq_re_le`: the grid Sobolev norms do not increase under taking real parts.
* `RH r`: `y ↦ Re R_h(y)`; `norm_RH_le`: `‖R_h‖ ≤ a_r` independently of `N` (from `Rh_bound`).
* `meanG`, `P0L`, `PL`: spatial means and the mean-zero projection; `norm_PL_le` (`‖P_⊥‖ ≤ 2`).
* `L_RH`: `L_h R_h = I` on mean-zero targets; `P0_L`: `P₀ L_h = 0`.
* **`supp_initial_range`**: for odd `N` with `h < h₀`, the data `(L_h, R_h, P_⊥, P₀, 𝒩_h = C_h - L_h)`
  form a `RangeData` whose radii depend only on `N`-independent constants; hence for every
  `z ∈ ker L_h` with `‖z‖ ≤ δ` there is a unique mean-zero `y_h(z)`, `‖y_h(z)‖ ≤ σ`, with
  `P_⊥ C_h(z + R_h y_h(z)) = 0` (`eq:supp-initial-range-zero`), `‖y_h(z)‖ ≤ 2pC‖z‖²`, and the mean
  map `Θ_h(z) = P₀ C_h(z + R_h y_h(z))` vanishes at `0` with zero derivative there and is analytic.
-/

open Filter Finset Metric Set ComplexConjugate
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialRange

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps InitialCalculus InitialConstraintLinearRange
open LatticeTorusPlancherel

variable {N : ℕ} [NeZero N]

/-! ### Real parts and the grid Sobolev norms -/

/-- The real part of a complex array, as a complex array. -/
def reArr (w : Grid N → ℂ) : Grid N → ℂ := fun x => ((w x).re : ℂ)

/-- An endomorphism commuting with taking real parts. -/
def PresRe (T : Module.End ℂ (Grid N → ℂ)) : Prop := ∀ w, T (reArr w) = reArr (T w)

theorem presRe_S (i : Fin 3) : PresRe (PeriodicGridSobolev.S (N := N) i) := fun w => rfl

theorem presRe_one : PresRe (1 : Module.End ℂ (Grid N → ℂ)) := fun w => rfl

theorem PresRe.mul {T T' : Module.End ℂ (Grid N → ℂ)} (h : PresRe T) (h' : PresRe T') :
    PresRe (T * T') := fun w => by rw [Module.End.mul_apply, h', h]; rfl

theorem PresRe.pow {T : Module.End ℂ (Grid N → ℂ)} (h : PresRe T) (n : ℕ) : PresRe (T ^ n) := by
  induction n with
  | zero => exact presRe_one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem presRe_Dp (i : Fin 3) : PresRe (PeriodicGridSobolev.Dp (N := N) i) := by
  intro w
  funext x
  simp only [PeriodicGridSobolev.Dp, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, reArr, S_apply]
  simp [Complex.mul_re]

theorem presRe_Dα (α : Fin 3 → ℕ) : PresRe (PeriodicGridSobolev.Dα (N := N) α) :=
  (((presRe_Dp 0).pow _).mul ((presRe_Dp 1).pow _)).mul ((presRe_Dp 2).pow _)

theorem gridNormSq_reArr_le (w : Grid N → ℂ) : gridNormSq (reArr w) ≤ gridNormSq w := by
  unfold gridNormSq
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => ?_) (by positivity)
  simp only [reArr, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

/-- **Taking real parts does not increase the grid Sobolev norms.** -/
theorem sobSq_re_le (s : ℕ) (w : Grid N → ℂ) : sobSq s (reArr w) ≤ sobSq s w := by
  unfold sobSq
  refine sum_le_sum fun α _ => ?_
  rw [presRe_Dα α w]
  exact gridNormSq_reArr_le _

/-! ### The real range inverse -/

/-- The target space `𝒴^r_h = (H^r_h)^4` (lapse row, three shift rows). -/
abbrev YH (N r : ℕ) := Fin 4 → GridH N r

/-- Complexification of a target. -/
def cplxY {r : ℕ} (y : YH N r) : Tgt N := (GridH.cxv (y 0), fun i => GridH.cxv (y i.succ))

/-- Real part of a data pair, as an element of `𝒫^r_h`. -/
def reX (r : ℕ) (w : Dom N) : XH N r :=
  (fun c => GridH.mk fun x => (w.1 c x).re, fun c => GridH.mk fun x => (w.2 c x).re)

/-- The real range inverse `y ↦ Re R_h(y)`. -/
def RHlin (r : ℕ) : YH N r →ₗ[ℝ] XH N r where
  toFun y := reX r (Rh (cplxY y))
  map_add' y y' := by
    have h : cplxY (y + y') = cplxY y + cplxY y' := by
      ext <;> simp [cplxY, GridH.cxv]
    rw [h, map_add]
    refine Prod.ext (funext fun c => GridH.ext fun x => ?_) (funext fun c => GridH.ext fun x => ?_) <;>
      simp [reX]
  map_smul' t y := by
    have h : cplxY (t • y) = (t : ℂ) • cplxY y := by
      ext <;> simp [cplxY, GridH.cxv]
    rw [h, map_smul]
    refine Prod.ext (funext fun c => GridH.ext fun x => ?_) (funext fun c => GridH.ext fun x => ?_) <;>
      simp [reX, Complex.mul_re]

/-- The real range inverse as a continuous linear map. -/
def RH (r : ℕ) : YH N r →L[ℝ] XH N r := LinearMap.toContinuousLinearMap (RHlin r)

theorem RH_apply (r : ℕ) (y : YH N r) : RH r y = reX r (Rh (cplxY y)) := rfl

theorem sobY_cplxY_le (r : ℕ) (y : YH N r) : sobY r (cplxY y) ≤ 4 * ‖y‖ ^ 2 := by
  unfold sobY cplxY
  have hc : ∀ c : Fin 4, sobSq r (GridH.cxv (y c)) ≤ ‖y‖ ^ 2 := by
    intro c
    have h1 : sobSq r (GridH.cxv (y c)) = ‖y c‖ ^ 2 := by
      rw [GridH.norm_def, sobNorm, Real.sq_sqrt (sobSq_nonneg _ _)]
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm y c) 2
  simp only [Fin.sum_univ_three]
  linarith [hc 0, hc (Fin.succ 0), hc (Fin.succ 1), hc (Fin.succ 2)]

/-- **`‖R_h‖ ≤ a_r` independently of the cutoff.** -/
theorem exists_norm_RH_le (r : ℕ) : ∃ a : ℝ, 0 < a ∧ ∀ (N : ℕ) [NeZero N],
    ‖(RH (N := N) r)‖ ≤ a := by
  obtain ⟨C, hC, hR⟩ := Rh_bound r
  refine ⟨2 * Real.sqrt C + 1, by positivity, fun N _ => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  set w := Rh (cplxY y)
  have hw : sobP r w ≤ C * (4 * ‖y‖ ^ 2) :=
    (hR N (cplxY y)).trans (mul_le_mul_of_nonneg_left (sobY_cplxY_le r y) hC)
  have hsq : Real.sqrt (sobP r w) ≤ 2 * Real.sqrt C * ‖y‖ := by
    calc Real.sqrt (sobP r w) ≤ Real.sqrt (C * (4 * ‖y‖ ^ 2)) := Real.sqrt_le_sqrt hw
      _ = 2 * Real.sqrt C * ‖y‖ := by
          rw [show C * (4 * ‖y‖ ^ 2) = (2 * ‖y‖) ^ 2 * C by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
          ring
  have hP0 : 0 ≤ sobP r w := by
    unfold sobP
    exact add_nonneg (sum_nonneg fun _ _ => sobSq_nonneg _ _) (sum_nonneg fun _ _ => sobSq_nonneg _ _)
  have hcomp : ‖RH (N := N) r y‖ ≤ Real.sqrt (sobP r w) := by
    rw [RH_apply, Prod.norm_def]
    refine max_le ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun c => ?_)
      ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun c => ?_)
    · rw [GridH.norm_def, sobNorm]
      refine Real.sqrt_le_sqrt ?_
      refine (sobSq_re_le (r + 2) (w.1 c)).trans ?_
      unfold sobP
      exact le_add_of_le_of_nonneg (single_le_sum (f := fun a => sobSq (r + 2) (w.1 a))
        (fun _ _ => sobSq_nonneg _ _) (mem_univ c)) (sum_nonneg fun _ _ => sobSq_nonneg _ _)
    · rw [GridH.norm_def, sobNorm]
      refine Real.sqrt_le_sqrt ?_
      refine (sobSq_re_le (r + 1) (w.2 c)).trans ?_
      unfold sobP
      exact le_add_of_nonneg_of_le (sum_nonneg fun _ _ => sobSq_nonneg _ _)
        (single_le_sum (f := fun a => sobSq (r + 1) (w.2 a)) (fun _ _ => sobSq_nonneg _ _)
          (mem_univ c))
  calc ‖RH (N := N) r y‖ ≤ 2 * Real.sqrt C * ‖y‖ := hcomp.trans hsq
    _ ≤ (2 * Real.sqrt C + 1) * ‖y‖ := by nlinarith [norm_nonneg y]

/-! ### Spatial means and the mean-zero projection -/

/-- The spatial mean `h³ Σ_x u(x)` of an array. -/
def meanG {r : ℕ} (u : GridH N r) : ℝ := ((N : ℝ) ^ 3)⁻¹ * ∑ x, GridH.val u x

/-- The mean as a linear map. -/
def meanLin (r : ℕ) : GridH N r →ₗ[ℝ] ℝ where
  toFun := meanG
  map_add' u w := by simp [meanG, sum_add_distrib, mul_add]
  map_smul' t u := by simp [meanG, mul_sum, smul_eq_mul]; ring_nf

theorem dftL_zero_cxv {r : ℕ} (u : GridH N r) : dftL 0 (GridH.cxv u) = (meanG u : ℂ) := by
  simp only [dftL_apply, dft, smul_eq_mul, meanG]
  have h0 : ∀ x : Grid N, latticeChar 0 x = 1 := by
    intro x; rw [latticeChar_comm]; exact latticeChar_zero_right x
  simp only [h0, map_one, one_mul, GridH.cxv]
  push_cast
  ring

theorem meanG_constArr {r : ℕ} (m : ℝ) : meanG (GridH.constArr (N := N) r m) = m := by
  simp only [meanG, GridH.constArr_val, sum_const, card_univ, nsmul_eq_mul]
  rw [card_grid]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp

theorem abs_meanG_le {r : ℕ} (u : GridH N r) : |meanG u| ≤ ‖u‖ := by
  have hN : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)); positivity
  have hcs : (∑ x, GridH.val u x) ^ 2 ≤ (Fintype.card (Grid N) : ℝ) * ∑ x, GridH.val u x ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [card_grid] at hcs
  have hsq : meanG u ^ 2 ≤ ‖u‖ ^ 2 := by
    have h1 : meanG u ^ 2 ≤ gridNormSq (GridH.cxv u) := by
      unfold meanG gridNormSq
      simp only [GridH.cxv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [mul_pow]
      calc ((N : ℝ) ^ 3)⁻¹ ^ 2 * (∑ x, GridH.val u x) ^ 2
          ≤ ((N : ℝ) ^ 3)⁻¹ ^ 2 * ((N : ℝ) ^ 3 * ∑ x, GridH.val u x ^ 2) := by gcongr
        _ = ((N : ℝ) ^ 3)⁻¹ * ∑ x, GridH.val u x ^ 2 := by field_simp
    have h2 : gridNormSq (GridH.cxv u) ≤ ‖u‖ ^ 2 := by
      rw [GridH.norm_def, sobNorm, Real.sq_sqrt (sobSq_nonneg _ _), ← sobSq_zero]
      exact sobSq_mono (Nat.zero_le r) _
    exact h1.trans h2
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |> fun h => abs_le.mpr h

/-- The mean map `P₀ : 𝒴^r_h → ℝ⁴`. -/
def P0L (r : ℕ) : YH N r →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap ((LinearMap.pi fun c => (meanLin (N := N) r).comp
    (LinearMap.proj c)))

theorem P0L_apply (r : ℕ) (y : YH N r) (c : Fin 4) : P0L r y c = meanG (y c) := rfl

/-- The constant arrays of a mean vector. -/
def constL (r : ℕ) : (Fin 4 → ℝ) →L[ℝ] YH N r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m c => GridH.constArr r (m c)
      map_add' := fun m m' => by funext c; exact GridH.ext fun x => rfl
      map_smul' := fun t m => by funext c; exact GridH.ext fun x => rfl }

theorem constL_apply (r : ℕ) (m : Fin 4 → ℝ) (c : Fin 4) : constL (N := N) r m c = GridH.constArr r (m c) :=
  rfl

/-- The mean-zero projection `P_⊥ = I - P₀`. -/
def PL (r : ℕ) : YH N r →L[ℝ] YH N r := ContinuousLinearMap.id ℝ _ - (constL r).comp (P0L r)

theorem PL_apply (r : ℕ) (y : YH N r) (c : Fin 4) :
    PL r y c = y c - GridH.constArr r (meanG (y c)) := rfl

theorem norm_PL_le (r : ℕ) : ‖PL (N := N) r‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun c => ?_
  rw [PL_apply]
  refine (norm_sub_le _ _).trans ?_
  rw [GridH.norm_constArr]
  have h1 := norm_le_pi_norm y c
  have h2 := (abs_meanG_le (y c)).trans h1
  linarith

theorem meanG_sub {r : ℕ} (u w : GridH N r) : meanG (u - w) = meanG u - meanG w :=
  map_sub (meanLin (N := N) r) u w

theorem meanG_PL (r : ℕ) (y : YH N r) (c : Fin 4) : meanG (PL r y c) = 0 := by
  rw [PL_apply, meanG_sub, meanG_constArr, sub_self]

/-! ### The linear constraint map on the real Sobolev spaces -/

/-- The real part of a complex coordinate field, as a metric field. -/
def reM (v : Fin 6 → Grid N → ℂ) : MetF N := fun y c => (v c y).re

/-- The imaginary part of a complex coordinate field, as a metric field. -/
def imM (v : Fin 6 → Grid N → ℂ) : MetF N := fun y c => (v c y).im

theorem decomp_dom (w : Dom N) :
    w = (cplx (reM w.1), cplx (reM w.2)) + Complex.I • (cplx (imM w.1), cplx (imM w.2)) := by
  refine Prod.ext (funext fun c => funext fun x => ?_) (funext fun c => funext fun x => ?_) <;>
    simp only [cplx, reM, imM, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    rw [mul_comm, Complex.re_add_im]

/-- **`L_h` commutes with real parts** (odd `N`). -/
theorem re_Lh (hNo : Odd N) (w : Dom N) :
    (∀ x, R1F (reM w.1) x = ((Lh w).1 x).re) ∧ ∀ a x, divF (reM w.2) x a = ((Lh w).2 a x).re := by
  have h := congrArg Lh (decomp_dom w)
  rw [map_add, map_smul, Lh_cplx hNo, Lh_cplx hNo] at h
  refine ⟨fun x => ?_, fun a x => ?_⟩
  · have := congrArg (fun p => (p.1 x).re) h
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero] at this
    linarith
  · have := congrArg (fun p => (p.2 a x).re) h
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero] at this
    linarith

theorem meanG_R1F_divF (hNo : Odd N) {r : ℕ} (u π : MetF N) :
    meanG (GridH.mk (r := r) (fun x => R1F u x)) = 0 ∧
      ∀ a, meanG (GridH.mk (r := r) (fun x => divF π x a)) = 0 := by
  have h := (mem_meanZero _).mp (Lh_mem_meanZero (cplx u, cplx π))
  rw [Lh_cplx hNo] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun a => ?_⟩
  · have := dftL_zero_cxv (GridH.mk (r := r) (fun x => R1F u x))
    rw [show GridH.cxv (GridH.mk (r := r) (fun x => R1F u x)) = fun x => ((R1F u x : ℝ) : ℂ) from rfl,
      h1] at this
    exact_mod_cast this.symm
  · have := dftL_zero_cxv (GridH.mk (r := r) (fun x => divF π x a))
    rw [show GridH.cxv (GridH.mk (r := r) (fun x => divF π x a)) =
      fun x => ((divF π x a : ℝ) : ℂ) from rfl, h2 a] at this
    exact_mod_cast this.symm

/-- The flat linearization `L_h` (`χ = 1`) on `𝒫^r_h → 𝒴^r_h`, as a function. -/
def LHfun (r : ℕ) (X : XH N r) : YH N r := encY r (fun x => 1 * R1F (metOf X.1) x, divF (metOf X.2))

theorem meanG_LHfun (hNo : Odd N) (r : ℕ) (X : XH N r) (c : Fin 4) : meanG (LHfun r X c) = 0 := by
  obtain ⟨h1, h2⟩ := meanG_R1F_divF (r := r) hNo (metOf X.1) (metOf X.2)
  cases c using Fin.cases with
  | zero =>
    have e : LHfun r X 0 = GridH.mk (r := r) (fun x => R1F (metOf X.1) x) := by
      refine GridH.ext fun x => ?_; simp [LHfun, encY]
    rw [e, h1]
  | succ a =>
    have e : LHfun r X a.succ = GridH.mk (r := r) (fun x => divF (metOf X.2) x a) := by
      refine GridH.ext fun x => ?_; simp [LHfun, encY]
    rw [e, h2 a]

/-- **`L_h R_h = I` on mean-zero targets**, on the real Sobolev spaces. -/
theorem LHfun_RH (hNo : Odd N) (r : ℕ) {y : YH N r} (hy : PL r y = y) : LHfun r (RH r y) = y := by
  have hm : ∀ c, meanG (y c) = 0 := fun c => by rw [← congrFun hy c]; exact meanG_PL r y c
  have hz : cplxY y ∈ meanZero N := by
    rw [mem_meanZero]
    refine ⟨by rw [show (cplxY y).1 = GridH.cxv (y 0) from rfl, dftL_zero_cxv, hm 0]; simp,
      fun i => by rw [show (cplxY y).2 i = GridH.cxv (y i.succ) from rfl, dftL_zero_cxv, hm i.succ]; simp⟩
  set w := Rh (cplxY y)
  have hL : Lh w = cplxY y := Lh_Rh hz
  obtain ⟨h1, h2⟩ := re_Lh hNo w
  have hmet1 : metOf (RH (N := N) r y).1 = reM w.1 := rfl
  have hmet2 : metOf (RH (N := N) r y).2 = reM w.2 := rfl
  funext c
  refine GridH.ext fun x => ?_
  cases c using Fin.cases with
  | zero =>
    simp only [LHfun, encY, Fin.cases_zero, GridH.val_mk, one_mul, hmet1, h1, hL]
    simp [cplxY, GridH.cxv]
  | succ a =>
    simp only [LHfun, encY, Fin.cases_succ, GridH.val_mk, hmet2, h2, hL]
    simp [cplxY, GridH.cxv]

/-! ### `lem:supp-initial-range` -/

theorem constArr_zero {r : ℕ} : GridH.constArr (N := N) r 0 = 0 := GridH.ext fun _ => rfl

/-- **`lem:supp-initial-range` (nonlinear half, with cutoff-independent radii).**  For `r ≥ 2`
there are constants independent of the cutoff (radii `σ, δ` with `radiiOK a 2 C ρ σ δ`) such that
for every odd `N` with `h < h₀` the actual constraint map `C_h = CHmap` (`χ = 1`) of
`supp_initial_calculus`, its linearization `L_h` (`eq:supp-initial-linear-map`), the real range
inverse `R_h` (`eq:supp-initial-right-inverse`), the mean-zero projection `P_⊥` and the mean map
`P₀` form a `LyapunovSchmidt.RangeData`, and:
* for every `z ∈ ker L_h` with `‖z‖ ≤ δ` there is exactly one mean-zero `y` with `‖y‖ ≤ σ` and
  `P_⊥ C_h(z + R_h y) = 0` (`eq:supp-initial-range-zero`);
* the solution `y_h(z)` obeys `‖y_h(z)‖ ≤ 4C‖z‖²` (`y_h(z) = O(‖z‖²)`);
* the mean map `Θ_h(z) = P₀ C_h(z + R_h y_h(z))` has zero constant and linear jets on `ker L_h`
  and is analytic on `ker L_h ∩ B(0, δ)`. -/
theorem supp_initial_range (r : ℕ) (hr : 2 ≤ r) :
    ∃ M ρ' ρ C a h₀ σ δ : ℝ, 0 < δ ∧ LyapunovSchmidt.radiiOK a 2 C ρ σ δ ∧ 0 < h₀ ∧
      ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
        ∃ D : LyapunovSchmidt.RangeData (XH N r) (YH N r) (Fin 4 → ℝ),
          (∀ X, D.L X = LHfun r X) ∧
          (∀ X, D.full X = CHmap hNo 1 r M (aBlock one_ne_zero) ρ' X) ∧
          D.R = RH r ∧ D.P = PL r ∧ D.P0 = P0L r ∧ D.a = a ∧ D.p = 2 ∧ D.C = C ∧ D.ρ = ρ ∧
          (∀ z, D.L z = 0 → ‖z‖ ≤ δ → ∃! y, (PL r y = y ∧ ‖y‖ ≤ σ) ∧
            PL r (CHmap hNo 1 r M (aBlock one_ne_zero) ρ' (z + RH r y)) = 0) ∧
          (∀ z, D.L z = 0 → ‖z‖ ≤ δ → ‖D.sol σ δ z‖ ≤ 2 * 2 * C * ‖z‖ ^ 2) ∧
          D.meanMap σ δ 0 = 0 ∧
          HasFDerivAt (fun z : LinearMap.ker (D.L : XH N r →ₗ[ℝ] YH N r) =>
            D.meanMap σ δ (z : XH N r))
            (0 : LinearMap.ker (D.L : XH N r →ₗ[ℝ] YH N r) →L[ℝ] (Fin 4 → ℝ)) 0 ∧
          (∀ z0 : D.K, ‖(z0 : XH N r)‖ < δ →
            AnalyticAt ℝ (fun z : D.K => D.meanMap σ δ (z : XH N r)) z0) := by
  obtain ⟨M, ρ', ρ, C, h₀, ε, Mk, hρ, hC, hh₀, hε, hall⟩ :=
    supp_initial_calculus (χ := 1) one_ne_zero r hr 0
  obtain ⟨a, ha, hRa⟩ := exists_norm_RH_le r
  obtain ⟨σ, δ, hδ, hrad⟩ := LyapunovSchmidt.exists_radiiOK ha.le (by norm_num : (0 : ℝ) ≤ 2) hC hρ
  refine ⟨M, ρ', ρ, C, a, h₀, σ, δ, hδ, hrad, hh₀, fun N _ hNo hh => ?_⟩
  obtain ⟨hAn, hCH0, hDCH, hTay, -, -⟩ := hall N hNo hh
  set CH := CHmap hNo 1 r M (aBlock one_ne_zero) ρ'
  set L := fderiv ℝ CH 0
  have hLX : ∀ X, L X = LHfun r X := fun X => (hDCH X).trans rfl
  have hmeanL : ∀ X c, meanG (L X c) = 0 := fun X c => by rw [hLX]; exact meanG_LHfun hNo r X c
  let D : LyapunovSchmidt.RangeData (XH N r) (YH N r) (Fin 4 → ℝ) :=
    { L := L
      R := RH r
      P := PL r
      P0 := P0L r
      N := fun X => CH X - L X
      DN := fun X => fderiv ℝ CH X - L
      ρ := ρ
      C := C
      a := a
      p := 2
      hPP := fun w => by
        funext c
        rw [PL_apply (y := PL r w), meanG_PL, constArr_zero, sub_zero]
      hPL := fun x => by
        funext c
        rw [PL_apply, hmeanL, constArr_zero, sub_zero]
      hLR := fun y hy => by rw [hLX]; exact LHfun_RH hNo r hy
      hP0L := fun x => by funext c; exact hmeanL x c
      hsplit := fun w hP hP0 => by
        funext c
        have h1 := congrFun hP c
        have h2 : meanG (w c) = 0 := congrFun hP0 c
        rw [PL_apply, h2, constArr_zero, sub_zero] at h1
        exact h1
      hN := fun x hx => (hAn x hx).differentiableAt.hasFDerivAt.sub L.hasFDerivAt
      hDN := fun x hx => (hTay x hx).2
      hN0 := by simp [hCH0]
      hC := hC
      ha := hRa N
      hp := norm_PL_le r }
  have hfull : ∀ X, D.full X = CH X := fun X => by
    show L X + (CH X - L X) = CH X
    abel
  have hNa : ∀ x ∈ ball (0 : XH N r) D.ρ, AnalyticAt ℝ D.N x := fun x hx =>
    (hAn x hx).sub (L.analyticAt x)
  refine ⟨D, hLX, hfull, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun z hz hzδ => ?_,
    fun z hz hzδ => D.norm_sol_le hrad hz hzδ, D.meanMap_zero hrad,
    D.hasFDerivAt_meanMap_zero hrad hδ, fun z0 hz0 => D.analyticAt_meanMap hNa hrad hz0⟩
  have := D.exists_unique_solution hrad hz hzδ
  simpa [LyapunovSchmidt.RangeData.S, hfull] using this

end RenewalGeometry.ExactPhaseAction.InitialRange
