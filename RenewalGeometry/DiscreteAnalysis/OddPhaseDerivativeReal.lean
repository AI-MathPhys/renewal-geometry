/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.InitialConstraintLinearRange
import RenewalGeometry.Action.ExactThreeSiteGrid

/-!
# The real odd-grid phase derivative
  (`eq:supp-exact-phase-compatible-derivative`, `eq:supp-initial-phase-derivative`;
  emergent-spacetime manuscript, supplement)

On the periodic grid `(ℤ/N)³` (`N = 2m + 1`, `h = 1/N`) the odd phase derivative is the Fourier
multiplier `\widehat{δ_i u}(k) = i κ_i(k) û(k)`, `κ_i(k) = 2 h⁻¹ sin(π h k_i)`, `-m ≤ k_i ≤ m`.
Since `κ_i` is odd in `k_i` for odd `N`, `δ_i` is a *real* operator: it is the convolution along
the axis `i` with the explicit real kernel (`kernel`)

  `K(s) = N⁻¹ Σ_{k ∈ ℤ/N} κ(k) sin(2π k̃ s̃ / N)`,  `κ(k) = 2N sin(π k̃ / N)`,

where `k̃ = k.valMinAbs ∈ {-m, …, m}` and `s̃ = s.val ∈ {0, …, N - 1}`.

* `pd i u x = Σ_s K(s) • u(x + s e_i)`: the real phase derivative, defined for fields with
  values in any real vector space `E` (`pd`, `pd_apply`).
* Calculus: `pd_map`, `pd_map_clm`, `pd_pi_apply`, `pd_matrix_apply` (entrywise
  differentiation), `pd_comm` (`[δ_i, δ_j] = 0`), `kernel_neg` (`K` is odd), `sum_kernel`,
  `pd_const`, `pd_of_indep`, and the exact skew-adjointness `pd_skew` against any bilinear
  pairing.
* Faithfulness (odd `N`): `sum_kernel_mul_stdAddChar` (the one-dimensional symbol
  `Σ_s K(s) e(q s) = i κ(q)`), `pd_latticeChar` (eigenvalue `i κ_i(q)` on the character
  `x ↦ e(q·x)`), `pd_eq_delta` and `ofReal_pd` (`pd` agrees with the complex Fourier-multiplier
  encoding `InitialConstraintLinearRange.delta`).
* `pd_three`: at `N = 3`, `pd i = ExactThreeSite.phaseDeriv i = 3 (S_i - S_i⁻¹)`.
* Mode lemmas (odd `N ≥ 3`, `ω_N = 2N sin(π/N)`): `pd_cos`, `pd_sin`, `pd_of_ne`.
-/

open Finset ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.OddPhaseDerivativeReal

open PeriodicGridSobolev LatticeTorusPlancherel

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### The kernel -/

/-- The one-dimensional phase symbol `κ(k) = 2 h⁻¹ sin(π h k̃)`, `k̃ = k.valMinAbs`. -/
noncomputable def kap1 (N : ℕ) (k : ZMod N) : ℝ := 2 * N * Real.sin (π * k.valMinAbs / N)

/-- The real convolution kernel of the odd phase derivative,
`K(s) = N⁻¹ Σ_k κ(k) sin(2π k̃ s̃ / N)` with `κ(k) = 2N sin(π k̃ / N)`. -/
noncomputable def kernel (N : ℕ) [NeZero N] (s : ZMod N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k : ZMod N, (2 * N * Real.sin (π * k.valMinAbs / N)) *
    Real.sin (2 * π * k.valMinAbs * s.val / N)

/-- The kernel written with the symbol `kap1`. -/
theorem kernel_eq_kap1 (s : ZMod N) :
    kernel N s = (N : ℝ)⁻¹ * ∑ k : ZMod N, kap1 N k * Real.sin (2 * π * k.valMinAbs * s.val / N) :=
  rfl

/-- The sine of the kernel as a difference of characters. -/
theorem ofReal_sin_eq (k s : ZMod N) :
    ((Real.sin (2 * π * k.valMinAbs * s.val / N) : ℝ) : ℂ) =
      (ZMod.stdAddChar (k * s) - ZMod.stdAddChar (-(k * s))) / (2 * Complex.I) := by
  have e1 : k * s = (((k.valMinAbs * (s.val : ℤ)) : ℤ) : ZMod N) := by
    push_cast; simp
  have e2 : -(k * s) = (((-(k.valMinAbs * (s.val : ℤ))) : ℤ) : ZMod N) := by
    rw [e1]; push_cast; ring
  rw [e2, e1, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, Complex.ofReal_sin]
  set θ : ℂ := ((2 * π * k.valMinAbs * s.val / N : ℝ) : ℂ) with hθ
  have h1 : 2 * (π : ℂ) * Complex.I * (((k.valMinAbs * (s.val : ℤ)) : ℤ) : ℂ) / N =
      θ * Complex.I := by
    rw [hθ]; push_cast; ring
  have h2 : 2 * (π : ℂ) * Complex.I * (((-(k.valMinAbs * (s.val : ℤ))) : ℤ) : ℂ) / N =
      -(θ * Complex.I) := by
    rw [hθ]; push_cast; ring
  rw [h1, h2, Complex.sin]
  field_simp
  rw [show -(θ * Complex.I) = -θ * Complex.I by ring]
  linear_combination (Complex.exp (-θ * Complex.I) - Complex.exp (θ * Complex.I)) * Complex.I_sq

/-- The complexified kernel, written with characters (valid for every `N`). -/
theorem ofReal_kernel (s : ZMod N) :
    ((kernel N s : ℝ) : ℂ) = (N : ℂ)⁻¹ * ∑ k : ZMod N, (kap1 N k : ℂ) *
      ((ZMod.stdAddChar (k * s) - ZMod.stdAddChar (-(k * s))) / (2 * Complex.I)) := by
  rw [kernel_eq_kap1]
  push_cast
  simp only [← ofReal_sin_eq]
  push_cast
  rfl

/-- **The kernel is odd**: `K(-s) = -K(s)`. -/
theorem kernel_neg (s : ZMod N) : kernel N (-s) = -kernel N s := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, ofReal_kernel, ofReal_kernel, ← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [mul_neg, neg_neg]
  ring

/-- `K(0) = 0`. -/
theorem kernel_zero : kernel N 0 = 0 := by
  have := kernel_neg (N := N) 0
  rw [neg_zero] at this
  linarith

/-- The kernel has zero sum. -/
theorem sum_kernel : ∑ s : ZMod N, kernel N s = 0 := by
  have h : ∑ s : ZMod N, kernel N s = ∑ s : ZMod N, kernel N (-s) :=
    (Equiv.sum_comp (Equiv.neg (ZMod N)) (kernel N)).symm
  simp only [kernel_neg, sum_neg_distrib] at h
  linarith

/-- For odd `N` the symbol is odd: `κ(-k) = -κ(k)`. -/
theorem kap1_neg (hN : Odd N) (k : ZMod N) : kap1 N (-k) = -kap1 N k := by
  have h : 2 * k.val ≠ N := by
    intro h; rw [← h] at hN; exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hN
  rw [kap1, kap1, ZMod.valMinAbs_neg_of_ne_half h]
  push_cast
  rw [mul_neg, neg_div, Real.sin_neg]
  ring

/-- For odd `N` the kernel is the inverse DFT of the symbol `i κ`:
`K(s) = N⁻¹ Σ_k i κ(k) e(-k s)`. -/
theorem ofReal_kernel_eq_inv_dft (hN : Odd N) (s : ZMod N) :
    ((kernel N s : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ k : ZMod N, Complex.I * (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s)) := by
  rw [ofReal_kernel]
  congr 1
  have hre : ∑ k : ZMod N, (kap1 N k : ℂ) * ZMod.stdAddChar (k * s) =
      -∑ k : ZMod N, (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s)) := by
    rw [← Equiv.sum_comp (Equiv.neg (ZMod N)), ← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [Equiv.neg_apply, kap1_neg hN, Complex.ofReal_neg, neg_mul]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have e : ∀ k : ZMod N, (kap1 N k : ℂ) *
      ((ZMod.stdAddChar (k * s) - ZMod.stdAddChar (-(k * s))) / (2 * Complex.I)) =
      ((kap1 N k : ℂ) * ZMod.stdAddChar (k * s) -
        (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s))) / (2 * Complex.I) := fun k => by ring
  have hI' : ∑ k : ZMod N, Complex.I * (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s)) =
      Complex.I * ∑ k : ZMod N, (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s)) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  simp only [e]
  rw [← sum_div, sum_sub_distrib, hre, hI']
  field_simp
  linear_combination (-2 * ∑ k : ZMod N, (kap1 N k : ℂ) * ZMod.stdAddChar (-(k * s))) *
    Complex.I_sq

/-- **The one-dimensional symbol** (odd `N`): `Σ_s K(s) e(q s) = i κ(q)`. -/
theorem sum_kernel_mul_stdAddChar (hN : Odd N) (q : ZMod N) :
    ∑ s : ZMod N, ((kernel N s : ℝ) : ℂ) * ZMod.stdAddChar (q * s) =
      Complex.I * (kap1 N q : ℂ) := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc ∑ s : ZMod N, ((kernel N s : ℝ) : ℂ) * ZMod.stdAddChar (q * s)
      = ∑ s : ZMod N, ∑ k : ZMod N, (N : ℂ)⁻¹ * (Complex.I * (kap1 N k : ℂ)) *
          ZMod.stdAddChar (s * (q - k)) := by
        refine sum_congr rfl fun s _ => ?_
        rw [ofReal_kernel_eq_inv_dft hN, mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [show s * (q - k) = -(k * s) + q * s by ring, AddChar.map_add_eq_mul]
        ring
    _ = ∑ k : ZMod N, (N : ℂ)⁻¹ * (Complex.I * (kap1 N k : ℂ)) *
          ∑ s : ZMod N, ZMod.stdAddChar (s * (q - k)) := by
        rw [sum_comm]; simp only [mul_sum]
    _ = Complex.I * (kap1 N q : ℂ) := by
        simp only [sum_stdAddChar_mul, sub_eq_zero, mul_ite, mul_zero]
        rw [sum_ite_eq]
        simp only [mem_univ, ite_true]
        field_simp

/-! ### The real phase derivative -/

/-- **The real odd phase derivative** `δ_i u(x) = Σ_s K(s) u(x + s e_i)`, for fields with values
in any real vector space. -/
noncomputable def pd (i : Fin 3) {E : Type*} [AddCommGroup E] [Module ℝ E] :
    (Grid N → E) →ₗ[ℝ] (Grid N → E) where
  toFun u x := ∑ s : ZMod N, kernel N s • u (x + Pi.single i s)
  map_add' u v := by
    funext x
    simp [smul_add, sum_add_distrib]
  map_smul' c u := by
    funext x
    simp [smul_sum, smul_comm c]

section Calculus

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]

/-- The defining formula `δ_i u(x) = Σ_s K(s) u(x + s e_i)`. -/
theorem pd_apply (i : Fin 3) (u : Grid N → E) (x : Grid N) :
    pd i u x = ∑ s : ZMod N, kernel N s • u (x + Pi.single i s) := rfl

/-- `δ_i` commutes with every real-linear map applied pointwise. -/
theorem pd_map (i : Fin 3) (f : E →ₗ[ℝ] F) (u : Grid N → E) :
    pd i (fun x => f (u x)) = fun x => f (pd i u x) := by
  funext x
  simp [pd_apply, map_sum, map_smul]

/-- `δ_i` commutes with every continuous real-linear map applied pointwise. -/
theorem pd_map_clm [TopologicalSpace E] [TopologicalSpace F] (i : Fin 3) (f : E →L[ℝ] F)
    (u : Grid N → E) : pd i (fun x => f (u x)) = fun x => f (pd i u x) :=
  pd_map i f.toLinearMap u

/-- Componentwise differentiation of vector-valued fields. -/
theorem pd_pi_apply {ι : Type*} (i : Fin 3) (u : Grid N → ι → E) (x : Grid N) (j : ι) :
    pd i u x j = pd i (fun y => u y j) x := by
  simp [pd_apply, Finset.sum_apply]

/-- Entrywise differentiation of matrix-valued fields. -/
theorem pd_matrix_apply {m n : Type*} (i : Fin 3) (u : Grid N → Matrix m n ℝ) (x : Grid N)
    (a : m) (b : n) : pd i u x a b = pd i (fun y => u y a b) x := by
  simp [pd_apply, Matrix.sum_apply]

/-- **The phase derivatives commute**: `δ_i δ_j = δ_j δ_i`. -/
theorem pd_comm (i j : Fin 3) (u : Grid N → E) : pd i (pd j u) = pd j (pd i u) := by
  funext x
  simp only [pd_apply, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  rw [mul_comm, add_right_comm]

/-- `δ_i` annihilates constants. -/
theorem pd_const (i : Fin 3) (c : E) : pd i (fun _ : Grid N => c) = 0 := by
  funext x
  simp [pd_apply, ← sum_smul, sum_kernel]

/-- `δ_i` annihilates fields independent of the coordinate `x_i`. -/
theorem pd_of_indep (i : Fin 3) (u : Grid N → E) (h : ∀ x s, u (x + Pi.single i s) = u x) :
    pd i u = 0 := by
  funext x
  simp [pd_apply, h, ← sum_smul, sum_kernel]

/-- **Exact skew-adjointness**: `Σ_x B(δ_i u, v) = -Σ_x B(u, δ_i v)` for every bilinear
pairing `B`. -/
theorem pd_skew (i : Fin 3) (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (u : Grid N → E) (v : Grid N → F) :
    ∑ x, B (pd i u x) (v x) = -∑ x, B (u x) (pd i v x) := by
  simp only [pd_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_comm, sum_comm (s := univ) (t := univ) (f := fun x s => kernel N s • B (u x) _)]
  simp only [← smul_sum]
  have hre : ∀ s : ZMod N, ∑ x : Grid N, B (u (x + Pi.single i s)) (v x) =
      ∑ x : Grid N, B (u x) (v (x + Pi.single i (-s))) := by
    intro s
    rw [← Equiv.sum_comp (Equiv.subRight (Pi.single i s : Grid N))]
    refine sum_congr rfl fun x _ => ?_
    simp [Pi.single_neg, sub_eq_add_neg]
  simp only [hre]
  rw [← Equiv.sum_comp (Equiv.neg (ZMod N)), ← sum_neg_distrib]
  refine sum_congr rfl fun s _ => ?_
  simp [kernel_neg]

end Calculus

/-! ### Faithfulness: the Fourier symbol `i κ_i(k)` -/

/-- The three-dimensional symbol `κ_i(q)` of `InitialConstraintLinearRange` is `κ(q_i)`. -/
theorem kap_eq_kap1 (i : Fin 3) (q : Grid N) :
    InitialConstraintLinearRange.kap i q = kap1 N (q i) := by
  simp [InitialConstraintLinearRange.kap, kap1, freq]

/-- The character of an axis vector: `e(q · s e_i) = e(q_i s)`. -/
theorem latticeChar_single_apply (q : Grid N) (i : Fin 3) (s : ZMod N) :
    latticeChar q (Pi.single i s : Grid N) = ZMod.stdAddChar (q i * s) := by
  unfold latticeChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro μ _ hμ
    simp [hμ]
  · intro h
    exact absurd (mem_univ i) h

/-- **Eigenvalue on characters** (odd `N`): `δ_i e_q = i κ_i(q) e_q`. -/
theorem pd_latticeChar (hN : Odd N) (i : Fin 3) (q : Grid N) :
    pd i (fun x => latticeChar q x) =
      fun x => Complex.I * (InitialConstraintLinearRange.kap i q : ℂ) * latticeChar q x := by
  funext x
  rw [pd_apply, kap_eq_kap1, ← sum_kernel_mul_stdAddChar hN, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  rw [latticeChar_add_right, latticeChar_single_apply, Complex.real_smul]
  ring

/-- **Faithfulness** (odd `N`): on complex fields `pd i` is the Fourier multiplier `i κ_i(k)`
of `InitialConstraintLinearRange.delta`. -/
theorem pd_eq_delta (hN : Odd N) (i : Fin 3) (v : Grid N → ℂ) :
    pd i v = InitialConstraintLinearRange.delta i v := by
  funext x
  change _ = ∑ k, latticeChar k x *
    (Complex.I * (InitialConstraintLinearRange.kap i k : ℂ) * dft v k)
  rw [pd_apply]
  have hv : ∀ y, v y = ∑ k, latticeChar k y * dft v k := fun y => (dft_inversion v y).symm
  simp only [hv]
  simp only [smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have h := congrFun (pd_latticeChar hN i k) x
  rw [pd_apply] at h
  have e : ∑ s : ZMod N, kernel N s • (latticeChar k (x + Pi.single i s) * dft v k) =
      (∑ s : ZMod N, kernel N s • latticeChar k (x + Pi.single i s)) * dft v k := by
    rw [sum_mul]
    exact sum_congr rfl fun s _ => (smul_mul_assoc _ _ _).symm
  rw [e, h]
  ring

/-- **Faithfulness for real fields** (odd `N`): the real phase derivative, complexified, is the
Fourier multiplier `InitialConstraintLinearRange.delta`. -/
theorem ofReal_pd (hN : Odd N) (i : Fin 3) (u : Grid N → ℝ) :
    (fun x => ((pd i u x : ℝ) : ℂ)) =
      InitialConstraintLinearRange.delta i (fun x => (u x : ℂ)) := by
  rw [← pd_eq_delta hN]
  funext x
  simp [pd_apply, Complex.real_smul]

/-! ### The three-site grid -/

/-- At `N = 3`, `K(1) = 3`. -/
theorem kernel_three_one : kernel 3 1 = 3 := by
  rw [kernel]
  change (3 : ℝ)⁻¹ * ∑ k : Fin 3, _ = 3
  rw [Fin.sum_univ_three]
  have v0 : @ZMod.valMinAbs 3 (0 : Fin 3) = 0 := by decide
  have v1 : @ZMod.valMinAbs 3 (1 : Fin 3) = 1 := by decide
  have v2 : @ZMod.valMinAbs 3 (2 : Fin 3) = -1 := by decide
  have w1 : (1 : ZMod 3).val = 1 := rfl
  simp only [v0, v1, v2, w1]
  have s1 : Real.sin (π / 3) = √3 / 2 := Real.sin_pi_div_three
  have s2 : Real.sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, s1]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [Nat.cast_ofNat, Int.cast_zero, Int.cast_one, Int.cast_neg, Nat.cast_one, mul_zero,
    zero_div, Real.sin_zero, mul_one, mul_neg, neg_mul, neg_div, Real.sin_neg, s1, s2]
  linear_combination h3

/-- At `N = 3`, `K(2) = K(-1) = -3`. -/
theorem kernel_three_two : kernel 3 2 = -3 := by
  rw [show (2 : ZMod 3) = -1 by decide, kernel_neg, kernel_three_one]

/-- **The three-site case**: at `N = 3`, `δ_i = 3 (S_i - S_i⁻¹)`
(`ExactThreeSite.phaseDeriv`, `eq:supp-exact-phase-derivative`). -/
theorem pd_three (i : Fin 3) (u : ExactThreeSite.Site → ℝ) :
    pd (N := 3) i u = ExactThreeSite.phaseDeriv i u := by
  funext x
  rw [pd_apply, ExactThreeSite.phaseDeriv_apply]
  change ∑ s : Fin 3, kernel 3 s • u (x + Pi.single i s) = _
  rw [Fin.sum_univ_three]
  have k0 : kernel 3 (0 : Fin 3) = 0 := kernel_zero
  have k1 : kernel 3 (1 : Fin 3) = 3 := kernel_three_one
  have k2 : kernel 3 (2 : Fin 3) = -3 := kernel_three_two
  have p1 : x + Pi.single i ((1 : Fin 3) : ZMod 3) = x + ExactThreeSite.unitVec i := rfl
  have p2 : x + Pi.single i ((2 : Fin 3) : ZMod 3) = x - ExactThreeSite.unitVec i := by
    rw [sub_eq_add_neg, ExactThreeSite.unitVec, ← Pi.single_neg]
    congr 2
  rw [k0, k1, k2, p1, p2]
  simp only [smul_eq_mul]
  ring

/-! ### Single-mode lemmas -/

/-- The lowest phase frequency `ω_N = 2N sin(π/N) = κ(1)`. -/
noncomputable def omega (N : ℕ) : ℝ := 2 * N * Real.sin (π / N)

/-- `κ(1) = ω_N` for `N ≥ 3`. -/
theorem kap1_one (h3 : 3 ≤ N) : kap1 N 1 = omega N := by
  have h : (1 : ZMod N).valMinAbs = 1 := by
    have := ZMod.valMinAbs_natCast_of_le_half (n := N) (a := 1) (by omega)
    simpa using this
  simp [kap1, omega, h]

/-- The standard character `e(a) = exp(2π i ã / N)`, `ã = a.val`, in polar form. -/
theorem stdAddChar_eq_exp (a : ZMod N) :
    (ZMod.stdAddChar a : ℂ) = Complex.exp (((2 * π * a.val / N : ℝ) : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- `Re e(a) = cos(2π ã / N)`. -/
theorem re_stdAddChar (a : ZMod N) :
    (ZMod.stdAddChar a : ℂ).re = Real.cos (2 * π * a.val / N) := by
  rw [stdAddChar_eq_exp, Complex.exp_ofReal_mul_I_re]

/-- `Im e(a) = sin(2π ã / N)`. -/
theorem im_stdAddChar (a : ZMod N) :
    (ZMod.stdAddChar a : ℂ).im = Real.sin (2 * π * a.val / N) := by
  rw [stdAddChar_eq_exp, Complex.exp_ofReal_mul_I_im]

/-- The axis character `x ↦ e(x_i)` is an eigenfunction: `δ_i e(x_i) = i ω_N e(x_i)`
(odd `N ≥ 3`). -/
theorem pd_stdAddChar (hN : Odd N) (h3 : 3 ≤ N) (i : Fin 3) :
    pd i (fun x : Grid N => (ZMod.stdAddChar (x i) : ℂ)) =
      fun x => Complex.I * (omega N : ℂ) * ZMod.stdAddChar (x i) := by
  have e : ∀ x : Grid N, (ZMod.stdAddChar (x i) : ℂ) = latticeChar (Pi.single i 1 : Grid N) x :=
    fun x => by rw [latticeChar_comm, latticeChar_single_apply, mul_one]
  simp only [e]
  rw [pd_latticeChar hN, kap_eq_kap1, Pi.single_eq_same, kap1_one h3]

/-- **Cosine mode**: `δ_i cos(2π x_i / N) = -ω_N sin(2π x_i / N)` (odd `N ≥ 3`). -/
theorem pd_cos (hN : Odd N) (h3 : 3 ≤ N) (i : Fin 3) :
    pd i (fun x : Grid N => Real.cos (2 * π * (x i).val / N)) =
      fun x => -(omega N) * Real.sin (2 * π * (x i).val / N) := by
  have h := pd_map i Complex.reLm (fun x : Grid N => (ZMod.stdAddChar (x i) : ℂ))
  rw [pd_stdAddChar hN h3] at h
  simp only [Complex.reLm_coe, re_stdAddChar] at h
  rw [h]
  funext x
  simp [Complex.mul_re, im_stdAddChar]

/-- **Sine mode**: `δ_i sin(2π x_i / N) = ω_N cos(2π x_i / N)` (odd `N ≥ 3`). -/
theorem pd_sin (hN : Odd N) (h3 : 3 ≤ N) (i : Fin 3) :
    pd i (fun x : Grid N => Real.sin (2 * π * (x i).val / N)) =
      fun x => omega N * Real.cos (2 * π * (x i).val / N) := by
  have h := pd_map i Complex.imLm (fun x : Grid N => (ZMod.stdAddChar (x i) : ℂ))
  rw [pd_stdAddChar hN h3] at h
  simp only [Complex.imLm_coe, im_stdAddChar] at h
  rw [h]
  funext x
  simp [Complex.mul_im, re_stdAddChar]

/-- A field depending only on `x_i` is annihilated by `δ_j`, `j ≠ i`. -/
theorem pd_of_ne {E : Type*} [AddCommGroup E] [Module ℝ E] {i j : Fin 3} (hij : j ≠ i)
    (f : ZMod N → E) : pd j (fun x : Grid N => f (x i)) = 0 :=
  pd_of_indep j _ fun x s => by simp [Ne.symm hij]

end RenewalGeometry.OddPhaseDerivativeReal
