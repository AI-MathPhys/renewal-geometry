/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact periodic discrete Hodge identity
  (`lem:native-discrete-Hodge`, Einstein–SM action closure)

Setting.  The periodic grid is any finite additive commutative group `X`
(for the paper `X = (ZMod N)⁴`, the odd periodic grid of side `2π`), the
coordinate directions form a finite linearly ordered type `ι` (for the paper
`ι = Fin 4`) with unit lattice steps `e μ : X`, and `h` is the mesh.  A
nodal one-form is `A : ι → X → E` with values in a real inner product space
`E` (the Lie algebra with its invariant inner product).

* `periodicHodgeFwd h e μ u x = (u(x + e_μ) - u x)/h`  (`D^+_{μ,h}`,
  `eq:native-critical-norms`);
* `periodicHodgeBwd h e μ u x = (u x - u(x - e_μ))/h`  (`D^-_{μ,h} = (I - T_{μ,-1})/h`);
* `periodicHodgeCodiff h e A = - Σ_μ D^-_μ A_μ`  (`δ_h`, `eq:native-discrete-divergence`);
* `periodicHodgeExtD h e A μ ν = D^+_μ A_ν - D^+_ν A_μ`  (`d_h^+`);
* `periodicHodgeNormSq ι h u = h^{dim} Σ_x ‖u x‖²`  (`‖·‖²_{2,h}` with `dim = card ι`);
* `periodicHodgeExtDNormSq` = `Σ_{μ<ν} ‖(d_h^+ A)_{μν}‖²_{2,h}`.

Results:

* `periodicHodge_identity` — `eq:native-discrete-Hodge`:
  `Σ_{μ,ν} ‖D^+_μ A_ν‖²_{2,h} = ‖d_h^+ A‖²_{2,h} + ‖δ_h A‖²_{2,h}`, exactly, for
  every mesh `h` and every nodal one-form;
* `periodicHodge_H1_bound` — the consequence
  `‖A‖_{1,h} ≤ C(‖d_h^+A‖_{2,h} + ‖δ_h A‖_{2,h} + ‖A‖_{2,h})` with `C = 1`,
  uniformly in `h > 0`, where `‖A‖²_{1,h} = Σ_ν ‖A_ν‖²_{2,h} + Σ_{μ,ν} ‖D^+_μ A_ν‖²_{2,h}`.

The proof is in position space (two translations of the periodic sum)
instead of the Fourier argument of the paper; the identity is the same.
-/

namespace RenewalGeometry

open Finset

noncomputable section

section PeriodicHodge

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {X : Type*} [AddCommGroup X] [Fintype X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Forward difference `D^+_{μ,h} u(x) = (u(x + h e_μ) - u(x))/h` on the periodic
grid (`eq:native-critical-norms`). -/
def periodicHodgeFwd (h : ℝ) (e : ι → X) (μ : ι) (u : X → E) (x : X) : E :=
  h⁻¹ • (u (x + e μ) - u x)

/-- Backward difference `D^-_{μ,h} = (I - T_{μ,-1})/h`. -/
def periodicHodgeBwd (h : ℝ) (e : ι → X) (μ : ι) (u : X → E) (x : X) : E :=
  h⁻¹ • (u x - u (x - e μ))

/-- Discrete codifferential `δ_h A = - Σ_μ D^-_{μ,h} A_μ`
(`eq:native-discrete-divergence`). -/
def periodicHodgeCodiff (h : ℝ) (e : ι → X) (A : ι → X → E) (x : X) : E :=
  -∑ μ, periodicHodgeBwd h e μ (A μ) x

/-- Forward exterior derivative `(d_h^+ A)_{μν} = D^+_μ A_ν - D^+_ν A_μ`. -/
def periodicHodgeExtD (h : ℝ) (e : ι → X) (A : ι → X → E) (μ ν : ι) (x : X) : E :=
  periodicHodgeFwd h e μ (A ν) x - periodicHodgeFwd h e ν (A μ) x

variable (ι) in
/-- Discrete `L²` norm squared `‖u‖²_{2,h} = h^{dim} Σ_x ‖u(x)‖²`,
`dim = card ι` (`h⁴` in four dimensions). -/
def periodicHodgeNormSq (h : ℝ) (u : X → E) : ℝ :=
  h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 2

/-- `‖d_h^+ A‖²_{2,h} = Σ_{μ<ν} ‖(d_h^+A)_{μν}‖²_{2,h}`. -/
def periodicHodgeExtDNormSq (h : ℝ) (e : ι → X) (A : ι → X → E) : ℝ :=
  ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
    periodicHodgeNormSq ι h (periodicHodgeExtD h e A p.1 p.2)

/-- Sum over ordered pairs `μ < ν` of a symmetric function vanishing on the
diagonal is half the full double sum. -/
theorem periodicHodge_sum_lt_eq_half {F : ι → ι → ℝ} (hsymm : ∀ μ ν, F μ ν = F ν μ)
    (hdiag : ∀ μ, F μ μ = 0) :
    ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2), F p.1 p.2 =
      (1 / 2) * ∑ μ, ∑ ν, F μ ν := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (ι × ι))
    (fun p => p.1 < p.2) (fun p => F p.1 p.2)
  have hnot : ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => ¬ p.1 < p.2), F p.1 p.2 =
      ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2), F p.1 p.2 := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← (Equiv.prodComm ι ι).sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, not_lt.mpr hlt.le]
      exact hsymm _ _
    · simp [heq, hdiag]
    · simp [hgt, not_lt.mpr hgt.le]
  have hfull : ∑ p : ι × ι, F p.1 p.2 = ∑ μ, ∑ ν, F μ ν :=
    Fintype.sum_prod_type _
  rw [hnot] at hsplit
  rw [← hfull, ← hsplit]
  ring

/-- Translation pairing on the periodic grid: for all `f, g` and shifts `a, b`,
`Σ_x ⟨f(x) - f(x-a), g(x) - g(x-b)⟩ = Σ_x ⟨f(x+b) - f(x), g(x+a) - g(x)⟩`
(two summations by parts and commutation of shifts). -/
theorem periodicHodge_shift_pairing (f g : X → E) (a b : X) :
    ∑ x, inner ℝ (f x - f (x - a)) (g x - g (x - b)) =
      ∑ x, inner ℝ (f (x + b) - f x) (g (x + a) - g x) := by
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  have h1 : ∑ x, inner ℝ (f x) (g (x - b)) = ∑ x, inner ℝ (f (x + b)) (g x) := by
    rw [← Equiv.sum_comp (Equiv.addRight b) (fun x => inner ℝ (f x) (g (x - b)))]
    simp
  have h2 : ∑ x, inner ℝ (f (x - a)) (g x) = ∑ x, inner ℝ (f x) (g (x + a)) := by
    rw [← Equiv.sum_comp (Equiv.addRight a) (fun x => inner ℝ (f (x - a)) (g x))]
    simp
  have h3 : ∑ x, inner ℝ (f (x - a)) (g (x - b)) = ∑ x, inner ℝ (f (x + b)) (g (x + a)) := by
    rw [← Equiv.sum_comp (Equiv.addRight (a + b)) (fun x => inner ℝ (f (x - a)) (g (x - b)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight]
    congr 2 <;> abel_nf
  rw [h1, h2, h3]
  ring

/-- Unscaled form of the Hodge identity (`h = 1`, no volume factor). -/
theorem periodicHodge_identity_unscaled (e : ι → X) (A : ι → X → E) :
    ∑ μ, ∑ ν, ∑ x, ‖A ν (x + e μ) - A ν x‖ ^ 2 =
      ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        ∑ x, ‖(A p.2 (x + e p.1) - A p.2 x) - (A p.1 (x + e p.2) - A p.1 x)‖ ^ 2 +
      ∑ x, ‖∑ μ, (A μ x - A μ (x - e μ))‖ ^ 2 := by
  -- notation
  set Dp : ι → ι → X → E := fun μ ν x => A ν (x + e μ) - A ν x with hDp
  set P : ι → ι → ℝ := fun μ ν => ∑ x, inner ℝ (Dp μ ν x) (Dp ν μ x) with hP
  set N : ι → ι → ℝ := fun μ ν => ∑ x, ‖Dp μ ν x‖ ^ 2 with hN
  -- exterior part
  have hext : ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        ∑ x, ‖Dp p.1 p.2 x - Dp p.2 p.1 x‖ ^ 2 =
      ∑ μ, ∑ ν, N μ ν - ∑ μ, ∑ ν, P μ ν := by
    rw [periodicHodge_sum_lt_eq_half (F := fun μ ν => ∑ x, ‖Dp μ ν x - Dp ν μ x‖ ^ 2)]
    · have hexp : ∀ μ ν, ∑ x, ‖Dp μ ν x - Dp ν μ x‖ ^ 2 = N μ ν + N ν μ - 2 * P μ ν := by
        intro μ ν
        simp only [hN, hP, norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
        ring
      simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun μ ν => N ν μ)]
      simp only [← Finset.mul_sum]
      ring
    · intro μ ν
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← norm_neg, neg_sub]
    · intro μ
      simp
  -- codifferential part
  have hcod : ∑ x, ‖∑ μ, (A μ x - A μ (x - e μ))‖ ^ 2 = ∑ μ, ∑ ν, P μ ν := by
    have hx : ∀ x, ‖∑ μ, (A μ x - A μ (x - e μ))‖ ^ 2 =
        ∑ μ, ∑ ν, inner ℝ (A μ x - A μ (x - e μ)) (A ν x - A ν (x - e ν)) := by
      intro x
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [inner_sum]
    simp only [hx]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [periodicHodge_shift_pairing (A μ) (A ν) (e μ) (e ν)]
    simp only [hP, hDp]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact real_inner_comm _ _
  have hlhs : ∑ μ, ∑ ν, ∑ x, ‖A ν (x + e μ) - A ν x‖ ^ 2 = ∑ μ, ∑ ν, N μ ν := rfl
  rw [hlhs, hcod]
  have hext' := hext
  simp only [hDp] at hext'
  rw [hext']
  ring

/-- `lem:native-discrete-Hodge`, `eq:native-discrete-Hodge`: for every mesh
`h` and every nodal one-form on the periodic grid,
`Σ_{μ,ν} ‖D^+_{μ,h} A_ν‖²_{2,h} = ‖d_h^+ A‖²_{2,h} + ‖δ_h A‖²_{2,h}`. -/
theorem periodicHodge_identity (h : ℝ) (e : ι → X) (A : ι → X → E) :
    ∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h e μ (A ν)) =
      periodicHodgeExtDNormSq h e A + periodicHodgeNormSq ι h (periodicHodgeCodiff h e A) := by
  have hsm : ∀ v : E, ‖h⁻¹ • v‖ ^ 2 = (h⁻¹) ^ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have key := periodicHodge_identity_unscaled e A
  set w : ℝ := h ^ Fintype.card ι * (h⁻¹) ^ 2 with hw
  have hL : ∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h e μ (A ν)) =
      w * ∑ μ, ∑ ν, ∑ x, ‖A ν (x + e μ) - A ν x‖ ^ 2 := by
    simp only [periodicHodgeNormSq, periodicHodgeFwd, hsm, Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hD : periodicHodgeExtDNormSq h e A =
      w * ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        ∑ x, ‖(A p.2 (x + e p.1) - A p.2 x) - (A p.1 (x + e p.2) - A p.1 x)‖ ^ 2 := by
    simp only [periodicHodgeExtDNormSq, periodicHodgeNormSq, periodicHodgeExtD,
      periodicHodgeFwd, ← smul_sub, hsm, Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hC : periodicHodgeNormSq ι h (periodicHodgeCodiff h e A) =
      w * ∑ x, ‖∑ μ, (A μ x - A μ (x - e μ))‖ ^ 2 := by
    simp only [periodicHodgeNormSq, periodicHodgeCodiff, periodicHodgeBwd, ← Finset.smul_sum,
      norm_neg, hsm, Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [hL, hD, hC, key]
  ring

/-- Discrete `H¹` norm squared of a nodal one-form,
`‖A‖²_{1,h} = Σ_ν ‖A_ν‖²_{2,h} + Σ_{μ,ν} ‖D^+_{μ,h} A_ν‖²_{2,h}`
(componentwise version of the norm of `lem:native-reconstruction-identification`). -/
def periodicHodgeH1NormSq (h : ℝ) (e : ι → X) (A : ι → X → E) : ℝ :=
  ∑ ν, periodicHodgeNormSq ι h (A ν) +
    ∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h e μ (A ν))

theorem periodicHodgeNormSq_nonneg {h : ℝ} (hh : 0 ≤ h) (u : X → E) :
    0 ≤ periodicHodgeNormSq ι h u :=
  mul_nonneg (pow_nonneg hh _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `lem:native-discrete-Hodge`, consequence: uniformly in the mesh `h > 0`
(indeed with constant `C = 1`),
`‖A‖_{1,h} ≤ ‖d_h^+ A‖_{2,h} + ‖δ_h A‖_{2,h} + ‖A‖_{2,h}`,
with `‖A‖²_{2,h} = Σ_ν ‖A_ν‖²_{2,h}`. -/
theorem periodicHodge_H1_bound {h : ℝ} (hh : 0 ≤ h) (e : ι → X) (A : ι → X → E) :
    Real.sqrt (periodicHodgeH1NormSq h e A) ≤
      1 * (Real.sqrt (periodicHodgeExtDNormSq h e A) +
        Real.sqrt (periodicHodgeNormSq ι h (periodicHodgeCodiff h e A)) +
        Real.sqrt (∑ ν, periodicHodgeNormSq ι h (A ν))) := by
  have hid := periodicHodge_identity h e A
  set a := periodicHodgeExtDNormSq h e A
  set b := periodicHodgeNormSq ι h (periodicHodgeCodiff h e A)
  set c := ∑ ν, periodicHodgeNormSq ι h (A ν)
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ => periodicHodgeNormSq_nonneg hh _
  have hb : 0 ≤ b := periodicHodgeNormSq_nonneg hh _
  have hc : 0 ≤ c := Finset.sum_nonneg fun _ _ => periodicHodgeNormSq_nonneg hh _
  have hH : periodicHodgeH1NormSq h e A = a + b + c := by
    unfold periodicHodgeH1NormSq
    rw [hid]
    ring
  rw [hH, one_mul]
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsc := Real.sq_sqrt hc
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  have hnc := Real.sqrt_nonneg c
  have hsum : 0 ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by positivity
  have hsq : a + b + c ≤ (Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2 := by
    nlinarith [mul_nonneg hna hnb, mul_nonneg hna hnc, mul_nonneg hnb hnc]
  calc Real.sqrt (a + b + c) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b + Real.sqrt c) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt a + Real.sqrt b + Real.sqrt c := Real.sqrt_sq hsum

end PeriodicHodge

end

end RenewalGeometry
