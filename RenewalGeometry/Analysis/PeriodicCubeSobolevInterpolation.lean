/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.PeriodicCubeCalculus

/-!
# Sobolev interpolation for periodic functions on a cube, in derivative form

Generic infrastructure (no renewal notions) for the space-time interpolation step of
`prop:shadow-residual-upgrade` of the Einstein–Standard-Model action-closure manuscript.

Functions `f : ℝ^ι → W` (any finite index type `ι`, values in a real normed space) that are
periodic of period `L > 0` in every coordinate (`IsPer L f`), integrated over the cube
`[0, L]^ι` (`cube L`).  The Sobolev energies are written with classical derivatives: the squared
order-`j` energy density is the sum over all **ordered** words `w ∈ ι^j` of the squared partial
derivatives `∂_{w_1}⋯∂_{w_j} f = D^j f(e_{w_1}, …, e_{w_j})` (`pw f j`), and
`sobA L f j = ∫_{[0,L]^ι} pw f j` (`Σ_{j ≤ k} sobA L f j` is the squared `H^k` norm on the
torus `ℝ^ι / Lℤ^ι`).

## Main results

* `logConvex_pow_le`, `logConvex_pow_le_const`: a nonnegative sequence with
  `a_{j+1}² ≤ c a_j a_{j+2}` (`c ≥ 1`) satisfies `a_k^s ≤ c^{k C(s,2)} a_0^{s-k} a_s^k`.
* `integral_pd_eq_zero_L`, `integral_inner_pd`: integration by parts on the period cube.
* `sobA_succ_sq_le` (inner-product values): `a_{j+1}² ≤ |ι| a_j a_{j+2}`, from
  `‖∂_i∂_w f‖² = -⟨∂_w f, ∂_i∂_i∂_w f⟩` integrated over the cube.
* **`sobA_interp`** (inner-product values) and **`sobA_interp_normed`** (any finite-dimensional
  real normed space of values, through `toEuclidean`): the **interpolation inequality**
  `(∫ pw f k)^s ≤ C (∫ |f|²)^{s-k} (∫ pw f s)^k`, `k ≤ s`, with `C` depending only on `W`, `ι`,
  `k`, `s` (not on `f` or `L`).
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff InnerProductSpace Pointwise

namespace RenewalGeometry.PeriodicSobInterp

set_option linter.unusedSectionVars false

/-! ### Log-convex sequences -/

/-- Positive log-convex sequences: `b_k^s ≤ b_0^{s-k} b_s^k`. -/
theorem logConvex_pow_le_of_pos {b : ℕ → ℝ} {s : ℕ} (hpos : ∀ j ≤ s, 0 < b j)
    (hlc : ∀ j, j + 2 ≤ s → b (j + 1) ^ 2 ≤ b j * b (j + 2)) {k : ℕ} (hk : k ≤ s) :
    b k ^ s ≤ b 0 ^ (s - k) * b s ^ k := by
  rcases eq_or_lt_of_le hk with rfl | hks
  · simp
  set r : ℕ → ℝ := fun j => b (j + 1) / b j with hr
  have hstep : ∀ j, j + 2 ≤ s → r j ≤ r (j + 1) := by
    intro j hj
    simp only [hr]
    rw [div_le_div_iff₀ (hpos j (by omega)) (hpos (j + 1) (by omega))]
    have := hlc j hj
    nlinarith
  have hmono : ∀ i j, i ≤ j → j + 1 ≤ s → r i ≤ r j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hj
      exact (ih (by omega)).trans (hstep j (by omega))
  have hrb : ∀ j, j + 1 ≤ s → b (j + 1) = b j * r j := by
    intro j hj
    simp only [hr]
    field_simp [(hpos j (by omega)).ne']
  set ρ := r k with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (hpos (k + 1) (by omega)).le (hpos k (by omega)).le
  have hI : ∀ m ≤ k, b m ≤ b 0 * ρ ^ m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hrb m (by omega), pow_succ, ← mul_assoc]
      have h1 := ih (by omega)
      have h2 : r m ≤ ρ := hmono m k (by omega) (by omega)
      have h3 : 0 ≤ r m := div_nonneg (hpos (m + 1) (by omega)).le (hpos m (by omega)).le
      have h4 : 0 ≤ b m := (hpos m (by omega)).le
      calc b m * r m ≤ (b 0 * ρ ^ m) * r m := mul_le_mul_of_nonneg_right h1 h3
        _ ≤ (b 0 * ρ ^ m) * ρ := mul_le_mul_of_nonneg_left h2 (h4.trans h1)
  have hII : ∀ m, k ≤ m → m ≤ s → b k * ρ ^ (m - k) ≤ b m := by
    intro m hkm
    induction m, hkm using Nat.le_induction with
    | base => intro _; simp
    | succ m hkm ih =>
      intro hm
      rw [hrb m (by omega), show m + 1 - k = (m - k) + 1 by omega, pow_succ, ← mul_assoc]
      have h1 := ih (by omega)
      have h2 : ρ ≤ r m := hmono k m hkm (by omega)
      have h5 : 0 ≤ b k * ρ ^ (m - k) := mul_nonneg (hpos k (by omega)).le (pow_nonneg hρ0 _)
      calc b k * ρ ^ (m - k) * ρ ≤ b k * ρ ^ (m - k) * r m := mul_le_mul_of_nonneg_left h2 h5
        _ ≤ b m * r m := mul_le_mul_of_nonneg_right h1 (hρ0.trans h2)
  have hA := hI k le_rfl
  have hB := hII s hk le_rfl
  have hbk : 0 ≤ b k := (hpos k hk).le
  calc b k ^ s = b k ^ (s - k) * b k ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ ≤ (b 0 * ρ ^ k) ^ (s - k) * b k ^ k := by gcongr
    _ = b 0 ^ (s - k) * (b k * ρ ^ (s - k)) ^ k := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k (s - k)]; ring
    _ ≤ b 0 ^ (s - k) * b s ^ k := by
        have : 0 ≤ b 0 ^ (s - k) := pow_nonneg (hpos 0 (Nat.zero_le _)).le _
        gcongr

/-- **Log-convex sequences** (nonnegative): if `b_{j+1}² ≤ b_j b_{j+2}` for `j + 2 ≤ s`, then
`b_k^s ≤ b_0^{s-k} b_s^k` for `k ≤ s` (perturbation `b + δ`, `δ → 0`). -/
theorem logConvex_pow_le {b : ℕ → ℝ} {s : ℕ} (hnn : ∀ j, 0 ≤ b j)
    (hlc : ∀ j, j + 2 ≤ s → b (j + 1) ^ 2 ≤ b j * b (j + 2)) {k : ℕ} (hk : k ≤ s) :
    b k ^ s ≤ b 0 ^ (s - k) * b s ^ k := by
  have hδ : ∀ δ : ℝ, 0 < δ → (b k + δ) ^ s ≤ (b 0 + δ) ^ (s - k) * (b s + δ) ^ k := by
    intro δ hδ
    refine logConvex_pow_le_of_pos (b := fun j => b j + δ) (fun j _ => by
      have := hnn j; positivity) (fun j hj => ?_) hk
    have h := hlc j hj
    have h0 := hnn j; have h1 := hnn (j + 1); have h2 := hnn (j + 2)
    have hm : 2 * b (j + 1) ≤ b j + b (j + 2) := by
      by_contra hcon
      push Not at hcon
      have hs : (b j + b (j + 2)) * (b j + b (j + 2)) < (2 * b (j + 1)) * (2 * b (j + 1)) :=
        mul_self_lt_mul_self (by positivity) hcon
      nlinarith [sq_nonneg (b j - b (j + 2))]
    show (b (j + 1) + δ) ^ 2 ≤ (b j + δ) * (b (j + 2) + δ)
    nlinarith
  have hc1 : Continuous fun δ : ℝ => (b k + δ) ^ s := by fun_prop
  have hc2 : Continuous fun δ : ℝ => (b 0 + δ) ^ (s - k) * (b s + δ) ^ k := by fun_prop
  have t1 := (hc1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have t2 := (hc2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at t1 t2
  exact le_of_tendsto_of_tendsto t1 t2
    (eventually_nhdsWithin_of_forall fun δ hδ' => hδ δ hδ')

/-- `C(j,2) + C(j+2,2) = 2 C(j+1,2) + 1`. -/
theorem choose_two_add (j : ℕ) : j.choose 2 + (j + 2).choose 2 = 2 * (j + 1).choose 2 + 1 := by
  have e1 : (j + 1).choose 2 = j + j.choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  have e2 : (j + 2).choose 2 = (j + 1) + (j + 1).choose 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
  omega

/-- **Interpolation for sequences with a constant**: if `a_{j+1}² ≤ c a_j a_{j+2}` (`c ≥ 1`) for
`j + 2 ≤ s`, then `a_k^s ≤ c^{k C(s,2)} a_0^{s-k} a_s^k` for `k ≤ s`. -/
theorem logConvex_pow_le_const {a : ℕ → ℝ} {s : ℕ} {c : ℝ} (hc : 1 ≤ c) (hnn : ∀ j, 0 ≤ a j)
    (hlc : ∀ j, j + 2 ≤ s → a (j + 1) ^ 2 ≤ c * a j * a (j + 2)) {k : ℕ} (hk : k ≤ s) :
    a k ^ s ≤ c ^ (k * s.choose 2) * a 0 ^ (s - k) * a s ^ k := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  set b : ℕ → ℝ := fun j => a j * c ^ j.choose 2 with hb
  have hbn : ∀ j, 0 ≤ b j := fun j => mul_nonneg (hnn j) (pow_nonneg hc0.le _)
  have hblc : ∀ j, j + 2 ≤ s → b (j + 1) ^ 2 ≤ b j * b (j + 2) := by
    intro j hj
    simp only [hb]
    have h := hlc j hj
    have e : c ^ j.choose 2 * c ^ (j + 2).choose 2 = c * (c ^ (j + 1).choose 2) ^ 2 := by
      rw [← pow_add, choose_two_add, ← pow_mul, ← pow_succ', mul_comm 2]
    calc (a (j + 1) * c ^ (j + 1).choose 2) ^ 2 = a (j + 1) ^ 2 * (c ^ (j + 1).choose 2) ^ 2 := by
          ring
      _ ≤ (c * a j * a (j + 2)) * (c ^ (j + 1).choose 2) ^ 2 := by gcongr
      _ = a j * c ^ j.choose 2 * (a (j + 2) * c ^ (j + 2).choose 2) := by
          rw [mul_mul_mul_comm, e]; ring
  have h := logConvex_pow_le hbn hblc hk
  simp only [hb, Nat.choose_zero_succ, pow_zero, mul_one] at h
  have hge : 1 ≤ (c ^ k.choose 2) ^ s := one_le_pow₀ (one_le_pow₀ hc)
  have ha0 : 0 ≤ a k ^ s := pow_nonneg (hnn k) _
  calc a k ^ s ≤ a k ^ s * (c ^ k.choose 2) ^ s := le_mul_of_one_le_right ha0 hge
    _ = (a k * c ^ k.choose 2) ^ s := by rw [mul_pow]
    _ ≤ a 0 ^ (s - k) * (a s * c ^ s.choose 2) ^ k := h
    _ = c ^ (k * s.choose 2) * a 0 ^ (s - k) * a s ^ k := by
        rw [mul_pow, ← pow_mul, mul_comm (s.choose 2) k]; ring

/-- `x² ≤ a b` from the family `2λx ≤ λ²a + b` (`λ > 0`). -/
theorem sq_le_of_forall_quad {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : ∀ lam : ℝ, 0 < lam → 2 * lam * x ≤ lam ^ 2 * a + b) : x ^ 2 ≤ a * b := by
  rcases eq_or_lt_of_le hx with hx0 | hxp
  · rw [← hx0]; simp; positivity
  rcases eq_or_lt_of_le ha with ha0 | hap
  · exfalso
    have := h ((b + 1) / (2 * x)) (by positivity)
    rw [← ha0, mul_zero, zero_add] at this
    have e : 2 * ((b + 1) / (2 * x)) * x = b + 1 := by field_simp
    linarith
  · have := h (x / a) (by positivity)
    have e1 : 2 * (x / a) * x = 2 * (x ^ 2 / a) := by ring
    have e2 : (x / a) ^ 2 * a = x ^ 2 / a := by field_simp
    rw [e1, e2] at this
    have : x ^ 2 / a ≤ b := by linarith
    rwa [div_le_iff₀ hap, mul_comm] at this

/-! ### Periodic functions on the cube `[0, L]^ι` -/

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open SobolevOpen (pd)
open PeriodicCube (zvec IsZPeriodic)

/-- The period cube `[0, L]^ι`. -/
def cube (L : ℝ) : Set (ι → ℝ) := Icc 0 (fun _ => L)

/-- Periodicity of period `L` in every coordinate. -/
def IsPer (L : ℝ) {α : Type*} (f : (ι → ℝ) → α) : Prop :=
  ∀ (k : ι → ℤ) (x : ι → ℝ), f (x + L • zvec k) = f x

theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem natCast_lt_infty (n : ℕ) : (n : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top n

theorem smul_unit_cube {L : ℝ} (hL : 0 < L) : L • Icc (0 : ι → ℝ) 1 = cube L := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne', cube, Set.mem_Icc, Set.mem_Icc]
  simp only [Pi.le_def, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply]
  have hi : 0 < L⁻¹ := inv_pos.2 hL
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (mul_nonneg_iff_of_pos_left hi).1 (h1 i)
    · have := h2 i
      rw [inv_mul_le_iff₀ hL, mul_one] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => mul_nonneg hi.le (h1 i), fun i => ?_⟩
    rw [inv_mul_le_iff₀ hL, mul_one]
    exact h2 i

theorem IsPer.unit {L : ℝ} {α : Type*} {f : (ι → ℝ) → α} (hf : IsPer L f) :
    IsZPeriodic (fun y => f (L • y)) := fun k y => by
  simp only [smul_add]
  exact hf k (L • y)

theorem IsPer.comp {L : ℝ} {α β : Type*} {f : (ι → ℝ) → α} (hf : IsPer L f) (g : α → β) :
    IsPer L (g ∘ f) := fun k x => by simp [Function.comp, hf k x]

theorem IsPer.iteratedFDeriv {L : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ι → ℝ) → F} (hf : IsPer L f) (j : ℕ) : IsPer L (iteratedFDeriv ℝ j f) := fun k x => by
  have e : (fun z => f (z + L • zvec k)) = f := funext fun z => hf k z
  rw [← iteratedFDeriv_comp_add_right, e]

theorem pd_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : (ι → ℝ) → F}
    (hh : Differentiable ℝ h) (L : ℝ) (i : ι) (y : ι → ℝ) :
    pd (fun y => h (L • y)) i y = L • pd h i (L • y) := by
  unfold pd
  have hl : HasFDerivAt (fun y : ι → ℝ => L • y) (L • ContinuousLinearMap.id ℝ (ι → ℝ)) y :=
    (hasFDerivAt_id y).const_smul L
  have hc := (hh (L • y)).hasFDerivAt.comp y hl
  change fderiv ℝ (h ∘ fun y => L • y) y _ = _
  rw [hc.fderiv]
  simp

theorem integrableOn_cube {F : Type*} [NormedAddCommGroup F] {g : (ι → ℝ) → F}
    (hg : Continuous g) (L : ℝ) : IntegrableOn g (cube L) :=
  hg.integrableOn_Icc

/-- **Integration by parts on the period cube**: `∫_{[0,L]^ι} ∂_i h = 0` for `C¹`, `L`-periodic
`h`. -/
theorem integral_pd_eq_zero_L {L : ℝ} (hL : 0 < L) {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ 1 h)
    (hper : IsPer L h) (i : ι) : ∫ x in cube L, pd h i x = 0 := by
  have h1 := PeriodicCube.integral_pd_eq_zero (hh.comp (contDiff_const_smul L)) hper.unit i
  have e : ∀ y, pd (h ∘ fun y => L • y) i y = L * pd h i (L • y) := fun y =>
    pd_comp_smul (hh.differentiable one_ne_zero) L i y
  simp_rw [e] at h1
  rw [integral_const_mul] at h1
  have h2 : ∫ y in Icc (0 : ι → ℝ) 1, pd h i (L • y) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hL.ne'
    · exact h
  rw [Measure.setIntegral_comp_smul_of_pos _ _ _ hL, smul_unit_cube hL] at h2
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd h (inv_ne_zero (pow_ne_zero _ hL.ne'))
  · exact h

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem continuous_pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : (ι → ℝ) → F}
    (hu : ContDiff ℝ 1 u) (i : ι) : Continuous (pd u i) :=
  (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- **Integration by parts for the inner product**: `∫⟨∂_i u, v⟩ = -∫⟨u, ∂_i v⟩` on the period
cube for `C¹`, `L`-periodic `u, v`. -/
theorem integral_inner_pd {L : ℝ} (hL : 0 < L) {u v : (ι → ℝ) → W} (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hpu : IsPer L u) (hpv : IsPer L v) (i : ι) :
    ∫ x in cube L, ⟪pd u i x, v x⟫_ℝ = -∫ x in cube L, ⟪u x, pd v i x⟫_ℝ := by
  set h : (ι → ℝ) → ℝ := fun x => ⟪u x, v x⟫_ℝ with hhdef
  have hh : ContDiff ℝ 1 h := hu.inner ℝ hv
  have hper : IsPer L h := fun k x => by simp only [hhdef, hpu k x, hpv k x]
  have hpd : ∀ x, pd h i x = ⟪u x, pd v i x⟫_ℝ + ⟪pd u i x, v x⟫_ℝ := by
    intro x
    have hd := ((hu.differentiable one_ne_zero) x).hasFDerivAt.inner ℝ
      ((hv.differentiable one_ne_zero) x).hasFDerivAt
    unfold pd
    rw [hd.fderiv]
    simp
  have h0 := integral_pd_eq_zero_L hL hh hper i
  simp_rw [hpd] at h0
  rw [integral_add (integrableOn_cube ((hu.continuous.inner (continuous_pd hv i))) L)
    (integrableOn_cube ((continuous_pd hu i).inner hv.continuous) L)] at h0
  linarith

/-! ### Ordered partial derivatives and the Sobolev energies -/

/-- The coordinate vectors along a word `w ∈ ι^j`. -/
def evw {j : ℕ} (w : Fin j → ι) : Fin j → (ι → ℝ) := fun l => Pi.single (w l) 1

theorem evw_cons {j : ℕ} (i : ι) (w : Fin j → ι) :
    evw (Fin.cons i w : Fin (j + 1) → ι) = Fin.cons (Pi.single i 1) (evw w) := by
  funext l
  refine Fin.cases ?_ (fun l => ?_) l <;> simp [evw]

/-- The squared order-`j` energy density: `Σ_{w ∈ ι^j} ‖∂_{w_1}⋯∂_{w_j} f‖²`. -/
def pw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → ℝ) → F) (j : ℕ)
    (x : ι → ℝ) : ℝ :=
  ∑ w : Fin j → ι, ‖iteratedFDeriv ℝ j f x (evw w)‖ ^ 2

/-- The squared order-`j` Sobolev energy on the period cube. -/
def sobA {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ) (f : (ι → ℝ) → F)
    (j : ℕ) : ℝ :=
  ∫ x in cube L, pw f j x

theorem pw_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → ℝ) → F)
    (j : ℕ) (x : ι → ℝ) : 0 ≤ pw f j x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sobA_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ)
    (f : (ι → ℝ) → F) (j : ℕ) : 0 ≤ sobA L f j :=
  setIntegral_nonneg measurableSet_Icc fun x _ => pw_nonneg f j x

theorem pw_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → ℝ) → F)
    (x : ι → ℝ) : pw f 0 x = ‖f x‖ ^ 2 := by
  simp [pw]

theorem continuous_pw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (ι → ℝ) → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) : Continuous (pw f j) := by
  unfold pw
  refine continuous_finsetSum _ fun w _ => ?_
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ι → ℝ) F (evw w)).continuous.comp
    (hf.continuous_iteratedFDeriv (natCast_le_infty j))
  exact this.norm.pow 2

/-- The `j`-th derivative applied to fixed vectors, as a function. -/
def Fm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → ℝ) → F) (j : ℕ)
    (m : Fin j → (ι → ℝ)) (x : ι → ℝ) : F :=
  iteratedFDeriv ℝ j f x m

theorem contDiff_Fm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (ι → ℝ) → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (m : Fin j → (ι → ℝ)) : ContDiff ℝ ∞ (Fm f j m) := by
  have h1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast le_rfl)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ι → ℝ) F m).contDiff.comp h1

theorem IsPer.Fm {L : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (ι → ℝ) → F} (hf : IsPer L f) (j : ℕ) (m : Fin j → (ι → ℝ)) : IsPer L (Fm f j m) :=
  fun k x => by
    show _root_.iteratedFDeriv ℝ j f (x + L • zvec k) m = _root_.iteratedFDeriv ℝ j f x m
    rw [hf.iteratedFDeriv j k x]

/-- `∂_i (D^j f(m)) = D^{j+1} f(e_i, m)`. -/
theorem pd_Fm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (ι → ℝ) → F}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (m : Fin j → (ι → ℝ)) (i : ι) :
    pd (Fm f j m) i = Fm f (j + 1) (Fin.cons (Pi.single i 1) m) := by
  funext x
  unfold pd Fm
  rw [fderiv_continuousMultilinear_apply_const_apply
    ((hf.differentiable_iteratedFDeriv (natCast_lt_infty j)) x) m (Pi.single i 1),
    iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]

theorem sum_fin_succ_fun {M : Type*} [AddCommMonoid M] (j : ℕ) (g : (Fin (j + 1) → ι) → M) :
    ∑ w', g w' = ∑ i : ι, ∑ w : Fin j → ι, g (Fin.cons i w) := by
  rw [← (Fin.consEquiv fun _ : Fin (j + 1) => ι).sum_comp, Fintype.sum_prod_type]; rfl

theorem pw_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (ι → ℝ) → F)
    (j : ℕ) (x : ι → ℝ) :
    pw f (j + 1) x = ∑ i : ι, ∑ w : Fin j → ι, ‖Fm f (j + 1) (Fin.cons (Pi.single i 1) (evw w)) x‖ ^ 2 := by
  unfold pw Fm
  rw [sum_fin_succ_fun]
  simp only [evw_cons]

/-- **The key inequality**: for `λ > 0`,
`2λ ∫ pw f (j+1) ≤ λ² ∫ pw f j + |ι| ∫ pw f (j+2)` (inner-product values), from
`‖∂_i F‖² = -⟨F, ∂_i∂_i F⟩` integrated and `‖λF + S‖² ≥ 0`. -/
theorem sobA_succ_quad {L : ℝ} (hL : 0 < L) {f : (ι → ℝ) → W} (hf : ContDiff ℝ ∞ f)
    (hper : IsPer L f) (j : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    2 * lam * sobA L f (j + 1) ≤
      lam ^ 2 * sobA L f j + (Fintype.card ι : ℝ) * sobA L f (j + 2) := by
  set F : (Fin j → ι) → (ι → ℝ) → W := fun w => Fm f j (evw w) with hF
  have hFc : ∀ w, ContDiff ℝ ∞ (F w) := fun w => contDiff_Fm hf j _
  have hFp : ∀ w, IsPer L (F w) := fun w => hper.Fm j _
  -- `G w i = ∂_i ∂_i F_w`
  set G : (Fin j → ι) → ι → (ι → ℝ) → W := fun w i => pd (pd (F w) i) i with hG
  have hGc : ∀ w i, Continuous (G w i) := by
    intro w i
    simp only [hG, hF, pd_Fm hf]
    exact (contDiff_Fm hf _ _).continuous
  have hpdc : ∀ w i, ContDiff ℝ ∞ (pd (F w) i) := by
    intro w i; simp only [hF, pd_Fm hf]; exact contDiff_Fm hf _ _
  have hpdp : ∀ w i, IsPer L (pd (F w) i) := by
    intro w i; simp only [hF, pd_Fm hf]; exact hper.Fm _ _
  -- the integrated identity
  have hibp : ∀ w i, ∫ x in cube L, ‖pd (F w) i x‖ ^ 2 = -∫ x in cube L, ⟪F w x, G w i x⟫_ℝ := by
    intro w i
    have := integral_inner_pd hL ((hFc w).of_le (by exact_mod_cast le_top)) ((hpdc w i).of_le
      (by exact_mod_cast le_top)) (hFp w) (hpdp w i) i
    simp only [real_inner_self_eq_norm_sq] at this
    exact this
  -- `pw f (j+1) = Σ_i Σ_w ‖∂_i F_w‖²`
  have hpw1 : ∀ x, pw f (j + 1) x = ∑ i : ι, ∑ w : Fin j → ι, ‖pd (F w) i x‖ ^ 2 := by
    intro x
    rw [pw_succ]
    simp only [hF, pd_Fm hf]
  -- `Σ_w Σ_i ‖G_{w,i}‖² ≤ pw f (j+2)`
  have hGe : ∀ w i x, G w i x =
      Fm f (j + 1 + 1) (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single i 1) (evw w))) x := by
    intro w i x
    simp only [hG, hF, pd_Fm hf]
  have hpw2 : ∀ x, ∑ w : Fin j → ι, ∑ i : ι, ‖G w i x‖ ^ 2 ≤ pw f (j + 2) x := by
    intro x
    have e : pw f (j + 2) x = ∑ i : ι, ∑ i' : ι, ∑ w : Fin j → ι,
        ‖Fm f (j + 1 + 1) (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single i' 1) (evw w))) x‖ ^ 2 := by
      rw [pw_succ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_fin_succ_fun]
      simp only [evw_cons]
    rw [e, Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [hGe]
    exact Finset.single_le_sum (f := fun i' => ∑ w : Fin j → ι,
        ‖Fm f (j + 1 + 1) (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single i' 1) (evw w))) x‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg fun w _ => sq_nonneg _) (Finset.mem_univ i)
  -- pointwise quadratic bound
  have hpt : ∀ x, 2 * lam * (-∑ w : Fin j → ι, ⟪F w x, ∑ i : ι, G w i x⟫_ℝ) ≤
      lam ^ 2 * pw f j x + (Fintype.card ι : ℝ) * pw f (j + 2) x := by
    intro x
    have hq : ∀ w, 2 * lam * (-⟪F w x, ∑ i : ι, G w i x⟫_ℝ) ≤
        lam ^ 2 * ‖F w x‖ ^ 2 + ‖∑ i : ι, G w i x‖ ^ 2 := by
      intro w
      have h0 := norm_add_sq_real (lam • F w x) (∑ i : ι, G w i x)
      rw [norm_smul, real_inner_smul_left, Real.norm_eq_abs, abs_of_pos hlam] at h0
      nlinarith [sq_nonneg ‖lam • F w x + ∑ i : ι, G w i x‖]
    have hcs : ∀ w, ‖∑ i : ι, G w i x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ‖G w i x‖ ^ 2 := by
      intro w
      have h1 : ‖∑ i : ι, G w i x‖ ≤ ∑ i : ι, ‖G w i x‖ := norm_sum_le _ _
      have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖G w i x‖)
      rw [Finset.card_univ] at h2
      calc ‖∑ i : ι, G w i x‖ ^ 2 ≤ (∑ i : ι, ‖G w i x‖) ^ 2 := by gcongr
        _ ≤ _ := h2
    have hpwj : pw f j x = ∑ w : Fin j → ι, ‖F w x‖ ^ 2 := rfl
    calc 2 * lam * (-∑ w : Fin j → ι, ⟪F w x, ∑ i : ι, G w i x⟫_ℝ)
        = ∑ w : Fin j → ι, 2 * lam * (-⟪F w x, ∑ i : ι, G w i x⟫_ℝ) := by
          rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      _ ≤ ∑ w : Fin j → ι, (lam ^ 2 * ‖F w x‖ ^ 2 + ‖∑ i : ι, G w i x‖ ^ 2) :=
          Finset.sum_le_sum fun w _ => hq w
      _ ≤ ∑ w : Fin j → ι, (lam ^ 2 * ‖F w x‖ ^ 2 +
            (Fintype.card ι : ℝ) * ∑ i : ι, ‖G w i x‖ ^ 2) :=
          Finset.sum_le_sum fun w _ => by linarith [hcs w]
      _ = lam ^ 2 * pw f j x + (Fintype.card ι : ℝ) * ∑ w : Fin j → ι, ∑ i : ι, ‖G w i x‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hpwj]
      _ ≤ lam ^ 2 * pw f j x + (Fintype.card ι : ℝ) * pw f (j + 2) x := by
          gcongr; exact hpw2 x
  -- integrate
  have hcF : ∀ w, Continuous (F w) := fun w => (hFc w).continuous
  have hc1 : ∀ i w, Continuous (fun x => ‖pd (F w) i x‖ ^ 2) := fun i w =>
    (continuous_pd ((hFc w).of_le (by exact_mod_cast le_top)) i).norm.pow 2
  have hc2 : ∀ w i, Continuous (fun x => ⟪F w x, G w i x⟫_ℝ) := fun w i =>
    (hcF w).inner (hGc w i)
  have hL1 : sobA L f (j + 1) = ∑ i : ι, ∑ w : Fin j → ι, ∫ x in cube L, ‖pd (F w) i x‖ ^ 2 := by
    unfold sobA
    simp_rw [hpw1]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      intro w _
      exact integrableOn_cube (hc1 i w) L
    · intro i _
      exact integrableOn_cube (continuous_finsetSum _ fun w _ => hc1 i w) L
  have hR1 : ∫ x in cube L, -∑ w : Fin j → ι, ⟪F w x, ∑ i : ι, G w i x⟫_ℝ =
      ∑ i : ι, ∑ w : Fin j → ι, -∫ x in cube L, ⟪F w x, G w i x⟫_ℝ := by
    simp_rw [inner_sum]
    rw [integral_neg, integral_finset_sum]
    · have e : ∀ w : Fin j → ι, ∫ x in cube L, ∑ i : ι, ⟪F w x, G w i x⟫_ℝ =
          ∑ i : ι, ∫ x in cube L, ⟪F w x, G w i x⟫_ℝ := fun w =>
        integral_finset_sum _ fun i _ => integrableOn_cube (hc2 w i) L
      simp only [e, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    · intro w _
      exact integrableOn_cube (continuous_finsetSum _ fun i _ => hc2 w i) L
  have hint : sobA L f (j + 1) = ∫ x in cube L, -∑ w : Fin j → ι, ⟪F w x, ∑ i : ι, G w i x⟫_ℝ := by
    rw [hL1, hR1]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => hibp w i
  rw [hint, ← integral_const_mul (2 * lam)]
  unfold sobA
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (integrableOn_cube ((continuous_pw hf j).const_mul _) L)
    (integrableOn_cube ((continuous_pw hf (j + 2)).const_mul _) L)]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun x _ => hpt x
  · refine integrableOn_cube (continuous_const.mul ?_) L
    exact (continuous_finsetSum _ fun w _ => (hcF w).inner
      (continuous_finsetSum _ fun i _ => hGc w i)).neg
  · exact integrableOn_cube (((continuous_pw hf j).const_mul _).add
      ((continuous_pw hf (j + 2)).const_mul _)) L

/-- `a_{j+1}² ≤ |ι| a_j a_{j+2}` for the Sobolev energies of a smooth periodic function. -/
theorem sobA_succ_sq_le {L : ℝ} (hL : 0 < L) {f : (ι → ℝ) → W} (hf : ContDiff ℝ ∞ f)
    (hper : IsPer L f) (j : ℕ) :
    sobA L f (j + 1) ^ 2 ≤ (Fintype.card ι : ℝ) * sobA L f j * sobA L f (j + 2) := by
  have h := sq_le_of_forall_quad (sobA_nonneg L f j)
    (mul_nonneg (Nat.cast_nonneg _) (sobA_nonneg L f (j + 2))) (sobA_nonneg L f (j + 1))
    fun lam hlam => sobA_succ_quad hL hf hper j hlam
  linarith

/-- **Interpolation inequality** (inner-product values): for a smooth `L`-periodic `f` and
`k ≤ s`, `(∫ pw f k)^s ≤ c^{k C(s,2)} (∫ |f|²)^{s-k} (∫ pw f s)^k`, `c = max 1 |ι|`. -/
theorem sobA_interp {L : ℝ} (hL : 0 < L) {f : (ι → ℝ) → W} (hf : ContDiff ℝ ∞ f)
    (hper : IsPer L f) {k s : ℕ} (hks : k ≤ s) :
    sobA L f k ^ s ≤
      max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) * sobA L f 0 ^ (s - k) * sobA L f s ^ k := by
  refine logConvex_pow_le_const (le_max_left _ _) (sobA_nonneg L f) (fun j _ => ?_) hks
  refine (sobA_succ_sq_le hL hf hper j).trans ?_
  have h0 := sobA_nonneg L f j
  have h2 := sobA_nonneg L f (j + 2)
  have : (Fintype.card ι : ℝ) ≤ max 1 (Fintype.card ι : ℝ) := le_max_right _ _
  have := mul_le_mul_of_nonneg_right this (mul_nonneg h0 h2)
  nlinarith

/-! ### Values in a finite-dimensional normed space -/

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem pw_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (e : V →L[ℝ] E)
    {f : (ι → ℝ) → V} (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ι → ℝ) :
    pw (e ∘ f) j x ≤ ‖e‖ ^ 2 * pw f j x := by
  unfold pw
  rw [e.iteratedFDeriv_comp_left hf.contDiffAt (natCast_le_infty j), Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (e.le_opNorm _) 2

theorem sobA_mono {L : ℝ} {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (ι → ℝ) → F} {g : (ι → ℝ) → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {c : ℝ} (j : ℕ)
    (h : ∀ x, pw f j x ≤ c * pw g j x) : sobA L f j ≤ c * sobA L g j := by
  unfold sobA
  rw [← integral_const_mul]
  exact setIntegral_mono_on (integrableOn_cube (continuous_pw hf j) L)
    (integrableOn_cube ((continuous_pw hg j).const_mul c) L) measurableSet_Icc fun x _ => h x

variable [FiniteDimensional ℝ V]

/-- The constant of the interpolation inequality for values in `V`
(`(‖e‖ ‖e⁻¹‖)^{2s} max(1,|ι|)^{k C(s,2)}`, `e = toEuclidean`). -/
def interpConst (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ι : Type*) [Fintype ι] (k s : ℕ) : ℝ :=
  (‖((toEuclidean : V ≃L[ℝ] _) : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ *
    ‖(((toEuclidean : V ≃L[ℝ] _).symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V))‖) ^
      (2 * s) * max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2)

theorem interpConst_nonneg (k s : ℕ) : 0 ≤ interpConst V ι k s := by
  unfold interpConst; positivity

/-- **Interpolation inequality, finite-dimensional normed values**: for a smooth `L`-periodic
`f : ℝ^ι → V` and `k ≤ s`, `(∫ pw f k)^s ≤ C_{V,ι,k,s} (∫ |f|²)^{s-k} (∫ pw f s)^k`. -/
theorem sobA_interp_normed {L : ℝ} (hL : 0 < L) {f : (ι → ℝ) → V} (hf : ContDiff ℝ ∞ f)
    (hper : IsPer L f) {k s : ℕ} (hks : k ≤ s) :
    sobA L f k ^ s ≤ interpConst V ι k s * sobA L f 0 ^ (s - k) * sobA L f s ^ k := by
  set e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean with he
  set a := ‖(e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖ with ha
  set b := ‖((e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V))‖ with hb
  set g := (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ∘ f with hg
  have hgs : ContDiff ℝ ∞ g := by
    rw [hg]; exact (e : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))).contDiff.comp hf
  have hgp : IsPer L g := hper.comp _
  have hfg : (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V) ∘ g = f := by
    funext x; simp [hg]
  have h1 : ∀ j, sobA L f j ≤ b ^ 2 * sobA L g j := fun j => by
    refine sobA_mono hf hgs j fun x => ?_
    have := pw_comp_le (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V) hgs j x
    rwa [hfg] at this
  have h2 : ∀ j, sobA L g j ≤ a ^ 2 * sobA L f j := fun j =>
    sobA_mono hgs hf j fun x => pw_comp_le _ hf j x
  have hI := sobA_interp hL hgs hgp hks
  have hf0 := sobA_nonneg L f 0
  have hfs := sobA_nonneg L f s
  have hfk := sobA_nonneg L f k
  have hc0 : 0 ≤ max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) := by positivity
  calc sobA L f k ^ s ≤ (b ^ 2 * sobA L g k) ^ s := pow_le_pow_left₀ hfk (h1 k) s
    _ = (b ^ 2) ^ s * sobA L g k ^ s := by rw [mul_pow]
    _ ≤ (b ^ 2) ^ s * (max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) * sobA L g 0 ^ (s - k) *
          sobA L g s ^ k) := by gcongr
    _ ≤ (b ^ 2) ^ s * (max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) *
          (a ^ 2 * sobA L f 0) ^ (s - k) * (a ^ 2 * sobA L f s) ^ k) := by
        have := sobA_nonneg L g 0
        have := sobA_nonneg L g s
        gcongr
        · exact h2 0
        · exact h2 s
    _ = interpConst V ι k s * sobA L f 0 ^ (s - k) * sobA L f s ^ k := by
        unfold interpConst
        rw [← ha, ← hb]
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_pow]
        have hsk : 2 * (s - k) + 2 * k = 2 * s := by omega
        rw [show b ^ (2 * s) * (max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) *
            (a ^ (2 * (s - k)) * sobA L f 0 ^ (s - k)) * (a ^ (2 * k) * sobA L f s ^ k)) =
            (a ^ (2 * (s - k)) * a ^ (2 * k)) * b ^ (2 * s) *
              max 1 (Fintype.card ι : ℝ) ^ (k * s.choose 2) * sobA L f 0 ^ (s - k) *
              sobA L f s ^ k by ring, ← pow_add, hsk]

/-- **Interpolation with real exponents**: if `∫|f|² ≤ ε²` and `∫ pw f s ≤ M²` (`0 < s`,
`k ≤ s`), then `∫ pw f k ≤ C^{1/s} M^{2k/s} (ε^{1 - k/s})²`. -/
theorem sobA_le_rpow {L : ℝ} (hL : 0 < L) {f : (ι → ℝ) → V} (hf : ContDiff ℝ ∞ f)
    (hper : IsPer L f) {k s : ℕ} (hks : k ≤ s) (hs : 0 < s) {ε M : ℝ} (hε : 0 ≤ ε)
    (hM : 0 ≤ M) (h0 : sobA L f 0 ≤ ε ^ 2) (hS : sobA L f s ≤ M ^ 2) :
    sobA L f k ≤ interpConst V ι k s ^ (1 / (s : ℝ)) * M ^ (2 * (k : ℝ) / s) *
      (ε ^ (1 - (k : ℝ) / s)) ^ 2 := by
  have hI := sobA_interp_normed hL hf hper hks
  have hC := interpConst_nonneg (V := V) (ι := ι) k s
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hfk := sobA_nonneg L f k
  have hb : sobA L f k ^ s ≤ interpConst V ι k s * (ε ^ 2) ^ (s - k) * (M ^ 2) ^ k := by
    refine hI.trans ?_
    have := sobA_nonneg L f 0
    have := sobA_nonneg L f s
    gcongr
  have hroot : sobA L f k = (sobA L f k ^ s) ^ (1 / (s : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hfk, mul_one_div_cancel hsR.ne', Real.rpow_one]
  rw [hroot]
  refine (Real.rpow_le_rpow (by positivity) hb (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC (by positivity)]
  have e1 : ((ε ^ 2) ^ (s - k)) ^ (1 / (s : ℝ)) = (ε ^ (1 - (k : ℝ) / s)) ^ 2 := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hε, ← Real.rpow_natCast (ε ^ _) 2,
      ← Real.rpow_mul hε]
    congr 1
    push_cast [Nat.cast_sub hks]
    field_simp
  have e2 : ((M ^ 2) ^ k) ^ (1 / (s : ℝ)) = M ^ (2 * (k : ℝ) / s) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hM]
    congr 1
    push_cast
    field_simp
  rw [e1, e2]
  ring

end Normed

end

end RenewalGeometry.PeriodicSobInterp
