/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridSobolevInequality

/-!
# Discrete Hodge theory on the periodic grid `(ℤ/n)^d`: the co-closed primitive of a closed
  zero-mean two-form
  (`lem:determinant-Hodge-stability`, eq. `eq:determinant-Hodge-primitive`,
  `eq:determinant-Hodge-bounds`; Einstein–SM action closure)

Setting.  The periodic grid `ι → ZMod n` (`d = card ι` directions, unit steps
`gridStep i = e_i`), real scalars.  Unscaled operators (lattice units):
* `fwd i g x = g(x + e_i) - g x`, `bwd i g x = g x - g(x - e_i)`;
* `lap g = Σ_i bwd_i fwd_i g` (`= -h² Δ_h` on functions; on forms the periodic cubical
  Laplacian `Δ_h = d_h δ_h + δ_h d_h` acts componentwise as the scalar one);
* for a one-form `a x μ` and a two-form `φ x μ ν`: `curl a x μ ν = a x μ + a(x+e_μ) ν -
  a(x+e_ν) μ - a x ν` (`= h (d_h a)_{μν}`), `div a x = Σ_μ (a x μ - a(x-e_μ) μ)`
  (`= -h δ_h a`), and the cube sum `cubeSum φ x μ ν κ` (`= h (d_h φ)_{μνκ}`); these coincide
  definitionally with `DeterminantFlux.gridCurl`, `gridDiv`, `cubeSum`.

Results.
* `lapInv` — the inverse of `lap` on mean-zero functions (`Δ_h^†`, vanishing on the constant
  mode), obtained from injectivity of `g ↦ lap g + Σ g` and finite dimension;
  `lap_lapInv`, `sum_lapInv`, `lapInv_unique`, `lapInv_fwd`.
* `eq_const_of_fwd_eq_zero`, `sum_mul_lap` — the kernel of `lap` is the constants.
* `antisymm_of_closed_meanZero` — a closed zero-mean two-form is antisymmetric.
* `hodgePrimitive φ = Σ_κ bwd_κ (lapInv φ_{κ·})` (`= δ Δ^† φ` in lattice units) and
  `hodgePrimitive_curl`, `hodgePrimitive_div`, `sum_hodgePrimitive`: for closed zero-mean `φ`,
  `curl a = φ`, `div a = 0`, `Σ_x a = 0`; `eq_zero_of_curl_div_sum` — uniqueness.
* Scaled (`a⁰ = h · hodgePrimitive f = δ_h Δ_h^† f`, mesh `h`): `hodge_stability_exact` —
  `d_h a⁰ = f`, `δ_h a⁰ = 0`, `\bar{a⁰} = 0`, `‖D^+ a⁰‖_{2,h} = ‖f‖_{2,h}` exactly, and in four
  dimensions `L⁻¹ ‖a⁰_ν‖_{2,h} + ‖a⁰_ν‖_{4,h} ≤ (6 + 5√2) ‖f‖_{2,h}` (`L = n h`) for every
  component, uniformly in `n`.
-/

open Finset

namespace RenewalGeometry.GridHodge

open GridSobolev

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

/-! ### Scalar difference operators and the lattice Laplacian -/

/-- Unscaled forward difference `g(x + e_i) - g(x)`. -/
def fwd (i : ι) (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) : ℝ := g (x + gridStep i) - g x

/-- Unscaled backward difference `g(x) - g(x - e_i)`. -/
def bwd (i : ι) (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) : ℝ := g x - g (x - gridStep i)

/-- The lattice Laplacian `lap g = Σ_i (g(x+e_i) - 2 g(x) + g(x-e_i)) = Σ_i bwd_i fwd_i g`. -/
def lap (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) : ℝ := ∑ i, (fwd i g x - bwd i g x)

omit [Fintype ι] [NeZero n] in
theorem bwd_fwd (i : ι) (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) :
    bwd i (fwd i g) x = fwd i g x - bwd i g x := by
  simp only [bwd, fwd, sub_add_cancel]

omit [NeZero n] in
theorem lap_eq_sum_bwd_fwd (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) :
    lap g x = ∑ i, bwd i (fwd i g) x := by
  simp only [lap, bwd_fwd]

omit [Fintype ι] [NeZero n] in
theorem fwd_bwd_comm (i j : ι) (g : (ι → ZMod n) → ℝ) :
    fwd i (bwd j g) = bwd j (fwd i g) := by
  funext x; simp only [fwd, bwd]
  rw [show x + gridStep i - gridStep j = x - gridStep j + gridStep i by abel]; ring

omit [Fintype ι] [NeZero n] in
theorem fwd_fwd_comm (i j : ι) (g : (ι → ZMod n) → ℝ) :
    fwd i (fwd j g) = fwd j (fwd i g) := by
  funext x; simp only [fwd]
  rw [show x + gridStep i + gridStep j = x + gridStep j + gridStep i by abel]; ring

omit [Fintype ι] [NeZero n] in
theorem bwd_bwd_comm (i j : ι) (g : (ι → ZMod n) → ℝ) :
    bwd i (bwd j g) = bwd j (bwd i g) := by
  funext x; simp only [bwd]
  rw [show x - gridStep i - gridStep j = x - gridStep j - gridStep i by abel]; ring

omit [NeZero n] in
theorem lap_fwd_comm (i : ι) (g : (ι → ZMod n) → ℝ) : lap (fwd i g) = fwd i (lap g) := by
  funext x
  simp only [lap, fwd, bwd, sum_sub_distrib]
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [show x + gridStep j + gridStep i = x + gridStep i + gridStep j by abel,
    show x - gridStep j + gridStep i = x + gridStep i - gridStep j by abel]
  ring

omit [Fintype ι] [NeZero n] in
theorem fwd_add (i : ι) (f g : (ι → ZMod n) → ℝ) : fwd i (f + g) = fwd i f + fwd i g := by
  funext x; simp only [fwd, Pi.add_apply]; ring

omit [Fintype ι] [NeZero n] in
theorem fwd_sub (i : ι) (f g : (ι → ZMod n) → ℝ) : fwd i (f - g) = fwd i f - fwd i g := by
  funext x; simp only [fwd, Pi.sub_apply]; ring

omit [Fintype ι] [NeZero n] in
theorem bwd_sub (i : ι) (f g : (ι → ZMod n) → ℝ) : bwd i (f - g) = bwd i f - bwd i g := by
  funext x; simp only [bwd, Pi.sub_apply]; ring

omit [Fintype ι] [NeZero n] in
theorem bwd_neg (i : ι) (f : (ι → ZMod n) → ℝ) : bwd i (-f) = -bwd i f := by
  funext x; simp only [bwd, Pi.neg_apply]; ring

omit [Fintype ι] [NeZero n] in
theorem bwd_smul (i : ι) (c : ℝ) (f : (ι → ZMod n) → ℝ) : bwd i (c • f) = c • bwd i f := by
  funext x; simp only [bwd, Pi.smul_apply, smul_eq_mul]; ring

theorem sum_fwd (i : ι) (g : (ι → ZMod n) → ℝ) : ∑ x, fwd i g x = 0 := by
  simp only [fwd, sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight (gridStep i)) _ _ (fun _ => rfl)

theorem sum_bwd (i : ι) (g : (ι → ZMod n) → ℝ) : ∑ x, bwd i g x = 0 := by
  simp only [bwd, sum_sub_distrib]
  rw [sub_eq_zero]
  exact (Fintype.sum_equiv (Equiv.subRight (gridStep i)) _ _ (fun _ => rfl)).symm

theorem sum_lap (g : (ι → ZMod n) → ℝ) : ∑ x, lap g x = 0 := by
  simp only [lap_eq_sum_bwd_fwd]
  rw [sum_comm]
  exact sum_eq_zero fun i _ => sum_bwd i _

/-- Summation by parts: `Σ_x g lap g = -Σ_i Σ_x (fwd_i g)²`. -/
theorem sum_mul_lap (g : (ι → ZMod n) → ℝ) :
    ∑ x, g x * lap g x = -∑ i, ∑ x, (fwd i g x) ^ 2 := by
  simp only [lap, mul_sum]
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hsh : ∑ x, g x * bwd i g x = ∑ x, g (x + gridStep i) * fwd i g x := by
    refine (Fintype.sum_equiv (Equiv.addRight (gridStep i)) _ _ (fun x => ?_)).symm
    simp [bwd, fwd]
  have : ∑ x, g x * (fwd i g x - bwd i g x) =
      ∑ x, g x * fwd i g x - ∑ x, g (x + gridStep i) * fwd i g x := by
    rw [← hsh, ← sum_sub_distrib]; exact sum_congr rfl fun x _ => by ring
  rw [this, ← sum_sub_distrib, ← sum_neg_distrib]
  exact sum_congr rfl fun x _ => by simp only [fwd]; ring

/-- A grid function all of whose forward differences vanish is constant. -/
theorem eq_const_of_fwd_eq_zero (g : (ι → ZMod n) → ℝ) (hg : ∀ i x, fwd i g x = 0)
    (x : ι → ZMod n) : g x = g 0 := by
  have hstep : ∀ i y, g (y + gridStep i) = g y := fun i y => by
    have := hg i y; simp only [fwd] at this; linarith
  have hk : ∀ i (k : ℕ) y, g (y + k • gridStep i) = g y := by
    intro i k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [succ_nsmul, ← add_assoc, hstep, ih]
  have hs : ∀ (s : Finset ι) y, g (y + ∑ i ∈ s, (x i).val • gridStep i) = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert j s hj ih => intro y; rw [sum_insert hj, ← add_assoc, ih, hk]
  have hx : x = ∑ i, (x i).val • (gridStep i : ι → ZMod n) := by
    conv_lhs => rw [← univ_sum_single x]
    exact sum_congr rfl fun i _ => single_eq_val_nsmul x i
  have := hs univ 0
  rwa [zero_add, ← hx] at this

/-- The kernel of `lap` on mean-zero functions is trivial. -/
theorem eq_zero_of_lap_eq_zero (g : (ι → ZMod n) → ℝ) (hg : ∀ x, lap g x = 0)
    (hs : ∑ x, g x = 0) : g = 0 := by
  have h1 : ∑ i, ∑ x, (fwd i g x) ^ 2 = 0 := by
    have := sum_mul_lap g
    simp only [hg, mul_zero, sum_const_zero] at this
    linarith
  have h2 : ∀ i x, fwd i g x = 0 := by
    intro i x
    have hi := (sum_eq_zero_iff_of_nonneg fun i _ =>
      sum_nonneg fun x _ => sq_nonneg (fwd i g x)).1 h1 i (mem_univ i)
    have := (sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg (fwd i g x)).1 hi x (mem_univ x)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hc := eq_const_of_fwd_eq_zero g h2
  have h3 : ∑ x : ι → ZMod n, g x = Fintype.card (ι → ZMod n) * g 0 := by
    rw [sum_congr rfl fun x _ => hc x, sum_const, card_univ, nsmul_eq_mul]
  have hN : (0 : ℝ) < Fintype.card (ι → ZMod n) := by exact_mod_cast Fintype.card_pos
  have h0 : g 0 = 0 := by
    rw [hs] at h3
    exact (mul_eq_zero.1 h3.symm).resolve_left hN.ne'
  funext x; rw [hc, h0]; rfl

omit [NeZero n] in
theorem lap_add (f g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) :
    lap (f + g) x = lap f x + lap g x := by
  simp only [lap, fwd, bwd, Pi.add_apply]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

omit [NeZero n] in
theorem lap_smul (c : ℝ) (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) :
    lap (c • g) x = c * lap g x := by
  simp only [lap, fwd, bwd, Pi.smul_apply, smul_eq_mul]
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- The injective endomorphism `g ↦ lap g + Σ g` (adding the constant mode). -/
def lapShift : ((ι → ZMod n) → ℝ) →ₗ[ℝ] ((ι → ZMod n) → ℝ) where
  toFun g := fun x => lap g x + ∑ y, g y
  map_add' f g := by
    funext x
    simp only [lap_add, Pi.add_apply, sum_add_distrib]
    ring
  map_smul' c g := by
    funext x
    simp only [lap_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_sum]
    ring

theorem lapShift_apply (g : (ι → ZMod n) → ℝ) (x : ι → ZMod n) :
    lapShift g x = lap g x + ∑ y, g y := rfl

theorem sum_lapShift (g : (ι → ZMod n) → ℝ) :
    ∑ x, lapShift g x = Fintype.card (ι → ZMod n) * ∑ y, g y := by
  simp only [lapShift_apply, sum_add_distrib, sum_lap, sum_const, card_univ, nsmul_eq_mul,
    zero_add]

theorem lapShift_injective : Function.Injective (lapShift (ι := ι) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hN : (0 : ℝ) < Fintype.card (ι → ZMod n) := by exact_mod_cast Fintype.card_pos
  have hs : ∑ y, g y = 0 := by
    have := sum_lapShift g
    rw [hg] at this
    simp only [Pi.zero_apply, sum_const_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hN.ne'
  refine eq_zero_of_lap_eq_zero g (fun x => ?_) hs
  have := congrFun hg x
  rw [lapShift_apply, hs, add_zero] at this
  exact this

/-- The lattice Laplacian as a linear automorphism (`lap + constant mode`). -/
def lapShiftEquiv : ((ι → ZMod n) → ℝ) ≃ₗ[ℝ] ((ι → ZMod n) → ℝ) :=
  LinearEquiv.ofInjectiveEndo lapShift lapShift_injective

/-- `lapInv = Δ^†` in lattice units: the inverse of `lap` on mean-zero functions, vanishing
on the constant mode (`lapInv f` is the unique mean-zero `g` with `lap g = f - \bar f`). -/
def lapInv : ((ι → ZMod n) → ℝ) →ₗ[ℝ] ((ι → ZMod n) → ℝ) :=
  (lapShiftEquiv (ι := ι) (n := n)).symm.toLinearMap

theorem lapShift_lapInv (f : (ι → ZMod n) → ℝ) : lapShift (lapInv f) = f :=
  (lapShiftEquiv (ι := ι) (n := n)).apply_symm_apply f

/-- `lapInv f` has mean zero when `f` does. -/
theorem sum_lapInv (f : (ι → ZMod n) → ℝ) (hf : ∑ x, f x = 0) : ∑ x, lapInv f x = 0 := by
  have hN : (0 : ℝ) < Fintype.card (ι → ZMod n) := by exact_mod_cast Fintype.card_pos
  have := sum_lapShift (lapInv f)
  rw [lapShift_lapInv, hf] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hN.ne'

/-- `lap (lapInv f) = f` for mean-zero `f`. -/
theorem lap_lapInv (f : (ι → ZMod n) → ℝ) (hf : ∑ x, f x = 0) (x : ι → ZMod n) :
    lap (lapInv f) x = f x := by
  have := congrFun (lapShift_lapInv f) x
  rwa [lapShift_apply, sum_lapInv f hf, add_zero] at this

/-- Uniqueness: a mean-zero solution of `lap g = f` is `lapInv f`. -/
theorem lapInv_unique (f g : (ι → ZMod n) → ℝ) (hg : ∀ x, lap g x = f x)
    (hs : ∑ x, g x = 0) : lapInv f = g := by
  have : lapShift g = f := by funext x; rw [lapShift_apply, hs, add_zero, hg]
  rw [← this]
  exact (lapShiftEquiv (ι := ι) (n := n)).symm_apply_apply g

/-- `lapInv` commutes with forward differences on mean-zero data. -/
theorem lapInv_fwd (i : ι) (f : (ι → ZMod n) → ℝ) (hf : ∑ x, f x = 0) :
    lapInv (fwd i f) = fwd i (lapInv f) := by
  refine lapInv_unique _ _ (fun x => ?_) (sum_fwd i _)
  rw [lap_fwd_comm]
  simp only [fwd, lap_lapInv f hf]

/-! ### One- and two-forms -/

/-- The discrete curl `curl a x μ ν = a_μ(x) + a_ν(x+e_μ) - a_μ(x+e_ν) - a_ν(x)`
(`= h (d_h a)_{μν}(x)`; definitionally `DeterminantFlux.gridCurl`). -/
def curl (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν : ι) : ℝ :=
  a x μ + a (x + gridStep μ) ν - a (x + gridStep ν) μ - a x ν

/-- The backward divergence `div a x = Σ_μ (a_μ(x) - a_μ(x - e_μ))` (`= -h δ_h a`;
definitionally `DeterminantFlux.gridDiv`). -/
def div (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) : ℝ :=
  ∑ μ, (a x μ - a (x - gridStep μ) μ)

/-- The real cube sum of a two-form (`= h (d_h φ)_{μνκ}`; definitionally
`DeterminantFlux.cubeSum`). -/
def cubeSum (φ : (ι → ZMod n) → ι → ι → ℝ) (x : ι → ZMod n) (μ ν κ : ι) : ℝ :=
  φ (x + gridStep μ) ν κ - φ x ν κ - φ (x + gridStep ν) μ κ + φ x μ κ +
    φ (x + gridStep κ) μ ν - φ x μ ν

/-- The `(μ, ν)` component of a two-form, as a scalar grid function. -/
def comp (φ : (ι → ZMod n) → ι → ι → ℝ) (μ ν : ι) : (ι → ZMod n) → ℝ := fun x => φ x μ ν

/-- A closed two-form with zero-mean components is antisymmetric (the symmetric part has
vanishing differences and zero mean). -/
theorem antisymm_of_closed_meanZero (φ : (ι → ZMod n) → ι → ι → ℝ)
    (hclosed : ∀ x μ ν κ, cubeSum φ x μ ν κ = 0) (hmean : ∀ μ ν, ∑ x, φ x μ ν = 0)
    (x : ι → ZMod n) (μ ν : ι) : φ x ν μ = -φ x μ ν := by
  set s : (ι → ZMod n) → ℝ := fun y => φ y μ ν + φ y ν μ with hs
  have hfwd : ∀ κ y, fwd κ s y = 0 := by
    intro κ y
    have h1 := hclosed y μ ν κ
    have h2 := hclosed y ν μ κ
    simp only [cubeSum] at h1 h2
    simp only [fwd, hs]
    linarith
  have hsum : ∑ y, s y = 0 := by
    simp only [hs, sum_add_distrib, hmean, add_zero]
  have := congrFun (eq_zero_of_lap_eq_zero s (fun y => by
    simp only [lap, fwd, bwd]
    refine sum_eq_zero fun κ _ => ?_
    have h1 := hfwd κ y
    have h2 := hfwd κ (y - gridStep κ)
    simp only [fwd, sub_add_cancel] at h1 h2
    linarith) hsum) x
  simp only [hs, Pi.zero_apply] at this
  linarith

/-- **The Hodge primitive** `a = δ Δ^† φ` in lattice units:
`hodgePrimitive φ x ν = Σ_κ bwd_κ (lapInv φ_{κν})(x)`. -/
def hodgePrimitive (φ : (ι → ZMod n) → ι → ι → ℝ) (x : ι → ZMod n) (ν : ι) : ℝ :=
  ∑ κ, bwd κ (lapInv (comp φ κ ν)) x

section Primitive

variable (φ : (ι → ZMod n) → ι → ι → ℝ)
  (hclosed : ∀ x μ ν κ, cubeSum φ x μ ν κ = 0) (hmean : ∀ μ ν, ∑ x, φ x μ ν = 0)
include hclosed hmean

theorem lapInv_comp_antisymm (μ ν : ι) :
    lapInv (comp φ ν μ) = -lapInv (comp φ μ ν) := by
  have : comp φ ν μ = -comp φ μ ν := by
    funext x; simp only [comp, Pi.neg_apply]
    exact antisymm_of_closed_meanZero φ hclosed hmean x μ ν
  rw [this, map_neg]

/-- The closedness of `φ` passes to `Δ^† φ`. -/
theorem fwd_lapInv_closed (μ ν κ : ι) :
    fwd μ (lapInv (comp φ κ ν)) - fwd ν (lapInv (comp φ κ μ)) =
      fwd κ (lapInv (comp φ μ ν)) := by
  rw [← lapInv_fwd μ (comp φ κ ν) (hmean κ ν), ← lapInv_fwd ν (comp φ κ μ) (hmean κ μ),
    ← lapInv_fwd κ (comp φ μ ν) (hmean μ ν), ← map_sub]
  congr 1
  funext x
  have h := hclosed x μ κ ν
  have ha := antisymm_of_closed_meanZero φ hclosed hmean
  simp only [cubeSum] at h
  simp only [Pi.sub_apply, fwd, comp]
  rw [ha (x + gridStep ν) κ μ, ha x κ μ] at h
  linarith

/-- **`d a = φ`**: the curl of the Hodge primitive of a closed zero-mean two-form is the form. -/
theorem hodgePrimitive_curl (x : ι → ZMod n) (μ ν : ι) :
    curl (hodgePrimitive φ) x μ ν = φ x μ ν := by
  have h1 : curl (hodgePrimitive φ) x μ ν =
      ∑ κ, bwd κ (fwd μ (lapInv (comp φ κ ν)) - fwd ν (lapInv (comp φ κ μ))) x := by
    simp only [curl, hodgePrimitive, bwd_sub, Pi.sub_apply, sum_sub_distrib]
    have e1 : ∀ κ, bwd κ (fwd μ (lapInv (comp φ κ ν))) x =
        bwd κ (lapInv (comp φ κ ν)) (x + gridStep μ) - bwd κ (lapInv (comp φ κ ν)) x := by
      intro κ; rw [← fwd_bwd_comm]; rfl
    have e2 : ∀ κ, bwd κ (fwd ν (lapInv (comp φ κ μ))) x =
        bwd κ (lapInv (comp φ κ μ)) (x + gridStep ν) - bwd κ (lapInv (comp φ κ μ)) x := by
      intro κ; rw [← fwd_bwd_comm]; rfl
    simp only [e1, e2, sum_sub_distrib]
    ring
  rw [h1]
  simp only [fwd_lapInv_closed φ hclosed hmean]
  rw [← lap_eq_sum_bwd_fwd, lap_lapInv (comp φ μ ν) (hmean μ ν)]
  rfl

/-- **`δ a = 0`**: the Hodge primitive is co-closed. -/
theorem hodgePrimitive_div (x : ι → ZMod n) : div (hodgePrimitive φ) x = 0 := by
  have h1 : div (hodgePrimitive φ) x = ∑ μ, ∑ κ, bwd μ (bwd κ (lapInv (comp φ κ μ))) x := by
    simp only [div, hodgePrimitive, ← sum_sub_distrib]
    rfl
  have h2 : ∑ μ, ∑ κ, bwd μ (bwd κ (lapInv (comp φ κ μ))) x =
      -∑ μ, ∑ κ, bwd μ (bwd κ (lapInv (comp φ κ μ))) x := by
    conv_lhs => rw [sum_comm]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun κ _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun μ _ => ?_
    rw [bwd_bwd_comm, lapInv_comp_antisymm φ hclosed hmean, bwd_neg, bwd_neg]
    rfl
  linarith

omit hclosed hmean in
/-- **`\bar a = 0`**: each component of the Hodge primitive has zero mean. -/
theorem sum_hodgePrimitive (ν : ι) : ∑ x, hodgePrimitive φ x ν = 0 := by
  simp only [hodgePrimitive]
  rw [sum_comm]
  exact sum_eq_zero fun κ _ => sum_bwd κ _

end Primitive

omit [Fintype ι] [NeZero n] in
/-- The curl of any periodic one-form is closed. -/
theorem cubeSum_curl (b : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν κ : ι) :
    cubeSum (curl b) x μ ν κ = 0 := by
  simp only [cubeSum, curl]
  rw [show x + gridStep μ + gridStep ν = x + gridStep ν + gridStep μ by abel,
    show x + gridStep μ + gridStep κ = x + gridStep κ + gridStep μ by abel,
    show x + gridStep ν + gridStep κ = x + gridStep κ + gridStep ν by abel]
  ring

/-- The curl of any periodic one-form has zero mean. -/
theorem sum_curl (b : (ι → ZMod n) → ι → ℝ) (μ ν : ι) : ∑ x, curl b x μ ν = 0 := by
  have h1 : ∑ x, b (x + gridStep μ) ν = ∑ x, b x ν :=
    Fintype.sum_equiv (Equiv.addRight (gridStep μ)) _ (fun x => b x ν) (fun _ => rfl)
  have h2 : ∑ x, b (x + gridStep ν) μ = ∑ x, b x μ :=
    Fintype.sum_equiv (Equiv.addRight (gridStep ν)) _ (fun x => b x μ) (fun _ => rfl)
  simp only [curl, sum_sub_distrib, sum_add_distrib, h1, h2]
  ring

/-- **Uniqueness** of the co-closed zero-mean primitive: a one-form with `curl a = 0`,
`div a = 0` and zero-mean components vanishes.  Hence `hodgePrimitive φ` is the only
co-closed, zero-mean primitive of `φ`. -/
theorem eq_zero_of_curl_div_sum [LinearOrder ι] (a : (ι → ZMod n) → ι → ℝ)
    (hc : ∀ x μ ν, curl a x μ ν = 0) (hd : ∀ x, div a x = 0) (hs : ∀ ν, ∑ x, a x ν = 0) :
    a = 0 := by
  have key := periodicHodge_identity_unscaled (gridStep (n := n)) (fun ν x => a x ν)
  have hR : ∀ p : ι × ι, ∑ x, ‖a (x + gridStep p.1) p.2 - a x p.2 -
      (a (x + gridStep p.2) p.1 - a x p.1)‖ ^ 2 = 0 := by
    intro p
    refine sum_eq_zero fun x _ => ?_
    have := hc x p.1 p.2
    simp only [curl] at this
    rw [show a (x + gridStep p.1) p.2 - a x p.2 - (a (x + gridStep p.2) p.1 - a x p.1) = 0 by
      linarith]
    simp
  have hD : ∀ x, ‖∑ μ, (a x μ - a (x - gridStep μ) μ)‖ ^ 2 = 0 := by
    intro x; have := hd x; simp only [div] at this; rw [this]; simp
  simp only [hR, hD, sum_const_zero, add_zero] at key
  have hall : ∀ μ ν x, a (x + gridStep μ) ν - a x ν = 0 := by
    intro μ ν x
    have h1 := (sum_eq_zero_iff_of_nonneg fun μ _ => sum_nonneg fun ν _ =>
      sum_nonneg fun x _ => sq_nonneg ‖a (x + gridStep μ) ν - a x ν‖).1 key μ (mem_univ μ)
    have h2 := (sum_eq_zero_iff_of_nonneg fun ν _ =>
      sum_nonneg fun x _ => sq_nonneg ‖a (x + gridStep μ) ν - a x ν‖).1 h1 ν (mem_univ ν)
    have h3 := (sum_eq_zero_iff_of_nonneg fun x _ =>
      sq_nonneg ‖a (x + gridStep μ) ν - a x ν‖).1 h2 x (mem_univ x)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
  funext x ν
  have hz := eq_zero_of_lap_eq_zero (fun y => a y ν) (fun y => by
    simp only [lap, fwd, bwd]
    refine sum_eq_zero fun κ _ => ?_
    have h1 := hall κ ν y
    have h2 := hall κ ν (y - gridStep κ)
    rw [sub_add_cancel] at h2
    linarith) (hs ν)
  exact congrFun hz x

/-! ### Scaled statement: `lem:determinant-Hodge-stability`, finite identities and bounds -/

section Scaled

/-- `a⁰ = δ_h Δ_h^† f` for a real two-form `f` on the grid of mesh `h`, as a nodal one-form
`ν ↦ (x ↦ a⁰_ν(x))`; in lattice units `a⁰ = h · hodgePrimitive f`. -/
def scaledPrimitive (h : ℝ) (f : (ι → ZMod n) → ι → ι → ℝ) : ι → (ι → ZMod n) → ℝ :=
  fun ν x => h * hodgePrimitive f x ν

variable (f : (ι → ZMod n) → ι → ι → ℝ)
  (hclosed : ∀ x μ ν κ, cubeSum f x μ ν κ = 0) (hmean : ∀ μ ν, ∑ x, f x μ ν = 0)
include hclosed hmean

/-- **`lem:determinant-Hodge-stability`, exact identities.**  For a closed real two-form `f`
with zero-mean components on the periodic grid of mesh `h > 0`, `a⁰ = δ_h Δ_h^† f` satisfies
`d_h a⁰ = f`, `δ_h a⁰ = 0`, `\bar{a⁰} = 0` and `‖D^+ a⁰‖_{2,h} = ‖f‖_{2,h}` exactly, with
`‖D^+a‖²_{2,h} = Σ_{μ,ν} ‖D^+_μ a_ν‖²_{2,h}` and `‖f‖²_{2,h} = Σ_{μ<ν} ‖f_{μν}‖²_{2,h}`. -/
theorem hodge_stability_exact [LinearOrder ι] {h : ℝ} (hh : 0 < h) :
    (∀ x μ ν, periodicHodgeExtD h gridStep (scaledPrimitive h f) μ ν x = f x μ ν) ∧
    (∀ x, periodicHodgeCodiff h gridStep (scaledPrimitive h f) x = 0) ∧
    (∀ ν, ∑ x, scaledPrimitive h f ν x = 0) ∧
    ∑ μ, ∑ ν, periodicHodgeNormSq ι h (periodicHodgeFwd h gridStep μ (scaledPrimitive h f ν)) =
      ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        periodicHodgeNormSq ι h (comp f p.1 p.2) := by
  have hext : ∀ x μ ν, periodicHodgeExtD h gridStep (scaledPrimitive h f) μ ν x = f x μ ν := by
    intro x μ ν
    have hc := hodgePrimitive_curl f hclosed hmean x μ ν
    simp only [curl] at hc
    simp only [periodicHodgeExtD, periodicHodgeFwd, scaledPrimitive, smul_eq_mul]
    rw [← hc]
    field_simp
    ring
  have hcod : ∀ x, periodicHodgeCodiff h gridStep (scaledPrimitive h f) x = 0 := by
    intro x
    have hd := hodgePrimitive_div f hclosed hmean x
    simp only [div] at hd
    simp only [periodicHodgeCodiff, periodicHodgeBwd, scaledPrimitive, smul_eq_mul]
    rw [neg_eq_zero, ← mul_sum]
    simp only [← mul_sub, ← mul_sum, hd, mul_zero]
  refine ⟨hext, hcod, fun ν => ?_, ?_⟩
  · simp only [scaledPrimitive, ← mul_sum]
    rw [sum_hodgePrimitive f ν, mul_zero]
  · rw [periodicHodge_identity]
    have h0 : periodicHodgeNormSq ι h (periodicHodgeCodiff h gridStep (scaledPrimitive h f)) =
        0 := by
      simp [periodicHodgeNormSq, hcod]
    rw [h0, add_zero, periodicHodgeExtDNormSq]
    refine sum_congr rfl fun p _ => ?_
    congr 1
    funext x
    exact hext x p.1 p.2

/-- **`lem:determinant-Hodge-stability`, uniform bounds** (`eq:determinant-Hodge-bounds`) in
four dimensions: for every component,
`L⁻¹ ‖a⁰_ν‖_{2,h} + ‖a⁰_ν‖_{4,h} ≤ (6 + 5√2) ‖f‖_{2,h}`, `L = n h`, uniformly in `n` and `h`. -/
theorem hodge_stability_bounds [LinearOrder ι] (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h)
    (ν : ι) :
    ((n : ℝ) * h)⁻¹ * gridL2Norm h (scaledPrimitive h f ν) + gridL4Norm h (scaledPrimitive h f ν)
      ≤ (6 + 5 * √2) * √(∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        periodicHodgeNormSq ι h (comp f p.1 p.2)) := by
  obtain ⟨-, -, hmean0, hnorm⟩ := hodge_stability_exact f hclosed hmean hh
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set F := ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
    periodicHodgeNormSq ι h (comp f p.1 p.2)
  set u := scaledPrimitive h f ν
  have hsq : ∀ w : (ι → ZMod n) → ℝ, gridL2Norm h w ^ 2 = periodicHodgeNormSq ι h w := fun w =>
    Real.sq_sqrt (periodicHodgeNormSq_nonneg hh.le w)
  have hD : √(∑ μ, gridL2Norm h (gridFwd h μ u) ^ 2) ≤ √F := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hnorm]
    simp only [hsq]
    refine sum_le_sum fun μ _ => ?_
    exact single_le_sum (f := fun ν' => periodicHodgeNormSq ι h
      (periodicHodgeFwd h gridStep μ (scaledPrimitive h f ν')))
      (fun ν' _ => periodicHodgeNormSq_nonneg hh.le _) (mem_univ ν)
  obtain ⟨h4, h2⟩ := grid_sobolev_poincare_meanZero_l2 hh hι u (hmean0 ν)
  have hL2 : ((n : ℝ) * h)⁻¹ * gridL2Norm h u ≤ √2 * √F := by
    rw [inv_mul_le_iff₀ (by positivity)]
    calc gridL2Norm h u ≤ √2 * (n * h) * √(∑ μ, gridL2Norm h (gridFwd h μ u) ^ 2) := h2
      _ ≤ √2 * (n * h) * √F := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  have hL4 : gridL4Norm h u ≤ 2 * (3 + 2 * √2) * √F :=
    h4.trans (mul_le_mul_of_nonneg_left hD (by positivity))
  linarith

end Scaled

/-! ### Non-vacuity -/

/-- The curl of any periodic one-form is an admissible input (closed, zero mean); in particular
the hypotheses of `hodge_stability_exact` hold for `f = curl b`, and its primitive reproduces
`f`. -/
theorem hodgePrimitive_curl_curl (b : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν : ι) :
    curl (hodgePrimitive (curl b)) x μ ν = curl b x μ ν :=
  hodgePrimitive_curl (curl b) (cubeSum_curl b) (sum_curl b) x μ ν

/-- A nonzero admissible two-form on `(ℤ/3)⁴`: the curl of the one-form
`b_0(x) = [x_1 = 0]`, `b_μ = 0` for `μ ≠ 0`, has `(curl b)_{01}(0) = 1`; its Hodge primitive
therefore is a nonzero co-closed primitive. -/
example : curl (hodgePrimitive (curl (fun (x : Fin 4 → ZMod 3) (μ : Fin 4) =>
    if μ = 0 ∧ x 1 = 0 then (1 : ℝ) else 0))) 0 0 1 = 1 := by
  rw [hodgePrimitive_curl_curl]
  simp [curl, gridStep]

end

end RenewalGeometry.GridHodge
