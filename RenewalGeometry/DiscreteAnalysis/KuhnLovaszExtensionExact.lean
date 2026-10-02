/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.DiscreteCoordinateDifferenceBoundExact

/-!
# The Freudenthal–Kuhn (Lovász) piecewise-affine extension of lattice data

Infrastructure for `lem:A3-periodic-triangulation` (paper `predictive_spectral_geometry`).

For lattice data `g : ℤⁿ → ℝ` the *Kuhn extension*

  `kuhnExt g u = ∫₀¹ g(⌊u + s𝟙⌋) ds`   (componentwise floor)

is the continuous piecewise-affine interpolant of `g` on the Freudenthal–Kuhn triangulation of
`ℝⁿ` (the simplices `k + K_σ`, `K_σ = conv{0, e_{σ0}, e_{σ0} + e_{σ1}, …, 𝟙}`).  The integral
formula makes the analytic estimates elementary:

* `integral_floor_add`: `∫₀¹ ⌊a + s⌋ ds = a`;
* `kuhnExt_intCast`: the extension interpolates `g` at lattice points;
* `kuhnExt_add_intCast`: translation covariance (periodicity is inherited);
* `abs_kuhnExt_add_single_sub_le`, `abs_kuhnExt_sub_le`: if every unit step `k ↦ k + eᵢ`
  changes `g` by at most `Eᵢ`, then `|kuhnExt g v - kuhnExt g u| ≤ Σᵢ Eᵢ |vᵢ - uᵢ|`;
* `abs_kuhnExt_sub_floor_le`: `|kuhnExt g u - g ⌊u⌋| ≤ Σᵢ Eᵢ` (cell comparison).

In dimension three (`Fin 3`) we prove that this is the Kuhn piecewise-affine interpolant:

* `mem_kuhnSimplex_iff`: `k + K_σ = {u : 1 ≥ t_{σ0} ≥ t_{σ1} ≥ t_{σ2} ≥ 0}`, `t = u - k`;
* `exists_mem_kuhnSimplex`: the simplices cover `ℝ³`;
* `mem_convexHull_common_vertices`: two simplices meet in the convex hull of their common
  vertices (face-to-face compatibility, so the simplices form a triangulation);
* `mem_kuhnSimplex_of_near_center`, `abs_sub_le_one_of_mem_kuhnSimplex`: each simplex contains
  the sup-ball of radius `1/8` about its barycentre and has coordinate oscillation at most `1`
  (uniform shape regularity);
* `kuhnVertex_eq_add_steps`: consecutive-chain description of the edges (at most three unit
  steps between any two vertices of a simplex);
* `kuhnExt_eq_barycentric`: on `k + K_σ`, `kuhnExt g` is the affine barycentric formula
  `(1 - t_{σ0}) g(v₀) + (t_{σ0} - t_{σ1}) g(v₁) + (t_{σ1} - t_{σ2}) g(v₂) + t_{σ2} g(v₃)`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RenewalGeometry.KuhnLovaszExtension

open DiscreteCoordinateDifferenceBound

noncomputable section

/-! ### One-dimensional facts -/

theorem integral_eq_mul_of_eqOn_Ioo {F : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ s ∈ Ioo a b, F s = c) : ∫ s in a..b, F s = (b - a) * c := by
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ b := by
    rw [ae_iff]
    simp
  have heq : ∫ s in a..b, F s = ∫ _s in a..b, c := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with s hs hsI
    rw [uIoc_of_le hab] at hsI
    exact h s ⟨hsI.1, lt_of_le_of_ne hsI.2 hs⟩
  rw [heq, intervalIntegral.integral_const, smul_eq_mul]

theorem floor_add_eq_or (a s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ⌊a + s⌋ = ⌊a⌋ ∨ ⌊a + s⌋ = ⌊a⌋ + 1 := by
  have h1 : ⌊a⌋ ≤ ⌊a + s⌋ := Int.floor_mono (by linarith [hs.1])
  have h2 : ⌊a + s⌋ ≤ ⌊a⌋ + 1 := by
    rw [← Int.floor_add_one]
    exact Int.floor_mono (by linarith [hs.2])
  omega

theorem intervalIntegrable_floor_add (a : ℝ) :
    IntervalIntegrable (fun s : ℝ => (⌊a + s⌋ : ℝ)) volume 0 1 := by
  apply Monotone.intervalIntegrable
  intro x y hxy
  show (⌊a + x⌋ : ℝ) ≤ ⌊a + y⌋
  exact_mod_cast Int.floor_mono (by linarith)

/-- `∫₀¹ ⌊a + s⌋ ds = a`. -/
theorem integral_floor_add (a : ℝ) : ∫ s in (0 : ℝ)..1, (⌊a + s⌋ : ℝ) = a := by
  set c : ℝ := ⌊a⌋ + 1 - a with hc
  have hc0 : 0 < c := by have := Int.lt_floor_add_one a; linarith
  have hc1 : c ≤ 1 := by have := Int.floor_le a; linarith
  have hI := intervalIntegrable_floor_add a
  have hI1 : IntervalIntegrable (fun s : ℝ => (⌊a + s⌋ : ℝ)) volume 0 c :=
    hI.mono_set (by rw [uIcc_of_le hc0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hc1)
  have hI2 : IntervalIntegrable (fun s : ℝ => (⌊a + s⌋ : ℝ)) volume c 1 :=
    hI.mono_set (by rw [uIcc_of_le hc1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hc0.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
    integral_eq_mul_of_eqOn_Ioo hc0.le (c := (⌊a⌋ : ℝ)) ?_,
    integral_eq_mul_of_eqOn_Ioo hc1 (c := ((⌊a⌋ + 1 : ℤ) : ℝ)) ?_]
  · push_cast; rw [hc]; ring
  · intro s hs
    congr 1
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith [hs.1, hs.2, Int.floor_le a, Int.lt_floor_add_one a]
  · intro s hs
    congr 1
    rw [Int.floor_eq_iff]
    constructor <;> linarith [hs.1, hs.2, Int.floor_le a]

/-- `∫₀¹ |⌊a + δ + s⌋ - ⌊a + s⌋| ds = |δ|`. -/
theorem integral_abs_floor_sub (a δ : ℝ) :
    ∫ s in (0 : ℝ)..1, |((⌊a + δ + s⌋ : ℝ) - ⌊a + s⌋)| = |δ| := by
  have hsub : ∫ s in (0 : ℝ)..1, ((⌊a + δ + s⌋ : ℝ) - ⌊a + s⌋) = δ := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_floor_add (a + δ))
      (intervalIntegrable_floor_add a), integral_floor_add, integral_floor_add]
    ring
  rcases le_total 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ]
    refine Eq.trans ?_ hsub
    apply intervalIntegral.integral_congr
    intro s _
    apply abs_of_nonneg
    rw [sub_nonneg]
    exact_mod_cast Int.floor_mono (by linarith)
  · rw [abs_of_nonpos hδ]
    refine Eq.trans ?_ (congrArg Neg.neg hsub)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    apply abs_of_nonpos
    rw [sub_nonpos]
    exact_mod_cast Int.floor_mono (by linarith)

/-! ### The Kuhn extension in dimension `n` -/

variable {n : ℕ}

/-- The lattice point `⌊u + s𝟙⌋`. -/
def shiftFloor (u : Fin n → ℝ) (s : ℝ) : Fin n → ℤ := fun i => ⌊u i + s⌋

/-- The componentwise floor `⌊u⌋`. -/
def floorVec (u : Fin n → ℝ) : Fin n → ℤ := fun i => ⌊u i⌋

/-- The Kuhn (Lovász) extension `∫₀¹ g(⌊u + s𝟙⌋) ds` of lattice data `g`. -/
def kuhnExt (g : (Fin n → ℤ) → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, g (shiftFloor u s)

theorem measurable_shiftFloor (u : Fin n → ℝ) : Measurable (shiftFloor u) := by
  apply measurable_pi_lambda
  intro i
  exact Int.measurable_floor.comp (measurable_const.add measurable_id)

/-- On `[0,1]`, `⌊u + s𝟙⌋ = ⌊u⌋ + ε` with `ε ∈ {0,1}ⁿ`. -/
theorem exists_shiftFloor_eq (u : Fin n → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ ε : Fin n → Fin 2, shiftFloor u s = fun i => floorVec u i + ((ε i : ℕ) : ℤ) := by
  have h := fun i => floor_add_eq_or (u i) s hs
  refine ⟨fun i => if ⌊u i + s⌋ = ⌊u i⌋ then 0 else 1, ?_⟩
  funext i
  simp only [shiftFloor, floorVec]
  split_ifs with hi
  · simp [hi]
  · rcases h i with h' | h'
    · exact absurd h' hi
    · simp [h']

theorem intervalIntegrable_comp_shiftFloor (g : (Fin n → ℤ) → ℝ) (u : Fin n → ℝ) :
    IntervalIntegrable (fun s => g (shiftFloor u s)) volume 0 1 := by
  set B : ℝ := ∑ ε : Fin n → Fin 2, |g (fun i => floorVec u i + ((ε i : ℕ) : ℤ))|
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := B) (by simp)
    ((measurable_of_countable g).comp (measurable_shiftFloor u)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun s hs => ?_
  obtain ⟨ε, hε⟩ := exists_shiftFloor_eq u (Ioc_subset_Icc_self hs)
  rw [hε, Real.norm_eq_abs]
  exact Finset.single_le_sum
    (f := fun ε : Fin n → Fin 2 => |g (fun i => floorVec u i + ((ε i : ℕ) : ℤ))|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ ε)

/-- The Kuhn extension interpolates the lattice data. -/
theorem kuhnExt_intCast (g : (Fin n → ℤ) → ℝ) (k : Fin n → ℤ) :
    kuhnExt g (fun i => (k i : ℝ)) = g k := by
  unfold kuhnExt
  rw [integral_eq_mul_of_eqOn_Ioo zero_le_one (c := g k), sub_zero, one_mul]
  intro s hs
  congr 1
  funext i
  simp only [shiftFloor]
  rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨hs.1.le, hs.2⟩, add_zero]

/-- Translation covariance: `kuhnExt g (u + z) = kuhnExt (g (· + z)) u`. -/
theorem kuhnExt_add_intCast (g : (Fin n → ℤ) → ℝ) (u : Fin n → ℝ) (z : Fin n → ℤ) :
    kuhnExt g (u + fun i => (z i : ℝ)) = kuhnExt (fun k => g (k + z)) u := by
  unfold kuhnExt
  apply intervalIntegral.integral_congr
  intro s _
  simp only
  congr 1
  funext i
  simp only [shiftFloor, Pi.add_apply]
  rw [add_right_comm, Int.floor_add_intCast]

/-- Periodic lattice data have a periodic Kuhn extension. -/
theorem kuhnExt_add_intCast_of_periodic (g : (Fin n → ℤ) → ℝ) (z : Fin n → ℤ)
    (hg : ∀ k, g (k + z) = g k) (u : Fin n → ℝ) :
    kuhnExt g (u + fun i => (z i : ℝ)) = kuhnExt g u := by
  rw [kuhnExt_add_intCast]
  simp only [hg]

/-- **One-direction Lipschitz bound.** -/
theorem abs_kuhnExt_add_single_sub_le (g : (Fin n → ℤ) → ℝ) (i : Fin n) (E : ℝ)
    (hstep : ∀ k, |g (k + Pi.single i 1) - g k| ≤ E) (u : Fin n → ℝ) (δ : ℝ) :
    |kuhnExt g (u + Pi.single i δ) - kuhnExt g u| ≤ E * |δ| := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (hstep 0)
  let m : ℝ → ℤ := fun s => ⌊u i + δ + s⌋ - ⌊u i + s⌋
  have hshift : ∀ s, shiftFloor (u + Pi.single i δ) s =
      shiftFloor u s + m s • (Pi.single i 1 : Fin n → ℤ) := by
    intro s
    funext j
    by_cases hj : j = i
    · subst hj
      simp [shiftFloor, m]
    · simp [shiftFloor, hj]
  have hpt : ∀ s, |g (shiftFloor (u + Pi.single i δ) s) - g (shiftFloor u s)| ≤
      E * |((⌊u i + δ + s⌋ : ℝ) - ⌊u i + s⌋)| := by
    intro s
    rw [hshift]
    refine (abs_difference_zsmul_le g _ E hstep (m s) (shiftFloor u s)).trans ?_
    rw [mul_comm, Nat.cast_natAbs, Int.cast_abs]
    simp [m]
  have hbound : IntervalIntegrable
      (fun s : ℝ => E * |((⌊u i + δ + s⌋ : ℝ) - ⌊u i + s⌋)|) volume 0 1 :=
    (((intervalIntegrable_floor_add (u i + δ)).sub
      (intervalIntegrable_floor_add (u i))).abs).const_mul E
  unfold kuhnExt
  rw [← intervalIntegral.integral_sub (intervalIntegrable_comp_shiftFloor g _)
    (intervalIntegrable_comp_shiftFloor g u)]
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, E * |((⌊u i + δ + s⌋ : ℝ) - ⌊u i + s⌋)| := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Filter.Eventually.of_forall fun s _ => by
          simpa only [Real.norm_eq_abs] using hpt s) hbound
    _ = E * |δ| := by rw [intervalIntegral.integral_const_mul, integral_abs_floor_sub]

/-- **Lipschitz bound of the Kuhn extension** in terms of the unit-step oscillations. -/
theorem abs_kuhnExt_sub_le (g : (Fin n → ℤ) → ℝ) (E : Fin n → ℝ)
    (hstep : ∀ i k, |g (k + Pi.single i 1) - g k| ≤ E i) (u v : Fin n → ℝ) :
    |kuhnExt g v - kuhnExt g u| ≤ ∑ i, E i * |v i - u i| := by
  have key : ∀ s : Finset (Fin n),
      |kuhnExt g (u + ∑ i ∈ s, Pi.single i (v i - u i)) - kuhnExt g u| ≤
        ∑ i ∈ s, E i * |v i - u i| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← add_assoc, add_right_comm u]
      set X : Fin n → ℝ := u + ∑ j ∈ s, Pi.single j (v j - u j) with hX
      have h1 := abs_kuhnExt_add_single_sub_le g i (E i) (hstep i) X (v i - u i)
      have h2 := abs_sub_le (kuhnExt g (X + Pi.single i (v i - u i))) (kuhnExt g X)
        (kuhnExt g u)
      linarith
  have hv : u + ∑ i, Pi.single i (v i - u i) = v := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h := key Finset.univ
  rwa [hv] at h

/-- **Comparison with the floor (cell) value.** -/
theorem abs_kuhnExt_sub_floor_le (g : (Fin n → ℤ) → ℝ) (E : Fin n → ℝ)
    (hstep : ∀ i k, |g (k + Pi.single i 1) - g k| ≤ E i) (u : Fin n → ℝ) :
    |kuhnExt g u - g (floorVec u)| ≤ ∑ i, E i := by
  have hE : ∀ i, 0 ≤ E i := fun i => (abs_nonneg _).trans (hstep i 0)
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, |g (shiftFloor u s) - g (floorVec u)| ≤ ∑ i, E i := by
    intro s hs
    obtain ⟨ε, hε⟩ := exists_shiftFloor_eq u hs
    have hsum : shiftFloor u s =
        floorVec u + ∑ i, ((ε i : ℕ) : ℤ) • (Pi.single i 1 : Fin n → ℤ) := by
      rw [hε]
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine (abs_difference_sum_zsmul_le g (fun i => Pi.single i 1) E (hstep) _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    have hε1 : (((ε i : ℕ) : ℤ).natAbs : ℝ) ≤ 1 := by
      have := (ε i).isLt
      have h' : ((ε i : ℕ) : ℤ).natAbs = (ε i : ℕ) := Int.natAbs_natCast _
      rw [h']
      exact_mod_cast Nat.lt_succ_iff.mp this
    nlinarith [hE i]
  have hconst : g (floorVec u) = ∫ _s in (0 : ℝ)..1, g (floorVec u) := by simp
  unfold kuhnExt
  rw [hconst, ← intervalIntegral.integral_sub (intervalIntegrable_comp_shiftFloor g u)
    intervalIntegrable_const]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ∑ i, E i) (f := fun s => g (shiftFloor u s) - g (floorVec u)) (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      simpa only [Real.norm_eq_abs] using hpt s (Ioc_subset_Icc_self hs))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

/-! ### The Kuhn triangulation of `ℝ³` -/

/-- The Kuhn vertex `v_m = k + e_{σ 0} + ⋯ + e_{σ (m-1)}`. -/
def kuhnVertex (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (m : ℕ) : Fin 3 → ℤ :=
  fun j => k j + if ((σ.symm j : Fin 3) : ℕ) < m then 1 else 0

/-- The Kuhn vertex as a point of `ℝ³`. -/
def kuhnVertexR (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (m : ℕ) : Fin 3 → ℝ :=
  fun j => (kuhnVertex k σ m j : ℝ)

/-- The Kuhn simplex `k + K_σ = conv{v₀, v₁, v₂, v₃}`. -/
def kuhnSimplex (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (Set.range fun m : Fin 4 => kuhnVertexR k σ m)

/-- Local coordinates `t_a = u_{σ a} - k_{σ a}`. -/
def kuhnCoord (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) (a : Fin 3) : ℝ :=
  u (σ a) - k (σ a)

/-- The ordering `1 ≥ t₀ ≥ t₁ ≥ t₂ ≥ 0` defining `k + K_σ`. -/
def KuhnOrdered (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) : Prop :=
  kuhnCoord k σ u 0 ≤ 1 ∧ kuhnCoord k σ u 1 ≤ kuhnCoord k σ u 0 ∧
    kuhnCoord k σ u 2 ≤ kuhnCoord k σ u 1 ∧ 0 ≤ kuhnCoord k σ u 2

/-- Barycentric weights `(1 - t₀, t₀ - t₁, t₁ - t₂, t₂)`. -/
def kuhnWeights (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![1 - kuhnCoord k σ u 0, kuhnCoord k σ u 0 - kuhnCoord k σ u 1,
    kuhnCoord k σ u 1 - kuhnCoord k σ u 2, kuhnCoord k σ u 2]

variable {k k' : Fin 3 → ℤ} {σ σ' : Equiv.Perm (Fin 3)} {u : Fin 3 → ℝ}

theorem kuhnVertex_apply_perm (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (m : ℕ) (a : Fin 3) :
    kuhnVertex k σ m (σ a) = k (σ a) + if (a : ℕ) < m then 1 else 0 := by
  simp [kuhnVertex]

theorem kuhnCoord_vertex (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (m : ℕ) (a : Fin 3) :
    kuhnCoord k σ (kuhnVertexR k σ m) a = if (a : ℕ) < m then 1 else 0 := by
  simp only [kuhnCoord, kuhnVertexR, kuhnVertex_apply_perm]
  split_ifs <;> push_cast <;> ring

theorem convex_kuhnOrdered (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) :
    Convex ℝ {u | KuhnOrdered k σ u} := by
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  simp only [Set.mem_ofPred_eq, KuhnOrdered, kuhnCoord, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx4 ha, mul_le_mul_of_nonneg_left hy4 hb]

theorem kuhnWeights_nonneg (h : KuhnOrdered k σ u) (m : Fin 4) : 0 ≤ kuhnWeights k σ u m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  fin_cases m <;> simp [kuhnWeights] <;> linarith

theorem sum_kuhnWeights (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) :
    ∑ m, kuhnWeights k σ u m = 1 := by
  simp [kuhnWeights, Fin.sum_univ_four]

theorem sum_kuhnWeights_smul (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) :
    ∑ m, kuhnWeights k σ u m • kuhnVertexR k σ m = u := by
  funext j
  obtain ⟨a, rfl⟩ := σ.surjective j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four, kuhnVertexR,
    kuhnVertex_apply_perm, kuhnWeights, kuhnCoord]
  fin_cases a <;> simp <;> ring

/-- `k + K_σ` is the region `1 ≥ t_{σ0} ≥ t_{σ1} ≥ t_{σ2} ≥ 0`. -/
theorem mem_kuhnSimplex_iff : u ∈ kuhnSimplex k σ ↔ KuhnOrdered k σ u := by
  constructor
  · intro hu
    refine (convexHull_min ?_ (convex_kuhnOrdered k σ)) hu
    rintro _ ⟨m, rfl⟩
    simp only [Set.mem_ofPred_eq, KuhnOrdered, kuhnCoord_vertex]
    fin_cases m <;> simp
  · intro h
    rw [← sum_kuhnWeights_smul k σ u]
    exact (convex_convexHull ℝ _).sum_mem (fun m _ => kuhnWeights_nonneg h m)
      (sum_kuhnWeights k σ u) (fun m _ => subset_convexHull ℝ _ ⟨m, rfl⟩)

/-- The level `#{a : 1 - s ≤ t_a}` of `s` in the chain. -/
def kuhnLevel (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) (s : ℝ) : ℕ :=
  if 1 - s ≤ kuhnCoord k σ u 2 then 3 else if 1 - s ≤ kuhnCoord k σ u 1 then 2
    else if 1 - s ≤ kuhnCoord k σ u 0 then 1 else 0

theorem kuhnLevel_lt_four (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) (u : Fin 3 → ℝ) (s : ℝ) :
    kuhnLevel k σ u s < 4 := by
  unfold kuhnLevel
  split_ifs <;> norm_num

theorem floor_add_unit {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ⌊t + s⌋ = if 1 - s ≤ t then 1 else 0 := by
  split_ifs with h
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

/-- On `k + K_σ`, the lattice point `⌊u + s𝟙⌋` is the Kuhn vertex of level `kuhnLevel`. -/
theorem shiftFloor_eq_kuhnVertex (h : KuhnOrdered k σ u) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    shiftFloor u s = kuhnVertex k σ (kuhnLevel k σ u s) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext j
  obtain ⟨a, rfl⟩ := σ.surjective j
  have hu : u (σ a) + s = ((k (σ a) : ℤ) : ℝ) + (kuhnCoord k σ u a + s) := by
    simp only [kuhnCoord]; ring
  have ha0 : 0 ≤ kuhnCoord k σ u a := by fin_cases a <;> simp <;> linarith
  have ha1 : kuhnCoord k σ u a ≤ 1 := by fin_cases a <;> simp <;> linarith
  rw [shiftFloor, hu, Int.floor_intCast_add, kuhnVertex_apply_perm,
    floor_add_unit ha0 ha1 hs0 hs1]
  congr 1
  unfold kuhnLevel
  fin_cases a <;> simp <;> split_ifs <;> first | rfl | (exfalso; linarith)

theorem kuhnLevel_eq_zero (h : KuhnOrdered k σ u) {s : ℝ} (hs : s < 1 - kuhnCoord k σ u 0) :
    kuhnLevel k σ u s = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold kuhnLevel
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

theorem kuhnLevel_eq_one (h : KuhnOrdered k σ u) {s : ℝ} (hs : 1 - kuhnCoord k σ u 0 < s)
    (hs' : s < 1 - kuhnCoord k σ u 1) : kuhnLevel k σ u s = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold kuhnLevel
  rw [if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]

theorem kuhnLevel_eq_two (_h : KuhnOrdered k σ u) {s : ℝ} (hs : 1 - kuhnCoord k σ u 1 < s)
    (hs' : s < 1 - kuhnCoord k σ u 2) : kuhnLevel k σ u s = 2 := by
  unfold kuhnLevel
  rw [if_neg (by linarith), if_pos (by linarith)]

theorem kuhnLevel_eq_three {s : ℝ} (hs : 1 - kuhnCoord k σ u 2 < s) :
    kuhnLevel k σ u s = 3 := by
  unfold kuhnLevel
  rw [if_pos (by linarith)]

/-- **The Kuhn extension is the barycentric (P1) interpolant on every Kuhn simplex**: on
`k + K_σ` it equals `Σ_m λ_m g(v_m)` with the affine barycentric weights `λ = kuhnWeights`. -/
theorem kuhnExt_eq_barycentric (g : (Fin 3 → ℤ) → ℝ) (hu : u ∈ kuhnSimplex k σ) :
    kuhnExt g u = ∑ m : Fin 4, kuhnWeights k σ u m * g (kuhnVertex k σ m) := by
  have h := mem_kuhnSimplex_iff.mp hu
  have h' := h
  obtain ⟨h1, h2, h3, h4⟩ := h'
  set t := kuhnCoord k σ u with ht
  have hI := intervalIntegrable_comp_shiftFloor g u
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun s => g (shiftFloor u s)) volume a b := by
    intro a b ha hab hb
    exact hI.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)
  have piece : ∀ (a b : ℝ) (m : ℕ), 0 ≤ a → a ≤ b → b ≤ 1 →
      (∀ s ∈ Ioo a b, kuhnLevel k σ u s = m) →
      ∫ s in a..b, g (shiftFloor u s) = (b - a) * g (kuhnVertex k σ m) := by
    intro a b m ha hab hb hlev
    apply integral_eq_mul_of_eqOn_Ioo hab
    intro s hs
    rw [shiftFloor_eq_kuhnVertex h (by linarith [hs.1]) (by linarith [hs.2]), hlev s hs]
  unfold kuhnExt
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 - t 2)
      (hsub 0 _ le_rfl (by linarith) (by linarith))
      (hsub _ 1 (by linarith) (by linarith) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 - t 1)
      (hsub 0 _ le_rfl (by linarith) (by linarith))
      (hsub _ _ (by linarith) (by linarith) (by linarith)),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 - t 0)
      (hsub 0 _ le_rfl (by linarith) (by linarith))
      (hsub _ _ (by linarith) (by linarith) (by linarith)),
    piece 0 (1 - t 0) 0 le_rfl (by linarith) (by linarith)
      (fun s hs => kuhnLevel_eq_zero h hs.2),
    piece (1 - t 0) (1 - t 1) 1 (by linarith) (by linarith) (by linarith)
      (fun s hs => kuhnLevel_eq_one h hs.1 hs.2),
    piece (1 - t 1) (1 - t 2) 2 (by linarith) (by linarith) (by linarith)
      (fun s hs => kuhnLevel_eq_two h hs.1 hs.2),
    piece (1 - t 2) 1 3 (by linarith) (by linarith) le_rfl
      (fun s hs => kuhnLevel_eq_three hs.1)]
  simp only [Fin.sum_univ_four, kuhnWeights, ← ht]
  simp

/-- **Covering.**  Every point of `ℝ³` lies in some Kuhn simplex (`k = ⌊u⌋`, `σ` sorting the
fractional parts decreasingly). -/
theorem exists_mem_kuhnSimplex (u : Fin 3 → ℝ) : ∃ k σ, u ∈ kuhnSimplex k σ := by
  let t : Fin 3 → ℝ := fun i => Int.fract (u i)
  let σ := Tuple.sort (fun i => -t i)
  have hmono : Monotone ((fun i => -t i) ∘ σ) := Tuple.monotone_sort _
  refine ⟨floorVec u, σ, mem_kuhnSimplex_iff.mpr ?_⟩
  have hc : ∀ a, kuhnCoord (floorVec u) σ u a = t (σ a) := by
    intro a
    simp only [kuhnCoord, floorVec, t, Int.fract]
  have h01 := hmono (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := hmono (show (1 : Fin 3) ≤ 2 by decide)
  simp only [Function.comp] at h01 h12
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hc]
  · exact (Int.fract_lt_one _).le
  · linarith
  · linarith
  · exact Int.fract_nonneg _

/-- `⌊u + s𝟙⌋` (`0 ≤ s < 1`) is a vertex of every Kuhn simplex containing `u`. -/
theorem shiftFloor_mem_vertices (hu : u ∈ kuhnSimplex k σ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (fun j => (shiftFloor u s j : ℝ)) ∈ Set.range fun m : Fin 4 => kuhnVertexR k σ m := by
  have h := mem_kuhnSimplex_iff.mp hu
  refine ⟨⟨kuhnLevel k σ u s, kuhnLevel_lt_four k σ u s⟩, ?_⟩
  funext j
  simp [kuhnVertexR, shiftFloor_eq_kuhnVertex h hs0 hs1]

/-- **Face-to-face compatibility.**  Two Kuhn simplices meet in the convex hull of their common
vertices, i.e. in a common face; hence the simplices `k + K_σ` form a triangulation of `ℝ³`. -/
theorem mem_convexHull_common_vertices (hu : u ∈ kuhnSimplex k σ)
    (hu' : u ∈ kuhnSimplex k' σ') :
    u ∈ convexHull ℝ ((Set.range fun m : Fin 4 => kuhnVertexR k σ m) ∩
      Set.range fun m : Fin 4 => kuhnVertexR k' σ' m) := by
  have h := mem_kuhnSimplex_iff.mp hu
  have h' := h
  obtain ⟨h1, h2, h3, h4⟩ := h'
  set t := kuhnCoord k σ u with ht
  have hvert : ∀ (m : Fin 4) (s : ℝ), 0 ≤ s → s < 1 → kuhnLevel k σ u s = m →
      kuhnVertexR k σ m ∈ (Set.range fun m : Fin 4 => kuhnVertexR k σ m) ∩
        Set.range fun m : Fin 4 => kuhnVertexR k' σ' m := by
    intro m s hs0 hs1 hlev
    refine ⟨⟨m, rfl⟩, ?_⟩
    have hv := shiftFloor_mem_vertices hu' hs0 hs1
    have heq : kuhnVertexR k σ m = fun j => (shiftFloor u s j : ℝ) := by
      funext j
      simp [kuhnVertexR, shiftFloor_eq_kuhnVertex h hs0 hs1, hlev]
    rw [heq]
    exact hv
  classical
  have hcm := Finset.centerMass_mem_convexHull
    (Finset.univ.filter fun m : Fin 4 => kuhnWeights k σ u m ≠ 0)
    (w := kuhnWeights k σ u) (z := fun m => kuhnVertexR k σ m)
    (fun m _ => kuhnWeights_nonneg h m)
    (by rw [Finset.sum_filter_ne_zero, sum_kuhnWeights]; norm_num) (by
      intro m hm'
      have hm := (Finset.mem_filter.mp hm').2
      have hpos : 0 < kuhnWeights k σ u m :=
        lt_of_le_of_ne (kuhnWeights_nonneg h m) (Ne.symm hm)
      fin_cases m
      · simp only [kuhnWeights, ← ht] at hpos
        simp at hpos
        exact hvert 0 ((1 - t 0) / 2) (by linarith) (by linarith)
          (kuhnLevel_eq_zero h (by linarith))
      · simp only [kuhnWeights, ← ht] at hpos
        simp at hpos
        exact hvert 1 (1 - (t 0 + t 1) / 2) (by linarith) (by linarith)
          (kuhnLevel_eq_one h (by linarith) (by linarith))
      · simp only [kuhnWeights, ← ht] at hpos
        simp at hpos
        exact hvert 2 (1 - (t 1 + t 2) / 2) (by linarith) (by linarith)
          (kuhnLevel_eq_two h (by linarith) (by linarith))
      · simp only [kuhnWeights, ← ht] at hpos
        simp at hpos
        exact hvert 3 (1 - t 2 / 2) (by linarith) (by linarith)
          (kuhnLevel_eq_three (by linarith)))
  rwa [Finset.centerMass_filter_ne_zero, Finset.centerMass_eq_of_sum_1 _ _ (sum_kuhnWeights k σ u),
    sum_kuhnWeights_smul] at hcm

/-- The barycentre `k + (σ-ordered) (3/4, 1/2, 1/4)` of `k + K_σ`. -/
def kuhnCenter (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) : Fin 3 → ℝ :=
  fun j => (k j : ℝ) + (3 - (((σ.symm j : Fin 3) : ℕ) : ℝ)) / 4

/-- **Uniform fatness.**  Every Kuhn simplex contains the sup-norm ball of radius `1/8` about
its barycentre. -/
theorem mem_kuhnSimplex_of_near_center {v : Fin 3 → ℝ}
    (hv : ∀ j, |v j - kuhnCenter k σ j| < 1 / 8) : v ∈ kuhnSimplex k σ := by
  rw [mem_kuhnSimplex_iff]
  have hc : ∀ a : Fin 3, |kuhnCoord k σ v a - (3 - ((a : ℕ) : ℝ)) / 4| < 1 / 8 := by
    intro a
    have h := hv (σ a)
    have he : kuhnCoord k σ v a - (3 - ((a : ℕ) : ℝ)) / 4 = v (σ a) - kuhnCenter k σ (σ a) := by
      simp [kuhnCoord, kuhnCenter]
      ring
    rw [he]
    exact h
  have h0 := abs_lt.mp (hc 0)
  have h1 := abs_lt.mp (hc 1)
  have h2 := abs_lt.mp (hc 2)
  norm_num at h0 h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- **Uniformly bounded size.**  Two points of one Kuhn simplex differ by at most one in every
coordinate. -/
theorem abs_sub_le_one_of_mem_kuhnSimplex {v w : Fin 3 → ℝ} (hv : v ∈ kuhnSimplex k σ)
    (hw : w ∈ kuhnSimplex k σ) (j : Fin 3) : |v j - w j| ≤ 1 := by
  rw [mem_kuhnSimplex_iff] at hv hw
  obtain ⟨a, rfl⟩ := σ.surjective j
  obtain ⟨v1, v2, v3, v4⟩ := hv
  obtain ⟨w1, w2, w3, w4⟩ := hw
  have hva : 0 ≤ kuhnCoord k σ v a ∧ kuhnCoord k σ v a ≤ 1 := by
    fin_cases a <;> simp <;> constructor <;> linarith
  have hwa : 0 ≤ kuhnCoord k σ w a ∧ kuhnCoord k σ w a ≤ 1 := by
    fin_cases a <;> simp <;> constructor <;> linarith
  have : v (σ a) - w (σ a) = kuhnCoord k σ v a - kuhnCoord k σ w a := by
    simp [kuhnCoord]
  rw [this, abs_le]
  constructor <;> linarith [hva.1, hva.2, hwa.1, hwa.2]

/-- **Edges are chains of at most three unit steps.**  For `a ≤ b`, `v_b = v_a + Σ e_{σ c}`
over the (at most three) `c` with `a ≤ c < b`. -/
theorem kuhnVertex_eq_add_steps (k : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 3)) {a b : ℕ}
    (hab : a ≤ b) :
    kuhnVertex k σ b = kuhnVertex k σ a +
      ∑ c ∈ Finset.univ.filter (fun c : Fin 3 => a ≤ (c : ℕ) ∧ (c : ℕ) < b),
        (Pi.single (σ c) 1 : Fin 3 → ℤ) := by
  funext j
  obtain ⟨c0, rfl⟩ := σ.surjective j
  rw [Pi.add_apply, Finset.sum_apply, kuhnVertex_apply_perm, kuhnVertex_apply_perm]
  have hs : ∀ c : Fin 3,
      (Pi.single (σ c) (1 : ℤ) : Fin 3 → ℤ) (σ c0) = if c0 = c then 1 else 0 := by
    intro c
    by_cases hc : c0 = c
    · subst hc; simp
    · simp [σ.injective.ne hc, hc]
  simp only [hs, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

end

end RenewalGeometry.KuhnLovaszExtension
