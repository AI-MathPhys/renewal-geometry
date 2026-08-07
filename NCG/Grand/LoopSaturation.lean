/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Primitive invariant-loop saturation
  (`thm:YM-primitive-loop-saturation`, Gran-Tensor manuscript)

* `finite_stone_weierstrass`: the density engine — a unital
  subalgebra of the finite-lattice function algebra that
  separates configurations is the whole algebra (Lagrange
  interpolation through the separating writers), so the loop
  writers saturate the selected gauge-invariant algebra as soon
  as they separate its spectrum;
* `single_generator_mem`: the interpolation core — every
  point indicator lies in a separating unital subalgebra;
* `full_support_cyclic`: the cyclicity clause — a strictly
  positive (everywhere nonvanishing) finite-regulator vacuum is
  cyclic for the function algebra: every vector is reached by a
  multiplication operator.

Rendering disclosed: the identification of the selected
finite-lattice gauge-invariant algebra with a finite function
algebra on the physical configuration spectrum (gauge averaging
and the retained cycle/centre-flux/topological records) is the
manuscript's lattice-gauge layer; the separation-to-density
engine and the strict-positivity cyclicity are proved here.
-/

namespace NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Interpolation core: a separating unital subalgebra of the
finite function algebra contains every point indicator. -/
theorem single_generator_mem [DecidableEq ι]
    (A : Subalgebra ℂ (ι → ℂ))
    (hsep : ∀ i j : ι, i ≠ j → ∃ f ∈ A, f i ≠ f j) (i₀ : ι) :
    Pi.single i₀ (1 : ℂ) ∈ A := by
  classical
  have hex : ∀ j : ι, j ≠ i₀ → ∃ f ∈ A, f i₀ ≠ f j :=
    fun j hj => hsep i₀ j (Ne.symm hj)
  choose! g hgA hgne using hex
  set hfun : ι → (ι → ℂ) := fun j =>
    (g j - algebraMap ℂ (ι → ℂ) (g j j))
      * algebraMap ℂ (ι → ℂ) (g j i₀ - g j j)⁻¹ with hhfun
  have hmem : ∀ j ∈ Finset.univ.erase i₀, hfun j ∈ A := by
    intro j hj
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact Subalgebra.mul_mem A
      (Subalgebra.sub_mem A (hgA j hjne)
        (Subalgebra.algebraMap_mem A _))
      (Subalgebra.algebraMap_mem A _)
  have hprod : (∏ j ∈ Finset.univ.erase i₀, hfun j) ∈ A :=
    Subalgebra.prod_mem A hmem
  have heval : (∏ j ∈ Finset.univ.erase i₀, hfun j)
      = Pi.single i₀ (1 : ℂ) := by
    funext k
    rw [Finset.prod_apply]
    by_cases hk : k = i₀
    · subst hk
      rw [Pi.single_eq_same]
      refine Finset.prod_eq_one fun j hj => ?_
      have hjne : j ≠ k := (Finset.mem_erase.mp hj).1
      have hne : g j k - g j j ≠ 0 :=
        sub_ne_zero.mpr (hgne j hjne)
      rw [hhfun]
      simp only [Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact mul_inv_cancel₀ hne
    · rw [Pi.single_eq_of_ne hk]
      refine Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) ?_
      rw [hhfun]
      simp only [Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      rw [sub_self, zero_mul]
  rw [← heval]
  exact hprod

omit [Fintype ι] [DecidableEq ι] in
/-- Finite Stone–Weierstrass density engine: a unital
subalgebra of the finite function algebra separating
configurations is everything. -/
theorem finite_stone_weierstrass [Finite ι]
    (A : Subalgebra ℂ (ι → ℂ))
    (hsep : ∀ i j : ι, i ≠ j → ∃ f ∈ A, f i ≠ f j) :
    A = ⊤ := by
  classical
  haveI := Fintype.ofFinite ι
  rw [eq_top_iff]
  intro v _
  have hdecomp : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
    funext k
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single k
      (fun j _ hj => by
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj),
          smul_zero])
      (fun hk => absurd (Finset.mem_univ k) hk)]
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [hdecomp]
  exact Subalgebra.sum_mem A fun i _ =>
    Subalgebra.smul_mem A (single_generator_mem A hsep i) _

omit [Fintype ι] [DecidableEq ι] in
/-- Cyclicity of the strictly positive vacuum: an everywhere
nonvanishing vector is cyclic for the multiplication algebra —
every target vector is reached. -/
theorem full_support_cyclic (w : ι → ℂ) (hw : ∀ i, w i ≠ 0)
    (v : ι → ℂ) : ∃ d : ι → ℂ, (fun i => d i * w i) = v :=
  ⟨fun i => v i / w i,
    funext fun i => div_mul_cancel₀ (v i) (hw i)⟩

end NCG
