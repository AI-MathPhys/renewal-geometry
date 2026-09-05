/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Scalar data do not select a `C*`-adjoint
  (`cth:metric-adjoint-no-go`, Gran-Tensor manuscript)

* `metric_adjoint_no_go`: for `A = diag(α,β)` with `α ≠ β` and the
  tilted metric `G_t`, the standard adjoint gives the commutative
  diagonal algebra `C*(A,A*) ≅ ℂ²` (spectral projections are
  polynomials in `A`, and every element of the generated algebra
  is diagonal), while the `G_t`-adjoint `A^{†t} = G_t⁻¹AG_t` has
  both off-diagonal entries nonzero and generates with `A` the
  full `M₂(ℂ)` — a scalar Hankel realization does not determine
  its formal adjoint.

Rendering disclosed: the manuscript's `0<α<β<1`, `0<t<1` window
is rendered by the exact nondegeneracy conditions it implies
(`α ≠ β`, `t ≠ 0`, `t² ≠ 1`); `C*(A,A*) ≅ ℂ²` is rendered by
diagonality of the adjoined algebra plus polynomial recovery of
the spectral projections.
-/

open Matrix

namespace NCG

/-- The diagonal generator `A = diag(α,β)`. -/
noncomputable def maGen (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), 0; 0, (b : ℂ)]

/-- The tilted metric `G_t`. -/
noncomputable def maMetric (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (t : ℂ); (t : ℂ), 1]

/-- `cth:metric-adjoint-no-go`: standard adjoint is diagonal
(`ℂ²`), tilted adjoint has nonzero off-diagonals and generates
`M₂(ℂ)`. -/
theorem metric_adjoint_no_go (a b t : ℝ)
    (hab : a ≠ b) (ht0 : t ≠ 0) (ht1 : t ^ 2 ≠ 1) :
    ((maGen a b)ᴴ = maGen a b)
    ∧ (((a : ℂ) - b)⁻¹ • (maGen a b - (b : ℂ) • 1)
        = !![1, 0; 0, 0])
    ∧ (∀ M ∈ Algebra.adjoin ℂ
        ({maGen a b, (maGen a b)ᴴ} :
          Set (Matrix (Fin 2) (Fin 2) ℂ)),
        M 0 1 = 0 ∧ M 1 0 = 0)
    ∧ (((maMetric t)⁻¹ * maGen a b * maMetric t) 0 1 ≠ 0
        ∧ ((maMetric t)⁻¹ * maGen a b * maMetric t) 1 0 ≠ 0)
    ∧ (Algebra.adjoin ℂ
        ({maGen a b, (maMetric t)⁻¹ * maGen a b * maMetric t} :
          Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤) := by
  have hab' : (a : ℂ) ≠ (b : ℂ) := fun h => hab (by exact_mod_cast h)
  have hab'' : (a : ℂ) - b ≠ 0 := sub_ne_zero.mpr hab'
  have ht0' : (t : ℂ) ≠ 0 := fun h => ht0 (by exact_mod_cast h)
  have ht1' : (1 : ℂ) - (t : ℂ) ^ 2 ≠ 0 := by
    intro h
    apply ht1
    have := sub_eq_zero.mp h
    exact_mod_cast this.symm
  have hAH : (maGen a b)ᴴ = maGen a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [maGen, Complex.conj_ofReal]
  have hE11 : ((a : ℂ) - b)⁻¹ • (maGen a b - (b : ℂ) • 1)
      = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [maGen]; try field_simp)
  have hGinv : (maMetric t)⁻¹
      = ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ • !![1, -(t : ℂ); -(t : ℂ), 1] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [maMetric, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  have hAdag : (maMetric t)⁻¹ * maGen a b * maMetric t
      = ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹
        • !![(a : ℂ) - b * t ^ 2, (t : ℂ) * ((a : ℂ) - b);
             (t : ℂ) * ((b : ℂ) - a), (b : ℂ) - a * t ^ 2] := by
    rw [hGinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [maGen, maMetric, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
  refine ⟨hAH, hE11, ?_, ?_, ?_⟩
  · -- diagonality of the standard-adjoint algebra
    intro M hM
    induction hM using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with rfl | hx
        · constructor <;> simp [maGen]
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [hAH]
          constructor <;> simp [maGen]
    | algebraMap r =>
        constructor <;>
          simp [Matrix.algebraMap_matrix_apply]
    | add x y hx hy px py =>
        exact ⟨by rw [Matrix.add_apply, px.1, py.1, add_zero],
          by rw [Matrix.add_apply, px.2, py.2, add_zero]⟩
    | mul x y hx hy px py =>
        constructor <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two,
            px.1, px.2, py.1, py.2]
  · -- nonzero off-diagonal entries of the tilted adjoint
    have h01 : ((maMetric t)⁻¹ * maGen a b * maMetric t) 0 1
        = ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹
          * ((t : ℂ) * ((a : ℂ) - b)) := by
      rw [hAdag]
      rfl
    have h10 : ((maMetric t)⁻¹ * maGen a b * maMetric t) 1 0
        = ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹
          * ((t : ℂ) * ((b : ℂ) - a)) := by
      rw [hAdag]
      rfl
    constructor
    · rw [h01]
      exact mul_ne_zero (inv_ne_zero ht1')
        (mul_ne_zero ht0' hab'')
    · rw [h10]
      exact mul_ne_zero (inv_ne_zero ht1')
        (mul_ne_zero ht0' (sub_ne_zero.mpr hab'.symm))
  · -- generation of the full matrix algebra
    set S := Algebra.adjoin ℂ
      ({maGen a b, (maMetric t)⁻¹ * maGen a b * maMetric t} :
        Set (Matrix (Fin 2) (Fin 2) ℂ)) with hS
    have hAmem : maGen a b ∈ S :=
      Algebra.subset_adjoin (Set.mem_insert _ _)
    have hDmem : (maMetric t)⁻¹ * maGen a b * maMetric t ∈ S :=
      Algebra.subset_adjoin
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h11mem : (!![1, 0; 0, 0] :
        Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [← hE11]
      exact S.smul_mem
        (S.sub_mem hAmem (S.smul_mem (S.one_mem) _)) _
    have h22eq : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
        = 1 - !![1, 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h22mem : (!![0, 0; 0, 1] :
        Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      rw [h22eq]
      exact S.sub_mem (S.one_mem) h11mem
    -- the two off-diagonal units
    have hc12 : ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((a : ℂ) - b))
        ≠ 0 :=
      mul_ne_zero (inv_ne_zero ht1') (mul_ne_zero ht0' hab'')
    have hc21 : ((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((b : ℂ) - a))
        ≠ 0 :=
      mul_ne_zero (inv_ne_zero ht1')
        (mul_ne_zero ht0' (sub_ne_zero.mpr hab'.symm))
    have hprod12 : !![1, 0; 0, 0]
        * ((maMetric t)⁻¹ * maGen a b * maMetric t)
        * !![0, 0; 0, 1]
        = (((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((a : ℂ) - b)))
          • !![0, 1; 0, 0] := by
      rw [hAdag]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hprod21 : !![0, 0; 0, 1]
        * ((maMetric t)⁻¹ * maGen a b * maMetric t)
        * !![1, 0; 0, 0]
        = (((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((b : ℂ) - a)))
          • !![0, 0; 1, 0] := by
      rw [hAdag]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h12mem : (!![0, 1; 0, 0] :
        Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      have hm := S.smul_mem
        (S.mul_mem (S.mul_mem h11mem hDmem) h22mem)
        (((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((a : ℂ) - b)))⁻¹
      rw [hprod12, smul_smul, inv_mul_cancel₀ hc12, one_smul] at hm
      exact hm
    have h21mem : (!![0, 0; 1, 0] :
        Matrix (Fin 2) (Fin 2) ℂ) ∈ S := by
      have hm := S.smul_mem
        (S.mul_mem (S.mul_mem h22mem hDmem) h11mem)
        (((1 : ℂ) - (t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * ((b : ℂ) - a)))⁻¹
      rw [hprod21, smul_smul, inv_mul_cancel₀ hc21, one_smul] at hm
      exact hm
    rw [Algebra.eq_top_iff]
    intro M
    have hMdec : M = M 0 0 • !![1, 0; 0, 0]
        + M 0 1 • !![0, 1; 0, 0]
        + M 1 0 • !![0, 0; 1, 0]
        + M 1 1 • !![0, 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hMdec]
    exact S.add_mem
      (S.add_mem
        (S.add_mem (S.smul_mem h11mem _) (S.smul_mem h12mem _))
        (S.smul_mem h21mem _))
      (S.smul_mem h22mem _)

end NCG
