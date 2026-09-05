/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.V036HDA

/-!
# Complete finite coherent vacuum HDA (Gran-Tensor form)
  (`thm:finite-HDA`, Gran-Tensor manuscript)

* `cross_kernel_reconstruction`: hypothesis (H1) in exact form —
  for a Hermitian generator the two calibrated phase settings
  `1` and `i` reconstruct the complex cross kernel from real
  quadratic measurements:
  `u*Av = ((Q(u+v) - Qu - Qv) - i(Q(u+iv) - Qu - Qv))/2`
  with `Q(x) = x*Ax`; the `-1, -i` settings are consistency
  checks by conjugation;
* `finite_hda_smearing` / `finite_hda_locality`: the bracket
  engine (re-exported from the proved flagship HDA layer) —
  `[H[N], H[M]] = Σ_{x,y} N_xM_y·[n_x,n_y]` and its (H2)
  reduction to the declared one-link neighborhood.

Rendering disclosed: the identification of the reduced local
commutators with the three HDA right-hand sides (the
coefficient law and reducing-carrier Feshbach cancellation) and
the continuum passage are the manuscript's operator layer; the
cross-kernel reconstruction and the smearing/locality engine
are proved here.
-/

open Matrix

namespace NCG

variable {n : Type*} [Fintype n]

/-- (H1): the calibrated phases `1` and `i` reconstruct the
complex cross kernel of a Hermitian generator from real
quadratic measurements. -/
theorem cross_kernel_reconstruction (A : Matrix n n ℂ)
    (hA : Aᴴ = A) (u v : n → ℂ) :
    star u ⬝ᵥ A.mulVec v
      = ((star (u + v) ⬝ᵥ A.mulVec (u + v)
            - star u ⬝ᵥ A.mulVec u
            - star v ⬝ᵥ A.mulVec v)
          - Complex.I
            * (star (u + Complex.I • v)
                ⬝ᵥ A.mulVec (u + Complex.I • v)
              - star u ⬝ᵥ A.mulVec u
              - star v ⬝ᵥ A.mulVec v)) / 2 := by
  have hAentry : ∀ i j, star (A i j) = A j i := by
    intro i j
    have h := congrFun (congrFun hA j) i
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hsymm : star v ⬝ᵥ A.mulVec u
      = star (star u ⬝ᵥ A.mulVec v) := by
    calc star v ⬝ᵥ A.mulVec u
        = ∑ i, ∑ j, star (v i) * (A i j * u j) := by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ j, ∑ i, star (v i) * (A i j * u j) :=
          Finset.sum_comm
      _ = star (star u ⬝ᵥ A.mulVec v) := by
          simp only [dotProduct, Matrix.mulVec,
            Pi.star_apply, star_sum, star_mul', star_star,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => ?_
          rw [hAentry j i]
          ring
  set B := star u ⬝ᵥ A.mulVec v with hB
  have hBbar : star v ⬝ᵥ A.mulVec u = star B := hsymm
  have hQ1 : star (u + v) ⬝ᵥ A.mulVec (u + v)
      = star u ⬝ᵥ A.mulVec u + B + star B
        + star v ⬝ᵥ A.mulVec v := by
    rw [star_add, Matrix.mulVec_add, add_dotProduct,
      dotProduct_add, dotProduct_add, ← hB, ← hBbar]
    ring
  have hQi : star (u + Complex.I • v)
        ⬝ᵥ A.mulVec (u + Complex.I • v)
      = star u ⬝ᵥ A.mulVec u + Complex.I * B
        - Complex.I * star B
        + star v ⬝ᵥ A.mulVec v := by
    rw [star_add, star_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, ← hB, ← hBbar]
    rw [Complex.star_def, Complex.conj_I]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    linear_combination
      (-(star v ⬝ᵥ A.mulVec v)) * Complex.I_sq
  rw [hQ1, hQi]
  linear_combination ((B - star B) / 2) * Complex.I_sq

/-- The bracket smearing engine for this record (re-export of
the proved flagship HDA layer). -/
theorem finite_hda_smearing {d ι : Type*} [Fintype d]
    [Fintype ι] (nloc : ι → Matrix d d ℂ) (N M : ι → ℂ) :
    (∑ x, N x • nloc x) * (∑ y, M y • nloc y)
      - (∑ y, M y • nloc y) * (∑ x, N x • nloc x)
    = ∑ x, ∑ y, (N x * M y) •
        (nloc x * nloc y - nloc y * nloc x) :=
  bilocal_commutator_expansion nloc N M

/-- (H2) locality reduction for this record (re-export). -/
theorem finite_hda_locality {d ι : Type*} [Fintype d]
    [Fintype ι] (nloc : ι → Matrix d d ℂ) (N M : ι → ℂ)
    (E : Finset (ι × ι))
    (hloc : ∀ x y, (x, y) ∉ E →
      nloc x * nloc y = nloc y * nloc x) :
    (∑ x, ∑ y, (N x * M y) •
        (nloc x * nloc y - nloc y * nloc x))
    = ∑ p ∈ E, (N p.1 * M p.2) •
        (nloc p.1 * nloc p.2 - nloc p.2 * nloc p.1) :=
  bilocal_support_reduction nloc N M E hloc

end NCG
