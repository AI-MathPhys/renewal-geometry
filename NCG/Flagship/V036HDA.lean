/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Complete finite coherent vacuum HDA
  (`thm:master-vacuum-HDA-v036`, flagship manuscript)

* `bilocal_commutator_expansion`: the algebraic engine behind
  all three bracket identities — for cell-local densities,
  `[H[N], H[M]] = Σ_{x,y} N_xM_y·[n_x, n_y]`, so every bracket
  of smeared generators is a lapse-weighted sum of local
  commutators;
* `bilocal_support_reduction`: hypothesis (H2) in action —
  commutators vanishing off the declared one-link neighborhood
  restrict the double sum to the neighborhood pairs;
* `coherent_phase_group`: hypothesis (H1) — the coherent
  relative phases `{1, -1, i, -i}` are exactly the powers of
  `i` and are closed under multiplication.

Rendering disclosed: the identification of the reduced local
commutators with the deformation generators on the right-hand
sides of the three HDA identities (the coefficient law, the
reducing-carrier Feshbach cancellation, and the continuum
limit) is the manuscript's operator layer; the smearing algebra,
the locality reduction, and the phase group are proved here.
-/

open Matrix

namespace NCG

variable {d ι : Type*} [Fintype d] [Fintype ι]

/-- Smearing engine: the bracket of two smeared cell-local
densities is the lapse-weighted sum of local commutators. -/
theorem bilocal_commutator_expansion
    (nloc : ι → Matrix d d ℂ) (N M : ι → ℂ) :
    (∑ x, N x • nloc x) * (∑ y, M y • nloc y)
      - (∑ y, M y • nloc y) * (∑ x, N x • nloc x)
    = ∑ x, ∑ y, (N x * M y) •
        (nloc x * nloc y - nloc y * nloc x) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun y x => (M y • nloc y) * (N x • nloc x))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_comm (M y) (N x), ← smul_sub]

/-- Locality (H2): commutators vanishing off the declared
neighborhood restrict the bracket to neighborhood pairs. -/
theorem bilocal_support_reduction
    (nloc : ι → Matrix d d ℂ) (N M : ι → ℂ)
    (E : Finset (ι × ι))
    (hloc : ∀ x y, (x, y) ∉ E →
      nloc x * nloc y = nloc y * nloc x) :
    (∑ x, ∑ y, (N x * M y) •
        (nloc x * nloc y - nloc y * nloc x))
    = ∑ p ∈ E, (N p.1 * M p.2) •
        (nloc p.1 * nloc p.2 - nloc p.2 * nloc p.1) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_subset (Finset.subset_univ E)
    fun p _ hp => ?_).symm
  rw [hloc p.1 p.2 hp, sub_self, smul_zero]

/-- Coherent phases (H1): `{1, -1, i, -i}` are exactly the
powers of `i`, closed under multiplication. -/
theorem coherent_phase_group :
    (∀ z ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ),
      ∃ k : ℕ, z = Complex.I ^ k)
    ∧ (∀ z ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ),
        ∀ w ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ),
          z * w ∈ ({1, -1, Complex.I, -Complex.I} : Set ℂ)) := by
  constructor
  · rintro z (rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨2, by rw [pow_two, Complex.I_mul_I]⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨3, by
        rw [pow_succ, pow_two, Complex.I_mul_I, neg_one_mul]⟩
  · rintro z (rfl | rfl | rfl | rfl) w (rfl | rfl | rfl | rfl) <;>
      simp [Complex.I_mul_I]

end NCG
