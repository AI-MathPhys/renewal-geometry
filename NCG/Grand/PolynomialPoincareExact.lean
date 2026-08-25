/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The polynomial Poincaré lemma

Even-sector machinery for `thm:SM-common-action-integrability` (RG.1/RG.2).

For a polynomial force one-form `ω = ∑ᵢ dxⁱ Fᵢ` over a characteristic-zero coefficient
ring, the curl `∂ᵢFⱼ - ∂ⱼFᵢ` vanishes exactly when `Fᵢ = ∂ᵢS` for a single action `S`
(`curl_zero_iff_exists_potential`).  The action is reconstructed by radial integration,
which for polynomials is the exact algebraic homotopy
`S = ∑_d (d+1)⁻¹ ∑ᵢ xⁱ (Fᵢ)_d` on homogeneous components, closed by Euler's identity
(`IsHomogeneous.sum_X_mul_pderiv`).
-/

open MvPolynomial

namespace NCG
namespace PolyPoincare

variable {σ : Type*} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `pderiv` is `ℚ`-linear over a `ℚ`-algebra. -/
theorem pderiv_qsmul (i : σ) (q : ℚ) (P : MvPolynomial σ R) :
    pderiv i (q • P) = q • pderiv i P := by
  rw [← algebraMap_smul R q P, smul_eq_C_mul, pderiv_C_mul, ← smul_eq_C_mul,
    algebraMap_smul]

omit [Algebra ℚ R] in
/-- Mixed polynomial partials commute. -/
theorem pderiv_pderiv (i j : σ) (P : MvPolynomial σ R) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [pderiv_monomial]
      have h1 : ((s - Finsupp.single j 1 : σ →₀ ℕ)) i = s i := by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hij), Nat.sub_zero]
      have h2 : ((s - Finsupp.single i 1 : σ →₀ ℕ)) j = s j := by
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hij, Nat.sub_zero]
      rw [h1, h2]
      have hex : s - Finsupp.single j 1 - Finsupp.single i 1
          = s - Finsupp.single i 1 - Finsupp.single j 1 := by
        ext t
        simp only [Finsupp.tsub_apply, Finsupp.single_apply]
        omega
      rw [hex]
      ring_nf
  | add p q hp hq => simp [hp, hq]

omit [Algebra ℚ R] in
/-- The homogeneous component of a monomial. -/
theorem hc_monomial (n : ℕ) (s : σ →₀ ℕ) (a : R) :
    homogeneousComponent n (monomial s a)
      = if Finsupp.degree s = n then monomial s a else 0 := by
  classical
  ext m
  rw [coeff_homogeneousComponent]
  by_cases hm : Finsupp.degree m = n
  · rw [if_pos hm]
    by_cases hdeg : Finsupp.degree s = n
    · rw [if_pos hdeg]
    · rw [if_neg hdeg, coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact hdeg hm
  · rw [if_neg hm]
    by_cases hdeg : Finsupp.degree s = n
    · rw [if_pos hdeg, coeff_monomial]
      exact (if_neg (by rintro rfl; exact hm hdeg)).symm
    · rw [if_neg hdeg, coeff_zero]

omit [Algebra ℚ R] in
theorem degree_eq_sum (t : σ →₀ ℕ) : Finsupp.degree t = t.sum fun _ n => n := rfl

omit [Algebra ℚ R] in
/-- `pderiv` lowers homogeneous components by one. -/
theorem pderiv_homogeneousComponent (j : σ) (d : ℕ) (P : MvPolynomial σ R) :
    pderiv j (homogeneousComponent (d + 1) P) = homogeneousComponent d (pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [hc_monomial, pderiv_monomial, hc_monomial]
    by_cases hsj : s j = 0
    · -- the `j`-derivative kills the monomial in both orders
      have hcoeff : a * (s j : R) = 0 := by rw [hsj, Nat.cast_zero, mul_zero]
      by_cases hdeg : Finsupp.degree s = d + 1
      · rw [if_pos hdeg, pderiv_monomial, hcoeff, monomial_zero]
        by_cases h2 : Finsupp.degree (s - Finsupp.single j 1) = d
        · rw [if_pos h2]
        · rw [if_neg h2]
      · rw [if_neg hdeg, map_zero]
        by_cases h2 : Finsupp.degree (s - Finsupp.single j 1) = d
        · rw [if_pos h2, hcoeff, monomial_zero]
        · rw [if_neg h2]
    · -- the derivative genuinely lowers the degree by one
      have hsub : Finsupp.degree (s - Finsupp.single j 1) = Finsupp.degree s - 1 := by
        rw [degree_eq_sum, degree_eq_sum]
        rw [show s.sum (fun _ n => n) = (s - Finsupp.single j 1).sum (fun _ n => n)
            + (Finsupp.single j 1).sum (fun _ n => n) from ?_]
        · simp [Finsupp.sum_single_index]
        · rw [← Finsupp.sum_add_index (by simp) (by simp)]
          congr 1
          ext t
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          have hle : (if j = t then 1 else 0) ≤ s t := by
            by_cases hjt : j = t
            · subst hjt
              simp
              omega
            · simp [hjt]
          have := Nat.sub_add_cancel hle
          omega
      have hpos : 0 < Finsupp.degree s := by
        rw [degree_eq_sum, Finsupp.sum]
        refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨j, ?_, by omega⟩
        exact Finsupp.mem_support_iff.mpr hsj
      by_cases hdeg : Finsupp.degree s = d + 1
      · rw [if_pos hdeg, pderiv_monomial, if_pos (by omega)]
      · rw [if_neg hdeg, map_zero, if_neg (by omega)]
  | add p q hp hq => simp [hp, hq]

omit [Algebra ℚ R] in
/-- The Euler homotopy step for a homogeneous curl-free force family. -/
theorem homogeneous_potential_step [Fintype σ] (d : ℕ) (G : σ → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous d)
    (hcurl : ∀ i j, pderiv i (G j) = pderiv j (G i)) (j : σ) :
    pderiv j (∑ i, X i * G i) = (d + 1) • G j := by
  classical
  rw [map_sum]
  have hterm : ∀ i : σ, pderiv j (X i * G i)
      = (if i = j then G i else 0) + X i * pderiv i (G j) := by
    intro i
    rw [pderiv_mul, pderiv_X, hcurl j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j (fun i => G i), if_pos (Finset.mem_univ j),
    (hG j).sum_X_mul_pderiv, succ_nsmul, add_comm]

/-- **The polynomial Poincaré lemma (existence)**: a curl-free polynomial force family is
the gradient of a single polynomial action, reconstructed by algebraic radial
integration on homogeneous components. -/
theorem exists_potential [Finite σ] (F : σ → MvPolynomial σ R)
    (hcurl : ∀ i j, pderiv i (F j) = pderiv j (F i)) :
    ∃ S : MvPolynomial σ R, ∀ j, pderiv j S = F j := by
  classical
  cases nonempty_fintype σ
  set N : ℕ := Finset.univ.sup fun i => (F i).totalDegree with hN
  refine ⟨∑ d ∈ Finset.range (N + 1),
    ((d + 1 : ℚ))⁻¹ • ∑ i, X i * homogeneousComponent d (F i), fun j => ?_⟩
  have hcomp : ∀ d : ℕ, ∀ i l : σ,
      pderiv i (homogeneousComponent d (F l))
        = pderiv l (homogeneousComponent d (F i)) := by
    intro d i l
    rcases d with _ | d'
    · rw [homogeneousComponent_zero, homogeneousComponent_zero, pderiv_C, pderiv_C]
    · rw [pderiv_homogeneousComponent, pderiv_homogeneousComponent, hcurl i l]
  have hstep : ∀ d : ℕ, pderiv j (((d + 1 : ℚ))⁻¹
      • ∑ i, X i * homogeneousComponent d (F i)) = homogeneousComponent d (F j) := by
    intro d
    rw [pderiv_qsmul, homogeneous_potential_step d _
      (fun i => homogeneousComponent_isHomogeneous d (F i)) (hcomp d) j,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    have hcast : ((d : ℚ) + 1)⁻¹ * ((d + 1 : ℕ) : ℚ) = 1 := by
      push_cast
      exact inv_mul_cancel₀ (by positivity)
    rw [hcast, one_smul]
  rw [map_sum, Finset.sum_congr rfl fun d _ => hstep d]
  -- the components of `F j` up to the common bound sum back to `F j`
  have hsub : Finset.range ((F j).totalDegree + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    have hle : (F j).totalDegree ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun i => (F i).totalDegree) (Finset.mem_univ j)
    omega
  conv_rhs => rw [← sum_homogeneousComponent (φ := F j)]
  refine (Finset.sum_subset hsub fun d _ hd => ?_).symm
  exact homogeneousComponent_eq_zero d (F j) (by
    simp only [Finset.mem_range, not_lt] at hd
    omega)

/-- **RG.1/RG.2, even sector**: the polynomial curl vanishes exactly when the force family
is the gradient of one action; sectorwise fits define one physical theory only when the
complete mixed curl vanishes. -/
theorem curl_zero_iff_exists_potential [Finite σ] (F : σ → MvPolynomial σ R) :
    (∀ i j, pderiv i (F j) = pderiv j (F i)) ↔
      ∃ S : MvPolynomial σ R, ∀ j, pderiv j S = F j := by
  constructor
  · exact exists_potential F
  · rintro ⟨S, hS⟩ i j
    rw [← hS i, ← hS j, pderiv_pderiv]

end PolyPoincare
end NCG
