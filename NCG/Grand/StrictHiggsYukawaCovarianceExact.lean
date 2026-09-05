/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Strict Higgs--Yukawa cross covariance

For a finite positive law, the independent-copy covariance identity turns
strict comonotonicity into strict positive covariance.  Applied to
`X = Z²`, `f(X)=X²`, and `g(X)=X/(m²+uX)`, this gives the strict negative
mixed Higgs--Yukawa writer in `cor:SMFS-strict-HY`.
-/

namespace NCG
namespace StrictHiggsYukawa

variable {Ω : Type*} [Fintype Ω]

def expectation (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

def covariance (p : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  expectation p (fun ω => f ω * g ω) - expectation p f * expectation p g

/-- The finite independent-copy identity for covariance. -/
theorem two_covariance_eq_pair_sum
    (p : Ω → ℝ) (f g : Ω → ℝ) (hp : ∑ ω, p ω = 1) :
    2 * covariance p f g =
      ∑ a, ∑ b, p a * p b * ((f a - f b) * (g a - g b)) := by
  classical
  have hpoint : ∀ a b,
      p a * p b * ((f a - f b) * (g a - g b)) =
        (p a * (f a * g a)) * p b
          + p a * (p b * (f b * g b))
          - (p a * f a) * (p b * g b)
          - (p a * g a) * (p b * f b) := by
    intro a b
    ring
  have hdouble :
      (∑ a, ∑ b, p a * p b * ((f a - f b) * (g a - g b))) =
        (∑ a, p a * (f a * g a)) * (∑ b, p b)
          + (∑ a, p a) * (∑ b, p b * (f b * g b))
          - (∑ a, p a * f a) * (∑ b, p b * g b)
          - (∑ a, p a * g a) * (∑ b, p b * f b) := by
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Fintype.sum_mul_sum, ← Fintype.sum_mul_sum,
      ← Fintype.sum_mul_sum, ← Fintype.sum_mul_sum]
  rw [hdouble, hp]
  simp only [covariance, expectation]
  ring

/-- Strict finite Chebyshev/FKG covariance: two strictly increasing functions
of a nonconstant random variable have positive covariance.  Nonconstancy is
required on two atoms of positive probability, which is the exact finite-law
meaning relevant to the shell model. -/
theorem covariance_pos_of_strictlyIncreasing
    (p : Ω → ℝ) (X : Ω → ℝ) (f g : ℝ → ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp : ∑ ω, p ω = 1)
    (hf : StrictMono f) (hg : StrictMono g)
    (hnonconstant : ∃ a b, 0 < p a ∧ 0 < p b ∧ X a ≠ X b) :
    0 < covariance p (fun ω => f (X ω)) (fun ω => g (X ω)) := by
  obtain ⟨a0, b0, hpa, hpb, hab⟩ := hnonconstant
  have hterm_nonneg : ∀ a b,
      0 ≤ p a * p b *
        ((f (X a) - f (X b)) * (g (X a) - g (X b))) := by
    intro a b
    have hprod : 0 ≤
        (f (X a) - f (X b)) * (g (X a) - g (X b)) := by
      rcases le_total (X a) (X b) with hle | hle
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hf.monotone hle))
          (sub_nonpos.mpr (hg.monotone hle))
      · exact mul_nonneg
          (sub_nonneg.mpr (hf.monotone hle))
          (sub_nonneg.mpr (hg.monotone hle))
    exact mul_nonneg (mul_nonneg (hp0 a) (hp0 b)) hprod
  have hpair_pos : 0 < p a0 * p b0 *
      ((f (X a0) - f (X b0)) * (g (X a0) - g (X b0))) := by
    have hprod : 0 <
        (f (X a0) - f (X b0)) * (g (X a0) - g (X b0)) := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact mul_pos_of_neg_of_neg
          (sub_neg.mpr (hf hlt)) (sub_neg.mpr (hg hlt))
      · exact mul_pos (sub_pos.mpr (hf hgt)) (sub_pos.mpr (hg hgt))
    exact mul_pos (mul_pos hpa hpb) hprod
  have hsum_pos : 0 < ∑ a, ∑ b,
      p a * p b * ((f (X a) - f (X b)) * (g (X a) - g (X b))) := by
    refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ =>
      hterm_nonneg a b) ⟨a0, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun b _ => hterm_nonneg a0 b)
      ⟨b0, Finset.mem_univ _, hpair_pos⟩
  have hid := two_covariance_eq_pair_sum p
    (fun ω => f (X ω)) (fun ω => g (X ω)) hp
  nlinarith

/-- On nonnegative Higgs intensity, both `x ↦ x²` and
`x ↦ x/(m²+ux)` are strictly increasing when `m²>0` and `u≥0`. -/
theorem higgs_yukawa_strict_covariance
    (p : Ω → ℝ) (Z : Ω → ℝ) (m2 u : ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp : ∑ ω, p ω = 1)
    (hm2 : 0 < m2) (hu : 0 ≤ u)
    (hnonconstant : ∃ a b, 0 < p a ∧ 0 < p b ∧ Z a ^ 2 ≠ Z b ^ 2) :
    0 < covariance p (fun ω => Z ω ^ 4)
      (fun ω => Z ω ^ 2 / (m2 + u * Z ω ^ 2)) := by
  let X : Ω → ℝ := fun ω => Z ω ^ 2
  let f : ℝ → ℝ := fun x => x ^ 2
  let g : ℝ → ℝ := fun x => x / (m2 + u * x)
  have hf : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x < y → f x < f y := by
    intro x y hx hy hxy
    dsimp only [f]
    nlinarith
  have hg : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x < y → g x < g y := by
    intro x y hx hy hxy
    have hdx : 0 < m2 + u * x := by positivity
    have hdy : 0 < m2 + u * y := by positivity
    dsimp only [g]
    rw [div_lt_div_iff₀ hdx hdy]
    nlinarith [mul_lt_mul_of_pos_left hxy hm2]
  have hmono_f : StrictMonoOn f (Set.Ici 0) := fun x hx y hy hxy => hf hx hy hxy
  have hmono_g : StrictMonoOn g (Set.Ici 0) := fun x hx y hy hxy => hg hx hy hxy
  have hterm_nonneg : ∀ a b,
      0 ≤ p a * p b *
        ((f (X a) - f (X b)) * (g (X a) - g (X b))) := by
    intro a b
    have hXa : 0 ≤ X a := by exact sq_nonneg _
    have hXb : 0 ≤ X b := by exact sq_nonneg _
    have hprod : 0 ≤ (f (X a) - f (X b)) * (g (X a) - g (X b)) := by
      rcases le_total (X a) (X b) with hle | hle
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hmono_f.monotoneOn hXa hXb hle))
          (sub_nonpos.mpr (hmono_g.monotoneOn hXa hXb hle))
      · exact mul_nonneg
          (sub_nonneg.mpr (hmono_f.monotoneOn hXb hXa hle))
          (sub_nonneg.mpr (hmono_g.monotoneOn hXb hXa hle))
    exact mul_nonneg (mul_nonneg (hp0 a) (hp0 b)) hprod
  obtain ⟨a0, b0, hpa, hpb, hab⟩ := hnonconstant
  change X a0 ≠ X b0 at hab
  have hpair_pos : 0 < p a0 * p b0 *
      ((f (X a0) - f (X b0)) * (g (X a0) - g (X b0))) := by
    have hXa : 0 ≤ X a0 := by exact sq_nonneg _
    have hXb : 0 ≤ X b0 := by exact sq_nonneg _
    have hprod : 0 < (f (X a0) - f (X b0)) * (g (X a0) - g (X b0)) := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact mul_pos_of_neg_of_neg
          (sub_neg.mpr (hmono_f hXa hXb hlt))
          (sub_neg.mpr (hmono_g hXa hXb hlt))
      · exact mul_pos
          (sub_pos.mpr (hmono_f hXb hXa hgt))
          (sub_pos.mpr (hmono_g hXb hXa hgt))
    exact mul_pos (mul_pos hpa hpb) hprod
  have hsum_pos : 0 < ∑ a, ∑ b,
      p a * p b * ((f (X a) - f (X b)) * (g (X a) - g (X b))) := by
    refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ =>
      hterm_nonneg a b) ⟨a0, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun b _ => hterm_nonneg a0 b)
      ⟨b0, Finset.mem_univ _, hpair_pos⟩
  have hid := two_covariance_eq_pair_sum p
    (fun ω => f (X ω)) (fun ω => g (X ω)) hp
  have hcov : 0 < covariance p (fun ω => f (X ω)) (fun ω => g (X ω)) := by
    nlinarith
  have hf_eq : (fun ω => f (X ω)) = (fun ω => Z ω ^ 4) := by
    funext ω
    dsimp [X, f]
    ring
  have hg_eq : (fun ω => g (X ω)) =
      (fun ω => Z ω ^ 2 / (m2 + u * Z ω ^ 2)) := by
    rfl
  rwa [hf_eq, hg_eq] at hcov

/-- The manuscript's strict mixed writer: multiplying the positive covariance
by the negative fermion multiplicity gives a strictly negative response. -/
theorem strict_higgs_yukawa_cross_writer
    (p : Ω → ℝ) (Z : Ω → ℝ) (m2 u rF : ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp : ∑ ω, p ω = 1)
    (hm2 : 0 < m2) (hu : 0 ≤ u) (hrF : 0 < rF)
    (hnonconstant : ∃ a b, 0 < p a ∧ 0 < p b ∧ Z a ^ 2 ≠ Z b ^ 2) :
    -rF * covariance p (fun ω => Z ω ^ 4)
      (fun ω => Z ω ^ 2 / (m2 + u * Z ω ^ 2)) < 0 := by
  have hcov := higgs_yukawa_strict_covariance p Z m2 u hp0 hp hm2 hu hnonconstant
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hrF) hcov

end StrictHiggsYukawa
end NCG
