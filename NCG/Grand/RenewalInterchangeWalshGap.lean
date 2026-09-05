/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.InterchangeGap
import NCG.Grand.DiscreteClock

/-!
# Sharp renewal--interchange gap on the Walsh basis

This module carries out the product-space diagonalization that was previously
only assumed.  Walsh coefficients are indexed by subsets of the vertex set;
the renewal part has eigenvalue `g * |A|`, swaps act by permuting subsets, and
the symmetric first-chaos vector supplies sharpness.
-/

open Finset
open Matrix
open scoped Kronecker

namespace NCG
namespace RenewalInterchangeWalshGap

/-- The two-site coordinate swap on the one-site Walsh carrier. -/
def twoSiteSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun p q => if p = (q.2, q.1) then 1 else 0

/-- Sum of arbitrary one-site operators on the two factors. -/
def twoSiteOneBody (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ B)

/-- The exposed interchange has a unit matrix coefficient between the two
first-chaos basis vectors, while every sum of one-site operators has zero
there.  This is the norm-one separating functional behind the distance and
simultaneous-shorting clause. -/
theorem exposedSwap_unit_separatingCoefficient
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (twoSiteSwap - 1 - twoSiteOneBody A B) (0, 1) (1, 0) = 1 := by
  simp [twoSiteSwap, twoSiteOneBody, Matrix.kroneckerMap_apply]

/-- Squared `L²` norm in the orthonormal Walsh basis. -/
def walshNormSq {V : Type*} [Fintype V] (f : Finset V → ℝ) : ℝ :=
  ∑ A, (f A) ^ 2

/-- Diagonal renewal energy: the Walsh word on `A` has eigenvalue `g |A|`. -/
def renewalWalshEnergy {V : Type*} [Fintype V]
    (g : ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ A, g * A.card * (f A) ^ 2

/-- Relabel a Walsh support by the transposition of two vertices. -/
def swapSupport {V : Type*} [DecidableEq V]
    (i j : V) (A : Finset V) : Finset V :=
  A.image (Equiv.swap i j)

/-- Genuine interchange Dirichlet energy on Walsh coefficients. -/
noncomputable def interchangeWalshEnergy {V : Type*} [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (f : Finset V → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ p ∈ edges, kappa p.1 p.2 *
    ∑ A, (f A - f (swapSupport p.1 p.2 A)) ^ 2

/-- The symmetric first-chaos coefficient vector. -/
def symmetricFirstChaos {V : Type*} (A : Finset V) : ℝ :=
  if A.card = 1 then 1 else 0

/-- Embed arbitrary vertex coefficients into the singleton Walsh sector. -/
def firstChaosCoefficients {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℝ) (A : Finset V) : ℝ :=
  ∑ v, if A = {v} then c v else 0

/-- Graph interchange Laplacian written directly from the exposed edge list. -/
def edgeCoefficientLaplacian {V : Type*} [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (c : V → ℝ) (v : V) : ℝ :=
  ∑ p ∈ edges, kappa p.1 p.2 *
    (c (Equiv.swap p.1 p.2 v) - c v)

/-- Concrete renewal--interchange generator on every Walsh coefficient. -/
def walshInterchangeGenerator {V : Type*} [Fintype V] [DecidableEq V]
    (g : ℝ) (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (f : Finset V → ℝ) (A : Finset V) : ℝ :=
  -g * A.card * f A + ∑ p ∈ edges, kappa p.1 p.2 *
    (f (swapSupport p.1 p.2 A) - f A)

private theorem firstChaosCoefficients_eq_zero_of_card_ne_one {V : Type*}
    [Fintype V] [DecidableEq V] (c : V → ℝ) (A : Finset V)
    (hA : A.card ≠ 1) :
    firstChaosCoefficients c A = 0 := by
  rw [firstChaosCoefficients]
  apply Finset.sum_eq_zero
  intro v _
  have hne : A ≠ {v} := by
    intro h
    apply hA
    rw [h]
    simp
  simp [hne]

/-- Direct computation of the generator on the singleton Walsh sector.  No
per-generator action is assumed. -/
theorem concrete_firstChaos_reactionDiffusion {V : Type*}
    [Fintype V] [DecidableEq V]
    (g : ℝ) (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (c : V → ℝ) :
    walshInterchangeGenerator g edges kappa (firstChaosCoefficients c) =
      firstChaosCoefficients
        (fun v => edgeCoefficientLaplacian edges kappa c v - g * c v) := by
  funext A
  by_cases hA : A.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hA
    simp [walshInterchangeGenerator, firstChaosCoefficients,
      edgeCoefficientLaplacian, swapSupport]
    ring
  · have hswap : ∀ p : V × V,
        (swapSupport p.1 p.2 A).card ≠ 1 := by
      intro p hp
      apply hA
      rw [← hp]
      simpa only [swapSupport] using
        (Finset.card_image_of_injective A (Equiv.swap p.1 p.2).injective).symm
    rw [walshInterchangeGenerator,
      firstChaosCoefficients_eq_zero_of_card_ne_one c A hA,
      firstChaosCoefficients_eq_zero_of_card_ne_one
        (fun v => edgeCoefficientLaplacian edges kappa c v - g * c v) A hA]
    simp only [mul_zero, zero_add]
    apply Finset.sum_eq_zero
    intro p hp
    rw [firstChaosCoefficients_eq_zero_of_card_ne_one c _ (hswap p)]
    simp

/-- Every mean-zero Walsh expansion has renewal energy at least `g` times its
norm.  This is the genuine tensorized one-site floor. -/
theorem renewalWalshEnergy_floor {V : Type*} [Fintype V]
    (g : ℝ) (hg : 0 ≤ g) (f : Finset V → ℝ) (hmean : f ∅ = 0) :
    g * walshNormSq f ≤ renewalWalshEnergy g f := by
  rw [walshNormSq, renewalWalshEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A = ∅
  · subst A
    simp [hmean]
  · have hcard : 1 ≤ A.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hA)
    have hsquare : 0 ≤ (f A) ^ 2 := sq_nonneg _
    have hcardR : (1 : ℝ) ≤ A.card := by exact_mod_cast hcard
    calc
      g * (f A) ^ 2 = (g * 1) * (f A) ^ 2 := by ring
      _ ≤ (g * (A.card : ℝ)) * (f A) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcardR hg) hsquare
      _ = g * (A.card : ℝ) * (f A) ^ 2 := rfl

/-- Swap energy is nonnegative for every nonnegative rate family. -/
theorem interchangeWalshEnergy_nonneg {V : Type*}
    [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (hkappa : ∀ p ∈ edges, 0 ≤ kappa p.1 p.2)
    (f : Finset V → ℝ) :
    0 ≤ interchangeWalshEnergy edges kappa f := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (hkappa p hp)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Vertex transpositions preserve subset cardinality, so the symmetric
first-chaos vector is fixed by every interchange. -/
theorem symmetricFirstChaos_swapInvariant {V : Type*} [DecidableEq V]
    (i j : V) (A : Finset V) :
    symmetricFirstChaos (swapSupport i j A) = symmetricFirstChaos A := by
  have hcard : (swapSupport i j A).card = A.card := by
    exact Finset.card_image_of_injective A (Equiv.swap i j).injective
  simp only [symmetricFirstChaos, hcard]

/-- The symmetric first-chaos vector has renewal energy exactly `g` times its
Walsh norm and zero interchange energy. -/
theorem symmetricFirstChaos_sharp {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (g : ℝ) (edges : Finset (V × V)) (kappa : V → V → ℝ) :
    symmetricFirstChaos (V := V) ∅ = 0 ∧
      0 < walshNormSq (symmetricFirstChaos (V := V)) ∧
      renewalWalshEnergy g (symmetricFirstChaos (V := V)) =
        g * walshNormSq (symmetricFirstChaos (V := V)) ∧
      interchangeWalshEnergy edges kappa (symmetricFirstChaos (V := V)) = 0 := by
  classical
  have hinv : ∀ p : V × V, ∀ A : Finset V,
      symmetricFirstChaos (swapSupport p.1 p.2 A) = symmetricFirstChaos A :=
    fun p A => symmetricFirstChaos_swapInvariant p.1 p.2 A
  refine ⟨by simp [symmetricFirstChaos], ?_, ?_, ?_⟩
  · obtain ⟨v⟩ := ‹Nonempty V›
    have hterm : (1 : ℝ) ≤ walshNormSq (symmetricFirstChaos (V := V)) := by
      rw [walshNormSq]
      have hle := Finset.single_le_sum
        (s := (Finset.univ : Finset (Finset V)))
        (f := fun A => (symmetricFirstChaos (V := V) A) ^ 2)
        (fun A _ => sq_nonneg _) (Finset.mem_univ ({v} : Finset V))
      simpa [symmetricFirstChaos] using hle
    linarith
  · rw [renewalWalshEnergy, walshNormSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hcard : A.card = 1
    · simp [symmetricFirstChaos, hcard]
    · simp [symmetricFirstChaos, hcard]
  · simp [interchangeWalshEnergy, hinv]

/-- Exact sharp gap of the full renewal--interchange energy. -/
theorem renewalInterchange_exactGap {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (lam : ℝ) (hlam : 0 ≤ lam)
    (edges : Finset (V × V)) (kappa : V → V → ℝ)
    (hkappa : ∀ p ∈ edges, 0 ≤ kappa p.1 p.2) :
    let g := 22 * lam / 15
    (∀ f : Finset V → ℝ, f ∅ = 0 →
      g * walshNormSq f ≤
        renewalWalshEnergy g f + interchangeWalshEnergy edges kappa f) ∧
    ∃ f : Finset V → ℝ,
      f ∅ = 0 ∧ 0 < walshNormSq f ∧
      renewalWalshEnergy g f + interchangeWalshEnergy edges kappa f =
        g * walshNormSq f := by
  dsimp only
  have hg : 0 ≤ 22 * lam / 15 := by positivity
  constructor
  · intro f hmean
    exact (renewalWalshEnergy_floor _ hg f hmean).trans
      (le_add_of_nonneg_right (interchangeWalshEnergy_nonneg edges kappa hkappa f))
  · refine ⟨symmetricFirstChaos, ?_⟩
    obtain ⟨hmean, hnorm, hrenew, hswap⟩ :=
      symmetricFirstChaos_sharp (V := V) (22 * lam / 15) edges kappa
    exact ⟨hmean, hnorm, by rw [hrenew, hswap, add_zero]⟩

end RenewalInterchangeWalshGap
end NCG
