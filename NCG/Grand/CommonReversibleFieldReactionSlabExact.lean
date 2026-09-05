/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.YMDoobKoopmanPathLawExact

/-!
# Common reversible field--reaction slab

This file proves the finite, literal content of
`thm:SMFS-common-reversible-slab`.  Three conservative reversible generators
are added on the product field--particle law.  Uniformization constructs a
stationary two-sided cylinder law for their sum, the independent particle and
field gaps combine with the sharp minimum constant, a nonnegative reaction
form cannot lower that gap, and conditional independence of the two path
halves gives the exact Osterwalder--Schrader square.  Product marginalization
also proves that every inherited charge moment (in particular the Green
writer and fourth cumulant inputs) is unchanged.
-/

open Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace NCG.CommonReversibleFieldReactionSlab

variable {X Y A H : Type*}

/-- The literal common law `Π_λ ⊗ ν_n` from (FS.28). -/
def productLaw (particleLaw : X → ℝ) (fieldLaw : Y → ℝ) : X × Y → ℝ :=
  fun z => particleLaw z.1 * fieldLaw z.2

theorem productLaw_nonnegative [Fintype X] [Fintype Y]
    (particleLaw : X → ℝ) (fieldLaw : Y → ℝ)
    (hp : ∀ x, 0 ≤ particleLaw x) (hf : ∀ y, 0 ≤ fieldLaw y) :
    ∀ z, 0 ≤ productLaw particleLaw fieldLaw z := by
  intro z
  exact mul_nonneg (hp z.1) (hf z.2)

theorem productLaw_normalized [Fintype X] [Fintype Y]
    (particleLaw : X → ℝ) (fieldLaw : Y → ℝ)
    (hp : ∑ x, particleLaw x = 1) (hf : ∑ y, fieldLaw y = 1) :
    ∑ z, productLaw particleLaw fieldLaw z = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [productLaw, ← Finset.mul_sum, hf, mul_one, hp]

/-- Action of a finite continuous-time generator on a writer. -/
def generatorAction [Fintype A] (L : A → A → ℝ) (f : A → ℝ) (x : A) : ℝ :=
  ∑ y, L x y * f y

/-- The weighted Dirichlet form `-⟨f,Lf⟩_μ`. -/
def dirichletForm [Fintype A] (mu : A → ℝ) (L : A → A → ℝ)
    (f : A → ℝ) : ℝ :=
  -∑ x, mu x * f x * generatorAction L f x

/-- Pointwise sum of the particle, reaction, and field generators. -/
def commonGenerator (Lparticle Lreaction Lfield : A → A → ℝ) : A → A → ℝ :=
  fun x y => Lparticle x y + Lreaction x y + Lfield x y

theorem commonGenerator_rows_zero [Fintype A]
    (Lparticle Lreaction Lfield : A → A → ℝ)
    (hp : ∀ x, ∑ y, Lparticle x y = 0)
    (hr : ∀ x, ∑ y, Lreaction x y = 0)
    (hf : ∀ x, ∑ y, Lfield x y = 0) :
    ∀ x, ∑ y, commonGenerator Lparticle Lreaction Lfield x y = 0 := by
  intro x
  simp [commonGenerator, Finset.sum_add_distrib, hp x, hr x, hf x]

theorem commonGenerator_offDiagonal_nonnegative
    (Lparticle Lreaction Lfield : A → A → ℝ)
    (hp : ∀ x y, x ≠ y → 0 ≤ Lparticle x y)
    (hr : ∀ x y, x ≠ y → 0 ≤ Lreaction x y)
    (hf : ∀ x y, x ≠ y → 0 ≤ Lfield x y) :
    ∀ x y, x ≠ y → 0 ≤ commonGenerator Lparticle Lreaction Lfield x y := by
  intro x y hxy
  exact add_nonneg (add_nonneg (hp x y hxy) (hr x y hxy)) (hf x y hxy)

theorem commonGenerator_reversible (mu : A → ℝ)
    (Lparticle Lreaction Lfield : A → A → ℝ)
    (hp : ∀ x y, mu x * Lparticle x y = mu y * Lparticle y x)
    (hr : ∀ x y, mu x * Lreaction x y = mu y * Lreaction y x)
    (hf : ∀ x y, mu x * Lfield x y = mu y * Lfield y x) :
    ∀ x y, mu x * commonGenerator Lparticle Lreaction Lfield x y =
      mu y * commonGenerator Lparticle Lreaction Lfield y x := by
  intro x y
  simp only [commonGenerator]
  rw [mul_add, mul_add, mul_add, mul_add, hp x y, hr x y, hf x y]

theorem dirichletForm_commonGenerator [Fintype A]
    (mu : A → ℝ) (Lparticle Lreaction Lfield : A → A → ℝ)
    (f : A → ℝ) :
    dirichletForm mu (commonGenerator Lparticle Lreaction Lfield) f =
      dirichletForm mu Lparticle f + dirichletForm mu Lreaction f +
        dirichletForm mu Lfield f := by
  have haction (x : A) :
      generatorAction (commonGenerator Lparticle Lreaction Lfield) f x =
        generatorAction Lparticle f x + generatorAction Lreaction f x +
          generatorAction Lfield f x := by
    unfold generatorAction commonGenerator
    simp_rw [add_mul, Finset.sum_add_distrib]
  unfold dirichletForm
  simp_rw [haction]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Uniformization of a bounded finite generator. -/
def uniformizedKernel [DecidableEq A] (L : A → A → ℝ) (rate : ℝ) :
    A → A → ℝ :=
  fun x y => (if x = y then 1 else 0) + L x y / rate

theorem uniformizedKernel_nonnegative [Fintype A] [DecidableEq A]
    (L : A → A → ℝ) (rate : ℝ) (hrate : 0 < rate)
    (hoff : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hexit : ∀ x, -L x x ≤ rate) :
    ∀ x y, 0 ≤ uniformizedKernel L rate x y := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp only [uniformizedKernel, if_pos]
    rw [show 1 + L x x / rate = (rate + L x x) / rate by
      field_simp]
    exact div_nonneg (by linarith [hexit x]) hrate.le
  · simp only [uniformizedKernel, if_neg hxy, zero_add]
    exact div_nonneg (hoff x y hxy) hrate.le

theorem uniformizedKernel_rows_one [Fintype A] [DecidableEq A]
    (L : A → A → ℝ) (rate : ℝ) (hrate : rate ≠ 0)
    (hrow : ∀ x, ∑ y, L x y = 0) :
    ∀ x, ∑ y, uniformizedKernel L rate x y = 1 := by
  intro x
  simp only [uniformizedKernel, Finset.sum_add_distrib]
  rw [← Finset.sum_div, hrow x, zero_div, add_zero]
  simp

theorem uniformizedKernel_reversible [Fintype A] [DecidableEq A]
    (mu : A → ℝ) (L : A → A → ℝ) (rate : ℝ)
    (hrev : ∀ x y, mu x * L x y = mu y * L y x) :
    ∀ x y, mu x * uniformizedKernel L rate x y =
      mu y * uniformizedKernel L rate y x := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    simp only [uniformizedKernel, if_neg hxy, if_neg hyx, zero_add]
    rw [← mul_div_assoc, ← mul_div_assoc, hrev x y]

/-- The minimum of the independent particle and field gaps is retained after
adding any nonnegative reaction form. -/
theorem minimum_gap_of_variance_split [Fintype A]
    (mu : A → ℝ) (Lparticle Lreaction Lfield : A → A → ℝ)
    (particleVariance fieldVariance : (A → ℝ) → ℝ)
    (variance : (A → ℝ) → ℝ) (particleGap fieldGap : ℝ)
    (hparticleGap : 0 ≤ particleGap) (hfieldGap : 0 ≤ fieldGap)
    (hsplit : ∀ f, variance f = particleVariance f + fieldVariance f)
    (hpVar : ∀ f, 0 ≤ particleVariance f)
    (hfVar : ∀ f, 0 ≤ fieldVariance f)
    (hp : ∀ f, particleGap * particleVariance f ≤
      dirichletForm mu Lparticle f)
    (hf : ∀ f, fieldGap * fieldVariance f ≤
      dirichletForm mu Lfield f)
    (hr : ∀ f, 0 ≤ dirichletForm mu Lreaction f) :
    ∀ f, min particleGap fieldGap * variance f ≤
      dirichletForm mu (commonGenerator Lparticle Lreaction Lfield) f := by
  intro f
  rw [dirichletForm_commonGenerator, hsplit]
  calc
    min particleGap fieldGap * (particleVariance f + fieldVariance f) =
        min particleGap fieldGap * particleVariance f +
          min particleGap fieldGap * fieldVariance f := by ring
    _ ≤ particleGap * particleVariance f + fieldGap * fieldVariance f := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (hpVar f))
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (hfVar f))
    _ ≤ dirichletForm mu Lparticle f + dirichletForm mu Lfield f :=
      add_le_add (hp f) (hf f)
    _ ≤ dirichletForm mu Lparticle f + dirichletForm mu Lreaction f +
          dirichletForm mu Lfield f := by linarith [hr f]

/-- Conditional future expectation given the time-zero state. -/
def conditionalFuture [Fintype H] (K : A → H → ℝ) (F : A → H → ℂ)
    (x : A) : ℂ :=
  ∑ h, (K x h : ℂ) * F x h

/-- Expectation of the reflected product under two conditionally independent
path halves. -/
def osExpectation [Fintype A] [Fintype H]
    (mu : A → ℝ) (K : A → H → ℝ) (F : A → H → ℂ) : ℂ :=
  ∑ x, (mu x : ℂ) *
    (∑ hp, (K x hp : ℂ) * star (F x hp)) *
    (∑ hf, (K x hf : ℂ) * F x hf)

/-- Exact Markov Osterwalder--Schrader square (FS.30). -/
theorem osExpectation_eq_square [Fintype A] [Fintype H]
    (mu : A → ℝ) (K : A → H → ℝ) (F : A → H → ℂ) :
    osExpectation mu K F =
      ∑ x, (mu x : ℂ) * star (conditionalFuture K F x) *
        conditionalFuture K F x := by
  unfold osExpectation conditionalFuture
  apply Finset.sum_congr rfl
  intro x _
  have hstar :
      star (∑ h, (K x h : ℂ) * F x h) =
        ∑ h, (K x h : ℂ) * star (F x h) := by
    change (starRingEnd ℂ) (∑ h, (K x h : ℂ) * F x h) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro h _
    simp
  rw [hstar]

theorem osExpectation_nonnegative [Fintype A] [Fintype H]
    (mu : A → ℝ) (K : A → H → ℝ) (F : A → H → ℂ)
    (hmu : ∀ x, 0 ≤ mu x) :
    0 ≤ (osExpectation mu K F).re := by
  rw [osExpectation_eq_square]
  have hre (x : A) :
      ((mu x : ℂ) * star (conditionalFuture K F x) *
        conditionalFuture K F x).re =
      mu x * Complex.normSq (conditionalFuture K F x) := by
    rw [mul_assoc]
    change ((mu x : ℂ) *
      (conj (conditionalFuture K F x) * conditionalFuture K F x)).re = _
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  rw [Complex.re_sum]
  simp_rw [hre]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (hmu x) (Complex.normSq_nonneg _)

/-- Product marginalization preserves every particle-only moment. -/
theorem productLaw_particleMoment [Fintype X] [Fintype Y]
    (particleLaw : X → ℝ) (fieldLaw : Y → ℝ)
    (hfield : ∑ y, fieldLaw y = 1) (q : X → ℝ) (k : ℕ) :
    ∑ z : X × Y, productLaw particleLaw fieldLaw z * (q z.1) ^ k =
      ∑ x, particleLaw x * (q x) ^ k := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [productLaw]
  rw [show (∑ y, particleLaw x * fieldLaw y * q x ^ k) =
      particleLaw x * q x ^ k * ∑ y, fieldLaw y by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring]
  rw [hfield, mul_one]

/-- **`thm:SMFS-common-reversible-slab`, exact finite form.**  The theorem
returns the normalized common law, reversibility and Markov normalization of
the physical uniformized sum generator, its stationary two-sided cylinder
law, the sharp minimum gap, the OS square and positivity for every finite
positive-time history writer, and preservation of all inherited charge
moments (hence in particular orders two and four). -/
theorem common_reversible_field_reaction_slab
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [Fintype H]
    (particleLaw : X → ℝ) (fieldLaw : Y → ℝ)
    (hp0 : ∀ x, 0 ≤ particleLaw x) (hf0 : ∀ y, 0 ≤ fieldLaw y)
    (hp1 : ∑ x, particleLaw x = 1) (hf1 : ∑ y, fieldLaw y = 1)
    (Lparticle Lreaction Lfield : X × Y → X × Y → ℝ)
    (hrowsP : ∀ x, ∑ y, Lparticle x y = 0)
    (hrowsR : ∀ x, ∑ y, Lreaction x y = 0)
    (hrowsF : ∀ x, ∑ y, Lfield x y = 0)
    (hoffP : ∀ x y, x ≠ y → 0 ≤ Lparticle x y)
    (hoffR : ∀ x y, x ≠ y → 0 ≤ Lreaction x y)
    (hoffF : ∀ x y, x ≠ y → 0 ≤ Lfield x y)
    (hrevP : ∀ x y, productLaw particleLaw fieldLaw x * Lparticle x y =
      productLaw particleLaw fieldLaw y * Lparticle y x)
    (hrevR : ∀ x y, productLaw particleLaw fieldLaw x * Lreaction x y =
      productLaw particleLaw fieldLaw y * Lreaction y x)
    (hrevF : ∀ x y, productLaw particleLaw fieldLaw x * Lfield x y =
      productLaw particleLaw fieldLaw y * Lfield y x)
    (rate : ℝ) (hrate : 0 < rate)
    (hexit : ∀ x, -commonGenerator Lparticle Lreaction Lfield x x ≤ rate)
    (particleVariance fieldVariance variance : ((X × Y → ℝ) → ℝ))
    (particleGap fieldGap : ℝ)
    (hparticleGap : 0 ≤ particleGap) (hfieldGap : 0 ≤ fieldGap)
    (hsplit : ∀ f, variance f = particleVariance f + fieldVariance f)
    (hpVar : ∀ f, 0 ≤ particleVariance f)
    (hfVar : ∀ f, 0 ≤ fieldVariance f)
    (hgapP : ∀ f, particleGap * particleVariance f ≤
      dirichletForm (productLaw particleLaw fieldLaw) Lparticle f)
    (hgapF : ∀ f, fieldGap * fieldVariance f ≤
      dirichletForm (productLaw particleLaw fieldLaw) Lfield f)
    (hnonnegR : ∀ f, 0 ≤
      dirichletForm (productLaw particleLaw fieldLaw) Lreaction f)
    (historyKernel : X × Y → H → ℝ) (writer : X × Y → H → ℂ)
    (charge : X → ℝ) :
    (∑ z, productLaw particleLaw fieldLaw z = 1) ∧
    (∀ x y, productLaw particleLaw fieldLaw x *
        commonGenerator Lparticle Lreaction Lfield x y =
      productLaw particleLaw fieldLaw y *
        commonGenerator Lparticle Lreaction Lfield y x) ∧
    (∀ x, ∑ y, uniformizedKernel
        (commonGenerator Lparticle Lreaction Lfield) rate x y = 1) ∧
    Nonempty (NCG.YMDoobKoopman.TwoSidedCylinderLaw
      (productLaw particleLaw fieldLaw)
      (uniformizedKernel (commonGenerator Lparticle Lreaction Lfield) rate)) ∧
    (∀ f, min particleGap fieldGap * variance f ≤
      dirichletForm (productLaw particleLaw fieldLaw)
        (commonGenerator Lparticle Lreaction Lfield) f) ∧
    osExpectation (productLaw particleLaw fieldLaw) historyKernel writer =
      ∑ x, (productLaw particleLaw fieldLaw x : ℂ) *
        star (conditionalFuture historyKernel writer x) *
        conditionalFuture historyKernel writer x ∧
    0 ≤ (osExpectation (productLaw particleLaw fieldLaw)
      historyKernel writer).re ∧
    (∀ k, ∑ z : X × Y, productLaw particleLaw fieldLaw z *
        (charge z.1) ^ k = ∑ x, particleLaw x * (charge x) ^ k) := by
  let mu : X × Y → ℝ := productLaw particleLaw fieldLaw
  let L := commonGenerator Lparticle Lreaction Lfield
  let P := uniformizedKernel L rate
  have hmu0 : ∀ z, 0 ≤ mu z :=
    productLaw_nonnegative particleLaw fieldLaw hp0 hf0
  have hmu1 : ∑ z, mu z = 1 :=
    productLaw_normalized particleLaw fieldLaw hp1 hf1
  have hrowL : ∀ x, ∑ y, L x y = 0 :=
    commonGenerator_rows_zero Lparticle Lreaction Lfield hrowsP hrowsR hrowsF
  have hoffL : ∀ x y, x ≠ y → 0 ≤ L x y :=
    commonGenerator_offDiagonal_nonnegative Lparticle Lreaction Lfield
      hoffP hoffR hoffF
  have hrevL : ∀ x y, mu x * L x y = mu y * L y x :=
    commonGenerator_reversible mu Lparticle Lreaction Lfield hrevP hrevR hrevF
  have hP0 : ∀ x y, 0 ≤ P x y :=
    uniformizedKernel_nonnegative L rate hrate hoffL hexit
  have hP1 : ∀ x, ∑ y, P x y = 1 :=
    uniformizedKernel_rows_one L rate hrate.ne' hrowL
  have hPrev : ∀ x y, mu x * P x y = mu y * P y x :=
    uniformizedKernel_reversible mu L rate hrevL
  refine ⟨hmu1, hrevL, hP1,
    NCG.YMDoobKoopman.twoSidedCylinderLaw_exists mu P
      hmu0 hmu1 hP0 hP1 hPrev,
    minimum_gap_of_variance_split mu Lparticle Lreaction Lfield
      particleVariance fieldVariance variance particleGap fieldGap
      hparticleGap hfieldGap hsplit hpVar hfVar hgapP hgapF hnonnegR,
    osExpectation_eq_square mu historyKernel writer,
    osExpectation_nonnegative mu historyKernel writer hmu0,
    fun k => productLaw_particleMoment particleLaw fieldLaw hf1 charge k⟩

end NCG.CommonReversibleFieldReactionSlab
