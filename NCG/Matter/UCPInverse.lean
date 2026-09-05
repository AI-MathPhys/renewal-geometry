/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The UCP inverse theorem (`thm:ucp-unit`, SM_emergence)

A unital `2`-positive (in particular completely positive) map `Ψ` on a
finite-dimensional matrix factor with a `2`-positive two-sided inverse
is a `*`-automorphism.

* `amp2` / `TwoPositive` — the `M₂(A)` amplification and
  `2`-positivity;
* `kadison_schwarz` — the Kadison–Schwarz inequality
  `Ψ(a*a) ⪰ Ψ(a)*Ψ(a)` for unital `2`-positive `Ψ`, via the block
  certificate `[[1, a],[a*, a*a]] = B*B ⪰ 0` and the Schur defect;
* `ucp_inverse_automorphism` — the UCP inverse theorem: squeezing the
  Schwarz inequality through the inverse forces equality in the
  multiplicative-domain inequality for every element, and polarization
  upgrades it to full multiplicativity: `Ψ` is a bijective unital
  `*`-homomorphism (`thm:ucp-unit`).

The inverse `Φ` needs only `2`-positivity and the two inverse
identities: its unitality and `*`-preservation are derived.
-/

namespace NCG.UCP

open Matrix

open scoped ComplexOrder

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma star_sum_elim {s n : Type*} (x : s → ℂ) (y : n → ℂ) :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  funext i
  cases i <;> rfl

/-- The `2`-amplification of a linear map, acting blockwise on
`M₂(A) = A ⊗ M₂`. -/
def amp2 (Ψ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (M : Matrix (d ⊕ d) (d ⊕ d) ℂ) : Matrix (d ⊕ d) (d ⊕ d) ℂ :=
  Matrix.fromBlocks (Ψ M.toBlocks₁₁) (Ψ M.toBlocks₁₂)
    (Ψ M.toBlocks₂₁) (Ψ M.toBlocks₂₂)

/-- `2`-positivity of a linear map on the matrix factor. -/
def TwoPositive (Ψ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : Prop :=
  ∀ M : Matrix (d ⊕ d) (d ⊕ d) ℂ, M.PosSemidef → (amp2 Ψ M).PosSemidef

omit [Fintype d] [DecidableEq d] in
private lemma corner_psd [Finite d] {M : Matrix d d ℂ}
    (hM : M.PosSemidef) :
    (Matrix.fromBlocks M 0 0 (0 : Matrix d d ℂ)).PosSemidef := by
  haveI := Fintype.ofFinite d
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (Matrix.fromBlocks M 0 0 (0 : Matrix d d ℂ))ᴴ = _
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hM.1]
  · intro v
    obtain ⟨x, y, rfl⟩ : ∃ x y, v = Sum.elim x y :=
      ⟨v ∘ Sum.inl, v ∘ Sum.inr, (Sum.elim_comp_inl_inr v).symm⟩
    have h := hM.dotProduct_mulVec_nonneg x
    rw [Matrix.fromBlocks_mulVec, star_sum_elim, sumElim_dotProduct_sumElim]
    simpa using h

omit [Fintype d] [DecidableEq d] in
private lemma psd_block₁₁ [Finite d] {A B C D : Matrix d d ℂ}
    (h : (Matrix.fromBlocks A B C D).PosSemidef) : A.PosSemidef := by
  haveI := Fintype.ofFinite d
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hh : Aᴴ = A := by
      have hc := congrArg Matrix.toBlocks₁₁ h.1
      simpa [Matrix.fromBlocks_conjTranspose] using hc
    exact hh
  · intro x
    have hq := h.dotProduct_mulVec_nonneg (Sum.elim x 0)
    rw [Matrix.fromBlocks_mulVec, star_sum_elim,
      sumElim_dotProduct_sumElim] at hq
    simpa using hq

omit [Fintype d] [DecidableEq d] in
/-- `1`-positivity follows from `2`-positivity by corner embedding. -/
theorem pos_of_two_positive [Finite d]
    {Ψ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ}
    (hΨ2 : TwoPositive Ψ) {M : Matrix d d ℂ} (hM : M.PosSemidef) :
    (Ψ M).PosSemidef := by
  have h := hΨ2 _ (corner_psd hM)
  rw [amp2] at h
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
    map_zero] at h
  exact psd_block₁₁ h

private lemma schur_defect {X Y : Matrix d d ℂ}
    (h : (Matrix.fromBlocks 1 X Xᴴ Y).PosSemidef) :
    (Y - Xᴴ * X).PosSemidef := by
  have hYh : Yᴴ = Y := by
    have hh := congrArg Matrix.toBlocks₂₂ h.1
    simpa [Matrix.fromBlocks_conjTranspose] using hh
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (Y - Xᴴ * X)ᴴ = Y - Xᴴ * X
    rw [Matrix.conjTranspose_sub, hYh, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  · intro v
    have hq := h.dotProduct_mulVec_nonneg (Sum.elim (-(X *ᵥ v)) v)
    have hadj : ∀ w u : d → ℂ,
        star u ⬝ᵥ (Xᴴ *ᵥ w) = star (X *ᵥ u) ⬝ᵥ w := by
      intro w u
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]
    have key : star (Sum.elim (-(X *ᵥ v)) v)
        ⬝ᵥ ((Matrix.fromBlocks 1 X Xᴴ Y) *ᵥ Sum.elim (-(X *ᵥ v)) v)
        = star v ⬝ᵥ ((Y - Xᴴ * X) *ᵥ v) := by
      rw [Matrix.fromBlocks_mulVec, star_sum_elim,
        sumElim_dotProduct_sumElim]
      have e1 : (Sum.elim (-(X *ᵥ v)) v ∘ Sum.inl) = -(X *ᵥ v) := rfl
      have e2 : (Sum.elim (-(X *ᵥ v)) v ∘ Sum.inr) = v := rfl
      rw [e1, e2]
      simp only [Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_neg,
        star_neg, neg_dotProduct, dotProduct_neg, dotProduct_add,
        dotProduct_sub, ← Matrix.mulVec_mulVec, hadj]
      ring
    rw [key] at hq
    exact hq

/-- The Kadison–Schwarz inequality: for a unital `2`-positive map,
`Ψ(a*a) ⪰ Ψ(a)*Ψ(a)`. -/
theorem kadison_schwarz {Ψ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ}
    (hΨ1 : Ψ 1 = 1) (hΨs : ∀ a, Ψ aᴴ = (Ψ a)ᴴ) (hΨ2 : TwoPositive Ψ)
    (a : Matrix d d ℂ) :
    (Ψ (aᴴ * a) - (Ψ a)ᴴ * Ψ a).PosSemidef := by
  have hC : (Matrix.fromBlocks 1 a aᴴ (aᴴ * a)).PosSemidef := by
    have hfac : Matrix.fromBlocks (1 : Matrix d d ℂ) a aᴴ (aᴴ * a)
        = (Matrix.fromBlocks 1 a 0 0)ᴴ * Matrix.fromBlocks 1 a 0 0 := by
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      simp
    rw [hfac]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have h2 := hΨ2 _ hC
  rw [amp2] at h2
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
    hΨ1, hΨs] at h2
  exact schur_defect h2

omit [DecidableEq d] in
private lemma eq_zero_of_quadratic {X : Matrix d d ℂ}
    (h : ∀ v : d → ℂ, star v ⬝ᵥ (X *ᵥ v) = 0) : X = 0 := by
  classical
  have hb : ∀ v w : d → ℂ,
      star v ⬝ᵥ (X *ᵥ w) + star w ⬝ᵥ (X *ᵥ v) = 0 := by
    intro v w
    have h1 := h (v + w)
    have h2 := h v
    have h3 := h w
    simp only [star_add, Matrix.mulVec_add, add_dotProduct,
      dotProduct_add] at h1
    linear_combination h1 - h2 - h3
  have hsymm : ∀ v w : d → ℂ,
      star v ⬝ᵥ (X *ᵥ w) = star w ⬝ᵥ (X *ᵥ v) := by
    intro v w
    have h1 := hb v (Complex.I • w)
    simp only [Matrix.mulVec_smul, dotProduct_smul, star_smul,
      smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_I] at h1
    have h3 : Complex.I * (star v ⬝ᵥ (X *ᵥ w) - star w ⬝ᵥ (X *ᵥ v))
        = Complex.I * 0 := by
      rw [mul_zero]
      linear_combination h1
    exact sub_eq_zero.mp (mul_left_cancel₀ Complex.I_ne_zero h3)
  have hzero : ∀ v w : d → ℂ, star v ⬝ᵥ (X *ᵥ w) = 0 := by
    intro v w
    linear_combination (1 / 2 : ℂ) * hb v w + (1 / 2 : ℂ) * hsymm v w
  ext i j
  have hij := hzero (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_ite_eq'] using hij

omit [Fintype d] [DecidableEq d] in
private lemma psd_add_eq_zero [Finite d] {X Y : Matrix d d ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X + Y = 0) : X = 0 := by
  haveI := Fintype.ofFinite d
  refine eq_zero_of_quadratic fun v => ?_
  have h1 := hX.dotProduct_mulVec_nonneg v
  have h2 := hY.dotProduct_mulVec_nonneg v
  have h3 : star v ⬝ᵥ (X *ᵥ v) + star v ⬝ᵥ (Y *ᵥ v) = 0 := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, hXY,
      Matrix.zero_mulVec, dotProduct_zero]
  have hle : star v ⬝ᵥ (X *ᵥ v) ≤ 0 := by
    calc star v ⬝ᵥ (X *ᵥ v) = -(star v ⬝ᵥ (Y *ᵥ v)) := by
          linear_combination h3
    _ ≤ 0 := neg_nonpos.mpr h2
  exact le_antisymm hle h1

/-- `thm:ucp-unit` (UCP inverse theorem): a unital `2`-positive map on
a finite matrix factor with a `2`-positive two-sided inverse is a
`*`-automorphism: multiplicative, `*`-preserving, and bijective.  The
inverse needs only `2`-positivity — its unitality and `*`-preservation
are derived from the inverse identities. -/
theorem ucp_inverse_automorphism
    (Ψ Φ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hΨ1 : Ψ 1 = 1) (hΨs : ∀ a, Ψ aᴴ = (Ψ a)ᴴ) (hΨ2 : TwoPositive Ψ)
    (hΦ2 : TwoPositive Φ)
    (hΦΨ : ∀ a, Φ (Ψ a) = a) (hΨΦ : ∀ a, Ψ (Φ a) = a) :
    (∀ x y, Ψ (x * y) = Ψ x * Ψ y) ∧ (∀ x, Ψ xᴴ = (Ψ x)ᴴ)
      ∧ Function.Bijective Ψ := by
  -- the inverse is automatically unital and star-preserving
  have hΦ1 : Φ 1 = 1 := by
    conv_lhs => rw [← hΨ1]
    rw [hΦΨ]
  have hΦs : ∀ a, Φ aᴴ = (Φ a)ᴴ := by
    intro a
    conv_lhs => rw [← hΨΦ a, ← hΨs, hΦΨ]
  -- Schwarz equality for every element
  have hKSeq : ∀ a, Ψ (aᴴ * a) = (Ψ a)ᴴ * Ψ a := by
    intro a
    have hS1 : (Φ (Ψ (aᴴ * a)) - Φ ((Ψ a)ᴴ * Ψ a)).PosSemidef := by
      have hp := pos_of_two_positive hΦ2 (kadison_schwarz hΨ1 hΨs hΨ2 a)
      rwa [map_sub] at hp
    have hS2 : (Φ ((Ψ a)ᴴ * Ψ a) - (Φ (Ψ a))ᴴ * Φ (Ψ a)).PosSemidef :=
      kadison_schwarz hΦ1 hΦs hΦ2 (Ψ a)
    have hsum : (Φ (Ψ (aᴴ * a)) - Φ ((Ψ a)ᴴ * Ψ a))
        + (Φ ((Ψ a)ᴴ * Ψ a) - (Φ (Ψ a))ᴴ * Φ (Ψ a)) = 0 := by
      rw [hΦΨ (aᴴ * a), hΦΨ a]
      abel
    have h0 := psd_add_eq_zero hS1 hS2 hsum
    have hinj : Function.Injective Φ := fun x y hxy => by
      have hc := congrArg Ψ hxy
      rwa [hΨΦ, hΨΦ] at hc
    exact hinj (sub_eq_zero.mp h0)
  -- polarization: the sesquilinear defect vanishes identically
  have hB : ∀ x y, Ψ (xᴴ * y) = (Ψ x)ᴴ * Ψ y := by
    have hdiag : ∀ x, Ψ (xᴴ * x) - (Ψ x)ᴴ * Ψ x = 0 := fun x =>
      sub_eq_zero_of_eq (hKSeq x)
    have hadd : ∀ x y, (Ψ (xᴴ * y) - (Ψ x)ᴴ * Ψ y)
        + (Ψ (yᴴ * x) - (Ψ y)ᴴ * Ψ x) = 0 := by
      intro x y
      have h1 := hdiag (x + y)
      have h2 := hdiag x
      have h3 := hdiag y
      simp only [Matrix.conjTranspose_add, map_add, add_mul,
        mul_add] at h1
      linear_combination (norm := module) h1 - h2 - h3
    have hsymm : ∀ x y, Ψ (xᴴ * y) - (Ψ x)ᴴ * Ψ y
        = Ψ (yᴴ * x) - (Ψ y)ᴴ * Ψ x := by
      intro x y
      have h1 := hadd x (Complex.I • y)
      simp only [Matrix.conjTranspose_smul, map_smul, map_neg, neg_mul,
        smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I,
        neg_smul] at h1
      have h3 : Complex.I • ((Ψ (xᴴ * y) - (Ψ x)ᴴ * Ψ y)
            - (Ψ (yᴴ * x) - (Ψ y)ᴴ * Ψ x))
          = Complex.I • (0 : Matrix d d ℂ) := by
        rw [smul_zero]
        linear_combination (norm := module) h1
      have h4 := smul_right_injective (Matrix d d ℂ)
        Complex.I_ne_zero h3
      exact sub_eq_zero.mp h4
    intro x y
    have h1 := hadd x y
    have h2 := hsymm x y
    have h3 : (2 : ℂ) • (Ψ (xᴴ * y) - (Ψ x)ᴴ * Ψ y) = 0 := by
      rw [two_smul]
      linear_combination (norm := module) h1 + h2
    have h3' : (2 : ℂ) • (Ψ (xᴴ * y) - (Ψ x)ᴴ * Ψ y)
        = (2 : ℂ) • (0 : Matrix d d ℂ) := by
      rw [smul_zero]
      exact h3
    have h4 := smul_right_injective (Matrix d d ℂ) two_ne_zero h3'
    exact sub_eq_zero.mp h4
  refine ⟨fun x y => ?_, hΨs,
    Function.LeftInverse.injective hΦΨ,
    Function.RightInverse.surjective hΨΦ⟩
  have hxy := hB xᴴ y
  rwa [Matrix.conjTranspose_conjTranspose, hΨs,
    Matrix.conjTranspose_conjTranspose] at hxy

end

end NCG.UCP
