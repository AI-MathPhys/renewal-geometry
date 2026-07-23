/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.SchwarzMap

/-!
# Kadison–Schwarz, Choi's multiplicative domain, and the predictive-unit theorem

This file supplies the two operator-algebraic inputs of the manuscript's
**predictive-unit theorem** (`thm:predictive-unit`) and assembles the full
result: *a unital completely positive map with a UCP inverse is a
`*`-homomorphism*, so the unit group `𝖴_pred` of the predictive channel
monoid acts by `*`-automorphisms of the internal algebra.

Because `NCG.IsCompletelyPositive` is defined by quadratic-form matrix
amplification, the **Kadison–Schwarz inequality is proved purely
order-algebraically**: the Gram matrix `[[a⋆a, a⋆b], [b⋆a, b⋆b]]` is
quadratic-form positive by an explicit square, and evaluating the amplified
matrix at well-chosen vectors yields both star-preservation and the Schwarz
inequality.  The only analytic ingredient in Choi's multiplicative-domain
theorem is the **Archimedean property** of the order
(`NCG.IsArchimedeanStarOrder`) — satisfied by every C⋆-algebra — which we
isolate as a hypothesis and verify for `ℂ`.

## Main results

* `NCG.matrixQF_pair` — the Gram matrix of a pair is quadratic-form
  positive;
* `NCG.IsCompletelyPositive.map_star` — CP maps are star-preserving;
* `NCG.IsCompletelyPositive.isSchwarzMap` — **Kadison–Schwarz**: a unital
  CP map satisfies `φ(x)⋆ φ(x) ≤ φ(x⋆ x)`;
* `NCG.IsArchimedeanStarOrder`, `NCG.isArchimedeanStarOrder_complex` —
  the Archimedean property, verified for `ℂ`;
* `NCG.multiplicative_of_schwarz_eq` — **Choi's theorem**: equality in the
  Schwarz inequality at `x` gives `φ(x⋆ w) = φ(x)⋆ φ(w)` for all `w`;
* `NCG.UCPMap.unit_map_star`, `NCG.UCPMap.unit_map_mul` — the
  **predictive-unit theorem** (`thm:predictive-unit`): units of the channel
  monoid `UCPMap A` are `*`-homomorphisms.
-/

namespace NCG

/-! ### The Archimedean property -/

/-- A partially ordered star ring is **Archimedean** when a selfadjoint
element all of whose natural multiples are dominated by a single element is
nonpositive.  Every C⋆-algebra satisfies this (apply states and use the
Archimedean property of `ℝ`); `NCG.isArchimedeanStarOrder_complex` verifies
it for `ℂ`.  This is the sole analytic input of Choi's multiplicative-domain
theorem. -/
def IsArchimedeanStarOrder (A : Type*) [Ring A] [PartialOrder A]
    [StarRing A] : Prop :=
  ∀ a d : A, IsSelfAdjoint a → (∀ n : ℕ, n • a ≤ d) → a ≤ 0

section ComplexArchimedean

open scoped ComplexOrder

/-- `ℂ` with its standard partial order is Archimedean. -/
theorem isArchimedeanStarOrder_complex : IsArchimedeanStarOrder ℂ := by
  intro a d _ h
  have hre : ∀ n : ℕ, (n : ℝ) * a.re ≤ d.re ∧ (n : ℝ) * a.im = d.im := by
    intro n
    have hn := h n
    rw [Complex.le_def] at hn
    constructor
    · have h1 := hn.1
      simpa [nsmul_eq_mul, Complex.mul_re] using h1
    · have h2 := hn.2
      simpa [nsmul_eq_mul, Complex.mul_im] using h2
  -- the imaginary part vanishes
  have him : a.im = 0 := by
    have h1 := (hre 1).2
    have h2 := (hre 2).2
    simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2
    linarith
  -- the real part is nonpositive, by the Archimedean property of `ℝ`
  have hle : a.re ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (d.re / a.re)
    have hmul : d.re < (n : ℝ) * a.re := by
      rw [div_lt_iff₀ hpos] at hn
      linarith
    exact absurd (hre n).1 (not_le.mpr hmul)
  rw [Complex.le_def]
  simp [hle, him]

end ComplexArchimedean

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Algebra ℂ A] [StarModule ℂ A]

/-! ### Scalar helpers -/

/-- Multiplication by the square of a natural scalar preserves positivity:
`(m·m) • p = (m•1)⋆ p (m•1) ≥ 0`. -/
theorem sq_natCast_smul_nonneg (m : ℕ) {p : A} (hp : 0 ≤ p) :
    0 ≤ ((m : ℂ) * (m : ℂ)) • p := by
  have h := star_left_conjugate_nonneg hp ((m : ℂ) • (1 : A))
  have hc : star ((m : ℂ) • (1 : A)) * p * ((m : ℂ) • (1 : A))
      = ((m : ℂ) * (m : ℂ)) • p := by
    rw [star_smul, star_one, star_natCast, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_smul]
  rwa [hc] at h

/-- Multiplication by the square of a natural scalar is monotone. -/
theorem sq_natCast_smul_mono (m : ℕ) {x y : A} (h : x ≤ y) :
    ((m : ℂ) * (m : ℂ)) • x ≤ ((m : ℂ) * (m : ℂ)) • y := by
  have h0 := sq_natCast_smul_nonneg m (sub_nonneg.mpr h)
  rw [smul_sub] at h0
  exact sub_nonneg.mp h0

/-- Cancellation of selfadjoint outer terms: if `a + t + b` is selfadjoint
with `a` and `b` selfadjoint, so is the middle term `t`. -/
theorem star_middle_eq {a t b : A} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (h : IsSelfAdjoint (a + t + b)) : star t = t := by
  have hs := h.star_eq
  rw [star_add, star_add, ha.star_eq, hb.star_eq] at hs
  exact add_left_cancel (add_right_cancel hs)

/-! ### The Gram matrix and its quadratic-form positivity -/

/-- The Gram-type `2 × 2` matrix `[[a⋆a, a⋆b], [b⋆a, b⋆b]]` of the
Kadison–Schwarz argument. -/
def pairMatrix (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![star a * a, star a * b], ![star b * a, star b * b]]

/-- The Gram matrix of a pair is quadratic-form positive: the sandwich sum
is the explicit square `(a u₀ + b u₁)⋆ (a u₀ + b u₁)`. -/
theorem matrixQF_pair (a b : A) : MatrixQF (pairMatrix a b) := by
  intro u
  have key : star (a * u 0 + b * u 1) * (a * u 0 + b * u 1)
      = star (u 0) * (star a * a) * u 0 + star (u 0) * (star a * b) * u 1
        + (star (u 1) * (star b * a) * u 0
          + star (u 1) * (star b * b) * u 1) := by
    simp only [star_add, star_mul]
    noncomm_ring
  have h := star_mul_self_nonneg (a * u 0 + b * u 1)
  rw [key] at h
  simpa [pairMatrix, Fin.sum_univ_two] using h

/-! ### Star-preservation and the Kadison–Schwarz inequality -/

section CP

variable {φ : A →ₗ[ℂ] A}

/-- The sandwich sum of the amplified Gram matrix `[[1,x],[x⋆,x⋆x]].map φ`
at the vector `(c•1, 1)`, in middle-grouped form. -/
private theorem gram_sandwich_sum (φ : A →ₗ[ℂ] A) (x : A) (c : ℂ) :
    (∑ i, ∑ j, star ((![c • (1 : A), 1] : Fin 2 → A) i)
        * ((pairMatrix (1 : A) x).map φ) i j
        * ((![c • (1 : A), 1] : Fin 2 → A) j))
      = (c * star c) • φ 1 + (star c • φ x + c • φ (star x))
        + φ (star x * x) := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.map_apply, pairMatrix, Matrix.of_apply,
    star_smul, star_one, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  module

/-- **Completely positive maps are star-preserving**: `φ(x⋆) = φ(x)⋆`.
Extracted from selfadjointness of the amplified Gram sandwich sums at the
vectors `(1, 1)` and `(i·1, 1)`. -/
theorem IsCompletelyPositive.map_star (hφ : IsCompletelyPositive φ) (x : A) :
    φ (star x) = star (φ x) := by
  have hN := hφ 2 (pairMatrix 1 x) (matrixQF_pair 1 x)
  have hφ1 : IsSelfAdjoint (φ 1) :=
    IsSelfAdjoint.of_nonneg (hφ.isPositiveMap 1
      (by simpa using star_mul_self_nonneg (1 : A)))
  have hφxx : IsSelfAdjoint (φ (star x * x)) :=
    IsSelfAdjoint.of_nonneg (hφ.isPositiveMap _ (star_mul_self_nonneg x))
  -- the middle term of the sandwich sum is selfadjoint, for every `c`
  have hmid : ∀ c : ℂ, star (star c • φ x + c • φ (star x))
      = star c • φ x + c • φ (star x) := by
    intro c
    have hsa : IsSelfAdjoint ((c * star c) • φ 1
        + (star c • φ x + c • φ (star x)) + φ (star x * x)) := by
      rw [← gram_sandwich_sum φ x c]
      exact IsSelfAdjoint.of_nonneg (hN _)
    have hu : IsSelfAdjoint ((c * star c) • φ 1) := by
      rw [IsSelfAdjoint, star_smul, star_mul, star_star, hφ1.star_eq]
    exact star_middle_eq hu hφxx hsa
  -- specialize at `c = 1`
  have hA : star (φ x) + star (φ (star x)) = φ x + φ (star x) := by
    have h := hmid 1
    simpa [star_add, star_smul] using h
  -- specialize at `c = i` and clear the `i`s
  have hB : star (φ x) - star (φ (star x)) = -φ x + φ (star x) := by
    have h := hmid Complex.I
    simp only [star_add, star_neg, star_smul, Complex.star_def,
      Complex.conj_I, map_neg, neg_neg, neg_smul] at h
    -- h : I • star (φ x) + -(I • star (φ (star x)))
    --       = -(I • φ x) + I • φ (star x)
    have e1 : (-Complex.I) * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I, neg_neg]
    have h' := congrArg (fun v => (-Complex.I) • v) h
    simp only [smul_add, smul_neg, smul_smul, e1, one_smul, neg_neg] at h'
    -- h' : star (φ x) + -star (φ (star x)) = -φ x + φ (star x)
    rw [sub_eq_add_neg]
    exact h'
  -- combine: `2 · star(φ x) = 2 · φ(x⋆)`
  have h2 : star (φ x) + star (φ x) = φ (star x) + φ (star x) := by
    calc star (φ x) + star (φ x)
        = (star (φ x) + star (φ (star x)))
          + (star (φ x) - star (φ (star x))) := by abel
      _ = (φ x + φ (star x)) + (-φ x + φ (star x)) := by rw [hA, hB]
      _ = φ (star x) + φ (star x) := by abel
  have hs2 : (2 : ℂ) • star (φ x) = (2 : ℂ) • φ (star x) := by
    rw [two_smul, two_smul]
    exact h2
  have h3 := congrArg (fun v => ((2 : ℂ)⁻¹ : ℂ) • v) hs2
  simp only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul] at h3
  exact h3.symm

/-- **The Kadison–Schwarz inequality** (input to `thm:predictive-unit`): a
unital completely positive map satisfies `φ(x)⋆ φ(x) ≤ φ(x⋆ x)`.  Proved by
evaluating the amplified Gram matrix at the vector `(-φ(x), 1)` — the
Schur-complement trick, carried out entirely in quadratic-form terms. -/
theorem IsCompletelyPositive.isSchwarzMap (hφ : IsCompletelyPositive φ)
    (h1 : φ 1 = 1) : IsSchwarzMap φ := by
  intro x
  have hN := hφ 2 (pairMatrix 1 x) (matrixQF_pair 1 x)
  have hval : (∑ i, ∑ j, star ((![-(φ x), (1 : A)] : Fin 2 → A) i)
      * ((pairMatrix (1 : A) x).map φ) i j
      * ((![-(φ x), (1 : A)] : Fin 2 → A) j))
      = φ (star x * x) - star (φ x) * φ x := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.map_apply, pairMatrix, Matrix.of_apply,
      star_one, one_mul, mul_one, h1, hφ.map_star x, star_neg, neg_mul,
      mul_neg, neg_neg]
    abel
  have h := hN (![-(φ x), (1 : A)])
  rw [hval] at h
  exact sub_nonneg.mp h

end CP

/-! ### Choi's multiplicative-domain theorem -/

/-- Polarization expansion of the Schwarz defect
`D(z) = φ(z⋆z) − φ(z)⋆φ(z)` at `z = x + l•w`. -/
private theorem schwarz_defect_expand (φ : A →ₗ[ℂ] A) (x w : A) (l : ℂ) :
    φ (star (x + l • w) * (x + l • w))
        - star (φ (x + l • w)) * φ (x + l • w)
      = (φ (star x * x) - star (φ x) * φ x)
        + (l • (φ (star x * w) - star (φ x) * φ w)
        + (star l • (φ (star w * x) - star (φ w) * φ x)
        + (star l * l) • (φ (star w * w) - star (φ w) * φ w))) := by
  simp only [star_add, star_smul, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_add, map_smul, smul_sub]
  module

/-- **Choi's multiplicative-domain theorem** (final step of
`thm:predictive-unit`): if a star-preserving Schwarz map has *equality* in
the Schwarz inequality at `x`, then over an Archimedean order

`φ(x⋆ w) = φ(x)⋆ φ(w)`  for every `w`.

The proof polarizes the Schwarz defect `D(x + l•w) ≥ 0` in the complex
parameter `l`, obtaining `(n+1) • v ≤ D(w)` for the four selfadjoint
combinations `±(G₁+G₂)`, `±i(G₂−G₁)` of the cross terms, and kills them
with the Archimedean property. -/
theorem multiplicative_of_schwarz_eq {φ : A →ₗ[ℂ] A}
    (harch : IsArchimedeanStarOrder A) (hKS : IsSchwarzMap φ)
    (hstar : ∀ y, φ (star y) = star (φ y))
    {x : A} (hx : φ (star x * x) = star (φ x) * φ x) (w : A) :
    φ (star x * w) = star (φ x) * φ w := by
  set G₁ := φ (star x * w) - star (φ x) * φ w with hG₁
  set G₂ := φ (star w * x) - star (φ w) * φ x with hG₂
  set Dw := φ (star w * w) - star (φ w) * φ w with hDw
  have hDw0 : 0 ≤ Dw := sub_nonneg.mpr (hKS w)
  have hG₂star : G₂ = star G₁ := by
    have e1 : star (φ (star x * w)) = φ (star w * x) := by
      rw [← hstar (star x * w), star_mul, star_star]
    have e2 : star (star (φ x) * φ w) = star (φ w) * φ x := by
      rw [star_mul, star_star]
    rw [hG₁, hG₂, star_sub, e1, e2]
  -- the polarized inequality
  have hineq : ∀ l : ℂ,
      0 ≤ l • G₁ + (star l • G₂ + (star l * l) • Dw) := by
    intro l
    have h0 := sub_nonneg.mpr (hKS (x + l • w))
    rw [schwarz_defect_expand φ x w l, hx, sub_self, zero_add] at h0
    exact h0
  -- the scalars `1/(n+1)` are star-fixed and nonzero
  have hstarc : ∀ n : ℕ, star ((((n : ℂ)) + 1)⁻¹) = (((n : ℂ)) + 1)⁻¹ := by
    intro n
    simp [Complex.star_def, map_inv₀, map_add, map_natCast, map_one]
  have hcne : ∀ n : ℕ, ((n : ℂ)) + 1 ≠ 0 := by
    intro n
    have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    push_cast at h
    exact h
  -- from `c⁻¹ • v ≤ (c⁻¹ · c⁻¹) • Dw` for all `n`, conclude `v ≤ 0`
  have hbound : ∀ v : A, IsSelfAdjoint v →
      (∀ n : ℕ, (((n : ℂ)) + 1)⁻¹ • v
        ≤ ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw) → v ≤ 0 := by
    intro v hv hall
    refine harch v Dw hv ?_
    intro n
    cases n with
    | zero => simpa using hDw0
    | succ m =>
        have h := sq_natCast_smul_mono (m + 1) (hall m)
        rw [smul_smul, smul_smul] at h
        have hc : ((m + 1 : ℕ) : ℂ) = ((m : ℂ)) + 1 := by push_cast; ring
        rw [hc] at h
        have hne := hcne m
        have e1 : (((m : ℂ) + 1) * ((m : ℂ) + 1)) * (((m : ℂ)) + 1)⁻¹
            = ((m : ℂ)) + 1 := mul_inv_cancel_right₀ hne _
        have e2 : (((m : ℂ) + 1) * ((m : ℂ) + 1))
            * ((((m : ℂ)) + 1)⁻¹ * (((m : ℂ)) + 1)⁻¹) = 1 := by
          rw [← mul_inv]
          exact mul_inv_cancel₀ (mul_ne_zero hne hne)
        rw [e1, e2, one_smul] at h
        calc (m + 1) • v = (((m + 1 : ℕ) : ℂ)) • v :=
              (Nat.cast_smul_eq_nsmul ℂ (m + 1) v).symm
          _ = (((m : ℂ)) + 1) • v := by rw [hc]
          _ ≤ Dw := h
  -- directions `l = ∓ 1/(n+1)`: the combination `S = G₁ + G₂`
  have hS : G₁ + G₂ ≤ 0 ∧ -(G₁ + G₂) ≤ 0 := by
    have hsa : IsSelfAdjoint (G₁ + G₂) := by
      rw [IsSelfAdjoint, hG₂star, star_add, star_star, add_comm]
    constructor
    · refine hbound _ hsa ?_
      intro n
      have h := hineq (-((((n : ℂ)) + 1)⁻¹))
      rw [star_neg, hstarc n, neg_mul_neg, neg_smul, neg_smul] at h
      have e : -((((n : ℂ)) + 1)⁻¹ • G₁) + (-((((n : ℂ)) + 1)⁻¹ • G₂)
          + ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw)
          = ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw
            - ((((n : ℂ)) + 1)⁻¹ • G₁ + (((n : ℂ)) + 1)⁻¹ • G₂) := by
        abel
      rw [e] at h
      rw [smul_add]
      exact sub_nonneg.mp h
    · refine hbound _ hsa.neg ?_
      intro n
      have h := hineq ((((n : ℂ)) + 1)⁻¹)
      rw [hstarc n] at h
      have e : (((n : ℂ)) + 1)⁻¹ • G₁ + ((((n : ℂ)) + 1)⁻¹ • G₂
          + ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw)
          = ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw
            - (((n : ℂ)) + 1)⁻¹ • (-(G₁ + G₂)) := by
        rw [smul_neg, smul_add]
        abel
      rw [e] at h
      exact sub_nonneg.mp h
  -- directions `l = ± i/(n+1)`: the combination `K = i•G₂ − i•G₁`
  have hK : Complex.I • G₂ - Complex.I • G₁ ≤ 0
      ∧ -(Complex.I • G₂ - Complex.I • G₁) ≤ 0 := by
    have hsa : IsSelfAdjoint (Complex.I • G₂ - Complex.I • G₁) := by
      rw [IsSelfAdjoint, star_sub, star_smul, star_smul, Complex.star_def,
        Complex.conj_I, hG₂star, star_star, neg_smul, neg_smul]
      abel
    have hstarl : ∀ n : ℕ, star (Complex.I * (((n : ℂ)) + 1)⁻¹)
        = -(Complex.I * (((n : ℂ)) + 1)⁻¹) := by
      intro n
      rw [star_mul', hstarc n, Complex.star_def, Complex.conj_I]
      ring
    have hll : ∀ n : ℕ, -(Complex.I * (((n : ℂ)) + 1)⁻¹)
        * (Complex.I * (((n : ℂ)) + 1)⁻¹)
        = (((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹ := by
      intro n
      have e : -(Complex.I * (((n : ℂ)) + 1)⁻¹)
          * (Complex.I * (((n : ℂ)) + 1)⁻¹)
          = -(Complex.I * Complex.I) * ((((n : ℂ)) + 1)⁻¹
            * (((n : ℂ)) + 1)⁻¹) := by ring
      rw [e, Complex.I_mul_I, neg_neg, one_mul]
    constructor
    · -- `l = i/(n+1)` bounds `K` above
      refine hbound _ hsa ?_
      intro n
      have h := hineq (Complex.I * (((n : ℂ)) + 1)⁻¹)
      rw [hstarl n, hll n] at h
      have e : (Complex.I * (((n : ℂ)) + 1)⁻¹) • G₁
          + (-(Complex.I * (((n : ℂ)) + 1)⁻¹) • G₂
            + ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw)
          = ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw
            - (((n : ℂ)) + 1)⁻¹ • (Complex.I • G₂ - Complex.I • G₁) := by
        module
      rw [e] at h
      exact sub_nonneg.mp h
    · -- `l = -i/(n+1)` bounds `-K` above
      refine hbound _ hsa.neg ?_
      intro n
      have h := hineq (-(Complex.I * (((n : ℂ)) + 1)⁻¹))
      rw [star_neg, hstarl n, neg_neg] at h
      have hmm : (Complex.I * (((n : ℂ)) + 1)⁻¹)
          * -(Complex.I * (((n : ℂ)) + 1)⁻¹)
          = (((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹ := by
        rw [mul_comm]
        exact hll n
      rw [hmm] at h
      have e : -(Complex.I * (((n : ℂ)) + 1)⁻¹) • G₁
          + ((Complex.I * (((n : ℂ)) + 1)⁻¹) • G₂
            + ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw)
          = ((((n : ℂ)) + 1)⁻¹ * (((n : ℂ)) + 1)⁻¹) • Dw
            - (((n : ℂ)) + 1)⁻¹
              • (-(Complex.I • G₂ - Complex.I • G₁)) := by
        module
      rw [e] at h
      exact sub_nonneg.mp h
  -- assemble: `S = 0` and `K = 0` force `G₁ = 0`
  have hS0 : G₁ + G₂ = 0 := le_antisymm hS.1 (neg_nonpos.mp hS.2)
  have hK0 : Complex.I • G₂ - Complex.I • G₁ = 0 :=
    le_antisymm hK.1 (neg_nonpos.mp hK.2)
  have hG₂G₁ : G₂ = G₁ := by
    have h : Complex.I • (G₂ - G₁) = 0 := by
      rw [smul_sub]
      exact hK0
    have h2 := congrArg (fun v => (Complex.I)⁻¹ • v) h
    simp only [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul,
      smul_zero] at h2
    exact sub_eq_zero.mp h2
  have hG₁0 : G₁ = 0 := by
    have h : (2 : ℂ) • G₁ = 0 := by
      rw [two_smul]
      calc G₁ + G₁ = G₁ + G₂ := by rw [hG₂G₁]
        _ = 0 := hS0
    have h2 := congrArg (fun v => ((2 : ℂ)⁻¹) • v) h
    simp only [smul_smul,
      inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul,
      smul_zero] at h2
    exact h2
  have hfin : φ (star x * w) - star (φ x) * φ w = 0 := by
    rw [← hG₁]
    exact hG₁0
  exact sub_eq_zero.mp hfin

/-! ### The predictive-unit theorem -/

namespace UCPMap

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- **Predictive units are star-preserving** (`thm:predictive-unit`): every
unit of the channel monoid `UCPMap A` respects the involution. -/
theorem unit_map_star (u : (UCPMap A)ˣ) (a : A) :
    (u.val : UCPMap A) (star a) = star ((u.val : UCPMap A) a) := by
  have h := (u.val : UCPMap A).completelyPositive.map_star a
  simpa [UCPMap.coe_toLinearMap] using h

/-- **The predictive-unit theorem** (`thm:predictive-unit`): over an
Archimedean order, every unit of the channel monoid `UCPMap A` is
multiplicative.  Together with `unit_map_star` this makes every predictive
unit a `*`-homomorphism, hence `𝖴_pred ⊆ Aut(𝒜_int)`.

The proof composes the pieces exactly as in the manuscript: the sandwich
equality (`unit_sandwich_eq`) says equality holds in the Kadison–Schwarz
inequality for `u⁻¹` at every point of the range of `u`; Choi's theorem
turns this into the multiplicative-domain identity for `u⁻¹`; and
injectivity of `u⁻¹` transports multiplicativity back to `u`. -/
theorem unit_map_mul (harch : IsArchimedeanStarOrder A) (u : (UCPMap A)ˣ)
    (a b : A) :
    (u.val : UCPMap A) (a * b)
      = (u.val : UCPMap A) a * (u.val : UCPMap A) b := by
  have hΨCP := (u.val : UCPMap A).completelyPositive
  have hΘCP := (u.inv : UCPMap A).completelyPositive
  have hΨKS : IsSchwarzMap (u.val : UCPMap A).toLinearMap :=
    hΨCP.isSchwarzMap (u.val : UCPMap A).map_one'
  have hΘKS : IsSchwarzMap (u.inv : UCPMap A).toLinearMap :=
    hΘCP.isSchwarzMap (u.inv : UCPMap A).map_one'
  -- Schwarz equality for `u⁻¹` at range points of `u`, from the sandwich
  have hxeq : (u.inv : UCPMap A).toLinearMap
        (star ((u.val : UCPMap A) (star a)) * (u.val : UCPMap A) (star a))
      = star ((u.inv : UCPMap A).toLinearMap ((u.val : UCPMap A) (star a)))
        * (u.inv : UCPMap A).toLinearMap ((u.val : UCPMap A) (star a)) := by
    have hs := unit_sandwich_eq u hΨKS hΘKS (star a)
    simp only [UCPMap.coe_toLinearMap]
    rw [hs, inv_val_apply]
  -- Choi's theorem for `u⁻¹` at `x := u (star a)`
  have hchoi := multiplicative_of_schwarz_eq harch hΘKS
    (fun y => hΘCP.map_star y) hxeq
  -- rewrite the Choi identity into `u⁻¹(u a * w) = a * u⁻¹ w`
  have hkey : ∀ w : A, (u.inv : UCPMap A) ((u.val : UCPMap A) a * w)
      = a * (u.inv : UCPMap A) w := by
    intro w
    have h := hchoi w
    simp only [UCPMap.coe_toLinearMap] at h
    rw [show star ((u.val : UCPMap A) (star a)) = (u.val : UCPMap A) a from
        by rw [← unit_map_star u (star a), star_star],
      inv_val_apply, star_star] at h
    exact h
  -- transport back through the injective inverse
  have hinj : Function.Injective ⇑(u.inv : UCPMap A) := by
    intro p q hpq
    have h := congrArg (⇑(u.val : UCPMap A)) hpq
    rwa [val_inv_apply, val_inv_apply] at h
  apply hinj
  rw [inv_val_apply, hkey ((u.val : UCPMap A) b), inv_val_apply]

end UCPMap

end NCG
