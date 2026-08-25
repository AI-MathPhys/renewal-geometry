/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.TraceExpDerivative

/-!
# SMQG exterior-power cluster: exact medium records (batch 07)

Exact formalizations for eleven Gran-Tensor records of the SMQG (quadratic-fermion /
exterior second quantization) cluster:

* `cor:SMQG-dressing` — one-sided dressing preserves positivity (QG.24–QG.25);
* `cor:SMQG-exterior-rank` — rank of exterior powers and of `Γ∧` (QG.15–QG.16);
* `cor:SMQG-zero-positivity-order` — divisor-safe positivity order (QG.53);
* `cth:SMQG-marginals-no-mixture` — marginals do not determine the mixture (QG.55);
* `cth:SMQG-normalized-no-absolute` — normalized convergence vs. absolute kernel;
* `lem:SMQG-Gamma-bound` — uniform exterior norm bound (QG.78–QG.79);
* `lem:SMQG-exterior-bound` — exterior-power perturbation bound (QG.57);
* `thm:SMQG-Gaussian-occurrence` — exact Gaussian-occurrence theorem (QG.40–QG.41);
* `thm:SMQG-Grassmann-Wick` — finite Grassmann Wick–exterior theorem (QG.8–QG.9);
* `thm:SMQG-cutoff-exterior` — one-particle Pythagoras and strict exterior transport
  (QG.69–QG.72);
* `thm:SMQG-exterior-positivity` — exact exterior reflection-positivity criterion
  (QG.11–QG.14).

The finite rendering realizes the exterior power `⋀^r E` of `E = ℂ^d` concretely on the
orthonormal wedge basis indexed by `r`-element subsets of `Fin d`: `⋀^r A` is the `r`-th
compound (minor) matrix `cmpd r A`, and the fermionic second quantization
`Γ∧(A) = ⊕_r ⋀^r A` is the subset-indexed block matrix `Gamma A`.  The whole calculus
(Cauchy–Binet multiplicativity, adjoints, diagonalization, operator-norm bounds through
the tensor-power dilation, PSD preservation) is developed from scratch in Part I–II and
shared by all records.
-/

open Matrix

namespace NCG
namespace MediumExact07

/-! ### Part I: subsets, selections, compound matrices, second quantization -/

/-- The grade-`r` wedge-basis index: `r`-element subsets of `Fin d`. -/
abbrev GradeIdx (r d : ℕ) := {S : Finset (Fin d) // S.card = r}

variable {r d m n p : ℕ}

/-- The increasing enumeration of an `r`-element subset. -/
def sel (S : GradeIdx r d) : Fin r → Fin d := fun i => S.1.orderEmbOfFin S.2 i

theorem sel_injective (S : GradeIdx r d) : Function.Injective (sel S) := fun _ _ h =>
  (S.1.orderEmbOfFin S.2).injective h

theorem sel_mem (S : GradeIdx r d) (i : Fin r) : sel S i ∈ S.1 :=
  Finset.orderEmbOfFin_mem S.1 S.2 i

theorem image_sel (S : GradeIdx r d) : Finset.image (sel S) Finset.univ = S.1 :=
  Finset.image_orderEmbOfFin_univ S.1 S.2

/-- The `r`-th compound matrix: entries are the `r × r` minors.  This is the matrix of
`⋀^r A` in the orthonormal wedge bases. -/
noncomputable def cmpd (r : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (GradeIdx r m) (GradeIdx r n) ℂ :=
  Matrix.of fun S T => (A.submatrix (sel S) (sel T)).det

theorem cmpd_apply (A : Matrix (Fin m) (Fin n) ℂ) (S : GradeIdx r m) (T : GradeIdx r n) :
    cmpd r A S T = (A.submatrix (sel S) (sel T)).det := rfl

/-- The slot-product matrix on `r`-tuples: the matrix of `C 0 ⊗ C 1 ⊗ ⋯` on the tensor
power basis. -/
noncomputable def slotProd (C : Fin r → Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin r → Fin m) (Fin r → Fin n) ℂ :=
  Matrix.of fun f g => ∏ k, C k (f k) (g k)

/-- The `r`-th tensor power of `A`. -/
noncomputable def tpow (r : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin r → Fin m) (Fin r → Fin n) ℂ :=
  slotProd fun _ => A

theorem slotProd_apply (C : Fin r → Matrix (Fin m) (Fin n) ℂ) (f : Fin r → Fin m)
    (g : Fin r → Fin n) : slotProd C f g = ∏ k, C k (f k) (g k) := rfl

/-- Slotwise multiplicativity of the slot product. -/
theorem slotProd_mul (C : Fin r → Matrix (Fin m) (Fin n) ℂ)
    (C' : Fin r → Matrix (Fin n) (Fin p) ℂ) :
    slotProd C * slotProd C' = slotProd fun k => C k * C' k := by
  ext f h
  rw [Matrix.mul_apply]
  simp only [slotProd_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum fun k j => C k (f k) j * C' k j (h k)]
  exact Finset.sum_congr rfl fun g _ => Finset.prod_mul_distrib.symm

/-- Tensor powers are multiplicative. -/
theorem tpow_mul (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    tpow r (A * B) = tpow r A * tpow r B :=
  (slotProd_mul _ _).symm

/-- The antisymmetrizer: the (unnormalized) matrix of the inclusion of the wedge basis
into the tensor-power basis. -/
noncomputable def asym (r d : ℕ) : Matrix (Fin r → Fin d) (GradeIdx r d) ℂ :=
  Matrix.of fun f S => ∑ σ : Equiv.Perm (Fin r),
    if f = sel S ∘ σ then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0

theorem asym_apply (f : Fin r → Fin d) (S : GradeIdx r d) :
    asym r d f S = ∑ σ : Equiv.Perm (Fin r),
      if f = sel S ∘ σ then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0 := rfl

/-- Any injective tuple factors as an ordered selection composed with a permutation. -/
theorem exists_sel_factor {f : Fin r → Fin d} (hf : Function.Injective f) :
    ∃ (S : GradeIdx r d) (σ : Equiv.Perm (Fin r)), f = sel S ∘ σ := by
  classical
  have hcard : (Finset.image f Finset.univ).card = r := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  refine ⟨⟨Finset.image f Finset.univ, hcard⟩, ?_⟩
  have hmem : ∀ k, f k ∈ Finset.image f Finset.univ := fun k =>
    Finset.mem_image_of_mem f (Finset.mem_univ k)
  have hinj : Function.Injective fun k => (⟨f k, hmem k⟩ : (Finset.image f Finset.univ : Finset _)) :=
    fun a b hab => hf (congrArg Subtype.val hab)
  have hbij : Function.Bijective fun k =>
      (⟨f k, hmem k⟩ : (Finset.image f Finset.univ : Finset _)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [Fintype.card_coe, hcard, Fintype.card_fin]⟩
  set e : Fin r ≃ (Finset.image f Finset.univ : Finset _) := Equiv.ofBijective _ hbij with he
  refine ⟨e.trans ((Finset.image f Finset.univ).orderIsoOfFin hcard).toEquiv.symm, ?_⟩
  funext k
  show f k = sel _ (((Finset.image f Finset.univ).orderIsoOfFin hcard).toEquiv.symm (e k))
  have : sel (⟨Finset.image f Finset.univ, hcard⟩ : GradeIdx r d)
      (((Finset.image f Finset.univ).orderIsoOfFin hcard).toEquiv.symm (e k))
      = ((((Finset.image f Finset.univ).orderIsoOfFin hcard))
          (((Finset.image f Finset.univ).orderIsoOfFin hcard).toEquiv.symm (e k)) : Fin d) := by
    rw [sel, ← Finset.coe_orderIsoOfFin_apply]
  rw [this]
  have h2 : (((Finset.image f Finset.univ).orderIsoOfFin hcard))
      (((Finset.image f Finset.univ).orderIsoOfFin hcard).toEquiv.symm (e k)) = e k := by
    exact ((Finset.image f Finset.univ).orderIsoOfFin hcard).apply_symm_apply (e k)
  rw [h2]
  rfl

/-- The subset in a selection factorization is the image. -/
theorem sel_factor_subset {f : Fin r → Fin d} {S : GradeIdx r d} {σ : Equiv.Perm (Fin r)}
    (h : f = sel S ∘ σ) : S.1 = Finset.image f Finset.univ := by
  classical
  rw [h]
  have : Finset.image (sel S ∘ σ) Finset.univ
      = Finset.image (sel S) (Finset.image σ Finset.univ) := by
    rw [Finset.image_image]
  rw [this, Finset.image_univ_equiv, image_sel]

/-- Uniqueness of the selection factorization. -/
theorem sel_factor_unique {f : Fin r → Fin d} {S S' : GradeIdx r d}
    {σ σ' : Equiv.Perm (Fin r)} (h : f = sel S ∘ σ) (h' : f = sel S' ∘ σ') :
    S = S' ∧ σ = σ' := by
  have hSS : S = S' := Subtype.ext ((sel_factor_subset h).trans (sel_factor_subset h').symm)
  subst hSS
  refine ⟨rfl, Equiv.ext fun k => sel_injective S ?_⟩
  have := congrFun (h.symm.trans h') k
  exact this

/-- A tuple admitting a selection factorization is injective. -/
theorem sel_factor_injective {f : Fin r → Fin d} {S : GradeIdx r d} {σ : Equiv.Perm (Fin r)}
    (h : f = sel S ∘ σ) : Function.Injective f := by
  rw [h]
  exact (sel_injective S).comp σ.injective

/-- **The intertwining relation**: the tensor power restricted along the antisymmetrizer
is the compound matrix, `T_r(A) ∘ J = J ∘ ⋀^r A`. -/
theorem tpow_mul_asym (A : Matrix (Fin m) (Fin n) ℂ) :
    tpow r A * asym r n = asym r m * cmpd r A := by
  classical
  ext f T
  -- LHS: collapse the tuple sum against the antisymmetrizer ites
  have hlhs : (tpow r A * asym r n) f T
      = ∑ τ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (f k) (sel T (τ k)) := by
    rw [Matrix.mul_apply]
    simp only [tpow, slotProd_apply, asym_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hcollapse : ∀ g : Fin r → Fin n,
        (∏ k, A (f k) (g k)) * (if g = sel T ∘ τ then ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0)
        = if g = sel T ∘ τ then ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (f k) (sel T (τ k))
          else 0 := by
      intro g
      by_cases hg : g = sel T ∘ τ
      · subst hg
        rw [if_pos rfl, if_pos rfl, mul_comm]
        rfl
      · rw [if_neg hg, if_neg hg, mul_zero]
    rw [Finset.sum_congr rfl fun g _ => hcollapse g, Finset.sum_ite_eq' Finset.univ]
    rw [if_pos (Finset.mem_univ _)]
  -- the τ-sum is a determinant
  have hdet : (∑ τ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (f k) (sel T (τ k)))
      = (Matrix.of fun a b => A (f b) (sel T a)).det := by
    rw [Matrix.det_apply']
  rw [hlhs, hdet]
  -- RHS
  rw [Matrix.mul_apply]
  simp only [asym_apply, cmpd_apply, Finset.sum_mul]
  by_cases hf : Function.Injective f
  · -- injective case: exactly one factorization survives on the right
    obtain ⟨S₀, σ₀, hfac⟩ := exists_sel_factor hf
    have hrhs : ∑ S : GradeIdx r m, ∑ σ : Equiv.Perm (Fin r),
        (if f = sel S ∘ σ then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0)
          * (A.submatrix (sel S) (sel T)).det
        = ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) * (A.submatrix (sel S₀) (sel T)).det := by
      rw [Finset.sum_eq_single S₀]
      · rw [Finset.sum_eq_single σ₀]
        · rw [if_pos hfac]
        · intro σ _ hσ
          rw [if_neg fun hc => hσ (sel_factor_unique hc hfac).2, zero_mul]
        · intro h; exact absurd (Finset.mem_univ σ₀) h
      · intro S _ hS
        refine Finset.sum_eq_zero fun σ _ => ?_
        rw [if_neg fun hc => hS (sel_factor_unique hc hfac).1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ S₀) h
    rw [hrhs]
    -- identify the determinant with the permuted minor
    have htrans : (Matrix.of fun a b => A (f b) (sel T a)).det
        = ((A.submatrix (sel S₀) (sel T)).submatrix σ₀ id)ᵀ.det := by
      congr 1
      ext a b
      rw [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.of_apply, id_eq]
      rw [hfac]
      rfl
    rw [htrans, Matrix.det_transpose, Matrix.det_permute]
    push_cast
    ring
  · -- non-injective case: both sides vanish
    have hzero : (Matrix.of fun a b => A (f b) (sel T a)).det = 0 := by
      rw [Function.not_injective_iff] at hf
      obtain ⟨b, b', hbb', hne⟩ := hf
      refine Matrix.det_zero_of_column_eq hne ?_
      ext a
      rw [Matrix.of_apply, Matrix.of_apply, hbb']
    rw [hzero]
    refine (Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun σ _ => ?_).symm
    rw [if_neg fun hc => hf (sel_factor_injective hc), zero_mul]

/-- The antisymmetrizer is `√(r!)`-isometric: `Jᴴ J = r! • 1`. -/
theorem conjTranspose_asym_mul_asym :
    (asym r d)ᴴ * asym r d = ((r.factorial : ℂ) • 1 : Matrix (GradeIdx r d) (GradeIdx r d) ℂ) := by
  classical
  ext S T
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, asym_apply, star_sum, star_ite, star_intCast,
    star_zero, Finset.sum_mul_sum]
  have hterm : ∀ f : Fin r → Fin d, ∀ σ τ : Equiv.Perm (Fin r),
      (if f = sel S ∘ σ then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0)
        * (if f = sel T ∘ τ then ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0)
      = if f = sel S ∘ σ ∧ sel S ∘ σ = sel T ∘ τ then
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0 := by
    intro f σ τ
    by_cases h1 : f = sel S ∘ σ
    · subst h1
      by_cases h2 : f = sel T ∘ τ
      · rw [if_pos h2, if_pos ⟨rfl, h2⟩]
      · rw [if_neg h2, if_neg (fun hc => h2 hc.2), mul_zero]
    · rw [if_neg h1, if_neg (fun hc => h1 hc.1), zero_mul]
  rw [Finset.sum_comm]
  simp only [hterm]
  have hcollapse : ∀ σ τ : Equiv.Perm (Fin r),
      (∑ f : Fin r → Fin d, if f = sel S ∘ σ ∧ sel S ∘ σ = sel T ∘ τ then
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0)
      = if sel S ∘ σ = sel T ∘ τ then
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0 := by
    intro σ τ
    rw [Finset.sum_eq_single (sel S ∘ σ)]
    · by_cases h2 : sel S ∘ σ = sel T ∘ τ
      · rw [if_pos ⟨rfl, h2⟩, if_pos h2]
      · rw [if_neg fun hc => h2 hc.2, if_neg h2]
    · intro f _ hfne
      rw [if_neg fun hc => hfne hc.1]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => hcollapse σ τ]
  by_cases hST : S = T
  · subst hST
    have hdiag : ∀ σ τ : Equiv.Perm (Fin r), (sel S ∘ σ = sel S ∘ τ) ↔ σ = τ := by
      intro σ τ
      constructor
      · intro h
        exact Equiv.ext fun k => sel_injective S (congrFun h k)
      · rintro rfl; rfl
    have hsum : ∀ σ : Equiv.Perm (Fin r),
        (∑ τ : Equiv.Perm (Fin r), if sel S ∘ σ = sel S ∘ τ then
            ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) else 0)
        = 1 := by
      intro σ
      rw [Finset.sum_eq_single σ]
      · rw [if_pos rfl]
        have : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> rfl
        push_cast [← this]
        ring
      · intro τ _ hτ
        rw [if_neg fun hc => hτ ((hdiag σ τ).mp hc)]
      · intro h; exact absurd (Finset.mem_univ σ) h
    rw [Finset.sum_congr rfl fun σ _ => hsum σ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, nsmul_eq_mul]
  · have hne : ∀ σ τ : Equiv.Perm (Fin r), ¬(sel S ∘ σ = sel T ∘ τ) := by
      intro σ τ hc
      exact hST (sel_factor_unique (f := sel S ∘ σ) rfl hc).1
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => if_neg (hne σ τ)]
    rw [Finset.sum_const, Finset.sum_const, smul_zero, smul_zero,
      Matrix.smul_apply, Matrix.one_apply_ne hST, smul_zero]

/-- Cancellation of the factorial scalar. -/
theorem factorial_smul_cancel {α β : Type*} [Fintype α] [Fintype β]
    {X Y : Matrix α β ℂ} (h : (r.factorial : ℂ) • X = (r.factorial : ℂ) • Y) : X = Y := by
  have hr : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  exact smul_right_injective _ hr h

/-- **Cauchy–Binet / functoriality**: compounds are multiplicative. -/
theorem cmpd_mul (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    cmpd r (A * B) = cmpd r A * cmpd r B := by
  refine factorial_smul_cancel (r := r) ?_
  have h1 : asym r m * cmpd r (A * B) = asym r m * (cmpd r A * cmpd r B) := by
    rw [← tpow_mul_asym, tpow_mul, Matrix.mul_assoc, tpow_mul_asym, ← Matrix.mul_assoc,
      tpow_mul_asym, Matrix.mul_assoc]
  calc (r.factorial : ℂ) • cmpd r (A * B)
      = ((r.factorial : ℂ) • (1 : Matrix (GradeIdx r m) (GradeIdx r m) ℂ)) * cmpd r (A * B) := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = (asym r m)ᴴ * (asym r m * cmpd r (A * B)) := by
        rw [← conjTranspose_asym_mul_asym, Matrix.mul_assoc]
    _ = (asym r m)ᴴ * (asym r m * (cmpd r A * cmpd r B)) := by rw [h1]
    _ = ((r.factorial : ℂ) • (1 : Matrix (GradeIdx r m) (GradeIdx r m) ℂ))
          * (cmpd r A * cmpd r B) := by
        rw [← Matrix.mul_assoc, conjTranspose_asym_mul_asym]
    _ = (r.factorial : ℂ) • (cmpd r A * cmpd r B) := by rw [Matrix.smul_mul, Matrix.one_mul]

/-- Compounds intertwine adjoints. -/
theorem cmpd_conjTranspose (A : Matrix (Fin m) (Fin n) ℂ) :
    cmpd r Aᴴ = (cmpd r A)ᴴ := by
  ext S T
  rw [cmpd_apply, Matrix.conjTranspose_apply, cmpd_apply, Matrix.conjTranspose_submatrix,
    Matrix.det_conjTranspose]

/-- The compound of a diagonal matrix is diagonal, with entries the subset products. -/
theorem cmpd_diagonal (v : Fin m → ℂ) :
    cmpd r (Matrix.diagonal v)
      = Matrix.diagonal (fun S : GradeIdx r m => ∏ i ∈ S.1, v i) := by
  classical
  ext S T
  by_cases hST : S = T
  · subst hST
    rw [Matrix.diagonal_apply_eq, cmpd_apply]
    have hsub : (Matrix.diagonal v).submatrix (sel S) (sel S)
        = Matrix.diagonal fun i => v (sel S i) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.submatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ fun hc => hij (sel_injective S hc),
          Matrix.diagonal_apply_ne _ hij]
    rw [hsub, Matrix.det_diagonal, ← image_sel S,
      Finset.prod_image fun a _ b _ h => sel_injective S h]
  · rw [Matrix.diagonal_apply_ne _ hST, cmpd_apply]
    have hdiff : (S.1 \ T.1).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hST (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (T.2.trans S.2.symm).le))
    obtain ⟨i₀, hi₀⟩ := hdiff
    have hi₀S : i₀ ∈ S.1 := (Finset.mem_sdiff.mp hi₀).1
    have hi₀T : i₀ ∉ T.1 := (Finset.mem_sdiff.mp hi₀).2
    set a : Fin r := (S.1.orderIsoOfFin S.2).symm ⟨i₀, hi₀S⟩ with ha
    have hsel : sel S a = i₀ := by
      rw [sel, ← Finset.coe_orderIsoOfFin_apply, ha]
      rw [(S.1.orderIsoOfFin S.2).apply_symm_apply]
    refine Matrix.det_eq_zero_of_row_eq_zero a fun j => ?_
    rw [Matrix.submatrix_apply, hsel]
    exact Matrix.diagonal_apply_ne _ fun hc => hi₀T (hc ▸ sel_mem T j)

/-- The compound of the identity is the identity. -/
theorem cmpd_one : cmpd r (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  rw [← Matrix.diagonal_one, cmpd_diagonal]
  have : (fun S : GradeIdx r m => ∏ i ∈ S.1, (1 : ℂ)) = fun _ => 1 := by
    funext S
    exact Finset.prod_const_one
  rw [this, Matrix.diagonal_one]

open scoped ComplexOrder in
/-- Compounds of positive semidefinite matrices are positive semidefinite. -/
theorem cmpd_posSemidef {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) :
    (cmpd r P).PosSemidef := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ P := hP.nonneg
  have hBps : (CFC.sqrt P).PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hBB : CFC.sqrt P * CFC.sqrt P = P := by rw [← sq, CFC.sq_sqrt h0]
  have hfac : cmpd r P = (cmpd r (CFC.sqrt P))ᴴ * cmpd r (CFC.sqrt P) := by
    rw [← cmpd_conjTranspose, ← cmpd_mul, hBps.1.eq, hBB]
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end MediumExact07
end NCG
