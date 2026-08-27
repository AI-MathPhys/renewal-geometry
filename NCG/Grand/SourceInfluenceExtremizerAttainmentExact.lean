/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceCoercivityInfluenceExact
import NCG.Grand.ThreeCylinderActionResponseExact

/-!
# Attainment of the finite source-influence extremizer

This closes the compact finite-spectral clause of
`thm:GT-source-coercivity-influence`: on the positive finite branch the
optimal generalized Rayleigh quotient is attained and can be normalized to
the three identities RI.6.
-/

open Matrix Finset NCG.GeometricThresholdBank
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace SourceInfluenceAttainment

open SourceCoercivityInfluence ThreeCylinderActionResponse

variable {d : ℕ}

/-- Kernel inclusion makes the target right-supported on `supp B`. -/
theorem target_mul_support {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) :
    C * supportProj hB.1 = C := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [← Matrix.mulVec_mulVec]
  have hk := hker (x - supportProj hB.1 *ᵥ x)
    (mulVec_sub_supportProj hB x)
  rw [Matrix.mulVec_sub] at hk
  exact (sub_eq_zero.mp hk).symm

/-- For Hermitian `C`, right support implies left support. -/
theorem support_mul_target {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.IsHermitian)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) :
    supportProj hB.1 * C = C := by
  have h := congrArg Matrix.conjTranspose (target_mul_support hB hker)
  simpa [Matrix.conjTranspose_mul, hC.eq,
    (supportProj_posSemidef hB.1).1.eq] using h

/-- The whitened target operator `B^{†/2} C B^{†/2}`. -/
noncomputable def whitened (B C : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) : Matrix (Fin d) (Fin d) ℂ :=
  invSqrt hB * C * invSqrt hB

theorem whitened_posSemidef {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (whitened B C hB.1).PosSemidef := by
  unfold whitened
  simpa only [(invSqrt_isHermitian hB.1).eq] using
    hC.conjTranspose_mul_mul_same (invSqrt hB.1)

/-- The positive spectral square root is PSD. -/
theorem sqrtM_posSemidef {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) : (sqrtM hB.1).PosSemidef := by
  unfold sqrtM
  exact spectralFunction_posSemidef hB.1 _ fun i => by
    split_ifs with hi
    · exact Real.sqrt_nonneg _
    · exact le_rfl
/-- The compiled spectral square root squares to the PSD matrix. -/
theorem sqrtM_mul_sqrtM {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) :
    sqrtM hB.1 * sqrtM hB.1 = B := by
  have hid := spectralFunction_id hB.1
  unfold sqrtM
  rw [spectralFunction_mul]
  calc
    spectralFunction hB.1
        (fun l => (if 0 < l then Real.sqrt l else 0) *
          (if 0 < l then Real.sqrt l else 0)) =
        spectralFunction hB.1 id := by
      refine spectralFunction_congr hB.1 fun i => ?_
      by_cases hi : 0 < hB.1.eigenvalues i
      · rw [if_pos hi, Real.mul_self_sqrt hi.le]
        rfl
      · have hz : hB.1.eigenvalues i = 0 :=
          le_antisymm (not_lt.mp hi) (hB.eigenvalues_nonneg i)
        rw [if_neg hi, zero_mul, hz]
        rfl
    _ = B := hid

theorem sqrtM_mul_supportProj {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) :
    sqrtM hB.1 * supportProj hB.1 = sqrtM hB.1 := by
  unfold sqrtM supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hB.1 fun i => ?_
  split_ifs <;> simp

theorem B_mul_invSqrt {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) :
    B * invSqrt hB.1 = sqrtM hB.1 := by
  calc
    B * invSqrt hB.1 =
        (sqrtM hB.1 * sqrtM hB.1) * invSqrt hB.1 := by
      rw [sqrtM_mul_sqrtM hB]
    _ = sqrtM hB.1 * (sqrtM hB.1 * invSqrt hB.1) := by
      rw [Matrix.mul_assoc]
    _ = sqrtM hB.1 * supportProj hB.1 := by
      rw [sqrtM_mul_invSqrt]
    _ = sqrtM hB.1 := sqrtM_mul_supportProj hB

/-- Whitening and unwhitening reproduce the target on the supported branch. -/
theorem sqrt_whitened_sqrt {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.IsHermitian)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) :
    sqrtM hB.1 * whitened B C hB.1 * sqrtM hB.1 = C := by
  unfold whitened
  calc
    sqrtM hB.1 * (invSqrt hB.1 * C * invSqrt hB.1) * sqrtM hB.1 =
        (sqrtM hB.1 * invSqrt hB.1) * C *
          (invSqrt hB.1 * sqrtM hB.1) := by
      simp only [Matrix.mul_assoc]
    _ = supportProj hB.1 * C * supportProj hB.1 := by
      rw [sqrtM_mul_invSqrt, invSqrt_mul_sqrtM]
    _ = C := by rw [support_mul_target hB hC hker, target_mul_support hB hker]

/-- Source energy becomes Euclidean norm squared after multiplication by
`B^{1/2}`. -/
theorem rayleigh_source_eq_sqrt_norm {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (x : Fin d → ℂ) :
    rayleigh B x = ∑ i, ‖(sqrtM hB.1 *ᵥ x) i‖ ^ 2 := by
  rw [← rayleigh_one]
  unfold rayleigh
  apply congrArg Complex.re
  rw [Matrix.one_mulVec]
  rw [← dotProduct_mulVec_hermitian (sqrtM_posSemidef hB).1 x
    (sqrtM hB.1 *ᵥ x)]
  rw [Matrix.mulVec_mulVec, sqrtM_mul_sqrtM hB]
/-- Target energy is the Rayleigh form of the whitened target evaluated at
`B^{1/2}x`. -/
theorem rayleigh_target_eq_whitened_sqrt
    {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0)
    (x : Fin d → ℂ) :
    rayleigh C x = rayleigh (whitened B C hB.1)
      (sqrtM hB.1 *ᵥ x) := by
  unfold rayleigh
  apply congrArg Complex.re
  rw [← dotProduct_mulVec_hermitian (sqrtM_posSemidef hB).1 x
    (whitened B C hB.1 *ᵥ (sqrtM hB.1 *ᵥ x))]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    sqrt_whitened_sqrt hB hC.1 hker]

/-- The whitened target is supported on `supp B`. -/
theorem support_mul_whitened {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) :
    supportProj hB.1 * whitened B C hB.1 = whitened B C hB.1 := by
  unfold whitened
  calc
    supportProj hB.1 * (invSqrt hB.1 * C * invSqrt hB.1) =
        (supportProj hB.1 * invSqrt hB.1) * C * invSqrt hB.1 := by
      simp only [Matrix.mul_assoc]
    _ = invSqrt hB.1 * C * invSqrt hB.1 := by
      rw [supportProj_mul_invSqrt]

/-- A finite Hermitian spectrum has an index carrying its largest eigenvalue. -/
theorem exists_max_eigenindex {W : Matrix (Fin d) (Fin d) ℂ}
    [Nonempty (Fin d)] (hW : W.IsHermitian) :
    ∃ k : Fin d, ∀ i, hW.eigenvalues i ≤ hW.eigenvalues k := by
  classical
  let vals := Finset.univ.image hW.eigenvalues
  have hvals : vals.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  have hmem := Finset.max'_mem vals hvals
  obtain ⟨k, hk, hkval⟩ := Finset.mem_image.mp hmem
  refine ⟨k, fun i => ?_⟩
  rw [hkval]
  exact Finset.le_max' vals (hW.eigenvalues i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The largest eigenvalue is a Rayleigh upper bound. -/
theorem rayleigh_le_max_eigenvalue {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W.PosSemidef) {k : Fin d}
    (hk : ∀ i, hW.1.eigenvalues i ≤ hW.1.eigenvalues k)
    (x : Fin d → ℂ) :
    rayleigh W x ≤ hW.1.eigenvalues k * ∑ i, ‖x i‖ ^ 2 := by
  have hpsd : (((hW.1.eigenvalues k : ℝ) : ℂ) •
      (1 : Matrix (Fin d) (Fin d) ℂ) - W).PosSemidef := by
    have heq : ((hW.1.eigenvalues k : ℝ) : ℂ) •
        (1 : Matrix (Fin d) (Fin d) ℂ) - W =
        spectralFunction hW.1 (fun l => hW.1.eigenvalues k - id l) := by
      rw [spectralFunction_sub, spectralFunction_const, spectralFunction_id]
    rw [heq]
    exact spectralFunction_posSemidef hW.1 _ fun i => by
      simp only [id]
      linarith [hk i]
  have h := rayleigh_le_of_posSemidef hpsd x
  rw [rayleigh_smul, rayleigh_one] at h
  exact h

/-- Every generalized source/target quotient is bounded by a Rayleigh upper
bound for the whitened target. -/
theorem quotient_le_whitened_max
    {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0)
    {k : Fin d}
    (hk : ∀ i, (whitened_posSemidef hB hC).1.eigenvalues i ≤
      (whitened_posSemidef hB hC).1.eigenvalues k)
    {r : ℝ} (hr : r ∈ quotients B C) :
    r ≤ (whitened_posSemidef hB hC).1.eigenvalues k := by
  obtain ⟨x, hBx, rfl⟩ := hr
  rw [rayleigh_target_eq_whitened_sqrt hB hC hker,
    rayleigh_source_eq_sqrt_norm hB]
  rw [div_le_iff₀]
  · exact rayleigh_le_max_eigenvalue (whitened_posSemidef hB hC) hk _
  · simpa [rayleigh_source_eq_sqrt_norm hB x] using hBx
/-- The eigenvector-basis vector at a maximal eigenvalue is unit, nonzero,
and realizes that Rayleigh value. -/
theorem max_eigenvector_realizes {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W.PosSemidef) (k : Fin d) :
    let y : Fin d → ℂ := ⇑(hW.1.eigenvectorBasis k)
    y ≠ 0 ∧
      W *ᵥ y = (hW.1.eigenvalues k : ℂ) • y ∧
      (∑ i, ‖y i‖ ^ 2) = 1 ∧
      rayleigh W y = hW.1.eigenvalues k := by
  dsimp only
  have hy0 : (⇑(hW.1.eigenvectorBasis k) : Fin d → ℂ) ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 <| hW.1.eigenvectorBasis.orthonormal.ne_zero k
  have heig := hW.1.mulVec_eigenvectorBasis k
  have hinner : star (⇑(hW.1.eigenvectorBasis k) : Fin d → ℂ) ⬝ᵥ
      ⇑(hW.1.eigenvectorBasis k) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      @inner_self_eq_norm_sq_to_K ℂ,
      hW.1.eigenvectorBasis.orthonormal.1 k]
    norm_num
  have hsum : (∑ i, ‖(⇑(hW.1.eigenvectorBasis k) : Fin d → ℂ) i‖ ^ 2) = 1 := by
    have hq : rayleigh (1 : Matrix (Fin d) (Fin d) ℂ)
        ⇑(hW.1.eigenvectorBasis k) = 1 := by
      unfold rayleigh
      rw [Matrix.one_mulVec, hinner]
      norm_num
    rwa [rayleigh_one] at hq
  refine ⟨hy0, ?_, hsum, ?_⟩
  · simpa using heig
  · exact (hW.1.eigenvalues_eq k).symm

/-- Left unwhitening turns the whitened operator into `C B^{†/2}`. -/
theorem sqrt_mul_whitened {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hC : C.IsHermitian)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0) :
    sqrtM hB.1 * whitened B C hB.1 = C * invSqrt hB.1 := by
  unfold whitened
  calc
    sqrtM hB.1 * (invSqrt hB.1 * C * invSqrt hB.1) =
        (sqrtM hB.1 * invSqrt hB.1) * C * invSqrt hB.1 := by
      simp only [Matrix.mul_assoc]
    _ = supportProj hB.1 * C * invSqrt hB.1 := by
      rw [sqrtM_mul_invSqrt]
    _ = C * invSqrt hB.1 := by rw [support_mul_target hB hC hker]

/-- Scaling a vector by a real scalar scales every Rayleigh form by its
square. -/
theorem rayleigh_real_smul_vector (t : ℝ)
    (M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    rayleigh M ((t : ℂ) • x) = t ^ 2 * rayleigh M x := by
  unfold rayleigh
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, ← sq, Complex.re_ofReal_mul]

/-- The maximal whitened eigenvector is supported whenever its eigenvalue is
nonzero. -/
theorem max_eigenvector_supported
    {B C : Matrix (Fin d) (Fin d) ℂ} (hB : B.PosSemidef)
    (y : Fin d → ℂ) {lam : ℝ} (hlam : lam ≠ 0)
    (heig : whitened B C hB.1 *ᵥ y = (lam : ℂ) • y) :
    supportProj hB.1 *ᵥ y = y := by
  have h := congrArg (fun v => supportProj hB.1 *ᵥ v) heig
  rw [Matrix.mulVec_smul] at h
  rw [Matrix.mulVec_mulVec, support_mul_whitened hB, heig] at h
  exact smul_right_injective _ (Complex.ofReal_ne_zero.mpr hlam) h.symm

/-- **RI.6 attainment.**  On the positive finite branch there is a
target-normalized vector attaining inverse influence and satisfying the
generalized eigenvector equation on the supported quotient. -/
theorem source_influence_extremizer_exists
    {B C : Matrix (Fin d) (Fin d) ℂ} [Nonempty (Fin d)]
    (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hker : ∀ x, B *ᵥ x = 0 → C *ᵥ x = 0)
    (hpos : 0 < influence B C) :
    ∃ z : Fin d → ℂ,
      rayleigh C z = 1 ∧
      rayleigh B z = (influence B C)⁻¹ ∧
      B *ᵥ z = (((influence B C)⁻¹ : ℝ) : ℂ) • (C *ᵥ z) := by
  let W := whitened B C hB.1
  have hW : W.PosSemidef := whitened_posSemidef hB hC
  obtain ⟨k, hk⟩ := exists_max_eigenindex hW.1
  let lam : ℝ := hW.1.eigenvalues k
  let y : Fin d → ℂ := ⇑(hW.1.eigenvectorBasis k)
  obtain ⟨hy0, heig, hynorm, hyW⟩ := max_eigenvector_realizes hW k
  have hsup : influence B C = sSup (quotients B C) :=
    influence_eq_sup hB hC hker
  have hqne : (quotients B C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hsup, h, Real.sSup_empty] at hpos
    exact (lt_irrefl 0 hpos)
  have hupper : ∀ r ∈ quotients B C, r ≤ lam := by
    intro r hr
    exact quotient_le_whitened_max hB hC hker hk hr
  have hinflam : influence B C ≤ lam := by
    rw [hsup]
    exact csSup_le hqne hupper
  have hlampos : 0 < lam := lt_of_lt_of_le hpos hinflam
  have hyQ : supportProj hB.1 *ᵥ y = y :=
    max_eigenvector_supported hB y hlampos.ne' heig
  let z0 : Fin d → ℂ := invSqrt hB.1 *ᵥ y
  have hBz0 : rayleigh B z0 = 1 := by
    rw [rayleigh_source_eq_sqrt_norm hB]
    change (∑ i, ‖(sqrtM hB.1 *ᵥ (invSqrt hB.1 *ᵥ y)) i‖ ^ 2) = 1
    rw [Matrix.mulVec_mulVec, sqrtM_mul_invSqrt, hyQ]
    exact hynorm
  have hCz0 : rayleigh C z0 = lam := by
    rw [rayleigh_target_eq_whitened_sqrt hB hC hker]
    change rayleigh W (sqrtM hB.1 *ᵥ (invSqrt hB.1 *ᵥ y)) = lam
    rw [Matrix.mulVec_mulVec, sqrtM_mul_invSqrt, hyQ]
    exact hyW
  have hqmem : lam ∈ quotients B C := by
    refine ⟨z0, ?_, ?_⟩
    · rw [hBz0]
      norm_num
    · rw [hCz0, hBz0, div_one]
  have hbdd : BddAbove (quotients B C) := ⟨lam, hupper⟩
  have hlaminf : lam = influence B C := by
    apply le_antisymm
    · rw [hsup]
      exact le_csSup hbdd hqmem
    · exact hinflam
  have hBvec0 : B *ᵥ z0 = sqrtM hB.1 *ᵥ y := by
    change B *ᵥ (invSqrt hB.1 *ᵥ y) = _
    rw [Matrix.mulVec_mulVec, B_mul_invSqrt hB]
  have hCvec0 : C *ᵥ z0 = (lam : ℂ) • (sqrtM hB.1 *ᵥ y) := by
    have h := congrArg (fun v => sqrtM hB.1 *ᵥ v) heig
    rw [Matrix.mulVec_smul] at h
    rw [Matrix.mulVec_mulVec, sqrt_mul_whitened hB hC.1 hker] at h
    rw [← Matrix.mulVec_mulVec] at h
    exact h
  have hvec0 : B *ᵥ z0 = ((lam⁻¹ : ℝ) : ℂ) • (C *ᵥ z0) := by
    rw [hBvec0, hCvec0, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hlampos.ne', Complex.ofReal_one, one_smul]
  let t : ℝ := (Real.sqrt lam)⁻¹
  let z : Fin d → ℂ := (t : ℂ) • z0
  have ht2 : t ^ 2 = lam⁻¹ := by
    dsimp [t]
    rw [inv_pow, sq, Real.mul_self_sqrt hlampos.le]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [rayleigh_real_smul_vector, hCz0, ht2,
      inv_mul_cancel₀ hlampos.ne']
  · rw [rayleigh_real_smul_vector, hBz0, mul_one, ht2, hlaminf]
  · change B *ᵥ ((t : ℂ) • z0) =
      ((((influence B C)⁻¹ : ℝ) : ℂ) • (C *ᵥ ((t : ℂ) • z0)))
    calc
      B *ᵥ ((t : ℂ) • z0) = (t : ℂ) • (B *ᵥ z0) := by
        rw [Matrix.mulVec_smul]
      _ = (t : ℂ) • (((lam⁻¹ : ℝ) : ℂ) • (C *ᵥ z0)) := by rw [hvec0]
      _ = (((influence B C)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • (C *ᵥ z0)) := by
        rw [← hlaminf]
        exact smul_comm _ _ _
      _ = (((influence B C)⁻¹ : ℝ) : ℂ) • (C *ᵥ ((t : ℂ) • z0)) := by
        rw [Matrix.mulVec_smul]
end SourceInfluenceAttainment
end NCG
