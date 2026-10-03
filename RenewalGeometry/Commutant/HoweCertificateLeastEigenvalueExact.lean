/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.CommutantLaplacianHoweGram
import RenewalGeometry.Commutant.JointCommutatorUnboundedLimitGapChain

/-!
# The finite commutant certificate with the named least positive eigenvalue

Covers `thm:howe-certificate` of the spacetime--gauge duality manuscript on the finite
Hilbert--Schmidt carrier `EuclideanSpace ℂ (n × n)` of `n × n` matrices.

* `HoweCertificateExact.IsLeastPositiveEigenvalue T λ`: `λ > 0` is an eigenvalue of `T` and
  every positive eigenvalue of `T` is `≥ λ`.
* `howeCertificate_leastPositiveEigenvalue_exists`: if the commutant is proper, the commutant
  Laplacian `𝓛_𝒞` has a least positive eigenvalue, namely `jointCommutatorFirstPositiveGap c 1`;
  `howeCertificate_leastPositiveEigenvalue_unique`: every least positive eigenvalue equals it.
* `howeCertificate_coercivity` (`eq:commutant-coercivity`): if `λ_𝒞` is the least positive
  eigenvalue of `𝓛_𝒞`, then `‖X − P_{𝒞'} X‖² ≤ λ_𝒞⁻¹ Σ_j ‖[c_j, X]‖²_HS`.
* `relativeHoweGram_posDef_iff` (`eq:howe-certificate`): for `M ⊆ 𝒞'` and a Hilbert--Schmidt
  orthonormal basis `E` of `M^⊥`, `𝔾_Howe(c | M) ≻ 0 ⟺ 𝒞' = M`.
* `relativeHoweGram_leastEigenvalue_eq` (closing clause): on that branch, when `M^⊥ ≠ 0`, the
  least eigenvalue of `𝔾_Howe(c | M)` is the least positive eigenvalue of `𝓛_𝒞`.
* `howeCertificate_exact`: the assembled theorem.

The proof of the closing clause transports along the unitary coordinates
`x ↦ Σ_a x_a E_a` of `M^⊥`, which intertwine `𝔾_Howe` with `𝓛_𝒞` (`𝓛_𝒞` preserves `M^⊥`
whenever `M ⊆ Ker 𝓛_𝒞`).
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RenewalGeometry

namespace HoweCertificateExact

open Matrix

/-- `λ` is the **least positive eigenvalue** of the operator `T`: it is a positive eigenvalue,
and every positive eigenvalue is at least `λ`. -/
def IsLeastPositiveEigenvalue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (lam : ℝ) : Prop :=
  0 < lam ∧ Module.End.HasEigenvalue T.toLinearMap (lam : ℂ) ∧
    ∀ ν : ℝ, 0 < ν → Module.End.HasEigenvalue T.toLinearMap (ν : ℂ) → lam ≤ ν

/-- A least positive eigenvalue is unique. -/
theorem IsLeastPositiveEigenvalue.unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T : E →L[ℂ] E} {lam mu : ℝ}
    (h1 : IsLeastPositiveEigenvalue T lam) (h2 : IsLeastPositiveEigenvalue T mu) :
    lam = mu :=
  le_antisymm (h1.2.2 mu h2.1 h2.2.1) (h2.2.2 lam h1.1 h1.2.1)

end HoweCertificateExact

open HoweCertificateExact Matrix

variable {n : Type*} [Fintype n] {s : ℕ}

/-- `‖∂ x‖² = Σ_j ‖[c_j, x]‖²_HS` on the stacked carrier. -/
theorem howeCertificate_norm_jointCommutatorCLM_sq (c : Fin s → Matrix n n ℂ)
    (x : EuclideanSpace ℂ (n × n)) :
    ‖jointCommutatorCLM c x‖ ^ 2 = ∑ j, ‖adCLM c j x‖ ^ 2 := by
  have h := inner_jointCommutatorCLM c x x
  calc ‖jointCommutatorCLM c x‖ ^ 2
      = RCLike.re ⟪jointCommutatorCLM c x, jointCommutatorCLM c x⟫_ℂ :=
        (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (∑ j, ⟪adCLM c j x, adCLM c j x⟫_ℂ) := by rw [h]
    _ = ∑ j, RCLike.re ⟪adCLM c j x, adCLM c j x⟫_ℂ := map_sum _ _ _
    _ = ∑ j, ‖adCLM c j x‖ ^ 2 := by simp_rw [inner_self_eq_norm_sq]

/-- If the commutant is a proper subspace, the complement-compressed shift-`1` resolvent of the
commutant Laplacian is nonzero. -/
theorem howeCertificate_complementCompression_ne_zero (c : Fin s → Matrix n n ℂ)
    (hker : LinearMap.ker (jointCommutatorCLM c).toLinearMap ≠ ⊤) :
    SpectralGap.complementCompression (jointCommutatorResolvent c 1 one_pos)
      (jointCommutatorKernelProjection c) ≠ 0 := by
  apply SpectralGap.complementCompression_ne_zero_of_injective_of_commute
  · exact (shiftedCommutantLaplacianEquiv c 1 one_pos).symm.injective
  · exact jointCommutatorKernelProjection_isStarProjection c
  · exact jointCommutatorResolvent_commute_kernelProjection c 1 one_pos
  · intro h1
    apply hker
    rw [eq_top_iff]
    intro x _
    have hx : jointCommutatorKernelProjection c x = x := by rw [h1]; rfl
    rw [← hx, ← range_jointCommutatorKernelProjection c]
    exact ⟨x, rfl⟩

/-- **Existence of `λ_𝒞`.**  If the commutant `𝒞' = Ker ∂` is a proper subspace of the
Hilbert--Schmidt space, `jointCommutatorFirstPositiveGap c 1` is the least positive eigenvalue
of the commutant Laplacian. -/
theorem howeCertificate_leastPositiveEigenvalue_exists (c : Fin s → Matrix n n ℂ)
    (hker : LinearMap.ker (jointCommutatorCLM c).toLinearMap ≠ ⊤) :
    IsLeastPositiveEigenvalue (commutantLaplacianCLM c) (jointCommutatorFirstPositiveGap c 1) := by
  have h := jointCommutator_inverseNormGap_is_leastPositiveEigenvalue c 1 one_pos
    (howeCertificate_complementCompression_ne_zero c hker)
  have hgap : jointCommutatorFirstPositiveGap c 1 =
      ‖SpectralGap.complementCompression (jointCommutatorResolvent c 1 one_pos)
        (jointCommutatorKernelProjection c)‖⁻¹ - 1 := by
    rw [jointCommutatorFirstPositiveGap, jointCommutatorResolventAllShifts_of_pos c 1 one_pos]
  rw [hgap]
  exact h

/-- A positive eigenvector of the commutant Laplacian lies outside the commutant, so a least
positive eigenvalue forces a proper commutant. -/
theorem howeCertificate_ker_ne_top_of_leastPositiveEigenvalue (c : Fin s → Matrix n n ℂ)
    {lam : ℝ} (h : IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam) :
    LinearMap.ker (jointCommutatorCLM c).toLinearMap ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := h.2.1.exists_hasEigenvector
  have hvker : v ∈ LinearMap.ker (commutantLaplacianCLM c).toLinearMap := by
    rw [ker_commutantLaplacianCLM, htop]; exact Submodule.mem_top
  have hLv : commutantLaplacianCLM c v = 0 := LinearMap.mem_ker.mp hvker
  have happly := hv.apply_eq_smul
  change commutantLaplacianCLM c v = _ at happly
  rw [hLv] at happly
  have hlam : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h.1.ne'
  exact hv.2 ((smul_eq_zero.mp happly.symm).resolve_left hlam)

/-- **Uniqueness of `λ_𝒞`.**  Every least positive eigenvalue of the commutant Laplacian is
`jointCommutatorFirstPositiveGap c 1`. -/
theorem howeCertificate_leastPositiveEigenvalue_unique (c : Fin s → Matrix n n ℂ) {lam : ℝ}
    (h : IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam) :
    lam = jointCommutatorFirstPositiveGap c 1 :=
  h.unique (howeCertificate_leastPositiveEigenvalue_exists c
    (howeCertificate_ker_ne_top_of_leastPositiveEigenvalue c h))

/-- **`eq:commutant-coercivity`** with the named constant: if `λ_𝒞` is the least positive
eigenvalue of the commutant Laplacian, then for every Hilbert--Schmidt vector `X`,
`‖X − P_{𝒞'} X‖² ≤ λ_𝒞⁻¹ Σ_j ‖[c_j, X]‖²_HS`, with `P_{𝒞'}` the orthogonal projection onto
the commutant `Ker ∂`. -/
theorem howeCertificate_coercivity (c : Fin s → Matrix n n ℂ) {lam : ℝ}
    (h : IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam)
    (X : EuclideanSpace ℂ (n × n)) :
    ‖X - jointCommutatorKernelProjection c X‖ ^ 2 ≤ lam⁻¹ * ∑ j, ‖adCLM c j X‖ ^ 2 := by
  have hcoer := jointCommutatorFirstPositiveGap_coercivity c 1 one_pos X
  rw [← howeCertificate_leastPositiveEigenvalue_unique c h,
    howeCertificate_norm_jointCommutatorCLM_sq] at hcoer
  rw [le_inv_mul_iff₀ h.1]
  exact hcoer

/-- **`eq:commutant-coercivity`** in matrix form:
`‖X − P_{𝒞'}X‖²_HS ≤ λ_𝒞⁻¹ Σ_j Re tr([c_j,X]ᴴ [c_j,X])`. -/
theorem howeCertificate_coercivity_matrix (c : Fin s → Matrix n n ℂ) {lam : ℝ}
    (h : IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam) (X : Matrix n n ℂ) :
    ‖matrixL2 X - jointCommutatorKernelProjection c (matrixL2 X)‖ ^ 2 ≤
      lam⁻¹ * ∑ j, (((c j * X - X * c j)ᴴ * (c j * X - X * c j)).trace).re := by
  have h1 := howeCertificate_coercivity c h (matrixL2 X)
  rw [← howeCertificate_norm_jointCommutatorCLM_sq, jointCommutatorCLM_norm_sq] at h1
  exact h1

/-! ### Unitary coordinates of `M^⊥` -/

/-- The synthesis map `x ↦ Σ_a x_a E_a` of a labelled family of matrices into the
Hilbert--Schmidt carrier. -/
def howeCoordinateSynthesis {r : ℕ} (E : Fin r → Matrix n n ℂ) (x : Fin r → ℂ) :
    EuclideanSpace ℂ (n × n) :=
  ∑ a, x a • matrixL2 (E a)

theorem howeCoordinateSynthesis_inner {r : ℕ} {E : Fin r → Matrix n n ℂ}
    (hE : Orthonormal ℂ (fun a => matrixL2 (E a))) (x : Fin r → ℂ) (c : Fin r) :
    ⟪matrixL2 (E c), howeCoordinateSynthesis E x⟫_ℂ = x c := by
  rw [howeCoordinateSynthesis, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp hE c]
  simp

theorem howeCoordinateSynthesis_injective {r : ℕ} {E : Fin r → Matrix n n ℂ}
    (hE : Orthonormal ℂ (fun a => matrixL2 (E a))) :
    Function.Injective (howeCoordinateSynthesis E) := by
  intro x y hxy
  funext a
  rw [← howeCoordinateSynthesis_inner hE x a, hxy, howeCoordinateSynthesis_inner hE y a]

theorem howeCoordinateSynthesis_zero {r : ℕ} (E : Fin r → Matrix n n ℂ) :
    howeCoordinateSynthesis E 0 = 0 := by
  simp [howeCoordinateSynthesis]

theorem howeCoordinateSynthesis_smul {r : ℕ} (E : Fin r → Matrix n n ℂ) (t : ℂ)
    (x : Fin r → ℂ) :
    howeCoordinateSynthesis E (t • x) = t • howeCoordinateSynthesis E x := by
  simp only [howeCoordinateSynthesis, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem howeCoordinateSynthesis_mem {M : Submodule ℂ (EuclideanSpace ℂ (n × n))} {r : ℕ}
    {E : Fin r → Matrix n n ℂ} (hE : IsHSOrthonormalBasisOf M E) (x : Fin r → ℂ) :
    howeCoordinateSynthesis E x ∈ Mᗮ := by
  rw [← hE.2]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- Two vectors of `M^⊥` with the same coordinates against an orthonormal basis of `M^⊥` agree. -/
theorem howeCertificate_eq_of_inner_basis {M : Submodule ℂ (EuclideanSpace ℂ (n × n))}
    {r : ℕ} {E : Fin r → Matrix n n ℂ} (hE : IsHSOrthonormalBasisOf M E)
    {v w : EuclideanSpace ℂ (n × n)} (hv : v ∈ Mᗮ) (hw : w ∈ Mᗮ)
    (h : ∀ a, ⟪matrixL2 (E a), v⟫_ℂ = ⟪matrixL2 (E a), w⟫_ℂ) : v = w := by
  have hd : v - w ∈ Mᗮ := Submodule.sub_mem _ hv hw
  have hle : Submodule.span ℂ (Set.range fun a => matrixL2 (E a)) ≤ (ℂ ∙ (v - w))ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right,
      h a, sub_self]
  rw [hE.2] at hle
  have h0 := hle hd
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h0
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- Every vector of `M^⊥` is the synthesis of its coordinates. -/
theorem howeCertificate_eq_synthesis {M : Submodule ℂ (EuclideanSpace ℂ (n × n))} {r : ℕ}
    {E : Fin r → Matrix n n ℂ} (hE : IsHSOrthonormalBasisOf M E)
    {v : EuclideanSpace ℂ (n × n)} (hv : v ∈ Mᗮ) :
    v = howeCoordinateSynthesis E (fun a => ⟪matrixL2 (E a), v⟫_ℂ) :=
  howeCertificate_eq_of_inner_basis hE hv (howeCoordinateSynthesis_mem hE _)
    fun a => (howeCoordinateSynthesis_inner hE.1 (fun a => ⟪matrixL2 (E a), v⟫_ℂ) a).symm

/-- The quadratic form of the relative Howe Gram is the commutator energy of the synthesised
vector: `x^* 𝔾 x = ‖∂(Σ_a x_a E_a)‖²`. -/
theorem relativeHoweGram_quadraticForm (c : Fin s → Matrix n n ℂ) {r : ℕ}
    (E : Fin r → Matrix n n ℂ) (x : Fin r → ℂ) :
    star x ⬝ᵥ (relativeHoweGram c E *ᵥ x) =
      ((‖jointCommutatorCLM c (howeCoordinateSynthesis E x)‖ ^ 2 : ℝ) : ℂ) := by
  have hsq : ((‖jointCommutatorCLM c (howeCoordinateSynthesis E x)‖ ^ 2 : ℝ) : ℂ) =
      ⟪jointCommutatorCLM c (howeCoordinateSynthesis E x),
        jointCommutatorCLM c (howeCoordinateSynthesis E x)⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hsq]
  simp only [howeCoordinateSynthesis, map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply,
    relativeHoweGram_eq_inner_jointCommutatorCLM, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

/-- **`eq:howe-certificate`.**  For a proposed protected subspace `M ⊆ 𝒞' = Ker ∂` and a
Hilbert--Schmidt orthonormal basis `E` of `M^⊥`, the relative Howe Gram is positive definite
exactly when the commutant equals `M`. -/
theorem relativeHoweGram_posDef_iff (c : Fin s → Matrix n n ℂ)
    {M : Submodule ℂ (EuclideanSpace ℂ (n × n))} {r : ℕ} {E : Fin r → Matrix n n ℂ}
    (hE : IsHSOrthonormalBasisOf M E)
    (hM : M ≤ LinearMap.ker (jointCommutatorCLM c).toLinearMap) :
    (relativeHoweGram c E).PosDef ↔ LinearMap.ker (jointCommutatorCLM c).toLinearMap = M := by
  rw [← howe_certificate (jointCommutatorCLM c).toLinearMap M hM,
    Matrix.posDef_iff_dotProduct_mulVec]
  simp only [relativeHoweGram_quadraticForm, Complex.zero_lt_real, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨-, h⟩ v hv hv0
    have hvx := howeCertificate_eq_synthesis hE hv
    rw [hvx]
    refine h fun hx => hv0 ?_
    rw [hvx, hx, howeCoordinateSynthesis_zero]
  · intro h
    refine ⟨relativeHoweGram_isHermitian c E, fun x hx => h _ (howeCoordinateSynthesis_mem hE x) ?_⟩
    intro h0
    apply hx
    apply howeCoordinateSynthesis_injective hE.1
    rw [h0, howeCoordinateSynthesis_zero]

/-- The commutant Laplacian maps into `M^⊥` whenever `M ⊆ Ker ∂`. -/
theorem commutantLaplacianCLM_mem_orthogonal (c : Fin s → Matrix n n ℂ)
    {M : Submodule ℂ (EuclideanSpace ℂ (n × n))}
    (hM : M ≤ LinearMap.ker (jointCommutatorCLM c).toLinearMap)
    (v : EuclideanSpace ℂ (n × n)) : commutantLaplacianCLM c v ∈ Mᗮ := by
  rw [Submodule.mem_orthogonal]
  intro m hm
  rw [commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  have h0 : jointCommutatorCLM c m = 0 := LinearMap.mem_ker.mp (hM hm)
  rw [h0, inner_zero_left]

/-- The unitary coordinates of `M^⊥` intertwine the relative Howe Gram with the commutant
Laplacian: `𝓛_𝒞 (Σ_a x_a E_a) = Σ_a (𝔾 x)_a E_a`. -/
theorem commutantLaplacianCLM_howeCoordinateSynthesis (c : Fin s → Matrix n n ℂ)
    {M : Submodule ℂ (EuclideanSpace ℂ (n × n))} {r : ℕ} {E : Fin r → Matrix n n ℂ}
    (hE : IsHSOrthonormalBasisOf M E)
    (hM : M ≤ LinearMap.ker (jointCommutatorCLM c).toLinearMap) (x : Fin r → ℂ) :
    commutantLaplacianCLM c (howeCoordinateSynthesis E x) =
      howeCoordinateSynthesis E (relativeHoweGram c E *ᵥ x) := by
  apply howeCertificate_eq_of_inner_basis hE (commutantLaplacianCLM_mem_orthogonal c hM _)
    (howeCoordinateSynthesis_mem hE _)
  intro a
  rw [howeCoordinateSynthesis_inner hE.1, commutantLaplacianCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [howeCoordinateSynthesis, map_sum, map_smul, inner_sum, inner_smul_right,
    Matrix.mulVec, dotProduct, relativeHoweGram_eq_inner_jointCommutatorCLM]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Closing clause of `thm:howe-certificate`.**  On the exact branch `𝒞' = M`, the least
eigenvalue of the relative Howe Gram is the least positive eigenvalue `λ_𝒞` of the commutant
Laplacian: `λ_𝒞` is one of the (real) eigenvalues of `𝔾_Howe(c | M)` and all of them are
`≥ λ_𝒞`.  (A least positive eigenvalue exists exactly when the complement `M^⊥` is nonzero, see
`howeCertificate_leastPositiveEigenvalue_exists` and
`howeCertificate_ker_ne_top_of_leastPositiveEigenvalue`.) -/
theorem relativeHoweGram_leastEigenvalue_eq (c : Fin s → Matrix n n ℂ)
    {M : Submodule ℂ (EuclideanSpace ℂ (n × n))} {r : ℕ} {E : Fin r → Matrix n n ℂ}
    (hE : IsHSOrthonormalBasisOf M E)
    (hker : LinearMap.ker (jointCommutatorCLM c).toLinearMap = M) {lam : ℝ}
    (hlam : IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam) :
    (∃ i, (relativeHoweGram_isHermitian c E).eigenvalues i = lam) ∧
      ∀ i, lam ≤ (relativeHoweGram_isHermitian c E).eigenvalues i := by
  classical
  have hM : M ≤ LinearMap.ker (jointCommutatorCLM c).toLinearMap := hker.ge
  set G := relativeHoweGram c E with hGdef
  have hG : G.IsHermitian := relativeHoweGram_isHermitian c E
  have hPD : G.PosDef := (relativeHoweGram_posDef_iff c hE hM).mpr hker
  constructor
  · -- `λ_𝒞` is an eigenvalue of the Gram
    obtain ⟨v, hv⟩ := hlam.2.1.exists_hasEigenvector
    have hLv : commutantLaplacianCLM c v = ((lam : ℝ) : ℂ) • v := hv.apply_eq_smul
    have hlam0 : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam.1.ne'
    have hvM : v ∈ Mᗮ := by
      have hv' : v = (((lam : ℝ) : ℂ)⁻¹) • commutantLaplacianCLM c v := by
        rw [hLv, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      rw [hv']
      exact Submodule.smul_mem _ _ (commutantLaplacianCLM_mem_orthogonal c hM v)
    set x : Fin r → ℂ := fun a => ⟪matrixL2 (E a), v⟫_ℂ with hxdef
    have hvx : v = howeCoordinateSynthesis E x := howeCertificate_eq_synthesis hE hvM
    have hGx : G *ᵥ x = ((lam : ℝ) : ℂ) • x := by
      apply howeCoordinateSynthesis_injective hE.1
      rw [← commutantLaplacianCLM_howeCoordinateSynthesis c hE hM, ← hvx, hLv,
        howeCoordinateSynthesis_smul, ← hvx]
    have hx0 : x ≠ 0 := by
      intro h0
      apply hv.2
      rw [hvx, h0, howeCoordinateSynthesis_zero]
    have hspec : lam ∈ spectrum ℝ G := by
      rw [spectrum.mem_iff]
      intro hunit
      have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
      apply hx0
      apply hinj
      rw [Matrix.sub_mulVec, hGx, Matrix.mulVec_zero, Algebra.algebraMap_eq_smul_one,
        Matrix.smul_mulVec, Matrix.one_mulVec, ← Complex.coe_smul, sub_self]
    rw [hG.spectrum_real_eq_range_eigenvalues] at hspec
    exact hspec
  · -- every eigenvalue of the Gram is a positive eigenvalue of `𝓛_𝒞`
    intro i
    set y : Fin r → ℂ := ⇑(hG.eigenvectorBasis i) with hydef
    have hGy : G *ᵥ y = ((hG.eigenvalues i : ℝ) : ℂ) • y := by
      rw [hydef, hG.mulVec_eigenvectorBasis i, Complex.coe_smul]
    have hy0 : y ≠ 0 := by
      intro h0
      have hne := (hG.eigenvectorBasis).orthonormal.ne_zero i
      apply hne
      ext k
      have := congrFun h0 k
      simpa [hydef] using this
    have hpos : 0 < hG.eigenvalues i := hPD.eigenvalues_pos i
    apply hlam.2.2 _ hpos
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := howeCoordinateSynthesis E y)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      change commutantLaplacianCLM c (howeCoordinateSynthesis E y) = _
      rw [commutantLaplacianCLM_howeCoordinateSynthesis c hE hM, hGy,
        howeCoordinateSynthesis_smul]
    · intro h0
      apply hy0
      apply howeCoordinateSynthesis_injective hE.1
      rw [h0, howeCoordinateSynthesis_zero]

/-- The kernel of the joint commutator is the commutant of the span `𝒞 = span{c_j}`: a
matrix commutes with every element of `𝒞` iff it commutes with each generator. -/
theorem matrixL2_mem_jointCommutatorCLM_ker_iff_span (c : Fin s → Matrix n n ℂ)
    (X : Matrix n n ℂ) :
    matrixL2 X ∈ LinearMap.ker (jointCommutatorCLM c).toLinearMap ↔
      ∀ a ∈ Submodule.span ℂ (Set.range c), a * X = X * a := by
  rw [matrixL2_mem_jointCommutatorCLM_ker_iff]
  constructor
  · intro h a ha
    induction ha using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
    | smul t x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  · intro h j
    exact h _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **`thm:howe-certificate`** (spacetime--gauge duality manuscript), assembled.  For a finite
generator family `c_1, …, c_s` of `n × n` matrices, on the Hilbert--Schmidt carrier:

1. `𝓛_𝒞 = Σ_j ad_{c_j}^* ad_{c_j}` (`eq:commutant-laplacian`), `𝓛_𝒞 ⪰ 0`, and
   `Ker 𝓛_𝒞 = 𝒞'` (`eq:commutant-kernel`), with `𝒞'` the commutant of `𝒞 = span{c_j}`;
2. if the commutant is proper, `𝓛_𝒞` has a least positive eigenvalue; every least positive
   eigenvalue `λ_𝒞` equals `jointCommutatorFirstPositiveGap c 1` and satisfies
   `‖X − P_{𝒞'}X‖² ≤ λ_𝒞⁻¹ Σ_j ‖[c_j,X]‖²_HS` (`eq:commutant-coercivity`);
3. for `M ⊆ 𝒞'` with Hilbert--Schmidt orthonormal basis `E` of `M^⊥`:
   `𝔾_Howe(c | M) ≻ 0 ⟺ 𝒞' = M` (`eq:howe-certificate`), and on that branch the least
   eigenvalue of `𝔾_Howe(c | M)` is `λ_𝒞`. -/
theorem howeCertificate_exact (c : Fin s → Matrix n n ℂ) :
    commutantLaplacianCLM c = ∑ j, ContinuousLinearMap.adjoint (adCLM c j) ∘L adCLM c j ∧
    (commutantLaplacianCLM c).IsPositive ∧
    (∀ X : Matrix n n ℂ,
      matrixL2 X ∈ LinearMap.ker (commutantLaplacianCLM c).toLinearMap ↔
        ∀ a ∈ Submodule.span ℂ (Set.range c), a * X = X * a) ∧
    (LinearMap.ker (jointCommutatorCLM c).toLinearMap ≠ ⊤ →
      IsLeastPositiveEigenvalue (commutantLaplacianCLM c) (jointCommutatorFirstPositiveGap c 1)) ∧
    (∀ lam : ℝ, IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam →
      lam = jointCommutatorFirstPositiveGap c 1 ∧
      ∀ X : EuclideanSpace ℂ (n × n),
        ‖X - jointCommutatorKernelProjection c X‖ ^ 2 ≤ lam⁻¹ * ∑ j, ‖adCLM c j X‖ ^ 2) ∧
    (∀ (M : Submodule ℂ (EuclideanSpace ℂ (n × n))) (r : ℕ) (E : Fin r → Matrix n n ℂ),
      IsHSOrthonormalBasisOf M E →
      M ≤ LinearMap.ker (jointCommutatorCLM c).toLinearMap →
      ((relativeHoweGram c E).PosDef ↔ LinearMap.ker (jointCommutatorCLM c).toLinearMap = M) ∧
      (LinearMap.ker (jointCommutatorCLM c).toLinearMap = M →
        ∀ lam : ℝ, IsLeastPositiveEigenvalue (commutantLaplacianCLM c) lam →
          (∃ i, (relativeHoweGram_isHermitian c E).eigenvalues i = lam) ∧
            ∀ i, lam ≤ (relativeHoweGram_isHermitian c E).eigenvalues i)) := by
  refine ⟨commutantLaplacianCLM_eq_sum_adjoint_comp c, commutantLaplacianCLM_isPositive c,
    fun X => ?_, howeCertificate_leastPositiveEigenvalue_exists c,
    fun lam h => ⟨howeCertificate_leastPositiveEigenvalue_unique c h,
      howeCertificate_coercivity c h⟩,
    fun M r E hE hM => ⟨relativeHoweGram_posDef_iff c hE hM,
      fun hker lam hlam => relativeHoweGram_leastEigenvalue_eq c hE hker hlam⟩⟩
  rw [ker_commutantLaplacianCLM]
  exact matrixL2_mem_jointCommutatorCLM_ker_iff_span c X

/-! ### Non-vacuity -/

/-- The generator `diag(1, 0)` on `2 × 2` matrices (a non-scalar generator). -/
def howeCertificateWitnessGen : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => !![1, 0; 0, 0]

/-- `diag(1,0)` does not commute with `E₁₂`, so its commutant is proper. -/
theorem howeCertificateWitness_ker_ne_top :
    LinearMap.ker (jointCommutatorCLM howeCertificateWitnessGen).toLinearMap ≠ ⊤ := by
  intro htop
  have hmem : matrixL2 (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈
      LinearMap.ker (jointCommutatorCLM howeCertificateWitnessGen).toLinearMap := by
    rw [htop]; exact Submodule.mem_top
  rw [matrixL2_mem_jointCommutatorCLM_ker_iff] at hmem
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (hmem 0)
  simp [howeCertificateWitnessGen, Matrix.mul_apply, Fin.sum_univ_two] at h

/-- Non-vacuity: for `c = diag(1, 0)` the commutant Laplacian has a least positive eigenvalue
`λ_𝒞`, so the coercivity estimate of `thm:howe-certificate` is not vacuous. -/
example : IsLeastPositiveEigenvalue (commutantLaplacianCLM howeCertificateWitnessGen)
    (jointCommutatorFirstPositiveGap howeCertificateWitnessGen 1) :=
  howeCertificate_leastPositiveEigenvalue_exists _ howeCertificateWitness_ker_ne_top

end RenewalGeometry
