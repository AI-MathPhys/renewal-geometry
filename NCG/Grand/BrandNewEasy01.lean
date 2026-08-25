/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PsdBlockSchurExact

/-!
# Brand-new easy records, batch 01

Exact formalizations of seven brand-new manuscript records:

* `cth:SMOS-pair-contact-no-cocycle` — a bilinear pair contact table on `ℂ²`
  whose degree-zero Ward contact associator does not vanish
  (`SMOSPairContactNoCocycle`);
* `cth:SMOS-separate-Ward-shorts` — separate rowwise Ward repairs that share
  no common improvement, with `P_N Y = 0` and physical residual Gram `2I`
  (`SMOSSeparateWardShorts`);
* `cth:SMQG-determinant-no-covariance` — two invertible retained operators
  with equal determinant and different reflected covariances
  (`SMQGDeterminantNoCovariance`);
* `cth:SMQG-two-point-no-four-point` — positive kernels on `⋀(ℂ²)` with the
  same vacuum and one-particle blocks of which only one is the quasi-free
  exterior kernel of `P = I₂` (`SMQGTwoPointNoFourPoint`);
* `cth:SMQG-zero-positive-carrier` — a positive carrier with strictly
  positive total mass and vanishing complex coherence, hence no determined
  normalized phase (`SMQGZeroPositiveCarrier`);
* `cth:SMST-internal-Dirac-not-full-phase` — the one-complex-dimensional
  winding family `K(θ) = e^{iθ}` with constant internal Dirac
  (`SMSTInternalDiracNotFullPhase`);
* `thm:GT-MP-supported-Schur` — canonical support `P_D = DD^† = D^†D`,
  its uniqueness as the orthogonal projection onto `Ran D = (Ker D)^⊥`, and
  the supported Schur completion CERT.4–CERT.8 (`GTMPSupportedSchur`).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-! ## `cth:SMOS-pair-contact-no-cocycle`
A pair contact table need not satisfy the Ward cocycle. -/

namespace SMOSPairContactNoCocycle

/-- The first minimal projection `e₁ = (1,0)` of `E = ℂ²` with pointwise
product. -/
def e1 : Fin 2 → ℂ := ![1, 0]

/-- The second minimal projection `e₂ = (0,1)` of `E = ℂ²`. -/
def e2 : Fin 2 → ℂ := ![0, 1]

/-- `e₁` is idempotent for the pointwise product. -/
theorem e1_mul_e1 : e1 * e1 = e1 := by
  funext i; fin_cases i <;> simp [e1]

/-- `e₂` is idempotent for the pointwise product. -/
theorem e2_mul_e2 : e2 * e2 = e2 := by
  funext i; fin_cases i <;> simp [e2]

/-- The minimal projections are orthogonal: `e₁e₂ = 0`. -/
theorem e1_mul_e2 : e1 * e2 = 0 := by
  funext i; fin_cases i <;> simp [e1, e2]

/-- The bilinear contact cochain: the unique bilinear extension of the pair
contact table `c(e₁,e₁) = e₂`, `c(eᵢ,eⱼ) = 0` otherwise; explicitly
`c(a,b) = a₀b₀ · e₂`.  It is packaged as an honest bilinear map, so the pair
table is a perfectly finite bilinear source. -/
def contactCochain : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.mk₂ ℂ (fun a b => (a 0 * b 0) • e2)
    (fun a a' b => by simp only [Pi.add_apply]; rw [add_mul, add_smul])
    (fun r a b => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [smul_smul, mul_assoc])
    (fun a b b' => by simp only [Pi.add_apply]; rw [mul_add, add_smul])
    (fun r a b => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [smul_smul, mul_left_comm])

/-- Contact table value `c(e₁,e₁) = e₂`. -/
theorem contactCochain_e1_e1 : contactCochain e1 e1 = e2 := by
  simp [contactCochain, e1]

/-- Contact table value `c(e₁,e₂) = 0`. -/
theorem contactCochain_e1_e2 : contactCochain e1 e2 = 0 := by
  simp [contactCochain, e1, e2]

/-- Contact table value `c(e₂,e₁) = 0`. -/
theorem contactCochain_e2_e1 : contactCochain e2 e1 = 0 := by
  simp [contactCochain, e1, e2]

/-- Contact table value `c(e₂,e₂) = 0`. -/
theorem contactCochain_e2_e2 : contactCochain e2 e2 = 0 := by
  simp [contactCochain, e2]

/-- The degree-zero Ward contact associator of the manuscript
(eq. SMOS-Ward-contact-cocycle with `p = 0`):
`(δ⁰_μ c)(x,y,z) = c(x,y)z + c(xy,z) − x·c(y,z) − c(x,yz)`. -/
def wardContactAssociator (c : (Fin 2 → ℂ) → (Fin 2 → ℂ) → (Fin 2 → ℂ))
    (x y z : Fin 2 → ℂ) : Fin 2 → ℂ :=
  c x y * z + c (x * y) z - x * c y z - c x (y * z)

/-- The boxed counterexample value: `(δ⁰_μ c)(e₁,e₁,e₂) = e₂`. -/
theorem wardContactAssociator_eval :
    wardContactAssociator (fun a b => contactCochain a b) e1 e1 e2 = e2 := by
  simp only [wardContactAssociator, e1_mul_e1, e1_mul_e2, contactCochain_e1_e1,
    contactCochain_e1_e2, e2_mul_e2, map_zero, mul_zero, add_zero, sub_zero]

/-- `e₂ ≠ 0`. -/
theorem e2_ne_zero : e2 ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [e2] at h1

/-- **A pair contact table need not satisfy the Ward cocycle**
(`cth:SMOS-pair-contact-no-cocycle`).  The bilinear contact cochain realizes
the pair table `c(e₁,e₁) = e₂`, `c(eᵢ,eⱼ) = 0` otherwise, yet its degree-zero
Ward contact associator satisfies `(δ⁰_μ c)(e₁,e₁,e₂) = e₂ ≠ 0`: a direct
pairwise contact panel does not establish a consistent Ward identity on
triple products. -/
theorem pairContact_no_cocycle :
    contactCochain e1 e1 = e2 ∧ contactCochain e1 e2 = 0 ∧
      contactCochain e2 e1 = 0 ∧ contactCochain e2 e2 = 0 ∧
      wardContactAssociator (fun a b => contactCochain a b) e1 e1 e2 = e2 ∧
      e2 ≠ 0 :=
  ⟨contactCochain_e1_e1, contactCochain_e1_e2, contactCochain_e2_e1,
    contactCochain_e2_e2, wardContactAssociator_eval, e2_ne_zero⟩

end SMOSPairContactNoCocycle

/-! ## `cth:SMOS-separate-Ward-shorts`
Separate Ward-row repairs need not share one improvement. -/

namespace SMOSSeparateWardShorts

/-- The Ward defect synthesis `Y : ℂ → 𝒦_W = ℂ ⊕ ℂ`, `Yx = (x,x)`, as a
`2 × 1` matrix. -/
def Y : Matrix (Fin 2) (Fin 1) ℂ := !![1; 1]

/-- The trivial-modification synthesis `N : ℂ → 𝒦_W`, `Nℓ = (ℓ,−ℓ)`, as a
`2 × 1` matrix. -/
def N : Matrix (Fin 2) (Fin 1) ℂ := !![1; -1]

/-- The nuisance Gram `G_N = N^*N`. -/
def GN : Matrix (Fin 1) (Fin 1) ℂ := Nᴴ * N

/-- The Moore–Penrose inverse `G_N^†` of the nuisance Gram. -/
noncomputable def GNpinv : Matrix (Fin 1) (Fin 1) ℂ := !![(2 : ℂ)⁻¹]

/-- The nuisance projection `P_N = N G_N^† N^*`. -/
noncomputable def PN : Matrix (Fin 2) (Fin 2) ℂ := N * GNpinv * Nᴴ

/-- The first Ward row is cancelled by the separate fit `ℓ = x`. -/
theorem row_zero_repaired (x : ℂ) : (Y *ᵥ ![x] - N *ᵥ ![x]) 0 = 0 := by
  simp [Y, N]

/-- The second Ward row is cancelled by the separate fit `ℓ = −x`. -/
theorem row_one_repaired (x : ℂ) : (Y *ᵥ ![x] - N *ᵥ ![-x]) 1 = 0 := by
  simp [Y, N]

/-- No one coefficient cancels both rows: for `x ≠ 0` there is no `ℓ` with
`Yx = Nℓ`. -/
theorem no_common_repair {x : ℂ} (hx : x ≠ 0) :
    ¬∃ l : ℂ, Y *ᵥ ![x] = N *ᵥ ![l] := by
  rintro ⟨l, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Y, N] at h0 h1
  apply hx
  linear_combination (h0 + h1) / 2

/-- Uniqueness of the Moore–Penrose inverse: two matrices satisfying the four
Penrose identities for the same `A` coincide. -/
theorem moorePenrose_unique {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n m ℂ) (X W : Matrix m n ℂ)
    (hX1 : A * X * A = A) (hX2 : X * A * X = X)
    (hX3 : (A * X)ᴴ = A * X) (hX4 : (X * A)ᴴ = X * A)
    (hW1 : A * W * A = A) (hW2 : W * A * W = W)
    (hW3 : (A * W)ᴴ = A * W) (hW4 : (W * A)ᴴ = W * A) : X = W := by
  have hAX : A * X = A * W := by
    calc A * X = (A * W * A) * X := by rw [hW1]
      _ = (A * W) * (A * X) := by rw [Matrix.mul_assoc]
      _ = ((A * X)ᴴ * (A * W)ᴴ)ᴴ := by
          rw [← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = ((A * X) * (A * W))ᴴ := by rw [hX3, hW3]
      _ = (A * W)ᴴ := by rw [← Matrix.mul_assoc, hX1]
      _ = A * W := hW3
  have hXA : X * A = W * A := by
    calc X * A = X * (A * W * A) := by rw [hW1]
      _ = X * (A * (W * A)) := by rw [Matrix.mul_assoc A W A]
      _ = (X * A) * (W * A) := by rw [Matrix.mul_assoc]
      _ = ((W * A)ᴴ * (X * A)ᴴ)ᴴ := by
          rw [← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = ((W * A) * (X * A))ᴴ := by rw [hW4, hX4]
      _ = (W * (A * X * A))ᴴ := by
          rw [Matrix.mul_assoc W A (X * A), Matrix.mul_assoc A X A]
      _ = (W * A)ᴴ := by rw [hX1]
      _ = W * A := hW4
  calc X = X * A * X := hX2.symm
    _ = (W * A) * X := by rw [hXA]
    _ = W * (A * X) := by rw [Matrix.mul_assoc]
    _ = W * (A * W) := by rw [hAX]
    _ = W * A * W := by rw [Matrix.mul_assoc]
    _ = W := hW2

/-- The nuisance Gram is `G_N = (2)`. -/
theorem GN_eq : GN = !![(2 : ℂ)] := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [GN, N, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]

/-- `G_N G_N^† = 1`. -/
theorem GN_mul_GNpinv : GN * GNpinv = 1 := by
  rw [GN_eq]
  ext i j
  fin_cases i; fin_cases j
  norm_num [GNpinv, Matrix.mul_apply, Matrix.one_apply]

/-- `G_N^† G_N = 1`. -/
theorem GNpinv_mul_GN : GNpinv * GN = 1 := by
  rw [GN_eq]
  ext i j
  fin_cases i; fin_cases j
  norm_num [GNpinv, Matrix.mul_apply, Matrix.one_apply]

/-- `G_N^†` satisfies all four Penrose identities for `G_N`; by
`moorePenrose_unique` it is therefore THE Moore–Penrose inverse of the
nuisance Gram. -/
theorem GNpinv_penrose :
    GN * GNpinv * GN = GN ∧ GNpinv * GN * GNpinv = GNpinv ∧
      (GN * GNpinv)ᴴ = GN * GNpinv ∧ (GNpinv * GN)ᴴ = GNpinv * GN := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GN_mul_GNpinv, Matrix.one_mul]
  · rw [GNpinv_mul_GN, Matrix.one_mul]
  · rw [GN_mul_GNpinv, Matrix.conjTranspose_one]
  · rw [GNpinv_mul_GN, Matrix.conjTranspose_one]

/-- Any matrix satisfying the four Penrose identities for `G_N` equals
`G_N^†`. -/
theorem GNpinv_unique (X : Matrix (Fin 1) (Fin 1) ℂ)
    (h1 : GN * X * GN = GN) (h2 : X * GN * X = X)
    (h3 : (GN * X)ᴴ = GN * X) (h4 : (X * GN)ᴴ = X * GN) : X = GNpinv :=
  moorePenrose_unique GN X GNpinv h1 h2 h3 h4 GNpinv_penrose.1
    GNpinv_penrose.2.1 GNpinv_penrose.2.2.1 GNpinv_penrose.2.2.2

/-- The nuisance projection in closed form. -/
theorem PN_eq : PN = !![(2 : ℂ)⁻¹, -(2 : ℂ)⁻¹; -(2 : ℂ)⁻¹, (2 : ℂ)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [PN, N, GNpinv, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_one]

/-- `P_N` is Hermitian. -/
theorem PN_isHermitian : PNᴴ = PN := by
  rw [PN_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose_apply]

/-- `P_N` is idempotent. -/
theorem PN_idem : PN * PN = PN := by
  rw [PN_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `P_N` fixes the range of `N`: `P_N N = N`. -/
theorem PN_mul_N : PN * N = N := by
  rw [PN_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- First boxed identity: `P_N Y = 0`. -/
theorem PN_mul_Y : PN * Y = 0 := by
  rw [PN_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Y, Matrix.mul_apply, Fin.sum_univ_two]

/-- Second boxed identity: the physical Ward residual Gram is
`ℂ_W^phys = Y^*(I − P_N)Y = 2I`. -/
theorem physGram_eq : Yᴴ * (1 - PN) * Y = (2 : ℂ) • 1 := by
  rw [PN_eq]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Y, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- **Separate Ward-row repairs need not share one improvement**
(`cth:SMOS-separate-Ward-shorts`).  With `Yx = (x,x)` and `Nℓ = (ℓ,−ℓ)` the
two rows are separately repairable (`ℓ = x` resp. `ℓ = −x`), no single
coefficient repairs both, yet the assembled nuisance projection satisfies
`P_N Y = 0` and the physical residual Gram is `ℂ_W^phys = 2I`: separate
rowwise minimization falsely reports closure. -/
theorem separate_ward_shorts :
    (∀ x : ℂ, (Y *ᵥ ![x] - N *ᵥ ![x]) 0 = 0) ∧
      (∀ x : ℂ, (Y *ᵥ ![x] - N *ᵥ ![-x]) 1 = 0) ∧
      (∀ x : ℂ, x ≠ 0 → ¬∃ l : ℂ, Y *ᵥ ![x] = N *ᵥ ![l]) ∧
      PN * Y = 0 ∧ Yᴴ * (1 - PN) * Y = (2 : ℂ) • 1 :=
  ⟨row_zero_repaired, row_one_repaired, fun _ hx => no_common_repair hx,
    PN_mul_Y, physGram_eq⟩

end SMOSSeparateWardShorts

/-! ## `cth:SMQG-determinant-no-covariance`
Aggregate determinant data do not determine the reflected covariance. -/

namespace SMQGDeterminantNoCovariance

/-- The first retained operator `S₁ = diag(1,2)`. -/
def S1 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]

/-- The second retained operator `S₂ = [[1,1],[0,2]]`. -/
def S2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 2]

/-- `det S₁ = 2`. -/
theorem S1_det : S1.det = 2 := by
  rw [S1, Matrix.det_fin_two_of]; norm_num

/-- `det S₂ = 2`. -/
theorem S2_det : S2.det = 2 := by
  rw [S2, Matrix.det_fin_two_of]; norm_num

/-- `S₁` is invertible. -/
theorem S1_isUnit : IsUnit S1 := by
  rw [Matrix.isUnit_iff_isUnit_det, S1_det]
  exact isUnit_iff_ne_zero.mpr two_ne_zero

/-- `S₂` is invertible. -/
theorem S2_isUnit : IsUnit S2 := by
  rw [Matrix.isUnit_iff_isUnit_det, S2_det]
  exact isUnit_iff_ne_zero.mpr two_ne_zero

/-- The reflected covariance of `S₁` has vanishing off-diagonal source entry:
`(S₁⁻¹)₀₁ = 0`. -/
theorem S1_inv_entry : S1⁻¹ 0 1 = 0 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, S1_det, S1, Matrix.adjugate_fin_two]
  norm_num

/-- The reflected covariance of `S₂` has nonvanishing off-diagonal source
entry: `(S₂⁻¹)₀₁ = −2⁻¹`; a source detecting the off-diagonal entry separates
the two reflected covariances. -/
theorem S2_inv_entry : S2⁻¹ 0 1 = -(2 : ℂ)⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, S2_det, S2, Matrix.adjugate_fin_two]
  norm_num

/-- The reflected covariances differ: `S₁⁻¹ ≠ S₂⁻¹`. -/
theorem reflected_covariances_differ : S1⁻¹ ≠ S2⁻¹ := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [S1_inv_entry, S2_inv_entry] at h01
  norm_num at h01

/-- **Aggregate determinant data do not determine the reflected covariance**
(`cth:SMQG-determinant-no-covariance`).  The two invertible retained
operators `S₁, S₂` have the same determinant but different reflected
covariances `S₁⁻¹ ≠ S₂⁻¹`, so the partition and its phase do not reconstruct
the direct mixed two-point word. -/
theorem determinant_no_covariance :
    IsUnit S1 ∧ IsUnit S2 ∧ S1.det = S2.det ∧ S1⁻¹ ≠ S2⁻¹ :=
  ⟨S1_isUnit, S2_isUnit, by rw [S1_det, S2_det],
    reflected_covariances_differ⟩

end SMQGDeterminantNoCovariance

/-! ## `cth:SMQG-two-point-no-four-point`
Positive two-point data do not determine the four-point word. -/

namespace SMQGTwoPointNoFourPoint

/-- The quasi-free exterior kernel `Γ_∧(P) = 1 ⊕ P ⊕ ⋀²P` of a one-particle
kernel `P` on `E = ℂ²`, rendered on the total exterior space
`⋀⁰E ⊕ ⋀¹E ⊕ ⋀²E ≅ ℂ⁴` (index `0`: vacuum, indices `1,2`: one-particle,
index `3`: top degree, on which `⋀²P` acts as `det P`). -/
def exteriorKernel (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, P 0 0, P 0 1, 0;
     0, P 1 0, P 1 1, 0;
     0, 0, 0, P.det]

/-- The kernel `K⁽¹⁾ = 1 ⊕ I₂ ⊕ 1` of (QG.42). -/
def K1 : Matrix (Fin 4) (Fin 4) ℂ := 1

/-- The kernel `K⁽²⁾ = 1 ⊕ I₂ ⊕ 0` of (QG.42). -/
def K2 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, 1, 0]

/-- `K⁽¹⁾` is positive. -/
theorem K1_posSemidef : K1.PosSemidef := Matrix.PosSemidef.one

/-- `K⁽²⁾` is positive. -/
theorem K2_posSemidef : K2.PosSemidef := by
  refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> norm_num [Complex.le_def]

/-- `K⁽¹⁾` and `K⁽²⁾` have the same vacuum and one-particle blocks: every
entry outside the top-degree corner `(3,3)` agrees. -/
theorem same_two_point_blocks :
    ∀ i j : Fin 4, ¬(i = 3 ∧ j = 3) → K1 i j = K2 i j := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [K1, K2]

/-- The two kernels differ in the four-point (top-degree) word:
`K⁽¹⁾₃₃ = 1` while `K⁽²⁾₃₃ = 0`, so `K⁽¹⁾ ≠ K⁽²⁾`. -/
theorem four_point_differs : K1 3 3 = 1 ∧ K2 3 3 = 0 ∧ K1 ≠ K2 := by
  refine ⟨by simp [K1], by simp [K2], fun h => ?_⟩
  have h33 := congrFun (congrFun h 3) 3
  simp [K1, K2] at h33

/-- `K⁽¹⁾` is the quasi-free exterior kernel of `P = I₂`. -/
theorem K1_is_exteriorKernel : exteriorKernel 1 = K1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exteriorKernel, K1]

/-- `K⁽²⁾` is not the quasi-free exterior kernel of any one-particle kernel:
its one-particle block forces `P = I₂`, whence the top block would have to be
`det I₂ = 1 ≠ 0`. -/
theorem K2_not_exteriorKernel :
    ∀ P : Matrix (Fin 2) (Fin 2) ℂ, exteriorKernel P ≠ K2 := by
  intro P h
  have h11 : P 0 0 = 1 := by
    have := congrFun (congrFun h 1) 1
    simpa [exteriorKernel, K2, Matrix.diagonal_apply] using this
  have h12 : P 0 1 = 0 := by
    have := congrFun (congrFun h 1) 2
    simpa [exteriorKernel, K2, Matrix.diagonal_apply] using this
  have h21 : P 1 0 = 0 := by
    have := congrFun (congrFun h 2) 1
    simpa [exteriorKernel, K2, Matrix.diagonal_apply] using this
  have h22 : P 1 1 = 1 := by
    have := congrFun (congrFun h 2) 2
    simpa [exteriorKernel, K2, Matrix.diagonal_apply] using this
  have hdet : P.det = 0 := by
    have := congrFun (congrFun h 3) 3
    simpa [exteriorKernel, K2, Matrix.diagonal_apply] using this
  rw [Matrix.det_fin_two, h11, h12, h21, h22] at hdet
  norm_num at hdet

/-- **Positive two-point data do not determine the four-point word**
(`cth:SMQG-two-point-no-four-point`).  On `⋀(ℂ²)` with `P = I₂`, the
positive kernels `K⁽¹⁾ = 1 ⊕ I₂ ⊕ 1` and `K⁽²⁾ = 1 ⊕ I₂ ⊕ 0` share the
vacuum and one-particle blocks, but only `K⁽¹⁾` is the quasi-free exterior
kernel — `K⁽²⁾` is not the exterior kernel of any one-particle datum. -/
theorem two_point_no_four_point :
    K1.PosSemidef ∧ K2.PosSemidef ∧
      (∀ i j : Fin 4, ¬(i = 3 ∧ j = 3) → K1 i j = K2 i j) ∧
      K1 ≠ K2 ∧ exteriorKernel 1 = K1 ∧
      ∀ P : Matrix (Fin 2) (Fin 2) ℂ, exteriorKernel P ≠ K2 :=
  ⟨K1_posSemidef, K2_posSemidef, same_two_point_blocks,
    four_point_differs.2.2, K1_is_exteriorKernel, K2_not_exteriorKernel⟩

end SMQGTwoPointNoFourPoint

/-! ## `cth:SMQG-zero-positive-carrier`
A regular positive carrier can coexist with a partition zero. -/

namespace SMQGZeroPositiveCarrier

/-- The carrier: two equal positive histories with complex weights `+1` and
`−1`. -/
def w : Fin 2 → ℂ := ![1, -1]

/-- Every history carries strictly positive mass `‖wᵢ‖ = 1`. -/
theorem history_mass (i : Fin 2) : ‖w i‖ = 1 := by
  fin_cases i <;> simp [w]

/-- The positive total variation of the carrier is `2`, strictly positive. -/
theorem total_mass : ∑ i, ‖w i‖ = 2 := by
  simp [history_mass]

/-- The complex determinant coherence (the complex sum) vanishes. -/
theorem coherence_zero : ∑ i, w i = 0 := by
  simp [w, Fin.sum_univ_two]

/-- At the partition zero, no normalized fermionic phase is determined: the
polar equation `∑wᵢ = ‖∑wᵢ‖·u` does not single out a unimodular `u` (both
`u = 1` and `u = −1` satisfy it). -/
theorem no_normalized_phase :
    ¬∃! u : ℂ, ‖u‖ = 1 ∧ (∑ i, w i) = (‖∑ i, w i‖ : ℂ) * u := by
  rintro ⟨u, -, huniq⟩
  have h1 : (1 : ℂ) = u := huniq 1 ⟨by simp, by rw [coherence_zero]; simp⟩
  have h2 : (-1 : ℂ) = u := huniq (-1) ⟨by simp, by rw [coherence_zero]; simp⟩
  rw [← h2] at h1
  norm_num at h1

/-- **A regular positive carrier can coexist with a partition zero**
(`cth:SMQG-zero-positive-carrier`).  The positive carrier of two equal
histories with complex weights `±1` has strictly positive total mass `2`
while its complex determinant coherence is `0`; hence the regularity of the
positive acquisition instrument does not license a normalized fermionic
phase at the partition zero. -/
theorem zero_positive_carrier :
    (0 : ℝ) < ∑ i, ‖w i‖ ∧ (∑ i, w i) = 0 ∧
      ¬∃! u : ℂ, ‖u‖ = 1 ∧ (∑ i, w i) = (‖∑ i, w i‖ : ℂ) * u :=
  ⟨by rw [total_mass]; norm_num, coherence_zero, no_normalized_phase⟩

end SMQGZeroPositiveCarrier

/-! ## `cth:SMST-internal-Dirac-not-full-phase`
The internal finite Dirac does not determine the full phase. -/

namespace SMSTInternalDiracNotFullPhase

/-- The spacetime constituent on the parameter circle:
`D_sp(θ) = e^{iθ} − 1` (one complex dimension, `⋆₀ = Γ_Cl = 1`). -/
noncomputable def Dsp (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I) - 1

/-- The fixed internal finite Dirac `D_F = 1`. -/
def DF : ℂ := 1

/-- The complete coefficient `𝒦(θ) = D_sp(θ) + D_F`. -/
noncomputable def K (θ : ℝ) : ℂ := Dsp θ + DF

/-- Boxed identity (SMQ.0c): `𝒦(θ) = e^{iθ}`. -/
theorem K_eq (θ : ℝ) : K θ = Complex.exp (θ * Complex.I) := by
  rw [K, Dsp, DF, sub_add_cancel]

/-- The full coefficient is unimodular, so it IS its own phase. -/
theorem K_unimodular (θ : ℝ) : ‖K θ‖ = 1 := by
  rw [K_eq, Complex.norm_exp]
  simp

/-- At `θ = 0` the full phase is `1`. -/
theorem K_zero : K 0 = 1 := by
  rw [K_eq]
  simp

/-- At `θ = π` the full phase is `−1`, although the internal Dirac is
unchanged. -/
theorem K_pi : K Real.pi = -1 := by
  rw [K_eq]
  exact Complex.exp_pi_mul_I

/-- No construction from the internal determinant alone can recover the
physical fermionic phase: every function of the constant internal Dirac
`D_F` is constant, while `𝒦(θ)` winds. -/
theorem internal_Dirac_not_full_phase :
    ∀ f : ℂ → ℂ, ¬∀ θ : ℝ, f DF = K θ := by
  intro f h
  have h0 := h 0
  have hpi := h Real.pi
  rw [K_zero] at h0
  rw [K_pi] at hpi
  rw [h0] at hpi
  norm_num at hpi

/-- **The internal finite Dirac does not determine the full phase**
(`cth:SMST-internal-Dirac-not-full-phase`).  In one complex dimension, with
`D_F = 1` fixed and `D_sp(θ) = e^{iθ} − 1`, the full coefficient
`𝒦(θ) = e^{iθ}` is unimodular and winds (`𝒦(0) = 1`, `𝒦(π) = −1`) while the
internal Dirac is constant; no function of `D_F` reproduces the phase of
`𝒦`. -/
theorem internal_not_full_phase_bundle :
    (∀ θ : ℝ, K θ = Complex.exp (θ * Complex.I)) ∧
      (∀ θ : ℝ, ‖K θ‖ = 1) ∧ K 0 = 1 ∧ K Real.pi = -1 ∧
      ∀ f : ℂ → ℂ, ¬∀ θ : ℝ, f DF = K θ :=
  ⟨K_eq, K_unimodular, K_zero, K_pi, internal_Dirac_not_full_phase⟩

end SMSTInternalDiracNotFullPhase

/-! ## `thm:GT-MP-supported-Schur`
Canonical support and supported Schur completion (CERT.4–CERT.8). -/

namespace GTMPSupportedSchur

open SourceCoercivityInfluence PsdBlockSchur

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]

/-- **CERT.4**: for `D = D^* ⪰ 0` the canonical support satisfies
`P_D = DD^† = D^†D` and is a Hermitian idempotent (an orthogonal
projection). -/
theorem canonicalSupport (D : Matrix p p ℂ) (hD : D.PosSemidef) :
    D * pinv hD.1 = supportProj hD.1 ∧ pinv hD.1 * D = supportProj hD.1 ∧
      (supportProj hD.1)ᴴ = supportProj hD.1 ∧
      supportProj hD.1 * supportProj hD.1 = supportProj hD.1 :=
  ⟨mul_pinv_eq_supportProj hD.1, (supportProj_eq_pinv_mul hD.1).symm,
    (supportProj_posSemidef hD.1).1, supportProj_idem hD.1⟩

/-- `P_D D = D`: the support projection fixes `D`. -/
theorem supportProj_mul_self (D : Matrix p p ℂ) (hD : D.PosSemidef) :
    supportProj hD.1 * D = D := by
  have h := congrArg Matrix.conjTranspose (mul_supportProj hD)
  rwa [Matrix.conjTranspose_mul, (supportProj_posSemidef hD.1).1.eq,
    hD.1.eq] at h

/-- `P_D` projects exactly onto `Ran D`: a vector is fixed by `P_D` iff it
lies in the range of `D`. -/
theorem supportProj_fixes_iff_mem_range (D : Matrix p p ℂ)
    (hD : D.PosSemidef) (v : p → ℂ) :
    supportProj hD.1 *ᵥ v = v ↔ ∃ u, v = D *ᵥ u := by
  constructor
  · intro h
    exact ⟨pinv hD.1 *ᵥ v, by
      rw [Matrix.mulVec_mulVec, mul_pinv_eq_supportProj hD.1, h]⟩
  · rintro ⟨u, rfl⟩
    rw [Matrix.mulVec_mulVec, supportProj_mul_self D hD]

omit [DecidableEq p] in
/-- `Ran D = (Ker D)^⊥`: a vector lies in the range of the positive `D`
exactly when it is orthogonal to the kernel of `D`. -/
theorem mem_range_iff_orth_ker (D : Matrix p p ℂ) (hD : D.PosSemidef)
    (v : p → ℂ) :
    (∃ u, v = D *ᵥ u) ↔ ∀ u, D *ᵥ u = 0 → star u ⬝ᵥ v = 0 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩ z hz
    rw [dotProduct_mulVec_hermitian hD.1, hz, star_zero, zero_dotProduct]
  · intro h
    set r := v - supportProj hD.1 *ᵥ v with hr
    have hres : D *ᵥ r = 0 := mulVec_sub_supportProj hD v
    have hPr : supportProj hD.1 *ᵥ r = 0 := by
      rw [hr, Matrix.mulVec_sub, Matrix.mulVec_mulVec, supportProj_idem,
        sub_self]
    have key : star r ⬝ᵥ (v - supportProj hD.1 *ᵥ v) = 0 := by
      rw [dotProduct_sub, h r hres, zero_sub,
        dotProduct_mulVec_hermitian (supportProj_posSemidef hD.1).1, hPr,
        star_zero, zero_dotProduct, neg_zero]
    rw [← hr] at key
    have hr0 : r = 0 := dotProduct_star_self_eq_zero.mp key
    have hfix : supportProj hD.1 *ᵥ v = v :=
      (sub_eq_zero.mp (hr.symm.trans hr0)).symm
    exact (supportProj_fixes_iff_mem_range D hD v).mp hfix

/-- `P_D` is the UNIQUE orthogonal projection onto `Ran D`: any Hermitian
idempotent with the same range equals `P_D`.  A submitted support may be
used only after this equality has been verified. -/
theorem supportProj_unique (D : Matrix p p ℂ) (hD : D.PosSemidef)
    (Q : Matrix p p ℂ) (hherm : Qᴴ = Q) (hidem : Q * Q = Q)
    (hrange : ∀ v, (∃ u, v = Q *ᵥ u) ↔ ∃ u, v = D *ᵥ u) :
    Q = supportProj hD.1 := by
  have hPQ : supportProj hD.1 * Q = Q := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec]
    exact (supportProj_fixes_iff_mem_range D hD _).mpr
      ((hrange _).mp ⟨v, rfl⟩)
  have hQP : Q * supportProj hD.1 = supportProj hD.1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec]
    obtain ⟨u, hu⟩ := (hrange (supportProj hD.1 *ᵥ v)).mpr
      ⟨pinv hD.1 *ᵥ v, by
        rw [Matrix.mulVec_mulVec, mul_pinv_eq_supportProj hD.1]⟩
    rw [hu, Matrix.mulVec_mulVec, hidem]
  calc Q = supportProj hD.1 * Q := hPQ.symm
    _ = (Qᴴ * (supportProj hD.1)ᴴ)ᴴ := by
        rw [← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = (Q * supportProj hD.1)ᴴ := by
        rw [hherm, (supportProj_posSemidef hD.1).1.eq]
    _ = supportProj hD.1 := by
        rw [hQP, (supportProj_posSemidef hD.1).1.eq]

omit [Fintype m] in
/-- The exact support incidence **CERT.5** `B(I − P_D) = 0` yields the range
condition `DD^†B^* = B^*`. -/
theorem supported_range_condition {D : Matrix p p ℂ} (hD : D.PosSemidef)
    (B : Matrix m p ℂ) (hsupp : B * (1 - supportProj hD.1) = 0) :
    D * pinv hD.1 * Bᴴ = Bᴴ := by
  have hBP : B * supportProj hD.1 = B := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hsupp
    exact hsupp.symm
  have hPBH : supportProj hD.1 * Bᴴ = Bᴴ := by
    have h := congrArg Matrix.conjTranspose hBP
    rwa [Matrix.conjTranspose_mul, (supportProj_posSemidef hD.1).1.eq] at h
  rw [mul_pinv_eq_supportProj hD.1, hPBH]

/-- **CERT.7**: under the support incidence CERT.5, the quadratic form of
`M = [[A,B],[B^*,D]]` completes the square through the supported Schur
complement `S = A − BD^†B^*` of CERT.6:
`⟨(x,y), M(x,y)⟩ = ⟨x,Sx⟩ + ⟨y + D^†B^*x, D(y + D^†B^*x)⟩`. -/
theorem supported_completion_of_square {D : Matrix p p ℂ}
    (hD : D.PosSemidef) (A : Matrix m m ℂ) (B : Matrix m p ℂ)
    (hsupp : B * (1 - supportProj hD.1) = 0) (x : m → ℂ) (y : p → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim x y)
      = star x ⬝ᵥ ((A - B * pinv hD.1 * Bᴴ) *ᵥ x)
        + star (y + pinv hD.1 *ᵥ (Bᴴ *ᵥ x))
            ⬝ᵥ (D *ᵥ (y + pinv hD.1 *ᵥ (Bᴴ *ᵥ x))) := by
  have hrange := supported_range_condition hD B hsupp
  have hcs := completion_of_square hD Bᴴ A hrange y x
  rw [Matrix.conjTranspose_conjTranspose] at hcs
  have h2 := block_form D Bᴴ A y x
  rw [Matrix.conjTranspose_conjTranspose] at h2
  rw [h2] at hcs
  rw [block_form A B D x y]
  linear_combination hcs

omit [Fintype m] in
/-- **CERT.8**: under the support incidence CERT.5,
`M ⪰ 0 ⇔ D ⪰ 0 and S ⪰ 0`. -/
theorem supported_schur_posSemidef_iff [Finite m] {D : Matrix p p ℂ}
    (hD : D.PosSemidef) {A : Matrix m m ℂ} (hA : A.IsHermitian)
    (B : Matrix m p ℂ) (hsupp : B * (1 - supportProj hD.1) = 0) :
    (fromBlocks A B Bᴴ D).PosSemidef
      ↔ D.PosSemidef ∧ (A - B * pinv hD.1 * Bᴴ).PosSemidef := by
  haveI := Fintype.ofFinite m
  have hpH : (pinv hD.1).IsHermitian := pinv_isHermitian hD.1
  have hSherm : (A - B * pinv hD.1 * Bᴴ).IsHermitian := by
    change (A - B * pinv hD.1 * Bᴴ)ᴴ = A - B * pinv hD.1 * Bᴴ
    rw [Matrix.conjTranspose_sub, hA.eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpH.eq,
      Matrix.mul_assoc]
  constructor
  · intro hM
    refine ⟨hD, ?_⟩
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hSherm, fun x => ?_⟩
    have h := hM.dotProduct_mulVec_nonneg
      (Sum.elim x (-(pinv hD.1 *ᵥ (Bᴴ *ᵥ x))))
    rw [supported_completion_of_square hD A B hsupp, neg_add_cancel,
      Matrix.mulVec_zero, dotProduct_zero, add_zero] at h
    exact h
  · rintro ⟨hDpsd, hS⟩
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨Matrix.IsHermitian.fromBlocks hA rfl hD.1, fun z => ?_⟩
    rw [← Sum.elim_comp_inl_inr z,
      supported_completion_of_square hD A B hsupp]
    exact add_nonneg (hS.dotProduct_mulVec_nonneg _)
      (hDpsd.dotProduct_mulVec_nonneg _)

/-- **Canonical support and supported Schur completion**
(`thm:GT-MP-supported-Schur`), bundled: CERT.4 (canonical support, an
orthogonal projection onto `Ran D = (Ker D)^⊥`, unique by
`supportProj_unique`), CERT.7 (supported completion of the square), and
CERT.8 (the supported Schur positivity criterion) under the support
incidence CERT.5. -/
theorem supported_schur_bundle {D : Matrix p p ℂ} (hD : D.PosSemidef)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (B : Matrix m p ℂ)
    (hsupp : B * (1 - supportProj hD.1) = 0) :
    (D * pinv hD.1 = supportProj hD.1 ∧
        pinv hD.1 * D = supportProj hD.1) ∧
      (∀ v, supportProj hD.1 *ᵥ v = v ↔ ∃ u, v = D *ᵥ u) ∧
      (∀ v, (∃ u, v = D *ᵥ u) ↔ ∀ u, D *ᵥ u = 0 → star u ⬝ᵥ v = 0) ∧
      (∀ x y, star (Sum.elim x y) ⬝ᵥ (fromBlocks A B Bᴴ D *ᵥ Sum.elim x y)
        = star x ⬝ᵥ ((A - B * pinv hD.1 * Bᴴ) *ᵥ x)
          + star (y + pinv hD.1 *ᵥ (Bᴴ *ᵥ x))
              ⬝ᵥ (D *ᵥ (y + pinv hD.1 *ᵥ (Bᴴ *ᵥ x)))) ∧
      ((fromBlocks A B Bᴴ D).PosSemidef
        ↔ D.PosSemidef ∧ (A - B * pinv hD.1 * Bᴴ).PosSemidef) :=
  ⟨⟨(canonicalSupport D hD).1, (canonicalSupport D hD).2.1⟩,
    supportProj_fixes_iff_mem_range D hD,
    mem_range_iff_orth_ker D hD,
    supported_completion_of_square hD A B hsupp,
    supported_schur_posSemidef_iff hD hA B hsupp⟩

end GTMPSupportedSchur

end NCG
