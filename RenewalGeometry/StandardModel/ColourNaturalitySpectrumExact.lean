/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.WeakNaturalitySpectrumExact

/-!
# Colour defect spectrum and the exact naturality spectrum

Covers `lem:colour-naturality-spectrum` and `prop:exact-naturality-spectrum` of the
spacetime–gauge duality manuscript (appendix `app:naturality-spectrum`).

**Coordinates.**  After the volume identification `J_C : C → Λ²C*`
(`eq:volume-infinitesimal-action`, proved in `SixNaturalityCertificateExact.lean`), the
naturality port `𝒰 = Hom(C ⊗ W₂ ⊗ W₂, Λ²C*)` is `M₃(ℂ) ⊗ (W₂ ⊗ W₂)*`.  A port vector is a
function of `((p, a), (i, j))` (target colour `p`, input colour `a`, weak inputs `i j`),
the coefficient of the Hilbert–Schmidt-orthonormal matrix unit; `M₃(ℂ)` is vectorized by
`vec M (p, a) = M p a`.

* `adMat X` is the matrix of `ad_X = [X, ·]` on `M₃(ℂ)` (`adMat_mulVec`), and
  `colourDefect = ∑_{X ∈ 𝒢_C} ad_X* ad_X` with `𝒢_C = {E₁₂, E₂₁, E₂₃, E₃₂}`;
  `colourDefect_mulVec` identifies it with the operator `colourDefectMap` on `M₃(ℂ)`.
* `colourDefect_charpoly` (**`lem:colour-naturality-spectrum`**):
  `χ_{H_C} = X (X − 2)³ (X − 3)⁴ (X − 6)`, i.e. `spec H_C = {0⁽¹⁾, 2⁽³⁾, 3⁽⁴⁾, 6⁽¹⁾}`, via the
  explicit orthogonal eigenbasis of the paper's proof (`colourEigen_eigen`, `colourEigenbasis`).
* `natDefectOp` is `∑_X R_X* R_X + ∑_Y S_Y* S_Y` for the port defect maps
  `R_X = ad_X ⊗ I₄`, `S_Y = −I₉ ⊗ L_Yᵀ` (`eq:naturality-defects`), and
  `natDefectOp_eq_tensorSum` proves `eq:naturality-tensor-sum`:
  `H_nat = H_C ⊗ I₄ + I₉ ⊗ H_W`.
* `natDefect_charpoly` (**`prop:exact-naturality-spectrum`**):
  `χ_{H_nat} = X (X−2)⁵ (X−3)⁴ (X−4)⁷ (X−5)⁸ (X−6)⁴ (X−7)⁴ (X−8)² (X−10)`;
  `natDefect_mulVec_eq_zero_iff`: the kernel is the line of `I₃ ⊗ (w₁w₂ − w₂w₁)`;
  `natDefect_eigenvalue_two`, `natDefect_eigenvalue_mem`: the first positive eigenvalue is `2`
  and every eigenvalue is `0` or a real number in `[2, 10]`;
  `natDefect_gap_lower`, `natDefect_gap_upper`: `2(I − P_det) ⪯ H_nat ⪯ 10(I − P_det)`.

The general tool is `OrthEigenbasis`: an orthogonal eigenbasis with positive squared norms
gives the characteristic polynomial, the kernel, the eigenvalue set, the kernel dimension and
Loewner bounds; `OrthEigenbasis.kroneckerSum` builds the eigenbasis of `A ⊗ I + I ⊗ B`.
-/

open Matrix Polynomial
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace NaturalitySpectrum

/-! ## Orthogonal eigenbases -/

section Eigenbasis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal eigenbasis of `H`: the columns of `P` are pairwise orthogonal with squared
norms `N i > 0`, and `H P = P diag(ev)` with real eigenvalues `ev`. -/
structure OrthEigenbasis (H : Matrix n n ℂ) where
  /-- The eigenvector matrix (eigenvectors as columns). -/
  P : Matrix n n ℂ
  /-- Squared norms of the eigenvectors. -/
  N : n → ℝ
  /-- Eigenvalues. -/
  ev : n → ℝ
  N_pos : ∀ i, 0 < N i
  orth : Pᴴ * P = diagonal (fun i => (N i : ℂ))
  eig : H * P = P * diagonal (fun i => (ev i : ℂ))

namespace OrthEigenbasis

variable {H : Matrix n n ℂ} (E : OrthEigenbasis H)

/-- The inverse of the eigenvector matrix, `diag(N)⁻¹ Pᴴ`. -/
noncomputable def Q : Matrix n n ℂ := diagonal (fun i => ((E.N i : ℂ))⁻¹) * E.Pᴴ

theorem Q_mul_P : E.Q * E.P = 1 := by
  rw [Q, Matrix.mul_assoc, E.orth, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have : (E.N i : ℂ) ≠ 0 := by exact_mod_cast (E.N_pos i).ne'
  field_simp

theorem P_mul_Q : E.P * E.Q = 1 := mul_eq_one_comm.mp E.Q_mul_P

theorem H_eq : H = E.P * diagonal (fun i => (E.ev i : ℂ)) * E.Q := by
  calc H = H * (E.P * E.Q) := by rw [E.P_mul_Q, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, E.eig]

/-- The characteristic polynomial is `∏ (X − ev i)`. -/
theorem charpoly_eq : H.charpoly = ∏ i, (X - C ((E.ev i : ℝ) : ℂ)) := by
  calc H.charpoly = (E.P * diagonal (fun i => (E.ev i : ℂ)) * E.Q).charpoly := by
        conv_lhs => rw [E.H_eq]
    _ = _ := by
      rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, E.Q_mul_P,
        Matrix.mul_one, Matrix.charpoly_diagonal]

/-- Spectral combination `P diag(f / N) Pᴴ`. -/
noncomputable def specMat (f : n → ℝ) : Matrix n n ℂ :=
  E.P * diagonal (fun i => ((f i / E.N i : ℝ) : ℂ)) * E.Pᴴ

theorem specMat_eq (f : n → ℝ) :
    E.specMat f = E.P * diagonal (fun i => ((f i : ℝ) : ℂ)) * E.Q := by
  rw [specMat, Q, ← Matrix.mul_assoc (E.P * _), Matrix.mul_assoc E.P (diagonal _) (diagonal _),
    diagonal_mul_diagonal]
  congr 3
  funext i
  push_cast
  ring

theorem H_eq_specMat : H = E.specMat E.ev := by rw [specMat_eq, ← E.H_eq]

theorem one_eq_specMat : (1 : Matrix n n ℂ) = E.specMat (fun _ => 1) := by
  rw [specMat_eq]
  simp [E.P_mul_Q]

theorem specMat_sub (f g : n → ℝ) : E.specMat (f - g) = E.specMat f - E.specMat g := by
  simp only [specMat_eq, Pi.sub_apply]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  congr 3
  funext i
  push_cast
  ring

theorem specMat_smul (r : ℝ) (f : n → ℝ) :
    E.specMat (r • f) = (r : ℂ) • E.specMat f := by
  simp only [specMat_eq, Pi.smul_apply, smul_eq_mul]
  rw [show diagonal (fun i => ((r * f i : ℝ) : ℂ)) = (r : ℂ) • diagonal (fun i => (f i : ℂ)) by
      ext i j
      by_cases h : i = j <;> simp [h],
    Matrix.mul_smul, Matrix.smul_mul]

theorem specMat_posSemidef {f : n → ℝ} (hf : ∀ i, 0 ≤ f i) : (E.specMat f).PosSemidef := by
  rw [specMat]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal ?_) E.P
  intro i
  simp only [Pi.zero_apply]
  exact Complex.zero_le_real.mpr (div_nonneg (hf i) (E.N_pos i).le)

/-- The column `i` of the eigenvector matrix. -/
def col (i : n) : n → ℂ := fun r => E.P r i

theorem mulVec_col (i : n) : H *ᵥ E.col i = (E.ev i : ℂ) • E.col i := by
  ext r
  have h : (H * E.P) r i = (E.P * diagonal (fun i => (E.ev i : ℂ))) r i := by rw [E.eig]
  rw [mul_diagonal, mul_apply] at h
  simp only [mulVec, dotProduct, col, Pi.smul_apply, smul_eq_mul]
  rw [h]
  ring

theorem P_mulVec_single (i : n) (c : ℂ) : E.P *ᵥ Pi.single i c = c • E.col i := by
  ext r
  simp [mulVec, dotProduct, col, Pi.single_apply, mul_comm]

theorem Q_mulVec_P_mulVec (w : n → ℂ) : E.Q *ᵥ (E.P *ᵥ w) = w := by
  rw [mulVec_mulVec, E.Q_mul_P, one_mulVec]

theorem P_mulVec_Q_mulVec (w : n → ℂ) : E.P *ᵥ (E.Q *ᵥ w) = w := by
  rw [mulVec_mulVec, E.P_mul_Q, one_mulVec]

theorem H_mulVec (v : n → ℂ) :
    H *ᵥ v = E.P *ᵥ (fun i => (E.ev i : ℂ) * (E.Q *ᵥ v) i) := by
  conv_lhs => rw [E.H_eq]
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i
  rw [mulVec_diagonal]

/-- **Kernel of a matrix with a simple zero eigenvalue.** -/
theorem mulVec_eq_zero_iff (i₀ : n) (h₀ : E.ev i₀ = 0) (hne : ∀ i, i ≠ i₀ → E.ev i ≠ 0)
    (v : n → ℂ) : H *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • E.col i₀ := by
  constructor
  · intro hv
    rw [E.H_mulVec] at hv
    have h2 := congrArg (E.Q *ᵥ ·) hv
    simp only [E.Q_mulVec_P_mulVec, mulVec_zero] at h2
    refine ⟨(E.Q *ᵥ v) i₀, ?_⟩
    have hc : E.Q *ᵥ v = Pi.single i₀ ((E.Q *ᵥ v) i₀) := by
      ext i
      by_cases hi : i = i₀
      · subst hi; simp
      · have := congrFun h2 i
        simp only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at this
        rw [Pi.single_eq_of_ne hi]
        exact this.resolve_left (hne i hi)
    calc v = E.P *ᵥ (E.Q *ᵥ v) := (E.P_mulVec_Q_mulVec v).symm
      _ = E.P *ᵥ Pi.single i₀ ((E.Q *ᵥ v) i₀) := by rw [← hc]
      _ = _ := E.P_mulVec_single _ _
  · rintro ⟨c, rfl⟩
    rw [mulVec_smul, E.mulVec_col, h₀]
    simp

/-- Every eigenvalue of `H` is one of the `ev i`. -/
theorem eigenvalue_mem {μ : ℂ} {v : n → ℂ} (hv : v ≠ 0) (hμ : H *ᵥ v = μ • v) :
    ∃ i, μ = E.ev i := by
  set c := E.Q *ᵥ v with hcdef
  have hc : c ≠ 0 := by
    intro h0
    apply hv
    rw [← E.P_mulVec_Q_mulVec v, ← hcdef, h0, mulVec_zero]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  refine ⟨i, ?_⟩
  rw [E.H_mulVec] at hμ
  have h2 := congrArg (E.Q *ᵥ ·) hμ
  simp only [E.Q_mulVec_P_mulVec, mulVec_smul] at h2
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [← hcdef] at this
  exact (mul_right_cancel₀ hi this).symm

/-- The dimension of the kernel is the number of zero eigenvalues. -/
theorem finrank_ker :
    Module.finrank ℂ (LinearMap.ker H.mulVecLin) = Fintype.card {i // E.ev i = 0} := by
  have hrank : H.rank = Fintype.card {i // E.ev i ≠ 0} := by
    rw [congrArg Matrix.rank E.H_eq, Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse E.P_mul_Q),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse E.P_mul_Q),
      Matrix.rank_diagonal]
    simp
  have h := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  have h2 : H.rank = Module.finrank ℂ (LinearMap.range H.mulVecLin) := rfl
  have h3 : Fintype.card {i // E.ev i ≠ 0} = Fintype.card n - Fintype.card {i // E.ev i = 0} :=
    Fintype.card_subtype_compl _
  have h4 : Fintype.card {i // E.ev i = 0} ≤ Fintype.card n := Fintype.card_subtype_le _
  omega

/-- The spectral projector onto the eigenvector `i₀`. -/
noncomputable def proj (i₀ : n) : Matrix n n ℂ := E.specMat (fun i => if i = i₀ then 1 else 0)

theorem proj_eq (i₀ : n) :
    E.proj i₀ = ((E.N i₀ : ℂ))⁻¹ • vecMulVec (E.col i₀) (star (E.col i₀)) := by
  ext r s
  rw [proj, specMat, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply, col,
    Pi.star_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i₀]
  · simp only [ite_true]
    push_cast
    ring
  · intro b _ hb
    simp [hb]
  · simp

end OrthEigenbasis

/-- The eigenbasis of a Kronecker sum `A ⊗ I + I ⊗ B`. -/
noncomputable def OrthEigenbasis.kroneckerSum {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ} (EA : OrthEigenbasis A) (EB : OrthEigenbasis B) :
    OrthEigenbasis (A ⊗ₖ (1 : Matrix m m ℂ) + (1 : Matrix n n ℂ) ⊗ₖ B) where
  P := EA.P ⊗ₖ EB.P
  N := fun p => EA.N p.1 * EB.N p.2
  ev := fun p => EA.ev p.1 + EB.ev p.2
  N_pos := fun p => mul_pos (EA.N_pos p.1) (EB.N_pos p.2)
  orth := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, EA.orth, EB.orth,
      diagonal_kronecker_diagonal]
    congr 1
    funext p
    push_cast
    rfl
  eig := by
    rw [Matrix.add_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, EA.eig, EB.eig,
      Matrix.one_mul, Matrix.one_mul]
    have h1 : (EA.P * diagonal (fun i => (EA.ev i : ℂ))) ⊗ₖ EB.P =
        (EA.P ⊗ₖ EB.P) * (diagonal (fun i => (EA.ev i : ℂ)) ⊗ₖ (1 : Matrix m m ℂ)) := by
      rw [← mul_kronecker_mul, Matrix.mul_one]
    have h2 : EA.P ⊗ₖ (EB.P * diagonal (fun i => (EB.ev i : ℂ))) =
        (EA.P ⊗ₖ EB.P) * ((1 : Matrix n n ℂ) ⊗ₖ diagonal (fun i => (EB.ev i : ℂ))) := by
      rw [← mul_kronecker_mul, Matrix.mul_one]
    rw [h1, h2, ← Matrix.mul_add, ← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal,
      diagonal_kronecker_diagonal, diagonal_add]
    congr 2
    funext p
    simp

end Eigenbasis


/-! ## The colour defect operator `H_C` -/

section Colour

/-- Vectorization of `M₃(ℂ)` in the (Hilbert–Schmidt orthonormal) matrix-unit basis. -/
def vec3 (M : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 × Fin 3 → ℂ := fun r => M r.1 r.2

/-- The matrix of `ad_X = [X, ·]` on `M₃(ℂ)` in the matrix-unit basis. -/
def adMat (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  X ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) - (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Xᵀ

theorem adMat_mulVec (X M : Matrix (Fin 3) (Fin 3) ℂ) :
    adMat X *ᵥ vec3 M = vec3 (X * M - M * X) := by
  ext ⟨p, a⟩
  simp only [adMat, sub_mulVec, Pi.sub_apply, vec3, Matrix.sub_apply, mul_apply]
  simp [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    Fin.sum_univ_three, vec3]
  ring

/-- The Hilbert–Schmidt adjoint of `ad_X` is `ad_{X*}`. -/
theorem adMat_conjTranspose (X : Matrix (Fin 3) (Fin 3) ℂ) : (adMat X)ᴴ = adMat Xᴴ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [adMat, conjTranspose_apply, Matrix.sub_apply, kroneckerMap_apply, one_apply,
    transpose_apply, star_sub]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2, eq_comm]

/-- The colour generators `𝒢_C = {E₁₂, E₂₁, E₂₃, E₃₂}` (`eq:six-naturality-generators`). -/
def colourGen : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![single 0 1 1, single 1 0 1, single 1 2 1, single 2 1 1]

/-- The colour defect operator `H_C = ∑_{X ∈ 𝒢_C} ad_X* ad_X` on `M₃(ℂ)`
(`eq:naturality-tensor-sum`), as a `9 × 9` matrix in the matrix-unit basis. -/
noncomputable def colourDefect : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ∑ k, (adMat (colourGen k))ᴴ * adMat (colourGen k)

/-- The colour defect operator acting on `A ∈ M₃(ℂ)`:
`A ↦ ∑_X X*[X, A] − [X, A]X*`. -/
noncomputable def colourDefectMap (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ k, ((colourGen k)ᴴ * (colourGen k * A - A * colourGen k) -
    (colourGen k * A - A * colourGen k) * (colourGen k)ᴴ)

theorem colourDefect_mulVec (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colourDefect *ᵥ vec3 A = vec3 (colourDefectMap A) := by
  simp only [colourDefect, colourDefectMap, sum_mulVec, ← mulVec_mulVec, adMat_mulVec,
    adMat_conjTranspose]
  ext r
  simp [vec3, Matrix.sum_apply]

theorem colourDefect_isHermitian : colourDefect.IsHermitian := by
  simp only [IsHermitian, colourDefect, conjTranspose_sum, conjTranspose_mul,
    conjTranspose_conjTranspose]

/-- Vertex degrees `(1, 2, 1)` of the three-vertex path `1 − 2 − 3`. -/
def colourDeg : Fin 3 → ℂ := ![1, 2, 1]

/-- Explicit form: `H_C(A)_{pq} = (d_p + d_q) A_{pq} − 2 δ_{pq} ∑_{r ∼ p} A_{rr}`. -/
theorem colourDefectMap_apply (A : Matrix (Fin 3) (Fin 3) ℂ) (p q : Fin 3) :
    colourDefectMap A p q = (colourDeg p + colourDeg q) * A p q -
      (if p = q then 2 * ![A 1 1, A 0 0 + A 2 2, A 1 1] p else 0) := by
  simp only [colourDefectMap, Fin.sum_univ_four, colourGen, Matrix.add_apply]
  fin_cases p <;> fin_cases q <;>
    simp [mul_apply, Fin.sum_univ_three, single_apply, colourDeg] <;> ring

/-- Diagonal eigenvectors `(1,1,1)`, `(1,0,−1)`, `(1,−2,1)` of the path Laplacian. -/
def colourDiagVec : Fin 3 → Fin 3 → ℂ := ![![1, 1, 1], ![1, 0, -1], ![1, -2, 1]]

/-- The eigenbasis of the paper's proof: `E_{ab}` (`a ≠ b`) and the three diagonal path
Laplacian eigenvectors. -/
noncomputable def colourEigen (c : Fin 3 × Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  if c.1 = c.2 then diagonal (colourDiagVec c.1) else single c.1 c.2 1

/-- Eigenvalues: `d_a + d_b` on `E_{ab}` and `0, 2, 6` on the diagonal. -/
def colourEv (c : Fin 3 × Fin 3) : ℝ :=
  if c.1 = c.2 then ![0, 2, 6] c.1 else ![1, 2, 1] c.1 + ![1, 2, 1] c.2

/-- Squared norms of the eigenvectors. -/
def colourN (c : Fin 3 × Fin 3) : ℝ := if c.1 = c.2 then ![3, 2, 6] c.1 else 1

/-- The nine eigenvector equations of `lem:colour-naturality-spectrum`. -/
theorem colourEigen_eigen (c : Fin 3 × Fin 3) :
    colourDefectMap (colourEigen c) = (colourEv c : ℂ) • colourEigen c := by
  obtain ⟨a, b⟩ := c
  ext p q
  rw [colourDefectMap_apply]
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;>
    simp [colourEigen, colourEv, colourDiagVec, colourDeg, single_apply] <;> norm_num

/-- The eigenvector matrix of `H_C`. -/
noncomputable def colourP : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  of fun r c => colourEigen c r.1 r.2

theorem colourP_orth : colourPᴴ * colourP = diagonal (fun c => (colourN c : ℂ)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [mul_apply, conjTranspose_apply, colourP, of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, diagonal_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [colourEigen, colourN, colourDiagVec, single_apply] <;> norm_num

theorem colourP_eig :
    colourDefect * colourP = colourP * diagonal (fun c => (colourEv c : ℂ)) := by
  ext r c
  have h := congrFun (colourDefect_mulVec (colourEigen c)) r
  rw [colourEigen_eigen] at h
  simp only [mulVec, dotProduct, vec3, Matrix.smul_apply, smul_eq_mul] at h
  rw [mul_diagonal, mul_apply]
  simp only [colourP, of_apply]
  rw [h, mul_comm]

/-- The explicit orthogonal eigenbasis of `H_C`. -/
noncomputable def colourEigenbasis : OrthEigenbasis colourDefect where
  P := colourP
  N := colourN
  ev := colourEv
  N_pos := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [colourN]
  orth := colourP_orth
  eig := colourP_eig

/-- **Colour defect spectrum (`lem:colour-naturality-spectrum`).**
`χ_{H_C} = X (X − 2)³ (X − 3)⁴ (X − 6)`: `spec H_C = {0⁽¹⁾, 2⁽³⁾, 3⁽⁴⁾, 6⁽¹⁾}`
(`eq:colour-naturality-spectrum`); `H_C` is Hermitian (`colourDefect_isHermitian`). -/
theorem colourDefect_charpoly :
    colourDefect.charpoly = X * (X - 2) ^ 3 * (X - 3) ^ 4 * (X - 6) := by
  rw [colourEigenbasis.charpoly_eq]
  simp [Fintype.prod_prod_type, Fin.prod_univ_three, colourEigenbasis, colourEv, map_ofNat]
  ring

theorem colourEv_nonneg (c : Fin 3 × Fin 3) : 0 ≤ colourEv c := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [colourEv] <;> norm_num

theorem colourEv_le (c : Fin 3 × Fin 3) : colourEv c ≤ 6 := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [colourEv] <;> norm_num

theorem colourEv_ge_two (c : Fin 3 × Fin 3) (hc : c ≠ (0, 0)) : 2 ≤ colourEv c := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [colourEv] at hc ⊢ <;> norm_num

theorem colourEv_eq_zero_iff (c : Fin 3 × Fin 3) : colourEv c = 0 ↔ c = (0, 0) := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [colourEv] <;> norm_num

theorem colourEigen_zero : colourEigen (0, 0) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [colourEigen, colourDiagVec, one_apply]

/-- **Kernel of `H_C`**: the scalar colour matrices. -/
theorem colourDefect_mulVec_eq_zero_iff (v : Fin 3 × Fin 3 → ℂ) :
    colourDefect *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • vec3 1 := by
  rw [colourEigenbasis.mulVec_eq_zero_iff (0, 0) ((colourEv_eq_zero_iff _).2 rfl)
    (fun i hi => fun h => hi ((colourEv_eq_zero_iff i).1 h))]
  have : colourEigenbasis.col (0, 0) = vec3 1 := by
    ext r
    simp [OrthEigenbasis.col, colourEigenbasis, colourP, vec3, colourEigen_zero]
  rw [this]

end Colour

/-! ## The weak defect operator `H_W` -/

section Weak

/-- Weak eigenvectors: `w₁w₁`, `w₂w₂` (eigenvalue 2), `w₁w₂ + w₂w₁` (eigenvalue 4) and the
alternating covector `w₁w₂ − w₂w₁` (eigenvalue 0). -/
def weakEigenvec (c r : Fin 2 × Fin 2) : ℂ :=
  if c = (0, 0) then (if r = (0, 0) then 1 else 0)
  else if c = (1, 1) then (if r = (1, 1) then 1 else 0)
  else if c = (0, 1) then (if r = (0, 1) ∨ r = (1, 0) then 1 else 0)
  else weakAlternating r

/-- Weak eigenvalues. -/
def weakEv (c : Fin 2 × Fin 2) : ℝ := if c = (1, 0) then 0 else if c = (0, 1) then 4 else 2

/-- Squared norms of the weak eigenvectors. -/
def weakN (c : Fin 2 × Fin 2) : ℝ := if c = (0, 0) ∨ c = (1, 1) then 1 else 2

/-- The eigenvector matrix of `H_W`. -/
def weakP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := of fun r c => weakEigenvec c r

theorem weakP_orth : weakPᴴ * weakP = diagonal (fun c => (weakN c : ℂ)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [mul_apply, conjTranspose_apply, weakP, of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, diagonal_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [weakEigenvec, weakN, weakAlternating] <;> norm_num

theorem weakP_eig : weakDefect * weakP = weakP * diagonal (fun c => (weakEv c : ℂ)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [mul_apply, weakP, of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    diagonal_apply, weakDefect_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [weakEigenvec, weakEv, weakAlternating, weakDefectFin4, finProdFinEquiv] <;> norm_num

/-- The explicit orthogonal eigenbasis of `H_W` (`lem:weak-naturality-spectrum`). -/
noncomputable def weakEigenbasis : OrthEigenbasis weakDefect where
  P := weakP
  N := weakN
  ev := weakEv
  N_pos := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [weakN]
  orth := weakP_orth
  eig := weakP_eig

theorem weakEv_nonneg (c : Fin 2 × Fin 2) : 0 ≤ weakEv c := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [weakEv]

theorem weakEv_le (c : Fin 2 × Fin 2) : weakEv c ≤ 4 := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [weakEv] <;> norm_num

theorem weakEv_ge_two (c : Fin 2 × Fin 2) (hc : c ≠ (1, 0)) : 2 ≤ weakEv c := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [weakEv] at hc ⊢ <;> norm_num

theorem weakEv_eq_zero_iff (c : Fin 2 × Fin 2) : weakEv c = 0 ↔ c = (1, 0) := by
  obtain ⟨a, b⟩ := c
  fin_cases a <;> fin_cases b <;> simp [weakEv]

end Weak


namespace OrthEigenbasis

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (E : OrthEigenbasis H)

theorem col_ne_zero (i : n) : E.col i ≠ 0 := by
  intro h
  have h1 : (E.Pᴴ * E.P) i i = (E.N i : ℂ) := by rw [E.orth, diagonal_apply_eq]
  have h2 : (E.Pᴴ * E.P) i i = 0 := by
    rw [mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    have : E.P r i = 0 := congrFun h r
    simp [this]
  rw [h2] at h1
  have := E.N_pos i
  have h3 : (E.N i : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h3 h1.symm

/-- **Lower Loewner bound** `a (I − P_{i₀}) ⪯ H` when every other eigenvalue is `≥ a`. -/
theorem loewner_lower (i₀ : n) (a : ℝ) (h₀ : 0 ≤ E.ev i₀) (h : ∀ i, i ≠ i₀ → a ≤ E.ev i) :
    (H - (a : ℂ) • (1 - E.proj i₀)).PosSemidef := by
  have heq : H - (a : ℂ) • (1 - E.proj i₀) =
      E.specMat (E.ev - a • ((fun _ => (1 : ℝ)) - fun i => if i = i₀ then 1 else 0)) := by
    rw [E.specMat_sub, E.specMat_smul, E.specMat_sub, ← E.H_eq_specMat, ← E.one_eq_specMat,
      proj]
  rw [heq]
  apply E.specMat_posSemidef
  intro i
  by_cases hi : i = i₀
  · subst hi; simp [h₀]
  · simp only [Pi.sub_apply, Pi.smul_apply, hi, if_false, smul_eq_mul]
    linarith [h i hi]

/-- **Upper Loewner bound** `H ⪯ b (I − P_{i₀})` when `ev i₀ = 0` and every other
eigenvalue is `≤ b`. -/
theorem loewner_upper (i₀ : n) (b : ℝ) (h₀ : E.ev i₀ = 0) (h : ∀ i, i ≠ i₀ → E.ev i ≤ b) :
    ((b : ℂ) • (1 - E.proj i₀) - H).PosSemidef := by
  have heq : (b : ℂ) • (1 - E.proj i₀) - H =
      E.specMat (b • ((fun _ => (1 : ℝ)) - fun i => if i = i₀ then 1 else 0) - E.ev) := by
    rw [E.specMat_sub, E.specMat_smul, E.specMat_sub, ← E.H_eq_specMat, ← E.one_eq_specMat,
      proj]
  rw [heq]
  apply E.specMat_posSemidef
  intro i
  by_cases hi : i = i₀
  · subst hi; simp [h₀]
  · simp only [Pi.sub_apply, Pi.smul_apply, hi, if_false, smul_eq_mul]
    linarith [h i hi]

end OrthEigenbasis

/-! ## The naturality port and `H_nat` -/

section Nat

/-- The weak ladder `L_Y = Y ⊗ I + I ⊗ Y` on `W₂ ⊗ W₂`. -/
def weakL (Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Y ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Y

/-- The weak generators `𝒢_W = {F₁₂, F₂₁}` (`eq:six-naturality-generators`). -/
def weakGen : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![weakF12, weakF21]

/-- The 36-dimensional naturality port `𝒰 ≅ M₃(ℂ) ⊗ (W₂ ⊗ W₂)*` in matrix-unit coordinates
`((p, a), (i, j))`. -/
abbrev NatPort := (Fin 3 × Fin 3) × (Fin 2 × Fin 2)

/-- The colour defect map `ℛ_X T = dρ_C^out(X) T − T dρ_C^in(X)` on the port; in the volume
basis `dρ_C^out(X) = X − (Tr X) I` (`eq:volume-infinitesimal-action`) and the trace term
vanishes for the off-diagonal generators, so `ℛ_X = ad_X ⊗ I₄`. -/
def portR (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix NatPort NatPort ℂ :=
  adMat X ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)

/-- The weak defect map `𝒮_Y T = −T dρ_W^in(Y)` on the port: `𝒮_Y = I₉ ⊗ (−L_Yᵀ)`
(precomposition acts on the covector factor by the transpose). -/
def portS (Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix NatPort NatPort ℂ :=
  (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ (-(weakL Y)ᵀ)

/-- The positive naturality defect operator
`H_nat = ∑_X ℛ_X* ℛ_X + ∑_Y 𝒮_Y* 𝒮_Y` (`eq:naturality-operator`). -/
noncomputable def natDefectOp : Matrix NatPort NatPort ℂ :=
  ∑ k, (portR (colourGen k))ᴴ * portR (colourGen k) +
    ∑ k, (portS (weakGen k))ᴴ * portS (weakGen k)

/-- The tensor-sum form `H_C ⊗ I₄ + I₉ ⊗ H_W` (`eq:naturality-tensor-sum`). -/
noncomputable def natDefect : Matrix NatPort NatPort ℂ :=
  colourDefect ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
    (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ weakDefect

theorem weakLPlus_transpose : weakLPlusᵀ = weakLMinus := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [weakLPlus, weakLMinus, weakF12, weakF21, kroneckerMap_apply, one_apply]

theorem weakLMinus_conjTranspose : weakLMinusᴴ = weakLPlus := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [weakLPlus, weakLMinus, weakF12, weakF21, kroneckerMap_apply, one_apply]

theorem weakLPlus_conjTranspose : weakLPlusᴴ = weakLMinus := by
  rw [← weakLMinus_conjTranspose, conjTranspose_conjTranspose]

/-- The dual-space weak summand `∑_Y (L_Yᵀ)* L_Yᵀ` equals `H_W = L₊L₋ + L₋L₊`. -/
theorem weak_dual_sum :
    ∑ k, ((weakL (weakGen k))ᵀ)ᴴ * (weakL (weakGen k))ᵀ = weakDefect := by
  have h0 : weakL (weakGen 0) = weakLPlus := rfl
  have h1 : weakL (weakGen 1) = weakLMinus := rfl
  have hM : weakLMinusᵀ = weakLPlus := by rw [← weakLPlus_transpose, transpose_transpose]
  rw [Fin.sum_univ_two, h0, h1, weakLPlus_transpose, hM, weakLMinus_conjTranspose,
    weakLPlus_conjTranspose, weakDefect]

theorem sum_kronecker_one {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    (∑ k ∈ s, A k) ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      ∑ k ∈ s, A k ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext r c
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem one_kronecker_sum {ι : Type*} (s : Finset ι)
    (B : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ (∑ k ∈ s, B k) =
      ∑ k ∈ s, (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ B k := by
  ext r c
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

/-- **`eq:naturality-tensor-sum`**: `H_nat = H_C ⊗ I₄ + I₉ ⊗ H_W`. -/
theorem natDefectOp_eq_tensorSum : natDefectOp = natDefect := by
  have hR : ∀ k, (portR (colourGen k))ᴴ * portR (colourGen k) =
      ((adMat (colourGen k))ᴴ * adMat (colourGen k)) ⊗ₖ
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    intro k
    rw [portR, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  have hS : ∀ k, (portS (weakGen k))ᴴ * portS (weakGen k) =
      (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) ⊗ₖ
        (((weakL (weakGen k))ᵀ)ᴴ * (weakL (weakGen k))ᵀ) := by
    intro k
    rw [portS, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      conjTranspose_neg, neg_mul_neg]
  rw [natDefectOp, natDefect, ← weak_dual_sum, colourDefect]
  simp only [hR, hS, sum_kronecker_one, one_kronecker_sum]

theorem natDefect_isHermitian : natDefect.IsHermitian := by
  rw [← natDefectOp_eq_tensorSum]
  simp only [IsHermitian, natDefectOp, conjTranspose_add, conjTranspose_sum, conjTranspose_mul,
    conjTranspose_conjTranspose]

/-- The orthogonal eigenbasis of `H_nat`: tensor products of the colour and weak
eigenbases, with eigenvalues the sums. -/
noncomputable def natEigenbasis : OrthEigenbasis natDefect :=
  colourEigenbasis.kroneckerSum weakEigenbasis

theorem natEigenbasis_ev (i : NatPort) : natEigenbasis.ev i = colourEv i.1 + weakEv i.2 := rfl

/-- **Exact naturality spectrum (`prop:exact-naturality-spectrum`).**
`χ_{H_nat} = X (X−2)⁵ (X−3)⁴ (X−4)⁷ (X−5)⁸ (X−6)⁴ (X−7)⁴ (X−8)² (X−10)`, i.e.
`spec H_nat = {0⁽¹⁾, 2⁽⁵⁾, 3⁽⁴⁾, 4⁽⁷⁾, 5⁽⁸⁾, 6⁽⁴⁾, 7⁽⁴⁾, 8⁽²⁾, 10⁽¹⁾}`
(`eq:exact-naturality-spectrum`). -/
theorem natDefect_charpoly :
    natDefect.charpoly = X * (X - 2) ^ 5 * (X - 3) ^ 4 * (X - 4) ^ 7 * (X - 5) ^ 8 *
      (X - 6) ^ 4 * (X - 7) ^ 4 * (X - 8) ^ 2 * (X - 10) := by
  rw [natEigenbasis.charpoly_eq]
  simp only [natEigenbasis_ev, Fintype.prod_prod_type, Fin.prod_univ_three, Fin.prod_univ_two]
  simp [colourEv, weakEv, map_ofNat]
  norm_num
  ring

/-- The distinguished kernel index: scalar colour matrix ⊗ alternating weak covector. -/
def natI0 : NatPort := ((0, 0), (1, 0))

/-- The kernel vector `I₃ ⊗ (w₁w₂ − w₂w₁)`. -/
def natKernelVec : NatPort → ℂ :=
  fun r => (1 : Matrix (Fin 3) (Fin 3) ℂ) r.1.1 r.1.2 * weakAlternating r.2

theorem natEigenbasis_col : natEigenbasis.col natI0 = natKernelVec := by
  ext ⟨⟨p, a⟩, w⟩
  simp only [OrthEigenbasis.col, natEigenbasis, OrthEigenbasis.kroneckerSum, kroneckerMap_apply,
    natI0, natKernelVec]
  simp [colourEigenbasis, colourP, colourEigen_zero, weakEigenbasis, weakP, weakEigenvec]

theorem natEv_eq_zero_iff (i : NatPort) : natEigenbasis.ev i = 0 ↔ i = natI0 := by
  rw [natEigenbasis_ev]
  have h1 := colourEv_nonneg i.1
  have h2 := weakEv_nonneg i.2
  constructor
  · intro h
    have e1 : colourEv i.1 = 0 := by linarith
    have e2 : weakEv i.2 = 0 := by linarith
    rw [colourEv_eq_zero_iff] at e1
    rw [weakEv_eq_zero_iff] at e2
    exact Prod.ext e1 e2
  · rintro rfl
    rw [show natI0.1 = (0, 0) from rfl, show natI0.2 = (1, 0) from rfl,
      (colourEv_eq_zero_iff _).2 rfl, (weakEv_eq_zero_iff _).2 rfl, add_zero]

theorem natEv_bounds (i : NatPort) (hi : i ≠ natI0) :
    2 ≤ natEigenbasis.ev i ∧ natEigenbasis.ev i ≤ 10 := by
  rw [natEigenbasis_ev]
  have h1 := colourEv_nonneg i.1
  have h2 := weakEv_nonneg i.2
  refine ⟨?_, by linarith [colourEv_le i.1, weakEv_le i.2]⟩
  by_cases hc : i.1 = (0, 0)
  · have hw : i.2 ≠ (1, 0) := fun hw => hi (Prod.ext hc hw)
    linarith [weakEv_ge_two i.2 hw]
  · linarith [colourEv_ge_two i.1 hc]

/-- **Kernel clause of `prop:exact-naturality-spectrum`**: the kernel of `H_nat` is the line
of the scalar colour matrix tensored with the alternating weak covector. -/
theorem natDefect_mulVec_eq_zero_iff (v : NatPort → ℂ) :
    natDefect *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • natKernelVec := by
  rw [natEigenbasis.mulVec_eq_zero_iff natI0 ((natEv_eq_zero_iff _).2 rfl)
    (fun i hi h => hi ((natEv_eq_zero_iff i).1 h)), natEigenbasis_col]

/-- The kernel of `H_nat` is one-dimensional. -/
theorem natDefect_finrank_ker : Module.finrank ℂ (LinearMap.ker natDefect.mulVecLin) = 1 := by
  rw [natEigenbasis.finrank_ker, Fintype.card_eq_one_iff]
  refine ⟨⟨natI0, (natEv_eq_zero_iff _).2 rfl⟩, ?_⟩
  rintro ⟨j, hj⟩
  exact Subtype.ext ((natEv_eq_zero_iff j).1 hj)

/-- `2` is an eigenvalue of `H_nat`. -/
theorem natDefect_eigenvalue_two :
    ∃ v : NatPort → ℂ, v ≠ 0 ∧ natDefect *ᵥ v = (2 : ℂ) • v := by
  refine ⟨natEigenbasis.col ((0, 2), (1, 0)), natEigenbasis.col_ne_zero _, ?_⟩
  rw [natEigenbasis.mulVec_col, natEigenbasis_ev]
  simp [colourEv, weakEv]
  norm_num

/-- Every eigenvalue of `H_nat` is `0` or a real number in `[2, 10]`; with
`natDefect_eigenvalue_two`, the first positive eigenvalue is exactly `2`. -/
theorem natDefect_eigenvalue_mem {μ : ℂ} {v : NatPort → ℂ} (hv : v ≠ 0)
    (hμ : natDefect *ᵥ v = μ • v) :
    μ = 0 ∨ ∃ r : ℝ, μ = r ∧ 2 ≤ r ∧ r ≤ 10 := by
  obtain ⟨i, hi⟩ := natEigenbasis.eigenvalue_mem hv hμ
  by_cases h : i = natI0
  · left
    rw [hi, (natEv_eq_zero_iff i).2 h, Complex.ofReal_zero]
  · exact Or.inr ⟨_, hi, natEv_bounds i h⟩

/-- The determinant projector `P_det`, the orthogonal projector onto `Ker H_nat`. -/
noncomputable def natDetProj : Matrix NatPort NatPort ℂ := natEigenbasis.proj natI0

theorem natDetProj_eq :
    natDetProj = (6 : ℂ)⁻¹ • vecMulVec natKernelVec (star natKernelVec) := by
  rw [natDetProj, natEigenbasis.proj_eq, natEigenbasis_col]
  congr 2
  simp [natEigenbasis, OrthEigenbasis.kroneckerSum, natI0, colourEigenbasis, colourN,
    weakEigenbasis, weakN]
  norm_num

/-- **`eq:naturality-two-sided-gap`, lower half**: `2 (I − P_det) ⪯ H_nat`. -/
theorem natDefect_gap_lower : (natDefect - (2 : ℂ) • (1 - natDetProj)).PosSemidef := by
  have := natEigenbasis.loewner_lower natI0 2 ((natEv_eq_zero_iff _).2 rfl).ge
    (fun i hi => (natEv_bounds i hi).1)
  simpa [natDetProj] using this

/-- **`eq:naturality-two-sided-gap`, upper half**: `H_nat ⪯ 10 (I − P_det)`. -/
theorem natDefect_gap_upper : ((10 : ℂ) • (1 - natDetProj) - natDefect).PosSemidef := by
  have := natEigenbasis.loewner_upper natI0 10 ((natEv_eq_zero_iff _).2 rfl)
    (fun i hi => (natEv_bounds i hi).2)
  simpa [natDetProj] using this

end Nat

end NaturalitySpectrum
end RenewalGeometry
