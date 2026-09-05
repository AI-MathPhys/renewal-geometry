/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Medium-tier exact records, batch 03 (Gran-Tensor manuscript)

Exact full renderings for the MEDIUM batch `med_03`:

* `thm:GT-effective-action` (`gt_effective_action_full`): the effective head
  action `S_P(L) = A - BC⁻¹B* ⪰ 0`, the boxed completion of the square, the
  attained tail infimum, the boxed kernel description, and the boxed
  Moore–Penrose influence preservation `E*L†E = E*S_P(L)†E` for
  `Ran E ⊆ Ran S_P(L)` — stated for the genuine (unique) Moore–Penrose
  pseudoinverses, whose existence is proved via `hermPinv`.

* `cor:GT-boundary-relaxation-dispersion`
  (`gt_boundary_relaxation_dispersion_full`): with `K = D_T C⁻¹ D_T*`,
  the boxed BC.6 discrepancy `G_naive - G_{/T} = E*K(I+K)⁻¹E ⪰ 0` in the
  Loewner order, the exact vanishing criterion `K^{1/2}E = 0`, the boxed BC.7
  sandwich `S + (1+d²/γ)⁻¹E*E ⪯ G_{/T} ⪯ S + E*E`, and survival of interior
  floors.

Further records of the batch appear below in file order; see the individual
docstrings.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace MediumExact03

/-! ## Small dot-product and Loewner-order mini-library -/

/-- Dot product splits across a `Sum.elim` block vector. -/
theorem sum_elim_dotProduct {P Q : Type*} [Fintype P] [Fintype Q]
    (u x : P → ℂ) (v y : Q → ℂ) :
    Sum.elim u v ⬝ᵥ Sum.elim x y = u ⬝ᵥ x + v ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- `star` distributes over a `Sum.elim` block vector. -/
theorem star_sum_elim {P Q : Type*} (p : P → ℂ) (q : Q → ℂ) :
    star (Sum.elim p q) = Sum.elim (star p) (star q) := by
  funext i
  cases i <;> rfl

/-- The hermitian-adjoint move for the sesquilinear pairing. -/
theorem star_mulVec_dotProduct {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (Mᴴ *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (M *ᵥ y) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]

/-- Loewner monotonicity of two-sided compression by a rectangular matrix. -/
theorem conj_le_conj {n m : Type*} [Fintype n] [Fintype m]
    {X Y : Matrix n n ℂ} (h : X ≤ Y) (E : Matrix n m ℂ) :
    Eᴴ * X * E ≤ Eᴴ * Y * E := by
  rw [Matrix.le_iff] at h ⊢
  have := h.conjTranspose_mul_mul_same E
  have hdist : Eᴴ * (Y - X) * E = Eᴴ * Y * E - Eᴴ * X * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [hdist] at this

/-- Loewner monotonicity of the reversed compression `B X Bᴴ`. -/
theorem conj_le_conj' {n m : Type*} [Fintype n] [Fintype m]
    {X Y : Matrix n n ℂ} (h : X ≤ Y) (B : Matrix m n ℂ) :
    B * X * Bᴴ ≤ B * Y * Bᴴ := by
  rw [Matrix.le_iff] at h ⊢
  have := h.mul_mul_conjTranspose_same B
  have hdist : B * (Y - X) * Bᴴ = B * Y * Bᴴ - B * X * Bᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [hdist] at this

/-- A real-scalar Loewner floor `0 < γ`, `γ•1 ≤ C` forces positive definiteness. -/
theorem posDef_of_smul_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} {γ : ℝ} (hγ : 0 < γ) (h : γ • (1 : Matrix n n ℂ) ≤ C) :
    C.PosDef := by
  have hsm : (γ • (1 : Matrix n n ℂ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => by
      simpa using (Complex.ofReal_pos).mpr hγ
  have hdiff : (C - γ • (1 : Matrix n n ℂ)).PosSemidef := Matrix.le_iff.mp h
  have := hsm.add_posSemidef hdiff
  simpa using this

/-- Commutation passes to the (nonsingular) inverse. -/
theorem commute_nonsing_inv {n : Type*} [Fintype n] [DecidableEq n]
    {X M : Matrix n n ℂ} [Invertible M] (h : X * M = M * X) :
    X * M⁻¹ = M⁻¹ * X := by
  have h1 : M⁻¹ * (X * M) * M⁻¹ = M⁻¹ * (M * X) * M⁻¹ := by rw [h]
  calc X * M⁻¹ = M⁻¹ * (M * X) * M⁻¹ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
          Matrix.one_mul]
    _ = M⁻¹ * (X * M) * M⁻¹ := h1.symm
    _ = M⁻¹ * X := by
        rw [Matrix.mul_assoc M⁻¹ X M, ← Matrix.mul_assoc (M⁻¹ * X) M M⁻¹,
          Matrix.mul_assoc M⁻¹ X M, ← Matrix.mul_assoc X M M⁻¹,
          Matrix.mul_inv_of_invertible, Matrix.mul_one]

/-- Scalar floor inversion: `M ≻ 0`, `γ•1 ≤ M` gives `M⁻¹ ≤ γ⁻¹•1`. -/
theorem inv_le_smul_one_of_smul_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {γ : ℝ} (hγ : 0 < γ)
    (h : γ • (1 : Matrix n n ℂ) ≤ M) :
    M⁻¹ ≤ γ⁻¹ • (1 : Matrix n n ℂ) := by
  have hM : M.PosDef := posDef_of_smul_one_le hγ h
  have hRu : IsUnit (CFC.sqrt M) := NCG.sqrt_isUnit hM
  haveI := hRu.invertible
  set R := (CFC.sqrt M)⁻¹ with hR
  have hRH : Rᴴ = R := NCG.sqrt_inv_isHermitian M
  have hRR : R * R = M⁻¹ := NCG.sqrt_inv_mul_sqrt_inv hM
  have hRMR : R * M * R = 1 := by
    have hMs : M = CFC.sqrt M * CFC.sqrt M := (NCG.sqrt_mul_self_eq M hM.posSemidef).symm
    rw [hMs, hR, ← Matrix.mul_assoc, Matrix.mul_assoc _ (CFC.sqrt M) (CFC.sqrt M),
      ← Matrix.mul_assoc (CFC.sqrt M)⁻¹ (CFC.sqrt M) (CFC.sqrt M),
      Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hdiff : (M - γ • (1 : Matrix n n ℂ)).PosSemidef := Matrix.le_iff.mp h
  have hconj := hdiff.conjTranspose_mul_mul_same R
  rw [hRH] at hconj
  have hval : R * (M - γ • (1 : Matrix n n ℂ)) * R
      = 1 - γ • M⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hRMR, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hRR]
  rw [hval] at hconj
  rw [Matrix.le_iff]
  have hγinv : (0 : ℝ) ≤ γ⁻¹ := (inv_pos.mpr hγ).le
  have hsmul := hconj.smul (a := γ⁻¹) hγinv
  have : γ⁻¹ • ((1 : Matrix n n ℂ) - γ • M⁻¹)
      = γ⁻¹ • (1 : Matrix n n ℂ) - M⁻¹ := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  rwa [this] at hsmul

/-- Scalar cap inversion: `M ≻ 0`, `M ≤ b•1` gives `b⁻¹•1 ≤ M⁻¹`. -/
theorem smul_one_le_inv_of_le_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {b : ℝ} (hb : 0 < b) (hM : M.PosDef)
    (h : M ≤ b • (1 : Matrix n n ℂ)) :
    b⁻¹ • (1 : Matrix n n ℂ) ≤ M⁻¹ := by
  have hRu : IsUnit (CFC.sqrt M) := NCG.sqrt_isUnit hM
  haveI := hRu.invertible
  set R := (CFC.sqrt M)⁻¹ with hR
  have hRH : Rᴴ = R := NCG.sqrt_inv_isHermitian M
  have hRR : R * R = M⁻¹ := NCG.sqrt_inv_mul_sqrt_inv hM
  have hRMR : R * M * R = 1 := by
    have hMs : M = CFC.sqrt M * CFC.sqrt M := (NCG.sqrt_mul_self_eq M hM.posSemidef).symm
    rw [hMs, hR, ← Matrix.mul_assoc, Matrix.mul_assoc _ (CFC.sqrt M) (CFC.sqrt M),
      ← Matrix.mul_assoc (CFC.sqrt M)⁻¹ (CFC.sqrt M) (CFC.sqrt M),
      Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hdiff : (b • (1 : Matrix n n ℂ) - M).PosSemidef := Matrix.le_iff.mp h
  have hconj := hdiff.conjTranspose_mul_mul_same R
  rw [hRH] at hconj
  have hval : R * (b • (1 : Matrix n n ℂ) - M) * R = b • M⁻¹ - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hRMR, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hRR]
  rw [hval] at hconj
  rw [Matrix.le_iff]
  have hbinv : (0 : ℝ) ≤ b⁻¹ := (inv_pos.mpr hb).le
  have hsmul := hconj.smul (a := b⁻¹) hbinv
  have : b⁻¹ • (b • M⁻¹ - (1 : Matrix n n ℂ))
      = M⁻¹ - b⁻¹ • (1 : Matrix n n ℂ) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  rwa [this] at hsmul

/-- The L²-operator-norm cap: `‖D‖ ≤ d` gives the Loewner cap `DDᴴ ≤ d²•1`. -/
theorem mul_conjTranspose_le_smul_one {b T : Type*} [Fintype b] [Fintype T]
    [DecidableEq b] {D : Matrix b T ℂ} {d : ℝ} (hd : ‖D‖ ≤ d) :
    D * Dᴴ ≤ (d ^ 2 : ℝ) • (1 : Matrix b b ℂ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have h1 : (D * Dᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
    have h2 : ((d ^ 2 : ℝ) • (1 : Matrix b b ℂ)).IsHermitian := by
      apply Matrix.IsHermitian.smul_real
      exact Matrix.isHermitian_one
    exact h2.sub h1
  · have hd0 : (0 : ℝ) ≤ d := (norm_nonneg D).trans hd
    have hexp : star x ⬝ᵥ (((d ^ 2 : ℝ) • (1 : Matrix b b ℂ) - D * Dᴴ) *ᵥ x)
        = (d ^ 2 : ℝ) • (star x ⬝ᵥ x) - star (Dᴴ *ᵥ x) ⬝ᵥ (Dᴴ *ᵥ x) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec, dotProduct_smul]
      congr 1
      rw [← Matrix.mulVec_mulVec, ← star_mulVec_dotProduct D x (Dᴴ *ᵥ x)]
    rw [hexp]
    -- both quadratic pieces are squared Euclidean norms
    have hxsq : star x ⬝ᵥ x
        = ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 : ℝ) : ℂ) := by
      have := inner_self_eq_norm_sq_toK (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ b)
      rw [inner_toLp_toLp] at this
      rw [dotProduct_comm] at this
      simpa using this
    have hwsq : star (Dᴴ *ᵥ x) ⬝ᵥ (Dᴴ *ᵥ x)
        = ((‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ) := by
      have := inner_self_eq_norm_sq_toK (𝕜 := ℂ)
        (WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)
      rw [inner_toLp_toLp] at this
      rw [dotProduct_comm] at this
      simpa using this
    rw [hxsq, hwsq]
    have hb : ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖
        ≤ d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ := by
      have hDH : ‖Dᴴ‖ = ‖D‖ := Matrix.l2_opNorm_conjTranspose D
      have := Matrix.l2_opNorm_mulVec Dᴴ (WithLp.toLp 2 x : EuclideanSpace ℂ b)
      calc ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖
          ≤ ‖Dᴴ‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ := this
        _ ≤ d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ := by
            rw [hDH]
            exact mul_le_mul_of_nonneg_right (hDH ▸ hd) (norm_nonneg _)
    have hreal : ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2
        ≤ d ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 := by
      have h1 := norm_nonneg (WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)
      nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ b)]
    have : ((d ^ 2 * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2
        - ‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ)
        = (d ^ 2 : ℝ) • ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ b)‖ ^ 2 : ℝ) : ℂ)
          - ((‖(WithLp.toLp 2 (Dᴴ *ᵥ x) : EuclideanSpace ℂ T)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp [Complex.real_smul]
    rw [← this]
    rw [Complex.zero_le_real]
    linarith

/-! ## The Moore–Penrose pseudoinverse of a hermitian matrix -/

/-- The four Moore–Penrose axioms. -/
structure IsMPInv {n : Type*} [Fintype n] (M G : Matrix n n ℂ) : Prop where
  mul_inv_mul : M * G * M = M
  inv_mul_inv : G * M * G = G
  herm_right : (M * G)ᴴ = M * G
  herm_left : (G * M)ᴴ = G * M

/-- The Moore–Penrose pseudoinverse is unique. -/
theorem IsMPInv.unique {n : Type*} [Fintype n] {M G H : Matrix n n ℂ}
    (hG : IsMPInv M G) (hH : IsMPInv M H) : G = H := by
  have h1 : M * G = M * H := by
    calc M * G = (M * G)ᴴ := hG.herm_right.symm
      _ = ((M * H * M) * G)ᴴ := by rw [hH.mul_inv_mul]
      _ = (M * G)ᴴ * (M * H)ᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          rw [Matrix.mul_assoc]
      _ = (M * G) * (M * H) := by rw [hG.herm_right, hH.herm_right]
      _ = (M * G * M) * H := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = M * H := by rw [hG.mul_inv_mul]
  have h2 : G * M = H * M := by
    calc G * M = (G * M)ᴴ := hG.herm_left.symm
      _ = (G * (M * H * M))ᴴ := by rw [hH.mul_inv_mul]
      _ = (H * M)ᴴ * (G * M)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          congr 1
          · rw [← Matrix.mul_assoc]
          · rw [Matrix.conjTranspose_mul]
      _ = (H * M) * (G * M) := by rw [hG.herm_left, hH.herm_left]
      _ = H * (M * G * M) := by simp only [Matrix.mul_assoc]
      _ = H * M := by rw [hG.mul_inv_mul]
  calc G = G * M * G := hG.inv_mul_inv.symm
    _ = H * M * G := by rw [h2]
    _ = H * (M * G) := by rw [Matrix.mul_assoc]
    _ = H * (M * H) := by rw [h1]
    _ = H * M * H := by rw [Matrix.mul_assoc]
    _ = H := hH.inv_mul_inv

/-- Penrose axioms conjugate-transpose. -/
theorem IsMPInv.conjTranspose {n : Type*} [Fintype n] {M G : Matrix n n ℂ}
    (h : IsMPInv M G) : IsMPInv Mᴴ Gᴴ where
  mul_inv_mul := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc] at *
    rw [h.mul_inv_mul]
  inv_mul_inv := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc] at *
    rw [h.inv_mul_inv]
  herm_right := by
    rw [← Matrix.conjTranspose_mul]
    rw [Matrix.conjTranspose_conjTranspose, h.herm_left, Matrix.conjTranspose_mul]
  herm_left := by
    rw [← Matrix.conjTranspose_mul]
    rw [Matrix.conjTranspose_conjTranspose, h.herm_right, Matrix.conjTranspose_mul]

/-- The Moore–Penrose pseudoinverse of a hermitian matrix is hermitian. -/
theorem IsMPInv.herm_of_herm {n : Type*} [Fintype n] {M G : Matrix n n ℂ}
    (hM : M.IsHermitian) (h : IsMPInv M G) : Gᴴ = G := by
  have h' := h.conjTranspose
  rw [hM.eq] at h'
  exact h'.unique h

/-- Spectral pseudoinverse of a hermitian matrix: invert the nonzero
eigenvalues on the eigenbasis (the real total inverse sends `0` to `0`). -/
noncomputable def hermPinv {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : Matrix n n ℂ :=
  (hM.eigenvectorUnitary : Matrix n n ℂ)
    * diagonal (RCLike.ofReal ∘ fun i => (hM.eigenvalues i)⁻¹)
    * star (hM.eigenvectorUnitary : Matrix n n ℂ)

/-- The spectral pseudoinverse satisfies the four Penrose axioms; in
particular every hermitian matrix has a (unique) Moore–Penrose
pseudoinverse. -/
theorem hermPinv_isMPInv {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) : IsMPInv M (hermPinv hM) := by
  set U : Matrix n n ℂ := (hM.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hM.eigenvalues) with hD
  set D' : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ fun i => (hM.eigenvalues i)⁻¹) with hD'
  have hMeq : M = U * D * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
  have hmix : ∀ X Y : Matrix n n ℂ,
      (U * X * star U) * (U * Y * star U) = U * (X * Y) * star U := by
    intro X Y
    calc (U * X * star U) * (U * Y * star U)
        = U * X * (star U * U) * Y * star U := by simp only [Matrix.mul_assoc]
      _ = U * (X * Y) * star U := by
          rw [hU1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have hDDD : D * D' * D = D := by
    rw [hD, hD', diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    congr 1
    rcases eq_or_ne (hM.eigenvalues i) 0 with h0 | h0
    · simp [h0]
    · field_simp
  have hD'D'D' : D' * D * D' = D' := by
    rw [hD, hD', diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    congr 1
    rcases eq_or_ne (hM.eigenvalues i) 0 with h0 | h0
    · simp [h0]
    · field_simp
  have hDD'herm : (D * D')ᴴ = D * D' := by
    rw [hD, hD', diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1
    funext i
    simp [Function.comp_apply, ← RCLike.ofReal_mul, star_def]
  have hD'Dherm : (D' * D)ᴴ = D' * D := by
    rw [hD, hD', diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1
    funext i
    simp [Function.comp_apply, ← RCLike.ofReal_mul, star_def]
  have hconjherm : ∀ X : Matrix n n ℂ, Xᴴ = X → (U * X * star U)ᴴ = U * X * star U := by
    intro X hX
    calc (U * X * star U)ᴴ = (star U)ᴴ * Xᴴ * Uᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = U * X * star U := by
        rw [hX]
        congr 1
        · congr 1
          exact Matrix.conjTranspose_conjTranspose U
        · rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hMeq]
    show (U * D * star U) * (U * D' * star U) * (U * D * star U) = U * D * star U
    rw [hmix, hmix, hDDD]
  · show (U * D' * star U) * (U * D * star U) * (U * D' * star U) = U * D' * star U
    conv_lhs => rw [hMeq]
    rw [hmix, hmix, hD'D'D']
  · conv_lhs => rw [hMeq]
    show ((U * D * star U) * (U * D' * star U))ᴴ = M * hermPinv hM
    rw [hmix]
    conv_rhs => rw [hMeq]
    show (U * (D * D') * star U)ᴴ = (U * D * star U) * (U * D' * star U)
    rw [hmix, hconjherm _ hDD'herm]
  · conv_lhs => rw [hMeq]
    show ((U * D' * star U) * (U * D * star U))ᴴ = hermPinv hM * M
    rw [hmix]
    conv_rhs => rw [hMeq]
    show (U * (D' * D) * star U)ᴴ = (U * D' * star U) * (U * D * star U)
    rw [hmix, hconjherm _ hD'Dherm]

end MediumExact03
end NCG
