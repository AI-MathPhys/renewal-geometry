/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact native-energy to physical-tail certificate
  (`prop:native-reader`, Einstein–Standard-Model action-closure manuscript)

Finite-dimensional linear algebra of `app:native-reader-proof`.  The
source-coordinate space is a finite-dimensional real inner-product space
`H`, the native energy form is a symmetric positive semidefinite operator
`Q` (`⟪ξ, Q ξ⟫ ≥ 0`), the weighted high-frequency coefficient map
`𝖳 = 𝖳_{h,K,m}` is a linear map `H →ₗ (ι → F)` into block coefficients
indexed by the retained high modes `ι`, and the weighted block-`ℓ¹`
functional is `weightedTail w v = Σ_ℓ w_ℓ ‖v_ℓ‖` with the positive
weights `w_ℓ = (1 + |ℓ|₁/K)^m`.

* `SpectralDiag.pinvSqrt`: the pseudo-inverse square root `Q^{†/2}`
  built from the finite spectral theorem (`diagOp` in the eigenbasis with
  coefficients `λ_i ↦ λ_i^{-1/2}` on the nonzero spectrum, `0` on the
  kernel); `pinvSqrt_isSymmetric`, `pinvSqrt_nonneg`,
  `Q_pinvSq_Q`, `pinvSq_Q_pinvSq` certify that `(Q^{†/2})²` satisfies
  the Penrose identities of the Moore–Penrose inverse `Q^†` and
  `Q^{†/2}` is its positive square root;
* `readerConstant`: the operator norm `‖𝖳 Q^{†/2}‖_{2→ℓ¹(w)}` of
  `eq:source-reader-constant`;
* `exists_readerConstant_iff_kernel`: a finite constant `c` with
  `τ_w(𝖳 ξ) ≤ c ⟪ξ, Q ξ⟫^{1/2}` for all `ξ` exists iff
  `𝖳 (ker Q) = 0` (`eq:source-reader-kernel`);
* `readerConstant_isLeast`: under the kernel condition the constant
  `‖𝖳 Q^{†/2}‖_{2→ℓ¹(w)}` is admissible and is the least nonnegative
  admissible constant (`eq:source-reader-constant`);
* `affine_reader_tail`: the affine reader `u = u^{soft} + 𝖱 ξ` inherits
  `eq:source-reader-tail` by the triangle inequality.

The identification of `𝖳` with the high-mode Fourier coefficients of the
affine reader `𝖱` is carried abstractly (`𝖳` is any linear coefficient
map); the block norms are those of `F`.
-/

open scoped RealInnerProductSpace

namespace RenewalGeometry
namespace NativeReader

/-! ### Weighted block-`ℓ¹` tails -/

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weighted block-`ℓ¹` tail functional `τ_w(v) = Σ_ℓ w_ℓ ‖v_ℓ‖`. -/
def weightedTail (w : ι → ℝ) (v : ι → F) : ℝ := ∑ l, w l * ‖v l‖

theorem weightedTail_nonneg {w : ι → ℝ} (hw : ∀ l, 0 ≤ w l) (v : ι → F) :
    0 ≤ weightedTail w v :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (norm_nonneg _)

theorem weightedTail_add_le {w : ι → ℝ} (hw : ∀ l, 0 ≤ w l) (u v : ι → F) :
    weightedTail w (u + v) ≤ weightedTail w u + weightedTail w v := by
  unfold weightedTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw l)

theorem weightedTail_smul (w : ι → ℝ) (r : ℝ) (v : ι → F) :
    weightedTail w (r • v) = |r| * weightedTail w v := by
  unfold weightedTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  ring

theorem weightedTail_zero (w : ι → ℝ) : weightedTail w (0 : ι → F) = 0 := by
  simp [weightedTail]

/-- Positive weights: a vanishing tail forces vanishing coefficients. -/
theorem eq_zero_of_weightedTail_le_zero {w : ι → ℝ} (hw : ∀ l, 0 < w l) (v : ι → F)
    (h : weightedTail w v ≤ 0) : v = 0 := by
  have hterm : ∀ l ∈ Finset.univ, 0 ≤ w l * ‖v l‖ :=
    fun l _ => mul_nonneg (hw l).le (norm_nonneg _)
  have hzero : ∀ l ∈ Finset.univ, w l * ‖v l‖ = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
      (le_antisymm h (Finset.sum_nonneg hterm))
    exact this
  funext l
  have := hzero l (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (hw l).ne'
  · exact norm_eq_zero.mp h1

/-! ### Diagonal operators in an orthonormal eigenbasis -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The operator `v ↦ Σ_i α_i ⟪b_i, v⟫ b_i` acting diagonally in the
orthonormal basis `b`. -/
noncomputable def diagOp {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α : Fin n → ℝ) :
    H →ₗ[ℝ] H where
  toFun v := ∑ i, (α i * ⟪b i, v⟫) • b i
  map_add' u v := by
    simp only [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [real_inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf

theorem diagOp_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α : Fin n → ℝ) (v : H) :
    diagOp b α v = ∑ i, (α i * ⟪b i, v⟫) • b i := rfl

theorem inner_diagOp {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α : Fin n → ℝ)
    (v : H) (j : Fin n) : ⟪b j, diagOp b α v⟫ = α j * ⟪b j, v⟫ := by
  rw [diagOp_apply]
  exact b.orthonormal.inner_right_fintype (fun i => α i * ⟪b i, v⟫) j

theorem inner_eq_sum_basis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (u v : H) :
    ⟪u, v⟫ = ∑ i, ⟪b i, u⟫ * ⟪b i, v⟫ := by
  rw [← b.sum_inner_mul_inner u v]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm u (b i)]

theorem norm_sq_eq_sum_basis {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (v : H) :
    ‖v‖ ^ 2 = ∑ i, ⟪b i, v⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_basis b]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inner_diagOp_right {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α : Fin n → ℝ)
    (u v : H) : ⟪u, diagOp b α v⟫ = ∑ i, α i * (⟪b i, u⟫ * ⟪b i, v⟫) := by
  rw [inner_eq_sum_basis b]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_diagOp]
  ring

theorem diagOp_isSymmetric {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α : Fin n → ℝ) :
    (diagOp b α).IsSymmetric := by
  intro u v
  rw [real_inner_comm, inner_diagOp_right, inner_diagOp_right]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagOp_comp {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (α β : Fin n → ℝ) (v : H) :
    diagOp b α (diagOp b β v) = diagOp b (fun i => α i * β i) v := by
  rw [diagOp_apply b α, diagOp_apply b (fun i => α i * β i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_diagOp]
  ring_nf

theorem diagOp_congr {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) {α β : Fin n → ℝ}
    (h : ∀ i, α i = β i) : diagOp b α = diagOp b β := by
  have : α = β := funext h
  rw [this]

theorem diagOp_one {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ H) (v : H) :
    diagOp b (fun _ => 1) v = v := by
  rw [diagOp_apply]
  simp only [one_mul]
  exact b.sum_repr' v

/-! ### The spectral pseudo-inverse square root -/

variable [FiniteDimensional ℝ H]

/-- The spectral data of a symmetric operator: eigenbasis and eigenvalues. -/
structure SpectralDiag (Q : H →ₗ[ℝ] H) where
  /-- the dimension -/
  n : ℕ
  /-- the orthonormal eigenbasis -/
  b : OrthonormalBasis (Fin n) ℝ H
  /-- the eigenvalues -/
  lam : Fin n → ℝ
  /-- `Q` acts diagonally -/
  Q_eq : ∀ v, Q v = diagOp b lam v

/-- The finite spectral theorem supplies spectral data for every
symmetric operator. -/
noncomputable def spectralDiag (Q : H →ₗ[ℝ] H) (hQ : Q.IsSymmetric) : SpectralDiag Q where
  n := Module.finrank ℝ H
  b := hQ.eigenvectorBasis rfl
  lam := hQ.eigenvalues rfl
  Q_eq v := by
    conv_lhs => rw [← (hQ.eigenvectorBasis rfl).sum_repr' v]
    rw [map_sum, diagOp_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hQ.apply_eigenvectorBasis rfl i, smul_smul, mul_comm]
    simp

namespace SpectralDiag

variable {Q : H →ₗ[ℝ] H} (D : SpectralDiag Q)

theorem lam_nonneg (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (i : Fin D.n) : 0 ≤ D.lam i := by
  have h := hpos (D.b i)
  rw [D.Q_eq, inner_diagOp, real_inner_self_eq_norm_sq, D.b.orthonormal.1 i] at h
  simpa using h

/-- The coefficients `λ_i^{-1/2}` on the nonzero spectrum, `0` on the kernel. -/
noncomputable def pinvSqrtCoeff (i : Fin D.n) : ℝ :=
  if D.lam i = 0 then 0 else (Real.sqrt (D.lam i))⁻¹

/-- The pseudo-inverse square root `Q^{†/2}`. -/
noncomputable def pinvSqrt : H →ₗ[ℝ] H := diagOp D.b D.pinvSqrtCoeff

/-- The square root `Q^{1/2}`. -/
noncomputable def sqrtOp : H →ₗ[ℝ] H := diagOp D.b (fun i => Real.sqrt (D.lam i))

theorem pinvSqrt_isSymmetric : D.pinvSqrt.IsSymmetric := diagOp_isSymmetric _ _

theorem pinvSqrt_nonneg (v : H) : 0 ≤ ⟪v, D.pinvSqrt v⟫ := by
  unfold pinvSqrt
  rw [inner_diagOp_right]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · unfold pinvSqrtCoeff
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · exact mul_self_nonneg _

theorem lam_mul_coeff_sq (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (i : Fin D.n) :
    D.lam i * (D.pinvSqrtCoeff i * D.pinvSqrtCoeff i)
      = if D.lam i = 0 then 0 else 1 := by
  unfold pinvSqrtCoeff
  split_ifs with h0
  · simp [h0]
  · have hpos' : 0 < D.lam i := lt_of_le_of_ne (D.lam_nonneg hpos i) (Ne.symm h0)
    have hs : Real.sqrt (D.lam i) * Real.sqrt (D.lam i) = D.lam i :=
      Real.mul_self_sqrt hpos'.le
    have hs0 : Real.sqrt (D.lam i) ≠ 0 := (Real.sqrt_pos.mpr hpos').ne'
    field_simp
    linarith

theorem coeff_mul_sqrt (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (i : Fin D.n) :
    D.pinvSqrtCoeff i * Real.sqrt (D.lam i) = if D.lam i = 0 then 0 else 1 := by
  unfold pinvSqrtCoeff
  split_ifs with h0
  · simp
  · have hpos' : 0 < D.lam i := lt_of_le_of_ne (D.lam_nonneg hpos i) (Ne.symm h0)
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos').ne'

/-- **Penrose identity (1)** for `Q^† = (Q^{†/2})²`: `Q Q^† Q = Q`. -/
theorem Q_pinvSq_Q (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (v : H) :
    Q (D.pinvSqrt (D.pinvSqrt (Q v))) = Q v := by
  unfold pinvSqrt
  rw [D.Q_eq, D.Q_eq, diagOp_comp, diagOp_comp, diagOp_comp]
  congr 1
  apply diagOp_congr
  intro i
  have := D.lam_mul_coeff_sq hpos i
  split_ifs at this with h0
  · simp [h0]
  · linear_combination (D.lam i) * this

/-- **Penrose identity (2)**: `Q^† Q Q^† = Q^†`. -/
theorem pinvSq_Q_pinvSq (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (v : H) :
    D.pinvSqrt (D.pinvSqrt (Q (D.pinvSqrt (D.pinvSqrt v))))
      = D.pinvSqrt (D.pinvSqrt v) := by
  unfold pinvSqrt
  rw [D.Q_eq, diagOp_comp, diagOp_comp, diagOp_comp, diagOp_comp, diagOp_comp]
  congr 1
  apply diagOp_congr
  intro i
  have := D.lam_mul_coeff_sq hpos i
  split_ifs at this with h0
  · simp [pinvSqrtCoeff, h0]
  · linear_combination (D.pinvSqrtCoeff i * D.pinvSqrtCoeff i) * this

/-- The energy of `Q^{†/2} y` is at most `‖y‖²` (it equals the squared
norm of the projection of `y` onto the range of `Q`). -/
theorem energy_pinvSqrt_le (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (y : H) :
    ⟪D.pinvSqrt y, Q (D.pinvSqrt y)⟫ ≤ ‖y‖ ^ 2 := by
  unfold pinvSqrt
  rw [D.Q_eq, diagOp_comp, inner_diagOp_right, norm_sq_eq_sum_basis D.b]
  apply Finset.sum_le_sum
  intro i _
  rw [inner_diagOp]
  have hc := D.lam_mul_coeff_sq hpos i
  calc D.lam i * D.pinvSqrtCoeff i * (D.pinvSqrtCoeff i * ⟪D.b i, y⟫ * ⟪D.b i, y⟫)
      = (D.lam i * (D.pinvSqrtCoeff i * D.pinvSqrtCoeff i)) * ⟪D.b i, y⟫ ^ 2 := by ring
    _ ≤ 1 * ⟪D.b i, y⟫ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [hc]
        split_ifs <;> norm_num
    _ = ⟪D.b i, y⟫ ^ 2 := one_mul _

/-- `‖Q^{1/2} ξ‖² = ⟪ξ, Q ξ⟫`. -/
theorem norm_sq_sqrtOp (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (ξ : H) :
    ‖D.sqrtOp ξ‖ ^ 2 = ⟪ξ, Q ξ⟫ := by
  unfold sqrtOp
  rw [norm_sq_eq_sum_basis D.b, D.Q_eq, inner_diagOp_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_diagOp, mul_pow, Real.sq_sqrt (D.lam_nonneg hpos i)]
  ring

/-- `ξ - Q^{†/2} Q^{1/2} ξ` lies in the kernel of `Q`. -/
theorem Q_sub_pinvSqrt_sqrtOp (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (ξ : H) :
    Q (ξ - D.pinvSqrt (D.sqrtOp ξ)) = 0 := by
  unfold pinvSqrt sqrtOp
  rw [map_sub, D.Q_eq, D.Q_eq, diagOp_comp, diagOp_comp, sub_eq_zero]
  congr 1
  apply diagOp_congr
  intro i
  have := D.coeff_mul_sqrt hpos i
  split_ifs at this with h0
  · rw [h0]; ring
  · rw [mul_assoc, this, mul_one]

end SpectralDiag

/-! ### The reader constant -/

variable (w : ι → ℝ) (Q : H →ₗ[ℝ] H) (T : H →ₗ[ℝ] (ι → F))

/-- A constant `c` is admissible when `τ_w(𝖳 ξ) ≤ c ⟪ξ, Q ξ⟫^{1/2}` for all `ξ`
(the source-coordinate part of `eq:source-reader-tail`). -/
def IsReaderConstant (c : ℝ) : Prop :=
  ∀ ξ, weightedTail w (T ξ) ≤ c * Real.sqrt ⟪ξ, Q ξ⟫

/-- The kernel condition `𝖳 (ker Q) = 0` of `eq:source-reader-kernel`. -/
def KernelCondition : Prop := ∀ ξ, Q ξ = 0 → T ξ = 0

/-- The operator norm `‖𝖳 S‖_{2→ℓ¹(w)} = sup_{‖y‖≤1} τ_w(𝖳 S y)`. -/
noncomputable def opNormTail (S : H →ₗ[ℝ] H) : ℝ :=
  sSup ((fun y => weightedTail w (T (S y))) '' Metric.closedBall (0:H) 1)

/-- **`eq:source-reader-constant`**: the constant `‖𝖳 Q^{†/2}‖_{2→ℓ¹(w)}`. -/
noncomputable def readerConstant (hQ : Q.IsSymmetric) : ℝ :=
  opNormTail w T (spectralDiag Q hQ).pinvSqrt

variable {w Q T}

/-- A crude bound on the tail of a linear map. -/
theorem weightedTail_linear_le (hw : ∀ l, 0 ≤ w l) (S : H →ₗ[ℝ] H) :
    ∃ C, ∀ y, weightedTail w (T (S y)) ≤ C * ‖y‖ := by
  refine ⟨∑ l, w l * ‖LinearMap.toContinuousLinearMap
    ((LinearMap.proj l) ∘ₗ T ∘ₗ S)‖, fun y => ?_⟩
  unfold weightedTail
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hw l)
  have := ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap ((LinearMap.proj l) ∘ₗ T ∘ₗ S)) y
  simpa using this

theorem opNormTail_bddAbove (hw : ∀ l, 0 ≤ w l) (S : H →ₗ[ℝ] H) :
    BddAbove ((fun y => weightedTail w (T (S y))) '' Metric.closedBall (0:H) 1) := by
  obtain ⟨C, hC⟩ := weightedTail_linear_le (T := T) hw S
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  calc weightedTail w (T (S y)) ≤ C * ‖y‖ := hC y
    _ ≤ max C 0 * 1 := by
        apply mul_le_mul (le_max_left _ _) hy (norm_nonneg _) (le_max_right _ _)
    _ = max C 0 := mul_one _

theorem opNormTail_nonneg (hw : ∀ l, 0 ≤ w l) (S : H →ₗ[ℝ] H) :
    0 ≤ opNormTail w T S := by
  unfold opNormTail
  apply le_csSup_of_le (opNormTail_bddAbove hw S) ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  simp [weightedTail_zero]

/-- Homogeneity: `τ_w(𝖳 S y) ≤ ‖𝖳 S‖_{2→ℓ¹(w)} ‖y‖`. -/
theorem weightedTail_le_opNormTail (hw : ∀ l, 0 ≤ w l) (S : H →ₗ[ℝ] H) (y : H) :
    weightedTail w (T (S y)) ≤ opNormTail w T S * ‖y‖ := by
  by_cases hy : y = 0
  · subst hy
    simp [weightedTail_zero]
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set u := ‖y‖⁻¹ • y with hu
    have hu1 : u ∈ Metric.closedBall (0:H) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hn.ne']
    have hle : weightedTail w (T (S u)) ≤ opNormTail w T S :=
      le_csSup (opNormTail_bddAbove hw S) ⟨u, hu1, rfl⟩
    have hyu : y = ‖y‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc weightedTail w (T (S y)) = weightedTail w (T (S (‖y‖ • u))) := by rw [← hyu]
      _ = weightedTail w (‖y‖ • T (S u)) := by rw [map_smul, map_smul]
      _ = ‖y‖ * weightedTail w (T (S u)) := by
          rw [weightedTail_smul, abs_of_pos hn]
      _ ≤ ‖y‖ * opNormTail w T S := mul_le_mul_of_nonneg_left hle hn.le
      _ = opNormTail w T S * ‖y‖ := mul_comm _ _

/-- **Necessity** (`app:native-reader-proof`): kernel vectors have zero
energy, so an admissible constant forces `𝖳 (ker Q) = 0`. -/
theorem kernelCondition_of_isReaderConstant (hw : ∀ l, 0 < w l) {c : ℝ}
    (hc : IsReaderConstant w Q T c) : KernelCondition Q T := by
  intro ξ hξ
  have h := hc ξ
  rw [hξ, inner_zero_right, Real.sqrt_zero, mul_zero] at h
  exact eq_zero_of_weightedTail_le_zero hw _ h

/-- **Sufficiency with the explicit constant**: under the kernel condition
the constant `‖𝖳 Q^{†/2}‖_{2→ℓ¹(w)}` is admissible. -/
theorem isReaderConstant_readerConstant (hw : ∀ l, 0 ≤ w l) (hQ : Q.IsSymmetric)
    (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (hker : KernelCondition Q T) :
    IsReaderConstant w Q T (readerConstant w Q T hQ) := by
  intro ξ
  set D := spectralDiag Q hQ
  set y := D.sqrtOp ξ
  have hker' : T (ξ - D.pinvSqrt y) = 0 := hker _ (D.Q_sub_pinvSqrt_sqrtOp hpos ξ)
  have hT : T ξ = T (D.pinvSqrt y) := by
    rw [map_sub, sub_eq_zero] at hker'
    exact hker'
  have hnorm : ‖y‖ = Real.sqrt ⟪ξ, Q ξ⟫ := by
    rw [← D.norm_sq_sqrtOp hpos ξ, Real.sqrt_sq (norm_nonneg _)]
  rw [hT, ← hnorm]
  exact weightedTail_le_opNormTail hw D.pinvSqrt y

/-- **`prop:native-reader`, the existence criterion**: a finite constant
`c_{h,K,m}` with `τ_w(𝖳 ξ) ≤ c ⟪ξ, Q ξ⟫^{1/2}` for all `ξ` exists if and
only if `𝖳 (ker Q) = 0` (`eq:source-reader-kernel`). -/
theorem exists_readerConstant_iff_kernel (hw : ∀ l, 0 < w l) (hQ : Q.IsSymmetric)
    (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) :
    (∃ c, IsReaderConstant w Q T c) ↔ KernelCondition Q T := by
  constructor
  · rintro ⟨c, hc⟩
    exact kernelCondition_of_isReaderConstant hw hc
  · intro hker
    exact ⟨_, isReaderConstant_readerConstant (fun l => (hw l).le) hQ hpos hker⟩

/-- **`eq:source-reader-constant`, optimality**: under the kernel
condition, `‖𝖳 Q^{†/2}‖_{2→ℓ¹(w)}` is admissible and is the least
nonnegative admissible constant. -/
theorem readerConstant_isLeast (hw : ∀ l, 0 ≤ w l) (hQ : Q.IsSymmetric)
    (hpos : ∀ ξ, 0 ≤ ⟪ξ, Q ξ⟫) (hker : KernelCondition Q T) :
    IsReaderConstant w Q T (readerConstant w Q T hQ) ∧
      ∀ c, 0 ≤ c → IsReaderConstant w Q T c → readerConstant w Q T hQ ≤ c := by
  refine ⟨isReaderConstant_readerConstant hw hQ hpos hker, ?_⟩
  intro c hc0 hc
  set D := spectralDiag Q hQ with hD
  have hne : ((fun y => weightedTail w (T (D.pinvSqrt y))) ''
      Metric.closedBall (0:H) 1).Nonempty :=
    ⟨_, ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩⟩
  unfold readerConstant opNormTail
  refine csSup_le hne ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  calc weightedTail w (T (D.pinvSqrt y))
      ≤ c * Real.sqrt ⟪D.pinvSqrt y, Q (D.pinvSqrt y)⟫ := hc _
    _ ≤ c * Real.sqrt (‖y‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact Real.sqrt_le_sqrt (D.energy_pinvSqrt_le hpos y)
    _ = c * ‖y‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hy hc0
    _ = c := mul_one _

/-- **`eq:source-reader-tail`** for the affine reader: if the high-mode
coefficients of `u_h(x) = u^{soft} + 𝖱 ξ` are `u₀ + 𝖳 ξ`, then
`τ_w(u₀ + 𝖳 ξ) ≤ τ_w(u₀) + c ⟪ξ, Q ξ⟫^{1/2}` for every admissible `c`. -/
theorem affine_reader_tail (hw : ∀ l, 0 ≤ w l) {c : ℝ}
    (hc : IsReaderConstant w Q T c) (u₀ : ι → F) (ξ : H) :
    weightedTail w (u₀ + T ξ) ≤ weightedTail w u₀ + c * Real.sqrt ⟪ξ, Q ξ⟫ := by
  have h1 := weightedTail_add_le hw u₀ (T ξ)
  have h2 := hc ξ
  linarith

end NativeReader
end RenewalGeometry
