/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PsdBlockSchurExact
import NCG.Grand.ExactSourceSchurResidual

/-!
# Three-cylinder action-response closure

Exact encoding of `thm:GT-three-cylinder-action-response` (AR.11–AR.16) for a
finite synthesis `S` (writer bank → transfer space) and a self-adjoint slab
`0 ⪯ P ⪯ I`, with the moment cylinders `M_n = S^* P^n S`.

* `whitener` is `M_0^{†/2}` (spectral calculus), `J = S M_0^{†/2}` and
  `Π = J J^*` the range projection; `compression = M_0^{†/2} M_1 M_0^{†/2} = J^* P J`
  satisfies `0 ⪯ A_Γ ⪯ I` (AR.11, `compression_eq`, `compression_posSemidef`,
  `compression_le_one`);
* `innovation = M_0^{†/2}[M_2 - M_1 M_0^† M_1] M_0^{†/2} = J^* P (I - Π) P J ⪰ 0`
  (AR.12, `innovation_eq`, `innovation_posSemidef`);
* `innovation_eq_zero_iff` (AR.13): `𝕀 = 0 ⇔ (I - Π) P J = 0 ⇔ Π P = P Π`
  (the range of `J` reduces `P`);
* `compression_pow` (AR.14): on that branch `J^* P^m J = A_Γ^m`;
* `block_gram_posSemidef` / `block_gram_rank` (AR.15): the inversion-free block
  moment Gram is PSD and `rank 𝔹 - rank M_0 = rank 𝕀`;
* `new_writer_isometry` (AR.16): `J_new = (I - Π) P J 𝕀^{†/2}` is an isometry on
  `supp 𝕀`.
-/

open Matrix Finset NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace ThreeCylinderActionResponse

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {h d : ℕ}

/-! ### Spectral square roots of the pseudo-inverse -/

/-- `M^{†/2}`: the spectral inverse square root. -/
noncomputable def invSqrt {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    Matrix (Fin d) (Fin d) ℂ :=
  spectralFunction hM (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0)

/-- `M^{1/2}`: the spectral square root. -/
noncomputable def sqrtM {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    Matrix (Fin d) (Fin d) ℂ :=
  spectralFunction hM (fun l => if 0 < l then Real.sqrt l else 0)

theorem invSqrt_posSemidef {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    (invSqrt hM).PosSemidef :=
  spectralFunction_posSemidef hM _ fun i => by
    split_ifs with hl
    · exact (inv_pos.mpr (Real.sqrt_pos.mpr hl)).le
    · exact le_rfl

theorem invSqrt_isHermitian {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    (invSqrt hM).IsHermitian :=
  (invSqrt_posSemidef hM).1

theorem invSqrt_mul_invSqrt {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    invSqrt hM * invSqrt hM = pinv hM := by
  unfold invSqrt pinv
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs with hl
  · rw [← mul_inv, Real.mul_self_sqrt hl.le]
  · ring

theorem invSqrt_mul_sqrtM {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    invSqrt hM * sqrtM hM = supportProj hM := by
  unfold invSqrt sqrtM supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs with hl
  · exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hl).ne'
  · ring

theorem sqrtM_mul_invSqrt {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    sqrtM hM * invSqrt hM = supportProj hM := by
  unfold invSqrt sqrtM supportProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs with hl
  · exact mul_inv_cancel₀ (Real.sqrt_pos.mpr hl).ne'
  · ring

/-- `M^{†/2} M M^{†/2} = Q` (the support projection) for `M ⪰ 0`. -/
theorem invSqrt_mul_self_mul_invSqrt {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    invSqrt hM.1 * M * invSqrt hM.1 = supportProj hM.1 := by
  have hid := spectralFunction_id hM.1
  unfold invSqrt supportProj
  calc spectralFunction hM.1 (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0) * M
        * spectralFunction hM.1 (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0)
      = spectralFunction hM.1 (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0)
        * spectralFunction hM.1 id
        * spectralFunction hM.1 (fun l => if 0 < l then (Real.sqrt l)⁻¹ else 0) := by rw [hid]
    _ = spectralFunction hM.1 (fun l => (if 0 < l then (Real.sqrt l)⁻¹ else 0) * id l
          * (if 0 < l then (Real.sqrt l)⁻¹ else 0)) := by
        rw [spectralFunction_mul, spectralFunction_mul]
    _ = spectralFunction hM.1 (fun l => if 0 < l then 1 else 0) := by
        refine spectralFunction_congr hM.1 fun i => ?_
        simp only [id]
        split_ifs with hl
        · rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hl.le, inv_mul_cancel₀ hl.ne']
        · ring

/-- The support projection is dominated by the identity. -/
theorem one_sub_supportProj_posSemidef {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) - supportProj hM).PosSemidef := by
  have : (1 : Matrix (Fin d) (Fin d) ℂ) - supportProj hM
      = spectralFunction hM (fun l => 1 - if 0 < l then 1 else 0) := by
    unfold supportProj
    rw [spectralFunction_sub, spectralFunction_const]
    simp
  rw [this]
  refine spectralFunction_posSemidef hM _ fun i => ?_
  split_ifs <;> norm_num

theorem supportProj_mul_invSqrt {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    supportProj hM * invSqrt hM = invSqrt hM := by
  unfold supportProj invSqrt
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs <;> simp

theorem invSqrt_mul_supportProj {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    invSqrt hM * supportProj hM = invSqrt hM := by
  unfold supportProj invSqrt
  rw [spectralFunction_mul]
  refine spectralFunction_congr hM fun i => ?_
  split_ifs <;> simp

/-! ### The moment cylinders -/

variable (S : Matrix (Fin h) (Fin d) ℂ) (P : Matrix (Fin h) (Fin h) ℂ)

/-- The moment cylinder `M_n = S^* P^n S`. -/
def moment (n : ℕ) : Matrix (Fin d) (Fin d) ℂ := Sᴴ * P ^ n * S

theorem moment_zero : moment S P 0 = Sᴴ * S := by simp [moment]

theorem gramPsd : (Sᴴ * S).PosSemidef := posSemidef_conjTranspose_mul_self S

/-- The whitener `M_0^{†/2}`. -/
noncomputable def whitener : Matrix (Fin d) (Fin d) ℂ := invSqrt (gramPsd S).1

/-- The isometric synthesis `J = S M_0^{†/2}`. -/
noncomputable def isoSynthesis : Matrix (Fin h) (Fin d) ℂ := S * whitener S

/-- The range projection `Π = J J^*`. -/
noncomputable def rangeProj : Matrix (Fin h) (Fin h) ℂ :=
  isoSynthesis S * (isoSynthesis S)ᴴ

/-- The supported one-step compression `A_Γ = M_0^{†/2} M_1 M_0^{†/2}`. -/
noncomputable def compression : Matrix (Fin d) (Fin d) ℂ :=
  whitener S * moment S P 1 * whitener S

/-- The first temporal innovation `𝕀 = M_0^{†/2}[M_2 - M_1 M_0^† M_1] M_0^{†/2}`. -/
noncomputable def innovation : Matrix (Fin d) (Fin d) ℂ :=
  whitener S * (moment S P 2 - moment S P 1 * pinv (gramPsd S).1 * moment S P 1)
    * whitener S

theorem whitener_isHermitian : (whitener S).IsHermitian :=
  invSqrt_isHermitian _

theorem isoSynthesis_conjTranspose : (isoSynthesis S)ᴴ = whitener S * Sᴴ := by
  unfold isoSynthesis
  rw [conjTranspose_mul, (whitener_isHermitian S).eq]

/-- `J^* J = Q`, the support projection of `M_0`. -/
theorem isoSynthesis_gram :
    (isoSynthesis S)ᴴ * isoSynthesis S = supportProj (gramPsd S).1 := by
  rw [isoSynthesis_conjTranspose]
  unfold isoSynthesis whitener
  simpa only [Matrix.mul_assoc] using invSqrt_mul_self_mul_invSqrt (gramPsd S)

theorem isoSynthesis_mul_supportProj :
    isoSynthesis S * supportProj (gramPsd S).1 = isoSynthesis S := by
  unfold isoSynthesis whitener
  rw [Matrix.mul_assoc, invSqrt_mul_supportProj]

/-- **(AR.11)**: `A_Γ = J^* P J`. -/
theorem compression_eq : compression S P = (isoSynthesis S)ᴴ * P * isoSynthesis S := by
  unfold compression isoSynthesis moment
  rw [conjTranspose_mul, (whitener_isHermitian S).eq]
  simp only [pow_one, Matrix.mul_assoc]

theorem compression_posSemidef (hP : P.PosSemidef) : (compression S P).PosSemidef := by
  rw [compression_eq]
  exact hP.conjTranspose_mul_mul_same _

/-- **(AR.11)**: `A_Γ ⪯ I` when `P ⪯ I`. -/
theorem compression_le_one (hP1 : ((1 : Matrix (Fin h) (Fin h) ℂ) - P).PosSemidef) :
    ((1 : Matrix (Fin d) (Fin d) ℂ) - compression S P).PosSemidef := by
  have h1 := hP1.conjTranspose_mul_mul_same (isoSynthesis S)
  have h2 := one_sub_supportProj_posSemidef (gramPsd S).1
  have : (1 : Matrix (Fin d) (Fin d) ℂ) - compression S P
      = (isoSynthesis S)ᴴ * (1 - P) * isoSynthesis S
        + (1 - supportProj (gramPsd S).1) := by
    rw [compression_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, isoSynthesis_gram]
    abel
  rw [this]
  exact h1.add h2

/-- `Π` is a Hermitian idempotent with `Π J = J`. -/
theorem rangeProj_isHermitian : (rangeProj S).IsHermitian := by
  unfold rangeProj
  exact isHermitian_mul_conjTranspose_self _

theorem rangeProj_mul_isoSynthesis : rangeProj S * isoSynthesis S = isoSynthesis S := by
  unfold rangeProj
  rw [Matrix.mul_assoc, isoSynthesis_gram, isoSynthesis_mul_supportProj]

theorem rangeProj_idem : rangeProj S * rangeProj S = rangeProj S := by
  calc rangeProj S * rangeProj S
      = (rangeProj S * isoSynthesis S) * (isoSynthesis S)ᴴ :=
        (Matrix.mul_assoc (rangeProj S) (isoSynthesis S) (isoSynthesis S)ᴴ).symm
    _ = rangeProj S := by rw [rangeProj_mul_isoSynthesis]; rfl

/-- **(AR.12)**: `𝕀 = J^* P (I - Π) P J`. -/
theorem innovation_eq :
    innovation S P = (isoSynthesis S)ᴴ * P * (1 - rangeProj S) * P * isoSynthesis S := by
  have hRR := invSqrt_mul_invSqrt (gramPsd S).1
  have e1 : whitener S * moment S P 2 * whitener S
      = (isoSynthesis S)ᴴ * P * P * isoSynthesis S := by
    rw [isoSynthesis_conjTranspose]
    unfold moment isoSynthesis
    rw [pow_two]
    simp only [Matrix.mul_assoc]
  have e2 : whitener S * (moment S P 1 * pinv (gramPsd S).1 * moment S P 1) * whitener S
      = (isoSynthesis S)ᴴ * P * rangeProj S * P * isoSynthesis S := by
    unfold rangeProj
    rw [isoSynthesis_conjTranspose]
    unfold moment isoSynthesis whitener
    rw [← hRR, pow_one]
    simp only [Matrix.mul_assoc]
  unfold innovation
  rw [Matrix.mul_sub (whitener S), Matrix.sub_mul _ _ (whitener S), e1, e2,
    Matrix.mul_sub ((isoSynthesis S)ᴴ * P), Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul]

theorem innovation_posSemidef (hP : P.IsHermitian) : (innovation S P).PosSemidef := by
  rw [innovation_eq]
  have hH : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S).IsHermitian := by
    change ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_one, (rangeProj_isHermitian S).eq]
  have hidem : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)
      * ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S) = 1 - rangeProj S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, rangeProj_idem]
    abel
  have : (isoSynthesis S)ᴴ * P * (1 - rangeProj S) * P * isoSynthesis S
      = ((1 - rangeProj S) * P * isoSynthesis S)ᴴ
        * ((1 - rangeProj S) * P * isoSynthesis S) := by
    rw [conjTranspose_mul, conjTranspose_mul, hH.eq, hP.eq]
    calc (isoSynthesis S)ᴴ * P * (1 - rangeProj S) * P * isoSynthesis S
        = (isoSynthesis S)ᴴ * P * ((1 - rangeProj S) * (1 - rangeProj S)) * P
          * isoSynthesis S := by rw [hidem]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

/-- **(AR.13)**: `𝕀 = 0 ⇔ (I - Π) P J = 0 ⇔ Π P = P Π`. -/
theorem innovation_eq_zero_iff (hP : P.IsHermitian) :
    (innovation S P = 0 ↔ (1 - rangeProj S) * P * isoSynthesis S = 0) ∧
      ((1 - rangeProj S) * P * isoSynthesis S = 0 ↔ rangeProj S * P = P * rangeProj S) := by
  have hH : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S).IsHermitian := by
    change ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_one, (rangeProj_isHermitian S).eq]
  have hidem : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)
      * ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S) = 1 - rangeProj S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, rangeProj_idem]
    abel
  have hgram : innovation S P
      = ((1 - rangeProj S) * P * isoSynthesis S)ᴴ
        * ((1 - rangeProj S) * P * isoSynthesis S) := by
    rw [innovation_eq, conjTranspose_mul, conjTranspose_mul, hH.eq, hP.eq]
    calc (isoSynthesis S)ᴴ * P * (1 - rangeProj S) * P * isoSynthesis S
        = (isoSynthesis S)ᴴ * P * ((1 - rangeProj S) * (1 - rangeProj S)) * P
          * isoSynthesis S := by rw [hidem]
      _ = _ := by simp only [Matrix.mul_assoc]
  constructor
  · rw [hgram]
    exact conjTranspose_mul_self_eq_zero
  · constructor
    · intro h0
      -- `(I-Π) P Π = (I-Π) P J J^* = 0`, then take adjoints
      have h1 : (1 - rangeProj S) * P * rangeProj S = 0 := by
        have e : (1 - rangeProj S) * P * rangeProj S
            = ((1 - rangeProj S) * P * isoSynthesis S) * (isoSynthesis S)ᴴ :=
          (Matrix.mul_assoc ((1 - rangeProj S) * P) (isoSynthesis S)
            (isoSynthesis S)ᴴ).symm
        rw [e, h0, Matrix.zero_mul]
      have h2 : rangeProj S * P * (1 - rangeProj S) = 0 := by
        have := congrArg conjTranspose h1
        rwa [conjTranspose_mul, conjTranspose_mul, hH.eq, hP.eq, (rangeProj_isHermitian S).eq,
          conjTranspose_zero, ← Matrix.mul_assoc] at this
      have e1 : P * rangeProj S = rangeProj S * P * rangeProj S := by
        have := h1
        simp only [Matrix.sub_mul, Matrix.one_mul] at this
        exact sub_eq_zero.mp this
      have e2 : rangeProj S * P = rangeProj S * P * rangeProj S := by
        have := h2
        simp only [Matrix.mul_sub, Matrix.mul_one] at this
        exact sub_eq_zero.mp this
      exact e2.trans e1.symm
    · intro hcomm
      calc (1 - rangeProj S) * P * isoSynthesis S
          = (1 - rangeProj S) * P * (rangeProj S * isoSynthesis S) := by
            rw [rangeProj_mul_isoSynthesis]
        _ = ((1 - rangeProj S) * (P * rangeProj S)) * isoSynthesis S := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - rangeProj S) * (rangeProj S * P)) * isoSynthesis S := by rw [hcomm]
        _ = 0 := by
            rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, rangeProj_idem, sub_self,
              Matrix.zero_mul]

/-- **(AR.14)**: on the reducing branch `J^* P^{m+1} J = A_Γ^{m+1}` (at `m = 0` the
moment is the support projection `Q`, see `isoSynthesis_gram`). -/
theorem compression_pow (hcomm : rangeProj S * P = P * rangeProj S) (m : ℕ) :
    (isoSynthesis S)ᴴ * P ^ (m + 1) * isoSynthesis S = compression S P ^ (m + 1) := by
  induction m with
  | zero => rw [zero_add, pow_one, pow_one, compression_eq]
  | succ m ih =>
    rw [pow_succ (compression S P), ← ih, compression_eq]
    calc (isoSynthesis S)ᴴ * P ^ (m + 1 + 1) * isoSynthesis S
        = (isoSynthesis S)ᴴ * P ^ (m + 1) * (P * (rangeProj S * isoSynthesis S)) := by
          rw [rangeProj_mul_isoSynthesis, pow_succ]; simp only [Matrix.mul_assoc]
      _ = (isoSynthesis S)ᴴ * P ^ (m + 1) * ((P * rangeProj S) * isoSynthesis S) := by
          rw [← Matrix.mul_assoc P (rangeProj S) (isoSynthesis S)]
      _ = (isoSynthesis S)ᴴ * P ^ (m + 1) * ((rangeProj S * P) * isoSynthesis S) := by
          rw [hcomm]
      _ = _ := by unfold rangeProj; simp only [Matrix.mul_assoc]


/-! ### AR.15: the inversion-free block moment Gram -/

/-- Uniqueness of the Moore–Penrose inverse. -/
theorem pinv_unique {A X₁ X₂ : Matrix (Fin d) (Fin d) ℂ}
    (h₁₁ : A * X₁ * A = A) (h₁₂ : X₁ * A * X₁ = X₁) (h₁₃ : (A * X₁)ᴴ = A * X₁)
    (h₁₄ : (X₁ * A)ᴴ = X₁ * A)
    (h₂₁ : A * X₂ * A = A) (h₂₂ : X₂ * A * X₂ = X₂) (h₂₃ : (A * X₂)ᴴ = A * X₂)
    (h₂₄ : (X₂ * A)ᴴ = X₂ * A) : X₁ = X₂ := by
  have e1 : X₁ = X₁ * A * X₂ := by
    calc X₁ = X₁ * A * X₁ := h₁₂.symm
      _ = X₁ * (A * X₁)ᴴ := by rw [h₁₃, Matrix.mul_assoc]
      _ = X₁ * X₁ᴴ * (A * X₂ * A)ᴴ := by rw [h₂₁, conjTranspose_mul, Matrix.mul_assoc]
      _ = X₁ * (A * X₁)ᴴ * (A * X₂)ᴴ := by
        rw [conjTranspose_mul (A * X₂), conjTranspose_mul A X₁]
        simp only [Matrix.mul_assoc]
      _ = X₁ * A * X₁ * (A * X₂) := by rw [h₁₃, h₂₃]; simp only [Matrix.mul_assoc]
      _ = X₁ * A * X₂ := by rw [h₁₂, Matrix.mul_assoc]
  have e2 : X₂ = X₁ * A * X₂ := by
    calc X₂ = X₂ * A * X₂ := h₂₂.symm
      _ = (X₂ * A)ᴴ * X₂ := by rw [h₂₄]
      _ = (A * X₁ * A)ᴴ * X₂ᴴ * X₂ := by rw [h₁₁, conjTranspose_mul]
      _ = (X₁ * A)ᴴ * (X₂ * A)ᴴ * X₂ := by
        rw [conjTranspose_mul (A * X₁), conjTranspose_mul A X₁, conjTranspose_mul X₂ A,
          conjTranspose_mul X₁ A]
        simp only [Matrix.mul_assoc]
      _ = X₁ * A * (X₂ * A * X₂) := by rw [h₁₄, h₂₄]; simp only [Matrix.mul_assoc]
      _ = X₁ * A * X₂ := by rw [h₂₂]
  exact e1.trans e2.symm

/-- The spectral pseudo-inverse of `M_0` agrees with the cfc pseudo-inverse of
`ExactSourceSchurResidual`. -/
theorem pinv_eq_sourceGramPseudoinverse :
    pinv (gramPsd S).1 = sourceGramPseudoinverse S := by
  have hQ := supportProj_posSemidef (gramPsd S).1
  have hmp := mul_pinv_eq_supportProj (gramPsd S).1
  have hpm := (supportProj_eq_pinv_mul (gramPsd S).1).symm
  obtain ⟨hJ, hXJX, hJXJ, -, -, -⟩ := sourceGramPseudoinverse_projection S
  have hc := sourceGramPseudoinverse_commutes S
  refine pinv_unique (A := Sᴴ * S) ?_ (pinv_mul_self_mul_pinv _) ?_ ?_ hXJX hJXJ ?_ ?_
  · rw [Matrix.mul_assoc, hpm, mul_supportProj (gramPsd S)]
  · rw [hmp]; exact hQ.1.eq
  · rw [hpm]; exact hQ.1.eq
  · rw [conjTranspose_mul, hJ, (gramPsd S).1.eq, hc]
  · rw [conjTranspose_mul, hJ, (gramPsd S).1.eq, hc]

/-- `S Q = S` for the support projection of `M_0 = S^* S`. -/
theorem mul_supportProj_self : S * supportProj (gramPsd S).1 = S := by
  have hQ := supportProj_posSemidef (gramPsd S).1
  have h0 : (S * (1 - supportProj (gramPsd S).1))ᴴ * (S * (1 - supportProj (gramPsd S).1)) = 0 := by
    rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hQ.1.eq]
    calc (1 - supportProj (gramPsd S).1) * Sᴴ * (S * (1 - supportProj (gramPsd S).1))
        = (1 - supportProj (gramPsd S).1) * ((Sᴴ * S) * (1 - supportProj (gramPsd S).1)) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, mul_supportProj (gramPsd S), sub_self,
            Matrix.mul_zero]
  have := conjTranspose_mul_self_eq_zero.mp h0
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  exact this.symm

theorem supportProj_mul_conjTranspose : supportProj (gramPsd S).1 * Sᴴ = Sᴴ := by
  have hQ := supportProj_posSemidef (gramPsd S).1
  have := congrArg conjTranspose (mul_supportProj_self S)
  rwa [conjTranspose_mul, hQ.1.eq] at this

/-- The inversion-free block moment Gram `𝔹 = [[M_0, M_1], [M_1, M_2]]`. -/
def blockGram : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  fromBlocks (moment S P 0) (moment S P 1) (moment S P 1) (moment S P 2)

theorem moment_one_eq : moment S P 1 = Sᴴ * (P * S) := by
  unfold moment; rw [pow_one, Matrix.mul_assoc]

theorem moment_two_eq (hP : P.IsHermitian) : moment S P 2 = (P * S)ᴴ * (P * S) := by
  unfold moment; rw [pow_two, conjTranspose_mul, hP.eq]; simp only [Matrix.mul_assoc]

theorem moment_one_conjTranspose (hP : P.IsHermitian) : (moment S P 1)ᴴ = moment S P 1 := by
  unfold moment
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, pow_one, hP.eq,
    Matrix.mul_assoc]

/-- `𝔹` is the Gram matrix of the concatenated synthesis `[S | P S]`. -/
theorem blockGram_eq (hP : P.IsHermitian) :
    blockGram S P = fromBlocks (Sᴴ * S) (Sᴴ * (P * S)) ((Sᴴ * (P * S))ᴴ) ((P * S)ᴴ * (P * S)) := by
  unfold blockGram
  rw [moment_zero, ← moment_one_eq, ← moment_two_eq S P hP, moment_one_conjTranspose S P hP]

/-- **(AR.15)**: `𝔹 ⪰ 0`. -/
theorem blockGram_posSemidef (hP : P.IsHermitian) : (blockGram S P).PosSemidef := by
  rw [blockGram_eq S P hP]
  have : fromBlocks (Sᴴ * S) (Sᴴ * (P * S)) ((Sᴴ * (P * S))ᴴ) ((P * S)ᴴ * (P * S))
      = (fromCols S (P * S))ᴴ * fromCols S (P * S) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
      conjTranspose_mul, conjTranspose_conjTranspose]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

/-- The whitened innovation and the raw Schur residual have the same rank. -/
theorem innovation_rank (hP : P.IsHermitian) :
    (innovation S P).rank = (sourceSchurResidual S (P * S)).rank := by
  generalize hY : sourceSchurResidual S (P * S) = Y
  have hQS := supportProj_mul_conjTranspose S
  have hSQ := mul_supportProj_self S
  have hinn : innovation S P = whitener S * Y * whitener S := by
    unfold innovation
    rw [← hY, sourceSchurResidual, pinv_eq_sourceGramPseudoinverse, ← moment_one_eq,
      ← moment_two_eq S P hP, moment_one_conjTranspose S P hP]
  -- `Y = Q Y Q` since `Y = S^* (...) S`
  have hform : Y = Sᴴ * ((P * (P * S)) - P * S * sourceGramPseudoinverse S * (Sᴴ * (P * S))) := by
    rw [← hY, sourceSchurResidual]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP.eq, Matrix.mul_sub,
      Matrix.mul_assoc]
  have hform2 : Y = (Sᴴ * ((P * P) - P * S * sourceGramPseudoinverse S * (Sᴴ * P))) * S := by
    rw [hform]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hQY : supportProj (gramPsd S).1 * Y = Y := by
    conv_lhs => rw [hform]
    rw [← Matrix.mul_assoc, hQS, ← hform]
  have hYQ' : Y * supportProj (gramPsd S).1 = Y := by
    conv_lhs => rw [hform2]
    rw [Matrix.mul_assoc, hSQ, ← hform2]
  have hYQ : Y = supportProj (gramPsd S).1 * Y * supportProj (gramPsd S).1 := by
    rw [hQY, hYQ']
  have hYR : Y = sqrtM (gramPsd S).1 * innovation S P * sqrtM (gramPsd S).1 := by
    rw [hinn]
    unfold whitener
    calc Y = supportProj (gramPsd S).1 * Y * supportProj (gramPsd S).1 := hYQ
      _ = (sqrtM (gramPsd S).1 * invSqrt (gramPsd S).1) * Y
            * (invSqrt (gramPsd S).1 * sqrtM (gramPsd S).1) := by
          rw [sqrtM_mul_invSqrt, invSqrt_mul_sqrtM]
      _ = _ := by simp only [Matrix.mul_assoc]
  apply le_antisymm
  · rw [hinn]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · conv_lhs => rw [hYR]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- **(AR.15)**: `rank 𝔹 - rank M_0 = rank 𝕀`. -/
theorem blockGram_rank (hP : P.IsHermitian) :
    (blockGram S P).rank - (moment S P 0).rank = (innovation S P).rank := by
  rw [blockGram_eq S P hP, moment_zero, innovation_rank S P hP]
  exact sourceSchurResidual_rank_increment S (P * S)

/-! ### AR.16: the new writer -/

/-- The innovation as a Gram matrix: `𝕀 = X^* X` with `X = (I - Π) P J`. -/
theorem innovation_gram (hP : P.IsHermitian) :
    innovation S P = ((1 - rangeProj S) * P * isoSynthesis S)ᴴ
      * ((1 - rangeProj S) * P * isoSynthesis S) := by
  have hH : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S).IsHermitian := by
    change ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)ᴴ = _
    rw [conjTranspose_sub, conjTranspose_one, (rangeProj_isHermitian S).eq]
  have hidem : ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S)
      * ((1 : Matrix (Fin h) (Fin h) ℂ) - rangeProj S) = 1 - rangeProj S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, rangeProj_idem]
    abel
  rw [innovation_eq, conjTranspose_mul, conjTranspose_mul, hH.eq, hP.eq]
  calc (isoSynthesis S)ᴴ * P * (1 - rangeProj S) * P * isoSynthesis S
      = (isoSynthesis S)ᴴ * P * ((1 - rangeProj S) * (1 - rangeProj S)) * P
        * isoSynthesis S := by rw [hidem]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The new writer `J_new = (I - Π) P J 𝕀^{†/2}`. -/
noncomputable def newWriter (hP : P.IsHermitian) : Matrix (Fin h) (Fin d) ℂ :=
  (1 - rangeProj S) * P * isoSynthesis S * invSqrt (innovation_posSemidef S P hP).1

/-- **(AR.16)**: `J_new^* J_new = supp 𝕀`, i.e. `J_new` is an isometry on the
support of the innovation. -/
theorem newWriter_isometry (hP : P.IsHermitian) :
    (newWriter S P hP)ᴴ * newWriter S P hP = supportProj (innovation_posSemidef S P hP).1 := by
  unfold newWriter
  rw [conjTranspose_mul, (invSqrt_isHermitian _).eq]
  calc invSqrt (innovation_posSemidef S P hP).1 * ((1 - rangeProj S) * P * isoSynthesis S)ᴴ
        * ((1 - rangeProj S) * P * isoSynthesis S * invSqrt (innovation_posSemidef S P hP).1)
      = invSqrt (innovation_posSemidef S P hP).1
        * (((1 - rangeProj S) * P * isoSynthesis S)ᴴ * ((1 - rangeProj S) * P * isoSynthesis S))
        * invSqrt (innovation_posSemidef S P hP).1 := by simp only [Matrix.mul_assoc]
    _ = invSqrt (innovation_posSemidef S P hP).1 * innovation S P
        * invSqrt (innovation_posSemidef S P hP).1 := by rw [← innovation_gram S P hP]
    _ = _ := invSqrt_mul_self_mul_invSqrt (innovation_posSemidef S P hP)

/-- The new writer's range is orthogonal to `Ran J`: `Π J_new = 0`. -/
theorem rangeProj_mul_newWriter (hP : P.IsHermitian) : rangeProj S * newWriter S P hP = 0 := by
  unfold newWriter
  have : rangeProj S * (1 - rangeProj S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, rangeProj_idem, sub_self]
  simp only [← Matrix.mul_assoc, this, Matrix.zero_mul]

end ThreeCylinderActionResponse
end NCG
