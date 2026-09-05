/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ThreeCylinderActionResponseExact
import NCG.Grand.GRHRestoringShortExact

/-!
# Endpoint sampling versus continuous first-entry killing

Exact encoding of `thm:GT-sampled-versus-killed` (ER.15–ER.18) for a completely
assembled generator `H = [[A, B], [B^*, D]] ⪰ 0` on `Fin m ⊕ Fin p`, with `Q` the
projection onto the tail `Fin p`.

* `exp_spectralFunction`: the matrix exponential of a Hermitian matrix through the
  spectral calculus (`e^{-tH} = spectralFunction (l ↦ e^{-tl})`);
* `nonneg_of_spectralFunction_posSemidef`: the converse spectral test
  (`spectralFunction f ⪰ 0 ⇒ f ≥ 0` on the spectrum);
* `inv_le_inv_of_le` (Loewner inversion): `X ⪰ Y ≻ 0 ⇒ X⁻¹ ⪯ Y⁻¹`;
* `sampled_posSemidef` / `sampled_le_resolvent` (ER.18): with the static tail
  deficit `S = D - B^* A^† B ⪰ s I` (ER.17), `0 ⪯ Q e^{-tH} Q ⪯ (I + tS)⁻¹ ⪯ (1 + ts)⁻¹ I`;
* `taylor_data` (ER.16): `F(t) = Q e^{-tH} Q - e^{-tD}` has `F(0) = 0`, `F'(0) = 0`,
  `F''(0) = B^* B` (the `t²/2 · B^* B` leading term);
* `protocols_agree_iff` : the two protocols agree for all small `t` exactly when `B = 0`.
-/

open Matrix Asymptotics Filter Topology NCG.GeometricThresholdBank
  NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
  NCG.LocalizerExtensionFloor NCG.ThreeCylinderActionResponse NCG.GRHRestoringShort
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace SampledVersusKilled

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### The spectral exponential -/

section spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_isUnit {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    IsUnit (hH.eigenvectorUnitary : Matrix n n ℂ) :=
  ⟨⟨_, star (hH.eigenvectorUnitary : Matrix n n ℂ), Unitary.coe_mul_star_self _,
    Unitary.coe_star_mul_self _⟩, rfl⟩

theorem unitary_inv {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix n n ℂ)⁻¹ = star (hH.eigenvectorUnitary : Matrix n n ℂ) :=
  Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self _)

/-- The matrix exponential through the spectral calculus. -/
theorem exp_spectralFunction {H : Matrix n n ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    NormedSpace.exp (spectralFunction hH f) = spectralFunction hH (fun l => Real.exp (f l)) := by
  have hdiag : NormedSpace.exp ((RCLike.ofReal ∘ fun i => f (hH.eigenvalues i)) : n → ℂ)
      = RCLike.ofReal ∘ fun i => Real.exp (f (hH.eigenvalues i)) := by
    rw [Pi.exp_def]
    funext i
    change NormedSpace.exp ((f (hH.eigenvalues i) : ℝ) : ℂ)
      = ((Real.exp (f (hH.eigenvalues i)) : ℝ) : ℂ)
    rw [Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]
  unfold spectralFunction
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, ← unitary_inv hH,
    Matrix.exp_conj _ _ (unitary_isUnit hH), Matrix.exp_diagonal, hdiag]

/-- `-H` and real multiples through the spectral calculus. -/
theorem smul_eq_spectralFunction {H : Matrix n n ℂ} (hH : H.IsHermitian) (t : ℝ) :
    t • H = spectralFunction hH (fun l => t * l) := by
  rw [spectralFunction_smul]
  change _ = (t : ℂ) • spectralFunction hH id
  rw [spectralFunction_id]
  ext i j
  simp [Complex.real_smul]

/-- The converse spectral test: a positive spectral function has nonnegative values on
the spectrum. -/
theorem nonneg_of_spectralFunction_posSemidef {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (f : ℝ → ℝ) (hpos : (spectralFunction hH f).PosSemidef) (i : n) :
    0 ≤ f (hH.eigenvalues i) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have key : ∀ (v w : n → ℂ), star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hUU, vecMul_one]
  have h := hpos.dotProduct_mulVec_nonneg (U *ᵥ Pi.single i 1)
  have hval : star (U *ᵥ Pi.single i 1) ⬝ᵥ (spectralFunction hH f *ᵥ (U *ᵥ Pi.single i 1))
      = ((f (hH.eigenvalues i) : ℝ) : ℂ) := by
    unfold spectralFunction
    rw [Unitary.conjStarAlgAut_apply, ← hU, star_eq_conjTranspose, mulVec_mulVec,
      Matrix.mul_assoc _ Uᴴ U, hUU, Matrix.mul_one, ← mulVec_mulVec, key, diagonal_mulVec_single,
      dotProduct_single]
    simp
  rw [hval] at h
  exact Complex.zero_le_real.mp h

/-- Real scalar multiples of positive matrices are positive. -/
theorem smul_posSemidef_real {M : Matrix n n ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (t • M).PosSemidef := by
  have e : t • M = (t : ℂ) • M := by
    ext i j; simp [Complex.real_smul]
  rw [e]
  exact hM.smul (Complex.zero_le_real.mpr ht)

/-- The resolvent `(I + tM)⁻¹` of a positive matrix through the spectral calculus. -/
theorem resolvent_spectral {M : Matrix n n ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ((1 : Matrix n n ℂ) + t • M)⁻¹ = spectralFunction hM.1 (fun l => (1 + t * l)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  have e : (1 : Matrix n n ℂ) + t • M = spectralFunction hM.1 (fun l => 1 + t * l) := by
    rw [spectralFunction_add, spectralFunction_const, smul_eq_spectralFunction hM.1 t]
    simp
  rw [e, spectralFunction_mul]
  have : spectralFunction hM.1 (fun l => (1 + t * l)⁻¹ * (1 + t * l))
      = spectralFunction hM.1 (fun _ => 1) := by
    refine spectralFunction_congr hM.1 fun i => ?_
    have h0 := hM.eigenvalues_nonneg i
    exact inv_mul_cancel₀ (by positivity)
  rw [this, spectralFunction_const]
  simp

/-- `I + tM` is positive definite for `M ⪰ 0`, `t ≥ 0`. -/
theorem one_add_smul_posDef {M : Matrix n n ℂ} (hM : M.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ((1 : Matrix n n ℂ) + t • M).PosDef := by
  refine posDef_of_floor (γ := 1) ?_ one_pos
  have : (1 : Matrix n n ℂ) + t • M - ((1 : ℝ) : ℂ) • 1 = t • M := by simp
  rw [this]
  exact smul_posSemidef_real hM ht

end spectral

/-! ### Loewner inversion -/

section loewner

variable {p : ℕ}

theorem pinv_eq_inv {X : Matrix (Fin p) (Fin p) ℂ} (hX : X.PosDef) : pinv hX.1 = X⁻¹ :=
  (Matrix.inv_eq_left_inv (pinv_mul_self hX)).symm

theorem invSqrt_mul_sqrtM_of_posDef {Y : Matrix (Fin p) (Fin p) ℂ} (hY : Y.PosDef) :
    invSqrt hY.1 * sqrtM hY.1 = 1 := by
  rw [invSqrt_mul_sqrtM, supportProj_eq_one hY]

theorem sqrtM_mul_invSqrt_of_posDef {Y : Matrix (Fin p) (Fin p) ℂ} (hY : Y.PosDef) :
    sqrtM hY.1 * invSqrt hY.1 = 1 := by
  rw [sqrtM_mul_invSqrt, supportProj_eq_one hY]

theorem invSqrt_mul_self_mul_invSqrt_of_posDef {Y : Matrix (Fin p) (Fin p) ℂ} (hY : Y.PosDef) :
    invSqrt hY.1 * Y * invSqrt hY.1 = 1 := by
  rw [invSqrt_mul_self_mul_invSqrt hY.posSemidef, supportProj_eq_one hY]

/-- `M ⪰ I` implies `M⁻¹ ⪯ I` for a positive definite `M`. -/
theorem one_sub_inv_posSemidef {M : Matrix (Fin p) (Fin p) ℂ} (hM : M.PosDef)
    (h1 : (M - 1).PosSemidef) : ((1 : Matrix (Fin p) (Fin p) ℂ) - M⁻¹).PosSemidef := by
  have hspec : M - 1 = spectralFunction hM.1 (fun l => id l - 1) := by
    rw [spectralFunction_sub, spectralFunction_id, spectralFunction_const]
    simp
  rw [hspec] at h1
  have heig : ∀ i, 1 ≤ hM.1.eigenvalues i := fun i => by
    have := nonneg_of_spectralFunction_posSemidef hM.1 _ h1 i
    simp only [id] at this
    linarith
  rw [← pinv_eq_inv hM]
  have : (1 : Matrix (Fin p) (Fin p) ℂ) - pinv hM.1
      = spectralFunction hM.1 (fun l => 1 - if 0 < l then l⁻¹ else 0) := by
    unfold pinv
    rw [spectralFunction_sub, spectralFunction_const]
    simp
  rw [this]
  refine spectralFunction_posSemidef hM.1 _ fun i => ?_
  have h := heig i
  rw [if_pos (by linarith)]
  have : (hM.1.eigenvalues i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
  linarith

/-- **Loewner inversion**: `X ⪰ Y ≻ 0` implies `X⁻¹ ⪯ Y⁻¹`. -/
theorem inv_le_inv_of_le {X Y : Matrix (Fin p) (Fin p) ℂ} (hY : Y.PosDef) (hX : X.PosDef)
    (hXY : (X - Y).PosSemidef) : (Y⁻¹ - X⁻¹).PosSemidef := by
  set W := invSqrt hY.1 with hW
  set V := sqrtM hY.1 with hV
  have hWH : W.IsHermitian := invSqrt_isHermitian _
  have hWV : W * V = 1 := invSqrt_mul_sqrtM_of_posDef hY
  have hVW : V * W = 1 := sqrtM_mul_invSqrt_of_posDef hY
  have hWYW : W * Y * W = 1 := invSqrt_mul_self_mul_invSqrt_of_posDef hY
  have hWW : W * W = Y⁻¹ := by rw [hW, invSqrt_mul_invSqrt, pinv_eq_inv hY]
  -- `M = W X W ≻ 0` and `M ⪰ 1`
  have hWinj : Function.Injective W.mulVec := by
    intro a b hab
    have := congrArg (fun v => V *ᵥ v) hab
    simpa [mulVec_mulVec, hVW] using this
  have hM : (W * X * W).PosDef := by
    have := hX.conjTranspose_mul_mul_same hWinj
    rwa [hWH.eq] at this
  have hM1 : (W * X * W - 1).PosSemidef := by
    have := hXY.conjTranspose_mul_mul_same W
    rw [hWH.eq, Matrix.mul_sub, Matrix.sub_mul, hWYW] at this
    exact this
  have hMinv := one_sub_inv_posSemidef hM hM1
  -- `X⁻¹ = W M⁻¹ W`
  have hXinv : X⁻¹ = W * (W * X * W)⁻¹ * W := by
    apply Matrix.inv_eq_left_inv
    have hMM : (W * X * W)⁻¹ * (W * X * W) = 1 :=
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit)
    calc W * (W * X * W)⁻¹ * W * X
        = W * (W * X * W)⁻¹ * (W * X * (W * V)) := by
          rw [hWV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = W * ((W * X * W)⁻¹ * (W * X * W)) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMM, Matrix.mul_one, hWV]
  have e : Y⁻¹ - X⁻¹ = W * (1 - (W * X * W)⁻¹) * W := by
    rw [hXinv, ← hWW, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [e]
  have := hMinv.conjTranspose_mul_mul_same W
  rwa [hWH.eq] at this

end loewner

/-! ### The assembled generator and the sampled slab -/

section generator

variable {m p : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
  (D : Matrix (Fin p) (Fin p) ℂ)

/-- **(ER.15)**: the completely assembled generator `H = [[A, B], [B^*, D]]`. -/
def generator : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ := fromBlocks A B Bᴴ D

/-- The endpoint-sampled slab `Q e^{-tH} Q` (as the tail block). -/
noncomputable def sampled (t : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  (NormedSpace.exp (t • (-generator A B D))).toBlocks₂₂

/-- The continuously killed slab `e^{-tD}`. -/
noncomputable def killed (t : ℝ) : Matrix (Fin p) (Fin p) ℂ := NormedSpace.exp (t • (-D))

/-- **(ER.17)**: the canonical static tail deficit `S = D - B^* A^† B`. -/
noncomputable def tailDeficit (hA : A.IsHermitian) : Matrix (Fin p) (Fin p) ℂ :=
  D - Bᴴ * pinv hA * B

variable {A B D}

theorem generator_head (hH : (generator A B D).PosSemidef) : A.PosSemidef :=
  posSemidef_left_of_fromBlocks hH

/-- The tail block of a positive matrix is positive. -/
theorem posSemidef_toBlocks₂₂ {M : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ}
    (hM : M.PosSemidef) : M.toBlocks₂₂.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun y => ?_⟩
  · have := hM.1
    rw [← fromBlocks_toBlocks M] at this
    exact (isHermitian_fromBlocks_iff.mp this).2.2.2
  · have := hM.dotProduct_mulVec_nonneg (Sum.elim 0 y)
    rw [← fromBlocks_toBlocks M, fromBlocks_mulVec, star_sum_elim, dotProduct_sum_elim] at this
    simpa using this

/-- `e^{-tH}` through the spectral calculus. -/
theorem exp_neg_eq (hH : (generator A B D).IsHermitian) (t : ℝ) :
    NormedSpace.exp (t • (-generator A B D))
      = spectralFunction hH (fun l => Real.exp (-t * l)) := by
  rw [smul_neg, ← neg_smul, smul_eq_spectralFunction hH (-t), exp_spectralFunction]

/-- **(ER.18)**: `Q e^{-tH} Q ⪰ 0`. -/
theorem sampled_posSemidef (hH : (generator A B D).PosSemidef) (t : ℝ) :
    (sampled A B D t).PosSemidef := by
  unfold sampled
  rw [exp_neg_eq hH.1]
  exact posSemidef_toBlocks₂₂ (spectralFunction_posSemidef hH.1 _ fun i => (Real.exp_pos _).le)

/-- `e^{-tH} ⪯ (I + tH)⁻¹` for `t ≥ 0`. -/
theorem exp_le_resolvent (hH : (generator A B D).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (((1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) + t • generator A B D)⁻¹
      - NormedSpace.exp (t • (-generator A B D))).PosSemidef := by
  rw [resolvent_spectral hH ht, exp_neg_eq hH.1, ← spectralFunction_sub]
  refine spectralFunction_posSemidef hH.1 _ fun i => ?_
  have h0 := hH.eigenvalues_nonneg i
  have hx : 0 ≤ t * hH.1.eigenvalues i := mul_nonneg ht h0
  have h1 := Real.add_one_le_exp (t * hH.1.eigenvalues i)
  rw [neg_mul, Real.exp_neg, sub_nonneg]
  exact inv_anti₀ (by linarith) (by linarith)

/-- The block form of `I + tH`. -/
theorem one_add_smul_generator (t : ℝ) :
    (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) + t • generator A B D
      = fromBlocks (1 + t • A) (t • B) (t • Bᴴ) (1 + t • D) := by
  unfold generator
  rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp

theorem toBlocks₂₂_sub (M N : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) :
    (M - N).toBlocks₂₂ = M.toBlocks₂₂ - N.toBlocks₂₂ := rfl

/-- The head comparison `t²(I + tA)⁻¹ ⪯ t A^†` on the supported range: the sandwich
`B^* (A^† - t (I + tA)⁻¹) B ⪰ 0` under the range condition. -/
theorem head_comparison (hH : (generator A B D).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (Bᴴ * (pinv (generator_head hH).1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹)
      * B).PosSemidef := by
  have hA := generator_head hH
  have hQB : supportProj hA.1 * B = B := by
    rw [← mul_pinv_eq_supportProj]
    exact range_condition_of_posSemidef hA B D hH
  have hBQ : Bᴴ * supportProj hA.1 = Bᴴ := by
    have := congrArg conjTranspose hQB
    rwa [conjTranspose_mul, (supportProj_posSemidef hA.1).1.eq] at this
  have hG : pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹
      = spectralFunction hA.1 (fun l => (if 0 < l then l⁻¹ else 0) - t * (1 + t * l)⁻¹) := by
    rw [resolvent_spectral hA ht, spectralFunction_sub, spectralFunction_smul]
    unfold pinv
    congr 1
  have hQGQ : (supportProj hA.1 * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹)
      * supportProj hA.1).PosSemidef := by
    rw [hG]
    unfold supportProj
    rw [spectralFunction_mul, spectralFunction_mul]
    refine spectralFunction_posSemidef hA.1 _ fun i => ?_
    have h0 := hA.eigenvalues_nonneg i
    split_ifs with hl
    · have h1 : 0 < 1 + t * hA.1.eigenvalues i := by positivity
      have : (hA.1.eigenvalues i)⁻¹ - t * (1 + t * hA.1.eigenvalues i)⁻¹
          = (hA.1.eigenvalues i * (1 + t * hA.1.eigenvalues i))⁻¹ := by
        field_simp
        ring
      rw [this]
      have : 0 < hA.1.eigenvalues i * (1 + t * hA.1.eigenvalues i) := by positivity
      have := inv_pos.mpr this
      nlinarith
    · simp
  have e : Bᴴ * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹) * B
      = Bᴴ * (supportProj hA.1 * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹)
        * supportProj hA.1) * B := by
    calc Bᴴ * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹) * B
        = (Bᴴ * supportProj hA.1) * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹)
          * (supportProj hA.1 * B) := by rw [hBQ, hQB]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact hQGQ.conjTranspose_mul_mul_same B

/-- **(ER.18)**: with `S ⪰ s I`, `Q e^{-tH} Q ⪯ (I + tS)⁻¹`. -/
theorem sampled_le_resolvent (hH : (generator A B D).PosSemidef) {s t : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t)
    (hS : (tailDeficit A B D (generator_head hH).1 - (s : ℂ) • 1).PosSemidef) :
    (((1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D (generator_head hH).1)⁻¹
      - sampled A B D t).PosSemidef := by
  have hA := generator_head hH
  set S := tailDeficit A B D hA.1 with hSdef
  have hA' : ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A).PosDef := one_add_smul_posDef hA ht
  letI : Invertible ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A) :=
    Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp hA'.isUnit)
  set Sc : Matrix (Fin p) (Fin p) ℂ :=
    (1 + t • D) - (t • Bᴴ) * ⅟((1 : Matrix (Fin m) (Fin m) ℂ) + t • A) * (t • B) with hSc
  -- the Schur complement dominates `I + tS`
  have hSc_ge : (Sc - (1 + t • S)).PosSemidef := by
    have e : Sc - (1 + t • S)
        = t • (Bᴴ * (pinv hA.1 - t • ((1 : Matrix (Fin m) (Fin m) ℂ) + t • A)⁻¹) * B) := by
      rw [hSc, hSdef, Matrix.invOf_eq_nonsing_inv]
      unfold tailDeficit
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, smul_sub,
        smul_smul]
      module
    rw [e]
    exact smul_posSemidef_real (head_comparison hH ht) ht
  have h1S : ((1 : Matrix (Fin p) (Fin p) ℂ) + t • S).PosDef := by
    refine posDef_of_floor (γ := 1 + t * s) ?_ (by positivity)
    have e : (1 : Matrix (Fin p) (Fin p) ℂ) + t • S - ((1 + t * s : ℝ) : ℂ) • 1
        = t • (S - (s : ℂ) • 1) := by
      ext i j
      simp [Matrix.one_apply, Complex.real_smul]
      split_ifs <;> ring
    rw [e]
    exact smul_posSemidef_real hS ht
  have hScPD : Sc.PosDef := by
    refine posDef_of_floor (γ := 1 + t * s) ?_ (by positivity)
    have e : Sc - ((1 + t * s : ℝ) : ℂ) • 1
        = (Sc - (1 + t • S))
          + ((1 : Matrix (Fin p) (Fin p) ℂ) + t • S - ((1 + t * s : ℝ) : ℂ) • 1) := by
      abel
    rw [e]
    refine hSc_ge.add ?_
    have e2 : (1 : Matrix (Fin p) (Fin p) ℂ) + t • S - ((1 + t * s : ℝ) : ℂ) • 1
        = t • (S - (s : ℂ) • 1) := by
      ext i j
      simp [Matrix.one_apply, Complex.real_smul]
      split_ifs <;> ring
    rw [e2]
    exact smul_posSemidef_real hS ht
  letI : Invertible Sc :=
    Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp hScPD.isUnit)
  letI : Invertible (fromBlocks (1 + t • A) (t • B) (t • Bᴴ) (1 + t • D)) :=
    fromBlocks₁₁Invertible _ _ _ _
  have hblock :
      (((1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) + t • generator A B D)⁻¹).toBlocks₂₂
        = Sc⁻¹ := by
    rw [one_add_smul_generator, ← Matrix.invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq,
      toBlocks_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hL := inv_le_inv_of_le h1S hScPD hSc_ge
  have hE := posSemidef_toBlocks₂₂ (exp_le_resolvent hH ht)
  rw [toBlocks₂₂_sub, hblock] at hE
  have e : ((1 : Matrix (Fin p) (Fin p) ℂ) + t • S)⁻¹ - sampled A B D t
      = (((1 : Matrix (Fin p) (Fin p) ℂ) + t • S)⁻¹ - Sc⁻¹) + (Sc⁻¹ - sampled A B D t) := by abel
  rw [e]
  exact hL.add hE

/-- **(ER.18)**: the scalar bound `(I + tS)⁻¹ ⪯ (1 + ts)⁻¹ I`. -/
theorem resolvent_le_scalar (hA : A.IsHermitian) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (hS : (tailDeficit A B D hA - (s : ℂ) • 1).PosSemidef) :
    ((((1 + t * s)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)
      - ((1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D hA)⁻¹).PosSemidef := by
  have hpos : 0 < 1 + t * s := by positivity
  have hY : ((((1 + t * s : ℝ)) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ)).PosDef := by
    refine posDef_of_floor (γ := 1 + t * s) ?_ hpos
    rw [sub_self]; exact PosSemidef.zero
  have hYinv : ((((1 + t * s : ℝ)) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ))⁻¹
      = (((1 + t * s)⁻¹ : ℝ) : ℂ) • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne']
    simp
  have hX : ((1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D hA).PosDef := by
    refine posDef_of_floor (γ := 1 + t * s) ?_ hpos
    have e : (1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D hA - ((1 + t * s : ℝ) : ℂ) • 1
        = t • (tailDeficit A B D hA - (s : ℂ) • 1) := by
      ext i j
      simp [Matrix.one_apply, Complex.real_smul]
      split_ifs <;> ring
    rw [e]
    exact smul_posSemidef_real hS ht
  have hXY : ((1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D hA
      - (((1 + t * s : ℝ)) : ℂ) • 1).PosSemidef := by
    have e : (1 : Matrix (Fin p) (Fin p) ℂ) + t • tailDeficit A B D hA - ((1 + t * s : ℝ) : ℂ) • 1
        = t • (tailDeficit A B D hA - (s : ℂ) • 1) := by
      ext i j
      simp [Matrix.one_apply, Complex.real_smul]
      split_ifs <;> ring
    rw [e]
    exact smul_posSemidef_real hS ht
  have := inv_le_inv_of_le hY hX hXY
  rwa [hYinv] at this

end generator

/-! ### ER.16: the first difference and the protocol criterion -/

section er16

variable {m p : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin m) (Fin p) ℂ)
  (D : Matrix (Fin p) (Fin p) ℂ)

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _

/-- The genuine second-order Taylor expansion of the matrix exponential with
cubic Banach-algebra remainder. -/
theorem matrixExp_secondOrder_remainder_isBigO {n : Type*}
    [Fintype n] [DecidableEq n] :
    (fun X : Matrix n n ℂ => NormedSpace.exp X -
      (1 + X + (2 : ℂ)⁻¹ • X ^ 2))
      =O[𝓝 0] fun X : Matrix n n ℂ => ‖X‖ ^ 3 := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero
    (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isBigO_sub_partialSum_pow 3
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards with X
  simp only [zero_add]
  congr 1
  norm_num [FormalMultilinearSeries.partialSum,
    NormedSpace.expSeries_apply_eq, Finset.sum_range_succ]

/-- Along every real matrix line, the second-order exponential remainder is
`O(t^3)`. -/
theorem matrixExp_line_secondOrder_remainder_isBigO {n : Type*}
    [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    (fun t : ℝ => NormedSpace.exp (t • X) -
      (1 + t • X + ((t ^ 2 / 2 : ℝ) : ℂ) • X ^ 2))
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  have htend : Tendsto (fun t : ℝ => t • X) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t • X) :=
      continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  have h := matrixExp_secondOrder_remainder_isBigO.comp_tendsto htend
  have hnorm : (fun t : ℝ => ‖t • X‖ ^ 3)
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    refine IsBigO.of_bound (‖X‖ ^ 3) ?_
    filter_upwards with t
    simp only [norm_pow, norm_smul, Real.norm_eq_abs, abs_pow]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg X))]
    ring_nf
    exact le_rfl
  refine (h.trans hnorm).congr' ?_ EventuallyEq.rfl
  filter_upwards with t
  simp only [Function.comp_apply]
  have ht : t • X = (t : ℂ) • X := by
    ext i j
    simp [Complex.real_smul]
  rw [ht, smul_pow, smul_smul]
  have hcoef : (2 : ℂ)⁻¹ * (t : ℂ) ^ 2 = ((t ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    norm_num
    ring
  rw [hcoef]

/-- Tail-block extraction as a continuous linear map. -/
noncomputable def tailBlock :
    Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ →L[ℝ] Matrix (Fin p) (Fin p) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₂₂
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem tailBlock_apply (M : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) :
    tailBlock M = M.toBlocks₂₂ := rfl

theorem toBlocks₂₂_add_er16
    (M N : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) :
    (M + N).toBlocks₂₂ = M.toBlocks₂₂ + N.toBlocks₂₂ := rfl

theorem toBlocks₂₂_real_smul_er16 (t : ℝ)
    (M : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) :
    (t • M).toBlocks₂₂ = t • M.toBlocks₂₂ := rfl

theorem toBlocks₂₂_complex_smul_er16 (c : ℂ)
    (M : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ) :
    (c • M).toBlocks₂₂ = c • M.toBlocks₂₂ := rfl

theorem neg_generator_tail :
    (-generator A B D).toBlocks₂₂ = -D := by
  unfold generator
  rw [fromBlocks_neg, toBlocks_fromBlocks₂₂]

/-- The quadratic tail block is precisely the coupling energy plus the killed
quadratic term. -/
theorem neg_generator_sq_tail :
    ((-generator A B D) ^ 2).toBlocks₂₂ = Bᴴ * B + (-D) ^ 2 := by
  rw [pow_two, pow_two, neg_mul_neg, neg_mul_neg]
  unfold generator
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₂]

/-- **(ER.16)**: the first difference `F(t) = Q e^{-tH} Q - e^{-tD}`. -/
noncomputable def firstDiff (t : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  sampled A B D t - killed D t

/-- `F'(t)`. -/
noncomputable def firstDiff' (t : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  (NormedSpace.exp (t • (-generator A B D)) * (-generator A B D)).toBlocks₂₂
    - NormedSpace.exp (t • (-D)) * (-D)

/-- `F''(t)`. -/
noncomputable def firstDiff'' (t : ℝ) : Matrix (Fin p) (Fin p) ℂ :=
  (NormedSpace.exp (t • (-generator A B D)) * (-generator A B D) * (-generator A B D)).toBlocks₂₂
    - NormedSpace.exp (t • (-D)) * (-D) * (-D)

theorem hasDerivAt_firstDiff (t : ℝ) :
    HasDerivAt (firstDiff A B D) (firstDiff' A B D t) t := by
  have h1 := (tailBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (-generator A B D) t)
  have h2 := hasDerivAt_exp_smul_const (-D) t
  exact h1.sub h2

theorem hasDerivAt_firstDiff' (t : ℝ) :
    HasDerivAt (firstDiff' A B D) (firstDiff'' A B D t) t := by
  have h1 := (tailBlock (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const (-generator A B D) t).mul_const (-generator A B D))
  have h2 := (hasDerivAt_exp_smul_const (-D) t).mul_const (-D)
  exact h1.sub h2

theorem toBlocks₂₂_one : (1 : Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ).toBlocks₂₂ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]

/-- **(ER.16)**: `F(0) = 0`, `F'(0) = 0`, `F''(0) = B^* B`, i.e.
`Q e^{-tH} Q - e^{-tD} = (t²/2) B^* B + O(t³)`. -/
theorem taylor_data :
    firstDiff A B D 0 = 0 ∧ firstDiff' A B D 0 = 0 ∧ firstDiff'' A B D 0 = Bᴴ * B := by
  refine ⟨?_, ?_, ?_⟩
  · unfold firstDiff sampled killed
    rw [zero_smul, zero_smul, NormedSpace.exp_zero, NormedSpace.exp_zero, toBlocks₂₂_one, sub_self]
  · unfold firstDiff' generator
    rw [zero_smul, zero_smul, NormedSpace.exp_zero, NormedSpace.exp_zero, Matrix.one_mul,
      Matrix.one_mul, fromBlocks_neg, toBlocks_fromBlocks₂₂, sub_self]
  · unfold firstDiff'' generator
    rw [zero_smul, zero_smul, NormedSpace.exp_zero, NormedSpace.exp_zero, Matrix.one_mul,
      Matrix.one_mul, neg_mul_neg, neg_mul_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₂]
    abel

/-- **(ER.16), with its actual remainder**:
`Q e^{-tH} Q - e^{-tD} = (t²/2) B^*B + O(t³)` in matrix norm. -/
theorem firstDiff_cubic_remainder_isBigO :
    (fun t : ℝ => firstDiff A B D t -
      ((t ^ 2 / 2 : ℝ) : ℂ) • (Bᴴ * B))
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  let rH : ℝ → Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ := fun t =>
    NormedSpace.exp (t • (-generator A B D)) -
      (1 + t • (-generator A B D) +
        ((t ^ 2 / 2 : ℝ) : ℂ) • (-generator A B D) ^ 2)
  let rD : ℝ → Matrix (Fin p) (Fin p) ℂ := fun t =>
    NormedSpace.exp (t • (-D)) -
      (1 + t • (-D) + ((t ^ 2 / 2 : ℝ) : ℂ) • (-D) ^ 2)
  have hH : rH =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    exact matrixExp_line_secondOrder_remainder_isBigO (-generator A B D)
  have hHt : (fun t => tailBlock (rH t)) =O[𝓝 0] fun t : ℝ => t ^ 3 :=
    ((tailBlock (m := m) (p := p)).isBigO_comp rH (𝓝 0)).trans hH
  have hD : rD =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    exact matrixExp_line_secondOrder_remainder_isBigO (-D)
  refine (hHt.sub hD).congr' ?_ EventuallyEq.rfl
  filter_upwards with t
  dsimp only [rH, rD]
  unfold firstDiff sampled killed
  rw [tailBlock_apply, toBlocks₂₂_sub, toBlocks₂₂_add_er16,
    toBlocks₂₂_add_er16, toBlocks₂₂_one, toBlocks₂₂_real_smul_er16,
    toBlocks₂₂_complex_smul_er16, neg_generator_tail, neg_generator_sq_tail]
  module

/-- If the protocols agree near `t = 0`, the coupling vanishes. -/
theorem coupling_eq_zero_of_agree (h : ∀ᶠ t in nhds (0 : ℝ), firstDiff A B D t = 0) : B = 0 := by
  have h1 : ∀ᶠ t in nhds (0 : ℝ), firstDiff' A B D t = 0 := by
    filter_upwards [h.eventually_nhds] with t ht
    exact ((hasDerivAt_firstDiff A B D t).unique
      ((hasDerivAt_const t (0 : Matrix (Fin p) (Fin p) ℂ)).congr_of_eventuallyEq ht)).symm ▸ rfl
  have h2 : firstDiff'' A B D 0 = 0 :=
    ((hasDerivAt_firstDiff' A B D 0).unique
      ((hasDerivAt_const (0 : ℝ) (0 : Matrix (Fin p) (Fin p) ℂ)).congr_of_eventuallyEq
        h1)).symm ▸ rfl
  rw [(taylor_data A B D).2.2] at h2
  exact conjTranspose_mul_self_eq_zero.mp h2

/-- **Uniqueness of the exponential flow**: a differentiable `Y` with `Y' = Y X`,
`Y 0 = 1` is `t ↦ e^{tX}`. -/
theorem eq_exp_of_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (Y : ℝ → Matrix n n ℂ) (hY : ∀ t, HasDerivAt Y (Y t * X) t) (h0 : Y 0 = 1) (t : ℝ) :
    Y t = NormedSpace.exp (t • X) := by
  have hE : ∀ u : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • X))
      (-(NormedSpace.exp ((-u) • X) * X)) u := by
    intro u
    have := (hasDerivAt_exp_smul_const X (-u)).scomp u (hasDerivAt_neg' (x := u))
    rw [neg_one_smul] at this
    exact this
  have hcomm : ∀ u : ℝ, NormedSpace.exp ((-u) • X) * X = X * NormedSpace.exp ((-u) • X) :=
    fun u => (((Commute.refl X).smul_left (-u)).exp_left).eq
  have hZ : ∀ u, HasDerivAt (fun u => Y u * NormedSpace.exp ((-u) • X)) 0 u := by
    intro u
    have h := (hY u).mul (hE u)
    have e : Y u * X * NormedSpace.exp ((-u) • X) + Y u * -(NormedSpace.exp ((-u) • X) * X)
        = 0 := by
      rw [Matrix.mul_neg, hcomm, ← Matrix.mul_assoc, add_neg_cancel]
    exact h.congr_deriv e
  have hconst := is_const_of_deriv_eq_zero (fun u => (hZ u).differentiableAt)
    (fun u => (hZ u).deriv) t 0
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, h0, Matrix.mul_one] at hconst
  have hinv : NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left (-t)).smul_right t),
      neg_smul, neg_add_cancel, NormedSpace.exp_zero]
  calc Y t = Y t * (NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X)) := by
        rw [hinv, Matrix.mul_one]
    _ = NormedSpace.exp (t • X) := by rw [← Matrix.mul_assoc, hconst, Matrix.one_mul]

/-- Head embedding as a continuous linear map. -/
noncomputable def headEmbed :
    Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => fromBlocks M 0 0 0
      map_add' := fun M N => by rw [fromBlocks_add]; simp
      map_smul' := fun c M => by rw [RingHom.id_apply, fromBlocks_smul]; simp }

/-- Tail embedding as a continuous linear map. -/
noncomputable def tailEmbed :
    Matrix (Fin p) (Fin p) ℂ →L[ℝ] Matrix (Fin m ⊕ Fin p) (Fin m ⊕ Fin p) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => fromBlocks 0 0 0 M
      map_add' := fun M N => by rw [fromBlocks_add]; simp
      map_smul' := fun c M => by rw [RingHom.id_apply, fromBlocks_smul]; simp }

theorem headEmbed_add_tailEmbed (M : Matrix (Fin m) (Fin m) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) :
    headEmbed (p := p) M + tailEmbed (m := m) N = fromBlocks M 0 0 N := by
  change fromBlocks M 0 0 0 + fromBlocks 0 0 0 N = _
  rw [fromBlocks_add]
  simp

/-- The exponential of a block-diagonal generator. -/
theorem exp_blockDiag (t : ℝ) :
    NormedSpace.exp (t • fromBlocks A 0 0 D)
      = fromBlocks (NormedSpace.exp (t • A)) 0 0 (NormedSpace.exp (t • D)) := by
  symm
  refine eq_exp_of_hasDerivAt (fromBlocks A 0 0 D)
    (fun t => fromBlocks (NormedSpace.exp (t • A)) 0 0 (NormedSpace.exp (t • D))) (fun t => ?_)
    (by simp [NormedSpace.exp_zero, fromBlocks_one]) t
  have h1 := (headEmbed (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const A t)
  have h2 := (tailEmbed (m := m) (p := p)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const D t)
  have h := h1.add h2
  have e1 : (fun t : ℝ => fromBlocks (NormedSpace.exp (t • A)) 0 0 (NormedSpace.exp (t • D)))
      = fun t : ℝ => headEmbed (m := m) (p := p) (NormedSpace.exp (t • A))
        + tailEmbed (m := m) (p := p) (NormedSpace.exp (t • D)) := by
    funext t; rw [headEmbed_add_tailEmbed]
  have e2 : fromBlocks (NormedSpace.exp (t • A)) 0 0 (NormedSpace.exp (t • D)) * fromBlocks A 0 0 D
      = headEmbed (m := m) (p := p) (NormedSpace.exp (t • A) * A)
        + tailEmbed (m := m) (p := p) (NormedSpace.exp (t • D) * D) := by
    rw [headEmbed_add_tailEmbed, fromBlocks_multiply]
    simp
  rw [e1, e2]
  exact h

/-- If the coupling vanishes, the protocols agree for every `t`. -/
theorem agree_of_coupling_eq_zero (hB : B = 0) (t : ℝ) : firstDiff A B D t = 0 := by
  unfold firstDiff sampled killed generator
  rw [hB, conjTranspose_zero, fromBlocks_neg, neg_zero, neg_zero, exp_blockDiag,
    toBlocks_fromBlocks₂₂, sub_self]

/-- **Protocol criterion**: the two protocols agree for all sufficiently small `t` exactly
when `B = 0`. -/
theorem protocols_agree_iff :
    (∀ᶠ t in nhds (0 : ℝ), firstDiff A B D t = 0) ↔ B = 0 :=
  ⟨coupling_eq_zero_of_agree A B D, fun hB => Filter.Eventually.of_forall
    (agree_of_coupling_eq_zero A B D hB)⟩

end er16

end SampledVersusKilled
end NCG
