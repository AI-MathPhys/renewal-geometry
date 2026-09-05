/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LocalizerExtensionFloorExact

/-!
# The exact low-`A₊` restoring short and the harmonic row selector

Exact encodings of `thm:GRH-prime-scale-restoring-short` (GRH.8–GRH.12) and
`cor:GRH-restoring-row-selector` (GRH.13) in the sector coordinates
`Ran P = H_θ ⊕ L_θ` (index types `m` for the high sector and `p` for the low
sector), where `A₊` is block diagonal `diag(A_H, A_L)`, the coupling form
`D = C_tr + C_∂ + C_ret = [[D₂₂, D₂₁], [D₂₁^*, D₁₁]] ⪰ 0`, and
`K = B - hP = A₊ + D - h I`.

## Inertia via negative subspaces

`negIndex M` is the supremum of the dimensions of subspaces on which the
Hermitian form of `M` is negative definite, and `nullity M = dim ker M`.
`negIndex_eq` / `nullity_eq` are the Haynsworth inertia identities for a block
matrix `[[A, B], [B^*, D]]` with `A ≻ 0`: the harmonic extension
`x ↦ (-A⁻¹ B x, x)` and the low-sector projection exchange negative subspaces
(and kernels) of the block matrix and of its Schur complement `D - B^* A⁻¹ B`.

## Main statements

* `high_floor` (GRH.8): `H K H ⪰ (θ - 1) h H`;
* `restoringShort_posSemidef` (GRH.9): `𝓡_θ = L D L - L D H (H K H)⁻¹ H D L ⪰ 0`;
* `schur_eq` (GRH.10): `𝔖_θ = L (A₊ - hP) L + 𝓡_θ`;
* `negIndex_shifted` / `nullity_shifted` (GRH.11): `n₋(K) = n₋(𝔖_θ)`, `n₀(K) = n₀(𝔖_θ)`;
* `no_negative_direction_iff` (GRH.12): `K ⪰ 0 ⇔ 𝓡_θ ⪰ L (hP - A₊) L`;
* `restoringShort_rows` (GRH.13): the four-row expansion of `⟨x, 𝓡_θ x⟩`;
* `row_selector`: a negative Schur witness makes at least one row smaller than
  its assigned share of `d_θ(x)`.
-/

open Matrix NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
  NCG.LocalizerExtensionFloor
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace GRHRestoringShort

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-! ### Inertia via negative subspaces -/

section inertia

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `W` is a negative subspace for the Hermitian form of `M`. -/
def IsNegative (M : Matrix n n ℂ) (W : Submodule ℂ (n → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → rayleigh M x < 0

/-- The dimensions of negative subspaces. -/
def negDims (M : Matrix n n ℂ) : Set ℕ :=
  {k | ∃ W : Submodule ℂ (n → ℂ), IsNegative M W ∧ Module.finrank ℂ W = k}

/-- The negative index `n₋(M)`. -/
noncomputable def negIndex (M : Matrix n n ℂ) : ℕ := sSup (negDims M)

/-- The nullity `n₀(M) = dim ker M`. -/
noncomputable def nullity (M : Matrix n n ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (Matrix.toLin' M))

end inertia

theorem finrank_map_of_injective {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (U : Submodule ℂ V) :
    Module.finrank ℂ (U.map f) = Module.finrank ℂ U := by
  have h1 : U.map f = LinearMap.range (f.comp U.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hinj : Function.Injective (f.comp U.subtype) := fun a b hab => Subtype.ext (hf hab)
  rw [h1, LinearMap.finrank_range_of_inj hinj]

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-! ### Positive definite pivots -/

theorem supportProj_eq_one {A : Matrix m m ℂ} (hA : A.PosDef) : supportProj hA.1 = 1 := by
  unfold supportProj
  rw [spectralFunction_congr hA.1 (g := fun _ => (1 : ℝ)) (fun i => by simp [hA.eigenvalues_pos i]),
    spectralFunction_const]
  simp

theorem pinv_mul_self {A : Matrix m m ℂ} (hA : A.PosDef) : pinv hA.1 * A = 1 := by
  rw [← supportProj_eq_pinv_mul, supportProj_eq_one hA]

theorem self_mul_pinv {A : Matrix m m ℂ} (hA : A.PosDef) : A * pinv hA.1 = 1 := by
  rw [mul_pinv_eq_supportProj, supportProj_eq_one hA]

theorem range_condition_of_posDef {A : Matrix m m ℂ} (hA : A.PosDef) (B : Matrix m p ℂ) :
    A * pinv hA.1 * B = B := by
  rw [self_mul_pinv hA, Matrix.one_mul]

/-- A Hermitian matrix dominating a positive multiple of the identity is positive definite. -/
theorem posDef_of_floor {G : Matrix m m ℂ} {γ : ℝ} (hG : (G - (γ : ℂ) • 1).PosSemidef)
    (hγ : 0 < γ) : G.PosDef := by
  have h1 : ((γ : ℂ) • (1 : Matrix m m ℂ)).IsHermitian := by
    change ((γ : ℂ) • (1 : Matrix m m ℂ))ᴴ = _
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · have := hG.1.add h1
    rwa [sub_add_cancel] at this
  · have e : G = (G - (γ : ℂ) • 1) + (γ : ℂ) • 1 := (sub_add_cancel _ _).symm
    rw [e, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul]
    refine add_pos_of_nonneg_of_pos (hG.dotProduct_mulVec_nonneg x) ?_
    rw [smul_eq_mul]
    exact mul_pos (Complex.zero_lt_real.mpr hγ) (dotProduct_star_self_pos_iff.mpr hx)

/-! ### Haynsworth inertia for a positive definite pivot -/

variable {A : Matrix m m ℂ}

/-- The Schur complement `D - B^* A⁻¹ B`. -/
noncomputable def schurC (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) :
    Matrix p p ℂ := D - Bᴴ * pinv hA.1 * B

/-- The harmonic extension `x ↦ (-A⁻¹ B x, x)`. -/
noncomputable def harmonicExt (hA : A.PosDef) (B : Matrix m p ℂ) :
    (p → ℂ) →ₗ[ℂ] (m ⊕ p → ℂ) where
  toFun x := Sum.elim (-(pinv hA.1 *ᵥ (B *ᵥ x))) x
  map_add' x y := by
    funext i
    cases i with
    | inl i => simp [mulVec_add, add_comm]
    | inr i => simp
  map_smul' c x := by
    funext i
    cases i with
    | inl i => simp [mulVec_smul]
    | inr i => simp

theorem harmonicExt_apply (hA : A.PosDef) (B : Matrix m p ℂ) (x : p → ℂ) :
    harmonicExt hA B x = Sum.elim (-(pinv hA.1 *ᵥ (B *ᵥ x))) x := rfl

theorem harmonicExt_injective (hA : A.PosDef) (B : Matrix m p ℂ) :
    Function.Injective (harmonicExt hA B) := by
  intro x y hxy
  have := congrArg (fun z => z ∘ Sum.inr) hxy
  simpa [harmonicExt_apply] using this

/-- The block quadratic form after completing the square in the pivot. -/
theorem rayleigh_block (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) (y : m → ℂ)
    (x : p → ℂ) :
    rayleigh (fromBlocks A B Bᴴ D) (Sum.elim y x)
      = rayleigh A (y + pinv hA.1 *ᵥ (B *ᵥ x)) + rayleigh (schurC hA B D) x := by
  unfold rayleigh schurC
  rw [completion_of_square hA.posSemidef B D (range_condition_of_posDef hA B) y x, Complex.add_re]

theorem rayleigh_harmonicExt (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) (x : p → ℂ) :
    rayleigh (fromBlocks A B Bᴴ D) (harmonicExt hA B x) = rayleigh (schurC hA B D) x := by
  rw [harmonicExt_apply, rayleigh_block hA B D, neg_add_cancel]
  simp [rayleigh]

/-- **Haynsworth (negative part)**: the negative subspaces of the block matrix and of
its Schur complement have the same dimensions. -/
theorem negDims_eq (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) :
    negDims (fromBlocks A B Bᴴ D) = negDims (schurC hA B D) := by
  ext k
  constructor
  · rintro ⟨W, hW, rfl⟩
    let π : (m ⊕ p → ℂ) →ₗ[ℂ] (p → ℂ) := LinearMap.funLeft ℂ ℂ Sum.inr
    have hπ : ∀ z : m ⊕ p → ℂ, π z = z ∘ Sum.inr := fun z => rfl
    have hker : ∀ z ∈ W, z ∘ Sum.inr = 0 → z = 0 := by
      intro z hz h0
      by_contra hne
      have hneg := hW z hz hne
      rw [← Sum.elim_comp_inl_inr z, rayleigh_block hA B D, h0] at hneg
      simp only [mulVec_zero, add_zero] at hneg
      have h1 := rayleigh_nonneg hA.posSemidef (z ∘ Sum.inl)
      have h2 : rayleigh (schurC hA B D) 0 = 0 := by simp [rayleigh]
      linarith
    have hinj : Function.Injective (π.comp W.subtype) := by
      intro z₁ z₂ h
      apply Subtype.ext
      have hsub : (z₁ : m ⊕ p → ℂ) - (z₂ : m ⊕ p → ℂ) ∈ W := W.sub_mem z₁.2 z₂.2
      have h0 : ((z₁ : m ⊕ p → ℂ) - (z₂ : m ⊕ p → ℂ)) ∘ Sum.inr = 0 := by
        have this : (z₁ : m ⊕ p → ℂ) ∘ Sum.inr = (z₂ : m ⊕ p → ℂ) ∘ Sum.inr := h
        funext i
        simp only [Function.comp_apply, Pi.sub_apply, Pi.zero_apply]
        exact sub_eq_zero.mpr (congrFun this i)
      exact sub_eq_zero.mp (hker _ hsub h0)
    refine ⟨LinearMap.range (π.comp W.subtype), ?_, LinearMap.finrank_range_of_inj hinj⟩
    intro x hx hx0
    obtain ⟨⟨z, hz⟩, rfl⟩ := LinearMap.mem_range.mp hx
    have hzx : (π.comp W.subtype) ⟨z, hz⟩ = z ∘ Sum.inr := rfl
    rw [hzx] at hx0 ⊢
    have hz0 : z ≠ 0 := fun h => hx0 (by simp [h])
    have hneg := hW z hz hz0
    rw [← Sum.elim_comp_inl_inr z, rayleigh_block hA B D] at hneg
    have h1 := rayleigh_nonneg hA.posSemidef (z ∘ Sum.inl + pinv hA.1 *ᵥ (B *ᵥ (z ∘ Sum.inr)))
    linarith
  · rintro ⟨W', hW', rfl⟩
    refine ⟨W'.map (harmonicExt hA B), ?_,
      finrank_map_of_injective _ (harmonicExt_injective hA B) W'⟩
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    have hx0 : x ≠ 0 := fun h => hz0 (by simp [h])
    rw [rayleigh_harmonicExt]
    exact hW' x hx hx0

theorem negIndex_eq (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) :
    negIndex (fromBlocks A B Bᴴ D) = negIndex (schurC hA B D) := by
  unfold negIndex
  rw [negDims_eq hA B D]

/-- The kernel of the block matrix is the harmonic extension of the kernel of the
Schur complement. -/
theorem ker_eq (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) :
    LinearMap.ker (Matrix.toLin' (fromBlocks A B Bᴴ D))
      = (LinearMap.ker (Matrix.toLin' (schurC hA B D))).map (harmonicExt hA B) := by
  ext z
  simp only [LinearMap.mem_ker, Submodule.mem_map, Matrix.toLin'_apply]
  constructor
  · intro hz
    have hz' := hz
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at hz'
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hz'
    have h1 : A *ᵥ (z ∘ Sum.inl) + B *ᵥ (z ∘ Sum.inr) = 0 := by
      have := congrArg (fun w => w ∘ Sum.inl) hz'
      simpa using this
    have h2 : Bᴴ *ᵥ (z ∘ Sum.inl) + D *ᵥ (z ∘ Sum.inr) = 0 := by
      have := congrArg (fun w => w ∘ Sum.inr) hz'
      simpa using this
    have hy : z ∘ Sum.inl = -(pinv hA.1 *ᵥ (B *ᵥ (z ∘ Sum.inr))) := by
      have := congrArg (fun w => pinv hA.1 *ᵥ w) h1
      simp only [mulVec_add, mulVec_mulVec, pinv_mul_self hA, one_mulVec, mulVec_zero] at this
      rw [← mulVec_mulVec] at this
      exact eq_neg_of_add_eq_zero_left this
    refine ⟨z ∘ Sum.inr, ?_, ?_⟩
    · have e : (D - Bᴴ * pinv hA.1 * B) *ᵥ (z ∘ Sum.inr)
          = D *ᵥ (z ∘ Sum.inr) + Bᴴ *ᵥ (z ∘ Sum.inl) := by
        rw [hy, Matrix.sub_mulVec, mulVec_neg, ← mulVec_mulVec, ← mulVec_mulVec]
        abel
      change (D - Bᴴ * pinv hA.1 * B) *ᵥ (z ∘ Sum.inr) = 0
      rw [e, add_comm]
      exact h2
    · rw [harmonicExt_apply, ← hy]
      exact Sum.elim_comp_inl_inr z
  · rintro ⟨x, hx, rfl⟩
    change (D - Bᴴ * pinv hA.1 * B) *ᵥ x = 0 at hx
    rw [harmonicExt_apply, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have e1 : A *ᵥ (-(pinv hA.1 *ᵥ (B *ᵥ x))) + B *ᵥ x = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mulVec_mulVec, range_condition_of_posDef hA B,
        neg_add_cancel]
    have e2 : Bᴴ *ᵥ (-(pinv hA.1 *ᵥ (B *ᵥ x))) + D *ᵥ x = 0 := by
      rw [Matrix.sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec] at hx
      rw [mulVec_neg, add_comm, ← sub_eq_add_neg]
      exact hx
    rw [e1, e2]
    funext i
    cases i <;> rfl

/-- **Haynsworth (kernel)**: the nullities agree. -/
theorem nullity_eq (hA : A.PosDef) (B : Matrix m p ℂ) (D : Matrix p p ℂ) :
    nullity (fromBlocks A B Bᴴ D) = nullity (schurC hA B D) := by
  unfold nullity
  rw [ker_eq hA B D, finrank_map_of_injective _ (harmonicExt_injective hA B)]

/-! ### The restoring short (GRH.8–GRH.12) -/

section grh

variable (AH : Matrix m m ℂ) (AL : Matrix p p ℂ) (D₂₂ : Matrix m m ℂ) (D₂₁ : Matrix m p ℂ)
  (D₁₁ : Matrix p p ℂ) (h : ℝ)

/-- The high block `H_θ K H_θ = A_H + D₂₂ - h I`. -/
def highBlock : Matrix m m ℂ := AH + D₂₂ - (h : ℂ) • 1

/-- The old-positive form `A₊ = diag(A_H, A_L)` in sector coordinates. -/
def oldForm : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks AH 0 0 AL

/-- The coupling form `D = C_tr + C_∂ + C_ret`. -/
def coupling : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks D₂₂ D₂₁ D₂₁ᴴ D₁₁

/-- `K = B - hP = A₊ + D - h I` in sector coordinates. -/
def shifted : Matrix (m ⊕ p) (m ⊕ p) ℂ :=
  fromBlocks (highBlock AH D₂₂ h) D₂₁ D₂₁ᴴ (AL + D₁₁ - (h : ℂ) • 1)

theorem shifted_eq :
    shifted AH AL D₂₂ D₂₁ D₁₁ h = oldForm AH AL + coupling D₂₂ D₂₁ D₁₁ - (h : ℂ) • 1 := by
  unfold shifted oldForm coupling
  rw [sub_eq_add_neg (fromBlocks AH 0 0 AL + fromBlocks D₂₂ D₂₁ D₂₁ᴴ D₁₁), ← fromBlocks_one,
    fromBlocks_smul, fromBlocks_neg, fromBlocks_add, fromBlocks_add]
  unfold highBlock
  simp [sub_eq_add_neg]

/-- **(GRH.8)**: `H_θ K H_θ ⪰ (θ - 1) h H_θ`. -/
theorem high_floor {θ : ℝ} (hAH : (AH - ((θ * h : ℝ) : ℂ) • 1).PosSemidef)
    (hD : (coupling D₂₂ D₂₁ D₁₁).PosSemidef) :
    (highBlock AH D₂₂ h - (((θ - 1) * h : ℝ) : ℂ) • 1).PosSemidef := by
  have hD22 : D₂₂.PosSemidef := posSemidef_left_of_fromBlocks hD
  have e : highBlock AH D₂₂ h - (((θ - 1) * h : ℝ) : ℂ) • 1
      = (AH - ((θ * h : ℝ) : ℂ) • 1) + D₂₂ := by
    unfold highBlock
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e]
  exact hAH.add hD22

/-- The high block is positive definite for `θ > 1`, `h > 0`. -/
theorem highBlock_posDef {θ : ℝ} (hθ : 1 < θ) (hh : 0 < h)
    (hAH : (AH - ((θ * h : ℝ) : ℂ) • 1).PosSemidef)
    (hD : (coupling D₂₂ D₂₁ D₁₁).PosSemidef) : (highBlock AH D₂₂ h).PosDef :=
  posDef_of_floor (high_floor AH D₂₂ D₂₁ D₁₁ h hAH hD) (mul_pos (by linarith) hh)

/-- **(GRH.9)**: the exact restoring short `𝓡_θ = L D L - L D H (H K H)⁻¹ H D L`. -/
noncomputable def restoringShort (hG : (highBlock AH D₂₂ h).IsHermitian) : Matrix p p ℂ :=
  D₁₁ - D₂₁ᴴ * pinv hG * D₂₁

/-- **(GRH.9)**: `𝓡_θ ⪰ 0`. -/
theorem restoringShort_posSemidef (hG : (highBlock AH D₂₂ h).PosDef)
    (hAHh : (AH - (h : ℂ) • 1).PosSemidef) (hD : (coupling D₂₂ D₂₁ D₁₁).PosSemidef) :
    (restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1).PosSemidef := by
  have hD22 : D₂₂.PosSemidef := posSemidef_left_of_fromBlocks hD
  have hS0 := schur_posSemidef hD22 D₂₁ D₁₁ hD
  have hr := range_condition_of_posSemidef hD22 D₂₁ D₁₁ hD
  -- the comparison block matrix
  have hN0 : (fromBlocks D₂₂ D₂₁ D₂₁ᴴ (D₂₁ᴴ * pinv hD22.1 * D₂₁)).PosSemidef := by
    refine (posSemidef_block_iff hD22 D₂₁ _ ((pinv_posSemidef hD22.1).conjTranspose_mul_mul_same
      D₂₁).1).mpr ⟨hr, ?_⟩
    rw [sub_self]
    exact PosSemidef.zero
  have hN1 : (fromBlocks (highBlock AH D₂₂ h - D₂₂) 0 (0 : Matrix m p ℂ)ᴴ 0).PosSemidef := by
    have hX : (highBlock AH D₂₂ h - D₂₂).PosSemidef := by
      have e : highBlock AH D₂₂ h - D₂₂ = AH - (h : ℂ) • 1 := by
        unfold highBlock; abel
      rw [e]; exact hAHh
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun z => ?_⟩
    · rw [isHermitian_fromBlocks_iff]
      exact ⟨hX.1, by simp, by simp, isHermitian_zero⟩
    · rw [← Sum.elim_comp_inl_inr z, block_form]
      simpa using hX.dotProduct_mulVec_nonneg (z ∘ Sum.inl)
  have hN : (fromBlocks (highBlock AH D₂₂ h) D₂₁ D₂₁ᴴ (D₂₁ᴴ * pinv hD22.1 * D₂₁)).PosSemidef := by
    have e : fromBlocks (highBlock AH D₂₂ h) D₂₁ D₂₁ᴴ (D₂₁ᴴ * pinv hD22.1 * D₂₁)
        = fromBlocks D₂₂ D₂₁ D₂₁ᴴ (D₂₁ᴴ * pinv hD22.1 * D₂₁)
          + fromBlocks (highBlock AH D₂₂ h - D₂₂) 0 (0 : Matrix m p ℂ)ᴴ 0 := by
      rw [fromBlocks_add]
      simp
    rw [e]
    exact hN0.add hN1
  have hS1 := schur_posSemidef hG.posSemidef D₂₁ _ hN
  have e : restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1
      = (D₁₁ - D₂₁ᴴ * pinv hD22.1 * D₂₁)
        + (D₂₁ᴴ * pinv hD22.1 * D₂₁ - D₂₁ᴴ * pinv hG.posSemidef.1 * D₂₁) := by
    unfold restoringShort
    abel
  rw [e]
  exact hS0.add hS1

/-- **(GRH.10)**: `𝔖_θ = L (A₊ - hP) L + 𝓡_θ`. -/
theorem schur_eq (hG : (highBlock AH D₂₂ h).PosDef) :
    schurC hG D₂₁ (AL + D₁₁ - (h : ℂ) • 1)
      = (AL - (h : ℂ) • 1) + restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1 := by
  unfold schurC restoringShort
  abel

/-- **(GRH.11)**: `n₋(K) = n₋(𝔖_θ)`. -/
theorem negIndex_shifted (hG : (highBlock AH D₂₂ h).PosDef) :
    negIndex (shifted AH AL D₂₂ D₂₁ D₁₁ h)
      = negIndex ((AL - (h : ℂ) • 1) + restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1) := by
  rw [← schur_eq]
  exact negIndex_eq hG D₂₁ _

/-- **(GRH.11)**: `n₀(K) = n₀(𝔖_θ)`. -/
theorem nullity_shifted (hG : (highBlock AH D₂₂ h).PosDef) :
    nullity (shifted AH AL D₂₂ D₂₁ D₁₁ h)
      = nullity ((AL - (h : ℂ) • 1) + restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1) := by
  rw [← schur_eq]
  exact nullity_eq hG D₂₁ _

/-- **(GRH.12)**: the stable atom creates no negative direction (`K ⪰ 0`) exactly when
`𝓡_θ ⪰ L (hP - A₊) L`. -/
theorem no_negative_direction_iff (hG : (highBlock AH D₂₂ h).PosDef) (hAL : AL.IsHermitian)
    (hD11 : D₁₁.IsHermitian) :
    (shifted AH AL D₂₂ D₂₁ D₁₁ h).PosSemidef ↔
      (restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1 - ((h : ℂ) • 1 - AL)).PosSemidef := by
  have hherm : (AL + D₁₁ - (h : ℂ) • 1).IsHermitian := by
    have h1 : ((h : ℂ) • (1 : Matrix p p ℂ)).IsHermitian := by
      change ((h : ℂ) • (1 : Matrix p p ℂ))ᴴ = _
      rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
    exact (hAL.add hD11).sub h1
  unfold shifted
  rw [posSemidef_block_iff hG.posSemidef D₂₁ _ hherm]
  have hrange := range_condition_of_posDef hG D₂₁
  have e : AL + D₁₁ - (h : ℂ) • 1 - D₂₁ᴴ * pinv hG.posSemidef.1 * D₂₁
      = restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1 - ((h : ℂ) • 1 - AL) := by
    unfold restoringShort; abel
  rw [e]
  exact ⟨fun hh => hh.2, fun hh => ⟨hrange, hh⟩⟩

end grh

/-! ### The harmonic row selector (GRH.13) -/

section selector

variable (AH : Matrix m m ℂ) (AL : Matrix p p ℂ) (D₂₂ : Matrix m m ℂ) (D₂₁ : Matrix m p ℂ)
  (D₁₁ : Matrix p p ℂ) (h : ℝ)

theorem rayleigh_fromBlocks_diag (X : Matrix m m ℂ) (Y : Matrix p p ℂ) (y : m → ℂ)
    (x : p → ℂ) :
    rayleigh (fromBlocks X 0 0 Y) (Sum.elim y x) = rayleigh X y + rayleigh Y x := by
  unfold rayleigh
  rw [fromBlocks_mulVec, star_sum_elim, dotProduct_sum_elim]
  simp [Complex.add_re]

theorem rayleigh_one_sum_elim (y : m → ℂ) (x : p → ℂ) :
    rayleigh (1 : Matrix (m ⊕ p) (m ⊕ p) ℂ) (Sum.elim y x) = rayleigh 1 y + rayleigh 1 x := by
  rw [← fromBlocks_one, rayleigh_fromBlocks_diag]

include AL in
/-- **(GRH.13)**: for the harmonic lift `ℋ_θ x = (Q_θ x, x)` with `Q_θ = -(H K H)⁻¹ H D L`,
`⟨x, 𝓡_θ x⟩ = ⟨ℋ_θ x, D ℋ_θ x⟩ + ⟨Q_θ x, H (A₊ - hP) H Q_θ x⟩`. -/
theorem restoringShort_rows (hG : (highBlock AH D₂₂ h).PosDef) (x : p → ℂ) :
    rayleigh (restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1) x
      = rayleigh (coupling D₂₂ D₂₁ D₁₁) (harmonicExt hG D₂₁ x)
        + rayleigh (AH - (h : ℂ) • 1) (-(pinv hG.1 *ᵥ (D₂₁ *ᵥ x))) := by
  have hK := rayleigh_harmonicExt hG D₂₁ (AL + D₁₁ - (h : ℂ) • 1) x
  change rayleigh (shifted AH AL D₂₂ D₂₁ D₁₁ h) _ = _ at hK
  rw [schur_eq, rayleigh_add, shifted_eq, rayleigh_sub, rayleigh_add, rayleigh_smul] at hK
  rw [harmonicExt_apply] at hK ⊢
  unfold oldForm at hK
  rw [rayleigh_fromBlocks_diag, rayleigh_one_sum_elim, rayleigh_sub, rayleigh_smul] at hK
  rw [rayleigh_sub, rayleigh_smul]
  linarith

/-- Weighted pigeonhole: if four nonnegative rows sum to less than `d`, one of them is
below its assigned share. -/
theorem four_row_pigeonhole (r α : Fin 4 → ℝ) (hα : ∑ j, α j = 1) {d : ℝ}
    (hlt : ∑ j, r j < d) : ∃ j, r j < α j * d := by
  by_contra hcon
  push Not at hcon
  have : d ≤ ∑ j, r j := by
    calc d = ∑ j, α j * d := by rw [← Finset.sum_mul, hα, one_mul]
      _ ≤ ∑ j, r j := Finset.sum_le_sum fun j _ => hcon j
  linarith

/-- **Row selector**: with `D = C₁ + C₂ + C₃` (translated-test, taper-boundary,
stable-return rows) and the high-relaxation row, a negative Schur witness `x` makes at
least one of the four nonnegative rows smaller than its assigned share of
`d_θ(x) = ⟨x, L (hP - A₊) L x⟩`. -/
theorem row_selector (hG : (highBlock AH D₂₂ h).PosDef) (C₁ C₂ C₃ : Matrix (m ⊕ p) (m ⊕ p) ℂ)
    (hC : coupling D₂₂ D₂₁ D₁₁ = C₁ + C₂ + C₃) (x : p → ℂ)
    (hneg : rayleigh ((AL - (h : ℂ) • 1) + restoringShort AH D₂₂ D₂₁ D₁₁ h hG.1) x < 0)
    (α : Fin 4 → ℝ) (hα : ∑ j, α j = 1) :
    let z := harmonicExt hG D₂₁ x
    let rows : Fin 4 → ℝ := ![rayleigh C₁ z, rayleigh C₂ z, rayleigh C₃ z,
      rayleigh (AH - (h : ℂ) • 1) (-(pinv hG.1 *ᵥ (D₂₁ *ᵥ x)))]
    ∃ j, rows j < α j * rayleigh ((h : ℂ) • 1 - AL) x := by
  intro z rows
  apply four_row_pigeonhole rows α hα
  have hrows := restoringShort_rows AH AL D₂₂ D₂₁ D₁₁ h hG x
  rw [hC, rayleigh_add, rayleigh_add] at hrows
  rw [rayleigh_add] at hneg
  have hd : rayleigh ((h : ℂ) • 1 - AL) x = -rayleigh (AL - (h : ℂ) • 1) x := by
    rw [rayleigh_sub, rayleigh_sub]; ring
  have hsum : ∑ j, rows j = rayleigh C₁ z + rayleigh C₂ z + rayleigh C₃ z
      + rayleigh (AH - (h : ℂ) • 1) (-(pinv hG.1 *ᵥ (D₂₁ *ᵥ x))) := by
    simp [rows, Fin.sum_univ_four]
  rw [hsum, hd]
  linarith

end selector

end GRHRestoringShort
end NCG
