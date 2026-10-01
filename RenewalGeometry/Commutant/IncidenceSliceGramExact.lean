/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IntrinsicCoefficientQuiver

/-!
# Slice Gram and operator–Schmidt spectrum (`prop:incidence-slice-Gram`)

For one represented incidence `Y ∈ B(K_s, K_t) ⊗ B(M_s, M_t)`, written as a matrix
`Y : Matrix (K_t × M_t) (K_s × M_s) ℂ`, the slice map
`𝒮_Y(D̄) = (φ_D ⊗ id)(Y)`, `φ_D(A) = Tr(D^* A)`, is a linear map `B(K_s,K_t) → B(M_s,M_t)`.
Both operator spaces carry their Hilbert–Schmidt products; in the Hilbert–Schmidt orthonormal
coordinates given by the matrix units (`vecEquiv`, `X ↦ (X_{ij})_{(i,j)}`) the slice map is the
**realignment** matrix `realign Y`, `(realign Y)_{(n,m),(i,j)} = Y_{(i,n),(j,m)}`
(`vec_functionalSlice_hsFunctional`), its Hilbert–Schmidt adjoint is the conjugate transpose, and
the slice Gram is `H_Y = 𝒮_Y 𝒮_Y^* = realign Y * (realign Y)ᴴ` (`sliceGram`).

* `sliceGram_posSemidef`: `H_Y ⪰ 0`;
* `range_sliceGram_eq_range_realign`, `range_realign_eq_sliceSpace`:
  `Ran H_Y = Ran 𝒮_Y = 𝔅_Y` (`eq:incidence-slice-Gram-range`), with `𝔅_Y` the intrinsic
  coefficient space `{(φ ⊗ id)(Y) : φ}`;
* `sliceGram_mulVec_schmidt`, `rank_sliceGram_schmidt`, `trace_sliceGram`,
  `trace_sliceGram_schmidt`: for an operator–Schmidt decomposition
  `Y = ∑_k σ_k D_k ⊗ F_k` with Hilbert–Schmidt orthonormal families `(D_k)`, `(F_k)` and real
  nonzero `σ_k`: `H_Y F_k = σ_k² F_k`, `rank H_Y = r`, `Tr H_Y = ‖Y‖²_HS = ∑ σ_k²`
  (`eq:incidence-slice-Gram-spectrum`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace IncidenceSliceGram

open SMSTQuiverCommutantAssembly

set_option linter.unusedSectionVars false

variable {Kt Ks Mt Ms : Type*} [Fintype Kt] [Fintype Ks] [Fintype Mt] [Fintype Ms]
  [DecidableEq Kt] [DecidableEq Ks] [DecidableEq Mt] [DecidableEq Ms]

/-- The Hilbert–Schmidt inner product `⟪A, B⟫ = Tr(A^* B) = ∑_{ij} conj(A_ij) B_ij`. -/
def hsInner {a b : Type*} [Fintype a] [Fintype b] (A B : Matrix a b ℂ) : ℂ :=
  ∑ i, ∑ j, star (A i j) * B i j

/-- The functional `φ_D(A) = Tr(D^* A)` on `B(K_s, K_t)`. -/
def hsFunctional (D : Matrix Kt Ks ℂ) : Matrix Kt Ks ℂ →ₗ[ℂ] ℂ where
  toFun A := hsInner D A
  map_add' A B := by
    simp only [hsInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [hsInner, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Hilbert–Schmidt orthonormal coordinates: `X ↦ (X_{ij})_{(i,j)}`. -/
def vecEquiv {a b : Type*} : Matrix a b ℂ ≃ₗ[ℂ] (a × b → ℂ) where
  toFun X p := X p.1 p.2
  invFun v := Matrix.of fun i j => v (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem vecEquiv_apply {a b : Type*} (X : Matrix a b ℂ) (p : a × b) :
    vecEquiv X p = X p.1 p.2 := rfl

@[simp] theorem vecEquiv_symm_apply {a b : Type*} (v : a × b → ℂ) (i : a) (j : b) :
    vecEquiv.symm v i j = v (i, j) := rfl

/-- The intrinsic coefficient space `𝔅_Y = {(φ ⊗ id)(Y) : φ ∈ B(K_s, K_t)^*}`. -/
def sliceSpace (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : Submodule ℂ (Matrix Mt Ms ℂ) :=
  LinearMap.range (sliceLinearMap Y)

/-- The realignment of `Y`: the matrix of the slice map `𝒮_Y` in Hilbert–Schmidt orthonormal
coordinates. -/
def realign (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : Matrix (Mt × Ms) (Kt × Ks) ℂ :=
  Matrix.of fun p q => Y (q.1, p.1) (q.2, p.2)

/-- The slice Gram `H_Y = 𝒮_Y 𝒮_Y^*` in Hilbert–Schmidt orthonormal coordinates. -/
def sliceGram (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : Matrix (Mt × Ms) (Mt × Ms) ℂ :=
  realign Y * (realign Y)ᴴ

/-- **`𝒮_Y(D̄) = (φ_D ⊗ id)(Y)`**: the realignment applied to the coordinates of `D̄` is the
functional slice of `Y` along `φ_D = Tr(D^* ·)`. -/
theorem vec_functionalSlice_hsFunctional (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ)
    (D : Matrix Kt Ks ℂ) :
    vecEquiv (functionalSlice (hsFunctional D) Y) = realign Y *ᵥ vecEquiv (D.map star) := by
  funext p
  simp only [vecEquiv_apply, functionalSlice, hsFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    hsInner, realign, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.map_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `H_Y ⪰ 0`. -/
theorem sliceGram_posSemidef (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) : (sliceGram Y).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- `Ran 𝒮_Y = 𝔅_Y`: the range of the realignment is the intrinsic coefficient space (in
Hilbert–Schmidt coordinates). -/
theorem range_realign_eq_sliceSpace (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    LinearMap.range (realign Y).mulVecLin = (sliceSpace Y).map vecEquiv.toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨functionalSlice (hsFunctional ((vecEquiv.symm v).map star)) Y,
      ⟨hsFunctional ((vecEquiv.symm v).map star), rfl⟩, ?_⟩
    show vecEquiv (functionalSlice (hsFunctional ((vecEquiv.symm v).map star)) Y) = _
    rw [vec_functionalSlice_hsFunctional]
    congr 1
    funext q
    simp only [vecEquiv_apply, Matrix.map_apply, vecEquiv_symm_apply, star_star]
  · rintro _ ⟨B, ⟨φ, rfl⟩, rfl⟩
    -- every functional is `φ_D` for `D_ij = conj(φ(E_ij))`
    set D : Matrix Kt Ks ℂ := Matrix.of fun i j => star (φ (Matrix.single i j 1)) with hD
    have hφ : φ = hsFunctional D := by
      apply LinearMap.ext
      intro A
      conv_lhs => rw [Matrix.matrix_eq_sum_single A]
      simp only [map_sum, hsFunctional, LinearMap.coe_mk, AddHom.coe_mk, hsInner, hD,
        Matrix.of_apply, star_star]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul, mul_comm]
    refine ⟨vecEquiv (D.map star), ?_⟩
    show realign Y *ᵥ vecEquiv (D.map star) = vecEquiv (sliceLinearMap Y φ)
    rw [sliceLinearMap_apply, hφ, vec_functionalSlice_hsFunctional]

/-- **`Ran H_Y = Ran 𝒮_Y`** (`eq:incidence-slice-Gram-range`, first equality). -/
theorem range_sliceGram_eq_range_realign (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    LinearMap.range (sliceGram Y).mulVecLin = LinearMap.range (realign Y).mulVecLin := by
  have hle : LinearMap.range (sliceGram Y).mulVecLin ≤ LinearMap.range (realign Y).mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(realign Y)ᴴ *ᵥ v, ?_⟩
    simp [sliceGram, Matrix.mulVec_mulVec]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have h := Matrix.rank_self_mul_conjTranspose (realign Y)
  unfold Matrix.rank at h
  exact h

/-- **`eq:incidence-slice-Gram-range`**: `Ran H_Y = Ran 𝒮_Y = 𝔅_Y`. -/
theorem incidence_slice_Gram_range (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    LinearMap.range (sliceGram Y).mulVecLin = LinearMap.range (realign Y).mulVecLin ∧
      LinearMap.range (realign Y).mulVecLin = (sliceSpace Y).map vecEquiv.toLinearMap :=
  ⟨range_sliceGram_eq_range_realign Y, range_realign_eq_sliceSpace Y⟩

/-- `rank H_Y = dim 𝔅_Y`. -/
theorem rank_sliceGram_eq_finrank (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    (sliceGram Y).rank = Module.finrank ℂ (sliceSpace Y) := by
  unfold Matrix.rank
  rw [range_sliceGram_eq_range_realign, range_realign_eq_sliceSpace]
  exact LinearEquiv.finrank_map_eq _ _

/-! ### The trace -/

/-- **`Tr H_Y = ‖Y‖²_HS`.** -/
theorem trace_sliceGram (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    (sliceGram Y).trace = ((∑ a, ∑ b, Complex.normSq (Y a b) : ℝ) : ℂ) := by
  have hz : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => by
    rw [Complex.star_def, Complex.mul_conj]
  simp only [Matrix.trace, Matrix.diag, sliceGram, Matrix.mul_apply, conjTranspose_apply, hz,
    realign, Matrix.of_apply, Complex.ofReal_sum]
  rw [← Fintype.sum_prod_type' (f := fun (p : Mt × Ms) (q : Kt × Ks) =>
      (Complex.normSq (Y (q.1, p.1) (q.2, p.2)) : ℂ)),
    ← Fintype.sum_prod_type' (f := fun (a : Kt × Mt) (b : Ks × Ms) =>
      (Complex.normSq (Y a b) : ℂ))]
  let e : (Mt × Ms) × (Kt × Ks) ≃ (Kt × Mt) × (Ks × Ms) :=
    { toFun := fun x => ((x.2.1, x.1.1), (x.2.2, x.1.2))
      invFun := fun y => ((y.1.2, y.2.2), (y.1.1, y.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-! ### Operator–Schmidt spectrum -/

section Schmidt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entries of `H_Y` for `Y = ∑_k σ_k D_k ⊗ F_k` with Hilbert–Schmidt orthonormal `(D_k)`. -/
theorem sliceGram_apply_schmidt (σ : ι → ℝ) (D : ι → Matrix Kt Ks ℂ) (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (p p' : Mt × Ms) :
    sliceGram (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k)) p p' =
      ∑ k, ((σ k : ℂ) ^ 2) * F k p.1 p.2 * star (F k p'.1 p'.2) := by
  have hR : ∀ q : Kt × Ks, realign (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k)) p q =
      ∑ k, (σ k : ℂ) * D k q.1 q.2 * F k p.1 p.2 := by
    intro q
    simp [realign, Matrix.sum_apply, kroneckerMap_apply, mul_assoc]
  have hR' : ∀ q : Kt × Ks, realign (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k)) p' q =
      ∑ k, (σ k : ℂ) * D k q.1 q.2 * F k p'.1 p'.2 := by
    intro q
    simp [realign, Matrix.sum_apply, kroneckerMap_apply, mul_assoc]
  simp only [sliceGram, Matrix.mul_apply, conjTranspose_apply, hR, hR', star_sum, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hk : ∀ y, ∑ x : Kt × Ks, (σ y : ℂ) * D y x.1 x.2 * F y p.1 p.2 *
      ((σ k : ℂ) * (starRingEnd ℂ) (D k x.1 x.2) * (starRingEnd ℂ) (F k p'.1 p'.2)) =
      (σ y : ℂ) * F y p.1 p.2 * (σ k : ℂ) * (starRingEnd ℂ) (F k p'.1 p'.2) *
        hsInner (D k) (D y) := by
    intro y
    unfold hsInner
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.star_def]
    ring
  simp only [hk, hD]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true, mul_one]
    ring
  · intro l _ hl
    rw [if_neg (Ne.symm hl), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`H_Y F_k = σ_k² F_k`** (`eq:incidence-slice-Gram-spectrum`). -/
theorem sliceGram_mulVec_schmidt (σ : ι → ℝ) (D : ι → Matrix Kt Ks ℂ) (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) (k : ι) :
    sliceGram (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k)) *ᵥ vecEquiv (F k) =
      ((σ k : ℂ) ^ 2) • vecEquiv (F k) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, sliceGram_apply_schmidt σ D F hD, Pi.smul_apply,
    smul_eq_mul, vecEquiv_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hl : ∀ l, ∑ q : Mt × Ms, (σ l : ℂ) ^ 2 * F l p.1 p.2 * star (F l q.1 q.2) * F k q.1 q.2 =
      (σ l : ℂ) ^ 2 * F l p.1 p.2 * hsInner (F l) (F k) := by
    intro l
    simp only [hsInner, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hl, hF]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    rw [if_neg hlk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Hilbert–Schmidt orthonormal families are linearly independent (in coordinates). -/
theorem linearIndependent_vec_of_orthonormal (F : ι → Matrix Mt Ms ℂ)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) :
    LinearIndependent ℂ (fun k => vecEquiv (F k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  have h := congrArg (fun v : Mt × Ms → ℂ => ∑ q, star (F l q.1 q.2) * v q) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, vecEquiv_apply] at h
  have h2 : ∀ k, ∑ q : Mt × Ms, star (F l q.1 q.2) * (c k * F k q.1 q.2) =
      c k * hsInner (F l) (F k) := by
    intro k
    simp only [hsInner, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simp only [h2, hF] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro k _ hk
    rw [if_neg (Ne.symm hk), mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- **`rank H_Y = r`** (`eq:incidence-slice-Gram-spectrum`) for an operator–Schmidt
decomposition with nonzero Schmidt coefficients. -/
theorem rank_sliceGram_schmidt (σ : ι → ℝ) (hσ : ∀ k, σ k ≠ 0) (D : ι → Matrix Kt Ks ℂ)
    (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) :
    (sliceGram (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k))).rank = Fintype.card ι := by
  set Y := ∑ k, (σ k : ℂ) • (D k ⊗ₖ F k) with hY
  have hrange : LinearMap.range (sliceGram Y).mulVecLin =
      Submodule.span ℂ (Set.range fun k => vecEquiv (F k)) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hv : (sliceGram Y).mulVecLin v =
          ∑ k, (((σ k : ℂ) ^ 2) * ∑ q : Mt × Ms, star (F k q.1 q.2) * v q) •
            vecEquiv (F k) := by
        funext p
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hY,
          sliceGram_apply_schmidt σ D F hD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          vecEquiv_apply, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q _ => ?_
        ring
      rw [hv]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine ⟨(((σ k : ℂ) ^ 2)⁻¹) • vecEquiv (F k), ?_⟩
      have hσ2 : ((σ k : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hσ k))
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hY,
        sliceGram_mulVec_schmidt σ D F hD hF k, smul_smul, inv_mul_cancel₀ hσ2, one_smul]
  unfold Matrix.rank
  rw [hrange, finrank_span_eq_card (linearIndependent_vec_of_orthonormal F hF)]

/-- **`Tr H_Y = ∑_k σ_k²`** for an operator–Schmidt decomposition. -/
theorem trace_sliceGram_schmidt (σ : ι → ℝ) (D : ι → Matrix Kt Ks ℂ) (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) :
    (sliceGram (∑ k, (σ k : ℂ) • (D k ⊗ₖ F k))).trace = ∑ k, ((σ k : ℂ) ^ 2) := by
  simp only [Matrix.trace, Matrix.diag, sliceGram_apply_schmidt σ D F hD]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : ∑ i, ∑ j, star (F k i j) * F k i j = 1 := by
    have := hF k k
    simpa [hsInner] using this
  calc ∑ p : Mt × Ms, (σ k : ℂ) ^ 2 * F k p.1 p.2 * star (F k p.1 p.2)
      = (σ k : ℂ) ^ 2 * ∑ p : Mt × Ms, star (F k p.1 p.2) * F k p.1 p.2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ = (σ k : ℂ) ^ 2 := by rw [Fintype.sum_prod_type, h, mul_one]

/-- **`prop:incidence-slice-Gram`, assembled.**  `H_Y ⪰ 0`, `Ran H_Y = Ran 𝒮_Y = 𝔅_Y`,
`Tr H_Y = ‖Y‖²_HS`; and for an operator–Schmidt decomposition `Y = ∑_k σ_k D_k ⊗ F_k`
(Hilbert–Schmidt orthonormal coefficient families, real nonzero `σ_k`), `H_Y F_k = σ_k² F_k`,
`rank H_Y = r` and `Tr H_Y = ∑_k σ_k²`. -/
theorem incidence_slice_Gram (σ : ι → ℝ) (hσ : ∀ k, σ k ≠ 0) (D : ι → Matrix Kt Ks ℂ)
    (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) :
    let Y := ∑ k, (σ k : ℂ) • (D k ⊗ₖ F k)
    (sliceGram Y).PosSemidef ∧
      LinearMap.range (sliceGram Y).mulVecLin = LinearMap.range (realign Y).mulVecLin ∧
      LinearMap.range (realign Y).mulVecLin = (sliceSpace Y).map vecEquiv.toLinearMap ∧
      (∀ k, sliceGram Y *ᵥ vecEquiv (F k) = ((σ k : ℂ) ^ 2) • vecEquiv (F k)) ∧
      (sliceGram Y).rank = Fintype.card ι ∧
      (sliceGram Y).trace = ((∑ a, ∑ b, Complex.normSq (Y a b) : ℝ) : ℂ) ∧
      (sliceGram Y).trace = ∑ k, ((σ k : ℂ) ^ 2) :=
  ⟨sliceGram_posSemidef _, range_sliceGram_eq_range_realign _, range_realign_eq_sliceSpace _,
    sliceGram_mulVec_schmidt σ D F hD hF, rank_sliceGram_schmidt σ hσ D F hD hF,
    trace_sliceGram _, trace_sliceGram_schmidt σ D F hD hF⟩

end Schmidt

end IncidenceSliceGram
end RenewalGeometry
