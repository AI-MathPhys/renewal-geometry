/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.ChoiCriterion
/-!
# Kraus decompositions of completely positive matrix maps

Reusable infrastructure for `prop:ncg-compression-defect` and `lem:ncg-rank-one-forcing`
(predictive spectral geometry).  `RenewalGeometry.choi_criterion` characterises complete
positivity (`IsMatrixCompletelyPositive`, all identity ampliations positive) by positivity
of the Choi matrix; here we export the Kraus form.

* `MatrixKraus.exists_eq_conjTranspose_mul_self`: every PSD matrix is `Xᴴ X`;
* `MatrixKraus.krausMap W`: the linear map `X ↦ ∑ₐ Wₐ X Wₐᴴ` (any finite index types);
* `MatrixKraus.exists_kraus_of_completelyPositive`: a CP map `M_n → M_m` has a Kraus family
  indexed by `Fin n × Fin m`;
* `MatrixKraus.krausMap_completelyPositive`: Kraus maps are CP;
* `MatrixKraus.completelyPositive_iff_exists_kraus`: the two notions agree;
* `MatrixKraus.krausMap_posSemidef`, `MatrixKraus.trace_krausMap`: positivity and the trace
  identity `Tr Φ(X) = Tr((∑ Wᴴ W) X)`;
* `MatrixKraus.hsInner` (`⟪A, B⟫ = Tr(Aᴴ B)`), `MatrixKraus.hsInner_left_eq_iff`,
  `MatrixKraus.hsInner_krausMap`, `MatrixKraus.eq_krausMap_conjTranspose_of_hsAdjoint`: the
  Hilbert–Schmidt adjoint of `X ↦ ∑ Wₐ X Wₐᴴ` is (uniquely) `Y ↦ ∑ Wₐᴴ Y Wₐ`.
-/

namespace RenewalGeometry
namespace MatrixKraus

open Matrix
open scoped ComplexOrder MatrixOrder

/-- Every positive semidefinite complex matrix factors as `Xᴴ X`. -/
theorem exists_eq_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : ∃ X : Matrix ι ι ℂ, A = Xᴴ * X := by
  obtain ⟨X, hX, -, hXX⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hA.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
  refine ⟨X, ?_⟩
  have h : Xᴴ = X := hX
  rw [h, hXX]

/-- The Kraus map `X ↦ ∑ₐ Wₐ X Wₐᴴ` as a linear map. -/
noncomputable def krausMap {p q κ : Type*} [Fintype p] [Fintype κ]
    (W : κ → Matrix q p ℂ) : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ where
  toFun X := ∑ a, W a * X * (W a)ᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem krausMap_apply {p q κ : Type*} [Fintype p] [Fintype κ] (W : κ → Matrix q p ℂ)
    (X : Matrix p p ℂ) : krausMap W X = ∑ a, W a * X * (W a)ᴴ := rfl

/-- Kraus maps are positive. -/
theorem krausMap_posSemidef {p q κ : Type*} [Fintype p] [Fintype q] [Fintype κ]
    (W : κ → Matrix q p ℂ) {X : Matrix p p ℂ} (hX : X.PosSemidef) :
    (krausMap W X).PosSemidef := by
  rw [krausMap_apply]
  exact Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) PosSemidef.zero
    fun a _ => hX.mul_mul_conjTranspose_same (W a)

/-- The trace identity `Tr(∑ₐ Wₐ X Wₐᴴ) = Tr((∑ₐ Wₐᴴ Wₐ) X)`. -/
theorem trace_krausMap {p q κ : Type*} [Fintype p] [Fintype q] [Fintype κ]
    (W : κ → Matrix q p ℂ) (X : Matrix p p ℂ) :
    (krausMap W X).trace = ((∑ a, (W a)ᴴ * W a) * X).trace := by
  rw [krausMap_apply, trace_sum, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, trace_mul_comm]

variable {n m : ℕ}

/-- **Kraus decomposition** of a completely positive map `M_n(ℂ) → M_m(ℂ)`
(the backward half of the Choi–Kraus theorem, exported): there are `n·m` Kraus operators
`W_α : ℂⁿ → ℂᵐ` with `Φ(X) = ∑_α W_α X W_αᴴ`. -/
theorem exists_kraus_of_completelyPositive
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsMatrixCompletelyPositive Φ) :
    ∃ W : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ, ∀ X, Φ X = ∑ a, W a * X * (W a)ᴴ := by
  classical
  obtain ⟨S, hS⟩ := exists_eq_conjTranspose_mul_self (choiMatrix_posSemidef_of_cp hΦ)
  set W : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ :=
    fun α => Matrix.of fun k i => star (S α (i, k)) with hW
  have hCdecomp : ∀ (i j : Fin n) (k l : Fin m),
      Φ (Matrix.single i j 1) k l = ∑ α, W α k i * star (W α l j) := by
    intro i j k l
    have h3 : Φ (Matrix.single i j 1) k l = choiMatrix Φ (i, k) (j, l) := by
      simp [choiMatrix]
    rw [h3, hS, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp [hW, conjTranspose_apply]
  refine ⟨W, fun X => ?_⟩
  ext k l
  have hL : Φ X k l = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) k l := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    rw [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    rw [map_smul, Matrix.smul_apply, smul_eq_mul]
  have hL2 : (∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) k l)
      = ∑ i, ∑ j, ∑ α, W α k i * X i j * star (W α l j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hCdecomp i j k l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hswap : (∑ i, ∑ j, ∑ α, W α k i * X i j * star (W α l j))
      = ∑ α, ∑ i, ∑ j, W α k i * X i j * star (W α l j) := by
    rw [show (∑ i, ∑ j, ∑ α : Fin n × Fin m, W α k i * X i j * star (W α l j))
        = ∑ i, ∑ α : Fin n × Fin m, ∑ j, W α k i * X i j * star (W α l j) from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_comm
  have hR : (∑ α, W α * X * (W α)ᴴ) k l
      = ∑ α, ∑ i, ∑ j, W α k i * X i j * star (W α l j) := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Matrix.mul_apply]
    have h9 : ∀ b, (W α * X) k b * (W α)ᴴ b l = ∑ i, W α k i * X i b * star (W α l b) := by
      intro b
      rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun b _ => h9 b]
    exact Finset.sum_comm
  rw [hL, hL2, hswap, hR]

/-- Kraus maps are completely positive (their Choi matrix is a Gram matrix). -/
theorem krausMap_completelyPositive {κ : Type*} [Fintype κ]
    (W : κ → Matrix (Fin m) (Fin n) ℂ) : IsMatrixCompletelyPositive (krausMap W) := by
  classical
  apply cp_of_choiMatrix_posSemidef
  set Y : Matrix κ (Fin n × Fin m) ℂ := Matrix.of fun α p => star (W α p.2 p.1) with hY
  have hC : choiMatrix (krausMap W) = Yᴴ * Y := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [choiMatrix, Matrix.of_apply, krausMap_apply, Matrix.sum_apply,
      Matrix.mul_apply, conjTranspose_apply, hY, star_star]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp [single_apply]
      · intro b _ hb; simp [single_apply, Ne.symm hb]
      · simp
    · intro b _ hb
      rw [Finset.sum_eq_zero]
      · simp
      · intro c _; simp [single_apply]; intro _ h; exact absurd h.symm hb
    · simp
  rw [hC]
  exact posSemidef_conjTranspose_mul_self Y

/-- **Choi–Kraus**: a linear map of matrix algebras is completely positive iff it is a
Kraus map (with `n·m` Kraus operators). -/
theorem completelyPositive_iff_exists_kraus
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    IsMatrixCompletelyPositive Φ ↔
      ∃ W : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ, Φ = krausMap W := by
  constructor
  · intro hΦ
    obtain ⟨W, hW⟩ := exists_kraus_of_completelyPositive hΦ
    exact ⟨W, LinearMap.ext fun X => (hW X).trans (krausMap_apply W X).symm⟩
  · rintro ⟨W, rfl⟩
    exact krausMap_completelyPositive W

/-! ### Hilbert–Schmidt adjoints of Kraus maps -/

/-- The Hilbert–Schmidt inner product `⟪A, B⟫ = Tr(Aᴴ B)`. -/
def hsInner {p q : Type*} [Fintype p] [Fintype q] (A B : Matrix p q ℂ) : ℂ :=
  (Aᴴ * B).trace

/-- The Hilbert–Schmidt inner product is nondegenerate in its first slot. -/
theorem hsInner_left_eq_iff {p q : Type*} [Fintype p] [Fintype q] {A B : Matrix p q ℂ} :
    (∀ X, hsInner A X = hsInner B X) ↔ A = B := by
  refine ⟨fun h => ?_, fun h _ => h ▸ rfl⟩
  have h1 := h (A - B)
  have h2 : ((A - B)ᴴ * (A - B)).trace = 0 := by
    rw [conjTranspose_sub, Matrix.sub_mul, trace_sub]
    simp only [hsInner] at h1
    rw [h1, sub_self]
  exact sub_eq_zero.1 (trace_conjTranspose_mul_self_eq_zero_iff.1 h2)

/-- The Hilbert–Schmidt adjoint of a Kraus map is the Kraus map of the adjoint operators:
`⟪Y, ∑ Wₐ X Wₐᴴ⟫ = ⟪∑ Wₐᴴ Y Wₐ, X⟫`. -/
theorem hsInner_krausMap {p q κ : Type*} [Fintype p] [Fintype q] [Fintype κ]
    (W : κ → Matrix q p ℂ) (X : Matrix p p ℂ) (Y : Matrix q q ℂ) :
    hsInner Y (krausMap W X) = hsInner (krausMap (fun a => (W a)ᴴ) Y) X := by
  simp only [hsInner, krausMap_apply, conjTranspose_sum, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_sum, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

/-- Uniqueness: any Hilbert–Schmidt adjoint of a Kraus map equals the adjoint Kraus map. -/
theorem eq_krausMap_conjTranspose_of_hsAdjoint {p q κ : Type*} [Fintype p] [Fintype q]
    [Fintype κ] (W : κ → Matrix q p ℂ) (Ψ : Matrix q q ℂ →ₗ[ℂ] Matrix p p ℂ)
    (hΨ : ∀ X Y, hsInner Y (krausMap W X) = hsInner (Ψ Y) X) :
    Ψ = krausMap (fun a => (W a)ᴴ) := by
  ext1 Y
  exact hsInner_left_eq_iff.1 fun X => (hΨ X Y).symm.trans (hsInner_krausMap W X Y)

end MatrixKraus
end RenewalGeometry
