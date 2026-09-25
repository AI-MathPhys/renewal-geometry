/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.SourceKernelMinimalUniqueness

/-!
# Joint Gram classification of minimal joint realizations

Paper `predictive_spectral_geometry`, label `thm:supp-common-source`.

The retained marginal realization spaces are `E_a = ℂ^{n a}` (`a : ι`), with
total index `X = Σ a, n a`.  A block correlation operator is a matrix
`K : Matrix X X ℂ`; `block K a b` is its `(a, b)` block.

* `CorrelationSpectrahedron` is `Corr_X = {K ⪰ 0, K_aa = I}`
  (`eq:supp-correlation-spectrahedron`).
* `GaugeGroup n = Π_a U(E_a)` acts by block congruence `K ↦ D(g)ᴴ K D(g)`
  (`gaugeAct`), preserving `Corr_X` (`gaugeAct_mem_corr`); `stabilizer K` is
  the subgroup `Stab_{𝒢_X}(K)`.
* A joint realization of `K` on a common space `ℂ^C` is a matrix
  `S : Matrix C X ℂ` with Gram `Sᴴ S = K` (the columns over block `a` are the
  images of the marginal basis of `E_a`); its realization space is `Ran S`.
* `thm:supp-common-source`:
  - `gram_mem_corr_iff`: the Gram of a joint realization lies in `Corr_X`
    exactly when the marginal blocks are identities;
  - `exists_realization_of_mem_corr`: every point of `Corr_X` is realized;
  - `finrank_range_eq_rank`, `rank_le_card_of_realization`: the minimal
    realization (restriction to `Ran S`) has dimension `rank K`, which is the
    minimum possible joint realization dimension;
  - `frameUnitaryEquivalent_iff`: two joint realizations are equivalent up to
    a marginal frame change and a source-fixing unitary on the common spaces
    iff their Grams lie in the same `𝒢_X`-orbit — the classification by
    `Corr_X / 𝒢_X` (with the unitary unique, `exists_unique_range_unitary`);
  - `mem_stabilizer_iff_residual`: the residual gauge group of a
    representative `K` is exactly `Stab_{𝒢_X}(K)`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry
namespace JointGram

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → Type}
  [∀ a, Fintype (n a)] [∀ a, DecidableEq (n a)]

/-- The `(a, b)` block of a block operator on `Σ a, n a`. -/
def block (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) (a b : ι) : Matrix (n a) (n b) ℂ :=
  fun i j => K ⟨a, i⟩ ⟨b, j⟩

@[simp] theorem block_apply (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) (a b : ι) (i : n a) (j : n b) :
    block K a b i j = K ⟨a, i⟩ ⟨b, j⟩ := rfl

/-- **`eq:supp-correlation-spectrahedron`.**  The correlation spectrahedron
`Corr_X`: positive block operators with identity diagonal blocks. -/
def CorrelationSpectrahedron : Set (Matrix (Σ a, n a) (Σ a, n a) ℂ) :=
  {K | K.PosSemidef ∧ ∀ a, block K a a = 1}

/-- The gauge group `𝒢_X = Π_a U(E_a)` of the marginal realization spaces. -/
abbrev GaugeGroup (n : ι → Type) [∀ a, Fintype (n a)] [∀ a, DecidableEq (n a)] :=
  ∀ a, Matrix.unitaryGroup (n a) ℂ

/-- The block-diagonal matrix of a gauge element. -/
def gaugeMatrix (g : GaugeGroup n) : Matrix (Σ a, n a) (Σ a, n a) ℂ :=
  blockDiagonal' fun a => (g a : Matrix (n a) (n a) ℂ)

/-- The block congruence action `K ↦ D(g)ᴴ K D(g)` of the gauge group. -/
def gaugeAct (g : GaugeGroup n) (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) :
    Matrix (Σ a, n a) (Σ a, n a) ℂ :=
  (gaugeMatrix g)ᴴ * K * gaugeMatrix g

theorem gaugeMatrix_mul (g h : GaugeGroup n) :
    gaugeMatrix (g * h) = gaugeMatrix g * gaugeMatrix h := by
  simp only [gaugeMatrix, Pi.mul_apply, Submonoid.coe_mul, blockDiagonal'_mul]

theorem gaugeMatrix_one : gaugeMatrix (1 : GaugeGroup n) = 1 := by
  simp only [gaugeMatrix, Pi.one_apply, OneMemClass.coe_one]
  exact blockDiagonal'_one

theorem gaugeMatrix_conjTranspose_mul (g : GaugeGroup n) :
    (gaugeMatrix g)ᴴ * gaugeMatrix g = 1 := by
  simp only [gaugeMatrix, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
  have h : (fun a => ((g a : Matrix (n a) (n a) ℂ))ᴴ * (g a : Matrix (n a) (n a) ℂ)) =
      fun a => (1 : Matrix (n a) (n a) ℂ) := by
    funext a
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self (g a)
  rw [h]
  exact blockDiagonal'_one

theorem gaugeMatrix_mul_conjTranspose (g : GaugeGroup n) :
    gaugeMatrix g * (gaugeMatrix g)ᴴ = 1 := by
  simp only [gaugeMatrix, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
  have h : (fun a => (g a : Matrix (n a) (n a) ℂ) * ((g a : Matrix (n a) (n a) ℂ))ᴴ) =
      fun a => (1 : Matrix (n a) (n a) ℂ) := by
    funext a
    have := Matrix.mem_unitaryGroup_iff.mp (g a).2
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [h]
  exact blockDiagonal'_one

theorem gaugeMatrix_inv (g : GaugeGroup n) : gaugeMatrix g⁻¹ = (gaugeMatrix g)ᴴ := by
  simp only [gaugeMatrix, blockDiagonal'_conjTranspose]
  congr 1

theorem gaugeAct_mul (g h : GaugeGroup n) (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) :
    gaugeAct (g * h) K = gaugeAct h (gaugeAct g K) := by
  simp only [gaugeAct, gaugeMatrix_mul, conjTranspose_mul, Matrix.mul_assoc]

theorem gaugeAct_one (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) : gaugeAct 1 K = K := by
  simp [gaugeAct, gaugeMatrix_one]

/-- Entries of a right product with a block-diagonal gauge matrix. -/
theorem mul_gaugeMatrix_apply {C : Type*} (M : Matrix C (Σ a, n a) ℂ) (g : GaugeGroup n)
    (p : C) (b : ι) (j : n b) :
    (M * gaugeMatrix g) p ⟨b, j⟩ = ∑ l, M p ⟨b, l⟩ * (g b : Matrix (n b) (n b) ℂ) l j := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp [gaugeMatrix]
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro l _
    simp [gaugeMatrix, blockDiagonal'_apply_ne _ _ _ hc]
  · simp

/-- Entries of a left product with the adjoint of a block-diagonal gauge matrix. -/
theorem gaugeMatrix_conjTranspose_mul_apply {C : Type*} (M : Matrix (Σ a, n a) C ℂ)
    (g : GaugeGroup n) (a : ι) (i : n a) (q : C) :
    ((gaugeMatrix g)ᴴ * M) ⟨a, i⟩ q =
      ∑ k, star ((g a : Matrix (n a) (n a) ℂ) k i) * M ⟨a, k⟩ q := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp [gaugeMatrix, conjTranspose_apply]
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro k _
    simp [gaugeMatrix, conjTranspose_apply, blockDiagonal'_apply_ne _ _ _ hc]
  · simp

/-- The gauge action is blockwise congruence: `(g ⋆ K)_{ab} = g_aᴴ K_{ab} g_b`. -/
theorem block_gaugeAct (g : GaugeGroup n) (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) (a b : ι) :
    block (gaugeAct g K) a b =
      ((g a : Matrix (n a) (n a) ℂ))ᴴ * block K a b * (g b : Matrix (n b) (n b) ℂ) := by
  ext i j
  simp only [block_apply, gaugeAct]
  rw [mul_gaugeMatrix_apply]
  conv_rhs => rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [gaugeMatrix_conjTranspose_mul_apply, Matrix.mul_apply]
  simp [conjTranspose_apply, block_apply]

/-- The gauge action preserves `Corr_X`. -/
theorem gaugeAct_mem_corr {K : Matrix (Σ a, n a) (Σ a, n a) ℂ}
    (hK : K ∈ CorrelationSpectrahedron) (g : GaugeGroup n) :
    gaugeAct g K ∈ CorrelationSpectrahedron := by
  refine ⟨hK.1.conjTranspose_mul_mul_same _, fun a => ?_⟩
  rw [block_gaugeAct, hK.2 a, Matrix.mul_one]
  exact Matrix.UnitaryGroup.star_mul_self (g a)

/-- The stabilizer `Stab_{𝒢_X}(K)` of a block operator, as a subgroup. -/
def stabilizer (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) : Subgroup (GaugeGroup n) where
  carrier := {g | gaugeAct g K = K}
  one_mem' := gaugeAct_one K
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [gaugeAct_mul, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hg' : (gaugeMatrix g)ᴴ * K * gaugeMatrix g = K := hg
    show (gaugeMatrix g⁻¹)ᴴ * K * gaugeMatrix g⁻¹ = K
    rw [gaugeMatrix_inv, conjTranspose_conjTranspose]
    calc gaugeMatrix g * K * (gaugeMatrix g)ᴴ
        = gaugeMatrix g * ((gaugeMatrix g)ᴴ * K * gaugeMatrix g) * (gaugeMatrix g)ᴴ := by
          rw [hg']
      _ = (gaugeMatrix g * (gaugeMatrix g)ᴴ) * K * (gaugeMatrix g * (gaugeMatrix g)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = K := by rw [gaugeMatrix_mul_conjTranspose, Matrix.one_mul, Matrix.mul_one]

theorem mem_stabilizer_iff (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) (g : GaugeGroup n) :
    g ∈ stabilizer K ↔ gaugeAct g K = K := Iff.rfl

/-! ### Joint realizations -/

/-- A joint realization of `K` on the common space `ℂ^C`: a matrix
`S : Matrix C X ℂ` with Gram `Sᴴ S = K`. -/
def IsJointRealization (K : Matrix (Σ a, n a) (Σ a, n a) ℂ) {C : Type*} [Fintype C]
    (S : Matrix C (Σ a, n a) ℂ) : Prop :=
  Sᴴ * S = K

/-- The Gram of a joint realization lies in `Corr_X` exactly when its marginal
blocks are the identity (each `V_a` is an isometry). -/
theorem gram_mem_corr_iff {C : Type*} [Fintype C] (S : Matrix C (Σ a, n a) ℂ) :
    Sᴴ * S ∈ CorrelationSpectrahedron ↔ ∀ a, block (Sᴴ * S) a a = 1 :=
  ⟨fun h => h.2, fun h => ⟨Matrix.posSemidef_conjTranspose_mul_self S, h⟩⟩

/-- Every point of `Corr_X` (indeed every positive block operator) admits a
joint realization, of realization dimension `rank K`. -/
theorem exists_realization_of_mem_corr {K : Matrix (Σ a, n a) (Σ a, n a) ℂ}
    (hK : K ∈ CorrelationSpectrahedron) :
    ∃ S : Matrix (Σ a, n a) (Σ a, n a) ℂ, IsJointRealization K S ∧ S.rank = K.rank := by
  obtain ⟨hreal, -, hattain, -⟩ := source_kernel_realization_minimal_unique K hK.1
  exact ⟨CFC.sqrt K, hreal.symm, hattain⟩

/-- The realization space `Ran S` of any joint realization of `K` has
dimension exactly `rank K`: restricting to the range gives the minimal
realization. -/
theorem finrank_range_eq_rank {K : Matrix (Σ a, n a) (Σ a, n a) ℂ} {C : Type*} [Fintype C]
    {S : Matrix C (Σ a, n a) ℂ} (hS : IsJointRealization K S) :
    Module.finrank ℂ (LinearMap.range S.mulVecLin) = K.rank := by
  rw [← hS, Matrix.rank_conjTranspose_mul_self]
  rfl

/-- `rank K` is the minimum possible joint realization dimension. -/
theorem rank_le_card_of_realization {K : Matrix (Σ a, n a) (Σ a, n a) ℂ} {C : Type*}
    [Fintype C] {S : Matrix C (Σ a, n a) ℂ} (hS : IsJointRealization K S) :
    K.rank ≤ Fintype.card C := by
  rw [← hS, Matrix.rank_conjTranspose_mul_self]
  exact Matrix.rank_le_card_height S

/-- A marginal frame change `g` acts on a joint realization by `S ↦ S D(g)`;
the result realizes the gauged Gram. -/
theorem isJointRealization_mul_gaugeMatrix {K : Matrix (Σ a, n a) (Σ a, n a) ℂ} {C : Type*}
    [Fintype C] {S : Matrix C (Σ a, n a) ℂ} (hS : IsJointRealization K S) (g : GaugeGroup n) :
    IsJointRealization (gaugeAct g K) (S * gaugeMatrix g) := by
  unfold IsJointRealization gaugeAct at *
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ, hS, Matrix.mul_assoc]

/-- A source-fixing isometric identification of the realization spaces of two
joint realizations `M`, `T` (after the frame change is applied to `M`). -/
def SourceFixingUnitary {C C' : Type*} [Fintype C] [Fintype C']
    (M : Matrix C (Σ a, n a) ℂ) (T : Matrix C' (Σ a, n a) ℂ)
    (U : LinearMap.range M.mulVecLin ≃ₗ[ℂ] LinearMap.range T.mulVecLin) : Prop :=
  (∀ u, U (M.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u) ∧
    (∀ x y : LinearMap.range M.mulVecLin,
      star (x : C → ℂ) ⬝ᵥ (y : C → ℂ) = star (U x : C' → ℂ) ⬝ᵥ (U y : C' → ℂ))

/-- A source-fixing unitary between realization spaces forces equal Grams. -/
theorem gram_eq_of_sourceFixingUnitary {C C' : Type*} [Fintype C] [Fintype C']
    {M : Matrix C (Σ a, n a) ℂ} {T : Matrix C' (Σ a, n a) ℂ}
    {U : LinearMap.range M.mulVecLin ≃ₗ[ℂ] LinearMap.range T.mulVecLin}
    (hU : SourceFixingUnitary M T U) : Mᴴ * M = Tᴴ * T := by
  ext p q
  have h := hU.2 (M.mulVecLin.rangeRestrict (Pi.single p 1))
    (M.mulVecLin.rangeRestrict (Pi.single q 1))
  rw [hU.1, hU.1] at h
  simp only [LinearMap.rangeRestrict, LinearMap.codRestrict_apply, Matrix.mulVecLin_apply] at h
  rw [gram_realization_inner, gram_realization_inner] at h
  simpa [Matrix.mulVec_single_one, dotProduct_single_one, single_one_dotProduct] using h

/-- Two joint realizations of the same Gram have a unique source-fixing
unitary between their realization spaces (repo lemma
`joint_source_unique_range_unitary`). -/
theorem exists_unique_range_unitary {C C' : Type*} [Fintype C] [Fintype C']
    {M : Matrix C (Σ a, n a) ℂ} {T : Matrix C' (Σ a, n a) ℂ} (h : Mᴴ * M = Tᴴ * T) :
    ∃! U : LinearMap.range M.mulVecLin ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
      SourceFixingUnitary M T U :=
  joint_source_unique_range_unitary M T h

/-- Two joint realizations are equivalent through the fixed frame change `g`
(a source-fixing unitary between `Ran (S D(g))` and `Ran T`) iff the gauged
Gram of `S` is the Gram of `T`. -/
theorem exists_sourceFixingUnitary_iff {C C' : Type*} [Fintype C] [Fintype C']
    (S : Matrix C (Σ a, n a) ℂ) (T : Matrix C' (Σ a, n a) ℂ) (g : GaugeGroup n) :
    (∃ U : LinearMap.range (S * gaugeMatrix g).mulVecLin ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
        SourceFixingUnitary (S * gaugeMatrix g) T U) ↔
      gaugeAct g (Sᴴ * S) = Tᴴ * T := by
  constructor
  · rintro ⟨U, hU⟩
    have h := gram_eq_of_sourceFixingUnitary hU
    have hg := isJointRealization_mul_gaugeMatrix (K := Sᴴ * S) (S := S) rfl g
    unfold IsJointRealization at hg
    rw [← hg, h]
  · intro h
    have hg := isJointRealization_mul_gaugeMatrix (K := Sᴴ * S) (S := S) rfl g
    unfold IsJointRealization at hg
    obtain ⟨U, hU, -⟩ := exists_unique_range_unitary (hg.trans h)
    exact ⟨U, hU⟩

/-- Two joint realizations are equivalent up to a marginal frame change and a
source-fixing unitary on the common realization spaces. -/
def FrameUnitaryEquivalent {C C' : Type*} [Fintype C] [Fintype C']
    (S : Matrix C (Σ a, n a) ℂ) (T : Matrix C' (Σ a, n a) ℂ) : Prop :=
  ∃ g : GaugeGroup n,
    ∃ U : LinearMap.range (S * gaugeMatrix g).mulVecLin ≃ₗ[ℂ] LinearMap.range T.mulVecLin,
      SourceFixingUnitary (S * gaugeMatrix g) T U

/-- **Classification by `Corr_X / 𝒢_X` (`thm:supp-common-source`).**  Two
joint realizations are equivalent up to a marginal frame change and a unitary
on the common realization space iff their Grams lie in the same gauge orbit. -/
theorem frameUnitaryEquivalent_iff {C C' : Type*} [Fintype C] [Fintype C']
    (S : Matrix C (Σ a, n a) ℂ) (T : Matrix C' (Σ a, n a) ℂ) :
    FrameUnitaryEquivalent S T ↔ ∃ g : GaugeGroup n, gaugeAct g (Sᴴ * S) = Tᴴ * T := by
  unfold FrameUnitaryEquivalent
  simp only [exists_sourceFixingUnitary_iff]

/-- **Residual gauge group (`thm:supp-common-source`).**  For a joint
realization `S` of `K`, a marginal frame change `g` is implemented by a
source-fixing unitary on the realization space iff `g ∈ Stab_{𝒢_X}(K)`. -/
theorem mem_stabilizer_iff_residual {K : Matrix (Σ a, n a) (Σ a, n a) ℂ} {C : Type*}
    [Fintype C] {S : Matrix C (Σ a, n a) ℂ} (hS : IsJointRealization K S) (g : GaugeGroup n) :
    g ∈ stabilizer K ↔
      ∃ U : LinearMap.range (S * gaugeMatrix g).mulVecLin ≃ₗ[ℂ] LinearMap.range S.mulVecLin,
        SourceFixingUnitary (S * gaugeMatrix g) S U := by
  rw [mem_stabilizer_iff, exists_sourceFixingUnitary_iff]
  unfold IsJointRealization at hS
  rw [hS]

/-- **`thm:supp-common-source` (assembled).** -/
theorem joint_gram_classification {K : Matrix (Σ a, n a) (Σ a, n a) ℂ}
    (hK : K ∈ CorrelationSpectrahedron) :
    (∃ S : Matrix (Σ a, n a) (Σ a, n a) ℂ, IsJointRealization K S ∧ S.rank = K.rank) ∧
      (∀ {C : Type*} [Fintype C] (S : Matrix C (Σ a, n a) ℂ), IsJointRealization K S →
        Module.finrank ℂ (LinearMap.range S.mulVecLin) = K.rank ∧ K.rank ≤ Fintype.card C) ∧
      (∀ g : GaugeGroup n, gaugeAct g K ∈ CorrelationSpectrahedron) ∧
      (∀ {C C' : Type*} [Fintype C] [Fintype C'] (S : Matrix C (Σ a, n a) ℂ)
        (T : Matrix C' (Σ a, n a) ℂ),
        FrameUnitaryEquivalent S T ↔ ∃ g : GaugeGroup n, gaugeAct g (Sᴴ * S) = Tᴴ * T) ∧
      (∀ {C : Type*} [Fintype C] (S : Matrix C (Σ a, n a) ℂ), IsJointRealization K S →
        ∀ g : GaugeGroup n, g ∈ stabilizer K ↔
          ∃ U : LinearMap.range (S * gaugeMatrix g).mulVecLin ≃ₗ[ℂ]
            LinearMap.range S.mulVecLin, SourceFixingUnitary (S * gaugeMatrix g) S U) :=
  ⟨exists_realization_of_mem_corr hK,
    fun S hS => ⟨finrank_range_eq_rank hS, rank_le_card_of_realization hS⟩,
    gaugeAct_mem_corr hK,
    fun S T => frameUnitaryEquivalent_iff S T,
    fun S hS g => mem_stabilizer_iff_residual hS g⟩

end JointGram
end RenewalGeometry
