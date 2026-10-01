/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.EndpointAllocationCompilerExact
import RenewalGeometry.StandardModel.TensorFactorAlignmentExact

/-!
# Fusion-native sufficient criterion for same-carrier alignment
  (`thm:fusion-native-alignment`, spacetime–gauge duality manuscript)

Finite source-minimal Hilbert spaces are coordinate spaces `H_A → ℂ` with syntheses
`S_A : Matrix H_A E_A ℂ` onto `H_A` (`Function.Surjective S_A.mulVec`), Grams `G_A = S_A* S_A`;
coefficient occurrence maps are matrices `m_{A,B} : Matrix E_{AB} (E_A × E_B) ℂ`, and
`H_A ⊗ H_B` is `H_A × H_B` with Kronecker products.

* `fusionMap S_A S_B S_AB m` is `Γ_{A,B}`; `fusion_isometry`: under the metric identity
  `m* G_AB m = G_A ⊗ G_B` (`eq:fusion-metric-identity`) it is the unique matrix with
  `Γ (S_A ⊗ S_B) = S_AB m` (`eq:fusion-isometry-definition`, i.e. `Γ(S_A x ⊗ S_B y) =
  S_AB m(x ⊗ y)` for all `x, y`) and it is an isometry `Γ* Γ = I`.
* `fusion_unitary_of_zero_innovation`: zero innovation `S_AB*(I − ΓΓ*)S_AB = 0`
  (`eq:fusion-zero-innovation`) and source minimality give `Γ Γ* = I`.
* `fusion_native_alignment`: with the four pairs `(C,1), (1,2), (C1,2), (C,12)` and vanishing
  associator defect (`eq:fusion-associator-zero`), the two parenthesisations agree and define a
  unitary `Γ : (H_C ⊗ H_1) ⊗ H_2 → H_C12` (`eq:fusion-triple-unitary`); the transported factor
  actions (`eq:fusion-native-actions`) commute pairwise and generate `B(H_C12)`; for
  `dim = (3,2,2)` one has `dim H_C12 = 12`, `B(H_C12) ≅ M₁₂(ℂ)`; the same-carrier defect `Δ_⊗`
  of `thm:tensor-factor-alignment` (`TensorFactorAlignment.alignDefect`) vanishes for any
  families taken in the transported factor algebras; and with an extra multiplicity space `M`
  the actions `π(·) ⊗ I_M` generate exactly `B(H_C12) ⊗ I_M`.
* `fusion_associator_zero_of_assoc`: the coefficient associativity
  `eq:fusion-coefficient-associativity` already forces the associator defect to vanish.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace FusionNativeAlignment

/-! ## Generic facts -/

section Generic

/-- Squared Hilbert–Schmidt norm vanishes iff the matrix does. -/
theorem fusion_hsNormSq_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : EndpointAllocationCompiler.hsNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)).mp h
    ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (A i j)).mp
      (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
    simpa using h2
  · rintro rfl
    simp [EndpointAllocationCompiler.hsNormSq]

/-- A source synthesis onto its carrier has a right inverse. -/
theorem fusion_exists_rightInv {H E : Type*} [Fintype E] [DecidableEq H]
    (S : Matrix H E ℂ) (hS : Function.Surjective S.mulVec) :
    ∃ R : Matrix E H ℂ, S * R = 1 := by
  choose f hf using fun g : H => hS (Pi.single g 1)
  refine ⟨Matrix.of fun i g => f g i, ?_⟩
  ext n g
  have := congrFun (hf g) n
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using this

/-- A right inverse of `S_A ⊗ S_B`. -/
theorem fusion_kron_rightInv {HA HB EA EB : Type*} [Fintype EA] [Fintype EB] [DecidableEq HA]
    [DecidableEq HB] (SA : Matrix HA EA ℂ) (SB : Matrix HB EB ℂ)
    (hSA : Function.Surjective SA.mulVec) (hSB : Function.Surjective SB.mulVec) :
    ∃ R : Matrix (EA × EB) (HA × HB) ℂ, (SA ⊗ₖ SB) * R = 1 := by
  obtain ⟨RA, hRA⟩ := fusion_exists_rightInv SA hSA
  obtain ⟨RB, hRB⟩ := fusion_exists_rightInv SB hSB
  exact ⟨RA ⊗ₖ RB, by rw [← Matrix.mul_kronecker_mul, hRA, hRB, Matrix.one_kronecker_one]⟩

/-- A matrix with a right inverse can be cancelled on the right. -/
theorem fusion_cancel_right {m n p : Type*} [Fintype n] [Fintype p] [DecidableEq n]
    {K : Matrix n p ℂ} {R : Matrix p n ℂ} (hKR : K * R = 1) {A B : Matrix m n ℂ}
    (h : A * K = B * K) : A = B := by
  rw [← Matrix.mul_one A, ← Matrix.mul_one B, ← hKR, ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem fusion_kron_unitary {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] {Γ : Matrix m n ℂ}
    (h : Γᴴ * Γ = 1) : (Γ ⊗ₖ (1 : Matrix p p ℂ))ᴴ * (Γ ⊗ₖ (1 : Matrix p p ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, h,
    Matrix.mul_one, Matrix.one_kronecker_one]

theorem fusion_kron_unitary' {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] {Γ : Matrix m n ℂ}
    (h : Γ * Γᴴ = 1) : (Γ ⊗ₖ (1 : Matrix p p ℂ)) * (Γ ⊗ₖ (1 : Matrix p p ℂ))ᴴ = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, h,
    Matrix.mul_one, Matrix.one_kronecker_one]

end Generic

/-! ## Pair fusion maps -/

section Pair

variable {HA HB HAB EA EB EAB : Type} [Fintype HA] [Fintype HB] [Fintype HAB] [Fintype EA]
  [Fintype EB] [Fintype EAB] [DecidableEq HA] [DecidableEq HB] [DecidableEq HAB]
  [DecidableEq EA] [DecidableEq EB] [DecidableEq EAB]

/-- The fusion map `Γ_{A,B} : H_A ⊗ H_B → H_AB`, `Γ(S_A x ⊗ S_B y) = S_AB m(x ⊗ y)`
(`eq:fusion-isometry-definition`), built from a right inverse of `S_A ⊗ S_B`. -/
noncomputable def fusionMap (SA : Matrix HA EA ℂ) (SB : Matrix HB EB ℂ)
    (SAB : Matrix HAB EAB ℂ) (m : Matrix EAB (EA × EB) ℂ) : Matrix HAB (HA × HB) ℂ := by
  classical
  exact if h : ∃ R : Matrix (EA × EB) (HA × HB) ℂ, (SA ⊗ₖ SB) * R = 1 then
    SAB * m * h.choose else 0

/-- **Isometric extension.**  Under the metric identity `m* G_AB m = G_A ⊗ G_B` and source
minimality of `S_A, S_B`, `Γ_{A,B}` is the unique matrix with `Γ (S_A ⊗ S_B) = S_AB m`, and
it is an isometry. -/
theorem fusion_isometry (SA : Matrix HA EA ℂ) (SB : Matrix HB EB ℂ)
    (SAB : Matrix HAB EAB ℂ) (m : Matrix EAB (EA × EB) ℂ)
    (hSA : Function.Surjective SA.mulVec) (hSB : Function.Surjective SB.mulVec)
    (hmetric : mᴴ * (SABᴴ * SAB) * m = (SAᴴ * SA) ⊗ₖ (SBᴴ * SB)) :
    fusionMap SA SB SAB m * (SA ⊗ₖ SB) = SAB * m ∧
    (∀ Γ' : Matrix HAB (HA × HB) ℂ, Γ' * (SA ⊗ₖ SB) = SAB * m → Γ' = fusionMap SA SB SAB m) ∧
    (fusionMap SA SB SAB m)ᴴ * fusionMap SA SB SAB m = 1 := by
  have hex := fusion_kron_rightInv SA SB hSA hSB
  set K := SA ⊗ₖ SB with hK
  have hgram : Kᴴ * K = (SAᴴ * SA) ⊗ₖ (SBᴴ * SB) := by
    rw [hK, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  set R := hex.choose with hR
  have hKR : K * R = 1 := hex.choose_spec
  have hΓ : fusionMap SA SB SAB m = SAB * m * R := by
    unfold fusionMap
    rw [dite_cond_eq_true (eq_true hex)]
  -- well-definedness: `S_AB m` kills `Ker (S_A ⊗ S_B)`
  have hwd : SAB * m * R * K = SAB * m := by
    set Z := 1 - R * K with hZ
    have hKZ : K * Z = 0 := by
      rw [hZ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hKR, Matrix.one_mul, sub_self]
    have hY : (SAB * m * Z)ᴴ * (SAB * m * Z) = 0 := by
      have : (SAB * m * Z)ᴴ * (SAB * m * Z) = Zᴴ * (mᴴ * (SABᴴ * SAB) * m) * Z := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [this, hmetric, ← hgram]
      have : Zᴴ * (Kᴴ * K) * Z = (K * Z)ᴴ * (K * Z) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [this, hKZ, Matrix.mul_zero]
    have hY0 : SAB * m * Z = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hY
    rw [hZ, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hY0
    rw [Matrix.mul_assoc (SAB * m) R K, ← hY0]
  refine ⟨by rw [hΓ, hwd], fun Γ' hΓ' => ?_, ?_⟩
  · rw [hΓ, ← hΓ', Matrix.mul_assoc, hKR, Matrix.mul_one]
  · have hRK : Rᴴ * Kᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hKR, Matrix.conjTranspose_one]
    rw [hΓ]
    calc (SAB * m * R)ᴴ * (SAB * m * R)
        = Rᴴ * (mᴴ * (SABᴴ * SAB) * m) * R := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Rᴴ * (Kᴴ * K) * R := by rw [hmetric, hgram]
      _ = (Rᴴ * Kᴴ) * (K * R) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRK, hKR, Matrix.one_mul]

omit [Fintype HA] [Fintype HB] [Fintype EA] [Fintype EB] [DecidableEq HA] [DecidableEq HB]
  [DecidableEq EA] [DecidableEq EB] [DecidableEq EAB] in
/-- **Unitarity.**  An isometry `Γ` with zero innovation `S_AB*(I − ΓΓ*)S_AB = 0` against a
source-minimal `S_AB` is unitary. -/
theorem fusion_unitary_of_zero_innovation {T : Type} [Fintype T] [DecidableEq T]
    (Γ : Matrix HAB T ℂ) (hiso : Γᴴ * Γ = 1) (SAB : Matrix HAB EAB ℂ)
    (hSAB : Function.Surjective SAB.mulVec) (hinn : SABᴴ * (1 - Γ * Γᴴ) * SAB = 0) :
    Γ * Γᴴ = 1 := by
  set Pr := 1 - Γ * Γᴴ with hPr
  have hPrh : Prᴴ = Pr := by
    rw [hPr, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPrPr : Pr * Pr = Pr := by
    have : Γ * Γᴴ * (Γ * Γᴴ) = Γ * Γᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γᴴ, hiso, Matrix.one_mul]
    rw [hPr, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, this, sub_self,
      sub_zero]
  have h0 : (Pr * SAB)ᴴ * (Pr * SAB) = 0 := by
    rw [Matrix.conjTranspose_mul, hPrh, Matrix.mul_assoc, ← Matrix.mul_assoc Pr Pr, hPrPr,
      ← Matrix.mul_assoc]
    exact hinn
  have hPrS : Pr * SAB = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp h0
  obtain ⟨R, hR⟩ := fusion_exists_rightInv SAB hSAB
  have hPr0 : Pr = 0 := by
    rw [← Matrix.mul_one Pr, ← hR, ← Matrix.mul_assoc, hPrS, Matrix.zero_mul]
  rw [hPr, sub_eq_zero] at hPr0
  exact hPr0.symm

end Pair

/-! ## The triple unitary, transported actions and generation -/

section Triple

variable {HC H1 H2 HC12 : Type} [Fintype HC] [Fintype H1] [Fintype H2] [Fintype HC12]
  [DecidableEq HC] [DecidableEq H1] [DecidableEq H2] [DecidableEq HC12]

/-- Transported colour action `π̂_C(a) = Γ (a ⊗ I ⊗ I) Γ*`. -/
def fusionPiC (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (a : Matrix HC HC ℂ) :
    Matrix HC12 HC12 ℂ :=
  Γ * ((a ⊗ₖ (1 : Matrix H1 H1 ℂ)) ⊗ₖ (1 : Matrix H2 H2 ℂ)) * Γᴴ

/-- Transported first weak action `π̂_1(b) = Γ (I ⊗ b ⊗ I) Γ*`. -/
def fusionPi1 (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (b : Matrix H1 H1 ℂ) :
    Matrix HC12 HC12 ℂ :=
  Γ * (((1 : Matrix HC HC ℂ) ⊗ₖ b) ⊗ₖ (1 : Matrix H2 H2 ℂ)) * Γᴴ

/-- Transported second weak action `π̂_2(c) = Γ (I ⊗ I ⊗ c) Γ*`. -/
def fusionPi2 (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (c : Matrix H2 H2 ℂ) :
    Matrix HC12 HC12 ℂ :=
  Γ * (((1 : Matrix HC HC ℂ) ⊗ₖ (1 : Matrix H1 H1 ℂ)) ⊗ₖ c) * Γᴴ

theorem fusion_conj_mul {T : Type} [Fintype T] [DecidableEq T] {Γ : Matrix HC12 T ℂ} (hiso : Γᴴ * Γ = 1)
    (X Y : Matrix T T ℂ) : (Γ * X * Γᴴ) * (Γ * Y * Γᴴ) = Γ * (X * Y) * Γᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Γᴴ Γ, hiso, Matrix.one_mul]

theorem fusion_actions_commute (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (hiso : Γᴴ * Γ = 1) :
    (∀ a b, Commute (fusionPiC Γ a) (fusionPi1 Γ b)) ∧
    (∀ a c, Commute (fusionPiC Γ a) (fusionPi2 Γ c)) ∧
    (∀ b c, Commute (fusionPi1 Γ b) (fusionPi2 Γ c)) := by
  refine ⟨fun a b => ?_, fun a c => ?_, fun b c => ?_⟩ <;>
  · simp only [Commute, SemiconjBy, fusionPiC, fusionPi1, fusionPi2, fusion_conj_mul hiso]
    simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem fusion_actions_generate (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (hiso : Γᴴ * Γ = 1)
    (hco : Γ * Γᴴ = 1) :
    Algebra.adjoin ℂ (Set.range (fusionPiC (H1 := H1) (H2 := H2) Γ) ∪
      Set.range (fusionPi1 Γ) ∪ Set.range (fusionPi2 Γ)) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  set A := Algebra.adjoin ℂ (Set.range (fusionPiC (H1 := H1) (H2 := H2) Γ) ∪
      Set.range (fusionPi1 Γ) ∪ Set.range (fusionPi2 Γ))
  have hX : X = Γ * (Γᴴ * X * Γ) * Γᴴ := by
    simp only [← Matrix.mul_assoc]
    rw [hco, Matrix.one_mul, Matrix.mul_assoc, hco, Matrix.mul_one]
  have hunit : ∀ (p q : (HC × H1) × H2),
      Γ * Matrix.single p q (1 : ℂ) * Γᴴ ∈ A := by
    rintro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩
    have hfac : Matrix.single ((i, j), k) ((i', j'), k') (1 : ℂ)
        = ((Matrix.single i i' (1 : ℂ) ⊗ₖ (1 : Matrix H1 H1 ℂ)) ⊗ₖ (1 : Matrix H2 H2 ℂ)) *
          (((1 : Matrix HC HC ℂ) ⊗ₖ Matrix.single j j' (1 : ℂ)) ⊗ₖ (1 : Matrix H2 H2 ℂ)) *
          (((1 : Matrix HC HC ℂ) ⊗ₖ (1 : Matrix H1 H1 ℂ)) ⊗ₖ Matrix.single k k' (1 : ℂ)) := by
      simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_kronecker_one,
        Matrix.single_kronecker_single, mul_one]
    have hprod : Γ * Matrix.single ((i, j), k) ((i', j'), k') (1 : ℂ) * Γᴴ
        = fusionPiC Γ (Matrix.single i i' 1) * fusionPi1 Γ (Matrix.single j j' 1) *
          fusionPi2 Γ (Matrix.single k k' 1) := by
      rw [hfac, fusionPiC, fusionPi1, fusionPi2, fusion_conj_mul hiso, fusion_conj_mul hiso]
    rw [hprod]
    refine A.mul_mem (A.mul_mem ?_ ?_) ?_ <;> apply Algebra.subset_adjoin
    · exact Or.inl (Or.inl ⟨_, rfl⟩)
    · exact Or.inl (Or.inr ⟨_, rfl⟩)
    · exact Or.inr ⟨_, rfl⟩
  rw [hX, Matrix.matrix_eq_sum_single (Γᴴ * X * Γ), Matrix.mul_sum, Matrix.sum_mul]
  refine A.sum_mem fun p _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine A.sum_mem fun q _ => ?_
  have : Matrix.single p q ((Γᴴ * X * Γ) p q) = ((Γᴴ * X * Γ) p q) • Matrix.single p q 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]
  exact A.smul_mem (hunit p q) _

/-- Tensor amplification `X ↦ X ⊗ I_M` as an algebra homomorphism. -/
noncomputable def fusionAmplify (M : Type) [Fintype M] [DecidableEq M] :
    Matrix HC12 HC12 ℂ →ₐ[ℂ] Matrix (HC12 × M) (HC12 × M) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix M M ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' X Y := Matrix.add_kronecker _ _ _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.smul_kronecker, Matrix.one_kronecker_one]

end Triple

/-! ## The proposition -/

section Main

variable {HC H1 H2 HC1 H12 HC12 EC E1 E2 EC1 E12 EC12 : Type}
  [Fintype HC] [Fintype H1] [Fintype H2] [Fintype HC1] [Fintype H12] [Fintype HC12]
  [Fintype EC] [Fintype E1] [Fintype E2] [Fintype EC1] [Fintype E12] [Fintype EC12]
  [DecidableEq HC] [DecidableEq H1] [DecidableEq H2] [DecidableEq HC1] [DecidableEq H12]
  [DecidableEq HC12] [DecidableEq EC] [DecidableEq E1] [DecidableEq E2] [DecidableEq EC1]
  [DecidableEq E12] [DecidableEq EC12]

/-- The left parenthesisation `Γ_{C1,2}(Γ_{C,1} ⊗ I)`. -/
noncomputable def fusionLeft (SC : Matrix HC EC ℂ) (S1 : Matrix H1 E1 ℂ) (S2 : Matrix H2 E2 ℂ)
    (SC1 : Matrix HC1 EC1 ℂ) (SC12 : Matrix HC12 EC12 ℂ) (mC1 : Matrix EC1 (EC × E1) ℂ)
    (mC1_2 : Matrix EC12 (EC1 × E2) ℂ) : Matrix HC12 ((HC × H1) × H2) ℂ :=
  fusionMap SC1 S2 SC12 mC1_2 * (fusionMap SC S1 SC1 mC1 ⊗ₖ (1 : Matrix H2 H2 ℂ))

/-- The right parenthesisation `Γ_{C,12}(I ⊗ Γ_{1,2})`, reindexed along the associator
`(H_C ⊗ H_1) ⊗ H_2 ≅ H_C ⊗ (H_1 ⊗ H_2)`. -/
noncomputable def fusionRight (SC : Matrix HC EC ℂ) (S1 : Matrix H1 E1 ℂ)
    (S2 : Matrix H2 E2 ℂ) (S12 : Matrix H12 E12 ℂ) (SC12 : Matrix HC12 EC12 ℂ)
    (m12 : Matrix E12 (E1 × E2) ℂ) (mC_12 : Matrix EC12 (EC × E12) ℂ) :
    Matrix HC12 ((HC × H1) × H2) ℂ :=
  (fusionMap SC S12 SC12 mC_12 * ((1 : Matrix HC HC ℂ) ⊗ₖ fusionMap S1 S2 S12 m12)).submatrix
    id (Equiv.prodAssoc HC H1 H2)

/-- **`thm:fusion-native-alignment`.**  Source-minimal syntheses, the four metric identities
and the four zero innovations make every `Γ_{A,B}` the unique isometric extension of
`eq:fusion-isometry-definition` and a unitary; with zero associator defect the two
parenthesisations coincide and define a unitary `Γ` (`eq:fusion-triple-unitary`); the
transported factor actions commute pairwise and generate `B(H_C12)`; for any families taken in
the transported factor algebras the tensor-alignment defect `Δ_⊗` vanishes. -/
theorem fusion_native_alignment
    (SC : Matrix HC EC ℂ) (S1 : Matrix H1 E1 ℂ) (S2 : Matrix H2 E2 ℂ)
    (SC1 : Matrix HC1 EC1 ℂ) (S12 : Matrix H12 E12 ℂ) (SC12 : Matrix HC12 EC12 ℂ)
    (hSC : Function.Surjective SC.mulVec) (hS1 : Function.Surjective S1.mulVec)
    (hS2 : Function.Surjective S2.mulVec) (hSC1 : Function.Surjective SC1.mulVec)
    (hS12 : Function.Surjective S12.mulVec) (hSC12 : Function.Surjective SC12.mulVec)
    (mC1 : Matrix EC1 (EC × E1) ℂ) (m12 : Matrix E12 (E1 × E2) ℂ)
    (mC1_2 : Matrix EC12 (EC1 × E2) ℂ) (mC_12 : Matrix EC12 (EC × E12) ℂ)
    (_hassoc : mC1_2 * (mC1 ⊗ₖ (1 : Matrix E2 E2 ℂ))
      = (mC_12 * ((1 : Matrix EC EC ℂ) ⊗ₖ m12)).submatrix id (Equiv.prodAssoc EC E1 E2))
    (hmC1 : mC1ᴴ * (SC1ᴴ * SC1) * mC1 = (SCᴴ * SC) ⊗ₖ (S1ᴴ * S1))
    (hm12 : m12ᴴ * (S12ᴴ * S12) * m12 = (S1ᴴ * S1) ⊗ₖ (S2ᴴ * S2))
    (hmC1_2 : mC1_2ᴴ * (SC12ᴴ * SC12) * mC1_2 = (SC1ᴴ * SC1) ⊗ₖ (S2ᴴ * S2))
    (hmC_12 : mC_12ᴴ * (SC12ᴴ * SC12) * mC_12 = (SCᴴ * SC) ⊗ₖ (S12ᴴ * S12))
    (hinnC1 : SC1ᴴ * (1 - fusionMap SC S1 SC1 mC1 * (fusionMap SC S1 SC1 mC1)ᴴ) * SC1 = 0)
    (hinn12 : S12ᴴ * (1 - fusionMap S1 S2 S12 m12 * (fusionMap S1 S2 S12 m12)ᴴ) * S12 = 0)
    (hinnC1_2 : SC12ᴴ * (1 - fusionMap SC1 S2 SC12 mC1_2 * (fusionMap SC1 S2 SC12 mC1_2)ᴴ)
      * SC12 = 0)
    (hinnC_12 : SC12ᴴ * (1 - fusionMap SC S12 SC12 mC_12 * (fusionMap SC S12 SC12 mC_12)ᴴ)
      * SC12 = 0)
    (hassocDefect : EndpointAllocationCompiler.hsNormSq
      (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 - fusionRight SC S1 S2 S12 SC12 m12 mC_12) = 0) :
    -- every pair map is a unitary
    ((fusionMap SC S1 SC1 mC1)ᴴ * fusionMap SC S1 SC1 mC1 = 1 ∧
      fusionMap SC S1 SC1 mC1 * (fusionMap SC S1 SC1 mC1)ᴴ = 1) ∧
    ((fusionMap S1 S2 S12 m12)ᴴ * fusionMap S1 S2 S12 m12 = 1 ∧
      fusionMap S1 S2 S12 m12 * (fusionMap S1 S2 S12 m12)ᴴ = 1) ∧
    ((fusionMap SC1 S2 SC12 mC1_2)ᴴ * fusionMap SC1 S2 SC12 mC1_2 = 1 ∧
      fusionMap SC1 S2 SC12 mC1_2 * (fusionMap SC1 S2 SC12 mC1_2)ᴴ = 1) ∧
    ((fusionMap SC S12 SC12 mC_12)ᴴ * fusionMap SC S12 SC12 mC_12 = 1 ∧
      fusionMap SC S12 SC12 mC_12 * (fusionMap SC S12 SC12 mC_12)ᴴ = 1) ∧
    -- the two parenthesisations agree and give a unitary `Γ`
    fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 = fusionRight SC S1 S2 S12 SC12 m12 mC_12 ∧
    (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2)ᴴ * fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 = 1 ∧
    fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 * (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2)ᴴ = 1 ∧
    -- the transported factor actions commute pairwise ...
    ((∀ a b, Commute (fusionPiC (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) a)
        (fusionPi1 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) b)) ∧
      (∀ a c, Commute (fusionPiC (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) a)
        (fusionPi2 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) c)) ∧
      (∀ b c, Commute (fusionPi1 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) b)
        (fusionPi2 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2) c))) ∧
    -- ... and generate `B(H_C12)`
    Algebra.adjoin ℂ
      (Set.range (fusionPiC (H1 := H1) (H2 := H2) (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2)) ∪
        Set.range (fusionPi1 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2)) ∪
        Set.range (fusionPi2 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2))) = ⊤ ∧
    -- the same-carrier defect `Δ_⊗` vanishes for these factor actions
    (∀ {ια ιβ ιγ : Type} [Fintype ια] [Fintype ιβ] [Fintype ιγ]
      (Cf : ια → Matrix HC12 HC12 ℂ) (W₁ : ιβ → Matrix HC12 HC12 ℂ)
      (W₂ : ιγ → Matrix HC12 HC12 ℂ),
      (∀ a, Cf a ∈ Set.range
        (fusionPiC (H1 := H1) (H2 := H2) (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2))) →
      (∀ b, W₁ b ∈ Set.range (fusionPi1 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2))) →
      (∀ c, W₂ c ∈ Set.range (fusionPi2 (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2))) →
      TensorFactorAlignment.alignDefect Cf W₁ W₂ = 0) := by
  -- pair isometries and unitaries
  have iC1 := (fusion_isometry SC S1 SC1 mC1 hSC hS1 hmC1).2.2
  have i12 := (fusion_isometry S1 S2 S12 m12 hS1 hS2 hm12).2.2
  have iC1_2 := (fusion_isometry SC1 S2 SC12 mC1_2 hSC1 hS2 hmC1_2).2.2
  have iC_12 := (fusion_isometry SC S12 SC12 mC_12 hSC hS12 hmC_12).2.2
  have uC1 := fusion_unitary_of_zero_innovation _ iC1 SC1 hSC1 hinnC1
  have u12 := fusion_unitary_of_zero_innovation _ i12 S12 hS12 hinn12
  have uC1_2 := fusion_unitary_of_zero_innovation _ iC1_2 SC12 hSC12 hinnC1_2
  have uC_12 := fusion_unitary_of_zero_innovation _ iC_12 SC12 hSC12 hinnC_12
  set Γ := fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 with hΓ
  have hiso : Γᴴ * Γ = 1 := by
    rw [hΓ, fusionLeft, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (fusionMap SC1 S2 SC12 mC1_2)ᴴ, iC1_2, Matrix.one_mul,
      fusion_kron_unitary iC1]
  have hco : Γ * Γᴴ = 1 := by
    rw [hΓ, fusionLeft, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (fusionMap SC S1 SC1 mC1 ⊗ₖ (1 : Matrix H2 H2 ℂ)),
      fusion_kron_unitary' uC1, Matrix.one_mul, uC1_2]
  have hcomm := fusion_actions_commute Γ hiso
  refine ⟨⟨iC1, uC1⟩, ⟨i12, u12⟩, ⟨iC1_2, uC1_2⟩, ⟨iC_12, uC_12⟩,
    sub_eq_zero.mp ((fusion_hsNormSq_eq_zero_iff _).mp hassocDefect), hiso, hco, hcomm,
    fusion_actions_generate Γ hiso hco, ?_⟩
  intro ια ιβ ιγ _ _ _ Cf W₁ W₂ hC hW₁ hW₂
  have h1 : ∀ a b, Cf a * W₁ b - W₁ b * Cf a = 0 := by
    intro a b
    obtain ⟨x, hx⟩ := hC a; obtain ⟨y, hy⟩ := hW₁ b
    rw [← hx, ← hy, (hcomm.1 x y).eq, sub_self]
  have h2 : ∀ a c, Cf a * W₂ c - W₂ c * Cf a = 0 := by
    intro a c
    obtain ⟨x, hx⟩ := hC a; obtain ⟨z, hz⟩ := hW₂ c
    rw [← hx, ← hz, (hcomm.2.1 x z).eq, sub_self]
  have h3 : ∀ b c, W₁ b * W₂ c - W₂ c * W₁ b = 0 := by
    intro b c
    obtain ⟨y, hy⟩ := hW₁ b; obtain ⟨z, hz⟩ := hW₂ c
    rw [← hy, ← hz, (hcomm.2.2 y z).eq, sub_self]
  simp only [TensorFactorAlignment.alignDefect, h1, h2, h3,
    (TensorFactorAlignment.hsNormSq_eq_zero_iff (0 : Matrix HC12 HC12 ℂ)).mpr rfl,
    Finset.sum_const_zero, add_zero]

/-- **Dimensions `(3,2,2)`.**  A unitary `Γ : (H_C ⊗ H_1) ⊗ H_2 → H_C12` with
`dim H_C = 3`, `dim H_1 = dim H_2 = 2` forces `dim H_C12 = 12`, so `B(H_C12) ≅ M₁₂(ℂ)`. -/
theorem fusion_dim_twelve (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (hiso : Γᴴ * Γ = 1)
    (hco : Γ * Γᴴ = 1) (hC : Fintype.card HC = 3) (h1 : Fintype.card H1 = 2)
    (h2 : Fintype.card H2 = 2) :
    Fintype.card HC12 = 12 ∧
      Nonempty (Matrix HC12 HC12 ℂ ≃ₐ[ℂ] Matrix (Fin 12) (Fin 12) ℂ) := by
  have htr : ((Fintype.card ((HC × H1) × H2) : ℕ) : ℂ) = ((Fintype.card HC12 : ℕ) : ℂ) := by
    rw [← Matrix.trace_one, ← Matrix.trace_one, ← hiso, ← hco, Matrix.trace_mul_comm]
  have hcard : Fintype.card HC12 = 12 := by
    have := Nat.cast_injective htr
    rw [Fintype.card_prod, Fintype.card_prod, hC, h1, h2] at this
    omega
  exact ⟨hcard, ⟨Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFinOfCardEq hcard)⟩⟩

/-- **Multiplicity space.**  With an additional reducing multiplicity space `M`, the factor
actions `π̂(·) ⊗ I_M` generate exactly `B(H_C12) ⊗ I_M`. -/
theorem fusion_multiplicity_generate (Γ : Matrix HC12 ((HC × H1) × H2) ℂ) (hiso : Γᴴ * Γ = 1)
    (hco : Γ * Γᴴ = 1) (M : Type) [Fintype M] [DecidableEq M] :
    Algebra.adjoin ℂ ((fusionAmplify M) '' (Set.range (fusionPiC (H1 := H1) (H2 := H2) Γ) ∪
      Set.range (fusionPi1 Γ) ∪ Set.range (fusionPi2 Γ))) = (fusionAmplify M).range := by
  rw [← AlgHom.map_adjoin, fusion_actions_generate Γ hiso hco, Algebra.map_top]

/-- **Associativity forces the associator.**  The coefficient associativity
`eq:fusion-coefficient-associativity`, with source minimality and the metric identities, makes
the two parenthesisations equal (so the associator defect vanishes). -/
theorem fusion_associator_zero_of_assoc
    (SC : Matrix HC EC ℂ) (S1 : Matrix H1 E1 ℂ) (S2 : Matrix H2 E2 ℂ)
    (SC1 : Matrix HC1 EC1 ℂ) (S12 : Matrix H12 E12 ℂ) (SC12 : Matrix HC12 EC12 ℂ)
    (hSC : Function.Surjective SC.mulVec) (hS1 : Function.Surjective S1.mulVec)
    (hS2 : Function.Surjective S2.mulVec) (hSC1 : Function.Surjective SC1.mulVec)
    (hS12 : Function.Surjective S12.mulVec)
    (mC1 : Matrix EC1 (EC × E1) ℂ) (m12 : Matrix E12 (E1 × E2) ℂ)
    (mC1_2 : Matrix EC12 (EC1 × E2) ℂ) (mC_12 : Matrix EC12 (EC × E12) ℂ)
    (hassoc : mC1_2 * (mC1 ⊗ₖ (1 : Matrix E2 E2 ℂ))
      = (mC_12 * ((1 : Matrix EC EC ℂ) ⊗ₖ m12)).submatrix id (Equiv.prodAssoc EC E1 E2))
    (hmC1 : mC1ᴴ * (SC1ᴴ * SC1) * mC1 = (SCᴴ * SC) ⊗ₖ (S1ᴴ * S1))
    (hm12 : m12ᴴ * (S12ᴴ * S12) * m12 = (S1ᴴ * S1) ⊗ₖ (S2ᴴ * S2))
    (hmC1_2 : mC1_2ᴴ * (SC12ᴴ * SC12) * mC1_2 = (SC1ᴴ * SC1) ⊗ₖ (S2ᴴ * S2))
    (hmC_12 : mC_12ᴴ * (SC12ᴴ * SC12) * mC_12 = (SCᴴ * SC) ⊗ₖ (S12ᴴ * S12)) :
    EndpointAllocationCompiler.hsNormSq
      (fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 - fusionRight SC S1 S2 S12 SC12 m12 mC_12) = 0 := by
  rw [fusion_hsNormSq_eq_zero_iff, sub_eq_zero]
  have sC1 := (fusion_isometry SC S1 SC1 mC1 hSC hS1 hmC1).1
  have s12 := (fusion_isometry S1 S2 S12 m12 hS1 hS2 hm12).1
  have sC1_2 := (fusion_isometry SC1 S2 SC12 mC1_2 hSC1 hS2 hmC1_2).1
  have sC_12 := (fusion_isometry SC S12 SC12 mC_12 hSC hS12 hmC_12).1
  obtain ⟨RC1, hRC1⟩ := fusion_kron_rightInv SC S1 hSC hS1
  obtain ⟨R2, hR2⟩ := fusion_exists_rightInv S2 hS2
  set K3 := (SC ⊗ₖ S1) ⊗ₖ S2 with hK3
  have hK3R : K3 * (RC1 ⊗ₖ R2) = 1 := by
    rw [hK3, ← Matrix.mul_kronecker_mul, hRC1, hR2, Matrix.one_kronecker_one]
  apply fusion_cancel_right hK3R
  -- left parenthesisation on source vectors
  have hL : fusionLeft SC S1 S2 SC1 SC12 mC1 mC1_2 * K3
      = SC12 * (mC1_2 * (mC1 ⊗ₖ (1 : Matrix E2 E2 ℂ))) := by
    rw [fusionLeft, hK3, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, sC1, Matrix.one_mul]
    have e : (SC1 * mC1) ⊗ₖ S2 = (SC1 ⊗ₖ S2) * (mC1 ⊗ₖ (1 : Matrix E2 E2 ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, sC1_2, Matrix.mul_assoc]
  -- right parenthesisation on source vectors
  have hK3' : K3 = (SC ⊗ₖ (S1 ⊗ₖ S2)).submatrix (Equiv.prodAssoc HC H1 H2)
      (Equiv.prodAssoc EC E1 E2) := by
    rw [hK3, ← Matrix.kronecker_assoc]
    ext ⟨⟨a, b⟩, c⟩ ⟨⟨d, e⟩, f⟩
    simp [Matrix.reindex_apply, mul_assoc]
  have hR : fusionRight SC S1 S2 S12 SC12 m12 mC_12 * K3
      = (SC12 * (mC_12 * ((1 : Matrix EC EC ℂ) ⊗ₖ m12))).submatrix id
          (Equiv.prodAssoc EC E1 E2) := by
    rw [fusionRight, hK3', Matrix.submatrix_mul_equiv]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, s12, Matrix.one_mul]
    have e : SC ⊗ₖ (S12 * m12) = (SC ⊗ₖ S12) * ((1 : Matrix EC EC ℂ) ⊗ₖ m12) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, sC_12, Matrix.mul_assoc]
  rw [hL, hR, hassoc]
  ext i j
  simp [Matrix.mul_apply]

end Main

end FusionNativeAlignment
end RenewalGeometry
