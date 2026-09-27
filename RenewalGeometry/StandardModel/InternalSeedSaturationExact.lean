/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ExternalIsotypicKroneckerExact
import RenewalGeometry.StandardModel.InternalDeficitAlternativesExact
import RenewalGeometry.StandardModel.ReciprocalReturnBankExact

open NCG
/-!
# Relative-commutant saturation (`thm:internal-seed-saturation`)

`thm:internal-seed-saturation` of the spacetime–gauge duality paper: at a word depth
whose external multiplicity census is `(3, 2, 1, 1)` (`eq:SM-multiplicity-census`),
with the landing hypotheses (I1)–(I4), the represented internal word algebra equals
the external relative commutant,

`𝒜^word_int = 𝒜'_ext ≅ M₃(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` (`eq:active-internal-algebra`),

of dimension `15`, with a four-dimensional centre and two nonabelian factors
distinguished by their sizes (`9` and `4` matrix entries).

The file transports the concrete generation theorem
`InternalDeficit.internal_seed_saturation_concrete` (on the census carrier
`ℂ⁷ = ℂ³ ⊕ ℂ² ⊕ ℂ ⊕ ℂ`, block algebra `InternalAssembly.blockAlgebra`) along an
explicit algebra isomorphism with the external relative commutant furnished by the
parent theorem `thm:active-isotypic` (`ExternalIsotypic.external_isotypic`):

* `multBlockHom : (Π b, M_{J b}(ℂ)) →ₐ M_{Σ b, I b × J b}(ℂ)`, `Y ↦ ⊕_b 1 ⊗ Y b`, an
  injective algebra map with range `multBlockSet I J` (the parent's
  `eq:external-isotypic-commutant` after conjugation by the isotypic unitary `W`);
* `conjHom W : y ↦ W y Wᴴ` and `extEmbed W : Π b, M_{J b}(ℂ) →ₐ M_n(ℂ)`, whose range
  is the external relative commutant `extCommutant ρ`
  (`Subalgebra.centralizer` of `C^*(ρ(G))`);
* the census `(3, 2, 1, 1)` is rendered as a labelling `e : ι ≃ Fin 4` of the sectors
  with `|J (e.symm k)| = ![3, 2, 1, 1] k`; it yields a coordinate bijection
  `censusEquiv : Fin 7 ≃ Σ b, J b` sending the block partition `blockOf` of the census
  carrier to the sector partition, and `blockHom7 : Π b, M_{J b}(ℂ) →ₐ M₇(ℂ)` with range
  exactly `blockAlgebra`;
* `censusCommutantEquiv : blockAlgebra ≃ₐ[ℂ] extCommutant ρ`, hence
  `finrank ℂ (extCommutant ρ) = 15` and a four-dimensional centre
  (`finrank_center_extCommutant`, via `InternalDeficit.finrank_centre`);
* the reciprocal alternative of (I1): the returned word `r_{g,k} = B^* (v_g ⊗ h^k) A`
  of a mediator bank with `m_ret > 0` (`ReciprocalReturnMass.mass_pos_iff`,
  `thm:reciprocal-return`) is compressed onto the census colour three-space
  (`bankWord7`, type line `T ↦ 0`, private plane `H_priv ↦ {1, 2}`), giving a
  colour-supported represented word with `ω_col > 0` (`omega7_bankWord7_pos`);
* `internal_seed_saturation_of_bridge` (the `ω_col > 0` branch of (I1)),
  `internal_seed_saturation` (both branches) and
  `internal_seed_saturation_of_unitary` (for a unitary `ρ`, with the decomposition
  data produced by the parent theorem).

Renderings (disclosed): the isotypic decomposition data `(ι, I, J, W)` of
`thm:active-isotypic` are taken as hypotheses with exactly the properties the parent
proves (`Wᴴ W = 1 = W Wᴴ`, nonempty external factors, `Wᴴ 𝒜'_ext W = multBlockSet I J`);
the represented words are modelled, as in the concrete theorem, by the generator set
`baseGens ∪ bridgeGens u ∪ routerGen h` on the census carrier transported to
`𝒜'_ext` through the isomorphism (the private units, the type line and the scalar and
central supports are (I1)/(I3)/(I4), the colour-supported word `u` with `ω_col(u) > 0`
or the compressed reciprocal bridge word is (I1), the router `h` is (I2)); the coherent
realisation `T ⊕ H_priv` of the multiplicity-three sector is the choice of coordinates
made by `censusEquiv`.  Which of the four sectors carries which `S₄`-irreducible is
not tracked (only the multiplicities are).
-/

open Matrix Kronecker Module
open RenewalGeometry.InternalAssembly (blockOf blockAlgebra ColourSupported omega7)
open RenewalGeometry.InternalDeficit (baseGens bridgeGens routerGen Router)
open RenewalGeometry.ExternalIsotypic

namespace RenewalGeometry
namespace InternalSeedSaturation

/-! ### The multiplicity algebra as an algebra map -/

section MultBlock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- `Y ↦ ⊕_b 1_{I b} ⊗ Y b`, the multiplicity algebra `Π_b M_{J b}(ℂ)` embedded in
`M_{Σ b, I b × J b}(ℂ)`. -/
def multBlockHom (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] :
    (∀ b, Matrix (J b) (J b) ℂ) →ₐ[ℂ] Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ where
  toFun Y := blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b
  map_one' := by
    simp only [Pi.one_apply, Matrix.one_kronecker_one]
    exact blockDiagonal'_one
  map_mul' Y Z := by
    rw [← blockDiagonal'_mul]
    congr 1
    funext b
    rw [Pi.mul_apply, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by
    simp only [Pi.zero_apply, Matrix.kronecker_zero]
    exact blockDiagonal'_zero
  map_add' Y Z := by
    rw [← blockDiagonal'_add]
    congr 1
    funext b
    simp only [Pi.add_apply, Matrix.kronecker_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply, Matrix.kronecker_smul, Matrix.one_kronecker_one]
    rw [← blockDiagonal'_one, ← blockDiagonal'_smul]
    rfl

theorem multBlockHom_apply (Y : ∀ b, Matrix (J b) (J b) ℂ) :
    multBlockHom I J Y = blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b := rfl

/-- The range of `multBlockHom` is the multiplicity algebra `multBlockSet I J`. -/
theorem range_multBlockHom : Set.range (multBlockHom I J) = multBlockSet I J :=
  Set.ext fun _ => ⟨fun ⟨Y, hY⟩ => ⟨Y, hY.symm⟩, fun ⟨Y, hY⟩ => ⟨Y, hY.symm⟩⟩

theorem multBlockHom_injective (hNI : ∀ b, Nonempty (I b)) :
    Function.Injective (multBlockHom I J) := by
  intro Y Z hYZ
  funext b
  have := hNI b
  have h := congrArg (multBlockLin I J b (Classical.arbitrary (I b))) hYZ
  rwa [multBlockHom_apply, multBlockHom_apply, multBlockLin_multBlock,
    multBlockLin_multBlock] at h

end MultBlock

/-! ### Conjugation by the isotypic unitary and the external commutant -/

section Conj

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Fintype K] [DecidableEq K]

/-- `y ↦ W y Wᴴ` for a unitary `W : n → K`, as a unital algebra map `M_K(ℂ) →ₐ M_n(ℂ)`. -/
def conjHom (W : Matrix n K ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) :
    Matrix K K ℂ →ₐ[ℂ] Matrix n n ℂ :=
  AlgHom.ofLinearMap (conjLin Wᴴ)
    (by rw [conjLin_apply, Matrix.conjTranspose_conjTranspose, Matrix.mul_one, hW2])
    (conjLin_mul Wᴴ (by rw [Matrix.conjTranspose_conjTranspose, hW1]))

theorem conjHom_apply (W : Matrix n K ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (y : Matrix K K ℂ) : conjHom W hW1 hW2 y = W * y * Wᴴ := by
  simp only [conjHom, AlgHom.ofLinearMap_apply, conjLin_apply, Matrix.conjTranspose_conjTranspose]

theorem conjHom_injective (W : Matrix n K ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) :
    Function.Injective (conjHom W hW1 hW2) := by
  intro y z hyz
  rw [conjHom_apply, conjHom_apply] at hyz
  have h := congrArg (fun x => Wᴴ * x * W) hyz
  simp only [Matrix.mul_assoc, hW1, Matrix.mul_one] at h
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW1, Matrix.one_mul, Matrix.one_mul] at h

/-- The external relative commutant `𝒜'_ext = C^*(ρ(G))'` as a subalgebra of `M_n(ℂ)`. -/
def extCommutant {G : Type} [Group G] (ρ : G →* Matrix n n ℂ) : Subalgebra ℂ (Matrix n n ℂ) :=
  Subalgebra.centralizer ℂ (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ))

theorem mem_extCommutant {G : Type} [Group G] (ρ : G →* Matrix n n ℂ) {x : Matrix n n ℂ} :
    x ∈ extCommutant ρ ↔
      x ∈ matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) := by
  rw [extCommutant, Subalgebra.mem_centralizer_iff]
  exact forall_congr' fun a => forall_congr' fun _ => eq_comm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- The multiplicity algebra embedded into `M_n(ℂ)`: `Y ↦ W (⊕_b 1 ⊗ Y b) Wᴴ`. -/
def extEmbed (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] (W : Matrix n (Σ b, I b × J b) ℂ)
    (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) :
    (∀ b, Matrix (J b) (J b) ℂ) →ₐ[ℂ] Matrix n n ℂ :=
  (conjHom W hW1 hW2).comp (multBlockHom I J)

theorem extEmbed_apply (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (Y : ∀ b, Matrix (J b) (J b) ℂ) :
    extEmbed I J W hW1 hW2 Y = W * multBlockHom I J Y * Wᴴ := by
  simp only [extEmbed, AlgHom.comp_apply, conjHom_apply]

theorem extEmbed_injective (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hNI : ∀ b, Nonempty (I b)) :
    Function.Injective (extEmbed I J W hW1 hW2) :=
  (conjHom_injective W hW1 hW2).comp (multBlockHom_injective hNI)

/-- The range of the embedded multiplicity algebra is the external relative commutant
(`eq:external-isotypic-commutant` conjugated back by `W`). -/
theorem range_extEmbed {G : Type} [Group G] (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hM : (fun x => Wᴴ * x * W) ''
        matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J) :
    (extEmbed I J W hW1 hW2).range = extCommutant ρ := by
  ext x
  rw [AlgHom.mem_range, mem_extCommutant]
  constructor
  · rintro ⟨Y, rfl⟩
    have hmem : multBlockHom I J Y ∈ multBlockSet I J := ⟨Y, rfl⟩
    rw [← hM] at hmem
    obtain ⟨c, hc, hce⟩ := hmem
    rw [extEmbed_apply, ← hce]
    simp only [Matrix.mul_assoc]
    rw [hW2, Matrix.mul_one, ← Matrix.mul_assoc, hW2, Matrix.one_mul]
    exact hc
  · intro hx
    have hmem : Wᴴ * x * W ∈ multBlockSet I J := by
      rw [← hM]
      exact ⟨x, hx, rfl⟩
    obtain ⟨Y, hY⟩ := hmem
    refine ⟨Y, ?_⟩
    rw [extEmbed_apply, multBlockHom_apply, ← hY]
    simp only [Matrix.mul_assoc]
    rw [hW2, Matrix.mul_one, ← Matrix.mul_assoc, hW2, Matrix.one_mul]

end Conj

/-! ### The census `(3, 2, 1, 1)` and the census carrier -/

section Census

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ι → Type}
  [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- The block partition `blockOf = ![0,0,0,1,1,2,3]` of the census carrier has fibres of
sizes `3, 2, 1, 1`. -/
theorem card_fiber_blockOf :
    ∀ k : Fin 4, Fintype.card {i : Fin 7 // blockOf i = k} = ![3, 2, 1, 1] k := by
  decide

variable (e : ι ≃ Fin 4) (hcard : ∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k)

/-- Identification of the `k`-th block of the census carrier with the multiplicity
space of the sector `e.symm k`. -/
noncomputable def fiberEquiv (k : Fin 4) : {i : Fin 7 // blockOf i = k} ≃ J (e.symm k) :=
  Fintype.equivOfCardEq ((card_fiber_blockOf k).trans (hcard k).symm)

/-- The coordinate bijection `Fin 7 ≃ Σ b, J b` of the census: block `k` of the census
carrier is the multiplicity space of the sector `e.symm k`. -/
noncomputable def censusEquiv : Fin 7 ≃ Σ b, J b :=
  ((Equiv.sigmaFiberEquiv blockOf).symm.trans
    (Equiv.sigmaCongrRight (fiberEquiv e hcard))).trans (Equiv.sigmaCongrLeft e.symm)

theorem censusEquiv_fst (i : Fin 7) : (censusEquiv e hcard i).1 = e.symm (blockOf i) := rfl

theorem blockOf_censusEquiv_symm (p : Σ b, J b) :
    blockOf ((censusEquiv e hcard).symm p) = e p.1 := by
  have h := censusEquiv_fst e hcard ((censusEquiv e hcard).symm p)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.apply_symm_apply]

/-- Block-diagonal matrices as a unital algebra map `Π_b M_{J b}(ℂ) →ₐ M_{Σ b, J b}(ℂ)`. -/
def blockDiagonal'AlgHom (J : ι → Type) [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] :
    (∀ b, Matrix (J b) (J b) ℂ) →ₐ[ℂ] Matrix (Σ b, J b) (Σ b, J b) ℂ :=
  { Matrix.blockDiagonal'RingHom J ℂ with
    commutes' := fun c => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      show blockDiagonal' (c • (1 : ∀ b, Matrix (J b) (J b) ℂ)) = c • 1
      rw [blockDiagonal'_smul, blockDiagonal'_one] }

theorem blockDiagonal'AlgHom_apply (Y : ∀ b, Matrix (J b) (J b) ℂ) :
    blockDiagonal'AlgHom J Y = blockDiagonal' Y := rfl

/-- The multiplicity algebra `Π_b M_{J b}(ℂ)` realised on the census carrier `ℂ⁷`. -/
noncomputable def blockHom7 : (∀ b, Matrix (J b) (J b) ℂ) →ₐ[ℂ] Matrix (Fin 7) (Fin 7) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (censusEquiv e hcard).symm).toAlgHom.comp (blockDiagonal'AlgHom J)

theorem blockHom7_apply (Y : ∀ b, Matrix (J b) (J b) ℂ) (i j : Fin 7) :
    blockHom7 e hcard Y i j = blockDiagonal' Y (censusEquiv e hcard i) (censusEquiv e hcard j) := by
  simp only [blockHom7, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    blockDiagonal'AlgHom_apply]

theorem blockHom7_injective : Function.Injective (blockHom7 e hcard) := by
  intro Y Z hYZ
  have h : blockDiagonal' Y = blockDiagonal' Z :=
    (Matrix.reindexAlgEquiv ℂ ℂ (censusEquiv e hcard).symm).injective hYZ
  rw [← blockDiag'_blockDiagonal' Y, ← blockDiag'_blockDiagonal' Z, h]

/-- The range of `blockHom7` is exactly the block algebra `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` of the census
carrier. -/
theorem range_blockHom7 : (blockHom7 e hcard).range = blockAlgebra := by
  ext X
  rw [AlgHom.mem_range]
  constructor
  · rintro ⟨Y, rfl⟩ i j hij
    rw [blockHom7_apply, blockDiagonal'_apply, dite_eq_right_iff.mpr]
    intro h
    exact absurd (e.symm.injective h) hij
  · intro hX
    refine ⟨fun b => Matrix.of fun l l' =>
      X ((censusEquiv e hcard).symm ⟨b, l⟩) ((censusEquiv e hcard).symm ⟨b, l'⟩), ?_⟩
    ext i j
    obtain ⟨p, rfl⟩ := (censusEquiv e hcard).symm.surjective i
    obtain ⟨q, rfl⟩ := (censusEquiv e hcard).symm.surjective j
    rw [blockHom7_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨b, l⟩ := p
    obtain ⟨b', l'⟩ := q
    by_cases hb : b = b'
    · subst hb
      rw [blockDiagonal'_apply_eq]
      rfl
    · rw [blockDiagonal'_apply_ne _ _ _ hb]
      symm
      apply hX
      rw [blockOf_censusEquiv_symm, blockOf_censusEquiv_symm]
      exact fun h => hb (e.injective h)

end Census

/-! ### The isomorphism `blockAlgebra ≃ₐ 𝒜'_ext` at census `(3, 2, 1, 1)` -/

section Iso

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]
  {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- **`𝒜'_ext ≅ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` at census `(3, 2, 1, 1)`**: the block algebra of the
census carrier is isomorphic, as a unital `ℂ`-algebra, to the external relative
commutant. -/
noncomputable def censusCommutantEquiv (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
        matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    (e : ι ≃ Fin 4) (hcard : ∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k) :
    blockAlgebra ≃ₐ[ℂ] extCommutant ρ :=
  ((Subalgebra.equivOfEq _ _ (range_blockHom7 e hcard).symm).trans
    (AlgEquiv.ofInjective _ (blockHom7_injective e hcard)).symm).trans
    ((AlgEquiv.ofInjective _ (extEmbed_injective W hW1 hW2 hNI)).trans
      (Subalgebra.equivOfEq _ _ (range_extEmbed ρ W hW1 hW2 hM)))

/-- The centre of a subalgebra transported along an algebra isomorphism. -/
def centerCongr {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) : Subalgebra.center R A ≃ₗ[R] Subalgebra.center R B where
  toFun x := ⟨f x, Subalgebra.mem_center_iff.mpr fun b => by
    rw [← f.apply_symm_apply b, ← map_mul, ← map_mul,
      Subalgebra.mem_center_iff.mp x.2 (f.symm b)]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  invFun y := ⟨f.symm y, Subalgebra.mem_center_iff.mpr fun a => by
    rw [← f.symm_apply_apply a, ← map_mul, ← map_mul,
      Subalgebra.mem_center_iff.mp y.2 (f a)]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- The centre of `blockAlgebra` (`Subalgebra.center`) is the subspace
`InternalDeficit.centre` of `M₇(ℂ)`. -/
def centreEquivCenter : InternalDeficit.centre ≃ₗ[ℂ] Subalgebra.center ℂ blockAlgebra where
  toFun X := ⟨⟨X.1, X.2.1⟩, Subalgebra.mem_center_iff.mpr fun Y =>
    Subtype.ext (X.2.2 Y.1 Y.2).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun Z := ⟨Z.1.1, Z.1.2, fun Y hY =>
    (congrArg Subtype.val (Subalgebra.mem_center_iff.mp Z.2 ⟨Y, hY⟩)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The centre of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` has dimension four. -/
theorem finrank_center_blockAlgebra : finrank ℂ (Subalgebra.center ℂ blockAlgebra) = 4 := by
  rw [← centreEquivCenter.finrank_eq, InternalDeficit.finrank_centre]

/-- A generating set of a subalgebra `S`, read inside `S`, generates `S`. -/
theorem adjoin_preimage_val_eq_top {A : Type*} [Semiring A] [Algebra ℂ A] (S : Subalgebra ℂ A)
    (s : Set A) (hs : s ⊆ S) (h : Algebra.adjoin ℂ s = S) :
    Algebra.adjoin ℂ (Subtype.val ⁻¹' s : Set S) = ⊤ := by
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have himg : (S.val '' (Subtype.val ⁻¹' s : Set S)) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [himg, h]

/-- The generators of the concrete theorem lie in the block algebra. -/
theorem gens_subset_blockAlgebra {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    {h : Fin 7 → ℂ} (hw : InternalDeficit.WeakSupported h) :
    baseGens ∪ bridgeGens u ∪ routerGen h ⊆ (blockAlgebra : Set (Matrix (Fin 7) (Fin 7) ℂ)) :=
  Set.Subset.trans Algebra.subset_adjoin (InternalDeficit.adjoin_le_blockAlgebra hsupp hw)

end Iso

/-! ### The reciprocal alternative of (I1) -/

section Reciprocal

open ReciprocalReturnMass

variable {V N T H G' : Type} [Fintype V] [Fintype N] [DecidableEq N] [Fintype T] [Fintype H]

/-- Compression of an `H_priv ← T` corner `r` (the returned word `r_{g,k}` of a mediator
bank) onto the census colour three-space: the type line `T` is coordinate `0` and the
private plane `H_priv` is `{1, 2}`. -/
def bankWord7 [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.single 1 0 (r (eH.symm 0) default) + Matrix.single 2 0 (r (eH.symm 1) default)

theorem bankWord7_colourSupported [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) :
    ColourSupported (bankWord7 eH r) := by
  intro i j hij
  simp only [bankWord7, Matrix.add_apply, Matrix.single_apply]
  rw [if_neg, if_neg, add_zero]
  · rintro ⟨rfl, rfl⟩
    exact hij ⟨by decide, by decide⟩
  · rintro ⟨rfl, rfl⟩
    exact hij ⟨by decide, by decide⟩

theorem bankWord7_apply_one_zero [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) :
    bankWord7 eH r 1 0 = r (eH.symm 0) default := by
  simp [bankWord7]

theorem bankWord7_apply_two_zero [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) :
    bankWord7 eH r 2 0 = r (eH.symm 1) default := by
  simp [bankWord7]

theorem bankWord7_apply_zero_one [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) :
    bankWord7 eH r 0 1 = 0 := by
  simp [bankWord7]

theorem bankWord7_apply_zero_two [Unique T] (eH : H ≃ Fin 2) (r : Matrix H T ℂ) :
    bankWord7 eH r 0 2 = 0 := by
  simp [bankWord7]

/-- A nonzero `H_priv ← T` corner compresses to a colour bridge: `ω_col > 0`. -/
theorem omega7_bankWord7_pos [Unique T] (eH : H ≃ Fin 2) {r : Matrix H T ℂ} (hr : r ≠ 0) :
    0 < omega7 (bankWord7 eH r) := by
  rw [omega7, bankWord7_apply_one_zero, bankWord7_apply_two_zero, bankWord7_apply_zero_one,
    bankWord7_apply_zero_two, Complex.normSq_zero, add_zero, add_zero]
  have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have hne : r (eH.symm 0) default ≠ 0 ∨ r (eH.symm 1) default ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hr
    ext i j
    rw [Unique.eq_default j, Matrix.zero_apply]
    rcases hfin (eH i) with h | h
    · have h0 := hcon.1
      rwa [← h, Equiv.symm_apply_apply] at h0
    · have h1 := hcon.2
      rwa [← h, Equiv.symm_apply_apply] at h1
  have h1 := Complex.normSq_nonneg (r (eH.symm 0) default)
  have h2 := Complex.normSq_nonneg (r (eH.symm 1) default)
  rcases hne with h | h
  · have := Complex.normSq_pos.mpr h
    linarith
  · have := Complex.normSq_pos.mpr h
    linarith

/-- **The reciprocal alternative of (I1)**: the represented word `u` is the compression
onto the census colour three-space of a nonzero returned word `r_{g,k} = B^*(v_g ⊗ h^k) A`
of an admitted reciprocal mediator bank (`thm:reciprocal-return`: such a word exists
exactly when `m_ret > 0`, `ReciprocalReturnMass.mass_pos_iff`). -/
def ReciprocalBridge (u : Matrix (Fin 7) (Fin 7) ℂ) : Prop :=
  ∃ (V N T H G' : Type) (_ : Fintype V) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype T)
    (_ : Unique T) (_ : Fintype H) (eH : H ≃ Fin 2) (v : G' → Matrix V V ℂ) (h : Matrix N N ℂ)
    (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ) (g : G') (k : ℕ),
    word v h A B g k ≠ 0 ∧ u = bankWord7 eH (word v h A B g k)

/-- `m_ret > 0` at horizon `n` supplies a represented reciprocal bridge word. -/
theorem reciprocalBridge_of_mass_pos [Unique T] [DecidableEq V] [Fintype G'] [Group G']
    (eH : H ≃ Fin 2)
    (v : G' → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ) (B : Matrix (V × N) H ℂ)
    {m : ℕ} (hmass : 0 < mass v h A B m) :
    ∃ (g : G') (k : ℕ), word v h A B g k ≠ 0 ∧
      ReciprocalBridge (bankWord7 eH (word v h A B g k)) := by
  obtain ⟨g, k, hk⟩ := (mass_pos_iff v h A B m).mp hmass
  exact ⟨g, k, hk, V, N, T, H, G', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, eH, v, h, A, B, g, k, hk, rfl⟩

/-- A reciprocal bridge word is colour-supported with `ω_col > 0`. -/
theorem colourSupported_omega7_pos_of_reciprocalBridge {u : Matrix (Fin 7) (Fin 7) ℂ}
    (hb : ReciprocalBridge u) : ColourSupported u ∧ 0 < omega7 u := by
  obtain ⟨V, N, T, H, G', _, _, _, _, _, _, eH, v, h, A, B, g, k, hk, rfl⟩ := hb
  exact ⟨bankWord7_colourSupported eH _, omega7_bankWord7_pos eH hk⟩

end Reciprocal

/-! ### The theorem -/

section Main

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]
  {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- **`thm:internal-seed-saturation`, `ω_col > 0` branch of (I1).**  Let `ρ` be the
external action, with isotypic decomposition data `(ι, I, J, W)` as furnished by
`thm:active-isotypic` (`W` unitary, nonempty external factors,
`Wᴴ 𝒜'_ext W = ⊕_b 1 ⊗ M_{J b}(ℂ)`), and suppose the multiplicity census is `(3, 2, 1, 1)`
(`e : ι ≃ Fin 4`, `|J (e.symm k)| = ![3, 2, 1, 1] k`).  Let the represented words be the
transported generators: the type line, the private units and a colour-supported word `u`
with `ω_col(u) > 0` (I1), a weak router `h` (I2), the two multiplicity-one scalar sectors
(I3) and the independent central supports (I4).  Then there is a unital algebra
isomorphism `Φ : M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ ≃ₐ 𝒜'_ext` such that the algebra generated by the
represented words is `𝒜'_ext` (`eq:active-internal-algebra`), of complex dimension
`15`, with centre of dimension `4`, and the two nonabelian sectors have `9` and `4`
matrix entries. -/
theorem internal_seed_saturation_of_bridge (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
        matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    (e : ι ≃ Fin 4) (hcard : ∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k)
    {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u) (hpos : 0 < omega7 u)
    {h : Fin 7 → ℂ} (hr : Router h) :
    ∃ Φ : blockAlgebra ≃ₐ[ℂ] extCommutant ρ,
      Algebra.adjoin ℂ (((extCommutant ρ).val.comp Φ.toAlgHom) ''
          (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) = extCommutant ρ ∧
      finrank ℂ (extCommutant ρ) = 15 ∧
      finrank ℂ (Subalgebra.center ℂ (extCommutant ρ)) = 4 ∧
      finrank ℂ (Matrix (J (e.symm 0)) (J (e.symm 0)) ℂ) = 9 ∧
      finrank ℂ (Matrix (J (e.symm 1)) (J (e.symm 1)) ℂ) = 4 := by
  set Φ := censusCommutantEquiv ρ W hW1 hW2 hNI hM e hcard
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← AlgHom.map_adjoin,
      adjoin_preimage_val_eq_top blockAlgebra _ (gens_subset_blockAlgebra hsupp hr.1)
        (InternalDeficit.adjoin_both_eq_blockAlgebra hsupp hpos hr),
      Algebra.map_top]
    ext x
    rw [AlgHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact (Φ y).2
    · intro hx
      refine ⟨Φ.symm ⟨x, hx⟩, ?_⟩
      show ((Φ (Φ.symm ⟨x, hx⟩) : extCommutant ρ) : Matrix n n ℂ) = x
      rw [AlgEquiv.apply_symm_apply]
  · rw [← Φ.toLinearEquiv.finrank_eq, CentralSeparation.finrank_blockAlgebra]
  · rw [← (centerCongr Φ).finrank_eq, finrank_center_blockAlgebra]
  · rw [Module.finrank_matrix, hcard, Module.finrank_self]
    decide
  · rw [Module.finrank_matrix, hcard, Module.finrank_self]
    decide

/-- **`thm:internal-seed-saturation`.**  As `internal_seed_saturation_of_bridge`, with
(I1) in its full form: either the represented colour-supported word `u` has
`ω_col(u) > 0`, or `u` is the compression of a returned word of an admitted reciprocal
mediator bank with `m_ret > 0` (`ReciprocalBridge u`; `thm:reciprocal-return` supplies
the represented bridge, `reciprocalBridge_of_mass_pos`). -/
theorem internal_seed_saturation (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
        matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    (e : ι ≃ Fin 4) (hcard : ∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k)
    {u : Matrix (Fin 7) (Fin 7) ℂ}
    (hI1 : (ColourSupported u ∧ 0 < omega7 u) ∨ ReciprocalBridge u)
    {h : Fin 7 → ℂ} (hr : Router h) :
    ∃ Φ : blockAlgebra ≃ₐ[ℂ] extCommutant ρ,
      Algebra.adjoin ℂ (((extCommutant ρ).val.comp Φ.toAlgHom) ''
          (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) = extCommutant ρ ∧
      finrank ℂ (extCommutant ρ) = 15 ∧
      finrank ℂ (Subalgebra.center ℂ (extCommutant ρ)) = 4 ∧
      finrank ℂ (Matrix (J (e.symm 0)) (J (e.symm 0)) ℂ) = 9 ∧
      finrank ℂ (Matrix (J (e.symm 1)) (J (e.symm 1)) ℂ) = 4 := by
  obtain ⟨hsupp, hpos⟩ := hI1.elim id colourSupported_omega7_pos_of_reciprocalBridge
  exact internal_seed_saturation_of_bridge ρ W hW1 hW2 hNI hM e hcard hsupp hpos hr

/-- **`thm:internal-seed-saturation` for a unitary external action**, with the isotypic
decomposition data produced by `thm:active-isotypic`
(`ExternalIsotypic.external_isotypic`): for every unitary `ρ` there are sectors `ι`,
external factors `I b`, multiplicity spaces `J b` and a unitary `W` with
`Wᴴ 𝒜'_ext W = ⊕_b 1 ⊗ M_{J b}(ℂ)`, such that whenever the census is `(3, 2, 1, 1)` and
(I1)–(I4) hold, `𝒜^word_int = 𝒜'_ext ≅ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` with dimension `15`, centre of
dimension `4`, and nonabelian sectors of `9` and `4` entries. -/
theorem internal_seed_saturation_of_unitary [Fintype G] (ρ : G →* Matrix n n ℂ)
    (hunit : ∀ g, (ρ g)ᴴ = ρ g⁻¹) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (fun x => Wᴴ * x * W) ''
          matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) =
        multBlockSet I J ∧
      ∀ (e : ι ≃ Fin 4), (∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k) →
        ∀ {u : Matrix (Fin 7) (Fin 7) ℂ},
          (ColourSupported u ∧ 0 < omega7 u) ∨ ReciprocalBridge u →
          ∀ {h : Fin 7 → ℂ}, Router h →
          ∃ Φ : blockAlgebra ≃ₐ[ℂ] extCommutant ρ,
            Algebra.adjoin ℂ (((extCommutant ρ).val.comp Φ.toAlgHom) ''
                (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) = extCommutant ρ ∧
            finrank ℂ (extCommutant ρ) = 15 ∧
            finrank ℂ (Subalgebra.center ℂ (extCommutant ρ)) = 4 ∧
            finrank ℂ (Matrix (J (e.symm 0)) (J (e.symm 0)) ℂ) = 9 ∧
            finrank ℂ (Matrix (J (e.symm 1)) (J (e.symm 1)) ℂ) = 4 := by
  obtain ⟨ι, _, _, I, J, _, _, _, _, W, _, hW1, hW2, hNI, hNJ, _, _, _, _, _, hM, _⟩ :=
    external_isotypic ρ hunit
  refine ⟨ι, inferInstance, inferInstance, I, J, inferInstance, inferInstance, inferInstance,
    inferInstance, W, hW1, hW2, hNI, hNJ, hM, ?_⟩
  intro e hcard u hI1 h hr
  exact internal_seed_saturation ρ W hW1 hW2 hNI hM e hcard hI1 hr

end Main

end InternalSeedSaturation
end RenewalGeometry
