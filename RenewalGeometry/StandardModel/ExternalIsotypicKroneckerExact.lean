/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.ReciprocalWedderburnKronecker
import RenewalGeometry.Commutant.MatrixFactorNormalForm

open NCG
/-!
# External isotypic algebra and multiplicity census: the general clause
  (`thm:active-isotypic`, spacetime–gauge duality paper)

For a unitary matrix representation `ρ : G →* M_n(ℂ)` of a finite group (the
external tetrahedral action `ρ_r(S_4)` on a finite word-depth carrier) this file
proves the general clause of `thm:active-isotypic`:

* `eq:word-depth-isotypic`: a unitary `W` with
  `Wᴴ ρ(g) W = ⊕_b ρ_b(g) ⊗ 1_{J b}` where the `ρ_b : G →* M_{I b}(ℂ)` are
  irreducible (`external_isotypic` clauses `hfull`, `hirr`) and pairwise
  non-isomorphic (Schur clause `hschur`: no nonzero intertwiner between distinct
  sectors); so `V ≅ ⊕_b V_b ⊗ M_b` with `V_b = ℂ^{I b}` the irreducible external
  factors and `M_b = ℂ^{J b}` the multiplicity spaces, `m_b = |J b|`;
* `eq:external-isotypic`: `Wᴴ C^*(ρ(G)) W = ⊕_b M_{I b}(ℂ) ⊗ I` (Burnside);
* `eq:external-isotypic-commutant`: `Wᴴ C^*(ρ(G))' W = ⊕_b I ⊗ M_{|J b|}(ℂ)` (Schur);
* the consequence clause (`unital_matrix_in_commutant_le_multiplicity`): a unital
  `M_m(ℂ)` inside the relative commutant forces `m ≤ m_b` for every sector `b`
  (in particular for some external irreducible when the carrier is nonzero).

The external `C^*`-algebra is `Algebra.adjoin ℂ (Set.range ρ)`, the linear span of
`ρ(G)`; it is star-closed because `ρ(g)ᴴ = ρ(g⁻¹)`.  The heavy lifting is the
reciprocal Kronecker form `reciprocal_wedderburn`.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace RenewalGeometry
namespace ExternalIsotypic

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Conjugation `x ↦ Wᴴ x W` as a linear map. -/
def conjLin {K : Type} [Fintype K] (W : Matrix n K ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix K K ℂ where
  toFun x := Wᴴ * x * W
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem conjLin_apply {K : Type} [Fintype K] (W : Matrix n K ℂ) (x : Matrix n n ℂ) :
    conjLin W x = Wᴴ * x * W := rfl

theorem conjLin_mul {K : Type} [Fintype K] (W : Matrix n K ℂ) (h2 : W * Wᴴ = 1)
    (x y : Matrix n n ℂ) : conjLin W (x * y) = conjLin W x * conjLin W y := by
  simp only [conjLin_apply]
  calc Wᴴ * (x * y) * W = Wᴴ * x * (W * Wᴴ) * y * W := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = Wᴴ * x * W * (Wᴴ * y * W) := by simp only [Matrix.mul_assoc]

section Blocks

variable {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- The action block of a matrix on `⊕_b ℂ^{I b} ⊗ ℂ^{J b}` at sector `b`, read off along a
fixed multiplicity coordinate `l₀`. -/
def actionBlockLin (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] (b : ι) (l₀ : J b) :
    Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ →ₗ[ℂ] Matrix (I b) (I b) ℂ where
  toFun A := Matrix.of fun i i' => A ⟨b, (i, l₀)⟩ ⟨b, (i', l₀)⟩
  map_add' A B := by ext; simp
  map_smul' c A := by ext; simp

theorem actionBlockLin_actionBlock (b : ι) (l₀ : J b) (X : ∀ b, Matrix (I b) (I b) ℂ) :
    actionBlockLin I J b l₀ (blockDiagonal' fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) = X b := by
  ext i i'
  simp [actionBlockLin, blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]

/-- The multiplicity block of a matrix at sector `b`, read off along a fixed action
coordinate `i₀`. -/
def multBlockLin (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] (b : ι) (i₀ : I b) :
    Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ →ₗ[ℂ] Matrix (J b) (J b) ℂ where
  toFun A := Matrix.of fun l l' => A ⟨b, (i₀, l)⟩ ⟨b, (i₀, l')⟩
  map_add' A B := by ext; simp
  map_smul' c A := by ext; simp

theorem multBlockLin_multBlock (b : ι) (i₀ : I b) (Y : ∀ b, Matrix (J b) (J b) ℂ) :
    multBlockLin I J b i₀ (blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b) = Y b := by
  ext l l'
  simp [multBlockLin, blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]

/-- The block algebra `1 ⊗ M_{J b}` at sector `b` as an algebra map out of a unital
matrix subalgebra of `⊕_b 1 ⊗ M_{J b}`. -/
theorem unital_matrix_le_card {m : ℕ} [NeZero m]
    (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ)
    (hφ : ∀ a, φ a ∈ multBlockSet I J) (b : ι) [Nonempty (I b)] [Nonempty (J b)] :
    m ≤ Fintype.card (J b) := by
  classical
  choose Y hY using hφ
  let i₀ : I b := Classical.arbitrary _
  let ψl : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (J b) (J b) ℂ :=
    (multBlockLin I J b i₀).comp φ.toLinearMap
  have hψ : ∀ a, ψl a = Y a b := by
    intro a
    simp only [ψl, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hY a, multBlockLin_multBlock]
  have hone : (1 : Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ) =
      blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ (1 : Matrix (J b) (J b) ℂ) := by
    simp only [Matrix.one_kronecker_one]
    exact blockDiagonal'_one.symm
  let ψ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix (J b) (J b) ℂ :=
    AlgHom.ofLinearMap ψl
      (by
        simp only [ψl, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one]
        rw [hone, multBlockLin_multBlock])
      (by
        intro a c
        rw [hψ, hψ, hψ]
        have h : φ (a * c) = blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ (Y a b * Y c b) := by
          rw [map_mul, hY a, hY c, ← blockDiagonal'_mul]
          congr 1
          funext b
          rw [← mul_kronecker_mul, Matrix.one_mul]
        have h2 := congrArg (multBlockLin I J b i₀) h
        rw [hY (a * c), multBlockLin_multBlock, multBlockLin_multBlock] at h2
        exact h2)
  let e := Fintype.equivFin (J b)
  let ψ' : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ]
      Matrix (Fin (Fintype.card (J b))) (Fin (Fintype.card (J b))) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom.comp ψ
  obtain ⟨k, hk⟩ := matrix_representation_dimension ψ'
  have hpos : 0 < Fintype.card (J b) := Fintype.card_pos
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  calc m = m * 1 := (mul_one m).symm
    _ ≤ m * k := Nat.mul_le_mul_left m hk1
    _ = Fintype.card (J b) := hk.symm

end Blocks

variable {G : Type} [Group G] [Fintype G]

/-- The external algebra `C^*(ρ(G))` of a unitary representation is star-closed. -/
theorem adjoin_star_closed (ρ : G →* Matrix n n ℂ) (hunit : ∀ g, (ρ g)ᴴ = ρ g⁻¹) :
    ∀ a ∈ Algebra.adjoin ℂ (Set.range ρ), aᴴ ∈ Algebra.adjoin ℂ (Set.range ρ) := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [hunit]
    exact Algebra.subset_adjoin ⟨g⁻¹, rfl⟩
  | algebraMap c =>
    rw [← Matrix.star_eq_conjTranspose, ← algebraMap_star_comm]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.conjTranspose_add]
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.conjTranspose_mul]
    exact Subalgebra.mul_mem _ hy hx

/-- The external algebra is the linear span of `ρ(G)`. -/
theorem adjoin_toSubmodule_eq_span (ρ : G →* Matrix n n ℂ) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range ρ)) =
      Submodule.span ℂ (Set.range ρ) := by
  rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]

/-- **`thm:active-isotypic`, general clause.**  For every unitary representation
`ρ : G →* M_n(ℂ)` of a finite group there are a finite sector set `ι`, index types
`I b` (the irreducible external factors `V_b = ℂ^{I b}`) and `J b` (the multiplicity
spaces `M_b = ℂ^{J b}`), a unitary `W` and irreducible, pairwise non-isomorphic
representations `ρ_b : G →* M_{I b}(ℂ)` such that
`Wᴴ ρ(g) W = ⊕_b ρ_b(g) ⊗ 1` (`eq:word-depth-isotypic`),
`Wᴴ C^*(ρ(G)) W = ⊕_b M_{I b}(ℂ) ⊗ I` (`eq:external-isotypic`) and
`Wᴴ C^*(ρ(G))' W = ⊕_b I ⊗ M_{J b}(ℂ)` (`eq:external-isotypic-commutant`). -/
theorem external_isotypic (ρ : G →* Matrix n n ℂ) (hunit : ∀ g, (ρ g)ᴴ = ρ g⁻¹) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ) (ρb : ∀ b, G →* Matrix (I b) (I b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      -- `eq:word-depth-isotypic`
      (∀ g, Wᴴ * ρ g * W = blockDiagonal' fun b => ρb b g ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) ∧
      -- Burnside: each external factor is full
      (∀ b, Submodule.span ℂ (Set.range (ρb b)) = ⊤) ∧
      -- irreducibility of each external factor
      (∀ b (U : Submodule ℂ (I b → ℂ)), (∀ g, ∀ x ∈ U, ρb b g *ᵥ x ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      -- Schur: distinct sectors carry non-isomorphic representations
      (∀ b b', b ≠ b' → ∀ T : Matrix (I b) (I b') ℂ,
        (∀ g, T * ρb b' g = ρb b g * T) → T = 0) ∧
      -- `eq:external-isotypic`
      (fun x => Wᴴ * x * W) '' (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) =
        actionBlockSet I J ∧
      -- `eq:external-isotypic-commutant`
      (fun x => Wᴴ * x * W) ''
          matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) =
        multBlockSet I J ∧
      -- consequence: a unital `M_m(ℂ)` in the relative commutant needs multiplicity `≥ m`
      (∀ (m : ℕ) [NeZero m] (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix n n ℂ),
        (∀ a, φ a ∈ matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ))) →
        ∀ b, m ≤ Fintype.card (J b)) := by
  classical
  set S := Algebra.adjoin ℂ (Set.range ρ) with hSdef
  obtain ⟨ι, _, _, I, J, _, _, _, _, W, hW1, hW2, hNI, hNJ, hA, hM⟩ :=
    reciprocal_wedderburn S (adjoin_star_closed ρ hunit)
  have hρmem : ∀ g, conjLin W (ρ g) ∈ actionBlockSet I J := by
    intro g
    rw [← hA]
    exact ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  choose X hX using hρmem
  -- block extraction
  let l₀ : ∀ b, J b := fun b => Classical.arbitrary (J b)
  let L : ∀ b, Matrix n n ℂ →ₗ[ℂ] Matrix (I b) (I b) ℂ :=
    fun b => (actionBlockLin I J b (l₀ b)).comp (conjLin W)
  have hLρ : ∀ b g, L b (ρ g) = X g b := by
    intro b g
    simp only [L, LinearMap.comp_apply]
    rw [hX g, actionBlockLin_actionBlock]
  -- the sector representations
  let ρb : ∀ b, G →* Matrix (I b) (I b) ℂ := fun b =>
    { toFun := fun g => X g b
      map_one' := by
        have h : conjLin W (ρ 1) = blockDiagonal'
            (fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) := by
          rw [map_one, conjLin_apply, Matrix.mul_one, hW1]
          simp only [Matrix.one_kronecker_one]
          exact blockDiagonal'_one.symm
        have h2 := congrArg (actionBlockLin I J b (l₀ b)) h
        rw [hX 1, actionBlockLin_actionBlock, actionBlockLin_actionBlock] at h2
        exact h2
      map_mul' := by
        intro g h
        have h1 : conjLin W (ρ (g * h)) = blockDiagonal'
            (fun b => (X g b * X h b) ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) := by
          rw [map_mul, conjLin_mul W hW2, hX g, hX h, ← blockDiagonal'_mul]
          congr 1
          funext b
          rw [← mul_kronecker_mul, Matrix.one_mul]
        have h2 := congrArg (actionBlockLin I J b (l₀ b)) h1
        rw [hX (g * h), actionBlockLin_actionBlock, actionBlockLin_actionBlock] at h2
        exact h2 }
  have hρb : ∀ b g, ρb b g = X g b := fun _ _ => rfl
  have hiso : ∀ g, Wᴴ * ρ g * W = blockDiagonal' fun b => ρb b g ⊗ₖ (1 : Matrix (J b) (J b) ℂ) :=
    fun g => hX g
  -- the linear span of `ρ(G)` is the external algebra
  have hspan : Submodule.span ℂ (Set.range ρ) = Subalgebra.toSubmodule S :=
    (adjoin_toSubmodule_eq_span ρ).symm
  -- every action block is reached from the external algebra
  have hreach : ∀ b (Y : Matrix (I b) (I b) ℂ), ∃ a ∈ S, ∀ b',
      L b' a = Pi.single (M := fun b => Matrix (I b) (I b) ℂ) b Y b' := by
    intro b Y
    have hmem : blockDiagonal' (fun b' => (Pi.single (M := fun b => Matrix (I b) (I b) ℂ) b Y b')
        ⊗ₖ (1 : Matrix (J b') (J b') ℂ)) ∈ actionBlockSet I J := ⟨_, rfl⟩
    rw [← hA] at hmem
    obtain ⟨a, ha, hae⟩ := hmem
    beta_reduce at hae
    refine ⟨a, ha, fun b' => ?_⟩
    simp only [L, LinearMap.comp_apply, conjLin_apply]
    rw [hae, actionBlockLin_actionBlock]
  -- Burnside fullness
  have hfull : ∀ b, Submodule.span ℂ (Set.range (ρb b)) = ⊤ := by
    intro b
    rw [eq_top_iff]
    rintro Y -
    obtain ⟨a, ha, hLa⟩ := hreach b Y
    have hrange : Set.range (ρb b) = L b '' Set.range ρ := by
      rw [← Set.range_comp]
      congr 1
      funext g
      simp only [Function.comp_apply, hρb, hLρ]
    rw [hrange, ← Submodule.map_span, hspan]
    have hY : Y = L b a := by rw [hLa b, Pi.single_eq_same]
    rw [hY]
    exact Submodule.mem_map_of_mem ha
  -- irreducibility
  have hirr : ∀ b (U : Submodule ℂ (I b → ℂ)), (∀ g, ∀ x ∈ U, ρb b g *ᵥ x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro b U hU
    by_cases hbot : U = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      have hinv : ∀ A ∈ Submodule.span ℂ (Set.range (ρb b)), ∀ x ∈ U, A *ᵥ x ∈ U := by
        intro A hA
        induction hA using Submodule.span_induction with
        | mem A hA =>
          obtain ⟨g, rfl⟩ := hA
          exact hU g
        | zero =>
          intro x _
          rw [Matrix.zero_mulVec]
          exact U.zero_mem
        | add A B _ _ ihA ihB =>
          intro x hx
          rw [Matrix.add_mulVec]
          exact U.add_mem (ihA x hx) (ihB x hx)
        | smul c A _ ih =>
          intro x hx
          rw [Matrix.smul_mulVec]
          exact U.smul_mem c (ih x hx)
      rw [eq_top_iff]
      rintro w -
      have hsu : star u ⬝ᵥ u ≠ 0 := fun h => hu0 (dotProduct_star_self_eq_zero.mp h)
      have hAu : ((star u ⬝ᵥ u)⁻¹ • vecMulVec w (star u)) *ᵥ u = w := by
        rw [Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
          inv_mul_cancel₀ hsu, one_smul]
      rw [← hAu]
      exact hinv _ (by rw [hfull b]; exact Submodule.mem_top) u huU
  -- Schur separation of distinct sectors
  have hschur : ∀ b b', b ≠ b' → ∀ T : Matrix (I b) (I b') ℂ,
      (∀ g, T * ρb b' g = ρb b g * T) → T = 0 := by
    intro b b' hbb' T hT
    have hall : ∀ a ∈ Submodule.span ℂ (Set.range ρ), T * L b' a = L b a * T := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨g, rfl⟩ := ha
        rw [hLρ, hLρ, ← hρb, ← hρb]
        exact hT g
      | zero => rw [map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul]
      | add a c _ _ iha ihc => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, iha, ihc]
      | smul c a _ ih => rw [map_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul, ih]
    obtain ⟨a, ha, hLa⟩ := hreach b 1
    have h := hall a (by rw [hspan]; exact ha)
    rw [hLa b, hLa b', Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hbb'), Matrix.mul_zero,
      Matrix.one_mul] at h
    exact h.symm
  -- the multiplicity bound
  have hbound : ∀ (m : ℕ) [NeZero m] (φ : Matrix (Fin m) (Fin m) ℂ →ₐ[ℂ] Matrix n n ℂ),
      (∀ a, φ a ∈ matCommutant (S : Set (Matrix n n ℂ))) → ∀ b, m ≤ Fintype.card (J b) := by
    intro m _ φ hφ b
    let Φ : Matrix n n ℂ →ₐ[ℂ] Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ :=
      AlgHom.ofLinearMap (conjLin W) (by rw [conjLin_apply, Matrix.mul_one, hW1])
        (conjLin_mul W hW2)
    have hΦφ : ∀ a, (Φ.comp φ) a ∈ multBlockSet I J := by
      intro a
      rw [← hM]
      exact ⟨φ a, hφ a, rfl⟩
    haveI := hNI b
    haveI := hNJ b
    exact unital_matrix_le_card (Φ.comp φ) hΦφ b
  exact ⟨ι, inferInstance, inferInstance, I, J, inferInstance, inferInstance, inferInstance,
    inferInstance, W, ρb, hW1, hW2, hNI, hNJ, hiso, hfull, hirr, hschur, hA, hM, hbound⟩

end ExternalIsotypic
end RenewalGeometry
