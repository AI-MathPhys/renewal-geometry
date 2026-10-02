/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Boundary resets enlarge a block algebra to the full matrix algebra

Paper label: `prop:ncg-boundary-enlargement` (predictive spectral geometry).

The physical memory is `ℂ^n` (`n` a finite type, `N = card n`), the distinguished source
preparations are the diagonal matrix units `p_u = |e_u⟩⟨e_u|` (`BoundaryReset.sourcePrep`),
and memory operators carry the Hilbert–Schmidt inner product `⟪X, Y⟫ = Tr(Xᴴ Y)`
(`BoundaryReset.hsInner`).

* `reset u` is the superoperator `𝓡_u(X) = Tr(X) p_u`; `resetAdjoint u` (`Y ↦ Y_uu · 1`) is
  its Hilbert–Schmidt adjoint (`hsInner_reset`), and the unique one (`resetAdjoint_unique`).
* The source span `𝒱 = span{p_u}` is the image of `diagonal : (n → ℂ) → Matrix n n ℂ`, an
  HS isometry (`hsInner_diagonal`).  `𝓡_u` acts on it as the rank-one matrix `|e_u⟩⟨𝟏|`
  (`reset_diagonal`), `𝓡_u^*` as `|𝟏⟩⟨e_u|` (`resetAdjoint_diagonal`), and the products act as
  `𝓡_u 𝓡_v^* = N |e_u⟩⟨e_v|` (`reset_resetAdjoint_diagonal`,
  `resetSourceMatrix_mul_conjTranspose`).
* `adjoin_resetProducts_eq_top`: these products generate `M_N(ℂ)` as an algebra;
  `adjoin_sup_resetProducts_eq_top` / `lt_adjoin_sup_resetProducts`: adjoining them to any
  proper subalgebra (e.g. a proper block algebra `⊕ M_{n_λ} ⊗ I_{m_λ}`) yields all of
  `M_N(ℂ)`, so the block structure is destroyed; `exists_proper_subalgebra` shows proper
  subalgebras exist as soon as `N ≥ 2`.
-/

namespace RenewalGeometry
namespace BoundaryReset

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hilbert–Schmidt inner product `⟪X, Y⟫ = Tr(Xᴴ Y)` on memory operators. -/
def hsInner (X Y : Matrix n n ℂ) : ℂ := (Xᴴ * Y).trace

/-- The HS inner product is nondegenerate in its first slot. -/
theorem hsInner_left_eq_iff {A B : Matrix n n ℂ} :
    (∀ X, hsInner A X = hsInner B X) ↔ A = B := by
  refine ⟨fun h => ?_, fun h _ => h ▸ rfl⟩
  have h1 := h (A - B)
  have h2 : ((A - B)ᴴ * (A - B)).trace = 0 := by
    rw [conjTranspose_sub, Matrix.sub_mul, trace_sub]
    simp only [hsInner] at h1
    rw [h1, sub_self]
  exact sub_eq_zero.1 (trace_conjTranspose_mul_self_eq_zero_iff.1 h2)

/-- The distinguished source preparation `p_u = |e_u⟩⟨e_u|` (`prop:ncg-boundary-enlargement`). -/
def sourcePrep (u : n) : Matrix n n ℂ := Matrix.single u u 1

/-- The reset superoperator `𝓡_u(X) = Tr(X) p_u` (`prop:ncg-boundary-enlargement`). -/
def reset (u : n) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := X.trace • sourcePrep u
  map_add' X Y := by rw [trace_add, add_smul]
  map_smul' c X := by rw [trace_smul, smul_eq_mul, mul_smul]; rfl

/-- The Hilbert–Schmidt adjoint of the reset: `𝓡_u^*(Y) = Y_uu · 1`. -/
def resetAdjoint (u : n) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun Y := Y u u • (1 : Matrix n n ℂ)
  map_add' X Y := by rw [Matrix.add_apply, add_smul]
  map_smul' c X := by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]; rfl

theorem reset_apply (u : n) (X : Matrix n n ℂ) : reset u X = X.trace • sourcePrep u := rfl

theorem resetAdjoint_apply (u : n) (Y : Matrix n n ℂ) :
    resetAdjoint u Y = Y u u • (1 : Matrix n n ℂ) := rfl

/-- `resetAdjoint u` is the Hilbert–Schmidt adjoint of `reset u`:
`⟪Y, 𝓡_u X⟫ = ⟪𝓡_u^* Y, X⟫`. -/
theorem hsInner_reset (u : n) (X Y : Matrix n n ℂ) :
    hsInner Y (reset u X) = hsInner (resetAdjoint u Y) X := by
  simp only [hsInner, reset_apply, resetAdjoint_apply, sourcePrep, conjTranspose_smul,
    conjTranspose_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, trace_smul,
    smul_eq_mul]
  rw [trace_mul_single]
  simp [conjTranspose_apply, mul_comm]

/-- Uniqueness of the Hilbert–Schmidt adjoint of a reset. -/
theorem resetAdjoint_unique (u : n) (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hΨ : ∀ X Y, hsInner Y (reset u X) = hsInner (Ψ Y) X) : Ψ = resetAdjoint u := by
  ext1 Y
  exact hsInner_left_eq_iff.1 fun X => (hΨ X Y).symm.trans (hsInner_reset u X Y)

/-- The source span `𝒱 = span{p_u}` is the image of the diagonal embedding. -/
theorem diagonal_eq_sum_sourcePrep (x : n → ℂ) :
    diagonal x = ∑ u, x u • sourcePrep u := by
  ext i j
  simp only [sourcePrep, Matrix.sum_apply, Matrix.smul_apply, single_apply, smul_eq_mul,
    diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hk
    · exact absurd (hk.1.symm.trans hk.2) hij
    · rfl

/-- The diagonal embedding `x ↦ ∑ x_u p_u` is a Hilbert–Schmidt isometry onto the source
span. -/
theorem hsInner_diagonal (x y : n → ℂ) : hsInner (diagonal x) (diagonal y) = star x ⬝ᵥ y := by
  simp [hsInner, diagonal_conjTranspose, diagonal_mul_diagonal, trace_diagonal, dotProduct]

/-- The rank-one source matrix `|e_u⟩⟨𝟏|` (row `u` all ones). -/
def resetSourceMatrix (u : n) : Matrix n n ℂ := Matrix.of fun a _ => if a = u then 1 else 0

/-- On the source span, `𝓡_u` acts as `|e_u⟩⟨𝟏|`. -/
theorem reset_diagonal (u : n) (x : n → ℂ) :
    reset u (diagonal x) = diagonal (resetSourceMatrix u *ᵥ x) := by
  ext i j
  simp only [reset_apply, trace_diagonal, sourcePrep, Matrix.smul_apply, single_apply,
    smul_eq_mul, diagonal_apply, resetSourceMatrix, mulVec, dotProduct, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hiu : i = u
    · subst hiu; simp
    · simp [hiu, Ne.symm hiu]
  · simp [hij]; intro h1 h2; exact absurd (h1.symm.trans h2) hij

/-- On the source span, `𝓡_u^*` acts as `|𝟏⟩⟨e_u| = (|e_u⟩⟨𝟏|)ᴴ`. -/
theorem resetAdjoint_diagonal (u : n) (x : n → ℂ) :
    resetAdjoint u (diagonal x) = diagonal ((resetSourceMatrix u)ᴴ *ᵥ x) := by
  ext i j
  simp only [resetAdjoint_apply, diagonal_apply, Matrix.smul_apply, one_apply, smul_eq_mul,
    resetSourceMatrix, mulVec, dotProduct, conjTranspose_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The source matrices multiply to matrix units: `|e_u⟩⟨𝟏| (|e_v⟩⟨𝟏|)ᴴ = N |e_u⟩⟨e_v|`. -/
theorem resetSourceMatrix_mul_conjTranspose (u v : n) :
    resetSourceMatrix u * (resetSourceMatrix v)ᴴ = (Fintype.card n : ℂ) • single u v 1 := by
  ext i j
  simp only [resetSourceMatrix, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    Matrix.smul_apply, single_apply, smul_eq_mul]
  by_cases hiu : i = u
  · by_cases hjv : j = v
    · subst hiu; subst hjv; simp
    · simp [hjv, Ne.symm hjv]
  · simp [hiu]
    intro h1
    exact absurd h1.symm hiu

/-- **Products of resets with HS adjoints on the source span**:
`𝓡_u 𝓡_v^* (∑ x_w p_w) = ∑_w (N |e_u⟩⟨e_v| x)_w p_w`. -/
theorem reset_resetAdjoint_diagonal (u v : n) (x : n → ℂ) :
    reset u (resetAdjoint v (diagonal x))
      = diagonal (((Fintype.card n : ℂ) • single u v 1) *ᵥ x) := by
  rw [resetAdjoint_diagonal, reset_diagonal, mulVec_mulVec,
    resetSourceMatrix_mul_conjTranspose]

/-- The set of source-span matrices of the products `𝓡_u 𝓡_v^*`. -/
def resetProducts (n : Type*) [Fintype n] [DecidableEq n] : Set (Matrix n n ℂ) :=
  {M | ∃ u v : n, M = resetSourceMatrix u * (resetSourceMatrix v)ᴴ}

/-- Every element of `resetProducts n` is the source-span matrix of a product
`𝓡_u 𝓡_v^*`, i.e. it represents that superoperator on `𝒱`. -/
theorem resetProducts_represent {M : Matrix n n ℂ} (hM : M ∈ resetProducts n) :
    ∃ u v : n, ∀ x : n → ℂ, reset u (resetAdjoint v (diagonal x)) = diagonal (M *ᵥ x) := by
  obtain ⟨u, v, rfl⟩ := hM
  exact ⟨u, v, fun x => by
    rw [reset_resetAdjoint_diagonal, resetSourceMatrix_mul_conjTranspose]⟩

/-- **Proposition `prop:ncg-boundary-enlargement`**: on the source span, the products of the
resets with their Hilbert–Schmidt adjoints generate the full matrix algebra `M_N(ℂ)`. -/
theorem adjoin_resetProducts_eq_top :
    Algebra.adjoin ℂ (resetProducts n) = ⊤ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  have hN : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := n)).ne'
  rw [eq_top_iff]
  intro A _
  rw [matrix_eq_sum_single A]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
  have hmem : resetSourceMatrix i * (resetSourceMatrix j)ᴴ ∈ Algebra.adjoin ℂ (resetProducts n) :=
    Algebra.subset_adjoin ⟨i, j, rfl⟩
  rw [resetSourceMatrix_mul_conjTranspose] at hmem
  have h2 := Subalgebra.smul_mem _ hmem (A i j / (Fintype.card n : ℂ))
  rwa [smul_smul, div_mul_cancel₀ _ hN, smul_single, smul_eq_mul, mul_one] at h2

/-- Adjoining the reset products to any subalgebra (e.g. a block algebra
`⊕_λ M_{n_λ}(ℂ) ⊗ I_{m_λ}`) yields the full matrix algebra. -/
theorem adjoin_sup_resetProducts_eq_top (𝒜 : Subalgebra ℂ (Matrix n n ℂ)) :
    Algebra.adjoin ℂ ((𝒜 : Set (Matrix n n ℂ)) ∪ resetProducts n) = ⊤ := by
  rw [eq_top_iff, ← adjoin_resetProducts_eq_top]
  exact Algebra.adjoin_mono Set.subset_union_right

/-- **The block algebra is destroyed**: a proper subalgebra is strictly enlarged by
promoting the boundary preparations (resets) to internal generators. -/
theorem lt_adjoin_sup_resetProducts {𝒜 : Subalgebra ℂ (Matrix n n ℂ)} (h𝒜 : 𝒜 ≠ ⊤) :
    𝒜 < Algebra.adjoin ℂ ((𝒜 : Set (Matrix n n ℂ)) ∪ resetProducts n) := by
  rw [adjoin_sup_resetProducts_eq_top]
  exact lt_top_iff_ne_top.2 h𝒜

/-- For `N ≥ 2`, proper subalgebras of `M_N(ℂ)` exist (e.g. the scalar block algebra
`M_1(ℂ) ⊗ I_N`), so the enlargement of `lt_adjoin_sup_resetProducts` is a genuine one. -/
theorem exists_proper_subalgebra (hN : 2 ≤ Fintype.card n) :
    ∃ 𝒜 : Subalgebra ℂ (Matrix n n ℂ), 𝒜 ≠ ⊤ := by
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card hN
  refine ⟨⊥, fun h => ?_⟩
  have hmem : (single u v (1 : ℂ)) ∈ (⊥ : Subalgebra ℂ (Matrix n n ℂ)) := h ▸ Algebra.mem_top
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hmem
  have h0 := congrFun (congrFun hc u) v
  rw [algebraMap_eq_diagonal, diagonal_apply_ne _ huv] at h0
  simp at h0

end BoundaryReset
end RenewalGeometry
