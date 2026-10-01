/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.VaryingHilbertMosco

/-!
# Finite protected basis transport

Covers `lem:protected-basis-transport` of the spacetime–gauge duality paper.

For finite-dimensional protected subspaces `M_X ⊆ ℋ_X` of a fixed dimension `m` with
orthonormal bases `e_{a,X}`, transported to a common carrier `ℋ` by isometries `J_X`, the
transported orthogonal projections `P̂_X = J_X P_{M_X} J_X^*` are the sums of rank-one
projections onto the transported basis vectors, and
`‖P̂_X − P̂_∞‖ ≤ 2 m η_X` with `η_X = max_a ‖J_X e_{a,X} − J_∞ e_{a,∞}‖`.

* `norm_rankOne_self_sub_le`: `‖|u⟩⟨u| − |v⟩⟨v|‖ ≤ 2 ‖u − v‖` for unit vectors.
* `transportedProjection`: `Σ_a |u_a⟩⟨u_a|`.
* `transportedProjection_eq_conj_starProjection`: `J P_M J^* = Σ_a |J e_a⟩⟨J e_a|` for an
  orthonormal basis `e` of `M` and a linear isometry `J`.
* `norm_transportedProjection_sub_le`: the estimate `2 · card ι · η`.
* `System.protectedBasisTransport_exact`: the lemma on a varying Hilbert system —
  the bound `eq:protected-projection-transport` and `‖P̂_X − P̂_∞‖ → 0` from `η_X → 0`.
* `protectedAlgebraTransport`: the `*`-isomorphism clause (products and adjoints are
  identified across cutoffs through the specified unital `*`-isomorphisms).
-/

open Filter Topology InnerProductSpace

namespace RenewalGeometry.VaryingHilbert

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `|u⟩⟨u| − |v⟩⟨v| = |u − v⟩⟨u| + |v⟩⟨u − v|`. -/
theorem rankOne_self_sub_rankOne_self (u v : H) :
    rankOne ℂ u u - rankOne ℂ v v = rankOne ℂ (u - v) u + rankOne ℂ v (u - v) := by
  ext x
  simp only [sub_apply, add_apply, rankOne_apply,
    inner_sub_left, sub_smul, smul_sub]
  abel

/-- For unit vectors `u, v`: `‖|u⟩⟨u| − |v⟩⟨v|‖ ≤ 2 ‖u − v‖`. -/
theorem norm_rankOne_self_sub_le (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖rankOne ℂ u u - rankOne ℂ v v‖ ≤ 2 * ‖u - v‖ := by
  rw [rankOne_self_sub_rankOne_self]
  calc ‖rankOne ℂ (u - v) u + rankOne ℂ v (u - v)‖
      ≤ ‖rankOne ℂ (u - v) u‖ + ‖rankOne ℂ v (u - v)‖ := norm_add_le _ _
    _ = ‖u - v‖ * ‖u‖ + ‖v‖ * ‖u - v‖ := by rw [norm_rankOne, norm_rankOne]
    _ = 2 * ‖u - v‖ := by rw [hu, hv]; ring

/-- The transported projection `Σ_a |u_a⟩⟨u_a|` onto the span of a transported
orthonormal family. -/
noncomputable def transportedProjection {ι : Type*} [Fintype ι] (u : ι → H) : H →L[ℂ] H :=
  ∑ a, rankOne ℂ (u a) (u a)

theorem transportedProjection_apply {ι : Type*} [Fintype ι] (u : ι → H) (x : H) :
    transportedProjection u x = ∑ a, inner ℂ (u a) x • u a := by
  simp [transportedProjection]

/-- Summing the rank-one estimate over the `m` basis vectors:
`‖Σ_a |u_a⟩⟨u_a| − Σ_a |v_a⟩⟨v_a|‖ ≤ 2 m η` whenever `‖u_a − v_a‖ ≤ η` for all `a`. -/
theorem norm_transportedProjection_sub_le {ι : Type*} [Fintype ι] (u v : ι → H)
    (hu : ∀ a, ‖u a‖ = 1) (hv : ∀ a, ‖v a‖ = 1) (η : ℝ) (hη : ∀ a, ‖u a - v a‖ ≤ η) :
    ‖transportedProjection u - transportedProjection v‖ ≤ 2 * Fintype.card ι * η := by
  unfold transportedProjection
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ a, (rankOne ℂ (u a) (u a) - rankOne ℂ (v a) (v a))‖
      ≤ ∑ a, ‖rankOne ℂ (u a) (u a) - rankOne ℂ (v a) (v a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ι, 2 * η := Finset.sum_le_sum fun a _ =>
        (norm_rankOne_self_sub_le _ _ (hu a) (hv a)).trans
          (mul_le_mul_of_nonneg_left (hη a) (by norm_num))
    _ = 2 * Fintype.card ι * η := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end RankOne

section Projection

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The orthogonal projection onto a subspace with orthonormal basis `e` is
`Σ_a |e_a⟩⟨e_a|`. -/
theorem starProjection_eq_transportedProjection {ι : Type*} [Fintype ι]
    (M : Submodule ℂ E) [M.HasOrthogonalProjection] (e : ι → E) (he : Orthonormal ℂ e)
    (hspan : Submodule.span ℂ (Set.range e) = M) :
    M.starProjection = transportedProjection e := by
  ext x
  rw [transportedProjection_apply]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← hspan]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro w hw
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [inner_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [inner_smul_right, inner_sub_left, he.inner_left_fintype]
    simp

/-- **Transport of protected projections.**  For a linear isometry `J : E → H` and an
orthonormal basis `e` of `M ⊆ E`, the transported projection `J P_M J^*` is the sum of the
rank-one projections onto the transported basis vectors `J e_a`. -/
theorem transportedProjection_eq_conj_starProjection {ι : Type*} [Fintype ι]
    [CompleteSpace E] [CompleteSpace H]
    (J : E →ₗᵢ[ℂ] H) (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (e : ι → E) (he : Orthonormal ℂ e) (hspan : Submodule.span ℂ (Set.range e) = M) :
    J.toContinuousLinearMap ∘L M.starProjection ∘L
        ContinuousLinearMap.adjoint J.toContinuousLinearMap =
      transportedProjection (fun a => J (e a)) := by
  rw [starProjection_eq_transportedProjection M e he hspan]
  ext x
  simp only [ContinuousLinearMap.comp_apply, transportedProjection_apply, map_sum, map_smul,
    LinearIsometry.coe_toContinuousLinearMap]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap]

end Projection

section System

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Hn : ℕ → Type*} [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace ℂ (Hn n)]
variable {Elim : Type*} [NormedAddCommGroup Elim] [InnerProductSpace ℂ Elim]

namespace System

variable (J : System (K := ℂ) (H := H) (Hn := Hn))

/-- The transported protected projection `P̂_X = Σ_a |J_X e_{a,X}⟩⟨J_X e_{a,X}|`
(`= J_X P_{M_X} J_X^*` by `transportedProjection_eq_conj_starProjection`). -/
noncomputable def protectedProjection {ι : Type*} [Fintype ι] (e : ∀ X, ι → Hn X) (X : ℕ) :
    H →L[ℂ] H :=
  transportedProjection fun a => J.embedding X (e X a)

/-- The basis transport defect `η_X = max_a ‖J_X e_{a,X} − J_∞ e_{a,∞}‖`
(`eq:protected-basis-transport`), as a supremum over the finite index. -/
noncomputable def basisTransportDefect {ι : Type*} [Fintype ι] (e : ∀ X, ι → Hn X)
    (Jlim : Elim →ₗᵢ[ℂ] H) (elim : ι → Elim) (X : ℕ) : ℝ :=
  ⨆ a, ‖J.embedding X (e X a) - Jlim (elim a)‖

theorem norm_sub_le_basisTransportDefect {ι : Type*} [Fintype ι] (e : ∀ X, ι → Hn X)
    (Jlim : Elim →ₗᵢ[ℂ] H) (elim : ι → Elim) (X : ℕ) (a : ι) :
    ‖J.embedding X (e X a) - Jlim (elim a)‖ ≤ J.basisTransportDefect e Jlim elim X := by
  unfold basisTransportDefect
  exact le_ciSup (f := fun a => ‖J.embedding X (e X a) - Jlim (elim a)‖)
    (Set.finite_range _).bddAbove a

/-- **Finite protected basis transport (`lem:protected-basis-transport`).**
With orthonormal bases `e_{a,X}` of the protected spaces (only the unit-vector property is
used) and `η_X` the transport defect `eq:protected-basis-transport`, the transported
projections satisfy `‖P̂_X − P̂_∞‖ ≤ 2 m η_X` (`eq:protected-projection-transport`), and
`η_X → 0` gives `‖P̂_X − P̂_∞‖ → 0`. -/
theorem protectedBasisTransport_exact {ι : Type*} [Fintype ι] (e : ∀ X, ι → Hn X)
    (he : ∀ X a, ‖e X a‖ = 1) (Jlim : Elim →ₗᵢ[ℂ] H) (elim : ι → Elim) (helim : ∀ a, ‖elim a‖ = 1) :
    (∀ X, ‖J.protectedProjection e X - transportedProjection (fun a => Jlim (elim a))‖ ≤
        2 * Fintype.card ι * J.basisTransportDefect e Jlim elim X) ∧
      (Tendsto (J.basisTransportDefect e Jlim elim) atTop (𝓝 0) →
        Tendsto (fun X =>
          ‖J.protectedProjection e X - transportedProjection (fun a => Jlim (elim a))‖)
          atTop (𝓝 0)) := by
  have hbound : ∀ X,
      ‖J.protectedProjection e X - transportedProjection (fun a => Jlim (elim a))‖ ≤
        2 * Fintype.card ι * J.basisTransportDefect e Jlim elim X := by
    intro X
    apply norm_transportedProjection_sub_le
    · intro a
      rw [LinearIsometry.norm_map, he]
    · intro a
      rw [LinearIsometry.norm_map, helim]
    · intro a
      exact J.norm_sub_le_basisTransportDefect e Jlim elim X a
  refine ⟨hbound, fun hη => ?_⟩
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  simpa using hη.const_mul (2 * (Fintype.card ι : ℝ))

end System

end System

section StarTransport

/-- **`*`-isomorphism clause of `lem:protected-basis-transport`.**  If the protected
algebras are images of one fixed finite `C^*`-algebra `A` under specified unital
`*`-isomorphisms `φ_X : A ≃⋆ₐ M_X`, the composite `φ_∞ ∘ φ_X⁻¹` identifies `M_X` with `M_∞`
as a unital `*`-algebra, hence identifies multiplication and adjoints across cutoffs. -/
def protectedAlgebraTransport {A M Mlim : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring M] [Algebra ℂ M] [Star M] [Semiring Mlim] [Algebra ℂ Mlim] [Star Mlim]
    (φ : A ≃⋆ₐ[ℂ] M) (φlim : A ≃⋆ₐ[ℂ] Mlim) : M ≃⋆ₐ[ℂ] Mlim :=
  φ.symm.trans φlim

theorem protectedAlgebraTransport_mul {A M Mlim : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring M] [Algebra ℂ M] [Star M] [Semiring Mlim] [Algebra ℂ Mlim] [Star Mlim]
    (φ : A ≃⋆ₐ[ℂ] M) (φlim : A ≃⋆ₐ[ℂ] Mlim) (x y : M) :
    protectedAlgebraTransport φ φlim (x * y) =
      protectedAlgebraTransport φ φlim x * protectedAlgebraTransport φ φlim y :=
  map_mul _ _ _

theorem protectedAlgebraTransport_star {A M Mlim : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring M] [Algebra ℂ M] [Star M] [Semiring Mlim] [Algebra ℂ Mlim] [Star Mlim]
    (φ : A ≃⋆ₐ[ℂ] M) (φlim : A ≃⋆ₐ[ℂ] Mlim) (x : M) :
    protectedAlgebraTransport φ φlim (star x) = star (protectedAlgebraTransport φ φlim x) :=
  map_star _ _

theorem protectedAlgebraTransport_one {A M Mlim : Type*} [Semiring A] [Algebra ℂ A] [Star A]
    [Semiring M] [Algebra ℂ M] [Star M] [Semiring Mlim] [Algebra ℂ Mlim] [Star Mlim]
    (φ : A ≃⋆ₐ[ℂ] M) (φlim : A ≃⋆ₐ[ℂ] Mlim) :
    protectedAlgebraTransport φ φlim 1 = 1 :=
  map_one _

end StarTransport

end RenewalGeometry.VaryingHilbert
