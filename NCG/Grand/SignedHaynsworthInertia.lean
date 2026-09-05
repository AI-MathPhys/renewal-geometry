/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Signed Feshbach inertia (`thm:GT-signed-Haynsworth`,
  Gran-Tensor manuscript)

A small inertia theory for complex Hermitian matrices,
built variationally (no inertia theory exists in
Mathlib):

* `posInertia M` — the largest dimension of a subspace on
  which the quadratic form `v ↦ re⟨v, Mv⟩` is positive
  definite; `negInertia M := posInertia (-M)`;
  `nullInertia M := n - posInertia M - negInertia M`.

* `posInertia_eq_card_of_eigenbasis`: for a matrix with
  an orthonormal eigenbasis, `posInertia` equals the
  number of positive eigenvalues (the spectral
  computation; both inequalities go through the
  eigenspace splitting and the dimension count
  `dim V + dim N ≤ n` for a positive and a nonpositive
  subspace).

* `sylvester_inertia`: **Sylvester's law of inertia** —
  all three indices are invariant under invertible
  congruence `M ↦ XᴴMX` (the variational sets of
  positive-subspace dimensions transport through the
  linear equivalence `X`).

* `gt_signed_haynsworth`: the boxed SC.9 —
  for Hermitian `H = [[A, B], [Bᴴ, D]]` with the range
  condition `Ran Bᴴ ⊆ Ran D` presented by a Douglas
  solution `W` of `D·W = Bᴴ` (so that
  `Wᴴ·D·W = B·D†·Bᴴ` for the pseudo-inverse solution),
  the congruence by `[[I, 0], [-W, I]]`
  block-diagonalizes `H`, and
  `In(H) = In(A - Wᴴ·D·W) + In(D)` in all three signed
  indices.

The identification of the abstract nuisance/tail short
with this matrix Feshbach block form is the manuscript's
assembly layer.
-/

open Matrix Finset Module

namespace NCG

section Inertia

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The (real) quadratic form of a complex matrix. -/
def quadForm (M : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (M *ᵥ v)).re

/-- A subspace on which the form is positive definite. -/
def IsPosSubspace (M : Matrix n n ℂ)
    (V : Submodule ℂ (n → ℂ)) : Prop :=
  ∀ v ∈ V, v ≠ 0 → 0 < quadForm M v

/-- A subspace on which the form is nonpositive. -/
def IsNonposSubspace (M : Matrix n n ℂ)
    (V : Submodule ℂ (n → ℂ)) : Prop :=
  ∀ v ∈ V, quadForm M v ≤ 0

/-- Positive inertia index: the largest dimension of a
positive-definite subspace. -/
noncomputable def posInertia (M : Matrix n n ℂ) : ℕ :=
  sSup {d | ∃ V : Submodule ℂ (n → ℂ),
    IsPosSubspace M V ∧ finrank ℂ V = d}

/-- Negative inertia index. -/
noncomputable def negInertia (M : Matrix n n ℂ) : ℕ :=
  posInertia (-M)

/-- Null index. -/
noncomputable def nullInertia (M : Matrix n n ℂ) : ℕ :=
  Fintype.card n - posInertia M - negInertia M

omit [DecidableEq n] in
lemma isPosSubspace_bot (M : Matrix n n ℂ) :
    IsPosSubspace M ⊥ := by
  intro v hv hv0
  exact absurd (Submodule.mem_bot ℂ |>.mp hv) hv0

omit [DecidableEq n] in
lemma zero_mem_dimSet (M : Matrix n n ℂ) :
    0 ∈ {d | ∃ V : Submodule ℂ (n → ℂ),
      IsPosSubspace M V ∧ finrank ℂ V = d} :=
  ⟨⊥, isPosSubspace_bot M, finrank_bot ℂ _⟩

omit [DecidableEq n] in
lemma dimSet_bddAbove (M : Matrix n n ℂ) :
    ∀ d ∈ {d | ∃ V : Submodule ℂ (n → ℂ),
      IsPosSubspace M V ∧ finrank ℂ V = d},
      d ≤ Fintype.card n := by
  rintro d ⟨V, _, rfl⟩
  calc finrank ℂ V ≤ finrank ℂ (n → ℂ) :=
        V.finrank_le
    _ = Fintype.card n := finrank_pi ℂ

omit [DecidableEq n] in
/-- The dimension count: a positive and a nonpositive
subspace intersect trivially, so their dimensions add up
to at most `n`. -/
lemma finrank_pos_add_nonpos_le (M : Matrix n n ℂ)
    {V N : Submodule ℂ (n → ℂ)}
    (hV : IsPosSubspace M V) (hN : IsNonposSubspace M N) :
    finrank ℂ V + finrank ℂ N ≤ Fintype.card n := by
  have hdisj : V ⊓ N = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have h1 := hV x (Submodule.mem_inf.mp hx).1 hx0
    have h2 := hN x (Submodule.mem_inf.mp hx).2
    linarith
  have := Submodule.finrank_sup_add_finrank_inf_eq V N
  rw [hdisj] at this
  simp only [finrank_bot, add_zero] at this
  calc finrank ℂ V + finrank ℂ N
      = finrank ℂ ↥(V ⊔ N) := this.symm
    _ ≤ finrank ℂ (n → ℂ) := Submodule.finrank_le _
    _ = Fintype.card n := finrank_pi ℂ

/-- The quadratic form of an orthonormal-eigenvector
combination. -/
private lemma quad_eigen_sum {ι : Type} [Fintype ι]
    (M : Matrix n n ℂ) (μ : n → ℝ) (v : n → n → ℂ)
    (horth : ∀ i j, star (v i) ⬝ᵥ v j
      = if i = j then 1 else 0)
    (heig : ∀ j, M *ᵥ v j = (μ j : ℂ) • v j)
    (e : ι → n) (he : Function.Injective e) (c : ι → ℂ) :
    star (∑ i, c i • v (e i))
      ⬝ᵥ (M *ᵥ ∑ i, c i • v (e i))
    = ((∑ i, Complex.normSq (c i) * μ (e i) : ℝ) : ℂ) := by
  have hMv : M *ᵥ (∑ i, c i • v (e i))
      = ∑ j, c j • ((μ (e j) : ℂ) • v (e j)) := by
    have : M *ᵥ (∑ i, c i • v (e i))
        = ∑ i, c i • (M *ᵥ v (e i)) := by
      rw [← Matrix.mulVecLin_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, Matrix.mulVecLin_apply]
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [heig]
  have hst : star (∑ i, c i • v (e i))
      = ∑ i, (starRingEnd ℂ) (c i) • star (v (e i)) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [star_smul]
      rfl
  rw [hMv, hst, sum_dotProduct]
  have hterm : ∀ i,
      ((starRingEnd ℂ) (c i) • star (v (e i))) ⬝ᵥ
        (∑ j, c j • ((μ (e j) : ℂ) • v (e j)))
      = ((Complex.normSq (c i) * μ (e i) : ℝ) : ℂ) := by
    intro i
    rw [dotProduct_sum]
    rw [Finset.sum_eq_single i]
    · rw [smul_dotProduct, dotProduct_smul,
        dotProduct_smul, horth, if_pos rfl]
      simp only [smul_eq_mul, mul_one]
      have hcc : (starRingEnd ℂ) (c i) * c i
          = ((Complex.normSq (c i) : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
      calc (starRingEnd ℂ) (c i)
            * (c i * ((μ (e i) : ℝ) : ℂ))
          = ((starRingEnd ℂ) (c i) * c i)
            * ((μ (e i) : ℝ) : ℂ) := by ring
        _ = ((Complex.normSq (c i) : ℝ) : ℂ)
            * ((μ (e i) : ℝ) : ℂ) := by rw [hcc]
        _ = ((Complex.normSq (c i) * μ (e i) : ℝ) : ℂ) := by
            push_cast
            ring
    · intro j _ hj
      rw [smul_dotProduct, dotProduct_smul,
        dotProduct_smul, horth]
      rw [if_neg (fun h => hj (he h).symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  push_cast
  ring

/-- The spectral computation of the positive index: for
a matrix with an orthonormal eigenbasis, `posInertia` is
the number of positive eigenvalues. -/
theorem posInertia_eq_card_of_eigenbasis
    (M : Matrix n n ℂ) (μ : n → ℝ) (v : n → n → ℂ)
    (horth : ∀ i j, star (v i) ⬝ᵥ v j
      = if i = j then 1 else 0)
    (heig : ∀ j, M *ᵥ v j = (μ j : ℂ) • v j) :
    posInertia M = #{j | 0 < μ j} := by
  -- linear independence of any injectively indexed
  -- eigenvector subfamily
  have hli : ∀ {ι : Type} [Fintype ι] (e : ι → n),
      Function.Injective e →
      LinearIndependent ℂ (fun i => v (e i)) := by
    intro ι _ e he
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : star (v (e i)) ⬝ᵥ (∑ j, c j • v (e j))
        = 0 := by
      rw [hc, dotProduct_zero]
    rw [dotProduct_sum] at h0
    rw [Finset.sum_eq_single i] at h0
    · rwa [dotProduct_smul, horth, if_pos rfl,
        smul_eq_mul, mul_one] at h0
    · intro j _ hj
      rw [dotProduct_smul, horth,
        if_neg (fun h => hj (he h).symm), smul_eq_mul,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  -- the positive-eigenvector span
  set P : Submodule ℂ (n → ℂ) := Submodule.span ℂ
    (Set.range fun j : {j : n // 0 < μ j} => v j.1)
    with hP
  have hPpos : IsPosSubspace M P := by
    intro x hx hx0
    rw [hP, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have hquad := quad_eigen_sum M μ v horth heig
      (fun j : {j : n // 0 < μ j} => j.1)
      Subtype.val_injective c
    rw [hc] at hquad
    rw [quadForm, hquad, Complex.ofReal_re]
    have hex : ∃ i, c i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hx0
      rw [← hc]
      exact Finset.sum_eq_zero fun i _ => by
        rw [hall i, zero_smul]
    obtain ⟨i₀, hi₀⟩ := hex
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (Complex.normSq_nonneg _)
        (le_of_lt i.2)
    · exact ⟨i₀, Finset.mem_univ i₀, by
        have h1 : 0 < Complex.normSq (c i₀) := by
          simpa [Complex.normSq_pos] using hi₀
        exact mul_pos h1 i₀.2⟩
  have hPrank : finrank ℂ P = #{j | 0 < μ j} := by
    rw [hP, finrank_span_eq_card (hli _
      Subtype.val_injective)]
    exact Fintype.card_subtype _
  -- the nonpositive-eigenvector span
  set N : Submodule ℂ (n → ℂ) := Submodule.span ℂ
    (Set.range fun j : {j : n // ¬ 0 < μ j} => v j.1)
    with hN
  have hNnp : IsNonposSubspace M N := by
    intro x hx
    rw [hN, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have hquad := quad_eigen_sum M μ v horth heig
      (fun j : {j : n // ¬ 0 < μ j} => j.1)
      Subtype.val_injective c
    rw [hc] at hquad
    rw [quadForm, hquad, Complex.ofReal_re]
    apply Finset.sum_nonpos
    intro i _
    have hμ : μ i.1 ≤ 0 := le_of_not_gt i.2
    have h0 : 0 ≤ Complex.normSq (c i) :=
      Complex.normSq_nonneg _
    nlinarith
  have hNrank : finrank ℂ N
      = Fintype.card n - #{j | 0 < μ j} := by
    rw [hN, finrank_span_eq_card (hli _
      Subtype.val_injective)]
    rw [Fintype.card_subtype]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset n))
      (p := fun j => 0 < μ j)
    have huniv := Finset.card_univ (α := n)
    omega
  -- combine both bounds
  have hple : #{j | 0 < μ j} ≤ Fintype.card n := by
    calc #{j | 0 < μ j}
        ≤ #(Finset.univ : Finset n) :=
          Finset.card_filter_le _ _
      _ = Fintype.card n := rfl
  apply le_antisymm
  · apply csSup_le ⟨0, zero_mem_dimSet M⟩
    rintro d ⟨V, hVpos, rfl⟩
    have := finrank_pos_add_nonpos_le M hVpos hNnp
    omega
  · apply le_csSup
    · exact ⟨Fintype.card n, fun d hd =>
        dimSet_bddAbove M d hd⟩
    · exact ⟨P, hPpos, hPrank⟩

omit [DecidableEq n] in
/-- Congruence transport of the form. -/
lemma quadForm_congruence (M X : Matrix n n ℂ)
    (v : n → ℂ) :
    quadForm (Xᴴ * M * X) v = quadForm M (X *ᵥ v) := by
  unfold quadForm
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec (star v) Xᴴ]
  congr 1
  rw [← Matrix.star_mulVec]

/-- The invertible congruence as a linear equivalence. -/
noncomputable def congruenceEquiv (X : Matrix n n ℂ)
    (hX : IsUnit X.det) : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) :=
  LinearEquiv.ofLinear X.mulVecLin X⁻¹.mulVecLin
    (by
      rw [← Matrix.mulVecLin_mul,
        Matrix.mul_nonsing_inv X hX,
        Matrix.mulVecLin_one])
    (by
      rw [← Matrix.mulVecLin_mul,
        Matrix.nonsing_inv_mul X hX,
        Matrix.mulVecLin_one])

/-- **Sylvester's law of inertia**: all three inertia
indices are invariant under invertible congruence. -/
theorem sylvester_inertia (M X : Matrix n n ℂ)
    (hX : IsUnit X.det) :
    posInertia (Xᴴ * M * X) = posInertia M
    ∧ negInertia (Xᴴ * M * X) = negInertia M
    ∧ nullInertia (Xᴴ * M * X) = nullInertia M := by
  -- one congruence direction on the dimension sets
  have key : ∀ (M X : Matrix n n ℂ), IsUnit X.det →
      ∀ d ∈ {d | ∃ V : Submodule ℂ (n → ℂ),
        IsPosSubspace (Xᴴ * M * X) V ∧ finrank ℂ V = d},
      d ∈ {d | ∃ V : Submodule ℂ (n → ℂ),
        IsPosSubspace M V ∧ finrank ℂ V = d} := by
    rintro M X hX d ⟨V, hVpos, rfl⟩
    refine ⟨V.map (congruenceEquiv X hX :
      (n → ℂ) →ₗ[ℂ] (n → ℂ)), ?_, ?_⟩
    · rintro w hw hw0
      rw [Submodule.mem_map] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hu0 : u ≠ 0 := by
        rintro rfl
        exact hw0 (map_zero _)
      have := hVpos u hu hu0
      rwa [quadForm_congruence] at this
    · exact (LinearEquiv.finrank_map_eq _ V)
  have hpos : ∀ (M X : Matrix n n ℂ), IsUnit X.det →
      posInertia (Xᴴ * M * X) = posInertia M := by
    intro M X hX
    apply le_antisymm
    · exact csSup_le ⟨0, zero_mem_dimSet _⟩
        fun d hd => le_csSup
          ⟨Fintype.card n, fun d' hd' =>
            dimSet_bddAbove M d' hd'⟩
          (key M X hX d hd)
    · -- reverse: congruence by `X⁻¹` of `XᴴMX`
      have hXi : IsUnit X⁻¹.det :=
        (Matrix.isUnit_nonsing_inv_det_iff).mpr hX
      have hXH : IsUnit Xᴴ.det := by
        rw [Matrix.det_conjTranspose]
        exact hX.star
      have hM : (X⁻¹ᴴ * (Xᴴ * M * X) * X⁻¹) = M := by
        rw [Matrix.conjTranspose_nonsing_inv]
        rw [Matrix.mul_assoc Xᴴ M X]
        rw [← Matrix.mul_assoc Xᴴ⁻¹ Xᴴ (M * X)]
        rw [Matrix.nonsing_inv_mul Xᴴ hXH,
          Matrix.one_mul, Matrix.mul_assoc M X X⁻¹,
          Matrix.mul_nonsing_inv X hX, Matrix.mul_one]
      apply csSup_le ⟨0, zero_mem_dimSet _⟩
      intro d hd
      apply le_csSup ⟨Fintype.card n, fun d' hd' =>
        dimSet_bddAbove _ d' hd'⟩
      apply key (Xᴴ * M * X) X⁻¹ hXi
      rw [hM]
      exact hd
  have h1 := hpos M X hX
  have h2 : negInertia (Xᴴ * M * X) = negInertia M := by
    unfold negInertia
    have : -(Xᴴ * M * X) = Xᴴ * (-M) * X := by
      simp
    rw [this]
    exact hpos (-M) X hX
  exact ⟨h1, h2, by unfold nullInertia; rw [h1, h2]⟩

end Inertia

section Haynsworth

variable {p q : Type} [Fintype p] [Fintype q]
  [DecidableEq p] [DecidableEq q]

set_option linter.unusedDecidableInType false in
/-- Inertia additivity for Hermitian block-diagonal
matrices, through the assembled eigenbasis. -/
theorem posInertia_fromBlocks_diag
    (A : Matrix p p ℂ) (D : Matrix q q ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    posInertia (fromBlocks A 0 0 D)
      = posInertia A + posInertia D := by
  -- orthonormal eigen data of the blocks
  have horthA : ∀ i j,
      star ⇑(hA.eigenvectorBasis i) ⬝ᵥ
        ⇑(hA.eigenvectorBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have hU := Unitary.coe_star_mul_self
      hA.eigenvectorUnitary
    have := congrFun (congrFun hU i) j
    simp only [Matrix.mul_apply, Matrix.star_apply,
      Matrix.one_apply] at this
    rw [← this]
    simp only [dotProduct, Pi.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have horthD : ∀ i j,
      star ⇑(hD.eigenvectorBasis i) ⬝ᵥ
        ⇑(hD.eigenvectorBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have hU := Unitary.coe_star_mul_self
      hD.eigenvectorUnitary
    have := congrFun (congrFun hU i) j
    simp only [Matrix.mul_apply, Matrix.star_apply,
      Matrix.one_apply] at this
    rw [← this]
    simp only [dotProduct, Pi.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have heigA : ∀ j, A *ᵥ ⇑(hA.eigenvectorBasis j)
      = ((hA.eigenvalues j : ℂ))
        • ⇑(hA.eigenvectorBasis j) := by
    intro j
    rw [hA.mulVec_eigenvectorBasis]
    funext k
    simp [Complex.real_smul]
  have heigD : ∀ j, D *ᵥ ⇑(hD.eigenvectorBasis j)
      = ((hD.eigenvalues j : ℂ))
        • ⇑(hD.eigenvectorBasis j) := by
    intro j
    rw [hD.mulVec_eigenvectorBasis]
    funext k
    simp [Complex.real_smul]
  -- assemble the block eigen data
  set w : p ⊕ q → (p ⊕ q → ℂ) := Sum.elim
    (fun i => Sum.elim ⇑(hA.eigenvectorBasis i)
      (0 : q → ℂ))
    (fun i => Sum.elim (0 : p → ℂ)
      ⇑(hD.eigenvectorBasis i))
    with hw
  have hwl : ∀ i : p, w (Sum.inl i)
      = Sum.elim ⇑(hA.eigenvectorBasis i)
        (0 : q → ℂ) := fun i => rfl
  have hwr : ∀ i : q, w (Sum.inr i)
      = Sum.elim (0 : p → ℂ)
        ⇑(hD.eigenvectorBasis i) := fun i => rfl
  set μ : p ⊕ q → ℝ :=
    Sum.elim hA.eigenvalues hD.eigenvalues with hμ
  -- dot products decompose over the two blocks
  have hdot : ∀ (x₁ y₁ : p → ℂ) (x₂ y₂ : q → ℂ),
      (Sum.elim x₁ x₂) ⬝ᵥ (Sum.elim y₁ y₂)
      = x₁ ⬝ᵥ y₁ + x₂ ⬝ᵥ y₂ := by
    intro x₁ y₁ x₂ y₂
    simp [dotProduct, Fintype.sum_sum_type]
  have hstar : ∀ (x₁ : p → ℂ) (x₂ : q → ℂ),
      star (Sum.elim x₁ x₂)
        = Sum.elim (star x₁) (star x₂) := by
    intro x₁ x₂
    funext x
    cases x <;> rfl
  have horth : ∀ i j, star (w i) ⬝ᵥ w j
      = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [hwl, hwl, hstar, hdot]
        rw [horthA]
        simp [Sum.inl.injEq]
      | inr j =>
        rw [hwl, hwr, hstar, hdot]
        simp
    | inr i =>
      cases j with
      | inl j =>
        rw [hwr, hwl, hstar, hdot]
        simp
      | inr j =>
        rw [hwr, hwr, hstar, hdot]
        rw [horthD]
        simp [Sum.inr.injEq]
  have heig : ∀ j, (fromBlocks A 0 0 D) *ᵥ w j
      = ((μ j : ℂ)) • w j := by
    intro j
    cases j with
    | inl j =>
      rw [hwl]
      have hstep : (fromBlocks A 0 0 D) *ᵥ
          Sum.elim ⇑(hA.eigenvectorBasis j) (0 : q → ℂ)
          = Sum.elim (A *ᵥ ⇑(hA.eigenvectorBasis j))
            (0 : q → ℂ) := by
        rw [Matrix.fromBlocks_mulVec]
        simp
      rw [hstep, heigA]
      funext x
      cases x <;> simp [hμ]
    | inr j =>
      rw [hwr]
      have hstep : (fromBlocks A 0 0 D) *ᵥ
          Sum.elim (0 : p → ℂ) ⇑(hD.eigenvectorBasis j)
          = Sum.elim (0 : p → ℂ)
            (D *ᵥ ⇑(hD.eigenvectorBasis j)) := by
        rw [Matrix.fromBlocks_mulVec]
        simp
      rw [hstep, heigD]
      funext x
      cases x <;> simp [hμ]
  -- count positive eigenvalues over the sum type
  rw [posInertia_eq_card_of_eigenbasis _ μ w horth heig]
  rw [posInertia_eq_card_of_eigenbasis A hA.eigenvalues _
    horthA heigA]
  rw [posInertia_eq_card_of_eigenbasis D hD.eigenvalues _
    horthD heigD]
  rw [Finset.card_filter, Finset.card_filter,
    Finset.card_filter, Fintype.sum_sum_type]
  simp [hμ]

/-- `thm:GT-signed-Haynsworth` (the boxed SC.9): signed
Feshbach inertia additivity under the range condition,
presented by a Douglas solution `W` of `D·W = Bᴴ`. -/
theorem gt_signed_haynsworth
    (A : Matrix p p ℂ) (B : Matrix p q ℂ)
    (D : Matrix q q ℂ) (W : Matrix q p ℂ)
    (hH : (fromBlocks A B Bᴴ D).IsHermitian)
    (hW : D * W = Bᴴ) :
    -- the block-diagonalizing congruence
    ((fromBlocks 1 0 (-W) 1 :
        Matrix (p ⊕ q) (p ⊕ q) ℂ)ᴴ
      * fromBlocks A B Bᴴ D
      * fromBlocks 1 0 (-W) 1
      = fromBlocks (A - Wᴴ * D * W) 0 0 D)
    -- the boxed inertia additivity, all three indices
    ∧ posInertia (fromBlocks A B Bᴴ D)
      = posInertia (A - Wᴴ * D * W) + posInertia D
    ∧ negInertia (fromBlocks A B Bᴴ D)
      = negInertia (A - Wᴴ * D * W) + negInertia D
    ∧ nullInertia (fromBlocks A B Bᴴ D)
      = nullInertia (A - Wᴴ * D * W) + nullInertia D := by
  -- extract the block hermiticity
  have hHt := hH
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    at hHt
  have hA : A.IsHermitian := by
    have h := congrArg Matrix.toBlocks₁₁ hHt
    simp only [Matrix.toBlocks_fromBlocks₁₁] at h
    exact h
  have hD : D.IsHermitian := by
    have h := congrArg Matrix.toBlocks₂₂ hHt
    simp only [Matrix.toBlocks_fromBlocks₂₂] at h
    exact h
  have hB : B = Wᴴ * D := by
    have := congrArg Matrix.toBlocks₁₂ hHt
    simp only [Matrix.toBlocks_fromBlocks₁₂] at this
    calc B = Bᴴᴴ := (Matrix.conjTranspose_conjTranspose B).symm
      _ = (D * W)ᴴ := by rw [hW]
      _ = Wᴴ * Dᴴ := Matrix.conjTranspose_mul D W
      _ = Wᴴ * D := by rw [hD.eq]
  -- the congruence identity
  have hcong : (fromBlocks 1 0 (-W) 1 :
      Matrix (p ⊕ q) (p ⊕ q) ℂ)ᴴ
      * fromBlocks A B Bᴴ D * fromBlocks 1 0 (-W) 1
      = fromBlocks (A - Wᴴ * D * W) 0 0 D := by
    rw [Matrix.fromBlocks_conjTranspose]
    rw [Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- block 1 1
      have h1 : (Wᴴ * D)ᴴ = D * W := by
        rw [Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, hD.eq]
      rw [hB, h1]
      simp only [Matrix.conjTranspose_one,
        Matrix.conjTranspose_neg, Matrix.one_mul,
        Matrix.mul_one, Matrix.neg_mul]
      rw [add_neg_cancel, Matrix.zero_mul, add_zero,
        ← Matrix.mul_assoc, ← sub_eq_add_neg]
    · -- block 1 2
      simp only [Matrix.conjTranspose_one,
        Matrix.conjTranspose_neg]
      rw [hB]
      simp
    · -- block 2 1
      simp only [Matrix.conjTranspose_zero,
        Matrix.conjTranspose_one, Matrix.zero_mul,
        Matrix.one_mul, zero_add, Matrix.mul_one,
        Matrix.mul_neg]
      rw [hW]
      exact add_neg_cancel _
    · -- block 2 2
      simp
  refine ⟨hcong, ?_⟩
  -- the Schur complement is Hermitian
  have hS : (A - Wᴴ * D * W).IsHermitian := by
    apply hA.sub
    exact Matrix.isHermitian_conjTranspose_mul_mul W hD
  -- the congruence is invertible
  have hX : IsUnit (fromBlocks 1 0 (-W) 1 :
      Matrix (p ⊕ q) (p ⊕ q) ℂ).det := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hsylv := sylvester_inertia
    (fromBlocks A B Bᴴ D) (fromBlocks 1 0 (-W) 1) hX
  rw [hcong] at hsylv
  obtain ⟨hsp, hsn, hs0⟩ := hsylv
  have hdp := posInertia_fromBlocks_diag
    (A - Wᴴ * D * W) D hS hD
  have hdn : negInertia (fromBlocks (A - Wᴴ * D * W)
      0 0 D) = negInertia (A - Wᴴ * D * W)
        + negInertia D := by
    unfold negInertia
    have : -(fromBlocks (A - Wᴴ * D * W) 0 0 D)
        = fromBlocks (-(A - Wᴴ * D * W)) 0 0 (-D) := by
      rw [Matrix.fromBlocks_neg]
      norm_num
    rw [this]
    exact posInertia_fromBlocks_diag _ _ hS.neg hD.neg
  refine ⟨by rw [← hsp, hdp], by rw [← hsn, hdn], ?_⟩
  -- the null indices: subtract using the count formulas
  have hcount : ∀ {m : Type} [Fintype m] [DecidableEq m]
      (M : Matrix m m ℂ), M.IsHermitian →
      posInertia M + negInertia M ≤ Fintype.card m := by
    intro m _ _ M hM
    have horthM : ∀ i j,
        star ⇑(hM.eigenvectorBasis i) ⬝ᵥ
          ⇑(hM.eigenvectorBasis j)
        = if i = j then 1 else 0 := by
      intro i j
      have hU := Unitary.coe_star_mul_self
        hM.eigenvectorUnitary
      have := congrFun (congrFun hU i) j
      simp only [Matrix.mul_apply, Matrix.star_apply,
        Matrix.one_apply] at this
      rw [← this]
      simp only [dotProduct, Pi.star_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply]
    have heigM : ∀ j, M *ᵥ ⇑(hM.eigenvectorBasis j)
        = ((hM.eigenvalues j : ℂ))
          • ⇑(hM.eigenvectorBasis j) := by
      intro j
      rw [hM.mulVec_eigenvectorBasis]
      funext k
      simp [Complex.real_smul]
    have heigM' : ∀ j, (-M) *ᵥ ⇑(hM.eigenvectorBasis j)
        = (((- hM.eigenvalues j : ℝ) : ℂ))
          • ⇑(hM.eigenvectorBasis j) := by
      intro j
      rw [Matrix.neg_mulVec, heigM]
      push_cast
      rw [neg_smul]
    rw [posInertia_eq_card_of_eigenbasis M
      hM.eigenvalues _ horthM heigM]
    rw [negInertia,
      posInertia_eq_card_of_eigenbasis (-M)
        (fun j => - hM.eigenvalues j) _ horthM heigM']
    rw [Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    calc ∑ j, ((if 0 < hM.eigenvalues j then 1 else 0)
          + if 0 < - hM.eigenvalues j then 1 else 0)
        ≤ ∑ _j : m, 1 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases h : 0 < hM.eigenvalues j <;>
            by_cases h' : 0 < - hM.eigenvalues j <;>
            simp [h, h']
          linarith
      _ = Fintype.card m := by simp
  have hc1 := hcount (A - Wᴴ * D * W) hS
  have hc2 := hcount D hD
  unfold nullInertia
  rw [← hsp, ← hsn, hdp, hdn]
  have hcard : Fintype.card (p ⊕ q)
      = Fintype.card p + Fintype.card q :=
    Fintype.card_sum
  omega

end Haynsworth

end NCG
