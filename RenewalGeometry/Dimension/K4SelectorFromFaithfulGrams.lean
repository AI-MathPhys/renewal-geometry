/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Dimension.CutCycleExteriorFinrank
import RenewalGeometry.Dimension.DimensionK4Selector
import RenewalGeometry.Dimension.DimensionPairwise

/-!
# The minimal faithful `K₄` selector from its hypotheses (`thm:supp-k4-selector`,
  emergent-spacetime manuscript)

The selector is derived from the objects themselves, with all ranks computed as `finrank`s:

* (D1) the temporal–spatial coefficient space `ℝt ⊕ W_N` (`temporalSpatial N = ℝ × W_N`)
  carries a nondegenerate alternating bilinear form; `even_finrank_of_isAlt_nondegenerate`
  (via the Gram matrix in a basis) and `finrank_temporalSpatial` (`= N`) force `N` even;
* (D2) faithful (positive definite) endpoint and complete signed-edge Grams `G₀` on
  `W_N = Ran ∂` and `G₁` on `C₁(K_N)`; their ranks are `gramRank_endpoint : r₀ = N - 1`,
  `gramRank_edge : r₁ = C(N,2)` (from `finrank_meanZero`, `finrank_edgeSpace`);
* (D3) a nonzero cycle source `C ∈ Ker ∂ = Λ²W_N`; since `dim Ker ∂ = C(N-1,2)` this forces
  `N ≥ 3`;
* (D4) Pareto-minimality of the faithful source ranks `(r₀, r₁)` among admissible simplex
  cells (`Admissible N'`: (D1) and (D3) hold at `N'`; any faithful Grams at `N'`).

`k4_selector_of_faithful_grams` concludes `N = 4`, `r₀ = 3`, `r₁ = 6`, `G_rel = K₄` (with the
pair-homogeneous relation set of `ass:supp-relational-branch`, via
`dimension_pairwise_completion`) and `dim W₄ = 3`.  The admissibility of `N = 4` is proved by an
explicit nondegenerate alternating form on `ℝ × W₄` (`admissible_four`), and
`k4_selector_hypotheses_satisfiable` shows that the whole hypothesis packet holds at `N = 4`.
-/

open Matrix Module

namespace RenewalGeometry
namespace K4SelectorFaithful

open CutCycleExterior

/-- The temporal–spatial coefficient space `ℝt ⊕ W_N`. -/
abbrev temporalSpatial (N : ℕ) := ℝ × meanZero N

/-- A Gram (bilinear form) is faithful when it is positive definite. -/
def FaithfulGram {E : Type*} [AddCommGroup E] [Module ℝ E] (G : LinearMap.BilinForm ℝ E) :
    Prop :=
  ∀ x, x ≠ 0 → 0 < G x x

/-- The rank of a Gram: the dimension of its range in the dual. -/
noncomputable def gramRank {E : Type*} [AddCommGroup E] [Module ℝ E]
    (G : LinearMap.BilinForm ℝ E) : ℕ :=
  finrank ℝ (LinearMap.range G)

/-- `E` carries a nondegenerate alternating bilinear form. -/
def HasNondegAltForm (E : Type*) [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ ω : LinearMap.BilinForm ℝ E, ω.IsAlt ∧ ω.Nondegenerate

/-- The rank of a faithful Gram is the dimension of the space. -/
theorem gramRank_of_faithful {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {G : LinearMap.BilinForm ℝ E} (hG : FaithfulGram G) : gramRank G = finrank ℝ E := by
  unfold gramRank
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  by_contra hne
  have h := hG (x - y) (sub_ne_zero.mpr hne)
  have : G (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [this] at h
  exact lt_irrefl _ h

/-- Every finite-dimensional real space carries a faithful Gram. -/
theorem exists_faithfulGram (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] :
    ∃ G : LinearMap.BilinForm ℝ E, FaithfulGram G := by
  let b := Module.finBasis ℝ E
  refine ⟨Matrix.toBilin b 1, fun x hx => ?_⟩
  rw [Matrix.toBilin_apply]
  have hsum : ∀ i, ∑ j, b.repr x i * (1 : Matrix (Fin (finrank ℝ E)) _ ℝ) i j * b.repr x j
      = b.repr x i ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [sq]
    · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp only [hsum]
  have hne : b.repr x ≠ 0 := by
    intro h
    exact hx (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Finsupp.ext hall)
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by positivity⟩

/-- (D1) parity: a nondegenerate alternating real bilinear form lives in even dimension. -/
theorem even_finrank_of_isAlt_nondegenerate {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {ω : LinearMap.BilinForm ℝ E} (halt : ω.IsAlt)
    (hnd : ω.Nondegenerate) : Even (finrank ℝ E) := by
  let b := Module.finBasis ℝ E
  set J := LinearMap.BilinForm.toMatrix b ω with hJ
  have hskew : Jᵀ = -J := by
    ext i j
    simp only [hJ, Matrix.transpose_apply, Matrix.neg_apply,
      LinearMap.BilinForm.toMatrix_apply]
    exact (halt.neg_eq (b i) (b j)).symm
  have hdet : J.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  exact dimension_K4_selector.1 _ J hskew (isUnit_iff_ne_zero.mpr hdet)

/-- `dim (ℝt ⊕ W_N) = N` for `N ≥ 1`. -/
theorem finrank_temporalSpatial {N : ℕ} (hN : 1 ≤ N) : finrank ℝ (temporalSpatial N) = N := by
  rw [Module.finrank_prod, Module.finrank_self, finrank_meanZero hN]
  omega

theorem finrank_meanZero_zero : finrank ℝ (meanZero 0) = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc finrank ℝ (meanZero 0) ≤ finrank ℝ (Fin 0 → ℝ) := Submodule.finrank_le _
    _ = 0 := by simp

/-- (D2) the faithful endpoint rank is `r₀(N) = N - 1`. -/
theorem gramRank_endpoint {N : ℕ} (hN : 1 ≤ N) {G : LinearMap.BilinForm ℝ (meanZero N)}
    (hG : FaithfulGram G) : gramRank G = N - 1 := by
  rw [gramRank_of_faithful hG, finrank_meanZero hN]

/-- (D2) the faithful complete signed-edge rank is `r₁(N) = C(N, 2)`. -/
theorem gramRank_edge {N : ℕ} {G : LinearMap.BilinForm ℝ (edgeSpace N)}
    (hG : FaithfulGram G) : gramRank G = N.choose 2 := by
  rw [gramRank_of_faithful hG, finrank_edgeSpace]

/-- (D3) a nonzero cycle source forces `N ≥ 3`. -/
theorem three_le_of_cycle_ne_zero {N : ℕ} (hN : 1 ≤ N) {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C ∈ edgeSpace N ⊓ LinearMap.ker (boundary N)) (hC0 : C ≠ 0) : 3 ≤ N := by
  rw [edgeSpace_inf_ker_boundary hN] at hC
  have hne : cycleSpace N ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hC
    exact hC0 hC
  have hpos : finrank ℝ (cycleSpace N) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.mp h0)
  rw [finrank_cycleSpace hN] at hpos
  have : ¬ (N - 1 < 2) := fun h => hpos (Nat.choose_eq_zero_of_lt h)
  omega

/-- An admissible simplex cell: (D1) and (D3) hold at `N` (faithful Grams always exist,
`exists_faithfulGram`). -/
def Admissible (N : ℕ) : Prop :=
  HasNondegAltForm (temporalSpatial N) ∧
    ∃ C : Matrix (Fin N) (Fin N) ℝ, C ∈ edgeSpace N ⊓ LinearMap.ker (boundary N) ∧ C ≠ 0

/-- Admissible cells have even `N ≥ 4`. -/
theorem four_le_and_even_of_admissible {N : ℕ} (h : Admissible N) : 4 ≤ N ∧ Even N := by
  obtain ⟨⟨ω, halt, hnd⟩, C, hC, hC0⟩ := h
  have hev := even_finrank_of_isAlt_nondegenerate halt hnd
  have hN : 1 ≤ N := by
    by_contra h0
    have : N = 0 := by omega
    subst this
    rw [Module.finrank_prod, Module.finrank_self, finrank_meanZero_zero] at hev
    exact (Nat.not_even_one) hev
  rw [finrank_temporalSpatial hN] at hev
  have h3 := three_le_of_cycle_ne_zero hN hC hC0
  exact ⟨(dimension_K4_selector.2.1 N hev h3).1, hev⟩

/-- The standard symplectic matrix on `Fin 4`. -/
def stdSymplectic4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem stdSymplectic4_transpose : stdSymplectic4ᵀ = -stdSymplectic4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdSymplectic4]

theorem stdSymplectic4_mul_self : stdSymplectic4 * stdSymplectic4 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdSymplectic4, Matrix.mul_apply, Fin.sum_univ_four]

theorem stdSymplectic4_det_ne_zero : stdSymplectic4.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det stdSymplectic4_mul_self
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg] at this
  norm_num at this

/-- A nondegenerate alternating form on any real space of dimension `4`. -/
theorem hasNondegAltForm_of_finrank_four (E : Type*) [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h4 : finrank ℝ E = 4) : HasNondegAltForm E := by
  let b : Basis (Fin 4) ℝ E := Module.finBasisOfFinrankEq ℝ E h4
  refine ⟨Matrix.toBilin b stdSymplectic4, ?_, ?_⟩
  · intro x
    change Matrix.toBilin b stdSymplectic4 x x = 0
    rw [Matrix.toBilin_apply]
    have hanti : ∑ i, ∑ j, b.repr x i * stdSymplectic4 i j * b.repr x j
        = -∑ i, ∑ j, b.repr x i * stdSymplectic4 i j * b.repr x j := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun stdSymplectic4_transpose i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this]; ring
    linarith
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, LinearMap.BilinForm.toMatrix_toBilin]
    exact stdSymplectic4_det_ne_zero

/-- `N = 4` is admissible. -/
theorem admissible_four : Admissible 4 := by
  refine ⟨hasNondegAltForm_of_finrank_four _ (finrank_temporalSpatial (by norm_num)), ?_⟩
  have h3 : finrank ℝ (cycleSpace 4) = 3 := by
    rw [finrank_cycleSpace (by norm_num)]; decide
  have hne : cycleSpace 4 ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at h3; exact absurd h3 (by norm_num)
  obtain ⟨C, hC, hC0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨C, by rw [edgeSpace_inf_ker_boundary (by norm_num)]; exact hC, hC0⟩

/-- **`thm:supp-k4-selector`.**  Under `ass:supp-relational-branch` (a nonempty relation set
invariant under a group transitive on unordered endpoint pairs) and (D1)–(D4), `N = 4`, the
faithful ranks are `r₀ = N - 1 = 3` and `r₁ = C(N,2) = 6`, `G_rel = K₄`, and
`W_sp = W₄` has dimension `3`. -/
theorem k4_selector_of_faithful_grams (N : ℕ)
    -- `ass:supp-relational-branch`
    (Γ : Subgroup (Equiv.Perm (Fin N))) (R : Set (Sym2 (Fin N)))
    (htrans : ∀ p q : Sym2 (Fin N), ¬p.IsDiag → ¬q.IsDiag → ∃ g ∈ Γ, Sym2.map (⇑g) p = q)
    (hRinv : ∀ g ∈ Γ, ∀ p ∈ R, Sym2.map (⇑g) p ∈ R) (hRne : ∃ p ∈ R, ¬p.IsDiag)
    -- (D1)
    (ω : LinearMap.BilinForm ℝ (temporalSpatial N)) (hωalt : ω.IsAlt)
    (hωnd : ω.Nondegenerate)
    -- (D2)
    (G₀ : LinearMap.BilinForm ℝ (meanZero N)) (G₁ : LinearMap.BilinForm ℝ (edgeSpace N))
    (hG₀ : FaithfulGram G₀) (hG₁ : FaithfulGram G₁)
    -- (D3)
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C ∈ edgeSpace N ⊓ LinearMap.ker (boundary N))
    (hC0 : C ≠ 0)
    -- (D4) Pareto-minimal source innovation among admissible cells
    (hmin : ∀ N', Admissible N' → ∀ (G₀' : LinearMap.BilinForm ℝ (meanZero N'))
      (G₁' : LinearMap.BilinForm ℝ (edgeSpace N')), FaithfulGram G₀' → FaithfulGram G₁' →
      ¬ ((gramRank G₀', gramRank G₁') < (gramRank G₀, gramRank G₁))) :
    N = 4 ∧ gramRank G₀ = N - 1 ∧ gramRank G₁ = N.choose 2 ∧
      gramRank G₀ = 3 ∧ gramRank G₁ = 6 ∧
      (∀ q : Sym2 (Fin N), ¬q.IsDiag → q ∈ R) ∧ finrank ℝ (meanZero N) = 3 := by
  have hadm : Admissible N := ⟨⟨ω, hωalt, hωnd⟩, C, hC, hC0⟩
  obtain ⟨h4, -⟩ := four_le_and_even_of_admissible hadm
  have hN : 1 ≤ N := by omega
  have hr0 := gramRank_endpoint hN hG₀
  have hr1 := gramRank_edge hG₁
  have hN4 : N = 4 := by
    by_contra hne
    have h5 : 5 ≤ N := by omega
    obtain ⟨G₀', hG₀'⟩ := exists_faithfulGram (meanZero 4)
    obtain ⟨G₁', hG₁'⟩ := exists_faithfulGram (edgeSpace 4)
    apply hmin 4 admissible_four G₀' G₁' hG₀' hG₁'
    rw [gramRank_endpoint (by norm_num) hG₀', gramRank_edge hG₁', hr0, hr1]
    have hc : (5 : ℕ).choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 h5
    have h52 : (5 : ℕ).choose 2 = 10 := by decide
    have h42 : (4 : ℕ).choose 2 = 6 := by decide
    rw [Prod.lt_iff]
    left
    refine ⟨by omega, by omega⟩
  subst hN4
  refine ⟨rfl, hr0, hr1, by rw [hr0], by rw [hr1]; decide,
    dimension_pairwise_completion Γ R htrans hRinv hRne, finrank_meanZero (by norm_num)⟩

/-! ### Non-vacuity: the full hypothesis packet holds at `N = 4` -/

/-- The symmetric group acts transitively on unordered pairs of distinct points. -/
theorem perm_transitive_offDiag {X : Type*} [DecidableEq X] (p q : Sym2 X) (hp : ¬p.IsDiag)
    (hq : ¬q.IsDiag) : ∃ g ∈ (⊤ : Subgroup (Equiv.Perm X)), Sym2.map (⇑g) p = q := by
  induction p using Sym2.ind with
  | _ a b =>
  induction q using Sym2.ind with
  | _ c d =>
  rw [Sym2.mk_isDiag_iff] at hp hq
  let τ := Equiv.swap a c
  have hτb : τ b ≠ c := by
    intro h
    have : b = a := by
      have := congrArg (Equiv.swap a c) h
      simpa [τ] using this
    exact hp this.symm
  let ρ := Equiv.swap (τ b) d
  refine ⟨τ.trans ρ, Subgroup.mem_top _, ?_⟩
  simp only [Sym2.map_pair_eq, Equiv.coe_trans, Function.comp_apply]
  have h1 : ρ (τ a) = c := by
    simp only [τ, Equiv.swap_apply_left, ρ]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτb) hq
  have h2 : ρ (τ b) = d := by simp [ρ]
  rw [h1, h2]

/-- The whole hypothesis packet of `k4_selector_of_faithful_grams` is satisfiable (at `N = 4`
with `Γ = S₄`, `R` = all edges, the standard symplectic form, any faithful Grams and a nonzero
cycle), and Pareto-minimality holds there. -/
theorem k4_selector_hypotheses_satisfiable :
    ∃ (ω : LinearMap.BilinForm ℝ (temporalSpatial 4)) (G₀ : LinearMap.BilinForm ℝ (meanZero 4))
      (G₁ : LinearMap.BilinForm ℝ (edgeSpace 4)) (C : Matrix (Fin 4) (Fin 4) ℝ),
      ω.IsAlt ∧ ω.Nondegenerate ∧ FaithfulGram G₀ ∧ FaithfulGram G₁ ∧
      C ∈ edgeSpace 4 ⊓ LinearMap.ker (boundary 4) ∧ C ≠ 0 ∧
      (∀ p q : Sym2 (Fin 4), ¬p.IsDiag → ¬q.IsDiag →
        ∃ g ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))), Sym2.map (⇑g) p = q) ∧
      (∀ N', Admissible N' → ∀ (G₀' : LinearMap.BilinForm ℝ (meanZero N'))
        (G₁' : LinearMap.BilinForm ℝ (edgeSpace N')), FaithfulGram G₀' → FaithfulGram G₁' →
        ¬ ((gramRank G₀', gramRank G₁') < (gramRank G₀, gramRank G₁))) := by
  obtain ⟨⟨ω, halt, hnd⟩, C, hC, hC0⟩ := admissible_four
  obtain ⟨G₀, hG₀⟩ := exists_faithfulGram (meanZero 4)
  obtain ⟨G₁, hG₁⟩ := exists_faithfulGram (edgeSpace 4)
  refine ⟨ω, G₀, G₁, C, halt, hnd, hG₀, hG₁, hC, hC0, perm_transitive_offDiag, ?_⟩
  intro N' hadm G₀' G₁' hG₀' hG₁'
  obtain ⟨h4, -⟩ := four_le_and_even_of_admissible hadm
  rw [gramRank_endpoint (by omega) hG₀', gramRank_edge hG₁',
    gramRank_endpoint (by norm_num) hG₀, gramRank_edge hG₁, Prod.lt_iff]
  have hc : (4 : ℕ).choose 2 ≤ N'.choose 2 := Nat.choose_le_choose 2 h4
  omega

end K4SelectorFaithful
end RenewalGeometry
