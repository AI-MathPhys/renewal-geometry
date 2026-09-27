/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Krein.FormOrthogonalInertia
import RenewalGeometry.Krein.JSelfAdjointRootSpaces
import RenewalGeometry.Algebra.NilpotentHankelJordan

/-!
# Pole–Hankel invariants: the primary decomposition of a finite Pontryagin realization

Paper `predictive_spectral_geometry`, label `thm:supp-pole-Hankel`, items (P3) and (P4).

For a finite Pontryagin realization `P` (state operator `A`, `J`-self-adjoint) the root subspaces
`R_λ = ker (A - λ)^∞` (`rootSpace`, Mathlib's `maxGenEigenspace`) give the primary decomposition
`N = ⊕_λ R_λ`.  We group them into *pole blocks* `poleBlock λ = R_λ ⊔ R_{λ̄}` for `Im λ ≥ 0`
(a real pole gives `R_λ`, a nonreal conjugate pair gives the neutral pairing `R_λ ⊔ R_{λ̄}`).

* `form_eq_zero_of_mem_poleBlock`: distinct pole blocks are form-orthogonal (the primary
  decomposition is Pontryagin orthogonal).
* `poleBlock_sup_eq_top`: the pole blocks over a finite set containing the poles span `N`.
* `isNondegenerateOn_poleBlock`: each pole block carries a nondegenerate form.
* `subNegIndex_poleBlock_of_nonreal` (**P3**): for `Im λ > 0` the block `R_λ ⊔ R_{λ̄}` is a neutral
  pairing with `dim R_λ = dim R_{λ̄}` and negative index `= dim R_λ` = positive index (the local
  McMillan degree of the upper-half-plane pole contributes equally to both signs).
* `negIndex_eq_sum_local` (**P4**): the global negative index is the sum of the local
  contributions: `negIndex = ∑_{real poles} neg(R_λ) + ∑_{Im λ > 0} dim R_λ`.  For a minimal
  realization this global index is the number of negative squares of the Nevanlinna kernel
  (`negSquares_transfer_eq_negIndex`), the "minimum global negative index" of the paper.

The local statements (P1)–(P2) at a single pole are provided as general infrastructure in
`Algebra/NilpotentHankelJordan.lean` (shifted Hankel ranks of a controllable and observable local
realization are the ranks of the powers of the nilpotent part, which determine the Jordan
structure) and `Krein/FormOrthogonalInertia.lean` (`subNegIndex_eq_negInertia_gram`: the local
inertia is the inertia of the Gram matrix of any spanning family of the root subspace, in
particular of the local Krylov family whose Gram is the principal-part Hankel Gram).
-/

open scoped InnerProductSpace InnerProduct
open Module

noncomputable section

namespace RenewalGeometry
namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-! ## Root subspaces -/

/-- The state operator as a linear endomorphism. -/
abbrev endA : Module.End ℂ N := (P.A : N →ₗ[ℂ] N)

/-- The root subspace `R_λ = ker (A - λ)^∞` at `λ`. -/
abbrev rootSpace (lam : ℂ) : Submodule ℂ N := P.endA.maxGenEigenspace lam

theorem pow_sub_algebraMap_apply_eq (lam : ℂ) (p : ℕ) (x : N) :
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ p) x =
      ((P.endA - algebraMap ℂ (Module.End ℂ N) lam) ^ p) x := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', Module.End.mul_apply,
        sub_algebraMap_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]
      rfl

theorem mem_rootSpace_iff (lam : ℂ) (x : N) :
    x ∈ P.rootSpace lam ↔ ∃ k : ℕ, ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) x = 0 := by
  rw [Module.End.mem_maxGenEigenspace]
  simp_rw [pow_sub_algebraMap_apply_eq, Algebra.algebraMap_eq_smul_one]

/-- **Root subspaces at non-conjugate points are form-orthogonal** (P4 mechanism). -/
theorem form_eq_zero_of_mem_rootSpace {lam mu : ℂ} (hne : mu ≠ starRingEnd ℂ lam) {x y : N}
    (hx : x ∈ P.rootSpace lam) (hy : y ∈ P.rootSpace mu) : P.form x y = 0 := by
  obtain ⟨k, hk⟩ := (P.mem_rootSpace_iff lam x).mp hx
  obtain ⟨l, hl⟩ := (P.mem_rootSpace_iff mu y).mp hy
  exact P.form_eq_zero_of_rootSpaces hne k l x y hk hl

/-- **Nonreal root subspaces are neutral** (P3 mechanism). -/
theorem form_self_eq_zero_of_mem_rootSpace {lam : ℂ} (hlam : lam.im ≠ 0) {x : N}
    (hx : x ∈ P.rootSpace lam) : P.form x x = 0 := by
  obtain ⟨k, hk⟩ := (P.mem_rootSpace_iff lam x).mp hx
  exact P.form_self_eq_zero_of_rootSpace_nonreal hlam k x hk

variable [FiniteDimensional ℂ N]

theorem rootSpace_disjoint {lam mu : ℂ} (hne : lam ≠ mu) :
    Disjoint (P.rootSpace lam) (P.rootSpace mu) :=
  Module.End.disjoint_genEigenspace P.endA hne ⊤ ⊤

theorem iSup_rootSpace_eq_top : ⨆ lam, P.rootSpace lam = ⊤ :=
  Module.End.iSup_maxGenEigenspace_eq_top P.endA

/-- A point with a nontrivial root subspace is an eigenvalue of `A`. -/
theorem hasEigenvalue_of_rootSpace_ne_bot {lam : ℂ} (h : P.rootSpace lam ≠ ⊥) :
    P.endA.HasEigenvalue lam :=
  Module.End.HasUnifEigenvalue.lt zero_lt_one h

/-! ## Pole blocks -/

/-- The pole block at `λ` (`Im λ ≥ 0`): the root subspace `R_λ` for a real pole, and the neutral
pairing `R_λ ⊔ R_{λ̄}` for a nonreal conjugate pair. -/
def poleBlock (lam : ℂ) : Submodule ℂ N :=
  if 0 ≤ lam.im then P.rootSpace lam ⊔ P.rootSpace (starRingEnd ℂ lam) else ⊥

theorem poleBlock_of_nonneg {lam : ℂ} (h : 0 ≤ lam.im) :
    P.poleBlock lam = P.rootSpace lam ⊔ P.rootSpace (starRingEnd ℂ lam) := by
  simp [poleBlock, h]

theorem poleBlock_of_neg {lam : ℂ} (h : lam.im < 0) : P.poleBlock lam = ⊥ := by
  simp [poleBlock, not_le.mpr h]

theorem poleBlock_of_real {lam : ℂ} (h : lam.im = 0) : P.poleBlock lam = P.rootSpace lam := by
  rw [P.poleBlock_of_nonneg h.ge, Complex.conj_eq_iff_im.mpr h, sup_idem]

theorem rootSpace_le_poleBlock_of_nonneg {lam : ℂ} (h : 0 ≤ lam.im) :
    P.rootSpace lam ≤ P.poleBlock lam := by
  rw [P.poleBlock_of_nonneg h]
  exact le_sup_left

theorem rootSpace_le_poleBlock_conj_of_neg {lam : ℂ} (h : lam.im < 0) :
    P.rootSpace lam ≤ P.poleBlock (starRingEnd ℂ lam) := by
  rw [P.poleBlock_of_nonneg (by rw [Complex.conj_im]; linarith), Complex.conj_conj]
  exact le_sup_right

/-- Orthogonality of the two root subspaces of a sup of two root subspaces. -/
theorem form_eq_zero_of_mem_sup {a a' b b' : ℂ} (h1 : b ≠ starRingEnd ℂ a)
    (h2 : b' ≠ starRingEnd ℂ a) (h3 : b ≠ starRingEnd ℂ a') (h4 : b' ≠ starRingEnd ℂ a')
    {x y : N} (hx : x ∈ P.rootSpace a ⊔ P.rootSpace a') (hy : y ∈ P.rootSpace b ⊔ P.rootSpace b') :
    P.form x y = 0 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [form_add_left, form_add_right, form_add_right,
    P.form_eq_zero_of_mem_rootSpace h1 hx₁ hy₁, P.form_eq_zero_of_mem_rootSpace h2 hx₁ hy₂,
    P.form_eq_zero_of_mem_rootSpace h3 hx₂ hy₁, P.form_eq_zero_of_mem_rootSpace h4 hx₂ hy₂]
  ring

/-- **Distinct pole blocks are form-orthogonal**: the primary decomposition is Pontryagin
orthogonal (P4). -/
theorem form_eq_zero_of_mem_poleBlock {lam mu : ℂ} (hne : lam ≠ mu) {x y : N}
    (hx : x ∈ P.poleBlock lam) (hy : y ∈ P.poleBlock mu) : P.form x y = 0 := by
  by_cases hl : 0 ≤ lam.im
  · by_cases hm : 0 ≤ mu.im
    · rw [P.poleBlock_of_nonneg hl] at hx
      rw [P.poleBlock_of_nonneg hm] at hy
      have hconj : ∀ z w : ℂ, 0 ≤ z.im → 0 ≤ w.im → z ≠ w → w ≠ starRingEnd ℂ z := by
        intro z w hz hw hzw heq
        rcases hz.lt_or_eq with hz' | hz'
        · have := congrArg Complex.im heq
          rw [Complex.conj_im] at this
          linarith
        · rw [Complex.conj_eq_iff_im.mpr hz'.symm] at heq
          exact hzw heq.symm
      refine P.form_eq_zero_of_mem_sup (hconj lam mu hl hm hne) ?_ ?_ ?_ hx hy
      · exact fun h => hne ((starRingEnd ℂ).injective h).symm
      · rw [Complex.conj_conj]; exact hne.symm
      · rw [Complex.conj_conj]; exact (hconj mu lam hm hl hne.symm).symm
    · rw [P.poleBlock_of_neg (not_le.mp hm)] at hy
      rw [(Submodule.mem_bot ℂ).mp hy, form_zero_right]
  · rw [P.poleBlock_of_neg (not_le.mp hl)] at hx
    rw [(Submodule.mem_bot ℂ).mp hx, form_zero_left]

/-- **The pole blocks span the state space.**  `S` is any finite set of points containing every
pole with `Im ≥ 0` and the conjugate of every pole with `Im < 0` (e.g. the poles in the closed
upper half-plane). -/
theorem poleBlock_sup_eq_top (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S)) :
    S.sup P.poleBlock = ⊤ := by
  rw [eq_top_iff, ← P.iSup_rootSpace_eq_top]
  refine iSup_le fun lam => ?_
  by_cases hbot : P.rootSpace lam = ⊥
  · rw [hbot]; exact bot_le
  · rcases le_or_gt 0 lam.im with h | h
    · exact (P.rootSpace_le_poleBlock_of_nonneg h).trans (Finset.le_sup ((hS lam hbot).1 h))
    · exact (P.rootSpace_le_poleBlock_conj_of_neg h).trans (Finset.le_sup ((hS lam hbot).2 h))

/-- Each pole block carries a nondegenerate form (global nondegeneracy and orthogonality of the
blocks). -/
theorem isNondegenerateOn_poleBlock (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S))
    {lam : ℂ} (hlam : lam ∈ S) : P.IsNondegenerateOn (P.poleBlock lam) := by
  intro y hy horth
  refine P.eq_zero_of_form_eq_zero fun x => ?_
  have hK : S.sup P.poleBlock ≤ P.rightOrthogonal {y} := by
    refine Finset.sup_le fun mu hmu => ?_
    intro x hx y' hy'
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    by_cases hml : mu = lam
    · subst hml
      exact horth x hx
    · exact P.form_eq_zero_of_mem_poleBlock hml hx hy
  rw [P.poleBlock_sup_eq_top S hS] at hK
  exact hK Submodule.mem_top y (Set.mem_singleton y)

/-- **(P3) Neutral conjugate pairs.**  For a pole `λ` with `Im λ > 0` the block `R_λ ⊔ R_{λ̄}` is a
neutral pairing: `dim R_λ = dim R_{λ̄}`, and its negative and positive indices both equal the
local McMillan degree `dim R_λ`. -/
theorem subNegIndex_poleBlock_of_pos (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S))
    {lam : ℂ} (hlam : lam ∈ S) (him : 0 < lam.im) :
    finrank ℂ (P.rootSpace lam) = finrank ℂ (P.rootSpace (starRingEnd ℂ lam)) ∧
      P.subNegIndex (P.poleBlock lam) = finrank ℂ (P.rootSpace lam) ∧
      P.subPosIndex (P.poleBlock lam) = finrank ℂ (P.rootSpace lam) := by
  have hnd := P.isNondegenerateOn_poleBlock S hS hlam
  rw [P.poleBlock_of_nonneg him.le] at hnd ⊢
  have hne : lam ≠ starRingEnd ℂ lam := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine P.neutral_pair _ _ (disjoint_iff.mp (P.rootSpace_disjoint hne)) ?_ ?_ hnd
  · exact fun x hx => P.form_self_eq_zero_of_mem_rootSpace him.ne' hx
  · exact fun x hx => P.form_self_eq_zero_of_mem_rootSpace (by rw [Complex.conj_im]; linarith) hx

/-- The local contribution of a pole to the negative index: the local Pontryagin inertia
`neg(R_λ)` of a real pole, the local McMillan degree `dim R_λ` of a pole in the upper half-plane
(and `0` for the conjugate lower-half-plane copy). -/
def localIndex (lam : ℂ) : ℕ :=
  if lam.im = 0 then P.subNegIndex (P.rootSpace lam)
  else if 0 < lam.im then finrank ℂ (P.rootSpace lam) else 0

theorem subNegIndex_poleBlock_eq_localIndex (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S))
    {lam : ℂ} (hlam : lam ∈ S) : P.subNegIndex (P.poleBlock lam) = P.localIndex lam := by
  unfold localIndex
  by_cases h0 : lam.im = 0
  · simp only [h0, ite_true]
    rw [P.poleBlock_of_real h0]
  · simp only [h0, ite_false]
    by_cases hpos : 0 < lam.im
    · simp only [hpos, ite_true]
      exact (P.subNegIndex_poleBlock_of_pos S hS hlam hpos).2.1
    · simp only [hpos, ite_false]
      rw [P.poleBlock_of_neg (lt_of_le_of_ne (not_lt.mp hpos) h0), subNegIndex_bot]

theorem negIndex_eq_subNegIndex_top : negIndex P.form = P.subNegIndex ⊤ := by
  rw [subNegIndex]
  refine (negIndex_pullback_eq_of_surjective P.form (by simp) (⊤ : Submodule ℂ N).subtype ?_).symm
  exact Submodule.range_subtype ⊤

/-- **(P4) The global negative index is the sum of the local contributions.**  For any finite set
`S` containing the poles of the closed upper half-plane (and the conjugates of the others),
`negIndex = ∑_{λ ∈ S} localIndex λ = ∑_{real poles} neg(R_λ) + ∑_{Im λ > 0} dim R_λ`. -/
theorem negIndex_eq_sum_localIndex (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S)) :
    negIndex P.form = ∑ lam ∈ S, P.localIndex lam := by
  rw [P.negIndex_eq_subNegIndex_top, ← P.poleBlock_sup_eq_top S hS,
    P.subNegIndex_finset_sup_of_orthogonal P.poleBlock
      (fun i j hij x hx y hy => P.form_eq_zero_of_mem_poleBlock hij hx hy) S]
  exact Finset.sum_congr rfl fun lam hlam => P.subNegIndex_poleBlock_eq_localIndex S hS hlam

/-- A finite set of points satisfying the pole-closure condition always exists (the eigenvalues of
`A` in the closed upper half-plane together with the conjugates of the others). -/
theorem exists_poleFinset : ∃ S : Finset ℂ, ∀ lam, P.rootSpace lam ≠ ⊥ →
    (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S) := by
  classical
  have hfin := P.endA.finite_hasEigenvalue
  refine ⟨hfin.toFinset ∪ hfin.toFinset.image (starRingEnd ℂ), fun lam hlam => ⟨fun _ => ?_,
    fun _ => ?_⟩⟩
  · exact Finset.mem_union_left _ (hfin.mem_toFinset.mpr (P.hasEigenvalue_of_rootSpace_ne_bot hlam))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (hfin.mem_toFinset.mpr (P.hasEigenvalue_of_rootSpace_ne_bot hlam)))

/-- **(P4), minimal form**: for a source-cyclic (minimal) realization the number of negative
squares of the Nevanlinna kernel of `Q` — the minimum global negative index — is the sum of the
local contributions of the poles. -/
theorem negSquares_eq_sum_localIndex (hcyc : P.IsCyclic) (S : Finset ℂ)
    (hS : ∀ lam, P.rootSpace lam ≠ ⊥ →
      (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S)) :
    negSquares (nevanlinnaKernel P.transfer) P.upperResolventSet = ∑ lam ∈ S, P.localIndex lam := by
  rw [P.negSquares_transfer_eq_negIndex hcyc, P.negIndex_eq_sum_localIndex S hS]

end PontryaginRealization
end RenewalGeometry

end
