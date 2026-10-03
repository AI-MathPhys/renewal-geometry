/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.InternalSeedSaturationExact

/-!
# The complete labelled `S₄` census (`eq:SM-complete-census`)

The census clause of `thm:active-isotypic`: the five irreducible complex representations of
`S₄` are recorded in the fixed order `(𝟏, sgn, W, W^sgn, V₂)` (`eq:complete-S4-census`).  The
proposed assignment puts the colour block on `𝟏`, the weak block on `W` and the two scalar
blocks on `W^sgn` and `V₂` (`place = ![0, 2, 3, 4] : Fin 4 → Fin 5`), with target block sizes
`smCensus = (3, 0, 2, 1, 1)`.

* `matrix_algEquiv_iff`: `M_a(ℂ) ≅ M_b(ℂ)` iff `a = b`;
* `labelled_exhaustion_iff`: label-preserving identifications of every multiplicity factor
  `M_{m_λ}(ℂ)` with the assigned factor exist iff `m = (3, 0, 2, 1, 1)`;
* `finrank_pi_matrix`, `sign_entry_extra_summand`: with the colour, weak and scalar entries
  in place, `dim ⊕_λ M_{m_λ} = 15 + m_sgn²`, so the product is `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (dimension
  `15`) iff `m_sgn = 0` — a nonzero sign entry is an additional summand;
* for the external relative commutant with sector labelling `lab : ι → Fin 5` (injective, the
  `S₄`-label of each isotypic sector of `thm:active-isotypic`):
  `finrank_extCommutant_eq_sum_sq` (`dim 𝒜'_tet,r = ∑_λ m_{λ,r}²`),
  `labelled_census_iff_assignment` (the census is `(3, 0, 2, 1, 1)` iff the sectors are
  identified with the four blocks of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` compatibly with the assignment, i.e.
  the census hypothesis `(e, hcard)` of `thm:internal-seed-saturation`), and
  `extCommutant_finrank_of_sign_entry` (a nonzero sign entry raises the dimension of the
  relative commutant to `15 + m_sgn² > 15`).
-/

open Matrix Module Finset

namespace RenewalGeometry
namespace LabelledCensus

/-- The target census `(m_𝟏, m_sgn, m_W, m_{W^sgn}, m_{V₂}) = (3, 0, 2, 1, 1)`. -/
def smCensus : Fin 5 → ℕ := ![3, 0, 2, 1, 1]

/-- The proposed assignment of the colour, weak and two scalar blocks to the trivial,
standard, sign-twisted standard and two-dimensional sectors. -/
def place : Fin 4 → Fin 5 := ![0, 2, 3, 4]

theorem place_injective : Function.Injective place := by decide

theorem place_ne_sgn (k : Fin 4) : place k ≠ 1 := by fin_cases k <;> decide

theorem exists_place_of_ne_sgn (l : Fin 5) (h : l ≠ 1) : ∃ k, place k = l := by
  fin_cases l <;> first | exact absurd rfl h | decide

theorem smCensus_place (k : Fin 4) : smCensus (place k) = ![3, 2, 1, 1] k := by
  fin_cases k <;> rfl

/-- `M_a(ℂ) ≅ M_b(ℂ)` as `ℂ`-algebras iff `a = b`. -/
theorem matrix_algEquiv_iff (a b : ℕ) :
    Nonempty (Matrix (Fin a) (Fin a) ℂ ≃ₐ[ℂ] Matrix (Fin b) (Fin b) ℂ) ↔ a = b := by
  constructor
  · rintro ⟨φ⟩
    have h := φ.toLinearEquiv.finrank_eq
    simp only [finrank_matrix, Fintype.card_fin, finrank_self, mul_one] at h
    exact Nat.mul_self_inj.mp h
  · rintro rfl
    exact ⟨AlgEquiv.refl⟩

/-- **`eq:SM-complete-census`, block form.**  Exact exhaustion of the relative commutant by
the assigned blocks — a label-preserving identification of every multiplicity factor
`M_{m_λ}(ℂ)` with the assigned factor (`M₃` on `𝟏`, nothing on `sgn`, `M₂` on `W`, `ℂ` on
`W^sgn` and `V₂`) — holds iff `m = (3, 0, 2, 1, 1)`. -/
theorem labelled_exhaustion_iff (m : Fin 5 → ℕ) :
    (∀ l, Nonempty (Matrix (Fin (m l)) (Fin (m l)) ℂ ≃ₐ[ℂ]
      Matrix (Fin (smCensus l)) (Fin (smCensus l)) ℂ)) ↔ m = smCensus := by
  constructor
  · intro h; funext l; exact (matrix_algEquiv_iff _ _).mp (h l)
  · rintro rfl l; exact ⟨AlgEquiv.refl⟩

/-- `dim ⊕_λ M_{m_λ}(ℂ) = ∑_λ m_λ²`. -/
theorem finrank_pi_matrix {κ : Type} [Fintype κ] (m : κ → ℕ) :
    finrank ℂ (∀ l, Matrix (Fin (m l)) (Fin (m l)) ℂ) = ∑ l, m l * m l := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_matrix]

/-- **The sign entry is an additional summand.**  If the colour, weak and scalar entries are
`3, 2, 1, 1`, then `dim ⊕_λ M_{m_λ} = 15 + m_sgn²`, and the labelled multiplicity algebra is
isomorphic to `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` iff `m_sgn = 0`. -/
theorem sign_entry_extra_summand (m : Fin 5 → ℕ) (h0 : m 0 = 3) (h2 : m 2 = 2) (h3 : m 3 = 1)
    (h4 : m 4 = 1) :
    finrank ℂ (∀ l, Matrix (Fin (m l)) (Fin (m l)) ℂ) = 15 + m 1 * m 1 ∧
    (Nonempty ((∀ l, Matrix (Fin (m l)) (Fin (m l)) ℂ) ≃ₐ[ℂ]
        (∀ l, Matrix (Fin (smCensus l)) (Fin (smCensus l)) ℂ)) ↔ m 1 = 0) := by
  have hdim : finrank ℂ (∀ l, Matrix (Fin (m l)) (Fin (m l)) ℂ) = 15 + m 1 * m 1 := by
    rw [finrank_pi_matrix, Fin.sum_univ_five, h0, h2, h3, h4]; ring
  refine ⟨hdim, ⟨fun ⟨φ⟩ => ?_, fun h1 => ?_⟩⟩
  · have h := φ.toLinearEquiv.finrank_eq
    rw [hdim, finrank_pi_matrix, Fin.sum_univ_five] at h
    simp [smCensus] at h
    exact h
  · have hm : m = smCensus := by
      funext l; fin_cases l <;> simp [smCensus, h0, h1, h2, h3, h4]
    subst hm
    exact ⟨AlgEquiv.refl⟩

/-! ### The labelled census of the external relative commutant -/

section Commutant

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ι → Type} [∀ b, Fintype (J b)]

/-- The labelled census `m_λ = ∑_{b : lab b = λ} |J b|` of a sector decomposition with
`S₄`-labels `lab`. -/
def labelledCensus (lab : ι → Fin 5) (J : ι → Type) [∀ b, Fintype (J b)] (l : Fin 5) : ℕ :=
  ∑ b ∈ univ.filter (fun b => lab b = l), Fintype.card (J b)

theorem labelledCensus_lab {lab : ι → Fin 5} (hlab : Function.Injective lab) (b : ι) :
    labelledCensus lab J (lab b) = Fintype.card (J b) := by
  rw [labelledCensus, Finset.sum_eq_single b]
  · intro b' hb' hne
    exact absurd (hlab (Finset.mem_filter.mp hb').2) hne
  · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ b, rfl⟩ :
      b ∈ univ.filter (fun b' => lab b' = lab b)) h

theorem labelledCensus_eq_zero {lab : ι → Fin 5} {l : Fin 5} (hl : ∀ b, lab b ≠ l) :
    labelledCensus lab J l = 0 := by
  rw [labelledCensus, Finset.sum_eq_zero]
  intro b hb
  exact absurd (Finset.mem_filter.mp hb).2 (hl b)

/-- With injective labels, `∑_λ m_λ² = ∑_b |J b|²`. -/
theorem sum_sq_labelledCensus {lab : ι → Fin 5} (hlab : Function.Injective lab) :
    ∑ l, labelledCensus lab J l * labelledCensus lab J l =
      ∑ b, Fintype.card (J b) * Fintype.card (J b) := by
  classical
  have h : ∀ l, labelledCensus lab J l * labelledCensus lab J l =
      ∑ b ∈ univ.filter (fun b => lab b = l), Fintype.card (J b) * Fintype.card (J b) := by
    intro l
    by_cases hl : ∃ b, lab b = l
    · obtain ⟨b, rfl⟩ := hl
      rw [labelledCensus_lab hlab, Finset.sum_eq_single b]
      · intro b' hb' hne
        exact absurd (hlab (Finset.mem_filter.mp hb').2) hne
      · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ b, rfl⟩ :
      b ∈ univ.filter (fun b' => lab b' = lab b)) h
    · push_neg at hl
      rw [labelledCensus_eq_zero hl, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      exact absurd (Finset.mem_filter.mp hb).2 (hl b)
  rw [Finset.sum_congr rfl fun l _ => h l]
  exact Finset.sum_fiberwise univ lab _

variable [∀ b, DecidableEq (J b)]

/-- **The labelled census is exactly the census hypothesis of `thm:internal-seed-saturation`.**
For injective sector labels and nonempty multiplicity spaces, the labelled census is
`(3, 0, 2, 1, 1)` iff there is an identification `e : ι ≃ Fin 4` of the sectors with the four
blocks of `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`, compatible with the assignment (`lab = place ∘ e`), with block
multiplicities `(3, 2, 1, 1)`. -/
theorem labelled_census_iff_assignment {lab : ι → Fin 5} (hlab : Function.Injective lab)
    (hNJ : ∀ b, Nonempty (J b)) :
    labelledCensus lab J = smCensus ↔
      ∃ e : ι ≃ Fin 4, (∀ b, lab b = place (e b)) ∧
        ∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k := by
  constructor
  · intro hc
    have hcard : ∀ b, Fintype.card (J b) = smCensus (lab b) := by
      intro b; rw [← labelledCensus_lab hlab b, hc]
    have hns : ∀ b, lab b ≠ 1 := by
      intro b hb
      have h := hcard b
      rw [hb] at h
      have h' : Fintype.card (J b) = 0 := by simpa [smCensus] using h
      exact absurd h' (Fintype.card_pos (α := J b)).ne'
    choose f hf using fun b => exists_place_of_ne_sgn (lab b) (hns b)
    have hfinj : Function.Injective f := by
      intro b b' h
      apply hlab
      rw [← hf b, ← hf b', h]
    have hfsurj : Function.Surjective f := by
      intro k
      have hpos : 0 < labelledCensus lab J (place k) := by
        rw [hc, smCensus_place]; fin_cases k <;> decide
      by_contra hnot
      push_neg at hnot
      have : ∀ b, lab b ≠ place k := by
        intro b hb
        apply hnot b
        apply place_injective
        rw [hf b, hb]
      rw [labelledCensus_eq_zero this] at hpos
      exact lt_irrefl _ hpos
    let e : ι ≃ Fin 4 := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
    refine ⟨e, fun b => (hf b).symm, fun k => ?_⟩
    rw [hcard, ← smCensus_place]
    congr 1
    have := hf (e.symm k)
    rw [← this]
    congr 1
    exact e.apply_symm_apply k
  · rintro ⟨e, hlabe, hcard⟩
    funext l
    by_cases hl : l = 1
    · subst hl
      rw [labelledCensus_eq_zero (fun b hb => place_ne_sgn (e b) ((hlabe b).symm.trans hb))]
      rfl
    · obtain ⟨k, rfl⟩ := exists_place_of_ne_sgn l hl
      have hb : lab (e.symm k) = place k := by rw [hlabe, e.apply_symm_apply]
      rw [← hb, labelledCensus_lab hlab, hcard, hb, smCensus_place]

end Commutant

section ExtCommutant

open InternalSeedSaturation

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]
  {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- **`eq:external-isotypic-commutant` in dimensions**: with the isotypic data of
`thm:active-isotypic` and injective `S₄`-labels of the sectors,
`dim 𝒜'_tet,r = ∑_λ m_{λ,r}²`. -/
theorem finrank_extCommutant_eq_sum_sq (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
      matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    {lab : ι → Fin 5} (hlab : Function.Injective lab) :
    finrank ℂ (extCommutant ρ) = ∑ l, labelledCensus lab J l * labelledCensus lab J l := by
  have e1 := AlgEquiv.ofInjective _ (extEmbed_injective W hW1 hW2 hNI)
  have e2 := Subalgebra.equivOfEq _ _ (range_extEmbed ρ W hW1 hW2 hM)
  rw [← (e1.trans e2).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype,
    sum_sq_labelledCensus hlab]
  simp [finrank_matrix]

/-- **A nonzero sign entry cannot be omitted**: if the trivial, standard, sign-twisted and
two-dimensional entries are `3, 2, 1, 1` but `m_sgn > 0`, then
`dim 𝒜'_tet,r = 15 + m_sgn² > 15 = dim (M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ)`, so the relative commutant is not
`M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` and no assignment-compatible identification exists. -/
theorem extCommutant_finrank_of_sign_entry (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
      matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    {lab : ι → Fin 5} (hlab : Function.Injective lab)
    (h0 : labelledCensus lab J 0 = 3) (h2 : labelledCensus lab J 2 = 2)
    (h3 : labelledCensus lab J 3 = 1) (h4 : labelledCensus lab J 4 = 1)
    (hsgn : 0 < labelledCensus lab J 1) :
    finrank ℂ (extCommutant ρ) = 15 + labelledCensus lab J 1 * labelledCensus lab J 1 ∧
      15 < finrank ℂ (extCommutant ρ) ∧
      IsEmpty (InternalAssembly.blockAlgebra ≃ₐ[ℂ] extCommutant ρ) ∧
      ¬ ∃ e : ι ≃ Fin 4, ∀ b, lab b = place (e b) := by
  have hdim : finrank ℂ (extCommutant ρ) =
      15 + labelledCensus lab J 1 * labelledCensus lab J 1 := by
    rw [finrank_extCommutant_eq_sum_sq ρ W hW1 hW2 hNI hM hlab, Fin.sum_univ_five, h0, h2, h3, h4]
    ring
  have hlt : 15 < finrank ℂ (extCommutant ρ) := by
    rw [hdim]; have := Nat.mul_pos hsgn hsgn; omega
  refine ⟨hdim, hlt, ⟨fun φ => ?_⟩, ?_⟩
  · have h := φ.toLinearEquiv.finrank_eq
    rw [CentralSeparation.finrank_blockAlgebra] at h
    omega
  · rintro ⟨e, he⟩
    have : ∀ b, lab b ≠ 1 := fun b hb => place_ne_sgn (e b) ((he b).symm.trans hb)
    rw [labelledCensus_eq_zero this] at hsgn
    exact lt_irrefl _ hsgn

end ExtCommutant

end LabelledCensus
end RenewalGeometry
