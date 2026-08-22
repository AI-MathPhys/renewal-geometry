/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PsdBlockSchurExact

/-!
# Target-short reverse influence

Exact encoding of `thm:GT-target-short-influence` (RI.7–RI.9).

Relative to the target support `K ⊕ K^⊥` (index types `k ⊕ l`), the source
Gram is `B = [[A, D], [D^*, E]] ⪰ 0` and the target `C = [[C₁, 0], [0, 0]]`
is supported on `K`.

* `protectedShort B = A - D E^† D^*` (RI.7) is positive (`protectedShort_posSemidef`);
* `admissible_iff` / `influence_eq` (RI.8): the admissible influence constants
  of `(B, C)` and of `(S_K(B), C₁)` coincide, hence `Λ(B,C) = Λ(S_K(B), C|_K)`,
  and `normalized_inf_eq`: `μ_C(B) = μ_{C|_K}(S_K(B))`;
* `influence_window` (RI.9): with `m P_K ⪯ C ⪯ M P_K` and `β_K(B) = λ_min(S_K(B))`,
  `m/β ≤ Λ(B,C) ≤ M/β`.

The infinite convention of (RI.9) is the `β = 0` branch, excluded here by
`0 < β` (then `m/β`, `M/β` are the displayed finite bounds).
-/

open Matrix Finset NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence NCG.PsdBlockSchur
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace TargetShortInfluence

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- The source Gram in target-support coordinates. -/
abbrev sourceBlock (A : Matrix k k ℂ) (D : Matrix k l ℂ) (E : Matrix l l ℂ) :
    Matrix (k ⊕ l) (k ⊕ l) ℂ :=
  fromBlocks A D Dᴴ E

/-- The target supported on `K`. -/
abbrev targetBlock (C₁ : Matrix k k ℂ) : Matrix (k ⊕ l) (k ⊕ l) ℂ :=
  fromBlocks C₁ 0 0 0

/-- The protected short `S_K(B) = A - D E^† D^*`. -/
noncomputable def protectedShort (A : Matrix k k ℂ) (D : Matrix k l ℂ) {E : Matrix l l ℂ}
    (hE : E.IsHermitian) : Matrix k k ℂ :=
  A - D * pinv hE * Dᴴ

/-- The swapped block matrix `[[E, D^*], [D, A]]` used to pivot on `K^⊥`. -/
abbrev swappedBlock (A : Matrix k k ℂ) (D : Matrix k l ℂ) (E : Matrix l l ℂ) :
    Matrix (l ⊕ k) (l ⊕ k) ℂ :=
  fromBlocks E Dᴴ D A

omit [DecidableEq k] [DecidableEq l] in
/-- The quadratic forms of the source block and of its swap agree. -/
theorem form_swap (A : Matrix k k ℂ) (D : Matrix k l ℂ) (E : Matrix l l ℂ) (y : k → ℂ)
    (v : l → ℂ) :
    star (Sum.elim y v) ⬝ᵥ (sourceBlock A D E *ᵥ Sum.elim y v)
      = star (Sum.elim v y) ⬝ᵥ (swappedBlock A D E *ᵥ Sum.elim v y) := by
  have h1 := block_form A D E y v
  have h2 := block_form E Dᴴ A v y
  rw [conjTranspose_conjTranspose] at h2
  rw [h1, h2]
  ring

omit [DecidableEq k] [DecidableEq l] in
/-- The target form only sees the `K` component. -/
theorem target_form (C₁ : Matrix k k ℂ) (y : k → ℂ) (v : l → ℂ) :
    star (Sum.elim y v) ⬝ᵥ (targetBlock C₁ *ᵥ Sum.elim y v) = star y ⬝ᵥ (C₁ *ᵥ y) := by
  have h := block_form C₁ (0 : Matrix k l ℂ) (0 : Matrix l l ℂ) y v
  rw [conjTranspose_zero] at h
  rw [h]
  simp

omit [DecidableEq k] [DecidableEq l] in
theorem swappedBlock_posSemidef {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) : (fromBlocks E Dᴴ Dᴴᴴ A).PosSemidef := by
  rw [conjTranspose_conjTranspose]
  have hH := isHermitian_fromBlocks_iff.mp hB.1
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨IsHermitian.fromBlocks hH.2.2.2 (by rw [conjTranspose_conjTranspose]) hH.1, fun z => ?_⟩
  rw [← Sum.elim_comp_inl_inr z, ← form_swap]
  exact hB.dotProduct_mulVec_nonneg _

omit [DecidableEq k] [DecidableEq l] in
theorem left_posSemidef {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) : E.PosSemidef := by
  have hH := isHermitian_fromBlocks_iff.mp hB.1
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH.2.2.2, fun v => ?_⟩
  have := hB.dotProduct_mulVec_nonneg (Sum.elim 0 v)
  rw [block_form] at this
  simpa using this

omit [DecidableEq k] in
/-- **(RI.7)**: the protected short is positive. -/
theorem protectedShort_posSemidef {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) :
    (protectedShort A D (left_posSemidef hB).1).PosSemidef := by
  have hS := schur_posSemidef (left_posSemidef hB) Dᴴ A (swappedBlock_posSemidef hB)
  rw [conjTranspose_conjTranspose] at hS
  exact hS

omit [DecidableEq k] in
/-- The range condition of the pivot block. -/
theorem range_condition {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) :
    E * pinv (left_posSemidef hB).1 * Dᴴ = Dᴴ :=
  range_condition_of_posSemidef (left_posSemidef hB) Dᴴ A (swappedBlock_posSemidef hB)

omit [DecidableEq k] in
/-- Completion of the square for the source form: the `K^⊥` component only
adds a positive term above the protected short. -/
theorem source_form_eq {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (y : k → ℂ) (v : l → ℂ) :
    star (Sum.elim y v) ⬝ᵥ (sourceBlock A D E *ᵥ Sum.elim y v)
      = star (v + pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y))
          ⬝ᵥ (E *ᵥ (v + pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y)))
        + star y ⬝ᵥ (protectedShort A D (left_posSemidef hB).1 *ᵥ y) := by
  rw [form_swap]
  have := completion_of_square (left_posSemidef hB) Dᴴ A (range_condition hB) v y
  rw [conjTranspose_conjTranspose] at this
  exact this

omit [DecidableEq k] in
theorem rayleigh_source_ge {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (y : k → ℂ) (v : l → ℂ) :
    rayleigh (protectedShort A D (left_posSemidef hB).1) y
      ≤ rayleigh (sourceBlock A D E) (Sum.elim y v) := by
  unfold rayleigh
  rw [source_form_eq hB, Complex.add_re]
  have := (Complex.le_def.mp ((left_posSemidef hB).dotProduct_mulVec_nonneg
    (v + pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y)))).1
  rw [Complex.zero_re] at this
  linarith

omit [DecidableEq k] in
theorem rayleigh_source_eq {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (y : k → ℂ) :
    rayleigh (sourceBlock A D E) (Sum.elim y (-(pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y))))
      = rayleigh (protectedShort A D (left_posSemidef hB).1) y := by
  unfold rayleigh
  rw [source_form_eq hB, neg_add_cancel, mulVec_zero, dotProduct_zero, zero_add]

omit [DecidableEq k] [DecidableEq l] in
theorem rayleigh_target (C₁ : Matrix k k ℂ) (y : k → ℂ) (v : l → ℂ) :
    rayleigh (targetBlock C₁) (Sum.elim y v) = rayleigh C₁ y := by
  unfold rayleigh
  rw [target_form]

omit [DecidableEq k] in
/-- **(RI.8, admissible constants)**: `C ⪯ λ B` iff `C|_K ⪯ λ S_K(B)`. -/
theorem admissible_iff {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (C₁ : Matrix k k ℂ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ x, rayleigh (targetBlock C₁) x ≤ lam * rayleigh (sourceBlock A D E) x) ↔
      ∀ y, rayleigh C₁ y ≤ lam * rayleigh (protectedShort A D (left_posSemidef hB).1) y := by
  constructor
  · intro h y
    have := h (Sum.elim y (-(pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y))))
    rwa [rayleigh_target, rayleigh_source_eq hB] at this
  · intro h x
    rw [← Sum.elim_comp_inl_inr x, rayleigh_target]
    refine le_trans (h _) ?_
    exact mul_le_mul_of_nonneg_left (rayleigh_source_ge hB _ _) hlam

omit [DecidableEq k] in
/-- **(RI.8)**: `Λ(B, C) = Λ(S_K(B), C|_K)`. -/
theorem influence_eq {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (C₁ : Matrix k k ℂ) :
    influence (sourceBlock A D E) (targetBlock C₁)
      = influence (protectedShort A D (left_posSemidef hB).1) C₁ := by
  unfold influence
  congr 1
  ext lam
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h⟩; exact ⟨h0, (admissible_iff hB C₁ lam h0).mp h⟩
  · rintro ⟨h0, h⟩; exact ⟨h0, (admissible_iff hB C₁ lam h0).mpr h⟩

omit [DecidableEq k] in
/-- **(RI.8)**: `μ_C(B) = μ_{C|_K}(S_K(B))`. -/
theorem normalized_inf_eq {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (C₁ : Matrix k k ℂ) :
    sInf (normalizedEnergies (sourceBlock A D E) (targetBlock C₁))
      = sInf (normalizedEnergies (protectedShort A D (left_posSemidef hB).1) C₁) := by
  set S := protectedShort A D (left_posSemidef hB).1 with hSdef
  have hSpsd : S.PosSemidef := protectedShort_posSemidef hB
  have hbdd₁ : BddBelow (normalizedEnergies (sourceBlock A D E) (targetBlock C₁)) :=
    ⟨0, fun s ⟨x, _, hx⟩ => hx ▸ rayleigh_nonneg hB x⟩
  have hbdd₂ : BddBelow (normalizedEnergies S C₁) :=
    ⟨0, fun s ⟨y, _, hy⟩ => hy ▸ rayleigh_nonneg hSpsd y⟩
  -- every short energy is a source energy
  have hsub : normalizedEnergies S C₁
      ⊆ normalizedEnergies (sourceBlock A D E) (targetBlock C₁) := by
    rintro s ⟨y, hy, rfl⟩
    refine ⟨Sum.elim y (-(pinv (left_posSemidef hB).1 *ᵥ (Dᴴ *ᵥ y))), ?_, ?_⟩
    · rw [rayleigh_target]; exact hy
    · rw [rayleigh_source_eq hB]
  rcases Set.eq_empty_or_nonempty (normalizedEnergies S C₁) with hemp | hne
  · -- then the source set is empty as well
    have : normalizedEnergies (sourceBlock A D E) (targetBlock C₁) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro s ⟨x, hx, rfl⟩
      rw [← Sum.elim_comp_inl_inr x, rayleigh_target] at hx
      have : rayleigh S (x ∘ Sum.inl) ∈ normalizedEnergies S C₁ := ⟨_, hx, rfl⟩
      rw [hemp] at this
      exact this
    rw [this, hemp]
  · apply le_antisymm
    · exact csInf_le_csInf hbdd₁ hne hsub
    · refine le_csInf (hne.mono hsub) fun s ⟨x, hx, hs⟩ => ?_
      rw [← Sum.elim_comp_inl_inr x, rayleigh_target] at hx
      have hmem : rayleigh S (x ∘ Sum.inl) ∈ normalizedEnergies S C₁ := ⟨_, hx, rfl⟩
      calc sInf (normalizedEnergies S C₁) ≤ rayleigh S (x ∘ Sum.inl) := csInf_le hbdd₂ hmem
        _ ≤ rayleigh (sourceBlock A D E) (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) :=
            rayleigh_source_ge hB _ _
        _ = s := by rw [Sum.elim_comp_inl_inr, hs]

omit [DecidableEq k] in
/-- **(RI.9)**: with `m P_K ⪯ C ⪯ M P_K` and `β = λ_min(S_K(B)) > 0`,
`m/β ≤ Λ(B,C) ≤ M/β`. -/
theorem influence_window {A : Matrix k k ℂ} {D : Matrix k l ℂ} {E : Matrix l l ℂ}
    (hB : (sourceBlock A D E).PosSemidef) (C₁ : Matrix k k ℂ) (m M β : ℝ) (hm : 0 ≤ m)
    (hmM : m ≤ M) (hβ : 0 < β)
    (hCm : ∀ y, m * ∑ j, ‖y j‖ ^ 2 ≤ rayleigh C₁ y)
    (hCM : ∀ y, rayleigh C₁ y ≤ M * ∑ j, ‖y j‖ ^ 2)
    (hβmin : IsMinRayleigh (protectedShort A D (left_posSemidef hB).1) β) :
    m / β ≤ influence (sourceBlock A D E) (targetBlock C₁) ∧
      influence (sourceBlock A D E) (targetBlock C₁) ≤ M / β := by
  rw [influence_eq hB C₁]
  set S := protectedShort A D (left_posSemidef hB).1 with hSdef
  obtain ⟨hβle, y₀, hy₀, hy₀eq⟩ := hβmin
  have hMβ : 0 ≤ M / β := div_nonneg (le_trans hm hmM) hβ.le
  have hmem : M / β ∈ {lam : ℝ | 0 ≤ lam ∧ ∀ y, rayleigh C₁ y ≤ lam * rayleigh S y} := by
    refine ⟨hMβ, fun y => ?_⟩
    calc rayleigh C₁ y ≤ M * ∑ j, ‖y j‖ ^ 2 := hCM y
      _ = (M / β) * (β * ∑ j, ‖y j‖ ^ 2) := by field_simp
      _ ≤ (M / β) * rayleigh S y := mul_le_mul_of_nonneg_left (hβle y) hMβ
  have hbdd : BddBelow {lam : ℝ | 0 ≤ lam ∧ ∀ y, rayleigh C₁ y ≤ lam * rayleigh S y} :=
    ⟨0, fun lam hl => hl.1⟩
  constructor
  · refine le_csInf ⟨_, hmem⟩ fun lam hl => ?_
    have hn : 0 < ∑ j, ‖y₀ j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy₀)
    have h1 := hCm y₀
    have h2 := hl.2 y₀
    rw [hy₀eq] at h2
    rw [div_le_iff₀ hβ]
    have : m * ∑ j, ‖y₀ j‖ ^ 2 ≤ lam * β * ∑ j, ‖y₀ j‖ ^ 2 := by
      calc m * ∑ j, ‖y₀ j‖ ^ 2 ≤ lam * (β * ∑ j, ‖y₀ j‖ ^ 2) := le_trans h1 h2
        _ = lam * β * ∑ j, ‖y₀ j‖ ^ 2 := by ring
    exact le_of_mul_le_mul_right this hn
  · exact csInf_le hbdd hmem

end TargetShortInfluence
end NCG
