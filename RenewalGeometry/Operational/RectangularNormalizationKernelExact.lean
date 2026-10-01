/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Operational.SpectatorProduct

/-!
# Exact rectangular normalization kernel

Covers `thm:rectangular-normalization-kernel` of the spacetime–gauge duality paper.

Recorded branches are grouped by their source sector: `Br σ` is the set of branches with
source `A_σ` (dimension `p_σ = card (Src σ)`), and branch `b : Br σ` has target `T σ b`
(dimension `q_b = card (T σ b)`).  With the full rectangular envelope on every branch, the
normalization map is
`Γ_rect((X_b)) = ⊕_σ Σ_{b : Br σ} Tr_{T_b} X_b` (`eq:rectangular-normalization-map`).

* `rectangularNormalization`: the linear map `Γ_rect`.
* `rectangularNormalization_surjective`: surjective onto `⊕_σ M_{p_σ}(ℂ)` when every source
  sector occurs in a branch (with a nonzero-dimensional target).
* `rectangularNormalization_finrank_ker`: the nullity
  `Σ_σ p_σ² (Σ_{b} q_b² − 1)` (`eq:rectangular-normalization-nullity`).
* `rectangularNormalization_injective_iff`: injective exactly when every source sector has
  one outgoing branch and that branch has one-dimensional target.

Scoped hypotheses made explicit: all sector and target dimensions are positive
(`Nonempty (Src σ)`, `Nonempty (T σ b)`), as in the paper's proof ("all `q_a` are positive
integers").
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry

section RectangularNormalization

variable {S : Type*} [Fintype S] [DecidableEq S]
  {Br : S → Type*} [∀ σ, Fintype (Br σ)] [∀ σ, DecidableEq (Br σ)]
  (Src : S → Type*) [∀ σ, Fintype (Src σ)] [∀ σ, DecidableEq (Src σ)]
  (T : ∀ σ, Br σ → Type*) [∀ σ b, Fintype (T σ b)] [∀ σ b, DecidableEq (T σ b)]

/-- The domain `⊕_σ ⊕_{b : Br σ} M_{q_b p_σ}(ℂ)` of amplitude coefficient matrices. -/
abbrev RectangularDomain :=
  ∀ σ, ∀ b : Br σ, Matrix (Src σ × T σ b) (Src σ × T σ b) ℂ

/-- The codomain `⊕_σ M_{p_σ}(ℂ)`. -/
abbrev RectangularCodomain := ∀ σ, Matrix (Src σ) (Src σ) ℂ

theorem partialTraceRight_add {dA dK : Type*} [Fintype dK]
    (X Y : Matrix (dA × dK) (dA × dK) ℂ) :
    partialTraceRight (X + Y) = partialTraceRight X + partialTraceRight Y := by
  ext i j
  simp [partialTraceRight, Finset.sum_add_distrib]

theorem partialTraceRight_smul {dA dK : Type*} [Fintype dK]
    (c : ℂ) (X : Matrix (dA × dK) (dA × dK) ℂ) :
    partialTraceRight (c • X) = c • partialTraceRight X := by
  ext i j
  simp [partialTraceRight, Finset.mul_sum]

/-- The rectangular normalization map `Γ_rect((X_b)) = ⊕_σ Σ_{b : Br σ} Tr_{T_b} X_b`
(`eq:rectangular-normalization-map`). -/
noncomputable def rectangularNormalization :
    RectangularDomain Src T →ₗ[ℂ] RectangularCodomain Src where
  toFun X σ := ∑ b, partialTraceRight (X σ b)
  map_add' X Y := by
    ext σ i j
    simp [partialTraceRight_add, Finset.sum_add_distrib]
  map_smul' c X := by
    funext σ
    simp only [RingHom.id_apply, Pi.smul_apply, partialTraceRight_smul, Finset.smul_sum]

theorem rectangularNormalization_apply (X : RectangularDomain Src T) (σ : S) :
    rectangularNormalization Src T X σ = ∑ b, partialTraceRight (X σ b) :=
  rfl

/-- The lifted amplitude `q⁻¹ (Y ⊗ 1_{T})` normalizes to `Y`. -/
theorem partialTraceRight_kronecker_one {dA dK : Type*} [Fintype dK] [DecidableEq dK]
    (Y : Matrix dA dA ℂ) :
    partialTraceRight (Y ⊗ₖ (1 : Matrix dK dK ℂ)) = (Fintype.card dK : ℂ) • Y := by
  rw [(renewal_spectator_product (dA := dA) (dK := dK) LinearMap.id LinearMap.id
    (fun _ => rfl)).1]
  simp [Matrix.trace_one]

/-- **Surjectivity clause.**  If every source sector occurs in at least one branch (with
positive target dimension), `Γ_rect` is surjective onto `⊕_σ M_{p_σ}(ℂ)`. -/
theorem rectangularNormalization_surjective
    (hocc : ∀ σ, ∃ b : Br σ, Nonempty (T σ b)) :
    Function.Surjective (rectangularNormalization Src T) := by
  classical
  choose b₀ hb₀ using hocc
  intro Y
  refine ⟨fun σ b => if b = b₀ σ then
    ((Fintype.card (T σ b) : ℂ)⁻¹) • (Y σ ⊗ₖ (1 : Matrix (T σ b) (T σ b) ℂ)) else 0, ?_⟩
  ext σ i j
  rw [rectangularNormalization_apply]
  have hsum : ∀ b : Br σ, partialTraceRight
      (if b = b₀ σ then
        ((Fintype.card (T σ b) : ℂ)⁻¹) • (Y σ ⊗ₖ (1 : Matrix (T σ b) (T σ b) ℂ)) else 0) =
      if b = b₀ σ then Y σ else 0 := by
    intro b
    split_ifs with hb
    · rw [partialTraceRight_smul, partialTraceRight_kronecker_one, smul_smul]
      have hcard : (Fintype.card (T σ b) : ℂ) ≠ 0 := by
        subst hb
        have := hb₀ σ
        exact_mod_cast Fintype.card_ne_zero
      rw [inv_mul_cancel₀ hcard, one_smul]
    · ext k l
      simp [partialTraceRight]
  simp_rw [hsum]
  rw [Finset.sum_ite_eq' Finset.univ (b₀ σ)]
  simp

/-- The domain dimension `Σ_σ p_σ² Σ_{b} q_b²`. -/
theorem finrank_rectangularDomain :
    Module.finrank ℂ (RectangularDomain Src T) =
      ∑ σ, Fintype.card (Src σ) ^ 2 * ∑ b : Br σ, Fintype.card (T σ b) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.finrank_pi_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Module.finrank_matrix, Fintype.card_prod, Module.finrank_self]
  ring

/-- The codomain dimension `Σ_σ p_σ²`. -/
theorem finrank_rectangularCodomain :
    Module.finrank ℂ (RectangularCodomain Src) = ∑ σ, Fintype.card (Src σ) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.finrank_matrix, Module.finrank_self]
  ring

/-- Rank–nullity form of the nullity formula (no subtraction):
`dim Ker Γ_rect + Σ_σ p_σ² = Σ_σ p_σ² Σ_b q_b²`. -/
theorem rectangularNormalization_finrank_ker_add
    (hocc : ∀ σ, ∃ b : Br σ, Nonempty (T σ b)) :
    Module.finrank ℂ (LinearMap.ker (rectangularNormalization Src T)) +
        ∑ σ, Fintype.card (Src σ) ^ 2 =
      ∑ σ, Fintype.card (Src σ) ^ 2 * ∑ b : Br σ, Fintype.card (T σ b) ^ 2 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (rectangularNormalization Src T)
  rw [LinearMap.range_eq_top.mpr (rectangularNormalization_surjective Src T hocc),
    finrank_top, finrank_rectangularCodomain, finrank_rectangularDomain] at hrn
  rw [add_comm]
  exact hrn

/-- Each sector with an occurring branch of positive target dimension has
`Σ_b q_b² ≥ 1`. -/
theorem one_le_sum_card_sq (hocc : ∀ σ, ∃ b : Br σ, Nonempty (T σ b)) (σ : S) :
    1 ≤ ∑ b : Br σ, Fintype.card (T σ b) ^ 2 := by
  obtain ⟨b, hb⟩ := hocc σ
  calc 1 ≤ Fintype.card (T σ b) ^ 2 := by
        have := Fintype.card_pos (α := T σ b)
        nlinarith
    _ ≤ ∑ b : Br σ, Fintype.card (T σ b) ^ 2 :=
        Finset.single_le_sum (f := fun b => Fintype.card (T σ b) ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

/-- **Nullity clause (`eq:rectangular-normalization-nullity`).**
`dim_ℂ Ker Γ_rect = Σ_σ p_σ² (Σ_{b : Br σ} q_b² − 1)`. -/
theorem rectangularNormalization_finrank_ker
    (hocc : ∀ σ, ∃ b : Br σ, Nonempty (T σ b)) :
    Module.finrank ℂ (LinearMap.ker (rectangularNormalization Src T)) =
      ∑ σ, Fintype.card (Src σ) ^ 2 * (∑ b : Br σ, Fintype.card (T σ b) ^ 2 - 1) := by
  have h := rectangularNormalization_finrank_ker_add Src T hocc
  have hsplit : ∀ σ, Fintype.card (Src σ) ^ 2 * ∑ b : Br σ, Fintype.card (T σ b) ^ 2 =
      Fintype.card (Src σ) ^ 2 * (∑ b : Br σ, Fintype.card (T σ b) ^ 2 - 1) +
        Fintype.card (Src σ) ^ 2 := by
    intro σ
    rw [Nat.mul_sub_one, Nat.sub_add_cancel]
    exact Nat.le_mul_of_pos_right _ (one_le_sum_card_sq T hocc σ)
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, Finset.sum_add_distrib] at h
  exact Nat.add_right_cancel h

/-- A sector's summand vanishes exactly when it has one branch with one-dimensional
target (positive dimensions throughout). -/
theorem sum_card_sq_eq_one_iff (σ : S) [Nonempty (Br σ)] (hq : ∀ b, Nonempty (T σ b)) :
    ∑ b : Br σ, Fintype.card (T σ b) ^ 2 = 1 ↔
      Fintype.card (Br σ) = 1 ∧ ∀ b, Fintype.card (T σ b) = 1 := by
  have hpos : ∀ b : Br σ, 1 ≤ Fintype.card (T σ b) ^ 2 := by
    intro b
    have := hq b
    have := Fintype.card_pos (α := T σ b)
    nlinarith
  constructor
  · intro h
    have hcard : Fintype.card (Br σ) ≤ 1 := by
      calc Fintype.card (Br σ) = ∑ _b : Br σ, 1 := by simp
        _ ≤ ∑ b : Br σ, Fintype.card (T σ b) ^ 2 := Finset.sum_le_sum fun b _ => hpos b
        _ = 1 := h
    refine ⟨le_antisymm hcard Fintype.card_pos, fun b => ?_⟩
    have hle : Fintype.card (T σ b) ^ 2 ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun b => Fintype.card (T σ b) ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have hsq : Fintype.card (T σ b) ^ 2 = 1 := le_antisymm hle (hpos b)
    exact (pow_eq_one_iff.mp hsq).resolve_right (by norm_num)
  · rintro ⟨hBr, hT⟩
    calc ∑ b : Br σ, Fintype.card (T σ b) ^ 2 = ∑ _b : Br σ, 1 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hT b, one_pow]
      _ = 1 := by simp [hBr]

/-- **Injectivity clause.**  With positive sector and target dimensions and every sector
occurring, `Γ_rect` is injective exactly when every source sector has one outgoing recorded
branch and that branch has one-dimensional target. -/
theorem rectangularNormalization_injective_iff
    (hp : ∀ σ, Nonempty (Src σ)) (hq : ∀ σ b, Nonempty (T σ b))
    (hocc : ∀ σ, Nonempty (Br σ)) :
    Function.Injective (rectangularNormalization Src T) ↔
      ∀ σ, Fintype.card (Br σ) = 1 ∧ ∀ b, Fintype.card (T σ b) = 1 := by
  have hocc' : ∀ σ, ∃ b : Br σ, Nonempty (T σ b) := fun σ =>
    ⟨Classical.choice (hocc σ), hq σ _⟩
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero,
    rectangularNormalization_finrank_ker Src T hocc', Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_imp_iff]
  refine forall_congr' fun σ => ?_
  have := hocc σ
  have := hp σ
  have hpσ : Fintype.card (Src σ) ^ 2 ≠ 0 := by
    have := Fintype.card_pos (α := Src σ)
    positivity
  rw [mul_eq_zero, or_iff_right hpσ, Nat.sub_eq_zero_iff_le]
  have h1 := one_le_sum_card_sq T hocc' σ
  rw [← sum_card_sq_eq_one_iff T σ (hq σ)]
  constructor
  · intro h
    exact le_antisymm h h1
  · intro h
    exact h.le

end RectangularNormalization

end RenewalGeometry
