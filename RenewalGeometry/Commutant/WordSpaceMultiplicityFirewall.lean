/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.EdgeCommutantBasisExact

/-!
# Word-space multiplicity firewall

Covers `cor:word-multiplicity-firewall` of the spacetime–gauge duality paper on the
twelve-root benchmark of `prop:word-space-inflation` (the directed-edge carrier `E` of `K₄`
with the relabeling action of `S₄`, `A = M_12(ℂ)`).

* `conjRep σ : X ↦ P_σ X P_σ⁻¹` is the conjugation representation of `S₄` on the word
  space `L²(M_12)`; its fixed points are exactly the invariant algebra
  `A^{S₄} = commutantSubmodule` (`mem_commutantSubmodule_iff_conjRep_fixed`), of
  dimension `7` (`commutant_finrank_eq_seven`).
* `physRep σ = P_σ` is the physical representation on the exposed carrier `ℂ^E`; its
  fixed points are the constants (`physFixed_eq_span`), of dimension `1`.
* `wordBlock` embeds `End(A^{S₄}) ≅ M_7(ℂ)` injectively and multiplicatively into the
  commutant of the conjugation representation (`wordBlock_injective`, `wordBlock_mul`,
  `wordBlock_commute_conjRep`), via the group average `E_G`.
* `word_space_multiplicity_firewall`: the trivial multiplicity is `7` on the word space but
  `1` on the physical carrier, the word-space commutant contains an `M_7(ℂ)` block, and the
  physical invariant algebra admits no `M_3(ℂ)` (`no_M3_embedding`).
-/

open Matrix RenewalGeometry.ActiveResidual RenewalGeometry.EdgeCommutant
  RenewalGeometry.EdgeCommutantBasis

namespace RenewalGeometry
namespace WordSpaceFirewall

theorem Pm_mul_inv (σ : Equiv.Perm V) : Pm σ * Pm σ⁻¹ = 1 := by
  rw [Pm_mul, mul_inv_cancel, Pm_one]

theorem Pm_inv_mul (σ : Equiv.Perm V) : Pm σ⁻¹ * Pm σ = 1 := by
  rw [Pm_mul, inv_mul_cancel, Pm_one]

/-! ### The conjugation representation on the word space -/

/-- The conjugation representation `U_σ X = P_σ X P_σ⁻¹` of `S₄` on `L²(M_12)`. -/
def conjRep (σ : Equiv.Perm V) : Module.End ℂ (Matrix E E ℂ) where
  toFun X := Pm σ * X * Pm σ⁻¹
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem conjRep_apply (σ : Equiv.Perm V) (X : Matrix E E ℂ) :
    conjRep σ X = Pm σ * X * Pm σ⁻¹ := rfl

theorem conjRep_conjRep (σ τ : Equiv.Perm V) (X : Matrix E E ℂ) :
    conjRep σ (conjRep τ X) = conjRep (σ * τ) X := by
  simp only [conjRep_apply, _root_.mul_inv_rev, ← Pm_mul, Matrix.mul_assoc]

/-- The fixed points of the conjugation representation are the invariant algebra
`A^{S₄}`, i.e. the commutant of the relabeling matrices. -/
theorem mem_commutantSubmodule_iff_conjRep_fixed (X : Matrix E E ℂ) :
    X ∈ commutantSubmodule ↔ ∀ σ, conjRep σ X = X := by
  rw [mem_commutant]
  constructor
  · intro h σ
    rw [conjRep_apply, ← h σ, Matrix.mul_assoc, Pm_mul_inv, Matrix.mul_one]
  · intro h σ
    have hσ := h σ
    rw [conjRep_apply] at hσ
    calc X * Pm σ = Pm σ * X * Pm σ⁻¹ * Pm σ := by rw [hσ]
      _ = Pm σ * X := by rw [Matrix.mul_assoc, Pm_inv_mul, Matrix.mul_one]

/-! ### The physical representation on the exposed carrier -/

/-- The physical representation `P_σ` of `S₄` on the exposed carrier `ℂ^E`. -/
def physRep (σ : Equiv.Perm V) : Module.End ℂ (E → ℂ) :=
  Matrix.mulVecLin (Pm σ)

theorem Pm_mulVec (σ : Equiv.Perm V) (f : E → ℂ) (e : E) :
    (Pm σ *ᵥ f) e = f (act σ⁻¹ e) := by
  simp only [Matrix.mulVec, dotProduct, Pm_apply]
  rw [Finset.sum_eq_single (act σ⁻¹ e)]
  · rw [if_pos, one_mul]
    rw [← act_mul, mul_inv_cancel, act_one]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    rw [h, ← act_mul, inv_mul_cancel, act_one]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem physRep_apply (σ : Equiv.Perm V) (f : E → ℂ) (e : E) :
    physRep σ f e = f (act σ⁻¹ e) := by
  rw [physRep, Matrix.mulVecLin_apply, Pm_mulVec]

set_option maxHeartbeats 4000000 in
/-- `S₄` acts transitively on the directed edges of `K₄`. -/
theorem act_transitive : ∀ e e' : E, ∃ σ : Equiv.Perm V, act σ e = e' := by
  decide

/-- The fixed vectors of the physical representation. -/
def physFixed : Submodule ℂ (E → ℂ) where
  carrier := {f | ∀ σ, physRep σ f = f}
  zero_mem' := fun σ => map_zero _
  add_mem' := fun {f g} hf hg σ => by rw [map_add, hf σ, hg σ]
  smul_mem' := fun c {f} hf σ => by rw [map_smul, hf σ]

theorem mem_physFixed_iff (f : E → ℂ) : f ∈ physFixed ↔ ∀ e e', f e = f e' := by
  constructor
  · intro h e e'
    obtain ⟨σ, hσ⟩ := act_transitive e' e
    have hfix := congrFun (h σ) e
    rw [physRep_apply] at hfix
    rw [← hfix, ← hσ, ← act_mul, inv_mul_cancel, act_one]
  · intro h σ
    funext e
    rw [physRep_apply]
    exact h _ _

/-- The fixed vectors of the physical representation are the constants. -/
theorem physFixed_eq_span : physFixed = Submodule.span ℂ {fun _ : E => (1 : ℂ)} := by
  ext f
  rw [mem_physFixed_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨f e01, ?_⟩
    funext e
    simp [h e e01]
  · rintro ⟨a, rfl⟩ e e'
    simp

/-- The trivial representation has multiplicity `1` on the physical carrier. -/
theorem finrank_physFixed : Module.finrank ℂ physFixed = 1 := by
  rw [physFixed_eq_span]
  apply finrank_span_singleton
  intro h
  have := congrFun h e01
  simp at this

/-! ### The `M_7(ℂ)` block of the word-space commutant -/

/-- The group average `E_G(X) = |S₄|⁻¹ ∑_σ P_σ X P_σ⁻¹`. -/
noncomputable def groupAverage (X : Matrix E E ℂ) : Matrix E E ℂ :=
  (Fintype.card (Equiv.Perm V) : ℂ)⁻¹ • ∑ σ, conjRep σ X

theorem conjRep_groupAverage (τ : Equiv.Perm V) (X : Matrix E E ℂ) :
    conjRep τ (groupAverage X) = groupAverage X := by
  unfold groupAverage
  rw [map_smul, map_sum]
  congr 1
  simp_rw [conjRep_conjRep]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => conjRep σ X)

theorem groupAverage_conjRep (τ : Equiv.Perm V) (X : Matrix E E ℂ) :
    groupAverage (conjRep τ X) = groupAverage X := by
  unfold groupAverage
  congr 1
  simp_rw [conjRep_conjRep]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => conjRep σ X)

theorem groupAverage_mem (X : Matrix E E ℂ) : groupAverage X ∈ commutantSubmodule := by
  rw [mem_commutantSubmodule_iff_conjRep_fixed]
  exact fun τ => conjRep_groupAverage τ X

theorem groupAverage_of_mem {X : Matrix E E ℂ} (hX : X ∈ commutantSubmodule) :
    groupAverage X = X := by
  rw [mem_commutantSubmodule_iff_conjRep_fixed] at hX
  unfold groupAverage
  simp_rw [hX]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- The group average as a linear map onto the invariant algebra. -/
noncomputable def groupAverageLin : Matrix E E ℂ →ₗ[ℂ] commutantSubmodule where
  toFun X := ⟨groupAverage X, groupAverage_mem X⟩
  map_add' X Y := by
    apply Subtype.ext
    simp [groupAverage, Finset.sum_add_distrib, smul_add]
  map_smul' c X := by
    apply Subtype.ext
    simp [groupAverage, Finset.smul_sum, smul_comm c]

theorem groupAverageLin_apply (X : Matrix E E ℂ) :
    (groupAverageLin X : Matrix E E ℂ) = groupAverage X := rfl

theorem groupAverageLin_val (Y : commutantSubmodule) : groupAverageLin (Y : Matrix E E ℂ) = Y :=
  Subtype.ext (groupAverage_of_mem Y.2)

/-- The word-space operator `X ↦ f(E_G X)` attached to an endomorphism `f` of the invariant
algebra `A^{S₄}`. -/
noncomputable def wordBlock (f : Module.End ℂ commutantSubmodule) :
    Module.End ℂ (Matrix E E ℂ) :=
  commutantSubmodule.subtype ∘ₗ f ∘ₗ groupAverageLin

theorem wordBlock_apply (f : Module.End ℂ commutantSubmodule) (X : Matrix E E ℂ) :
    wordBlock f X = (f (groupAverageLin X) : Matrix E E ℂ) := rfl

theorem wordBlock_mul (f g : Module.End ℂ commutantSubmodule) :
    wordBlock (f * g) = wordBlock f * wordBlock g := by
  ext X
  rw [Module.End.mul_apply, wordBlock_apply, wordBlock_apply, wordBlock_apply,
    groupAverageLin_val, Module.End.mul_apply]

theorem wordBlock_add (f g : Module.End ℂ commutantSubmodule) :
    wordBlock (f + g) = wordBlock f + wordBlock g := by
  ext X
  simp [wordBlock_apply]

theorem wordBlock_smul (c : ℂ) (f : Module.End ℂ commutantSubmodule) :
    wordBlock (c • f) = c • wordBlock f := by
  ext X
  simp [wordBlock_apply]

theorem wordBlock_injective : Function.Injective wordBlock := by
  intro f g hfg
  refine LinearMap.ext fun Y => Subtype.ext ?_
  have h := congrArg (fun T : Module.End ℂ (Matrix E E ℂ) => T (Y : Matrix E E ℂ)) hfg
  simp only [wordBlock_apply, groupAverageLin_val] at h
  exact h

/-- The word-space operators `wordBlock f` commute with the conjugation representation. -/
theorem wordBlock_commute_conjRep (f : Module.End ℂ commutantSubmodule) (σ : Equiv.Perm V) :
    wordBlock f * conjRep σ = conjRep σ * wordBlock f := by
  refine LinearMap.ext fun X => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, wordBlock_apply, wordBlock_apply]
  have h1 : groupAverageLin (conjRep σ X) = groupAverageLin X :=
    Subtype.ext (groupAverage_conjRep σ X)
  rw [h1]
  exact ((mem_commutantSubmodule_iff_conjRep_fixed _).mp (f (groupAverageLin X)).2 σ).symm

/-- `wordBlock` as a linear map. -/
noncomputable def wordBlockLin :
    Module.End ℂ commutantSubmodule →ₗ[ℂ] Module.End ℂ (Matrix E E ℂ) where
  toFun := wordBlock
  map_add' := wordBlock_add
  map_smul' := wordBlock_smul

/-- The identification `End(A^{S₄}) ≅ M_7(ℂ)` through a basis of the seven-dimensional
invariant algebra. -/
noncomputable def endEquivM7 :
    Module.End ℂ commutantSubmodule ≃ₐ[ℂ] Matrix (Fin 7) (Fin 7) ℂ :=
  LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq ℂ commutantSubmodule
    commutant_finrank_eq_seven)

/-- The `M_7(ℂ)` word-space block: an injective multiplicative embedding of `M_7(ℂ)` into
the commutant of the conjugation representation. -/
noncomputable def m7Block : Matrix (Fin 7) (Fin 7) ℂ →ₗ[ℂ] Module.End ℂ (Matrix E E ℂ) :=
  wordBlockLin ∘ₗ endEquivM7.symm.toLinearMap

theorem m7Block_injective : Function.Injective m7Block := by
  intro A B h
  have h' : wordBlock (endEquivM7.symm A) = wordBlock (endEquivM7.symm B) := h
  exact endEquivM7.symm.injective (wordBlock_injective h')

theorem m7Block_mul (A B : Matrix (Fin 7) (Fin 7) ℂ) :
    m7Block (A * B) = m7Block A * m7Block B := by
  show wordBlock (endEquivM7.symm (A * B)) = wordBlock (endEquivM7.symm A) * wordBlock (endEquivM7.symm B)
  rw [map_mul, wordBlock_mul]

theorem m7Block_commute_conjRep (A : Matrix (Fin 7) (Fin 7) ℂ) (σ : Equiv.Perm V) :
    m7Block A * conjRep σ = conjRep σ * m7Block A :=
  wordBlock_commute_conjRep _ σ

/-- **Word-space multiplicity firewall (`cor:word-multiplicity-firewall`), on the
twelve-root benchmark.**  The trivial representation of `S₄` has multiplicity `7` in the
conjugation representation on the word space `L²(M_12)` (its fixed points are the invariant
algebra `A^{S₄}`) but multiplicity `1` on the exposed physical carrier `ℂ^E`; the word-space
commutant contains an `M_7(ℂ)` block (an injective multiplicative embedding commuting with
the conjugation representation), while the physical invariant algebra `A^{S₄}` admits no
injective linear image of `M_3(ℂ)`. -/
theorem word_space_multiplicity_firewall :
    (∀ X : Matrix E E ℂ, X ∈ commutantSubmodule ↔ ∀ σ, conjRep σ X = X) ∧
      Module.finrank ℂ commutantSubmodule = 7 ∧
      Module.finrank ℂ physFixed = 1 ∧
      (∃ Φ : Matrix (Fin 7) (Fin 7) ℂ →ₗ[ℂ] Module.End ℂ (Matrix E E ℂ),
        Function.Injective Φ ∧ (∀ A B, Φ (A * B) = Φ A * Φ B) ∧
          ∀ A σ, Φ A * conjRep σ = conjRep σ * Φ A) ∧
      (∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] commutantSubmodule, ¬ Function.Injective f) :=
  ⟨mem_commutantSubmodule_iff_conjRep_fixed, commutant_finrank_eq_seven, finrank_physFixed,
    ⟨m7Block, m7Block_injective, m7Block_mul, m7Block_commute_conjRep⟩, no_M3_embedding⟩

end WordSpaceFirewall
end RenewalGeometry
