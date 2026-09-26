/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementExactTransverseExact

/-!
# Lossless elimination of the transverse source columns
  (`cor:supp-exact-transverse-elimination`, `eq:supp-exact-rank-split`,
  `eq:supp-exact-Gram-split`; emergent-spacetime manuscript)

The corollary is derived from its parent `thm:supp-exact-transverse`
(`Gravity/SupplementExactTransverseExact.lean`, mode representation) in two
steps.

## Abstract elimination for linear maps into an inner product space

For `A : E →ₗ H` and `G : Y →ₗ H` into a finite-dimensional inner product
space `H`, let `Π_A` be the orthogonal projection onto `range A`
(`rangeProj`), `Ḡ = (I − Π_A) G` (`residual`), and, for injective `A`,
`C = A⁻¹ Π_A G` (`elimCoeff`, the paper's `(A^*A)⁻¹ A^* G`) with the
triangular column operation `U (e, y) = (e − C y, y)` (`blockUnit`, a linear
automorphism of `E × Y`).

* `coprod_comp_blockUnit`: `F U = [A Ḡ]` for `F = [A G] = A.coprod G`;
* `range_coprod_residual`: `range [A Ḡ] = range F` (the column operation
  leaves the actual target unchanged);
* `finrank_range_coprod` (**`eq:supp-exact-rank-split`**, abstract form):
  `rank F = rank A + rank Ḡ` (orthogonal column ranges are in direct sum);
* `gram_blockUnit` (**`eq:supp-exact-Gram-split`**, abstract form): for a
  symmetric `K` with `K A = ½ A`,
  `⟪F U x, K F U x'⟫ = ½ ⟪A e, A e'⟫ + ⟪Ḡ y, K Ḡ y'⟫`, i.e.
  `U^* (F^* K F) U = diag(½ A^*A, Ḡ^* K Ḡ)`.

## Instantiation on the transverse source

`toEuc` identifies the mode families `K → Matrix (Fin 3) (Fin 3) ℂ` with the
Euclidean space on `K × Fin 3 × Fin 3`, whose inner product is the summed
Frobenius pairing `∑_k frobInner` (`inner_toEuc`).  `transverseSource` is
`A_h` restricted to `𝒯_h` (`sourceMap.domRestrict (transverseSpace κ)`), and
`signedGramMap` is `K₀⁻¹ = ½ I − ¾ 𝖯_tr` acting mode-wise
(`dewittInvK0`), which is symmetric (`signedGramMap_isSymmetric`) and acts by
`½` on the trace-free range of `A_h` (`signedGramMap_transverseSource`).
With `rank A_h = 2|K|` (`finrank_range_source`) this gives

* `transverse_elimination` (**`cor:supp-exact-transverse-elimination`**):
  for every remaining source block `G_h : Y →ₗ H`,
  `rank F_h = 2|K| + rank Ḡ_h`, `F_h U = [A_h Ḡ_h]` with the same range, and
  `⟪F_h U x, K₀⁻¹ F_h U x'⟫ = ½ ⟪A_h e, A_h e'⟫ + ⟪Ḡ_h y, K₀⁻¹ Ḡ_h y'⟫`.

The only scoping relative to the paper is the one inherited from the parent
theorem: the grid operators are represented by their Fourier modes
(`|K| = V − 1`), so `2|K| = 2(V − 1)`.
-/

namespace RenewalGeometry
namespace ExactTransverse

open Complex Finset ComplexConjugate Module

noncomputable section

/-! ### Abstract elimination -/

section Abstract

variable {E Y H : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup Y] [Module ℂ Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- The orthogonal projection `Π_A` onto `range A`. -/
def rangeProj (A : E →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  ((LinearMap.range A).starProjection : H →L[ℂ] H).toLinearMap

theorem rangeProj_apply_mem (A : E →ₗ[ℂ] H) (v : H) : rangeProj A v ∈ LinearMap.range A :=
  Submodule.starProjection_apply_mem _ v

/-- The residual columns `Ḡ = (I − Π_A) G`. -/
def residual (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) : Y →ₗ[ℂ] H :=
  G - rangeProj A ∘ₗ G

theorem residual_apply (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) (y : Y) :
    residual A G y = G y - rangeProj A (G y) := rfl

/-- `Ḡ y ⟂ range A`. -/
theorem residual_apply_mem_orthogonal (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) (y : Y) :
    residual A G y ∈ (LinearMap.range A)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range A) (G y)

theorem range_residual_le_orthogonal (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) :
    LinearMap.range (residual A G) ≤ (LinearMap.range A)ᗮ := by
  rintro _ ⟨y, rfl⟩
  exact residual_apply_mem_orthogonal A G y

/-- `range A ⊔ range Ḡ = range A ⊔ range G`. -/
theorem range_sup_range_residual (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) :
    LinearMap.range A ⊔ LinearMap.range (residual A G)
      = LinearMap.range A ⊔ LinearMap.range G := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rintro _ ⟨y, rfl⟩
    rw [residual_apply, sub_eq_add_neg]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y, rfl⟩)
      (Submodule.neg_mem _ (Submodule.mem_sup_left (rangeProj_apply_mem A (G y))))
  · refine sup_le le_sup_left ?_
    rintro _ ⟨y, rfl⟩
    have : G y = residual A G y + rangeProj A (G y) := by
      rw [residual_apply, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y, rfl⟩)
      (Submodule.mem_sup_left (rangeProj_apply_mem A (G y)))

/-- The column operation leaves the actual target unchanged:
`range [A Ḡ] = range [A G]`. -/
theorem range_coprod_residual (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) :
    LinearMap.range (A.coprod (residual A G)) = LinearMap.range (A.coprod G) := by
  rw [LinearMap.range_coprod, LinearMap.range_coprod, range_sup_range_residual]

/-- **`eq:supp-exact-rank-split`**, abstract form:
`rank [A G] = rank A + rank Ḡ`. -/
theorem finrank_range_coprod (A : E →ₗ[ℂ] H) (G : Y →ₗ[ℂ] H) :
    finrank ℂ (LinearMap.range (A.coprod G))
      = finrank ℂ (LinearMap.range A) + finrank ℂ (LinearMap.range (residual A G)) := by
  rw [← range_coprod_residual, LinearMap.range_coprod]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A)
    (LinearMap.range (residual A G))
  have hinf : LinearMap.range A ⊓ LinearMap.range (residual A G) = ⊥ := by
    rw [eq_bot_iff, ← (LinearMap.range A).inf_orthogonal_eq_bot]
    exact inf_le_inf_left _ (range_residual_le_orthogonal A G)
  rw [hinf, finrank_bot, add_zero] at h
  exact h

/-- The elimination coefficient `C = A⁻¹ Π_A G` (the paper's `(A^*A)⁻¹ A^* G`),
for injective `A`. -/
def elimCoeff (A : E →ₗ[ℂ] H) (hA : Function.Injective A) (G : Y →ₗ[ℂ] H) : Y →ₗ[ℂ] E :=
  (LinearEquiv.ofInjective A hA).symm.toLinearMap ∘ₗ
    (rangeProj A ∘ₗ G).codRestrict (LinearMap.range A) (fun y => rangeProj_apply_mem A (G y))

/-- `A C = Π_A G`. -/
theorem apply_elimCoeff (A : E →ₗ[ℂ] H) (hA : Function.Injective A) (G : Y →ₗ[ℂ] H) (y : Y) :
    A (elimCoeff A hA G y) = rangeProj A (G y) := by
  unfold elimCoeff
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

/-- The triangular column operation `U (e, y) = (e − C y, y)` as a linear map. -/
def blockUnitMap (C : Y →ₗ[ℂ] E) : E × Y →ₗ[ℂ] E × Y :=
  LinearMap.prod (LinearMap.fst ℂ E Y - C ∘ₗ LinearMap.snd ℂ E Y) (LinearMap.snd ℂ E Y)

theorem blockUnitMap_apply (C : Y →ₗ[ℂ] E) (x : E × Y) :
    blockUnitMap C x = (x.1 - C x.2, x.2) := rfl

/-- The triangular column operation `U = [[I, −C], [0, I]]` as a linear automorphism of
`E × Y` (inverse `[[I, C], [0, I]]`). -/
def blockUnit (C : Y →ₗ[ℂ] E) : (E × Y) ≃ₗ[ℂ] (E × Y) :=
  LinearEquiv.ofLinearMap (blockUnitMap C) (blockUnitMap (-C))
    (by ext x <;> simp [blockUnitMap_apply])
    (by ext x <;> simp [blockUnitMap_apply])

theorem blockUnit_apply (C : Y →ₗ[ℂ] E) (x : E × Y) :
    blockUnit C x = (x.1 - C x.2, x.2) := rfl

/-- `[A G] U = [A Ḡ]`. -/
theorem coprod_comp_blockUnit (A : E →ₗ[ℂ] H) (hA : Function.Injective A) (G : Y →ₗ[ℂ] H) :
    A.coprod G ∘ₗ (blockUnit (elimCoeff A hA G)).toLinearMap = A.coprod (residual A G) := by
  ext x
  · simp [blockUnit_apply]
  · simp [blockUnit_apply, apply_elimCoeff, residual_apply, sub_eq_neg_add]

theorem coprod_blockUnit_apply (A : E →ₗ[ℂ] H) (hA : Function.Injective A) (G : Y →ₗ[ℂ] H)
    (x : E × Y) :
    A.coprod G (blockUnit (elimCoeff A hA G) x) = A x.1 + residual A G x.2 := by
  have := congrArg (fun f => f x) (coprod_comp_blockUnit A hA G)
  simpa using this

/-- **`eq:supp-exact-Gram-split`**, abstract form.  For a symmetric `K` with
`K A = ½ A`, the column operation `U` is a congruence of the signed Gram form:
`⟪F U x, K F U x'⟫ = ½ ⟪A e, A e'⟫ + ⟪Ḡ y, K Ḡ y'⟫`, `x = (e, y)`, `x' = (e', y')`. -/
theorem gram_blockUnit (A : E →ₗ[ℂ] H) (hA : Function.Injective A) (G : Y →ₗ[ℂ] H)
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (hKA : ∀ e, K (A e) = (1 / 2 : ℂ) • A e)
    (x x' : E × Y) :
    ⟪A.coprod G (blockUnit (elimCoeff A hA G) x),
        K (A.coprod G (blockUnit (elimCoeff A hA G) x'))⟫
      = (1 / 2 : ℂ) * ⟪A x.1, A x'.1⟫ + ⟪residual A G x.2, K (residual A G x'.2)⟫ := by
  rw [coprod_blockUnit_apply, coprod_blockUnit_apply, map_add, inner_add_left, inner_add_right,
    inner_add_right, hKA, inner_smul_right]
  have h1 : ⟪A x.1, K (residual A G x'.2)⟫ = 0 := by
    rw [← hK, hKA, inner_smul_left]
    rw [Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self A x.1)
      (residual_apply_mem_orthogonal A G x'.2), mul_zero]
  have h2 : ⟪residual A G x.2, (1 / 2 : ℂ) • A x'.1⟫ = 0 := by
    rw [inner_smul_right, Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self A x'.1)
      (residual_apply_mem_orthogonal A G x.2), mul_zero]
  rw [h1, h2]
  ring

end Abstract

/-! ### Instantiation on the transverse source -/

section Instance

variable {K : Type*} [Fintype K]

/-- Mode families as the Euclidean space on `K × Fin 3 × Fin 3`. -/
def toEuc : (K → Matrix (Fin 3) (Fin 3) ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (K × Fin 3 × Fin 3) where
  toFun M := WithLp.toLp 2 fun p => M p.1 p.2.1 p.2.2
  invFun x := fun k i j => WithLp.ofLp x (k, i, j)
  map_add' M N := rfl
  map_smul' c M := rfl
  left_inv M := rfl
  right_inv x := rfl

theorem toEuc_apply (M : K → Matrix (Fin 3) (Fin 3) ℂ) (p : K × Fin 3 × Fin 3) :
    (toEuc M) p = M p.1 p.2.1 p.2.2 := rfl

theorem toEuc_symm_apply (x : EuclideanSpace ℂ (K × Fin 3 × Fin 3)) (k : K) (i j : Fin 3) :
    toEuc.symm x k i j = x (k, i, j) := rfl

/-- The Euclidean inner product is the summed Frobenius pairing `∑_k ⟨M_k, N_k⟩_F`. -/
theorem inner_toEuc (M N : K → Matrix (Fin 3) (Fin 3) ℂ) :
    @inner ℂ _ _ (toEuc M) (toEuc N) = ∑ k, frobInner (M k) (N k) := by
  change @inner ℂ _ _ (WithLp.toLp 2 fun p : K × Fin 3 × Fin 3 => M p.1 p.2.1 p.2.2)
    (WithLp.toLp 2 fun p : K × Fin 3 × Fin 3 => N p.1 p.2.1 p.2.2) = _
  rw [EuclideanSpace.inner_toLp_toLp]
  unfold frobInner dotProduct
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

/-- The transverse source `A_h` restricted to `𝒯_h`, as a map into the Euclidean space. -/
def transverseSource (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ) :
    transverseSpace κ →ₗ[ℂ] EuclideanSpace ℂ (K × Fin 3 × Fin 3) :=
  toEuc.toLinearMap ∘ₗ (sourceMap h ϰ κ σ).domRestrict (transverseSpace κ)

theorem transverseSource_apply (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ)
    (b : transverseSpace κ) :
    transverseSource h ϰ κ σ b = toEuc (sourceMap h ϰ κ σ b) := rfl

theorem transverseSource_injective (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1) :
    Function.Injective (transverseSource h ϰ κ σ) := by
  unfold transverseSource
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact toEuc.injective.comp (source_injective_on_transverse h ϰ hh hϰ κ hκ σ hσ)

/-- `rank A_h = 2|K|` (`eq:supp-exact-transverse-rank`, transported). -/
theorem finrank_range_transverseSource (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1) :
    finrank ℂ (LinearMap.range (transverseSource h ϰ κ σ)) = 2 * Fintype.card K := by
  unfold transverseSource
  rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq, finrank_range_source h ϰ hh hϰ κ hκ σ hσ]

/-- `K₀⁻¹` acting mode-wise on mode families, as a linear map. -/
def dewittMap : (K → Matrix (Fin 3) (Fin 3) ℂ) →ₗ[ℂ] (K → Matrix (Fin 3) (Fin 3) ℂ) where
  toFun M := fun k => dewittInvK0 (M k)
  map_add' M N := by
    funext k
    simp only [Pi.add_apply, dewittInvK0, traceProj, Matrix.trace_add]
    rw [add_div, add_smul, smul_add, smul_add]
    abel
  map_smul' c M := by
    funext k
    simp only [Pi.smul_apply, dewittInvK0, traceProj, Matrix.trace_smul, RingHom.id_apply,
      smul_eq_mul, smul_sub, smul_smul]
    congr 2
    · ring
    · rw [mul_div_assoc]; ring

theorem dewittMap_apply (M : K → Matrix (Fin 3) (Fin 3) ℂ) (k : K) :
    dewittMap M k = dewittInvK0 (M k) := rfl

/-- `K₀⁻¹` on the Euclidean space. -/
def signedGramMap : EuclideanSpace ℂ (K × Fin 3 × Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (K × Fin 3 × Fin 3) :=
  toEuc.toLinearMap ∘ₗ dewittMap ∘ₗ toEuc.symm.toLinearMap

theorem signedGramMap_toEuc (M : K → Matrix (Fin 3) (Fin 3) ℂ) :
    signedGramMap (toEuc M) = toEuc (dewittMap M) := by
  unfold signedGramMap
  simp

/-- `K₀⁻¹` is symmetric for the Frobenius pairing at one mode. -/
theorem frobInner_dewittInvK0 (S T : Matrix (Fin 3) (Fin 3) ℂ) :
    frobInner (dewittInvK0 S) T = frobInner S (dewittInvK0 T) := by
  simp only [frobInner, dewittInvK0, traceProj, Matrix.trace, Matrix.diag, Fin.sum_univ_three,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.isValue]
  simp only [Fin.isValue, ne_eq, zero_ne_one, one_ne_zero, Fin.reduceEq, not_false_eq_true,
    ite_true, ite_false, mul_one, mul_zero, sub_zero]
  simp only [map_sub, map_mul, map_add, map_div₀, map_one, map_zero, map_ofNat]
  ring

/-- `K₀⁻¹` is symmetric (`signedGramMap` is self-adjoint on the Euclidean space). -/
theorem signedGramMap_isSymmetric : (signedGramMap (K := K)).IsSymmetric := by
  intro x y
  obtain ⟨M, rfl⟩ := toEuc.surjective x
  obtain ⟨N, rfl⟩ := toEuc.surjective y
  rw [signedGramMap_toEuc, signedGramMap_toEuc, inner_toEuc, inner_toEuc]
  exact Finset.sum_congr rfl fun k _ => frobInner_dewittInvK0 _ _

/-- `K₀⁻¹ A_h = ½ A_h` (`eq:supp-exact-transverse-positive`, transported). -/
theorem signedGramMap_transverseSource (h ϰ : ℝ) (κ : K → Fin 3 → ℝ) (σ : K → Fin 3 → ℂ)
    (b : transverseSpace κ) :
    signedGramMap (transverseSource h ϰ κ σ b) = (1 / 2 : ℂ) • transverseSource h ϰ κ σ b := by
  rw [transverseSource_apply, signedGramMap_toEuc, ← map_smul]
  congr 1
  funext k
  rw [dewittMap_apply, Pi.smul_apply]
  exact dewittInvK0_of_trace_zero _ (trace_sourceMode h ϰ (κ k) (σ k) ((b : K → Fin 3 → ℂ) k))

/-- **`cor:supp-exact-transverse-elimination`** (mode representation).
Let `A_h = transverseSource` be the transverse source on `𝒯_h` and `G_h : Y →ₗ H` any
remaining leading source block, `F_h = [A_h G_h]`, `Ḡ_h = (I − Π_{A,h}) G_h`, and
`U = [[I, −C_h], [0, I]]` with `C_h = A_h⁻¹ Π_{A,h} G_h`.  Then

* `rank F_h = 2|K| + rank Ḡ_h` (**`eq:supp-exact-rank-split`**, `2|K| = 2(V−1)`);
* `F_h U = [A_h Ḡ_h]` and `range [A_h Ḡ_h] = range F_h` (the triangular column
  transformation leaves the actual target unchanged);
* `⟪F_h U x, K₀⁻¹ F_h U x'⟫ = ½ ⟪A_h e, A_h e'⟫ + ⟪Ḡ_h y, K₀⁻¹ Ḡ_h y'⟫`
  (**`eq:supp-exact-Gram-split`**, `U^* F_h^* K₀⁻¹ F_h U = diag(½ A_h^*A_h, Ḡ_h^* K₀⁻¹ Ḡ_h)`). -/
theorem transverse_elimination (h ϰ : ℝ) (hh : h ≠ 0) (hϰ : 0 < ϰ)
    (κ : K → Fin 3 → ℝ) (hκ : ∀ k, κ k ≠ 0) (σ : K → Fin 3 → ℂ)
    (hσ : ∀ k i, normSq (σ k i) = 1)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (G : Y →ₗ[ℂ] EuclideanSpace ℂ (K × Fin 3 × Fin 3)) :
    finrank ℂ (LinearMap.range ((transverseSource h ϰ κ σ).coprod G))
        = 2 * Fintype.card K
          + finrank ℂ (LinearMap.range (residual (transverseSource h ϰ κ σ) G)) ∧
    (transverseSource h ϰ κ σ).coprod G ∘ₗ
        (blockUnit (elimCoeff (transverseSource h ϰ κ σ)
          (transverseSource_injective h ϰ hh hϰ κ hκ σ hσ) G)).toLinearMap
      = (transverseSource h ϰ κ σ).coprod (residual (transverseSource h ϰ κ σ) G) ∧
    LinearMap.range ((transverseSource h ϰ κ σ).coprod (residual (transverseSource h ϰ κ σ) G))
      = LinearMap.range ((transverseSource h ϰ κ σ).coprod G) ∧
    ∀ x x' : transverseSpace κ × Y,
      @inner ℂ _ _
        ((transverseSource h ϰ κ σ).coprod G
          (blockUnit (elimCoeff (transverseSource h ϰ κ σ)
            (transverseSource_injective h ϰ hh hϰ κ hκ σ hσ) G) x))
        (signedGramMap ((transverseSource h ϰ κ σ).coprod G
          (blockUnit (elimCoeff (transverseSource h ϰ κ σ)
            (transverseSource_injective h ϰ hh hϰ κ hκ σ hσ) G) x')))
      = (1 / 2 : ℂ) * @inner ℂ _ _ (transverseSource h ϰ κ σ x.1)
            (transverseSource h ϰ κ σ x'.1)
        + @inner ℂ _ _ (residual (transverseSource h ϰ κ σ) G x.2)
            (signedGramMap (residual (transverseSource h ϰ κ σ) G x'.2)) := by
  refine ⟨?_, coprod_comp_blockUnit _ _ G, range_coprod_residual _ G, fun x x' => ?_⟩
  · rw [finrank_range_coprod, finrank_range_transverseSource h ϰ hh hϰ κ hκ σ hσ]
  · exact gram_blockUnit _ _ G signedGramMap signedGramMap_isSymmetric
      (signedGramMap_transverseSource h ϰ κ σ) x x'

end Instance

end

end ExactTransverse
end RenewalGeometry
