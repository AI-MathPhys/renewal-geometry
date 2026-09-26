/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ActiveResidualAlgebra
import RenewalGeometry.StandardModel.GeometryShortQuotientExact
import RenewalGeometry.Commutant.DegreeOneColourNoGoExact

/-!
# The `S₄ × ⟨ι⟩` census of the categorical residual, by characters

Completes the representation-theoretic clauses of `thm:geometry-short`
(`eq:residual-S4` and the rank-three endpoint survival) and the multiplicity censuses
of `thm:active-isotypic` (`(1,2,1,1)` on the degree-one carrier, `(2,2,1,1)` with one
private line) of the spacetime–gauge duality paper, on the ordered-root carrier `E`
of `ActiveResidualAlgebra`.

The five irreducible characters of `S₄` are named by their standard permutation
models: `1`; the standard representation `W` (`χ_W = fix − 1`, the four vertices);
`V₂` (`χ_{V₂} = fixMatch − 1`, the three perfect matchings of `K₄`); `W ⊗ sgn`
(`χ = sgn · (fix − 1)`); and `sgn`.  A finite-dimensional representation is
determined by its character, so the identification of a block with a named
irreducible is the identity of characters.

* `block_char_*`: for every `σ ∈ S₄`, `Tr(P_σ Q) = χ_λ(σ)` for the five census
  projectors `Q ∈ {Qtype, QW2, QC, QG, QP}` with `λ = 1, V₂, W, W, W ⊗ sgn`, and
  `Rm Q = ±Q` (`+` on the first three, `−` on the last two): this is
  **`eq:residual-S4`**, `E ⊗ ℂ ≅ ℂ⁺_type ⊕ W₊ ⊕ (V₂)₊ ⊕ W₋ ⊕ (W ⊗ sgn)₋`
  (`residual_S4_census`), the blocks being irreducible (every corner `Q X Q` lies
  in the represented algebra, `ActiveResidualAlgebra.*_corner_mem`) and pairwise
  inequivalent (`blockChar_injective`).
* `rank_eq_trace_of_idempotent`, `QG_rank`, …: the complex ranks `1, 2, 3, 3, 3`.
* `endpoint_block_survives`: if a Gram form is strictly positive on the nonzero
  vectors of the endpoint block `Ran QG = W₋`, that block meets `Ker G` trivially and
  injects into the source-minimal quotient `E / Ker G` with complex rank **three**.
* `degree_one_multiplicity_census`: `χ_E = 1 + 2 χ_W + χ_{V₂} + χ_{W⊗sgn}`, the
  `(1, 2, 1, 1)` census `𝒱_cat ≅ ℂ ⊕ (W ⊗ ℂ²) ⊕ V₂ ⊕ W^sgn` of `thm:active-isotypic`;
  `private_line_multiplicity_census`: `(2, 2, 1, 1)` on `E ⊕ ℂ`.

All integer identities are kernel-checked by `decide` over `ℤ` and transported to `ℂ`.
-/

open Matrix Module RenewalGeometry.ActiveResidual
open scoped ComplexOrder

namespace RenewalGeometry
namespace ActiveResidualCensus

/-! ### Integer permutation matrices and the named characters -/

/-- The integer permutation matrix of a relabeling. -/
def PZ (σ : Equiv.Perm V) : Matrix E E ℤ := fun e f => if e = act σ f then 1 else 0

theorem Pm_eq_cz (σ : Equiv.Perm V) : Pm σ = cz (PZ σ) := by
  ext e f
  simp [Pm, PZ, cz, Matrix.map_apply, apply_ite (Int.cast : ℤ → ℂ)]

/-- Number of fixed vertices of `σ`. -/
def fixPts (σ : Equiv.Perm V) : ℤ := (Finset.univ.filter (fun x => σ x = x)).card

/-- The three perfect matchings of `K₄`, as fixed-point-free involutions. -/
def matching : Fin 3 → Equiv.Perm V :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

/-- Number of perfect matchings fixed by `σ` (conjugation action). -/
def fixMatch (σ : Equiv.Perm V) : ℤ :=
  (Finset.univ.filter (fun m : Fin 3 => σ * matching m * σ⁻¹ = matching m)).card

/-- `χ_W = fix − 1`: the standard three-dimensional irreducible of `S₄`. -/
def chiW (σ : Equiv.Perm V) : ℤ := fixPts σ - 1

/-- `χ_{V₂} = fixMatch − 1`: the two-dimensional irreducible of `S₄`. -/
def chiV2 (σ : Equiv.Perm V) : ℤ := fixMatch σ - 1

/-- `χ_{W ⊗ sgn} = sgn · (fix − 1)`. -/
def chiWsgn (σ : Equiv.Perm V) : ℤ := (Equiv.Perm.sign σ : ℤ) * (fixPts σ - 1)

set_option maxHeartbeats 4000000 in
theorem traceZ1 : ∀ σ : Equiv.Perm V, (PZ σ * Z1).trace = 24 := by decide

set_option maxHeartbeats 4000000 in
theorem traceZ2 : ∀ σ : Equiv.Perm V, (PZ σ * Z2).trace = 24 * chiV2 σ := by decide

set_option maxHeartbeats 4000000 in
theorem traceZ3 : ∀ σ : Equiv.Perm V, (PZ σ * Z3).trace = 24 * chiW σ := by decide

set_option maxHeartbeats 4000000 in
theorem traceZ4 : ∀ σ : Equiv.Perm V, (PZ σ * Z4).trace = 24 * chiW σ := by decide

set_option maxHeartbeats 4000000 in
theorem traceZ5 : ∀ σ : Equiv.Perm V, (PZ σ * Z5).trace = 24 * chiWsgn σ := by decide

set_option maxHeartbeats 4000000 in
theorem tracePZ : ∀ σ : Equiv.Perm V,
    (PZ σ).trace = 1 + 2 * chiW σ + chiV2 σ + chiWsgn σ := by decide

/-- Transport of an integer trace identity to the complex census projector. -/
theorem trace_Pm_smul_cz (σ : Equiv.Perm V) (Z : Matrix E E ℤ) (c : ℤ)
    (h : (PZ σ * Z).trace = 24 * c) :
    (Pm σ * ((24 : ℂ)⁻¹ • cz Z)).trace = (c : ℂ) := by
  rw [Pm_eq_cz, mul_smul_comm, Matrix.trace_smul, ← cz_mul, cz_trace, h, smul_eq_mul]
  push_cast
  ring

/-! ### The characters of the five blocks -/

theorem block_char_type (σ : Equiv.Perm V) : (Pm σ * Qtype).trace = 1 := by
  have := trace_Pm_smul_cz σ Z1 1 (by rw [traceZ1]; ring)
  simpa [Qtype] using this

theorem block_char_W2 (σ : Equiv.Perm V) : (Pm σ * QW2).trace = (chiV2 σ : ℂ) :=
  trace_Pm_smul_cz σ Z2 _ (traceZ2 σ)

theorem block_char_C (σ : Equiv.Perm V) : (Pm σ * QC).trace = (chiW σ : ℂ) :=
  trace_Pm_smul_cz σ Z3 _ (traceZ3 σ)

theorem block_char_G (σ : Equiv.Perm V) : (Pm σ * QG).trace = (chiW σ : ℂ) :=
  trace_Pm_smul_cz σ Z4 _ (traceZ4 σ)

theorem block_char_P (σ : Equiv.Perm V) : (Pm σ * QP).trace = (chiWsgn σ : ℂ) :=
  trace_Pm_smul_cz σ Z5 _ (traceZ5 σ)

/-- **The `(1, 2, 1, 1)` degree-one census of `thm:active-isotypic`**, at the level of
characters: `χ_{𝒱_cat} = χ_1 + 2 χ_W + χ_{V₂} + χ_{W ⊗ sgn}`, i.e.
`𝒱_cat ≅ ℂ_type ⊕ (W ⊗ ℂ²) ⊕ V₂ ⊕ W^sgn`. -/
theorem degree_one_multiplicity_census (σ : Equiv.Perm V) :
    (Pm σ).trace = 1 + 2 * (chiW σ : ℂ) + (chiV2 σ : ℂ) + (chiWsgn σ : ℂ) := by
  rw [Pm_eq_cz, cz_trace, tracePZ]
  push_cast
  ring

/-- **The `(2, 2, 1, 1)` census with one external-trivial private line**:
`χ_{E ⊕ ℂ} = 2 χ_1 + 2 χ_W + χ_{V₂} + χ_{W ⊗ sgn}`. -/
theorem trace_fromBlocks {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m m ℂ)
    (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem private_line_multiplicity_census (σ : Equiv.Perm V) :
    (DegreeOneColourNoGo.PmPlus σ).trace =
      2 * 1 + 2 * (chiW σ : ℂ) + (chiV2 σ : ℂ) + (chiWsgn σ : ℂ) := by
  rw [DegreeOneColourNoGo.PmPlus, trace_fromBlocks, degree_one_multiplicity_census,
    Matrix.trace_one, Fintype.card_unit]
  push_cast
  ring

/-! ### The reversal signs -/

theorem Rm_Qtype : Rm * Qtype = Qtype := by
  have := (cz_eigen (β := 1) (by rw [hRZ1, one_smul]) (by rw [hZ1R, one_smul]) Rm_eq_cz).1
  simpa [Qtype] using this

theorem Rm_QW2 : Rm * QW2 = QW2 := by
  have := (cz_eigen (β := 1) (by rw [hRZ2, one_smul]) (by rw [hZ2R, one_smul]) Rm_eq_cz).1
  simpa [QW2] using this

theorem Rm_QC : Rm * QC = QC := by
  have := (cz_eigen (β := 1) (by rw [hRZ3, one_smul]) (by rw [hZ3R, one_smul]) Rm_eq_cz).1
  simpa [QC] using this

theorem Rm_QG : Rm * QG = -QG := by
  have := (cz_eigen (β := -1) (by rw [hRZ4, neg_smul, one_smul])
    (by rw [hZ4R, neg_smul, one_smul]) Rm_eq_cz).1
  simpa [QG] using this

theorem Rm_QP : Rm * QP = -QP := by
  have := (cz_eigen (β := -1) (by rw [hRZ5, neg_smul, one_smul])
    (by rw [hZ5R, neg_smul, one_smul]) Rm_eq_cz).1
  simpa [QP] using this

/-! ### `eq:residual-S4` -/

/-- **`eq:residual-S4`**: the five orthogonal census projectors of the categorical
residual carry, for every `σ ∈ S₄` and for the reversal `ι`, the characters of
`ℂ⁺_type`, `(V₂)₊`, `W₊`, `W₋` and `(W ⊗ sgn)₋` respectively; they sum to one and each
block is irreducible for the represented `S₄ × ⟨ι⟩` algebra `AR` (every corner
`Q X Q` lies in `AR`). -/
theorem residual_S4_census :
    (∀ σ : Equiv.Perm V,
      (Pm σ * Qtype).trace = 1 ∧ (Pm σ * QW2).trace = (chiV2 σ : ℂ) ∧
      (Pm σ * QC).trace = (chiW σ : ℂ) ∧ (Pm σ * QG).trace = (chiW σ : ℂ) ∧
      (Pm σ * QP).trace = (chiWsgn σ : ℂ)) ∧
    (Rm * Qtype = Qtype ∧ Rm * QW2 = QW2 ∧ Rm * QC = QC ∧ Rm * QG = -QG ∧ Rm * QP = -QP) ∧
    Qtype + QW2 + QC + QG + QP = 1 ∧
    (∀ X : Matrix E E ℂ, Qtype * X * Qtype ∈ AR ∧ QW2 * X * QW2 ∈ AR ∧ QC * X * QC ∈ AR ∧
      QG * X * QG ∈ AR ∧ QP * X * QP ∈ AR) :=
  ⟨fun σ => ⟨block_char_type σ, block_char_W2 σ, block_char_C σ, block_char_G σ,
      block_char_P σ⟩,
    ⟨Rm_Qtype, Rm_QW2, Rm_QC, Rm_QG, Rm_QP⟩, Qsum,
    fun X => ⟨Qtype_corner_mem X, QW2_corner_mem X, QC_corner_mem X, QG_corner_mem X,
      QP_corner_mem X⟩⟩

/-- The five census projectors, indexed. -/
noncomputable def blockProj : Fin 5 → Matrix E E ℂ := ![Qtype, QW2, QC, QG, QP]

/-- The `S₄ × ⟨ι⟩` character of the `i`-th block: `(σ, ε) ↦ Tr(P_σ ι^ε Q_i)`. -/
noncomputable def blockChar (i : Fin 5) (σ : Equiv.Perm V) (ε : Bool) : ℂ :=
  (Pm σ * (if ε then Rm else 1) * blockProj i).trace

theorem chiW_sPerm : chiW sPerm = 1 := by decide
theorem chiV2_sPerm : chiV2 sPerm = 0 := by decide
theorem chiWsgn_sPerm : chiWsgn sPerm = -1 := by decide

/-- **Pairwise inequivalence** of the five blocks: their `S₄ × ⟨ι⟩` characters are
pairwise distinct (distinguished by dimension, reversal sign and the value at a
transposition). -/
theorem blockChar_injective : Function.Injective blockChar := by
  intro i j hij
  have h1 := congrFun (congrFun hij 1) false
  have h2 := congrFun (congrFun hij 1) true
  have h3 := congrFun (congrFun hij sPerm) false
  simp only [blockChar, Pm_one, Matrix.one_mul, Matrix.mul_one, Bool.false_eq_true, ↓reduceIte]
    at h1 h2 h3
  fin_cases i <;> fin_cases j <;>
    simp [blockProj, Rm_Qtype, Rm_QW2, Rm_QC, Rm_QG, Rm_QP, Qtype_trace, QW2_trace, QC_trace,
      QG_trace, QP_trace, block_char_type, block_char_W2, block_char_C, block_char_G,
      block_char_P, chiW_sPerm, chiV2_sPerm, chiWsgn_sPerm] at h1 h2 h3 ⊢ <;>
    first | done | (exfalso; revert h2; norm_num; done) | (exfalso; revert h3; norm_num; done)

/-! ### Ranks -/

/-- The rank of an idempotent complex matrix is its trace. -/
theorem rank_eq_trace_of_idempotent {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q * Q = Q) : (Q.rank : ℂ) = Q.trace := by
  have hidem : IsIdempotentElem Q.toLin' := by
    change Q.toLin' * Q.toLin' = Q.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hidem)
  rw [Matrix.trace_toLin'_eq] at h
  rw [h]
  rfl

theorem Qtype_rank : Qtype.rank = 1 := by
  have := rank_eq_trace_of_idempotent Qtype Qtype_idem
  rw [Qtype_trace] at this
  exact_mod_cast this

theorem QW2_rank : QW2.rank = 2 := by
  have := rank_eq_trace_of_idempotent QW2 QW2_idem
  rw [QW2_trace] at this
  exact_mod_cast this

theorem QC_rank : QC.rank = 3 := by
  have := rank_eq_trace_of_idempotent QC QC_idem
  rw [QC_trace] at this
  exact_mod_cast this

/-- The endpoint block `W₋ = Ran QG` has complex rank three. -/
theorem QG_rank : QG.rank = 3 := by
  have := rank_eq_trace_of_idempotent QG QG_idem
  rw [QG_trace] at this
  exact_mod_cast this

theorem QP_rank : QP.rank = 3 := by
  have := rank_eq_trace_of_idempotent QP QP_idem
  rw [QP_trace] at this
  exact_mod_cast this

/-! ### Endpoint survival at rank three -/

/-- `GeometryShortQuotient.block_survives` for an arbitrary finite index type. -/
theorem block_survives {ι : Type*} [Fintype ι] [DecidableEq ι] (G Q : Matrix ι ι ℂ)
    (hQ : Q * Q = Q)
    (hpos : ∀ v : ι → ℂ, Q *ᵥ v = v → v ≠ 0 → star v ⬝ᵥ (G *ᵥ v) ≠ 0) :
    LinearMap.range Q.mulVecLin ⊓ LinearMap.ker G.mulVecLin = ⊥ ∧
    finrank ℂ ((LinearMap.range Q.mulVecLin).map (LinearMap.ker G.mulVecLin).mkQ)
      = Q.rank := by
  have hdisj : LinearMap.range Q.mulVecLin ⊓ LinearMap.ker G.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_range, LinearMap.mem_ker] at hv
    obtain ⟨⟨w, hw⟩, hG⟩ := hv
    rw [Matrix.mulVecLin_apply] at hw hG
    rw [Submodule.mem_bot]
    by_contra hne
    apply hpos v _ hne
    · rw [hG, dotProduct_zero]
    · rw [← hw, Matrix.mulVec_mulVec, hQ]
  refine ⟨hdisj, ?_⟩
  set p := LinearMap.range Q.mulVecLin
  set K := LinearMap.ker G.mulVecLin
  have h1 := LinearMap.finrank_range_add_finrank_ker (K.mkQ.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  have hcomap : K.comap p.subtype = ⊥ := by
    rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]
    exact hdisj
  rw [hcomap, finrank_bot, add_zero] at h1
  rw [h1]
  rfl

/-- **Endpoint survival (`thm:geometry-short`, last clause)**: if the (shorted) Gram
form `G` is strictly positive on the nonzero vectors of the endpoint block
`W₋ = Ran QG`, then `Ran QG ∩ Ker G = 0` and the block injects into the source-minimal
quotient `E / Ker G` with complex rank **three**. -/
theorem endpoint_block_survives (G : Matrix E E ℂ)
    (hpos : ∀ v : E → ℂ, QG *ᵥ v = v → v ≠ 0 → 0 < star v ⬝ᵥ (G *ᵥ v)) :
    LinearMap.range QG.mulVecLin ⊓ LinearMap.ker G.mulVecLin = ⊥ ∧
    finrank ℂ ((LinearMap.range QG.mulVecLin).map (LinearMap.ker G.mulVecLin).mkQ) = 3 := by
  have h := block_survives G QG QG_idem fun v hv hne => (hpos v hv hne).ne'
  rw [QG_rank] at h
  exact h

end ActiveResidualCensus
end RenewalGeometry
