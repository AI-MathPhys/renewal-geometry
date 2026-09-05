/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The selective scalar block splitting
  (`thm:selective-scalar-block`, SM_emergence)

The left–right matrix space factorises as
`Hom(ℂ²_R, ℂ²_L) ⊗ End(ℂ⁴)`, and the `SU(4)` content of the second
factor is the multiplicity-one splitting `End(ℂ⁴) = 𝟏 ⊕ 𝟏𝟓`:

* `traceless` — the adjoint (`𝟏𝟓`) as the trace kernel;
* `scalar_traceless_compl` — `End(ℂ⁴) = ℂ·1 ⊕ traceless` is an
  exact direct-sum decomposition (`IsCompl`): every `M` splits
  uniquely as `(tr M/4)·1 + (M - (tr M/4)·1)`;
* `finrank_traceless` — the dimension count `16 = 1 + 15`.

Hence `D_LR ⇝ (2,2,1) ⊕ (2,2,15)` with multiplicity one, and the
choice `D_LR ≠ 0`, `D_{RRᶜ} = D_{LLᶜ} = 0` produces one primitive
`(2,2,1)` and one primitive `(2,2,15)` and no decuplet or sextet —
the same-chirality blocks are independent entries of the finite
Dirac operator (the equivariance of the splitting under `SU(4)`
conjugation is the disclosed representation-theory layer).
-/

namespace NCG

open Matrix

/-- The adjoint (`𝟏𝟓`) summand: traceless `4 × 4` matrices. -/
def traceless : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 4) ℂ ℂ)

/-- The scalar (`𝟏`) summand. -/
def scalarLine : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Submodule.span ℂ {(1 : Matrix (Fin 4) (Fin 4) ℂ)}

/-- `thm:selective-scalar-block` (splitting): `End(ℂ⁴) = 𝟏 ⊕ 𝟏𝟓`
exactly — the scalar line and the traceless hyperplane are
complementary. -/
theorem scalar_traceless_compl : IsCompl scalarLine traceless := by
  constructor
  · -- disjoint
    rw [Submodule.disjoint_def]
    intro M hM1 hM2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hM1
    have htr : Matrix.trace (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) = 0 :=
      hM2
    rw [Matrix.trace_smul, Matrix.trace_one] at htr
    simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at htr
    have hc : c = 0 :=
      (mul_eq_zero.mp htr).resolve_right (by norm_num)
    rw [hc, zero_smul]
  · -- codisjoint: every M = (tr M/4)•1 + traceless
    rw [codisjoint_iff, eq_top_iff]
    intro M _
    have hsplit : M = (Matrix.trace M / 4) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ)
        + (M - (Matrix.trace M / 4) • 1) := by module
    rw [hsplit]
    apply Submodule.add_mem_sup
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · change Matrix.trace (M - (Matrix.trace M / 4) • 1) = 0
      rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
      simp only [Fintype.card_fin, smul_eq_mul]
      ring

/-- The dimension count `16 = 1 + 15`. -/
theorem finrank_traceless :
    Module.finrank ℂ traceless = 15 ∧
      Module.finrank ℂ scalarLine = 1 ∧
      Module.finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ) = 16 := by
  have hfull : Module.finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ) = 16 := by
    rw [Module.finrank_matrix]
    simp
  have hline : Module.finrank ℂ scalarLine = 1 := by
    rw [scalarLine, finrank_span_singleton]
    exact one_ne_zero
  have hsum : Module.finrank ℂ scalarLine
      + Module.finrank ℂ traceless = 16 := by
    rw [← hfull]
    exact (Submodule.finrank_add_eq_of_isCompl
      scalar_traceless_compl)
  exact ⟨by omega, hline, hfull⟩

end NCG
