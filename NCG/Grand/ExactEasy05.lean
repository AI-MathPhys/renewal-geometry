/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RegularTrace
import Mathlib.LinearAlgebra.Trace

/-!
# Exact EASY batch 05: intrinsic regular trace

This file supplies the coordinate-free normalization and isomorphism
invariance clauses omitted by the original Wedderburn-coordinate proof.
-/

namespace NCG

/-- The intrinsic regular trace: the ordinary linear trace of left
multiplication.  No commutativity of the algebra is assumed. -/
noncomputable def regularTraceIntrinsic (A : Type*) [Ring A] [Algebra ℂ A] :
    A →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ A).comp (Algebra.lmul ℂ A).toLinearMap

theorem regularTraceIntrinsic_apply (A : Type*) [Ring A] [Algebra ℂ A]
    (a : A) :
    regularTraceIntrinsic A a =
      LinearMap.trace ℂ A (Algebra.lmul ℂ A a) := rfl

/-- Cyclicity of the intrinsic regular trace. -/
theorem regularTraceIntrinsic_mul_comm (A : Type*) [Ring A] [Algebra ℂ A]
    [Module.Free ℂ A] [Module.Finite ℂ A] (a b : A) :
    regularTraceIntrinsic A (a * b) = regularTraceIntrinsic A (b * a) := by
  rw [regularTraceIntrinsic_apply, regularTraceIntrinsic_apply]
  have hab : Algebra.lmul ℂ A (a * b) =
      (Algebra.lmul ℂ A a).comp (Algebra.lmul ℂ A b) := by
    ext x
    simp [mul_assoc]
  have hba : Algebra.lmul ℂ A (b * a) =
      (Algebra.lmul ℂ A b).comp (Algebra.lmul ℂ A a) := by
    ext x
    simp [mul_assoc]
  rw [hab, hba]
  exact LinearMap.trace_comp_comm' (R := ℂ)
    (Algebra.lmul ℂ A b) (Algebra.lmul ℂ A a)

/-- The regular trace of the unit is the complex dimension. -/
theorem regularTraceIntrinsic_one (A : Type*) [Ring A] [Algebra ℂ A]
    [Module.Free ℂ A] [Module.Finite ℂ A] :
    regularTraceIntrinsic A 1 = Module.finrank ℂ A := by
  rw [regularTraceIntrinsic_apply]
  have hone : Algebra.lmul ℂ A 1 = LinearMap.id := by
    ext x
    simp
  rw [hone, LinearMap.trace_id]

/-- Algebra isomorphisms conjugate left multiplication and therefore
preserve the intrinsic regular trace.  This applies in particular to
every star-algebra isomorphism. -/
theorem regularTraceIntrinsic_algEquiv {A B : Type*}
    [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    [Module.Free ℂ A] [Module.Finite ℂ A]
    [Module.Free ℂ B] [Module.Finite ℂ B]
    (e : A ≃ₐ[ℂ] B) (a : A) :
    regularTraceIntrinsic B (e a) = regularTraceIntrinsic A a := by
  rw [regularTraceIntrinsic_apply, regularTraceIntrinsic_apply,
    ← LinearMap.trace_conj' (Algebra.lmul ℂ A a) e.toLinearEquiv]
  congr 1
  ext b
  simp [LinearEquiv.conj_apply]

/-- The normalized intrinsic regular trace. -/
noncomputable def normalizedRegularTrace (A : Type*) [Ring A] [Algebra ℂ A] :
    A →ₗ[ℂ] ℂ :=
  (Module.finrank ℂ A : ℂ)⁻¹ • regularTraceIntrinsic A

/-- Normalization at the unit, for every nonzero finite-dimensional
algebra. -/
theorem normalizedRegularTrace_one (A : Type*) [Ring A] [Algebra ℂ A]
    [Module.Free ℂ A] [Module.Finite ℂ A]
    (hfin : Module.finrank ℂ A ≠ 0) :
    normalizedRegularTrace A 1 = 1 := by
  simp only [normalizedRegularTrace, LinearMap.smul_apply,
    smul_eq_mul, regularTraceIntrinsic_one]
  have hcast : (Module.finrank ℂ A : ℂ) ≠ 0 := by exact_mod_cast hfin
  exact inv_mul_cancel₀ hcast

/-- Normalized regular trace is preserved by algebra isomorphisms. -/
theorem normalizedRegularTrace_algEquiv {A B : Type*}
    [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    [Module.Free ℂ A] [Module.Finite ℂ A]
    [Module.Free ℂ B] [Module.Finite ℂ B]
    (e : A ≃ₐ[ℂ] B) (a : A) :
    normalizedRegularTrace B (e a) = normalizedRegularTrace A a := by
  have hdim : Module.finrank ℂ B = Module.finrank ℂ A :=
    (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  simp only [normalizedRegularTrace, LinearMap.smul_apply, smul_eq_mul,
    regularTraceIntrinsic_algEquiv e a, hdim]

/-- `thm:regular-trace`: the existing Wedderburn-coordinate
traciality/faithfulness/dimension theorem together with the intrinsic
normalization and isomorphism-invariance clauses. -/
theorem regular_trace_exact {L : Type*} [Fintype L] [Nonempty L] (nd : L → ℕ)
    (hpos : ∀ l, 0 < nd l) :
    ((∀ a b : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
        ∑ l, (nd l : ℂ) * (a l * b l).trace
          = ∑ l, (nd l : ℂ) * (b l * a l).trace)
      ∧ (∀ a : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
          ∑ l, (nd l : ℂ) * (star (a l) * a l).trace = 0 → a = 0)
      ∧ Module.finrank ℂ
          (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ)
        = ∑ l, nd l ^ 2)
    ∧ normalizedRegularTrace
        (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) 1 = 1
    ∧ (∀ {B : Type*} [Ring B] [Algebra ℂ B]
        [Module.Free ℂ B] [Module.Finite ℂ B]
        (e : (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) ≃ₐ[ℂ] B)
        (a : ∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ),
        normalizedRegularTrace B (e a) =
          normalizedRegularTrace
            (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) a) := by
  have hbase := regular_trace nd
  refine ⟨⟨hbase.1, ?_, hbase.2.2⟩, ?_, ?_⟩
  · intro a ha
    exact hbase.2.1 a ha hpos
  · apply normalizedRegularTrace_one
    classical
    let l₀ : L := Classical.choice (inferInstance : Nonempty L)
    let i₀ : Fin (nd l₀) := ⟨0, hpos l₀⟩
    have hne : (0 : ∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) ≠ 1 := by
      intro h
      have hentry := congrFun (congrFun (congrFun h l₀) i₀) i₀
      simpa using hentry
    letI : Nontrivial (∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ) :=
      ⟨0, 1, hne⟩
    exact (Module.finrank_pos (R := ℂ)
      (M := ∀ l, Matrix (Fin (nd l)) (Fin (nd l)) ℂ)).ne'
  · intro B _ _ _ _ e a
    exact normalizedRegularTrace_algEquiv e a

end NCG
