/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Algebra.Algebra.Pi

/-!
# Protected Palatini--Cartan--Holst graph writer

This module formalizes the exact finite record-theoretic content of
`thm:SMST-PCH-graph-writer`.  Once the finite PCH bulk-plus-boundary functional
is a deterministic real-analytic function of the protected tuple on the chosen
logarithm branch, adjoining its graph coordinate is injective, has the old
tuple projection as a two-sided inverse, preserves every finite marginal and
payload, and induces a canonical equivalence of the full finite record
algebras.  The analytic graph-map statement is included explicitly.
-/

open scoped BigOperators

namespace NCG

/-- The graph record of a deterministic writer `g`. -/
def ProtectedGraphRecord {Θ R : Type*} (g : Θ → R) :=
  {z : Θ × R // z.2 = g z.1}

/-- Append the deterministic graph coordinate. -/
def protectedGraphWriter {Θ R : Type*} (g : Θ → R) (θ : Θ) :
    ProtectedGraphRecord g :=
  ⟨(θ, g θ), rfl⟩

/-- Discard the appended coordinate. -/
def protectedGraphDiscard {Θ R : Type*} {g : Θ → R}
    (z : ProtectedGraphRecord g) : Θ :=
  z.1.1

@[simp]
theorem protectedGraphDiscard_writer {Θ R : Type*} (g : Θ → R) (θ : Θ) :
    protectedGraphDiscard (protectedGraphWriter g θ) = θ := rfl

@[simp]
theorem protectedGraphWriter_discard {Θ R : Type*} (g : Θ → R)
    (z : ProtectedGraphRecord g) :
    protectedGraphWriter g (protectedGraphDiscard z) = z := by
  rcases z with ⟨⟨θ, r⟩, hr⟩
  apply Subtype.ext
  change (θ, g θ) = (θ, r)
  congr
  exact hr.symm

/-- The old protected record and its graph extension are canonically
equivalent. -/
def protectedGraphEquiv {Θ R : Type*} (g : Θ → R) :
    Θ ≃ ProtectedGraphRecord g where
  toFun := protectedGraphWriter g
  invFun := protectedGraphDiscard
  left_inv := protectedGraphDiscard_writer g
  right_inv := protectedGraphWriter_discard g

/-- The graph writer is injective, so it neither identifies nor loses old
records. -/
theorem protectedGraphWriter_injective {Θ R : Type*} (g : Θ → R) :
    Function.Injective (protectedGraphWriter g) :=
  (protectedGraphEquiv g).injective

/-- Every old payload is recovered exactly by discarding the graph
coordinate. -/
theorem protectedGraph_payload_recovery {Θ R β : Type*}
    (g : Θ → R) (f : Θ → β) (θ : Θ) :
    f (protectedGraphDiscard (protectedGraphWriter g θ)) = f θ := rfl

/-- Exact conservation of finite total mass (and hence of normalized
probabilities) under the deterministic graph writer. -/
theorem protectedGraph_sum_conservation {Θ R A : Type*}
    [Fintype Θ] [AddCommMonoid A] (g : Θ → R) (w : Θ → A) :
    letI := Fintype.ofEquiv Θ (protectedGraphEquiv g)
    ∑ z : ProtectedGraphRecord g, w (protectedGraphDiscard z) = ∑ θ : Θ, w θ := by
  letI := Fintype.ofEquiv Θ (protectedGraphEquiv g)
  change ∑ z, w ((protectedGraphEquiv g).symm z) = ∑ θ, w θ
  exact (protectedGraphEquiv g).symm.sum_comp w

/-- The full finite record-function algebras before and after adjoining the
graph coordinate are canonically isomorphic. -/
noncomputable def protectedGraphRecordAlgEquiv
    {Θ R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (g : Θ → A) : (Θ → A) ≃ₐ[R] (ProtectedGraphRecord g → A) :=
  AlgEquiv.piCongrLeft R (fun _ : ProtectedGraphRecord g => A)
    (protectedGraphEquiv g)

@[simp]
theorem protectedGraphRecordAlgEquiv_apply
    {Θ R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (g : Θ → A) (f : Θ → A) (θ : Θ) :
    protectedGraphRecordAlgEquiv (R := R) g f (protectedGraphWriter g θ) = f θ := by
  rfl

/-- A real-analytic deterministic functional has a real-analytic graph map. -/
theorem protectedGraphWriter_analytic
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (g : Θ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ) :
    AnalyticOnNhd ℝ (fun θ => (θ, g θ)) Set.univ :=
  analyticOnNhd_id.prod hg

/-- `thm:SMST-PCH-graph-writer`: complete finite conservative-writer packet.

Here `gPCH` is the already assembled finite PCH bulk-plus-boundary expression
on its nondegenerate logarithm branch.  Its real analyticity is precisely the
branch hypothesis; every remaining conservativity and record-algebra clause is
proved by the graph equivalence. -/
theorem protected_pch_graph_writer
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (gPCH : Θ → ℝ) (hg : AnalyticOnNhd ℝ gPCH Set.univ) :
    AnalyticOnNhd ℝ (fun θ => (θ, gPCH θ)) Set.univ ∧
    Function.Injective (protectedGraphWriter gPCH) ∧
    (∀ z, protectedGraphWriter gPCH (protectedGraphDiscard z) = z) ∧
    (∀ (β : Type*) (f : Θ → β) θ,
      f (protectedGraphDiscard (protectedGraphWriter gPCH θ)) = f θ) ∧
    (∃ e : (Θ → ℝ) ≃ₐ[ℝ] (ProtectedGraphRecord gPCH → ℝ),
      ∀ f θ, e f (protectedGraphWriter gPCH θ) = f θ) := by
  refine ⟨protectedGraphWriter_analytic gPCH hg,
    protectedGraphWriter_injective gPCH, protectedGraphWriter_discard gPCH,
    ?_, ?_⟩
  · intro β f θ
    exact protectedGraph_payload_recovery gPCH f θ
  · exact ⟨protectedGraphRecordAlgEquiv (R := ℝ) gPCH,
      protectedGraphRecordAlgEquiv_apply gPCH⟩

end NCG
