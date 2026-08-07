/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical one-generation incidence audit
  (`thm:SMST-one-generation-audit`, Gran-Tensor manuscript)

* `smst_one_generation_audit`:
  (i) the Schur engine: a matrix commuting with the full
      matrix algebra of an irreducible gauge block is scalar —
      giving `𝒜_gauge' ≅ ℂ⁵` for the five pairwise
      inequivalent modules `Q ⊕ u ⊕ d ⊕ L ⊕ e`;
  (ii) the cross-generation engine: a nonzero incidence block
      `Y` between two summands generates every scaled matrix
      unit of the cross block via endpoint rank-one
      multiplications
      (`E_{ai}·Y·E_{jb} = Y_{ij}·E_{ab}`), so products and
      adjoints generate the full matrix algebra on each
      connected component of the incidence graph;
  (iii) the residual count: matrices commuting with the
      two-component block algebra
      `{diag(A, B) : A ∈ M_m, B ∈ M_l}` are exactly
      `diag(a·I, b·I)` — the residual is `ℂ²`, one central
      direction for the quark component `{Q,u,d}` (dim 12)
      and one for the lepton component `{L,e}` (dim 3).

Rendering disclosed: the specific dimensions (6,3,3,2,1 and
12,3), the pairwise inequivalence of the five gauge modules,
and the nonvanishing of the three Higgs-contracted incidence
histories are the manuscript's representation-theoretic
inputs; adding a neutral singlet changes only the lepton
component dimension, leaving the `ℂ²` residual of (iii).
-/

open Matrix

namespace NCG

private lemma scalar_of_central {g : Type*} [Fintype g]
    [DecidableEq g] (T : Matrix g g ℂ)
    (h : ∀ a : Matrix g g ℂ, T * a = a * T) :
    ∃ c : ℂ, T = c • 1 := by
  obtain ⟨c, hc⟩ :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => (h (Matrix.single i j 1)).symm)
  refine ⟨c, ?_⟩
  rw [← hc]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

/-- `thm:SMST-one-generation-audit`. -/
theorem smst_one_generation_audit :
    -- (i) Schur: irreducible blocks have scalar commutant
    (∀ {g : Type} [Fintype g] [DecidableEq g]
      (T : Matrix g g ℂ),
      (∀ a : Matrix g g ℂ, T * a = a * T)
        ↔ ∃ c : ℂ, T = c • 1)
    -- (ii) a nonzero incidence block generates every scaled
    --      cross matrix unit
    ∧ (∀ {s r : Type} [Fintype s] [Fintype r] [DecidableEq s]
        [DecidableEq r] (Y : Matrix s r ℂ) (a i : s)
        (j b : r),
        Matrix.single a i (1 : ℂ) * Y
            * Matrix.single j b (1 : ℂ)
          = Y i j • Matrix.single a b 1)
    -- (iii) the two-component residual is `ℂ²`
    ∧ (∀ {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
        [DecidableEq l] (T : Matrix (m ⊕ l) (m ⊕ l) ℂ),
        (∀ (A : Matrix m m ℂ) (B : Matrix l l ℂ),
          T * Matrix.fromBlocks A 0 0 B
            = Matrix.fromBlocks A 0 0 B * T)
        ↔ ∃ a b : ℂ,
            T = Matrix.fromBlocks (a • 1) 0 0 (b • 1)) := by
  have hschur : ∀ {g : Type} [Fintype g] [DecidableEq g]
      (T : Matrix g g ℂ),
      (∀ a : Matrix g g ℂ, T * a = a * T)
        ↔ ∃ c : ℂ, T = c • 1 := by
    intro g _ _ T
    constructor
    · exact scalar_of_central T
    · rintro ⟨c, rfl⟩ a
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
  refine ⟨hschur, ?_, ?_⟩
  · intro s r _ _ _ _ Y a i j b
    ext u v
    simp only [Matrix.mul_apply, Matrix.single_apply,
      Matrix.smul_apply, smul_eq_mul, ite_mul, mul_ite,
      one_mul, mul_one, zero_mul, mul_zero]
    by_cases hu : a = u <;> by_cases hv : b = v <;>
      simp [hu, hv]
  · intro m l _ _ _ _ T
    constructor
    · intro hT
      -- the diagonal idempotent kills the off-diagonal blocks
      have hE := hT 1 0
      rw [← Matrix.fromBlocks_toBlocks T,
        Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply] at hE
      simp only [Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_zero, Matrix.zero_mul, add_zero] at hE
      have h12 : T.toBlocks₁₂ = 0 := by
        have h := congrArg Matrix.toBlocks₁₂ hE
        simpa [Matrix.toBlocks_fromBlocks₁₂] using h.symm
      have h21 : T.toBlocks₂₁ = 0 := by
        have h := congrArg Matrix.toBlocks₂₁ hE
        simpa [Matrix.toBlocks_fromBlocks₂₁] using h
      -- Schur on each diagonal block
      obtain ⟨a, ha⟩ := scalar_of_central T.toBlocks₁₁
        (fun A => by
          have h := hT A 0
          rw [← Matrix.fromBlocks_toBlocks T,
            Matrix.fromBlocks_multiply,
            Matrix.fromBlocks_multiply] at h
          have h11 := congrArg Matrix.toBlocks₁₁ h
          simpa [Matrix.toBlocks_fromBlocks₁₁,
            Matrix.mul_zero, Matrix.zero_mul, add_zero,
            zero_add] using h11)
      obtain ⟨b, hb⟩ := scalar_of_central T.toBlocks₂₂
        (fun B => by
          have h := hT 0 B
          rw [← Matrix.fromBlocks_toBlocks T,
            Matrix.fromBlocks_multiply,
            Matrix.fromBlocks_multiply] at h
          have h22 := congrArg Matrix.toBlocks₂₂ h
          simpa [Matrix.toBlocks_fromBlocks₂₂,
            Matrix.mul_zero, Matrix.zero_mul, add_zero,
            zero_add] using h22)
      refine ⟨a, b, ?_⟩
      rw [← Matrix.fromBlocks_toBlocks T, h12, h21, ha, hb]
    · rintro ⟨a, b, rfl⟩ A B
      rw [Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      simp [Matrix.mul_smul]

end NCG
