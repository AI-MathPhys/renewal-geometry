/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandFactorObstruction
import NCG.Algebra.SkolemNoether

/-!
# abstract matrix-factor normal form

This supplies the abstract representation-theoretic clause omitted from the
split-carrier proof of `thm:SMST-factor-obstruction`.  A unital representation
of `M_n(ℂ)` on `ℂ^N` forces `N = n k`; after reindexing the carrier as
`Fin n × Fin k`, it is conjugate to the left Kronecker representation.
Together with `smst_factor_obstruction`, this is exactly the manuscript's
factor/commutant normal form and centre obstruction.
-/

open Matrix Kronecker Module LinearMap

namespace NCG

/-- The carrier dimension of a unital finite-dimensional representation of
`M_n(ℂ)` is a multiple of `n`. -/
theorem matrix_representation_dimension {n N : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
      Matrix (Fin N) (Fin N) ℂ) :
    ∃ k : ℕ, N = n * k := by
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun i j => Matrix.single i j 1
  have hEmul : ∀ i j k l,
      E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    simp only [E]
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg hjk]
      exact Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i j k hjk 1
  have hEsum : (∑ i : Fin n, E i i) = 1 := by
    simpa only [E] using (sum_single_diag_eq_one (n := n))
  have hPidem : φ (E 0 0) * φ (E 0 0) = φ (E 0 0) := by
    rw [← map_mul, hEmul]
    simp
  have htr_all : ∀ i : Fin n,
      (φ (E i i)).trace = (φ (E 0 0)).trace := by
    intro i
    have h1 : E i i = E i 0 * E 0 i := by rw [hEmul]; simp
    have h2 : E 0 0 = E 0 i * E i 0 := by rw [hEmul]; simp
    rw [h1, map_mul, Matrix.trace_mul_comm, ← map_mul, ← h2]
  have htotal : (n : ℂ) * (φ (E 0 0)).trace = (N : ℂ) := by
    have h1 : (∑ i, φ (E i i)) = 1 := by
      rw [← map_sum, hEsum, map_one]
    have h2 := congrArg Matrix.trace h1
    rw [Matrix.trace_sum, Matrix.trace_one] at h2
    calc
      (n : ℂ) * (φ (E 0 0)).trace
          = ∑ _i : Fin n, (φ (E 0 0)).trace := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      _ = ∑ i : Fin n, (φ (E i i)).trace :=
            Finset.sum_congr rfl fun i _ => (htr_all i).symm
      _ = (N : ℂ) := by simpa using h2
  let k : ℕ := finrank ℂ
    (LinearMap.range (Matrix.toLin' (φ (E 0 0))))
  have htrace : (φ (E 0 0)).trace = (k : ℂ) := by
    simpa only [k] using trace_isIdempotentElem hPidem
  refine ⟨k, ?_⟩
  rw [htrace] at htotal
  exact_mod_cast htotal.symm

/-- Abstract normal form: after identifying `Fin N` with
`Fin n × Fin k`, every unital representation is conjugate to
`a ↦ a ⊗ I_k`. -/
theorem matrix_representation_normal_form {n N : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
      Matrix (Fin N) (Fin N) ℂ) :
    ∃ (k : ℕ) (hNk : N = n * k)
      (e : Fin n × Fin k ≃ Fin N)
      (u : (Matrix (Fin N) (Fin N) ℂ)ˣ),
      ∀ a : Matrix (Fin n) (Fin n) ℂ,
        ((Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom.comp
            (CommonOrigin.leftKron (I := Fin n) (J := Fin k))) a
          = (u : Matrix (Fin N) (Fin N) ℂ) * φ a
              * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
                  Matrix (Fin N) (Fin N) ℂ) := by
  obtain ⟨k, hNk⟩ := matrix_representation_dimension φ
  have hcard : Fintype.card (Fin n × Fin k) = Fintype.card (Fin N) := by
    simp [hNk]
  let e : Fin n × Fin k ≃ Fin N := Fintype.equivOfCardEq hcard
  let ψ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
      Matrix (Fin N) (Fin N) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom.comp
      (CommonOrigin.leftKron (I := Fin n) (J := Fin k))
  obtain ⟨u, hu⟩ := skolem_noether φ ψ
  exact ⟨k, hNk, e, u, hu⟩

/-- Exact assembly of the abstract normal form with the split-carrier
commutant, factoriality, and nontrivial-centre obstruction. -/
theorem smst_factor_obstruction_exact :
    (∀ {n N : ℕ} [NeZero n]
      (φ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
        Matrix (Fin N) (Fin N) ℂ),
      ∃ (k : ℕ) (hNk : N = n * k)
        (e : Fin n × Fin k ≃ Fin N)
        (u : (Matrix (Fin N) (Fin N) ℂ)ˣ),
        ∀ a : Matrix (Fin n) (Fin n) ℂ,
          ((Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom.comp
              (CommonOrigin.leftKron (I := Fin n) (J := Fin k))) a
            = (u : Matrix (Fin N) (Fin N) ℂ) * φ a
                * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
                    Matrix (Fin N) (Fin N) ℂ))
    ∧ (∀ {I J : Type*} [Fintype I] [DecidableEq I]
        [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J],
        ({B : Matrix (I × J) (I × J) ℂ |
            ∀ g : Matrix I I ℂ,
              (g ⊗ₖ (1 : Matrix J J ℂ)) * B = B * (g ⊗ₖ 1)}
          = Set.range fun b : Matrix J J ℂ =>
              (1 : Matrix I I ℂ) ⊗ₖ b)) := by
  refine ⟨?_, ?_⟩
  · intro n N _ φ
    exact matrix_representation_normal_form φ
  · intro I J _ _ _ _ _ _
    exact (smst_factor_obstruction (I := I) (J := J)).1

end NCG
