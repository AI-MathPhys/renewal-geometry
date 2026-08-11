/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Matter.QutritBell
import NCG.Flagship.ReplacementDilation
import NCG.Algebra.ChoiCriterion

/-!
# Nondegenerate qutrit Heisenberg erasure

This module proves the representation-independent clauses of
`thm:SM-qutrit-packet`.  The implementers are arbitrary qutrit unitaries; the
only representation input is their nondegenerate Heisenberg conjugation
character.  From that input we derive Hilbert--Schmidt orthogonality, full
matrix generation, the exact erasure twirl, Choi rank nine, and the canonical
key/record Stinespring factorization.
-/

open Matrix
open scoped Kronecker

namespace NCG

section AbstractHeisenbergFamily

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Uniform conjugation twirl of an arbitrary finite qutrit Heisenberg
family. -/
noncomputable def qutritHeisenbergTwirl
    (R : H → Matrix (Fin 3) (Fin 3) ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (Fintype.card H : ℂ)⁻¹ • ∑ a : H, R a * A * (R a)ᴴ

/-- Nondegeneracy of the alternating commutator characters forces arbitrary
distinct implementers to be Hilbert--Schmidt orthogonal. -/
theorem nondegenerateHeisenberg_hilbertSchmidt_pairing
    (R : H → Matrix (Fin 3) (Fin 3) ℂ) (phase : H → H → ℂ)
    (hunit : ∀ a, (R a)ᴴ * R a = 1 ∧ R a * (R a)ᴴ = 1)
    (heigen : ∀ c a, R c * R a * (R c)ᴴ = phase c a • R a)
    (hseparate : ∀ a b, a ≠ b →
      ∃ c, star (phase c a) * phase c b ≠ 1)
    (a b : H) :
    ((R a)ᴴ * R b).trace = if a = b then 3 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl, (hunit a).1, Matrix.trace_one]
    simp
  · rw [if_neg hab]
    obtain ⟨c, hphase⟩ := hseparate a b hab
    let Z := (R a)ᴴ * R b
    have hconjugated :
        R c * Z * (R c)ᴴ =
          (star (phase c a) * phase c b) • Z := by
      have hproduct :
          R c * Z * (R c)ᴴ =
            (R c * R a * (R c)ᴴ)ᴴ *
              (R c * R b * (R c)ᴴ) := by
        dsimp [Z]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (R c)ᴴ (R c), (hunit c).1,
          Matrix.one_mul]
      rw [hproduct, heigen c a, heigen c b,
        Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul]
    have htraceInvariant : (R c * Z * (R c)ᴴ).trace = Z.trace := by
      rw [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (R c) (Z * (R c)ᴴ)]
      simp only [Matrix.mul_assoc]
      rw [(hunit c).1, Matrix.mul_one]
    rw [hconjugated, Matrix.trace_smul, smul_eq_mul] at htraceInvariant
    have hfactor :
        (1 - star (phase c a) * phase c b) * Z.trace = 0 := by
      calc
        (1 - star (phase c a) * phase c b) * Z.trace =
            Z.trace - (star (phase c a) * phase c b) * Z.trace := by ring
        _ = 0 := sub_eq_zero.mpr htraceInvariant.symm
    have hnonzero : 1 - star (phase c a) * phase c b ≠ 0 :=
      sub_ne_zero.mpr hphase.symm
    exact (mul_eq_zero.mp hfactor).resolve_left hnonzero

/-- The nine arbitrary nondegenerate Heisenberg implementers are linearly
independent. -/
theorem nondegenerateHeisenberg_linearIndependent
    (R : H → Matrix (Fin 3) (Fin 3) ℂ) (phase : H → H → ℂ)
    (hcard : Fintype.card H = 9)
    (hunit : ∀ a, (R a)ᴴ * R a = 1 ∧ R a * (R a)ᴴ = 1)
    (heigen : ∀ c a, R c * R a * (R c)ᴴ = phase c a • R a)
    (hseparate : ∀ a b, a ≠ b →
      ∃ c, star (phase c a) * phase c b ≠ 1) :
    LinearIndependent ℂ R := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum a
  have htested := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℂ => ((R a)ᴴ * M).trace) hsum
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul] at htested
  rw [Finset.sum_eq_single a] at htested
  · rw [nondegenerateHeisenberg_hilbertSchmidt_pairing
      R phase hunit heigen hseparate a a, if_pos rfl] at htested
    norm_num at htested ⊢
    exact htested
  · intro b _ hba
    rw [nondegenerateHeisenberg_hilbertSchmidt_pairing
      R phase hunit heigen hseparate a b, if_neg hba.symm, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ a) hmem

/-- Every arbitrary nondegenerate Heisenberg family on a qutrit generates the
full matrix algebra. -/
theorem nondegenerateHeisenberg_span_fullMatrix
    (R : H → Matrix (Fin 3) (Fin 3) ℂ) (phase : H → H → ℂ)
    (hcard : Fintype.card H = 9)
    (hunit : ∀ a, (R a)ᴴ * R a = 1 ∧ R a * (R a)ᴴ = 1)
    (heigen : ∀ c a, R c * R a * (R c)ᴴ = phase c a • R a)
    (hseparate : ∀ a b, a ≠ b →
      ∃ c, star (phase c a) * phase c b ≠ 1) :
    Submodule.span ℂ (Set.range R) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
    (nondegenerateHeisenberg_linearIndependent
      R phase hcard hunit heigen hseparate)
  rw [hcard]
  simp [Module.finrank_matrix]

/-- For any projective qutrit Heisenberg representation, the uniform twirl is
exact tracial erasure.  Additivity of the adjoint action is the cocycle-free
statement that conjugation by `R beta` permutes the projective family. -/
theorem nondegenerateHeisenberg_twirl_eq_tracialErasure
    (R : H → Matrix (Fin 3) (Fin 3) ℂ) (phase : H → H → ℂ)
    (hcard : Fintype.card H = 9)
    (hunit : ∀ a, (R a)ᴴ * R a = 1 ∧ R a * (R a)ᴴ = 1)
    (heigen : ∀ c a, R c * R a * (R c)ᴴ = phase c a • R a)
    (hseparate : ∀ a b, a ≠ b →
      ∃ c, star (phase c a) * phase c b ≠ 1)
    (hAd : ∀ beta a A,
      R beta * (R a * A * (R a)ᴴ) * (R beta)ᴴ =
        R (beta + a) * A * (R (beta + a))ᴴ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    qutritHeisenbergTwirl R A = (A.trace / 3) • 1 := by
  let T := qutritHeisenbergTwirl R A
  have hinvariant (beta : H) : R beta * T * (R beta)ᴴ = T := by
    dsimp [T, qutritHeisenbergTwirl]
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    calc
      ∑ a : H, R beta * (R a * A * (R a)ᴴ) * (R beta)ᴴ =
          ∑ a : H, R (beta + a) * A * (R (beta + a))ᴴ :=
        Finset.sum_congr rfl fun a _ => hAd beta a A
      _ = ∑ a : H, R a * A * (R a)ᴴ :=
        Fintype.sum_equiv (Equiv.addLeft beta) _ _ fun a => rfl
  have hcommGenerator (beta : H) : R beta * T = T * R beta := by
    have h := congrArg (fun M => M * R beta) (hinvariant beta)
    simpa only [Matrix.mul_assoc, (hunit beta).1, Matrix.mul_one] using h
  have hspan := nondegenerateHeisenberg_span_fullMatrix
    R phase hcard hunit heigen hseparate
  have hcommAll (X : Matrix (Fin 3) (Fin 3) ℂ) : T * X = X * T := by
    have hx : X ∈ Submodule.span ℂ (Set.range R) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨a, rfl⟩ := hX
        exact (hcommGenerator a).symm
    | zero => simp
    | add X Y _ _ hX hY => rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
    | smul c X _ hX =>
        rw [Matrix.mul_smul, Matrix.smul_mul, hX]
  have hscalar : ∃ c : ℂ, T = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    have hrange : T ∈ Set.range (Matrix.scalar (Fin 3)) := by
      rw [Matrix.mem_range_scalar_iff_commute_single']
      intro i j
      exact (hcommAll (Matrix.single i j 1)).symm
    obtain ⟨c, hc⟩ := hrange
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij,
        Matrix.diagonal_apply_ne _ hij]
  have htraceT : T.trace = A.trace := by
    dsimp [T, qutritHeisenbergTwirl]
    rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    have hterm : ∀ a : H, (R a * A * (R a)ᴴ).trace = A.trace := by
      intro a
      rw [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (R a) (A * (R a)ᴴ)]
      simp only [Matrix.mul_assoc]
      rw [(hunit a).1, Matrix.mul_one]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    ring
  obtain ⟨c, hc⟩ := hscalar
  have hcoefficient : c = A.trace / 3 := by
    have ht := htraceT
    rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
    exact (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).2 ht
  change T = (A.trace / 3) • 1
  rw [hc, hcoefficient]

/-- Relative revisions cancel an arbitrary unit-modulus projective cocycle and
therefore form an honest representation on the doubled qutrit. -/
theorem relativeHeisenberg_projectiveCocycle_cancels
    (R : H → Matrix (Fin 3) (Fin 3) ℂ) (tau : H → H → ℂ)
    (hmul : ∀ a b, R a * R b = tau a b • R (a + b))
    (hphase : ∀ a b, star (tau a b) * tau a b = 1)
    (a b : H) :
    ((R a).map (starRingEnd ℂ) ⊗ₖ R a) *
        ((R b).map (starRingEnd ℂ) ⊗ₖ R b) =
      (R (a + b)).map (starRingEnd ℂ) ⊗ₖ R (a + b) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.map_mul, hmul a b]
  rw [map_conj_smul, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul]
  have hp := hphase a b
  change (starRingEnd ℂ) (tau a b) * tau a b = 1 at hp
  rw [hp, one_smul]

end AbstractHeisenbergFamily

/-- Choi matrix of qutrit tracial erasure. -/
noncomputable def qutritTracialErasureChoi :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 3 : ℂ) • 1

/-- Exact Choi rank of qutrit erasure: all nine Choi directions survive. -/
theorem qutritTracialErasureChoi_rank : qutritTracialErasureChoi.rank = 9 := by
  have hunit : IsUnit qutritTracialErasureChoi := by
    rw [Matrix.isUnit_iff_isUnit_det]
    unfold qutritTracialErasureChoi
    rw [Matrix.det_smul, Matrix.det_one]
    norm_num
  rw [Matrix.rank_of_isUnit qutritTracialErasureChoi hunit]
  simp

/-- The standard qutrit replacement dilation has a `3 x 3` environment: the
first factor purifies the maximally mixed output and the second stores the
input record.  Its dimension is nine, and the reference-system identity makes
the no-hiding factorization literal. -/
theorem qutritErasure_stinespring_keyRecordFactorization
    {Ref : Type*} [Fintype Ref]
    (Omega : Fin 3 × Fin 3 → ℂ)
    (hOmega : star Omega ⬝ᵥ Omega = 1)
    (hpur : ∀ X : Matrix (Fin 3) (Fin 3) ℂ,
      star Omega ⬝ᵥ ((X ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ Omega) =
        (((1 / 3 : ℂ) • 1) * X).trace)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hU : Uᴴ * U = 1) :
    (∀ psi phi : Fin 3 → ℂ,
      star (repVec Omega U psi) ⬝ᵥ repVec Omega U phi = star psi ⬝ᵥ phi) ∧
    (∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∀ psi phi : Fin 3 → ℂ,
      star (repVec Omega U psi) ⬝ᵥ
          (((X ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) ⊗ₖ
            (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ repVec Omega U phi) =
        ((((1 / 3 : ℂ) • 1) * X).trace) * (star psi ⬝ᵥ phi)) ∧
    Fintype.card (Fin 3 × Fin 3) = 9 ∧
    (∀ (Psi : Ref × Fin 3 → ℂ) x p k,
      repVec Omega U (fun k' => Psi (x, k')) (p, k) =
        (U *ᵥ fun k' => Psi (x, k')) k * Omega p) := by
  refine ⟨replacement_isometry Omega hOmega U hU,
    replacement_channel Omega ((1 / 3 : ℂ) • 1) hpur U hU,
    by simp, ?_⟩
  exact replacement_reference_split Omega U

end NCG
