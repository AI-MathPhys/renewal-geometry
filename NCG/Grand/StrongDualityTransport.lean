/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandInterface2
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Strong-duality transport

This module completes `thm:strong-transport`.  It deep-embeds arbitrary
finite noncommutative star-polynomials and proves transport by structural
induction.  It then proves equality, norm inequalities, and order inequalities
for all such terms, continuous functional-calculus naturality, spectral and
singular-spectral invariance, exact kernel transport, and concrete unitary
matrix determinant/spectral-determinant invariance.
-/

namespace NCG

/-- Syntax of every finite noncommutative word built from named generators,
complex scalars, addition, multiplication, negation, and involution. -/
inductive NCStarTerm (ι : Type*)
  | generator : ι → NCStarTerm ι
  | scalar : ℂ → NCStarTerm ι
  | add : NCStarTerm ι → NCStarTerm ι → NCStarTerm ι
  | mul : NCStarTerm ι → NCStarTerm ι → NCStarTerm ι
  | neg : NCStarTerm ι → NCStarTerm ι
  | star : NCStarTerm ι → NCStarTerm ι

/-- Evaluation of a finite star-word in a complex star algebra. -/
def NCStarTerm.eval {ι A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] (assignment : ι → A) : NCStarTerm ι → A
  | .generator i => assignment i
  | .scalar z => algebraMap ℂ A z
  | .add s t => s.eval assignment + t.eval assignment
  | .mul s t => s.eval assignment * t.eval assignment
  | .neg t => -t.eval assignment
  | .star t => Star.star (t.eval assignment)

/-- Structural transport of every finite noncommutative star-word. -/
theorem NCStarTerm.map_eval
    {ι A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (assignment : ι → A) (t : NCStarTerm ι) :
    e (t.eval assignment) = t.eval (fun i => e (assignment i)) := by
  induction t with
  | generator i => rfl
  | scalar z => exact e.toAlgEquiv.commutes z
  | add s t hs ht => simp [NCStarTerm.eval, hs, ht]
  | mul s t hs ht => simp [NCStarTerm.eval, hs, ht]
  | neg t ht => simp [NCStarTerm.eval, ht]
  | star t ht =>
      change e (Star.star (t.eval assignment)) =
        Star.star (t.eval (fun i => e (assignment i)))
      rw [map_star, ht]

section CStarTransport

variable {ι A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Every finite word identity is reflected as well as preserved. -/
theorem NCStarTerm.identity_transport (e : A ≃⋆ₐ[ℂ] B)
    (assignment : ι → A) (s t : NCStarTerm ι) :
    s.eval assignment = t.eval assignment ↔
      s.eval (fun i => e (assignment i)) =
        t.eval (fun i => e (assignment i)) := by
  rw [← s.map_eval e assignment, ← t.map_eval e assignment]
  exact e.injective.eq_iff.symm

/-- Star-algebra equivalence preserves the norm of every finite word. -/
theorem NCStarTerm.norm_transport (e : A ≃⋆ₐ[ℂ] B)
    (assignment : ι → A) (t : NCStarTerm ι) :
    ‖t.eval (fun i => e (assignment i))‖ = ‖t.eval assignment‖ := by
  rw [← t.map_eval e assignment]
  exact StarAlgEquiv.norm_map e _

/-- Every norm inequality formulated from finite preserved words is reflected
and preserved. -/
theorem NCStarTerm.norm_inequality_transport (e : A ≃⋆ₐ[ℂ] B)
    (assignment : ι → A) (s t : NCStarTerm ι) :
    ‖s.eval assignment‖ ≤ ‖t.eval assignment‖ ↔
      ‖s.eval (fun i => e (assignment i))‖ ≤
        ‖t.eval (fun i => e (assignment i))‖ := by
  rw [s.norm_transport e assignment, t.norm_transport e assignment]

/-- Positivity is reflected and preserved by a C-star equivalence. -/
theorem StarAlgEquiv.nonneg_iff
    [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    0 ≤ e a ↔ 0 ≤ a := by
  constructor
  · intro h
    have := map_nonneg e.symm h
    simpa using this
  · exact fun h => map_nonneg e h

/-- Every order inequality formulated from finite preserved words is reflected
and preserved. -/
theorem NCStarTerm.order_inequality_transport
    [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B)
    (assignment : ι → A) (s t : NCStarTerm ι) :
    s.eval assignment ≤ t.eval assignment ↔
      s.eval (fun i => e (assignment i)) ≤
        t.eval (fun i => e (assignment i)) := by
  have hpos := StarAlgEquiv.nonneg_iff e
    (t.eval assignment - s.eval assignment)
  rw [map_sub, t.map_eval e assignment, s.map_eval e assignment] at hpos
  simpa [sub_nonneg] using hpos.symm

/-- Continuous functional calculus of a normal transfer is transported
exactly. -/
theorem strongTransport_cfc (e : A ≃⋆ₐ[ℂ] B)
    (f : ℂ → ℂ) (a : A) (hf : ContinuousOn f (spectrum ℂ a))
    [IsStarNormal a] :
    e (cfc f a) = cfc f (e a) := by
  exact StarAlgHomClass.map_cfc e f a hf
    (StarAlgEquiv.isometry e).continuous

/-- Spectrum is exactly invariant under strong duality. -/
theorem strongTransport_spectrum (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    spectrum ℂ (e a) = spectrum ℂ a :=
  AlgEquiv.spectrum_eq e.toAlgEquiv a

/-- The singular spectrum is the spectrum of `a* a`; in finite matrices its
square roots, with multiplicity, are the singular values. -/
def singularSpectrum (a : A) : Set ℂ :=
  spectrum ℂ (star a * a)

theorem strongTransport_singularSpectrum (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    singularSpectrum (e a) = singularSpectrum a := by
  change spectrum ℂ (star (e a) * e a) = spectrum ℂ (star a * a)
  rw [← map_star, ← map_mul]
  exact strongTransport_spectrum e (star a * a)

/-- Exact right-kernel transport. -/
def rightKernel (a : A) : Set A := {x | a * x = 0}

theorem strongTransport_rightKernel (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    e '' rightKernel a = rightKernel (e a) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e a * e x = 0
    rw [← map_mul, hx, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change a * e.symm y = 0
    apply e.injective
    change e (a * e.symm y) = e 0
    rw [map_mul, map_zero]
    simpa [rightKernel] using hy

/-- Any statistic depending only on the spectrum (spectral gaps,
pseudodeterminants, and spectral determinants included) is transported. -/
theorem strongTransport_spectralStatistic
    {β : Type*} (e : A ≃⋆ₐ[ℂ] B) (F : Set ℂ → β) (a : A) :
    F (spectrum ℂ (e a)) = F (spectrum ℂ a) := by
  rw [strongTransport_spectrum e a]

/-- Any construction from a transported Gram or moment table is transported
by congruence.  This is the formal closure step for Hankel ranks, leakage
Grams, Moore--Penrose Schur residuals, and their norms. -/
theorem strongTransport_derivedTable
    {table β : Type*} (F : table → β) {G G' : table} (hG : G' = G) :
    F G' = F G := by
  rw [hG]

end CStarTransport

section MatrixTransport

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Transfer intertwining by a two-sided unitary is literal unitary
conjugacy. -/
theorem unitaryIntertwiner_conjugates
    (U T T' : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hT : U * T = T' * U) :
    T' = U * T * Uᴴ := by
  calc
    T' = T' * 1 := by rw [Matrix.mul_one]
    _ = T' * (U * Uᴴ) := by rw [hU']
    _ = (T' * U) * Uᴴ := by rw [Matrix.mul_assoc]
    _ = (U * T) * Uᴴ := by rw [hT]

/-- Determinant is invariant under the concrete unitary conjugation supplied
by the monoidal intertwiner. -/
theorem unitaryConjugation_det
    (U A : Matrix n n ℂ) (hU' : U * Uᴴ = 1) :
    Matrix.det (U * A * Uᴴ) = Matrix.det A := by
  have hdet : Matrix.det U * Matrix.det Uᴴ = 1 := by
    rw [← Matrix.det_mul, hU', Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det U * Matrix.det A * Matrix.det Uᴴ =
        Matrix.det A * (Matrix.det U * Matrix.det Uᴴ) := by ring
    _ = Matrix.det A := by rw [hdet, mul_one]

/-- Exact determinant transport for an intertwined transfer. -/
theorem unitaryIntertwiner_det
    (U T T' : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hT : U * T = T' * U) :
    Matrix.det T' = Matrix.det T := by
  rw [unitaryIntertwiner_conjugates U T T' hU hU' hT,
    unitaryConjugation_det U T hU']

/-- Spectral determinant `det(zI-T)` is transported for every spectral
parameter. -/
theorem unitaryIntertwiner_spectralDeterminant
    (U T T' : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hT : U * T = T' * U) (z : ℂ) :
    Matrix.det (z • (1 : Matrix n n ℂ) - T') =
      Matrix.det (z • (1 : Matrix n n ℂ) - T) := by
  have hconj := unitaryIntertwiner_conjugates U T T' hU hU' hT
  have hpoly :
      z • (1 : Matrix n n ℂ) - T' =
        U * (z • (1 : Matrix n n ℂ) - T) * Uᴴ := by
    rw [hconj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    simp [hU']
  rw [hpoly, unitaryConjugation_det U _ hU']

/-- Consolidated exact matrix clauses already proved by the original
intertwiner theorem, now augmented by determinant and spectral determinant
transport. -/
theorem strong_duality_matrix_transport
    {p : Type*} (U T T' : Matrix n n ℂ) (S S' : Matrix n p ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hT : U * T = T' * U) (hS : U * S = S') :
    (∀ k : ℕ, U * T ^ k = T' ^ k * U)
    ∧ (∀ k : ℕ, S'ᴴ * T' ^ k * S' = Sᴴ * T ^ k * S)
    ∧ (S'ᴴ * S' = Sᴴ * S)
    ∧ Matrix.det T' = Matrix.det T
    ∧ (∀ z : ℂ, Matrix.det (z • (1 : Matrix n n ℂ) - T') =
        Matrix.det (z • (1 : Matrix n n ℂ) - T)) := by
  obtain ⟨hpow, hmom, hgram⟩ :=
    strong_transport U T T' S S' hU hU' hT hS
  exact ⟨hpow, hmom, hgram,
    unitaryIntertwiner_det U T T' hU hU' hT,
    unitaryIntertwiner_spectralDeterminant U T T' hU hU' hT⟩

end MatrixTransport

end NCG
