/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.GeneratorProjections
import NCG.Grand.MomentLeakage
import NCG.Grand.OneDoubletOddTangentClassification
import NCG.Flagship.CharacterLeakage

/-!
# Saturated finite-Dirac generator

This module completes the finite-dimensional mechanisms in
`thm:SMST-generator-projections`.

* `finiteKrylovChain_firstStabilization` proves that a nested finite Krylov
  chain has a first plateau and that the plateau is transition invariant.
* `stabilizedIsometricCarrier_reduces` turns that invariance into the exact
  reducing-projection equations for a self-adjoint generator.
* `finiteDiracProjection_pythagoras` proves the Hilbert--Schmidt budget from
  the defining equations of the orthogonal relation-space projector.
* `zeroOddProvenance_fixesFiniteDiracProjection` uses the exact singular
  source-Schur theorem to prove that zero provenance defect puts the complete
  odd generator in the finite-Dirac space; no Gram invertibility is assumed.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Every nested chain of subspaces in a finite-dimensional carrier has a
first plateau.  If the transition sends each head into the next head, that
first plateau is transition invariant.  This is the abstract form of the
manuscript's finite Krylov stabilization argument. -/
theorem finiteKrylovChain_firstStabilization
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (K : ℕ → Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hmono : ∀ n, K n ≤ K (n + 1))
    (hforward : ∀ n, Submodule.map T (K n) ≤ K (n + 1)) :
    ∃ nStar,
      (∀ m, m < nStar → K m ≠ K (m + 1)) ∧
      K nStar = K (nStar + 1) ∧
      Submodule.map T (K nStar) ≤ K nStar := by
  let f : ℕ → ℕ := fun n => Module.finrank ℂ (K n)
  have hKmonotone : Monotone K := monotone_nat_of_le_succ hmono
  have hfmonotone : Monotone f := by
    intro a b hab
    exact Submodule.finrank_mono (hKmonotone hab)
  have hfbound : ∀ n, f n ≤ Module.finrank ℂ E := by
    intro n
    exact Submodule.finrank_le (K n)
  obtain ⟨b, N, hconstant⟩ :=
    converges_of_monotone_of_bounded hfmonotone hfbound
  have hplateau : ∃ n, K n = K (n + 1) := by
    refine ⟨N, ?_⟩
    apply Submodule.eq_of_le_of_finrank_le (hmono N) ?_
    change f (N + 1) ≤ f N
    rw [hconstant N le_rfl, hconstant (N + 1) (Nat.le_succ N)]
  let nStar := Nat.find hplateau
  have hfirst : K nStar = K (nStar + 1) := Nat.find_spec hplateau
  refine ⟨nStar, ?_, hfirst, ?_⟩
  · intro m hm heq
    exact (Nat.find_min hplateau hm) heq
  · calc
      Submodule.map T (K nStar) ≤ K (nStar + 1) := hforward nStar
      _ = K nStar := hfirst.symm

/-- An isometric synthesis of a stabilized invariant carrier gives the exact
boxed leakage equation.  Self-adjointness supplies the reverse leakage, so
the saturated projection genuinely reduces the generator. -/
theorem stabilizedIsometricCarrier_reduces
    {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq h] [DecidableEq k]
    (W : Matrix h k ℂ) (G : Matrix h h ℂ)
    (hW : Wᴴ * W = 1) (hG : Gᴴ = G)
    (hinvariant : ∃ C : Matrix k k ℂ, G * W = W * C) :
    let P := W * Wᴴ
    ((1 : Matrix h h ℂ) - P) * G * P = 0 ∧
      P * G * ((1 : Matrix h h ℂ) - P) = 0 ∧
      P * G = G * P := by
  dsimp only
  let P : Matrix h h ℂ := W * Wᴴ
  let Q : Matrix h h ℂ := 1 - P
  have hPH : Pᴴ = P := by
    simp [P, Matrix.conjTranspose_mul]
  have hQH : Qᴴ = Q := by
    simp [Q, hPH]
  have hQW : Q * W = 0 := by
    dsimp [Q, P]
    rw [Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hW, Matrix.mul_one, sub_self]
  obtain ⟨C, hC⟩ := hinvariant
  have hleft : Q * G * P = 0 := by
    calc
      Q * G * P = (Q * (G * W)) * Wᴴ := by simp only [P, Matrix.mul_assoc]
      _ = (Q * (W * C)) * Wᴴ := by rw [hC]
      _ = ((Q * W) * C) * Wᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hQW, Matrix.zero_mul, Matrix.zero_mul]
  have hright : P * G * Q = 0 := by
    have hstar := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, hPH, hQH, hG,
      Matrix.conjTranspose_zero, Matrix.mul_assoc] using hstar
  have hsum : P + Q = 1 := by
    dsimp [Q]
    abel
  have hPG : P * G = P * G * P := by
    calc
      P * G = P * G * (P + Q) := by rw [hsum, Matrix.mul_one]
      _ = P * G * P + P * G * Q := by rw [Matrix.mul_add]
      _ = P * G * P := by rw [hright, add_zero]
  have hGP : G * P = P * G * P := by
    calc
      G * P = (P + Q) * G * P := by rw [hsum, Matrix.one_mul]
      _ = P * G * P + Q * G * P := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = P * G * P := by rw [hleft, add_zero]
  have hcomm : P * G = G * P := hPG.trans hGP.symm
  exact ⟨hleft, hright, hcomm⟩

/-- The innovation Gram at any isometric Krylov head is positive, has exactly
the rank of the next missing layer, and vanishes precisely at stabilization.
This packages the constructive "add the positive innovation" clause. -/
theorem finiteKrylovInnovation_detectsStabilization
    {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq h] [DecidableEq k]
    (W : Matrix h k ℂ) (G : Matrix h h ℂ)
    (hW : Wᴴ * W = 1) (hG : Gᴴ = G) :
    let innovation :=
      Wᴴ * (G * G) * W - (Wᴴ * G * W) * (Wᴴ * G * W)
    innovation = (((1 : Matrix h h ℂ) - W * Wᴴ) * G * W)ᴴ *
        (((1 : Matrix h h ℂ) - W * Wᴴ) * G * W) ∧
      innovation.PosSemidef ∧
      innovation.rank = (((1 : Matrix h h ℂ) - W * Wᴴ) * G * W).rank ∧
      (innovation = 0 ↔ ((1 : Matrix h h ℂ) - W * Wᴴ) * G * W = 0) := by
  exact universal_moment_leakage W G hW hG

/-- Hilbert--Schmidt Pythagoras for the canonical finite-Dirac relation-space
projection.  The generator may have several columns, so this also covers a
simultaneous packet of typed residue slots. -/
theorem finiteDiracProjection_pythagoras
    {d k : Type*} [Fintype d] [Fintype k]
    [DecidableEq d] [DecidableEq k]
    (Pi : Matrix d d ℂ) (X : Matrix d k ℂ)
    (hPiH : Piᴴ = Pi) (hPi2 : Pi * Pi = Pi) :
    let D := Pi * X
    let R := ((1 : Matrix d d ℂ) - Pi) * X
    X = D + R ∧ Dᴴ * R = 0 ∧ Rᴴ * D = 0 ∧
      (Xᴴ * X).trace = (Dᴴ * D).trace + (Rᴴ * R).trace := by
  dsimp only
  let D := Pi * X
  let R := ((1 : Matrix d d ℂ) - Pi) * X
  have hQH : ((1 : Matrix d d ℂ) - Pi)ᴴ = 1 - Pi := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPiH]
  have hDR : Dᴴ * R = 0 := by
    dsimp [D, R]
    rw [Matrix.conjTranspose_mul, hPiH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pi (1 - Pi), Matrix.mul_sub,
      Matrix.mul_one, hPi2, sub_self, Matrix.zero_mul, Matrix.mul_zero]
  have hRD : Rᴴ * D = 0 := by
    dsimp [D, R]
    rw [Matrix.conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - Pi) Pi, Matrix.sub_mul,
      Matrix.one_mul, hPi2, sub_self, Matrix.zero_mul, Matrix.mul_zero]
  have hsum : X = D + R := by
    dsimp [D, R]
    rw [← Matrix.add_mul]
    congr 1
    abel
    simp
  refine ⟨hsum, hDR, hRD, ?_⟩
  conv_lhs => rw [hsum]
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add]
  simp only [Matrix.trace_add, hDR, hRD, Matrix.trace_zero]
  abel

/-- Conjugation by a self-adjoint involution preserves the
Hilbert--Schmidt inner product. -/
theorem gradingConjugation_hilbertSchmidtInner_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    (Gamma X Y : Matrix n n ℂ)
    (hGammaH : Gammaᴴ = Gamma) (hGamma2 : Gamma * Gamma = 1) :
    (((Gamma * X * Gamma)ᴴ) * (Gamma * Y * Gamma)).trace =
      (Xᴴ * Y).trace := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGammaH]
  have hmatrix :
      (Gamma * (Xᴴ * Gamma)) * (Gamma * Y * Gamma) =
        Gamma * (Xᴴ * Y) * Gamma := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Gamma Gamma (Y * Gamma), hGamma2,
      Matrix.one_mul]
  rw [hmatrix]
  rw [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Gamma ((Xᴴ * Y) * Gamma)]
  simp only [Matrix.mul_assoc]
  rw [hGamma2, Matrix.mul_one]

/-- The grading-even and grading-odd shortings are exactly orthogonal in the
Hilbert--Schmidt inner product. -/
theorem gradingEvenOdd_hilbertSchmidt_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (G Gamma : Matrix n n ℂ)
    (hGammaH : Gammaᴴ = Gamma) (hGamma2 : Gamma * Gamma = 1) :
    let evenPart := (2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)
    let oddPart := (2 : ℂ)⁻¹ • (G - Gamma * G * Gamma)
    (evenPartᴴ * oddPart).trace = 0 ∧
      (oddPartᴴ * evenPart).trace = 0 := by
  dsimp only
  let evenPart := (2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)
  let oddPart := (2 : ℂ)⁻¹ • (G - Gamma * G * Gamma)
  have hsplit := (smst_generator_projections (h := n)).2.1 G Gamma hGamma2
  have heven : Gamma * evenPart * Gamma = evenPart := hsplit.2.1
  have hodd : Gamma * oddPart * Gamma = -oddPart := hsplit.2.2
  have hinvariantEO := gradingConjugation_hilbertSchmidtInner_invariant
    Gamma evenPart oddPart hGammaH hGamma2
  rw [heven, hodd, Matrix.mul_neg, Matrix.trace_neg] at hinvariantEO
  have hEO : (evenPartᴴ * oddPart).trace = 0 := by
    simpa only [CharZero.neg_eq_self_iff] using hinvariantEO
  have hinvariantOE := gradingConjugation_hilbertSchmidtInner_invariant
    Gamma oddPart evenPart hGammaH hGamma2
  rw [hodd, heven, Matrix.conjTranspose_neg, Matrix.neg_mul,
    Matrix.trace_neg] at hinvariantOE
  have hOE : (oddPartᴴ * evenPart).trace = 0 := by
    simpa only [CharZero.neg_eq_self_iff] using hinvariantOE
  exact ⟨hEO, hOE⟩

/-- Exact three-term Hilbert--Schmidt budget: grading-even dynamics plus the
canonical finite-Dirac projection of the odd part plus its orthogonal extra
odd residue. -/
theorem gradedFiniteDirac_hilbertSchmidtBudget
    {n : Type*} [Fintype n] [DecidableEq n]
    (G Gamma Pi : Matrix n n ℂ)
    (hGammaH : Gammaᴴ = Gamma) (hGamma2 : Gamma * Gamma = 1)
    (hPiH : Piᴴ = Pi) (hPi2 : Pi * Pi = Pi) :
    let evenPart := (2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)
    let oddPart := (2 : ℂ)⁻¹ • (G - Gamma * G * Gamma)
    let canonicalDirac := Pi * oddPart
    let extraOdd := ((1 : Matrix n n ℂ) - Pi) * oddPart
    (Gᴴ * G).trace = (evenPartᴴ * evenPart).trace +
      (canonicalDiracᴴ * canonicalDirac).trace +
      (extraOddᴴ * extraOdd).trace := by
  dsimp only
  let evenPart := (2 : ℂ)⁻¹ • (G + Gamma * G * Gamma)
  let oddPart := (2 : ℂ)⁻¹ • (G - Gamma * G * Gamma)
  let canonicalDirac := Pi * oddPart
  let extraOdd := ((1 : Matrix n n ℂ) - Pi) * oddPart
  have hsplit := (smst_generator_projections (h := n)).2.1 G Gamma hGamma2
  have hsum : evenPart + oddPart = G := hsplit.1
  have horth := gradingEvenOdd_hilbertSchmidt_orthogonal
    G Gamma hGammaH hGamma2
  have hEO : (evenPartᴴ * oddPart).trace = 0 := by
    simpa only [evenPart, oddPart] using horth.1
  have hOE : (oddPartᴴ * evenPart).trace = 0 := by
    simpa only [evenPart, oddPart] using horth.2
  have hoddBudget := finiteDiracProjection_pythagoras
    Pi oddPart hPiH hPi2
  calc
    (Gᴴ * G).trace = ((evenPart + oddPart)ᴴ *
        (evenPart + oddPart)).trace := by rw [hsum]
    _ = (evenPartᴴ * evenPart).trace +
        (oddPartᴴ * oddPart).trace := by
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add]
      simp only [Matrix.trace_add, hEO, hOE, Matrix.trace_zero]
      abel
    _ = (evenPartᴴ * evenPart).trace +
        (canonicalDiracᴴ * canonicalDirac).trace +
        (extraOddᴴ * extraOdd).trace := by
      rw [hoddBudget.2.2.2]
      dsimp only [canonicalDirac, extraOdd]
      abel

/-- Zero Moore--Penrose provenance defect forces the complete odd generator
into the already derived finite-Dirac relation space.  Consequently its
canonical projection is itself and the extra odd residual vanishes. -/
theorem zeroOddProvenance_fixesFiniteDiracProjection
    {d e k : ℕ}
    (Pi : Matrix (Fin d) (Fin d) ℂ)
    (selected : Matrix (Fin d) (Fin e) ℂ)
    (completeOdd : Matrix (Fin d) (Fin k) ℂ)
    (hselected : Pi * selected = selected)
    (hzero : oddProvenanceDefect selected completeOdd = 0) :
    Pi * completeOdd = completeOdd ∧
      ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * completeOdd = 0 ∧
      ∃ coefficients : Matrix (Fin e) (Fin k) ℂ,
        completeOdd = selected * coefficients := by
  obtain ⟨coefficients, hfactor⟩ :=
    (oddProvenanceDefect_eq_zero_iff_rangeIncluded
      selected completeOdd).mp hzero
  have hfix : Pi * completeOdd = completeOdd := by
    rw [hfactor, ← Matrix.mul_assoc, hselected]
  refine ⟨hfix, ?_, coefficients, hfactor⟩
  rw [Matrix.sub_mul, Matrix.one_mul, hfix, sub_self]

/-- Once the finite-Dirac projector fixes the odd generator, its exact
Pythagorean budget has zero extra slot. -/
theorem zeroOddProvenance_finiteDiracBudget
    {d e k : ℕ}
    (Pi : Matrix (Fin d) (Fin d) ℂ)
    (selected : Matrix (Fin d) (Fin e) ℂ)
    (completeOdd : Matrix (Fin d) (Fin k) ℂ)
    (hPiH : Piᴴ = Pi) (hPi2 : Pi * Pi = Pi)
    (hselected : Pi * selected = selected)
    (hzero : oddProvenanceDefect selected completeOdd = 0) :
    let canonicalDirac := Pi * completeOdd
    let extraOdd := ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * completeOdd
    (completeOddᴴ * completeOdd).trace =
        (canonicalDiracᴴ * canonicalDirac).trace +
          (extraOddᴴ * extraOdd).trace ∧
      canonicalDirac = completeOdd ∧ extraOdd = 0 := by
  dsimp only
  have hfix := zeroOddProvenance_fixesFiniteDiracProjection
    Pi selected completeOdd hselected hzero
  have hbudget := finiteDiracProjection_pythagoras
    Pi completeOdd hPiH hPi2
  exact ⟨hbudget.2.2.2, hfix.1, hfix.2.1⟩

end NCG
