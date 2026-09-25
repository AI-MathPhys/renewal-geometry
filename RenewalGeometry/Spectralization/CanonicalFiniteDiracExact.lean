/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.SaturatedFiniteDiracGenerator

/-!
# Canonical finite Dirac operator (`prop:finite-dirac`)

`prop:finite-dirac` of the spacetime–gauge duality manuscript.  Let `A` be a source-saturated
self-adjoint full-cell generator on the common carrier `ℂ^n` with grading `Γ` (`Γᴴ = Γ`,
`Γ² = 1`, `P_± = (1 ± Γ)/2`).  Its grading-odd part is `D_F = P₋ A P₊ + P₊ A P₋`
(`finiteDirac`, `eq:finite-dirac`).

* `finiteDirac_eq_oddPart`, `finiteDirac_conjTranspose`, `finiteDirac_odd`: `D_F` is the
  odd component `(A - Γ A Γ)/2`, self-adjoint and grading-odd;
* `oddPart_unique`: the grading decomposition `A = E + O` (`E` even, `O` odd) is unique, so the
  odd component is fixed by the represented generator: `O = D_F`;
* `finiteDirac_unique_of_zero_innovation`: **source minimality** — on an odd-provenance-complete
  branch (the range of `D_F` lies in the saturated represented range `Ran Pr`, `Pr D_F = D_F`),
  any self-adjoint generator `B` with the same represented action (`B Pr = D_F Pr`) and vanishing
  orthogonal innovation (`(1-Pr) B (1-Pr) = 0`) coincides with `D_F`;
* `typed_contractions`: for a typed resolution of the identity `∑_t P_t = 1` by orthogonal
  projectors (the modules of `eq:SM-types` in one common generation frame), the typed
  contractions `Y_{tt'} = P_t D_F P_{t'}` (Yukawa blocks for `t ≠ t'`, Majorana block for
  `t = t'`) recover `D_F = ∑_{t,t'} Y_{tt'}`, pair Hermitian-conjugately `Y_{tt'}ᴴ = Y_{t't}`,
  and are grading-odd whenever the type projectors commute with `Γ`;
* `canonical_finite_dirac`: the assembled statement.

The saturation input "the full-cell carrier is reducing" is
`stabilizedIsometricCarrier_reduces` (`SaturatedFiniteDiracGenerator.lean`), and the
odd-provenance-completeness hypothesis `Pr D_F = D_F` is produced from zero odd-provenance defect
by `zeroOddProvenance_fixesFiniteDiracProjection`.
-/

open Matrix

namespace RenewalGeometry
namespace CanonicalFiniteDirac

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The even grading projector `P₊ = (1 + Γ)/2`. -/
noncomputable def Pplus (Γ : Matrix n n ℂ) : Matrix n n ℂ := (2 : ℂ)⁻¹ • (1 + Γ)

/-- The odd grading projector `P₋ = (1 - Γ)/2`. -/
noncomputable def Pminus (Γ : Matrix n n ℂ) : Matrix n n ℂ := (2 : ℂ)⁻¹ • (1 - Γ)

/-- The finite Dirac operator `D_F = P₋ A P₊ + P₊ A P₋` (`eq:finite-dirac`). -/
noncomputable def finiteDirac (Γ A : Matrix n n ℂ) : Matrix n n ℂ :=
  Pminus Γ * A * Pplus Γ + Pplus Γ * A * Pminus Γ

/-- `D_F` is the grading-odd component `(A - Γ A Γ)/2` of `A`. -/
theorem finiteDirac_eq_oddPart (Γ A : Matrix n n ℂ) :
    finiteDirac Γ A = (2 : ℂ)⁻¹ • (A - Γ * A * Γ) := by
  have h : (1 - Γ) * A * (1 + Γ) + (1 + Γ) * A * (1 - Γ)
      = (A - Γ * A * Γ) + (A - Γ * A * Γ) := by noncomm_ring
  simp only [finiteDirac, Pplus, Pminus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← smul_add]
  rw [h, ← two_smul ℂ (A - Γ * A * Γ), smul_smul]
  congr 1
  norm_num

/-- `D_F` is self-adjoint when `A` and `Γ` are. -/
theorem finiteDirac_conjTranspose (Γ A : Matrix n n ℂ) (hΓH : Γᴴ = Γ) (hA : Aᴴ = A) :
    (finiteDirac Γ A)ᴴ = finiteDirac Γ A := by
  rw [finiteDirac_eq_oddPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hΓH, hA, Matrix.mul_assoc]
  congr 1
  simp

/-- `D_F` is grading-odd: `Γ D_F Γ = -D_F`. -/
theorem finiteDirac_odd (Γ A : Matrix n n ℂ) (hΓ2 : Γ * Γ = 1) :
    Γ * finiteDirac Γ A * Γ = -finiteDirac Γ A := by
  rw [finiteDirac_eq_oddPart]
  exact ((smst_generator_projections (h := n)).2.1 A Γ hΓ2).2.2

/-- **Uniqueness of the grading decomposition**: if `A = E + O` with `E` grading-even and `O`
grading-odd, then `O = D_F` and `E = A - D_F`.  The odd component is fixed by the represented
generator. -/
theorem oddPart_unique (Γ A E O : Matrix n n ℂ) (hsum : A = E + O)
    (hE : Γ * E * Γ = E) (hO : Γ * O * Γ = -O) :
    O = finiteDirac Γ A ∧ E = A - finiteDirac Γ A := by
  have hOO : A - Γ * A * Γ = O + O := by
    rw [hsum, Matrix.mul_add, Matrix.add_mul, hE, hO]
    abel
  have hO' : O = finiteDirac Γ A := by
    rw [finiteDirac_eq_oddPart, hOO, ← two_smul ℂ O, smul_smul]
    norm_num
  refine ⟨hO', ?_⟩
  rw [← hO', hsum]
  abel

/-- **Source minimality of `D_F`.**  Let `Pr` be the orthogonal projector onto the saturated
represented range.  If `D` (the finite Dirac operator) is self-adjoint with `Pr D = D`
(odd-provenance completeness: its range lies in the represented range), and `B` is any
self-adjoint generator with the same represented action `B Pr = D Pr` and zero orthogonal
innovation `(1 - Pr) B (1 - Pr) = 0`, then `B = D`. -/
theorem finiteDirac_unique_of_zero_innovation (Pr D B : Matrix n n ℂ)
    (hPrH : Prᴴ = Pr) (hPr2 : Pr * Pr = Pr) (hD : Dᴴ = D) (hB : Bᴴ = B)
    (hcomplete : Pr * D = D) (hagree : B * Pr = D * Pr)
    (hinnov : (1 - Pr) * B * (1 - Pr) = 0) : B = D := by
  have hdecomp : B = Pr * B * Pr + Pr * B * (1 - Pr) + (1 - Pr) * B * Pr + (1 - Pr) * B * (1 - Pr) := by
    noncomm_ring
  have h1 : Pr * B * Pr = Pr * D * Pr := by
    rw [Matrix.mul_assoc, hagree, ← Matrix.mul_assoc]
  have h3 : (1 - Pr) * B * Pr = (1 - Pr) * D * Pr := by
    rw [Matrix.mul_assoc, hagree, ← Matrix.mul_assoc]
  have hQH : (1 - Pr)ᴴ = 1 - Pr := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPrH]
  have h2 : Pr * B * (1 - Pr) = Pr * D * (1 - Pr) := by
    have h3' := congrArg Matrix.conjTranspose h3
    simp only [Matrix.conjTranspose_mul, hQH, hPrH, hB, hD] at h3'
    simpa only [Matrix.mul_assoc] using h3'
  have h0 : (1 - Pr) * D * Pr = 0 := by
    rw [← hcomplete, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPr2, sub_self,
      Matrix.zero_mul, Matrix.zero_mul]
  rw [hdecomp, h1, h2, h3, hinnov, h0]
  have hfinal : Pr * D * Pr + Pr * D * (1 - Pr) = Pr * D := by noncomm_ring
  rw [add_zero, add_zero, hfinal, hcomplete]

/-- **Typed contractions.**  For a typed resolution of the identity `∑_t P_t = 1` by
self-adjoint projectors, the typed blocks `Y_{tt'} = P_t D P_{t'}` recover `D`, pair
Hermitian-conjugately, and are grading-odd when the type projectors commute with `Γ` and `D`
is odd. -/
theorem typed_contractions {τ : Type*} [Fintype τ] (P : τ → Matrix n n ℂ)
    (hsum : ∑ t, P t = 1) (hP : ∀ t, (P t)ᴴ = P t) (Γ D : Matrix n n ℂ) (hD : Dᴴ = D) :
    D = ∑ t, ∑ t', P t * D * P t'
    ∧ (∀ t t', (P t * D * P t')ᴴ = P t' * D * P t)
    ∧ ((∀ t, Γ * P t = P t * Γ) → Γ * D * Γ = -D →
        ∀ t t', Γ * (P t * D * P t') * Γ = -(P t * D * P t')) := by
  refine ⟨?_, ?_, ?_⟩
  · calc D = (∑ t, P t) * D * (∑ t', P t') := by rw [hsum, Matrix.one_mul, Matrix.mul_one]
      _ = ∑ t, ∑ t', P t * D * P t' := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
  · intro t t'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hP, hD, Matrix.mul_assoc]
  · intro hcomm hodd t t'
    calc Γ * (P t * D * P t') * Γ = (Γ * P t) * D * (P t' * Γ) := by
          simp only [Matrix.mul_assoc]
      _ = (P t * Γ) * D * (Γ * P t') := by rw [hcomm t, hcomm t']
      _ = P t * (Γ * D * Γ) * P t' := by simp only [Matrix.mul_assoc]
      _ = -(P t * D * P t') := by rw [hodd, Matrix.mul_neg, Matrix.neg_mul]

/-- **`prop:finite-dirac` (Canonical finite Dirac operator), assembled.**  For a self-adjoint
full-cell generator `A` with grading `Γ`: `D_F` is the self-adjoint grading-odd component of
`A`, it is the unique odd summand of any even/odd decomposition of `A`, on an
odd-provenance-complete branch (`Pr D_F = D_F`) it is the unique self-adjoint generator with its
represented action and zero orthogonal innovation, and its typed contractions onto a typed
resolution of the identity recover it block by block with Hermitian pairing. -/
theorem canonical_finite_dirac (Γ A : Matrix n n ℂ) (hΓH : Γᴴ = Γ) (hΓ2 : Γ * Γ = 1)
    (hA : Aᴴ = A) :
    (finiteDirac Γ A)ᴴ = finiteDirac Γ A
    ∧ Γ * finiteDirac Γ A * Γ = -finiteDirac Γ A
    ∧ finiteDirac Γ A = (2 : ℂ)⁻¹ • (A - Γ * A * Γ)
    ∧ (∀ E O : Matrix n n ℂ, A = E + O → Γ * E * Γ = E → Γ * O * Γ = -O →
        O = finiteDirac Γ A)
    ∧ (∀ Pr B : Matrix n n ℂ, Prᴴ = Pr → Pr * Pr = Pr → Bᴴ = B →
        Pr * finiteDirac Γ A = finiteDirac Γ A →
        B * Pr = finiteDirac Γ A * Pr → (1 - Pr) * B * (1 - Pr) = 0 → B = finiteDirac Γ A)
    ∧ (∀ {τ : Type} [Fintype τ] (P : τ → Matrix n n ℂ), ∑ t, P t = 1 → (∀ t, (P t)ᴴ = P t) →
        finiteDirac Γ A = ∑ t, ∑ t', P t * finiteDirac Γ A * P t'
        ∧ (∀ t t', (P t * finiteDirac Γ A * P t')ᴴ = P t' * finiteDirac Γ A * P t)
        ∧ ((∀ t, Γ * P t = P t * Γ) →
            ∀ t t', Γ * (P t * finiteDirac Γ A * P t') * Γ
              = -(P t * finiteDirac Γ A * P t'))) := by
  have hDH := finiteDirac_conjTranspose Γ A hΓH hA
  refine ⟨hDH, finiteDirac_odd Γ A hΓ2, finiteDirac_eq_oddPart Γ A,
    fun E O hsum hE hO => (oddPart_unique Γ A E O hsum hE hO).1,
    fun Pr B hPrH hPr2 hB hcomplete hagree hinnov =>
      finiteDirac_unique_of_zero_innovation Pr (finiteDirac Γ A) B hPrH hPr2 hDH hB hcomplete
        hagree hinnov,
    fun P hsum hP => ?_⟩
  obtain ⟨h1, h2, h3⟩ := typed_contractions P hsum hP Γ (finiteDirac Γ A) hDH
  exact ⟨h1, h2, fun hcomm => h3 hcomm (finiteDirac_odd Γ A hΓ2)⟩

end CanonicalFiniteDirac
end RenewalGeometry
