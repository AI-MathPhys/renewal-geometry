/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.PetzRecoveryExact

/-!
# The data-processing defect and the Petz sufficiency sandwich

Layer QS.2–QS.3 of `thm:accepted-Petz-sufficiency`.  The data-processing
defect is

`Δ_DPI(ρ∣σ;Φ) = D(ρ‖σ) − D(Φ_*ρ‖Φ_*σ)`.

Its nonnegativity (QS.2, Uhlmann monotonicity of the finite quantum
relative entropy under CPTP maps) enters as the single named analytic
interface hypothesis (`hDPI`); the record's sufficiency reasoning is then
proved exactly:

* `kraus_isHermitian`, `kraus_state`: channels transport Hermitian
  matrices and states;
* `deltaDPI`: the data-processing defect; `deltaDPI_nonneg` is QS.2 from
  the interface;
* `recovery_implies_deltaDPI_eq_zero`: **the sufficiency sandwich** — if
  the Petz map recovers `ρ`, then
  `D(ρ‖σ) ≥ D(Φ_*ρ‖Φ_*σ) ≥ D(R Φ_*ρ‖R Φ_*σ) = D(ρ‖σ)` pins the defect
  at zero (the forward direction of QS.3);
* `family_deltaDPI_eq_zero_of_recGram_eq_zero`: a vanishing recovery
  Gram (QS.4) kills every declared family defect.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n m κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype κ]
variable {σ : Matrix n n ℂ}

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem kraus_isHermitian (K : κ → Matrix m n ℂ) {ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) : (kraus K ρ).IsHermitian := by
  unfold kraus Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Channels transport states to states. -/
theorem kraus_state (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    (kraus K ρ).PosSemidef ∧ (kraus K ρ).trace = 1 :=
  ⟨kraus_posSemidef K hρ, by rw [kraus_trace K hK, h1]⟩

omit [Fintype m] [DecidableEq m] [Fintype κ] in
/-- The relative entropy transports along matrix equalities. -/
theorem relEntropy_congr {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ}
    (hρe : ρ₁ = ρ₂) (hσe : σ₁ = σ₂)
    (h₁ : ρ₁.IsHermitian) (h₂ : σ₁.IsHermitian)
    (h₁' : ρ₂.IsHermitian) (h₂' : σ₂.IsHermitian) :
    relEntropy h₁ h₂ = relEntropy h₁' h₂' := by
  subst hρe
  subst hσe
  rfl

/-- **The data-processing defect** `Δ_DPI(ρ∣σ;Φ)` (QS.2). -/
noncomputable def deltaDPI (K : κ → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hbρ : (kraus K ρ).IsHermitian) (hbσ : (kraus K σ).IsHermitian) : ℝ :=
  relEntropy hρ hσ - relEntropy hbρ hbσ

/-- **(QS.2)** from the disclosed Uhlmann monotonicity interface: the
data-processing defect is nonnegative. -/
theorem deltaDPI_nonneg (K : κ → Matrix m n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hbρ : (kraus K ρ).IsHermitian) (hbσ : (kraus K σ).IsHermitian)
    (hDPI : relEntropy hbρ hbσ ≤ relEntropy hρ hσ) :
    0 ≤ deltaDPI K hρ hσ hbρ hbσ := by
  unfold deltaDPI
  linarith

/-- **The Petz sufficiency sandwich** (the forward direction of QS.3):
Petz recovery of `ρ` plus two applications of the monotonicity interface
pin the data-processing defect at zero. -/
theorem recovery_implies_deltaDPI_eq_zero (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (hbρ : (kraus K ρ).IsHermitian)
    (hrec : petz K hσp hbar (kraus K ρ) = ρ)
    (hDPI₁ : relEntropy hbρ (kraus_isHermitian K hσp.1) ≤
      relEntropy hρ hσp.1)
    (hDPI₂ : ∀ (h₁ : (petz K hσp hbar (kraus K ρ)).IsHermitian)
        (h₂ : (petz K hσp hbar (kraus K σ)).IsHermitian),
      relEntropy h₁ h₂ ≤ relEntropy hbρ (kraus_isHermitian K hσp.1)) :
    deltaDPI K hρ hσp.1 hbρ (kraus_isHermitian K hσp.1) = 0 := by
  have hσfix : petz K hσp hbar (kraus K σ) = σ :=
    petz_recovers_reference K hσp hbar hK
  have h₁ : (petz K hσp hbar (kraus K ρ)).IsHermitian := by
    rw [hrec]
    exact hρ
  have h₂ : (petz K hσp hbar (kraus K σ)).IsHermitian := by
    rw [hσfix]
    exact hσp.1
  have hlow := hDPI₂ h₁ h₂
  have heq : relEntropy h₁ h₂ = relEntropy hρ hσp.1 :=
    relEntropy_congr hrec hσfix h₁ h₂ hρ hσp.1
  rw [heq] at hlow
  unfold deltaDPI
  linarith

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **(QS.4 saturates QS.2)**: a vanishing recovery Gram kills every
declared family defect. -/
theorem family_deltaDPI_eq_zero_of_recGram_eq_zero
    (K : κ → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hσp : σ.PosDef) (hbar : (kraus K σ).PosDef)
    {A : Type*} [Fintype A] [DecidableEq A] (ρfam : A → Matrix n n ℂ)
    (hfam : ∀ a, (ρfam a).IsHermitian)
    (hGram : recGram K hσp hbar ρfam = 0)
    (hDPI₁ : ∀ a, relEntropy (kraus_isHermitian K (hfam a))
      (kraus_isHermitian K hσp.1) ≤ relEntropy (hfam a) hσp.1)
    (hDPI₂ : ∀ a,
      ∀ (h₁ : (petz K hσp hbar (kraus K (ρfam a))).IsHermitian)
        (h₂ : (petz K hσp hbar (kraus K σ)).IsHermitian),
      relEntropy h₁ h₂ ≤ relEntropy (kraus_isHermitian K (hfam a))
        (kraus_isHermitian K hσp.1)) :
    ∀ a, deltaDPI K (hfam a) hσp.1 (kraus_isHermitian K (hfam a))
      (kraus_isHermitian K hσp.1) = 0 := fun a =>
  recovery_implies_deltaDPI_eq_zero K hK (hfam a) hσp hbar
    (kraus_isHermitian K (hfam a))
    ((recGram_eq_zero_iff K hσp hbar ρfam).mp hGram a)
    (hDPI₁ a) (hDPI₂ a)

end Petz
end NCG
