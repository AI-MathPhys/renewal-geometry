/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.DataProcessingExact

/-!
# The Petz sufficiency record, unconditional layer

With the data-processing inequality proved (`relEntropy_kraus_le`), the
interface hypotheses `hDPI₁`/`hDPI₂` of the Petz sufficiency sandwich are
discharged: QS.2, the forward direction of QS.3, and the family clause of
QS.4 of `thm:accepted-Petz-sufficiency` hold unconditionally for a
Kraus-presented CPTP map with faithful `σ` and `Φσ`.

* `dpi_discharge₁`, `dpi_discharge₂`: the two monotonicity applications
  of the sandwich — the second applied to the **Petz channel itself**
  through its proved Kraus presentation;
* `deltaDPI_nonneg_proved`: **QS.2** unconditionally;
* `recovery_deltaDPI_eq_zero_proved`: **QS.3, forward** unconditionally;
* `deltaDPI_eq_zero_iff_recovery_of_converse`: the QS.3 equivalence with
  the Petz equality theorem (`Δ = 0 → recovery`) as the single remaining
  disclosed interface hypothesis;
* `family_deltaDPI_eq_zero_proved`: **QS.4 kills the family defects**
  unconditionally.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable {σ : Matrix n n ℂ}

/-! ### The two discharged monotonicity applications -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The first monotonicity application of the sandwich, now proved:
`D(Φρ‖Φσ) ≤ D(ρ‖σ)`. -/
theorem dpi_discharge₁ (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef) :
    relEntropy (kraus_isHermitian K hρp.1) (kraus_isHermitian K hσp.1) ≤
      relEntropy hρp.1 hσp.1 :=
  relEntropy_kraus_le K hK hρp hσp (kraus_isHermitian K hρp.1) hbar

omit [DecidableEq κ] [Nonempty κ] in
/-- The Kraus presentation of the Petz map is the Petz map. -/
theorem kraus_petzKraus (K : κ → Matrix m n ℂ) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef) (y : Matrix m m ℂ) :
    kraus (petzKraus K hσp hbar) y = petz K hσp hbar y := by
  rw [petz_eq_kraus]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option maxHeartbeats 1600000 in -- Petz-channel data processing
/-- The second monotonicity application of the sandwich, now proved: the
data-processing inequality applied to the **Petz channel** through its
Kraus presentation, `D(RΦρ‖RΦσ) ≤ D(Φρ‖Φσ)`. -/
theorem dpi_discharge₂ (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef) :
    ∀ (h₁ : (petz K hσp hbar (kraus K ρ)).IsHermitian)
      (h₂ : (petz K hσp hbar (kraus K σ)).IsHermitian),
      relEntropy h₁ h₂ ≤
        relEntropy (kraus_isHermitian K hρp.1)
          (kraus_isHermitian K hσp.1) := by
  intro h₁ h₂
  have hHermρ : (kraus (petzKraus K hσp hbar) (kraus K ρ)).IsHermitian :=
    kraus_isHermitian _ (kraus_isHermitian K hρp.1)
  have hPDσ : (kraus (petzKraus K hσp hbar) (kraus K σ)).PosDef := by
    rw [kraus_petzKraus, petz_recovers_reference K hσp hbar hK]
    exact hσp
  have h := relEntropy_kraus_le (petzKraus K hσp hbar)
    (petz_kraus_sum K hσp hbar) (kraus_posSemidef K hρp) hbar
    hHermρ hPDσ
  have hcongr : relEntropy hHermρ hPDσ.1 = relEntropy h₁ h₂ :=
    relEntropy_congr (kraus_petzKraus K hσp hbar (kraus K ρ))
      (kraus_petzKraus K hσp hbar (kraus K σ)) hHermρ hPDσ.1 h₁ h₂
  rw [hcongr] at h
  exact h

/-! ### QS.2, unconditional -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.2 proved**: the data-processing defect is nonnegative,
unconditionally. -/
theorem deltaDPI_nonneg_proved (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef) :
    0 ≤ deltaDPI K hρp.1 hσp.1 (kraus_isHermitian K hρp.1)
      (kraus_isHermitian K hσp.1) :=
  deltaDPI_nonneg K hρp.1 hσp.1 _ _ (dpi_discharge₁ K hK hρp hσp hbar)

/-! ### QS.3 forward, unconditional -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.3 forward proved**: Petz recovery of `ρ` pins the defect at
zero, unconditionally. -/
theorem recovery_deltaDPI_eq_zero_proved (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef)
    (hrec : petz K hσp hbar (kraus K ρ) = ρ) :
    deltaDPI K hρp.1 hσp.1 (kraus_isHermitian K hρp.1)
      (kraus_isHermitian K hσp.1) = 0 :=
  recovery_implies_deltaDPI_eq_zero K hK hρp.1 hσp hbar
    (kraus_isHermitian K hρp.1) hrec
    (dpi_discharge₁ K hK hρp hσp hbar)
    (dpi_discharge₂ K hK hρp hσp hbar)

/-! ### The QS.3 equivalence at the disclosed interface -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **The QS.3 equivalence**: `Δ_DPI = 0 ↔ Petz recovery`, with the
converse (the Petz equality theorem) as the single remaining disclosed
interface hypothesis `hconv`. -/
theorem deltaDPI_eq_zero_iff_recovery_of_converse (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ : Matrix n n ℂ}
    (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef)
    (hconv : deltaDPI K hρp.1 hσp.1 (kraus_isHermitian K hρp.1)
        (kraus_isHermitian K hσp.1) = 0 →
      petz K hσp hbar (kraus K ρ) = ρ) :
    deltaDPI K hρp.1 hσp.1 (kraus_isHermitian K hρp.1)
        (kraus_isHermitian K hσp.1) = 0 ↔
      petz K hσp hbar (kraus K ρ) = ρ :=
  ⟨hconv, recovery_deltaDPI_eq_zero_proved K hK hρp hσp hbar⟩

/-! ### QS.4 family clause, unconditional -/

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **QS.4 kills the family defects, unconditionally**: a vanishing
recovery Gram pins every declared family defect at zero. -/
theorem family_deltaDPI_eq_zero_proved (K : κ → Matrix m n ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hσp : σ.PosDef)
    (hbar : (kraus K σ).PosDef)
    {A : Type*} [Fintype A] [DecidableEq A] (ρfam : A → Matrix n n ℂ)
    (hfam : ∀ a, (ρfam a).PosSemidef)
    (hGram : recGram K hσp hbar ρfam = 0) :
    ∀ a, deltaDPI K (hfam a).1 hσp.1 (kraus_isHermitian K (hfam a).1)
      (kraus_isHermitian K hσp.1) = 0 :=
  family_deltaDPI_eq_zero_of_recGram_eq_zero K hK hσp hbar ρfam
    (fun a => (hfam a).1) hGram
    (fun a => dpi_discharge₁ K hK (hfam a) hσp hbar)
    (fun a => dpi_discharge₂ K hK (hfam a) hσp hbar)

end Petz
end NCG
