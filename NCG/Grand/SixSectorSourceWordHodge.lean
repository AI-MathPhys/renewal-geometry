import NCG.Grand.GTSectorResolution
import NCG.Grand.CompletedEulerSingularSupportShortAndOrder

/-!
# Six-sector source-word--transport--Hodge resolution

This file instantiates the generic finite sector resolution at the six literal
sectors of `thm:GT-source-word-Hodge`: missing algebraic word source, hidden
record source, missing transport source, covariant demand, open boundary
current, and boundary-free cycle current.  It also closes the converse
finite-domination criterion on a singular physical-action support.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG
namespace SixSectorSourceWordHodge

/-- The literal six SC.4 sectors. -/
abbrev Sector := Fin 6

def alg : Sector := 0
def hidden : Sector := 1
def transport : Sector := 2
def demand : Sector := 3
def openCurrent : Sector := 4
def cycle : Sector := 5

/-- An independently constructed algebra/record/transport/Hodge resolution.
The fields record exactly what the successive orthogonal projections prove:
self-adjoint idempotence and resolution of the identity. -/
structure Resolution (n : Type) [Fintype n] [DecidableEq n] where
  projection : Sector → Matrix n n ℂ
  sum_eq_one : ∑ s, projection s = 1
  selfAdjoint : ∀ s, (projection s)ᴴ = projection s
  idempotent : ∀ s, projection s * projection s = projection s

variable {n m : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- Gram contributed by one named resolved source sector. -/
def sectorGram (R : Resolution n) (W : Matrix n m ℂ) (s : Sector) :
    Matrix m m ℂ :=
  Wᴴ * R.projection s * W

abbrev algebraicInnovation (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W alg
abbrev hiddenInnovation (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W hidden
abbrev transportInnovation (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W transport
abbrev demandGram (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W demand
abbrev openCurrentGram (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W openCurrent
abbrev cycleGram (R : Resolution n) (W : Matrix n m ℂ) :=
  sectorGram R W cycle

/-- The first three terms are the unresolved source defect. -/
def sourceDefectGram (R : Resolution n) (W : Matrix n m ℂ) : Matrix m m ℂ :=
  algebraicInnovation R W + hiddenInnovation R W + transportInnovation R W

/-- The last three terms are the physical covariant Hodge action. -/
def physicalActionGram (R : Resolution n) (W : Matrix n m ℂ) : Matrix m m ℂ :=
  demandGram R W + openCurrentGram R W + cycleGram R W

/-- **SC.4, literal six-term form.** -/
theorem six_term_source_word_Hodge
    (R : Resolution n) (W : Matrix n m ℂ) :
    Wᴴ * W =
      algebraicInnovation R W + hiddenInnovation R W +
        transportInnovation R W + demandGram R W +
          openCurrentGram R W + cycleGram R W := by
  have h := (gt_sector_resolution R.projection W R.sum_eq_one
    R.selfAdjoint R.idempotent).1
  rw [Fin.sum_univ_six] at h
  simpa [sectorGram, alg, hidden, transport, demand, openCurrent, cycle] using h

/-- Every one of the literal six terms is positive semidefinite and vanishes
exactly when its resolved projector annihilates the source synthesis. -/
theorem six_sector_positive_and_zero_iff
    (R : Resolution n) (W : Matrix n m ℂ) :
    (∀ s, (sectorGram R W s).PosSemidef) ∧
      ∀ s, sectorGram R W s = 0 ↔ R.projection s * W = 0 := by
  have h := gt_sector_resolution R.projection W R.sum_eq_one
    R.selfAdjoint R.idempotent
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem sourceDefectGram_posSemidef
    (R : Resolution n) (W : Matrix n m ℂ) :
    (sourceDefectGram R W).PosSemidef := by
  have h := (six_sector_positive_and_zero_iff R W).1
  exact ((h alg).add (h hidden)).add (h transport)

theorem physicalActionGram_posSemidef
    (R : Resolution n) (W : Matrix n m ℂ) :
    (physicalActionGram R W).PosSemidef := by
  have h := (six_sector_positive_and_zero_iff R W).1
  exact ((h demand).add (h openCurrent)).add (h cycle)

open RelativeMetricSupportDensity
open CompletedEulerSingularSupport

/-- **SC.4 domination criterion and sharp constant.**  A finite physical-action
domination exists iff every zero-action direction has zero source defect.  On
that branch the norm of the support-relative density is the exact least
admissible constant. -/
theorem domination_iff_kernel_and_sharp
    (R : Resolution n) (W : Matrix n m ℂ)
    (D : SupportData (physicalActionGram R W)) :
    let A := sourceDefectGram R W
    let B := physicalActionGram R W
    ((∃ c : ℝ, 0 ≤ c ∧ (((c : ℂ) • B) - A).PosSemidef) ↔
      ∀ x : m → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0)
    ∧ ((∀ x : m → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0) →
      ∀ c : ℝ, 0 ≤ c →
        ((((c : ℂ) • B) - A).PosSemidef ↔
          ‖relativeDensity D A‖ ≤ c)) := by
  dsimp only
  let A := sourceDefectGram R W
  have hA : A.PosSemidef := sourceDefectGram_posSemidef R W
  have hsupport :
      kernelDefect D A = 0 ↔
        ∀ x : m → ℂ, physicalActionGram R W *ᵥ x = 0 → A *ᵥ x = 0 := by
    exact (kernelDefect_eq_zero_iff_supported D hA).trans
      (kernelIncluded_iff_supported D hA).symm
  constructor
  · exact (exists_domination_iff_kernelDefect_zero D hA).trans hsupport
  · intro hker c hc
    have hdef : kernelDefect D A = 0 := hsupport.mpr hker
    exact (sharp_domination_on_zero_defect D hA hdef).2 c hc

/-- Complete finite bundle for the manuscript theorem. -/
theorem source_word_transport_Hodge_identity
    (R : Resolution n) (W : Matrix n m ℂ)
    (D : SupportData (physicalActionGram R W)) :
    Wᴴ * W =
      algebraicInnovation R W + hiddenInnovation R W +
        transportInnovation R W + demandGram R W +
          openCurrentGram R W + cycleGram R W
    ∧ (∀ s, (sectorGram R W s).PosSemidef)
    ∧ ((∃ c : ℝ, 0 ≤ c ∧
        (((c : ℂ) • physicalActionGram R W) - sourceDefectGram R W).PosSemidef) ↔
      ∀ x : m → ℂ, physicalActionGram R W *ᵥ x = 0 →
        sourceDefectGram R W *ᵥ x = 0) := by
  exact ⟨six_term_source_word_Hodge R W,
    (six_sector_positive_and_zero_iff R W).1,
    (domination_iff_kernel_and_sharp R W D).1⟩

end SixSectorSourceWordHodge
end NCG
