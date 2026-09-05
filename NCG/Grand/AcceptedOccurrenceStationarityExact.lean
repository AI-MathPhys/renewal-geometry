import NCG.Grand.EntropicProjectionExact
import NCG.Grand.FiniteGibbsActionGap
import NCG.Grand.AcceptedBregmanStationarityExact

/-!
# Occurrence control of the accepted common-action stationarity gap

This file supplies the missing AO.14--AO.16 assembly.  It first proves that a
stationary average of row KL divergences is exactly the KL divergence of the
joint coupling with common source marginal.  Entropic-projection Pythagoras
then splits that quantity into occurrence and selection residuals.  The
occurrence-energy bound and the proved Bregman stationarity estimate compose
to give AO.15 and AO.16.
-/

open Finset

namespace NCG.AcceptedOccurrenceStationarity

open NCG.EntropicProjection

/-- Coupling obtained from a source law and a transition row. -/
def jointRow {X : Type*} (ν : X → ℝ) (K : X → X → ℝ) : X × X → ℝ :=
  fun p => ν p.1 * K p.1 p.2

/-- With a common strictly positive source marginal, joint KL is exactly the
source-weighted average of row KL divergences. -/
theorem jointKL_eq_average_rowKL
    {X : Type*} [Fintype X]
    (ν : X → ℝ) (K Q : X → X → ℝ)
    (hν : ∀ x, 0 < ν x) (hK : ∀ x y, 0 < K x y)
    (hQ : ∀ x y, 0 < Q x y) :
    EntropicProjection.kl (jointRow ν K) (jointRow ν Q) =
      ∑ x, ν x * NCG.finiteKL (K x) (Q x) := by
  classical
  unfold EntropicProjection.kl NCG.finiteKL
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change EntropicProjection.klTerm (ν x * K x y) (ν x * Q x y) =
    ν x * (K x y * Real.log (K x y / Q x y))
  rw [EntropicProjection.klTerm_eq
    (mul_nonneg (hν x).le (hK x y).le) (mul_pos (hν x) (hQ x y))]
  have hratio : (ν x * K x y) / (ν x * Q x y) = K x y / Q x y := by
    field_simp [(hν x).ne', (hQ x y).ne']
  rw [hratio]
  ring

/-- AO.14: Gibbs action gap equals `η⁻¹` times occurrence plus selection
residual, derived from the joint/row identity and information Pythagoras. -/
theorem observed_gibbs_gap_split
    {X : Type*} [Fintype X]
    {support : Set (X × X)} {ν : X → ℝ}
    (K Q : X → X → ℝ) (projection : X × X → ℝ)
    (a b : X → ℝ) (η : ℝ)
    (hν : ∀ x, 0 < ν x) (hK : ∀ x y, 0 < K x y)
    (hQ : ∀ x y, 0 < Q x y)
    (hprojection : projection ∈ feasible support ν ν)
    (hobserved : jointRow ν K ∈ feasible support ν ν)
    (hGibbs : IsGibbsOn (jointRow ν Q) a b (E := support) projection) :
    η⁻¹ * (∑ x, ν x * NCG.finiteKL (K x) (Q x)) =
      η⁻¹ * (EntropicProjection.kl projection (jointRow ν Q) +
        EntropicProjection.kl (jointRow ν K) projection) := by
  rw [← jointKL_eq_average_rowKL ν K Q hν hK hQ]
  rw [EntropicProjection.kl_pythagoras (jointRow ν Q) a b
    (fun p => mul_pos (hν p.1) (hQ p.1 p.2))
    hprojection hGibbs hobserved]
  ring

/-- AO.15 follows monotonically from the occurrence-energy estimate. -/
theorem observed_gibbs_gap_le_energy
    (η occurrence selection energy : ℝ) (hη : 0 < η)
    (hocc : occurrence ≤ energy) :
    η⁻¹ * (occurrence + selection) ≤ η⁻¹ * (energy + selection) := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
  linarith

/-- AO.16: compose the already-proved accepted-Bregman estimate
`represented ≤ C * gap` with AO.15.  The Bregman premise is exactly the output
of `AcceptedBregmanStationarity.integral_stationarity_form_le`, cited by the
ledger, rather than an assumed occurrence inequality. -/
theorem represented_stationarity_le
    (η occurrence selection energy C represented : ℝ)
    (hη : 0 < η) (hC : 0 ≤ C)
    (hocc : occurrence ≤ energy)
    (hBregman : represented ≤ C * (η⁻¹ * (occurrence + selection))) :
    represented ≤ C / η * (energy + selection) := by
  calc
    represented ≤ C * (η⁻¹ * (occurrence + selection)) := hBregman
    _ ≤ C * (η⁻¹ * (energy + selection)) :=
      mul_le_mul_of_nonneg_left
        (observed_gibbs_gap_le_energy η occurrence selection energy hη hocc) hC
    _ = C / η * (energy + selection) := by
      field_simp [hη.ne']

/-- On the entropy-optimal selected branch, the selection residual vanishes
exactly when the observed coupling equals the entropic projection. -/
theorem selection_zero_iff_observed_eq_projection
    {X : Type*} [Fintype X]
    {support : Set (X × X)} {ν : X → ℝ}
    (R projection observed : X × X → ℝ) (a b : X → ℝ)
    (hR : ∀ p, 0 < R p)
    (hprojection : projection ∈ feasible support ν ν)
    (hGibbs : IsGibbsOn R a b (E := support) projection)
    (hobserved : observed ∈ feasible support ν ν) :
    EntropicProjection.kl observed projection = 0 ↔ observed = projection :=
  EntropicProjection.selection_residual_eq_zero_iff R a b hR
    hprojection hGibbs hobserved

/-- Bundled scalar assembly of AO.14--AO.16 after the two substantive finite
theorems (Pythagoras and Bregman stationarity) have supplied their outputs. -/
theorem occurrence_control_of_stationarity_gap
    (η occurrence selection energy C represented : ℝ)
    (hη : 0 < η) (hC : 0 ≤ C) (hocc : occurrence ≤ energy)
    (hBregman : represented ≤ C * (η⁻¹ * (occurrence + selection))) :
    η⁻¹ * (occurrence + selection) ≤ η⁻¹ * (energy + selection) ∧
      represented ≤ C / η * (energy + selection) := by
  exact ⟨observed_gibbs_gap_le_energy η occurrence selection energy hη hocc,
    represented_stationarity_le η occurrence selection energy C represented
      hη hC hocc hBregman⟩

end NCG.AcceptedOccurrenceStationarity
