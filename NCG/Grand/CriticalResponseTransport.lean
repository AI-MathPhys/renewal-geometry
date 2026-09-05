import NCG.Grand.WeightedRegularizationConvergence
import NCG.Grand.GreenLocalityLaplaceBounds

/-!
# Cauchy transport of critical local responses

Cross-cutoff holomorphic defects are encoded as weighted difference packets.
The vector-valued Cauchy bounds control their first and mixed derivatives.
Summable adjacent defects then give unique limits in the complete weighted
Banach carrier; the same summable-increment argument applies after the
Laplace--Green transform.
-/

open Filter Set

noncomputable section

namespace NCG
namespace CriticalResponseTransport

open CriticalWeightedResponseLocality
open WeightedRegularizationConvergence

universe u v w

variable {Q : Type u} [Nonempty Q]
variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]
variable {Region : Type w}

/-- A weighted packet whose weights act identically realizes its weighted
supremum as the ambient Banach norm. -/
theorem weightedNorm_identity
    (P : Packet Q B Region) (T : B)
    (hweight : ∀ q, P.weight q T = T) :
    weightedNorm (fun q => P.weight q T) = ‖T‖ := by
  apply le_antisymm
  · apply weightedNorm_le
    intro q
    rw [hweight q]
  · obtain ⟨q⟩ := ‹Nonempty Q›
    have hB : BddAbove
        (Set.range fun q' => ‖P.weight q' T‖) := by
      refine ⟨‖T‖, ?_⟩
      rintro _ ⟨q', rfl⟩
      change ‖P.weight q' T‖ ≤ ‖T‖
      exact le_of_eq (congrArg norm (hweight q'))
    calc
      ‖T‖ = ‖P.weight q T‖ := congrArg norm (hweight q).symm
      _ ≤ weightedNorm (fun q' => P.weight q' T) :=
        le_csSup hB ⟨q, rfl⟩

/-- Exact Cauchy transport bounds for one cross-cutoff defect packet. -/
theorem weighted_critical_transport_bounds
    (D : Packet Q B Region) {eps rhoZ rhoW : ℝ}
    (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (holo : HolomorphicOnClosedPolydisc D rhoZ rhoW)
    (hboundary : HasWeightedCollar D rhoZ rhoW eps 0 0)
    (hweight : ∀ q T, D.weight q T = T) :
    ‖D.firstResponse‖ ≤ eps / rhoZ ∧
      ‖D.pairResponse‖ ≤ eps / (rhoZ * rhoW) := by
  have h := critical_weighted_bounds D hrhoZ hrhoW holo hboundary
  rw [weightedNorm_identity D D.firstResponse
      (fun q => hweight q D.firstResponse),
    weightedNorm_identity D D.pairResponse
      (fun q => hweight q D.pairResponse)] at h
  simpa using h

/-- Summable cross-cutoff holomorphic defects make the pulled-back first and
pair critical responses converge uniquely in the complete weighted carrier. -/
theorem weighted_critical_transport_limits
    (D : ℕ → Packet Q B Region) (first pair : ℕ → B)
    (eps : ℕ → ℝ) {rhoZ rhoW : ℝ}
    (hrhoZ : 0 < rhoZ) (hrhoW : 0 < rhoW)
    (holo : ∀ n, HolomorphicOnClosedPolydisc (D n) rhoZ rhoW)
    (hboundary : ∀ n, HasWeightedCollar (D n) rhoZ rhoW (eps n) 0 0)
    (hweight : ∀ n q T, (D n).weight q T = T)
    (hfirst : ∀ n, (D n).firstResponse = first (n + 1) - first n)
    (hpair : ∀ n, (D n).pairResponse = pair (n + 1) - pair n)
    (hsum : Summable eps) :
    (∃ firstLimit : B, Tendsto first atTop (nhds firstLimit)) ∧
      (∃ pairLimit : B, Tendsto pair atTop (nhds pairLimit)) := by
  have hb : ∀ n,
      ‖first (n + 1) - first n‖ ≤ eps n / rhoZ ∧
      ‖pair (n + 1) - pair n‖ ≤ eps n / (rhoZ * rhoW) := by
    intro n
    have h := weighted_critical_transport_bounds (D n)
      hrhoZ hrhoW (holo n) (hboundary n) (hweight n)
    simpa [hfirst n, hpair n] using h
  have hsumFirst : Summable (fun n => eps n / rhoZ) := by
    simpa [div_eq_mul_inv] using hsum.mul_right rhoZ⁻¹
  have hsumPair : Summable (fun n => eps n / (rhoZ * rhoW)) := by
    simpa [div_eq_mul_inv] using hsum.mul_right (rhoZ * rhoW)⁻¹
  constructor
  · exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable
        (fun n => eps n / rhoZ)
        (fun n => by
          simpa [dist_eq_norm, norm_sub_rev] using (hb n).1)
        hsumFirst)
  · exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable
        (fun n => eps n / (rhoZ * rhoW))
        (fun n => by
          simpa [dist_eq_norm, norm_sub_rev] using (hb n).2)
        hsumPair)

/-- Once time integration supplies summable adjacent Green defects, fixed-mass
Green responses converge uniquely in the same complete weighted carrier.  The
hypothesis is discharged by the first or pair Green norm bounds under the
manuscript's uniformly Laplace-integrable majorants. -/
theorem green_responses_converge_of_summable_defects
    (green : ℕ → B) (delta : ℕ → ℝ)
    (hdelta : Summable delta)
    (hstep : ∀ n, dist (green n) (green (n + 1)) ≤ delta n) :
    ∃ greenLimit : B, Tendsto green atTop (nhds greenLimit) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable delta hstep hdelta)

/-- Completeness also makes the transported weighted limit unique. -/
theorem transported_limit_unique
    (response : ℕ → B) {x y : B}
    (hx : Tendsto response atTop (nhds x))
    (hy : Tendsto response atTop (nhds y)) :
    x = y :=
  tendsto_nhds_unique hx hy

end CriticalResponseTransport
end NCG
