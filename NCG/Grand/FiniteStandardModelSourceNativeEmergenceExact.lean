/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteSMSTLoadedEmergence
import NCG.Grand.ActiveFiniteStructuralStandardModelExact
import NCG.Grand.CentralCharacterQuotientDescentExact
import NCG.Grand.ChannelNativeFiniteSMEntranceAssembly
import NCG.Grand.ExplicitRegulatedStandardModelActionExact
import NCG.Grand.CanonicalGraphRegulatorGeometry
import NCG.Grand.FiniteLineValuedEinstein
import NCG.Grand.CorrectedDualMeasureCriterion

/-!
# Finite Standard-Model source-native emergence

This is the top-level typed assembly for `thm:SM-GT`.  It replaces the old
arithmetic token bundle by one certificate containing the actual admissibly
loaded hierarchy and the actual active finite Standard-Model carrier.  The
literal and channel-native finite-Dirac entrances, conservative fallback, and
zero-residual semantics are inherited from that loaded hierarchy; the gauge
quotient, anomaly-forced weights, generation rank, weak doublet, odd Dirac
orbit, and determinant incidence all come from the same structural packet.

The theorem's explicitly conditional action and quantum clauses remain typed
by `explicit_regulated_standard_model_action_exact`,
`canonical_graph_regulator_geometry_exact`, `finite_line_valued_Einstein`,
and `independent_dual_factor_cancels`, all imported here and cited with this
assembly in the statement ledger.
-/

open Matrix Filter Set
open scoped ComplexOrder Kronecker

namespace NCG

/-- The coherent finite E1--E9 source-native certificate. -/
structure FiniteStandardModelSourceNativeCertificate
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY)
    {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (u : Matrix (Fin 7) (Fin 7) ℂ)
    (D0 Gamma : Matrix H H ℂ)
    (t weakHiggs : Fin 2 → ℂ) (T : DetIncidence.Shadow) : Type where
  /-- E1--E4, both E5 entrances, E6 fallback, and E9 residual semantics. -/
  loadedHierarchy : FiniteSMSTLoadedEmergenceCertificate L
  /-- E1--E6 on the literal active finite carrier. -/
  activeStructural :
    Nonempty (ActiveFiniteStructuralStandardModelPacket
      u D0 Gamma t weakHiggs T)
  /-- The actual global quotient group used by every matter sector. -/
  globalGaugeQuotient : SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup
  /-- The central descent criterion and its exact finite Fourier indicator. -/
  centralSelector : ∀ (zeta : ℂˣ), orderOf zeta = 6 →
    ∀ triality parity charge : ℤ,
      (SMCentralDescentSelector.centralKernelAction zeta
          triality parity charge = 1 ↔
        (6 : ℤ) ∣ 2 * triality + 3 * parity + charge) ∧
      ∀ m : ℕ,
        (∑ k ∈ Finset.range 6, (((zeta : ℂ) ^ m) ^ k)) =
          if 6 ∣ m then 6 else 0
  /-- The anomaly equations force precisely the primitive SM weight ray. -/
  anomalyForcedWeights : SMAnomalyClassification
  /-- The generated chiral labels are the displayed six-entry table. -/
  generatedMatterCharges :
    tensorExteriorCentralWeights (-2) 3 =
      (fun i => ((SMTensorGeneration.generatedMatterLabels i).charge : ℚ))
  /-- The endpoint cycle source has the protected rank three. -/
  endpointGenerationRank : Module.finrank ℂ (LinearMap.ker SMActive.sumF) = 3
  /-- Every exact loaded relation is the zero set of its positive residual. -/
  positiveResidualSemantics : ∀ {iota E0 : Type} [Zero E0]
      (s : Finset iota) (p : iota → E0) (q : E0 → ℝ),
    (∀ v, 0 ≤ q v) → (∀ v, q v = 0 → v = 0) → q 0 = 0 →
      ((∑ r ∈ s, q (p r)) = 0 ↔ ∀ r ∈ s, p r = 0)

/-- **Finite Standard-Model source-native emergence (`thm:SM-GT`).**
Starting only from the admissible loading data and the four concrete active
seed hypotheses (positive colour support, normalized odd Dirac seed,
independent weak reset, and nonzero alternating determinant incidence), this
constructs the complete finite certificate. -/
theorem finiteStandardModel_sourceNative_emergence
    {h e panel selected A B eY : Type}
    [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData h e panel selected A B eY)
    {H : Type} [Fintype H] [Nonempty H] [DecidableEq H]
    (u : Matrix (Fin 7) (Fin 7) ℂ)
    (hsupp : InternalAssembly.ColourSupported u)
    (hcol : 0 < InternalAssembly.omega7 u)
    (D0 Gamma : Matrix H H ℂ)
    (hDl : D0ᴴ * D0 = 1) (hDr : D0 * D0ᴴ = 1)
    (hself : D0ᴴ = D0) (hodd : Gamma * D0 = -(D0 * Gamma))
    (hGamma : Gamma * Gamma = 1)
    (t weakHiggs : Fin 2 → ℂ)
    (hind : t 0 * weakHiggs 1 - t 1 * weakHiggs 0 ≠ 0)
    (hover : (∑ m, star (t m) * weakHiggs m) ≠ 0)
    (T : DetIncidence.Shadow) (hT : DetIncidence.FullyAlternating T)
    (hdet : 0 < DetIncidence.mdet T) :
    Nonempty (FiniteStandardModelSourceNativeCertificate
      L u D0 Gamma t weakHiggs T) := by
  have hloaded := finiteSMSTLoadedEmergence L
  have hactive := activeFiniteStructuralStandardModel u hsupp hcol D0 Gamma
    hDl hDr hself hodd hGamma t weakHiggs hind hover T hT hdet
  refine ⟨{
    loadedHierarchy := hloaded
    activeStructural := hactive
    globalGaugeQuotient := smGaugeQuotientEquiv
    centralSelector := ?_
    anomalyForcedWeights := ?_
    generatedMatterCharges :=
      SMTensorGeneration.generatedMatter_charge_table
    endpointGenerationRank := SMActive.generation_rank
    positiveResidualSemantics := ?_ }⟩
  · intro zeta hzeta triality parity charge
    exact SMCentralDescentSelector.sm_central_descent_selector zeta hzeta
      triality parity charge
  · simpa [SMAnomalyClassification] using anomaly_forced_weights
  · intro iota E0 _ s p q hnonneg hdef hzero
    exact zero_loading_relations s p q hnonneg hdef hzero

end NCG
