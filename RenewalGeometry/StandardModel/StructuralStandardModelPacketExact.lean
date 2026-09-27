/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.StandardModel.InternalSeedSaturationExact
import RenewalGeometry.StandardModel.EndpointGenerationCarrierExact
import RenewalGeometry.StandardModel.CliffordOccurrenceTest
import RenewalGeometry.StandardModel.OperationalDeterminantSource
import RenewalGeometry.StandardModel.AnomalyForcedWeights
import RenewalGeometry.StandardModel.SMGaugeQuotientExact
import RenewalGeometry.Spectralization.SaturatedFiniteDiracGenerator
/-!
# Structural Standard-Model classification from a landed multiplicity packet
  (`thm:structural-SM`)

`thm:structural-SM` of the spacetime–gauge duality manuscript, on the abstract hypothesis
packet of the theorem (not on a fixed explicit carrier).

## The packet

`LandedMultiplicityPacket n G h e₁ e` is a finite source-complete joint packet on one
represented carrier `ℂⁿ`: the external tetrahedral action `ρ : G →* M_n(ℂ)` of a finite group
(unitary, `ρ(g)ᴴ = ρ(g⁻¹)`), and the complete represented spacetime source `S_ST` and accepted
internal source `S_int` on a common source carrier `ℂ^h`.  The **positive geometry short** of
`thm:geometry-short` is the shorted Gram

`G_{int|ST} = G_int − C G_ST^† C^* = S_int^* (I − P_ST) S_int ⪰ 0`

(`shortedGram`, the exact source Schur residual; its positivity `shortedGram_posSemidef` is
`thm:source-Schur`, so the packet satisfies the positive geometry short automatically).

## The six clauses (`structural_standard_model`)

On the same represented carrier:

* **(i)** (`thm:internal-seed-saturation`) with the isotypic decomposition data of
  `thm:active-isotypic` furnished for `ρ`: if one finite word depth satisfies the multiplicity
  census `(3, 2, 1, 1)` and the internal landing hypotheses (I1)–(I4) (a colour-supported
  represented word with `ω_col > 0` or a reciprocal mediator bridge, a weak router, the
  multiplicity-one scalar sectors and their independent central supports), then the complete
  internal relative commutant is `M₃(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` (an explicit algebra isomorphism
  onto `𝒜'_ext`, dimension `15`, centre `4`, sectors of `9` and `4` entries).
* **(ii)** (`prop:main-det-incidence`, `thm:gauge-group`) if the canonical fully alternating
  projection `𝔄T` of a represented incidence shadow is nonzero, it is a determinant seed
  `τ = 𝔄T ≠ 0` with `Θ_τ` the alternating projection, its unitary stabilizer in
  `U(3) × U(2)` is `S(U(3) × U(2))`, and `S(U(3) × U(2)) ≅ (SU(3) × SU(2) × U(1)) / ℤ₆` with
  the central kernel `{(z² I₃, z⁻³ I₂, z) : z⁶ = 1}`.
* **(iii)** (`thm:hypercharge`) for the represented tensor types `eq:SM-types`, the local
  anomalies vanish iff `3a + 2b = 0`; the primitive integral solutions are `±(−2, 3)` and the
  weights are `y(Q,u,d,L,e,H) = (1, 4, −2, −3, −6, 3)`.
* **(iv)** (`prop:generation-carrier`) if the shorted Gram is strictly positive on the
  rank-three reversal-odd endpoint block `W₋`, the supported generation factor has
  `dim_ℂ G_gen = 3`, and the sign-twisted triplet is a distinct type (no invertible
  intertwiner), so it remains loop provenance.
* **(v)** (`prop:clifford-occurrence`, `prop:finite-dirac`) `p_Cl > 0` for a represented
  grading `J` exactly when a represented Clifford axis changes the grading; and on an
  odd-provenance-complete branch the complete grading-odd generator is fixed by the
  finite-Dirac projector and factors through the represented range of `D_F`: one
  source-minimal finite Dirac operator.
* **(vi)** (source minimality of the primitive weak one-leg sector) if the primitive weak
  one-leg odd sector is source complete over one weak Schmidt line, the complete one-leg
  coefficient map factors through that line and has rank at most one (exactly one primitive
  doublet); a second persistent copy (rank `> 1`) forces a nonzero orthogonal odd source
  innovation.

Disclosed renderings: the paper's hypotheses are rendered as the hypotheses of the
ingredient theorems (isotypic data `(ι, I, J, W)` of `thm:active-isotypic`; census as a
labelling `e : ι ≃ Fin 4`; the represented words as the transported generators on the census
carrier; the incidence tensor as an up-incidence shadow `DetIncidence.Shadow`; the Clifford
grading on the represented carrier `ℂ⁴ ⊗ M`; odd-provenance completeness as vanishing odd
provenance defect; the weak one-leg sector as a coefficient map over a Schmidt line).  The
typed-contraction clause of (v) (Yukawa/Majorana residues as compressions of `D_F`) is
deterministic postprocessing and is not formalized as a separate object.  The no-go and
deficit branches quoted at the end of the theorem are other theorems
(`thm:degree-one-colour-no-go`, `thm:flat-depth-colour`, `thm:internal-deficit-alternatives`)
and are not part of this statement.
-/

open Matrix Module
open scoped ComplexOrder

namespace RenewalGeometry

open InternalSeedSaturation ExternalIsotypic
open RenewalGeometry.InternalAssembly (blockAlgebra ColourSupported omega7)
open RenewalGeometry.InternalDeficit (baseGens bridgeGens routerGen Router)
open EndpointGenerationCarrier CliffordTwirlMatterAudit OperationalDeterminantSource

/-- **A finite source-complete joint packet on one represented carrier**: the unitary external
action `ρ` of a finite group on `ℂⁿ`, and the complete spacetime and accepted internal sources
on a common source carrier `ℂ^h`. -/
structure LandedMultiplicityPacket (n G : Type) [Fintype n] [DecidableEq n] [Group G]
    [Fintype G] (h e₁ e : ℕ) where
  /-- the external tetrahedral action on the represented carrier -/
  ρ : G →* Matrix n n ℂ
  /-- the external action is unitary -/
  unitary : ∀ g, (ρ g)ᴴ = ρ g⁻¹
  /-- the complete represented spacetime source -/
  S_ST : Matrix (Fin h) (Fin e₁) ℂ
  /-- the accepted internal source -/
  S_int : Matrix (Fin h) (Fin e) ℂ

namespace LandedMultiplicityPacket

variable {n G : Type} [Fintype n] [DecidableEq n] [Group G] [Fintype G] {h e₁ e : ℕ}

/-- The geometry short `G_{int|ST} = S_int^* (I − P_ST) S_int` (`eq:geometry-short-general`). -/
noncomputable def shortedGram (Pk : LandedMultiplicityPacket n G h e₁ e) :
    Matrix (Fin e) (Fin e) ℂ :=
  sourceSchurResidual Pk.S_ST Pk.S_int

/-- **The positive geometry short**: `G_{int|ST} ⪰ 0` (`thm:geometry-short`). -/
theorem shortedGram_posSemidef (Pk : LandedMultiplicityPacket n G h e₁ e) :
    Pk.shortedGram.PosSemidef :=
  sourceSchurResidual_posSemidef _ _

/-- **`thm:structural-SM` (Structural Standard-Model classification from a landed
multiplicity packet).**  On a finite source-complete joint packet with its positive geometry
short, the six implications (i)–(vi) hold on the same represented carrier; see the module
docstring for the reading of each clause. -/
theorem structural_standard_model (Pk : LandedMultiplicityPacket n G h e₁ e) :
    -- (i) landed multiplicity census ⇒ internal relative commutant `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`
    (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (fun x => Wᴴ * x * W) ''
          matCommutant (Algebra.adjoin ℂ (Set.range Pk.ρ) : Set (Matrix n n ℂ)) =
        multBlockSet I J ∧
      ∀ (e : ι ≃ Fin 4), (∀ k, Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k) →
        ∀ {u : Matrix (Fin 7) (Fin 7) ℂ},
          (ColourSupported u ∧ 0 < omega7 u) ∨ ReciprocalBridge u →
          ∀ {h : Fin 7 → ℂ}, Router h →
          ∃ Φ : blockAlgebra ≃ₐ[ℂ] extCommutant Pk.ρ,
            Algebra.adjoin ℂ (((extCommutant Pk.ρ).val.comp Φ.toAlgHom) ''
                (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) = extCommutant Pk.ρ ∧
            finrank ℂ (extCommutant Pk.ρ) = 15 ∧
            finrank ℂ (Subalgebra.center ℂ (extCommutant Pk.ρ)) = 4 ∧
            finrank ℂ (Matrix (J (e.symm 0)) (J (e.symm 0)) ℂ) = 9 ∧
            finrank ℂ (Matrix (J (e.symm 1)) (J (e.symm 1)) ℂ) = 4)
    -- (ii) nonzero alternating incidence projection ⇒ `G_SM = S(U(3) × U(2)) ≅ cover / ℤ₆`
    ∧ (∀ T : DetIncidence.Shadow, DetIncidence.alt T ≠ 0 →
        (DetIncidence.alt (DetIncidence.theta (DetIncidence.alt T)) = DetIncidence.alt T) ∧
        determinantSeedStabilizer (DetIncidence.alt T) = SMGaugeGroup ∧
        Nonempty (SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup) ∧
        Function.Surjective smGaugeHom ∧
        (∀ x : SMGaugeCover, x ∈ smGaugeHom.ker ↔
          x.1.1.1 = (x.2 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
          x.1.2.1 = ((x.2 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
          (x.2 : ℂ) ^ 6 = 1))
    -- (iii) anomaly freedom ⇔ `3a + 2b = 0`, and the hypercharge table
    ∧ ((∀ a b : ℚ,
          ((3 * a + 2 * b) / 2 = 0
            ∧ 3 * (3 * a + 2 * b) = 0
            ∧ 3 * (3 * a + 2 * b) * (3 * a ^ 2 + 2 * b ^ 2) = 0)
          ↔ 3 * a + 2 * b = 0)
        ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 ↔ ∃ t : ℤ, a = -2 * t ∧ b = 3 * t)
        ∧ (∀ a b : ℤ, 3 * a + 2 * b = 0 → IsCoprime a b →
            (a = -2 ∧ b = 3) ∨ (a = 2 ∧ b = -3))
        ∧ smCentralWeights (-2) 3 = ![1, 4, -2, -3, -6, 3])
    -- (iv) strictly positive shorted endpoint Gram on `W₋` ⇒ `dim G_gen = 3`, sign twist distinct
    ∧ ((∀ Wminus : Submodule ℂ (Fin e → ℂ), finrank ℂ Wminus = 3 →
          StrictlyPositiveOn Pk.shortedGram Wminus →
          finrank ℂ (supported Pk.shortedGram Wminus) = 3)
        ∧ ¬ ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsUnit B ∧
            B * k4StandardTransposition = -(k4StandardTransposition * B) ∧
            B * k4StandardFourCycle = -(k4StandardFourCycle * B))
    -- (v) Clifford occurrence and the source-minimal finite Dirac operator
    ∧ ((∀ (m : Type) [Fintype m] [DecidableEq m] [Nonempty m]
          (J : Block (CliffordCarrier m)), Jᴴ = J → J * J = 1 →
          (0 < cliffordProbability J representedAxis ↔
            ∃ μ, J * representedAxis μ ≠ representedAxis μ * J))
        ∧ ∀ {d e' k : ℕ} (Pi : Matrix (Fin d) (Fin d) ℂ) (selected : Matrix (Fin d) (Fin e') ℂ)
            (completeOdd : Matrix (Fin d) (Fin k) ℂ), Pi * selected = selected →
            OddProvenanceComplete selected completeOdd →
            Pi * completeOdd = completeOdd ∧
              ((1 : Matrix (Fin d) (Fin d) ℂ) - Pi) * completeOdd = 0 ∧
              ∃ coefficients : Matrix (Fin e') (Fin k) ℂ, completeOdd = selected * coefficients)
    -- (vi) source-complete primitive weak one-leg sector ⇒ exactly one primitive doublet
    ∧ ∀ {h' e' k : ℕ} (line : Matrix (Fin h') (Fin 1) ℂ) (selected : Matrix (Fin h') (Fin e') ℂ)
        (complete : Matrix (Fin h') (Fin k) ℂ),
        (∃ coefficients : Matrix (Fin 1) (Fin e') ℂ, selected = line * coefficients) →
        (OddProvenanceComplete selected complete →
          ∃ coefficients : Matrix (Fin 1) (Fin k) ℂ,
            complete = line * coefficients ∧ complete.rank ≤ 1) ∧
        (1 < complete.rank → oddProvenanceDefect selected complete ≠ 0) := by
  refine ⟨internal_seed_saturation_of_unitary Pk.ρ Pk.unitary, ?_, anomaly_forced_weights,
    ⟨fun Wminus hdim hpos => endpoint_generation_carrier Pk.shortedGram_posSemidef hdim hpos,
      signTwist_not_equivalent⟩, ?_, ?_⟩
  · intro T hT
    refine ⟨DetIncidence.alternation_retracts _, determinantSeedStabilizer_eq_SMGaugeGroup hT,
      ⟨smGaugeQuotientEquiv⟩, smGaugeHom_surjective, mem_smGaugeHom_ker_iff_centralZ6⟩
  · refine ⟨fun m _ _ _ J hJH hJ2 => (clifford_occurrence_test J hJH hJ2).1, ?_⟩
    intro d e' k Pi selected completeOdd hsel hcomp
    exact zeroOddProvenance_fixesFiniteDiracProjection Pi selected completeOdd hsel hcomp
  · intro h' e' k line selected complete hline
    refine ⟨fun hcomp => zeroOddProvenance_commonWeakLine_rankOne line selected complete hline
      hcomp, fun hrank hdef => ?_⟩
    obtain ⟨_, _, hle⟩ := zeroOddProvenance_commonWeakLine_rankOne line selected complete hline
      hdef
    omega

end LandedMultiplicityPacket

end RenewalGeometry
