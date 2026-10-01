/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib
import RenewalGeometry.StandardModel.InternalSeedSaturationExact
import RenewalGeometry.StandardModel.DeterminantPhaseRigidityExact
import RenewalGeometry.StandardModel.FaithfulSMQuotientExact
import RenewalGeometry.StandardModel.SMGaugeQuotientExact
import RenewalGeometry.StandardModel.AnomalyForcedWeights
import RenewalGeometry.StandardModel.EndpointAncestryAllocationExact
import RenewalGeometry.StandardModel.EndpointGenerationCarrierExact
import RenewalGeometry.StandardModel.LinearAnomalyRigidityExact
import RenewalGeometry.StandardModel.CanonicalChiralProjectorsExact
import RenewalGeometry.StandardModel.TypedMatterLiftExact
import RenewalGeometry.StandardModel.WeakCopyCensusExact
import RenewalGeometry.Spectralization.FiniteDiracRelationSpaceExact

/-!
# Structural synthesis (`thm:structural-SM`, revised 30 Sep 2026)

The corollary combines, on its stated hypotheses, the proved ingredient theorems:

* **internal algebra** (`thm:internal-seed-saturation`): for the unitary external action with its
  isotypic data, the census and internal-landing hypotheses give
  `𝒜_int^word ≅ M₃(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ` (`internal_seed_saturation_of_unitary`);
* **global group**, either route: the aligned phase-sensitive determinant data
  (`thm:gauge-group`, `gauge_group_phase_sensitive`: `h_det > 0` iff the packet stabilizer is
  `S(U(3) × U(2))`), or the represented chiral tensor packet with primitive anomaly freedom and
  faithful kernel (`cor:anomaly-faithful-group`: `anomaly_forced_weights`,
  `FaithfulSMQuotient.faithful_quotient`); in both cases
  `G_phys ≅ S(U(3) × U(2)) ≅ (SU(3) × SU(2) × U(1)) / ℤ₆` (`smGaugeQuotientEquiv`);
* **charged-copy count** (`thm:endpoint-allocation` with `thm:linear-anomaly-rigidity`,
  `thm:canonical-chiral-projectors` and `eq:three-generations`): on the complete source-minimal
  fermion carrier with its canonical charged inventory, a faithful endpoint occurrence `T_{f₀}` of
  the supported endpoint carrier `G_gen` (which has dimension `3` on the positive endpoint branch,
  `endpoint_generation_carrier`) in a complete typed synthesis `S_{f₀}`, and
  `Δ_inv^F = Δ_lin = a_{f₀|G} = 0`, give `n_Q = n_u = n_d = n_L = n_e = 3`, `P_gch = P_SM` and
  `K_{F,gch}^min = ⊕_f P_{f,ε_f} K` with each `P_{f,ε_f} K ≅ V_f ⊗ ℂ³` unitarily: the carrier
  `3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕ 3e` (`structural_synthesis_charged_count`);
* **general duality** (`prop:typed-matter-lift` + `thm:main-duality`): the canonical matter
  action supplies the typing algebra and every represented incidence family, of arbitrary
  coefficient rank, satisfies the duality (`TypedMatterLift.typed_matter_lift`);
* **weak-copy test** (`thm:weak-copy-census`): `m_H > 0`, `𝔭_H = 0` give exactly one reached weak
  doublet (`rank B_H = 1`, `dim K_H^occ = 2`);
* **fixed-generator test** (`prop:finite-dirac`): `Δ_F^rel = 0`, `‖D_F^can‖ > 0` give an admitted
  nonzero finite-Dirac operator.

`structural_synthesis` is the assembled corollary.

Renderings disclosed: the five charged target types are the index `Fin 5` in the order
`(Q, u, d, L, e)` of `LinearAnomalyRigidity.ChargedMultiplicities.vec`, carried by an
`CanonicalChiralProjectors.Inventory` on the saturated carrier `ℂ^ι` (its `n f (εp f)` are the
physical multiplicities `n_f`); `Δ_inv^F` is `Tr(P_gch − P_SM)`; the multiplicity space
`N_{f₀} = 𝓘_{f₀,ε_{f₀}}` is written in the coordinates of its orthonormal basis
(`Fin (n f₀ (εp f₀))`); `G_gen` is written in coordinates as `Fin (dim supported)`.  The
"same-source packet" is not a single Lean structure: each clause is instantiated on the data its
ingredient theorem uses (the internal and group clauses hold for every such packet).
-/

open Matrix Module
open scoped ComplexOrder Kronecker

namespace RenewalGeometry
namespace StructuralSynthesis

open InternalSeedSaturation ExternalIsotypic
open RenewalGeometry.InternalAssembly (blockAlgebra ColourSupported omega7)
open RenewalGeometry.InternalDeficit (baseGens bridgeGens routerGen Router)
open OperationalDeterminantSource EndpointGenerationCarrier
open EndpointAncestryAllocation EndpointAllocationCompiler
open CanonicalChiralProjectors LinearAnomalyRigidity
open TypedMatterLift RepresentedJointPacket

/-! ### The charged-copy count -/

section ChargedCount

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {Vf : Fin 5 → Type*} [∀ f, Fintype (Vf f)] [∀ f, DecidableEq (Vf f)]
  {Gc : GaugeCarrier ι J}

/-- The physical charged multiplicities `n_f = dim 𝓘_{f,ε_f}` of an inventory, as the vector
`(n_Q, n_u, n_d, n_L, n_e)`. -/
def inventoryMultiplicities (D : Inventory Gc Vf) : ChargedMultiplicities :=
  ⟨D.n 0 (D.εp 0), D.n 1 (D.εp 1), D.n 2 (D.εp 2), D.n 3 (D.εp 3), D.n 4 (D.εp 4)⟩

theorem inventoryMultiplicities_vec (D : Inventory Gc Vf) (f : Fin 5) :
    (inventoryMultiplicities D).vec f = (D.n f (D.εp f) : ℤ) := by
  fin_cases f <;> rfl

theorem common_vec (g : ℤ) (f : Fin 5) : (common g).vec f = g := by
  fin_cases f <;> rfl

/-- **Charged-copy count of `thm:structural-SM`.**  On the saturated fermion carrier with its
canonical charged inventory `D`, let `G_gen = supported Gm W₋` be the supported endpoint carrier
of a positive endpoint Gram (`Gm ⪰ 0`, strictly positive on the three-dimensional `W₋`), let
`S : E → N_{f₀}` be a complete typed synthesis and `T : G_gen → N_{f₀}` a faithful endpoint
occurrence (`T^*T ≻ 0`) for one charged type `f₀`.  If `Δ_inv^F = Tr(P_gch − P_SM) = 0`,
`Δ_lin = 0` and `a_{f₀|G} = Tr 𝔸_{f₀|G} = 0`, then every charged multiplicity is `3`, the
future-visible charged carrier is exactly the target chiral part `P_gch = Σ_f P_{f,ε_f}`, and each
`P_{f,ε_f} K` is unitarily `V_f ⊗ ℂ³` (rank `3 · dim V_f`): `K_{F,gch}^min ≅ 3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕
3e`. -/
theorem structural_synthesis_charged_count (D : Inventory Gc Vf)
    {d : Type*} [Fintype d] [DecidableEq d] {Gm : Matrix d d ℂ} (hGm : Gm.PosSemidef)
    {Wminus : Submodule ℂ (d → ℂ)} (hdim : finrank ℂ Wminus = 3)
    (hpos : StrictlyPositiveOn Gm Wminus)
    (f₀ : Fin 5) {E : Type*} [Fintype E] [DecidableEq E]
    (S : Matrix (Fin (D.n f₀ (D.εp f₀))) E ℂ) (hS : Function.Surjective S.mulVec)
    (T : Matrix (Fin (D.n f₀ (D.εp f₀))) (Fin (finrank ℂ (supported Gm Wminus))) ℂ)
    (hT : (Tᴴ * T).PosDef)
    (hinv : (D.Pgch - D.Psm).trace = 0)
    (hlin : deltaLin (inventoryMultiplicities D) = 0)
    (halloc : (allocationResidual S T).trace = 0) :
    inventoryMultiplicities D = common 3 ∧
    (∀ f, D.n f (D.εp f) = 3) ∧
    D.Pgch = ∑ f, D.P f (D.εp f) ∧
    (∀ f, (D.P f (D.εp f)).rank = 3 * Fintype.card (Vf f)) ∧
    (∀ f, (evalMatrix (D.T f (D.εp f)))ᴴ * evalMatrix (D.T f (D.εp f)) = 1 ∧
      evalMatrix (D.T f (D.εp f)) * (evalMatrix (D.T f (D.εp f)))ᴴ = D.P f (D.εp f)) := by
  -- `dim G_gen = 3`
  have hG : Fintype.card (Fin (finrank ℂ (supported Gm Wminus))) = 3 := by
    rw [Fintype.card_fin]; exact endpoint_generation_carrier hGm hdim hpos
  -- `a = 0 ⇒ 𝔸 = 0 ⇒ rank 𝔸 = 0`
  have hall := endpoint_allocation S hS T hT
  have hA0 : allocationResidual S T = 0 := hall.2.2.2.2.2.2.1.mp halloc
  have hrank0 : (allocationResidual S T).rank = 0 := by rw [hA0]; exact Matrix.rank_zero
  -- `Δ_lin = 0` with the anchor `n_{f₀} = dim N_{f₀}`
  have hcommon : inventoryMultiplicities D = common 3 := by
    have := endpoint_allocation_anomaly_excess S hS T hT (inventoryMultiplicities D) hlin f₀
      (by rw [inventoryMultiplicities_vec, Fintype.card_fin])
    rw [this, hG, hrank0]
    rfl
  have hn : ∀ f, D.n f (D.εp f) = 3 := by
    intro f
    have := inventoryMultiplicities_vec D f
    rw [hcommon, common_vec] at this
    exact_mod_cast this.symm
  -- `Δ_inv = 0 ⇒ P_gch = P_SM`
  have hsplit := inventory_split D
  have hgch : D.Pgch = D.Psm := by
    have htr := hsplit.2.2.2.2.2.1
    rw [hinv] at htr
    have hranks : D.Pmir.rank + D.Pex.rank = 0 := by exact_mod_cast htr.symm
    exact hsplit.2.2.2.2.2.2.2.1.mp (by rw [hsplit.2.2.2.2.2.2.1]; exact hranks)
  refine ⟨hcommon, hn, hgch, fun f => ?_, fun f => ?_⟩
  · haveI := D.nonempty f
    rw [Inventory.P, (rank_projector (D.onb f (D.εp f))).1, hn f]
  · haveI := D.nonempty f
    exact evalMatrix_unitary (D.onb f (D.εp f))

end ChargedCount

/-! ### The assembled corollary -/

/-- **`thm:structural-SM` (Structural synthesis).**  Under the corollary's hypotheses:

1. (internal saturation) for every unitary external action, with the isotypic data, the census
   and internal-landing hypotheses give `𝒜_int^word ≅ M₃(ℂ) ⊕ M₂(ℂ) ⊕ ℂ ⊕ ℂ`;
2. (global group, determinant route) aligned phase-sensitive determinant data with `h_det > 0`
   have stabilizer `S(U(3) × U(2))`; (anomaly route) primitive anomaly freedom forces
   `±(−2, 3)` and the represented chiral tensor packet has faithful kernel `ℤ₆ = ker` of the cover
   map, so `G_phys = cover / ker ≅ S(U(3) × U(2))`; and `S(U(3) × U(2)) ≅ cover / ℤ₆`;
3. (charged count) on the fermion carrier with `Δ_inv^F = Δ_lin = a_{f₀|G} = 0`,
   `K_{F,gch}^min ≅ 3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕ 3e` (`structural_synthesis_charged_count`);
4. (general duality) the canonical matter action supplies the typing algebra, and every
   represented incidence family satisfies the duality;
5. (weak-copy test) `m_H > 0`, `𝔭_H = 0` give exactly one reached weak doublet;
6. (fixed-generator test) `Δ_F^rel = 0`, `‖D_F^can‖ > 0` give a nonzero admitted finite-Dirac
   operator. -/
theorem structural_synthesis
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    {Vf : Fin 5 → Type*} [∀ f, Fintype (Vf f)] [∀ f, DecidableEq (Vf f)]
    {Gc : GaugeCarrier ι J} (D : Inventory Gc Vf)
    {d : Type*} [Fintype d] [DecidableEq d] {Gm : Matrix d d ℂ} (hGm : Gm.PosSemidef)
    {Wminus : Submodule ℂ (d → ℂ)} (hdim : finrank ℂ Wminus = 3)
    (hpos : StrictlyPositiveOn Gm Wminus)
    (f₀ : Fin 5) {E : Type*} [Fintype E] [DecidableEq E]
    (S : Matrix (Fin (D.n f₀ (D.εp f₀))) E ℂ) (hS : Function.Surjective S.mulVec)
    (T : Matrix (Fin (D.n f₀ (D.εp f₀))) (Fin (finrank ℂ (supported Gm Wminus))) ℂ)
    (hT : (Tᴴ * T).PosDef)
    (hinv : (D.Pgch - D.Psm).trace = 0)
    (hlin : deltaLin (inventoryMultiplicities D) = 0)
    (halloc : (allocationResidual S T).trace = 0) :
    -- 1. internal saturation: `𝒜_int^word ≅ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`
    (∀ {n G : Type} [Fintype n] [DecidableEq n] [Group G] [Fintype G]
      (ρ : G →* Matrix n n ℂ), (∀ g, (ρ g)ᴴ = ρ g⁻¹) →
      ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι') (I J' : ι' → Type)
        (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
        (_ : ∀ b, Fintype (J' b)) (_ : ∀ b, DecidableEq (J' b))
        (W : Matrix n (Σ b, I b × J' b) ℂ),
        Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J' b)) ∧
        (fun x => Wᴴ * x * W) ''
            matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) =
          multBlockSet I J' ∧
        ∀ (e : ι' ≃ Fin 4), (∀ k, Fintype.card (J' (e.symm k)) = ![3, 2, 1, 1] k) →
          ∀ {u : Matrix (Fin 7) (Fin 7) ℂ},
            (ColourSupported u ∧ 0 < omega7 u) ∨ ReciprocalBridge u →
            ∀ {h : Fin 7 → ℂ}, Router h →
            ∃ Φ : blockAlgebra ≃ₐ[ℂ] extCommutant ρ,
              Algebra.adjoin ℂ (((extCommutant ρ).val.comp Φ.toAlgHom) ''
                  (Subtype.val ⁻¹' (baseGens ∪ bridgeGens u ∪ routerGen h))) =
                extCommutant ρ ∧
              finrank ℂ (extCommutant ρ) = 15 ∧
              finrank ℂ (Subalgebra.center ℂ (extCommutant ρ)) = 4 ∧
              finrank ℂ (Matrix (J' (e.symm 0)) (J' (e.symm 0)) ℂ) = 9 ∧
              finrank ℂ (Matrix (J' (e.symm 1)) (J' (e.symm 1)) ℂ) = 4) ∧
    -- 2. global group, both routes
    ((∀ {p q : Type*} [Fintype p] [Fintype q] (P : MarkedSectorPacket p q),
        0 < hDet P → packetStabilizer determinantProductHom P = SMGaugeGroup) ∧
      (∀ a b : ℤ, 3 * a + 2 * b = 0 → IsCoprime a b → (a = -2 ∧ b = 3) ∨ (a = 2 ∧ b = -3)) ∧
      FaithfulSMQuotient.jointRep.ker = smGaugeHom.ker ∧
      Function.Injective (QuotientGroup.kerLift FaithfulSMQuotient.jointRep.toHomUnits) ∧
      Nonempty (SMGaugeCover ⧸ FaithfulSMQuotient.jointRep.ker ≃* SMGaugeGroup) ∧
      Nonempty (SMGaugeCover ⧸ smGaugeHom.ker ≃* SMGaugeGroup) ∧
      (∀ x : SMGaugeCover, x ∈ smGaugeHom.ker ↔
        x.1.1.1 = (x.2 : ℂ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
        x.1.2.1 = ((x.2 : ℂ)⁻¹) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        (x.2 : ℂ) ^ 6 = 1)) ∧
    -- 3. charged-copy count: `K_{F,gch}^min ≅ 3Q ⊕ 3u ⊕ 3d ⊕ 3L ⊕ 3e`
    (inventoryMultiplicities D = common 3 ∧
      (∀ f, D.n f (D.εp f) = 3) ∧
      D.Pgch = ∑ f, D.P f (D.εp f) ∧
      (∀ f, (D.P f (D.εp f)).rank = 3 * Fintype.card (Vf f)) ∧
      (∀ f, (evalMatrix (D.T f (D.εp f)))ᴴ * evalMatrix (D.T f (D.εp f)) = 1 ∧
        evalMatrix (D.T f (D.εp f)) * (evalMatrix (D.T f (D.εp f)))ᴴ = D.P f (D.εp f))) ∧
    -- 4. Clifford-compatible typing algebra and general duality for the typed matter lift
    (∀ {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (κ : Λ → MatterType)
      (N : Λ → Type*) [∀ l, Fintype (N l)] [∀ l, DecidableEq (N l)],
      ((typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
          Set (Matrix (Carrier (fun l => matterV (κ l)) N) (Carrier (fun l => matterV (κ l)) N)
            ℂ)) = intAlgebra (fun l => matterV (κ l)) N) ∧
      (∀ x ∈ extAlgebra (fun l => matterV (κ l)) N,
        ∀ y ∈ (typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
          Set (Matrix (Carrier (fun l => matterV (κ l)) N) (Carrier (fun l => matterV (κ l)) N)
            ℂ)), x * y = y * x) ∧
      (Fintype.card (matterV .Q) = 6 ∧ Fintype.card (matterV .uc) = 3 ∧
        Fintype.card (matterV .dc) = 3 ∧ Fintype.card (matterV .L) = 2 ∧
        Fintype.card (matterV .ec) = 1 ∧ Fintype.card (matterV .nuc) = 1) ∧
      (∀ {E' : Type*} [Fintype E'] (P : RepresentedJointPacket Λ (fun l => matterV (κ l)) N E'),
        P.actionAlgebra = jointActionAlgebra (extAlgebra (fun l => matterV (κ l)) N)
          (typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
            Set (Matrix (Carrier (fun l => matterV (κ l)) N)
              (Carrier (fun l => matterV (κ l)) N) ℂ)) P.incidenceOp ∧
        matCommutant (P.actionAlgebra : Set (Matrix (Carrier (fun l => matterV (κ l)) N)
            (Carrier (fun l => matterV (κ l)) N) ℂ)) =
          ArbitraryIncidenceDuality.iotaTypedMultiplicity P ∧
        matCommutant (ArbitraryIncidenceDuality.iotaTypedMultiplicity P) =
          (P.actionAlgebra : Set (Matrix (Carrier (fun l => matterV (κ l)) N)
            (Carrier (fun l => matterV (κ l)) N) ℂ)))) ∧
    -- 5. weak-copy test: one reached weak doublet
    (∀ {M : Type*} [Fintype M] [DecidableEq M] {JH : Matrix (Fin 2 × M) (Fin 2 × M) ℂ},
      JH.PosSemidef →
      0 < (WeakCopyCensus.weakGram JH).trace →
      (WeakCopyCensus.weakGram JH).trace ^ 2 -
          (WeakCopyCensus.weakGram JH * WeakCopyCensus.weakGram JH).trace = 0 →
      (WeakCopyCensus.weakGram JH).rank = 1 ∧
        finrank ℂ (WeakCopyCensus.occCarrier JH) = 2) ∧
    -- 6. fixed-generator test: an admitted nonzero finite-Dirac operator
    (∀ {n' τ : Type*} [Fintype n'] [DecidableEq n'] (Γ : Matrix n' n' ℂ)
      (P : τ → Matrix n' n' ℂ) (Rel : Set (τ × τ)) (A : Matrix n' n' ℂ),
      CanonicalFiniteDirac.relationDefect Γ P Rel A = 0 →
      0 < ‖CanonicalFiniteDirac.canonicalFiniteDiracL2 Γ P Rel A‖ →
      CanonicalFiniteDirac.finiteDirac Γ A = CanonicalFiniteDirac.canonicalFiniteDirac Γ P Rel A ∧
      matrixL2 (CanonicalFiniteDirac.finiteDirac Γ A) ∈
        CanonicalFiniteDirac.relationSpace Γ P Rel ∧
      CanonicalFiniteDirac.finiteDirac Γ A ≠ 0) := by
  refine ⟨fun ρ hρ => internal_seed_saturation_of_unitary ρ hρ, ?_,
    structural_synthesis_charged_count D hGm hdim hpos f₀ S hS T hT hinv hlin halloc, ?_, ?_, ?_⟩
  · have hfq := FaithfulSMQuotient.faithful_quotient
    refine ⟨fun P hP => ((gauge_group_phase_sensitive P).2.1).mp hP,
      anomaly_forced_weights.2.2.1, hfq.2.1, hfq.2.2.2,
      ⟨(QuotientGroup.quotientMulEquivOfEq hfq.2.1).trans smGaugeQuotientEquiv⟩,
      ⟨smGaugeQuotientEquiv⟩, mem_smGaugeHom_ker_iff_centralZ6⟩
  · intro Λ _ _ κ N _ _
    exact TypedMatterLift.typed_matter_lift κ N
  · intro M _ _ JH hJ hm hp
    have hr := (WeakCopyCensus.rank_eq_one_iff hJ).mpr ⟨hm, hp⟩
    refine ⟨hr, ?_⟩
    rw [WeakCopyCensus.finrank_occCarrier hJ, hr]
  · intro n' τ _ _ Γ P Rel A hΔ hD
    exact CanonicalFiniteDirac.nonzero_admitted_of_relationDefect_zero Γ P Rel A hΔ hD

/-! ### Non-vacuity of the charged-count hypotheses

A toy saturated carrier `ℂ^{5 × 3}` with five one-dimensional target types of distinct central
weights `1, …, 5`, positive chirality, three copies each, together with the trivial positive
endpoint branch `Gm = I₃`, `W₋ = ℂ³`, satisfies every hypothesis of `structural_synthesis`
(`Δ_inv^F = Δ_lin = a_{f₀|G} = 0`). -/

namespace Witness

/-- The central generator `Y = diag(f + 1)` on `ℂ^{5 × 3}`. -/
def wY : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ :=
  diagonal fun p => ((p.1 : ℕ) + 1 : ℂ)

/-- The toy gauge carrier (no nonabelian generators, `Γ = I`). -/
def wCarrier : GaugeCarrier (Fin 5 × Fin 3) Empty where
  X j := j.elim
  Y := wY
  Γ := 1
  X_herm j := j.elim
  Y_herm := by
    rw [wY, Matrix.diagonal_conjTranspose]
    congr 1
    funext p
    simp
  Γ_herm := Matrix.conjTranspose_one
  Γ_sq := Matrix.mul_one 1
  Γ_comm_X j := j.elim
  Γ_comm_Y := by simp

/-- The toy target types: `V_f = ℂ`, central weight `f + 1`. -/
def wType (f : Fin 5) : TargetType Empty Unit where
  ρ j := j.elim
  y := (f : ℕ) + 1
  ρ_herm j := j.elim
  irred M _ := ⟨M () (), by ext i j; simp⟩

/-- The copy embeddings `T_{f,a} = e_{(f,a)}`. -/
def wT (f : Fin 5) (a : Fin 3) : Matrix (Fin 5 × Fin 3) Unit ℂ :=
  Matrix.of fun p _ => if p = (f, a) then 1 else 0

theorem wY_mul (S : Matrix (Fin 5 × Fin 3) Unit ℂ) (p : Fin 5 × Fin 3) :
    (wY * S) p () = ((p.1 : ℕ) + 1 : ℂ) * S p () := by
  simp [wY, Matrix.diagonal_mul]

theorem wT_mem (f : Fin 5) (a : Fin 3) : wT f a ∈ intertwiners wCarrier (wType f) (sgn true) := by
  rw [mem_intertwiners_iff]
  refine ⟨fun j => j.elim, ?_, ?_⟩
  · ext p u
    rw [show wCarrier.Y = wY from rfl, wY_mul]
    by_cases h : p = (f, a)
    · subst h; simp [wT, wType]
    · simp [wT, h]
  · simp [wCarrier, sgn]

theorem mem_true_iff (f : Fin 5) (S : Matrix (Fin 5 × Fin 3) Unit ℂ)
    (hS : S ∈ intertwiners wCarrier (wType f) (sgn true)) :
    S = ∑ a, S (f, a) () • wT f a := by
  rw [mem_intertwiners_iff] at hS
  have hY := hS.2.1
  ext ⟨g, i⟩ u
  have h := congrFun (congrFun hY (g, i)) ()
  rw [show wCarrier.Y = wY from rfl, wY_mul] at h
  simp only [Matrix.smul_apply, smul_eq_mul, wType] at h
  simp only [Matrix.sum_apply, Matrix.smul_apply, wT, Matrix.of_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Prod.mk.injEq]
  by_cases hg : g = f
  · subst hg
    simp [Finset.sum_ite_eq']
  · have hne : ((g : ℕ) + 1 : ℂ) ≠ ((f : ℕ) + 1 : ℂ) := by
      intro e
      apply hg
      have : ((g : ℕ) : ℂ) = ((f : ℕ) : ℂ) := by linear_combination e
      exact Fin.ext (by exact_mod_cast this)
    have : S (g, i) u = 0 := by
      have h' : (((g : ℕ) + 1 : ℂ) - ((f : ℕ) + 1 : ℂ)) * S (g, i) () = 0 := by
        push_cast at h
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
    simp [this, hg]

theorem mem_false_eq_zero (f : Fin 5) (S : Matrix (Fin 5 × Fin 3) Unit ℂ)
    (hS : S ∈ intertwiners wCarrier (wType f) (sgn false)) : S = 0 := by
  rw [mem_intertwiners_iff] at hS
  have h := hS.2.2
  simp only [wCarrier, Matrix.one_mul, sgn] at h
  ext p u
  have := congrFun (congrFun h p) u
  simp only [Bool.false_eq_true, if_false, Matrix.smul_apply, smul_eq_mul] at this
  simp only [Matrix.zero_apply]
  linear_combination this / 2

/-- The toy charged inventory: three positive-chirality copies of each of the five types. -/
def wInv : Inventory wCarrier (fun _ : Fin 5 => Unit) where
  τ := wType
  εp _ := true
  n _ b := cond b 3 0
  T f b := match b with
    | true => wT f
    | false => fun a => Fin.elim0 a
  onb f b := by
    cases b with
    | true =>
      refine ⟨fun a => wT_mem f a, fun a b => ?_, ?_⟩
      · simp only [multInner, Fintype.card_unit, Nat.cast_one, inv_one, one_mul]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, wT,
          Matrix.of_apply, Fintype.univ_unit, Finset.sum_singleton]
        by_cases hab : a = b
        · subst hab; simp [Fintype.sum_prod_type, Finset.sum_ite_eq']
        · simp [hab, Ne.symm hab]
      · apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨a, rfl⟩
          exact wT_mem f a
        · intro S hS
          rw [mem_true_iff f S hS]
          exact Submodule.sum_mem _ fun a _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | false =>
      refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, ?_⟩
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact Fin.elim0 a
      · intro S hS
        rw [mem_false_eq_zero f S hS]
        exact Submodule.zero_mem _
  nonempty _ := inferInstance
  ineq f g hfg M _ hy := by
    exfalso
    apply hfg
    simp only [wType] at hy
    have : ((f : ℕ) : ℂ) = ((g : ℕ) : ℂ) := by
      push_cast at hy
      linear_combination hy
    exact Fin.ext (by exact_mod_cast this)
  nontriv f w _ hy := by
    have hne : ((((f : ℕ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [wType] at hy
    exact (smul_eq_zero.mp hy).resolve_left hne
  P0 := 0
  P0_idem := Matrix.mul_zero 0
  P0_herm := Matrix.conjTranspose_zero
  P0_fix x := by
    simp only [Matrix.zero_mulVec, IsEmpty.forall_iff, true_and]
    constructor
    · intro h
      rw [← h]; exact Matrix.mulVec_zero _
    · intro h
      funext p
      have := congrFun h p
      simp only [show wCarrier.Y = wY from rfl, wY, Matrix.mulVec_diagonal, Pi.zero_apply] at this
      have hne : ((p.1 : ℕ) + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero _
      exact ((mul_eq_zero.mp this).resolve_left hne).symm

theorem wInv_inventory_zero : (wInv.Pgch - wInv.Psm).trace = 0 := by
  have hP : ∀ f a, (wT f a * (wT f a)ᴴ).trace = 1 := by
    intro f a
    rw [Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.mul_apply, wT, Finset.sum_ite_eq']
  have hf : ∀ f, (wInv.P f (wInv.εp f)).trace = 3 := by
    intro f
    show (projector (wT f)).trace = 3
    rw [projector, Matrix.trace_sum]
    simp [hP]
  have h1 : wInv.Pgch = 1 := by
    show 1 - (0 : Matrix (Fin 5 × Fin 3) (Fin 5 × Fin 3) ℂ) = 1
    exact sub_zero 1
  rw [h1, Matrix.trace_sub, Inventory.Psm, Matrix.trace_sum]
  simp only [hf, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ]
  norm_num

theorem wInv_deltaLin : deltaLin (inventoryMultiplicities wInv) = 0 := by
  decide

theorem wEndpoint_finrank : finrank ℂ (⊤ : Submodule ℂ (Fin 3 → ℂ)) = 3 := by
  simp

theorem wEndpoint_pos : StrictlyPositiveOn (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊤ := by
  intro w _ hw
  have := (Matrix.PosDef.one (n := Fin 3) (R := ℂ)).dotProduct_mulVec_pos hw
  exact (RCLike.pos_iff.mp this).1

/-- Non-vacuity: every hypothesis of `structural_synthesis` (identical to those of
`structural_synthesis_charged_count`) is met by the toy packet. -/
example : inventoryMultiplicities wInv = common 3 := by
  have hk : finrank ℂ (supported (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊤) = 3 :=
    endpoint_generation_carrier Matrix.PosSemidef.one wEndpoint_finrank wEndpoint_pos
  let T : Matrix (Fin (wInv.n 0 (wInv.εp 0)))
      (Fin (finrank ℂ (supported (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊤))) ℂ :=
    Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0
  have hT : (Tᴴ * T) = 1 := by
    ext j j'
    simp only [T, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    have hj : (j : ℕ) < 3 := j.2.trans_eq hk
    by_cases hjj : j = j'
    · subst hjj
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ j := fun e => hb (Fin.ext e)
        simp [this]
      · simp
    · have : (j : ℕ) ≠ j' := fun e => hjj (Fin.ext e)
      simp only [hjj, if_false]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : (b : ℕ) = j
      · simp [hb, this]
      · simp [hb]
  have hTpos : (Tᴴ * T).PosDef := by rw [hT]; exact Matrix.PosDef.one
  let S : Matrix (Fin (wInv.n 0 (wInv.εp 0))) (Fin (wInv.n 0 (wInv.εp 0))) ℂ := 1
  have hS : Function.Surjective S.mulVec := fun y => ⟨y, Matrix.one_mulVec y⟩
  have hall := endpoint_allocation S hS T hTpos
  have halloc : (allocationResidual S T).trace = 0 := by
    refine hall.2.2.2.2.2.2.1.mpr (hall.2.2.2.2.2.2.2.1.mpr (hall.2.2.2.2.2.2.2.2.mpr ?_))
    rw [Fintype.card_fin, Fintype.card_fin, hk]
    rfl
  exact (structural_synthesis_charged_count wInv Matrix.PosSemidef.one wEndpoint_finrank
    wEndpoint_pos 0 S hS T hTpos wInv_inventory_zero wInv_deltaLin halloc).1

end Witness

end StructuralSynthesis
end RenewalGeometry
