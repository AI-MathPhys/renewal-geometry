/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.GraphSupportPolarDuality
import RenewalGeometry.Commutant.IntrinsicCoefficientQuiver

/-!
# Support-polar duality for an arbitrary finite incidence bank

Covers `def:support-polar` and `thm:support-polar` of the spacetime–gauge duality paper, in
the generality of the paper: a finite bank `(F_e)_{e ∈ E}` indexed by an arbitrary finite
type `E` with source and target maps `src tgt : E → Λ` — several bank elements per ordered
pair of vertices (needed whenever an intrinsic arrow space `𝔅_e` has dimension `≥ 2`) and
loops `src e = tgt e` are allowed.  Each `F_e : M_{src e} → M_{tgt e}` is an arbitrary
rectangular (possibly singular, rank-deficient or zero) matrix.

* `bankSupportPolarAlgebra` is `O_F^sup = C^*(Z_λ, F_e^*F_e, U_e, U_e^* : λ, e)`
  (`eq:support-polar`), with `U_e = polarIsometry (F_e)` the canonical polar partial
  isometry (`F_e = U_e P_e`, `P_e ≥ 0`, `P_e² = F_e^*F_e`, `U_e^*U_e = supp P_e`).
* `bankTypedMultiplicityAlgebra` is the algebra of families `(R_λ)` with
  `R_{t(e)} F_e = F_e R_{s(e)}` and `R_{s(e)} F_e^* = F_e^* R_{t(e)}` for every `e`.
* `bank_exact_support_polar_duality`: `M_type = (O_F^sup)'`, `O_F^sup = M_type'` and
  `C^*(Z_λ, F_e, F_e^*) = O_F^sup` (`eq:support-polar-duality`,
  `eq:incidence-support-polar-equality`).
* **Link with the intrinsic arrow spaces.**  For a represented joint packet `P`
  (`def:joint-packet`) with intrinsic coefficient spaces `𝔅_e` (`P.coefficientSpace`), a
  bank *spans the intrinsic arrow spaces* (`SpansArrowSpaces`) when the corner-embedded bank
  and the corner-embedded `𝔅_e` span the same operator space on `𝓜 = ⊕_λ M_λ`.  Then the
  bank's typed algebra is the paper's `M_type` of `eq:typed-multiplicity`
  (`bankTypedMultiplicityAlgebra_eq_packet`), and `packet_support_polar_duality` states
  `thm:support-polar` with the packet's `M_type`.  The canonical bank of Hilbert–Schmidt
  coefficient blocks (`sliceBank`) spans the arrow spaces (`sliceBank_spansArrowSpaces`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry

namespace SupportPolarBank

open GraphLoadedEdgeCommutant

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable (M : Λ → Type*) [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)]
variable {E : Type*} {src tgt : E → Λ} (F : ∀ e, Matrix (M (tgt e)) (M (src e)) ℂ)

/-! ### The support-polar action algebra of a bank (`def:support-polar`) -/

/-- The incidence map `F_e` acting on `𝓜 = ⊕_λ M_λ` (on its `(t(e), s(e))` corner). -/
def bankIncidenceOp (e : E) : Matrix (TotalCarrier M) (TotalCarrier M) ℂ :=
  blockEmbed M (F e)

/-- The support metric `F_e^*F_e` on `𝓜`. -/
def bankSupportMetric (e : E) : Matrix (TotalCarrier M) (TotalCarrier M) ℂ :=
  (bankIncidenceOp M F e)ᴴ * bankIncidenceOp M F e

/-- The polar partial isometry `U_e` of `F_e` on `𝓜`. -/
noncomputable def bankPolarOp (e : E) : Matrix (TotalCarrier M) (TotalCarrier M) ℂ :=
  blockEmbed M (polarIsometry (F e))

/-- The generators `{Z_λ, F_e^*F_e, U_e, U_e^*}` of `O_F^sup`. -/
noncomputable def bankSupportPolarGenerators : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  Set.range (vertexProjection M) ∪ Set.range (bankSupportMetric M F) ∪
    Set.range (bankPolarOp M F) ∪ Set.range fun e => (bankPolarOp M F e)ᴴ

/-- **`def:support-polar`** for an arbitrary finite bank (multi-edges and loops allowed):
`O_F^sup = C^*(Z_λ, F_e^*F_e, U_e, U_e^* : λ, e) ⊆ B(𝓜)`. -/
noncomputable def bankSupportPolarAlgebra :
    StarSubalgebra ℂ (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  StarAlgebra.adjoin ℂ (bankSupportPolarGenerators M F)

/-- The incidence generators `{Z_λ, F_e, F_e^*}`. -/
def bankIncidenceGenerators : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  Set.range (vertexProjection M) ∪ Set.range (bankIncidenceOp M F) ∪
    Set.range fun e => (bankIncidenceOp M F e)ᴴ

/-- The incidence algebra `C^*(Z_λ, F_e, F_e^* : λ, e)`. -/
def bankIncidenceAlgebra : StarSubalgebra ℂ (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  StarAlgebra.adjoin ℂ (bankIncidenceGenerators M F)

/-! ### The typed multiplicity algebra of a bank -/

/-- The typed intertwining equations of the bank. -/
def IsBankTypedMultiplicity (R : ∀ l, Matrix (M l) (M l) ℂ) : Prop :=
  ∀ e, R (tgt e) * F e = F e * R (src e) ∧ R (src e) * (F e)ᴴ = (F e)ᴴ * R (tgt e)

/-- The typed multiplicity algebra of the bank: block families `(R_λ)` intertwining every
`F_e` and `F_e^*`. -/
def bankTypedMultiplicityAlgebra : StarSubalgebra ℂ (∀ l, Matrix (M l) (M l) ℂ) where
  carrier := {R | IsBankTypedMultiplicity M F R}
  mul_mem' := by
    intro R S hR hS e
    simp only [Pi.mul_apply]
    constructor
    · calc R (tgt e) * S (tgt e) * F e = R (tgt e) * (F e * S (src e)) := by
            rw [Matrix.mul_assoc, (hS e).1]
        _ = F e * R (src e) * S (src e) := by rw [← Matrix.mul_assoc, (hR e).1]
        _ = F e * (R (src e) * S (src e)) := by rw [Matrix.mul_assoc]
    · calc R (src e) * S (src e) * (F e)ᴴ = R (src e) * ((F e)ᴴ * S (tgt e)) := by
            rw [Matrix.mul_assoc, (hS e).2]
        _ = (F e)ᴴ * R (tgt e) * S (tgt e) := by rw [← Matrix.mul_assoc, (hR e).2]
        _ = (F e)ᴴ * (R (tgt e) * S (tgt e)) := by rw [Matrix.mul_assoc]
  one_mem' := by
    intro e
    simp
  add_mem' := by
    intro R S hR hS e
    simp only [Pi.add_apply]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, (hR e).1,
      (hS e).1, (hR e).2, (hS e).2]
    exact ⟨rfl, rfl⟩
  zero_mem' := by
    intro e
    simp
  algebraMap_mem' := by
    intro c e
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    exact ⟨rfl, rfl⟩
  star_mem' := by
    intro R hR e
    simp only [Set.mem_ofPred_eq] at hR
    simp only [Pi.star_apply, Matrix.star_eq_conjTranspose]
    constructor
    · have h2 := congrArg conjTranspose (hR e).2
      simp only [conjTranspose_mul, conjTranspose_conjTranspose] at h2
      exact h2.symm
    · have h1 := congrArg conjTranspose (hR e).1
      simp only [conjTranspose_mul] at h1
      exact h1.symm

theorem mem_bankTypedMultiplicityAlgebra (R : ∀ l, Matrix (M l) (M l) ℂ) :
    R ∈ bankTypedMultiplicityAlgebra M F ↔ IsBankTypedMultiplicity M F R :=
  Iff.rfl

/-- `M_type` of the bank represented on `𝓜` by the block-diagonal matrices `⊕_λ R_λ`. -/
def bankMultiplicityCarrierAlgebra : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ) :=
  (Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
    (bankTypedMultiplicityAlgebra M F : Set (∀ l, Matrix (M l) (M l) ℂ))

/-! ### The edge step (`lem:polar-edge`) and the duality -/

/-- On one bank element (any corner, including a loop), commuting with `F_e^*F_e`, `U_e`,
`U_e^*` is exactly the pair of intertwining equations. -/
theorem bank_commute_edge_generators_iff (R : ∀ l, Matrix (M l) (M l) ℂ) (e : E) :
    (blockDiagonal' R * bankSupportMetric M F e = bankSupportMetric M F e * blockDiagonal' R ∧
      blockDiagonal' R * bankPolarOp M F e = bankPolarOp M F e * blockDiagonal' R ∧
      blockDiagonal' R * (bankPolarOp M F e)ᴴ = (bankPolarOp M F e)ᴴ * blockDiagonal' R) ↔
    (R (tgt e) * F e = F e * R (src e) ∧ R (src e) * (F e)ᴴ = (F e)ᴴ * R (tgt e)) := by
  obtain ⟨P, Pd, hP, hFUP, hPP, hUp, hPd1, hPd2⟩ := polarIsometry_spec (F e)
  have hsupp := support_commute_of_polar_data (F e) (polarIsometry (F e)) P Pd hP hFUP hPP hUp
    hPd1 hPd2
  have hmetric : bankSupportMetric M F e = blockEmbed M ((F e)ᴴ * F e) := by
    rw [bankSupportMetric, bankIncidenceOp, blockEmbed_conjTranspose, blockEmbed_mul_blockEmbed]
  rw [hmetric, bankPolarOp, blockEmbed_conjTranspose, blockDiagonal'_commute_blockEmbed_iff,
    blockDiagonal'_commute_blockEmbed_iff, blockDiagonal'_commute_blockEmbed_iff]
  have hpe := (polar_edge_singular (F e) (polarIsometry (F e)) P Pd (R (src e)) (R (tgt e)) hP
    hFUP hPP hUp hPd1 hPd2 hsupp).1
  rw [hPP] at hpe
  exact hpe.symm

theorem bankSupportPolarGenerators_starClosed :
    ∀ x ∈ bankSupportPolarGenerators M F, xᴴ ∈ bankSupportPolarGenerators M F := by
  rintro x (((⟨v, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩)
  · rw [vertexProjection_conjTranspose]
    exact Or.inl (Or.inl (Or.inl ⟨v, rfl⟩))
  · have : (bankSupportMetric M F e)ᴴ = bankSupportMetric M F e := by
      rw [bankSupportMetric, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [this]
    exact Or.inl (Or.inl (Or.inr ⟨e, rfl⟩))
  · exact Or.inr ⟨e, rfl⟩
  · simp only [conjTranspose_conjTranspose]
    exact Or.inl (Or.inr ⟨e, rfl⟩)

/-- `{Z_λ, F_e^*F_e, U_e, U_e^*}' = M_type` on `𝓜`. -/
theorem matCommutant_bankSupportPolarGenerators :
    matCommutant (bankSupportPolarGenerators M F) = bankMultiplicityCarrierAlgebra M F := by
  ext X
  constructor
  · intro hX
    have hZ : ∀ v, X * vertexProjection M v = vertexProjection M v * X :=
      fun v => hX _ (Or.inl (Or.inl (Or.inl ⟨v, rfl⟩)))
    have hXeq := eq_blockDiagonal'_of_commute_vertexProjection M X hZ
    refine ⟨diagBlock M X, ?_, hXeq.symm⟩
    intro e
    have h1 := hX _ (Or.inl (Or.inl (Or.inr ⟨e, rfl⟩)))
    have h2 := hX _ (Or.inl (Or.inr ⟨e, rfl⟩))
    have h3 := hX _ (Or.inr ⟨e, rfl⟩)
    rw [hXeq] at h1 h2 h3
    exact (bank_commute_edge_generators_iff M F _ e).mp ⟨h1, h2, h3⟩
  · rintro ⟨R, hR, rfl⟩ a ha
    have hR' : IsBankTypedMultiplicity M F R := hR
    rcases ha with ((⟨v, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩) | ⟨e, rfl⟩
    · exact blockDiagonal'_commute_vertexProjection M R v
    · exact ((bank_commute_edge_generators_iff M F R e).mpr (hR' e)).1
    · exact ((bank_commute_edge_generators_iff M F R e).mpr (hR' e)).2.1
    · exact ((bank_commute_edge_generators_iff M F R e).mpr (hR' e)).2.2

/-- **`(O_F^sup)' = M_type`** for an arbitrary bank. -/
theorem matCommutant_bankSupportPolarAlgebra :
    matCommutant ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) =
      bankMultiplicityCarrierAlgebra M F := by
  rw [bankSupportPolarAlgebra,
    matCommutant_starAlgebra_adjoin _ (bankSupportPolarGenerators_starClosed M F),
    matCommutant_bankSupportPolarGenerators]

/-- **`M_type' = O_F^sup`** for an arbitrary bank (finite bicommutant). -/
theorem matCommutant_bankMultiplicityCarrierAlgebra :
    matCommutant (bankMultiplicityCarrierAlgebra M F) =
      ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) := by
  rw [← matCommutant_bankSupportPolarAlgebra, matCommutant_matCommutant_starSubalgebra]

theorem bankIncidenceGenerators_starClosed :
    ∀ x ∈ bankIncidenceGenerators M F, xᴴ ∈ bankIncidenceGenerators M F := by
  rintro x ((⟨v, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩)
  · rw [vertexProjection_conjTranspose]
    exact Or.inl (Or.inl ⟨v, rfl⟩)
  · exact Or.inr ⟨e, rfl⟩
  · simp only [conjTranspose_conjTranspose]
    exact Or.inl (Or.inr ⟨e, rfl⟩)

theorem matCommutant_bankIncidenceGenerators :
    matCommutant (bankIncidenceGenerators M F) = bankMultiplicityCarrierAlgebra M F := by
  ext X
  constructor
  · intro hX
    have hZ : ∀ v, X * vertexProjection M v = vertexProjection M v * X :=
      fun v => hX _ (Or.inl (Or.inl ⟨v, rfl⟩))
    have hXeq := eq_blockDiagonal'_of_commute_vertexProjection M X hZ
    refine ⟨diagBlock M X, ?_, hXeq.symm⟩
    intro e
    have h1 := hX _ (Or.inl (Or.inr ⟨e, rfl⟩))
    have h2 := hX _ (Or.inr ⟨e, rfl⟩)
    simp only at h2
    rw [hXeq, bankIncidenceOp] at h1 h2
    rw [blockEmbed_conjTranspose] at h2
    exact ⟨(blockDiagonal'_commute_blockEmbed_iff M _ _).mp h1,
      (blockDiagonal'_commute_blockEmbed_iff M _ _).mp h2⟩
  · rintro ⟨R, hR, rfl⟩ a ha
    have hR' : IsBankTypedMultiplicity M F R := hR
    rcases ha with (⟨v, rfl⟩ | ⟨e, rfl⟩) | ⟨e, rfl⟩
    · exact blockDiagonal'_commute_vertexProjection M R v
    · exact (blockDiagonal'_commute_blockEmbed_iff M _ _).mpr (hR' e).1
    · simp only [bankIncidenceOp, blockEmbed_conjTranspose]
      exact (blockDiagonal'_commute_blockEmbed_iff M _ _).mpr (hR' e).2

/-- **`eq:incidence-support-polar-equality`** for an arbitrary bank. -/
theorem bank_incidence_support_polar_equality :
    bankIncidenceAlgebra M F = bankSupportPolarAlgebra M F := by
  apply SetLike.coe_injective
  have h1 : matCommutant ((bankIncidenceAlgebra M F : StarSubalgebra ℂ _) : Set _) =
      bankMultiplicityCarrierAlgebra M F := by
    rw [bankIncidenceAlgebra,
      matCommutant_starAlgebra_adjoin _ (bankIncidenceGenerators_starClosed M F),
      matCommutant_bankIncidenceGenerators]
  rw [← matCommutant_matCommutant_starSubalgebra (bankIncidenceAlgebra M F), h1,
    ← matCommutant_bankSupportPolarAlgebra, matCommutant_matCommutant_starSubalgebra]

/-- **Exact support-polar duality (`thm:support-polar`) for an arbitrary finite bank**
(several elements per vertex pair, loops, rectangular / singular / zero maps):
`M_type = (O_F^sup)'`, `O_F^sup = M_type'`, `C^*(Z_λ, F_e, F_e^*) = O_F^sup`. -/
theorem bank_exact_support_polar_duality :
    bankMultiplicityCarrierAlgebra M F =
        matCommutant ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) ∧
      ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) =
        matCommutant (bankMultiplicityCarrierAlgebra M F) ∧
      bankIncidenceAlgebra M F = bankSupportPolarAlgebra M F :=
  ⟨(matCommutant_bankSupportPolarAlgebra M F).symm,
    (matCommutant_bankMultiplicityCarrierAlgebra M F).symm,
    bank_incidence_support_polar_equality M F⟩

/-! ### Link with the intrinsic arrow spaces of a joint packet -/

section Packet

variable {M}

/-- Simultaneous commutation with `X` and `X^*`. -/
def StarCommutes (T X : Matrix (TotalCarrier M) (TotalCarrier M) ℂ) : Prop :=
  T * X = X * T ∧ T * Xᴴ = Xᴴ * T

/-- Star-commutation with a set is star-commutation with its linear span. -/
theorem starCommutes_span_iff (T : Matrix (TotalCarrier M) (TotalCarrier M) ℂ)
    (S : Set (Matrix (TotalCarrier M) (TotalCarrier M) ℂ)) :
    (∀ X ∈ Submodule.span ℂ S, StarCommutes T X) ↔ ∀ X ∈ S, StarCommutes T X := by
  constructor
  · intro h X hX
    exact h X (Submodule.subset_span hX)
  · intro h X hX
    induction hX using Submodule.span_induction with
    | mem X hX => exact h X hX
    | zero => simp [StarCommutes]
    | add X Y _ _ hX hY =>
        refine ⟨?_, ?_⟩
        · rw [Matrix.mul_add, Matrix.add_mul, hX.1, hY.1]
        · rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, hX.2, hY.2]
    | smul c X _ hX =>
        refine ⟨?_, ?_⟩
        · rw [Matrix.mul_smul, Matrix.smul_mul, hX.1]
        · rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, hX.2]

theorem starCommutes_blockEmbed_iff (R : ∀ l, Matrix (M l) (M l) ℂ) {u v : Λ}
    (A : Matrix (M v) (M u) ℂ) :
    StarCommutes (blockDiagonal' R) (blockEmbed M A) ↔
      R v * A = A * R u ∧ R u * Aᴴ = Aᴴ * R v := by
  rw [StarCommutes, blockEmbed_conjTranspose, blockDiagonal'_commute_blockEmbed_iff,
    blockDiagonal'_commute_blockEmbed_iff]

variable {V : Λ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
variable {Ep : Type*} [Fintype Ep] (P : RepresentedJointPacket Λ V M Ep)

/-- The bank `(F_e)` **spans the intrinsic arrow spaces** of the packet: placed on their
corners of `𝓜 = ⊕_λ M_λ`, the bank elements and the intrinsic coefficient spaces `𝔅_e`
(`eq:intrinsic-incidence-coefficients`) span the same operator space. -/
def SpansArrowSpaces : Prop :=
  Submodule.span ℂ (Set.range fun e => blockEmbed M (F e)) =
    Submodule.span ℂ (⋃ e', blockEmbed M ''
      (P.coefficientSpace e' : Set (Matrix (M (P.tgt e')) (M (P.src e')) ℂ)))

/-- Membership in the bank's typed algebra is star-commutation with the corner-embedded bank. -/
theorem isBankTypedMultiplicity_iff_starCommutes (R : ∀ l, Matrix (M l) (M l) ℂ) :
    IsBankTypedMultiplicity M F R ↔
      ∀ X ∈ Set.range (fun e => blockEmbed M (F e)), StarCommutes (blockDiagonal' R) X := by
  constructor
  · rintro hR _ ⟨e, rfl⟩
    exact (starCommutes_blockEmbed_iff R (F e)).mpr (hR e)
  · intro h e
    exact (starCommutes_blockEmbed_iff R (F e)).mp (h _ ⟨e, rfl⟩)

/-- Membership in the packet's `M_type` is star-commutation with every corner-embedded
intrinsic coefficient. -/
theorem isTypedMultiplicity_iff_starCommutes (R : ∀ l, Matrix (M l) (M l) ℂ) :
    P.IsTypedMultiplicity R ↔
      ∀ X ∈ ⋃ e', blockEmbed M ''
        (P.coefficientSpace e' : Set (Matrix (M (P.tgt e')) (M (P.src e')) ℂ)),
        StarCommutes (blockDiagonal' R) X := by
  constructor
  · intro hR X hX
    obtain ⟨e', B, hB, rfl⟩ := Set.mem_iUnion.mp hX
    exact (starCommutes_blockEmbed_iff R B).mpr (hR e' B hB)
  · intro h e' B hB
    exact (starCommutes_blockEmbed_iff R B).mp
      (h _ (Set.mem_iUnion.mpr ⟨e', B, hB, rfl⟩))

/-- **The bank's `M_type` is the paper's `M_type` (`eq:typed-multiplicity`)** whenever the
bank spans the intrinsic arrow spaces. -/
theorem bankTypedMultiplicityAlgebra_eq_packet (h : SpansArrowSpaces F P) :
    bankTypedMultiplicityAlgebra M F = P.typedMultiplicityAlgebra := by
  ext R
  rw [mem_bankTypedMultiplicityAlgebra, RepresentedJointPacket.mem_typedMultiplicityAlgebra,
    isBankTypedMultiplicity_iff_starCommutes, isTypedMultiplicity_iff_starCommutes,
    ← starCommutes_span_iff, ← starCommutes_span_iff]
  unfold SpansArrowSpaces at h
  rw [h]

/-- **`thm:support-polar` with the intrinsic `M_type`.**  For a represented joint packet and
any finite bank spanning its intrinsic arrow spaces (several elements per arrow space, loops,
arbitrary rank): `ι_𝓜(M_type) = (O_F^sup)'`, `O_F^sup = ι_𝓜(M_type)'` and
`C^*(Z_λ, F_e, F_e^*) = O_F^sup`, where `ι_𝓜(R) = ⊕_λ R_λ`. -/
theorem packet_support_polar_duality (h : SpansArrowSpaces F P) :
    (Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
          (P.typedMultiplicityAlgebra : Set (∀ l, Matrix (M l) (M l) ℂ)) =
        matCommutant ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) ∧
      ((bankSupportPolarAlgebra M F : StarSubalgebra ℂ _) : Set _) =
        matCommutant ((Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
          (P.typedMultiplicityAlgebra : Set (∀ l, Matrix (M l) (M l) ℂ))) ∧
      bankIncidenceAlgebra M F = bankSupportPolarAlgebra M F := by
  have hM : bankMultiplicityCarrierAlgebra M F =
      (Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
        (P.typedMultiplicityAlgebra : Set (∀ l, Matrix (M l) (M l) ℂ)) := by
    rw [bankMultiplicityCarrierAlgebra, bankTypedMultiplicityAlgebra_eq_packet F P h]
  rw [← hM]
  exact bank_exact_support_polar_duality M F

/-! #### The canonical bank of Hilbert–Schmidt coefficient blocks -/

/-- Index type of the canonical bank: an edge `e` and a matrix entry `(vb, va)` of
`B(K_{s(e)}, K_{t(e)})`. -/
abbrev SliceIndex := Σ e : Ep, (Fin 4 × V (P.tgt e)) × (Fin 4 × V (P.src e))

/-- The canonical bank `F_{e,a} = blockSlice (Y_e) a` of Hilbert–Schmidt coefficient blocks
of `Y_e = ∑_a D_{e,a} ⊗ F_{e,a}` (`eq:general-incidence-expansion`); several elements per
edge, loops whenever `s(e) = t(e)`. -/
def sliceBank (j : SliceIndex P) :
    Matrix (M (P.tgt j.1)) (M (P.src j.1)) ℂ :=
  SMSTQuiverCommutantAssembly.blockSlice (P.Y j.1) j.2.1 j.2.2

/-- The canonical slice bank has the packet's `M_type`. -/
theorem bankTypedMultiplicityAlgebra_sliceBank :
    bankTypedMultiplicityAlgebra M (sliceBank P) = P.typedMultiplicityAlgebra := by
  ext R
  rw [mem_bankTypedMultiplicityAlgebra, RepresentedJointPacket.mem_typedMultiplicityAlgebra,
    RepresentedJointPacket.isTypedMultiplicity_iff_blockSlice]
  constructor
  · intro h e vb va
    exact h ⟨e, vb, va⟩
  · rintro h ⟨e, vb, va⟩
    exact h e vb va

/-- The canonical slice bank spans the intrinsic arrow spaces. -/
theorem sliceBank_spansArrowSpaces : SpansArrowSpaces (sliceBank P) P := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨e, vb, va⟩, rfl⟩
    apply Submodule.subset_span
    refine Set.mem_iUnion.mpr ⟨e, _, ?_, rfl⟩
    rw [RepresentedJointPacket.coefficientSpace_eq_span_blockSlice]
    exact Submodule.subset_span ⟨(vb, va), rfl⟩
  · rw [Submodule.span_le]
    intro X hX
    obtain ⟨e, B, hB, rfl⟩ := Set.mem_iUnion.mp hX
    clear hX
    rw [SetLike.mem_coe, RepresentedJointPacket.coefficientSpace_eq_span_blockSlice] at hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
        obtain ⟨⟨vb, va⟩, rfl⟩ := hB
        exact Submodule.subset_span ⟨⟨e, vb, va⟩, rfl⟩
    | zero =>
        have : blockEmbed M (0 : Matrix (M (P.tgt e)) (M (P.src e)) ℂ) = 0 := by
          ext p q; simp [blockEmbed]
        rw [SetLike.mem_coe, this]
        exact Submodule.zero_mem _
    | add B C _ _ hB hC =>
        have : blockEmbed M (B + C) = blockEmbed M B + blockEmbed M C := by
          ext p q; simp only [blockEmbed, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
        rw [SetLike.mem_coe, this]
        exact Submodule.add_mem _ hB hC
    | smul c B _ hB =>
        have : blockEmbed M (c • B) = c • blockEmbed M B := by
          ext p q; simp only [blockEmbed, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ hB

/-- `thm:support-polar` for every represented joint packet, with the canonical slice bank. -/
theorem packet_support_polar_duality_sliceBank :
    (Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
          (P.typedMultiplicityAlgebra : Set (∀ l, Matrix (M l) (M l) ℂ)) =
        matCommutant ((bankSupportPolarAlgebra M (sliceBank P) : StarSubalgebra ℂ _) : Set _) ∧
      ((bankSupportPolarAlgebra M (sliceBank P) : StarSubalgebra ℂ _) : Set _) =
        matCommutant ((Matrix.blockDiagonal' : (∀ l, Matrix (M l) (M l) ℂ) → _) ''
          (P.typedMultiplicityAlgebra : Set (∀ l, Matrix (M l) (M l) ℂ))) ∧
      bankIncidenceAlgebra M (sliceBank P) = bankSupportPolarAlgebra M (sliceBank P) :=
  packet_support_polar_duality (sliceBank P) P (sliceBank_spansArrowSpaces P)

end Packet

/-- Non-vacuity: a one-vertex bank with two parallel loops `E_{01}, E_{10}` on `M = ℂ²`
(a multi-edge loop bank, not expressible as a `SimpleGraph` edge family). -/
example :
    bankMultiplicityCarrierAlgebra (fun _ : Unit => Fin 2)
        (src := fun _ : Fin 2 => ()) (tgt := fun _ : Fin 2 => ())
        (fun i => if i = 0 then Matrix.single 0 1 1 else Matrix.single 1 0 1) =
      matCommutant ((bankSupportPolarAlgebra (fun _ : Unit => Fin 2)
        (src := fun _ : Fin 2 => ()) (tgt := fun _ : Fin 2 => ())
        (fun i => if i = 0 then Matrix.single 0 1 1 else Matrix.single 1 0 1) :
          StarSubalgebra ℂ _) : Set _) :=
  (bank_exact_support_polar_duality _ _).1

end SupportPolarBank

end RenewalGeometry
