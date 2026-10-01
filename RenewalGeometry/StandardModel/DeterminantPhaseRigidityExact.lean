/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.OperationalDeterminantSource

/-!
# Determinant phase rigidity and the packet-extension clause (`thm:gauge-group`)

Completes `thm:gauge-group` (Gauge-group reconstruction and the phase-sensitive criterion) of
the spacetime–gauge duality manuscript on top of `OperationalDeterminantSource.lean`.

* `MarkedSectorPacket.toMatrix`: the full Hermitian marked packet
  `J = (J₀₀, J₀D; J₀D^*, J_DD)` as a block matrix on `𝒱₀ ⊕ 𝖲_nat`;
* `packetAction_toMatrix_sub_hsNormSq`: the Hilbert–Schmidt displacement
  `‖ℛ(g) J ℛ(g)^* − J‖²_HS = 2 |χ(g)⁻¹ − 1|² h_det`;
* `determinant_phase_rigidity`: for `χ(g) = e^{iφ}`,
  `‖ℛ(g) J ℛ(g)^* − J‖²_HS = 8 h_det sin²(φ/2)` (`eq:determinant-phase-rigidity`);
* `hDet_pos_iff_packetStabilizer_eq_ker`: `h_det > 0 ⟺ Stab(J) = ker χ` for a nontrivial
  character (`eq:operational-determinant-group`, both directions);
* `mem_extendedStabilizer_iff`, `extendedStabilizer_eq_ker_iff`: a larger marked packet
  carrying further retained components has stabilizer the intersection of the componentwise
  stabilizers, which is `ker χ` exactly when every further component is `ker χ`-invariant;
* `gauge_group_phase_sensitive`: the assembled statement (with the seed stabilizer
  `S(U(3) × U(2)) = ker (det A det B)` from `determinantSeedStabilizer_eq_SMGaugeGroup`; the
  isomorphism with `(SU(3) × SU(2) × U(1))/ℤ₆` is `smGaugeQuotientEquiv`).
-/

open Matrix

namespace RenewalGeometry
namespace OperationalDeterminantSource

noncomputable section

section HilbertSchmidt

variable {m k : Type*} [Fintype m] [Fintype k]

/-- The squared Hilbert–Schmidt norm `∑_{ij} |X_{ij}|²`. -/
def hsNormSq (X : Matrix m k ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (X i j)

theorem hsNormSq_nonneg (X : Matrix m k ℂ) : 0 ≤ hsNormSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

@[simp] theorem hsNormSq_zero : hsNormSq (0 : Matrix m k ℂ) = 0 := by
  simp [hsNormSq]

theorem hsNormSq_conjTranspose (X : Matrix m k ℂ) : hsNormSq Xᴴ = hsNormSq X := by
  unfold hsNormSq
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply, Complex.normSq_conj]

theorem hsNormSq_smul (c : ℂ) (X : Matrix m k ℂ) :
    hsNormSq (c • X) = Complex.normSq c * hsNormSq X := by
  simp [hsNormSq, Complex.normSq_mul, Finset.mul_sum]

/-- `h_det` is the squared Hilbert–Schmidt norm of the cross block. -/
theorem hDet_eq_hsNormSq {p q : Type*} [Fintype p] [Fintype q] (P : MarkedSectorPacket p q) :
    hDet P = hsNormSq P.cross := rfl

variable {m' k' : Type*} [Fintype m'] [Fintype k']

theorem hsNormSq_fromBlocks (A : Matrix m k ℂ) (B : Matrix m k' ℂ) (C : Matrix m' k ℂ)
    (D : Matrix m' k' ℂ) :
    hsNormSq (Matrix.fromBlocks A B C D) = hsNormSq A + hsNormSq B + hsNormSq C + hsNormSq D := by
  simp only [hsNormSq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

end HilbertSchmidt

section PhaseRigidity

variable {G : Type*} [Group G] {p q : Type*} [Fintype p] [Fintype q]

/-- The full Hermitian marked packet `J = (J₀₀, J₀D; J₀D^*, J_DD)` on `𝒱₀ ⊕ 𝖲_nat`. -/
def MarkedSectorPacket.toMatrix (P : MarkedSectorPacket p q) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  Matrix.fromBlocks P.diag0 P.cross P.crossᴴ P.diag1

omit [Fintype p] [Fintype q] in
/-- The transformed full packet differs from `J` only in the two cross blocks. -/
theorem packetAction_toMatrix_sub (χ : G →* unitary ℂ) (g : G) (P : MarkedSectorPacket p q) :
    (packetAction χ g P).toMatrix - P.toMatrix =
      Matrix.fromBlocks 0 (((((χ g)⁻¹ : unitary ℂ) : ℂ) - 1) • P.cross)
        (((((χ g)⁻¹ : unitary ℂ) : ℂ) - 1) • P.cross)ᴴ 0 := by
  ext (i | i) (j | j)
  · simp [MarkedSectorPacket.toMatrix, packetAction]
  · simp [MarkedSectorPacket.toMatrix, packetAction, sub_smul]
  · simp [MarkedSectorPacket.toMatrix, packetAction, Matrix.conjTranspose_apply, sub_mul]
  · simp [MarkedSectorPacket.toMatrix, packetAction]

/-- `‖ℛ(g) J ℛ(g)^* − J‖²_HS = 2 |χ(g)⁻¹ − 1|² h_det`: the two orthogonal cross blocks
contribute equally, the diagonal blocks are invariant. -/
theorem packetAction_toMatrix_sub_hsNormSq (χ : G →* unitary ℂ) (g : G)
    (P : MarkedSectorPacket p q) :
    hsNormSq ((packetAction χ g P).toMatrix - P.toMatrix) =
      2 * Complex.normSq ((((χ g)⁻¹ : unitary ℂ) : ℂ) - 1) * hDet P := by
  rw [packetAction_toMatrix_sub, hsNormSq_fromBlocks, hsNormSq_conjTranspose,
    hsNormSq_smul, hDet_eq_hsNormSq]
  simp only [hsNormSq_zero]
  ring

/-- `|e^{iφ} − 1|² = 4 sin²(φ/2)`. -/
theorem normSq_exp_sub_one (φ : ℝ) :
    Complex.normSq (Complex.exp (φ * Complex.I) - 1) = 4 * Real.sin (φ / 2) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
  have h2 : 2 * (φ / 2) = φ := by ring
  have hc := Real.cos_sq (φ / 2)
  rw [h2] at hc
  have hs := Real.sin_sq (φ / 2)
  have hpyth := Real.sin_sq_add_cos_sq φ
  nlinarith [hc, hs, hpyth]

/-- The inverse of a unitary scalar is its conjugate. -/
theorem coe_unitary_inv (u : unitary ℂ) : ((u⁻¹ : unitary ℂ) : ℂ) = star (u : ℂ) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]

/-- **`eq:determinant-phase-rigidity`.**  For `χ(g) = e^{iφ}`,
`‖ℛ(g) J ℛ(g)^* − J‖²_HS = 8 h_det sin²(φ/2)`. -/
theorem determinant_phase_rigidity (χ : G →* unitary ℂ) (g : G) (P : MarkedSectorPacket p q)
    (φ : ℝ) (hφ : ((χ g : unitary ℂ) : ℂ) = Complex.exp (φ * Complex.I)) :
    hsNormSq ((packetAction χ g P).toMatrix - P.toMatrix) =
      8 * hDet P * Real.sin (φ / 2) ^ 2 := by
  rw [packetAction_toMatrix_sub_hsNormSq, coe_unitary_inv, hφ]
  have hconj : star (Complex.exp (φ * Complex.I)) - 1
      = (starRingEnd ℂ) (Complex.exp (φ * Complex.I) - 1) := by
    simp
  rw [hconj, Complex.normSq_conj, normSq_exp_sub_one]
  ring

/-- **`eq:operational-determinant-group`**, both directions: for a nontrivial character,
`h_det > 0 ⟺ Stab(J) = ker χ`. -/
theorem hDet_pos_iff_packetStabilizer_eq_ker (χ : G →* unitary ℂ) (hχ : χ.ker ≠ ⊤)
    (P : MarkedSectorPacket p q) :
    0 < hDet P ↔ packetStabilizer χ P = χ.ker := by
  constructor
  · exact packetStabilizer_eq_ker_of_hDet_pos χ P
  · intro h
    by_contra hpos
    have h0 : hDet P = 0 := le_antisymm (not_lt.mp hpos) (hDet_nonneg P)
    exact hχ (by rw [← h, packetStabilizer_eq_top_of_hDet_zero χ P h0])

/-- The stabilizer of a larger marked packet: the marked positive subpacket `J` together with a
family of further retained components `x i` on which the group acts. -/
def extendedStabilizer (χ : G →* unitary ℂ) (P : MarkedSectorPacket p q)
    {E : Type*} [MulAction G E] {ι : Type*} (x : ι → E) : Subgroup G :=
  packetStabilizer χ P ⊓ ⨅ i, MulAction.stabilizer G (x i)

omit [Fintype p] [Fintype q] in
/-- Membership in the extended stabilizer is fixing the packet and every further component:
stabilizers of additional marked data are intersected. -/
theorem mem_extendedStabilizer_iff (χ : G →* unitary ℂ) (P : MarkedSectorPacket p q)
    {E : Type*} [MulAction G E] {ι : Type*} (x : ι → E) (g : G) :
    g ∈ extendedStabilizer χ P x ↔ packetAction χ g P = P ∧ ∀ i, g • x i = x i := by
  simp only [extendedStabilizer, Subgroup.mem_inf, mem_packetStabilizer_iff, Subgroup.mem_iInf,
    MulAction.mem_stabilizer_iff]

/-- **Packet-extension clause of `thm:gauge-group`.**  When `h_det > 0`, the larger marked
packet has stabilizer `ker χ` exactly when every further retained component is
`ker χ`-invariant. -/
theorem extendedStabilizer_eq_ker_iff (χ : G →* unitary ℂ) (P : MarkedSectorPacket p q)
    (h : 0 < hDet P) {E : Type*} [MulAction G E] {ι : Type*} (x : ι → E) :
    extendedStabilizer χ P x = χ.ker ↔ ∀ i, ∀ g ∈ χ.ker, g • x i = x i := by
  rw [extendedStabilizer, packetStabilizer_eq_ker_of_hDet_pos χ P h, inf_eq_left, le_iInf_iff]
  simp only [SetLike.le_def, MulAction.mem_stabilizer_iff]

end PhaseRigidity

section StandardModel

/-- **`thm:gauge-group` (Gauge-group reconstruction and the phase-sensitive criterion),
assembled** for `χ(A,B) = det A det B` on `U(3) × U(2)`.

1. `eq:SM-gauge-group`: the unitary stabilizer of a nonzero phase-sensitive determinant seed
   is `S(U(3) × U(2)) = ker χ` (`SMGaugeGroup`; its presentation
   `(SU(3) × SU(2) × U(1))/ℤ₆` is `smGaugeQuotientEquiv`);
2. `eq:operational-determinant-group`: `h_det > 0 ⟺ Stab(J) = ker χ`, and if `h_det = 0` the
   whole group `U(3) × U(2) ≠ ker χ` fixes the marked packet whatever `J_DD` is;
3. `eq:determinant-phase-rigidity`: `‖ℛ(g) J ℛ(g)^* − J‖²_HS = 8 h_det sin²(φ/2)` for
   `χ(g) = e^{iφ}`;
4. a larger marked packet has stabilizer `ker χ` exactly when its further retained
   components are `ker χ`-invariant, the stabilizers being intersected. -/
theorem gauge_group_phase_sensitive {p q : Type*} [Fintype p] [Fintype q]
    (P : MarkedSectorPacket p q) :
    (∀ τ : ℂ, τ ≠ 0 → determinantSeedStabilizer τ = SMGaugeGroup)
    ∧ (0 < hDet P ↔ packetStabilizer determinantProductHom P = SMGaugeGroup)
    ∧ (hDet P = 0 → packetStabilizer determinantProductHom P = ⊤ ∧
        packetStabilizer determinantProductHom P ≠ SMGaugeGroup)
    ∧ (∀ (g : SMGaugeU3 × SMGaugeU2) (φ : ℝ),
        ((determinantProductHom g : unitary ℂ) : ℂ) = Complex.exp (φ * Complex.I) →
        hsNormSq ((packetAction determinantProductHom g P).toMatrix - P.toMatrix) =
          8 * hDet P * Real.sin (φ / 2) ^ 2)
    ∧ (0 < hDet P → ∀ {E : Type} [MulAction (SMGaugeU3 × SMGaugeU2) E] {ι : Type} (x : ι → E),
        extendedStabilizer determinantProductHom P x = SMGaugeGroup ↔
          ∀ i, ∀ g ∈ SMGaugeGroup, g • x i = x i) := by
  refine ⟨fun τ hτ => determinantSeedStabilizer_eq_SMGaugeGroup hτ,
    hDet_pos_iff_packetStabilizer_eq_ker determinantProductHom SMGaugeGroup_ne_top P,
    (operational_determinant_source P).2,
    fun g φ hφ => determinant_phase_rigidity determinantProductHom g P φ hφ,
    fun h => by
      intro E _ ι x
      exact extendedStabilizer_eq_ker_iff determinantProductHom P h x⟩

end StandardModel

end

end OperationalDeterminantSource
end RenewalGeometry
