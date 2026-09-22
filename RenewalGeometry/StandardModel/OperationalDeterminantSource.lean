/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.StandardModel.SMGaugeQuotientExact
import RenewalGeometry.StandardModel.DeterminantIncidenceExact

/-!
# Determinant seed stabilizer and the positive operational source criterion

Covers `definition:determinant-seed` (normalization and phase independence of
the determinant seed `τ : det C ⊗ det W₂ ≃ ℂ`) and
`prop:operational-determinant-source` (positive operational source criterion
for the determinant group) of the spacetime/gauge duality manuscript.

* A group `G` acting on a vector through a character `χ : G →* unitary ℂ`
  has stabilizer `ker χ` at every nonzero vector and the whole group at zero
  (`characterStabilizer_eq_ker`, `characterStabilizer_zero`); the stabilizer is
  unchanged by rescaling the vector (`characterStabilizer_smul`), which is the
  manuscript's remark that an overall phase of `τ` is irrelevant.
* `theta_unit_normalized`: the seed shadow `Θ_τ` is unit-normalized exactly
  when `|τ|² = 1/6`.
* `determinantSeedStabilizer_eq_SMGaugeGroup`: the stabilizer of a nonzero
  determinant seed inside `U(3) × U(2)` is `S(U(3) × U(2))`.
* `MarkedSectorPacket`: two marked coherent amplitude sectors (diagonal
  masses, characters `1` and `χ⁻¹`, hence invariant) with a Choi cross block
  `J₀₁` transforming by the relative character `χ⁻¹`; `hDet = ‖J₀₁‖²_HS`.
* `packetStabilizer_eq_ker_of_hDet_pos`: if `h_det > 0` the stabilizer of the
  marked positive subpacket is exactly `ker χ`;
  `packetStabilizer_eq_top_of_hDet_zero`: if `h_det = 0` the whole group
  fixes the packet, so the diagonal masses alone do not imply `ker χ`
  (`SMGaugeGroup_ne_top` records that `ker χ` is a proper subgroup).
* `operational_determinant_source`: the Standard-Model instance with
  `χ = det A det B` on `U(3) × U(2)`.
-/

open Matrix

namespace RenewalGeometry
namespace OperationalDeterminantSource

noncomputable section

section CharacterStabilizer

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The stabilizer of a vector `x` under the scalar action of `G` through the
unitary character `χ`, i.e. `{g | χ(g) • x = x}`. -/
def characterStabilizer (χ : G →* unitary ℂ) (x : M) : Subgroup G where
  carrier := {g | ((χ g : unitary ℂ) : ℂ) • x = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul, Submonoid.coe_mul] at ha hb ⊢
    rw [mul_smul, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv]
    calc (((χ a)⁻¹ : unitary ℂ) : ℂ) • x
        = (((χ a)⁻¹ : unitary ℂ) : ℂ) • (((χ a : unitary ℂ) : ℂ) • x) := by rw [ha]
      _ = x := by
          rw [smul_smul, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
            one_smul]

theorem mem_characterStabilizer_iff (χ : G →* unitary ℂ) (x : M) (g : G) :
    g ∈ characterStabilizer χ x ↔ ((χ g : unitary ℂ) : ℂ) • x = x :=
  Iff.rfl

/-- A unitary scalar fixing a nonzero vector is `1`. -/
theorem eq_one_of_smul_eq_self [NoZeroSMulDivisors ℂ M] {c : ℂ} {x : M}
    (hx : x ≠ 0) (h : c • x = x) : c = 1 := by
  have h0 : (c - 1) • x = 0 := by rw [sub_smul, one_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with hc | hc
  · exact sub_eq_zero.mp hc
  · exact absurd hc hx

/-- At a nonzero vector the character stabilizer is exactly `ker χ`. -/
theorem characterStabilizer_eq_ker [NoZeroSMulDivisors ℂ M] (χ : G →* unitary ℂ)
    {x : M} (hx : x ≠ 0) : characterStabilizer χ x = χ.ker := by
  ext g
  rw [mem_characterStabilizer_iff, MonoidHom.mem_ker]
  constructor
  · intro h
    exact Subtype.ext (eq_one_of_smul_eq_self hx h)
  · intro h
    rw [h, OneMemClass.coe_one, one_smul]

/-- At the zero vector every group element is in the stabilizer. -/
theorem characterStabilizer_zero (χ : G →* unitary ℂ) :
    characterStabilizer χ (0 : M) = ⊤ := by
  ext g
  simp [mem_characterStabilizer_iff]

/-- Rescaling the vector (e.g. by a phase) does not change the stabilizer:
the manuscript's remark that only the line of `τ` is physically relevant. -/
theorem characterStabilizer_smul (χ : G →* unitary ℂ) (x : M) {c : ℂ} (hc : c ≠ 0) :
    characterStabilizer χ (c • x) = characterStabilizer χ x := by
  ext g
  simp only [mem_characterStabilizer_iff, smul_comm ((χ g : unitary ℂ) : ℂ) c x]
  exact smul_right_injective M hc |>.eq_iff

end CharacterStabilizer

section DeterminantSeed

open DetIncidence

/-- `definition:determinant-seed`, normalization clause: the seed shadow
`Θ_τ` has unit Hilbert–Schmidt weight exactly when `|τ|² = 1/6`. -/
theorem theta_unit_normalized (τ : ℂ) :
    shadowNormSq (theta τ) = 1 ↔ Complex.normSq τ = 6⁻¹ := by
  rw [theta_norm]
  constructor
  · intro h
    have : Complex.normSq τ = 1 / 6 := by linarith
    rw [this]; norm_num
  · intro h
    rw [h]; norm_num

/-- The stabilizer of the determinant seed `τ ∈ ℂ ≅ (det C ⊗ det W₂)^*`
inside `U(C) × U(W₂) = U(3) × U(2)`, the pairs `(A,B)` with
`det A det B · τ = τ`. -/
def determinantSeedStabilizer (τ : ℂ) : Subgroup (SMGaugeU3 × SMGaugeU2) :=
  characterStabilizer determinantProductHom τ

/-- `definition:determinant-seed` / `thm:gauge-group`: a nonzero determinant
seed has stabilizer `S(U(3) × U(2)) = ker (det A det B)`. -/
theorem determinantSeedStabilizer_eq_SMGaugeGroup {τ : ℂ} (hτ : τ ≠ 0) :
    determinantSeedStabilizer τ = SMGaugeGroup :=
  characterStabilizer_eq_ker determinantProductHom hτ

/-- Phase independence of the determinant seed stabilizer. -/
theorem determinantSeedStabilizer_phase (τ : ℂ) {c : ℂ} (hc : c ≠ 0) :
    determinantSeedStabilizer (c * τ) = determinantSeedStabilizer τ :=
  characterStabilizer_smul determinantProductHom τ hc

end DeterminantSeed

section MarkedPacket

variable {G : Type*} [Group G] {p q : Type*} [Fintype p] [Fintype q]

/-- The marked positive subpacket of a typed incidence instrument: two
coherent amplitude sectors with diagonal Choi blocks `J₀₀`, `J₁₁` and the
Choi cross block `J₀₁`. -/
@[ext]
structure MarkedSectorPacket (p q : Type*) where
  /-- Diagonal Choi block of the sector carrying the trivial character. -/
  diag0 : Matrix p p ℂ
  /-- Diagonal Choi block of the sector carrying the character `χ⁻¹`. -/
  diag1 : Matrix q q ℂ
  /-- The Choi cross block `J₀₁` between the two marked sectors. -/
  cross : Matrix p q ℂ

/-- The action of `g` on the marked packet when the two sectors carry the
characters `1` and `χ⁻¹`: the diagonal blocks are invariant (characters
`1·1̄ = 1` and `χ⁻¹·χ = 1`), the cross block transforms by the relative
character `χ(g)⁻¹`. -/
def packetAction (χ : G →* unitary ℂ) (g : G) (P : MarkedSectorPacket p q) :
    MarkedSectorPacket p q where
  diag0 := P.diag0
  diag1 := P.diag1
  cross := (((χ g)⁻¹ : unitary ℂ) : ℂ) • P.cross

/-- The determinant cross mass `h_det = ‖J₀₁‖²_HS`
(`eq:determinant-cross-mass`). -/
def hDet (P : MarkedSectorPacket p q) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (P.cross i j)

theorem hDet_nonneg (P : MarkedSectorPacket p q) : 0 ≤ hDet P :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem hDet_eq_zero_iff (P : MarkedSectorPacket p q) : hDet P = 0 ↔ P.cross = 0 := by
  constructor
  · intro h
    unfold hDet at h
    ext i j
    have hi : ∑ j, Complex.normSq (P.cross i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).mp h i
        (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp hi j (Finset.mem_univ j)
    simpa [Complex.normSq_eq_zero] using hij
  · intro h
    simp [hDet, h]

theorem hDet_pos_iff (P : MarkedSectorPacket p q) : 0 < hDet P ↔ P.cross ≠ 0 := by
  rw [← not_iff_not, not_lt, not_not]
  constructor
  · intro h
    exact (hDet_eq_zero_iff P).mp (le_antisymm h (hDet_nonneg P))
  · intro h
    exact ((hDet_eq_zero_iff P).mpr h).le

/-- The stabilizer of the marked positive subpacket. -/
def packetStabilizer (χ : G →* unitary ℂ) (P : MarkedSectorPacket p q) : Subgroup G :=
  characterStabilizer (χ⁻¹) P.cross

omit [Fintype p] [Fintype q] in
theorem mem_packetStabilizer_iff (χ : G →* unitary ℂ) (P : MarkedSectorPacket p q)
    (g : G) : g ∈ packetStabilizer χ P ↔ packetAction χ g P = P := by
  rw [packetStabilizer, mem_characterStabilizer_iff]
  constructor
  · intro h
    ext1
    · rfl
    · rfl
    · simpa [packetAction] using h
  · intro h
    have := congrArg MarkedSectorPacket.cross h
    simpa [packetAction] using this

theorem ker_inv (χ : G →* unitary ℂ) : (χ⁻¹).ker = χ.ker := by
  ext g
  simp [MonoidHom.mem_ker]

/-- `prop:operational-determinant-source`, positive branch: if `h_det > 0`
the stabilizer of the marked positive subpacket is exactly `ker χ`. -/
theorem packetStabilizer_eq_ker_of_hDet_pos (χ : G →* unitary ℂ)
    (P : MarkedSectorPacket p q) (h : 0 < hDet P) :
    packetStabilizer χ P = χ.ker := by
  rw [packetStabilizer, characterStabilizer_eq_ker _ ((hDet_pos_iff P).mp h), ker_inv]

/-- `prop:operational-determinant-source`, vanishing branch: if `h_det = 0`
every group element fixes the packet (independent phase rotation of the two
diagonal sectors is undetected), so the packet does not imply `ker χ`. -/
theorem packetStabilizer_eq_top_of_hDet_zero (χ : G →* unitary ℂ)
    (P : MarkedSectorPacket p q) (h : hDet P = 0) :
    packetStabilizer χ P = ⊤ := by
  rw [packetStabilizer, (hDet_eq_zero_iff P).mp h, characterStabilizer_zero]

end MarkedPacket

section StandardModel

/-- The element `(-I₃, I₂)` of `U(3) × U(2)` has `det A det B = -1`. -/
theorem SMGaugeGroup_ne_top : (SMGaugeGroup : Subgroup (SMGaugeU3 × SMGaugeU2)) ≠ ⊤ := by
  intro htop
  have hmem : ((-1 : SMGaugeU3), (1 : SMGaugeU2)) ∈ SMGaugeGroup := by
    rw [htop]; exact Subgroup.mem_top _
  rw [SMGaugeGroup, MonoidHom.mem_ker] at hmem
  have hval := congrArg (fun z : unitary ℂ => (z : ℂ)) hmem
  simp only [determinantProductHom, unitaryDetHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_mul, OneMemClass.coe_one, Unitary.coe_neg] at hval
  rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at hval
  norm_num at hval

/-- **`prop:operational-determinant-source`** for the Standard-Model
character `χ(A,B) = det A det B` on `U(3) × U(2)`.  If `h_det = ‖J₀₁‖²_HS > 0`
the stabilizer of the marked positive subpacket is exactly
`ker χ = S(U(3) × U(2))`; if `h_det = 0` the whole group `U(3) × U(2)` fixes
the packet, which is strictly larger than `S(U(3) × U(2))`. -/
theorem operational_determinant_source {p q : Type*} [Fintype p] [Fintype q]
    (P : MarkedSectorPacket p q) :
    (0 < hDet P → packetStabilizer determinantProductHom P = SMGaugeGroup) ∧
    (hDet P = 0 → packetStabilizer determinantProductHom P = ⊤ ∧
      packetStabilizer determinantProductHom P ≠ SMGaugeGroup) := by
  refine ⟨fun h => packetStabilizer_eq_ker_of_hDet_pos _ P h, fun h => ?_⟩
  have htop := packetStabilizer_eq_top_of_hDet_zero determinantProductHom P h
  exact ⟨htop, by rw [htop]; exact SMGaugeGroup_ne_top.symm⟩

end StandardModel

end

end OperationalDeterminantSource
end RenewalGeometry
