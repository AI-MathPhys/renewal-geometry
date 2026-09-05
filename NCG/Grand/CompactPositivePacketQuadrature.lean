/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CompactHaarRankOneAverage
import NCG.Grand.CompactOrbitConvexHull
import NCG.Grand.SMPositivePacketOrbit

/-!
# Exact finite quadrature for a compact positive-packet orbit

This file proves the compact-Haar form of
`cor:SM-finite-positive-packet-orbit`.  A continuous compact group orbit of a
positive semidefinite `d × d` packet is Hermitian.  Its normalized Haar
barycenter belongs to the (non-closed) real convex hull of the orbit because:

* Hermitian Carathéodory gives a uniform `d² + 1` quadrature bound;
* that bound makes the orbit convex hull compact and closed; and
* Jensen's integral theorem therefore places the Haar barycenter in it.

Applying the same Hermitian Carathéodory theorem once more produces an exact
positive quadrature with at most `d² + 1` orbit nodes.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace NCG
namespace CompactPositivePacketQuadrature

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]

variable {d : ℕ} [Nonempty (Fin d)]

noncomputable local instance matrixContinuousENorm :
    ContinuousENorm (Matrix (Fin d) (Fin d) ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _
    Matrix.seminormedAddCommGroup.toSeminormedAddGroup

/-- The conjugation orbit of a matrix packet. -/
def packetOrbit (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin d) ℂ) (g : G) :
    Matrix (Fin d) (Fin d) ℂ :=
  ρ g * J * (ρ g)ᴴ

/-- The normalized compact-Haar barycenter of a packet orbit. -/
noncomputable def packetAverage (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ g : G, packetOrbit ρ J g
    ∂CompactHaarRankOneAverage.normalizedHaar G

theorem continuous_packetOrbit (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ : Continuous ρ) (J : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (packetOrbit ρ J) := by
  unfold packetOrbit
  fun_prop

/-- Conjugating one orbit point translates its group parameter on the left. -/
theorem packetOrbit_mul (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (J : Matrix (Fin d) (Fin d) ℂ) (h g : G) :
    ρ h * packetOrbit ρ J g * (ρ h)ᴴ = packetOrbit ρ J (h * g) := by
  unfold packetOrbit
  rw [hρmul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem integrable_packetOrbit (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ : Continuous ρ) (J : Matrix (Fin d) (Fin d) ℂ) :
    Integrable (packetOrbit ρ J)
      (CompactHaarRankOneAverage.normalizedHaar G) := by
  have hc := continuous_packetOrbit ρ hρ J
  exact integrableOn_univ.mp
    (hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
      MeasurableSet.univ Subset.rfl
      (measure_ne_top (CompactHaarRankOneAverage.normalizedHaar G) Set.univ))

set_option maxHeartbeats 1600000 in
-- Instantiating compact Carathéodory on the `d × d` Hermitian carrier is elaboration-heavy.
/-- The normalized Haar barycenter lies in the ordinary real convex hull of
the compact orbit (not merely in its closure). -/
theorem packetAverage_mem_convexHull (ρ : G → Matrix (Fin d) (Fin d) ℂ)
    (hρ : Continuous ρ) (J : Matrix (Fin d) (Fin d) ℂ)
    (hJ : J.PosSemidef) :
    packetAverage ρ J ∈ convexHull ℝ (Set.range (packetOrbit ρ J)) := by
  let orbit := packetOrbit ρ J
  have horbit : Continuous orbit := continuous_packetOrbit ρ hρ J
  have hHerm : ∀ g, (orbit g).IsHermitian := by
    intro g
    exact (hJ.mul_mul_conjTranspose_same (ρ g)).1
  have hquad : ∀ x ∈ convexHull ℝ (Set.range orbit),
      ∃ (L : ℕ) (w : Fin L → ℝ) (g : Fin L → G),
        L ≤ d ^ 2 + 1 ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
          x = ∑ i, w i • orbit (g i) := by
    intro x hx
    exact finite_hermitian_quadrature_of_mem_convexHull orbit hHerm x hx
  have hclosed : IsClosed (convexHull ℝ (Set.range orbit)) :=
    CompactOrbitConvexHull.isClosed_convexHull_range_of_uniform_quadrature
      orbit horbit (d ^ 2 + 1) hquad
  have hmem : (∫ g : G, orbit g
      ∂CompactHaarRankOneAverage.normalizedHaar G) ∈
      convexHull ℝ (Set.range orbit) := by
    apply (convex_convexHull ℝ (Set.range orbit)).integral_mem hclosed
    · filter_upwards [] with g
      exact subset_convexHull ℝ (Set.range orbit) (Set.mem_range_self g)
    · exact integrable_packetOrbit ρ hρ J
  exact hmem

/-- **Compact positive-packet quadrature.**  The normalized Haar average of a
continuous compact conjugation orbit has an exact positive quadrature with at
most `d² + 1` nodes. -/
theorem compact_positive_packet_quadrature
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (J : Matrix (Fin d) (Fin d) ℂ) (hJ : J.PosSemidef) :
    ∃ (L : ℕ) (w : Fin L → ℝ) (g : Fin L → G),
      L ≤ d ^ 2 + 1 ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        packetAverage ρ J =
          ∑ i, w i • packetOrbit ρ J (g i) := by
  have hHerm : ∀ g, (packetOrbit ρ J g).IsHermitian := by
    intro g
    exact (hJ.mul_mul_conjTranspose_same (ρ g)).1
  exact finite_hermitian_quadrature_of_mem_convexHull
    (packetOrbit ρ J) hHerm (packetAverage ρ J)
    (packetAverage_mem_convexHull ρ hρ J hJ)

/-- A compact-Haar average of a positive packet is positive semidefinite.  The
proof uses the exact finite positive quadrature, so no order/integral exchange
is left implicit. -/
theorem packetAverage_posSemidef
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (J : Matrix (Fin d) (Fin d) ℂ) (hJ : J.PosSemidef) :
    (packetAverage ρ J).PosSemidef := by
  classical
  obtain ⟨L, w, g, _hL, hw0, _hw1, havg⟩ :=
    compact_positive_packet_quadrature ρ hρ J hJ
  rw [havg]
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  have horbit : (packetOrbit ρ J (g i)).PosSemidef :=
    hJ.mul_mul_conjTranspose_same (ρ (g i))
  have hwi : (0 : ℂ) ≤ (w i : ℂ) := by
    rw [Complex.zero_le_real]
    exact hw0 i
  have hsmul := horbit.smul hwi
  simpa [Complex.real_smul] using hsmul

/-- In a positive weighted sum of PSD matrices, every term carrying strictly
positive weight kills any vector killed by the sum. -/
lemma positive_weight_term_mulVec_eq_zero
    {L : ℕ} (A : Fin L → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (w : Fin L → ℝ)
    (hw : ∀ i, 0 ≤ w i) {i : Fin L} (hwi : 0 < w i)
    {x : Fin d → ℂ} (hsumx : (∑ j, w j • A j) *ᵥ x = 0) :
    A i *ᵥ x = 0 := by
  have hform0 : star x ⬝ᵥ ((∑ j, w j • A j) *ᵥ x) = 0 := by
    rw [hsumx, dotProduct_zero]
  rw [Matrix.sum_mulVec, dotProduct_sum] at hform0
  have hnonneg : ∀ j : Fin L,
      (0 : ℂ) ≤ star x ⬝ᵥ ((w j • A j) *ᵥ x) := by
    intro j
    rw [Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul]
    have hwc : (0 : ℂ) ≤ (w j : ℂ) := by
      rw [Complex.zero_le_real]
      exact hw j
    exact mul_nonneg hwc ((hA j).dotProduct_mulVec_nonneg x)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => hnonneg j)).mp hform0 i (Finset.mem_univ i)
  rw [Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul] at hterm
  have hwne : (w i : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hwi
  have hquad : star x ⬝ᵥ (A i *ᵥ x) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hwne
  exact posSemidef_mulVec_eq_zero_of_form_eq_zero (hA i) hquad

/-- The compact-Haar packet average commutes with the representation. -/
theorem packetAverage_covariant
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (J : Matrix (Fin d) (Fin d) ℂ) (h : G) :
    ρ h * packetAverage ρ J * (ρ h)ᴴ = packetAverage ρ J := by
  let conjugate : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun A => ρ h * A * (ρ h)ᴴ
      map_add' := by
        intro A B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c A
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp }
  let conjugateC := conjugate.toContinuousLinearMap
  have hint := integrable_packetOrbit ρ hρ J
  change conjugateC (packetAverage ρ J) = packetAverage ρ J
  rw [packetAverage]
  calc
    conjugateC (∫ g : G, packetOrbit ρ J g
        ∂CompactHaarRankOneAverage.normalizedHaar G) =
        ∫ g : G, conjugateC (packetOrbit ρ J g)
          ∂CompactHaarRankOneAverage.normalizedHaar G :=
      (ContinuousLinearMap.integral_comp_comm conjugateC hint).symm
    _ = ∫ g : G, packetOrbit ρ J (h * g)
          ∂CompactHaarRankOneAverage.normalizedHaar G := by
      apply integral_congr_ae
      filter_upwards [] with g
      dsimp [conjugateC, conjugate]
      unfold packetOrbit
      rw [hρmul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = ∫ g : G, packetOrbit ρ J g
          ∂CompactHaarRankOneAverage.normalizedHaar G :=
      integral_mul_left_eq_self
        (μ := CompactHaarRankOneAverage.normalizedHaar G)
        (packetOrbit ρ J) h

/-- **Compact packet kernel law.**  For a continuous unitary matrix
representation, the Haar average kills `x` exactly when the source packet
kills every adjoint-translated copy of `x`. -/
theorem packetAverage_mulVec_eq_zero_iff
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (hunit : ∀ g, (ρ g)ᴴ * ρ g = 1)
    (J : Matrix (Fin d) (Fin d) ℂ) (hJ : J.PosSemidef)
    (x : Fin d → ℂ) :
    packetAverage ρ J *ᵥ x = 0 ↔
      ∀ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) = 0 := by
  classical
  obtain ⟨L, w, nodes, _hL, hw0, hw1, havg⟩ :=
    compact_positive_packet_quadrature ρ hρ J hJ
  have hpos : ∃ i : Fin L, 0 < w i := by
    by_contra hnone
    push Not at hnone
    have hwzero : ∀ i : Fin L, w i = 0 := by
      intro i
      exact le_antisymm (hnone i) (hw0 i)
    have : (∑ i : Fin L, w i) = 0 := by simp [hwzero]
    linarith [hw1]
  obtain ⟨i0, hi0⟩ := hpos
  constructor
  · intro hFx k
    let h : G := k * (nodes i0)⁻¹
    have horbitShift : ∀ i : Fin L,
        ρ h * packetOrbit ρ J (nodes i) * (ρ h)ᴴ =
          packetOrbit ρ J (h * nodes i) := by
      intro i
      exact packetOrbit_mul ρ hρmul J h (nodes i)
    have hshift : packetAverage ρ J =
        ∑ i, w i • packetOrbit ρ J (h * nodes i) := by
      calc
        packetAverage ρ J =
            ρ h * packetAverage ρ J * (ρ h)ᴴ :=
          (packetAverage_covariant ρ hρ hρmul J h).symm
        _ = ρ h * (∑ i, w i • packetOrbit ρ J (nodes i)) * (ρ h)ᴴ := by
          rw [← havg]
        _ = ∑ i, w i • packetOrbit ρ J (h * nodes i) := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Matrix.mul_smul, Matrix.smul_mul, horbitShift i]
    have hshiftx : (∑ i, w i • packetOrbit ρ J (h * nodes i)) *ᵥ x = 0 := by
      rw [← hshift]
      exact hFx
    have horbit : packetOrbit ρ J (h * nodes i0) *ᵥ x = 0 :=
      positive_weight_term_mulVec_eq_zero
        (fun i => packetOrbit ρ J (h * nodes i))
        (fun i => hJ.mul_mul_conjTranspose_same (ρ (h * nodes i)))
        w hw0 hi0 hshiftx
    have hh : h * nodes i0 = k := by
      simp [h]
    rw [hh] at horbit
    calc
      J *ᵥ ((ρ k)ᴴ *ᵥ x) =
          ((ρ k)ᴴ * ρ k) *ᵥ (J *ᵥ ((ρ k)ᴴ *ᵥ x)) := by
        rw [hunit k, Matrix.one_mulVec]
      _ = (ρ k)ᴴ *ᵥ (packetOrbit ρ J k *ᵥ x) := by
        simp only [packetOrbit, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [horbit, Matrix.mulVec_zero]
  · intro hall
    rw [havg, Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.smul_mulVec]
    have hi : packetOrbit ρ J (nodes i) *ᵥ x = 0 := by
      unfold packetOrbit
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hall (nodes i), Matrix.mulVec_zero]
    rw [hi, smul_zero]

/-- The compact controlled orbit exhausts the carrier exactly when its Haar
packet average is positive definite. -/
theorem packetAverage_posDef_iff_orbit_exhausts
    (ρ : G → Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (hρmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (hunit : ∀ g, (ρ g)ᴴ * ρ g = 1)
    (J : Matrix (Fin d) (Fin d) ℂ) (hJ : J.PosSemidef) :
    (packetAverage ρ J).PosDef ↔
      ∀ x : Fin d → ℂ, x ≠ 0 →
        ∃ g : G, J *ᵥ ((ρ g)ᴴ *ᵥ x) ≠ 0 := by
  have hF := packetAverage_posSemidef ρ hρ J hJ
  have hker := packetAverage_mulVec_eq_zero_iff
    ρ hρ hρmul hunit J hJ
  constructor
  · intro hpd x hx
    by_contra hnone
    push Not at hnone
    have hFx : packetAverage ρ J *ᵥ x = 0 := (hker x).mpr hnone
    have hpos := hpd.dotProduct_mulVec_pos hx
    rw [hFx, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos
  · intro hex
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hF.1
    intro x hx
    rcases eq_or_lt_of_le (hF.dotProduct_mulVec_nonneg x) with heq | hlt
    · exfalso
      have hFx : packetAverage ρ J *ᵥ x = 0 :=
        posSemidef_mulVec_eq_zero_of_form_eq_zero hF heq.symm
      obtain ⟨g, hg⟩ := hex x hx
      exact hg ((hker x).mp hFx g)
    · exact hlt

end CompactPositivePacketQuadrature
end NCG
