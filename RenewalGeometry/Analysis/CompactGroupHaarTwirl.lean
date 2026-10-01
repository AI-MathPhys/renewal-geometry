/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib

/-!
# Haar twirls over compact matrix groups

Mathlib constructs Haar measure on any locally compact Hausdorff topological group but does not
equip `Matrix.specialUnitaryGroup n ℂ` with the structure needed to use it, nor does it provide
Schur averaging of matrix-valued functions.  This module supplies both.

* `specialUnitaryGroup` instances: `IsTopologicalGroup`, `CompactSpace` (closed and entrywise
  bounded by `1`), the Borel `MeasurableSpace` and `BorelSpace`.
* `HaarTwirl.suHaar n`: the normalized Haar probability measure on `SU(n)`
  (`haarMeasure ⊤`), left invariant and of total mass one.
* `HaarTwirl.matrixIntegral`: entrywise Bochner integral of a matrix-valued function.
* `HaarTwirl.twirl_conj_invariant`: for a left-invariant measure, the twirl
  `∫ v(g) Y v(g)^* dμ` is invariant under conjugation by every `v(h)`.
* `HaarTwirl.haar_schur_twirl`: if `v` is a continuous unitary representation of a compact
  group with scalar commutant and `μ` is a left-invariant probability measure, then
  `∫ v(g) Y v(g)^* dμ(g) = (Tr Y / dim V) · I` (Schur averaging, compact-group version of
  `ReciprocalReturnMass.schur_twirl`).
* `HaarTwirl.su2_commutant_scalar`: the defining representation of `SU(2)` has scalar commutant
  (commuting with `iσ_z` and `iσ_x` already forces a scalar).
* `HaarTwirl.range_le_range_of_ker_le_ker`: for Hermitian matrices, kernel inclusion
  reverses to range inclusion.

Used for `thm:weak-copy-census` (spacetime_gauge_duality).
-/

open Matrix MeasureTheory

namespace RenewalGeometry

section SpecialUnitaryTopology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `SU(n)` is a closed subset of `M_n(ℂ)`. -/
theorem specialUnitaryGroup_isClosed :
    IsClosed (Matrix.specialUnitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have h2 : IsClosed {A : Matrix n n ℂ | A * star A = 1} :=
    isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have h3 : IsClosed {A : Matrix n n ℂ | A.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have : (Matrix.specialUnitaryGroup n ℂ : Set (Matrix n n ℂ)) =
      {A | A * star A = 1} ∩ {A | A.det = 1} := by
    ext A
    simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    rfl
  rw [this]
  exact h2.inter h3

/-- `SU(n)` is a compact subset of `M_n(ℂ)`: it is closed and its entries are bounded by `1`. -/
theorem specialUnitaryGroup_isCompact :
    IsCompact (Matrix.specialUnitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have hK : IsCompact (Set.univ.pi fun _ : n =>
      Set.univ.pi fun _ : n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset specialUnitaryGroup_isClosed ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_const]
  intro i j
  exact entry_norm_bound_of_unitary hA.1 i j

instance specialUnitaryGroup_compactSpace : CompactSpace (Matrix.specialUnitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp specialUnitaryGroup_isCompact

instance specialUnitaryGroup_continuousMul : ContinuousMul (Matrix.specialUnitaryGroup n ℂ) :=
  inferInstance

instance specialUnitaryGroup_continuousInv : ContinuousInv (Matrix.specialUnitaryGroup n ℂ) :=
  ⟨Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _⟩

instance specialUnitaryGroup_isTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup n ℂ) where

/-- The Borel σ-algebra on `SU(n)`. -/
noncomputable instance specialUnitaryGroup_measurableSpace : MeasurableSpace (Matrix.specialUnitaryGroup n ℂ) :=
  borel _

instance specialUnitaryGroup_borelSpace : BorelSpace (Matrix.specialUnitaryGroup n ℂ) := ⟨rfl⟩

end SpecialUnitaryTopology

namespace HaarTwirl

section Haar

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The normalized Haar measure on `SU(n)`: Mathlib's Haar measure normalized on the whole
(compact) group. -/
noncomputable def suHaar : Measure (Matrix.specialUnitaryGroup n ℂ) :=
  Measure.haarMeasure ⊤

instance suHaar_isMulLeftInvariant : (suHaar n).IsMulLeftInvariant := by
  unfold suHaar; infer_instance

instance suHaar_isHaarMeasure : (suHaar n).IsHaarMeasure := by
  unfold suHaar; infer_instance

instance suHaar_isProbabilityMeasure : IsProbabilityMeasure (suHaar n) := by
  refine ⟨?_⟩
  have h := Measure.haarMeasure_self (G := Matrix.specialUnitaryGroup n ℂ)
    (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.specialUnitaryGroup n ℂ)))
  simpa [suHaar] using h

end Haar

section MatrixIntegral

variable {G : Type*} [MeasurableSpace G] {V W : Type*}

/-- Entrywise integral of a matrix-valued function. -/
noncomputable def matrixIntegral (μ : Measure G) (F : G → Matrix V W ℂ) : Matrix V W ℂ :=
  Matrix.of fun i j => ∫ g, F g i j ∂μ

theorem matrixIntegral_apply (μ : Measure G) (F : G → Matrix V W ℂ) (i : V) (j : W) :
    matrixIntegral μ F i j = ∫ g, F g i j ∂μ := rfl

end MatrixIntegral

section Twirl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [Fintype V] [DecidableEq V]

/-- The twirl `∫ v(g) Y v(g)^* dμ(g)`. -/
noncomputable def twirl (μ : Measure G) (v : G → Matrix V V ℂ) (Y : Matrix V V ℂ) :
    Matrix V V ℂ :=
  matrixIntegral μ fun g => v g * Y * (v g)ᴴ

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [DecidableEq V] in
theorem continuous_conj_entry {v : G → Matrix V V ℂ} (hcont : Continuous v) (Y : Matrix V V ℂ)
    (i j : V) : Continuous fun g => (v g * Y * (v g)ᴴ) i j := by
  have : Continuous fun g => v g * Y * (v g)ᴴ :=
    (hcont.matrix_mul continuous_const).matrix_mul hcont.matrix_conjTranspose
  exact this.matrix_elem i j

omit [Group G] [IsTopologicalGroup G] [DecidableEq V] in
theorem integrable_conj_entry (μ : Measure G) [IsFiniteMeasure μ] {v : G → Matrix V V ℂ}
    (hcont : Continuous v) (Y : Matrix V V ℂ) (i j : V) :
    Integrable (fun g => (v g * Y * (v g)ᴴ) i j) μ :=
  (continuous_conj_entry hcont Y i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Invariance of the twirl.** For a left-invariant finite measure,
`v(h) (∫ v(g) Y v(g)^*) v(h)^* = ∫ v(g) Y v(g)^*`. -/
theorem twirl_conj_invariant (μ : Measure G) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    {v : G → Matrix V V ℂ} (hmul : ∀ g h, v (g * h) = v g * v h) (hcont : Continuous v)
    (Y : Matrix V V ℂ) (h : G) :
    v h * twirl μ v Y * (v h)ᴴ = twirl μ v Y := by
  ext i j
  have hint := integrable_conj_entry μ hcont Y
  calc (v h * twirl μ v Y * (v h)ᴴ) i j
      = ∑ l, (∑ k, v h i k * ∫ g, (v g * Y * (v g)ᴴ) k l ∂μ) * (v h)ᴴ l j := by
        simp only [Matrix.mul_apply, twirl, matrixIntegral_apply]
    _ = ∫ g, ∑ l, (∑ k, v h i k * (v g * Y * (v g)ᴴ) k l) * (v h)ᴴ l j ∂μ := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun l _ => ?_
          rw [integral_mul_const, integral_finsetSum]
          · simp only [integral_const_mul]
          · intro k _; exact (hint k l).const_mul _
        · intro l _
          exact (integrable_finsetSum _ fun k _ => (hint k l).const_mul _).mul_const _
    _ = ∫ g, (v (h * g) * Y * (v (h * g))ᴴ) i j ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e : v (h * g) * Y * (v (h * g))ᴴ = v h * (v g * Y * (v g)ᴴ) * (v h)ᴴ := by
          rw [hmul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        show _ = (v (h * g) * Y * (v (h * g))ᴴ) i j
        rw [e]
        simp only [Matrix.mul_apply]
    _ = ∫ g, (v g * Y * (v g)ᴴ) i j ∂μ :=
        integral_mul_left_eq_self (fun g => (v g * Y * (v g)ᴴ) i j) h
    _ = twirl μ v Y i j := rfl

/-- The trace of the twirl of `Y` against a probability measure is `Tr Y`. -/
theorem trace_twirl (μ : Measure G) [IsProbabilityMeasure μ] {v : G → Matrix V V ℂ}
    (hunit : ∀ g, (v g)ᴴ * v g = 1) (hcont : Continuous v) (Y : Matrix V V ℂ) :
    (twirl μ v Y).trace = Y.trace := by
  have hint := integrable_conj_entry μ hcont Y
  calc (twirl μ v Y).trace = ∫ g, (v g * Y * (v g)ᴴ).trace ∂μ := by
        simp only [Matrix.trace, Matrix.diag, twirl, matrixIntegral_apply]
        rw [integral_finsetSum]
        intro i _; exact hint i i
    _ = ∫ _g, Y.trace ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
    _ = Y.trace := by simp

/-- **Schur averaging over a compact group (Haar twirl).**  Let `v` be a continuous unitary
representation of a compact group `G` on `ℂ^V` whose commutant is scalar, and let `μ` be a
left-invariant probability measure (e.g. normalized Haar measure).  Then
`∫ v(g) Y v(g)^* dμ(g) = (Tr Y / dim V) · I`. -/
theorem haar_schur_twirl [Nonempty V] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] {v : G → Matrix V V ℂ} (hmul : ∀ g h, v (g * h) = v g * v h)
    (hunit : ∀ g, (v g)ᴴ * v g = 1) (hcont : Continuous v)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (Y : Matrix V V ℂ) :
    twirl μ v Y = (Y.trace / Fintype.card V) • (1 : Matrix V V ℂ) := by
  have hcomm : ∀ g, twirl μ v Y * v g = v g * twirl μ v Y := by
    intro g
    conv_lhs => rw [← twirl_conj_invariant μ hmul hcont Y g]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hunit, Matrix.mul_one]
  obtain ⟨c, hc⟩ := hirr _ hcomm
  have htr := trace_twirl μ hunit hcont Y
  rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htr
  have hV : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hc]
  congr 1
  rw [← htr]
  field_simp

end Twirl

section SU2

/-- `iσ_z = diag(i, -i) ∈ SU(2)`. -/
def isigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- `iσ_x ∈ SU(2)`. -/
def isigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-- `iσ_y ∈ SU(2)`. -/
def isigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem isigmaZ_mem : isigmaZ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [isigmaZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [isigmaZ, Matrix.det_fin_two]

theorem isigmaX_mem : isigmaX ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [isigmaX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [isigmaX, Matrix.det_fin_two]

theorem isigmaY_mem : isigmaY ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [isigmaY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [isigmaY, Matrix.det_fin_two]

/-- Every `2 × 2` complex matrix is a linear combination of the four `SU(2)` elements
`1, iσ_x, iσ_y, iσ_z`; in particular `SU(2)` spans `M_2(ℂ)`. -/
theorem su2_span_decomp (E : Matrix (Fin 2) (Fin 2) ℂ) :
    E = ((E 0 0 + E 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (-Complex.I * (E 0 1 + E 1 0) / 2) • isigmaX
      + ((E 0 1 - E 1 0) / 2) • isigmaY
      + (-Complex.I * (E 0 0 - E 1 1) / 2) • isigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isigmaX, isigmaY, isigmaZ] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **Schur's lemma for the defining representation of `SU(2)`.**  A matrix commuting with
`iσ_z` and `iσ_x` is scalar; hence the commutant of `SU(2)` on `ℂ²` is `ℂ · I`. -/
theorem su2_commutant_scalar (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, X * g.1 = g.1 * X) :
    ∃ c : ℂ, X = c • 1 := by
  have hz := congrFun (congrFun (hX ⟨isigmaZ, isigmaZ_mem⟩) 0) 1
  have hz' := congrFun (congrFun (hX ⟨isigmaZ, isigmaZ_mem⟩) 1) 0
  have hx := congrFun (congrFun (hX ⟨isigmaX, isigmaX_mem⟩) 0) 1
  simp [isigmaZ, isigmaX, Matrix.mul_apply, Fin.sum_univ_two] at hz hz' hx
  refine ⟨X 0 0, ?_⟩
  have h01 : X 0 1 = 0 := by
    have : (2 * Complex.I) * X 0 1 = 0 := by linear_combination -hz
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  have h10 : X 1 0 = 0 := by
    have : (2 * Complex.I) * X 1 0 = 0 := by linear_combination hz'
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  have h11 : X 1 1 = X 0 0 := by
    have : Complex.I * (X 1 1 - X 0 0) = 0 := by linear_combination -hx
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact (sub_eq_zero.mp h)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

/-- **Haar twirl on `SU(2)`.**  For every left-invariant probability measure on `SU(2)` (in
particular normalized Haar measure `suHaar (Fin 2)`),
`∫ g Y g^* dμ(g) = (Tr Y / 2) · I`. -/
theorem su2_haar_twirl (μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    twirl μ (fun g => g.1) Y = (Y.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have := haar_schur_twirl μ (v := fun g => g.1) (fun _ _ => rfl)
    (fun g => g.2.1.1) continuous_subtype_val su2_commutant_scalar Y
  simpa using this

end SU2

section HermitianRange

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For Hermitian matrices, `ker T ⊆ ker A` implies `Ran A ⊆ Ran T`. -/
theorem range_le_range_of_ker_le_ker {A T : Matrix n n ℂ} (hA : A.IsHermitian)
    (hT : T.IsHermitian)
    (h : LinearMap.ker T.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range T.mulVecLin := by
  have hA' := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
  have hT' := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hT)
  have key := (ContinuousLinearMap.ker_le_ker_iff_range_le_range
    (T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A)
    (U := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) T) hA' hT').mp (by
      intro x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      have hx' : T *ᵥ WithLp.ofLp x = 0 := by
        have := congrArg WithLp.ofLp hx
        simpa using this
      have := h (show WithLp.ofLp x ∈ LinearMap.ker T.mulVecLin by simpa using hx')
      have h0 : A *ᵥ WithLp.ofLp x = 0 := by simpa using this
      apply (WithLp.ofLp_injective 2)
      simpa using h0)
  rintro _ ⟨x, rfl⟩
  have hx : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (WithLp.toLp 2 x) ∈
      LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) T :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) := key ⟨WithLp.toLp 2 x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine ⟨WithLp.ofLp y, ?_⟩
  have := congrArg WithLp.ofLp hy
  simpa using this

end HermitianRange

end HaarTwirl

end RenewalGeometry
