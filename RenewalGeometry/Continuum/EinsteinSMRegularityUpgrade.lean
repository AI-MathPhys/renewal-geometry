/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure

/-!
# From distributional to pointwise Euler equations (`cor:strong-solution-upgrade`, regularity
  step; Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMReducedClosure.lean`.  The limit of `thm:reduced-closure` is a
distributional solution: its complete first-variation covector field `Λ(x) = Cov(z)(x)` (first-order
gravity + Yang–Mills + Higgs + Dirac–Yukawa, evaluated on the limit jet) satisfies
`∫_Q Λ(x)(testJet v x) dx = 0` for every physical test `v`.  Writing the test jet as
`v(x) ↦ (v, ∂v)` (`valEmb`, `derEmb`), the **Euler row** of the limit is
`E(x) = Λ(x) ∘ valEmb - Σ_i ∂_i(Λ ∘ derEmb_i)(x)`, a covector on field-variation values: its
gravitational (metric) part is the second-order Einstein row `(Ein(g) + Λg - κT)√|g|` (in the
first-order representative), the gauge and Higgs parts the second-order Yang–Mills / Higgs rows,
the spinor parts the first-order Dirac rows.

* `testJet_scaled`: the test jet of `ψ(x) w` is `ψ valEmb w + Σ_i ∂_iψ derEmb_i w`;
* `exists_periodic_bump`, `exists_slab_bump`: smooth, nonnegative, spatially periodic bumps
  concentrated near a point of the fundamental box (built from `cos(2π s)`);
* `integral_bump_mul_eulerRow`: integration by parts on the slab (`integral_div_slab_eq_zero`,
  periodic spatial faces) turns the distributional identity into `∫_Q ψ E(·)(w) = 0`;
* **`eulerRow_eq_zero`** (du Bois-Reymond): if `Λ` is `C¹` on the open slab and spatially periodic,
  the distributional Euler identities imply that the Euler row vanishes **pointwise** in every
  admissible direction (symmetric metric variations, `smLie` gauge variations, chiral spinor
  variations) at every point of the open fundamental box `(0,T) × (0,1)³`;
* `strong_solution_upgrade`: combined with `reduced_closure`: every subsequence has a further
  subsequence and a limit which is a distributional solution and, if its first-variation covector
  fields are `C¹` and periodic (the classical regularity of the limit; implied by the manuscript's
  `C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`, `s ≥ 5`, class through Sobolev embedding and the smooth
  dependence of the covectors on the jet — **not formalised**), all Euler rows vanish pointwise.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Values and first jets of field variations -/

section Embeddings

variable {C : Type} [Fintype C]

/-- Field-variation values `(k, a, η_H, η_Ψ, η_Ψ̄)`. -/
abbrev FieldVal (C : Type) [Fintype C] : Type :=
  CoframeFibre × ConnFibre × HiggsFibre × SpinorFibre C × SpinorFibre C

/-- Admissible variation values (the fibres of `𝒱_K`): symmetric `k`, `smLie`-valued `a`, chiral
`η_Ψ`, co-chiral `η_Ψ̄`. -/
def IsAdmissible (left : C → Bool) (w : FieldVal C) : Prop :=
  (∀ μ ν, w.1 μ ν = w.1 ν μ) ∧ (∀ μ, w.2.1 μ ∈ smLie) ∧ IsChiral left w.2.2.2.1 ∧
    IsCoChiral left w.2.2.2.2

theorem IsAdmissible.neg {left : C → Bool} {w : FieldVal C} (hw : IsAdmissible left w) :
    IsAdmissible left (-w) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  refine ⟨fun μ ν => ?_, fun μ => ?_, fun s c hs => ?_, fun s c hs => ?_⟩
  · show -(w.1 μ ν) = -(w.1 ν μ); rw [h1]
  · exact smLie.neg_mem (h2 μ)
  · show -(w.2.2.2.1 s c) = 0; rw [h3 s c hs, neg_zero]
  · show -(w.2.2.2.2 s c) = 0; rw [h4 s c hs, neg_zero]

/-- The value embedding `w ↦ (w, 0)` into the jet space. -/
def valEmb (C : Type) [Fintype C] : FieldVal C →L[ℝ] RJet C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => RJet.mk w.1 0 w.2.1 0 w.2.2.1 0 w.2.2.2.1 0 w.2.2.2.2 0
      map_add' := fun w w' => by simp [RJet.mk]
      map_smul' := fun c w => by simp [RJet.mk] }

/-- The derivative embedding `w ↦ (0, e_i ⊗ w)`: the jet of a variation with `∂_i v = w`. -/
def derEmb (C : Type) [Fintype C] (i : Fin 4) : FieldVal C →L[ℝ] RJet C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => RJet.mk 0 (Pi.single i w.1) 0 (Pi.single i w.2.1) 0 (Pi.single i w.2.2.1)
        0 (Pi.single i w.2.2.2.1) 0 (Pi.single i w.2.2.2.2)
      map_add' := fun w w' => by simp [RJet.mk, Pi.single_add]
      map_smul' := fun c w => by simp [RJet.mk, Pi.single_smul] }

theorem valEmb_apply (w : FieldVal C) :
    valEmb C w = RJet.mk w.1 0 w.2.1 0 w.2.2.1 0 w.2.2.2.1 0 w.2.2.2.2 0 := rfl

theorem derEmb_apply (i : Fin 4) (w : FieldVal C) :
    derEmb C i w = RJet.mk 0 (Pi.single i w.1) 0 (Pi.single i w.2.1) 0 (Pi.single i w.2.2.1)
      0 (Pi.single i w.2.2.2.1) 0 (Pi.single i w.2.2.2.2) := rfl

/-- The field tuple `x ↦ ψ(x) w`. -/
def scaledField (ψ : E4 → ℝ) (w : FieldVal C) : FieldTuple C :=
  FieldTuple.mk (fun x => ψ x • w.1) (fun x => ψ x • w.2.1) (fun x => ψ x • w.2.2.1)
    (fun x => ψ x • w.2.2.2.1) (fun x => ψ x • w.2.2.2.2)

theorem pd_smul_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ψ : E4 → ℝ}
    (hψ : Differentiable ℝ ψ) (c : F) (i : Fin 4) (x : E4) :
    pd (fun y => ψ y • c) i x = pd ψ i x • c := by
  unfold pd
  rw [fderiv_smul_const (hψ x)]
  rfl

theorem sum_single_smul {F : Type*} [AddCommMonoid F] [Module ℝ F] (a : Fin 4 → ℝ) (c : F) :
    (∑ i, a i • (Pi.single i c : Fin 4 → F)) = fun j => a j • c := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_apply, Ne.symm hij]
  · simp

theorem clm_scaled_jet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (π : RJet C →L[ℝ] F) (a : ℝ) (b : Fin 4 → ℝ) (w : FieldVal C) :
    π (a • valEmb C w + ∑ i, b i • derEmb C i w) =
      a • π (valEmb C w) + ∑ i, b i • π (derEmb C i w) := by
  rw [map_add, map_smul, map_sum]
  simp only [map_smul]

/-- **The test jet of `ψ w`**: `testJet (ψ w) = ψ valEmb w + Σ_i ∂_iψ derEmb_i w`. -/
theorem testJet_scaled {ψ : E4 → ℝ} (hψ : Differentiable ℝ ψ) (w : FieldVal C) (x : E4) :
    testJet (scaledField ψ w) x = ψ x • valEmb C w + ∑ i, pd ψ i x • derEmb C i w := by
  have key : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (π : RJet C →L[ℝ] F),
      π (ψ x • valEmb C w + ∑ i, pd ψ i x • derEmb C i w) =
        ψ x • π (valEmb C w) + ∑ i, pd ψ i x • π (derEmb C i w) := fun π =>
    clm_scaled_jet π _ _ w
  refine RJet.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := key (πe (C := C)); simp only [πe_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.e, valEmb_apply, derEmb_apply]
  · have := key (πde (C := C)); simp only [πde_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.e, valEmb_apply, derEmb_apply,
      pd_smul_const hψ, sum_single_smul]
  · have := key (πA (C := C)); simp only [πA_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.A, valEmb_apply, derEmb_apply]
  · have := key (πF (C := C)); simp only [πF_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.A, valEmb_apply, derEmb_apply,
      pd_smul_const hψ, sum_single_smul]
  · have := key (πH (C := C)); simp only [πH_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.H, valEmb_apply, derEmb_apply]
  · have := key (πK (C := C)); simp only [πK_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.H, valEmb_apply, derEmb_apply,
      pd_smul_const hψ, sum_single_smul]
  · have := key (πΨ (C := C)); simp only [πΨ_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.Ψ, valEmb_apply, derEmb_apply]
  · have := key (πdΨ (C := C)); simp only [πdΨ_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.Ψ, valEmb_apply, derEmb_apply,
      pd_smul_const hψ, sum_single_smul]
  · have := key (πΨb (C := C)); simp only [πΨb_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.Ψb, valEmb_apply, derEmb_apply]
  · have := key (πdΨb (C := C)); simp only [πdΨb_apply] at this; rw [this]
    simp [testJet, scaledField, FieldTuple.mk, FieldTuple.Ψb, valEmb_apply, derEmb_apply,
      pd_smul_const hψ, sum_single_smul]

end Embeddings

/-! ### Euler rows -/

section Rows

variable {C : Type} [Fintype C]

/-- **The Euler row** `E(x) = Λ(x) ∘ valEmb - Σ_i ∂_i(Λ ∘ derEmb_i)(x)` of a covector field. -/
def eulerRow (Λ : E4 → RJet C →L[ℝ] ℝ) (x : E4) : FieldVal C →L[ℝ] ℝ :=
  (Λ x).comp (valEmb C) - ∑ i, (pd Λ i x).comp (derEmb C i)

end Rows

/-! ### Periodic bumps -/

section Bumps

/-- A smooth, nonnegative, `1`-periodic bump on `ℝ`, positive at `c ∈ (0,1)` and, on `(0,1)`,
supported within distance `r` of `c`. -/
theorem exists_periodic_bump {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) {r : ℝ} (hr : 0 < r) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ Function.Periodic β 1 ∧ (∀ s, 0 ≤ β s) ∧ 0 < β c ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, β s ≠ 0 → |s - c| < r := by
  set ε := min r (min c (1 - c)) with hε
  have hε0 : 0 < ε := lt_min hr (lt_min hc.1 (by linarith [hc.2]))
  have hεc : ε ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 - c := (min_le_right _ _).trans (min_le_right _ _)
  have hεr : ε ≤ r := min_le_left _ _
  have hK : (Icc ε (1 - ε)).Nonempty := ⟨ε, le_rfl, by linarith⟩
  obtain ⟨d₀, hd₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hK
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    (f := fun d => Real.cos (2 * Real.pi * d))
  set M := Real.cos (2 * Real.pi * d₀)
  have hM1 : M < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h
    have hd : (n : ℝ) = d₀ := by
      have := Real.pi_pos
      field_simp at hn
      nlinarith [hn]
    have h1 : (0 : ℝ) < n := by rw [hd]; linarith [hd₀.1]
    have h2 : (n : ℝ) < 1 := by rw [hd]; linarith [hd₀.2]
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  set η := 1 - M
  have hη : 0 < η := by simp only [η]; linarith
  let ϑ : ContDiffBump (1 : ℝ) := ⟨η / 2, η, half_pos hη, half_lt_self hη⟩
  refine ⟨fun s => ϑ (Real.cos (2 * Real.pi * (s - c))), ?_, fun s => ?_, fun s => ϑ.nonneg, ?_,
    fun s hs hne => ?_⟩
  · exact ϑ.contDiff.comp (Real.contDiff_cos.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  · show ϑ (Real.cos (2 * Real.pi * (s + 1 - c))) = ϑ (Real.cos (2 * Real.pi * (s - c)))
    rw [show 2 * Real.pi * (s + 1 - c) = 2 * Real.pi * (s - c) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · show 0 < ϑ (Real.cos (2 * Real.pi * (c - c)))
    rw [sub_self, mul_zero, Real.cos_zero]
    exact ϑ.pos_of_mem_ball (Metric.mem_ball_self ϑ.rOut_pos)
  · have hsupp : Real.cos (2 * Real.pi * (s - c)) ∈ Metric.ball (1 : ℝ) η := by
      have : Real.cos (2 * Real.pi * (s - c)) ∈ Function.support ϑ := hne
      rwa [ϑ.support_eq] at this
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hsupp
    by_contra hfar
    push Not at hfar
    have hin : |s - c| ∈ Icc ε (1 - ε) := by
      refine ⟨hεr.trans hfar, ?_⟩
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have hle := hmax hin
    simp only [mem_ofPred_eq] at hle
    rw [show 2 * Real.pi * |s - c| = |2 * Real.pi * (s - c)| by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)], Real.cos_abs] at hle
    linarith [hsupp.1]

/-- A smooth, nonnegative, spatially periodic bump on the lift `ℝ⁴`, positive at a point `x₀` of
the fundamental box, with time support in a compact subinterval of `(t₀,t₁)`, and, on the
fundamental box, supported within sup-distance `r` of `x₀`. -/
theorem exists_slab_bump {t₀ t₁ : ℝ} {x₀ : E4} (ht : x₀ 0 ∈ Ioo t₀ t₁)
    (hs : ∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1) {r : ℝ} (hr : 0 < r) :
    ∃ ψ : E4 → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ n x, ψ (x + spatialShift n) = ψ x) ∧
      (∃ a b, t₀ < a ∧ b < t₁ ∧ ∀ x, x 0 ∉ Icc a b → ψ x = 0) ∧ (∀ x, 0 ≤ ψ x) ∧
      0 < ψ x₀ ∧ ∀ x, (∀ i : Fin 3, x i.succ ∈ Ioo 0 1) → ψ x ≠ 0 → ∀ j, |x j - x₀ j| < r := by
  choose β hβs hβp hβn hβc hβl using fun i : Fin 3 => exists_periodic_bump (hs i) hr
  set δ := min r (min (x₀ 0 - t₀) (t₁ - x₀ 0)) / 2 with hδ
  have hδ0 : 0 < δ := by
    have := ht.1; have := ht.2
    simp only [hδ]; positivity
  have hδr : δ < r := by
    simp only [hδ]; linarith [min_le_left r (min (x₀ 0 - t₀) (t₁ - x₀ 0))]
  have hδa : δ < x₀ 0 - t₀ := by
    simp only [hδ]
    have := min_le_right r (min (x₀ 0 - t₀) (t₁ - x₀ 0))
    have := min_le_left (x₀ 0 - t₀) (t₁ - x₀ 0)
    linarith [ht.1]
  have hδb : δ < t₁ - x₀ 0 := by
    simp only [hδ]
    have := min_le_right r (min (x₀ 0 - t₀) (t₁ - x₀ 0))
    have := min_le_right (x₀ 0 - t₀) (t₁ - x₀ 0)
    linarith [ht.2]
  let ρ : ContDiffBump (x₀ 0) := ⟨δ / 2, δ, half_pos hδ0, half_lt_self hδ0⟩
  refine ⟨fun x => ρ (x 0) * ∏ i : Fin 3, β i (x i.succ), ?_, fun n x => ?_,
    ⟨x₀ 0 - δ, x₀ 0 + δ, by linarith, by linarith, fun x hx => ?_⟩, fun x => ?_, ?_,
    fun x hx hne j => ?_⟩
  · exact (ρ.contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
      (contDiff_prod fun i _ => (hβs i).comp (contDiff_apply ℝ ℝ i.succ))
  · simp only [Pi.add_apply, spatialShift_zero, add_zero, spatialShift_succ]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have := (hβp i).int_mul (n i) (x i.succ)
    rwa [mul_one] at this
  · have : ρ (x 0) = 0 := by
      refine ρ.zero_of_le_dist ?_
      rw [Real.dist_eq]
      simp only [mem_Icc, not_and_or, not_le] at hx
      show δ ≤ |x 0 - x₀ 0|
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [this]
  · exact mul_nonneg ρ.nonneg (Finset.prod_nonneg fun i _ => hβn i _)
  · exact mul_pos (ρ.pos_of_mem_ball (Metric.mem_ball_self ρ.rOut_pos))
      (Finset.prod_pos fun i _ => hβc i)
  · have hρ : ρ (x 0) ≠ 0 := fun h => hne (by simp [h])
    have hβ : ∀ i, β i (x i.succ) ≠ 0 := fun i h => hne (by
      simp only
      rw [Finset.prod_eq_zero (Finset.mem_univ i) h, mul_zero])
    refine Fin.cases ?_ (fun i => ?_) j
    · have : x 0 ∈ Function.support ρ := hρ
      rw [ρ.support_eq, Metric.mem_ball, Real.dist_eq] at this
      exact this.trans hδr
    · exact hβl i _ (hx i) (hβ i)

end Bumps

/-! ### du Bois-Reymond on the slab -/

section DuBoisReymond

variable {T : ℝ} {C : Type} [Fintype C] {left : C → Bool} {r : ℕ}

theorem isCylTest_smul_const {K : CylRegion T} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ψ : E4 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : ∀ n x, ψ (x + spatialShift n) = ψ x) (hsupp : tsupport ψ ⊆ K.lift) (c : F) :
    IsCylTest K (fun x => ψ x • c) :=
  ⟨hψ.smul contDiff_const, fun n x => by simp [hper n x],
    (tsupport_smul_subset_left _ _).trans hsupp⟩

/-- The physical test `x ↦ ψ(x) w` in `𝒱_K` (admissible `w`). -/
def scaledTest (K : CylRegion T) {ψ : E4 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : ∀ n x, ψ (x + spatialShift n) = ψ x) (hsupp : tsupport ψ ⊆ K.lift) {w : FieldVal C}
    (hw : IsAdmissible left w) : CrTest left r K :=
  (⟨scaledField ψ w, isCylTest_smul_const hψ hper hsupp _, isCylTest_smul_const hψ hper hsupp _,
    isCylTest_smul_const hψ hper hsupp _, isCylTest_smul_const hψ hper hsupp _,
    isCylTest_smul_const hψ hper hsupp _,
    fun x μ ν => by
      show ψ x • w.1 μ ν = ψ x • w.1 ν μ
      rw [hw.1 μ ν],
    fun x μ => smLie.smul_mem (ψ x) (hw.2.1 μ),
    fun x s c hs => by
      show ψ x • w.2.2.2.1 s c = 0
      rw [hw.2.2.1 s c hs, smul_zero],
    fun x s c hs => by
      show ψ x • w.2.2.2.2 s c = 0
      rw [hw.2.2.2 s c hs, smul_zero]⟩ : ↥(testSubmodule left K))

theorem pd_mul_apply {Λ : E4 → RJet C →L[ℝ] ℝ} {ψ : E4 → ℝ} {x : E4}
    (hψ : DifferentiableAt ℝ ψ x) (hΛ : DifferentiableAt ℝ Λ x) (c : RJet C) (i : Fin 4) :
    pd (fun y => ψ y * Λ y c) i x = pd ψ i x * Λ x c + ψ x * pd Λ i x c := by
  have h1 : DifferentiableAt ℝ (fun y => Λ y c) x :=
    (ContinuousLinearMap.apply ℝ ℝ c).differentiableAt.comp x hΛ
  have h2 : pd (fun y => Λ y c) i x = pd Λ i x c :=
    pd_clm_comp hΛ (ContinuousLinearMap.apply ℝ ℝ c) i
  unfold pd at h2 ⊢
  rw [fderiv_fun_mul hψ h1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, h2, smul_eq_mul, smul_eq_mul]
  ring

theorem integrableOn_slab_of_continuousOn {t₀ t₁ : ℝ} {h0 : 0 < t₀} {h01 : t₀ < t₁}
    {h1 : t₁ < T} {f : E4 → ℝ} (hf : ContinuousOn f (cylSlab T)) :
    IntegrableOn f (slabChart t₀ t₁ h0 h01 h1 (T := T)).set := by
  have hcl := isCompact_closure_slabChart h0 h01 h1 (T := T)
  have hsub : closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  exact ((hf.mono hsub).integrableOn_compact hcl).mono_set subset_closure

/-- **Integration by parts against a periodic bump**: the distributional Euler identities give
`∫_Q ψ E(·)(w) = 0` for every smooth spatially periodic `ψ` with compact time support in `(t₀,t₁)`
and every admissible `w`. -/
theorem integral_bump_mul_eulerRow {Λ : E4 → RJet C →L[ℝ] ℝ} (hΛ : ContDiffOn ℝ 1 Λ (cylSlab T))
    (hΛper : ∀ n x, Λ (x + spatialShift n) = Λ x)
    (hEuler : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest left r K,
        ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, Λ x (testJet v.val x) = 0)
    {t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T) {ψ : E4 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hper : ∀ n x, ψ (x + spatialShift n) = ψ x) {a b : ℝ}
    (ha : t₀ < a) (hb : b < t₁) (hz : ∀ x, x 0 ∉ Icc a b → ψ x = 0) {w : FieldVal C}
    (hw : IsAdmissible left w) :
    ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, ψ x * eulerRow Λ x w = 0 := by
  set Q := slabChart t₀ t₁ h0 h01 h1 (T := T) with hQ
  let K : CylRegion T := ⟨Icc a b ×ˢ univ, isCompact_Icc.prod isCompact_univ, fun p hp =>
    ⟨⟨h0.trans (ha.trans_le hp.1.1), hp.1.2.trans_lt (hb.trans h1)⟩, trivial⟩⟩
  have hK : ∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁ := fun p hp => ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb⟩
  have hlift : K.lift = (fun x : E4 => x 0) ⁻¹' Icc a b := by
    ext x; simp [CylRegion.lift, K, cylProj]
  have hsupp : tsupport ψ ⊆ K.lift := by
    rw [hlift]
    refine closure_minimal (fun x hx => ?_) (isClosed_Icc.preimage (continuous_apply 0))
    by_contra hxK
    exact hx (hz x hxK)
  set v : CrTest left r K := scaledTest K hψ hper hsupp hw
  have hE := hEuler K t₀ t₁ h0 h01 h1 hK v
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hΛd : ∀ x ∈ cylSlab T, DifferentiableAt ℝ Λ x := fun x hx =>
    (hΛ.contDiffAt ((isOpen_cylSlab T).mem_nhds hx)).differentiableAt one_ne_zero
  set f : Fin 4 → E4 → ℝ := fun i x => ψ x * Λ x (derEmb C i w) with hf
  have hfC : ∀ i, ContDiffOn ℝ 1 (f i) (cylSlab T) := fun i =>
    (hψ.of_le (by simp)).contDiffOn.mul (hΛ.clm_apply contDiffOn_const)
  have hclQ : closure Q.set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have hdiv := integral_div_slab_eq_zero h0 h01 h1 (f := f) (isOpen_cylSlab T) hclQ hfC
    (fun x hx => by
      have : ψ x = 0 := hz x fun h => by rcases hx with hx | hx <;> rw [hx] at h <;> linarith [h.1, h.2]
      simp [hf, this])
    (fun j x => by
      simp only [hf]
      rw [hper, hΛper])
  have hpt : ∀ x ∈ Q.set, ψ x * eulerRow Λ x w =
      Λ x (testJet v.val x) - ∑ i, pd (f i) i x := by
    intro x hx
    have hxs : x ∈ cylSlab T := hclQ (subset_closure hx)
    have hv : v.val = scaledField ψ w := rfl
    rw [hv, testJet_scaled hψd, map_add, map_smul, map_sum]
    simp only [hf, pd_mul_apply (hψd x) (hΛd x hxs), map_smul, smul_eq_mul, eulerRow,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.comp_apply, Finset.sum_add_distrib]
    rw [mul_sub, Finset.mul_sum]
    ring
  have hcont1 : ContinuousOn (fun x => Λ x (testJet v.val x)) (cylSlab T) :=
    hΛ.continuousOn.clm_apply (continuous_testJet v).continuousOn
  have hcont2 : ContinuousOn (fun x => ∑ i, pd (f i) i x) (cylSlab T) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact ((hfC i).continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply
      continuousOn_const
  rw [setIntegral_congr_fun Q.isOpen.measurableSet hpt,
    integral_sub (integrableOn_slab_of_continuousOn hcont1)
      (integrableOn_slab_of_continuousOn hcont2), hE, hdiv, sub_zero]

/-- **du Bois-Reymond: distributional Euler identities with `C¹` coefficients are pointwise.**
Let `Λ` be a `C¹`, spatially periodic covector field on the open slab whose induced functional
vanishes on every physical test of every `𝒱_K`.  Then its Euler row
`E(x) = Λ(x) ∘ valEmb - Σ_i ∂_i(Λ ∘ derEmb_i)(x)` vanishes in every admissible direction at every
point of the open fundamental box `(0,T) × (0,1)³`. -/
theorem eulerRow_eq_zero {Λ : E4 → RJet C →L[ℝ] ℝ} (hΛ : ContDiffOn ℝ 1 Λ (cylSlab T))
    (hΛper : ∀ n x, Λ (x + spatialShift n) = Λ x)
    (hEuler : ∀ (K : CylRegion T) t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
      (∀ p ∈ K.carrier, p.1 ∈ Ioo t₀ t₁) → ∀ v : CrTest left r K,
        ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, Λ x (testJet v.val x) = 0)
    {x₀ : E4} (hx₀ : x₀ 0 ∈ Ioo 0 T) (hx₀s : ∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1)
    {w : FieldVal C} (hw : IsAdmissible left w) : eulerRow Λ x₀ w = 0 := by
  have hcontRow : ∀ w : FieldVal C, ContinuousOn (fun x => eulerRow Λ x w) (cylSlab T) := by
    intro w
    have hpd : ∀ i, ContinuousOn (fun x => pd Λ i x) (cylSlab T) := fun i =>
      (hΛ.continuousOn_fderiv_of_isOpen (isOpen_cylSlab T) le_rfl).clm_apply continuousOn_const
    simp only [eulerRow, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.comp_apply]
    exact (hΛ.continuousOn.clm_apply continuousOn_const).sub
      (continuousOn_finsetSum _ fun i _ => (hpd i).clm_apply continuousOn_const)
  have key : ∀ w : FieldVal C, IsAdmissible left w → ¬ 0 < eulerRow Λ x₀ w := by
    intro w hw hpos
    set t₀ := x₀ 0 / 2
    set t₁ := (x₀ 0 + T) / 2
    have h0 : 0 < t₀ := by simp only [t₀]; linarith [hx₀.1]
    have h01 : t₀ < t₁ := by simp only [t₀, t₁]; linarith [hx₀.1, hx₀.2]
    have h1 : t₁ < T := by simp only [t₁]; linarith [hx₀.2]
    have ht : x₀ 0 ∈ Ioo t₀ t₁ := ⟨by simp only [t₀]; linarith [hx₀.1],
      by simp only [t₁]; linarith [hx₀.2]⟩
    set g : E4 → ℝ := fun x => eulerRow Λ x w
    have hslab : x₀ ∈ cylSlab T := hx₀
    have hgc : ContinuousAt g x₀ := (hcontRow w).continuousAt ((isOpen_cylSlab T).mem_nhds hslab)
    obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hgc (g x₀ / 2) (half_pos hpos)
    obtain ⟨ψ, hψs, hψp, ⟨a, b, ha, hb, hz⟩, hψn, hψ0, hψl⟩ := exists_slab_bump ht hx₀s hρ₁
    have hint := integral_bump_mul_eulerRow hΛ hΛper hEuler h0 h01 h1 hψs hψp ha hb hz hw
    set Q := slabChart t₀ t₁ h0 h01 h1 (T := T)
    have hgpos : ∀ x ∈ Q.set, ψ x ≠ 0 → 0 < g x := by
      intro x hx hne
      have hxs := (mem_slabChart.mp hx).2
      have hd : dist x x₀ < ρ₁ := (dist_pi_lt_iff hρ₁).mpr fun j => by
        rw [Real.dist_eq]; exact hψl x hxs hne j
      have := hball hd
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hnn : 0 ≤ᵐ[volume.restrict Q.set] fun x => ψ x * g x := by
      refine (ae_restrict_iff' Q.isOpen.measurableSet).mpr (Eventually.of_forall fun x hx => ?_)
      by_cases hne : ψ x = 0
      · simp [hne]
      · exact mul_nonneg (hψn x) (hgpos x hx hne).le
    have hclQ : closure Q.set ⊆ cylSlab T :=
      (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
    have hcont : ContinuousOn (fun x => ψ x * g x) (cylSlab T) :=
      hψs.continuous.continuousOn.mul (hcontRow w)
    have hpos' : 0 < ∫ x in Q.set, ψ x * g x := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_slab_of_continuousOn hcont)]
      set W := (cylSlab T ∩ (fun x => ψ x * g x) ⁻¹' Ioi 0) ∩ Q.set
      have hWo : IsOpen W :=
        (hcont.isOpen_inter_preimage (isOpen_cylSlab T) isOpen_Ioi).inter Q.isOpen
      have hx₀Q : x₀ ∈ Q.set := mem_slabChart.mpr ⟨ht, hx₀s⟩
      have hx₀W : x₀ ∈ W := ⟨⟨hslab, mul_pos hψ0 hpos⟩, hx₀Q⟩
      refine lt_of_lt_of_le (hWo.measure_pos volume ⟨x₀, hx₀W⟩) (measure_mono fun x hx => ?_)
      exact ⟨ne_of_gt hx.1.2, hx.2⟩
    have : ∫ x in Q.set, ψ x * g x = 0 := hint
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine key (-w) hw.neg ?_
    rw [map_neg]; linarith
  · exact key w hw hgt

end DuBoisReymond

/-! ### `cor:strong-solution-upgrade` -/

section Upgrade

variable {T : ℝ} {Ysec : Type} [Fintype Ysec] {FC : FermionCarrier Ysec}

/-- The total first-variation covector field of limit fields: first-order gravity + Yang–Mills +
Higgs + complete Dirac–Yukawa, on the limit jet. -/
def totalCov (θ : CoefficientBank Ysec) (L : LimitFields FC.C) (x : E4) :
    RJet FC.C →L[ℝ] ℝ :=
  gravCov θ (limitJet L x) + (bosonCov θ (limitJet L x) + diracCov FC θ (limitJet L x))

/-- Classical regularity of the limit's first-variation coefficients: the gravitational and
matter covector fields are `C¹` on the open slab and spatially periodic. -/
structure CovRegular (θ : CoefficientBank Ysec) (L : LimitFields FC.C) : Prop where
  grav : ContDiffOn ℝ 1 (fun x => gravCov θ (limitJet L x)) (cylSlab T)
  matter : ContDiffOn ℝ 1 (fun x => bosonCov θ (limitJet L x) + diracCov FC θ (limitJet L x))
    (cylSlab T)
  periodic : ∀ n x, totalCov θ L (x + spatialShift n) = totalCov θ L x

/-- **`cor:strong-solution-upgrade` (regularity step).**  Under the hypotheses of
`reduced_closure`, every cutoff subsequence has a further subsequence with a limit `(L, θ₀)` in
the reduced action topology which is a distributional solution of all Euler equations and such
that, **if** the limit's first-variation coefficients are classical (`CovRegular`: `C¹`, spatially
periodic — the manuscript derives this from `C_tH^s ∩ C¹_tH^{s-1} ∩ C²_tH^{s-2}`, `s ≥ 5`, by
Sobolev multiplication, not formalised here), then **all Euler rows vanish pointwise**: the
second-order bosonic rows (metric, gauge, Higgs) and the first-order spinor rows, in every
admissible direction at every point of `(0,T) × (0,1)³`. -/
theorem strong_solution_upgrade (hT : 0 < T) (reg : RegulatorSequence T FC)
    (hcert : ∀ Q : ChartBox T, reg.SatisfiesReducedCertificate Q)
    (hcons : reg.FirstVariationConsistent) (hstat : reg.PhysicallyStationary)
    (hyuk : FC.YukawaContinuous) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (L : LimitFields FC.C) (θ₀ : CoefficientBank Ysec),
      (∀ t₀ t₁ (h0 : 0 < t₀) (h01 : t₀ < t₁) (h1 : t₁ < T),
        ReducedConvergence (slabChart t₀ t₁ h0 h01 h1) (fun k => reg.fields (ns (ψ k)))
          (fun k => reg.bank (ns (ψ k))) L θ₀) ∧
      (CovRegular (T := T) θ₀ L → ∀ x₀ : E4, x₀ 0 ∈ Ioo 0 T → (∀ i : Fin 3, x₀ i.succ ∈ Ioo 0 1) →
        ∀ w : FieldVal FC.C, IsAdmissible FC.left w → eulerRow (totalCov θ₀ L) x₀ w = 0) := by
  obtain ⟨ψ, hψ, L, θ₀, -, hRC, -, heuler, -⟩ := reduced_closure hT reg hcert hcons hstat hyuk ns hns
  refine ⟨ψ, hψ, L, θ₀, fun t₀ t₁ h0 h01 h1 => (hRC t₀ t₁ h0 h01 h1).1, fun hreg x₀ hx₀ hx₀s w hw => ?_⟩
  have hΛ : ContDiffOn ℝ 1 (totalCov θ₀ L) (cylSlab T) := hreg.grav.add hreg.matter
  refine eulerRow_eq_zero (r := reg.r0) hΛ hreg.periodic ?_ hx₀ hx₀s hw
  intro K t₀ t₁ h0 h01 h1 hK v
  have hcl : closure (slabChart t₀ t₁ h0 h01 h1 (T := T)).set ⊆ cylSlab T :=
    (closure_slabChart_subset h0 h01 h1).trans (slabTime_subset_cylSlab h0 h1)
  have i1 := integrableOn_slab_of_continuousOn (h0 := h0) (h01 := h01) (h1 := h1)
    (hreg.grav.continuousOn.clm_apply (continuous_testJet v).continuousOn)
  have i2 := integrableOn_slab_of_continuousOn (h0 := h0) (h01 := h01) (h1 := h1)
    (hreg.matter.continuousOn.clm_apply (continuous_testJet v).continuousOn)
  have he := heuler K t₀ t₁ h0 h01 h1 hK v
  simp only [gravLimitVariation, smLimitVariation] at he
  have e : ∀ x, totalCov θ₀ L x (testJet v.val x) = gravCov θ₀ (limitJet L x) (testJet v.val x) +
      (bosonCov θ₀ (limitJet L x) + diracCov FC θ₀ (limitJet L x)) (testJet v.val x) :=
    fun x => rfl
  simp only [e]
  rw [integral_add i1 i2]
  exact he

end Upgrade

/-! ### Non-vacuity -/

section NonVacuity

variable {T : ℝ}

/-- The flat limit fields over the trivial carrier. -/
def flatLimitT : LimitFields (trivialCarrier Unit).C :=
  ⟨fun _ => flatCoframe, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem limitJet_flatLimitT_de (x : E4) : (limitJet flatLimitT x).de = 0 := by
  funext i a μ; simp [limitJet, flatLimitT, toJet, reJet, RJet.mk, RJet.de]

theorem totalCov_flat (x : E4) : totalCov (FC := trivialCarrier Unit) physicalBank flatLimitT x = 0 := by
  simp only [totalCov, gravCov_flat _ (limitJet_flatLimitT_de x),
    smCov_flat (limitJet flatLimitT x) rfl rfl rfl rfl rfl rfl rfl rfl, add_zero]

/-- **Non-vacuity of `CovRegular`**: the flat limit has classical coefficients (its covector fields
vanish identically). -/
theorem flatLimit_covRegular :
    CovRegular (T := T) (FC := trivialCarrier Unit) physicalBank flatLimitT := by
  refine ⟨contDiffOn_const.congr fun x _ => gravCov_flat _ (limitJet_flatLimitT_de x),
    contDiffOn_const.congr fun x _ => smCov_flat _ rfl rfl rfl rfl rfl rfl rfl rfl,
    fun n x => by rw [totalCov_flat, totalCov_flat]⟩

end NonVacuity

end EinsteinSM
end RenewalGeometry
