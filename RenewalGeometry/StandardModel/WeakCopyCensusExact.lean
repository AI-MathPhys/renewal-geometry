/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import Mathlib
import RenewalGeometry.Analysis.CompactGroupHaarTwirl
import RenewalGeometry.StandardModel.ReciprocalReturnMassExact

/-!
# Positive weak-copy census (`thm:weak-copy-census`, spacetime_gauge_duality)

Let `W₂ = ℂ²` (index `Fin 2`) be the weak defining module, `M` a finite multiplicity space and
`J ⪰ 0` an operator on `W₂ ⊗ M` (index `Fin 2 × M`).  With `B := Tr_{W₂} J`:

* `weakGram_posSemidef`: `B ⪰ 0`.
* `weakTwirl_eq`: for **every** left-invariant probability measure `μ` on `SU(2)` — in
  particular for normalized Haar measure `HaarTwirl.suHaar (Fin 2)` — the Haar twirl
  `∫ (g ⊗ I) J (g^* ⊗ I) dμ(g)` equals `½ I ⊗ B` (`eq:weak-copy-twirl`).  The integral is the
  genuine (entrywise Bochner) Haar integral on the compact group `SU(2)`; no finite design is
  substituted.
* `occCarrier_eq_weakTensor`, `range_weakTwirl_eq`: the gauge-cyclic carrier
  `span{(g ⊗ I) v : g ∈ SU(2), v ∈ Ran J}` equals `Ran J̄ = W₂ ⊗ Ran B`
  (`eq:weak-gauge-cyclic-support`).
* `finrank_occCarrier`: `dim K^occ = 2 · rank B`, i.e. the carrier is `rank B` copies of the
  doublet (`eq:weak-copy-count`).
* `rank_eq_one_iff`: exactly one copy iff `m_H = Tr B > 0` and `p_H = m_H² - Tr B² = 0`
  (`eq:one-weak-doublet-test`).
* `weakGram_basis_change`, `census_basis_invariant`: invariance under a unitary change of basis
  of `M` (the criterion depends on `J` only, hence not on Kraus coordinates or phases).
* `weak_copy_census`: the assembled proposition.
-/

open Matrix MeasureTheory
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace WeakCopyCensus

open ReciprocalReturnMass (partialTrace blk partialTrace_apply)

/-- The weak gauge group `SU(W₂) = SU(2)`. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The weak lift `g ⊗ I_M` on `W₂ ⊗ M`. -/
def weakLift (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × M) (Fin 2 × M) ℂ :=
  g ⊗ₖ (1 : Matrix M M ℂ)

/-- The weak-copy Gram `B_H = Tr_{W₂} J_H` (`eq:weak-copy-Gram`). -/
def weakGram (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) : Matrix M M ℂ :=
  partialTrace J

/-- The Haar twirl `J̄_H = ∫ (g ⊗ I) J_H (g^* ⊗ I) dμ(g)` (entrywise integral). -/
noncomputable def weakTwirl (μ : Measure SU2) (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    Matrix (Fin 2 × M) (Fin 2 × M) ℂ :=
  HaarTwirl.matrixIntegral μ fun g => weakLift g.1 * J * (weakLift g.1)ᴴ

/-- The gauge-cyclic occurrence carrier
`K_H^occ = span{(g ⊗ I) v : g ∈ SU(W₂), v ∈ Ran J_H}` (`eq:weak-gauge-cyclic-carrier`). -/
def occCarrier (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) : Submodule ℂ (Fin 2 × M → ℂ) :=
  Submodule.span ℂ
    {x | ∃ g : SU2, ∃ v ∈ LinearMap.range J.mulVecLin, x = weakLift g.1 *ᵥ v}

/-- The subspace `W₂ ⊗ R ⊆ W₂ ⊗ M`: the span of the elementary tensors `e ⊗ w`, `w ∈ R`. -/
def weakTensor (R : Submodule ℂ (M → ℂ)) : Submodule ℂ (Fin 2 × M → ℂ) :=
  Submodule.span ℂ {x | ∃ e : Fin 2 → ℂ, ∃ w ∈ R, x = fun p => e p.1 * w p.2}

/-- Slice description of `W₂ ⊗ R`: vectors all of whose `W₂`-slices lie in `R`. -/
def sliceSub (R : Submodule ℂ (M → ℂ)) : Submodule ℂ (Fin 2 × M → ℂ) where
  carrier := {v | ∀ a, (fun i => v (a, i)) ∈ R}
  add_mem' {v w} hv hw a := by
    exact R.add_mem (hv a) (hw a)
  zero_mem' a := R.zero_mem
  smul_mem' c v hv a := R.smul_mem c (hv a)

/-! ### Elementary computations -/

/-- The embedding `w ↦ e_c ⊗ w`. -/
def slot (c : Fin 2) (w : M → ℂ) : Fin 2 × M → ℂ := fun p => if p.1 = c then w p.2 else 0

theorem weakLift_mulVec_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 × M → ℂ) (a : Fin 2)
    (i : M) : (weakLift g *ᵥ x) (a, i) = ∑ c, g a c * x (c, i) := by
  simp only [weakLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq]

theorem one_kronecker_mulVec_apply (B : Matrix M M ℂ) (x : Fin 2 × M → ℂ) (a : Fin 2) (i : M) :
    (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) *ᵥ x) (a, i) = (B *ᵥ fun k => x (a, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq]

theorem slice_sum_slot (v : Fin 2 × M → ℂ) : v = ∑ a, slot a (fun i => v (a, i)) := by
  funext ⟨c, i⟩
  simp [slot, Finset.sum_apply]

theorem mulVec_slot_apply (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) (c : Fin 2) (w : M → ℂ)
    (p : Fin 2 × M) : (J *ᵥ slot c w) p = ∑ k, J p (c, k) * w k := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, slot, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq']

theorem star_slot_dotProduct (c : Fin 2) (w : M → ℂ) (v : Fin 2 × M → ℂ) :
    star (slot c w) ⬝ᵥ v = ∑ i, star (w i) * v (c, i) := by
  simp only [dotProduct, Fintype.sum_prod_type, slot, Pi.star_apply, apply_ite star, star_zero,
    ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']

/-- `w^* B w = Σ_c (e_c ⊗ w)^* J (e_c ⊗ w)`. -/
theorem quadratic_weakGram (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) (w : M → ℂ) :
    star w ⬝ᵥ (weakGram J *ᵥ w) = ∑ c, star (slot c w) ⬝ᵥ (J *ᵥ slot c w) := by
  simp only [star_slot_dotProduct, mulVec_slot_apply]
  simp only [weakGram, partialTrace, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ i, ∑ c, ∑ k, star (w i) * (J (c, i) (c, k) * w k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-! ### Positivity of the Gram -/

/-- `B_H = Tr_{W₂} J_H ⪰ 0` whenever `J_H ⪰ 0`. -/
theorem weakGram_posSemidef {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    (weakGram J).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext i j
    simp only [weakGram, partialTrace, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := congrFun (congrFun hJ.1 (c, i)) (c, j)
    rw [← this]
    simp [Matrix.conjTranspose_apply]
  · rw [quadratic_weakGram]
    exact Finset.sum_nonneg fun c _ => hJ.dotProduct_mulVec_nonneg _

/-! ### The Haar twirl -/

theorem weakLift_conj_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ)
    (x y : Fin 2) (a b : M) :
    (weakLift (M := M) g * J * (weakLift (M := M) g)ᴴ : Matrix (Fin 2 × M) (Fin 2 × M) ℂ)
      (x, a) (y, b) = (g * blk J a b * gᴴ) x y := by
  -- `blk` in `ReciprocalReturnMass` is indexed `V × N` with `V` the acted factor
  have hb : blk (weakLift g * J * (weakLift g)ᴴ) a b = g * blk J a b * gᴴ := by
    rw [weakLift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ReciprocalReturnMass.blk_mul_kronecker, ReciprocalReturnMass.blk_kronecker_mul]
  have := congrFun (congrFun hb x) y
  simpa [blk] using this

/-- **Weak Haar twirl** (`eq:weak-copy-twirl`).  For every left-invariant probability measure
`μ` on `SU(2)` (normalized Haar measure in particular),
`∫ (g ⊗ I) J (g^* ⊗ I) dμ(g) = ½ I_{W₂} ⊗ Tr_{W₂} J`.  No positivity is needed. -/
theorem weakTwirl_eq (μ : Measure SU2) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    weakTwirl μ J = (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakGram J) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  have h := congrFun (congrFun (HaarTwirl.su2_haar_twirl μ (blk J a b)) x) y
  simp only [weakTwirl, HaarTwirl.matrixIntegral_apply, weakLift_conj_apply]
  simp only [HaarTwirl.twirl, HaarTwirl.matrixIntegral_apply] at h
  rw [h, Matrix.smul_apply, Matrix.smul_apply, kronecker_apply, weakGram, partialTrace_apply,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The twirl against normalized Haar measure on `SU(2)`. -/
theorem weakTwirl_haar_eq (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    weakTwirl (HaarTwirl.suHaar (Fin 2)) J =
      (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakGram J) :=
  weakTwirl_eq _ J

/-! ### Ranges and the gauge-cyclic carrier -/

theorem weakTensor_eq_sliceSub (R : Submodule ℂ (M → ℂ)) : weakTensor R = sliceSub R := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, w, hw, rfl⟩ a
    have := R.smul_mem (e a) hw
    simpa [Pi.smul_def] using this
  · intro v hv
    rw [slice_sum_slot v]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ?_
    refine ⟨Pi.single a 1, fun i => v (a, i), hv a, ?_⟩
    funext ⟨c, i⟩
    by_cases h : c = a
    · subst h; simp [slot]
    · simp [slot, h, Pi.single_apply]

theorem range_one_kronecker_eq_sliceSub (B : Matrix M M ℂ) :
    LinearMap.range ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B).mulVecLin =
      sliceSub (LinearMap.range B.mulVecLin) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ a
    refine ⟨fun k => x (a, k), ?_⟩
    funext i
    simp [one_kronecker_mulVec_apply]
  · intro v hv
    choose u hu using hv
    refine ⟨fun p => u p.1 p.2, ?_⟩
    funext ⟨a, i⟩
    simp only [Matrix.mulVecLin_apply, one_kronecker_mulVec_apply]
    have := congrFun (hu a) i
    simpa using this

/-- `Ran J̄_H = W₂ ⊗ Ran B_H` (second equality of `eq:weak-gauge-cyclic-support`). -/
theorem range_weakTwirl_eq (μ : Measure SU2) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    LinearMap.range (weakTwirl μ J).mulVecLin =
      weakTensor (LinearMap.range (weakGram J).mulVecLin) := by
  rw [weakTensor_eq_sliceSub, ← range_one_kronecker_eq_sliceSub, weakTwirl_eq]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨(1 / 2 : ℂ) • y, ?_⟩
    simp [Matrix.smul_mulVec, Matrix.mulVec_smul]
  · rintro _ ⟨y, rfl⟩
    refine ⟨(2 : ℂ) • y, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    norm_num

/-- `ker (I ⊗ B) ⊆ ker J` for `J ⪰ 0`, `B = Tr_{W₂} J`. -/
theorem ker_le_ker {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    LinearMap.ker ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakGram J).mulVecLin ≤
      LinearMap.ker J.mulVecLin := by
  intro x hx
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
  have hslice : ∀ a, weakGram J *ᵥ (fun k => x (a, k)) = 0 := by
    intro a; funext i
    have := congrFun hx (a, i)
    simpa [one_kronecker_mulVec_apply] using this
  have hslot : ∀ a c, J *ᵥ slot c (fun k => x (a, k)) = 0 := by
    intro a c
    rw [← hJ.dotProduct_mulVec_zero_iff]
    have hsum := quadratic_weakGram J (fun k => x (a, k))
    rw [hslice a, dotProduct_zero] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hJ.dotProduct_mulVec_nonneg _)).mp
      hsum.symm c (Finset.mem_univ c)
  rw [slice_sum_slot x, Matrix.mulVec_sum]
  exact Finset.sum_eq_zero fun a _ => hslot a a

/-- `Ran J ⊆ W₂ ⊗ Ran B` for `J ⪰ 0`. -/
theorem range_le_sliceSub {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    LinearMap.range J.mulVecLin ≤ sliceSub (LinearMap.range (weakGram J).mulVecLin) := by
  rw [← range_one_kronecker_eq_sliceSub]
  refine HaarTwirl.range_le_range_of_ker_le_ker hJ.1 ?_ (ker_le_ker hJ)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, (weakGram_posSemidef hJ).1.eq]

/-- The carrier `K^occ` is invariant under `g ⊗ I` for `g ∈ SU(2)`. -/
theorem occCarrier_weakLift_mem (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) (g : SU2)
    {x : Fin 2 × M → ℂ} (hx : x ∈ occCarrier J) : weakLift g.1 *ᵥ x ∈ occCarrier J := by
  have hle : occCarrier J ≤ (occCarrier J).comap (weakLift (M := M) g.1).mulVecLin := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, v, hv, rfl⟩
    refine Submodule.subset_span ⟨g * h, v, hv, ?_⟩
    simp [weakLift, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]
  exact hle hx

/-- The carrier `K^occ` is invariant under `E ⊗ I` for every `E ∈ M₂(ℂ)` (`SU(2)` spans
`M₂(ℂ)`). -/
theorem occCarrier_kronecker_mem (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ)
    (E : Matrix (Fin 2) (Fin 2) ℂ) {x : Fin 2 × M → ℂ} (hx : x ∈ occCarrier J) :
    weakLift E *ᵥ x ∈ occCarrier J := by
  have h1 := hx
  have hX := occCarrier_weakLift_mem J ⟨_, HaarTwirl.isigmaX_mem⟩ hx
  have hY := occCarrier_weakLift_mem J ⟨_, HaarTwirl.isigmaY_mem⟩ hx
  have hZ := occCarrier_weakLift_mem J ⟨_, HaarTwirl.isigmaZ_mem⟩ hx
  rw [HaarTwirl.su2_span_decomp E]
  simp only [weakLift, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_kronecker_one, Matrix.one_mulVec] at hX hY hZ ⊢
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ h1
  · exact Submodule.smul_mem _ _ hX
  · exact Submodule.smul_mem _ _ hY
  · exact Submodule.smul_mem _ _ hZ

theorem range_le_occCarrier (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    LinearMap.range J.mulVecLin ≤ occCarrier J := by
  intro v hv
  refine Submodule.subset_span ⟨1, v, hv, ?_⟩
  simp [weakLift]

/-- `e_b ⊗ B u = Σ_a (E_{ba} ⊗ I) J (e_a ⊗ u)`. -/
theorem slot_weakGram_mulVec (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) (b : Fin 2) (u : M → ℂ) :
    slot b (weakGram J *ᵥ u) =
      ∑ a, weakLift (Matrix.single b a (1 : ℂ)) *ᵥ (J *ᵥ slot a u) := by
  funext ⟨c, i⟩
  simp only [Finset.sum_apply, weakLift_mulVec_apply, mulVec_slot_apply]
  by_cases hc : c = b
  · subst hc
    have : ∀ a, ∑ c', Matrix.single c a (1 : ℂ) c c' * ∑ k, J (c', i) (a, k) * u k
        = ∑ k, J (a, i) (a, k) * u k := by
      intro a
      simp [Matrix.single_apply]
    simp only [this, slot, ↓reduceIte, weakGram, partialTrace, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · have : ∀ a c' : Fin 2, (Matrix.single b a (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) c c' = 0 := by
      intro a c'
      simp [Matrix.single_apply, Ne.symm hc]
    simp [this, slot, hc]

/-- `W₂ ⊗ Ran B ⊆ K^occ`. -/
theorem sliceSub_le_occCarrier (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) :
    sliceSub (LinearMap.range (weakGram J).mulVecLin) ≤ occCarrier J := by
  intro v hv
  rw [slice_sum_slot v]
  refine Submodule.sum_mem _ fun b _ => ?_
  obtain ⟨u, hu⟩ := hv b
  simp only [Matrix.mulVecLin_apply] at hu
  rw [← hu, slot_weakGram_mulVec]
  refine Submodule.sum_mem _ fun a _ => occCarrier_kronecker_mem J _ ?_
  exact range_le_occCarrier J ⟨slot a u, rfl⟩

/-- **Gauge-cyclic support** (`eq:weak-gauge-cyclic-support`, first equality with the second):
`K_H^occ = W₂ ⊗ Ran B_H` for `J_H ⪰ 0`. -/
theorem occCarrier_eq_weakTensor {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    occCarrier J = weakTensor (LinearMap.range (weakGram J).mulVecLin) := by
  rw [weakTensor_eq_sliceSub]
  refine le_antisymm ?_ (sliceSub_le_occCarrier J)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, v, hv, rfl⟩ a
  have hv' := range_le_sliceSub hJ hv
  have : (fun i => (weakLift g.1 *ᵥ v) (a, i)) = ∑ c, g.1 a c • fun i => v (c, i) := by
    funext i
    simp [weakLift_mulVec_apply, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hv' c)

/-! ### The copy count -/

/-- `W₂ ⊗ R ≃ R²` via slices. -/
def sliceEquiv (R : Submodule ℂ (M → ℂ)) : sliceSub R ≃ₗ[ℂ] (Fin 2 → R) where
  toFun v a := ⟨fun i => v.1 (a, i), v.2 a⟩
  invFun f := ⟨fun p => (f p.1).1 p.2, fun a => by simpa using (f a).2⟩
  map_add' v w := by funext a; ext i; simp
  map_smul' c v := by funext a; ext i; simp
  left_inv v := by ext ⟨a, i⟩; simp
  right_inv f := by funext a; ext i; simp

theorem finrank_weakTensor (R : Submodule ℂ (M → ℂ)) :
    Module.finrank ℂ (weakTensor R) = 2 * Module.finrank ℂ R := by
  rw [weakTensor_eq_sliceSub, (sliceEquiv R).finrank_eq, Module.finrank_pi_fintype]
  simp [Finset.sum_const, two_mul]

/-- **Copy count** (`eq:weak-copy-count`): `dim K_H^occ = 2 · rank B_H`, i.e. the gauge-cyclic
carrier consists of `g_H^occ = rank B_H` weak doublets. -/
theorem finrank_occCarrier {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    Module.finrank ℂ (occCarrier J) = 2 * (weakGram J).rank := by
  rw [occCarrier_eq_weakTensor hJ, finrank_weakTensor, Matrix.rank]

/-! ### The one-doublet trace test -/

/-- For nonnegative reals, exactly one is nonzero iff the sum is positive and
`(Σ λ)² - Σ λ² = 0`. -/
theorem card_ne_zero_eq_one_iff {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    Fintype.card {i // l i ≠ 0} = 1 ↔
      0 < ∑ i, l i ∧ (∑ i, l i) ^ 2 - ∑ i, l i ^ 2 = 0 := by
  classical
  have hpos : 0 < ∑ i, l i ↔ 0 < Fintype.card {i // l i ≠ 0} := by
    rw [Fintype.card_pos_iff]
    constructor
    · intro h
      by_contra hne
      push_neg at hne
      have : ∀ i, l i = 0 := fun i => by
        by_contra hi; exact hne.elim ⟨i, hi⟩
      simp [this] at h
    · rintro ⟨i, hi⟩
      exact lt_of_lt_of_le (lt_of_le_of_ne (hl i) (Ne.symm hi))
        (Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i))
  have hcross : (∑ i, l i) ^ 2 - ∑ i, l i ^ 2 =
      ∑ i, ∑ j ∈ Finset.univ.erase i, l i * l j := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  have hle : (∑ i, l i) ^ 2 - ∑ i, l i ^ 2 = 0 ↔ Fintype.card {i // l i ≠ 0} ≤ 1 := by
    rw [hcross, Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hl i) (hl j)), Fintype.card_le_one_iff]
    constructor
    · rintro h ⟨i, hi⟩ ⟨j, hj⟩
      by_contra hij
      have hij' : i ≠ j := fun e => hij (Subtype.ext e)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hl i) (hl k))).mp
        (h i (Finset.mem_univ i)) j (Finset.mem_erase.mpr ⟨Ne.symm hij', Finset.mem_univ j⟩)
      rcases mul_eq_zero.mp this with h' | h'
      · exact hi h'
      · exact hj h'
    · intro h i _
      refine Finset.sum_eq_zero fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      by_cases hi : l i = 0
      · simp [hi]
      by_cases hj' : l j = 0
      · simp [hj']
      exact absurd (congrArg Subtype.val (h ⟨i, hi⟩ ⟨j, hj'⟩)) (Ne.symm hji)
  rw [hle, hpos]
  omega

/-- `Tr(B²) = Σ λ_i²` for Hermitian `B`. -/
theorem trace_mul_self_eq_sum_sq {B : Matrix M M ℂ} (hB : B.IsHermitian) :
    (B * B).trace = ((∑ i, hB.eigenvalues i ^ 2 : ℝ) : ℂ) := by
  have hspec := hB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU : star (hB.eigenvectorUnitary : Matrix M M ℂ) * hB.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  have key : ∀ (U D : Matrix M M ℂ), star U * U = 1 →
      (U * D * star U * (U * D * star U)).trace = (D * D).trace := by
    intro U D hU
    have : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  conv_lhs => rw [hspec]
  rw [key _ _ hU, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  push_cast
  simp [sq]

/-- **One-doublet test** (`eq:one-weak-doublet-test`): for `B ⪰ 0`, `rank B = 1` iff
`m = Tr B > 0` and `p = m² - Tr B² = 0`. -/
theorem rank_eq_one_iff_of_posSemidef {B : Matrix M M ℂ} (hB : B.PosSemidef) :
    B.rank = 1 ↔ 0 < B.trace ∧ B.trace ^ 2 - (B * B).trace = 0 := by
  rw [hB.1.rank_eq_card_non_zero_eigs,
    card_ne_zero_eq_one_iff _ (fun i => hB.eigenvalues_nonneg i)]
  have ht : B.trace = ((∑ i, hB.1.eigenvalues i : ℝ) : ℂ) := by
    rw [hB.1.trace_eq_sum_eigenvalues]
    push_cast
    rfl
  rw [ht, trace_mul_self_eq_sum_sq hB.1, Complex.zero_lt_real, ← Complex.ofReal_pow,
    ← Complex.ofReal_sub, Complex.ofReal_eq_zero]

/-- The one-doublet test for the weak-copy census: for `J ⪰ 0`, exactly one weak doublet is
reached (`rank B_H = 1`) iff `m_H > 0` and `p_H = 0`. -/
theorem rank_eq_one_iff {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    (weakGram J).rank = 1 ↔
      0 < (weakGram J).trace ∧ (weakGram J).trace ^ 2 - (weakGram J * weakGram J).trace = 0 :=
  rank_eq_one_iff_of_posSemidef (weakGram_posSemidef hJ)

/-! ### Basis independence -/

/-- A unitary change of basis `U` of `M_H` acts on the packet by `(I ⊗ U) J (I ⊗ U)^*` and on the
Gram by `U B U^*`. -/
theorem weakGram_basis_change (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ) (U : Matrix M M ℂ) :
    weakGram (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U) * J * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U)ᴴ)
      = U * weakGram J * Uᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, weakGram,
    ReciprocalReturnMass.partialTrace_mul_one_kronecker,
    ReciprocalReturnMass.partialTrace_one_kronecker_mul]
  rfl

/-- The census data `rank B`, `m_H = Tr B`, `Tr B²` (hence `p_H`) are invariant under a unitary
change of basis of the multiplicity space. -/
theorem census_basis_invariant (J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ)
    {U : Matrix M M ℂ} (hU : U ∈ Matrix.unitaryGroup M ℂ) :
    let J' := ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U) * J *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ U)ᴴ
    (weakGram J').rank = (weakGram J).rank ∧ (weakGram J').trace = (weakGram J).trace ∧
      (weakGram J' * weakGram J').trace = (weakGram J * weakGram J).trace := by
  intro J'
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hdet : IsUnit U.det := by
    have := congrArg Matrix.det hUU'
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hdet' : IsUnit Uᴴ.det := by
    have := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hG : weakGram J' = U * weakGram J * Uᴴ := weakGram_basis_change J U
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
  · rw [hG, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  · rw [hG]
    have : U * weakGram J * Uᴴ * (U * weakGram J * Uᴴ) = U * (weakGram J * weakGram J) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

/-! ### Assembly -/

/-- **`thm:weak-copy-census` (Positive weak-copy census).**  Let `J_H ⪰ 0` on `W₂ ⊗ M_H` and
`B_H = Tr_{W₂} J_H`.  Then `B_H ⪰ 0`; for every left-invariant probability measure on `SU(2)`
(normalized Haar measure in particular) the twirl is `J̄_H = ½ I ⊗ B_H`; the gauge-cyclic
carrier satisfies `K_H^occ = Ran J̄_H = W₂ ⊗ Ran B_H`, of dimension `2 · rank B_H`
(`g_H^occ = rank B_H` doublets); and there is exactly one reached doublet iff `m_H > 0` and
`p_H = 0`. -/
theorem weak_copy_census {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef)
    (μ : Measure SU2) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    (weakGram J).PosSemidef ∧
    weakTwirl μ J = (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakGram J) ∧
    occCarrier J = LinearMap.range (weakTwirl μ J).mulVecLin ∧
    LinearMap.range (weakTwirl μ J).mulVecLin =
      weakTensor (LinearMap.range (weakGram J).mulVecLin) ∧
    Module.finrank ℂ (occCarrier J) = 2 * (weakGram J).rank ∧
    ((weakGram J).rank = 1 ↔
      0 < (weakGram J).trace ∧
        (weakGram J).trace ^ 2 - (weakGram J * weakGram J).trace = 0) :=
  ⟨weakGram_posSemidef hJ, weakTwirl_eq μ J,
    (occCarrier_eq_weakTensor hJ).trans (range_weakTwirl_eq μ J).symm,
    range_weakTwirl_eq μ J, finrank_occCarrier hJ, rank_eq_one_iff hJ⟩

/-- Non-vacuity: the census applies with normalized Haar measure on `SU(2)`. -/
example {J : Matrix (Fin 2 × M) (Fin 2 × M) ℂ} (hJ : J.PosSemidef) :
    weakTwirl (HaarTwirl.suHaar (Fin 2)) J =
      (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ weakGram J) :=
  (weak_copy_census hJ (HaarTwirl.suHaar (Fin 2))).2.1

end WeakCopyCensus
end RenewalGeometry
