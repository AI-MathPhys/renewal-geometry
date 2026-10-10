/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeNeumannLaplacian

/-!
# Reflection averages on `𝕋⁴` and symmetric weak formulations
  (stage B2 support for the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `reflSetEquiv`, `reflSet_involutive`, `reflSet_reflect`: the partial reflections
  `R_A = ∏_{i ∈ A} R_i` of `𝕋⁴` and their group law `R_A ∘ R_j = R_{A ∆ {j}}`;
* `IsTPartial.comp_reflSet`: `∂_μ (f ∘ R_A) = ±(∂_μ f) ∘ R_A` (sign `pSign A μ`);
* `integral_conj_comp_reflSet`: for `F` of parity pattern `S`,
  `∫ conj(G ∘ R_A) F = (∏_{i ∈ A} pSign S i) ∫ conj(G) F`;
* `avgEven u = 16⁻¹ Σ_A u ∘ R_A` (**the even part**), `hasParity_avgEven` (it is even),
  `isTPartial_avgEven` (its derivatives), `integral_conj_avgEven_partial` (**testing against the
  even part suffices**: for `F_μ` of pattern `{μ}`, `∫ conj(∂_μ avgEven u) F_μ = ∫ conj(∂_μ u) F_μ`).
  Consequence: a weak equation `Σ_μ ∫ conj(∂_μ u) F_μ = 0` with Neumann-patterned `F` holds for
  all torus test functions as soon as it holds for even ones, i.e. for the cube test functions
  `W^{1,2}(Q₀)`;
* `weakLinCoulomb_comp_reflect`: the weak linearised Coulomb equation is invariant under the
  reflections when the connection and the datum are Neumann-patterned.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.CubeNeumann

open SobolevOpen TorusSobolev UhlenbeckTorus UhlenbeckOpenness

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

/-! ### Partial reflections -/

theorem reflSet_involutive (A : Finset (Fin 4)) (t : 𝕋⁴) : reflSet A (reflSet A t) = t := by
  funext i; by_cases hi : i ∈ A <;> simp [reflSet, hi]

/-- `R_A` as a measurable equivalence. -/
def reflSetEquiv (A : Finset (Fin 4)) : 𝕋⁴ ≃ᵐ 𝕋⁴ where
  toFun := reflSet A
  invFun := reflSet A
  left_inv := reflSet_involutive A
  right_inv := reflSet_involutive A
  measurable_toFun := (measurePreserving_reflSet A).measurable
  measurable_invFun := (measurePreserving_reflSet A).measurable

theorem reflSet_reflect (A : Finset (Fin 4)) (j : Fin 4) (t : 𝕋⁴) :
    reflSet A (reflect j t) = reflSet (symmDiff A {j}) t := by
  funext i
  by_cases hi : i = j
  · subst hi
    by_cases hA : i ∈ A <;> simp [reflSet, reflect_apply_self, hA, Finset.mem_symmDiff]
  · by_cases hA : i ∈ A <;> simp [reflSet, reflect_apply_ne hi, hA, Finset.mem_symmDiff, hi]

theorem integral_comp_reflSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝕋⁴ → E) (A : Finset (Fin 4)) : ∫ x, f (reflSet A x) = ∫ x, f x :=
  (measurePreserving_reflSet A).integral_comp' (f := reflSetEquiv A) f

/-- **Derivatives under partial reflections.** -/
theorem IsTPartial.comp_reflSet {μ : Fin 4} (A : Finset (Fin 4)) :
    ∀ {f g : 𝕋⁴ → ℂ}, IsTPartial μ f g →
      IsTPartial μ (fun x => f (reflSet A x)) (fun x => pSign A μ * g (reflSet A x)) := by
  induction A using Finset.induction_on with
  | empty =>
    intro f g h
    simpa [reflSet_empty, pSign] using h
  | insert j A hj ih =>
    intro f g h
    have h1 := ih (IsTPartial.comp_reflect h j)
    have e1 : (fun x => f (reflect j (reflSet A x))) = fun x => f (reflSet (insert j A) x) := by
      funext x; rw [reflSet_insert hj]
    have e2 : (fun x => pSign A μ * (dSign j μ * g (reflect j (reflSet A x)))) =
        fun x => pSign (insert j A) μ * g (reflSet (insert j A) x) := by
      funext x
      rw [reflSet_insert hj, ← mul_assoc]
      congr 1
      unfold pSign dSign
      by_cases hμ : μ = j
      · subst hμ; simp [hj]
      · simp [Finset.mem_insert, hμ]
    rw [e1, e2] at h1
    exact h1

theorem prod_pSign_singleton (A : Finset (Fin 4)) (μ : Fin 4) :
    ∏ i ∈ A, pSign {μ} i = pSign A μ := by
  unfold pSign
  by_cases hμ : μ ∈ A
  · rw [← Finset.mul_prod_erase A _ hμ]
    simp only [Finset.mem_singleton, if_true, hμ]
    rw [Finset.prod_eq_one fun i hi => by
      have : i ≠ μ := Finset.ne_of_mem_erase hi
      simp [Finset.mem_singleton, this]]
    ring
  · rw [Finset.prod_eq_one fun i hi => by
      have : i ≠ μ := fun h => hμ (h ▸ hi)
      simp [this]]
    simp [hμ]

/-- **Change of variables against a parity function**:
`∫ conj(G ∘ R_A) F = (∏_{i ∈ A} pSign S i) ∫ conj(G) F` for `F` of pattern `S`. -/
theorem integral_conj_comp_reflSet {S : Finset (Fin 4)} {F : 𝕋⁴ → ℂ} (hF : HasParity S F)
    (G : 𝕋⁴ → ℂ) (A : Finset (Fin 4)) :
    ∫ t, conj (G (reflSet A t)) * F t = (∏ i ∈ A, pSign S i) * ∫ t, conj (G t) * F t := by
  rw [← integral_comp_reflSet (fun t => conj (G (reflSet A t)) * F t) A, ← integral_const_mul]
  refine integral_congr_ae ((hF.comp_reflSet A).mono fun t ht => ?_)
  simp only [reflSet_involutive, ht]; ring

/-! ### The even part -/

/-- **The even part** `avgEven u = 16⁻¹ Σ_A u ∘ R_A`. -/
def avgEven (u : 𝕋⁴ → ℂ) (t : 𝕋⁴) : ℂ := (1 / 16 : ℂ) * ∑ A : Finset (Fin 4), u (reflSet A t)

/-- The symmetric-difference involution of `Finset (Fin 4)`. -/
def symmDiffEquiv (j : Fin 4) : Finset (Fin 4) ≃ Finset (Fin 4) where
  toFun A := symmDiff A {j}
  invFun A := symmDiff A {j}
  left_inv A := symmDiff_symmDiff_cancel_right {j} A
  right_inv A := symmDiff_symmDiff_cancel_right {j} A

theorem hasParity_avgEven (u : 𝕋⁴ → ℂ) : HasParity ∅ (avgEven u) := by
  intro j
  refine Eventually.of_forall fun t => ?_
  simp only [avgEven, pSign_empty, one_mul, reflSet_reflect]
  congr 1
  exact Fintype.sum_equiv (symmDiffEquiv j) _ _ fun A => rfl

theorem memLp_avgEven {u : 𝕋⁴ → ℂ} (hu : MemLp u 2 volume) : MemLp (avgEven u) 2 volume :=
  (memLp_finsetSum _ fun A _ => hu.comp_measurePreserving (measurePreserving_reflSet A)).const_mul _

/-- The partial derivative of the even part. -/
def avgEvenGrad (g : Fin 4 → 𝕋⁴ → ℂ) (μ : Fin 4) (t : 𝕋⁴) : ℂ :=
  (1 / 16 : ℂ) * ∑ A : Finset (Fin 4), pSign A μ * g μ (reflSet A t)

theorem memLp_avgEvenGrad {g : Fin 4 → 𝕋⁴ → ℂ} (hg : ∀ μ, MemLp (g μ) 2 volume) (μ : Fin 4) :
    MemLp (avgEvenGrad g μ) 2 volume :=
  (memLp_finsetSum _ fun A _ =>
    ((hg μ).comp_measurePreserving (measurePreserving_reflSet A)).const_mul _).const_mul _

theorem isTPartial_avgEven {u : 𝕋⁴ → ℂ} {g : Fin 4 → 𝕋⁴ → ℂ} (hu : MemLp u 2 volume)
    (hg : ∀ μ, MemLp (g μ) 2 volume) (hd : ∀ μ, IsTPartial μ u (g μ)) (μ : Fin 4) :
    IsTPartial μ (avgEven u) (avgEvenGrad g μ) := by
  refine IsTPartial.const_mul ?_ _
  refine IsTPartial.finset_sum Finset.univ (fun A => IsTPartial.comp_reflSet A (hd μ)) (fun A => ?_)
    (fun A => ?_)
  · exact integrable_of_memLp_two (hu.comp_measurePreserving (measurePreserving_reflSet A))
  · exact integrable_of_memLp_two
      (((hg μ).comp_measurePreserving (measurePreserving_reflSet A)).const_mul _)

/-- **Testing against the even part suffices**: for `F` with the pattern `{μ}`,
`∫ conj(∂_μ (avgEven u)) F = ∫ conj(∂_μ u) F`. -/
theorem integral_conj_avgEvenGrad {μ : Fin 4} {F : 𝕋⁴ → ℂ} (hF : HasParity {μ} F)
    (hFm : MemLp F 2 volume) {g : Fin 4 → 𝕋⁴ → ℂ} (hg : ∀ ν, MemLp (g ν) 2 volume) :
    ∫ t, conj (avgEvenGrad g μ t) * F t = ∫ t, conj (g μ t) * F t := by
  have hint : ∀ A : Finset (Fin 4), Integrable (fun t => conj (pSign A μ * g μ (reflSet A t)) * F t) :=
    fun A => integrable_conj_mul
      (((hg μ).comp_measurePreserving (measurePreserving_reflSet A)).const_mul _) hFm
  have e : (fun t => conj (avgEvenGrad g μ t) * F t) = fun t =>
      (1 / 16 : ℂ) * ∑ A : Finset (Fin 4), conj (pSign A μ * g μ (reflSet A t)) * F t := by
    funext t
    simp only [avgEvenGrad, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp only [map_div₀, map_one, map_ofNat]; ring
  rw [e, integral_const_mul, integral_finset_sum _ fun A _ => hint A]
  have hA : ∀ A : Finset (Fin 4), ∫ t, conj (pSign A μ * g μ (reflSet A t)) * F t =
      ∫ t, conj (g μ t) * F t := by
    intro A
    have hs : conj (pSign A μ) = pSign A μ := by unfold pSign; split_ifs <;> simp
    simp only [map_mul, hs, mul_assoc]
    rw [integral_const_mul, integral_conj_comp_reflSet hF (g μ) A, prod_pSign_singleton,
      ← mul_assoc, pSign_mul_self, one_mul]
  simp only [hA, Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul]
  have : (Fintype.card (Finset (Fin 4)) : ℂ) = 16 := by
    rw [Fintype.card_finset]; norm_num
  rw [this]; ring

/-! ### Reflection invariance of the weak linearised Coulomb equation -/

variable {m : ℕ}

/-- A matrix-valued datum `h c e μ` with the Neumann pattern (`h_μ` odd under `R_μ`, even under the
other reflections). -/
def IsNeumannData (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : Prop :=
  ∀ c e μ, HasParity {μ} (h c e μ)

theorem conj_dSign (j μ : Fin 4) : conj (dSign j μ) = dSign j μ := by
  unfold dSign; split_ifs <;> simp

theorem sum_comm_sign (p : ℂ) {m : ℕ} (A B B' A' : Fin m → ℂ) :
    ∑ k, (p * A k * B k - B' k * (p * A' k)) = p * ∑ k, (A k * B k - B' k * A' k) := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- **Reflection invariance**: if the connection `a` and the datum `h` have the Neumann pattern
and `ξ` solves `d^* d_a ξ = d^* h` weakly, so does `ξ ∘ R_j` (with derivatives `±(∂ξ) ∘ R_j`). -/
theorem weakLinCoulomb_comp_reflect {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} {ξ : Fin m → Fin m → 𝕋⁴ → ℂ}
    {dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (ha : IsNeumannMForm a) (hh : IsNeumannData h)
    (hw : WeakLinCoulomb a h ξ dξ) (j : Fin 4) :
    WeakLinCoulomb a h (fun c e x => ξ c e (reflect j x))
      (fun c e μ x => dSign j μ * dξ c e μ (reflect j x)) := by
  intro u gu hu hgu hdu c e
  have ht := hw (fun x => u (reflect j x)) (fun μ x => dSign j μ * gu μ (reflect j x))
    (memLp_comp_reflect hu j) (fun μ => (memLp_comp_reflect (hgu μ) j).const_mul _)
    (fun μ => IsTPartial.comp_reflect (hdu μ) j) c e
  have hpar : ∀ᵐ x ∂volume, ∀ μ c' e', a μ c' e' (reflect j x) = dSign j μ * a μ c' e' x := by
    have : ∀ μ c' e', ∀ᵐ x ∂volume, a μ c' e' (reflect j x) = dSign j μ * a μ c' e' x :=
      fun μ c' e' => by
        filter_upwards [ha μ c' e' j] with x hx
        rw [hx, pSign_singleton]
    exact ae_all_iff.2 fun μ => ae_all_iff.2 fun c' => ae_all_iff.2 fun e' => this μ c' e'
  have hparh : ∀ᵐ x ∂volume, ∀ μ, h c e μ (reflect j x) = dSign j μ * h c e μ x := by
    refine ae_all_iff.2 fun μ => ?_
    filter_upwards [hh c e μ j] with x hx
    rw [hx, pSign_singleton]
  have hL : ∀ μ, ∫ x, conj (dSign j μ * gu μ (reflect j x)) * covLin a ξ dξ c e μ x =
      ∫ x, conj (gu μ x) * covLin a (fun c e x => ξ c e (reflect j x))
        (fun c e μ x => dSign j μ * dξ c e μ (reflect j x)) c e μ x := by
    intro μ
    rw [← integral_comp_reflect' (fun x => conj (dSign j μ * gu μ (reflect j x)) *
      covLin a ξ dξ c e μ x) j]
    refine integral_congr_ae (hpar.mono fun x hx => ?_)
    simp only [reflect_reflect, covLin, hx, map_mul, conj_dSign]
    rw [sum_comm_sign]
    have hs := dSign_mul_self j μ
    linear_combination (conj (gu μ x) * (∑ k, (a μ c k x * ξ k e (reflect j x) -
      ξ c k (reflect j x) * a μ k e x))) * hs
  have hR : ∀ μ, ∫ x, conj (dSign j μ * gu μ (reflect j x)) * h c e μ x =
      ∫ x, conj (gu μ x) * h c e μ x := by
    intro μ
    rw [← integral_comp_reflect' (fun x => conj (dSign j μ * gu μ (reflect j x)) *
      h c e μ x) j]
    refine integral_congr_ae (hparh.mono fun x hx => ?_)
    simp only [reflect_reflect, hx, map_mul, conj_dSign]
    have hs := dSign_mul_self j μ
    linear_combination (conj (gu μ x) * h c e μ x) * hs
  simp only [hL, hR] at ht
  exact ht

/-- **The linearised Coulomb isomorphism on the symmetric class**: for a Neumann-patterned
connection with small `L⁴` norm and a Neumann-patterned datum, the unique mean-zero solution of
`linearized_coulomb_iso` is **even** (and its gradient has the Neumann pattern). -/
theorem linearized_coulomb_iso_even (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112))
    (haN : IsNeumannMForm a)
    (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) (hh : ∀ c e μ, MemLp (h c e μ) 2 volume)
    (hhN : IsNeumannData h) :
    ∃ (ξ : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      (∀ c e, MemLp (ξ c e) 2 volume) ∧ (∀ c e μ, MemLp (dξ c e μ) 2 volume) ∧
      (∀ c e μ, IsTPartial μ (ξ c e) (dξ c e μ)) ∧ (∀ c e, mFourierCoeff (ξ c e) 0 = 0) ∧
      WeakLinCoulomb a h ξ dξ ∧
      (∀ c e μ, eLpNorm (dξ c e μ) 2 volume ≤
        2 * ∑ c', ∑ e', ∑ μ', eLpNorm (h c' e' μ') 2 volume) ∧
      (∀ c e, HasParity ∅ (ξ c e)) ∧ (∀ c e μ, HasParity {μ} (dξ c e μ)) ∧
      ∀ (ξ' : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ' : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
        (∀ c e, MemLp (ξ' c e) 2 volume) → (∀ c e μ, MemLp (dξ' c e μ) 2 volume) →
        (∀ c e μ, IsTPartial μ (ξ' c e) (dξ' c e μ)) → (∀ c e, mFourierCoeff (ξ' c e) 0 = 0) →
        WeakLinCoulomb a h ξ' dξ' → ∀ c e, ξ' c e =ᵐ[volume] ξ c e := by
  obtain ⟨ξ, dξ, h1, h2, h3, h4, h5, h6, h7⟩ := linearized_coulomb_iso a ha hsmall h hh
  have heven : ∀ c e, HasParity ∅ (ξ c e) := by
    intro c e j
    have hu := h7 (fun c e x => ξ c e (reflect j x))
      (fun c e μ x => dSign j μ * dξ c e μ (reflect j x))
      (fun c e => memLp_comp_reflect (h1 c e) j)
      (fun c e μ => (memLp_comp_reflect (h2 c e μ) j).const_mul _)
      (fun c e μ => IsTPartial.comp_reflect (h3 c e μ) j)
      (fun c e => by rw [mFourierCoeff_comp_reflect, flip_zero, h4 c e])
      (weakLinCoulomb_comp_reflect haN hhN h5 j) c e
    filter_upwards [hu] with x hx
    rw [hx, pSign_empty, one_mul]
  refine ⟨ξ, dξ, h1, h2, h3, h4, h5, h6, heven, fun c e μ => ?_, h7⟩
  have := (heven c e).partial (h1 c e) (h2 c e μ) (h3 c e μ)
  rwa [show symmDiff (∅ : Finset (Fin 4)) {μ} = {μ} by ext; simp [Finset.mem_symmDiff]] at this

end RenewalGeometry.CubeNeumann
