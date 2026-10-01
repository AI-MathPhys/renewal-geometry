/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialConstraintReductionExact

/-!
# Uniform initial-constraint retraction
  (`prop:initial-constraint-retraction`, Einstein–SM action closure)

Setting: an exact finite-dimensional constraint reduction
`R : ExactInitialConstraintReduction Ck x0 m r B` (`def:exact-initial-reduction`,
`Action/ExactInitialConstraintReductionExact.lean`) with reduced coordinates
`λ ∈ ℝ^{m_h}` (`EuclideanSpace ℝ (Fin m)`), retained map `Φ_h = R.retained`,
correction family `ι_h = R.corr` and base datum `x0 = 𝒰(ẑ_h)(0)`.

* `initialConstraintRetraction` — for a linear map `A` with
  `σ_min(A) ≥ γ_*` (rendered as `γ_* ‖v‖ ≤ ‖A v‖` for all `v`, which is the
  definition of the smallest singular value for the Euclidean norm),
  the derivative margin `‖D_λΦ_h(λ) - A‖ ≤ γ_*/2` on `|λ| ≤ r_*`
  (`eq:constraint-derivative-margin`, with the derivative taken within the
  closed ball where `Φ_h` is `C¹`), a small residual `|Φ_h(0)| ≤ β_h` and
  `2 γ_*⁻¹ β_h ≤ r_*` (`eq:constraint-small-residual`): there is a unique
  zero `λ_h` of `Φ_h` in the closed ball of radius `2 γ_*⁻¹ β_h`, and every
  such zero gives a corrected datum `d_h = ι_h(λ_h)` with `𝔠_k(d_h) = 0`
  and `‖d_h - 𝒰(ẑ_h)(0)‖ ≤ 2 B_* γ_*⁻¹ β_h`
  (`eq:initial-data-retraction`).  The proof is the paper's: the
  frozen-inverse map `T λ = λ - A⁻¹ Φ_h(λ)` is a `1/2`-contraction of the ball
  into itself (mean-value inequality for `N = Φ_h - A`), Banach's fixed-point
  theorem, invertibility of `A`, the exact factorization and the reader
  Lipschitz bound.
* `initialConstraintRetraction_derivAtZero` — the literal form with
  `A_h := D_λΦ_h(x_h, 0)` (`eq:constraint-linear-margin`).

Scoped hypothesis disclosed: the reader Lipschitz constant satisfies
`0 ≤ B_*` (implicit for a Lipschitz constant).
-/

namespace RenewalGeometry

open Metric

section InitialConstraintRetraction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- `prop:initial-constraint-retraction`: under the linear margin
`σ_min(A) ≥ γ_*`, the derivative margin `‖DΦ_h(λ) - A‖ ≤ γ_*/2` on
`|λ| ≤ r_*`, the small residual `|Φ_h(0)| ≤ β_h` and `2γ_*⁻¹β_h ≤ r_*`,
the reduced exact map `Φ_h` has a unique zero in the closed ball of radius
`2γ_*⁻¹β_h`, and every such zero `λ_h` gives a corrected datum
`d_h = ι_h(λ_h)` satisfying the exact constraints and
`‖d_h - 𝒰(ẑ_h)(0)‖ ≤ 2 B_* γ_*⁻¹ β_h` (`eq:initial-data-retraction`). -/
theorem initialConstraintRetraction {Ck : X → Y} {x0 : X} {m : ℕ} {r B : ℝ}
    (R : ExactInitialConstraintReduction Ck x0 m r B)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) {γ β : ℝ} (hγ : 0 < γ)
    (hA : ∀ v, γ * ‖v‖ ≤ ‖A v‖)
    (hmargin : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
      ‖fderivWithin ℝ R.retained (closedBall 0 r) l - A‖ ≤ γ / 2)
    (hres : ‖R.retained 0‖ ≤ β) (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B) :
    (∃! l, l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * β) ∧ R.retained l = 0) ∧
      ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * β), R.retained l = 0 →
        Ck (R.corr l) = 0 ∧ ‖R.corr l - x0‖ ≤ 2 * B * γ⁻¹ * β := by
  set E := EuclideanSpace ℝ (Fin m)
  set Φ := R.retained
  set ρ := 2 * γ⁻¹ * β with hρdef
  have hβ : 0 ≤ β := (norm_nonneg _).trans hres
  have hρ : 0 ≤ ρ := by positivity
  have hball : closedBall (0 : E) ρ ⊆ closedBall 0 r := closedBall_subset_closedBall hrad
  -- invertibility of `A`
  have hinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hA v
    rw [hv, norm_zero] at h
    exact norm_le_zero_iff.1 (le_of_mul_le_mul_left (by simpa using h) hγ)
  have hsurj : Function.Surjective A :=
    LinearMap.injective_iff_surjective.1 (show Function.Injective (A : E →ₗ[ℝ] E) from hinj)
  set Ainv : E → E := Function.surjInv hsurj
  have hAAinv : ∀ w, A (Ainv w) = w := Function.surjInv_eq hsurj
  -- mean-value inequality for the nonlinear part `N = Φ - A`
  have hdiff : DifferentiableOn ℝ Φ (closedBall 0 r) :=
    R.retained_contDiffOn.differentiableOn one_ne_zero
  have hN : ∀ l ∈ closedBall (0 : E) r, ∀ l' ∈ closedBall (0 : E) r,
      ‖(Φ l - A l) - (Φ l' - A l')‖ ≤ γ / 2 * ‖l - l'‖ := by
    intro l hl l' hl'
    have := (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun x => Φ x - A x) (f' := fun x => fderivWithin ℝ Φ (closedBall 0 r) x - A)
      (fun x hx => ((hdiff x hx).hasFDerivWithinAt).sub A.hasFDerivWithinAt)
      hmargin hl' hl
    simpa using this
  -- the frozen-inverse map
  set T : E → E := fun l => l - Ainv (Φ l)
  have hAT : ∀ l, A (T l) = -((Φ l - A l) - (Φ 0 - A 0)) - Φ 0 := by
    intro l
    simp only [T, map_sub, hAAinv, map_zero]
    abel
  have hTlip : ∀ l ∈ closedBall (0 : E) r, ∀ l' ∈ closedBall (0 : E) r,
      ‖T l - T l'‖ ≤ 1 / 2 * ‖l - l'‖ := by
    intro l hl l' hl'
    have h1 : A (T l - T l') = -((Φ l - A l) - (Φ l' - A l')) := by
      rw [map_sub, hAT, hAT]; abel
    have h2 := hA (T l - T l')
    rw [h1, norm_neg] at h2
    have h3 := h2.trans (hN l hl l' hl')
    have : γ * ‖T l - T l'‖ ≤ γ * (1 / 2 * ‖l - l'‖) := by linarith
    exact le_of_mul_le_mul_left this hγ
  have hTmaps : ∀ l ∈ closedBall (0 : E) ρ, T l ∈ closedBall (0 : E) ρ := by
    intro l hl
    rw [mem_closedBall_zero_iff] at hl ⊢
    have h2 := hA (T l)
    rw [hAT] at h2
    have h0 : (0 : E) ∈ closedBall (0 : E) r := hball (mem_closedBall_self hρ)
    have h3 : ‖-((Φ l - A l) - (Φ 0 - A 0)) - Φ 0‖ ≤ γ / 2 * ‖l‖ + β := by
      calc ‖-((Φ l - A l) - (Φ 0 - A 0)) - Φ 0‖
          ≤ ‖-((Φ l - A l) - (Φ 0 - A 0))‖ + ‖Φ 0‖ := norm_sub_le _ _
        _ ≤ γ / 2 * ‖l - 0‖ + β := by
            rw [norm_neg]
            exact add_le_add (hN l (hball (mem_closedBall_zero_iff.2 hl)) 0 h0) hres
        _ = γ / 2 * ‖l‖ + β := by rw [sub_zero]
    have h4 : γ * ‖T l‖ ≤ γ * ρ := by
      have : γ * ρ = 2 * β := by rw [hρdef]; field_simp
      nlinarith
    exact le_of_mul_le_mul_left h4 hγ
  -- fixed points of `T` are exactly zeros of `Φ`
  have hfix : ∀ l, T l = l ↔ Φ l = 0 := by
    intro l
    simp only [T, sub_eq_self]
    constructor
    · intro h
      rw [← hAAinv (Φ l), h, map_zero]
    · intro h
      apply hinj
      rw [hAAinv, h, map_zero]
  -- uniqueness of zeros in the ball
  have huniq : ∀ l ∈ closedBall (0 : E) ρ, ∀ l' ∈ closedBall (0 : E) ρ,
      Φ l = 0 → Φ l' = 0 → l = l' := by
    intro l hl l' hl' h h'
    have h1 := hTlip l (hball hl) l' (hball hl')
    rw [(hfix l).2 h, (hfix l').2 h'] at h1
    have : ‖l - l'‖ = 0 := by linarith [norm_nonneg (l - l')]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  -- existence by Banach's fixed-point theorem on the closed ball
  set S := closedBall (0 : E) ρ
  have : CompleteSpace S := isClosed_closedBall.completeSpace_coe
  have : Nonempty S := ⟨⟨0, mem_closedBall_self hρ⟩⟩
  let f : S → S := fun l => ⟨T l, hTmaps l l.2⟩
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num), ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have := hTlip x (hball x.2) y (hball y.2)
    simpa using this
  set l₀ := ContractingWith.fixedPoint f hf
  have hl₀ : T l₀ = l₀ :=
    congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt (f := f) hf)
  refine ⟨⟨(l₀ : E), ⟨l₀.2, (hfix _).1 hl₀⟩,
    fun l hl => huniq l hl.1 _ l₀.2 hl.2 ((hfix _).1 hl₀)⟩, fun l hl hzero => ⟨?_, ?_⟩⟩
  · rw [R.factorization l (hball hl)]
    change R.embed (Φ l) = 0
    rw [hzero, map_zero]
  · have h0 : (0 : E) ∈ closedBall (0 : E) r := hball (mem_closedBall_self hρ)
    have := R.lipschitz l (hball hl) 0 h0
    rw [R.basepoint, sub_zero] at this
    calc ‖R.corr l - x0‖ ≤ B * ‖l‖ := this
      _ ≤ B * ρ := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hl) hB
      _ = 2 * B * γ⁻¹ * β := by rw [hρdef]; ring

/-- `prop:initial-constraint-retraction`, literal form: with
`A_h := D_λΦ_h(x_h, 0)` (`eq:constraint-linear-margin`, `σ_min(A_h) ≥ γ_*`),
the margin `eq:constraint-derivative-margin` and the small residual
`eq:constraint-small-residual`, the reduced exact map has a unique zero in the
closed ball of radius `2γ_*⁻¹β_h`, and the corrected datum belongs to the
exact constraint set and satisfies `eq:initial-data-retraction`. -/
theorem initialConstraintRetraction_derivAtZero {Ck : X → Y} {x0 : X} {m : ℕ} {r B : ℝ}
    (R : ExactInitialConstraintReduction Ck x0 m r B) {γ β : ℝ} (hγ : 0 < γ)
    (hA : ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ R.retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
      ‖fderivWithin ℝ R.retained (closedBall 0 r) l -
        fderivWithin ℝ R.retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hres : ‖R.retained 0‖ ≤ β) (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B) :
    (∃! l, l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * β) ∧ R.retained l = 0) ∧
      ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) (2 * γ⁻¹ * β), R.retained l = 0 →
        Ck (R.corr l) = 0 ∧ ‖R.corr l - x0‖ ≤ 2 * B * γ⁻¹ * β :=
  initialConstraintRetraction R _ hγ hA hmargin hres hrad hB

end InitialConstraintRetraction

end RenewalGeometry
