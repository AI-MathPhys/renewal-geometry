/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A sufficient Euclidean defect-removal mechanism (`prop:monotonicity`, Einstein–SM
action closure)

Abstract monotone-operator argument of the proposition.  `V` is a real normed space
(the Hilbert space `V ↪ L⁴` of the paper; only its norm enters), `n₄` is the second
(`L⁴`) norm, and the gauge-fixed Euclidean Higgs operators are maps
`A n : V → V'` into the strong dual satisfying the strong monotonicity inequality

  `c₁ ‖u - v‖² + c₂ n₄(u - v)⁴ ≤ ⟨A n u - A n v, u - v⟩`,   `c₁, c₂ > 0`.

If `H n ⇀ H` weakly in `V`, `A n (H n) = J n → J` and `A n H → J` strongly in `V'`, then
`H n → H` in `V` and `n₄(H n - H) → 0` (`tendsto_of_monotone`), i.e. `H n → H` in
`V ∩ L⁴`.  Weak convergence is rendered as convergence of every continuous linear
functional; the norm boundedness of the weakly convergent sequence is derived from the
Banach–Steinhaus theorem through the isometric double-dual embedding
(`norm_bounded_of_weak_tendsto`).  The pairing `⟨J n - A n H, H n - H⟩` tends to zero as
a strong-dual times bounded product (`pairing_tendsto_zero`), and each nonnegative term
on the left of the monotonicity inequality is squeezed to zero.

The final sentence of the proposition ("if `V` controls the covariant `H¹` norm, both
Higgs defects vanish") is the interpretation of strong `V ∩ L⁴` convergence in terms of
the defect measures of the paper and is not formalised here.
-/

open Filter Topology

namespace RenewalGeometry.MonotoneDefectRemoval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A weakly convergent sequence in a normed space is norm bounded (Banach–Steinhaus
through the double-dual embedding). -/
theorem norm_bounded_of_weak_tendsto (Hs : ℕ → V) (H : V)
    (hweak : ∀ φ : StrongDual ℝ V, Tendsto (fun n => φ (Hs n)) atTop (𝓝 (φ H))) :
    ∃ C : ℝ, ∀ n, ‖Hs n‖ ≤ C := by
  have hpt : ∀ φ : StrongDual ℝ V, ∃ C, ∀ n,
      ‖(NormedSpace.inclusionInDoubleDual ℝ V (Hs n)) φ‖ ≤ C := by
    intro φ
    obtain ⟨C, hC⟩ := (hweak φ).norm.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus
    (g := fun n => NormedSpace.inclusionInDoubleDual ℝ V (Hs n)) hpt
  refine ⟨C', fun n => ?_⟩
  rw [← (NormedSpace.inclusionInDoubleDualLi ℝ (E := V)).norm_map (Hs n)]
  exact hC' n

/-- A nonnegative real sequence whose `k`-th powers tend to zero tends to zero. -/
theorem tendsto_zero_of_pow_tendsto_zero {ι : Type*} {l : Filter ι} (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) {k : ℕ} (hk : k ≠ 0)
    (h : Tendsto (fun i => x i ^ k) l (𝓝 0)) : Tendsto x l (𝓝 0) := by
  have h1 : Tendsto (fun i => (x i ^ k) ^ ((k : ℝ)⁻¹)) l (𝓝 ((0 : ℝ) ^ ((k : ℝ)⁻¹))) :=
    h.rpow_const (Or.inr (by positivity))
  have hk' : ((k : ℝ)⁻¹) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    exact inv_ne_zero this
  rw [Real.zero_rpow hk'] at h1
  refine h1.congr fun i => ?_
  exact Real.pow_rpow_inv_natCast (hx i) hk

/-- The pairing `⟨A n (H n) - A n H, H n - H⟩` tends to zero when
`A n (H n) → J`, `A n H → J` strongly in `V'` and `H n` is norm bounded. -/
theorem pairing_tendsto_zero (A : ℕ → V → StrongDual ℝ V) (Hs : ℕ → V) (H : V)
    (J : StrongDual ℝ V) (C : ℝ) (hbdd : ∀ n, ‖Hs n‖ ≤ C)
    (hJ : Tendsto (fun n => A n (Hs n)) atTop (𝓝 J))
    (hAH : Tendsto (fun n => A n H) atTop (𝓝 J)) :
    Tendsto (fun n => (A n (Hs n) - A n H) (Hs n - H)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n => ‖A n (Hs n) - A n H‖) atTop (𝓝 0) := by
    simpa using (hJ.sub hAH).norm
  have hmajor : Tendsto (fun n => ‖A n (Hs n) - A n H‖ * (C + ‖H‖)) atTop (𝓝 0) := by
    simpa using hdiff.mul_const (C + ‖H‖)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmajor
  calc ‖(A n (Hs n) - A n H) (Hs n - H)‖
      ≤ ‖A n (Hs n) - A n H‖ * ‖Hs n - H‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A n (Hs n) - A n H‖ * (C + ‖H‖) := by
        gcongr
        calc ‖Hs n - H‖ ≤ ‖Hs n‖ + ‖H‖ := norm_sub_le _ _
          _ ≤ C + ‖H‖ := by gcongr; exact hbdd n

/-- **`prop:monotonicity`.**  Strong monotonicity of the operators `A n`, weak
convergence `H n ⇀ H`, and strong dual convergence `A n (H n) → J`, `A n H → J` force
`H n → H` in `V` and `n₄(H n - H) → 0`. -/
theorem tendsto_of_monotone (A : ℕ → V → StrongDual ℝ V) (n₄ : V → ℝ)
    (hn₄ : ∀ u, 0 ≤ n₄ u) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hmono : ∀ n u v, c₁ * ‖u - v‖ ^ 2 + c₂ * n₄ (u - v) ^ 4 ≤ (A n u - A n v) (u - v))
    (Hs : ℕ → V) (H : V) (J : StrongDual ℝ V)
    (hweak : ∀ φ : StrongDual ℝ V, Tendsto (fun n => φ (Hs n)) atTop (𝓝 (φ H)))
    (hJ : Tendsto (fun n => A n (Hs n)) atTop (𝓝 J))
    (hAH : Tendsto (fun n => A n H) atTop (𝓝 J)) :
    Tendsto Hs atTop (𝓝 H) ∧ Tendsto (fun n => n₄ (Hs n - H)) atTop (𝓝 0) := by
  obtain ⟨C, hbdd⟩ := norm_bounded_of_weak_tendsto Hs H hweak
  have hpair := pairing_tendsto_zero A Hs H J C hbdd hJ hAH
  -- each nonnegative term of the monotonicity inequality is squeezed to zero
  have hsq : Tendsto (fun n => c₁ * ‖Hs n - H‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hpair
    have h := hmono n (Hs n) H
    have : 0 ≤ c₂ * n₄ (Hs n - H) ^ 4 := by have := hn₄ (Hs n - H); positivity
    linarith
  have hquart : Tendsto (fun n => c₂ * n₄ (Hs n - H) ^ 4) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by have := hn₄ (Hs n - H); positivity) (fun n => ?_) hpair
    have h := hmono n (Hs n) H
    have : 0 ≤ c₁ * ‖Hs n - H‖ ^ 2 := by positivity
    linarith
  have hsq' : Tendsto (fun n => ‖Hs n - H‖ ^ 2) atTop (𝓝 0) := by
    have := hsq.const_mul (1 / c₁)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    field_simp
  have hquart' : Tendsto (fun n => n₄ (Hs n - H) ^ 4) atTop (𝓝 0) := by
    have := hquart.const_mul (1 / c₂)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    field_simp
  constructor
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact tendsto_zero_of_pow_tendsto_zero (fun n => ‖Hs n - H‖) (fun n => norm_nonneg _)
      (by norm_num) hsq'
  · exact tendsto_zero_of_pow_tendsto_zero (fun n => n₄ (Hs n - H)) (fun n => hn₄ _)
      (by norm_num) hquart'

end RenewalGeometry.MonotoneDefectRemoval
