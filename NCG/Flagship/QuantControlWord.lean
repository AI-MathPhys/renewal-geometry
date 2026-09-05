/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Quantitative exact finite-word synthesis
  (`thm:quantitative-control-word-master`, flagship manuscript)

Three layers, matching the manuscript proof:

* the quantitative inverse-function/contraction step
  (`quantitative_local_surjectivity`): if the chart map `f` has
  derivative `f'` with `f' 0 = L`, least singular value
  `σ = ‖L⁻¹‖⁻¹`, and Hessian bound `M` on the `ρ`-ball with
  `ρM ≤ σ/2`, then the image of the `ρ`-ball contains the ball of
  radius `r_loc = σρ/4` around `f 0`; proved through
  `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`
  (Banach/Newton iteration) after two mean-value reductions;
* the geodesic-partition filling step (`ball_filling`): with the
  increment-splitting property of a bi-invariant metric, every
  target within `K·r` of the identity is a product of exactly `K`
  elements of the `r`-ball;
* the boxed primitive length count
  (`quantitative_control_word`): every target within the diameter
  `D_G` is an exact word of primitive length at most
  `K_glob · Σ_ν (2ℓ(w_ν) + 1)`, `K_glob = ⌈D_G/r_loc⌉`.

Two standard inputs enter as displayed hypotheses (disclosed): the
increment-splitting property of a minimizing geodesic (`hsplit`),
and the chart realization of each `r_loc`-ball element as a local
word of `d` conjugated pulses `w_ν e^{t_ν A} w_ν⁻¹`, each of
primitive length `2ℓ(w_ν) + 1` (`hlocal`; this is the transport of
the local surjectivity statement through the logarithm chart).
-/

open Metric Set
open scoped NNReal

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Mean-value reduction: a Hessian bound on the convex ball makes
the derivative Lipschitz. -/
theorem deriv_lipschitz_of_hessian_bound
    (f' : E → E →L[ℝ] E) (f'' : E → E →L[ℝ] E →L[ℝ] E) (ρ M : ℝ)
    (hd2 : ∀ x ∈ closedBall (0 : E) ρ,
      HasFDerivWithinAt f' (f'' x) (closedBall (0 : E) ρ) x)
    (hM : ∀ x ∈ closedBall (0 : E) ρ, ‖f'' x‖ ≤ M)
    {x y : E} (hx : x ∈ closedBall (0 : E) ρ)
    (hy : y ∈ closedBall (0 : E) ρ) :
    ‖f' y - f' x‖ ≤ M * ‖y - x‖ :=
  (convex_closedBall (0 : E) ρ)
    |>.norm_image_sub_le_of_norm_hasFDerivWithin_le hd2 hM hx hy

omit [CompleteSpace E] in
/-- Mean-value reduction: a Lipschitz derivative near `L` gives the
linear-approximation estimate. -/
theorem approximates_of_deriv_bound
    (f : E → E) (f' : E → E →L[ℝ] E) (L : E →L[ℝ] E) (ρ κ : ℝ)
    (hd1 : ∀ x ∈ closedBall (0 : E) ρ,
      HasFDerivWithinAt f (f' x) (closedBall (0 : E) ρ) x)
    (hκ : ∀ x ∈ closedBall (0 : E) ρ, ‖f' x - L‖ ≤ κ)
    {x y : E} (hx : x ∈ closedBall (0 : E) ρ)
    (hy : y ∈ closedBall (0 : E) ρ) :
    ‖f x - f y - L (x - y)‖ ≤ κ * ‖x - y‖ :=
  (convex_closedBall (0 : E) ρ)
    |>.norm_image_sub_le_of_norm_hasFDerivWithin_le' hd1 hκ hy hx

/-- The quantitative inverse-function step: under the manuscript
hypothesis `ρ M ≤ σ/2`, the image of the `ρ`-ball contains the
ball of radius `r_loc = σρ/4` around `f 0`. -/
theorem quantitative_local_surjectivity
    (f : E → E) (f' : E → E →L[ℝ] E)
    (f'' : E → E →L[ℝ] E →L[ℝ] E)
    (L : E ≃L[ℝ] E) (σ ρ M : ℝ) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hL0 : (L : E →L[ℝ] E) = f' 0)
    (hLinv : ‖(L.symm : E →L[ℝ] E)‖ ≤ σ⁻¹)
    (hd1 : ∀ x ∈ closedBall (0 : E) ρ,
      HasFDerivWithinAt f (f' x) (closedBall (0 : E) ρ) x)
    (hd2 : ∀ x ∈ closedBall (0 : E) ρ,
      HasFDerivWithinAt f' (f'' x) (closedBall (0 : E) ρ) x)
    (hM : ∀ x ∈ closedBall (0 : E) ρ, ‖f'' x‖ ≤ M)
    (hsmall : ρ * M ≤ σ / 2) :
    ∀ y ∈ closedBall (f 0) (σ * ρ / 4),
      ∃ x ∈ closedBall (0 : E) ρ, f x = y := by
  intro y hy
  by_cases hns : ‖(L.symm : E →L[ℝ] E)‖ = 0
  · -- degenerate case: the space is trivial
    have hsub : ∀ z : E, z = 0 := by
      intro z
      have h0 : (L.symm : E →L[ℝ] E) = 0 :=
        norm_eq_zero.mp hns
      have h1 : L ((L.symm : E →L[ℝ] E) z) = z :=
        L.apply_symm_apply z
      rw [h0] at h1
      simpa using h1.symm
    refine ⟨0, mem_closedBall_self hρ.le, ?_⟩
    rw [hsub (f 0), hsub y]
  · have hpos : 0 < ‖(L.symm : E →L[ℝ] E)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hns)
    have hinvσ : σ ≤ ‖(L.symm : E →L[ℝ] E)‖⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_left hLinv hσ.le,
        inv_mul_cancel₀ (ne_of_gt hpos),
        mul_inv_cancel₀ (ne_of_gt hσ)]
    have hb0 : (0 : E) ∈ closedBall (0 : E) ρ :=
      mem_closedBall_self hρ.le
    have hM0 : 0 ≤ M :=
      le_trans (norm_nonneg (f'' 0)) (hM 0 hb0)
    -- derivative stays within σ/2 of L on the ball
    have hκ : ∀ x ∈ closedBall (0 : E) ρ,
        ‖f' x - (L : E →L[ℝ] E)‖ ≤ σ / 2 := by
      intro x hx
      have h1 : ‖f' x - f' 0‖ ≤ M * ‖x - 0‖ :=
        deriv_lipschitz_of_hessian_bound f' f'' ρ M hd2 hM hb0 hx
      have h2 : ‖x - 0‖ ≤ ρ := by
        simpa [dist_eq_norm] using mem_closedBall.mp hx
      calc ‖f' x - (L : E →L[ℝ] E)‖
          = ‖f' x - f' 0‖ := by rw [hL0]
        _ ≤ M * ‖x - 0‖ := h1
        _ ≤ M * ρ := mul_le_mul_of_nonneg_left h2 hM0
        _ ≤ σ / 2 := by linarith
    have happrox : ApproximatesLinearOn f (L : E →L[ℝ] E)
        (closedBall (0 : E) ρ) (Real.toNNReal (σ / 2)) := by
      intro x hx z hz
      rw [Real.coe_toNNReal _ (by positivity)]
      exact approximates_of_deriv_bound f f' (L : E →L[ℝ] E)
        ρ (σ / 2) hd1 hκ hx hz
    have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse
      L.toNonlinearRightInverse hρ.le (subset_refl _)
    have hnn : ((L.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)
        = ‖(L.symm : E →L[ℝ] E)‖ := rfl
    have hrad : σ * ρ / 4
        ≤ (((L.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹
            - (Real.toNNReal (σ / 2) : ℝ)) * ρ := by
      rw [hnn, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ σ / 2)]
      nlinarith [hinvσ, hρ.le]
    have hy' : y ∈ closedBall (f 0)
        ((((L.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹
          - (Real.toNNReal (σ / 2) : ℝ)) * ρ) :=
      closedBall_subset_closedBall hrad hy
    obtain ⟨x, hx, hfx⟩ := hsurj hy'
    exact ⟨x, hx, hfx⟩

/-- Geodesic-partition filling: with the increment-splitting
property (`hsplit`, disclosed), every target within `K·r` of the
identity is a product of exactly `K` elements of the `r`-ball. -/
theorem ball_filling {G : Type*} [Group G] [MetricSpace G] (r : ℝ)
    (hsplit : ∀ (n : ℕ) (g : G), dist 1 g ≤ (n + 1 : ℕ) * r →
      ∃ h : G, dist 1 h ≤ r ∧ dist 1 (h⁻¹ * g) ≤ n * r) :
    ∀ (K : ℕ) (g : G), dist 1 g ≤ K * r →
      ∃ l : List G, l.length = K ∧ (∀ h ∈ l, dist 1 h ≤ r)
        ∧ l.prod = g := by
  intro K
  induction K with
  | zero =>
      intro g hg
      refine ⟨[], rfl, by simp, ?_⟩
      have h0 : dist 1 g ≤ 0 := by simpa using hg
      have h1 : dist (1 : G) g = 0 := le_antisymm h0 dist_nonneg
      rw [List.prod_nil]
      exact dist_eq_zero.mp h1
  | succ n ih =>
      intro g hg
      obtain ⟨h, hh, hrest⟩ := hsplit n g (by exact_mod_cast hg)
      obtain ⟨l, hlen, hmem, hprod⟩ := ih (h⁻¹ * g) hrest
      refine ⟨h :: l, by simp [hlen], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hh
        · exact hmem x hx'
      · rw [List.prod_cons, hprod]
        exact mul_inv_cancel_left h g

/-- Concatenation of local words: if every element satisfying `P`
is a word of primitive length at most `B`, a product of `K` such
elements is a word of primitive length at most `K·B`. -/
theorem word_concat {G α : Type*} [Group G]
    (wordProd : List α → G) (hword_nil : wordProd [] = 1)
    (hword_mul : ∀ u v,
      wordProd (u ++ v) = wordProd u * wordProd v)
    (B : ℕ) (P : G → Prop)
    (hloc : ∀ h : G, P h →
      ∃ w : List α, wordProd w = h ∧ w.length ≤ B) :
    ∀ l : List G, (∀ h ∈ l, P h) →
      ∃ w : List α, wordProd w = l.prod
        ∧ w.length ≤ l.length * B := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨[], by simp [hword_nil], by simp⟩
  | cons h tl ih =>
      intro hall
      obtain ⟨w1, hw1, hl1⟩ := hloc h (hall h (by simp))
      obtain ⟨w2, hw2, hl2⟩ :=
        ih (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx)))
      refine ⟨w1 ++ w2, ?_, ?_⟩
      · rw [hword_mul, hw1, hw2, List.prod_cons]
      · rw [List.length_append, List.length_cons]
        calc w1.length + w2.length
            ≤ B + tl.length * B := Nat.add_le_add hl1 hl2
          _ = (tl.length + 1) * B := by ring

/-- `thm:quantitative-control-word-master`, boxed global length
bound: every target within the diameter `D_G` is an exact word of
primitive length at most `⌈D_G/r_loc⌉ · Σ_ν (2ℓ(w_ν)+1)` with
`r_loc = σρ/4`. -/
theorem quantitative_control_word {G α : Type*} [Group G]
    [MetricSpace G] {d : ℕ} (ℓ : Fin d → ℕ)
    (wordProd : List α → G) (hword_nil : wordProd [] = 1)
    (hword_mul : ∀ u v,
      wordProd (u ++ v) = wordProd u * wordProd v)
    (σ ρ DG : ℝ) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hsplit : ∀ (n : ℕ) (g : G),
      dist 1 g ≤ (n + 1 : ℕ) * (σ * ρ / 4) →
      ∃ h : G, dist 1 h ≤ σ * ρ / 4
        ∧ dist 1 (h⁻¹ * g) ≤ n * (σ * ρ / 4))
    (hlocal : ∀ h : G, dist 1 h ≤ σ * ρ / 4 →
      ∃ w : List α, wordProd w = h
        ∧ w.length ≤ ∑ ν, (2 * ℓ ν + 1))
    (g : G) (hg : dist 1 g ≤ DG) :
    ∃ w : List α, wordProd w = g
      ∧ w.length ≤ ⌈DG / (σ * ρ / 4)⌉₊ * ∑ ν, (2 * ℓ ν + 1) := by
  classical
  have hrpos : 0 < σ * ρ / 4 := by positivity
  have hcover : dist 1 g ≤ (⌈DG / (σ * ρ / 4)⌉₊ : ℝ)
      * (σ * ρ / 4) := by
    calc dist 1 g ≤ DG := hg
      _ = DG / (σ * ρ / 4) * (σ * ρ / 4) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hrpos)]
      _ ≤ (⌈DG / (σ * ρ / 4)⌉₊ : ℝ) * (σ * ρ / 4) :=
          mul_le_mul_of_nonneg_right
            (Nat.le_ceil _) hrpos.le
  obtain ⟨l, hlen, hmem, hprod⟩ := ball_filling (σ * ρ / 4)
    hsplit ⌈DG / (σ * ρ / 4)⌉₊ g hcover
  obtain ⟨w, hwprod, hwlen⟩ := word_concat wordProd hword_nil
    hword_mul (∑ ν, (2 * ℓ ν + 1))
    (fun h => dist 1 h ≤ σ * ρ / 4) hlocal l hmem
  rw [hprod] at hwprod
  rw [hlen] at hwlen
  exact ⟨w, hwprod, hwlen⟩

end NCG
