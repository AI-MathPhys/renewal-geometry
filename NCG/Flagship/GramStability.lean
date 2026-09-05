/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Gram-to-source polar stability
  (`thm:Gram-source-stability-master`, flagship manuscript)

For normalized linearly independent target vectors `η_a` (a basis
`b` of their span) with Gram floor `G₀ ⪰ gI` and measured vectors
`ξ_a` with `‖G - G₀‖ ≤ ε_G < g`:

* the synthesis frame inequality
  `(1 - ε_G/g)I ⪯ S*S ⪯ (1 + ε_G/g)I` in quadratic-form
  language (`gram_frame_bounds`);
* the boxed polar bound: a unitary `U` with
  `‖ξ_a - Uη_a‖ ≤ 1 - √(1 - ε_G/g)` (`gram_source_stability`),
  built from the spectral theorem for `S*S`: the polar unitary is
  `U = S|S|⁻¹` realized on the orthonormal eigenbasis, and the
  displacement is controlled by `max|√μ - 1|` over the spectrum
  `μ ∈ [1 - r, 1 + r]` together with
  `1 - √(1-r) ≥ √(1+r) - 1`.

The operator-norm hypothesis `‖G - G₀‖ ≤ ε_G` enters through its
quadratic-form consequence `|c*(G - G₀)c| ≤ ε_G‖c‖²` (a weaker
hypothesis, hence a stronger theorem), and the Gram floor through
`g‖c‖² ≤ ‖Σc_aη_a‖²`.
-/

open Finset Module

namespace NCG

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

omit [FiniteDimensional ℂ E] in
/-- The synthesis frame inequality from the Gram data:
`(1 - ε_G/g)‖v‖² ≤ ‖Sv‖² ≤ (1 + ε_G/g)‖v‖²`. -/
theorem gram_frame_bounds (b : Basis ι ℂ E)
    (ξ : ι → E) (g εG : ℝ) (hg : 0 < g) (hεG : 0 ≤ εG)
    (hG0 : ∀ c : ι → ℂ,
      g * ∑ a, ‖c a‖ ^ 2 ≤ ‖∑ a, c a • b a‖ ^ 2)
    (hGd : ∀ c : ι → ℂ,
      |‖∑ a, c a • ξ a‖ ^ 2 - ‖∑ a, c a • b a‖ ^ 2|
        ≤ εG * ∑ a, ‖c a‖ ^ 2) (v : E) :
    (1 - εG / g) * ‖v‖ ^ 2 ≤ ‖b.constr ℂ ξ v‖ ^ 2
      ∧ ‖b.constr ℂ ξ v‖ ^ 2 ≤ (1 + εG / g) * ‖v‖ ^ 2 := by
  set c : ι → ℂ := fun a => b.repr v a with hc
  have hv : v = ∑ a, c a • b a := by
    conv_lhs => rw [← b.sum_repr v]
  have hS : b.constr ℂ ξ v = ∑ a, c a • ξ a := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Basis.constr_basis]
  have h1 := hG0 c
  have h2 := hGd c
  rw [← hv] at h1 h2
  rw [hS]
  have hcv : ∑ a, ‖c a‖ ^ 2 ≤ ‖v‖ ^ 2 / g := by
    rw [le_div_iff₀ hg, mul_comm]
    exact h1
  have habs := abs_le.mp h2
  have hcnn : (0 : ℝ) ≤ ∑ a, ‖c a‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have h3 : εG * (‖v‖ ^ 2 / g) = εG / g * ‖v‖ ^ 2 := by
    ring
  have h4 := mul_le_mul_of_nonneg_left hcv hεG
  constructor
  · nlinarith [habs.1]
  · nlinarith [habs.2]

omit [Fintype ι] in
/-- `thm:Gram-source-stability-master`, boxed polar bound: a
unitary `U` with `‖ξ_a - Uη_a‖ ≤ 1 - √(1 - ε_G/g)`, from the
spectral theorem for `S*S`. -/
theorem gram_source_stability [Finite ι] (b : Basis ι ℂ E)
    (ξ : ι → E) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbnorm : ∀ a, ‖b a‖ = 1)
    (hlow : ∀ v : E,
      (1 - r) * ‖v‖ ^ 2 ≤ ‖b.constr ℂ ξ v‖ ^ 2)
    (hhigh : ∀ v : E,
      ‖b.constr ℂ ξ v‖ ^ 2 ≤ (1 + r) * ‖v‖ ^ 2) :
    ∃ U : E →ₗ[ℂ] E,
      (∀ v w : E, ⟪U v, U w⟫ = ⟪v, w⟫)
      ∧ ∀ a, ‖ξ a - U (b a)‖ ≤ 1 - Real.sqrt (1 - r) := by
  classical
  cases nonempty_fintype ι
  set S : E →ₗ[ℂ] E := b.constr ℂ ξ with hSdef
  set A : E →ₗ[ℂ] E := LinearMap.adjoint S ∘ₗ S with hAdef
  have hA : A.IsSymmetric := by
    intro v w
    rw [hAdef, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.adjoint_inner_left,
      LinearMap.adjoint_inner_right]
  have hD : Module.finrank ℂ E = Fintype.card ι :=
    Module.finrank_eq_card_basis b
  set u := hA.eigenvectorBasis hD with hu
  set μ := hA.eigenvalues hD with hμdef
  have hApply : ∀ i, A (u i) = (μ i : ℂ) • u i := fun i =>
    hA.apply_eigenvectorBasis hD i
  have hone : ∀ i, ‖u i‖ = 1 := fun i => u.orthonormal.1 i
  have hite : ∀ i j, ⟪u i, u j⟫ = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp u.orthonormal i j
  have hSS : ∀ i j,
      ⟪S (u i), S (u j)⟫ = if i = j then (μ j : ℂ) else 0 := by
    intro i j
    have h1 : ⟪S (u i), S (u j)⟫ = ⟪u i, A (u j)⟫ := by
      rw [hAdef, LinearMap.comp_apply,
        LinearMap.adjoint_inner_right]
    rw [h1, hApply j, inner_smul_right, hite]
    by_cases hij : i = j <;> simp [hij]
  have hμval : ∀ i, ‖S (u i)‖ ^ 2 = μ i := by
    intro i
    have h1 := hSS i i
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (S (u i))
    rw [h1, if_pos rfl] at h2
    have h3 := congrArg Complex.re h2.symm
    simpa [← Complex.ofReal_pow] using h3
  have hμlow : ∀ i, 1 - r ≤ μ i := by
    intro i
    have := hlow (u i)
    rw [hone i] at this
    rw [← hμval i]
    simpa using this
  have hμhigh : ∀ i, μ i ≤ 1 + r := by
    intro i
    have := hhigh (u i)
    rw [hone i] at this
    rw [← hμval i]
    simpa using this
  have hμpos : ∀ i, 0 < μ i := fun i =>
    lt_of_lt_of_le (by linarith) (hμlow i)
  set t : Fin (Fintype.card ι) → ℝ := fun i =>
    (Real.sqrt (μ i))⁻¹ with ht
  set U : E →ₗ[ℂ] E := u.toBasis.constr ℂ
    (fun i => ((t i : ℝ) : ℂ) • S (u i)) with hUdef
  have hUu : ∀ i, U (u i) = ((t i : ℝ) : ℂ) • S (u i) := by
    intro i
    have h0 : u i = u.toBasis i :=
      (congrFun u.coe_toBasis i).symm
    conv_lhs => rw [h0]
    rw [hUdef, Basis.constr_basis]
  have htmu : ∀ i, (t i) ^ 2 * μ i = 1 := by
    intro i
    rw [ht]
    have h1 : Real.sqrt (μ i) ^ 2 = μ i :=
      Real.sq_sqrt (hμpos i).le
    have h2 : Real.sqrt (μ i) ≠ 0 := by
      have := Real.sqrt_pos.mpr (hμpos i)
      linarith
    field_simp
    linarith [h1]
  -- expansion of images
  have hexpand : ∀ (v : E) (T : E →ₗ[ℂ] E),
      T v = ∑ i, u.repr v i • T (u i) := by
    intro v T
    conv_lhs => rw [← u.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  -- inner products of expansions through hSS
  have hinner_ST : ∀ (e f : Fin (Fintype.card ι) → ℂ),
      ⟪∑ i, e i • S (u i), ∑ j, f j • S (u j)⟫
      = ∑ i, starRingEnd ℂ (e i) * f i * (μ i : ℂ) := by
    intro e f
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    rw [Finset.sum_eq_single i
      (fun j _ hj => by
        rw [inner_smul_left, inner_smul_right, hSS]
        simp [Ne.symm hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [inner_smul_left, inner_smul_right, hSS, if_pos rfl]
    ring
  have hparseval : ∀ v w : E,
      ⟪v, w⟫ = ∑ i, starRingEnd ℂ (u.repr v i) * u.repr w i := by
    intro v w
    conv_lhs => rw [← u.sum_repr v, ← u.sum_repr w]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    rw [Finset.sum_eq_single i
      (fun j _ hj => by
        rw [inner_smul_left, inner_smul_right, hite]
        simp [Ne.symm hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [inner_smul_left, inner_smul_right, hite, if_pos rfl]
    ring
  have hUv : ∀ v : E, U v
      = ∑ i, (u.repr v i * ((t i : ℝ) : ℂ)) • S (u i) := by
    intro v
    rw [hexpand v U]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hUu, smul_smul]
  refine ⟨U, ?_, ?_⟩
  · intro v w
    rw [hUv v, hUv w, hinner_ST, hparseval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have h9 : (((t i : ℝ) : ℂ)) * (((t i : ℝ) : ℂ))
        * ((μ i : ℝ) : ℂ) = 1 := by
      have h10 := htmu i
      have h11 : (((t i : ℝ) : ℂ)) ^ 2 * ((μ i : ℝ) : ℂ)
          = 1 := by
        exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h10
      linear_combination h11
    calc starRingEnd ℂ (u.repr v i) * ((t i : ℝ) : ℂ)
          * (u.repr w i * ((t i : ℝ) : ℂ)) * ((μ i : ℝ) : ℂ)
        = starRingEnd ℂ (u.repr v i) * u.repr w i
          * ((((t i : ℝ) : ℂ)) * (((t i : ℝ) : ℂ))
            * ((μ i : ℝ) : ℂ)) := by ring
      _ = starRingEnd ℂ (u.repr v i) * u.repr w i := by
          rw [h9, mul_one]
  · intro a
    have hξa : ξ a = S (b a) := by
      rw [hSdef, Basis.constr_basis]
    rw [hξa]
    -- vectorial displacement bound
    have hdisp : ∀ v : E,
        ‖S v - U v‖ ^ 2
          ≤ (1 - Real.sqrt (1 - r)) ^ 2 * ‖v‖ ^ 2 := by
      intro v
      have hSv : S v - U v = ∑ i,
          (u.repr v i * (1 - ((t i : ℝ) : ℂ))) • S (u i) := by
        rw [hexpand v S, hUv v, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul]
        congr 1
        ring
      have hnorm2 : ‖S v - U v‖ ^ 2
          = ∑ i, ‖u.repr v i‖ ^ 2 * ((1 - t i) ^ 2 * μ i) := by
        have h1 : ((‖S v - U v‖ : ℝ) : ℂ) ^ 2
            = ∑ i, starRingEnd ℂ
                (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
              * (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
              * ((μ i : ℝ) : ℂ) := by
          calc ((‖S v - U v‖ : ℝ) : ℂ) ^ 2
              = ⟪S v - U v, S v - U v⟫ :=
                (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
                  (S v - U v)).symm
            _ = ∑ i, starRingEnd ℂ
                  (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
                * (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
                * ((μ i : ℝ) : ℂ) := by
                rw [hSv]
                exact hinner_ST _ _
        have h2 : ((∑ i, ‖u.repr v i‖ ^ 2
            * ((1 - t i) ^ 2 * μ i) : ℝ) : ℂ)
            = ∑ i, starRingEnd ℂ
                (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
              * (u.repr v i * (1 - ((t i : ℝ) : ℂ)))
              * ((μ i : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_mul, map_sub, map_one,
            Complex.conj_ofReal]
          push_cast
          linear_combination (-((1 - ((t i : ℝ) : ℂ))
              * (1 - ((t i : ℝ) : ℂ)) * ((μ i : ℝ) : ℂ)))
            * Complex.mul_conj' (u.repr v i)
        have h3 := h1.trans h2.symm
        exact_mod_cast h3
      rw [hnorm2]
      have hterm : ∀ i, (1 - t i) ^ 2 * μ i
          = (Real.sqrt (μ i) - 1) ^ 2 := by
        intro i
        rw [ht]
        have h1 : Real.sqrt (μ i) ^ 2 = μ i :=
          Real.sq_sqrt (hμpos i).le
        have h2 : Real.sqrt (μ i) ≠ 0 := by
          have := Real.sqrt_pos.mpr (hμpos i)
          linarith
        field_simp
        nlinarith [h1]
      have hbound : ∀ i, (Real.sqrt (μ i) - 1) ^ 2
          ≤ (1 - Real.sqrt (1 - r)) ^ 2 := by
        intro i
        have h1 : Real.sqrt (1 - r) ≤ Real.sqrt (μ i) :=
          Real.sqrt_le_sqrt (hμlow i)
        have h2 : Real.sqrt (μ i) ≤ Real.sqrt (1 + r) :=
          Real.sqrt_le_sqrt (hμhigh i)
        have h4 : Real.sqrt (1 - r) ^ 2 = 1 - r :=
          Real.sq_sqrt (by linarith)
        have h5 : Real.sqrt (1 + r) ^ 2 = 1 + r :=
          Real.sq_sqrt (by linarith)
        have h3 : Real.sqrt (1 - r) * Real.sqrt (1 + r) ≤ 1 := by
          rw [← Real.sqrt_mul (by linarith)]
          refine Real.sqrt_le_one.mpr ?_
          nlinarith
        have h6 : Real.sqrt (1 - r) + Real.sqrt (1 + r) ≤ 2 := by
          nlinarith [Real.sqrt_nonneg (1 - r),
            Real.sqrt_nonneg (1 + r)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ)
            ≤ Real.sqrt (μ i) - Real.sqrt (1 - r))
          (by linarith : (0:ℝ)
            ≤ 2 - Real.sqrt (1 - r) - Real.sqrt (μ i))]
      have hpars : ∑ i, ‖u.repr v i‖ ^ 2 = ‖v‖ ^ 2 := by
        have h1 : ((‖v‖ : ℝ) : ℂ) ^ 2
            = ∑ i, starRingEnd ℂ (u.repr v i) * u.repr v i := by
          calc ((‖v‖ : ℝ) : ℂ) ^ 2 = ⟪v, v⟫ :=
              (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v).symm
            _ = _ := hparseval v v
        have h2 : ((∑ i, ‖u.repr v i‖ ^ 2 : ℝ) : ℂ)
            = ∑ i, starRingEnd ℂ (u.repr v i) * u.repr v i := by
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_comm]
          exact (Complex.mul_conj' _).symm
        have h3 := h1.trans h2.symm
        exact_mod_cast h3.symm
      calc ∑ i, ‖u.repr v i‖ ^ 2 * ((1 - t i) ^ 2 * μ i)
          ≤ ∑ i, ‖u.repr v i‖ ^ 2
              * (1 - Real.sqrt (1 - r)) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hterm i]
            exact mul_le_mul_of_nonneg_left (hbound i)
              (sq_nonneg _)
        _ = (1 - Real.sqrt (1 - r)) ^ 2 * ‖v‖ ^ 2 := by
            rw [← Finset.sum_mul, hpars]
            ring
    have h7 := hdisp (b a)
    rw [hbnorm a] at h7
    have h8 : 0 ≤ 1 - Real.sqrt (1 - r) := by
      have := Real.sqrt_le_one.mpr
        (by linarith : (1 : ℝ) - r ≤ 1)
      linarith
    have h9 : ‖S (b a) - U (b a)‖ ^ 2
        ≤ (1 - Real.sqrt (1 - r)) ^ 2 := by
      simpa using h7
    calc ‖S (b a) - U (b a)‖
        = Real.sqrt (‖S (b a) - U (b a)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 - Real.sqrt (1 - r)) ^ 2) :=
          Real.sqrt_le_sqrt h9
      _ = 1 - Real.sqrt (1 - r) := Real.sqrt_sq h8

end NCG
