/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLocalJets
import RenewalGeometry.Analysis.TaylorHermiteResidual
import RenewalGeometry.Analysis.TaylorHermitePrecision

/-!
# The complete Taylor–Hermite residual of the local finite writer
  (`lem:supp-open-hermite-residual`, `eq:supp-open-local-taylor`,
  `eq:supp-open-hermite-correction`, `eq:supp-open-hermite-local-defect`;
  emergent-spacetime manuscript)

* `gridWriter s B`: the law-family writer `𝓕_{B,h} = lawField s B` on
  `𝒳^s_h = (H^{s+1}_h)^{10} × (H^s_h)^{10}` as a second-order writer
  (`TaylorHermiteResidual.Writer`): position space `(H^{s+1}_h)^{10}`, velocity space
  `(H^s_h)^{10}`, `ι` the inclusion and `u` the inverse inequality (identity of arrays), and
  acceleration `V_{B,h}`; `gridWriter_field`: its field is `lawField s B`.
* `gridWriter_bounds`: the inverse-mesh bounds of `lem:supp-open-local-jets` give
  `Writer.Bounds (1/N) A δ` with mesh-independent `A, δ`.
* `open_hermite_residual` (**`lem:supp-open-hermite-residual`**): for `c₋h² ≤ τ ≤ c₊h²` and
  sufficiently fine grids, the endpoint-corrected degree-seven polynomial `Q_X` of the source `X`
  (`Writer.hermiteC`, jets `(q, v, V(X), J(X))` at `0` and `(X₁, V(X₁), J(X₁))` at `τ`) stays in
  the common chart and its defect satisfies `‖f_X‖_{C(I;H^s_h)} ≤ C ε h⁵` and
  `‖∂_t f_X‖_{C(I;H^s_h)} ≤ C ε h³` (hence also in `H^{s-3}_h`).
* `open_hermite_precision` (**`lem:supp-open-hermite-precision`**): for a degree-seven endpoint
  Hermite perturbation `δQ` of `Q_X` with `b_h ≥ max_{e,j≤3} τʲ‖δQ⁽ʲ⁾(eτ)‖_{H^s_h}`:
  `‖δQ⁽ʲ⁾‖_{C(I;H^s_h)} ≤ C_j τ^{-j} b_h`; and if `b_h ≤ c ε τ² h⁵`, the perturbed polynomial stays
  in the chart, the residual and its time derivative change by at most `C τ^{-2} b_h` and
  `C τ^{-3} b_h`, and the bounds `eq:supp-open-hermite-local-defect` are preserved.
-/

open Set Metric Filter Topology
open scoped ContDiff

namespace RenewalGeometry.OpenWriterLocalJets

open OpenWriterEnergyEstimate OpenWriterLifespan PeriodicGridSobolev.GridH IteratedDerivBounds
  TaylorHermiteResidual TwoPointHermite
open PeriodicGridSobolev (GridH invConst invConst_nonneg)

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The inclusion `(H^{s+1}_h)^{10} → (H^s_h)^{10}`. -/
def iotaG (s : ℕ) : (Upper → GridH N (s + 1)) →L[ℝ] (Upper → GridH N s) :=
  ContinuousLinearMap.pi fun κ => (incl (Nat.le_succ s)).comp (ContinuousLinearMap.proj κ)

/-- The identity `(H^s_h)^{10} → (H^{s+1}_h)^{10}` (inverse inequality). -/
def upG (s : ℕ) : (Upper → GridH N s) →L[ℝ] (Upper → GridH N (s + 1)) :=
  ContinuousLinearMap.pi fun κ => (up s).comp (ContinuousLinearMap.proj κ)

/-- **The law-family writer as a second-order writer**. -/
def gridWriter (s : ℕ) (B : Upper → Upper → ℝ) :
    TaylorHermiteResidual.Writer (Upper → GridH N (s + 1)) (Upper → GridH N s) where
  ι := iotaG s
  u := upG s
  V X := (lawField s B X).2
  ι_u y := funext fun κ => GridH.ext fun x => rfl
  u_ι x := funext fun κ => GridH.ext fun x => rfl

theorem gridWriter_field (s : ℕ) (B : Upper → Upper → ℝ) :
    (gridWriter (N := N) s B).field = lawField s B := rfl

theorem norm_iotaG_le (s : ℕ) : ‖iotaG (N := N) s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun κ => ?_
  show ‖incl (Nat.le_succ s) (q κ)‖ ≤ ‖q‖
  refine ((incl (N := N) (Nat.le_succ s)).le_opNorm _).trans ?_
  calc ‖incl (N := N) (Nat.le_succ s)‖ * ‖q κ‖ ≤ 1 * ‖q κ‖ :=
        mul_le_mul_of_nonneg_right (norm_incl_le _) (norm_nonneg _)
    _ ≤ ‖q‖ := by rw [one_mul]; exact norm_le_pi_norm q κ

theorem norm_upG_le (s : ℕ) : ‖upG (N := N) s‖ ≤ invConst s * N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := invConst_nonneg s; positivity)
    fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by have := invConst_nonneg s; positivity)).mpr fun κ => ?_
  show ‖up s (v κ)‖ ≤ _
  refine ((up (N := N) s).le_opNorm _).trans ?_
  exact mul_le_mul (norm_up_le s) (norm_le_pi_norm v κ) (norm_nonneg _)
    (by have := invConst_nonneg s; positivity)

/-- **The inverse-mesh bounds of the grid writer** in the form `Writer.Bounds (1/N) A δ`, with
`A, δ` independent of the mesh and of the mark. -/
theorem gridWriter_bounds (s : ℕ) (hs : 2 ≤ s) (b : ℝ) :
    ∃ δ > 0, ∃ A ≥ 1, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      (gridWriter (N := N) s B).Bounds (1 / (N : ℝ)) A δ := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := local_vector_bounds s hs 9 b
  refine ⟨min δ 1, lt_min hδ one_pos, max (max C (invConst s)) 1, le_max_right _ _,
    fun N _ B hB => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hinv : (1 / (N : ℝ))⁻¹ = N := by rw [one_div, inv_inv]
  set A := max (max C (invConst s)) 1
  have hCA : C ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hIA : invConst s ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hd := (hb N B hB).subset (ball_subset_ball (min_le_left δ 1))
  have hd' : DerivBound (gridWriter (N := N) s B).field (ball 0 (min δ 1)) 9 (A * (1 / (N : ℝ))⁻¹) :=
    hd.mono le_rfl (by rw [hinv]; exact mul_le_mul_of_nonneg_right hCA hN0.le)
  refine ⟨by positivity, by rw [div_le_one hN0]; exact hN1, le_max_right _ _, lt_min hδ one_pos,
    min_le_right _ _, norm_iotaG_le s, ?_, hd', fun Z hZ => ?_⟩
  · rw [hinv]; exact (norm_upG_le s).trans (mul_le_mul_of_nonneg_right hIA hN0.le)
  · have := norm_lawField_le s (by norm_num) hd' hZ
    exact this

/-- **`lem:supp-open-hermite-residual`** for the local finite writer.  Fix `s ≥ 2` (the
manuscript takes `s ≥ 11`), a bound `b` on the mark entries (`B = 0` is the open writer) and
`0 < c₋ ≤ c₊`.  There are `δ > 0`, `N₀` and `C`, independent of the mesh `h = 1/N` and of the
mark, such that for every `N ≥ N₀`, every source `X ∈ 𝒳^s_h` with `‖X‖ ≤ ε ≤ δ/4` and every
step `c₋h² ≤ τ ≤ c₊h²`, the endpoint-corrected Taylor–Hermite polynomial `Q_X` (the unique
degree-seven polynomial with jets `(q, v, V_{B,h}(X), J_{B,h}(X))` at `0` and
`(X₁, V_{B,h}(X₁), J_{B,h}(X₁))` at `τ`, `Writer.hermiteC_jets`, `Writer.hermiteC_unique`)
satisfies on the complete interval `[0, τ]`: `(Q_X, Q_X')` stays in the common chart, the actual
defect `f_X = Q_X'' − V_{B,h}(Q_X, Q_X')` has `‖f_X(t)‖_{H^s_h} ≤ C ε h⁵`, and `f_X` is
differentiable with `‖∂_t f_X(t)‖_{H^s_h} ≤ C ε h³` (`eq:supp-open-hermite-local-defect`; the
manuscript retains only the weaker `H^{s-3}_h` norm for `∂_t f_X`). -/
theorem open_hermite_residual (s : ℕ) (hs : 2 ≤ s) (b cm cp : ℝ) (hcm : 0 < cm) (hcp : 0 < cp) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      ∀ (X : XS N s) (ε τ : ℝ), ‖X‖ ≤ ε → 4 * ε ≤ δ →
      cm * (1 / (N : ℝ)) ^ 2 ≤ τ → τ ≤ cp * (1 / (N : ℝ)) ^ 2 →
      ∀ t ∈ Icc 0 τ,
        (gridWriter s B).phase ((gridWriter s B).hermiteC X τ) t ∈ ball 0 δ ∧
        ‖(gridWriter s B).defect ((gridWriter s B).hermiteC X τ) t‖ ≤
          C * ε * (1 / (N : ℝ)) ^ 5 ∧
        HasDerivAt ((gridWriter s B).defect ((gridWriter s B).hermiteC X τ))
          ((gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ) t) t ∧
        ‖(gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ) t‖ ≤
          C * ε * (1 / (N : ℝ)) ^ 3 := by
  obtain ⟨δ, hδ, A, hA, hB⟩ := gridWriter_bounds s hs b
  obtain ⟨h₀, hh₀, C, hC, hres⟩ := hermite_residual.{0, 0} A cm cp hA hcm hcp
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / h₀)
  refine ⟨δ, hδ, N₀ + 1, C, hC, fun N _ hN B hBb X ε τ hX hεδ hτm hτp t ht => ?_⟩
  have hN : (1 / h₀ : ℝ) ≤ N := hN₀.trans (by exact_mod_cast (Nat.le_succ N₀).trans hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hh : 1 / (N : ℝ) ≤ h₀ := by
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hh₀] at hN
    linarith
  exact hres (gridWriter s B) (1 / (N : ℝ)) δ (hB N B hBb) hh X ε τ hX hεδ hτm hτp t ht


/-- **`lem:supp-open-hermite-precision`** for the local finite writer (Sobolev-scaled finite
precision).  Fix `s ≥ 2`, a mark bound `b`, `0 < c₋ ≤ c₊` and `c ≥ 0`.  There are `δ > 0`,
`N₀` and `C`, independent of `h = 1/N` and of the mark, such that for `N ≥ N₀`, every source
`‖X‖ ≤ ε ≤ δ/4` (the smaller common chart), every step `c₋h² ≤ τ ≤ c₊h²`, every degree-seven
perturbation `δQ` (coefficients `d`) of the polynomial `Q_X` of `open_hermite_residual`, and every
`b_h ≥ max_{e ∈ {0,1}, j ≤ 3} τʲ ‖δQ⁽ʲ⁾(eτ)‖_{H^s_h}` (`eq:supp-open-hermite-precision`), on
`[0, τ]`: `‖δQ⁽ʲ⁾(t)‖_{H^s_h} ≤ C_j τ^{-j} b_h` (`C_j = hermiteConst 3 j`); and if
`b_h ≤ c ε τ² h⁵`, then `Q̃_X = Q_X + δQ` stays in the local phase tube (chart), the complete
residual changes by at most `C τ^{-2} b_h` and its time derivative by at most `C τ^{-3} b_h`, and
`‖f_{Q̃}‖ ≤ C ε h⁵`, `‖∂_t f_{Q̃}‖ ≤ C ε h³` (the bounds `eq:supp-open-hermite-local-defect` are
preserved). -/
theorem open_hermite_precision (s : ℕ) (hs : 2 ≤ s) (b cm cp cb : ℝ) (hcm : 0 < cm)
    (hcp : 0 < cp) (hcb : 0 ≤ cb) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      ∀ (X : XS N s) (ε τ : ℝ), ‖X‖ ≤ ε → 4 * ε ≤ δ →
      cm * (1 / (N : ℝ)) ^ 2 ≤ τ → τ ≤ cp * (1 / (N : ℝ)) ^ 2 →
      ∀ (d : Fin 8 → Upper → GridH N (s + 1)) (bh : ℝ),
      (∀ e : Fin 2, ∀ i : Fin 4, τ ^ (i : ℕ) *
        ‖(gridWriter s B).ι (polyCurveDeriv i d (((e : ℕ) : ℝ) * τ))‖ ≤ bh) →
      ∀ t ∈ Icc 0 τ,
        (∀ j, ‖(gridWriter s B).ι (polyCurveDeriv j d t)‖ ≤ hermiteConst 3 j * bh / τ ^ j) ∧
        (bh ≤ cb * ε * τ ^ 2 * (1 / (N : ℝ)) ^ 5 →
          (gridWriter s B).phase ((gridWriter s B).hermiteC X τ + d) t ∈ ball 0 δ ∧
          ‖(gridWriter s B).defect ((gridWriter s B).hermiteC X τ + d) t -
            (gridWriter s B).defect ((gridWriter s B).hermiteC X τ) t‖ ≤ C * bh / τ ^ 2 ∧
          ‖(gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ + d) t -
            (gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ) t‖ ≤ C * bh / τ ^ 3 ∧
          ‖(gridWriter s B).defect ((gridWriter s B).hermiteC X τ + d) t‖ ≤
            C * ε * (1 / (N : ℝ)) ^ 5 ∧
          HasDerivAt ((gridWriter s B).defect ((gridWriter s B).hermiteC X τ + d))
            ((gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ + d) t) t ∧
          ‖(gridWriter s B).defectDeriv ((gridWriter s B).hermiteC X τ + d) t‖ ≤
            C * ε * (1 / (N : ℝ)) ^ 3) := by
  obtain ⟨δ, hδ, A, hA, hB⟩ := gridWriter_bounds s hs b
  obtain ⟨h₀, hh₀, C, hC, hprec⟩ := hermite_precision.{0, 0} A cm cp cb hA hcm hcp hcb
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / h₀)
  refine ⟨δ, hδ, N₀ + 1, C, hC, fun N _ hN B hBb X ε τ hX hεδ hτm hτp d bh hbh t ht => ?_⟩
  have hN : (1 / h₀ : ℝ) ≤ N := hN₀.trans (by exact_mod_cast (Nat.le_succ N₀).trans hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hh : 1 / (N : ℝ) ≤ h₀ := by
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hh₀] at hN
    linarith
  exact hprec (gridWriter s B) (1 / (N : ℝ)) δ (hB N B hBb) hh X ε τ hX hεδ hτm hτp d bh hbh t ht

/-- Non-vacuity: the hypotheses of `open_hermite_residual` are satisfiable (the flat source
`X = 0`, `ε = 0` and the step `τ = c h²`). -/
example (s : ℕ) (c : ℝ) (hc : 0 < c) :
    ‖(0 : XS N s)‖ ≤ 0 ∧ 4 * (0 : ℝ) ≤ 1 ∧ c * (1 / (N : ℝ)) ^ 2 ≤ c * (1 / (N : ℝ)) ^ 2 :=
  ⟨by simp, by norm_num, le_rfl⟩

end

end RenewalGeometry.OpenWriterLocalJets
