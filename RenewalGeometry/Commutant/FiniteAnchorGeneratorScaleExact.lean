/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.FiniteAnchorOperatorNormExact

/-!
# Finite-anchor stability: generator-scale control and the tail clause (`thm:finite-anchor`)

Completes `thm:finite-anchor` (Finite-anchor stability and generator-scale control) of the
spacetime–gauge duality manuscript on top of `FiniteAnchorOperatorNormExact.lean`, which
proved the operator-norm anchor clause `eq:anchor-tail` ⟹ `eq:anchor-lock`.

* `jointCommutatorL2_sqrt_anchor`: the anchor floor `γ₀ ‖x‖² ≤ ‖∂_{c₀} x‖²` gives
  `√γ₀ ‖x‖ ≤ ‖∂_{c₀} x‖`;
* `jointCommutatorL2_generatorScale_floor`: the triangle inequality directly on `M^⊥`,
  `‖∂_c x‖ ≥ (√γ₀ − 2 ε_{X,X₀}) ‖x‖`, with no bound on the generator norms;
* `finiteAnchorHowe_generatorScale`: **`eq:generator-scale-gap`** — if
  `2 ε_{X,X₀} < √γ₀` then `C*(c_X)' = M` and
  `λ⁺_min(ℒ_X) ≥ (√γ₀ − 2 ε_{X,X₀})²`;
* `finiteAnchorHowe_tail`, `finiteAnchorHowe_eventually`: the "throughout that tail"
  restatement for a cutoff family — whenever one of the two conditions holds at every later
  cutoff (resp. eventually), the exact commutant and a positive gap hold at every later cutoff
  (resp. eventually);
* `finite_anchor_stability`: the assembled statement with both conditions.
-/

open Matrix Filter
open scoped Matrix.Norms.L2Operator

namespace RenewalGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The anchor floor `γ₀ ‖x‖² ≤ ‖∂_{c₀} x‖²` gives `√γ₀ ‖x‖ ≤ ‖∂_{c₀} x‖`. -/
theorem jointCommutatorL2_sqrt_anchor {s : ℕ} (c₀ : Fin s → Matrix n n ℂ) {γ₀ : ℝ}
    (hγ : 0 ≤ γ₀) (x : EuclideanSpace ℂ (n × n))
    (hx : γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2) :
    Real.sqrt γ₀ * ‖x‖ ≤ ‖jointCommutatorL2 c₀ x‖ := by
  calc Real.sqrt γ₀ * ‖x‖ = Real.sqrt (γ₀ * ‖x‖ ^ 2) := by
        rw [Real.sqrt_mul hγ, Real.sqrt_sq (norm_nonneg x)]
    _ ≤ Real.sqrt (‖jointCommutatorL2 c₀ x‖ ^ 2) := Real.sqrt_le_sqrt hx
    _ = ‖jointCommutatorL2 c₀ x‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Generator-scale floor.**  Directly on the complement, the triangle inequality gives
`‖∂_c x‖ ≥ (√γ₀ − 2 ε_{X,X₀}) ‖x‖` from the anchor floor at `x`, without any bound on the
generator norms `C_X`, `C_{X₀}`. -/
theorem jointCommutatorL2_generatorScale_floor {s : ℕ} (c₀ c : Fin s → Matrix n n ℂ)
    {γ₀ : ℝ} (hγ : 0 ≤ γ₀) (x : EuclideanSpace ℂ (n × n))
    (hx : γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2) :
    (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) * ‖x‖ ≤ ‖jointCommutatorL2 c x‖ := by
  have h1 := jointCommutatorL2_sqrt_anchor c₀ hγ x hx
  have h2 : ‖jointCommutatorL2 c₀ x‖ - ‖jointCommutatorL2 c x‖
      ≤ 2 * opNormDisplacement c c₀ * ‖x‖ := by
    calc ‖jointCommutatorL2 c₀ x‖ - ‖jointCommutatorL2 c x‖
        ≤ ‖jointCommutatorL2 c₀ x - jointCommutatorL2 c x‖ := norm_sub_norm_le _ _
      _ = ‖jointCommutatorL2 c x - jointCommutatorL2 c₀ x‖ := norm_sub_rev _ _
      _ ≤ 2 * opNormDisplacement c c₀ * ‖x‖ := jointCommutatorL2_sub_norm_le c c₀ x
  nlinarith

/-- The squared generator-scale floor `(√γ₀ − 2 ε)² ‖x‖² ≤ ‖∂_c x‖²` when `2 ε < √γ₀`. -/
theorem jointCommutatorL2_generatorScale_sq_floor {s : ℕ} (c₀ c : Fin s → Matrix n n ℂ)
    {γ₀ : ℝ} (hγ : 0 ≤ γ₀) (hsmall : 2 * opNormDisplacement c c₀ < Real.sqrt γ₀)
    (x : EuclideanSpace ℂ (n × n))
    (hx : γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2) :
    (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2 * ‖x‖ ^ 2
      ≤ ‖jointCommutatorL2 c x‖ ^ 2 := by
  have h := jointCommutatorL2_generatorScale_floor c₀ c hγ x hx
  have h0 : 0 ≤ (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) * ‖x‖ :=
    mul_nonneg (by linarith) (norm_nonneg x)
  rw [← mul_pow]
  exact pow_le_pow_left₀ h0 h 2

/-- **`thm:finite-anchor`, generator-scale clause (`eq:generator-scale-gap`).**  On a common
finite screened carrier, if the protected algebra `M` commutes with the anchor tuple `c₀` and
the later tuple `c`, the anchor Howe Gram has the floor `γ₀ > 0` on `M^⊥`, and
`2 ε_{X,X₀} < √γ₀`, then `C*(c_X)' = M` (Hilbert–Schmidt-kernel and matrix-commutant forms)
and `λ⁺_min(ℒ_X) ≥ (√γ₀ − 2 ε_{X,X₀})² > 0`, without an upper bound on the generator norm. -/
theorem finiteAnchorHowe_generatorScale {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2)
    (hsmall : 2 * opNormDisplacement c c₀ < Real.sqrt γ₀) :
    LinearMap.ker (jointCommutatorL2 c) = M
    ∧ 0 < (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2
    ∧ (∀ x ∈ Mᗮ,
        (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2 * ‖x‖ ^ 2
          ≤ ‖jointCommutatorL2 c x‖ ^ 2)
    ∧ (∀ X : Matrix n n ℂ,
        matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔ ∀ j, c j * X = X * c j)
    ∧ RelativeHoweSpectralMargin c := by
  have _ := hM₀
  have hfloor : ∀ x ∈ Mᗮ,
      (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2 * ‖x‖ ^ 2
        ≤ ‖jointCommutatorL2 c x‖ ^ 2 := fun x hx =>
    jointCommutatorL2_generatorScale_sq_floor c₀ c hγ.le hsmall x (hanchor x hx)
  have hmargin : 0 < (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2 :=
    pow_pos (by linarith) 2
  have hpos : ∀ x ∈ Mᗮ, x ≠ 0 → 0 < ‖jointCommutatorL2 c x‖ ^ 2 := by
    intro x hx hne
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hf := hfloor x hx
    nlinarith
  have hker : LinearMap.ker (jointCommutatorL2 c) = M :=
    (howe_certificate (jointCommutatorL2 c) M hM).1 hpos
  exact ⟨hker, hmargin, hfloor, matrixL2_mem_jointCommutator_ker_iff c,
    matrix_commutant_least_eigenvalue_gap c⟩

/-- The two finite-anchor conditions of `thm:finite-anchor` for the later tuple `c` relative
to the anchor `c₀`: the operator-norm budget `eq:anchor-tail` or the generator-scale condition
`2 ε_{X,X₀} < √γ₀`. -/
def AnchorCondition {s : ℕ} (c₀ c : Fin s → Matrix n n ℂ) (γ₀ : ℝ) : Prop :=
  4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀ < γ₀
    ∨ 2 * opNormDisplacement c c₀ < Real.sqrt γ₀

/-- The finite-anchor conclusion `eq:anchor-lock` / `eq:generator-scale-gap` for the tuple
`c`: the exact commutant `C*(c)' = M` (both forms), a positive quadratic floor on `M^⊥`, and
the attained least positive eigenvalue of the commutant Laplacian. -/
def AnchorConclusion {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n))) : Prop :=
  LinearMap.ker (jointCommutatorL2 c) = M
    ∧ (∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ Mᗮ, κ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c x‖ ^ 2)
    ∧ (∀ X : Matrix n n ℂ,
        matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔ ∀ j, c j * X = X * c j)
    ∧ RelativeHoweSpectralMargin c

/-- Either finite-anchor condition yields the finite-anchor conclusion, with the explicit
gap `γ₀ − 4 (C_X + C_{X₀}) ε_{X,X₀}` resp. `(√γ₀ − 2 ε_{X,X₀})²`. -/
theorem anchorConclusion_of_anchorCondition {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2)
    (hcond : AnchorCondition c₀ c γ₀) :
    AnchorConclusion c M := by
  rcases hcond with h | h
  · obtain ⟨hker, hpos, hfloor, hmat, hmargin⟩ :=
      finiteAnchorHowe_operatorNormData c₀ c M γ₀ hγ hM₀ hM hanchor h
    exact ⟨hker, ⟨_, hpos, hfloor⟩, hmat, hmargin⟩
  · obtain ⟨hker, hpos, hfloor, hmat, hmargin⟩ :=
      finiteAnchorHowe_generatorScale c₀ c M γ₀ hγ hM₀ hM hanchor h
    exact ⟨hker, ⟨_, hpos, hfloor⟩, hmat, hmargin⟩

/-- **Tail clause of `thm:finite-anchor`.**  For a cutoff family `c_X` transported to the
common carrier, anchored at `X₀`: if the corresponding condition holds for every later `X`,
the conclusion holds throughout that tail. -/
theorem finiteAnchorHowe_tail {s : ℕ}
    (c : ℕ → Fin s → Matrix n n ℂ) (X₀ : ℕ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM : ∀ X, M ≤ LinearMap.ker (jointCommutatorL2 (c X)))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 (c X₀) x‖ ^ 2)
    (hcond : ∀ X, X₀ ≤ X → AnchorCondition (c X₀) (c X) γ₀) :
    ∀ X, X₀ ≤ X → AnchorConclusion (c X) M :=
  fun X hX =>
    anchorConclusion_of_anchorCondition (c X₀) (c X) M γ₀ hγ (hM X₀) (hM X) hanchor (hcond X hX)

/-- **Tail clause of `thm:finite-anchor`**, filter form: if the condition holds eventually
along the cutoff family, the conclusion holds eventually. -/
theorem finiteAnchorHowe_eventually {s : ℕ}
    (c : ℕ → Fin s → Matrix n n ℂ) (X₀ : ℕ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM : ∀ X, M ≤ LinearMap.ker (jointCommutatorL2 (c X)))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 (c X₀) x‖ ^ 2)
    (hcond : ∀ᶠ X in atTop, AnchorCondition (c X₀) (c X) γ₀) :
    ∀ᶠ X in atTop, AnchorConclusion (c X) M :=
  hcond.mono fun X hX =>
    anchorConclusion_of_anchorCondition (c X₀) (c X) M γ₀ hγ (hM X₀) (hM X) hanchor hX

/-- **`thm:finite-anchor` (Finite-anchor stability and generator-scale control),
assembled.**  With `M` commuting with both tuples and the anchor floor
`𝔾_Howe(c_{X₀} | M) ⪰ γ₀ I` on `M^⊥`:
(1) `eq:anchor-tail` ⟹ `eq:anchor-lock` (operator-norm budget);
(2) `2 ε_{X,X₀} < √γ₀` ⟹ `eq:generator-scale-gap` (no bound on the generator norm);
(3) if either condition holds for every later cutoff of a family, the exact commutant and a
positive gap hold throughout that tail. -/
theorem finite_anchor_stability {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ : ℝ) (hγ : 0 < γ₀)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ, γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2) :
    (4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀ < γ₀ →
      LinearMap.ker (jointCommutatorL2 c) = M
      ∧ (∀ x ∈ Mᗮ,
          (γ₀ - 4 * (opNormBudget c + opNormBudget c₀) * opNormDisplacement c c₀) * ‖x‖ ^ 2
            ≤ ‖jointCommutatorL2 c x‖ ^ 2)
      ∧ (∀ X : Matrix n n ℂ,
          matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔ ∀ j, c j * X = X * c j)
      ∧ RelativeHoweSpectralMargin c)
    ∧ (2 * opNormDisplacement c c₀ < Real.sqrt γ₀ →
      LinearMap.ker (jointCommutatorL2 c) = M
      ∧ (∀ x ∈ Mᗮ,
          (Real.sqrt γ₀ - 2 * opNormDisplacement c c₀) ^ 2 * ‖x‖ ^ 2
            ≤ ‖jointCommutatorL2 c x‖ ^ 2)
      ∧ (∀ X : Matrix n n ℂ,
          matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c) ↔ ∀ j, c j * X = X * c j)
      ∧ RelativeHoweSpectralMargin c)
    ∧ (∀ (cX : ℕ → Fin s → Matrix n n ℂ) (X₀ : ℕ), cX X₀ = c₀ →
        (∀ X, M ≤ LinearMap.ker (jointCommutatorL2 (cX X))) →
        (∀ X, X₀ ≤ X → AnchorCondition c₀ (cX X) γ₀) →
        ∀ X, X₀ ≤ X → AnchorConclusion (cX X) M) := by
  refine ⟨fun h => ?_, fun h => ?_, fun cX X₀ hX₀ hMX hcond => ?_⟩
  · obtain ⟨hker, -, hfloor, hmat, hmargin⟩ :=
      finiteAnchorHowe_operatorNormData c₀ c M γ₀ hγ hM₀ hM hanchor h
    exact ⟨hker, hfloor, hmat, hmargin⟩
  · obtain ⟨hker, -, hfloor, hmat, hmargin⟩ :=
      finiteAnchorHowe_generatorScale c₀ c M γ₀ hγ hM₀ hM hanchor h
    exact ⟨hker, hfloor, hmat, hmargin⟩
  · subst hX₀
    exact finiteAnchorHowe_tail cX X₀ M γ₀ hγ hMX hanchor hcond

end RenewalGeometry
