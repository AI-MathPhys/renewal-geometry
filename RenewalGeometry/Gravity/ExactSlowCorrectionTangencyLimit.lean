/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowGateExact
import RenewalGeometry.Gravity.ExactSlowCompatibilityLimit

/-!
# First slow correction and initial tangency of bounded-rate limits
  (`prop:supp-exact-slow-correction`; emergent-spacetime manuscript)

`ExactSlowGate.slow_first_tangency` proves the tangency identity
`eq:supp-exact-slow-first-tangency` for any path along which the five slow identities
`𝔆_sl(ξ₀(τ)) = 0` hold.  `SlowCompatibility.five_compatibility`
(`thm:supp-exact-five-compatibility`) proves these identities for every uniformly convergent
subsequence of bounded-rate exact histories.  This file combines the two:

* `differentiable_sigma0`, `differentiable_phi1`: the slow coefficients `Σ₀`, `Φ₁` of
  `eq:supp-exact-slow-coefficients` (multilinear evaluations of the iterated derivatives of the
  remainders) are differentiable everywhere, so `DΣ₀(0)`, `DΦ₁(0)` exist;
* `slow_correction_limit` (**`prop:supp-exact-slow-correction`**): under the hypotheses of
  `thm:supp-exact-five-compatibility` and the coupling tests, (i) for every `ξ₀`,
  `Φ₀ ξ₁ + Φ₁(ξ₀) = 0` is solvable iff `𝔪(ξ₀) = 0`; (ii) for every right inverse `R₀` of `Φ₀`
  on its range and `𝔪(ξ₀) = 0`, the solutions are exactly `-R₀ Φ₁(ξ₀) + ker Φ₀`; (iii) every
  limiting path of the theorem with `ξ₀(0) = 0` and (one-sided) derivative `b` at `0` satisfies
  `D𝔆_sl(0)[b] = (p_g C_red DΣ₀(0)[b], p_H DΦ₁(0)[b]) = 0`.
-/

open Filter Set
open scoped Topology

namespace RenewalGeometry
namespace ExactSlowCorrectionLimit

open ExactSlowExpansion ExactSlowBranch ExactSlowGate SlowCompatibility

section Coefficients

variable {Xs W : Type*} [NormedAddCommGroup Xs] [NormedSpace ℝ Xs]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `Σ₀` (`eq:supp-exact-slow-coefficients`) is differentiable. -/
theorem differentiable_sigma0 (Rs : ℝ × (Xs × W) → Xs) : Differentiable ℝ (sigma0 Rs) := by
  have hd : Differentiable ℝ fun ξ : Xs × W => slowDir ξ := by
    unfold slowDir; fun_prop
  have hM : ∀ (L : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ℝ × (Xs × W)) Xs)
      (g : Xs × W → Fin 3 → ℝ × (Xs × W)), Differentiable ℝ g →
      Differentiable ℝ fun ξ => L (g ξ) := fun L g hg =>
    ((L.contDiff (n := 1)).differentiable one_ne_zero).comp hg
  unfold sigma0
  refine Differentiable.add (Differentiable.const_smul ?_ _) (Differentiable.const_smul ?_ _)
  · refine hM _ _ (differentiable_pi.2 fun i => ?_)
    fin_cases i <;> simp [hd]
  · refine hM _ _ (differentiable_pi.2 fun i => ?_)
    fin_cases i <;> simp [hd]

/-- `Φ₁` (`eq:supp-exact-slow-coefficients`) is differentiable. -/
theorem differentiable_phi1 (Rf : ℝ × (Xs × W) → W) : Differentiable ℝ (phi1 Rf) := by
  have hd : Differentiable ℝ fun ξ : Xs × W => slowDir ξ := by
    unfold slowDir; fun_prop
  have hM : ∀ (L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × (Xs × W)) W)
      (g : Xs × W → Fin 2 → ℝ × (Xs × W)), Differentiable ℝ g →
      Differentiable ℝ fun ξ => L (g ξ) := fun L g hg =>
    ((L.contDiff (n := 1)).differentiable one_ne_zero).comp hg
  unfold phi1
  refine Differentiable.add ?_ (Differentiable.const_smul ?_ _)
  · refine hM _ _ (differentiable_pi.2 fun i => ?_)
    fin_cases i <;> simp [hd]
  · refine hM _ _ (differentiable_pi.2 fun i => ?_)
    fin_cases i <;> simp [hd]

end Coefficients

section Record

variable {Xs W Zg Hs : Type*} [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [FiniteDimensional ℝ Xs]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]

/-- **`prop:supp-exact-slow-correction`** (first correction and initial slow tangency).
Data and hypotheses of `thm:supp-exact-five-compatibility` (exact histories `v_j` of the
unbalanced field on `0 ≤ t ≤ T a_j` with graded analytic remainders and bounded slow rate), the
weak decomposition `eq:supp-exact-weak-decomposition` and the coupling tests `p_H C_red = 0`,
`p_g C_red` onto `𝒵_g`.  Then:
1. for every `ξ₀` (in particular `ξ₀ ∈ ker Φ₀`), `Φ₀ ξ₁ + Φ₁(ξ₀) = 0` is solvable iff
   `𝔪(ξ₀) = p_H Φ₁(ξ₀) = 0`;
2. if `𝔪(ξ₀) = 0` and `R₀` is a right inverse of `Φ₀` on its range, the solutions are exactly
   `ξ₁ ∈ -R₀ Φ₁(ξ₀) + ker Φ₀`;
3. every limiting path `ξ₀` of a uniformly convergent subsequence of the slow forms with
   `ξ₀(0) = 0` and derivative `b` at `0` (one-sided, on `[0, T]`; implied by `C¹` at zero)
   satisfies `eq:supp-exact-slow-first-tangency`:
   `(p_g C_red DΣ₀(0)[b], p_H DΦ₁(0)[b]) = 0`, and this is `D𝔆_sl(0)[b]`. -/
theorem slow_correction_limit (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (bs : Xs) (bw : W)
    (Rs : ℝ × (Xs × W) → Xs) (Rf : ℝ × (Xs × W) → W)
    (hRs : AnalyticAt ℝ Rs 0) (hRf : AnalyticAt ℝ Rf 0)
    (hbs : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rs (a, v)‖ ≤ C * (a ^ 4 + a ^ 2 * ‖v‖ + a * ‖v‖ ^ 2))
    (hbf : ∃ δ > 0, ∃ C, ∀ a v, 0 < a → a < δ → ‖v‖ < δ →
      ‖Rf (a, v)‖ ≤ C * (a ^ 4 + a * ‖v‖ + ‖v‖ ^ 2))
    {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W} {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}
    (hD : WeakDecomposition B Jg JH pg pH) (hHC : ∀ x, pH (Cred x) = 0)
    (hgC : Function.Surjective fun x => pg (Cred x))
    {T : ℝ} (hT : 0 < T) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ha0 : Tendsto a atTop (𝓝 0))
    (v : ℕ → ℝ → Xs × W)
    (hv : ∀ j, ∀ s ∈ Icc 0 (T / a j ^ 2), HasDerivWithinAt (v j)
      (unbalancedField Cred B bs bw Rs Rf (a j) (v j s)) (Icc 0 (T / a j ^ 2)) s)
    (M : ℝ) (hM : ∀ j, ∀ τ ∈ Icc 0 T, ‖slowForm (a j) (v j) τ‖
      + ‖derivWithin (slowForm (a j) (v j)) (Icc 0 T) τ‖ ≤ M) :
    (∀ ξ₀ : Xs × W, (∃ ξ₁, leadingConstraint Cred B ξ₁ + phi1 Rf ξ₀ = 0) ↔
        slowMean pH (phi1 Rf) ξ₀ = 0) ∧
    (∀ (ξ₀ : Xs × W) (R₀ : W → Xs × W),
        (∀ w ∈ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W),
          leadingConstraint Cred B (R₀ w) = w) →
        slowMean pH (phi1 Rf) ξ₀ = 0 →
        ∀ ξ₁, leadingConstraint Cred B ξ₁ + phi1 Rf ξ₀ = 0 ↔
          ξ₁ - -R₀ (phi1 Rf ξ₀) ∈ LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) ∧
    (∀ φ : ℕ → ℕ, StrictMono φ → ∀ ξ₀ : ℝ → Xs × W,
      TendstoUniformlyOn (fun n => slowForm (a (φ n)) (v (φ n))) ξ₀ atTop (Icc 0 T) →
      ξ₀ 0 = 0 → ∀ b : Xs × W, HasDerivWithinAt ξ₀ b (Ici 0) 0 →
      HasFDerivAt (slowConstraint pg pH Cred bs (sigma0 Rs) (phi1 Rf))
          ((pg.comp (Cred.comp (fderiv ℝ (sigma0 Rs) 0))).prod
            (pH.comp (fderiv ℝ (phi1 Rf) 0))) 0 ∧
        (pg (Cred (fderiv ℝ (sigma0 Rs) 0 b)), pH (fderiv ℝ (phi1 Rf) 0 b)) = 0) := by
  refine ⟨fun ξ₀ => slow_correction_solvable_iff hD hHC hgC (phi1 Rf) ξ₀,
    fun ξ₀ R₀ hR₀ hm ξ₁ => slow_correction_solution_set hD hHC hgC (phi1 Rf) ξ₀ R₀ hR₀ hm ξ₁,
    ?_⟩
  intro φ hφ ξ₀ hconv h0 b hb
  have hfive := (five_compatibility Cred B bs bw Rs Rf hRs hRf hbs hbf hD hHC hT a ha ha0 v hv
    M hM).2 φ hφ ξ₀ hconv
  exact slow_first_tangency bs (sigma0 Rs) (phi1 Rf) _ _
    ((differentiable_sigma0 Rs) 0).hasFDerivAt ((differentiable_phi1 Rf) 0).hasFDerivAt
    ξ₀ b hT h0 hb hfive.2.2.2

/-- Non-vacuity: the hypothesis packet of `slow_correction_limit` is satisfiable
(`Xs = ℝ`, `W = ℝ²`, `C_red x = (x, 0)`, `B = 0`, `W = 0 ⊕ ℝ ⊕ ℝ`, zero remainders and
sources, zero histories, `a_j = 1/(j+1)`), including the surjectivity coupling test. -/
example : True := by
  have hD : WeakDecomposition (0 : ℝ × ℝ →L[ℝ] ℝ × ℝ) (ContinuousLinearMap.inl ℝ ℝ ℝ)
      (ContinuousLinearMap.inr ℝ ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
    { pg_Jg := fun _ => rfl, pH_JH := fun _ => rfl, pg_JH := fun _ => rfl,
      pH_Jg := fun _ => rfl, pg_B := fun _ => rfl, pH_B := fun _ => rfl,
      split := fun w => ⟨0, by simp⟩ }
  have := slow_correction_limit (Xs := ℝ) (W := ℝ × ℝ) (Zg := ℝ) (Hs := ℝ)
    (ContinuousLinearMap.inl ℝ ℝ ℝ) 0 0 0
    (fun _ => 0) (fun _ => 0) analyticAt_const analyticAt_const
    ⟨1, one_pos, 0, fun _ _ _ _ _ => by simp⟩ ⟨1, one_pos, 0, fun _ _ _ _ _ => by simp⟩
    hD (fun _ => rfl) (fun z => ⟨z, rfl⟩) one_pos (fun j => 1 / ((j : ℝ) + 1))
    (fun j => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat (fun _ _ => 0)
    (fun j s _ => by
      have h := hasDerivWithinAt_const (𝕜 := ℝ) s (Icc 0 (1 / (1 / ((j : ℝ) + 1)) ^ 2))
        (0 : ℝ × (ℝ × ℝ))
      refine h.congr_deriv ?_
      simp [unbalancedField]
      rfl)
    0 (fun j τ _ => by
      have h0 : slowForm (1 / ((j : ℝ) + 1)) (fun _ => (0 : ℝ × (ℝ × ℝ))) = fun _ => 0 :=
        funext fun _ => by simp [slowForm]
      rw [h0]; simp)
  trivial

end Record

end ExactSlowCorrectionLimit
end RenewalGeometry
