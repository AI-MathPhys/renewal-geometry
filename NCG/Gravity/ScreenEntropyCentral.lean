/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Central screen-entropy decomposition and predictive-pure rigidity
  (`lem:central-screen-entropy`, `thm:predictive-pure-entropy`,
   GR_emergence)

The central state `ρ_Σ = ⊕_y p_y ρ_y^L ⊗ ρ_y^R` has eigenvalues
`p_y λ_i^{(y)} μ_j^{(y)}`, so its von Neumann entropy is a spectral
sum which decomposes exactly:

* `negMulLog_triple` — the three-factor expansion of `-x log x`;
* `central_screen_entropy` — the boxed formula
  `S(ρ_Σ) = H(p) + Σ_y p_y S(ρ_y^L) + Σ_y p_y S(ρ_y^R)`, in
  spectral form;
* `predictive_pure_entropy` — predictive purity (all conditional
  spectral entropies zero) collapses the cell entropy to the Shannon
  entropy `H(p)` of the resolved record;
* `conditional_entropy_nonneg` — on a larger algebra the only
  additional term `S_cond = 𝔼_Y[S(ρ_Y^L) + S(ρ_Y^R)]` is
  nonnegative, never a coherent negative correction;
* `markov_rate_form` — the stationary first-order record rate
  `h(Π) = -Σ_{x,y} π_x Π_{xy} log Π_{xy}` as an `H(p)` instance.

The identification of the von Neumann entropy with the spectral sum
(diagonalization of each central block) and the strip/stationary
limit `S/N → h(Π)` are the declared spectral-calculus inputs.
-/

namespace NCG

open Real

/-- Three-factor expansion of the entropy kernel. -/
theorem negMulLog_triple (a b c : ℝ) :
    Real.negMulLog (a * b * c)
      = b * c * Real.negMulLog a + a * c * Real.negMulLog b
        + a * b * Real.negMulLog c := by
  rw [Real.negMulLog_mul (a * b) c, Real.negMulLog_mul a b]
  ring

/-- `lem:central-screen-entropy` (boxed formula, spectral form): the
central state `⊕_y p_y ρ_y^L ⊗ ρ_y^R` with conditional spectra
`λ^{(y)}, μ^{(y)}` has entropy
`H(p) + Σ_y p_y S(λ^{(y)}) + Σ_y p_y S(μ^{(y)})`. -/
theorem central_screen_entropy {Y I J : Type*} [Fintype Y]
    [Fintype I] [Fintype J]
    (p : Y → ℝ) (lam : Y → I → ℝ) (mu : Y → J → ℝ)
    (hlam1 : ∀ y, ∑ i, lam y i = 1) (hmu1 : ∀ y, ∑ j, mu y j = 1) :
    (∑ y, ∑ i, ∑ j, Real.negMulLog (p y * lam y i * mu y j))
      = (∑ y, Real.negMulLog (p y))
        + (∑ y, p y * ∑ i, Real.negMulLog (lam y i))
        + ∑ y, p y * ∑ j, Real.negMulLog (mu y j) := by
  have hpt : ∀ y, (∑ i, ∑ j, Real.negMulLog (p y * lam y i * mu y j))
      = Real.negMulLog (p y)
        + p y * (∑ i, Real.negMulLog (lam y i))
        + p y * ∑ j, Real.negMulLog (mu y j) := by
    intro y
    have hexp : (∑ i, ∑ j, Real.negMulLog (p y * lam y i * mu y j))
        = ∑ i, ∑ j,
            (lam y i * mu y j * Real.negMulLog (p y)
              + p y * mu y j * Real.negMulLog (lam y i)
              + p y * lam y i * Real.negMulLog (mu y j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact negMulLog_triple (p y) (lam y i) (mu y j)
    rw [hexp]
    simp only [Finset.sum_add_distrib]
    congr 1
    · congr 1
      · -- Σ_i Σ_j λμ·nml(p) = nml(p)
        rw [show (∑ i, ∑ j, lam y i * mu y j * Real.negMulLog (p y))
          = (∑ i, lam y i) * (∑ j, mu y j) * Real.negMulLog (p y)
          from by
            rw [Finset.sum_mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]]
        rw [hlam1 y, hmu1 y]
        ring
      · -- Σ_i Σ_j pμ·nml(λ) = p·Σ nml(λ)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show (∑ j, p y * mu y j * Real.negMulLog (lam y i))
          = p y * Real.negMulLog (lam y i) * ∑ j, mu y j from by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring]
        rw [hmu1 y]
        ring
    · -- Σ_i Σ_j pλ·nml(μ) = p·Σ nml(μ)
      calc (∑ i, ∑ j, p y * lam y i * Real.negMulLog (mu y j))
          = ∑ i, lam y i * (p y * ∑ j, Real.negMulLog (mu y j)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i, lam y i) * (p y * ∑ j, Real.negMulLog (mu y j)) :=
            (Finset.sum_mul _ _ _).symm
      _ = p y * ∑ j, Real.negMulLog (mu y j) := by
            rw [hlam1 y, one_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  exact hpt y

/-- `thm:predictive-pure-entropy` (rigidity): predictive purity kills
every conditional entropy, so the cell entropy equals the Shannon
entropy of the resolved record. -/
theorem predictive_pure_entropy {Y I J : Type*} [Fintype Y]
    [Fintype I] [Fintype J]
    (p : Y → ℝ) (lam : Y → I → ℝ) (mu : Y → J → ℝ)
    (hlam1 : ∀ y, ∑ i, lam y i = 1) (hmu1 : ∀ y, ∑ j, mu y j = 1)
    (hpureL : ∀ y, (∑ i, Real.negMulLog (lam y i)) = 0)
    (hpureR : ∀ y, (∑ j, Real.negMulLog (mu y j)) = 0) :
    (∑ y, ∑ i, ∑ j, Real.negMulLog (p y * lam y i * mu y j))
      = ∑ y, Real.negMulLog (p y) := by
  rw [central_screen_entropy p lam mu hlam1 hmu1]
  simp [hpureL, hpureR]

/-- `thm:predictive-pure-entropy` (larger algebra): the only
additional term is the nonnegative conditional density
`S_cond = Σ_y p_y (S(λ^{(y)}) + S(μ^{(y)})) ≥ 0`. -/
theorem conditional_entropy_nonneg {Y I J : Type*} [Fintype Y]
    [Fintype I] [Fintype J]
    (p : Y → ℝ) (lam : Y → I → ℝ) (mu : Y → J → ℝ)
    (hp : ∀ y, 0 ≤ p y)
    (hlam : ∀ y i, 0 ≤ lam y i) (hmu : ∀ y j, 0 ≤ mu y j)
    (hlam1 : ∀ y, ∑ i, lam y i = 1) (hmu1 : ∀ y, ∑ j, mu y j = 1) :
    0 ≤ ∑ y, p y * ((∑ i, Real.negMulLog (lam y i))
      + ∑ j, Real.negMulLog (mu y j)) := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hp y)
  have hL : 0 ≤ ∑ i, Real.negMulLog (lam y i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Real.negMulLog_nonneg (hlam y i)
    calc lam y i ≤ ∑ i', lam y i' :=
          Finset.single_le_sum (fun i' _ => hlam y i')
            (Finset.mem_univ i)
    _ = 1 := hlam1 y
  have hR : 0 ≤ ∑ j, Real.negMulLog (mu y j) := by
    apply Finset.sum_nonneg
    intro j _
    apply Real.negMulLog_nonneg (hmu y j)
    calc mu y j ≤ ∑ j', mu y j' :=
          Finset.single_le_sum (fun j' _ => hmu y j')
            (Finset.mem_univ j)
    _ = 1 := hmu1 y
  linarith

/-- `thm:predictive-pure-entropy` (Markov rate form): for a
stationary first-order record, the Shannon entropy of the joint step
distribution `p_{(x,y)} = π_x Π_{xy}` decomposes as
`H(π) + h(Π)` with `h(Π) = -Σ_{x,y} π_x Π_{xy} log Π_{xy}` — the
boxed conditional-entropy rate. -/
theorem markov_rate_form {X : Type*} [Fintype X]
    (pi : X → ℝ) (Pi : X → X → ℝ)
    (hrow : ∀ x, ∑ y, Pi x y = 1) :
    (∑ x, ∑ y, Real.negMulLog (pi x * Pi x y))
      = (∑ x, Real.negMulLog (pi x))
        + ∑ x, ∑ y, pi x * Real.negMulLog (Pi x y) := by
  have hpt : ∀ x, (∑ y, Real.negMulLog (pi x * Pi x y))
      = Real.negMulLog (pi x)
        + ∑ y, pi x * Real.negMulLog (Pi x y) := by
    intro x
    have hexp : (∑ y, Real.negMulLog (pi x * Pi x y))
        = ∑ y, (Pi x y * Real.negMulLog (pi x)
            + pi x * Real.negMulLog (Pi x y)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.negMulLog_mul]
    rw [hexp, Finset.sum_add_distrib, ← Finset.sum_mul, hrow x,
      one_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact hpt x

end NCG
