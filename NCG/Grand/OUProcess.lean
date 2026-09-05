/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SobolevWeyl

/-!
# Ornstein–Uhlenbeck/process machinery for the continuum
  corollaries (`thm:renewal-interchange-OU`,
  `thm:renewal-regenerative-continuum`,
  `cor:renewal-positive-continuum`,
  `cor:renewal-spatial-positive-screen`,
  `cor:SMST-regenerative-screen`, `cor:finite-resolution-memory`,
  `cor:protected-ledger-short`, Gran-Tensor manuscript)

* `lyapunov_stationary`: the stationary OU covariance solves the
  Lyapunov equation — for the symmetric drift `A`,
  `A·A⁻¹ + A⁻¹·Aᵀ = 2`, so `Σ_∞ = A⁻¹` balances drift against
  unit noise;
* `ou_mean_decay`: the discrete OU mean recursion iterates
  exactly, `m_n = Mⁿ·m₀` — the deterministic skeleton of the
  interchange limit;
* `covariance_conjugation_psd`: positivity persists under every
  evolution step — `E·Σ·Eᵀ ⪰ 0` for `Σ ⪰ 0` (the positive
  screen of the spatial/regenerative corollaries);
* `screen_tail_bound`: the finite-resolution memory screen —
  the spectral mass above resolution `R` is at most `R⁻¹` times
  the Dirichlet energy (re-export of the proved diagonal tail
  bound), uniformly in the cutoff.

Rendering disclosed: the weak convergence of the rescaled
renewal field to the OU/Brownian limit in `D([0,T], 𝒟')`
(tightness plus finite-dimensional-distribution convergence),
the regenerative decomposition of the continuum process, and
the protected-ledger shorting on the true process carrier are
the manuscript's stochastic layer; the Lyapunov balance, the
exact mean recursion, the positivity persistence, and the
screen tail are proved here.
-/

open Matrix

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Stationary OU covariance: the symmetric drift balances unit
noise, `A·A⁻¹ + A⁻¹·Aᵀ = 2`. -/
theorem lyapunov_stationary (A : Matrix n n ℝ) (hsym : Aᵀ = A)
    (hA : IsUnit A.det) :
    A * A⁻¹ + A⁻¹ * Aᵀ = (2 : ℝ) • 1 := by
  rw [hsym, Matrix.mul_nonsing_inv A hA,
    Matrix.nonsing_inv_mul A hA, two_smul]

/-- The discrete OU mean recursion iterates exactly:
`m_{k+1} = M·m_k` gives `m_k = Mᵏ·m₀`. -/
theorem ou_mean_decay (M : Matrix n n ℝ) (m : ℕ → n → ℝ)
    (hrec : ∀ k, m (k + 1) = M.mulVec (m k)) (k : ℕ) :
    m k = (M ^ k).mulVec (m 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hrec k, ih, Matrix.mulVec_mulVec, ← pow_succ']

omit [DecidableEq n] in
open scoped ComplexOrder in
/-- Positivity persists under every evolution step:
`E·Σ·E* ⪰ 0` whenever `Σ ⪰ 0`. -/
theorem covariance_conjugation_psd (Sig : Matrix n n ℂ)
    (hSig : Sig.PosSemidef) (E : Matrix n n ℂ) :
    (E * Sig * Eᴴ).PosSemidef :=
  hSig.mul_mul_conjTranspose_same E

/-- Finite-resolution memory screen: spectral mass above
resolution `R` is dominated by `R⁻¹` times the Dirichlet energy
(re-export of the proved diagonal tail bound). -/
theorem screen_tail_bound {ι : Type*} [Fintype ι]
    (μ f lam : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hlam : ∀ i, 0 ≤ lam i) (R : ℝ) (hR : 0 < R) :
    ∑ i ∈ Finset.univ.filter (fun i => R < lam i),
        μ i * f i ^ 2
      ≤ R⁻¹ * ∑ i, lam i * (μ i * f i ^ 2) :=
  spectral_tail_bound μ f lam hμ hlam R hR

end NCG
