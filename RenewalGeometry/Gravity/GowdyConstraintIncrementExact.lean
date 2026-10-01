/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyStaggeredMomentumExact

/-!
# Exact constraint increment of a residual-perturbed Gowdy step
  (`eq:supp-gowdy-constraint-increment` of `prop:supp-gowdy-residual-control`;
  emergent-spacetime manuscript)

For an update `X_{j+1} = Φ_h(X_j) + r_j` (`eq:supp-gowdy-residual-update`), where `Φ_h` is the
source-half / transport / source-half composition of
`RenewalGeometry/Gravity/GowdyStaggeredMomentumExact.lean` and the residual has background part
`r^λ` and frame part `r^U`, the staggered momentum `𝒦_ℓ = D₊λ - 2𝖠₊𝒥(U)` changes exactly by

`𝒦_ℓ(X_{j+1}) - 𝒦_ℓ(X_j) = D₊ r^λ - 2𝖠₊[∇𝒥(Û_j)·r^U + 𝒥(r^U)]`,

with `Û_j` the deterministic predicted frame (the frame of `Φ_h(X_j)`).  The proof expands the
quadratic `𝒥` about `Û_j` (`J_add_sub`) and uses exact preservation of `𝒦_ℓ` by `Φ_h`
(`staggeredMomentum_symmetric_splitting`).
-/

namespace RenewalGeometry.GowdyStaggered

open Matrix

/-- Quadratic expansion `𝒥(u + r) - 𝒥(u) = ∇𝒥(u)·r + 𝒥(r)`. -/
theorem J_add_sub (u r : Fin 4 → ℝ) : J (u + r) - J u = gradJ u ⬝ᵥ r + J r := by
  simp only [J, gradJ, dotProduct, Fin.sum_univ_four, Pi.add_apply]
  simp
  ring

variable {N : ℕ}

/-- **Exact constraint increment** (`eq:supp-gowdy-constraint-increment`).  If `X₃` is the image
of `X₀` under the symmetric splitting step and `X'` differs from `X₃` by the residual
`(r^U, r^λ)`, then
`𝒦_ℓ(X') - 𝒦_ℓ(X₀) = D₊ r^λ - 2 𝖠₊ [∇𝒥(Û)·r^U + 𝒥(r^U)]` at every site, `Û` the frame of
`X₃`. -/
theorem staggeredMomentum_residual_increment (ℓ σ : ℝ) (hℓ : ℓ ≠ 0)
    {X₀ X₁ X₃ X' : GridState N} (h₁ : IsSourceStep σ X₀ X₁)
    (h₃ : IsSourceStep σ (transport ℓ X₁) X₃) (rlam : ZMod N → ℝ) (rU : ZMod N → Fin 4 → ℝ)
    (hlam : ∀ j, X'.lam j = X₃.lam j + rlam j) (hU : ∀ j, (X'.site j).u = (X₃.site j).u + rU j)
    (j : ZMod N) :
    staggeredMomentum ℓ X' j - staggeredMomentum ℓ X₀ j =
      (rlam (j + 1) - rlam j) / ℓ -
        2 * (((gradJ (X₃.site j).u ⬝ᵥ rU j + J (rU j)) +
          (gradJ (X₃.site (j + 1)).u ⬝ᵥ rU (j + 1) + J (rU (j + 1)))) / 2) := by
  rw [← staggeredMomentum_symmetric_splitting ℓ σ hℓ h₁ h₃ j]
  have e1 := J_add_sub (X₃.site j).u (rU j)
  have e2 := J_add_sub (X₃.site (j + 1)).u (rU (j + 1))
  simp only [staggeredMomentum, hlam, hU]
  rw [← e1, ← e2]
  field_simp
  ring

end RenewalGeometry.GowdyStaggered
