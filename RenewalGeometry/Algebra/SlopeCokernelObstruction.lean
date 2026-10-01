/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cokernel obstruction for the canonical slope polynomial
  (`cor:supp-exact-slope-cokernel`, `eq:supp-exact-cokernel-constant`,
  `eq:supp-exact-cokernel-no-root`; emergent-spacetime manuscript)

The corollary is the linear-algebra consequence of the canonical rank-two
factorization `eq:supp-exact-rank-two-factorization`
`𝒬_can(c) = q_{0,can} - 𝒞 ℛ(c)` with `𝒞 = 𝒞_g 𝒜_g⁻¹`
(`thm:supp-exact-rank-two-factorization`), which enters here as the hypothesis
`hfact`; that theorem itself is not formalised, so this file is a conditional
wrapper.  Given the factorization:

* `cokernel_pairing_constant`: `λᵀ 𝒬_can(c) = λᵀ q_{0,can}` for every
  `λ ∈ ker 𝒞_gᵀ` and every `c` (`eq:supp-exact-cokernel-constant`);
* `no_root_of_not_mem_range`: `q_{0,can} ∉ Ran 𝒞_g ⇒ 𝒬_can(c) ≠ 0` for every `c`
  (`eq:supp-exact-cokernel-no-root`).
-/

namespace RenewalGeometry
namespace SlopeCokernel

open Matrix

variable {ρ ζ κ : Type*} [Fintype ρ] [Fintype ζ] [DecidableEq ζ]

/-- `eq:supp-exact-cokernel-constant` (`cor:supp-exact-slope-cokernel`), given the
rank-two factorization `𝒬_can(c) = q₀ - (𝒞_g 𝒜_g⁻¹) ℛ(c)`: a left-null covector
of `𝒞_g` pairs to the same value with `𝒬_can(c)` and `q₀`. -/
theorem cokernel_pairing_constant (Cg : Matrix ρ ζ ℝ) (Ag : Matrix ζ ζ ℝ) (q0 : ρ → ℝ)
    (Qcan : κ → ρ → ℝ) (R : κ → ζ → ℝ)
    (hfact : ∀ c, Qcan c = q0 - (Cg * Ag⁻¹) *ᵥ R c)
    (lam : ρ → ℝ) (hlam : Cgᵀ *ᵥ lam = 0) (c : κ) :
    lam ⬝ᵥ Qcan c = lam ⬝ᵥ q0 := by
  rw [hfact c, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hlam,
    zero_dotProduct, sub_zero]

omit [Fintype ρ] in
/-- `eq:supp-exact-cokernel-no-root` (`cor:supp-exact-slope-cokernel`), given the
rank-two factorization: if `q₀ ∉ Ran 𝒞_g` then `𝒬_can(c) ≠ 0` for every `c`. -/
theorem no_root_of_not_mem_range (Cg : Matrix ρ ζ ℝ) (Ag : Matrix ζ ζ ℝ) (q0 : ρ → ℝ)
    (Qcan : κ → ρ → ℝ) (R : κ → ζ → ℝ)
    (hfact : ∀ c, Qcan c = q0 - (Cg * Ag⁻¹) *ᵥ R c)
    (hq0 : q0 ∉ LinearMap.range Cg.mulVecLin) (c : κ) :
    Qcan c ≠ 0 := by
  intro h0
  apply hq0
  refine ⟨Ag⁻¹ *ᵥ R c, ?_⟩
  rw [mulVecLin_apply, mulVec_mulVec]
  have := hfact c
  rw [h0] at this
  exact (sub_eq_zero.mp this.symm).symm

/-- Existence of the obstructing covector: if `q₀ ∉ Ran 𝒞_g` there is
`λ ∈ ker 𝒞_gᵀ` with `λᵀ q₀ ≠ 0`, so by `cokernel_pairing_constant`
`λᵀ 𝒬_can(c) = λᵀ q₀ ≠ 0` for all `c` (the paper's proof of
`eq:supp-exact-cokernel-no-root`). -/
theorem exists_cokernel_covector (Cg : Matrix ρ ζ ℝ) (q0 : ρ → ℝ)
    (hq0 : q0 ∉ LinearMap.range Cg.mulVecLin) :
    ∃ lam : ρ → ℝ, Cgᵀ *ᵥ lam = 0 ∧ lam ⬝ᵥ q0 ≠ 0 := by
  classical
  -- work in Euclidean space: the orthogonal complement of the range
  set W : Submodule ℝ (ρ → ℝ) := LinearMap.range Cg.mulVecLin with hW
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hq0
  -- every covector annihilating `W` annihilates `q0`
  have hann : ∀ lam : ρ → ℝ, (∀ w ∈ W, lam ⬝ᵥ w = 0) → lam ⬝ᵥ q0 = 0 := by
    intro lam hlam
    apply hcon lam
    ext j
    have := hlam (Cg *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [Pi.zero_apply, ← this, mulVec_transpose]
  -- transfer to `EuclideanSpace` and use `Wᗮᗮ = W`
  let e := (WithLp.linearEquiv 2 ℝ (ρ → ℝ)).symm
  set W' : Submodule ℝ (EuclideanSpace ℝ ρ) := W.map (e : (ρ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ρ)
  have hmem : e q0 ∈ W' := by
    rw [← Submodule.orthogonal_orthogonal W']
    intro v hv
    have := hann (WithLp.equiv 2 _ v) fun w hw => by
      have h := hv (e w) ⟨w, hw, rfl⟩
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h
      simpa [e, dotProduct_comm] using h
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [e, dotProduct_comm] using this
  obtain ⟨w, hw, hwq⟩ := hmem
  have : w = q0 := e.injective hwq
  exact this ▸ hw

end SlopeCokernel
end RenewalGeometry
