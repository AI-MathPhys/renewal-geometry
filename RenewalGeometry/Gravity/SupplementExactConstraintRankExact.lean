/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite characteristic quotient on a regular one-null branch
  (`thm:supp-exact-constraint-rank`, `eq:supp-exact-dirac-matrix`,
  `eq:supp-exact-dirac-rank`; emergent-spacetime manuscript)

Abstract block-matrix content of the theorem.  Let `Λ` be the finite
dimensional multiplier space (dimension `4V` in the paper), `M = D_λ P_h`
the multiplier Jacobian of the constraint map, `𝒜 = D_X P_h 𝕁 (D_X P_h)^*`
the constraint bracket, `B = D_X P_h F_h^{can}` the consistency source, and
`λ` the phase-compatible multiplier with `ker M = span{λ}`.  The extended
constraint bracket is the block map
`𝔇 (r, s) = (-M s, M r + 𝒜 s)` (`eq:supp-exact-dirac-matrix`).

* `diracMatrix`: the block map `[[0, -M], [M, 𝒜]]` on `Λ × Λ`.
* `bracket_mul_lambda_eq_source`: the identity `𝒜 λ = B` obtained by
  differentiating the homogeneity identity in `X` and pairing with the
  Hamiltonian vector field — once the canonical field is written as
  `F^{can} = 𝕁 (D_X P)^* λ`, the identity is `D_X P (𝕁 ((D_X P)^* λ)) = B`.
* `ker_diracMatrix`: on a regular one-null branch (`ker M = span{λ}`,
  `λ ≠ 0`, `𝒜 λ = B`, `B ∈ range M`, i.e. the first consistency condition
  `B + M λ̇ = 0` is solvable) the kernel is
  `span{(λ, 0), (-r₀, λ)}` for any particular solution `r₀` of `M r₀ = B`
  (the paper writes `r₀ = M^† B`) — the boxed `eq:supp-exact-dirac-rank`.
* `finrank_ker_diracMatrix`, `finrank_range_diracMatrix`: the kernel has
  dimension two and the rank is `2 dim Λ - 2 = 8V - 2`.
* `characteristic_quotient_dim`: the dimension count of the local
  characteristic quotient, `20V - 8V - 2 = 12V - 2`, on the extended phase
  of dimension `20V` with `8V` independent primary and secondary
  constraints (`D_X P_h` onto).

The identification of `M, 𝒜, B` with the derivatives of the actual
reconstructed finite action is not formalised: the maps enter as
parameters, as the paper's proof only uses the listed algebraic facts.
-/

namespace RenewalGeometry
namespace ExactConstraintRank

open Module

variable {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]

/-- The extended constraint bracket (Dirac block matrix)
`𝔇 (r, s) = (-M s, M r + 𝒜 s)` of `eq:supp-exact-dirac-matrix`. -/
def diracMatrix (M A : Λ →ₗ[ℝ] Λ) : Λ × Λ →ₗ[ℝ] Λ × Λ :=
  LinearMap.prod (-(M.comp (LinearMap.snd ℝ Λ Λ)))
    (M.comp (LinearMap.fst ℝ Λ Λ) + A.comp (LinearMap.snd ℝ Λ Λ))

@[simp]
theorem diracMatrix_apply (M A : Λ →ₗ[ℝ] Λ) (p : Λ × Λ) :
    diracMatrix M A p = (-(M p.2), M p.1 + A p.2) := rfl

/-- The homogeneity identity `𝒜 λ = B`: once the canonical field is
`F^{can} = 𝕁 ((D_X P)^* λ)` (the `X`-derivative of `H(X, cλ) = c H(X, λ)`
paired with the Hamiltonian vector field), the constraint bracket
`𝒜 = D_X P ∘ 𝕁 ∘ (D_X P)^*` applied to `λ` is the source
`B = D_X P F^{can}`. -/
theorem bracket_mul_lambda_eq_source {X : Type*} [AddCommGroup X] [Module ℝ X]
    (DP : X →ₗ[ℝ] Λ) (DPadj : Λ →ₗ[ℝ] X) (J : X →ₗ[ℝ] X) (lam : Λ) (Fcan : X)
    (hF : Fcan = J (DPadj lam)) :
    (DP.comp (J.comp DPadj)) lam = DP Fcan := by
  subst hF; rfl

variable (M A : Λ →ₗ[ℝ] Λ) {lam B r₀ : Λ}

theorem diracMatrix_lambda_zero (hlam : lam ∈ LinearMap.ker M) :
    diracMatrix M A (lam, 0) = 0 := by
  simp [LinearMap.mem_ker.mp hlam]

theorem diracMatrix_second_vector (hlam : lam ∈ LinearMap.ker M) (hAlam : A lam = B)
    (hr₀ : M r₀ = B) : diracMatrix M A (-r₀, lam) = 0 := by
  simp [LinearMap.mem_ker.mp hlam, hAlam, hr₀]

/-- **`eq:supp-exact-dirac-rank`, kernel.** On a regular one-null branch
(`ker M = span{λ}`, `𝒜 λ = B`, first consistency solvable with particular
solution `r₀`, e.g. `r₀ = M^† B`), the kernel of the Dirac block matrix is
spanned by `(λ, 0)` and `(-r₀, λ)`. -/
theorem ker_diracMatrix (hker : LinearMap.ker M = Submodule.span ℝ {lam})
    (hAlam : A lam = B) (hr₀ : M r₀ = B) :
    LinearMap.ker (diracMatrix M A)
      = Submodule.span ℝ {(lam, (0 : Λ)), (-r₀, lam)} := by
  have hlam : lam ∈ LinearMap.ker M := by
    rw [hker]; exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro p hp
    rw [LinearMap.mem_ker, diracMatrix_apply, Prod.mk_eq_zero, neg_eq_zero] at hp
    obtain ⟨h1, h2⟩ := hp
    -- first row: `s ∈ ker M = span{λ}`
    have hs : p.2 ∈ Submodule.span ℝ {lam} := hker ▸ LinearMap.mem_ker.mpr h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    -- second row: `r + c r₀ ∈ ker M`
    have hr : p.1 + c • r₀ ∈ Submodule.span ℝ {lam} := by
      rw [← hker, LinearMap.mem_ker, map_add, map_smul, hr₀]
      have : A p.2 = c • B := by rw [← hc, map_smul, hAlam]
      rw [← this]; exact h2
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hr
    have hp1 : p.1 = d • lam - c • r₀ := by rw [hd]; abel
    have hp : p = d • (lam, (0 : Λ)) + c • (-r₀, lam) := by
      ext
      · simp [hp1]; abel
      · simp [← hc]
    rw [hp]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact LinearMap.mem_ker.mpr (diracMatrix_lambda_zero M A hlam)
    · exact LinearMap.mem_ker.mpr (diracMatrix_second_vector M A hlam hAlam hr₀)

/-- The two characteristic directions are linearly independent
(`λ ≠ 0`). -/
theorem linearIndependent_characteristic (hlam : lam ≠ 0) :
    LinearIndependent ℝ ![(lam, (0 : Λ)), (-r₀, lam)] := by
  rw [LinearIndependent.pair_iff' (by simp [hlam])]
  intro a h
  have := congrArg Prod.snd h
  simp at this
  exact hlam this.symm

/-- The kernel of the Dirac block matrix has dimension two. -/
theorem finrank_ker_diracMatrix (hker : LinearMap.ker M = Submodule.span ℝ {lam})
    (hlam : lam ≠ 0) (hAlam : A lam = B) (hr₀ : M r₀ = B) :
    finrank ℝ (LinearMap.ker (diracMatrix M A)) = 2 := by
  rw [ker_diracMatrix M A hker hAlam hr₀, ← Matrix.range_cons_cons_empty _ _ ![],
    finrank_span_eq_card (linearIndependent_characteristic (r₀ := r₀) hlam)]
  simp

variable [FiniteDimensional ℝ Λ]

/-- **`eq:supp-exact-dirac-rank`, rank.** `rank 𝔇 = 2 dim Λ - 2`, i.e.
`8V - 2` when `dim Λ = 4V`. -/
theorem finrank_range_diracMatrix (hker : LinearMap.ker M = Submodule.span ℝ {lam})
    (hlam : lam ≠ 0) (hAlam : A lam = B) (hr₀ : M r₀ = B) :
    finrank ℝ (LinearMap.range (diracMatrix M A)) = 2 * finrank ℝ Λ - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (diracMatrix M A)
  rw [finrank_ker_diracMatrix M A hker hlam hAlam hr₀, Module.finrank_prod] at h
  omega

/-- The rank in the paper's normalisation `dim Λ = 4V`: `rank 𝔇 = 8V - 2`. -/
theorem finrank_range_diracMatrix_of_dim (V : ℕ) (hΛ : finrank ℝ Λ = 4 * V)
    (hker : LinearMap.ker M = Submodule.span ℝ {lam})
    (hlam : lam ≠ 0) (hAlam : A lam = B) (hr₀ : M r₀ = B) :
    finrank ℝ (LinearMap.range (diracMatrix M A)) = 8 * V - 2 := by
  rw [finrank_range_diracMatrix M A hker hlam hAlam hr₀, hΛ]; omega

omit [FiniteDimensional ℝ Λ] in
/-- The local characteristic quotient: the extended phase of dimension `20V`
minus the `8V` independent primary and secondary constraints (`D_X P_h`
onto) minus the two characteristic directions has dimension `12V - 2`. -/
theorem characteristic_quotient_dim (V : ℕ)
    (hker : LinearMap.ker M = Submodule.span ℝ {lam})
    (hlam : lam ≠ 0) (hAlam : A lam = B) (hr₀ : M r₀ = B) :
    20 * V - 8 * V - finrank ℝ (LinearMap.ker (diracMatrix M A)) = 12 * V - 2 := by
  rw [finrank_ker_diracMatrix M A hker hlam hAlam hr₀]; omega

end ExactConstraintRank
end RenewalGeometry
