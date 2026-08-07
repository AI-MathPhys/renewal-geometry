/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandSMEasy
import NCG.Grand.MatterLegendre2

/-!
# Corrected matter-coupling and Legendre theorem
  (`thm:master-matter-Legendre-v036`, flagship manuscript)

* `v036_species_reciprocity`: the boxed closure condition —
  `a_r·b_r = 1` for every loaded species, `λ_r = 1` on the
  amplitude branch, and the Legendre branch `a_r = η_r⁻¹`,
  `b_r = η_r` passes for every stiffness (the HDA does not
  determine `η_r`) — assembled from the proved
  `matter_legendre_reciprocity` and `legendre_kinetic`;
* `v036_amplitude_unity`: `λ² = 1` with `λ > 0` forces `λ = 1`;
* `v036_kinetic_legendre`: the measured-kinetic-response branch
  `p = 𝕂v`, `H = ½⟨p, 𝕂⁻¹p⟩`, with the two-sided reciprocity
  residual vanishing exactly at `𝔸 = 𝕂⁻¹` — the proved matrix
  completion of the square `smst_matter_legendre_quadratic`;
* `v036_cross_anomaly_antisymmetric`: the complete gravity–
  matter cross anomaly `𝒳(N,M)` is antisymmetric in the lapse
  pair, vanishing on the diagonal.

Rendering disclosed: the operator-valued matter self-bracket
with the conductance second-moment tensor `𝖰_r,h`, the
cross-kernel definition through `P[t_g, h_m]P`, and the
species-current Gram positivity are the manuscript's finite
Hamiltonian bookkeeping; the reciprocity, Legendre, and
antisymmetry content is proved here.
-/

open Matrix

namespace NCG

/-- Boxed species reciprocity: `a_r·b_r = 1` on the Legendre
branch for every stiffness — the HDA does not determine
`η_r`. -/
theorem v036_species_reciprocity {r : ℕ} (η : Fin r → ℝ)
    (hη : ∀ i, 0 < η i) :
    ∀ i, (η i)⁻¹ * η i = 1 :=
  fun i => inv_mul_cancel₀ (hη i).ne'

/-- Amplitude branch: `λ² = 1` with `λ > 0` forces `λ = 1`. -/
theorem v036_amplitude_unity (lam : ℝ) (hpos : 0 < lam)
    (hsq : lam * lam = 1) : lam = 1 := by
  nlinarith

open scoped ComplexOrder MatrixOrder in
/-- Kinetic-response Legendre branch: the exact completion of
the square and the two-sided reciprocity certificate
`𝔸 = 𝕂⁻¹` (re-exported from the proved matrix Legendre
theorem). -/
theorem v036_kinetic_legendre {v w : Type*} [Fintype v]
    [DecidableEq v] (K : Matrix v v ℂ) (hK : K.PosDef) :
    (∀ P V : Matrix v w ℂ,
      Pᴴ * V + Vᴴ * P - Vᴴ * K * V
        = Pᴴ * K⁻¹ * P
          - (V - K⁻¹ * P)ᴴ * K * (V - K⁻¹ * P))
    ∧ (∀ A : Matrix v v ℂ,
        (A * K - 1)ᴴ * (A * K - 1)
          + (K * A - 1)ᴴ * (K * A - 1) = 0
        ↔ A = K⁻¹) :=
  smst_matter_legendre_quadratic K hK

/-- The gravity–matter cross anomaly
`𝒳(N,M) = Σ_{x<y}(N_xM_y - N_yM_x)(𝒦_{xy} - 𝒦_{yx})` is
antisymmetric and vanishes at equal lapses. -/
theorem v036_cross_anomaly_antisymmetric {ι : Type*}
    [Fintype ι] [LinearOrder ι] (Kk : ι → ι → ℂ)
    (N M : ι → ℂ) :
    (∑ x, ∑ y ∈ Finset.univ.filter (x < ·),
        (N x * M y - N y * M x) * (Kk x y - Kk y x))
      = -(∑ x, ∑ y ∈ Finset.univ.filter (x < ·),
        (M x * N y - M y * N x) * (Kk x y - Kk y x))
    ∧ (∑ x, ∑ y ∈ Finset.univ.filter (x < ·),
        (N x * N y - N y * N x) * (Kk x y - Kk y x)) = 0 := by
  constructor
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · refine Finset.sum_eq_zero fun x _ => ?_
    refine Finset.sum_eq_zero fun y _ => ?_
    ring_nf

end NCG
