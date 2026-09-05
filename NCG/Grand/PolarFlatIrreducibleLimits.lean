/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.PolarMetricHolonomy

/-!
# flat and irreducible polar limits

This identifies the concrete scalar/full-matrix facts in `polar_extremes` with
the root-fibre commutants of `smst_polar_holonomy`.
-/

open Matrix

namespace NCG

/-- A generator family has the full matrix algebra as commutant exactly when
every generator is scalar. -/
theorem matCommutant_eq_univ_iff_generators_scalar
    {g : Type*} [Fintype g] [DecidableEq g]
    (S : Set (Matrix g g ℂ)) :
    matCommutant S = Set.univ ↔
      ∀ A ∈ S, ∃ α : ℂ, A = α • 1 := by
  constructor
  · intro hfull A hAS
    have hcentral : ∀ R : Matrix g g ℂ, A * R = R * A := by
      intro R
      have hR : R ∈ matCommutant S := by rw [hfull]; exact Set.mem_univ R
      exact (hR A hAS).symm
    exact (polar_extremes (g := g)).2.1 A hcentral
  · intro hscalar
    ext R
    simp only [Set.mem_univ, iff_true]
    intro A hAS
    obtain ⟨α, rfl⟩ := hscalar A hAS
    exact (polar_extremes (g := g)).1 α R

/-- For a finite unital star algebra, scalar commutant is equivalent to the
algebra being the full matrix algebra. -/
theorem matCommutant_eq_scalars_iff_eq_top
    {g : Type*} [Fintype g] [DecidableEq g]
    (O : Subalgebra ℂ (Matrix g g ℂ))
    (hstar : ∀ A ∈ O, Aᴴ ∈ O) :
    matCommutant (O : Set (Matrix g g ℂ))
        = Set.range (fun α : ℂ => α • (1 : Matrix g g ℂ))
      ↔ O = ⊤ := by
  constructor
  · intro hscalar
    rw [eq_top_iff]
    intro T _
    apply double_commutant O hstar T
    intro B hB
    rw [hscalar] at hB
    obtain ⟨α, rfl⟩ := hB
    exact (polar_extremes (g := g)).1 α T
  · intro htop
    ext B
    constructor
    · intro hB
      rw [htop] at hB
      obtain ⟨α, hα⟩ :=
        (polar_extremes (g := g)).2.1 B (fun A => hB A (by simp))
      exact ⟨α, hα.symm⟩
    · rintro ⟨α, rfl⟩ A hAO
      exact ((polar_extremes (g := g)).1 α A).symm

/-- A unitary edge has trivial positive polar metric `P²`; transporting that
metric to the root fibre also gives the identity generator. -/
theorem unitary_edge_polar_metric_trivial
    {g : Type*} [Fintype g] [DecidableEq g]
    (F P Q : Matrix g g ℂ)
    (hF : Fᴴ * F = 1) (hP2 : P * P = Fᴴ * F)
    (hQ : Qᴴ * Q = 1) :
    P * P = 1 ∧ Qᴴ * (P * P) * Q = 1 := by
  have hmetric : P * P = 1 := hP2.trans hF
  refine ⟨hmetric, ?_⟩
  rw [hmetric, Matrix.mul_one, hQ]

/-- Exact four-clause polar-extremes packet in the root-fibre language. -/
theorem smst_polar_extremes_exact
    {g : Type*} [Fintype g] [DecidableEq g]
    (S : Set (Matrix g g ℂ))
    (O : Subalgebra ℂ (Matrix g g ℂ))
    (hstar : ∀ A ∈ O, Aᴴ ∈ O) :
    (matCommutant S = Set.univ ↔
      ∀ A ∈ S, ∃ α : ℂ, A = α • 1)
    ∧ (matCommutant (O : Set (Matrix g g ℂ))
          = Set.range (fun α : ℂ => α • (1 : Matrix g g ℂ))
        ↔ O = ⊤)
    ∧ (∀ (F P Q : Matrix g g ℂ), Fᴴ * F = 1 →
          P * P = Fᴴ * F → Qᴴ * Q = 1 →
          Qᴴ * (P * P) * Q = 1)
    ∧ (∃ K R : Matrix (Fin 2) (Fin 2) ℂ,
          Kᴴ = K ∧ R * K ≠ K * R) := by
  refine ⟨matCommutant_eq_univ_iff_generators_scalar S,
    matCommutant_eq_scalars_iff_eq_top O hstar, ?_,
    (polar_extremes (g := g)).2.2.2⟩
  intro F P Q hF hP hQ
  exact (unitary_edge_polar_metric_trivial F P Q hF hP hQ).2

end NCG
