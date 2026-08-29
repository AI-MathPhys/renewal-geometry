/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite-collar contact-tail alternative

An exact normed-space rendering of `thm:GTLOC-contact-tail-alternative`.
The quotient Cauchy property is stated constructively: every sufficiently
small regulator difference is within the requested norm tolerance of an
element of the closed local-counterterm space.
-/

open Filter Topology

namespace NCG
namespace ContactTailFiniteCollarAlternative

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complementary linear compression `I-P`. -/
def complement (P : E →ₗ[ℝ] E) : E →ₗ[ℝ] E := LinearMap.id - P

@[simp] theorem complement_apply (P : E →ₗ[ℝ] E) (x : E) :
    complement P x = x - P x := rfl

/-- Cauchy convergence as a positive real regulator tends to zero. -/
def CauchyAtZero (f : ℝ → E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < ε₀ →
      ‖f ε - f δ‖ < η

/-- Constructive Cauchy convergence in the quotient by `L`. -/
def QuotientCauchyAtZero (L : Submodule ℝ E) (f : ℝ → E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < ε₀ →
      ∃ l : E, l ∈ L ∧ ‖(f ε - f δ) - l‖ < η

/-- A persistent complementary collar tail cannot be removed by any bank
whose values are supported in that collar. -/
theorem persistent_tail_prevents_fixed_collar_cauchy
    (C : ℝ → E) (Pi : ℕ → E →ₗ[ℝ] E)
    (hcontract : ∀ R x, ‖complement (Pi R) x‖ ≤ ‖x‖)
    (cstar : ℝ) (hc : 0 < cstar)
    (hpersistent : ∀ R ε₀, 0 < ε₀ →
      ∃ ε δ : ℝ, 0 < ε ∧ ε < ε₀ ∧ 0 < δ ∧ δ < ε₀ ∧
        cstar ≤ ‖complement (Pi R) (C ε - C δ)‖) :
    ∀ R (K : ℝ → E),
      (∀ ε, complement (Pi R) (K ε) = 0) →
        ¬ CauchyAtZero (fun ε ↦ C ε - K ε) := by
  intro R K hK hC
  obtain ⟨ε₀, hε₀, hsmall⟩ := hC (cstar / 2) (half_pos hc)
  obtain ⟨ε, δ, hε, hεlt, hδ, hδlt, htail⟩ :=
    hpersistent R ε₀ hε₀
  have hfull := hsmall ε δ hε hεlt hδ hδlt
  have heq : complement (Pi R)
      ((C ε - K ε) - (C δ - K δ)) =
      complement (Pi R) (C ε - C δ) := by
    rw [map_sub, map_sub, map_sub, hK ε, hK δ]
    simpa using ((complement (Pi R)).map_sub (C ε) (C δ)).symm
  have hle := hcontract R ((C ε - K ε) - (C δ - K δ))
  rw [heq] at hle
  linarith

/-- Exact finite-collar quotient estimate.  The chosen local subtraction is
`PL_R Pi_R x`; no best-approximation existence is hidden. -/
theorem finite_collar_quotient_bound
    (Lloc : Submodule ℝ E) (Pi PL : ℕ → E →ₗ[ℝ] E)
    (hlocal : ∀ R x, PL R (Pi R x) ∈ Lloc)
    (C : ℝ → E) (μ Θ : ℝ) (R : ℕ) (ε δ : ℝ)
    (htail : ∀ e : ℝ,
      ‖complement (Pi R) (C e)‖ ≤ Real.exp (-μ * R) * Θ) :
    ∃ l : E, l ∈ Lloc ∧
      ‖(C ε - C δ) - l‖ ≤
        ‖complement (PL R) (Pi R (C ε - C δ))‖ +
          2 * Real.exp (-μ * R) * Θ := by
  let x := C ε - C δ
  refine ⟨PL R (Pi R x), hlocal R x, ?_⟩
  have hsplit : x - PL R (Pi R x) =
      complement (PL R) (Pi R x) + complement (Pi R) x := by
    simp [complement, x]
  rw [hsplit]
  calc
    ‖complement (PL R) (Pi R x) + complement (Pi R) x‖
        ≤ ‖complement (PL R) (Pi R x)‖ + ‖complement (Pi R) x‖ :=
          norm_add_le _ _
    _ ≤ ‖complement (PL R) (Pi R x)‖ +
          (‖complement (Pi R) (C ε)‖ +
            ‖complement (Pi R) (C δ)‖) := by
      gcongr
      rw [show x = C ε - C δ by rfl, map_sub]
      exact norm_sub_le _ _
    _ ≤ ‖complement (PL R) (Pi R x)‖ +
          2 * Real.exp (-μ * R) * Θ := by
      have hε := htail ε
      have hδ := htail δ
      linarith

/-- Exponential collars vanish as the integer radius tends to infinity. -/
theorem exponential_tail_eventually_small
    {μ Θ η : ℝ} (hμ : 0 < μ) (hΘ : 0 ≤ Θ) (hη : 0 < η) :
    ∃ R : ℕ, 2 * Real.exp (-μ * R) * Θ < η := by
  by_cases hΘ0 : Θ = 0
  · exact ⟨0, by simp [hΘ0, hη]⟩
  · have hΘpos : 0 < Θ := lt_of_le_of_ne hΘ (Ne.symm hΘ0)
    have hlim : Tendsto (fun R : ℕ ↦ 2 * Real.exp (-μ * R) * Θ)
        atTop (𝓝 0) := by
      have hnat : Tendsto (fun R : ℕ ↦ (R : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have hmul : Tendsto (fun R : ℕ ↦ μ * (R : ℝ)) atTop atTop :=
        hnat.const_mul_atTop hμ
      have hneg : Tendsto (fun R : ℕ ↦ -(μ * (R : ℝ))) atTop atBot :=
        tendsto_neg_atBot_iff.mpr hmul
      have hexp : Tendsto (fun R : ℕ ↦ Real.exp (-(μ * (R : ℝ))))
          atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
      simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hexp.const_mul (2 * Θ))
    have hev : ∀ᶠ R : ℕ in atTop,
        2 * Real.exp (-μ * R) * Θ < η :=
      (tendsto_order.1 hlim).2 _ hη
    exact Filter.Eventually.exists hev

/-- **`thm:GTLOC-contact-tail-alternative`, rescue branch.**  Collarwise
Cauchy residuals plus the exponential tail imply Cauchy convergence in the
quotient by the closed local-counterterm space. -/
theorem exponential_tail_rescues_local_quotient
    (Lloc : Submodule ℝ E) (Pi PL : ℕ → E →ₗ[ℝ] E)
    (hlocal : ∀ R x, PL R (Pi R x) ∈ Lloc)
    (C : ℝ → E) (μ Θ : ℝ) (hμ : 0 < μ) (hΘ : 0 ≤ Θ)
    (htail : ∀ (R : ℕ) (e : ℝ),
      ‖complement (Pi R) (C e)‖ ≤ Real.exp (-μ * R) * Θ)
    (hcollar : ∀ R,
      CauchyAtZero (fun e ↦ complement (PL R) (Pi R (C e)))) :
    QuotientCauchyAtZero Lloc C := by
  intro η hη
  obtain ⟨R, hR⟩ := exponential_tail_eventually_small hμ hΘ (half_pos hη)
  obtain ⟨ε₀, hε₀, hsmall⟩ := hcollar R (η / 2) (half_pos hη)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε δ hε hεlt hδ hδlt
  obtain ⟨l, hl, hbound⟩ := finite_collar_quotient_bound
    Lloc Pi PL hlocal C μ Θ R ε δ (htail R)
  refine ⟨l, hl, lt_of_le_of_lt hbound ?_⟩
  have hsmall' := hsmall ε δ hε hεlt hδ hδlt
  have hlin : complement (PL R) (Pi R (C ε - C δ)) =
      complement (PL R) (Pi R (C ε)) -
        complement (PL R) (Pi R (C δ)) := by
    simp
    abel
  rw [hlin]
  linarith

end

end ContactTailFiniteCollarAlternative
end NCG
