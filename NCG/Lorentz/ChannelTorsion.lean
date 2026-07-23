/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.DiscreteCartan
import NCG.Lorentz.StationaryExchange

/-!
# The channel-composition torsion theorem, revised hypotheses

Covers `thm:channel-torsion` from `manuscripts/lorentzian_emergence/lorentzian_emergence.tex` in its
revised form: the reset channels are assumed to lie in the
**exchange-covariant stationary diamond phase**
(`ass:stationary-diamond`), and first-moment plaquette closure is
*derived* from it via the stationary exchange theorem
(`thm:stationary-exchange`), rather than being postulated.

Concretely: the translational plaquette defect is assumed to have
the diamond expansion `h²·(stationary mean of the exchange-odd
defect) + h³·C` at two distinct nonzero scales.  The stationary
exchange theorem kills the `h²`-coefficient, the exact plaquette
split (`plaquette_defect_eq`) identifies it with the discrete
torsion `T = D_ie_j − D_je_i + γ_ie_j − γ_je_i` plus a cubic
remainder, and two-scale coefficient extraction
(`coeff_extraction`) forces `T = 0`.  The rotational (curvature)
defect is untouched, and together with the derived metric
compatibility (`prop:second-moment-isometry` + `prop:iso-metric`)
the discrete fundamental theorem (`thm:fundamental`,
`NCG.cartan_uniqueness`) selects the unique Levi–Civita
connection. -/

namespace NCG

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [NoZeroSMulDivisors ℝ V]
  {D : Type*} [Fintype D] [DecidableEq D]

/-- **Theorem `thm:channel-torsion` (revised)**: for reset channels
whose resolved two-reset diamond records lie in the primitive
exchange-covariant stationary phase, the translational plaquette
defect closes and the discrete torsion vanishes; no constraint is
placed on the rotational record. -/
theorem channel_torsion_of_stationary_diamond
    {P : D → D → ℝ} {s : D → D} {π : D → ℝ} {m : ℕ}
    (hs : Function.Involutive s) (hrow : ∀ a, ∑ b, P a b = 1)
    (hcov : ∀ a b, P (s a) (s b) = P a b)
    (hprim : ∀ a b, 0 < kernelPow P m a b)
    (hπ1 : ∑ a, π a = 1) (hπ : ∀ b, ∑ a, π a * P a b = π b)
    (dtr : D → V) (hodd : ∀ a, dtr (s a) = -dtr a)
    (ei ej Dij Dji : V) (γi γj : V →ₗ[ℝ] V) (Cc : V)
    {h₁ h₂ : ℝ} (hne₁ : h₁ ≠ 0) (hne₂ : h₂ ≠ 0) (hdist : h₁ ≠ h₂)
    (hexp : ∀ h ∈ ({h₁, h₂} : Set ℝ),
      plaquetteDefect h ei ej Dij γi - plaquetteDefect h ej ei Dji γj
        = h ^ 2 • (∑ a, π a • dtr a) + h ^ 3 • Cc) :
    Dij - Dji + γi ej - γj ei = 0 := by
  -- the stationary mean of the exchange-odd defect vanishes
  have hmean : (∑ a, π a • dtr a) = 0 :=
    stationary_exchange_mean_zero hs hrow hcov hprim hπ1 hπ dtr hodd
  -- hence first-moment plaquette closure at both scales
  have hclosure : ∀ h ∈ ({h₁, h₂} : Set ℝ),
      plaquetteDefect h ei ej Dij γi - plaquetteDefect h ej ei Dji γj
        = h ^ 3 • Cc := by
    intro h hh
    rw [hexp h hh, hmean, smul_zero, zero_add]
  have e₁ := hclosure h₁ (Or.inl rfl)
  have e₂ := hclosure h₂ (Or.inr rfl)
  rw [plaquette_defect_eq] at e₁ e₂
  -- fold into vanishing polynomial data and extract the h² coefficient
  have f₁ : (h₁ ^ 2) • (Dij - Dji + γi ej - γj ei)
      + (h₁ ^ 3) • (γi Dij - γj Dji - Cc) = 0 := by
    have hgoal : (h₁ ^ 2) • (Dij - Dji + γi ej - γj ei)
        + (h₁ ^ 3) • (γi Dij - γj Dji - Cc)
        = ((h₁ ^ 2) • (Dij - Dji + γi ej - γj ei)
          + (h₁ ^ 3) • (γi Dij - γj Dji)) - (h₁ ^ 3) • Cc := by
      module
    rw [hgoal, e₁, sub_self]
  have f₂ : (h₂ ^ 2) • (Dij - Dji + γi ej - γj ei)
      + (h₂ ^ 3) • (γi Dij - γj Dji - Cc) = 0 := by
    have hgoal : (h₂ ^ 2) • (Dij - Dji + γi ej - γj ei)
        + (h₂ ^ 3) • (γi Dij - γj Dji - Cc)
        = ((h₂ ^ 2) • (Dij - Dji + γi ej - γj ei)
          + (h₂ ^ 3) • (γi Dij - γj Dji)) - (h₂ ^ 3) • Cc := by
      module
    rw [hgoal, e₂, sub_self]
  exact (coeff_extraction hne₁ hne₂ hdist f₁ f₂).1

end NCG
