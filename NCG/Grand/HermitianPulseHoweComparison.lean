/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import NCG.Grand.HermitianExponentialRemainder
import NCG.Grand.PulseHoweComparison
import NCG.Grand.StoreNativePrincipalLog

/-!
# Hermitian pulse-to-Howe comparison

This module discharges the exponential premise in `PulseHoweComparison`
directly from a Hermitian generator.  On the principal spectral window it also
proves exact equality of the pulse and generator commutants.
-/

namespace NCG

section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The sharp pulse remainder for the manuscript convention
`V_t = exp(-i t G)`. -/
theorem norm_expUnitary_pulse_remainder_le
    (G : selfAdjoint A) (t : ℝ) :
    ‖(selfAdjoint.expUnitary ((-t) • G) : A) - 1 -
        ((-Complex.I * t : ℂ) • (G : A))‖ ≤
      |t| ^ 2 * ‖(G : A)‖ ^ 2 / 2 := by
  let x : A := (-Complex.I) • (G : A)
  have hx : x ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff]
    simp [x, G.prop.star_eq]
  have h := norm_exp_real_smul_skew_sub_one_sub_le x hx t
  have hpulse : (selfAdjoint.expUnitary ((-t) • G) : A) =
      NormedSpace.exp (t • x) := by
    rw [selfAdjoint.expUnitary_coe]
    congr 1
    dsimp [x]
    module
  have hlinear : ((-Complex.I * t : ℂ) • (G : A)) = t • x := by
    dsimp [x]
    module
  rw [hpulse, hlinear]
  simpa [x, norm_smul] using h

/-- The first boxed pulse estimate, fully derived from a Hermitian generator. -/
theorem norm_expUnitary_finitePulseDerivation_sub_generator_le
    (G : selfAdjoint A) (t : ℝ) (ht : t ≠ 0) :
    ‖finitePulseDerivation t (selfAdjoint.expUnitary ((-t) • G) : A) -
        generatorDerivation (G : A)‖ ≤ |t| * ‖(G : A)‖ ^ 2 := by
  let R : A := (selfAdjoint.expUnitary ((-t) • G) : A) - 1 -
    ((-Complex.I * t : ℂ) • (G : A))
  apply norm_finitePulseDerivation_sub_generator_le t ‖(G : A)‖ ht
    (norm_nonneg _) _ _ R
  · dsimp [R]
    noncomm_ring
  · exact norm_expUnitary_pulse_remainder_le G t

private theorem star_unitary_commutes_of_commutes
    (u : unitary A) (a : A) (h : Commute (u : A) a) :
    Commute (star (u : A)) a := by
  rw [Commute] at h ⊢
  have huL : star (u : A) * (u : A) = 1 := u.prop.1
  have huR : (u : A) * star (u : A) = 1 := u.prop.2
  calc
    star (u : A) * a =
        (star (u : A) * a) * ((u : A) * star (u : A)) := by
      rw [huR, mul_one]
    _ = star (u : A) * (a * (u : A)) * star (u : A) := by
      simp only [mul_assoc]
    _ = star (u : A) * ((u : A) * a) * star (u : A) := by rw [h]
    _ = a * star (u : A) := by
      rw [← mul_assoc, huL, one_mul]

/-- Inside the principal logarithm window, commuting with the finite pulse is
equivalent to commuting with its Hermitian generator. -/
theorem commute_expUnitary_iff_commute_generator
    (G : selfAdjoint A) (t : ℝ) (ht : t ≠ 0)
    (hbranch : ‖(-t) • G‖ < Real.pi) (a : A) :
    Commute a (selfAdjoint.expUnitary ((-t) • G) : A) ↔
      Commute a (G : A) := by
  let u : unitary A := selfAdjoint.expUnitary ((-t) • G)
  constructor
  · intro hau
    have hua : Commute (u : A) a := by simpa [u] using hau.symm
    have hsua : Commute (star (u : A)) a :=
      star_unitary_commutes_of_commutes u a hua
    have harg : Commute (Unitary.argSelfAdjoint u : A) a := by
      simpa only [Unitary.argSelfAdjoint_coe] using
        hua.cfc hsua (fun z : ℂ => (Complex.arg z : ℂ))
    have hlog : Commute (principalUnitaryLog u) a := by
      exact harg.smul_left Complex.I
    have hscaled : Commute
        ((Complex.I / t : ℂ) • principalUnitaryLog u) a :=
      hlog.smul_left (Complex.I / t)
    rw [principalUnitaryLog_reconstructs_generator G t ht hbranch] at hscaled
    exact hscaled.symm
  · intro haG
    change Commute a
      (NormedSpace.exp (Complex.I • (((-t : ℝ) : ℂ) • (G : A))))
    exact ((haG.smul_right (((-t : ℝ) : ℂ))).smul_right Complex.I).exp_right

/-- Set-level equality of the pulse and generator commutants on the principal
spectral window. -/
theorem expUnitary_commutant_eq_generator_commutant
    (G : selfAdjoint A) (t : ℝ) (ht : t ≠ 0)
    (hbranch : ‖(-t) • G‖ < Real.pi) :
    {a : A | Commute a (selfAdjoint.expUnitary ((-t) • G) : A)} =
      {a : A | Commute a (G : A)} := by
  ext a
  exact commute_expUnitary_iff_commute_generator G t ht hbranch a

end

end NCG
