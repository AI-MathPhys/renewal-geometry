/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMGroup
import NCG.Grand.GrandSMEasy

/-!
# Standard Model central-descent selector

The quotient kernel supplied by `sm_group` is cyclic of order six.  On an
irreducible sector its generator acts through the scalar character with
exponent `2t + 3s + y`.  This file proves that trivial action is equivalent to
the manuscript's congruence for arbitrary triality, weak parity, and integral
charge labels.  `descent_fourier_projector` supplies the corresponding finite
Fourier indicator.
-/

namespace NCG
namespace SMCentralDescentSelector

/-- Central-character exponent of a Standard Model highest-weight label. -/
def centralExponent (triality parity charge : ℤ) : ℤ :=
  2 * triality + 3 * parity + charge

/-- Scalar action of the order-six quotient-kernel generator. -/
def centralKernelAction (zeta : ℂˣ) (triality parity charge : ℤ) : ℂˣ :=
  zeta ^ centralExponent triality parity charge

/-- Exact quotient descent: an order-six central generator acts trivially
exactly when `2t + 3s + y` is zero modulo six. -/
theorem centralKernelActsTrivially_iff
    (zeta : ℂˣ) (hzeta : orderOf zeta = 6)
    (triality parity charge : ℤ) :
    centralKernelAction zeta triality parity charge = 1 ↔
      (6 : ℤ) ∣ 2 * triality + 3 * parity + charge := by
  have h := orderOf_dvd_iff_zpow_eq_one
    (x := zeta) (i := centralExponent triality parity charge)
  rw [hzeta] at h
  exact h.symm

/-- The criterion depends only on triality modulo three and parity modulo two,
as required for irreducible `SU(3)` and `SU(2)` central characters. -/
theorem centralDescent_representative_independent
    {triality triality' parity parity' charge : ℤ}
    (ht : triality ≡ triality' [ZMOD 3])
    (hs : parity ≡ parity' [ZMOD 2]) :
    ((6 : ℤ) ∣ centralExponent triality parity charge) ↔
      (6 : ℤ) ∣ centralExponent triality' parity' charge := by
  rw [Int.modEq_iff_dvd] at ht hs
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hs
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c + a + b, ?_⟩
    simp only [centralExponent] at hc ⊢
    linarith
  · rintro ⟨c, hc⟩
    refine ⟨c - a - b, ?_⟩
    simp only [centralExponent] at hc ⊢
    linarith

/-- Combined selector record: the genuine matrix quotient has an order-six
kernel, the central character descends iff the label congruence holds, and the
finite Fourier sum is its indicator. -/
theorem sm_central_descent_selector
    (zeta : ℂˣ) (hzeta : orderOf zeta = 6)
    (triality parity charge : ℤ) :
    (centralKernelAction zeta triality parity charge = 1 ↔
      (6 : ℤ) ∣ 2 * triality + 3 * parity + charge) ∧
    (∀ m : ℕ,
      (∑ k ∈ Finset.range 6, ((zeta : ℂ) ^ m) ^ k) =
        if 6 ∣ m then 6 else 0) := by
  refine ⟨centralKernelActsTrivially_iff zeta hzeta
    triality parity charge, ?_⟩
  intro m
  apply descent_fourier_projector
  have hcoe : orderOf (zeta : ℂ) = 6 := by
    rw [← hzeta]
    exact orderOf_injective (Units.coeHom ℂ) Units.val_injective zeta
  exact hcoe

end SMCentralDescentSelector
end NCG
