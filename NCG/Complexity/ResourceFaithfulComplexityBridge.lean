/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Complexity.FiniteBooleanCircuits

/-!
# Resource-faithful circuit-complexity bridge

This is the exact conditional content of `thm:PvsNP-resource-bridge`.
`P` and `NP` are represented as classes of Boolean language families;
NP-completeness includes membership in `NP` (the reduction/hardness witness is
retained as an abstract relation because it is not used by this implication).
The standard inclusion `P ⊆ P/poly` is an explicit hypothesis.

The proof does not abstract circuit size to an arbitrary scalar: it uses the
least gate count of the concrete finite Boolean circuits defined in
`FiniteBooleanCircuits`.
-/

namespace NCG.Complexity

/-- An NP-complete language relative to a declared reduction relation. -/
structure IsNPComplete (NP : Set LanguageFamily)
    (Reduces : LanguageFamily → LanguageFamily → Prop)
    (L : LanguageFamily) : Prop where
  memNP : L ∈ NP
  hard : ∀ A ∈ NP, Reduces A L

/-- A language lies in `P/poly` exactly when it has a nonuniform polynomial
circuit family. -/
def InPPoly : Set LanguageFamily :=
  {L | HasPolynomialCircuits L}

/-- `thm:PvsNP-resource-bridge`.

The displayed comparison is stated in its literal real-division form. The
positive polynomial denominator converts it to
`R(n) ≤ p(n) * CircuitSize(f_n)`. A hypothetical polynomial circuit family
would then polynomially bound `R`, contradicting its declared growth. -/
theorem resource_faithful_complexity_bridge
    (P NP : Set LanguageFamily)
    (Reduces : LanguageFamily → LanguageFamily → Prop)
    (L : LanguageFamily) (hcomplete : IsNPComplete NP Reduces L)
    (hPpoly : P ⊆ InPPoly)
    (R p : ℕ → ℕ)
    (hp : PolynomiallyBounded p) (hpPos : ∀ n, 0 < p n)
    (hcompare : ∀ n,
      (R n : ℝ) / (p n : ℝ) ≤ (circuitSize (L n) : ℝ))
    (hsuper : GrowsFasterThanEveryPolynomial R) :
    L ∉ InPPoly ∧ P ≠ NP := by
  have hnotPoly : L ∉ InPPoly := by
    rintro ⟨C, k, hcircuits⟩
    obtain ⟨D, ell, hpBound⟩ := hp
    obtain ⟨n, hnLarge⟩ := hsuper (D * C) (ell + k)
    obtain ⟨c, hc, hcSize⟩ := hcircuits n
    have hmin : circuitSize (L n) ≤ c.gateCount :=
      circuitSize_le_gateCount (L n) c hc
    have hcrossReal : (R n : ℝ) ≤
        (p n : ℝ) * (circuitSize (L n) : ℝ) := by
      exact (div_le_iff₀' (by exact_mod_cast hpPos n)).mp (hcompare n)
    have hcross : R n ≤ p n * circuitSize (L n) := by
      exact_mod_cast hcrossReal
    have hpoly : R n ≤ (D * C) * (n + 1) ^ (ell + k) := by
      calc
        R n ≤ p n * circuitSize (L n) := hcross
        _ ≤ (D * (n + 1) ^ ell) * (C * (n + 1) ^ k) :=
          Nat.mul_le_mul (hpBound n) (hmin.trans hcSize)
        _ = (D * C) * (n + 1) ^ (ell + k) := by
          rw [pow_add]
          ac_rfl
    exact (Nat.not_lt_of_ge hpoly) hnLarge
  refine ⟨hnotPoly, ?_⟩
  intro hclasses
  have hLP : L ∈ P := by
    rw [hclasses]
    exact hcomplete.memNP
  exact hnotPoly (hPpoly hLP)

end NCG.Complexity
