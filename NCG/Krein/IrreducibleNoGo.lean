/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.FundamentalSymmetry

/-!
# The irreducible positive-sector no-go

The updated manuscript sharpens the positivity obstruction into an
irreducible-commutant statement (**irreducible positive-sector no-go**,
`thm:irreducible-positive-no-go`): if the natural positive renewal algebra
`𝔅₊` acts with trivial commutant (`𝔅₊' = ℂ·1`,
Assumption `ass:irreducible-positive-sector`), then every fundamental
symmetry that commutes with `𝔅₊` is scalar,

`J = +1  or  J = −1`,

so its form is definite and no Lorentzian splitting can be extracted from
the positive sector alone.  Complete positivity by itself does *not* give
this (a reducible positive representation may admit non-scalar commuting
involutions); the content is the trivial-commutant hypothesis.

## Main results

* `NCG.IsFundamentalSymmetry.eq_one_or_neg_one_of_scalar` — a scalar
  fundamental symmetry is `±1`;
* `NCG.IsFundamentalSymmetry.eq_one_or_neg_one_of_mem_centralizer` — the
  no-go theorem: with a scalar commutant, any fundamental symmetry in the
  commutant of the positive algebra is `±1`
  (`thm:irreducible-positive-no-go`, `cor:cp-positivity-boundary`).
-/

namespace NCG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

namespace IsFundamentalSymmetry

/-- A **scalar** fundamental symmetry is `+1` or `−1`: the involution
condition forces the scalar to be a square root of unity. -/
theorem eq_one_or_neg_one_of_scalar {J : H →L[ℂ] H}
    (hJ : IsFundamentalSymmetry J) {c : ℂ}
    (hc : J = c • (1 : H →L[ℂ] H)) :
    J = 1 ∨ J = -1 := by
  -- the involution gives `c² = 1` after evaluating on a nonzero vector
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hsq : (c * c) • x = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hJ.mul_self
    simp only [mul_apply_eq_comp, one_apply_eq_self,
      hc, smul_apply] at h
    simpa [smul_smul] using h
  have hc2 : c * c = 1 := by
    have h0 : (c * c - 1) • x = 0 := by
      rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · linear_combination h
    · exact absurd h hx
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · left
    rw [hc, h, one_smul]
  · right
    rw [hc, h, neg_smul, one_smul]

/-- **The irreducible positive-sector no-go**
(`thm:irreducible-positive-no-go`): if every operator commuting with the
positive renewal algebra `S` is scalar (trivial commutant,
Assumption `ass:irreducible-positive-sector`), then every fundamental
symmetry commuting with `S` is `+1` or `−1`.  Its Krein form is definite,
so the natural irreducible positive representation does not determine a
Lorentzian splitting: signature must come from the signed sector. -/
theorem eq_one_or_neg_one_of_mem_centralizer {J : H →L[ℂ] H}
    (hJ : IsFundamentalSymmetry J) (S : Set (H →L[ℂ] H))
    (hcomm : ∀ T ∈ Set.centralizer S, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hJS : J ∈ Set.centralizer S) :
    J = 1 ∨ J = -1 := by
  obtain ⟨c, hc⟩ := hcomm J hJS
  exact hJ.eq_one_or_neg_one_of_scalar hc

end IsFundamentalSymmetry

end NCG
