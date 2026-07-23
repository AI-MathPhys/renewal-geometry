/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.ProjectiveDefect
import NCG.Algebra.RevisionCocycle

/-!
# The scalar projective law, derived

**Theorem `thm:revision-structure-main` (repair)**: previously the
multiplicative law `R_α·R_β = ε^{s(α,β)}·R_{α+β}` entered the library
only as the structure field `RevisionFamily.hmul` — an *input*.  This
file closes that gap: `NCG.revisionFamilyOfDefect` *constructs* a
`RevisionFamily` from the primitive implementer data, with `hmul`
**derived** rather than assumed.

The derivation chain, matching the manuscript's proof:

1. implementers with a common conjugation action have **central**
   projective defects — `NCG.projDefect_mem_center_of_ad` (the Schur
   step, proved);
2. central defects satisfy the **cocycle identity** —
   `NCG.projDefect_cocycle` (proved);
3. on the finite factor the centre is the scalars, and the Hermitian
   normalization pins each defect to `{1, ε}` — this scalar-centre
   input (`hdef` below) is the *only* remaining hypothesis, exactly
   the finite-factor/Wedderburn step every note in this chapter
   already discloses;
4. from `hdef`, the sign `s(α,β)` is *defined* by which value the
   defect takes, and the law `R_α·R_β = ε^{s(α,β)}·R_{α+β}` follows
   from the defect's defining property `projDefect_spec` — this is
   `hmul`, now a theorem of the construction
   (`NCG.revisionFamilyOfDefect_hmul`).

Every downstream `RevisionFamily` theorem (cocycle formula, quadratic
refinement, commutator bicharacter, twirl invariance, …) therefore
applies to any implementer system satisfying 1–3, with no
multiplicative law assumed.
-/

namespace NCG

variable {G : Type*} [Group G] {L : Type*} [AddCommGroup L]

open Classical in
/-- **The scalar projective law, derived**
(Theorem `thm:revision-structure-main`): given implementers `R` with
identity normalization and the scalar-centre input — every projective
defect lies in `{1, ε}` for a central involution `ε` — the
`RevisionFamily` structure is *constructed*, its multiplier
`s(α,β)` read off from the defect, and the multiplicative law `hmul`
derived from `projDefect_spec` rather than assumed. -/
noncomputable def revisionFamilyOfDefect (R : L → G) (ε : G)
    (hcen : ∀ g : G, Commute ε g) (hsq : ε * ε = 1) (h0 : R 0 = 1)
    (hdef : ∀ α β, projDefect R α β = 1 ∨ projDefect R α β = ε) :
    RevisionFamily G L where
  R := R
  ε := ε
  s := fun α β => if projDefect R α β = 1 then 0 else 1
  hcen := hcen
  hsq := hsq
  h0 := h0
  hmul := by
    intro α β
    by_cases h1 : projDefect R α β = 1
    · rw [if_pos h1, sgnPow_zero, one_mul, projDefect_spec R α β, h1,
        one_mul]
    · have h : projDefect R α β = ε := (hdef α β).resolve_left h1
      have hval : sgnPow ε (1 : ZMod 2) = ε := by
        rw [sgnPow, show (1 : ZMod 2).val = 1 from rfl, pow_one]
      rw [if_neg h1, hval, projDefect_spec R α β, h]

/-- The constructed family's implementers are the given ones — nothing
is replaced in the construction. -/
theorem revisionFamilyOfDefect_R (R : L → G) (ε : G)
    (hcen : ∀ g : G, Commute ε g) (hsq : ε * ε = 1) (h0 : R 0 = 1)
    (hdef : ∀ α β, projDefect R α β = 1 ∨ projDefect R α β = ε) :
    (revisionFamilyOfDefect R ε hcen hsq h0 hdef).R = R := rfl

/-- **`hmul` as a theorem**: the multiplicative law
`R_α·R_β = ε^{s(α,β)}·R_{α+β}` holds for the *given* implementers with
the *derived* multiplier — the projective law is an output of the
defect analysis, not an input. -/
theorem revisionFamilyOfDefect_hmul (R : L → G) (ε : G)
    (hcen : ∀ g : G, Commute ε g) (hsq : ε * ε = 1) (h0 : R 0 = 1)
    (hdef : ∀ α β, projDefect R α β = 1 ∨ projDefect R α β = ε)
    (α β : L) :
    R α * R β
      = sgnPow ε ((revisionFamilyOfDefect R ε hcen hsq h0 hdef).s α β)
        * R (α + β) :=
  (revisionFamilyOfDefect R ε hcen hsq h0 hdef).hmul α β

open Classical in
/-- The derived multiplier reads off the defect: `s(α,β) = 0` exactly
when the defect is trivial. -/
theorem revisionFamilyOfDefect_s_eq_zero_iff (R : L → G) (ε : G)
    (hcen : ∀ g : G, Commute ε g) (hsq : ε * ε = 1) (h0 : R 0 = 1)
    (hdef : ∀ α β, projDefect R α β = 1 ∨ projDefect R α β = ε)
    (α β : L) :
    (revisionFamilyOfDefect R ε hcen hsq h0 hdef).s α β = 0
      ↔ projDefect R α β = 1 := by
  have hs : (revisionFamilyOfDefect R ε hcen hsq h0 hdef).s α β
      = if projDefect R α β = 1 then 0 else 1 := rfl
  rw [hs]
  constructor
  · intro h
    by_contra h1
    rw [if_neg h1] at h
    exact one_ne_zero h
  · intro h1
    rw [if_pos h1]

end NCG
