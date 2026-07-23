/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The revision cocycle: quadratic refinement, full extension, projective law

The derived modular revision datum is a projective family `R : 𝐇 → G`
with a `{±1}`-valued multiplier.  We model the sign as a central
involution `ε` and the multiplier as `s : L → L → ℤ/2`, and prove:

* **Theorem `thm:reversible-predictive-revision`** (involutivity):
  additively labelled revisions over an elementary 2-group square to the
  identity (`NCG.revision_involutive`; the `*`-automorphism part is
  `NCG.UCPMap.unit_map_mul`/`unit_map_star`);
* **Proposition `prop:projective-revision` /
  Definition `def:modular-form-main`**: the commutator bicharacter is
  `⁅R_α, R_β⁆ = ε^{ω(α,β)}` with `ω = s + sᵀ`
  (`NCG.RevisionFamily.commutator_eq`), it is well defined
  (`NCG.sgnPow_injective`), and invariant under scalar regauging
  (`NCG.regauge_polar_invariant`);
* **Theorem `thm:revision-quadratic-refinement-main`**: lift squares are
  `R_γ² = ε^{q(γ)}`, `q(γ) = s(γ,γ)`
  (`NCG.RevisionFamily.lift_square`), and for a bilinear `B` the
  diagonal `q` satisfies the quadratic-refinement identity
  `q(α+β) = q(α) + q(β) + ω(α,β)` with `ω` alternating, and `q ≡ 0`
  forces `ω ≡ 0` (`NCG.quadratic_refinement`, `NCG.polar_alt`,
  `NCG.polar_eq_zero_of_diag_zero`);
* **Proposition `prop:full-revision-cocycle-main`**: adjoining the
  temporal generator `J` with exchange pairing `χ` gives the extended
  family `R_{(α,e)} = R_α Jᵉ` with multiplier
  `ŝ((α,e),(β,d)) = s(α,β) + e·χ(β)`
  (`NCG.RevisionFamily.full_cocycle`) and assembled alternating form
  `ω̂ = ω(α,β) + e·χ(β) + d·χ(α)` (`NCG.full_polar_form`);
* **Theorem `thm:revision-central-extension-main`** (kernel step): a
  projectively scalar lift lies in the radical of `ω`
  (`NCG.RevisionFamily.projective_kernel_in_radical`); the extraspecial
  order count `2^{1+dim}` is not formalised. -/

namespace NCG

open scoped commutatorElement

/-- **Theorem `thm:reversible-predictive-revision`** (involutivity core):
additively labelled revisions over an elementary abelian 2-group are
involutive, `Φ_α² = Φ_{2α} = Φ_0 = id`. -/
theorem revision_involutive {L M : Type*} [AddCommGroup L] [Monoid M]
    (Φ : L → M) (h0 : Φ 0 = 1)
    (hadd : ∀ α β, Φ α * Φ β = Φ (α + β))
    (hL2 : ∀ γ : L, γ + γ = 0) (α : L) : Φ α * Φ α = 1 := by
  rw [hadd, hL2, h0]

variable {G : Type*} [Group G]

/-- The `ε`-power of a `ℤ/2` exponent. -/
def sgnPow (ε : G) (a : ZMod 2) : G := ε ^ a.val

@[simp] theorem sgnPow_zero (ε : G) : sgnPow ε 0 = 1 := by
  simp [sgnPow, ZMod.val_zero]

@[simp] theorem sgnPow_one (ε : G) : sgnPow ε 1 = ε := by
  simp [sgnPow, ZMod.val_one]

theorem sgnPow_add {ε : G} (hsq : ε * ε = 1) (a b : ZMod 2) :
    sgnPow ε (a + b) = sgnPow ε a * sgnPow ε b := by
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
    simp [show (1 + 1 : ZMod 2) = 0 from rfl, hsq.symm]

theorem sgnPow_inv {ε : G} (hsq : ε * ε = 1) (a : ZMod 2) :
    (sgnPow ε a)⁻¹ = sgnPow ε a := by
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases a with rfl | rfl
  · simp
  · simp [inv_eq_of_mul_eq_one_left hsq]

/-- The bicharacter is **well defined**
(Definition `def:modular-form-main`): for a nontrivial sign `ε` the
exponent is determined by the commutator value. -/
theorem sgnPow_injective {ε : G} (hε : ε ≠ 1) {a b : ZMod 2}
    (h : sgnPow ε a = sgnPow ε b) : a = b := by
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
    simp_all

/-! ### The projective revision family -/

variable {L : Type*} [AddCommGroup L]

/-- A **`{±1}`-projective revision family**
(Theorem `thm:spatial-multiplier-scalar-main` /
Definition `def:revision-operators-main`): implementers `R`, a central
involutive sign `ε`, and a `ℤ/2`-valued multiplier `s` with
`R_α R_β = ε^{s(α,β)} R_{α+β}`. -/
structure RevisionFamily (G : Type*) [Group G] (L : Type*)
    [AddCommGroup L] where
  R : L → G
  ε : G
  s : L → L → ZMod 2
  hcen : ∀ g : G, Commute ε g
  hsq : ε * ε = 1
  h0 : R 0 = 1
  hmul : ∀ α β, R α * R β = sgnPow ε (s α β) * R (α + β)

namespace RevisionFamily

variable (F : RevisionFamily G L)

/-- **Lift squares** (Theorem `thm:revision-quadratic-refinement-main`,
operator half): `R_γ² = ε^{q(γ)}` with `q(γ) = s(γ,γ)`. -/
theorem lift_square (hL2 : ∀ γ : L, γ + γ = 0) (γ : L) :
    F.R γ * F.R γ = sgnPow F.ε (F.s γ γ) := by
  rw [F.hmul, hL2, F.h0, mul_one]

/-- **The projective revision law**
(Proposition `prop:projective-revision` /
Definition `def:modular-form-main`): the commutator is the `{±1}`
bicharacter of the polar form,
`⁅R_α, R_β⁆ = ε^{s(α,β) + s(β,α)}`. -/
theorem commutator_eq (α β : L) :
    ⁅F.R α, F.R β⁆ = sgnPow F.ε (F.s α β + F.s β α) := by
  have h1 := F.hmul α β
  have h2 := F.hmul β α
  rw [add_comm β α] at h2
  have hform : ⁅F.R α, F.R β⁆
      = (F.R α * F.R β) * (F.R β * F.R α)⁻¹ := by
    rw [commutatorElement_def, mul_inv_rev]
    group
  rw [hform, h1, h2, mul_inv_rev, sgnPow_inv F.hsq]
  calc sgnPow F.ε (F.s α β) * F.R (α + β)
        * ((F.R (α + β))⁻¹ * sgnPow F.ε (F.s β α))
      = sgnPow F.ε (F.s α β) * sgnPow F.ε (F.s β α) := by group
    _ = sgnPow F.ε (F.s α β + F.s β α) := (sgnPow_add F.hsq _ _).symm

/-- **Theorem `thm:revision-central-extension-main`** (kernel step): a
lift commuting with every other lift has trivial polar pairing — the
projective kernel lies in `rad ω`. -/
theorem projective_kernel_in_radical (hε : F.ε ≠ 1) (γ : L)
    (hcomm : ∀ β, Commute (F.R γ) (F.R β)) (β : L) :
    F.s γ β + F.s β γ = 0 := by
  have h := F.commutator_eq γ β
  rw [commutatorElement_eq_one_iff_commute.mpr (hcomm β)] at h
  exact (sgnPow_injective hε (a := 0)
    (by rw [sgnPow_zero, h])).symm

end RevisionFamily

/-! ### The quadratic refinement over `𝔽₂` -/

section Quadratic

variable {B : L → L → ZMod 2}

/-- **Theorem `thm:revision-quadratic-refinement-main`** (polarisation):
for bilinear `B`, the diagonal `q(γ) = B(γ,γ)` refines the polar form
`ω = B + Bᵀ`:  `q(α+β) = q(α) + q(β) + ω(α,β)`. -/
theorem quadratic_refinement
    (hBl : ∀ α β γ, B (α + β) γ = B α γ + B β γ)
    (hBr : ∀ α β γ, B α (β + γ) = B α β + B α γ) (α β : L) :
    B (α + β) (α + β)
      = B α α + B β β + (B α β + B β α) := by
  rw [hBl, hBr, hBr]
  abel

/-- The polar form is alternating. -/
theorem polar_alt (γ : L) : B γ γ + B γ γ = 0 :=
  CharTwo.add_self_eq_zero _

/-- If the quadratic function vanishes identically, so does its polar
form (Theorem `thm:revision-quadratic-refinement-main`, last claim). -/
theorem polar_eq_zero_of_diag_zero
    (hBl : ∀ α β γ, B (α + β) γ = B α γ + B β γ)
    (hBr : ∀ α β γ, B α (β + γ) = B α β + B α γ)
    (hq : ∀ γ, B γ γ = 0) (α β : L) : B α β + B β α = 0 := by
  have h := quadratic_refinement hBl hBr α β
  rw [hq, hq, hq, zero_add, zero_add] at h
  exact h.symm

/-- **Proposition `prop:projective-revision`** (gauge invariance): a
scalar regauging shifts the multiplier by the symmetric coboundary
`δμ(α,β) = μ(α)+μ(β)+μ(α+β)`, which cancels from the polar form. -/
theorem regauge_polar_invariant (s : L → L → ZMod 2) (μ : L → ZMod 2)
    (α β : L) :
    (s α β + (μ α + μ β + μ (α + β)))
        + (s β α + (μ β + μ α + μ (β + α)))
      = s α β + s β α := by
  rw [add_comm β α]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  linear_combination h2 (μ α) + h2 (μ β) + h2 (μ (α + β))

end Quadratic

/-! ### The full revision group (`prop:full-revision-cocycle-main`) -/

namespace RevisionFamily

variable (F : RevisionFamily G L)

/-- The **extended family** `R_{(α,ε)} = R_α J^ε` over `𝐇 = H ⊕ ⟨t⟩`
(Proposition `prop:full-revision-cocycle-main`). -/
def fullR (J : G) (p : L × ZMod 2) : G := F.R p.1 * sgnPow J p.2

/-- **Proposition `prop:full-revision-cocycle-main`**: the extended
family is projective with multiplier
`ŝ((α,e),(β,d)) = s(α,β) + e·χ(β)` — the spatial block and the
canonical temporal row assemble into one scalar cocycle on `𝐇`. -/
theorem full_cocycle (J : G) (χ : L → ZMod 2) (hJ2 : J * J = 1)
    (hex : ∀ β, J * F.R β = sgnPow F.ε (χ β) * (F.R β * J))
    (α β : L) (e d : ZMod 2) :
    F.fullR J (α, e) * F.fullR J (β, d)
      = sgnPow F.ε (F.s α β + e * χ β)
          * F.fullR J (α + β, e + d) := by
  have hJmove : ∀ (e : ZMod 2) (β : L),
      sgnPow J e * F.R β
        = sgnPow F.ε (e * χ β) * (F.R β * sgnPow J e) := by
    intro e β
    have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hcases e with rfl | rfl
    · simp
    · simpa using hex β
  unfold fullR
  calc F.R α * sgnPow J e * (F.R β * sgnPow J d)
      = F.R α * (sgnPow J e * F.R β) * sgnPow J d := by group
    _ = F.R α * (sgnPow F.ε (e * χ β) * (F.R β * sgnPow J e))
        * sgnPow J d := by rw [hJmove]
    _ = sgnPow F.ε (e * χ β) * (F.R α * F.R β)
        * (sgnPow J e * sgnPow J d) := by
        have hc := (F.hcen (F.R α)).symm
        have hc2 : F.R α * sgnPow F.ε (e * χ β)
            = sgnPow F.ε (e * χ β) * F.R α := by
          have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
          rcases hcases (e * χ β) with h | h <;> rw [h]
          · simp
          · simpa using (F.hcen (F.R α)).symm.eq
        calc F.R α * (sgnPow F.ε (e * χ β) * (F.R β * sgnPow J e))
            * sgnPow J d
            = (F.R α * sgnPow F.ε (e * χ β)) * F.R β
              * (sgnPow J e * sgnPow J d) := by group
          _ = (sgnPow F.ε (e * χ β) * F.R α) * F.R β
              * (sgnPow J e * sgnPow J d) := by rw [hc2]
          _ = sgnPow F.ε (e * χ β) * (F.R α * F.R β)
              * (sgnPow J e * sgnPow J d) := by group
    _ = sgnPow F.ε (e * χ β)
        * (sgnPow F.ε (F.s α β) * F.R (α + β))
        * sgnPow J (e + d) := by
        rw [F.hmul, sgnPow_add hJ2]
    _ = sgnPow F.ε (F.s α β + e * χ β)
        * (F.R (α + β) * sgnPow J (e + d)) := by
        rw [add_comm (F.s α β) (e * χ β), sgnPow_add F.hsq]
        group

end RevisionFamily

/-- **Proposition `prop:full-revision-cocycle-main`** (assembled polar
form): the alternating form of the extended multiplier is
`ω̂((α,e),(β,d)) = ω(α,β) + e·χ(β) + d·χ(α)`. -/
theorem full_polar_form (s : L → L → ZMod 2) (χ : L → ZMod 2)
    (α β : L) (e d : ZMod 2) :
    (s α β + e * χ β) + (s β α + d * χ α)
      = (s α β + s β α) + (e * χ β + d * χ α) := by
  abel

end NCG
