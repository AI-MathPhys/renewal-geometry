/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.KMSDual

/-!
# Detailed balance, cancellation current, and composition defects

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:current` — KMS detailed balance `Φ = Φ^♯` and the
  renewal/anti-renewal cancellation current `𝒥_ρ(Φ) = Φ − Φ^♯`;
* `thm:cancellation-criterion` — `𝒥 = 0` iff detailed balance; the
  current is KMS anti-self-adjoint; the adjoint form
  `⟨a, 𝒥b⟩ = −⟨𝒥a, b⟩`; and the diagonal cancellation
  `⟨a, 𝒥a⟩ = 0` for self-adjoint `a`;
* `thm:current-composition` — both displayed forms of
  `𝒥(Φ∘Ψ) = 𝒥(Φ)∘Ψ + Φ^♯∘𝒥(Ψ) + [Φ^♯,Ψ^♯]`, the commutator
  being the noncommutative curvature term;
* `cor:balanced-product` — for balanced factors
  `𝒥(Φ∘Ψ) = [Φ,Ψ]`; the composite is balanced iff the factors
  commute; convex combinations and powers of balanced maps stay
  balanced.
-/

namespace NCG.Upstream

open NCG

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A]

section Current

variable (τ : A →ₗ[ℂ] ℂ) (σ σi : A)
variable (hτc : ∀ x y : A, τ (x * y) = τ (y * x))
variable (hτs : ∀ x : A, τ (star x) = star (τ x))
variable (hσ : star σ = σ) (hσi : σ * σi = 1) (hiσ : σi * σ = 1)

/-- **Definition `def:current` (detailed balance)**: `Φ = Φ^♯`. -/
def KMSDetailedBalance (Φ Φstar : A →ₗ[ℂ] A) : Prop :=
  Φ = antiDual σ σi Φstar

/-- **Definition `def:current` (cancellation current)**:
`𝒥_ρ(Φ) = Φ − Φ^♯`. -/
def kmsCurrent (Φ Φstar : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  Φ - antiDual σ σi Φstar

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:cancellation-criterion` (i)**: the current
vanishes exactly at detailed balance. -/
theorem kmsCurrent_eq_zero_iff (Φ Φstar : A →ₗ[ℂ] A) :
    kmsCurrent σ σi Φ Φstar = 0 ↔
      KMSDetailedBalance σ σi Φ Φstar :=
  sub_eq_zero

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- The anti-renewal dual is linear in the predual: differences pass
through. -/
theorem antiDual_sub (f g : A →ₗ[ℂ] A) :
    antiDual σ σi (f - g) = antiDual σ σi f - antiDual σ σi g := by
  apply LinearMap.ext
  intro a
  change σi * ((f - g) (σ * a * σ)) * σi = _
  rw [LinearMap.sub_apply]
  change σi * (f (σ * a * σ) - g (σ * a * σ)) * σi
      = σi * f (σ * a * σ) * σi - σi * g (σ * a * σ) * σi
  noncomm_ring

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem antiDual_add (f g : A →ₗ[ℂ] A) :
    antiDual σ σi (f + g) = antiDual σ σi f + antiDual σ σi g := by
  apply LinearMap.ext
  intro a
  change σi * ((f + g) (σ * a * σ)) * σi = _
  rw [LinearMap.add_apply]
  change σi * (f (σ * a * σ) + g (σ * a * σ)) * σi
      = σi * f (σ * a * σ) * σi + σi * g (σ * a * σ) * σi
  noncomm_ring

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem antiDual_smul (c : ℂ) (f : A →ₗ[ℂ] A) :
    antiDual σ σi (c • f) = c • antiDual σ σi f := by
  apply LinearMap.ext
  intro a
  change σi * ((c • f) (σ * a * σ)) * σi = _
  rw [LinearMap.smul_apply]
  change σi * (c • f (σ * a * σ)) * σi = c • (σi * f (σ * a * σ) * σi)
  rw [mul_smul_comm, smul_mul_assoc]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- The dual of the identity is the identity. -/
theorem antiDual_one :
    antiDual σ σi (1 : Module.End ℂ A) = 1 := by
  apply LinearMap.ext
  intro a
  change σi * (σ * a * σ) * σi = a
  calc σi * (σ * a * σ) * σi = (σi * σ) * a * (σ * σi) := by
        noncomm_ring
    _ = a := by rw [hiσ, hσi, one_mul, mul_one]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:cancellation-criterion` (ii)**: the current is
KMS anti-self-adjoint, `𝒥^♯ = −𝒥` (its predual is the difference
of the two preduals, per clause (vi) of
`thm:canonical-anti-renewal`). -/
theorem kmsCurrent_anti (Φ Φstar : A →ₗ[ℂ] A) :
    antiDual σ σi
        (Φstar - ((sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)))
      = -(kmsCurrent σ σi Φ Φstar) := by
  rw [antiDual_sub, antiDual_involutive σ σi hσi hiσ, kmsCurrent,
    neg_sub]

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:cancellation` (decomposition sums to `Φ`)**:
`Φ_sym + Φ_asym = Φ` with `Φ_sym = ½(Φ + Φ^♯)` and `Φ_asym = ½𝒥_ρ(Φ)`. -/
theorem symPart_add_asymPart (Φ Φstar : A →ₗ[ℂ] A) :
    (1/2 : ℂ) • (Φ + antiDual σ σi Φstar)
      + (1/2 : ℂ) • kmsCurrent σ σi Φ Φstar = Φ := by
  unfold kmsCurrent
  rw [← smul_add]
  have h : Φ + antiDual σ σi Φstar + (Φ - antiDual σ σi Φstar)
      = (2 : ℂ) • Φ := by
    rw [two_smul]; abel
  rw [h, smul_smul]
  norm_num

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:cancellation` (`Φ_sym` is KMS self-adjoint)**:
the sharp of the symmetric part — computed via its predual
`½(Φ* + σ(·)σ ∘ Φ ∘ σ⁻¹(·)σ⁻¹)` — is the symmetric part itself. -/
theorem symPart_selfAdjoint (Φ Φstar : A →ₗ[ℂ] A) :
    antiDual σ σi
        ((1/2 : ℂ) • (Φstar + (sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)))
      = (1/2 : ℂ) • (Φ + antiDual σ σi Φstar) := by
  rw [antiDual_smul, antiDual_add,
    antiDual_involutive σ σi hσi hiσ, add_comm]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:cancellation` (`Φ_asym` is KMS
skew-adjoint)**: the sharp of the antisymmetric part is its
negative. -/
theorem asymPart_skewAdjoint (Φ Φstar : A →ₗ[ℂ] A) :
    antiDual σ σi
        ((1/2 : ℂ) • (Φstar - (sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)))
      = -((1/2 : ℂ) • kmsCurrent σ σi Φ Φstar) := by
  rw [antiDual_smul, kmsCurrent_anti σ σi hσi hiσ Φ Φstar, smul_neg]

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:cancellation` (uniqueness)**: the
decomposition of a channel into a KMS self-adjoint and a KMS
skew-adjoint part (each recorded with its predual, the preduals
summing compatibly) is unique — the ±1-eigenspace decomposition of
the sharp involution. -/
theorem cancellation_decomposition_unique
    {S B S' B' Sstar Bstar S'star B'star : A →ₗ[ℂ] A}
    (hS : antiDual σ σi Sstar = S) (hB : antiDual σ σi Bstar = -B)
    (hS' : antiDual σ σi S'star = S') (hB' : antiDual σ σi B'star = -B')
    (hsum : S + B = S' + B') (hpre : Sstar + Bstar = S'star + B'star) :
    S = S' ∧ B = B' := by
  have h2 : S - B = S' - B' := by
    have h := congrArg (antiDual σ σi) hpre
    rw [antiDual_add, antiDual_add, hS, hB, hS', hB'] at h
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact h
  have h4 : (2 : ℂ) • S = (2 : ℂ) • S' := by
    calc (2 : ℂ) • S = (S + B) + (S - B) := by rw [two_smul]; abel
      _ = (S' + B') + (S' - B') := by rw [hsum, h2]
      _ = (2 : ℂ) • S' := by rw [two_smul]; abel
  have hSS : S = S' := by
    have h5 : ((2 : ℂ)⁻¹ * 2) • S = ((2 : ℂ)⁻¹ * 2) • S' := by
      rw [← smul_smul, ← smul_smul, h4]
    rw [show ((2 : ℂ)⁻¹ * 2) = 1 from by norm_num, one_smul, one_smul]
      at h5
    exact h5
  refine ⟨hSS, ?_⟩
  have h6 := hsum
  rw [hSS] at h6
  exact add_left_cancel h6

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
theorem kmsInner_sub_right (a x y : A) :
    kmsInner τ σ a (x - y) = kmsInner τ σ a x - kmsInner τ σ a y := by
  unfold kmsInner
  rw [mul_sub, map_sub]

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
theorem kmsInner_sub_left (x y b : A) :
    kmsInner τ σ (x - y) b = kmsInner τ σ x b - kmsInner τ σ y b := by
  unfold kmsInner
  rw [star_sub]
  have h1 : σ * (star x - star y) * σ * b
      = (σ * star x * σ) * b - (σ * star y * σ) * b := by
    noncomm_ring
  rw [h1, map_sub]

include hτc hτs hσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- Hermitian symmetry of the KMS inner product. -/
theorem kmsInner_conj (x y : A) :
    star (kmsInner τ σ x y) = kmsInner τ σ y x := by
  unfold kmsInner
  rw [← hτs]
  have h1 : star ((σ * star x * σ) * y) = star y * (σ * x * σ) := by
    rw [star_mul, star_mul, star_mul, hσ, star_star]
    noncomm_ring
  rw [h1]
  calc τ (star y * (σ * x * σ))
      = τ ((star y * (σ * x)) * σ) := by congr 1; noncomm_ring
    _ = τ (σ * (star y * (σ * x))) := hτc _ _
    _ = τ ((σ * star y * σ) * x) := by congr 1; noncomm_ring

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- The KMS pairing of two self-adjoint elements is symmetric. -/
theorem kmsInner_symm_of_selfAdjoint (u v : A) (hu : star u = u)
    (hv : star v = v) :
    kmsInner τ σ u v = kmsInner τ σ v u := by
  unfold kmsInner
  rw [hu, hv]
  calc τ ((σ * u * σ) * v) = τ (v * (σ * u * σ)) := hτc _ _
    _ = τ ((v * (σ * u)) * σ) := by congr 1; noncomm_ring
    _ = τ (σ * (v * (σ * u))) := hτc _ _
    _ = τ ((σ * v * σ) * u) := by congr 1; noncomm_ring

variable {Φ Φstar : A →ₗ[ℂ] A}

include hσ hσi in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- The Petz predual `Γ Φ Γ⁻¹` preserves the star when `Φ` does. -/
theorem sandwich_star_preserving
    (hΦsp : ∀ x : A, Φ (star x) = star (Φ x)) (x : A) :
    ((sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)) (star x)
      = star (((sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)) x) := by
  have hσi' : star σi = σi := star_sigmaInv σ σi hσ hσi
  change σ * Φ (σi * star x * σi) * σ = star (σ * Φ (σi * x * σi) * σ)
  rw [star_mul, star_mul, hσ, ← hΦsp]
  have h1 : star (σi * x * σi) = σi * star x * σi := by
    rw [star_mul, star_mul, hσi', ← mul_assoc]
  rw [h1]
  noncomm_ring

include hτc hσ hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Theorem `thm:cancellation-criterion` (iii)**: the adjoint form
`⟨a, 𝒥b⟩ = −⟨𝒥a, b⟩`. -/
theorem kmsCurrent_adjoint_form
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a))
    (hstarpres : ∀ x : A, Φstar (star x) = star (Φstar x))
    (hΦsp : ∀ x : A, Φ (star x) = star (Φ x)) (a b : A) :
    kmsInner τ σ a (kmsCurrent σ σi Φ Φstar b)
      = -(kmsInner τ σ (kmsCurrent σ σi Φ Φstar a) b) := by
  have hAdj1 : ∀ x y : A, kmsInner τ σ x (Φ y)
      = kmsInner τ σ (antiDual σ σi Φstar x) y := fun x y =>
    antiDual_kms_adjoint τ σ σi hσ hσi hiσ hpair hstarpres x y
  have hAdj2 : ∀ x y : A, kmsInner τ σ x (antiDual σ σi Φstar y)
      = kmsInner τ σ (Φ x) y := by
    intro x y
    have h := antiDual_kms_adjoint τ σ σi hσ hσi hiσ
      (Φ := antiDual σ σi Φstar)
      (Φstar := (sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi))
      (antiDual_predual_pairing τ σ σi hτc hpair)
      (sandwich_star_preserving σ σi hσ hσi hΦsp) x y
    rw [antiDual_involutive σ σi hσi hiσ] at h
    exact h
  change kmsInner τ σ a ((Φ - antiDual σ σi Φstar) b) = _
  have hsplit : (Φ - antiDual σ σi Φstar) b
      = Φ b - antiDual σ σi Φstar b := rfl
  rw [hsplit, kmsInner_sub_right, hAdj1, hAdj2]
  have hsplit2 : kmsInner τ σ (kmsCurrent σ σi Φ Φstar a) b
      = kmsInner τ σ (Φ a) b
        - kmsInner τ σ (antiDual σ σi Φstar a) b := by
    change kmsInner τ σ ((Φ - antiDual σ σi Φstar) a) b = _
    have h : (Φ - antiDual σ σi Φstar) a
        = Φ a - antiDual σ σi Φstar a := rfl
    rw [h, kmsInner_sub_left]
  rw [hsplit2]
  ring

include hτc hτs hσ hσi hiσ in
omit hτs [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Theorem `thm:cancellation-criterion` (iv)**: diagonal
cancellation — `⟨a, 𝒥a⟩ = 0` for every self-adjoint `a`: the
mismatch is an oriented off-diagonal component, not a positive
observable. -/
theorem kmsCurrent_diagonal
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a))
    (hstarpres : ∀ x : A, Φstar (star x) = star (Φstar x))
    (hΦsp : ∀ x : A, Φ (star x) = star (Φ x)) (a : A)
    (ha : star a = a) :
    kmsInner τ σ a (kmsCurrent σ σi Φ Φstar a) = 0 := by
  have hσi' : star σi = σi := star_sigmaInv σ σi hσ hσi
  -- the current preserves self-adjointness
  have hJa : star (kmsCurrent σ σi Φ Φstar a)
      = kmsCurrent σ σi Φ Φstar a := by
    change star ((Φ - antiDual σ σi Φstar) a) = _
    have h0 : (Φ - antiDual σ σi Φstar) a
        = Φ a - antiDual σ σi Φstar a := rfl
    rw [h0, star_sub]
    have h1 : star (Φ a) = Φ a := by rw [← hΦsp, ha]
    have h2 : star (antiDual σ σi Φstar a)
        = antiDual σ σi Φstar a := by
      rw [antiDual_apply, star_mul, star_mul, hσi', ← hstarpres]
      have h3 : star (σ * a * σ) = σ * a * σ := by
        rw [star_mul, star_mul, hσ, ha, ← mul_assoc]
      rw [h3]
      noncomm_ring
    rw [h1, h2]
    exact h0.symm
  -- symmetry and antisymmetry force vanishing
  have hsymm := kmsInner_symm_of_selfAdjoint τ σ hτc a
    (kmsCurrent σ σi Φ Φstar a) ha hJa
  have hanti := kmsCurrent_adjoint_form τ σ σi hτc hσ hσi hiσ
    hpair hstarpres hΦsp a a
  rw [hsymm] at hanti
  -- hanti : ⟨Ja, a⟩ = −⟨Ja, a⟩
  have h4 : kmsInner τ σ (kmsCurrent σ σi Φ Φstar a) a = 0 := by
    have h5 : kmsInner τ σ (kmsCurrent σ σi Φ Φstar a) a
        + kmsInner τ σ (kmsCurrent σ σi Φ Φstar a) a = 0 := by
      nth_rewrite 2 [hanti]
      ring
    exact add_self_eq_zero.mp h5
  rw [hsymm, h4]

/-- **Theorem `thm:current-composition` (ring identity, first
form)**. -/
theorem current_composition_ring {R : Type*} [Ring R] (Φ Ψ S T : R) :
    Φ * Ψ - T * S
      = (Φ - S) * Ψ + S * (Ψ - T) + (S * T - T * S) := by
  noncomm_ring

/-- **Theorem `thm:current-composition` (ring identity, second
form)**. -/
theorem current_composition_ring' {R : Type*} [Ring R] (Φ Ψ S T : R) :
    Φ * Ψ - T * S
      = Φ * (Ψ - T) + (Φ - S) * T + (S * T - T * S) := by
  noncomm_ring

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:current-composition`**: the composition law with
the noncommutative curvature term, first displayed form —
`𝒥(Φ∘Ψ) = 𝒥(Φ)∘Ψ + Φ^♯∘𝒥(Ψ) + [Φ^♯,Ψ^♯]`. -/
theorem kmsCurrent_composition (Φ Ψ Φs Ψs : A →ₗ[ℂ] A) :
    kmsCurrent σ σi (Φ ∘ₗ Ψ) (Ψs ∘ₗ Φs)
      = ((kmsCurrent σ σi Φ Φs) ∘ₗ Ψ)
        + (antiDual σ σi Φs ∘ₗ (kmsCurrent σ σi Ψ Ψs))
        + ((antiDual σ σi Φs ∘ₗ antiDual σ σi Ψs)
           - (antiDual σ σi Ψs ∘ₗ antiDual σ σi Φs)) := by
  change (Φ ∘ₗ Ψ) - antiDual σ σi (Ψs ∘ₗ Φs) = _
  rw [antiDual_comp σ σi hσi hiσ]
  exact current_composition_ring (R := Module.End ℂ A) Φ Ψ
    (antiDual σ σi Φs) (antiDual σ σi Ψs)

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:current-composition`**: second displayed form —
`𝒥(Φ∘Ψ) = Φ∘𝒥(Ψ) + 𝒥(Φ)∘Ψ^♯ + [Φ^♯,Ψ^♯]`. -/
theorem kmsCurrent_composition' (Φ Ψ Φs Ψs : A →ₗ[ℂ] A) :
    kmsCurrent σ σi (Φ ∘ₗ Ψ) (Ψs ∘ₗ Φs)
      = (Φ ∘ₗ (kmsCurrent σ σi Ψ Ψs))
        + ((kmsCurrent σ σi Φ Φs) ∘ₗ antiDual σ σi Ψs)
        + ((antiDual σ σi Φs ∘ₗ antiDual σ σi Ψs)
           - (antiDual σ σi Ψs ∘ₗ antiDual σ σi Φs)) := by
  change (Φ ∘ₗ Ψ) - antiDual σ σi (Ψs ∘ₗ Φs) = _
  rw [antiDual_comp σ σi hσi hiσ]
  exact current_composition_ring' (R := Module.End ℂ A) Φ Ψ
    (antiDual σ σi Φs) (antiDual σ σi Ψs)

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Corollary `cor:balanced-product` (commutator formula)**: for
detailed-balanced factors, `𝒥(Φ∘Ψ) = [Φ, Ψ]`. -/
theorem balanced_product (Φ Ψ Φs Ψs : A →ₗ[ℂ] A)
    (hbΦ : KMSDetailedBalance σ σi Φ Φs)
    (hbΨ : KMSDetailedBalance σ σi Ψ Ψs) :
    kmsCurrent σ σi (Φ ∘ₗ Ψ) (Ψs ∘ₗ Φs)
      = (Φ ∘ₗ Ψ) - (Ψ ∘ₗ Φ) := by
  change (Φ ∘ₗ Ψ) - antiDual σ σi (Ψs ∘ₗ Φs) = _
  rw [antiDual_comp σ σi hσi hiσ, ← hbΦ, ← hbΨ]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Corollary `cor:balanced-product` (commutation criterion)**:
the composite of two detailed-balanced maps is detailed-balanced iff
they commute. -/
theorem balanced_product_iff (Φ Ψ Φs Ψs : A →ₗ[ℂ] A)
    (hbΦ : KMSDetailedBalance σ σi Φ Φs)
    (hbΨ : KMSDetailedBalance σ σi Ψ Ψs) :
    kmsCurrent σ σi (Φ ∘ₗ Ψ) (Ψs ∘ₗ Φs) = 0 ↔
      Φ ∘ₗ Ψ = Ψ ∘ₗ Φ := by
  rw [balanced_product σ σi hσi hiσ Φ Ψ Φs Ψs hbΦ hbΨ]
  exact sub_eq_zero

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Corollary `cor:balanced-product` (convexity)**: convex (indeed
arbitrary affine) combinations of detailed-balanced maps remain
detailed-balanced. -/
theorem balanced_convex (Φ Ψ Φs Ψs : A →ₗ[ℂ] A) (c : ℂ)
    (hbΦ : KMSDetailedBalance σ σi Φ Φs)
    (hbΨ : KMSDetailedBalance σ σi Ψ Ψs) :
    KMSDetailedBalance σ σi (c • Φ + (1 - c) • Ψ)
      (c • Φs + (1 - c) • Ψs) := by
  unfold KMSDetailedBalance
  rw [antiDual_add, antiDual_smul, antiDual_smul, ← hbΦ, ← hbΨ]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Corollary `cor:balanced-product` (powers)**: every power of a
detailed-balanced map is detailed-balanced. -/
theorem balanced_pow (Φ Φs : A →ₗ[ℂ] A)
    (hb : KMSDetailedBalance σ σi Φ Φs) (n : ℕ) :
    KMSDetailedBalance σ σi (Φ ^ n) (Φs ^ n) := by
  unfold KMSDetailedBalance at *
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (antiDual_one σ σi hσi hiσ).symm
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, hb]
    exact (antiDual_comp σ σi hσi hiσ Φs (Φs ^ n)).symm

end Current

end NCG.Upstream
