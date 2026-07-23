/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CPMap

/-!
# The KMS/Petz anti-renewal dual

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:kms-dual` — the anti-renewal dual
  `Φ^♯ = Γ_ρ⁻¹ ∘ Φ_* ∘ Γ_ρ`,
  `Φ^♯(a) = ρ^{-1/2} Φ_*(ρ^{1/2} a ρ^{1/2}) ρ^{-1/2}`;
* `thm:canonical-anti-renewal` — all six clauses: CP and unitality
  with `ρ`-preservation, the KMS-adjoint identity, involutivity,
  exact composition reversal, the Kraus formula
  `L_k = ρ^{1/2} K_k^* ρ^{-1/2}`, and the Petz-transpose predual;
* `def:three-adjoints` — Hilbert–Schmidt, right-GNS, and KMS/Petz
  adjoints;
* `prop:reverse-comparison` — the HS adjoint is trace preserving and
  unital iff bistochastic; the KMS dual is CP always and unital iff
  `ρ` is stationary; the GNS/KMS conjugation relation
  `Φ^G = 𝓜⁻¹ Φ^♯ 𝓜`; equality under half-step modular covariance;
* `prop:unitary-reverse` — on the stationary unitary sector the
  anti-renewal dual is inverse evolution;
* `prop:replacement-self-dual` — the replacement channel is unital,
  positive (completely positive in the matrix realization via its
  matrix-unit Kraus decomposition), `ρ`-preserving, self-dual,
  idempotent, and noninvertible in dimension `> 1`.

The notes fix `𝒜 = M_d(ℂ)` for this section.  The algebraic clauses
are proved for any star-ordered `ℂ`-algebra equipped with a cyclic,
star-compatible trace functional `τ` and a self-adjoint invertible
element `σ = ρ^{1/2}` squaring to the stationary state `ρ = σ²` —
`M_d(ℂ)` with its trace, Loewner order, and positive-definite square
root is the intended instance.  Passing from the faithful state to
its square root and (in `prop:reverse-comparison`) from real modular
covariance to the imaginary half-step are the standard
finite-dimensional functional-calculus steps; they enter as the form
of the hypotheses.
-/

namespace NCG.Upstream

open NCG

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A]

/-! ## Congruences and Kraus sums are completely positive -/

/-- The star-congruence `a ↦ c* a c`. -/
def congrMap (c : A) : A →ₗ[ℂ] A where
  toFun a := star c * a * c
  map_add' a b := by simp [mul_add, add_mul]
  map_smul' r a := by simp []

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
theorem congrMap_apply (c a : A) : congrMap c a = star c * a * c := rfl

omit [StarModule ℂ A] [StarOrderedRing A] in
/-- Star-congruences are completely positive. -/
theorem congrMap_cp (c : A) : IsCompletelyPositive (congrMap c) := by
  intro k M hM x
  have h := hM fun i => c * x i
  have heq : ∑ i, ∑ j, star (x i) * (M.map (congrMap c)) i j * x j
      = ∑ i, ∑ j, star (c * x i) * M i j * (c * x j) := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.map_apply, congrMap_apply]
    rw [star_mul]
    noncomm_ring
  rw [heq]
  exact h

omit [StarModule ℂ A] [StarOrderedRing A] in
theorem cp_zero : IsCompletelyPositive (0 : A →ₗ[ℂ] A) := by
  intro k M hM x
  simp

omit [StarModule ℂ A] in
theorem cp_add {φ ψ : A →ₗ[ℂ] A} (hφ : IsCompletelyPositive φ)
    (hψ : IsCompletelyPositive ψ) : IsCompletelyPositive (φ + ψ) := by
  intro k M hM x
  have heq : ∑ i, ∑ j, star (x i) * (M.map (φ + ψ)) i j * x j
      = (∑ i, ∑ j, star (x i) * (M.map φ) i j * x j)
        + ∑ i, ∑ j, star (x i) * (M.map ψ) i j * x j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.map_apply, mul_add, add_mul]
  rw [heq]
  exact add_nonneg (hφ k M hM x) (hψ k M hM x)

omit [StarModule ℂ A] in
/-- Finite sums of completely positive maps are completely
positive. -/
theorem cp_sum {ι : Type*} (s : Finset ι) (f : ι → (A →ₗ[ℂ] A))
    (h : ∀ i ∈ s, IsCompletelyPositive (f i)) :
    IsCompletelyPositive (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cp_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact cp_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [StarModule ℂ A] in
/-- **Kraus form implies complete positivity**: any map
`a ↦ ∑ₖ Kₖ* a Kₖ` is CP. -/
theorem kraus_cp {ι : Type*} [Fintype ι] (K : ι → A)
    {φ : A →ₗ[ℂ] A} (hφ : ∀ a, φ a = ∑ k, star (K k) * a * K k) :
    IsCompletelyPositive φ := by
  have hφeq : φ = ∑ k, congrMap (K k) := by
    apply LinearMap.ext
    intro a
    rw [hφ a]
    simp [congrMap_apply]
  rw [hφeq]
  exact cp_sum _ _ fun k _ => congrMap_cp (K k)

/-! ## The KMS system and the anti-renewal dual -/

section KMS

variable (τ : A →ₗ[ℂ] ℂ) (σ σi : A)
variable (hτc : ∀ x y : A, τ (x * y) = τ (y * x))
variable (hσ : star σ = σ) (hσi : σ * σi = 1) (hiσ : σi * σ = 1)

/-- The two-sided multiplication `a ↦ c a c` — the congruence
`Γ_ρ(a) = ρ^{1/2} a ρ^{1/2}` for `c = ρ^{1/2}`, and its inverse for
`c = ρ^{-1/2}`. -/
def sandwich (c : A) : A →ₗ[ℂ] A where
  toFun a := c * a * c
  map_add' a b := by simp [mul_add, add_mul]
  map_smul' r a := by simp []

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem sandwich_apply (c a : A) : sandwich c a = c * a * c := rfl

include hσ in
omit [StarModule ℂ A] [StarOrderedRing A] in
theorem sandwich_cp_self : IsCompletelyPositive (sandwich σ) := by
  have h : sandwich σ = congrMap σ := by
    apply LinearMap.ext
    intro a
    rw [sandwich_apply, congrMap_apply, hσ]
  rw [h]
  exact congrMap_cp σ

include hσ hσi in
omit [Algebra ℂ A] [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
theorem star_sigmaInv : star σi = σi := by
  have h1 : star σi * star σ = 1 := by
    rw [← star_mul, hσi, star_one]
  rw [hσ] at h1
  calc star σi = star σi * (σ * σi) := by rw [hσi, mul_one]
    _ = (star σi * σ) * σi := by rw [mul_assoc]
    _ = σi := by rw [h1, one_mul]

/-- **Definition `def:kms-dual`**: the anti-renewal dual
`Φ^♯ = Γ⁻¹ ∘ Φ_* ∘ Γ`, i.e. `Φ^♯(a) = σ⁻¹ Φ_*(σ a σ) σ⁻¹` with
`σ = ρ^{1/2}`. -/
def antiDual (Φstar : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  (sandwich σi) ∘ₗ Φstar ∘ₗ (sandwich σ)

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem antiDual_apply (Φstar : A →ₗ[ℂ] A) (a : A) :
    antiDual σ σi Φstar a = σi * Φstar (σ * a * σ) * σi := rfl

/-- The symmetric KMS inner product
`⟨a,b⟩_{ρ,1/2} = Tr(ρ^{1/2} a* ρ^{1/2} b)`. -/
def kmsInner (a b : A) : ℂ := τ ((σ * star a * σ) * b)

variable {Φ Φstar : A →ₗ[ℂ] A}

include hσ hσi in
omit [StarModule ℂ A] [StarOrderedRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (i, complete
positivity)**: the dual of a CP predual is CP. -/
theorem antiDual_cp (hCP : IsCompletelyPositive Φstar) :
    IsCompletelyPositive (antiDual σ σi Φstar) := by
  have hσi' : star σi = σi := star_sigmaInv σ σi hσ hσi
  exact IsCompletelyPositive.comp
    (IsCompletelyPositive.comp (sandwich_cp_self σ hσ) hCP)
    (sandwich_cp_self σi hσi')

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (i, unitality)** /
**Proposition `prop:reverse-comparison` (KMS clause)**: the dual is
unital *iff* `ρ = σ²` is stationary
(`rem:stationarity-unitality`). -/
theorem antiDual_unital_iff :
    antiDual σ σi Φstar 1 = 1 ↔ Φstar (σ * σ) = σ * σ := by
  rw [antiDual_apply, mul_one]
  constructor
  · intro h
    calc Φstar (σ * σ)
        = (σ * σi) * Φstar (σ * σ) * (σi * σ) := by
          rw [hσi, hiσ, one_mul, mul_one]
      _ = σ * (σi * Φstar (σ * σ) * σi) * σ := by noncomm_ring
      _ = σ * 1 * σ := by rw [h]
      _ = σ * σ := by rw [mul_one]
  · intro hstat
    rw [hstat]
    calc σi * (σ * σ) * σi = (σi * σ) * (σ * σi) := by noncomm_ring
      _ = 1 := by rw [hiσ, hσi, one_mul]

include hτc hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (i, invariance)**: `ρ` is
stationary for the dual: `Tr(ρ Φ^♯(b)) = Tr(ρ b)`. -/
theorem antiDual_state_invariant
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a))
    (hΦ1 : Φ 1 = 1) (b : A) :
    τ ((σ * σ) * antiDual σ σi Φstar b) = τ ((σ * σ) * b) := by
  rw [antiDual_apply]
  have h1 : (σ * σ) * (σi * Φstar (σ * b * σ) * σi)
      = σ * (Φstar (σ * b * σ) * σi) := by
    calc (σ * σ) * (σi * Φstar (σ * b * σ) * σi)
        = σ * (σ * σi) * (Φstar (σ * b * σ) * σi) := by noncomm_ring
      _ = σ * (Φstar (σ * b * σ) * σi) := by rw [hσi, mul_one]
  rw [h1, hτc σ (Φstar (σ * b * σ) * σi)]
  calc τ (Φstar (σ * b * σ) * σi * σ)
      = τ (Φstar (σ * b * σ) * 1) := by rw [mul_assoc, hiσ]
    _ = τ ((σ * b * σ) * Φ 1) := hpair _ _
    _ = τ (σ * b * σ) := by rw [hΦ1, mul_one]
    _ = τ ((b * σ) * σ) := by rw [mul_assoc, hτc σ (b * σ)]
    _ = τ ((σ * σ) * b) := by rw [mul_assoc, hτc b (σ * σ)]

include hσ hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (ii, KMS adjoint
identity)**: `⟨a, Φ(b)⟩_{ρ,1/2} = ⟨Φ^♯(a), b⟩_{ρ,1/2}`. -/
theorem antiDual_kms_adjoint
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a))
    (hstarpres : ∀ x : A, Φstar (star x) = star (Φstar x)) (a b : A) :
    kmsInner τ σ a (Φ b) = kmsInner τ σ (antiDual σ σi Φstar a) b := by
  have hσi' : star σi = σi := star_sigmaInv σ σi hσ hσi
  unfold kmsInner
  have hW : star (σ * a * σ) = σ * star a * σ := by
    rw [star_mul, star_mul, hσ, ← mul_assoc]
  have hR : σ * star (antiDual σ σi Φstar a) * σ
      = Φstar (σ * star a * σ) := by
    rw [antiDual_apply, star_mul, star_mul, hσi', ← hstarpres, hW]
    calc σ * (σi * (Φstar (σ * star a * σ) * σi)) * σ
        = (σ * σi) * Φstar (σ * star a * σ) * (σi * σ) := by
          noncomm_ring
      _ = Φstar (σ * star a * σ) := by
          rw [hσi, hiσ, one_mul, mul_one]
  rw [hR, hpair]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (iii, involutivity)**:
applying the anti-renewal construction to the dual's own predual
`Γ ∘ Φ ∘ Γ⁻¹` (clause (vi)) returns `Φ` — `(Φ^♯)^♯ = Φ`. -/
theorem antiDual_involutive (Φheis : A →ₗ[ℂ] A) :
    antiDual σ σi ((sandwich σ) ∘ₗ Φheis ∘ₗ (sandwich σi)) = Φheis := by
  apply LinearMap.ext
  intro a
  change σi * (σ * Φheis (σi * (σ * a * σ) * σi) * σ) * σi = Φheis a
  have hin : σi * (σ * a * σ) * σi = a := by
    calc σi * (σ * a * σ) * σi = (σi * σ) * a * (σ * σi) := by
          noncomm_ring
      _ = a := by rw [hiσ, hσi, one_mul, mul_one]
  rw [hin]
  calc σi * (σ * Φheis a * σ) * σi
      = (σi * σ) * Φheis a * (σ * σi) := by noncomm_ring
    _ = Φheis a := by rw [hiσ, hσi, one_mul, mul_one]

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (iv, composition
reversal)**: `(Φ ∘ Ψ)^♯ = Ψ^♯ ∘ Φ^♯` (the predual of `Φ ∘ Ψ` is
`Ψ_* ∘ Φ_*`). -/
theorem antiDual_comp (Φs Ψs : A →ₗ[ℂ] A) :
    antiDual σ σi (Ψs ∘ₗ Φs)
      = (antiDual σ σi Ψs) ∘ₗ (antiDual σ σi Φs) := by
  apply LinearMap.ext
  intro a
  change σi * Ψs (Φs (σ * a * σ)) * σi
      = σi * Ψs (σ * (σi * Φs (σ * a * σ) * σi) * σ) * σi
  have h : σ * (σi * Φs (σ * a * σ) * σi) * σ = Φs (σ * a * σ) := by
    calc σ * (σi * Φs (σ * a * σ) * σi) * σ
        = (σ * σi) * Φs (σ * a * σ) * (σi * σ) := by noncomm_ring
      _ = Φs (σ * a * σ) := by rw [hσi, hiσ, one_mul, mul_one]
  rw [h]

include hσ hσi in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Theorem `thm:canonical-anti-renewal` (v, Kraus form)**: if
`Φ_*(x) = ∑ₖ Kₖ x Kₖ*` (Heisenberg `Φ(a) = ∑ₖ Kₖ* a Kₖ`), then
`Φ^♯(a) = ∑ₖ Lₖ* a Lₖ` with `Lₖ = ρ^{1/2} Kₖ* ρ^{-1/2}` — with
`kraus_cp` this re-proves complete positivity of the dual. -/
theorem antiDual_kraus {ι : Type*} [Fintype ι] (K : ι → A)
    (hK : ∀ x, Φstar x = ∑ k, K k * x * star (K k)) (a : A) :
    antiDual σ σi Φstar a
      = ∑ k, star (σ * star (K k) * σi) * a * (σ * star (K k) * σi) := by
  have hσi' : star σi = σi := star_sigmaInv σ σi hσ hσi
  rw [antiDual_apply, hK, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul, star_mul, hσi', star_star, hσ]
  noncomm_ring

include hτc hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] hiσ hσi in
/-- **Theorem `thm:canonical-anti-renewal` (vi, Petz-transpose
predual)**: `Γ ∘ Φ ∘ Γ⁻¹` satisfies the defining trace pairing of
the predual of `Φ^♯` — the KMS adjoint in the Heisenberg picture
and the Petz transpose in the Schrödinger picture are the same
construction. -/
theorem antiDual_predual_pairing
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a)) (x a : A) :
    τ (((sandwich σ) ∘ₗ Φ ∘ₗ (sandwich σi)) x * a)
      = τ (x * antiDual σ σi Φstar a) := by
  change τ ((σ * Φ (σi * x * σi) * σ) * a)
      = τ (x * (σi * Φstar (σ * a * σ) * σi))
  calc τ ((σ * Φ (σi * x * σi) * σ) * a)
      = τ (σ * (Φ (σi * x * σi) * σ * a)) := by
        congr 1
        noncomm_ring
    _ = τ ((Φ (σi * x * σi) * σ * a) * σ) := hτc _ _
    _ = τ (Φ (σi * x * σi) * (σ * a * σ)) := by
        congr 1
        noncomm_ring
    _ = τ ((σ * a * σ) * Φ (σi * x * σi)) := hτc _ _
    _ = τ (Φstar (σ * a * σ) * (σi * x * σi)) := (hpair _ _).symm
    _ = τ ((σi * x * σi) * Φstar (σ * a * σ)) := hτc _ _
    _ = τ (σi * (x * σi * Φstar (σ * a * σ))) := by
        congr 1
        noncomm_ring
    _ = τ ((x * σi * Φstar (σ * a * σ)) * σi) := hτc _ _
    _ = τ (x * (σi * Φstar (σ * a * σ) * σi)) := by
        congr 1
        noncomm_ring

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] hτc in
/-- The predual of `Φ^♯` is unique under nondegeneracy of the trace
pairing (so clause (vi) identifies it exactly). -/
theorem predual_unique
    (hnd : ∀ x : A, (∀ a : A, τ (x * a) = 0) → x = 0)
    (Ψ₁ Ψ₂ Θ : A →ₗ[ℂ] A)
    (h₁ : ∀ x a : A, τ (Ψ₁ x * a) = τ (x * Θ a))
    (h₂ : ∀ x a : A, τ (Ψ₂ x * a) = τ (x * Θ a)) : Ψ₁ = Ψ₂ := by
  apply LinearMap.ext
  intro x
  have hz : Ψ₁ x - Ψ₂ x = 0 := by
    apply hnd
    intro a
    rw [sub_mul, map_sub, h₁, h₂, sub_self]
  exact sub_eq_zero.mp hz

/-! ## `def:three-adjoints` and `prop:reverse-comparison` -/

/-- **Definition `def:three-adjoints` (a)**: the Hilbert–Schmidt
adjoint under the trace identification is the predual itself. -/
def hsAdjoint (Φs : A →ₗ[ℂ] A) : A →ₗ[ℂ] A := Φs

/-- **Definition `def:three-adjoints` (b)**: the right-GNS adjoint
`Φ^G(a) = Φ_*(a ρ) ρ⁻¹`. -/
def gnsDual (Φs : A →ₗ[ℂ] A) : A →ₗ[ℂ] A where
  toFun a := Φs (a * (σ * σ)) * (σi * σi)
  map_add' a b := by simp [add_mul]
  map_smul' r a := by simp []

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem gnsDual_apply (Φs : A →ₗ[ℂ] A) (a : A) :
    gnsDual σ σi Φs a = Φs (a * (σ * σ)) * (σi * σi) := rfl

/-- Bistochasticity: unital in both pictures. -/
def Bistochastic (Φheis Φs : A →ₗ[ℂ] A) : Prop :=
  Φheis 1 = 1 ∧ Φs 1 = 1

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] hτc in
/-- **Proposition `prop:reverse-comparison` (HS clause, trace
preservation)**: the Hilbert–Schmidt adjoint is trace preserving. -/
theorem hsAdjoint_trace_preserving
    (hpair : ∀ x a : A, τ (Φstar x * a) = τ (x * Φ a))
    (hΦ1 : Φ 1 = 1) (x : A) : τ (hsAdjoint Φstar x) = τ x := by
  calc τ (hsAdjoint Φstar x) = τ (Φstar x * 1) := by
        rw [hsAdjoint, mul_one]
    _ = τ (x * Φ 1) := hpair _ _
    _ = τ x := by rw [hΦ1, mul_one]

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:reverse-comparison` (HS clause,
unitality)**: given `Φ(1) = 1`, the HS adjoint is unital exactly
when `Φ` is bistochastic. -/
theorem hsAdjoint_unital_iff (hΦ1 : Φ 1 = 1) :
    hsAdjoint Φstar 1 = 1 ↔ Bistochastic Φ Φstar :=
  ⟨fun h => ⟨hΦ1, h⟩, fun h => h.2⟩

include hσi in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:reverse-comparison` (GNS/KMS relation)**:
`Φ^G = 𝓜_ρ⁻¹ ∘ Φ^♯ ∘ 𝓜_ρ` with `𝓜_ρ(a) = ρ^{-1/2} a ρ^{1/2}`. -/
theorem gnsDual_eq_conj (a : A) :
    gnsDual σ σi Φstar a
      = σ * (antiDual σ σi Φstar (σi * a * σ)) * σi := by
  rw [gnsDual_apply, antiDual_apply]
  have h1 : σ * (σi * a * σ) * σ = a * (σ * σ) := by
    calc σ * (σi * a * σ) * σ = (σ * σi) * a * (σ * σ) := by
          noncomm_ring
      _ = a * (σ * σ) := by rw [hσi, one_mul]
  rw [h1]
  calc Φstar (a * (σ * σ)) * (σi * σi)
      = (σ * σi) * Φstar (a * (σ * σ)) * (σi * σi) := by
        rw [hσi, one_mul]
    _ = σ * (σi * Φstar (a * (σ * σ)) * σi) * σi := by noncomm_ring

include hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:reverse-comparison` (modular covariance)**:
if the predual commutes with the imaginary half-step of the modular
group (`𝓜_ρ`-covariance, the finite-dimensional extension of real
modular covariance), the GNS and KMS adjoints coincide. -/
theorem gnsDual_eq_antiDual_of_halfstep
    (hcov : ∀ x, Φstar (σi * x * σ) = σi * Φstar x * σ) (a : A) :
    gnsDual σ σi Φstar a = antiDual σ σi Φstar a := by
  rw [gnsDual_apply, antiDual_apply]
  have h1 : a * (σ * σ) = σi * (σ * a * σ) * σ := by
    have h2 : σi * (σ * a * σ) * σ = a * (σ * σ) := by
      calc σi * (σ * a * σ) * σ = (σi * σ) * a * (σ * σ) := by
            noncomm_ring
        _ = a * (σ * σ) := by rw [hiσ, one_mul]
    exact h2.symm
  rw [h1, hcov]
  calc (σi * Φstar (σ * a * σ) * σ) * (σi * σi)
      = σi * Φstar (σ * a * σ) * ((σ * σi) * σi) := by noncomm_ring
    _ = σi * Φstar (σ * a * σ) * σi := by rw [hσi, one_mul]

/-! ## `prop:unitary-reverse` -/

include hσ hσi hiσ in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Proposition `prop:unitary-reverse`**: for reversible unitary
evolution `Φ(a) = U* a U` with stationary `ρ` (equivalently `U`
commuting with `ρ^{1/2}`), the anti-renewal dual is inverse
evolution, `Φ^♯(a) = U a U*`. -/
theorem unitary_antiDual (U : A) (hcomm : U * σ = σ * U)
    (hΦstar : ∀ x, Φstar x = U * x * star U) (a : A) :
    antiDual σ σi Φstar a = U * a * star U := by
  have hcomm' : σ * star U = star U * σ := by
    have h := congrArg star hcomm
    rw [star_mul, star_mul, hσ] at h
    exact h
  have hUσi : σi * U = U * σi := by
    calc σi * U = σi * U * (σ * σi) := by rw [hσi, mul_one]
      _ = σi * (U * σ) * σi := by noncomm_ring
      _ = σi * (σ * U) * σi := by rw [hcomm]
      _ = (σi * σ) * (U * σi) := by noncomm_ring
      _ = U * σi := by rw [hiσ, one_mul]
  have hU'σi : star U * σi = σi * star U := by
    calc star U * σi = (σi * σ) * star U * σi := by
          rw [hiσ, one_mul]
      _ = σi * (σ * star U) * σi := by noncomm_ring
      _ = σi * (star U * σ) * σi := by rw [hcomm']
      _ = σi * star U * (σ * σi) := by noncomm_ring
      _ = σi * star U := by rw [hσi, mul_one]
  rw [antiDual_apply, hΦstar]
  calc σi * (U * (σ * a * σ) * star U) * σi
      = (σi * U * σ) * a * (σ * star U * σi) := by noncomm_ring
    _ = (U * σi * σ) * a * (star U * σ * σi) := by
        rw [show σi * U = U * σi from hUσi, hcomm']
    _ = U * a * star U := by rw [mul_assoc U σi σ, hiσ, mul_one,
        mul_assoc (star U) σ σi, hσi, mul_one]

omit [Algebra ℂ A] [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] in
/-- **Proposition `prop:unitary-reverse` (inverse property)**: the
dual undoes the unitary evolution. -/
theorem unitary_antiDual_inverse (U : A) (hU : U * star U = 1)
    (a : A) : U * (star U * a * U) * star U = a := by
  calc U * (star U * a * U) * star U
      = (U * star U) * a * (U * star U) := by noncomm_ring
    _ = a := by rw [hU, one_mul, mul_one]

/-! ## `prop:replacement-self-dual` -/

/-- The replacement (information-erasure) channel
`Φ_ρ^rep(a) = Tr(ρ a) 1 = Tr(ρ^{1/2} a ρ^{1/2}) 1`. -/
def replacementMap : A →ₗ[ℂ] A where
  toFun a := τ (σ * a * σ) • 1
  map_add' a b := by simp [mul_add, add_mul, add_smul]
  map_smul' r a := by
    simp [smul_smul]

omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem replacementMap_apply (a : A) :
    replacementMap τ σ a = τ (σ * a * σ) • 1 := rfl

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
theorem replacementMap_apply' (a : A) :
    replacementMap τ σ a = τ ((σ * σ) * a) • 1 := by
  rw [replacementMap_apply]
  congr 1
  rw [hτc (σ * a) σ, ← mul_assoc]

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:replacement-self-dual` (unitality)**. -/
theorem replacementMap_unital (hτρ : τ (σ * σ) = 1) :
    replacementMap τ σ 1 = 1 := by
  rw [replacementMap_apply' τ σ hτc, mul_one, hτρ, one_smul]

include hσi hiσ hτc in
omit hτc [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:replacement-self-dual` (self-duality)**: the
anti-renewal dual of the replacement channel (with predual
`x ↦ Tr(x) ρ`) is the replacement channel itself — KMS detailed
balance without invertibility. -/
theorem antiDual_replacement (a : A) :
    antiDual σ σi
      { toFun := fun x => τ x • (σ * σ)
        map_add' := by simp [add_smul]
        map_smul' := by simp [smul_smul] } a
      = replacementMap τ σ a := by
  rw [antiDual_apply, replacementMap_apply]
  change σi * (τ (σ * a * σ) • (σ * σ)) * σi = τ (σ * a * σ) • 1
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc σi * (σ * σ) * σi = (σi * σ) * (σ * σi) := by noncomm_ring
    _ = 1 := by rw [hiσ, hσi, one_mul]

include hτc in
omit [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- The replacement predual satisfies the defining trace pairing. -/
theorem replacement_predual_pairing (x a : A) :
    τ ((τ x • (σ * σ)) * a) = τ (x * replacementMap τ σ a) := by
  rw [replacementMap_apply' τ σ hτc, smul_mul_assoc, map_smul,
    mul_smul_comm, map_smul, mul_one, smul_eq_mul, smul_eq_mul,
    mul_comm]

include hτc in
omit hτc [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:replacement-self-dual` (idempotency)**. -/
theorem replacementMap_idem (hτρ : τ (σ * σ) = 1) (a : A) :
    replacementMap τ σ (replacementMap τ σ a)
      = replacementMap τ σ a := by
  rw [replacementMap_apply τ σ a, map_smul,
    replacementMap_apply τ σ 1, mul_one, hτρ, one_smul]

include hτc in
omit hτc [PartialOrder A] [StarModule ℂ A] [StarOrderedRing A] [StarRing A] in
/-- **Proposition `prop:replacement-self-dual` (noninvertibility)**:
every centred element is annihilated, so the channel is not
injective as soon as some element is not a scalar (`d > 1`). -/
theorem replacementMap_not_injective (hτρ : τ (σ * σ) = 1)
    (a : A) :
    replacementMap τ σ (a - τ (σ * a * σ) • 1) = 0 := by
  rw [map_sub, map_smul, replacementMap_apply τ σ 1, mul_one, hτρ,
    one_smul, replacementMap_apply, sub_self]

open scoped ComplexOrder in
include hτc in
omit hτc in
/-- **Proposition `prop:replacement-self-dual` (positivity)**: the
replacement channel of a positive faithful state is a positive
map. -/
theorem replacementMap_positive
    (hτpos : ∀ a : A, 0 ≤ a → 0 ≤ τ (σ * a * σ)) :
    IsPositiveMap (replacementMap τ σ) := by
  intro a ha
  rw [replacementMap_apply]
  have hc := hτpos a ha
  obtain ⟨hre, him⟩ := (Complex.le_def.mp hc)
  set c : ℂ := τ (σ * a * σ) with hcdef
  have hcr : c = ((c.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him.symm
  have hre' : (0 : ℝ) ≤ c.re := by simpa using hre
  rw [hcr]
  have h1 := star_mul_self_nonneg
    (((Real.sqrt c.re : ℝ) : ℂ) • (1 : A))
  have h2 : star ((((Real.sqrt c.re : ℝ) : ℂ)) • (1 : A))
      = (((Real.sqrt c.re : ℝ) : ℂ)) • (1 : A) := by
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  rw [h2, smul_mul_smul_comm, mul_one, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hre'] at h1
  exact h1

end KMS

/-! ## Complete positivity of the replacement channel in the matrix
model -/

section MatrixModel

open scoped MatrixOrder ComplexOrder

variable {d : ℕ}

/-- Each matrix-unit sandwich collapses to a diagonal unit. -/
theorem single_sandwich (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Matrix.single j i (1 : ℂ) * X * Matrix.single i j (1 : ℂ)
      = Matrix.single j j (X i i) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.single_apply]
  by_cases hx : j = x <;> by_cases hy : j = y <;>
    simp [hx, hy, ite_and, Finset.sum_ite_eq,
      mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]

/-- Matrix units sandwich identity:
`∑ᵢⱼ Eⱼᵢ X Eᵢⱼ = Tr(X)·1`. -/
theorem matrix_units_sandwich (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i : Fin d, ∑ j : Fin d,
        Matrix.single j i (1 : ℂ) * X * Matrix.single i j (1 : ℂ)
      = Matrix.trace X • 1 := by
  have h2 : ∑ i : Fin d, ∑ j : Fin d,
      Matrix.single j i (1 : ℂ) * X * Matrix.single i j (1 : ℂ)
      = ∑ i : Fin d, ∑ j : Fin d, Matrix.single j j (X i i) :=
    Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => single_sandwich X i j
  rw [h2, Finset.sum_comm]
  ext x y
  simp only [Matrix.sum_apply, Matrix.single_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.trace, Matrix.diag]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, smul_eq_mul, mul_one, Finset.sum_comm]
    simp only [and_self]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq' Finset.univ x fun _ => X i i]
    simp
  · rw [if_neg hxy, smul_eq_mul, mul_zero]
    refine Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hxy (h1.symm.trans h2)

/-- **Proposition `prop:replacement-self-dual` (complete
positivity)**: in the matrix model of the notes, the replacement
channel has the matrix-unit Kraus decomposition
`K_{ij} = ρ^{1/2} E_{ij}`, hence is completely positive. -/
theorem replacementMap_cp_matrix (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : star σ = σ) :
    IsCompletelyPositive
      (replacementMap (Matrix.traceLinearMap (Fin d) ℂ ℂ) σ) := by
  refine kraus_cp
    (fun p : Fin d × Fin d => σ * Matrix.single p.1 p.2 (1 : ℂ)) ?_
  intro a
  rw [replacementMap_apply]
  have hstar : ∀ p : Fin d × Fin d,
      star (σ * Matrix.single p.1 p.2 (1 : ℂ))
        = Matrix.single p.2 p.1 (1 : ℂ) * σ := by
    intro p
    rw [star_mul, hσ]
    congr 1
    ext x y
    simp [Matrix.single_apply, Matrix.star_apply,
      apply_ite (star : ℂ → ℂ), and_comm]
  calc Matrix.traceLinearMap (Fin d) ℂ ℂ (σ * a * σ) • (1 : Matrix (Fin d) (Fin d) ℂ)
      = ∑ i : Fin d, ∑ j : Fin d,
          Matrix.single j i (1 : ℂ) * (σ * a * σ)
            * Matrix.single i j (1 : ℂ) :=
        (matrix_units_sandwich (σ * a * σ)).symm
    _ = ∑ p : Fin d × Fin d,
          star (σ * Matrix.single p.1 p.2 (1 : ℂ)) * a
            * (σ * Matrix.single p.1 p.2 (1 : ℂ)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [hstar (i, j)]
        noncomm_ring

end MatrixModel

end NCG.Upstream
