/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact finite-dimensional constraint reduction
  (`def:exact-initial-reduction`, Einstein–SM action closure)

Setting.  `X` is the initial-data space `𝒳_k` with its `H^k` norm (an abstract
real normed space; the Sobolev structure is not used by the definition),
`Y` is the constraint target `𝒴_k^con` (a real vector space), and
`Ck : X → Y` is the full constraint map `𝔠_k`.  The datum
`x0 = 𝒰(ẑ_h)(0)` is the initial slice of the (normalized) record; the
record `x_h` and the normalization of `thm:aposteriori-physical-shadow` enter
only through this datum, which is a parameter.  Reduced coordinates are
`λ ∈ ℝ^{m_h}` with the Euclidean norm (`EuclideanSpace ℝ (Fin m)`).

* `ExactInitialConstraintReduction` — the structure of the definition: a
  `C¹` correction family `ι_h(x_h, ·)` on the ball `|λ| ≤ r_*`, a fixed
  injective linear map `j_h : ℝ^{m_h} → 𝒴_k^con`, a `C¹` retained map
  `Φ_h(x_h, ·)`, the base point `eq:exact-initial-basepoint`, the exact
  factorization `eq:exact-initial-factorization` on the ball, and the
  reader Lipschitz bound `eq:exact-initial-reader-Lipschitz`;
* `exactInitial_factorization_iff_split` and
  `ExactInitialConstraintReduction.split` — the "equivalently" sentence: for a
  splitting of the constraint target (retained coordinate `ℓ` with
  `ℓ ∘ j = id`, complementary component `π` with `ker π = range j`), the
  factorization holds at `λ` iff the complementary component of
  `𝔠_k(ι_h(λ))` vanishes and its retained component is `Φ_h(λ)`;
* `ExactInitialConstraintReduction.constraint_zero_iff` — the exact zero set
  of the constraints along the family is the zero set of `Φ_h`.
-/

namespace RenewalGeometry

open Metric

section ExactInitialConstraintReduction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- `def:exact-initial-reduction`: an exact finite-dimensional constraint
reduction at the normalized initial record, with constraint map `Ck`, base
datum `x0 = 𝒰(ẑ_h)(0)`, reduced dimension `m = m_h`, radius `r = r_*` and
reader Lipschitz constant `B = B_*`. -/
structure ExactInitialConstraintReduction (Ck : X → Y) (x0 : X) (m : ℕ) (r B : ℝ) where
  /-- The correction family `λ ↦ ι_h(x_h, λ) ∈ 𝒳_k`. -/
  corr : EuclideanSpace ℝ (Fin m) → X
  /-- The correction family is `C¹` on `|λ| ≤ r_*`. -/
  corr_contDiffOn : ContDiffOn ℝ 1 corr (closedBall 0 r)
  /-- The fixed linear map `j_h : ℝ^{m_h} → 𝒴_k^con`. -/
  embed : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y
  /-- `j_h` is injective. -/
  embed_injective : Function.Injective embed
  /-- The retained constraint map `λ ↦ Φ_h(x_h, λ) ∈ ℝ^{m_h}`. -/
  retained : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)
  /-- `Φ_h` is `C¹` on `|λ| ≤ r_*`. -/
  retained_contDiffOn : ContDiffOn ℝ 1 retained (closedBall 0 r)
  /-- `eq:exact-initial-basepoint`: `ι_h(x_h, 0) = 𝒰(ẑ_h)(0)`. -/
  basepoint : corr 0 = x0
  /-- `eq:exact-initial-factorization`: `𝔠_k(ι_h(x_h, λ)) = j_h Φ_h(x_h, λ)` for `|λ| ≤ r_*`. -/
  factorization : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
    Ck (corr l) = embed (retained l)
  /-- `eq:exact-initial-reader-Lipschitz`:
  `‖ι_h(x_h, λ) - ι_h(x_h, μ)‖_{H^k} ≤ B_* |λ - μ|` on the ball. -/
  lipschitz : ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
    ∀ l' ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r, ‖corr l - corr l'‖ ≤ B * ‖l - l'‖

variable {E Z : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Z] [Module ℝ Z]

/-- Splitting form of the factorization: for a retained coordinate `ℓ`
(`ℓ ∘ j = id`) and a complementary component `π` with `π ∘ j = 0` and
`π y = 0 → y = j (ℓ y)` (i.e. `ker π = range j`), `y = j φ` holds iff the
complementary component of `y` vanishes and its retained component is `φ`. -/
theorem exactInitial_factorization_iff_split (j : E →ₗ[ℝ] Y) (ℓ : Y →ₗ[ℝ] E)
    (π : Y →ₗ[ℝ] Z) (hℓ : ∀ v, ℓ (j v) = v) (hπ : ∀ v, π (j v) = 0)
    (hsplit : ∀ y, π y = 0 → y = j (ℓ y)) (y : Y) (φ : E) :
    y = j φ ↔ π y = 0 ∧ ℓ y = φ := by
  constructor
  · rintro rfl
    exact ⟨hπ φ, hℓ φ⟩
  · rintro ⟨h0, h1⟩
    rw [hsplit y h0, h1]

/-- `def:exact-initial-reduction`, "equivalently": along the correction family
the complementary component of the constraints vanishes identically and the
retained component is `Φ_h`. -/
theorem ExactInitialConstraintReduction.split {Ck : X → Y} {x0 : X} {m : ℕ} {r B : ℝ}
    (R : ExactInitialConstraintReduction Ck x0 m r B)
    (ℓ : Y →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (π : Y →ₗ[ℝ] Z)
    (hℓ : ∀ v, ℓ (R.embed v) = v) (hπ : ∀ v, π (R.embed v) = 0)
    (l : EuclideanSpace ℝ (Fin m)) (hl : l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r) :
    π (Ck (R.corr l)) = 0 ∧ ℓ (Ck (R.corr l)) = R.retained l := by
  rw [R.factorization l hl]
  exact ⟨hπ _, hℓ _⟩

/-- Converse of `ExactInitialConstraintReduction.split`: a family whose
complementary component vanishes and whose retained component is `Φ` satisfies
the exact factorization `eq:exact-initial-factorization`. -/
theorem exactInitial_factorization_of_split {m : ℕ} (Ck : X → Y)
    (corr : EuclideanSpace ℝ (Fin m) → X) (j : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y)
    (Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ℓ : Y →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (π : Y →ₗ[ℝ] Z)
    (hsplit : ∀ y, π y = 0 → y = j (ℓ y)) (S : Set (EuclideanSpace ℝ (Fin m)))
    (hcomp : ∀ l ∈ S, π (Ck (corr l)) = 0) (hret : ∀ l ∈ S, ℓ (Ck (corr l)) = Φ l) :
    ∀ l ∈ S, Ck (corr l) = j (Φ l) := by
  intro l hl
  rw [hsplit _ (hcomp l hl), hret l hl]

/-- Along an exact reduction the exact constraint zero set is the zero set of the
retained map: `𝔠_k(ι_h(λ)) = 0 ↔ Φ_h(λ) = 0` for `|λ| ≤ r_*` (uses injectivity
of `j_h`). -/
theorem ExactInitialConstraintReduction.constraint_zero_iff {Ck : X → Y} {x0 : X} {m : ℕ}
    {r B : ℝ} (R : ExactInitialConstraintReduction Ck x0 m r B)
    (l : EuclideanSpace ℝ (Fin m)) (hl : l ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) r) :
    Ck (R.corr l) = 0 ↔ R.retained l = 0 := by
  rw [R.factorization l hl]
  constructor
  · intro h
    exact R.embed_injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end ExactInitialConstraintReduction

end RenewalGeometry
