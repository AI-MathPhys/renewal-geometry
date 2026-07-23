/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The discrete Cartan reconstruction

The discrete-geometry chapter of the manuscript, formalised as **exact
polynomial identities** (the manuscript's `O(h³)` statements are the
`h²`/`h³`-coefficient readings):

* **Theorem `thm:fundamental`** — `NCG.cartan_uniqueness`: a difference
  of two metric torsion-free connections vanishes (the six-step index
  chase); `NCG.koszul_antisym`, `NCG.koszul_torsion`: the discrete
  Koszul formula `γ_{d;ae} = ½(C_{dea} − C_{ade} − C_{ead})` is metric
  and solves the torsion equation; `NCG.cartan_derived_eq`: any metric
  torsion-free connection equals it.  (The `O(h²)` convergence to the
  Levi–Civita spin connection is not formalised.)

* **Proposition `prop:iso-metric`** — `NCG.first_order_orthogonal`:
  `(1−hγ)ᵀ(1−hγ) = 1 − h(γ+γᵀ) + h²·γᵀγ`, so the transport is
  orthogonal to first order iff `γᵀ = −γ`
  (`NCG.antisymm_iff_first_order_vanishes`,
  `NCG.first_order_orthogonal_of_antisymm`).

* **Definition `def:plaquette-defect` / Lemma `lem:plaquette-torsion`**
  — `NCG.plaquetteDefect`, `NCG.plaquette_defect_eq`: the traversal
  mismatch of the elementary plaquette is exactly
  `Δ = h²·T + h³·(cubic)`, `T = D_ie_j − D_je_i + γ_ie_j − γ_je_i`.

* **Definition `def:reset-motion` / Lemma `lem:plaquette-split`** —
  `NCG.euclComp`, `NCG.firstMoment`: reset channels as Euclidean
  motions `(R, t)`; `NCG.translational_defect`: the first-moment
  plaquette defect is exactly `h²·T`; `NCG.rotational_defect`: the
  rotation defect is exactly `−h²·F + h³·(cubic)`,
  `F = ∂_iγ_j − ∂_jγ_i + [γ_i, γ_j]`.

* **Theorem `thm:channel-torsion` / Corollary `cor:cix-discharged`** —
  `NCG.coeff_extraction` + `NCG.torsion_of_first_moment_closure`:
  vanishing of the defect at two distinct scales forces the `h²`
  coefficient — the torsion — to vanish, while the rotational
  (curvature) defect is untouched; combined with `cartan_derived_eq`
  the connection is the discrete Levi–Civita one. -/

namespace NCG

/-! ### The discrete fundamental theorem (`thm:fundamental`) -/

section Fundamental

variable {ι : Type*}

/-- **Theorem `thm:fundamental`, uniqueness**: a difference of
connections that is metric (`Δ_{d;ae} = −Δ_{d;ea}`) and satisfies the
homogeneous torsion equation (`Δ_{d;ae} = Δ_{e;ad}`) vanishes. -/
theorem cartan_uniqueness (Δ : ι → ι → ι → ℝ)
    (hQ : ∀ d a e, Δ d a e = -(Δ d e a))
    (hT : ∀ d a e, Δ d a e = Δ e a d) (d a e : ι) :
    Δ d a e = 0 := by
  have hchain : Δ d a e = -(Δ d a e) := by
    calc Δ d a e = Δ e a d := hT d a e
      _ = -(Δ e d a) := hQ e a d
      _ = -(Δ a d e) := by rw [hT e d a]
      _ = Δ a e d := by rw [hQ a d e, neg_neg]
      _ = Δ d e a := hT a e d
      _ = -(Δ d a e) := by rw [hQ d a e, neg_neg]
  linarith

/-- The **discrete Koszul formula**
`γ_{d;ae} = ½(C_{dea} − C_{ade} − C_{ead})`
(Theorem `thm:fundamental`). -/
noncomputable def koszul (C : ι → ι → ι → ℝ) (d a e : ι) : ℝ :=
  (C d e a - C a d e - C e a d) / 2

/-- The Koszul connection is metric: antisymmetric in the frame pair. -/
theorem koszul_antisym {C : ι → ι → ι → ℝ}
    (hC : ∀ x y z, C x y z = -(C x z y)) (d a e : ι) :
    koszul C d a e = -(koszul C d e a) := by
  unfold koszul
  have h1 := hC d e a
  have h2 := hC a d e
  have h3 := hC e a d
  linarith

/-- The Koszul connection solves the discrete torsion equation
`γ_{d;ae} − γ_{e;ad} = −C_{ade}` (Theorem `thm:fundamental`,
existence). -/
theorem koszul_torsion {C : ι → ι → ι → ℝ}
    (hC : ∀ x y z, C x y z = -(C x z y)) (d a e : ι) :
    koszul C d a e - koszul C e a d = -(C a d e) := by
  unfold koszul
  have h1 := hC d e a
  have h2 := hC e a d
  have h3 := hC a d e
  linarith

/-- **Theorems `thm:fundamental` / `thm:cartan-derived` /
`thm:discrete-cartan`** (algebraic core): every metric torsion-free
connection equals the discrete Koszul connection — with metric
compatibility from isometric comparison (`prop:iso-metric`) and
vanishing torsion from plaquette closure (`lem:plaquette-torsion`), the
induced connection is the unique discrete Levi–Civita connection. -/
theorem cartan_derived_eq {C : ι → ι → ι → ℝ}
    (hC : ∀ x y z, C x y z = -(C x z y)) (γ : ι → ι → ι → ℝ)
    (hγQ : ∀ d a e, γ d a e = -(γ d e a))
    (hγT : ∀ d a e, γ d a e - γ e a d = -(C a d e)) (d a e : ι) :
    γ d a e = koszul C d a e := by
  have hzero := cartan_uniqueness
    (fun d a e => γ d a e - koszul C d a e)
    (fun d a e => by
      have h1 := hγQ d a e
      have h2 := koszul_antisym hC d a e
      change γ d a e - koszul C d a e = -(γ d e a - koszul C d e a)
      linarith)
    (fun d a e => by
      have h1 := hγT d a e
      have h2 := koszul_torsion hC d a e
      change γ d a e - koszul C d a e = γ e a d - koszul C e a d
      linarith)
    d a e
  have hzero' : γ d a e - koszul C d a e = 0 := hzero
  linarith

end Fundamental

/-! ### Isometric comparison (`prop:iso-metric`) -/

section IsoMetric

open Matrix

variable {n : ℕ}

/-- **Proposition `prop:iso-metric`, expansion**: the exact Gram of the
near-identity transport,
`(1−hγ)ᵀ(1−hγ) = 1 − h(γ+γᵀ) + h²·γᵀγ`. -/
theorem first_order_orthogonal (γ : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) :
    (1 - h • γ)ᵀ * (1 - h • γ)
      = 1 - h • (γ + γᵀ) + (h ^ 2) • (γᵀ * γ) := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_add]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  ring

/-- **Proposition `prop:iso-metric`**: the first-order (metricity)
defect vanishes iff the generator is antisymmetric, `γ ∈ 𝔰𝔬(d)` —
isometric comparison is exactly metric compatibility `Q ≡ 0`. -/
theorem antisymm_iff_first_order_vanishes
    (γ : Matrix (Fin n) (Fin n) ℝ) :
    γᵀ = -γ ↔ γ + γᵀ = 0 := by
  constructor
  · intro hγ
    rw [hγ]
    abel
  · intro hγ
    have := congrArg (fun M => M - γ) hγ
    simp only [add_sub_cancel_left, zero_sub] at this
    exact this

/-- Antisymmetric generators give exactly-second-order Gram defect:
`(1−hγ)ᵀ(1−hγ) = 1 + h²·γᵀγ`. -/
theorem first_order_orthogonal_of_antisymm
    (γ : Matrix (Fin n) (Fin n) ℝ) (hγ : γᵀ = -γ) (h : ℝ) :
    (1 - h • γ)ᵀ * (1 - h • γ) = 1 + (h ^ 2) • (γᵀ * γ) := by
  rw [first_order_orthogonal,
    (antisymm_iff_first_order_vanishes γ).mp hγ]
  simp

end IsoMetric

/-! ### The plaquette defect (`def:plaquette-defect`,
`lem:plaquette-torsion`) -/

section Plaquette

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Definition `def:plaquette-defect`** (discrete model): the
`i`-then-`j` accumulated displacement, with transport `U⁻¹ = 1 + hγ`
and shifted coframe `e_j(x+he_i) = e_j + h·D_ie_j`. -/
def plaquetteDefect (h : ℝ) (ei ej Dij : V) (γi : V →ₗ[ℝ] V) : V :=
  h • ei + h • ((ej + h • Dij) + h • γi (ej + h • Dij))

/-- **Lemma `lem:plaquette-torsion`** (exact form): the traversal
mismatch of the elementary plaquette is
`Δ_{(ij)} − Δ_{(ji)} = h²·T + h³·(cubic)`,
`T = D_ie_j − D_je_i + γ_ie_j − γ_je_i` — first-order closure is
exactly vanishing discrete torsion. -/
theorem plaquette_defect_eq (h : ℝ) (ei ej Dij Dji : V)
    (γi γj : V →ₗ[ℝ] V) :
    plaquetteDefect h ei ej Dij γi - plaquetteDefect h ej ei Dji γj
      = (h ^ 2) • (Dij - Dji + γi ej - γj ei)
        + (h ^ 3) • (γi Dij - γj Dji) := by
  unfold plaquetteDefect
  simp only [map_add, map_smul]
  module

end Plaquette

/-! ### Reset motions and the plaquette split (`def:reset-motion`,
`lem:plaquette-split`) -/

section ResetMotion

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Definition `def:reset-motion`**: a reset channel's developed-frame
datum is a Euclidean motion `(R, t)` acting by `q ↦ Rq + t`; motions
compose by `(R₂,t₂)(R₁,t₁) = (R₂R₁, R₂t₁ + t₂)`. -/
def euclComp (g₂ g₁ : (V →ₗ[ℝ] V) × V) : (V →ₗ[ℝ] V) × V :=
  (g₂.1 ∘ₗ g₁.1, g₂.1 g₁.2 + g₂.2)

/-- The **first spatial moment** of a channel: the translation part of
its developed-frame motion (Definition `def:reset-motion`). -/
def firstMoment (g : (V →ₗ[ℝ] V) × V) : V := g.2

@[simp]
theorem firstMoment_euclComp (g₂ g₁ : (V →ₗ[ℝ] V) × V) :
    firstMoment (euclComp g₂ g₁) = g₂.1 g₁.2 + g₂.2 := rfl

/-- **Lemma `lem:plaquette-split`, translational half** (exact form):
with reset motions `g_i = (1 − hγ_i, he_i)` and shifted data, the
first-moment plaquette defect is **exactly** `h²·T` — torsion is the
translational defect. -/
theorem translational_defect (h : ℝ) (ei ej Dij Dji : V)
    (γi γj : V →ₗ[ℝ] V) :
    firstMoment (euclComp
        (LinearMap.id - h • γj, h • (ej + h • Dij))
        (LinearMap.id, h • ei))
      - firstMoment (euclComp
        (LinearMap.id - h • γi, h • (ei + h • Dji))
        (LinearMap.id, h • ej))
      = (h ^ 2) • (Dij - Dji + γi ej - γj ei) := by
  simp only [firstMoment_euclComp, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, map_smul]
  module

end ResetMotion

section Rotational

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Exact expansion of the composite rotation
`(1 − hγ_j − h²∂_iγ_j)(1 − hγ_i)`. -/
theorem rot_expand (h : ℝ) (γi γj Dij : A) :
    (1 - h • γj - (h ^ 2) • Dij) * (1 - h • γi)
      = 1 - h • γi - h • γj + (h ^ 2) • (γj * γi)
        - (h ^ 2) • Dij + (h ^ 3) • (Dij * γi) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm]
  module

/-- **Lemma `lem:plaquette-split`, rotational half** (exact form): the
rotation defect of the plaquette is
`−h²·F + h³·(cubic)`, `F = ∂_iγ_j − ∂_jγ_i + [γ_i,γ_j]` — curvature is
the rotational defect, untouched by first-moment closure
(`thm:channel-torsion`, Remark `rem:trans-only`). -/
theorem rotational_defect (h : ℝ) (γi γj Dij Dji : A) :
    (1 - h • γj - (h ^ 2) • Dij) * (1 - h • γi)
      - (1 - h • γi - (h ^ 2) • Dji) * (1 - h • γj)
      = -((h ^ 2) • (Dij - Dji + γi * γj - γj * γi))
        + (h ^ 3) • (Dij * γi - Dji * γj) := by
  rw [rot_expand, rot_expand]
  module

end Rotational

/-! ### The channel-composition torsion theorem
(`thm:channel-torsion`, `cor:cix-discharged`) -/

section Torsion

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [NoZeroSMulDivisors ℝ V]

/-- **Coefficient extraction**: a vector polynomial
`h²·T + h³·C` vanishing at two distinct nonzero scales has both
coefficients zero — the formal content of "the `O(h²)` coefficient
vanishes". -/
theorem coeff_extraction {T C : V} {h₁ h₂ : ℝ}
    (hne₁ : h₁ ≠ 0) (hne₂ : h₂ ≠ 0) (hdist : h₁ ≠ h₂)
    (e₁ : (h₁ ^ 2) • T + (h₁ ^ 3) • C = 0)
    (e₂ : (h₂ ^ 2) • T + (h₂ ^ 3) • C = 0) :
    T = 0 ∧ C = 0 := by
  have hdiv : ∀ (h : ℝ), h ≠ 0 →
      (h ^ 2) • T + (h ^ 3) • C = 0 → T + h • C = 0 := by
    intro h hne he
    have h2 := congrArg (fun x => ((h ^ 2)⁻¹ : ℝ) • x) he
    simp only [smul_add, smul_smul, smul_zero] at h2
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hne), one_smul,
      show ((h ^ 2)⁻¹ : ℝ) * h ^ 3 = h by
        rw [show (h : ℝ) ^ 3 = h ^ 2 * h by ring, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero 2 hne), one_mul]] at h2
    exact h2
  have f₁ := hdiv h₁ hne₁ e₁
  have f₂ := hdiv h₂ hne₂ e₂
  have hC : C = 0 := by
    have hsub : (h₁ - h₂) • C = 0 := by
      have h3 : T + h₁ • C - (T + h₂ • C) = (h₁ - h₂) • C := by
        rw [sub_smul]
        abel
      rw [← h3, f₁, f₂, sub_zero]
    rcases smul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hdist
    · exact h
  refine ⟨?_, hC⟩
  have := f₁
  rw [hC, smul_zero, add_zero] at this
  exact this

/-- **Theorem `thm:channel-torsion` / Corollary `cor:cix-discharged`**:
first-moment plaquette closure (vanishing translational defect at two
scales) forces the discrete torsion to vanish — the torsion-free Cartan
rule is a consequence of the reset-channel first moments, while the
rotational (curvature) defect is unconstrained. -/
theorem torsion_of_first_moment_closure
    (ei ej Dij Dji : V) (γi γj : V →ₗ[ℝ] V) {h₁ h₂ : ℝ}
    (hne₁ : h₁ ≠ 0) (hne₂ : h₂ ≠ 0) (hdist : h₁ ≠ h₂)
    (hclosure : ∀ h ∈ ({h₁, h₂} : Set ℝ),
      plaquetteDefect h ei ej Dij γi
        - plaquetteDefect h ej ei Dji γj = 0) :
    Dij - Dji + γi ej - γj ei = 0 := by
  have e₁ := hclosure h₁ (Or.inl rfl)
  have e₂ := hclosure h₂ (Or.inr rfl)
  rw [plaquette_defect_eq] at e₁ e₂
  exact (coeff_extraction hne₁ hne₂ hdist e₁ e₂).1

end Torsion

/-- **Lemma `lem:covariant-consistency` (cancellation core)**: the
order-`h²` brackets of the forward and backward midpoint transports
agree, so they cancel in the central difference — the covariant
central difference reproduces exactly `2h` times the derivative term,
leaving a remainder of order `h³` (hence `O(h²)` after division by
`2h`). -/
theorem central_difference_second_order {V : Type*} [AddCommGroup V]
    [Module ℝ V] (h : ℝ) (ψ dψ c : V) :
    (ψ + h • dψ + (h ^ 2) • c) - (ψ - h • dψ + (h ^ 2) • c)
      = (2 * h) • dψ := by
  module

end NCG
