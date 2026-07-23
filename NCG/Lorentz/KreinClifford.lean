/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Krein–Clifford reset datum and the emergent metric

This file formalises the algebraic layer of the continuum construction:

* **Definition `def:krein-clifford`** — `NCG.KreinCliffordDatum`: a
  fundamental symmetry `J`, a Krein-odd timelike generator `γ⁰`, and
  Euclidean spatial generators `γ¹, …, γ^d` with the displayed star and
  (anti)commutation relations;
* **the Clifford square** — `NCG.clifford_square`:
  `(Σ aᵢ γᵢ)² = (Σ aᵢ²)·1`, so unit directions satisfy `γ(θ)² = 1`;
* **Lemma `lem:symbol-square`** — `NCG.symbol_square`: the spacetime
  symbol squares to the scalar quadratic form
  `(ξ₀γ⁰ + Σ aᵢγᵢ)² = (q·ξ₀² + Σ aᵢ²)·1`, `q = (γ⁰)²` — the emergent
  inverse metric `g = diag(−q, −κ²M²)` after the `i`-prefactor;
* **Theorem `thm:signature-krein`, sign dichotomy** —
  `NCG.signature_lorentzian_iff`: the timelike slot `−q` is positive iff
  `q = −1`; the spatial block is negative (semi)definite always;
* **Lemma `lem:alpha-selfadjoint`, matrix part** — `NCG.alpha_star`,
  `NCG.alpha_mul`, `NCG.alpha_cliff`, `NCG.multiplier_star`,
  `NCG.multiplier_square`: the Dirac matrices `Aⁱ = γ⁰γⁱ` are Hermitian,
  satisfy `{Aⁱ,Aʲ} = 2δ`, and the multiplier `h(ξ) = Σ aᵢAⁱ` is
  Hermitian with `h(ξ)² = |a|²·1`.  (The Sobolev-domain self-adjointness
  of the Fourier multiplier operator is not formalised.)

* **Definition `def:dirac-symbol`** — `NCG.symbol_through_second_moment`:
  the coarse-grained symbol depends on the direction measure only
  through its second moment, `Σ_a p_a γ(θ_a)(θ_a·ξ) = Σᵢⱼ γᵢ Mᵢⱼ ξⱼ`. -/

namespace NCG

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **The Clifford square** `(Σ aᵢ gᵢ)² = (Σ aᵢ²)·1` for anticommuting
generators with `gᵢgⱼ + gⱼgᵢ = 2δᵢⱼ` (Definition `def:krein-clifford`:
`γ(θ)² = 1` on unit directions; Lemma `lem:alpha-selfadjoint`:
`h(ξ)² = |Mξ|²·1`). -/
theorem clifford_square {d : ℕ} (g : Fin d → A)
    (hrel : ∀ i j, g i * g j + g j * g i
      = (if i = j then (2 : ℝ) else 0) • 1)
    (a : Fin d → ℝ) :
    (∑ i, a i • g i) * (∑ i, a i • g i) = (∑ i, a i ^ 2) • 1 := by
  have hexp : ∀ b c : Fin d → ℝ,
      (∑ i, b i • g i) * (∑ j, c j • g j)
        = ∑ i, ∑ j, (b i * c j) • (g i * g j) := by
    intro b c
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hdouble :
      (2 : ℝ) • ((∑ i, a i • g i) * (∑ i, a i • g i))
        = (2 : ℝ) • ((∑ i, a i ^ 2) • (1 : A)) := by
    rw [two_smul, two_smul]
    calc (∑ i, a i • g i) * (∑ i, a i • g i)
          + (∑ i, a i • g i) * (∑ i, a i • g i)
        = (∑ i, ∑ j, (a i * a j) • (g i * g j))
          + ∑ j, ∑ i, (a i * a j) • (g i * g j) := by
          rw [hexp a a]
          congr 1
          exact Finset.sum_comm
      _ = ∑ i, ∑ j, ((a i * a j) • (g i * g j)
            + (a j * a i) • (g j * g i)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, (a i * a j) • (g i * g j + g j * g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_add, mul_comm (a j) (a i)]
      _ = ∑ i, ∑ j,
            (if i = j then (a i * a j * 2 : ℝ) else 0) • (1 : A) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hrel i j, smul_smul, mul_ite, mul_zero]
      _ = ∑ i, (a i * a i * 2) • (1 : A) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [ite_smul]
      _ = (∑ i, a i ^ 2) • (1:A) + (∑ i, a i ^ 2) • (1:A) := by
          rw [← Finset.sum_smul, ← add_smul, ← Finset.sum_add_distrib]
          refine congrArg (· • (1:A)) ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have h2 := congrArg (fun x => ((1:ℝ)/2) • x) hdouble
  simp only [smul_smul] at h2
  rw [show ((1:ℝ)/2) * (2 * ∑ i, a i ^ 2) = ∑ i, a i ^ 2 by ring,
    show ((1:ℝ)/2) * 2 = 1 by norm_num, one_smul] at h2
  exact h2

/-- **Definition `def:krein-clifford`**: a Krein–Clifford reset datum —
fundamental symmetry `J`, Krein-odd timelike generator `γ⁰`, Euclidean
spatial generators with the standard relations.  The modular square
`q = (γ⁰)²` is the sole signature branch. -/
structure KreinCliffordDatum (A : Type*) [Ring A] [Algebra ℝ A]
    [StarRing A] (d : ℕ) where
  /-- the fundamental symmetry -/
  J : A
  /-- the timelike (modular) generator `γ⁰ = R_{α₀}` -/
  γ0 : A
  /-- the spatial generators -/
  γ : Fin d → A
  J_star : star J = J
  J_sq : J * J = 1
  J_γ0 : J * γ0 * J = -γ0
  J_γ : ∀ i, J * γ i * J = γ i
  γ0_star : star γ0 = -γ0
  γ_star : ∀ i, star (γ i) = γ i
  anticomm0 : ∀ i, γ0 * γ i = -(γ i * γ0)
  cliff : ∀ i j, γ i * γ j + γ j * γ i
    = (if i = j then (2 : ℝ) else 0) • 1

namespace KreinCliffordDatum

variable [StarRing A] {d : ℕ} (D : KreinCliffordDatum A d)

/-- `γ(θ)² = 1` for unit spatial directions
(Definition `def:krein-clifford`). -/
theorem gamma_dir_sq (θ : Fin d → ℝ) (hθ : ∑ i, θ i ^ 2 = 1) :
    (∑ i, θ i • D.γ i) * (∑ i, θ i • D.γ i) = 1 := by
  rw [clifford_square D.γ D.cliff θ, hθ, one_smul]

/-- **Lemma `lem:alpha-selfadjoint`**: the Dirac matrices `Aⁱ = γ⁰γⁱ`
are Hermitian — the Krein-odd star of `γ⁰` compensates the
anticommutation. -/
theorem alpha_star (i : Fin d) :
    star (D.γ0 * D.γ i) = D.γ0 * D.γ i := by
  rw [star_mul, D.γ_star, D.γ0_star, mul_neg, D.anticomm0 i]

/-- In the Lorentzian branch `(γ⁰)² = −1`, the products collapse:
`AⁱAʲ = γⁱγʲ` (Lemma `lem:alpha-selfadjoint`). -/
theorem alpha_mul (hq : D.γ0 * D.γ0 = (-1 : ℝ) • 1) (i j : Fin d) :
    (D.γ0 * D.γ i) * (D.γ0 * D.γ j) = D.γ i * D.γ j := by
  have hswap : D.γ i * D.γ0 = -(D.γ0 * D.γ i) := by
    rw [D.anticomm0 i, neg_neg]
  calc (D.γ0 * D.γ i) * (D.γ0 * D.γ j)
      = D.γ0 * (D.γ i * D.γ0) * D.γ j := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = D.γ0 * -(D.γ0 * D.γ i) * D.γ j := by rw [hswap]
    _ = -((D.γ0 * D.γ0) * (D.γ i * D.γ j)) := by
        rw [mul_neg, neg_mul]
        congr 1
        rw [← mul_assoc, mul_assoc]
    _ = -(((-1 : ℝ) • 1) * (D.γ i * D.γ j)) := by
        rw [hq]
    _ = D.γ i * D.γ j := by
        rw [smul_mul_assoc, one_mul, neg_smul, one_smul, neg_neg]

/-- **Lemma `lem:alpha-selfadjoint`**: `{Aⁱ, Aʲ} = 2δⁱʲ`. -/
theorem alpha_cliff (hq : D.γ0 * D.γ0 = (-1 : ℝ) • 1) (i j : Fin d) :
    (D.γ0 * D.γ i) * (D.γ0 * D.γ j)
      + (D.γ0 * D.γ j) * (D.γ0 * D.γ i)
      = (if i = j then (2 : ℝ) else 0) • 1 := by
  rw [alpha_mul D hq, alpha_mul D hq, D.cliff]

variable [StarModule ℝ A]

/-- **Lemma `lem:alpha-selfadjoint`**: the multiplier `h(ξ) = Σ aᵢAⁱ`
is Hermitian. -/
theorem multiplier_star (a : Fin d → ℝ) :
    star (∑ i, a i • (D.γ0 * D.γ i))
      = ∑ i, a i • (D.γ0 * D.γ i) := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, alpha_star, star_trivial]

omit [StarModule ℝ A] in
/-- **Lemma `lem:alpha-selfadjoint`**: the multiplier squares to the
scalar `|a|²·1` — with `a = κMξ` this is
`h(ξ)² = κ²·ξᵀM²ξ·1`. -/
theorem multiplier_square (hq : D.γ0 * D.γ0 = (-1 : ℝ) • 1)
    (a : Fin d → ℝ) :
    (∑ i, a i • (D.γ0 * D.γ i)) * (∑ i, a i • (D.γ0 * D.γ i))
      = (∑ i, a i ^ 2) • 1 :=
  clifford_square (fun i => D.γ0 * D.γ i) (alpha_cliff D hq) a

omit [StarModule ℝ A] in
/-- **Lemma `lem:symbol-square`**: the spacetime symbol squares to a
scalar — the emergent inverse metric.  With `q = (γ⁰)²` and spatial
coefficients `a = κMξ`,

`(ξ₀γ⁰ + Σ aᵢγᵢ)² = (q·ξ₀² + |a|²)·1`,

so after the `i`-prefactor `g = diag(−q, −κ²M²)`. -/
theorem symbol_square {q : ℝ} (hq : D.γ0 * D.γ0 = q • 1)
    (ξ0 : ℝ) (a : Fin d → ℝ) :
    (ξ0 • D.γ0 + ∑ i, a i • D.γ i)
        * (ξ0 • D.γ0 + ∑ i, a i • D.γ i)
      = (q * ξ0 ^ 2 + ∑ i, a i ^ 2) • 1 := by
  have hcross : D.γ0 * (∑ i, a i • D.γ i)
      + (∑ i, a i • D.γ i) * D.γ0 = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, D.anticomm0 i]
    simp
  have hS := clifford_square D.γ D.cliff a
  rw [add_mul, mul_add, mul_add]
  rw [smul_mul_smul_comm, hq, smul_smul]
  rw [smul_mul_assoc, mul_smul_comm, hS]
  have hcross' : ξ0 • (D.γ0 * ∑ i, a i • D.γ i)
      + ξ0 • ((∑ i, a i • D.γ i) * D.γ0) = 0 := by
    rw [← smul_add, hcross, smul_zero]
  calc (ξ0 * ξ0 * q) • (1:A)
        + ξ0 • (D.γ0 * ∑ i, a i • D.γ i)
        + (ξ0 • ((∑ i, a i • D.γ i) * D.γ0)
          + (∑ i, a i ^ 2) • 1)
      = (ξ0 * ξ0 * q) • (1:A) + (∑ i, a i ^ 2) • 1
        + (ξ0 • (D.γ0 * ∑ i, a i • D.γ i)
          + ξ0 • ((∑ i, a i • D.γ i) * D.γ0)) := by abel
    _ = (q * ξ0 ^ 2 + ∑ i, a i ^ 2) • 1 := by
        rw [hcross', add_zero, ← add_smul]
        congr 1
        ring

end KreinCliffordDatum

/-- **Theorem `thm:signature-krein`, sign dichotomy**: for the modular
square `q ∈ {±1}`, the timelike slot `−q` of the emergent metric is
positive iff `q = −1` — the Lorentzian branch is exactly
`R_{α₀}² = −1`; `q = +1` gives the negative-definite branch. -/
theorem signature_lorentzian_iff {q : ℝ} (hq : q = 1 ∨ q = -1) :
    0 < -q ↔ q = -1 := by
  rcases hq with rfl | rfl <;> norm_num

/-- **Theorem `thm:signature-krein` (i)**: the spatial block of the
emergent metric is negative definite — for a spanning direction system
(`Mξ ≠ 0` for `ξ ≠ 0`) the spatial quadratic form is strictly
negative. -/
theorem spatial_block_negative {d : ℕ} {κ : ℝ} (hκ : κ ≠ 0)
    (a : Fin d → ℝ) (ha : a ≠ 0) :
    -κ ^ 2 * ∑ i, a i ^ 2 < 0 := by
  have hpos : 0 < ∑ i, a i ^ 2 := by
    rcases Function.ne_iff.mp ha with ⟨i, hi⟩
    have hile : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a j))
        (Finset.mem_univ i)
    have hne : a i ^ 2 ≠ 0 := pow_ne_zero 2 hi
    have : 0 < a i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    linarith
  have : 0 < κ ^ 2 := by positivity
  nlinarith

/-- **Definition `def:dirac-symbol`** (dependence through the second
moment): the coarse-grained spatial symbol equals the `M`-contracted
generator sum,

`Σ_a p_a (θ_a·ξ)·γ(θ_a) = Σᵢ (Σⱼ Mᵢⱼ ξⱼ)·γᵢ`,  `Mᵢⱼ = Σ_a p_a θ_aⁱθ_aʲ`

— the symbol depends on the direction measure only through `M(ν)`. -/
theorem symbol_through_second_moment {m d : ℕ}
    (θ : Fin m → Fin d → ℝ) (p : Fin m → ℝ) (ξ : Fin d → ℝ)
    (g : Fin d → A) :
    ∑ a, (p a * ∑ j, θ a j * ξ j) • (∑ i, θ a i • g i)
      = ∑ i, (∑ j, (∑ a, p a * θ a i * θ a j) * ξ j) • g i := by
  calc ∑ a, (p a * ∑ j, θ a j * ξ j) • (∑ i, θ a i • g i)
      = ∑ a, ∑ i, ((p a * ∑ j, θ a j * ξ j) * θ a i) • g i := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
    _ = ∑ i, ∑ a, ((p a * ∑ j, θ a j * ξ j) * θ a i) • g i :=
        Finset.sum_comm
    _ = ∑ i, (∑ j, (∑ a, p a * θ a i * θ a j) * ξ j) • g i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        calc ∑ a, p a * (∑ j, θ a j * ξ j) * θ a i
            = ∑ a, ∑ j, p a * θ a i * θ a j * ξ j := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ = ∑ j, ∑ a, p a * θ a i * θ a j * ξ j := Finset.sum_comm
          _ = ∑ j, (∑ a, p a * θ a i * θ a j) * ξ j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]

end NCG
