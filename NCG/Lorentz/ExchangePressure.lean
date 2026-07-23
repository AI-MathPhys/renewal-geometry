/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exchange-source pressure and its torsion-free stationary point

Definition `def:exchange-source-pressure` and Theorem
`thm:exchange-pressure-stationarity` of `manuscripts/renewal_emergence/renewal_emergence.tex`.

On a finite resolved diamond space `Ω` with exchange involution `ϑ`,
exchange-even action `S` and exchange-odd defect `D : Ω → V`, the
exchange-source pressure of a covector `l` is

`Ψ(l) = log ∑_ω exp (−S ω + l (D ω))`  (`exchangePressure`).

Everything is derived from one master estimate for finite exponential
sums, `sq_sum_exp_avg_le` (with strict version
`sq_sum_exp_avg_lt`): `(∑ e^{(u+v)/2})² ≤ (∑ e^u)(∑ e^v)`, proved by
pair symmetrization and AM–GM — the integrated form of
`∇²Ψ = Cov ⪰ 0`.  The clauses of the theorem:

* `exchangePressure_neg` — evenness `Ψ(−l) = Ψ(l)` (change of
  variables along `ϑ`);
* `exchangePressure_midpoint_convex` — midpoint convexity, the
  positive-semidefinite-Hessian clause in integrated form;
* `exchangePressure_zero_le` — `λ = 0` is a global minimum;
* `exchangePressure_eq_zero_iff` — the minimum is unique modulo the
  annihilator of `span {D ω − D ω'}`;
* `hasDerivAt_exchangePressure` — the gradient identity
  `∇Ψ = 𝔼_{π_λ} D` as a genuine directional derivative, with the
  Gibbs expectation `gibbsExpect`;
* `gibbsExpect_defect_zero` / `sum_exp_smul_defect_zero` — at zero
  source the Gibbs mean of every exchange-odd defect vanishes: zero
  exchange source is exactly the Euler–Lagrange condition for
  first-moment plaquette closure.
-/

namespace NCG

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## The master exponential-sum estimate -/

/-- Pointwise AM–GM for exponentials:
`2 e^{(x+y)/2} ≤ e^x + e^y`. -/
theorem two_exp_avg_le (x y : ℝ) :
    2 * Real.exp ((x + y) / 2) ≤ Real.exp x + Real.exp y := by
  have h1 : Real.exp ((x + y) / 2)
      = Real.exp (x / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [sq_nonneg (Real.exp (x / 2) - Real.exp (y / 2))]

/-- Strict pointwise AM–GM for `x ≠ y`. -/
theorem two_exp_avg_lt {x y : ℝ} (hxy : x ≠ y) :
    2 * Real.exp ((x + y) / 2) < Real.exp x + Real.exp y := by
  have h1 : Real.exp ((x + y) / 2)
      = Real.exp (x / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h4 : Real.exp (x / 2) ≠ Real.exp (y / 2) := by
    intro hcon
    exact hxy (by
      have := Real.exp_injective hcon
      linarith)
  have h5 : 0 < (Real.exp (x / 2) - Real.exp (y / 2)) ^ 2 := by
    have h6 : Real.exp (x / 2) - Real.exp (y / 2) ≠ 0 :=
      sub_ne_zero.mpr h4
    positivity
  nlinarith

/-- **The master estimate**: `(∑ e^{(u+v)/2})² ≤ (∑ e^u)(∑ e^v)` —
the integrated positive-semidefinite-Hessian inequality of the
exchange-source pressure. -/
theorem sq_sum_exp_avg_le (u v : Ω → ℝ) :
    (∑ ω, Real.exp ((u ω + v ω) / 2)) ^ 2
      ≤ (∑ ω, Real.exp (u ω)) * (∑ ω, Real.exp (v ω)) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.exp (u ω / 2)) (fun ω => Real.exp (v ω / 2))
  have h2 : ∀ ω : Ω, Real.exp (u ω / 2) * Real.exp (v ω / 2)
      = Real.exp ((u ω + v ω) / 2) := by
    intro ω
    rw [← Real.exp_add]
    ring_nf
  have h3 : ∀ ω : Ω, Real.exp (u ω / 2) ^ 2 = Real.exp (u ω) := by
    intro ω
    rw [sq, ← Real.exp_add]
    ring_nf
  have h4 : ∀ ω : Ω, Real.exp (v ω / 2) ^ 2 = Real.exp (v ω) := by
    intro ω
    rw [sq, ← Real.exp_add]
    ring_nf
  calc (∑ ω, Real.exp ((u ω + v ω) / 2)) ^ 2
      = (∑ ω, Real.exp (u ω / 2) * Real.exp (v ω / 2)) ^ 2 := by
        rw [Finset.sum_congr rfl fun ω _ => (h2 ω).symm]
    _ ≤ (∑ ω, Real.exp (u ω / 2) ^ 2)
        * (∑ ω, Real.exp (v ω / 2) ^ 2) := h1
    _ = (∑ ω, Real.exp (u ω)) * (∑ ω, Real.exp (v ω)) := by
        rw [Finset.sum_congr rfl fun ω _ => h3 ω,
          Finset.sum_congr rfl fun ω _ => h4 ω]

/-- **Strict master estimate**: strict whenever `u − v` is not
constant — pair symmetrization plus strict AM–GM on one pair. -/
theorem sq_sum_exp_avg_lt {u v : Ω → ℝ} {ω₀ ω₁ : Ω}
    (hne : u ω₀ - v ω₀ ≠ u ω₁ - v ω₁) :
    (∑ ω, Real.exp ((u ω + v ω) / 2)) ^ 2
      < (∑ ω, Real.exp (u ω)) * (∑ ω, Real.exp (v ω)) := by
  classical
  -- double sums over ordered pairs
  have hL : (∑ ω, Real.exp (u ω)) * (∑ ω, Real.exp (v ω))
      = ∑ p : Ω × Ω, Real.exp (u p.1 + v p.2) := by
    rw [Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.exp_add]
  have hR : (∑ ω, Real.exp ((u ω + v ω) / 2)) ^ 2
      = ∑ p : Ω × Ω,
          Real.exp ((u p.1 + v p.1) / 2 + (u p.2 + v p.2) / 2) := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.exp_add]
  -- symmetrize the left double sum via the swap bijection
  have hswap : ∑ p : Ω × Ω, Real.exp (u p.1 + v p.2)
      = ∑ p : Ω × Ω, Real.exp (u p.2 + v p.1) := by
    exact Fintype.sum_equiv (Equiv.prodComm Ω Ω)
      (fun p => Real.exp (u p.1 + v p.2))
      (fun p => Real.exp (u p.2 + v p.1))
      (fun p => rfl)
  have hpair : ∀ p : Ω × Ω,
      2 * Real.exp ((u p.1 + v p.1) / 2 + (u p.2 + v p.2) / 2)
        ≤ Real.exp (u p.1 + v p.2) + Real.exp (u p.2 + v p.1) := by
    intro p
    have h1 := two_exp_avg_le (u p.1 + v p.2) (u p.2 + v p.1)
    have h2 : (u p.1 + v p.2 + (u p.2 + v p.1)) / 2
        = (u p.1 + v p.1) / 2 + (u p.2 + v p.2) / 2 := by ring
    rwa [h2] at h1
  have hstrict :
      2 * Real.exp ((u ω₀ + v ω₀) / 2 + (u ω₁ + v ω₁) / 2)
        < Real.exp (u ω₀ + v ω₁) + Real.exp (u ω₁ + v ω₀) := by
    have h1 : u ω₀ + v ω₁ ≠ u ω₁ + v ω₀ := by
      intro hcon
      exact hne (by linarith)
    have h2 := two_exp_avg_lt h1
    have h3 : (u ω₀ + v ω₁ + (u ω₁ + v ω₀)) / 2
        = (u ω₀ + v ω₀) / 2 + (u ω₁ + v ω₁) / 2 := by ring
    rwa [h3] at h2
  -- sum the pointwise bounds, one of them strictly
  have hsum : 2 * ∑ p : Ω × Ω,
      Real.exp ((u p.1 + v p.1) / 2 + (u p.2 + v p.2) / 2)
      < 2 * ∑ p : Ω × Ω, Real.exp (u p.1 + v p.2) := by
    have h4 : ∑ p : Ω × Ω,
        2 * Real.exp ((u p.1 + v p.1) / 2 + (u p.2 + v p.2) / 2)
        < ∑ p : Ω × Ω,
          (Real.exp (u p.1 + v p.2) + Real.exp (u p.2 + v p.1)) := by
      refine Finset.sum_lt_sum (fun p _ => hpair p)
        ⟨(ω₀, ω₁), Finset.mem_univ _, hstrict⟩
    have h5 : ∑ p : Ω × Ω,
        (Real.exp (u p.1 + v p.2) + Real.exp (u p.2 + v p.1))
        = 2 * ∑ p : Ω × Ω, Real.exp (u p.1 + v p.2) := by
      rw [Finset.sum_add_distrib, ← hswap, two_mul]
    rw [← Finset.mul_sum] at h4
    rw [h5] at h4
    exact h4
  rw [hL, hR]
  linarith

/-! ## The exchange-source pressure -/

/-- The partition function at source `b`. -/
noncomputable def sourcePartition (S b : Ω → ℝ) : ℝ :=
  ∑ ω, Real.exp (-S ω + b ω)

theorem sourcePartition_pos (S b : Ω → ℝ) :
    0 < sourcePartition S b :=
  Finset.sum_pos (fun ω _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Definition `def:exchange-source-pressure`** (scalar-source
form): the pressure `log ∑ exp (−S + b)`. -/
noncomputable def sourcePressure (S b : Ω → ℝ) : ℝ :=
  Real.log (sourcePartition S b)

/-- The Gibbs expectation of an observable at source `b`. -/
noncomputable def gibbsExpect (S b m : Ω → ℝ) : ℝ :=
  (∑ ω, m ω * Real.exp (-S ω + b ω)) / sourcePartition S b

section Exchange

variable {ϑ : Ω → Ω} (hinv : Function.Involutive ϑ)

include hinv

/-- Change of variables along the exchange involution. -/
theorem sourcePartition_exchange {S b : Ω → ℝ}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hb : ∀ ω, b (ϑ ω) = -b ω) :
    sourcePartition S (fun ω => -b ω) = sourcePartition S b := by
  unfold sourcePartition
  rw [← Equiv.sum_comp (Function.Involutive.toPerm ϑ hinv)
    (fun ω => Real.exp (-S ω + b ω))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h1 : (Function.Involutive.toPerm ϑ hinv) ω = ϑ ω := rfl
  rw [h1, hS ω, hb ω]

/-- **`thm:exchange-pressure-stationarity`, evenness**:
`Ψ(−b) = Ψ(b)`. -/
theorem sourcePressure_neg {S b : Ω → ℝ}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hb : ∀ ω, b (ϑ ω) = -b ω) :
    sourcePressure S (fun ω => -b ω) = sourcePressure S b := by
  unfold sourcePressure
  rw [sourcePartition_exchange hinv hS hb]

/-- **`thm:exchange-pressure-stationarity`, global minimum**: the
zero source minimizes the pressure. -/
theorem sourcePressure_zero_le {S b : Ω → ℝ}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hb : ∀ ω, b (ϑ ω) = -b ω) :
    sourcePressure S 0 ≤ sourcePressure S b := by
  -- Ψ(b) + Ψ(−b) ≥ 2Ψ(0) by the master estimate
  have h1 := sq_sum_exp_avg_le (Ω := Ω)
    (fun ω => -S ω + b ω) (fun ω => -S ω + -b ω)
  have h2 : ∀ ω : Ω, (-S ω + b ω + (-S ω + -b ω)) / 2
      = -S ω + (0 : Ω → ℝ) ω := by
    intro ω
    simp only [Pi.zero_apply]
    ring
  rw [Finset.sum_congr rfl fun ω _ => by rw [h2 ω]] at h1
  have h3 : (sourcePartition S 0) ^ 2
      ≤ sourcePartition S b * sourcePartition S (fun ω => -b ω) := by
    unfold sourcePartition
    exact h1
  rw [sourcePartition_exchange hinv hS hb] at h3
  have h4 : Real.log ((sourcePartition S 0) ^ 2)
      ≤ Real.log ((sourcePartition S b) ^ 2) := by
    refine Real.log_le_log (pow_pos (sourcePartition_pos S 0) 2) ?_
    calc (sourcePartition S 0) ^ 2
        ≤ sourcePartition S b * sourcePartition S b := h3
      _ = (sourcePartition S b) ^ 2 := (sq _).symm
  rw [Real.log_pow, Real.log_pow] at h4
  unfold sourcePressure
  push_cast at h4
  linarith

/-- **`thm:exchange-pressure-stationarity`, uniqueness modulo the
annihilator**: the pressure equals its minimum exactly when the
source is constant on the diamond space (equivalently, kills every
difference `D ω − D ω'`); by oddness the constant is zero. -/
theorem sourcePressure_eq_zero_iff {S b : Ω → ℝ}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hb : ∀ ω, b (ϑ ω) = -b ω) :
    sourcePressure S b = sourcePressure S 0
      ↔ ∀ ω ω' : Ω, b ω = b ω' := by
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    obtain ⟨ω₀, ω₁, hne⟩ := hcon
    -- strict master estimate
    have h1 := sq_sum_exp_avg_lt (Ω := Ω)
      (u := fun ω => -S ω + b ω) (v := fun ω => -S ω + -b ω)
      (ω₀ := ω₀) (ω₁ := ω₁) (by
        intro hcon2
        exact hne (by linarith))
    have h2 : ∀ ω : Ω, (-S ω + b ω + (-S ω + -b ω)) / 2
        = -S ω + (0 : Ω → ℝ) ω := by
      intro ω
      simp only [Pi.zero_apply]
      ring
    rw [Finset.sum_congr rfl fun ω _ => by rw [h2 ω]] at h1
    have h3 : (sourcePartition S 0) ^ 2
        < sourcePartition S b
          * sourcePartition S (fun ω => -b ω) := h1
    rw [sourcePartition_exchange hinv hS hb] at h3
    have h4 : Real.log ((sourcePartition S 0) ^ 2)
        < Real.log ((sourcePartition S b) ^ 2) := by
      refine Real.log_lt_log (pow_pos (sourcePartition_pos S 0) 2) ?_
      calc (sourcePartition S 0) ^ 2
          < sourcePartition S b * sourcePartition S b := h3
        _ = (sourcePartition S b) ^ 2 := (sq _).symm
    rw [Real.log_pow, Real.log_pow] at h4
    unfold sourcePressure at heq
    simp only [Nat.cast_ofNat] at h4
    linarith
  · intro hconst
    -- a constant odd source is zero
    have hzero : ∀ ω, b ω = 0 := by
      intro ω
      have h1 := hconst ω (ϑ ω)
      rw [hb ω] at h1
      linarith
    unfold sourcePressure sourcePartition
    congr 1
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hzero ω]
    simp

omit hinv in
/-- **`thm:exchange-pressure-stationarity`, midpoint convexity** —
the positive-semidefinite Hessian (`∇²Ψ = Cov ⪰ 0`) in integrated
form: `2 Ψ((b₁+b₂)/2) ≤ Ψ(b₁) + Ψ(b₂)`. -/
theorem sourcePressure_midpoint_convex (S b₁ b₂ : Ω → ℝ) :
    2 * sourcePressure S (fun ω => (b₁ ω + b₂ ω) / 2)
      ≤ sourcePressure S b₁ + sourcePressure S b₂ := by
  have h1 := sq_sum_exp_avg_le (Ω := Ω)
    (fun ω => -S ω + b₁ ω) (fun ω => -S ω + b₂ ω)
  have h2 : ∀ ω : Ω, (-S ω + b₁ ω + (-S ω + b₂ ω)) / 2
      = -S ω + (b₁ ω + b₂ ω) / 2 := by
    intro ω
    ring
  rw [Finset.sum_congr rfl fun ω _ => by rw [h2 ω]] at h1
  have h3 : (sourcePartition S (fun ω => (b₁ ω + b₂ ω) / 2)) ^ 2
      ≤ sourcePartition S b₁ * sourcePartition S b₂ := h1
  have h4 := Real.log_le_log (x := (sourcePartition S
    (fun ω => (b₁ ω + b₂ ω) / 2)) ^ 2)
    (pow_pos (sourcePartition_pos S _) 2) h3
  rw [Real.log_pow, Real.log_mul
    (sourcePartition_pos S b₁).ne' (sourcePartition_pos S b₂).ne']
    at h4
  unfold sourcePressure
  simp only [Nat.cast_ofNat] at h4
  linarith

/-- **Zero exchange source closes the first moment**: at `b = 0` the
Gibbs expectation of every exchange-odd scalar observable vanishes. -/
theorem gibbsExpect_defect_zero {S m : Ω → ℝ}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hm : ∀ ω, m (ϑ ω) = -m ω) :
    gibbsExpect S 0 m = 0 := by
  unfold gibbsExpect
  rw [div_eq_zero_iff]
  left
  have h1 : ∑ ω, m ω * Real.exp (-S ω + (0 : Ω → ℝ) ω)
      = ∑ ω, m (ϑ ω) * Real.exp (-S (ϑ ω) + 0) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm ϑ hinv)
      (fun ω => m ω * Real.exp (-S ω + (0 : Ω → ℝ) ω))]
    rfl
  have h2 : ∑ ω, m (ϑ ω) * Real.exp (-S (ϑ ω) + 0)
      = -∑ ω, m ω * Real.exp (-S ω + (0 : Ω → ℝ) ω) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hm ω, hS ω]
    simp only [Pi.zero_apply]
    ring
  have h3 := h1.trans h2
  linarith

/-- **Vector form of the zero mean defect**: at zero source the Gibbs
mean of the exchange-odd vector defect vanishes in the value module —
the Euler–Lagrange condition for first-moment plaquette closure. -/
theorem sum_exp_smul_defect_zero {V : Type*} [AddCommGroup V]
    [Module ℝ V] {S : Ω → ℝ} {D : Ω → V}
    (hS : ∀ ω, S (ϑ ω) = S ω) (hD : ∀ ω, D (ϑ ω) = -D ω) :
    ∑ ω, Real.exp (-S ω) • D ω = 0 := by
  have h1 : ∑ ω, Real.exp (-S ω) • D ω
      = ∑ ω, Real.exp (-S (ϑ ω)) • D (ϑ ω) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm ϑ hinv)
      (fun ω => Real.exp (-S ω) • D ω)]
    rfl
  have h2 : ∑ ω, Real.exp (-S (ϑ ω)) • D (ϑ ω)
      = -∑ ω, Real.exp (-S ω) • D ω := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hS ω, hD ω, smul_neg]
  have h3 := h1.trans h2
  have h4 : (2 : ℝ) • ∑ ω, Real.exp (-S ω) • D ω = 0 := by
    have h5 : ∑ ω, Real.exp (-S ω) • D ω
        + ∑ ω, Real.exp (-S ω) • D ω = 0 := by
      nth_rewrite 1 [h3]
      simp
    rw [two_smul]
    exact h5
  have h6 := congrArg (fun x => (2 : ℝ)⁻¹ • x) h4
  simpa [smul_smul] using h6

end Exchange

/-! ## The gradient identity -/

/-- **`thm:exchange-pressure-stationarity`, gradient**: along every
line `t ↦ b + t·m` the pressure has derivative the Gibbs expectation
of `m` — `∇Ψ(λ) = 𝔼_{π_λ} D` in directional form. -/
theorem hasDerivAt_sourcePressure (S b m : Ω → ℝ) :
    HasDerivAt (fun t : ℝ => sourcePressure S (fun ω => b ω + t * m ω))
      (gibbsExpect S b m) 0 := by
  have hF : HasDerivAt
      (fun t : ℝ => ∑ ω, Real.exp (-S ω + (b ω + t * m ω)))
      (∑ ω, m ω * Real.exp (-S ω + b ω)) 0 := by
    have h1 : ∀ ω : Ω, HasDerivAt
        (fun t : ℝ => Real.exp (-S ω + (b ω + t * m ω)))
        (m ω * Real.exp (-S ω + b ω)) 0 := by
      intro ω
      have h2 : HasDerivAt (fun t : ℝ => -S ω + (b ω + t * m ω))
          (m ω) 0 := by
        have h3 : HasDerivAt (fun t : ℝ => t * m ω) (m ω) 0 :=
          hasDerivAt_mul_const (m ω)
        exact (h3.const_add (b ω)).const_add (-S ω)
      have h4 := h2.exp
      have h5 : -S ω + (b ω + 0 * m ω) = -S ω + b ω := by ring
      rw [h5] at h4
      convert h4 using 1
      ring
    have h6 := HasDerivAt.sum
      (fun ω (_ : ω ∈ Finset.univ) => h1 ω)
    have hfun : (∑ ω : Ω, fun t : ℝ =>
        Real.exp (-S ω + (b ω + t * m ω)))
        = fun t : ℝ => ∑ ω, Real.exp (-S ω + (b ω + t * m ω)) := by
      funext t
      simp
    rwa [hfun] at h6
  have hpos : (∑ ω, Real.exp (-S ω + (b ω + 0 * m ω))) ≠ 0 := by
    have h7 : 0 < ∑ ω, Real.exp (-S ω + (b ω + 0 * m ω)) :=
      Finset.sum_pos (fun ω _ => Real.exp_pos _) Finset.univ_nonempty
    exact h7.ne'
  have hlog := hF.log (by
    have h8 : ∀ ω : Ω, -S ω + (b ω + 0 * m ω) = -S ω + b ω := by
      intro ω
      ring
    rw [show (∑ ω, Real.exp (-S ω + (b ω + (0:ℝ) * m ω)))
        = ∑ ω, Real.exp (-S ω + b ω) from
      Finset.sum_congr rfl fun ω _ => by rw [h8 ω]]
    exact (sourcePartition_pos S b).ne')
  have h9 : (∑ ω, Real.exp (-S ω + (b ω + (0:ℝ) * m ω)))
      = sourcePartition S b := by
    unfold sourcePartition
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    ring
  have h10 : (∑ ω, m ω * Real.exp (-S ω + b ω))
      / (∑ ω, Real.exp (-S ω + (b ω + 0 * m ω)))
      = gibbsExpect S b m := by
    rw [h9]
    rfl
  rw [← h10]
  exact hlog

/-! ## The covector packaging -/

section Dual

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Definition `def:exchange-source-pressure`**: the
exchange-source pressure of a covector `l` against the exchange-odd
defect `D`. -/
noncomputable def exchangePressure (S : Ω → ℝ) (D : Ω → V)
    (l : Module.Dual ℝ V) : ℝ :=
  sourcePressure S (fun ω => l (D ω))

variable {ϑ : Ω → Ω} (hinv : Function.Involutive ϑ)
variable {S : Ω → ℝ} {D : Ω → V}
variable (hS : ∀ ω, S (ϑ ω) = S ω) (hD : ∀ ω, D (ϑ ω) = -D ω)

include hinv hS hD in
/-- Evenness `Ψ(−λ) = Ψ(λ)`. -/
theorem exchangePressure_neg (l : Module.Dual ℝ V) :
    exchangePressure S D (-l) = exchangePressure S D l := by
  unfold exchangePressure
  have h1 : (fun ω => (-l) (D ω)) = fun ω => -(l (D ω)) := by
    funext ω
    simp
  rw [h1]
  exact sourcePressure_neg hinv hS
    (fun ω => by rw [hD ω, map_neg])

include hinv hS hD in
/-- The zero covector is a global minimum of the pressure. -/
theorem exchangePressure_zero_le (l : Module.Dual ℝ V) :
    exchangePressure S D 0 ≤ exchangePressure S D l := by
  unfold exchangePressure
  have h1 : (fun ω => (0 : Module.Dual ℝ V) (D ω))
      = (0 : Ω → ℝ) := by
    funext ω
    simp
  rw [h1]
  exact sourcePressure_zero_le hinv hS
    (fun ω => by rw [hD ω, map_neg])

include hinv hS hD in
/-- **Uniqueness modulo the annihilator**: the minimum value is
attained at `λ` exactly when `λ` annihilates every difference
`D ω − D ω'`. -/
theorem exchangePressure_eq_zero_iff (l : Module.Dual ℝ V) :
    exchangePressure S D l = exchangePressure S D 0
      ↔ ∀ ω ω' : Ω, l (D ω - D ω') = 0 := by
  unfold exchangePressure
  have h1 : (fun ω => (0 : Module.Dual ℝ V) (D ω))
      = (0 : Ω → ℝ) := by
    funext ω
    simp
  rw [h1]
  rw [sourcePressure_eq_zero_iff hinv hS
    (fun ω => by rw [hD ω, map_neg])]
  constructor
  · intro h ω ω'
    rw [map_sub, h ω ω', sub_self]
  · intro h ω ω'
    have h2 := h ω ω'
    rw [map_sub, sub_eq_zero] at h2
    exact h2

/-- The gradient identity for the covector pressure. -/
theorem hasDerivAt_exchangePressure (l m : Module.Dual ℝ V) :
    HasDerivAt (fun t : ℝ => exchangePressure S D (l + t • m))
      (gibbsExpect S (fun ω => l (D ω)) (fun ω => m (D ω))) 0 := by
  have h1 : ∀ t : ℝ, exchangePressure S D (l + t • m)
      = sourcePressure S
          (fun ω => l (D ω) + t * m (D ω)) := by
    intro t
    unfold exchangePressure
    congr 1
  have h2 := hasDerivAt_sourcePressure S
    (fun ω => l (D ω)) (fun ω => m (D ω))
  have h3 : (fun t : ℝ => exchangePressure S D (l + t • m))
      = fun t : ℝ =>
        sourcePressure S (fun ω => l (D ω) + t * m (D ω)) := by
    funext t
    exact h1 t
  rw [h3]
  exact h2

end Dual

end NCG
