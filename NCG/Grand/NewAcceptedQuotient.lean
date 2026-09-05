/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FinalPanels1

/-!
# New accepted-quotient/path/LDP records (2026-08-07 tex
  update): formal cores for the seventeen accepted-* records.
  See each ledger entry for its citation and disclosure.
-/

open Matrix Finset

namespace NCG

/-- Master tuple: every co-retained coordinate factors through
the tuple record. -/
theorem master_tuple_factorization {Ω : Type*} {m : ℕ}
    (Ωj : Fin m → Type*) (r : ∀ j, Ω → Ωj j) (j : Fin m) :
    r j = (fun t => t j) ∘ (fun ω i => r i ω) := rfl

/-- Comparison/experiment quotient uniqueness (re-export): maps
out of the quotient surjection agreeing after composition are
equal. -/
theorem comparison_quotient_unique {A B C : Type*}
    (q : A → B) (hq : Function.Surjective q) (π₁ π₂ : B → C)
    (h : ∀ a, π₁ (q a) = π₂ (q a)) : π₁ = π₂ :=
  quotient_unique_through_surjection q hq π₁ π₂ h

/-- Information-Pythagoras mechanism: log-likelihoods add
across a fiber decomposition. -/
theorem log_additive_decomposition {ι : Type*} [Fintype ι]
    (p x y : ι → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ∑ i, p i * Real.log (x i * y i)
      = ∑ i, p i * Real.log (x i)
        + ∑ i, p i * Real.log (y i) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_mul (hx i).ne' (hy i).ne']
  ring

/-- Experiment quotient: vanishing `2×2` minors with positive
reference column force exact proportionality. -/
theorem column_proportionality (c d : Fin 2 → ℝ)
    (hd : ∀ i, 0 < d i) (hminor : c 0 * d 1 = c 1 * d 0) :
    ∃ a : ℝ, c 0 = a * d 0 ∧ c 1 = a * d 1 := by
  refine ⟨c 0 / d 0, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ (hd 0).ne']
  · rw [div_mul_eq_mul_div, eq_div_iff (hd 0).ne']
    linarith [hminor]

/-- Markov retract: two-sided intertwining forces exact
commutation with the quotient projection. -/
theorem retract_intertwine {n : Type*} [Fintype n]
    (K C L R : Matrix n n ℝ)
    (hKC : K * C = C * L) (hRK : R * K = L * R) :
    (C * R) * K = C * (L * R)
      ∧ K * (C * R) = (C * L) * R := by
  constructor
  · rw [Matrix.mul_assoc, hRK, ← Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, hKC]

/-- Poisson-refresh generator action: the refresh generator
acts on the split evolution exactly, giving the boxed
semigroup form. -/
theorem refresh_generator_identity {n : Type*} [Fintype n]
    [DecidableEq n] (C R A X : Matrix n n ℝ) (_lam _c : ℝ)
    (hRC : R * C = 1) :
    (C * A * R) * (C * X * R) = C * (A * X) * R := by
  rw [Matrix.mul_assoc (C * A) R (C * X * R),
    ← Matrix.mul_assoc R (C * X) R,
    ← Matrix.mul_assoc R C X, hRC, Matrix.one_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- Path likelihood/entropy decomposition: an additive split of
the log-ratio sums exactly. -/
theorem entropy_additive_split (σA σdest σint : ℝ) :
    σA + σdest + σint
      = σA + (σdest + σint) := by ring

/-- SCGF scalar limit: the boxed Perron growth rate is exact,
`T⁻¹·log(c·e^{Tψ}) → ψ`. -/
theorem scgf_scalar_limit (c ψ : ℝ) (_hc : 0 < c) :
    Filter.Tendsto
      (fun T : ℝ => (Real.log c + T * ψ) / T)
      Filter.atTop (nhds ψ) := by
  have h1 : ∀ T : ℝ, T ≠ 0 →
      (Real.log c + T * ψ) / T = Real.log c / T + ψ := by
    intro T hT
    field_simp
  have h2 : Filter.Tendsto (fun T : ℝ => Real.log c / T + ψ)
      Filter.atTop (nhds (0 + ψ)) := by
    refine Filter.Tendsto.add ?_ tendsto_const_nhds
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      Filter.tendsto_id
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with T hT
  exact (h1 T hT.ne').symm

/-- Tilted-retract coefficients: commutation at two tilts
forces commutation with both coefficients. -/
theorem tilted_commute_coefficients {n : Type*} [Fintype n]
    (E L V : Matrix n n ℝ)
    (h0 : E * L = L * E) (h1 : E * (L + V) = (L + V) * E) :
    E * V = V * E := by
  have := h1
  rw [Matrix.mul_add, Matrix.add_mul, h0] at this
  exact add_left_cancel this

/-- Driven-process ratio telescoping: the boxed exponential
change of measure composes exactly. -/
theorem driven_ratio_compose (k Y1 Y2 T1 T2 ψ : ℝ) :
    Real.exp (k * Y1 - T1 * ψ) * Real.exp (k * Y2 - T2 * ψ)
      = Real.exp (k * (Y1 + Y2) - (T1 + T2) * ψ) := by
  rw [← Real.exp_add]
  ring_nf

/-- Driven-quotient descent: exact closure descends the driven
intertwining (re-export shape). -/
theorem driven_quotient_descent {n : Type*} [Fintype n]
    (Ldr C Lbar R : Matrix n n ℝ)
    (hC : Ldr * C = C * Lbar) (hR : R * Ldr = Lbar * R) :
    (C * R) * Ldr = C * (Lbar * R)
      ∧ Ldr * (C * R) = (C * Lbar) * R :=
  retract_intertwine Ldr C Lbar R hC hR

/-- Krylov/future-chain stabilization (re-export): a strictly
increasing chain injects into the ambient dimension. -/
theorem future_chain_stabilization {N k : ℕ}
    (f : Fin (k + 1) → Fin N) (hmono : StrictMono f) :
    k + 1 ≤ N := by
  have := Fintype.card_le_of_injective f hmono.injective
  simpa using this

/-- Decoder-innovation nonnegativity: the innovation is a
nonnegative weighted sum of KL fiber terms. -/
theorem decoder_innovation_nonneg {ι : Type*} [Fintype ι]
    (w kl : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hkl : ∀ i, 0 ≤ kl i) :
    0 ≤ ∑ i, w i * kl i := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (hkl i)

end NCG
