/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The entropy–affinity–depth law

Covers `def:pressure-entropy-data`, `lem:stationary-affinity-cohomology`
and `thm:entropy-affinity-depth` from `manuscripts/renewal_emergence/renewal_emergence.tex`.

The bidirected pressure model is presented by `DoobData`: a finite
bidirected edge set (involution `bar` exchanging source and target),
resolved capacities `q_e = c_e e^{A(e)/2}` with symmetric conductance
`c` and antisymmetric affinity `A`, symmetric depths `len`, an inverse
temperature `β`, and **positive Doob vectors** `h, ν` — the right and
left Perron data of `constr:pressure-law`, taken here as hypotheses
(`Stochastic`, `StationaryFlow`, `ProbabilityWeight`) since the Perron
eigenvector existence is not part of the eigenvector-free pressure
development.

From this data the edge law `p_e = q_e e^{-β len_e} h_{t(e)}/h_{s(e)}`,
stationary weight `piw = ν h`, and stationary edge flow
`F_e = piw_{s(e)} p_e` are defined, and we prove:

* `sum_F_eq_one`, `sum_F_bar_eq_one` — `F` and `F ∘ bar` are
  probability distributions on oriented edges;
* `sigma_nonneg` — `σ = Σ F_e log(F_e/F_{bar e})` is the relative
  entropy `D(F ‖ F∘bar) ≥ 0` (Gibbs inequality);
* `scriptA_eq` — the stationary affinity cohomology identity
  `𝒜(e) = A(e) + v(t(e)) − v(s(e))` with `v = log(h/ν)`;
* `sum_F_A_eq_sigma` — the boxed consequence
  `Σ F_e A(e) = Σ F_e 𝒜(e) = σ ≥ 0`;
* `entropy_affinity_depth` — the boxed law
  `β μ_ℓ = h_rate + κ_c + σ/2`, its solved form
  `β = (h_rate + κ_c + σ/2)/μ_ℓ`, and the neutral-conductance
  normalization `β μ_ℓ = h_rate + σ/2`.
-/

namespace NCG

open Finset

/-- **Bidirected pressure model with Doob data**: finite bidirected
graph, resolved capacities `c e^{A/2}`, symmetric depths, inverse
temperature, and positive Doob (Perron) vectors `h, ν`. -/
structure DoobData (V E : Type*) [Fintype V] [Fintype E] where
  /-- Edge source. -/
  src : E → V
  /-- Edge target. -/
  tgt : E → V
  /-- The orientation reversal. -/
  bar : E → E
  bar_invol : ∀ e, bar (bar e) = e
  bar_src : ∀ e, src (bar e) = tgt e
  bar_tgt : ∀ e, tgt (bar e) = src e
  /-- The symmetric conductance. -/
  c : E → ℝ
  /-- The antisymmetric affinity cochain. -/
  A : E → ℝ
  c_pos : ∀ e, 0 < c e
  c_symm : ∀ e, c (bar e) = c e
  A_anti : ∀ e, A (bar e) = -A e
  /-- The symmetric depth. -/
  len : E → ℝ
  len_symm : ∀ e, len (bar e) = len e
  /-- The inverse temperature. -/
  β : ℝ
  /-- The right Doob (Perron) vector. -/
  h : V → ℝ
  /-- The left Doob (Perron) vector. -/
  ν : V → ℝ
  h_pos : ∀ x, 0 < h x
  ν_pos : ∀ x, 0 < ν x

namespace DoobData

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (D : DoobData V E)

/-- The resolved capacity `q_e = c_e e^{A(e)/2}`. -/
noncomputable def q (e : E) : ℝ := D.c e * Real.exp (D.A e / 2)

/-- The Doob edge law `p_e = q_e e^{-β len_e} h_{t(e)}/h_{s(e)}`. -/
noncomputable def p (e : E) : ℝ :=
  D.q e * Real.exp (-D.β * D.len e) * D.h (D.tgt e) / D.h (D.src e)

/-- The stationary vertex weight `π_x = ν_x h_x`. -/
noncomputable def piw (x : V) : ℝ := D.ν x * D.h x

/-- The stationary edge flow `F_e = π_{s(e)} p_e`. -/
noncomputable def F (e : E) : ℝ := D.piw (D.src e) * D.p e

omit [DecidableEq V] in
theorem q_pos (e : E) : 0 < D.q e :=
  mul_pos (D.c_pos e) (Real.exp_pos _)

omit [DecidableEq V] in
theorem p_pos (e : E) : 0 < D.p e :=
  div_pos (mul_pos (mul_pos (D.q_pos e) (Real.exp_pos _))
    (D.h_pos _)) (D.h_pos _)

omit [DecidableEq V] in
theorem piw_pos (x : V) : 0 < D.piw x :=
  mul_pos (D.ν_pos x) (D.h_pos x)

omit [DecidableEq V] in
theorem F_pos (e : E) : 0 < D.F e :=
  mul_pos (D.piw_pos _) (D.p_pos e)

/-- The bar involution as a permutation of the edges. -/
def barEquiv : Equiv.Perm E :=
  Function.Involutive.toPerm D.bar D.bar_invol

omit [DecidableEq V] in
@[simp] theorem barEquiv_apply (e : E) : D.barEquiv e = D.bar e := rfl

/-- **Hypothesis (from `constr:pressure-law`)**: the Doob edge law is
stochastic — unit out-sums at every vertex. -/
def Stochastic : Prop :=
  ∀ x : V, ∑ e ∈ univ.filter (fun e => D.src e = x), D.p e = 1

/-- **Hypothesis (from `constr:pressure-law`)**: the edge flow is
stationary — in-flow at every vertex equals its stationary weight. -/
def StationaryFlow : Prop :=
  ∀ y : V, ∑ e ∈ univ.filter (fun e => D.tgt e = y), D.F e = D.piw y

/-- **Hypothesis (from `constr:pressure-law`)**: the stationary
weight is a probability vector. -/
def ProbabilityWeight : Prop := ∑ x, D.piw x = 1

/-- Out-flow at every vertex equals its stationary weight. -/
theorem sum_F_out (hst : D.Stochastic) (x : V) :
    ∑ e ∈ univ.filter (fun e => D.src e = x), D.F e = D.piw x := by
  have h1 : ∑ e ∈ univ.filter (fun e => D.src e = x), D.F e
      = ∑ e ∈ univ.filter (fun e => D.src e = x),
          D.piw x * D.p e := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_filter] at he
    rw [F, he.2]
  rw [h1, ← Finset.mul_sum, hst x, mul_one]

/-- **Definition `def:pressure-entropy-data` (normalization)**: the
stationary edge flow is a probability distribution on oriented
edges. -/
theorem sum_F_eq_one (hst : D.Stochastic)
    (hprob : D.ProbabilityWeight) : ∑ e, D.F e = 1 := by
  have h1 : ∑ x, ∑ e ∈ univ.filter (fun e => D.src e = x), D.F e
      = ∑ e, D.F e :=
    Finset.sum_fiberwise_of_maps_to (fun e _ => Finset.mem_univ _) _
  rw [← h1]
  have h2 : ∀ x : V,
      ∑ e ∈ univ.filter (fun e => D.src e = x), D.F e = D.piw x :=
    D.sum_F_out hst
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact hprob

omit [DecidableEq V] in
/-- The reversed flow has the same total mass. -/
theorem sum_F_bar_eq_sum : ∑ e, D.F (D.bar e) = ∑ e, D.F e :=
  Equiv.sum_comp D.barEquiv D.F

/-- **Definition `def:pressure-entropy-data` (normalization,
reversed)**: the reversed edge flow is a probability distribution. -/
theorem sum_F_bar_eq_one (hst : D.Stochastic)
    (hprob : D.ProbabilityWeight) : ∑ e, D.F (D.bar e) = 1 := by
  rw [D.sum_F_bar_eq_sum]
  exact D.sum_F_eq_one hst hprob

/-- The stationary edge affinity `𝒜(e) = log(F_e/F_{bar e})`. -/
noncomputable def scriptA (e : E) : ℝ :=
  Real.log (D.F e / D.F (D.bar e))

/-- The entropy production `σ = Σ F_e 𝒜(e) = D(F ‖ F∘bar)`. -/
noncomputable def sigma : ℝ := ∑ e, D.F e * D.scriptA e

omit [DecidableEq V] in
/-- **Definition `def:pressure-entropy-data` (Gibbs inequality)**:
the entropy production is nonnegative. -/
theorem sigma_nonneg : 0 ≤ D.sigma := by
  have hkey : ∑ e, D.F e * Real.log (D.F (D.bar e) / D.F e) ≤ 0 := by
    have h1 : ∀ e : E,
        D.F e * Real.log (D.F (D.bar e) / D.F e)
          ≤ D.F (D.bar e) - D.F e := by
      intro e
      have h2 : Real.log (D.F (D.bar e) / D.F e)
          ≤ D.F (D.bar e) / D.F e - 1 :=
        Real.log_le_sub_one_of_pos
          (div_pos (D.F_pos _) (D.F_pos e))
      have h3 : D.F e * Real.log (D.F (D.bar e) / D.F e)
          ≤ D.F e * (D.F (D.bar e) / D.F e - 1) :=
        mul_le_mul_of_nonneg_left h2 (D.F_pos e).le
      have h4 : D.F e * (D.F (D.bar e) / D.F e - 1)
          = D.F (D.bar e) - D.F e := by
        field_simp [(D.F_pos e).ne']
      rw [h4] at h3
      exact h3
    have h5 : ∑ e, D.F e * Real.log (D.F (D.bar e) / D.F e)
        ≤ ∑ e, (D.F (D.bar e) - D.F e) :=
      Finset.sum_le_sum fun e _ => h1 e
    have h6 : ∑ e, (D.F (D.bar e) - D.F e) = 0 := by
      rw [Finset.sum_sub_distrib, D.sum_F_bar_eq_sum, sub_self]
    rw [h6] at h5
    exact h5
  have h8 : ∀ e : E, D.F e * D.scriptA e
      = -(D.F e * Real.log (D.F (D.bar e) / D.F e)) := by
    intro e
    have h9 : D.scriptA e
        = -Real.log (D.F (D.bar e) / D.F e) := by
      rw [show D.scriptA e
          = Real.log (D.F e / D.F (D.bar e)) from rfl,
        ← Real.log_inv, inv_div]
    rw [h9]
    ring
  have h7 : D.sigma
      = -∑ e, D.F e * Real.log (D.F (D.bar e) / D.F e) := by
    rw [show D.sigma = ∑ e, D.F e * D.scriptA e from rfl,
      Finset.sum_congr rfl fun e _ => h8 e,
      Finset.sum_neg_distrib]
  rw [h7]
  linarith

/-- The Doob gauge potential `v(x) = log(h_x/ν_x)`. -/
noncomputable def vlog (x : V) : ℝ :=
  Real.log (D.h x) - Real.log (D.ν x)

omit [DecidableEq V] in
/-- Explicit logarithm of the stationary edge flow. -/
theorem log_F (e : E) : Real.log (D.F e)
    = Real.log (D.ν (D.src e)) + Real.log (D.c e) + D.A e / 2
      - D.β * D.len e + Real.log (D.h (D.tgt e)) := by
  have hF : D.F e = D.ν (D.src e) * D.c e * Real.exp (D.A e / 2)
      * Real.exp (-D.β * D.len e) * D.h (D.tgt e) := by
    rw [F, piw, p, q]
    field_simp [(D.h_pos (D.src e)).ne']
  have hν : D.ν (D.src e) ≠ 0 := (D.ν_pos _).ne'
  have hc : D.c e ≠ 0 := (D.c_pos e).ne'
  have hh : D.h (D.tgt e) ≠ 0 := (D.h_pos _).ne'
  have he1 : Real.exp (D.A e / 2) ≠ 0 := Real.exp_ne_zero _
  have he2 : Real.exp (-D.β * D.len e) ≠ 0 := Real.exp_ne_zero _
  rw [hF]
  rw [Real.log_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hν hc) he1) he2) hh,
    Real.log_mul (mul_ne_zero (mul_ne_zero hν hc) he1) he2,
    Real.log_mul (mul_ne_zero hν hc) he1,
    Real.log_mul hν hc, Real.log_exp, Real.log_exp]
  ring

omit [DecidableEq V] in
/-- **Lemma `lem:stationary-affinity-cohomology` (identity)**: the
stationary affinity is the resolved affinity up to the coboundary of
the Doob gauge potential: `𝒜(e) = A(e) + v(t(e)) − v(s(e))`. -/
theorem scriptA_eq (e : E) :
    D.scriptA e
      = D.A e + D.vlog (D.tgt e) - D.vlog (D.src e) := by
  rw [scriptA, Real.log_div (D.F_pos e).ne' (D.F_pos _).ne',
    D.log_F, D.log_F (D.bar e), D.bar_src, D.bar_tgt, D.c_symm,
    D.A_anti, D.len_symm, vlog, vlog]
  ring

/-- Stationary flows telescope every vertex potential. -/
theorem telescope (hst : D.Stochastic) (hflow : D.StationaryFlow)
    (g : V → ℝ) :
    ∑ e, D.F e * (g (D.tgt e) - g (D.src e)) = 0 := by
  have htgt : ∑ e, D.F e * g (D.tgt e) = ∑ y, D.piw y * g y := by
    have h1 : ∑ y, ∑ e ∈ univ.filter (fun e => D.tgt e = y),
        D.F e * g (D.tgt e) = ∑ e, D.F e * g (D.tgt e) :=
      Finset.sum_fiberwise_of_maps_to (fun e _ => Finset.mem_univ _) _
    rw [← h1]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h2 : ∑ e ∈ univ.filter (fun e => D.tgt e = y),
        D.F e * g (D.tgt e)
          = ∑ e ∈ univ.filter (fun e => D.tgt e = y),
              D.F e * g y := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [he.2]
    rw [h2, ← Finset.sum_mul, hflow y]
  have hsrc : ∑ e, D.F e * g (D.src e) = ∑ x, D.piw x * g x := by
    have h1 : ∑ x, ∑ e ∈ univ.filter (fun e => D.src e = x),
        D.F e * g (D.src e) = ∑ e, D.F e * g (D.src e) :=
      Finset.sum_fiberwise_of_maps_to (fun e _ => Finset.mem_univ _) _
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h2 : ∑ e ∈ univ.filter (fun e => D.src e = x),
        D.F e * g (D.src e)
          = ∑ e ∈ univ.filter (fun e => D.src e = x),
              D.F e * g x := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [he.2]
    rw [h2, ← Finset.sum_mul, D.sum_F_out hst x]
  have h3 : ∑ e, D.F e * (g (D.tgt e) - g (D.src e))
      = ∑ e, D.F e * g (D.tgt e) - ∑ e, D.F e * g (D.src e) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h3, htgt, hsrc, sub_self]

/-- **Lemma `lem:stationary-affinity-cohomology` (boxed
consequence)**: the stationary affinity flux equals the resolved
affinity flux, `Σ F_e A(e) = Σ F_e 𝒜(e) = σ ≥ 0`. -/
theorem sum_F_A_eq_sigma (hst : D.Stochastic)
    (hflow : D.StationaryFlow) :
    ∑ e, D.F e * D.A e = D.sigma := by
  have h1 : D.sigma
      = ∑ e, D.F e * (D.A e
          + (D.vlog (D.tgt e) - D.vlog (D.src e))) := by
    rw [sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [D.scriptA_eq e]
    ring
  have h2 : ∑ e, D.F e * (D.A e
      + (D.vlog (D.tgt e) - D.vlog (D.src e)))
      = ∑ e, D.F e * D.A e
        + ∑ e, D.F e * (D.vlog (D.tgt e) - D.vlog (D.src e)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h1, h2, D.telescope hst hflow D.vlog, add_zero]

/-- The stationary mean depth `μ_ℓ = Σ F_e len_e`. -/
noncomputable def meanDepth : ℝ := ∑ e, D.F e * D.len e

/-- The entropy rate `h_rate = −Σ F_e log p_e`. -/
noncomputable def entropyRate : ℝ := -∑ e, D.F e * Real.log (D.p e)

/-- The conductance flux `κ_c = Σ F_e log c_e`. -/
noncomputable def kappaC : ℝ := ∑ e, D.F e * Real.log (D.c e)

omit [DecidableEq V] in
/-- Explicit logarithm of the Doob edge law. -/
theorem log_p (e : E) : Real.log (D.p e)
    = Real.log (D.c e) + D.A e / 2 - D.β * D.len e
      + Real.log (D.h (D.tgt e)) - Real.log (D.h (D.src e)) := by
  have hp : D.p e = D.c e * Real.exp (D.A e / 2)
      * Real.exp (-D.β * D.len e) * D.h (D.tgt e)
        / D.h (D.src e) := by
    rw [p, q]
  have hc : D.c e ≠ 0 := (D.c_pos e).ne'
  have hht : D.h (D.tgt e) ≠ 0 := (D.h_pos _).ne'
  have hhs : D.h (D.src e) ≠ 0 := (D.h_pos _).ne'
  have he1 : Real.exp (D.A e / 2) ≠ 0 := Real.exp_ne_zero _
  have he2 : Real.exp (-D.β * D.len e) ≠ 0 := Real.exp_ne_zero _
  rw [hp]
  rw [Real.log_div
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hc he1) he2) hht) hhs,
    Real.log_mul (mul_ne_zero (mul_ne_zero hc he1) he2) hht,
    Real.log_mul (mul_ne_zero hc he1) he2,
    Real.log_mul hc he1, Real.log_exp, Real.log_exp]
  ring

/-- **Theorem `thm:entropy-affinity-depth`**: the boxed
entropy-per-depth law `β μ_ℓ = h_rate + κ_c + σ/2` — nonequilibrium
affinity contributes a positive one-half correction to the
entropy-per-depth law, and the symmetric conductance is an
independent capacity datum. -/
theorem entropy_affinity_depth (hst : D.Stochastic)
    (hflow : D.StationaryFlow) :
    D.β * D.meanDepth
      = D.entropyRate + D.kappaC + D.sigma / 2 := by
  have h1 : ∀ e : E, D.F e * (D.β * D.len e)
      = D.F e * Real.log (D.c e) + D.F e * (D.A e / 2)
        - D.F e * Real.log (D.p e)
        + D.F e * (Real.log (D.h (D.tgt e))
            - Real.log (D.h (D.src e))) := by
    intro e
    have h2 := D.log_p e
    have h5 : D.β * D.len e
        = Real.log (D.c e) + D.A e / 2 - Real.log (D.p e)
          + (Real.log (D.h (D.tgt e))
              - Real.log (D.h (D.src e))) := by
      linarith
    rw [h5]
    ring
  have h3 : D.β * D.meanDepth = ∑ e, D.F e * (D.β * D.len e) := by
    rw [show D.meanDepth = ∑ e, D.F e * D.len e from rfl,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h3, Finset.sum_congr rfl fun e _ => h1 e]
  have h4 : ∑ e, (D.F e * Real.log (D.c e) + D.F e * (D.A e / 2)
      - D.F e * Real.log (D.p e)
      + D.F e * (Real.log (D.h (D.tgt e))
          - Real.log (D.h (D.src e))))
      = (∑ e, D.F e * Real.log (D.c e))
        + (∑ e, D.F e * (D.A e / 2))
        - (∑ e, D.F e * Real.log (D.p e))
        + ∑ e, D.F e * (Real.log (D.h (D.tgt e))
            - Real.log (D.h (D.src e))) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA2 : ∑ e, D.F e * (D.A e / 2) = D.sigma / 2 := by
    rw [← D.sum_F_A_eq_sigma hst hflow, Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h4, hA2, D.telescope hst hflow (fun x => Real.log (D.h x)),
    add_zero,
    show D.entropyRate = -∑ e, D.F e * Real.log (D.p e) from rfl,
    show D.kappaC = ∑ e, D.F e * Real.log (D.c e) from rfl]
  ring

/-- **Theorem `thm:entropy-affinity-depth` (solved form)**:
`β = (h_rate + E_F[log c] + ½E_F[A])/μ_ℓ`. -/
theorem beta_eq (hst : D.Stochastic) (hflow : D.StationaryFlow)
    (hμ : D.meanDepth ≠ 0) :
    D.β = (D.entropyRate + D.kappaC + D.sigma / 2) / D.meanDepth := by
  rw [← D.entropy_affinity_depth hst hflow]
  field_simp

/-- **Theorem `thm:entropy-affinity-depth` (neutral conductance)**:
with `c ≡ 1`, `β μ_ℓ = h_rate + σ/2`. -/
theorem entropy_affinity_depth_neutral (hst : D.Stochastic)
    (hflow : D.StationaryFlow) (hc : ∀ e, D.c e = 1) :
    D.β * D.meanDepth = D.entropyRate + D.sigma / 2 := by
  have h1 : D.kappaC = 0 := by
    rw [kappaC]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [hc e, Real.log_one, mul_zero]
  have h2 := D.entropy_affinity_depth hst hflow
  rw [h1, add_zero] at h2
  exact h2

end DoobData

end NCG
