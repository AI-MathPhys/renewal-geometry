/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pressure-adapted coherent ADM packet and its regenerative
  regularity derivation (`thm:SMST-ADM-Cartan`,
  `thm:SMST-regenerative-ADM`, Gran-Tensor manuscript)

* `smst_lapse_bounds`: clause (i) — the boxed lapse
  `𝒩ₕ = βₕ·ℓ₀,ₕ` has positive two-sided bounds on every compact
  pressure phase;
* `link_chain_near_identity`: hypothesis (P4) in action — a
  chain of near-identity physical links stays near the identity,
  `‖aₙ⋯a₁ - 1‖ ≤ (1+ε)ⁿ - 1` (the transport step behind the
  environment-unitary clause (ii));
* `type_mass_amplitude_cap`: the (R1)–(R2) conversion — a
  positive type-mass floor turns the integrated quadratic energy
  into a uniform amplitude cap, `aₜ² ≤ E/m₀`;
* `amplitude_to_L4`: the cap bootstraps every finite `L^r`
  bound — `Σ m·a⁴ ≤ (E/m₀)·E`;
* `conorm_window`: the (R3) exponent window is nonempty —
  `p > 4` gives `4p/(p+2) < 4` and `0 < 1 - 4/p`, so the
  `C^{0,α}` compactness range is nonvoid.

Rendering disclosed: the environment-unitary transport, the
cb-generator calculus, the Hodge–Sobolev/weighted-inverse
branch, the `W^{1,p}_loc` connection estimate, and the
`C^{0,α}_loc` precompactness are the manuscript's analytic
layer; the lapse interval arithmetic, the link-chain estimate,
the type-mass conversions, and the exponent window are proved
here.
-/

namespace NCG

/-- Clause (i): the boxed lapse `𝒩 = β·ℓ` inherits positive
two-sided bounds. -/
theorem smst_lapse_bounds (β ℓ a A b B : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hβl : a ≤ β) (hβu : β ≤ A) (hℓl : b ≤ ℓ)
    (hℓu : ℓ ≤ B) :
    0 < β * ℓ ∧ a * b ≤ β * ℓ ∧ β * ℓ ≤ A * B := by
  have hβ0 : 0 < β := lt_of_lt_of_le ha hβl
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hb hℓl
  exact ⟨mul_pos hβ0 hℓ0, by nlinarith, by nlinarith⟩

/-- (P4) link transport: a chain of near-identity links stays
near the identity, `‖aₙ⋯a₁ - 1‖ ≤ (1+ε)ⁿ - 1`. -/
theorem link_chain_near_identity {A : Type*} [NormedRing A]
    [NormOneClass A] (ε : ℝ) (hε : 0 ≤ ε) (l : List A)
    (hl : ∀ x ∈ l, ‖x - 1‖ ≤ ε) :
    ‖l.prod - 1‖ ≤ (1 + ε) ^ l.length - 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : ‖a - 1‖ ≤ ε := hl a (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, ‖x - 1‖ ≤ ε :=
      fun x hx => hl x (List.mem_cons_of_mem a hx)
    have iht := ih ht
    have hsplit : a * t.prod - 1
        = (a - 1) * (t.prod - 1) + (a - 1) + (t.prod - 1) := by
      noncomm_ring
    have htp : ‖t.prod - 1‖ ≤ (1 + ε) ^ t.length - 1 := iht
    have hpow : (0 : ℝ) ≤ (1 + ε) ^ t.length - 1 := by
      have : (1 : ℝ) ≤ (1 + ε) ^ t.length :=
        one_le_pow₀ (by linarith)
      linarith
    calc ‖(a :: t).prod - 1‖
        = ‖(a - 1) * (t.prod - 1) + (a - 1)
            + (t.prod - 1)‖ := by
          rw [List.prod_cons, hsplit]
      _ ≤ ‖(a - 1) * (t.prod - 1)‖ + ‖a - 1‖
          + ‖t.prod - 1‖ := norm_add₃_le
      _ ≤ ‖a - 1‖ * ‖t.prod - 1‖ + ‖a - 1‖
          + ‖t.prod - 1‖ := by
          have := norm_mul_le (a - 1) (t.prod - 1)
          linarith
      _ ≤ ε * ((1 + ε) ^ t.length - 1) + ε
          + ((1 + ε) ^ t.length - 1) := by
          have h1 : ‖a - 1‖ * ‖t.prod - 1‖
              ≤ ε * ((1 + ε) ^ t.length - 1) :=
            mul_le_mul ha htp (norm_nonneg _) hε
          linarith
      _ = (1 + ε) * (1 + ε) ^ t.length - 1 := by ring
      _ = (1 + ε) ^ (a :: t).length - 1 := by
          rw [List.length_cons, pow_succ]
          ring

/-- (R1)–(R2): the type-mass floor converts integrated
quadratic energy into a uniform amplitude cap. -/
theorem type_mass_amplitude_cap {T : Type*} [Fintype T]
    (m aamp : T → ℝ) (m0 E : ℝ) (hm0 : 0 < m0)
    (hfloor : ∀ t, m0 ≤ m t)
    (henergy : ∑ t, m t * aamp t ^ 2 ≤ E) (t : T) :
    aamp t ^ 2 ≤ E / m0 := by
  have hterm : m0 * aamp t ^ 2 ≤ E := by
    have h1 : m0 * aamp t ^ 2 ≤ m t * aamp t ^ 2 :=
      mul_le_mul_of_nonneg_right (hfloor t) (sq_nonneg _)
    have h2 : m t * aamp t ^ 2 ≤ ∑ s, m s * aamp s ^ 2 := by
      refine Finset.single_le_sum
        (f := fun s => m s * aamp s ^ 2) (fun s _ => ?_)
        (Finset.mem_univ t)
      have := lt_of_lt_of_le hm0 (hfloor s)
      positivity
    linarith
  rw [le_div_iff₀ hm0]
  linarith [hterm]

/-- The amplitude cap bootstraps the quartic energy:
`Σ m·a⁴ ≤ (E/m₀)·E`. -/
theorem amplitude_to_L4 {T : Type*} [Fintype T]
    (m aamp : T → ℝ) (m0 E : ℝ) (hm0 : 0 < m0) (hE : 0 ≤ E)
    (hfloor : ∀ t, m0 ≤ m t)
    (henergy : ∑ t, m t * aamp t ^ 2 ≤ E) :
    ∑ t, m t * aamp t ^ 4 ≤ E / m0 * E := by
  have hcap := type_mass_amplitude_cap m aamp m0 E hm0
    hfloor henergy
  have hstep : ∀ t ∈ Finset.univ,
      m t * aamp t ^ 4 ≤ E / m0 * (m t * aamp t ^ 2) := by
    intro t _
    have hmt : 0 < m t := lt_of_lt_of_le hm0 (hfloor t)
    have h4 : aamp t ^ 4 = aamp t ^ 2 * aamp t ^ 2 := by ring
    rw [h4]
    have hc := hcap t
    have hkey := mul_le_mul_of_nonneg_left hc
      (mul_nonneg hmt.le (sq_nonneg (aamp t)))
    nlinarith [hkey]
  calc ∑ t, m t * aamp t ^ 4
      ≤ ∑ t, E / m0 * (m t * aamp t ^ 2) :=
        Finset.sum_le_sum hstep
    _ = E / m0 * ∑ t, m t * aamp t ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ E / m0 * E := by
        refine mul_le_mul_of_nonneg_left henergy ?_
        positivity

/-- (R3): the conorm exponent window is nonempty for `p > 4` —
`4p/(p+2) < 4` and `0 < 1 - 4/p`. -/
theorem conorm_window (p : ℝ) (hp : 4 < p) :
    4 * p / (p + 2) < 4 ∧ 0 < 1 - 4 / p := by
  have hp0 : 0 < p := by linarith
  constructor
  · rw [div_lt_iff₀ (by linarith)]
    linarith
  · have : 4 / p < 1 := (div_lt_one hp0).mpr hp
    linarith

end NCG
