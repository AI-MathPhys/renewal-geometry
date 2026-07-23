/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.HeatBathPrimitivity

/-!
# Dobrushin contraction and exponential mixing

The quantitative mixing tail of `thm:common-origin-balance`
(`manuscripts/renewal_emergence/renewal_emergence.tex`):

* `dobrushin_contraction` — a stochastic kernel with entries `≥ δ`
  contracts zero-mass signed measures in `ℓ¹` by the factor
  `1 − |D|δ` (subtract the `δ`-floor, which annihilates zero-mass
  vectors, and bound termwise);
* `zero_mass_step` — zero mass is preserved by a stochastic kernel;
* `dobrushin_pow_contraction` — iterates contract geometrically;
* `heatBath_exponential_mixing` — the common-origin heat-bath chain
  mixes exponentially: there is a floor `δ > 0` (primitivity at
  power `|Λ|`) such that for every pair of probability laws
  `π₀, π₁`, the `ℓ¹` distance of their images under `K^{|Λ|·k}`
  decays by `(1 − |Ω_Λ|·δ)^k`, and `0 ≤ 1 − |Ω_Λ|·δ < 1`.
-/

namespace NCG.CommonOrigin

open Matrix

/-! ## The abstract contraction -/

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

omit [Nonempty D] in
theorem kernelPow_succ (Q : D → D → ℝ) (k : ℕ) (a b : D) :
    kernelPow Q (k + 1) a b = ∑ c, Q a c * kernelPow Q k c b := rfl

omit [DecidableEq D] in
omit [DecidableEq D] [Nonempty D] in
/-- **Dobrushin `ℓ¹`-contraction**: a kernel with entrywise floor
`δ` contracts zero-mass vectors by `1 − |D|δ`. -/
theorem dobrushin_contraction (Q : D → D → ℝ) {δ : ℝ}
    (hpos : ∀ a b, δ ≤ Q a b) (hrow : ∀ a, ∑ b, Q a b = 1)
    {μ : D → ℝ} (hzero : ∑ a, μ a = 0) :
    ∑ b, |∑ a, μ a * Q a b|
      ≤ (1 - Fintype.card D * δ) * ∑ a, |μ a| := by
  have hfloor : ∀ b, ∑ a, μ a * Q a b
      = ∑ a, μ a * (Q a b - δ) := by
    intro b
    have h1 : ∑ a, μ a * (Q a b - δ)
        = (∑ a, μ a * Q a b) - δ * ∑ a, μ a := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [h1, hzero, mul_zero, sub_zero]
  have hterm : ∀ b, |∑ a, μ a * Q a b|
      ≤ ∑ a, |μ a| * (Q a b - δ) := by
    intro b
    rw [hfloor b]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hpos a b))]
  calc ∑ b, |∑ a, μ a * Q a b|
      ≤ ∑ b, ∑ a, |μ a| * (Q a b - δ) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = ∑ a, |μ a| * ((∑ b, Q a b) - Fintype.card D * δ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
    _ = (1 - Fintype.card D * δ) * ∑ a, |μ a| := by
        have h2 : ∀ a, |μ a| * ((∑ b, Q a b)
            - Fintype.card D * δ)
            = (1 - Fintype.card D * δ) * |μ a| := by
          intro a
          rw [hrow a]
          ring
        rw [Finset.sum_congr rfl fun a _ => h2 a,
          ← Finset.mul_sum]

omit [DecidableEq D] in
omit [DecidableEq D] [Nonempty D] in
/-- Zero mass is preserved by a stochastic kernel. -/
theorem zero_mass_step (Q : D → D → ℝ)
    (hrow : ∀ a, ∑ b, Q a b = 1) {μ : D → ℝ}
    (hzero : ∑ a, μ a = 0) :
    ∑ b, (∑ a, μ a * Q a b) = 0 := by
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ b, μ a * Q a b = μ a := by
    intro a
    rw [← Finset.mul_sum, hrow a, mul_one]
  rw [Finset.sum_congr rfl fun a _ => h1 a, hzero]

/-- **Geometric decay of iterates** on zero-mass vectors. -/
theorem dobrushin_pow_contraction (Q : D → D → ℝ) {δ : ℝ}
    (hpos : ∀ a b, δ ≤ Q a b) (hrow : ∀ a, ∑ b, Q a b = 1) :
    ∀ (k : ℕ) (μ : D → ℝ), (∑ a, μ a = 0) →
      ∑ b, |∑ a, μ a * (kernelPow Q k) a b|
        ≤ (1 - Fintype.card D * δ) ^ k * ∑ a, |μ a| := by
  have hle1 : Fintype.card D * δ ≤ 1 := by
    have a : D := Classical.arbitrary D
    have h1 : (Fintype.card D : ℝ) * δ = ∑ _b : D, δ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, ← hrow a]
    exact Finset.sum_le_sum fun b _ => hpos a b
  have hfac_nonneg : (0 : ℝ) ≤ 1 - Fintype.card D * δ := by
    linarith
  intro k
  induction k with
  | zero =>
    intro μ hzero
    simp only [pow_zero, one_mul]
    have h1 : ∀ b, (∑ a, μ a * (kernelPow Q 0) a b) = μ b := by
      intro b
      have hthis : ∀ a, μ a * (kernelPow Q 0) a b
          = if a = b then μ a else 0 := by
        intro a
        change μ a * (if a = b then (1 : ℝ) else 0)
          = if a = b then μ a else 0
        split <;> simp
      rw [Finset.sum_congr rfl fun a _ => hthis a,
        Finset.sum_ite_eq' Finset.univ b μ]
      simp
    have hgoal : ∑ b, |∑ a, μ a * (kernelPow Q 0) a b|
        = ∑ b, |μ b| :=
      Finset.sum_congr rfl fun b _ => by rw [h1 b]
    rw [hgoal]
  | succ k ih =>
    intro μ hzero
    set μ1 : D → ℝ := fun c => ∑ a, μ a * Q a c with hμ1
    have hμ1zero : ∑ c, μ1 c = 0 := zero_mass_step Q hrow hzero
    have hrec : ∀ b, (∑ a, μ a * (kernelPow Q (k + 1)) a b)
        = ∑ c, μ1 c * (kernelPow Q k) c b := by
      intro b
      have hexpand : ∀ a, μ a * (kernelPow Q (k + 1)) a b
          = ∑ c, μ a * Q a c * (kernelPow Q k) c b := by
        intro a
        rw [kernelPow_succ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      rw [Finset.sum_congr rfl fun a _ => hexpand a,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      change ∑ a, μ a * Q a c * (kernelPow Q k) c b
        = (∑ a, μ a * Q a c) * (kernelPow Q k) c b
      rw [Finset.sum_mul]
    have hgoal : ∑ b, |∑ a, μ a * (kernelPow Q (k + 1)) a b|
        = ∑ b, |∑ c, μ1 c * (kernelPow Q k) c b| :=
      Finset.sum_congr rfl fun b _ => by rw [hrec b]
    rw [hgoal]
    have hIH := ih μ1 hμ1zero
    have hcontr := dobrushin_contraction Q hpos hrow hzero
    calc ∑ b, |∑ c, μ1 c * (kernelPow Q k) c b|
        ≤ (1 - Fintype.card D * δ) ^ k * ∑ c, |μ1 c| := hIH
      _ ≤ (1 - Fintype.card D * δ) ^ k
            * ((1 - Fintype.card D * δ) * ∑ a, |μ a|) := by
          apply mul_le_mul_of_nonneg_left _
            (pow_nonneg hfac_nonneg k)
          exact hcontr
      _ = (1 - Fintype.card D * δ) ^ (k + 1) * ∑ a, |μ a| := by
          rw [pow_succ]
          ring

/-! ## The heat-bath chain mixes exponentially -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The common-origin heat-bath chain mixes exponentially**
(`thm:common-origin-balance`, mixing clause, scalar-marginal level):
there is a strictly positive floor `δ` (primitivity at power `|Λ|`)
with contraction factor `1 − |Ω_Λ|·δ ∈ [0, 1)` such that any two
probability laws converge together under `K^{|Λ|·k}` at rate
`(1 − |Ω_Λ|·δ)^k`. -/
theorem heatBath_exponential_mixing [Nonempty ι]
    (D : IsingData ι) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i)
    (hν1 : ∑ i, ν i = 1) :
    ∃ δ : ℝ, 0 < δ ∧ Fintype.card (ι → Bool) * δ ≤ 1
      ∧ ∀ (k : ℕ) (π₀ π₁ : (ι → Bool) → ℝ),
          (∑ β, π₀ β = 1) → (∑ β, π₁ β = 1) →
          ∑ β', |(∑ β, π₀ β
              * (kernelPow
                (fun a b => (heatBathMatrix D ν
                  ^ Fintype.card ι) a b) k) β β')
            - (∑ β, π₁ β
              * (kernelPow
                (fun a b => (heatBathMatrix D ν
                  ^ Fintype.card ι) a b) k) β β')|
            ≤ (1 - Fintype.card (ι → Bool) * δ) ^ k
                * ∑ β, |π₀ β - π₁ β| := by
  classical
  set Q : (ι → Bool) → (ι → Bool) → ℝ :=
    fun a b => (heatBathMatrix D ν ^ Fintype.card ι) a b with hQ
  have hQpos : ∀ a b, 0 < Q a b :=
    fun a b => heatBathMatrix_pow_pos D ν hν a b
  have hQrow : ∀ a, ∑ b, Q a b = 1 :=
    fun a => rowStochastic_pow (heatBathMatrix_rowSum D ν hν1)
      (Fintype.card ι) a
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun p : (ι → Bool) × (ι → Bool) => Q p.1 p.2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro p _
    exact hQpos p.1 p.2
  have hδle : ∀ a b, δ ≤ Q a b := by
    intro a b
    rw [hδ]
    exact Finset.inf'_le _ (Finset.mem_univ (a, b))
  have hcardδ : Fintype.card (ι → Bool) * δ ≤ 1 := by
    have a : (ι → Bool) := Classical.arbitrary _
    have h1 : (Fintype.card (ι → Bool) : ℝ) * δ
        = ∑ _b : (ι → Bool), δ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, ← hQrow a]
    exact Finset.sum_le_sum fun b _ => hδle a b
  refine ⟨δ, hδpos, hcardδ, fun k π₀ π₁ h0 h1 => ?_⟩
  set μ : (ι → Bool) → ℝ := fun β => π₀ β - π₁ β with hμ
  have hμzero : ∑ β, μ β = 0 := by
    rw [hμ]
    rw [Finset.sum_sub_distrib, h0, h1, sub_self]
  have hcombine : ∀ β', (∑ β, π₀ β * (kernelPow Q k) β β')
      - (∑ β, π₁ β * (kernelPow Q k) β β')
      = ∑ β, μ β * (kernelPow Q k) β β' := by
    intro β'
    rw [hμ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hgoal : ∑ β', |(∑ β, π₀ β * (kernelPow Q k) β β')
      - (∑ β, π₁ β * (kernelPow Q k) β β')|
      = ∑ β', |∑ β, μ β * (kernelPow Q k) β β'| :=
    Finset.sum_congr rfl fun β' _ => by rw [hcombine β']
  rw [hgoal]
  exact dobrushin_pow_contraction Q hδle hQrow k μ hμzero

end NCG.CommonOrigin
