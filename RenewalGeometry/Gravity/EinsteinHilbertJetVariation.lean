/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicDefectForcingExact

/-!
# The first variation of the Einstein–Hilbert density on metric 2-jets

Infrastructure for `thm:native-closure` (Einstein–Standard-Model action-closure manuscript,
bridge step P3: "the Euler rows of the native Lagrangian are the physical field equations"), in the
jet convention of `Gravity/HarmonicDefectForcingExact.lean` (any finite index type `n`):
`g`, `gi = g⁻¹`, `dg α μ ν = ∂_α g_{μν}`, `ddg α β μ ν = ∂_α∂_β g_{μν}`, Christoffel symbols
`chr gi dg`, their jet `dchr`, Ricci `ricci`, Einstein `einstein`.

A variation of the metric is a jet `(k, dk, ddk)` (`k = δg_{μν}`, `dk = ∂k`, `ddk = ∂∂k`).
The variations of the derived jets are the explicit product-rule expressions
`ginvVar = δg^{-1} = -g⁻¹ k g⁻¹`, `chrVar = δΓ`, `dginvVar = δ(∂g⁻¹)`, `dchrVar = δ(∂Γ)`,
`ricciVarJ = δRic`.

## Main results (pure finite index algebra, every statement exact)

* `dginv_eq_chr` — metric compatibility `∂_λ g^{μν} = -g^{μa}Γ^ν_{λa} - g^{νa}Γ^μ_{λa}`;
* `trace_chr` — `Σ_a Γ^a_{aλ} = ½ g^{ab}∂_λ g_{ab}`;
* `contracted_palatini` — **the contracted Palatini identity** for an arbitrary symmetric
  connection variation `X = δΓ` with arbitrary jet `dX`:
  `g^{μν} δRic_{μν} = ∂_λ V^λ + Γ^a_{aλ} V^λ`, `V^λ = g^{μν}X^λ_{μν} - g^{λμ}X^ν_{μν}`
  (`fluxV`, `fluxDivJ`), i.e. `√|g| g^{μν}δRic_{μν} = ∂_λ(√|g| V^λ)`;
* `eh_jet_variation` — **the Einstein–Hilbert variation on jets**:
  `δ(v R) = -v G^{μν} k_{μν} + v (∂_λV^λ + Γ^a_{aλ}V^λ)` with `δv = ½ v g^{μν}k_{μν}`,
  `G^{μν} = g^{μa}g^{νb}G_{ab}` (`einsteinUp`).
-/

namespace RenewalGeometry

namespace EHJetVariation

open Finset HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The variations of the derived jets -/

/-- `δg^{ab} = -g^{ac} k_{cd} g^{db}`. -/
def ginvVar (gi k : n → n → ℝ) (a b : n) : ℝ := -∑ c, ∑ d, gi a c * k c d * gi d b

/-- `δΓ^l_{μν} = Γ(δg⁻¹, ∂g) + Γ(g⁻¹, ∂k)`. -/
def chrVar (gi : n → n → ℝ) (dg : n → n → n → ℝ) (k : n → n → ℝ) (dk : n → n → n → ℝ)
    (l μ ν : n) : ℝ :=
  chr (ginvVar gi k) dg l μ ν + chr gi dk l μ ν

/-- `δ(∂_α g^{lσ})`. -/
def dginvVar (gi : n → n → ℝ) (dg : n → n → n → ℝ) (k : n → n → ℝ) (dk : n → n → n → ℝ)
    (α l σ : n) : ℝ :=
  -∑ a, ∑ b, (ginvVar gi k l a * dg α a b * gi b σ + gi l a * dk α a b * gi b σ +
    gi l a * dg α a b * ginvVar gi k b σ)

/-- `δ(∂_α Γ^l_{μν})`. -/
def dchrVar (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (k : n → n → ℝ)
    (dk : n → n → n → ℝ) (ddk : n → n → n → n → ℝ) (α l μ ν : n) : ℝ :=
  (1 / 2) * ∑ σ, dginvVar gi dg k dk α l σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν) +
    (1 / 2) * ∑ σ, dginv gi dg α l σ * (dk μ σ ν + dk ν σ μ - dk σ μ ν) +
    (1 / 2) * ∑ σ, ginvVar gi k l σ * (ddg α μ σ ν + ddg α ν σ μ - ddg α σ μ ν) +
    (1 / 2) * ∑ σ, gi l σ * (ddk α μ σ ν + ddk α ν σ μ - ddk α σ μ ν)

/-- `δRic_{μν}` from the connection `Γ`, its variation `X = δΓ` and `dX = δ(∂Γ)`. -/
def ricciVarJ (Γ X : n → n → n → ℝ) (dX : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ∑ α, dX α α μ ν - ∑ α, dX ν α μ α + ∑ α, ∑ l, (X α α l * Γ l μ ν + Γ α α l * X l μ ν) -
    ∑ α, ∑ l, (X α ν l * Γ l μ α + Γ α ν l * X l μ α)

/-- The Palatini flux `V^λ = g^{μν}X^λ_{μν} - g^{λμ}X^ν_{μν}`. -/
def fluxV (gi : n → n → ℝ) (X : n → n → n → ℝ) (lam : n) : ℝ :=
  ∑ μ, ∑ ν, gi μ ν * X lam μ ν - ∑ μ, ∑ ν, gi lam μ * X ν μ ν

/-- The jet of `∂_λV^λ` (summed over `λ`): `∂_λ g^{μν} X^λ_{μν} + g^{μν}∂_λX^λ_{μν} -
∂_λ g^{λμ} X^ν_{μν} - g^{λμ}∂_λX^ν_{μν}`, with `dgi α l σ = ∂_α g^{lσ}`, `dX α l μ ν = ∂_αX^l_{μν}`. -/
def fluxDivJ (gi : n → n → ℝ) (dgi : n → n → n → ℝ) (X : n → n → n → ℝ)
    (dX : n → n → n → n → ℝ) : ℝ :=
  ∑ lam, ((∑ μ, ∑ ν, (dgi lam μ ν * X lam μ ν + gi μ ν * dX lam lam μ ν)) -
    ∑ μ, ∑ ν, (dgi lam lam μ * X ν μ ν + gi lam μ * dX lam ν μ ν))

/-- The contravariant Einstein tensor `G^{μν} = g^{μa}g^{νb}G_{ab}`. -/
def einsteinUp (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (μ ν : n) :
    ℝ :=
  ∑ a, ∑ b, gi μ a * gi ν b * einstein g gi dg ddg a b

/-- The scalar curvature `R = g^{μν}R_{μν}`. -/
def scal (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) : ℝ :=
  trG gi (ricci gi dg ddg)

/-! ### Re-indexing helpers -/

theorem sum4_comm_inner (f : n → n → n → n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Iterated quadruple sums as sums over the product type. -/
theorem sum4_eq (f : n → n → n → n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ x : n × n × n × n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [Fintype.sum_prod_type]

/-- Re-indexing of quadruple sums along an equivalence of the index product. -/
theorem sum4_reindex (f g : n → n → n → n → ℝ) (e : (n × n × n × n) ≃ (n × n × n × n))
    (h : ∀ x : n × n × n × n, f x.1 x.2.1 x.2.2.1 x.2.2.2 =
      g (e x).1 (e x).2.1 (e x).2.2.1 (e x).2.2.2) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  rw [sum4_eq, sum4_eq]
  exact Fintype.sum_equiv e _ _ h

/-- Iterated triple sums as sums over the product type. -/
theorem sum3_eq (f : n → n → n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ x : n × n × n, f x.1 x.2.1 x.2.2 := by
  simp only [Fintype.sum_prod_type]

/-- Re-indexing of triple sums along an equivalence of the index product. -/
theorem sum3_reindex (f g : n → n → n → ℝ) (e : (n × n × n) ≃ (n × n × n))
    (h : ∀ x : n × n × n, f x.1 x.2.1 x.2.2 = g (e x).1 (e x).2.1 (e x).2.2) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ b, ∑ c, g a b c := by
  rw [sum3_eq, sum3_eq]
  exact Fintype.sum_equiv e _ _ h

/-! ### Metric compatibility -/

theorem chr_symm (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (l μ ν : n) : chr gi dg l μ ν = chr gi dg l ν μ := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ μ ν]
  ring

/-- **Metric compatibility**: `∂_λ g^{μν} = -g^{μa}Γ^ν_{λa} - g^{νa}Γ^μ_{λa}`. -/
theorem dginv_eq_chr (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (lam μ ν : n) :
    dginv gi dg lam μ ν = -∑ a, (gi μ a * chr gi dg ν lam a + gi ν a * chr gi dg μ lam a) := by
  unfold dginv chr
  simp only [Finset.mul_sum, Finset.sum_add_distrib, neg_inj]
  -- `Σ_a Σ_σ gi μ a gi ν σ (…)` and the swapped term
  have h1 : ∑ a, ∑ σ, gi μ a * ((1 / 2) * (gi ν σ * (dg lam σ a + dg a σ lam - dg σ lam a))) =
      ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam σ a * gi σ ν) +
        ∑ a, ∑ σ, (1 / 2) * (gi μ a * gi ν σ * (dg a σ lam - dg σ lam a)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hgi ν σ]; ring
  have h2 : ∑ a, ∑ σ, gi ν a * ((1 / 2) * (gi μ σ * (dg lam σ a + dg a σ lam - dg σ lam a))) =
      ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam a σ * gi σ ν) -
        ∑ a, ∑ σ, (1 / 2) * (gi μ a * gi ν σ * (dg a σ lam - dg σ lam a)) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hgi ν σ, hdg σ a lam, hdg a lam σ]; ring
  rw [h1, h2]
  have h3 : ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam σ a * gi σ ν) =
      ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam a σ * gi σ ν) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun σ _ => by rw [hdg lam σ a]
  rw [h3]
  have h4 : ∑ a, ∑ σ, gi μ a * dg lam a σ * gi σ ν =
      ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam a σ * gi σ ν) +
        ∑ a, ∑ σ, (1 / 2) * (gi μ a * dg lam a σ * gi σ ν) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [h4]
  ring

/-- `Σ_a Γ^a_{aλ} = ½ g^{ab}∂_λ g_{ab}`. -/
theorem trace_chr (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (lam : n) :
    ∑ a, chr gi dg a a lam = (1 / 2) * ∑ a, ∑ b, gi a b * dg lam a b := by
  unfold chr
  rw [← Finset.mul_sum]
  congr 1
  have h1 : ∑ a, ∑ σ, gi a σ * dg a σ lam = ∑ a, ∑ σ, gi a σ * dg σ a lam := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [hgi]
  have h2 : ∑ a, ∑ σ, gi a σ * (dg a σ lam + dg lam σ a - dg σ a lam) =
      ∑ a, ∑ σ, gi a σ * dg a σ lam + ∑ a, ∑ σ, gi a σ * dg lam σ a -
        ∑ a, ∑ σ, gi a σ * dg σ a lam := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h2, h1]
  have h3 : ∑ a, ∑ σ, gi a σ * dg lam σ a = ∑ a, ∑ b, gi a b * dg lam a b :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun σ _ => by rw [hdg lam σ a]
  rw [h3]; ring

/-! ### The contracted Palatini identity -/

/-- **The contracted Palatini identity**: for the Levi-Civita connection `Γ = chr gi dg` of a
symmetric inverse metric and symmetric first jet, any variation `X` symmetric in its lower
indices and any jet `dX`,
`g^{μν} δRic_{μν} = ∂_λV^λ + Γ^a_{aλ}V^λ` with `V^λ = g^{μν}X^λ_{μν} - g^{λμ}X^ν_{μν}`. -/
theorem contracted_palatini (gi : n → n → ℝ) (dg : n → n → n → ℝ) (X : n → n → n → ℝ)
    (dX : n → n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (hX : ∀ l μ ν, X l μ ν = X l ν μ) :
    ∑ μ, ∑ ν, gi μ ν * ricciVarJ (chr gi dg) X dX μ ν =
      fluxDivJ gi (dginv gi dg) X dX + ∑ lam, (∑ a, chr gi dg a a lam) * fluxV gi X lam := by
  set Γ := chr gi dg with hΓ
  have hΓs : ∀ l μ ν, Γ l μ ν = Γ l ν μ := chr_symm gi dg hdg
  have hdgi : ∀ lam μ ν, dginv gi dg lam μ ν =
      -∑ a, (gi μ a * Γ ν lam a + gi ν a * Γ μ lam a) := dginv_eq_chr gi dg hgi hdg
  -- the six pieces of the left side
  have hL : ∑ μ, ∑ ν, gi μ ν * ricciVarJ Γ X dX μ ν =
      ∑ μ, ∑ ν, ∑ α, gi μ ν * dX α α μ ν - ∑ μ, ∑ ν, ∑ α, gi μ ν * dX ν α μ α +
      ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (X α α l * Γ l μ ν) +
      ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (Γ α α l * X l μ ν) -
      ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (X α ν l * Γ l μ α) -
      ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (Γ α ν l * X l μ α) := by
    unfold ricciVarJ
    simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring_nf
  -- the pieces of the right side
  have hR : fluxDivJ gi (dginv gi dg) X dX + ∑ lam, (∑ a, Γ a a lam) * fluxV gi X lam =
      (∑ lam, ∑ μ, ∑ ν, dginv gi dg lam μ ν * X lam μ ν) +
      ∑ lam, ∑ μ, ∑ ν, gi μ ν * dX lam lam μ ν -
      ∑ lam, ∑ μ, ∑ ν, dginv gi dg lam lam μ * X ν μ ν -
      ∑ lam, ∑ μ, ∑ ν, gi lam μ * dX lam ν μ ν +
      ∑ lam, ∑ μ, ∑ ν, ∑ a, Γ a a lam * gi μ ν * X lam μ ν -
      ∑ lam, ∑ μ, ∑ ν, ∑ a, Γ a a lam * gi lam μ * X ν μ ν := by
    unfold fluxDivJ fluxV
    simp only [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring_nf
  rw [hL, hR]
  -- second-derivative terms
  have e1 : ∑ μ, ∑ ν, ∑ α, gi μ ν * dX α α μ ν = ∑ lam, ∑ μ, ∑ ν, gi μ ν * dX lam lam μ ν :=
    sum3_reindex _ _
      { toFun := fun x => (x.2.2, x.1, x.2.1)
        invFun := fun x => (x.2.1, x.2.2, x.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => rfl
  have e2 : ∑ μ, ∑ ν, ∑ α, gi μ ν * dX ν α μ α = ∑ lam, ∑ μ, ∑ ν, gi lam μ * dX lam ν μ ν := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun α _ => ?_
    rw [hgi]
  -- the `Γ^a_{aλ}` trace term
  have e3 : ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (Γ α α l * X l μ ν) =
      ∑ lam, ∑ μ, ∑ ν, ∑ a, Γ a a lam * gi μ ν * X lam μ ν := by
    refine sum4_reindex _ _
      { toFun := fun x => (x.2.2.2, x.1, x.2.1, x.2.2.1)
        invFun := fun x => (x.2.1, x.2.2.1, x.2.2.2, x.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  -- the metric-compatibility terms
  have hD1 : ∑ lam, ∑ μ, ∑ ν, dginv gi dg lam μ ν * X lam μ ν =
      -(∑ lam, ∑ μ, ∑ ν, ∑ a, gi μ a * Γ ν lam a * X lam μ ν) -
        ∑ lam, ∑ μ, ∑ ν, ∑ a, gi ν a * Γ μ lam a * X lam μ ν := by
    simp only [hdgi, neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  have hD2 : ∑ lam, ∑ μ, ∑ ν, dginv gi dg lam lam μ * X ν μ ν =
      -(∑ lam, ∑ μ, ∑ ν, ∑ a, gi lam a * Γ μ lam a * X ν μ ν) -
        ∑ lam, ∑ μ, ∑ ν, ∑ a, gi μ a * Γ lam lam a * X ν μ ν := by
    simp only [hdgi, neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [hD1, hD2]
  -- matching: `A = A'`
  have eA : ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (X α α l * Γ l μ ν) =
      ∑ lam, ∑ μ, ∑ ν, ∑ a, gi lam a * Γ μ lam a * X ν μ ν := by
    refine sum4_reindex _ _
      { toFun := fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1)
        invFun := fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    rw [hX x.2.2.1 x.2.2.1 x.2.2.2]
    ring
  -- `B = B'`
  have eB : ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (X α ν l * Γ l μ α) =
      ∑ lam, ∑ μ, ∑ ν, ∑ a, gi μ a * Γ ν lam a * X lam μ ν := by
    refine sum4_reindex _ _
      { toFun := fun x => (x.2.2.1, x.2.1, x.2.2.2, x.1)
        invFun := fun x => (x.2.2.2, x.2.1, x.1, x.2.2.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    rw [hgi x.1 x.2.1, hΓs x.2.2.2 x.1 x.2.2.1]
    ring
  -- `C = C'`
  have eC : ∑ μ, ∑ ν, ∑ α, ∑ l, gi μ ν * (Γ α ν l * X l μ α) =
      ∑ lam, ∑ μ, ∑ ν, ∑ a, gi ν a * Γ μ lam a * X lam μ ν := by
    refine sum4_reindex _ _
      { toFun := fun x => (x.2.2.2, x.2.2.1, x.1, x.2.1)
        invFun := fun x => (x.2.2.1, x.2.2.2, x.2.1, x.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    rw [hΓs x.2.2.1 x.2.1 x.2.2.2, hX x.2.2.2 x.1 x.2.2.1]
    ring
  -- the cancelling trace pair
  have eT : ∑ lam, ∑ μ, ∑ ν, ∑ a, gi μ a * Γ lam lam a * X ν μ ν =
      ∑ lam, ∑ μ, ∑ ν, ∑ a, Γ a a lam * gi lam μ * X ν μ ν := by
    refine sum4_reindex _ _
      { toFun := fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1)
        invFun := fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    rw [hgi x.2.1 x.2.2.2]
    ring
  rw [e1, e2, e3, eA, eB, eC, eT]
  ring

/-! ### The Einstein–Hilbert variation -/

/-- The variation of the Ricci jet of the metric. -/
def ricciVar (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (k : n → n → ℝ)
    (dk : n → n → n → ℝ) (ddk : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ricciVarJ (chr gi dg) (chrVar gi dg k dk) (dchrVar gi dg ddg k dk ddk) μ ν

/-- The variation of the scalar curvature `δR = δg^{μν}R_{μν} + g^{μν}δR_{μν}`. -/
def scalVar (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (k : n → n → ℝ)
    (dk : n → n → n → ℝ) (ddk : n → n → n → n → ℝ) : ℝ :=
  trG (ginvVar gi k) (ricci gi dg ddg) + trG gi (ricciVar gi dg ddg k dk ddk)

theorem chrVar_symm (gi : n → n → ℝ) (dg : n → n → n → ℝ) (k : n → n → ℝ) (dk : n → n → n → ℝ)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (hdk : ∀ α μ ν, dk α μ ν = dk α ν μ) (l μ ν : n) :
    chrVar gi dg k dk l μ ν = chrVar gi dg k dk l ν μ := by
  unfold chrVar
  rw [chr_symm _ dg hdg, chr_symm gi dk hdk]

/-- `g^{μa} g_{ab} g^{bν} = g^{μν}`. -/
theorem ginv_g_ginv (g gi : n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) (μ ν : n) :
    ∑ a, ∑ b, gi μ a * gi ν b * g a b = gi μ ν := by
  have : ∀ a, ∑ b, gi μ a * gi ν b * g a b = gi μ a * (if a = ν then 1 else 0) := by
    intro a
    rw [← hinv a ν, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hgi ν b]; ring
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The Einstein–Hilbert variation on metric 2-jets.**  With `δv = ½ v g^{μν}k_{μν}`:
`δv R + v δR = -v G^{μν}k_{μν} + v(∂_λV^λ + Γ^a_{aλ}V^λ)`, `V = fluxV g⁻¹ δΓ`, where
`∂_λV^λ` is the jet `fluxDivJ` built from `∂g⁻¹ = dginv` and `∂δΓ = dchrVar`. -/
theorem eh_jet_variation (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (k : n → n → ℝ) (dk : n → n → n → ℝ) (ddk : n → n → n → n → ℝ) (v : ℝ)
    (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ) (hdk : ∀ α μ ν, dk α μ ν = dk α ν μ) :
    ((1 / 2) * v * trG gi k) * scal gi dg ddg + v * scalVar gi dg ddg k dk ddk =
      -(v * ∑ μ, ∑ ν, einsteinUp g gi dg ddg μ ν * k μ ν) +
        v * (fluxDivJ gi (dginv gi dg) (chrVar gi dg k dk) (dchrVar gi dg ddg k dk ddk) +
          ∑ lam, (∑ a, chr gi dg a a lam) * fluxV gi (chrVar gi dg k dk) lam) := by
  have hP := contracted_palatini gi dg (chrVar gi dg k dk) (dchrVar gi dg ddg k dk ddk) hgi hdg
    (chrVar_symm gi dg k dk hdg hdk)
  unfold scalVar
  rw [show trG gi (ricciVar gi dg ddg k dk ddk) =
      ∑ μ, ∑ ν, gi μ ν * ricciVarJ (chr gi dg) (chrVar gi dg k dk)
        (dchrVar gi dg ddg k dk ddk) μ ν from rfl, hP]
  -- the algebraic part: `½ R g^{μν}k_{μν} + δg^{μν}R_{μν} = -G^{μν}k_{μν}`
  have hG : ∑ μ, ∑ ν, einsteinUp g gi dg ddg μ ν * k μ ν =
      -(trG (ginvVar gi k) (ricci gi dg ddg)) - (1 / 2) * trG gi k * scal gi dg ddg := by
    set Ric := ricci gi dg ddg
    set R := scal gi dg ddg
    have hE : ∀ μ ν, einsteinUp g gi dg ddg μ ν =
        ∑ a, ∑ b, gi μ a * gi ν b * Ric a b - (1 / 2) * R * gi μ ν := by
      intro μ ν
      unfold einsteinUp einstein
      rw [← ginv_g_ginv g gi hgi hinv μ ν, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      show _ = _ - (1 / 2) * trG gi Ric * _
      ring
    simp only [hE, sub_mul, Finset.sum_sub_distrib]
    have h1 : ∑ μ, ∑ ν, (∑ a, ∑ b, gi μ a * gi ν b * Ric a b) * k μ ν =
        -trG (ginvVar gi k) Ric := by
      unfold trG ginvVar
      simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul]
      refine sum4_reindex _ _
        { toFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
          invFun := fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1)
          left_inv := fun x => rfl
          right_inv := fun x => rfl } fun x => ?_
      simp only [Equiv.coe_fn_mk]
      rw [hgi x.1 x.2.2.1]
      ring
    have h2 : ∑ μ, ∑ ν, (1 / 2) * R * gi μ ν * k μ ν = (1 / 2) * trG gi k * R := by
      unfold trG
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
    rw [h1, h2]
  rw [hG]
  ring

end

end EHJetVariation

end RenewalGeometry
