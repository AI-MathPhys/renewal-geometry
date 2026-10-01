/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact harmonic-defect forcing identity (`lem:harmonic-defect-forcing`)

Einstein–SM action closure, `lem:harmonic-defect-forcing`, as an exact identity of finite
index algebra on the metric 2-jet at a point (the convention of
`Gravity/CoordinateCurvature.lean`), over an arbitrary finite index type `n` (dimension four
where the trace computations need it, `Fintype.card n = 4`).

Data: `g`, its inverse `gi` (`g gi = 1`, `gi` symmetric), `dg α μ ν = ∂_α g_{μν}`,
`ddg α β μ ν = ∂_α∂_β g_{μν}` (symmetric in `αβ` and in `μν`).  The derived jets are the
ones produced by the product rule: `∂ g⁻¹ = -g⁻¹ ∂g g⁻¹` (`dginv`; forced by
`dginv_unique`), `Γ = chr`, `∂Γ = dchr = dchr1 + dchr2`, `C^μ = g^{αβ}Γ^μ_{αβ}`,
`∇_μ C_ν = ∂_μ(g_{νλ}C^λ) - Γ^λ_{μν}C_λ` (`nablaDefect`).

* `reducedEinstein_eq` — `Ĝ = G - 𝓗` (`eq:reduced-Einstein`, `eq:harmonic-defect-tensor`);
* `trG_defectTensor` — `tr_g 𝓗 = -∇_αC^α` in dimension four;
* `harmonic_residual_trace_reversal` — `eq:harmonic-residual-trace-reversal`;
* `ricci_sub_symDefect` — the reduced Ricci identity
  `R_{μν} - ∇_{(μ}C_{ν)} = -½ g^{αβ}∂_α∂_β g_{μν} + 𝓠_{μν}(g, ∂g)`, with the explicit
  remainder `qRem` (no second derivatives), proved via the principal-part cancellation
  `principal_part`;
* `qRem_smul`, `qRem_contDiff` — `𝓠` is quadratic in `∂g` and a smooth (polynomial)
  function of `(g, g⁻¹, ∂g)`;
* `ricci_trace_reversal` — `eq:trace-reversal-residual`;
* `off_harmonic_metric_wave` — `eq:off-harmonic-metric-wave`.
-/

namespace RenewalGeometry

namespace HarmonicDefect

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Christoffel symbols `Γ^λ_{μν} = ½ g^{λσ}(∂_μ g_{σν} + ∂_ν g_{σμ} - ∂_σ g_{μν})` from
the inverse metric `gi` and the first jet `dg α μ ν = ∂_α g_{μν}`. -/
def chr (gi : n → n → ℝ) (dg : n → n → n → ℝ) (l μ ν : n) : ℝ :=
  (1 / 2) * ∑ σ, gi l σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν)

/-- First jet of the inverse metric, `∂_α g^{λσ} = -g^{λa} ∂_α g_{ab} g^{bσ}`. -/
def dginv (gi : n → n → ℝ) (dg : n → n → n → ℝ) (α l σ : n) : ℝ :=
  -∑ a, ∑ b, gi l a * dg α a b * gi b σ

/-- The part of `∂_α Γ^λ_{μν}` coming from the differentiated inverse metric. -/
def dchr1 (gi : n → n → ℝ) (dg : n → n → n → ℝ) (α l μ ν : n) : ℝ :=
  (1 / 2) * ∑ σ, dginv gi dg α l σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν)

/-- The second-derivative part of `∂_α Γ^λ_{μν}`, with `ddg α β μ ν = ∂_α∂_β g_{μν}`. -/
def dchr2 (gi : n → n → ℝ) (ddg : n → n → n → n → ℝ) (α l μ ν : n) : ℝ :=
  (1 / 2) * ∑ σ, gi l σ * (ddg α μ σ ν + ddg α ν σ μ - ddg α σ μ ν)

/-- Ricci tensor from a connection jet `(Γ, D = ∂Γ)`:
`R_{μν} = ∂_αΓ^α_{μν} - ∂_νΓ^α_{μα} + Γ^α_{αλ}Γ^λ_{μν} - Γ^α_{νλ}Γ^λ_{μα}`. -/
def ricciJ (Γ : n → n → n → ℝ) (D : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ∑ α, D α α μ ν - ∑ α, D ν α μ α + ∑ α, ∑ l, Γ α α l * Γ l μ ν - ∑ α, ∑ l, Γ α ν l * Γ l μ α

/-- The harmonic defect `C^μ = g^{αβ} Γ^μ_{αβ}`. -/
def cUp (gi : n → n → ℝ) (Γ : n → n → n → ℝ) (μ : n) : ℝ :=
  ∑ a, ∑ b, gi a b * Γ μ a b

/-- Its jet `∂_α C^μ = ∂_α g^{ab} Γ^μ_{ab} + g^{ab} ∂_α Γ^μ_{ab}`. -/
def dcUp (gi : n → n → ℝ) (dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (D : n → n → n → n → ℝ) (α μ : n) : ℝ :=
  ∑ a, ∑ b, (dgi α a b * Γ μ a b + gi a b * D α μ a b)

/-- The lowered defect `C_ν = g_{νμ} C^μ`. -/
def cDown (g gi : n → n → ℝ) (Γ : n → n → n → ℝ) (ν : n) : ℝ :=
  ∑ μ, g ν μ * cUp gi Γ μ

/-- `∇_μ C_ν = ∂_μ (g_{νλ} C^λ) - Γ^λ_{μν} C_λ` from the jets. -/
def nablaC (g gi : n → n → ℝ) (dg dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (D : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ∑ l, (dg μ ν l * cUp gi Γ l + g ν l * dcUp gi dgi Γ D μ l) - ∑ l, Γ l μ ν * cDown g gi Γ l

/-- `∇_{(μ} C_{ν)}`. -/
def symNablaC (g gi : n → n → ℝ) (dg dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (D : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  (nablaC g gi dg dgi Γ D μ ν + nablaC g gi dg dgi Γ D ν μ) / 2

/-- Metric trace `tr_g X = g^{μν} X_{μν}`. -/
def trG (gi : n → n → ℝ) (X : n → n → ℝ) : ℝ := ∑ μ, ∑ ν, gi μ ν * X μ ν

/-- Trace reversal `X^tr = X - ½ g tr_g X`. -/
def traceRev (g gi : n → n → ℝ) (X : n → n → ℝ) (μ ν : n) : ℝ :=
  X μ ν - (1 / 2) * g μ ν * trG gi X

/-! ### The metric 2-jet -/

/-- The full jet `∂_α Γ^λ_{μν}` of the Christoffel symbols. -/
def dchr (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (α l μ ν : n) : ℝ :=
  dchr1 gi dg α l μ ν + dchr2 gi ddg α l μ ν

/-- Ricci tensor of the metric 2-jet. -/
def ricci (gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ricciJ (chr gi dg) (dchr gi dg ddg) μ ν

/-- Einstein tensor `G = Ric - ½ g R` of the metric 2-jet. -/
def einstein (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ricci gi dg ddg μ ν - (1 / 2) * g μ ν * trG gi (ricci gi dg ddg)

/-- `∇_μ C_ν` of the metric 2-jet, with `C^μ = g^{αβ}Γ^μ_{αβ}`. -/
def nablaDefect (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (μ ν : n) : ℝ :=
  nablaC g gi dg (dginv gi dg) (chr gi dg) (dchr gi dg ddg) μ ν

/-- `∇_{(μ}C_{ν)}` of the metric 2-jet. -/
def symDefect (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (μ ν : n) : ℝ :=
  (nablaDefect g gi dg ddg μ ν + nablaDefect g gi dg ddg ν μ) / 2

/-- `∇_α C^α = g^{αβ} ∇_α C_β` (metric compatibility). -/
def divDefect (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) : ℝ :=
  trG gi (nablaDefect g gi dg ddg)

/-- The harmonic-defect tensor `𝓗_{μν} = ∇_{(μ}C_{ν)} - ½ g_{μν} ∇_α C^α`
(`eq:harmonic-defect-tensor`). -/
def defectTensor (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (μ ν : n) : ℝ :=
  symDefect g gi dg ddg μ ν - (1 / 2) * g μ ν * divDefect g gi dg ddg

/-- The reduced Einstein tensor `Ĝ_{μν} = G_{μν} - ∇_{(μ}C_{ν)} + ½ g_{μν} ∇^α C_α`
(`eq:reduced-Einstein`). -/
def reducedEinstein (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (μ ν : n) : ℝ :=
  einstein g gi dg ddg μ ν - symDefect g gi dg ddg μ ν + (1 / 2) * g μ ν * divDefect g gi dg ddg

/-- The principal (metric-wave) part `g^{αβ} ∂_α∂_β g_{μν}`. -/
def waveOp (gi : n → n → ℝ) (ddg : n → n → n → n → ℝ) (μ ν : n) : ℝ :=
  ∑ α, ∑ β, gi α β * ddg α β μ ν

/-- The first-order remainder `𝓠_{μν}(g, ∂g)`: the reduced Ricci combination with the
second-derivative part of `∂Γ` removed.  It involves only `g`, `g⁻¹` and `∂g`. -/
def qRem (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (μ ν : n) : ℝ :=
  ricciJ (chr gi dg) (dchr1 gi dg) μ ν -
    (nablaC g gi dg (dginv gi dg) (chr gi dg) (dchr1 gi dg) μ ν +
      nablaC g gi dg (dginv gi dg) (chr gi dg) (dchr1 gi dg) ν μ) / 2

/-! ### Affinity in the derivative jet -/

theorem ricciJ_add (Γ : n → n → n → ℝ) (D₁ D₂ : n → n → n → n → ℝ) (μ ν : n) :
    ricciJ Γ (fun α l a b => D₁ α l a b + D₂ α l a b) μ ν =
      ricciJ Γ D₁ μ ν + (∑ α, D₂ α α μ ν - ∑ α, D₂ ν α μ α) := by
  unfold ricciJ
  simp only [Finset.sum_add_distrib]
  ring

theorem nablaC_add (g gi : n → n → ℝ) (dg dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (D₁ D₂ : n → n → n → n → ℝ) (μ ν : n) :
    nablaC g gi dg dgi Γ (fun α l a b => D₁ α l a b + D₂ α l a b) μ ν =
      nablaC g gi dg dgi Γ D₁ μ ν + ∑ l, g ν l * ∑ a, ∑ b, gi a b * D₂ μ l a b := by
  unfold nablaC dcUp
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-! ### The second-derivative part -/

/-- Index contraction with `g g⁻¹ = 1`. -/
theorem contract_inverse (g gi : n → n → ℝ)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (c : ℝ) (X : n → n → n → ℝ) (ν : n) :
    ∑ l, g ν l * ∑ a, ∑ b, gi a b * (c * ∑ σ, gi l σ * X a b σ) =
      c * ∑ a, ∑ b, gi a b * X a b ν := by
  have hin : ∀ a b σ, ∑ l, g ν l * (gi a b * (c * (gi l σ * X a b σ))) =
      gi a b * (c * X a b σ) * (if ν = σ then 1 else 0) := by
    intro a b σ
    rw [← hinv ν σ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ l, g ν l * ∑ a, ∑ b, gi a b * (c * ∑ σ, gi l σ * X a b σ)
      = ∑ l, ∑ a, ∑ b, ∑ σ, g ν l * (gi a b * (c * (gi l σ * X a b σ))) := by
        simp only [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∑ σ, ∑ l, g ν l * (gi a b * (c * (gi l σ * X a b σ))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ σ, gi a b * (c * X a b σ) * (if ν = σ then 1 else 0) := by
        simp only [hin]
    _ = c * ∑ a, ∑ b, gi a b * X a b ν := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring

/-- Relabelling `a ↔ b` against a symmetric inverse metric. -/
theorem sum_swap_symm (gi : n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a) (f : n → n → ℝ) :
    ∑ a, ∑ b, gi a b * f a b = ∑ a, ∑ b, gi a b * f b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hgi]

/-- **The principal-part cancellation.**  The second-derivative part of
`R_{μν} - ∇_{(μ}C_{ν)}` is exactly `-½ g^{αβ} ∂_α∂_β g_{μν}`. -/
theorem principal_part (g gi : n → n → ℝ) (ddg : n → n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν)
    (hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (μ ν : n) :
    (∑ α, dchr2 gi ddg α α μ ν - ∑ α, dchr2 gi ddg ν α μ α) -
        ((∑ l, g ν l * ∑ a, ∑ b, gi a b * dchr2 gi ddg μ l a b) +
          (∑ l, g μ l * ∑ a, ∑ b, gi a b * dchr2 gi ddg ν l a b)) / 2 =
      -(1 / 2) * waveOp gi ddg μ ν := by
  -- the four basic contractions
  set T1 := ∑ a, ∑ b, gi a b * ddg a μ b ν with hT1
  set T2 := ∑ a, ∑ b, gi a b * ddg a ν b μ with hT2
  set T3 := ∑ a, ∑ b, gi a b * ddg μ ν a b with hT3
  set W := waveOp gi ddg μ ν with hW
  have hsum3 : ∀ (f₁ f₂ f₃ : n → n → ℝ),
      ∑ a, ∑ b, gi a b * (f₁ a b + f₂ a b - f₃ a b) =
        ∑ a, ∑ b, gi a b * f₁ a b + ∑ a, ∑ b, gi a b * f₂ a b -
          ∑ a, ∑ b, gi a b * f₃ a b := by
    intro f₁ f₂ f₃
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the trace part `A = Σ_α ∂_αΓ^α_{μν}`
  have hA : ∑ α, dchr2 gi ddg α α μ ν = (1 / 2) * (T1 + T2 - W) := by
    unfold dchr2
    rw [← Finset.mul_sum, hsum3]
    rfl
  -- the part `B = Σ_α ∂_νΓ^α_{μα}`
  have hB : ∑ α, dchr2 gi ddg ν α μ α = (1 / 2) * T3 := by
    unfold dchr2
    rw [← Finset.mul_sum, hsum3]
    have h1 : ∑ a, ∑ b, gi a b * ddg ν μ b a = T3 := by
      rw [hT3]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs1 ν μ, hs2 μ ν]
    have h23 : ∑ a, ∑ b, gi a b * ddg ν a b μ = ∑ a, ∑ b, gi a b * ddg ν b μ a := by
      rw [sum_swap_symm gi hgi (fun a b => ddg ν b μ a)]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs2 ν a]
    rw [h1, h23]
    ring
  -- the contracted defect parts
  have hC1 : ∑ l, g ν l * ∑ a, ∑ b, gi a b * dchr2 gi ddg μ l a b = (1 / 2) * (2 * T1 - T3) := by
    unfold dchr2
    rw [contract_inverse g gi hinv (1 / 2) (fun a b σ => ddg μ a σ b + ddg μ b σ a - ddg μ σ a b) ν]
    rw [hsum3]
    have h1 : ∑ a, ∑ b, gi a b * ddg μ a ν b = T1 := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs1 μ a, hs2 a μ]
    have h2 : ∑ a, ∑ b, gi a b * ddg μ b ν a = T1 := by
      rw [sum_swap_symm gi hgi (fun a b => ddg μ b ν a)]
      exact h1
    rw [h1, h2]
    ring
  have hC2 : ∑ l, g μ l * ∑ a, ∑ b, gi a b * dchr2 gi ddg ν l a b = (1 / 2) * (2 * T2 - T3) := by
    unfold dchr2
    rw [contract_inverse g gi hinv (1 / 2) (fun a b σ => ddg ν a σ b + ddg ν b σ a - ddg ν σ a b) μ]
    rw [hsum3]
    have h1 : ∑ a, ∑ b, gi a b * ddg ν a μ b = T2 := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs1 ν a, hs2 a ν]
    have h2 : ∑ a, ∑ b, gi a b * ddg ν b μ a = T2 := by
      rw [sum_swap_symm gi hgi (fun a b => ddg ν b μ a)]
      exact h1
    have h3 : ∑ a, ∑ b, gi a b * ddg ν μ a b = T3 := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs1 ν μ]
    rw [h1, h2, h3]
    ring
  rw [hA, hB, hC1, hC2]
  ring

/-! ### The reduced Ricci identity -/

/-- **Reduced Ricci identity.**  For every metric 2-jet,
`R_{μν} - ∇_{(μ}C_{ν)} = -½ g^{αβ}∂_α∂_β g_{μν} + 𝓠_{μν}(g, ∂g)`. -/
theorem ricci_sub_symDefect (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν)
    (hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ) (μ ν : n) :
    ricci gi dg ddg μ ν - symDefect g gi dg ddg μ ν =
      -(1 / 2) * waveOp gi ddg μ ν + qRem g gi dg μ ν := by
  have hD : dchr gi dg ddg = fun α l a b => dchr1 gi dg α l a b + dchr2 gi ddg α l a b := rfl
  unfold ricci symDefect nablaDefect qRem
  rw [hD, ricciJ_add, nablaC_add, nablaC_add]
  have := principal_part g gi ddg hgi hinv hs1 hs2 μ ν
  linarith

/-! ### `𝓠` is smooth in `(g, g⁻¹, ∂g)` and quadratic in `∂g` -/

theorem chr_smul (gi : n → n → ℝ) (dg : n → n → n → ℝ) (t : ℝ) :
    chr gi (fun α a b => t * dg α a b) = fun l μ ν => t * chr gi dg l μ ν := by
  funext l μ ν
  simp only [chr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem dginv_smul (gi : n → n → ℝ) (dg : n → n → n → ℝ) (t : ℝ) :
    dginv gi (fun α a b => t * dg α a b) = fun α l σ => t * dginv gi dg α l σ := by
  funext α l σ
  simp only [dginv, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem dchr1_smul (gi : n → n → ℝ) (dg : n → n → n → ℝ) (t : ℝ) :
    dchr1 gi (fun α a b => t * dg α a b) = fun α l μ ν => t ^ 2 * dchr1 gi dg α l μ ν := by
  funext α l μ ν
  rw [dchr1, dginv_smul]
  simp only [dchr1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem ricciJ_smul (Γ : n → n → n → ℝ) (D : n → n → n → n → ℝ) (t : ℝ) (μ ν : n) :
    ricciJ (fun l a b => t * Γ l a b) (fun α l a b => t ^ 2 * D α l a b) μ ν =
      t ^ 2 * ricciJ Γ D μ ν := by
  simp only [ricciJ, mul_sub, mul_add, Finset.mul_sum]
  ring_nf

theorem cUp_smul (gi : n → n → ℝ) (Γ : n → n → n → ℝ) (t : ℝ) (μ : n) :
    cUp gi (fun l a b => t * Γ l a b) μ = t * cUp gi Γ μ := by
  simp only [cUp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem nablaC_smul (g gi : n → n → ℝ) (dg dgi : n → n → n → ℝ) (Γ : n → n → n → ℝ)
    (D : n → n → n → n → ℝ) (t : ℝ) (μ ν : n) :
    nablaC g gi (fun α a b => t * dg α a b) (fun α a b => t * dgi α a b)
        (fun l a b => t * Γ l a b) (fun α l a b => t ^ 2 * D α l a b) μ ν =
      t ^ 2 * nablaC g gi dg dgi Γ D μ ν := by
  simp only [nablaC, cDown, cUp_smul, dcUp, mul_sub, mul_add, Finset.mul_sum]
  ring_nf

/-- `𝓠_{μν}` is **quadratic** in the first metric derivatives:
`𝓠(g, g⁻¹, t ∂g) = t² 𝓠(g, g⁻¹, ∂g)`. -/
theorem qRem_smul (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (t : ℝ) (μ ν : n) :
    qRem g gi (fun α a b => t * dg α a b) μ ν = t ^ 2 * qRem g gi dg μ ν := by
  simp only [qRem, chr_smul, dginv_smul, dchr1_smul, ricciJ_smul, nablaC_smul]
  ring

/-- `𝓠_{μν}` is a **smooth** (polynomial) function of `(g, g⁻¹, ∂g)`. -/
theorem qRem_contDiff (μ ν : n) :
    ContDiff ℝ ⊤ (fun p : (n → n → ℝ) × (n → n → ℝ) × (n → n → n → ℝ) =>
      qRem p.1 p.2.1 p.2.2 μ ν) := by
  simp only [qRem, ricciJ, nablaC, dcUp, cDown, cUp, chr, dchr1, dginv]
  fun_prop

/-! ### Traces and trace reversal in four dimensions -/

theorem trG_comb (gi : n → n → ℝ) (A B C : n → n → ℝ) (a b c : ℝ) :
    trG gi (fun μ ν => a * A μ ν + b * B μ ν + c * C μ ν) =
      a * trG gi A + b * trG gi B + c * trG gi C := by
  simp only [trG, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
    · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
  · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring

/-- `tr_g g = dim`. -/
theorem trG_metric (g gi : n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) :
    trG gi g = Fintype.card n := by
  unfold trG
  have : ∀ μ, ∑ ν, gi μ ν * g μ ν = 1 := by
    intro μ
    have h := hinv μ μ
    simp only [↓reduceIte] at h
    rw [← h]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hgi, mul_comm]
  simp [this]

/-- The trace of a symmetrisation is the trace. -/
theorem trG_symmetrize (gi : n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a) (N : n → n → ℝ) :
    trG gi (fun μ ν => (N μ ν + N ν μ) / 2) = trG gi N := by
  have h1 : trG gi (fun μ ν => (N μ ν + N ν μ) / 2) =
      (1 / 2) * trG gi N + (1 / 2) * trG gi (fun μ ν => N ν μ) + 0 * trG gi N := by
    rw [← trG_comb]
    congr 1
    funext μ ν
    ring
  have h2 : trG gi (fun μ ν => N ν μ) = trG gi N := by
    unfold trG
    exact (sum_swap_symm gi hgi (fun a b => N a b)).symm
  rw [h1, h2]
  ring

/-- `lem:harmonic-defect-forcing`, first identity: `Ĝ = G - 𝓗`. -/
theorem reducedEinstein_eq (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (μ ν : n) :
    reducedEinstein g gi dg ddg μ ν = einstein g gi dg ddg μ ν - defectTensor g gi dg ddg μ ν := by
  unfold reducedEinstein defectTensor
  ring

/-- `tr_g 𝓗 = -∇_α C^α` in dimension four. -/
theorem trG_defectTensor (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) :
    trG gi (defectTensor g gi dg ddg) = -divDefect g gi dg ddg := by
  have h : defectTensor g gi dg ddg = fun μ ν =>
      1 * symDefect g gi dg ddg μ ν + (-(1 / 2) * divDefect g gi dg ddg) * g μ ν +
        0 * g μ ν := by
    funext μ ν
    unfold defectTensor
    ring
  rw [h, trG_comb, trG_metric g gi hgi hinv, hcard]
  have hs : trG gi (symDefect g gi dg ddg) = divDefect g gi dg ddg := by
    unfold symDefect divDefect
    exact trG_symmetrize gi hgi _
  rw [hs]
  push_cast
  ring

/-- **`eq:harmonic-residual-trace-reversal`.**  In four dimensions, for any stress `T` and
constants `Λ, κ`, with `𝓔 = G + Λ g - κ T`,
`(Ĝ + Λ g - κ T)^{tr}_{μν} = 𝓔^{tr}_{μν} - ∇_{(μ}C_{ν)}`. -/
theorem harmonic_residual_trace_reversal (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) (T : n → n → ℝ) (Λ κ : ℝ) (μ ν : n) :
    traceRev g gi (fun a b => reducedEinstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν =
      traceRev g gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν -
        symDefect g gi dg ddg μ ν := by
  set E : n → n → ℝ := fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b with hE
  have hX : (fun a b => reducedEinstein g gi dg ddg a b + Λ * g a b - κ * T a b) =
      fun a b => 1 * E a b + (-1) * defectTensor g gi dg ddg a b + 0 * E a b := by
    funext a b
    rw [reducedEinstein_eq, hE]
    ring
  unfold traceRev
  rw [hX, trG_comb, trG_defectTensor g gi dg ddg hgi hinv hcard]
  simp only [hE]
  unfold defectTensor
  ring

/-- **`eq:trace-reversal-residual`.**  In four dimensions, with `𝓔 = G + Λ g - κ T`,
`R_{μν} = κ (T - ½ g tr_g T)_{μν} + Λ g_{μν} + 𝓔^{tr}_{μν}`. -/
theorem ricci_trace_reversal (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) (T : n → n → ℝ) (Λ κ : ℝ) (μ ν : n) :
    ricci gi dg ddg μ ν =
      κ * traceRev g gi T μ ν + Λ * g μ ν +
        traceRev g gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν := by
  have htrE : trG gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) =
      -trG gi (ricci gi dg ddg) + 4 * Λ - κ * trG gi T := by
    have h : (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) =
        fun a b => 1 * ricci gi dg ddg a b +
          (Λ - (1 / 2) * trG gi (ricci gi dg ddg)) * g a b + (-κ) * T a b := by
      funext a b
      unfold einstein
      ring
    rw [h, trG_comb, trG_metric g gi hgi hinv, hcard]
    push_cast
    ring
  unfold traceRev
  rw [htrE]
  unfold einstein
  ring

/-- **`eq:off-harmonic-metric-wave`** (`lem:harmonic-defect-forcing`).  In four dimensions,
for every metric 2-jet, stress `T` and constants `Λ, κ`,
`-½ g^{αβ}∂_α∂_β g_{μν} + 𝓠_{μν}(g, ∂g) =
  κ (T - ½ g tr_g T)_{μν} + Λ g_{μν} + 𝓔^{tr}_{μν} - ∇_{(μ}C_{ν)}`. -/
theorem off_harmonic_metric_wave (g gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν)
    (hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ)
    (hcard : Fintype.card n = 4) (T : n → n → ℝ) (Λ κ : ℝ) (μ ν : n) :
    -(1 / 2) * waveOp gi ddg μ ν + qRem g gi dg μ ν =
      κ * traceRev g gi T μ ν + Λ * g μ ν +
        traceRev g gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν -
          symDefect g gi dg ddg μ ν := by
  rw [← ricci_sub_symDefect g gi dg ddg hgi hinv hs1 hs2 μ ν,
    ricci_trace_reversal g gi dg ddg hgi hinv hcard T Λ κ μ ν]

/-- The inverse-metric jet is forced: any jet `D` of `g⁻¹` compatible with the
differentiated identity `∂_α(g g⁻¹) = 0`, i.e. `∂_α g · g⁻¹ + g · D_α = 0`, equals
`dginv = -g⁻¹ ∂_α g g⁻¹` (given `g⁻¹ g = 1`). -/
theorem dginv_unique (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (D : n → n → n → ℝ)
    (hleft : ∀ a c, ∑ b, gi a b * g b c = if a = c then 1 else 0)
    (hD : ∀ α a c, ∑ b, (dg α a b * gi b c + g a b * D α b c) = 0) :
    D = dginv gi dg := by
  funext α l σ
  have h1 : D α l σ = ∑ a, (if l = a then 1 else 0) * D α a σ := by
    simp
  have h2 : ∀ b, ∑ a, g b a * D α a σ = -∑ a, dg α b a * gi a σ := by
    intro b
    have := hD α b σ
    rw [Finset.sum_add_distrib] at this
    linarith
  rw [h1]
  simp_rw [← hleft]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold dginv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := h2 b
  calc ∑ a, gi l b * g b a * D α a σ = gi l b * ∑ a, g b a * D α a σ := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
    _ = gi l b * -∑ a, dg α b a * gi a σ := by rw [this]
    _ = -∑ a, gi l b * dg α b a * gi a σ := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        ring

end

end HarmonicDefect

end RenewalGeometry
