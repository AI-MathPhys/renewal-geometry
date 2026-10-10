/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedConstraintReduction
import RenewalGeometry.Algebra.DetDerivative

/-!
# Noether identities of the Einstein–Standard-Model theory data: the current sector

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`
(`app:generated-dynamics`): the propagation of the Gauss constraint along the independent symmetric
system uses the **Yang–Mills Bianchi identity** `D^νD^μF_{μν} = 0` and the **Noether identity of
the gauge current** `D^νJ_ν = (combination of the matter Euler residuals)`, which the manuscript
uses implicitly (for theory data violating it the Gauss law does not propagate:
`GenConstraintObs.bad_obstruction`).

## Densities

For a smooth field tuple `z` (`ActualJetBridge.Tuple`) put `ϱ = √|det g|` (`rho`).  Then

* `line_rho` — `∂_δϱ = ϱ Γ^λ{}_{λδ}` (Jacobi's formula `ActualJetCurveCalculus`-style along lines,
  from `RenewalGeometry.hasDerivAt_det`);
* **`div_density`** (the divergence of a vector density): for every differentiable covector field
  `w_β` (values in any normed space)
  `Σ_ν ∂_ν(ϱ g^{νβ}w_β) = ϱ g^{νρ}(∂_ρw_ν - Γ^l{}_{ρν}w_l)`;
* **`ymDensity_eq`** (the Yang–Mills divergence as a density divergence): with the antisymmetric
  density `𝔉^{μν} = ϱ g^{μα}g^{νβ}F_{αβ}`,
  `ϱ g^{νβ}(∇^μF_{μβ} + [A^μ, F_{μβ}]) = ∂_μ𝔉^{μν} + [A_μ, 𝔉^{μν}]`;
* **`ym_bianchi_density`** (the Yang–Mills Bianchi–Noether identity at field level): the covariant
  divergence of the Yang–Mills divergence density vanishes identically,
  `∂_ν(ϱ g^{νβ}∇^μF_{μβ}) + [A_ν, ϱ g^{νβ}∇^μF_{μβ}] = 0`
  (`∂_ν∂_μ𝔉^{μν} = 0`, Jacobi identity, and `[F_{μν}, 𝔉^{μν}] = 0`).

## The current Noether structure

* `densJ`, `divJ` — the current density `ϱ g^{νβ}J_β(z)` of the theory data along `z` and its gauge
  covariant divergence `ϱ D^νJ_ν` (`divJ_eq`: Christoffel form);
* **`CurrentNoether SM`** — the Noether identity of the gauge current as a hypothesis **on the
  theory data** (for every smooth tuple, at every point): `ϱ D^νJ_ν = K(r_H, r_D, r̄_D)` with `K`
  linear in the Higgs and Dirac residuals;
* **`div_rA`** — for every smooth tuple, the covariant divergence of the Yang–Mills residual
  density equals `-ϱ D^νJ_ν` (Yang–Mills Bianchi identity); under `CurrentNoether` it is a linear
  combination of the matter residuals.

## The Standard-Model instance (bosonic sector)

* `VariationalBosonic SM` — the theory data are those of the Yang–Mills–Higgs Lagrangian
  `-¼⟨F, F⟩ - ⟨DH, DH⟩ - λ(⟨H, H⟩ - v²)²`: a bilinear **moment map** `μ : V × V → 𝔤`
  (alternating, gauge equivariant), the current `J_ν = 2μ(H, D_νH)` and the Higgs source
  `S_H = 2λ(⟨H, H⟩ - v²)H`; the current and source do not depend on the spinors (no Yukawa/Dirac
  current: the library's co-spinor model has no spinor pairing `S' × S → 𝔤`, disclosed).
* **`currentNoether_of_variational`** — such data satisfy `CurrentNoether` with
  `ϱ D^νJ_ν = 2ϱ μ(H, r_H)`.
* `adjSM` — the concrete `gl(m)` Yang–Mills–adjoint-Higgs model with the trace forms, the moment
  map `μ(u, w) = [u, w]` and the Mexican-hat potential; `adjSM_variational`,
  `adjSM_currentNoether`; also `trivSMM` (flat-vacuum data).
* `not_currentNoether_badSM` — the obstruction data `GenConstraintObs.badSM` (non-conserved charge
  density) violate `CurrentNoether`: the hypothesis is not vacuous and is exactly what fails there.

Disclosure: the library's gauge algebra is `MatLie m = gl(m, ℝ)` with arbitrary `gl(m)`-valued
potentials; invariant forms for all of `gl(m)` exclude a fundamental (doublet) Higgs, so the
concrete instance is the adjoint Higgs; the general statement `currentNoether_of_variational`
holds for every Lie module with an equivariant alternating moment map.
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenNoether

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState JetCurve

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Index algebra -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A double sum of an antisymmetric family vanishes. -/
theorem sum_sum_eq_zero_of_anti {M : Type*} [AddCommGroup M] [Module ℝ M] (X : n → n → M)
    (h : ∀ μ ν, X ν μ = -X μ ν) : ∑ μ, ∑ ν, X μ ν = 0 := by
  have h1 : ∑ μ, ∑ ν, X μ ν = ∑ μ, ∑ ν, X ν μ := Finset.sum_comm
  have h2 : ∑ μ, ∑ ν, X ν μ = -∑ μ, ∑ ν, X μ ν := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ν _ => h μ ν
  have h3 : (2 : ℝ) • ∑ μ, ∑ ν, X μ ν = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    rw [h2, neg_add_cancel]
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

/-- A double sum of a symmetric coefficient against an antisymmetric family vanishes. -/
theorem sum_sym_anti_eq_zero {M : Type*} [AddCommGroup M] [Module ℝ M] (c : n → n → ℝ)
    (X : n → n → M) (hc : ∀ μ ν, c ν μ = c μ ν) (hX : ∀ μ ν, X ν μ = -X μ ν) :
    ∑ μ, ∑ ν, c μ ν • X μ ν = 0 :=
  sum_sum_eq_zero_of_anti _ fun μ ν => by rw [hc, hX, smul_neg]

/-- Symmetry of the Christoffel symbols in the lower indices. -/
theorem chr_symm (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hdg : ∀ α a b, dg α a b = dg α b a)
    (l μ ν : n) : chr gi dg l ν μ = chr gi dg l μ ν := by
  unfold chr
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hdg σ ν μ]
  ring

/-- `Γ^λ{}_{λν} = ½ g^{ab}∂_νg_{ba}` (the trace of the Christoffel symbols). -/
theorem chr_trace (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (ν : n) : ∑ l, chr gi dg l l ν = (1 / 2) * ∑ a, ∑ b, gi a b * dg ν b a := by
  unfold chr
  rw [← Finset.mul_sum]
  congr 1
  have e1 : ∑ l, ∑ σ, gi l σ * dg l σ ν = ∑ l, ∑ σ, gi l σ * dg σ l ν := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hgi]
  have e2 : ∑ l, ∑ σ, gi l σ * (dg l σ ν + dg ν σ l - dg σ l ν) =
      (∑ l, ∑ σ, gi l σ * dg l σ ν) + (∑ l, ∑ σ, gi l σ * dg ν σ l) -
        ∑ l, ∑ σ, gi l σ * dg σ l ν := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e2, e1]
  ring

/-- **Metric compatibility of the inverse metric**:
`∂_αg^{lσ} = -Γ^l{}_{αc}g^{cσ} - Γ^σ{}_{αc}g^{lc}` (`dginv`). -/
theorem dginv_eq_chr (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α a b, dg α a b = dg α b a) (α l σ : n) :
    dginv gi dg α l σ = -∑ c, (chr gi dg l α c * gi c σ + chr gi dg σ α c * gi l c) := by
  unfold dginv chr
  rw [Finset.sum_add_distrib]
  have e2 : ∑ c, (1 / 2) * (∑ k, gi σ k * (dg α k c + dg c k α - dg k α c)) * gi l c =
      ∑ k, (1 / 2) * (∑ c, gi l k * (dg α k c + dg k c α - dg c α k) * gi c σ) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hgi σ k, hdg α k c]
    ring
  have e1 : ∑ c, (1 / 2) * (∑ k, gi l k * (dg α k c + dg c k α - dg k α c)) * gi c σ =
      ∑ k, (1 / 2) * (∑ c, gi l k * (dg α k c + dg c k α - dg k α c) * gi c σ) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  have : ∀ c, gi l k * (dg α k c + dg c k α - dg k α c) * gi c σ +
      gi l k * (dg α k c + dg k c α - dg c α k) * gi c σ = 2 * (gi l k * dg α k c * gi c σ) := by
    intro c
    rw [hdg c k α, hdg k c α]
    ring
  simp only [this, ← Finset.mul_sum]
  ring

/-- **The coefficient identity of the density divergence**:
`Σ_ν (Γ^λ{}_{λν} g^{νl} + ∂_νg^{νl}) = -g^{νρ}Γ^l{}_{ρν}`. -/
theorem density_coeff (gi : n → n → ℝ) (dg : n → n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a)
    (hdg : ∀ α a b, dg α a b = dg α b a) (l : n) :
    ∑ ν, ((∑ k, chr gi dg k k ν) * gi ν l + dginv gi dg ν ν l) =
      -∑ ν, ∑ ρ, gi ν ρ * chr gi dg l ρ ν := by
  simp only [chr_trace gi dg hgi]
  unfold dginv chr
  -- the three sums of the right-hand side
  set P := ∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg ρ σ ν with hP
  set R := ∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg σ ρ ν with hR
  have hrhs : ∑ ν, ∑ ρ, gi ν ρ * ((1 / 2) * ∑ σ, gi l σ * (dg ρ σ ν + dg ν σ ρ - dg σ ρ ν)) =
      P - (1 / 2) * R := by
    have hQ : ∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg ν σ ρ = P := by
      rw [hP, Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun σ _ => by rw [hgi]
    have : ∑ ν, ∑ ρ, gi ν ρ * ((1 / 2) * ∑ σ, gi l σ * (dg ρ σ ν + dg ν σ ρ - dg σ ρ ν)) =
        (1 / 2) * ((∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg ρ σ ν) +
          (∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg ν σ ρ) -
          ∑ ν, ∑ ρ, ∑ σ, gi ν ρ * gi l σ * dg σ ρ ν) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
        Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [this, hQ]
    ring
  rw [hrhs]
  have hL1 : ∑ ν, (1 / 2) * (∑ a, ∑ b, gi a b * dg ν b a) * gi ν l = (1 / 2) * R := by
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- reorder `ν a b` to `a b ν`
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [hgi ν l]
    ring
  have hL2 : ∑ ν, -∑ a, ∑ b, gi ν a * dg ν a b * gi b l = -P := by
    rw [hP, Finset.sum_neg_distrib]
    congr 1
    -- `Σ_ν Σ_a Σ_b g^{νa}∂_νg_{ab}g^{bl}` with `(ν, a, b) ↦ (ρ, ν, σ)`
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [hgi ν a, hgi b l, hdg ν a b]
    ring
  rw [Finset.sum_add_distrib, hL1, hL2]
  ring

/-- **The density divergence, algebraic form**: with `∂_νϱ = ϱΓ^k{}_{kν}` and `∂_νg^{νβ} = dginv`,
`Σ_ν(Γ^k{}_{kν} g^{νβ}w_β + ∂_νg^{νβ}w_β + g^{νβ}∂_νw_β) = g^{νρ}(∂_ρw_ν - Γ^l{}_{ρν}w_l)`. -/
theorem div_alg {M : Type*} [AddCommGroup M] [Module ℝ M] (gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α a b, dg α a b = dg α b a) (w : n → M)
    (dw : n → n → M) :
    ∑ ν, ((∑ k, chr gi dg k k ν) • ∑ β, gi ν β • w β +
        ∑ β, (dginv gi dg ν ν β • w β + gi ν β • dw ν β)) =
      ∑ ν, ∑ r, gi ν r • (dw r ν - ∑ l, chr gi dg l r ν • w l) := by
  have hL : ∑ ν, ((∑ k, chr gi dg k k ν) • ∑ β, gi ν β • w β +
        ∑ β, (dginv gi dg ν ν β • w β + gi ν β • dw ν β)) =
      ∑ β, (∑ ν, ((∑ k, chr gi dg k k ν) * gi ν β + dginv gi dg ν ν β)) • w β +
        ∑ ν, ∑ β, gi ν β • dw ν β := by
    have : ∀ ν, (∑ k, chr gi dg k k ν) • ∑ β, gi ν β • w β +
        ∑ β, (dginv gi dg ν ν β • w β + gi ν β • dw ν β) =
        ∑ β, ((∑ k, chr gi dg k k ν) * gi ν β + dginv gi dg ν ν β) • w β +
          ∑ β, gi ν β • dw ν β := by
      intro ν
      rw [Finset.smul_sum, Finset.sum_add_distrib, ← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [add_smul, smul_smul]
    rw [Finset.sum_congr rfl fun ν _ => this ν, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_smul]
  have hR : ∑ ν, ∑ r, gi ν r • (dw r ν - ∑ l, chr gi dg l r ν • w l) =
      ∑ ν, ∑ r, gi ν r • dw r ν -
        ∑ l, (∑ ν, ∑ r, gi ν r * chr gi dg l r ν) • w l := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [eq_comm]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_comm
  rw [hL, hR]
  have hc : ∀ β, (∑ ν, ((∑ k, chr gi dg k k ν) * gi ν β + dginv gi dg ν ν β)) • w β =
      -((∑ ν, ∑ r, gi ν r * chr gi dg β r ν) • w β) := by
    intro β
    rw [density_coeff gi dg hgi hdg β, neg_smul]
  have hd : ∑ ν, ∑ β, gi ν β • dw ν β = ∑ ν, ∑ r, gi ν r • dw r ν := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hgi]
  rw [Finset.sum_congr rfl fun β _ => hc β, hd, Finset.sum_neg_distrib]
  abel

/-- **The Yang–Mills divergence as a density divergence, algebraic form**: for an antisymmetric
`F_{μβ}` with derivative jets `dF r μ β = ∂_rF_{μβ}` and `W^{(ν)}_μ = g^{νβ}F_{μβ}`,
`g^{μr}(∂_rW^{(ν)}_μ - Γ^l{}_{rμ}W^{(ν)}_l) = g^{νβ}g^{μr}(∂_rF_{μβ} - Γ^l{}_{rμ}F_{lβ} -
Γ^l{}_{rβ}F_{μl})` (metric compatibility `dginv_eq_chr`; the `Γ^ν` term cancels by symmetry
against antisymmetry). -/
theorem ym_alg {M : Type*} [AddCommGroup M] [Module ℝ M] (gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hdg : ∀ α a b, dg α a b = dg α b a) (F : n → n → M)
    (hF : ∀ a b, F b a = -F a b) (dF : n → n → n → M) (ν : n) :
    ∑ μ, ∑ r, gi μ r • (∑ β, (dginv gi dg r ν β • F μ β + gi ν β • dF r μ β) -
        ∑ l, chr gi dg l r μ • ∑ β, gi ν β • F l β) =
      ∑ β, gi ν β • ∑ μ, ∑ r, gi μ r • (dF r μ β -
        ∑ l, (chr gi dg l r μ • F l β + chr gi dg l r β • F μ l)) := by
  -- expand everything into quadruple sums
  have hexp : ∀ μ r, gi μ r • (∑ β, (dginv gi dg r ν β • F μ β + gi ν β • dF r μ β) -
        ∑ l, chr gi dg l r μ • ∑ β, gi ν β • F l β) =
      -(∑ β, ∑ c, (gi μ r * chr gi dg ν r c * gi c β) • F μ β) -
        (∑ β, ∑ c, (gi μ r * chr gi dg β r c * gi ν c) • F μ β) +
        ∑ β, (gi μ r * gi ν β) • dF r μ β -
        ∑ l, ∑ β, (gi μ r * chr gi dg l r μ * gi ν β) • F l β := by
    intro μ r
    simp only [dginv_eq_chr gi dg hgi hdg, smul_sub, Finset.smul_sum, smul_add, smul_smul,
      Finset.sum_add_distrib, neg_smul, Finset.sum_neg_distrib, add_smul, Finset.sum_smul,
      smul_neg]
    simp only [mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun r _ => hexp μ r]
  -- the `Γ^ν` term vanishes
  have hz : ∑ μ, ∑ r, ∑ β, ∑ c, (gi μ r * chr gi dg ν r c * gi c β) • F μ β = 0 := by
    have e : ∑ μ, ∑ r, ∑ β, ∑ c, (gi μ r * chr gi dg ν r c * gi c β) • F μ β =
        ∑ r, ∑ c, chr gi dg ν r c • ∑ μ, ∑ β, (gi μ r * gi c β) • F μ β := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => ?_
      ring_nf
    rw [e]
    refine sum_sym_anti_eq_zero _ _ (fun r c => chr_symm gi dg hdg ν r c) fun r c => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hF μ β, smul_neg, neg_neg, hgi μ c, hgi r β, mul_comm]
  have h3 : ∑ μ, ∑ r, ∑ β, (gi μ r * gi ν β) • dF r μ β =
      ∑ β, ∑ μ, ∑ r, (gi ν β * gi μ r) • dF r μ β := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun r _ => by rw [mul_comm]
  have h4 : ∑ μ, ∑ r, ∑ l, ∑ β, (gi μ r * chr gi dg l r μ * gi ν β) • F l β =
      ∑ β, ∑ μ, ∑ r, ∑ l, (gi ν β * (gi μ r * chr gi dg l r μ)) • F l β := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm,
      Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => by ring_nf
  have h2 : ∑ μ, ∑ r, ∑ β, ∑ c, (gi μ r * chr gi dg β r c * gi ν c) • F μ β =
      ∑ c, ∑ μ, ∑ r, ∑ β, (gi ν c * (gi μ r * chr gi dg β r c)) • F μ β := by
    rw [Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm,
      Finset.sum_congr rfl fun μ _ => Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun β _ => by ring_nf
  have hL : ∑ μ, ∑ r, (-(∑ β, ∑ c, (gi μ r * chr gi dg ν r c * gi c β) • F μ β) -
        (∑ β, ∑ c, (gi μ r * chr gi dg β r c * gi ν c) • F μ β) +
        ∑ β, (gi μ r * gi ν β) • dF r μ β -
        ∑ l, ∑ β, (gi μ r * chr gi dg l r μ * gi ν β) • F l β) =
      -(∑ μ, ∑ r, ∑ β, ∑ c, (gi μ r * chr gi dg ν r c * gi c β) • F μ β) -
        (∑ μ, ∑ r, ∑ β, ∑ c, (gi μ r * chr gi dg β r c * gi ν c) • F μ β) +
        (∑ μ, ∑ r, ∑ β, (gi μ r * gi ν β) • dF r μ β) -
        ∑ μ, ∑ r, ∑ l, ∑ β, (gi μ r * chr gi dg l r μ * gi ν β) • F l β := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hR : ∑ β, gi ν β • ∑ μ, ∑ r, gi μ r • (dF r μ β -
        ∑ l, (chr gi dg l r μ • F l β + chr gi dg l r β • F μ l)) =
      (∑ β, ∑ μ, ∑ r, (gi ν β * gi μ r) • dF r μ β) -
        (∑ β, ∑ μ, ∑ r, ∑ l, (gi ν β * (gi μ r * chr gi dg l r μ)) • F l β) -
        ∑ β, ∑ μ, ∑ r, ∑ l, (gi ν β * (gi μ r * chr gi dg l r β)) • F μ l := by
    simp only [smul_sub, smul_add, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    abel
  rw [hL, hR, hz, h2, h3, h4]
  abel

/-- Moving the last of four summation indices to the front. -/
theorem sum4_swap {M : Type*} [AddCommMonoid M] (f : n → n → n → n → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]

/-- **`[F_{μν}, 𝔉^{μν}] = 0`** for `𝔉^{μν} = ϱ g^{μα}g^{νβ}F_{αβ}` (symmetric weight against the
antisymmetric bracket). -/
theorem sum_lie_density_eq_zero {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (gi : n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (ρ : ℝ) (F : n → n → 𝔤) :
    ∑ μ, ∑ ν, ⁅F μ ν, ρ • ∑ α, ∑ β, (gi μ α * gi ν β) • F α β⁆ = 0 := by
  set f : n → n → n → n → 𝔤 := fun μ ν α β => (ρ * (gi μ α * gi ν β)) • ⁅F μ ν, F α β⁆ with hf
  have e : ∑ μ, ∑ ν, ⁅F μ ν, ρ • ∑ α, ∑ β, (gi μ α * gi ν β) • F α β⁆ =
      ∑ μ, ∑ ν, ∑ α, ∑ β, f μ ν α β := by
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [lie_smul, lie_sum, Finset.smul_sum, smul_smul, hf]
  rw [e]
  have hanti : ∀ μ ν α β, f α β μ ν = -f μ ν α β := by
    intro μ ν α β
    simp only [hf]
    rw [← lie_skew, smul_neg, hgi α μ, hgi β ν]
  have h2 : (2 : ℝ) • ∑ μ, ∑ ν, ∑ α, ∑ β, f μ ν α β = 0 := by
    rw [two_smul]
    nth_rewrite 2 [sum4_swap]
    have : ∑ c, ∑ d, ∑ a, ∑ b, f a b c d = -∑ c, ∑ d, ∑ a, ∑ b, f c d a b := by
      simp only [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
          rw [← hanti c d a b]
    rw [this, add_neg_cancel]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The Yang–Mills Bianchi algebra**: for an antisymmetric `𝔉^{μν}`,
`Σ_{μν}([∂_νA_μ, 𝔉^{μν}] + [A_ν, [A_μ, 𝔉^{μν}]]) = -½ Σ_{μν}[F_{μν}, 𝔉^{μν}]`
(Jacobi identity), `F = ∂A - ∂A + [A, A]`. -/
theorem bianchi_alg {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (A : Fin 4 → 𝔤)
    (dA : Fin 4 → Fin 4 → 𝔤) (𝔉 : Fin 4 → Fin 4 → 𝔤) (h𝔉 : ∀ μ ν, 𝔉 ν μ = -𝔉 μ ν) :
    ∑ μ, ∑ ν, (⁅dA ν μ, 𝔉 μ ν⁆ + ⁅A ν, ⁅A μ, 𝔉 μ ν⁆⁆) =
      -((1 / 2 : ℝ) • ∑ μ, ∑ ν, ⁅fieldStrength A dA μ ν, 𝔉 μ ν⁆) := by
  set K : Fin 4 → Fin 4 → 𝔤 := fun μ ν => ⁅dA ν μ, 𝔉 μ ν⁆ + ⁅A ν, ⁅A μ, 𝔉 μ ν⁆⁆ +
    (1 / 2 : ℝ) • ⁅fieldStrength A dA μ ν, 𝔉 μ ν⁆ with hK
  have hKa : ∀ μ ν, K ν μ = -K μ ν := by
    intro μ ν
    simp only [hK, h𝔉 μ ν, fieldStrength, lie_neg, add_lie, sub_lie, lie_lie]
    module
  have h0 := sum_sum_eq_zero_of_anti K hKa
  simp only [hK, Finset.sum_add_distrib, ← Finset.smul_sum] at h0
  rw [eq_neg_iff_add_eq_zero, ← h0]
  simp only [Finset.sum_add_distrib]

end Algebra

/-! ### Field calculus along a smooth tuple -/

section Fields

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (z : Tuple m V S S')

/-- `det g` along the tuple. -/
def detF (y : ST 3) : ℝ := (Matrix.of (z.g y)).det

/-- **The volume density** `ϱ = √|det g|`. -/
def rho (y : ST 3) : ℝ := Real.sqrt |detF z y|

theorem rho_pos (y : ST 3) : 0 < rho z y :=
  Real.sqrt_pos.2 (abs_pos.2 (z.det_ne y))

theorem contDiff_detF : ContDiff ℝ ∞ (detF z) := by
  have h := z.contDiff_gc
  unfold detF
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem contDiff_rho : ContDiff ℝ ∞ (rho z) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  have hd := (contDiff_detF z).contDiffAt (x := y)
  have hne := z.det_ne y
  have habs : ContDiffAt ℝ ∞ (fun y => |detF z y|) y := by
    have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => |t|) (detF z y) := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · refine (contDiffAt_id.neg).congr_of_eventuallyEq ?_
        filter_upwards [gt_mem_nhds hneg] with t ht
        simp [abs_of_neg ht]
      · refine contDiffAt_id.congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds hpos] with t ht
        simp [abs_of_pos ht]
    exact h2.comp y hd
  exact habs.sqrt (abs_pos.2 hne).ne'

theorem adjugate_eq_det_smul_inv {A : Matrix (Fin 4) (Fin 4) ℝ} (h : A.det ≠ 0) :
    A.adjugate = A.det • A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ h, one_smul]

/-- **Jacobi's formula** along a line: `∂_δ det g = det g · g^{ab}∂_δg_{ba}`. -/
theorem line_detF (x : ST 3) (δ : Fin 4) :
    HasDerivAt (fun s : ℝ => detF z (x + s • ev δ))
      (detF z x * ∑ a, ∑ b, z.gi x a b * z.dg x δ b a) 0 := by
  have h := RenewalGeometry.hasDerivAt_det (𝕜 := ℝ)
    (U := fun s : ℝ => Matrix.of (z.g (x + s • ev δ))) (V := Matrix.of (z.dg x δ)) (t := 0)
    (fun i j => by simpa using z.line_g x δ i j)
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero]
  rw [adjugate_eq_det_smul_inv (z.det_ne x), Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  unfold detF
  congr 1

/-- **`∂_δϱ = ϱ Γ^k{}_{kδ}`** along a line. -/
theorem line_rho (x : ST 3) (δ : Fin 4) :
    HasDerivAt (fun s : ℝ => rho z (x + s • ev δ))
      (rho z x * ∑ k, chr (z.gi x) (z.dg x) k k δ) 0 := by
  have e0 : x + (0 : ℝ) • ev δ = x := by simp
  have hne : detF z (x + (0 : ℝ) • ev δ) ≠ 0 := by rw [e0]; exact z.det_ne x
  have h1 := (hasDerivAt_abs hne).comp 0 (line_detF z x δ)
  have h2 := h1.sqrt (by simp only [Function.comp_apply]; exact (abs_pos.2 hne).ne')
  refine h2.congr_deriv ?_
  rw [chr_trace _ _ (fun a b => z.gi_symm x a b)]
  simp only [Function.comp_apply, e0]
  have hd := z.det_ne x
  set T := ∑ a, ∑ b, z.gi x a b * z.dg x δ b a
  have hsq : Real.sqrt |detF z x| ^ 2 = |detF z x| := Real.sq_sqrt (abs_nonneg _)
  have hpos : 0 < Real.sqrt |detF z x| := Real.sqrt_pos.2 (abs_pos.2 hd)
  have hsign : (SignType.sign (detF z x) : ℝ) * detF z x = |detF z x| := sign_mul_self _
  unfold rho
  field_simp
  rw [hsign]
  linear_combination (-T) * hsq

/-- **The divergence of a vector density** (`ϱ ∇_νw^ν = ∂_ν(ϱ w^ν)`): for every covector field `w`
differentiable at `x` (values in any normed space),
`Σ_ν ∂_ν(ϱ g^{νβ}w_β) = ϱ g^{νr}(∂_rw_ν - Γ^l{}_{rν}w_l)` at `x`. -/
theorem div_density {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ST 3 → Fin 4 → E)
    (x : ST 3) (hw : DifferentiableAt ℝ w x) :
    ∑ ν, pd (fun y => rho z y • ∑ β, z.gi y ν β • w y β) ν x =
      rho z x • ∑ ν, ∑ r, z.gi x ν r •
        (pd w r x ν - ∑ l, chr (z.gi x) (z.dg x) l r ν • w x l) := by
  have hpd : ∀ ν, pd (fun y => rho z y • ∑ β, z.gi y ν β • w y β) ν x =
      rho z x • ((∑ k, chr (z.gi x) (z.dg x) k k ν) • ∑ β, z.gi x ν β • w x β +
        ∑ β, (dginv (z.gi x) (z.dg x) ν ν β • w x β + z.gi x ν β • pd w ν x β)) := by
    intro ν
    have hdiff : DifferentiableAt ℝ (fun y => rho z y • ∑ β, z.gi y ν β • w y β) x := by
      refine ((contDiff_rho z).differentiable (by simp) x).smul
        (DifferentiableAt.fun_sum fun β _ => ?_)
      exact ((z.contDiff_gi ν β).differentiable (by simp) x).smul (differentiableAt_pi.1 hw β)
    refine pd_eq_of_line hdiff ?_
    have h2 : HasDerivAt (fun s : ℝ => ∑ β, z.gi (x + s • ev ν) ν β • w (x + s • ev ν) β)
        (∑ β, (dginv (z.gi x) (z.dg x) ν ν β • w x β + z.gi x ν β • pd w ν x β)) 0 := by
      refine HasDerivAt.fun_sum fun β _ => ?_
      have := (z.line_gi x ν ν β).smul (hasDerivAt_line0_apply hw ν β)
      simp only [zero_smul, add_zero] at this
      exact this.congr_deriv (add_comm _ _)
    have := (line_rho z x ν).smul h2
    simp only [zero_smul, add_zero] at this
    refine this.congr_deriv ?_
    rw [smul_add, mul_smul, add_comm]
  rw [Finset.sum_congr rfl fun ν _ => hpd ν, ← Finset.smul_sum,
    div_alg _ _ (fun a b => z.gi_symm x a b) (fun α a b => z.dg_symm x α a b) (w x)
      (fun r ν => pd w r x ν)]

/-- The field strength of the tuple. -/
def Fld (y : ST 3) (μ ν : Fin 4) : MatLie m := Fm (z.jet y).A (z.jet y).dA μ ν

/-- **The Yang–Mills density** `𝔉^{μν} = ϱ g^{μα}g^{νβ}F_{αβ}`. -/
def dens (y : ST 3) (μ ν : Fin 4) : MatLie m :=
  rho z y • ∑ α, ∑ β, (z.gi y μ α * z.gi y ν β) • Fld z y α β

theorem dens_eq (y : ST 3) (μ ν : Fin 4) :
    dens z y μ ν = rho z y • ∑ α, z.gi y μ α • ∑ β, z.gi y ν β • Fld z y α β := by
  unfold dens
  simp only [Finset.smul_sum, smul_smul]

theorem dens_anti (y : ST 3) (μ ν : Fin 4) : dens z y ν μ = -dens z y μ ν := by
  unfold dens
  rw [← smul_neg, ← Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  unfold Fld
  rw [Fm_anti, smul_neg, mul_comm]

theorem contDiff_Fld (μ ν : Fin 4) : ContDiff ℝ ∞ (fun y => Fld z y μ ν) :=
  ActualJetState.contDiff_Fm z μ ν

theorem contDiff_dens : ContDiff ℝ ∞ (dens z) := by
  refine contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_
  have h1 := contDiff_rho z
  have h2 := z.contDiff_gi
  have h3 := contDiff_Fld z
  unfold dens
  fun_prop

/-- The bracket term of the density divergence (algebra). -/
theorem lie_dens_alg {n : Type*} [Fintype n] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (gi : n → n → ℝ) (hgi : ∀ a b, gi a b = gi b a) (ρ : ℝ) (A : n → 𝔤) (F : n → n → 𝔤)
    (ν : n) :
    ∑ μ, ⁅A μ, ρ • ∑ α, ∑ β, (gi μ α * gi ν β) • F α β⁆ =
      ρ • ∑ β, gi ν β • ∑ μ, ∑ r, gi μ r • ⁅A r, F μ β⁆ := by
  simp only [lie_smul, lie_sum]
  rw [← Finset.smul_sum]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  -- LHS: `Σ_μ Σ_α Σ_β`, RHS: `Σ_β Σ_μ Σ_r` with `(μ, α) ↦ (r, μ)`
  rw [eq_comm, Finset.sum_congr rfl fun b _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hgi a c, mul_comm]

/-- **The Yang–Mills divergence as a density divergence**:
`∂_μ𝔉^{μν} + [A_μ, 𝔉^{μν}] = ϱ g^{νβ}(∇^μF_{μβ} + [A^μ, F_{μβ}])` (`ymDiv`, Levi-Civita
connection of the tuple's metric). -/
theorem ymDensity_eq (x : ST 3) (ν : Fin 4) :
    ∑ μ, (pd (fun y => dens z y μ ν) μ x + ⁅z.A x μ, dens z x μ ν⁆) =
      rho z x • ∑ β, z.gi x ν β • ymDiv (z.jet x).A (z.jet x).dA (z.jet x).ddA (z.gi x)
        (chr (z.gi x) (z.dg x)) β := by
  set W : ST 3 → Fin 4 → MatLie m := fun y α => ∑ β, z.gi y ν β • Fld z y α β with hW
  have hWs : ContDiff ℝ ∞ W := by
    refine contDiff_pi.2 fun α => ?_
    have h2 := z.contDiff_gi
    have h3 := contDiff_Fld z
    simp only [hW]
    fun_prop
  have hfun : ∀ μ, (fun y => dens z y μ ν) = fun y => rho z y • ∑ α, z.gi y μ α • W y α :=
    fun μ => funext fun y => dens_eq z y μ ν
  have hpdW : ∀ r μ, pd W r x μ = ∑ β, (dginv (z.gi x) (z.dg x) r ν β • Fld z x μ β +
      z.gi x ν β • dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA r μ β) := by
    intro r μ
    rw [← pd_apply ((hWs.differentiable (by simp)) x) r μ]
    have hd : DifferentiableAt ℝ (fun y => W y μ) x :=
      ((contDiff_pi.1 hWs μ).differentiable (by simp)) x
    refine pd_eq_of_line hd ?_
    refine HasDerivAt.fun_sum fun β _ => ?_
    have := (z.line_gi x r ν β).smul (z.line_Fm x r μ β)
    simp only [zero_smul, add_zero] at this
    exact this.congr_deriv (add_comm _ _)
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl fun μ _ => by rw [hfun μ],
    div_density z W x ((hWs.differentiable (by simp)) x)]
  simp only [hpdW]
  simp only [hW]
  rw [ym_alg _ _ (fun a b => z.gi_symm x a b) (fun α a b => z.dg_symm x α a b) (Fld z x)
    (fun a b => Fm_anti _ _ a b) (fun r μ β => dFm (z.jet x).A (z.jet x).dA (z.jet x).ddA r μ β) ν]
  unfold dens
  rw [lie_dens_alg _ (fun a b => z.gi_symm x a b), ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  unfold ymDiv
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← smul_add]
  rfl

/-- **The double covariant divergence of an antisymmetric density** (field level): for smooth `A`
and a smooth antisymmetric `𝔉^{μν}`, with `D^ν = ∂_μ𝔉^{μν} + [A_μ, 𝔉^{μν}]`,
`∂_νD^ν + [A_ν, D^ν] = Σ_{μν}([∂_νA_μ, 𝔉^{μν}] + [A_ν, [A_μ, 𝔉^{μν}]])`
(`∂_ν∂_μ𝔉^{μν} = 0` and the cross terms cancel by antisymmetry). -/
theorem double_div (𝔉 : ST 3 → Fin 4 → Fin 4 → MatLie m) (h𝔉 : ContDiff ℝ ∞ 𝔉)
    (hanti : ∀ y μ ν, 𝔉 y ν μ = -𝔉 y μ ν) (A : ST 3 → Fin 4 → MatLie m) (hA : ContDiff ℝ ∞ A)
    (x : ST 3) :
    ∑ ν, (pd (fun y => ∑ μ, (pd (fun y => 𝔉 y μ ν) μ y + ⁅A y μ, 𝔉 y μ ν⁆)) ν x +
        ⁅A x ν, ∑ μ, (pd (fun y => 𝔉 y μ ν) μ x + ⁅A x μ, 𝔉 x μ ν⁆)⁆) =
      ∑ μ, ∑ ν, (⁅pd A ν x μ, 𝔉 x μ ν⁆ + ⁅A x ν, ⁅A x μ, 𝔉 x μ ν⁆⁆) := by
  have hc : ∀ μ ν, ContDiff ℝ ∞ (fun y => 𝔉 y μ ν) := fun μ ν =>
    contDiff_pi.1 (contDiff_pi.1 h𝔉 μ) ν
  have hAc : ∀ μ, ContDiff ℝ ∞ (fun y => A y μ) := fun μ => contDiff_pi.1 hA μ
  have hpd : ∀ ν, pd (fun y => ∑ μ, (pd (fun y => 𝔉 y μ ν) μ y + ⁅A y μ, 𝔉 y μ ν⁆)) ν x =
      ∑ μ, (pd (pd (fun y => 𝔉 y μ ν) μ) ν x +
        (⁅pd A ν x μ, 𝔉 x μ ν⁆ + ⁅A x μ, pd (fun y => 𝔉 y μ ν) ν x⁆)) := by
    intro ν
    have hdiff : DifferentiableAt ℝ
        (fun y => ∑ μ, (pd (fun y => 𝔉 y μ ν) μ y + ⁅A y μ, 𝔉 y μ ν⁆)) x := by
      refine DifferentiableAt.fun_sum fun μ _ => ?_
      refine (((contDiff_pd (hc μ ν) μ).differentiable (by simp)) x).add ?_
      have h1 := (hAc μ).contDiffAt (x := x)
      have h2 := (hc μ ν).contDiffAt (x := x)
      exact (ContDiffAt.lie_mat h1 h2).differentiableAt (by simp)
    refine pd_eq_of_line hdiff ?_
    refine HasDerivAt.fun_sum fun μ _ => ?_
    have h1 := hasDerivAt_line0 (((contDiff_pd (hc μ ν) μ).differentiable (by simp)) x) ν
    have h2 := hasDerivAt_lie (hasDerivAt_line0_apply ((hA.differentiable (by simp)) x) ν μ)
      (hasDerivAt_line0 (((hc μ ν).differentiable (by simp)) x) ν)
    simp only [zero_smul, add_zero] at h2
    exact h1.add h2
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl fun ν _ => hpd ν]
  simp only [Finset.sum_add_distrib, lie_sum, lie_add]
  -- second derivatives cancel
  have hss : ∑ ν, ∑ μ, pd (pd (fun y => 𝔉 y μ ν) μ) ν x = 0 := by
    rw [Finset.sum_comm]
    refine sum_sum_eq_zero_of_anti _ fun μ ν => ?_
    have hf : (fun y => 𝔉 y ν μ) = -(fun y => 𝔉 y μ ν) := funext fun y => hanti y μ ν
    have hneg : ∀ (f : ST 3 → MatLie m) (i : Fin 4), pd (-f) i = -pd f i := by
      intro f i
      funext y
      unfold SobolevOpen.pd
      rw [fderiv_neg]
      rfl
    rw [hf, hneg, hneg, Pi.neg_apply, pd_pd_comm' (hc μ ν) ν μ x]
  -- cross terms cancel
  have hcross : ∑ ν, ∑ μ, ⁅A x μ, pd (fun y => 𝔉 y μ ν) ν x⁆ +
      ∑ ν, ∑ μ, ⁅A x ν, pd (fun y => 𝔉 y μ ν) μ x⁆ = 0 := by
    rw [Finset.sum_comm (f := fun ν μ => ⁅A x ν, pd (fun y => 𝔉 y μ ν) μ x⁆),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun μ _ => ?_
    have hf : (fun y => 𝔉 y ν μ) = -(fun y => 𝔉 y μ ν) := funext fun y => hanti y μ ν
    have hneg : pd (-(fun y => 𝔉 y μ ν)) ν x = -pd (fun y => 𝔉 y μ ν) ν x := by
      unfold SobolevOpen.pd
      rw [fderiv_neg]
      rfl
    rw [hf, hneg, lie_neg, add_neg_cancel]
  have h1 : ∑ ν, ∑ μ, ⁅pd A ν x μ, 𝔉 x μ ν⁆ = ∑ μ, ∑ ν, ⁅pd A ν x μ, 𝔉 x μ ν⁆ :=
    Finset.sum_comm
  have h2 : ∑ ν, ∑ μ, ⁅A x ν, ⁅A x μ, 𝔉 x μ ν⁆⁆ = ∑ μ, ∑ ν, ⁅A x ν, ⁅A x μ, 𝔉 x μ ν⁆⁆ :=
    Finset.sum_comm
  rw [hss, ← h1, ← h2]
  set P := ∑ ν, ∑ μ, ⁅A x μ, pd (fun y => 𝔉 y μ ν) ν x⁆
  set Q := ∑ ν, ∑ μ, ⁅A x ν, pd (fun y => 𝔉 y μ ν) μ x⁆
  set R1 := ∑ ν, ∑ μ, ⁅pd A ν x μ, 𝔉 x μ ν⁆
  set R2 := ∑ ν, ∑ μ, ⁅A x ν, ⁅A x μ, 𝔉 x μ ν⁆⁆
  have : (0 : MatLie m) + (R1 + P) + (Q + R2) = R1 + R2 + (P + Q) := by abel
  rw [this, hcross, add_zero]

/-- The Yang–Mills divergence density `ϱ g^{νβ}(∇^μF_{μβ} + [A^μ, F_{μβ}])` of the tuple. -/
def ymDens (y : ST 3) (ν : Fin 4) : MatLie m :=
  rho z y • ∑ β, z.gi y ν β • ymDiv (z.jet y).A (z.jet y).dA (z.jet y).ddA (z.gi y)
    (chr (z.gi y) (z.dg y)) β

theorem ymDens_eq (ν : Fin 4) :
    (fun y => ymDens z y ν) =
      fun y => ∑ μ, (pd (fun y => dens z y μ ν) μ y + ⁅z.A y μ, dens z y μ ν⁆) :=
  funext fun y => (ymDensity_eq z y ν).symm

theorem contDiff_ymDens (ν : Fin 4) : ContDiff ℝ ∞ (fun y => ymDens z y ν) := by
  rw [ymDens_eq]
  have hc : ∀ μ ν, ContDiff ℝ ∞ (fun y => dens z y μ ν) := fun μ ν =>
    contDiff_pi.1 (contDiff_pi.1 (contDiff_dens z) μ) ν
  refine ContDiff.sum fun μ _ => (contDiff_pd (hc μ ν) μ).add ?_
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  have h1 := (Tuple.contDiff_vec z.A_smooth μ).contDiffAt (x := y)
  have h2 := (hc μ ν).contDiffAt (x := y)
  exact ContDiffAt.lie_mat h1 h2

/-- **The Yang–Mills Bianchi–Noether identity at field level**: for every smooth tuple, the gauge
covariant divergence of the Yang–Mills divergence density vanishes identically,
`∂_ν(ϱ g^{νβ}∇^μF_{μβ}) + [A_ν, ϱ g^{νβ}∇^μF_{μβ}] = 0`, i.e. `ϱ D^ν(∇^μF_{μν}) = 0`. -/
theorem ym_bianchi_density (x : ST 3) :
    ∑ ν, (pd (fun y => ymDens z y ν) ν x + ⁅z.A x ν, ymDens z x ν⁆) = 0 := by
  have hx : ∀ ν, ymDens z x ν =
      ∑ μ, (pd (fun y => dens z y μ ν) μ x + ⁅z.A x μ, dens z x μ ν⁆) :=
    fun ν => (ymDensity_eq z x ν).symm
  simp only [ymDens_eq z, hx]
  rw [double_div (dens z) (contDiff_dens z) (dens_anti z) z.A z.A_smooth x]
  have hb := bianchi_alg (z.A x) (fun γ μ => pd z.A γ x μ) (dens z x) (dens_anti z x)
  rw [hb, neg_eq_zero, smul_eq_zero]
  right
  exact sum_lie_density_eq_zero (z.gi x) (fun a b => z.gi_symm x a b) (rho z x) (Fld z x)

end Fields

/-! ### The gauge current and its Noether identity -/

section Current

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

/-- The covariant Higgs gradient field `D_μH = ∂_μH + A_μ·H`. -/
def DHf (y : ST 3) : Fin 4 → V := ActualJetGauge.DH (z.jet y).A (z.jet y).H (z.jet y).dH

/-- The gauge current `J_ν(g, H, DH, Ψ, Ψ̄)` of the theory data along the tuple. -/
def Jf (y : ST 3) : Fin 4 → MatLie m :=
  SM.Jcur (z.jet y).FJ.g (z.jet y).FJ.gi (z.jet y).H (DHf z y) (z.jet y).ψ (z.jet y).ψb

/-- The current density `ϱ g^{νβ}J_β`. -/
def densJ (y : ST 3) (ν : Fin 4) : MatLie m := rho z y • ∑ β, z.gi y ν β • Jf SM z y β

/-- **The covariant divergence of the current density**, `ϱ D^νJ_ν = ∂_ν(ϱ g^{νβ}J_β) +
[A_ν, ϱ g^{νβ}J_β]` (`divJ_eq`: Christoffel form). -/
def divJ (x : ST 3) : MatLie m :=
  ∑ ν, (pd (fun y => densJ SM z y ν) ν x + ⁅z.A x ν, densJ SM z x ν⁆)

/-- The Yang–Mills residual density `ϱ g^{νβ}r^A_β`. -/
def densR (y : ST 3) (ν : Fin 4) : MatLie m := rho z y • ∑ β, z.gi y ν β • (bosF SM z y).2.1 β

theorem densR_eq (y : ST 3) (ν : Fin 4) : densR SM z y ν = ymDens z y ν - densJ SM z y ν := by
  unfold densR ymDens densJ
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← smul_sub]
  rfl

theorem contDiff_densR (hS : SMSmooth SM) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => densR SM z y ν) := by
  have h1 := contDiff_rho z
  have h2 := z.contDiff_gi
  have h3 := fun β => ActualJetState.contDiff_rA SM z hS β
  show ContDiff ℝ ∞ (fun y => rho z y • ∑ β, z.gi y ν β • ((z.jet y).res SM).rA β)
  fun_prop

/-- The current density is smooth for smooth theory data. -/
theorem contDiff_densJ (hS : SMSmooth SM) (ν : Fin 4) :
    ContDiff ℝ ∞ (fun y => densJ SM z y ν) := by
  have : (fun y => densJ SM z y ν) = fun y => ymDens z y ν - densR SM z y ν :=
    funext fun y => by rw [densR_eq]; abel
  rw [this]
  exact (contDiff_ymDens z ν).sub (contDiff_densR SM z hS ν)

/-- **The divergence of the Yang–Mills residual** (Yang–Mills Bianchi identity): for every smooth
tuple and smooth theory data, `ϱ D^νr^A_ν = -ϱ D^νJ_ν`. -/
theorem div_rA (hS : SMSmooth SM) (x : ST 3) :
    ∑ ν, (pd (fun y => densR SM z y ν) ν x + ⁅z.A x ν, densR SM z x ν⁆) = -divJ SM z x := by
  have hpd : ∀ ν, pd (fun y => densR SM z y ν) ν x =
      pd (fun y => ymDens z y ν) ν x - pd (fun y => densJ SM z y ν) ν x := by
    intro ν
    have : (fun y => densR SM z y ν) = fun y => ymDens z y ν - densJ SM z y ν :=
      funext fun y => densR_eq SM z y ν
    rw [this]
    unfold SobolevOpen.pd
    rw [fderiv_fun_sub (((contDiff_ymDens z ν).differentiable (by simp)) x)
      (((contDiff_densJ SM z hS ν).differentiable (by simp)) x)]
    rfl
  have h0 := ym_bianchi_density z x
  unfold divJ
  rw [Finset.sum_congr rfl fun ν _ => by rw [hpd ν, densR_eq, lie_sub], ← sub_eq_zero]
  have : ∑ ν, (pd (fun y => ymDens z y ν) ν x - pd (fun y => densJ SM z y ν) ν x +
      (⁅z.A x ν, ymDens z x ν⁆ - ⁅z.A x ν, densJ SM z x ν⁆)) -
      -∑ ν, (pd (fun y => densJ SM z y ν) ν x + ⁅z.A x ν, densJ SM z x ν⁆) =
      ∑ ν, (pd (fun y => ymDens z y ν) ν x + ⁅z.A x ν, ymDens z x ν⁆) := by
    rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    abel
  rw [this, h0]

/-- **The current Noether identity as a hypothesis on the theory data**
(`lem:generated-physical-identification`, implicit in the manuscript): for every smooth field tuple
and every point, the covariant divergence of the gauge current is a linear combination of the
Higgs and Dirac residuals, `ϱ D^νJ_ν = ϱ K(g, g⁻¹, H, DH, Ψ, Ψ̄)(r_H, r_D, r̄_D)`, with coefficients
`K` depending only on the undifferentiated fields and `DH` (as for the Euler–Lagrange currents of
a gauge-invariant Lagrangian). -/
structure CurrentNoether where
  /-- the coefficients of the residual combination -/
  K : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → V → (Fin 4 → V) → S → S' →
    (V × (S × S')) →ₗ[ℝ] MatLie m
  /-- the Noether identity -/
  div_eq : ∀ (z : Tuple m V S S') (x : ST 3), divJ SM z x =
    rho z x • K (z.g x) (z.gi x) (z.H x) (DHf z x) (z.ψ x) (z.ψb x)
      ((bosF SM z x).2.2, dirF SM z x)

variable {SM}

/-- Under the current Noether identity the current is covariantly conserved wherever the Higgs and
Dirac equations hold. -/
theorem divJ_eq_zero (hN : CurrentNoether SM) {x : ST 3} (hH : (bosF SM z x).2.2 = 0)
    (hD : dirF SM z x = 0) : divJ SM z x = 0 := by
  rw [hN.div_eq, hH, hD]
  have : ((0 : V), (0 : S × S')) = 0 := rfl
  rw [this, map_zero, smul_zero]

/-- **The Yang–Mills residual is covariantly conserved wherever the Higgs and Dirac equations hold**
(`ϱ D^νr^A_ν = 0`), for theory data satisfying the current Noether identity. -/
theorem div_rA_eq_zero (hN : CurrentNoether SM) (hS : SMSmooth SM) {x : ST 3}
    (hH : (bosF SM z x).2.2 = 0) (hD : dirF SM z x = 0) :
    ∑ ν, (pd (fun y => densR SM z y ν) ν x + ⁅z.A x ν, densR SM z x ν⁆) = 0 := by
  rw [div_rA SM z hS x, divJ_eq_zero z hN hH hD, neg_zero]

end Current

/-! ### The Standard-Model instance: Yang–Mills–Higgs theory data -/

section Instance

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **Variational bosonic theory data**: the sources are the Euler–Lagrange sources of the
Yang–Mills–Higgs Lagrangian `-¼⟨F, F⟩_𝔤 - ⟨DH, DH⟩_V - λ(⟨H, H⟩_V - v²)²` (the forms and the
potential of the stress `eq:YM-stress`, `eq:H-stress`): a bilinear moment map `μ : V × V → 𝔤`
dual to the gauge action (`⟨X, μ(u, w)⟩_𝔤 = ⟨X·u, w⟩_V`), alternating and gauge equivariant;
the current `J_ν = 2μ(H, D_νH)` (`δS/δA^ν`) and the Higgs source `S_H = 2λ(⟨H, H⟩ - v²)H`.
The current and the Higgs source carry no spinor terms (no Dirac current, no Yukawa source). -/
structure VariationalBosonic (SM : SMData (MatLie m) V S S') where
  /-- the moment map of the Higgs representation -/
  μ : V →ₗ[ℝ] V →ₗ[ℝ] MatLie m
  /-- the moment map is dual to the gauge action -/
  moment : ∀ (X : MatLie m) (u w : V), SM.ipG X (μ u w) = SM.ipV ⁅X, u⁆ w
  /-- it is alternating -/
  alt : ∀ u, μ u u = 0
  /-- it is gauge equivariant -/
  equiv : ∀ (X : MatLie m) (u w : V), ⁅X, μ u w⁆ = μ ⁅X, u⁆ w + μ u ⁅X, w⁆
  /-- the Yang–Mills source is the Higgs current -/
  J_eq : ∀ g gi H DH ψ ψb ν, SM.Jcur g gi H DH ψ ψb ν = (2 : ℝ) • μ H (DH ν)
  /-- the Higgs source is the gradient of the Higgs potential -/
  SH_eq : ∀ g gi H ψ ψb, SM.SH g gi H ψ ψb = (2 * SM.lamH * (SM.ipV H H - SM.vH ^ 2)) • H

variable (z : Tuple m V S S')

/-- The covariant Higgs gradient along a line. -/
theorem line_DHf (x : ST 3) (δ μ : Fin 4) :
    HasDerivAt (fun s : ℝ => DHf z (x + s • ev δ) μ)
      (dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
        (fun δ μ => pd (pd z.H μ) δ x) δ μ) 0 := by
  have hDH := hasDerivAt_DH (A := fun s : ℝ => z.A (x + s • ev δ))
    (dA := fun s : ℝ => fun μ ν => pd z.A μ (x + s • ev δ) ν)
    (H := fun s : ℝ => z.H (x + s • ev δ)) (dH := fun s : ℝ => fun μ => pd z.H μ (x + s • ev δ))
    (t := 0) (ddH := fun δ μ => pd (pd z.H μ) δ x) δ (by simpa using z.line_A x δ)
    (by simpa using z.line_H x δ) (fun μ => z.line_dH x δ μ) μ
  simp only [zero_smul, add_zero] at hDH
  exact hDH

theorem contDiff_DHf : ContDiff ℝ ∞ (DHf z) := by
  refine contDiff_pi.2 fun μ => ?_
  have h1 := Tuple.contDiff_vec z.A_smooth μ
  have h2 := z.H_smooth
  have h3 := contDiff_pd z.H_smooth μ
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  show ContDiffAt ℝ ∞ (fun y => pd z.H μ y + ⁅z.A y μ, z.H y⁆) y
  fun_prop

theorem pd_DHf (x : ST 3) (r μ : Fin 4) :
    pd (DHf z) r x μ = dDH (z.A x) (fun μ ν => pd z.A μ x ν) (z.H x) (fun μ => pd z.H μ x)
      (fun δ μ => pd (pd z.H μ) δ x) r μ := by
  rw [← pd_apply (((contDiff_DHf z).differentiable (by simp)) x) r μ]
  exact pd_eq_of_line (((contDiff_pi.1 (contDiff_DHf z) μ).differentiable (by simp)) x)
    (line_DHf z x r μ)

/-- The Higgs density `ϱ g^{νβ}D_βH`. -/
def densH (y : ST 3) (ν : Fin 4) : V := rho z y • ∑ β, z.gi y ν β • DHf z y β

theorem contDiff_densH (ν : Fin 4) : ContDiff ℝ ∞ (fun y => densH z y ν) := by
  have h1 := contDiff_rho z
  have h2 := z.contDiff_gi
  have h3 := fun β => contDiff_pi.1 (contDiff_DHf z) β
  unfold densH
  fun_prop

/-- **The covariant wave operator as a density divergence**:
`∂_ν(ϱ g^{νβ}D_βH) + A_ν·(ϱ g^{νβ}D_βH) = ϱ □_AH`. -/
theorem div_densH (x : ST 3) :
    ∑ ν, (pd (fun y => densH z y ν) ν x + ⁅z.A x ν, densH z x ν⁆) =
      rho z x • waveH (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH (z.jet x).ddH (z.gi x)
        (chr (z.gi x) (z.dg x)) := by
  rw [Finset.sum_add_distrib]
  unfold densH
  rw [div_density z (DHf z) x (((contDiff_DHf z).differentiable (by simp)) x)]
  have hbr : ∑ ν, ⁅z.A x ν, rho z x • ∑ β, z.gi x ν β • DHf z x β⁆ =
      rho z x • ∑ ν, ∑ r, z.gi x ν r • ⁅z.A x r, DHf z x ν⁆ := by
    simp only [lie_smul, lie_sum]
    rw [← Finset.smul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [z.gi_symm x b a]
  rw [hbr, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  unfold waveH
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← smul_add, pd_DHf]
  rfl

/-- **The current Noether identity for variational bosonic data**:
`ϱ D^νJ_ν = 2ϱ μ(H, r_H)` for every smooth tuple (gauge equivariance of `μ`, `μ(DH, DH)`
contracted with the symmetric `g^{νβ}` vanishes, and `μ(H, S_H) ∝ μ(H, H) = 0`). -/
theorem divJ_variational {SM : SMData (MatLie m) V S S'} (hV : VariationalBosonic SM)
    (x : ST 3) : divJ SM z x = rho z x • ((2 : ℝ) • hV.μ (z.H x) ((bosF SM z x).2.2)) := by
  have hJ : ∀ y ν, densJ SM z y ν = (2 : ℝ) • hV.μ (z.H y) (densH z y ν) := by
    intro y ν
    unfold densJ densH Jf
    simp only [hV.J_eq, map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [smul_smul]
    congr 1
    ring
  have hpd : ∀ ν, pd (fun y => densJ SM z y ν) ν x = (2 : ℝ) • (hV.μ (pd z.H ν x) (densH z x ν) +
      hV.μ (z.H x) (pd (fun y => densH z y ν) ν x)) := by
    intro ν
    rw [show (fun y => densJ SM z y ν) = fun y => (2 : ℝ) • hV.μ (z.H y) (densH z y ν) from
      funext fun y => hJ y ν]
    have hd : DifferentiableAt ℝ (fun y => (2 : ℝ) • hV.μ (z.H y) (densH z y ν)) x :=
      ((ContDiffAt.bilinApply hV.μ z.H_smooth.contDiffAt
        (contDiff_densH z ν).contDiffAt).const_smul (2 : ℝ)).differentiableAt (by simp)
    refine pd_eq_of_line hd ?_
    have := (hasDerivAt_bilin hV.μ (hasDerivAt_line0 (z.H_smooth.differentiable (by simp) x) ν)
      (hasDerivAt_line0 (((contDiff_densH z ν).differentiable (by simp)) x) ν)).const_smul (2 : ℝ)
    simp only [zero_smul, add_zero] at this
    exact this
  have hbr : ∀ ν, ⁅z.A x ν, densJ SM z x ν⁆ = (2 : ℝ) • (hV.μ ⁅z.A x ν, z.H x⁆ (densH z x ν) +
      hV.μ (z.H x) ⁅z.A x ν, densH z x ν⁆) := by
    intro ν
    rw [hJ, lie_smul, hV.equiv]
  -- the alternating moment map kills the symmetric contraction of `DH ⊗ DH`
  have hanti : ∀ u w, hV.μ w u = -hV.μ u w := by
    intro u w
    have h := hV.alt (u + w)
    simp only [map_add, LinearMap.add_apply, hV.alt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hsym : ∑ ν, hV.μ (DHf z x ν) (densH z x ν) = 0 := by
    unfold densH
    simp only [map_smul, map_sum]
    rw [← Finset.smul_sum]
    rw [sum_sym_anti_eq_zero (fun ν β => z.gi x ν β) (fun ν β => hV.μ (DHf z x ν) (DHf z x β))
      (fun a b => z.gi_symm x b a) (fun a b => hanti _ _), smul_zero]
  have hwave := div_densH z x
  have hSH : hV.μ (z.H x) (SM.SH (z.jet x).FJ.g (z.jet x).FJ.gi (z.jet x).H (z.jet x).ψ
      (z.jet x).ψb) = 0 := by
    rw [hV.SH_eq, map_smul]
    show _ • hV.μ (z.H x) (z.H x) = 0
    rw [hV.alt, smul_zero]
  have hrH : waveH (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH (z.jet x).ddH (z.gi x)
      (chr (z.gi x) (z.dg x)) = (bosF SM z x).2.2 +
        SM.SH (z.jet x).FJ.g (z.jet x).FJ.gi (z.jet x).H (z.jet x).ψ (z.jet x).ψb := by
    show _ = higgsRes _ _ _ _ _ _ _ _ + _
    unfold higgsRes
    rw [sub_add_cancel]
    rfl
  unfold divJ
  simp only [hpd, hbr, ← smul_add, ← Finset.smul_sum]
  have e : ∑ ν, (hV.μ (pd z.H ν x) (densH z x ν) + hV.μ (z.H x) (pd (fun y => densH z y ν) ν x) +
      (hV.μ ⁅z.A x ν, z.H x⁆ (densH z x ν) + hV.μ (z.H x) ⁅z.A x ν, densH z x ν⁆)) =
      ∑ ν, hV.μ (DHf z x ν) (densH z x ν) +
        hV.μ (z.H x) (∑ ν, (pd (fun y => densH z y ν) ν x + ⁅z.A x ν, densH z x ν⁆)) := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    show _ = hV.μ (pd z.H ν x + ⁅z.A x ν, z.H x⁆) (densH z x ν) + _
    rw [map_add, LinearMap.add_apply, map_add]
    abel
  rw [e, hsym, zero_add, hwave, hrH, map_smul, map_add, hSH, add_zero, smul_comm]

/-- **The Standard-Model (bosonic) instance of the current Noether identity**: variational
Yang–Mills–Higgs theory data satisfy `CurrentNoether` with `K(…, H, …)(r_H, r_D, r̄_D) = 2μ(H, r_H)`. -/
def currentNoether_of_variational {SM : SMData (MatLie m) V S S'} (hV : VariationalBosonic SM) :
    CurrentNoether SM where
  K := fun _ _ H _ _ _ => (2 : ℝ) • (hV.μ H).comp (LinearMap.fst ℝ V (S × S'))
  div_eq := fun z x => by
    rw [divJ_variational z hV x]
    rfl

end Instance

/-! ### The covariant divergence of the current in Christoffel form -/

section ChristoffelForm

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (SM : SMData (MatLie m) V S S') (z : Tuple m V S S')

theorem contDiff_Jf (hS : SMSmooth SM) : ContDiff ℝ ∞ (Jf SM z) := by
  refine contDiff_pi.2 fun ν => contDiff_iff_contDiffAt.2 fun y => ?_
  exact ContDiffAt.Jcur hS z.g_smooth.contDiffAt (z.contDiffAt_gi_fun y) z.H_smooth.contDiffAt
    (contDiff_DHf z).contDiffAt z.ψ_smooth.contDiffAt z.ψb_smooth.contDiffAt ν

/-- **`divJ` is `ϱ` times the gauge-covariant divergence of the current**:
`ϱ D^νJ_ν = ϱ g^{νr}(∂_rJ_ν - Γ^l{}_{rν}J_l + [A_r, J_ν])` (Levi-Civita connection of the tuple's
metric). -/
theorem divJ_eq (hS : SMSmooth SM) (x : ST 3) :
    divJ SM z x = rho z x • ∑ ν, ∑ r, z.gi x ν r • (pd (Jf SM z) r x ν -
      ∑ l, chr (z.gi x) (z.dg x) l r ν • Jf SM z x l + ⁅z.A x r, Jf SM z x ν⁆) := by
  unfold divJ densJ
  rw [Finset.sum_add_distrib,
    div_density z (Jf SM z) x (((contDiff_Jf SM z hS).differentiable (by simp)) x)]
  have hbr : ∑ ν, ⁅z.A x ν, rho z x • ∑ β, z.gi x ν β • Jf SM z x β⁆ =
      rho z x • ∑ ν, ∑ r, z.gi x ν r • ⁅z.A x r, Jf SM z x ν⁆ := by
    simp only [lie_smul, lie_sum]
    rw [← Finset.smul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [z.gi_symm x b a]
  rw [hbr, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← smul_add]

end ChristoffelForm

/-! ### Concrete instances -/

section Concrete

/-- `gl(m)` elements as matrices. -/
def toMat {m : ℕ} (X : MatLie m) : Matrix (Fin m) (Fin m) ℝ := X

theorem toMat_add {m : ℕ} (X Y : MatLie m) : toMat (X + Y) = toMat X + toMat Y := rfl
theorem toMat_smul {m : ℕ} (c : ℝ) (X : MatLie m) : toMat (c • X) = c • toMat X := rfl
theorem toMat_lie {m : ℕ} (X Y : MatLie m) :
    toMat ⁅X, Y⁆ = toMat X * toMat Y - toMat Y * toMat X := rfl

/-- The trace form `⟨X, Y⟩ = tr(XY)` on `gl(m)` (ad-invariant, nondegenerate). -/
def traceForm (m : ℕ) : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y : MatLie m => Matrix.trace (toMat X * toMat Y))
    (fun X X' Y => by rw [toMat_add, Matrix.add_mul, Matrix.trace_add])
    (fun c X Y => by rw [toMat_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun X Y Y' => by rw [toMat_add, Matrix.mul_add, Matrix.trace_add])
    (fun c X Y => by rw [toMat_smul, Matrix.mul_smul, Matrix.trace_smul])

theorem traceForm_apply (m : ℕ) (X Y : MatLie m) :
    traceForm m X Y = Matrix.trace (toMat X * toMat Y) := rfl

/-- A Dirac block on the zero spinor space for `gl(m)` with the adjoint Higgs. -/
def trivDiracGl (m : ℕ) : DiracData (MatLie m) (MatLie m) PUnit where
  Fr := trivFrame
  ρ := 0
  ρ_lie := fun _ _ => Subsingleton.elim _ _
  m0 := 0
  L := 0
  lorentz := ⟨by simp [trivFrame, lorentzSign], fun a => by
    simp [trivFrame, lorentzSign, Fin.succ_ne_zero]⟩
  comm := fun _ _ => Subsingleton.elim _ _
  mass_cl := fun _ _ _ => Subsingleton.elim _ _
  mass_eq := fun _ _ => Subsingleton.elim _ _

/-- **The `gl(m)` Yang–Mills–adjoint-Higgs theory data** (cosmological constant `Λ`, coupling `κ`,
Mexican-hat potential `λ(tr H² - v²)²`): trace forms on the gauge algebra and the Higgs space,
current `J_ν = 2[H, D_νH]` and Higgs source `S_H = 2λ(tr H² - v²)H` (the Euler–Lagrange sources of
`-¼ tr F² - tr (DH)² - λ(tr H² - v²)²`), no fermions. -/
def adjSM (m : ℕ) (Λ κ lam v : ℝ) : SMData (MatLie m) (MatLie m) PUnit PUnit where
  Λ := Λ
  κ := κ
  D := trivDiracGl m
  Db := trivDiracGl m
  Jcur := fun _ _ H DH _ _ ν => (2 : ℝ) • ⁅H, DH ν⁆
  SH := fun _ _ H _ _ => (2 * lam * (traceForm m H H - v ^ 2)) • H
  ipG := traceForm m
  ipV := traceForm m
  lamH := lam
  vH := v
  TD := ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- The adjoint model is variational: the moment map is the bracket (`tr(X[u, w]) = tr([X, u]w)`),
alternating and equivariant (Jacobi identity). -/
def adjSM_variational (m : ℕ) (Λ κ lam v : ℝ) : VariationalBosonic (adjSM m Λ κ lam v) where
  μ := lieB m
  moment := fun X u w => by
    show traceForm m X ⁅u, w⁆ = traceForm m ⁅X, u⁆ w
    rw [traceForm_apply, traceForm_apply, toMat_lie, toMat_lie, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_sub, Matrix.trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (toMat X * toMat w) (toMat u), Matrix.mul_assoc, Matrix.mul_assoc]
  alt := fun u => lie_self u
  equiv := fun X u w => leibniz_lie X u w
  J_eq := fun _ _ _ _ _ _ _ => rfl
  SH_eq := fun _ _ _ _ _ => rfl

/-- **The concrete Standard-Model-type instance of the current Noether identity**: the `gl(m)`
Yang–Mills–adjoint-Higgs data satisfy `CurrentNoether`, `ϱ D^νJ_ν = 2ϱ[H, r_H]`. -/
def adjSM_currentNoether (m : ℕ) (Λ κ lam v : ℝ) : CurrentNoether (adjSM m Λ κ lam v) :=
  currentNoether_of_variational (adjSM_variational m Λ κ lam v)

theorem adjSM_smooth (m : ℕ) (Λ κ lam v : ℝ) : SMSmooth (adjSM m Λ κ lam v) where
  J ν := by
    refine contDiff_iff_contDiffAt.2 fun p => ?_
    have h1 : ContDiffAt ℝ ∞ (fun p : Met × Met × MatLie m × (Fin 4 → MatLie m) × PUnit × PUnit =>
        p.2.2.1) p := by fun_prop
    have h2 : ContDiffAt ℝ ∞ (fun p : Met × Met × MatLie m × (Fin 4 → MatLie m) × PUnit × PUnit =>
        p.2.2.2.1 ν) p := by fun_prop
    exact (ContDiffAt.lie_mat h1 h2).const_smul (2 : ℝ)
  SH := by
    refine contDiff_iff_contDiffAt.2 fun p => ?_
    have h1 : ContDiffAt ℝ ∞ (fun p : Met × Met × MatLie m × PUnit × PUnit => p.2.2.1) p := by
      fun_prop
    have h2 := ContDiffAt.bilinApply (traceForm m) h1 h1
    show ContDiffAt ℝ ∞ (fun p : Met × Met × MatLie m × PUnit × PUnit =>
      (2 * lam * (traceForm m p.2.2.1 p.2.2.1 - v ^ 2)) • p.2.2.1) p
    fun_prop
  P2 := fun A B => by
    have : (fun p : MatLie m × PUnit × PUnit => (adjSM m Λ κ lam v).TD.P'' A B p.1 p.2.1 p.2.2) =
        fun _ => (0 : ℝ) := by funext p; rfl
    rw [this]; exact contDiff_const

/-- The flat-vacuum data `trivSMM` are variational (zero moment map). -/
def trivSMM_variational : VariationalBosonic trivSMM where
  μ := 0
  moment := fun _ _ _ => by simp [trivSMM]
  alt := fun _ => rfl
  equiv := fun _ _ _ => by simp
  J_eq := fun _ _ _ _ _ _ _ => by simp [trivSMM]
  SH_eq := fun _ _ H _ _ => by simp [trivSMM]

end Concrete

end RenewalGeometry.GenNoether
