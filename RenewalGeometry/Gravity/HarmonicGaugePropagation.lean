/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.MetricJetChainRule
import RenewalGeometry.Gravity.SliceGaussCodazziJet
import RenewalGeometry.Gravity.OpenWriterContinuumComparison
import RenewalGeometry.Continuum.TorusWaveEnergyUniqueness

/-!
# Propagation of the harmonic gauge for classical solutions of the reduced equation
  (vacuum clause of `thm:supp-open-einstein`; `lem:supp-open-subsidiary` with `r = 0`,
  `lem:supp-open-initial-gauge` with exact data; emergent-spacetime manuscript)

* `mhasDeriv_inv` — the derivative of the inverse metric, `∂(g⁻¹) = -g⁻¹ ∂g g⁻¹` (inverses taken
  at type `Matrix`).
* `normalRow_eq` — the harmonic normal row `eq:main-harmonic-normal-row` is
  `2(R_{μν} - ∇_{(μ}C_{ν)})` of the metric 2-jet; `reducedEinstein_eq_zero_of_normalRow` — a vanishing
  normal row gives a vanishing reduced Einstein tensor `Ĝ = G - 𝓗 = r`.
-/

open Finset Matrix Filter Topology
open scoped BigOperators

namespace RenewalGeometry.HarmonicGaugePropagation

open ContractedBianchiJet OpenWriterEnergy OpenWriterChart HarmonicDefect OpenWriterContinuum
  TorusSobolevTransfer

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The derivative of the inverse metric -/

/-- `∂(A⁻¹) = -A⁻¹ (∂A) A⁻¹` for an entrywise differentiable invertible `4 × 4` matrix. -/
theorem mhasDeriv_inv {A : ℝ → Matrix (Fin 4) (Fin 4) ℝ} {A' : Matrix (Fin 4) (Fin 4) ℝ} {s : ℝ}
    (hA : MHasDeriv A A' s) (hdet : (A s).det ≠ 0) :
    MHasDeriv (fun s => (A s)⁻¹) (-((A s)⁻¹ * A' * (A s)⁻¹)) s := by
  set a : ℝ → MetricRec := fun s => fun i j => A s i j
  have ha : HasDerivAt a (fun i j => A' i j) s :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hA i j
  have hdet' : (Matrix.of (a s)).det ≠ 0 := hdet
  -- differentiability of the inverse entries
  set D : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    fderiv ℝ (fun g : MetricRec => (Matrix.of g)⁻¹ i j) (a s) (fun i j => A' i j)
  have hD : MHasDeriv (fun s => (A s)⁻¹) D s := by
    intro i j
    have h1 := (analyticAt_inv_entry (a s) hdet' i j).differentiableAt.hasFDerivAt
    exact h1.comp_hasDerivAt s ha
  -- invertibility near `s`
  have hev : ∀ᶠ s' in 𝓝 s, (A s').det ≠ 0 := by
    have hc : ContinuousAt (fun s' => (Matrix.of (a s')).det) s :=
      (analyticAt_det (a s)).continuousAt.comp ha.continuousAt
    exact hc.eventually_ne hdet'
  have hprod := hA.mul hD
  have hzero : A' * (A s)⁻¹ + A s * D = 0 := by
    ext i j
    have h2 : HasDerivAt (fun s' => (A s' * (A s')⁻¹) i j) 0 s := by
      refine (hasDerivAt_const s ((1 : Matrix (Fin 4) (Fin 4) ℝ) i j)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with s' hs'
      rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hs')]
    exact (hprod i j).unique h2
  have hDe : D = -((A s)⁻¹ * A' * (A s)⁻¹) := by
    have h3 : (A s)⁻¹ * (A s) = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
    calc D = (A s)⁻¹ * (A s * D) := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      _ = (A s)⁻¹ * (-(A' * (A s)⁻¹)) := by rw [eq_neg_of_add_eq_zero_right hzero]
      _ = -((A s)⁻¹ * A' * (A s)⁻¹) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  exact hDe ▸ hD

/-! ### The normal row is twice the reduced Ricci combination -/

/-- The space-time second-derivative array `∂_α∂_β g_{μν}` from `(q_tt, ∂ᵢq_t, ∂ᵢ∂ⱼq)`. -/
def ddArr (w : MetricRec) (vd : Fin 3 → MetricRec) (qdd : Fin 3 → Fin 3 → MetricRec) :
    Fin 4 → Fin 4 → MetricRec :=
  fun α β => Fin.cases (Fin.cases w (fun j => vd j) β) (fun i => Fin.cases (vd i) (fun j => qdd i j) β) α

@[simp] theorem ddArr_zero_zero (w : MetricRec) (vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) : ddArr w vd qdd 0 0 = w := rfl
@[simp] theorem ddArr_zero_succ (w : MetricRec) (vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (j : Fin 3) : ddArr w vd qdd 0 j.succ = vd j := rfl
@[simp] theorem ddArr_succ_zero (w : MetricRec) (vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (i : Fin 3) : ddArr w vd qdd i.succ 0 = vd i := rfl
@[simp] theorem ddArr_succ_succ (w : MetricRec) (vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (i j : Fin 3) : ddArr w vd qdd i.succ j.succ = qdd i j := rfl

theorem recInv_symm {g : MetricRec} (hg : ∀ μ ν, g μ ν = g ν μ) (μ ν : Fin 4) :
    recInv g μ ν = recInv g ν μ := by
  have hT : Matrix.transpose (Matrix.of g) = Matrix.of g := by
    ext a b; simp [Matrix.transpose_apply, Matrix.of_apply, hg]
  have h := Matrix.transpose_nonsing_inv (Matrix.of g)
  rw [hT] at h
  have := congrFun (congrFun h ν) μ
  rw [Matrix.transpose_apply] at this
  exact this

theorem recInv_hinv {g : MetricRec} (hdet : (Matrix.of g).det ≠ 0) (a c : Fin 4) :
    ∑ b, g a b * recInv g b c = if a = c then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (Matrix.of g) (Ne.isUnit hdet)) a) c
  simpa [Matrix.mul_apply, Matrix.one_apply, recInv] using h

theorem waveOp_ddArr {gi : MetricRec} (hgi : ∀ a b, gi a b = gi b a) (w : MetricRec)
    (vd : Fin 3 → MetricRec) (qdd : Fin 3 → Fin 3 → MetricRec) (μ ν : Fin 4) :
    waveOp gi (ddArr w vd qdd) μ ν = gi 0 0 * w μ ν + 2 * ∑ i, gi 0 i.succ * vd i μ ν +
      ∑ i, ∑ j, gi i.succ j.succ * qdd i j μ ν := by
  simp only [waveOp, Fin.sum_univ_succ (n := 3), ddArr_zero_zero, ddArr_zero_succ,
    ddArr_succ_zero, ddArr_succ_succ]
  have : ∑ i : Fin 3, gi i.succ 0 * vd i μ ν = ∑ i : Fin 3, gi 0 i.succ * vd i μ ν :=
    Finset.sum_congr rfl fun i _ => by rw [hgi]
  rw [Finset.sum_add_distrib, this]
  ring

/-- **The normal row is `2(R_{μν} - ∇_{(μ}C_{ν)})`** of the metric 2-jet
`(g, g⁻¹, (q_t, ∂q), (q_tt, ∂q_t, ∂∂q))`, `g = η + q`. -/
theorem normalRow_eq (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (hq : ∀ μ ν, q μ ν = q ν μ)
    (hdet : (Matrix.of (minkowski + q)).det ≠ 0)
    (hw : ∀ μ ν, w μ ν = w ν μ) (hvd : ∀ i μ ν, vd i μ ν = vd i ν μ)
    (hqdd : ∀ i j μ ν, qdd i j μ ν = qdd i j ν μ) (hqdd' : ∀ i j, qdd i j = qdd j i) (μ ν : Fin 4) :
    normalRow q v w qd vd qdd μ ν =
      2 * (ricci (recInv (minkowski + q)) (metricJet (v, qd)) (ddArr w vd qdd) μ ν -
        symDefect (minkowski + q) (recInv (minkowski + q)) (metricJet (v, qd)) (ddArr w vd qdd) μ ν) := by
  have hg : ∀ μ ν, (minkowski + q) μ ν = (minkowski + q) ν μ := by
    intro μ ν
    simp only [Pi.add_apply, hq μ ν]
    congr 1
    unfold minkowski
    by_cases h : μ = ν
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hgi := recInv_symm hg
  have hs1 : ∀ α β μ ν, ddArr w vd qdd α β μ ν = ddArr w vd qdd β α μ ν := by
    intro α β μ ν
    refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;> simp [hqdd']
  have hs2 : ∀ α β μ ν, ddArr w vd qdd α β μ ν = ddArr w vd qdd α β ν μ := by
    intro α β μ ν
    refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
      simp [hw, hvd, hqdd]
  rw [ricci_sub_symDefect _ _ _ _ hgi (recInv_hinv hdet) hs1 hs2, waveOp_ddArr hgi]
  simp only [normalRow, harmonicSource, harmA, harmB, harmC, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply, recInv, neg_mul, Finset.sum_neg_distrib]
  ring

theorem trG_traceRev {n : Type*} [Fintype n] [DecidableEq n] (g gi : n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) (X : n → n → ℝ) : trG gi (traceRev g gi X) = -trG gi X := by
  have h : traceRev g gi X = fun a b => 1 * X a b + (-(1 / 2) * trG gi X) * g a b + 0 * X a b := by
    funext a b; unfold traceRev; ring
  rw [h, trG_comb, trG_metric g gi hgi hinv, hcard]
  push_cast; ring

/-- A trace-reversed tensor vanishes only if the tensor does (dimension four). -/
theorem eq_zero_of_traceRev_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (g gi : n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) (X : n → n → ℝ) (h : ∀ a b, traceRev g gi X a b = 0) :
    ∀ a b, X a b = 0 := by
  have htr : trG gi X = 0 := by
    have h1 := trG_traceRev g gi hgi hinv hcard X
    have h2 : trG gi (traceRev g gi X) = 0 := by
      unfold trG; simp [h]
    linarith
  intro a b
  have := h a b
  unfold traceRev at this
  rw [htr] at this
  linarith

/-- **A vanishing normal row gives a vanishing reduced Einstein tensor** `Ĝ = G - 𝓗 = 0`. -/
theorem reducedEinstein_eq_zero_of_normalRow (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (hq : ∀ μ ν, q μ ν = q ν μ)
    (hdet : (Matrix.of (minkowski + q)).det ≠ 0)
    (hw : ∀ μ ν, w μ ν = w ν μ) (hvd : ∀ i μ ν, vd i μ ν = vd i ν μ)
    (hqdd : ∀ i j μ ν, qdd i j μ ν = qdd i j ν μ) (hqdd' : ∀ i j, qdd i j = qdd j i)
    (hrow : ∀ μ ν, normalRow q v w qd vd qdd μ ν = 0) (μ ν : Fin 4) :
    reducedEinstein (minkowski + q) (recInv (minkowski + q)) (metricJet (v, qd)) (ddArr w vd qdd)
      μ ν = 0 := by
  have hg : ∀ μ ν, (minkowski + q) μ ν = (minkowski + q) ν μ := by
    intro μ ν
    simp only [Pi.add_apply, hq μ ν]
    congr 1
    unfold minkowski
    by_cases h : μ = ν
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hgi := recInv_symm hg
  have hinv := recInv_hinv hdet
  set g := minkowski + q
  set gi := recInv g
  set dg := metricJet (v, qd)
  set ddg := ddArr w vd qdd
  refine eq_zero_of_traceRev_eq_zero g gi hgi hinv (by simp) _ (fun a b => ?_) μ ν
  have h1 := harmonic_residual_trace_reversal g gi dg ddg hgi hinv (by simp) (fun _ _ => 0) 0 0 a b
  simp only [zero_mul, add_zero, sub_zero] at h1
  have h2 : traceRev g gi (fun a b => einstein g gi dg ddg a b) a b = ricci gi dg ddg a b := by
    have htr : trG gi (fun a b => einstein g gi dg ddg a b) = -trG gi (ricci gi dg ddg) := by
      have e : (fun a b => einstein g gi dg ddg a b) = fun a b => 1 * ricci gi dg ddg a b +
          (-(1 / 2) * trG gi (ricci gi dg ddg)) * g a b + 0 * g a b := by
        funext a b; unfold einstein; ring
      rw [e, trG_comb, trG_metric g gi hgi hinv]
      simp; ring
    unfold traceRev
    rw [htr]
    unfold einstein
    ring
  have h3 := normalRow_eq q v w qd vd qdd hq hdet hw hvd hqdd hqdd' a b
  rw [hrow a b] at h3
  have : (fun a b => reducedEinstein g gi dg ddg a b) = reducedEinstein g gi dg ddg := rfl
  rw [this] at h1
  rw [h1, h2]
  linarith


/-! ### Classical `C³` fields and their metric 3-jets -/

/-- The third-derivative array `∂_a∂_b∂_c g` from `(∂ₜ³q, ∂ᵢ∂ₜ²q, ∂ᵢ∂ⱼ∂ₜq, ∂ᵢ∂ⱼ∂ₖq)`. -/
def d3Arr (At : MetricRec) (Ad : Fin 3 → MetricRec) (Vdd : Fin 3 → Fin 3 → MetricRec)
    (Qddd : Fin 3 → Fin 3 → Fin 3 → MetricRec) : Fin 4 → Fin 4 → Fin 4 → MetricRec :=
  fun a b c => Fin.cases (ddArr At Ad Vdd b c) (fun i => ddArr (Ad i) (Vdd i) (Qddd i) b c) a

@[simp] theorem d3Arr_zero (At : MetricRec) (Ad : Fin 3 → MetricRec)
    (Vdd : Fin 3 → Fin 3 → MetricRec) (Qddd : Fin 3 → Fin 3 → Fin 3 → MetricRec) (b c : Fin 4) :
    d3Arr At Ad Vdd Qddd 0 b c = ddArr At Ad Vdd b c := rfl

@[simp] theorem d3Arr_succ (At : MetricRec) (Ad : Fin 3 → MetricRec)
    (Vdd : Fin 3 → Fin 3 → MetricRec) (Qddd : Fin 3 → Fin 3 → Fin 3 → MetricRec) (i : Fin 3)
    (b c : Fin 4) : d3Arr At Ad Vdd Qddd i.succ b c = ddArr (Ad i) (Vdd i) (Qddd i) b c := rfl

/-- A space-time field `g = η + Q` on `ℝ × 𝕋³` with candidate classical derivative fields up to
order three: `V = ∂ₜQ`, `A = ∂ₜ²Q`, `At = ∂ₜ³Q`, `Qd i = ∂ᵢQ`, `Vd i = ∂ᵢ∂ₜQ`, `Ad i = ∂ᵢ∂ₜ²Q`,
`Qdd i j = ∂ᵢ∂ⱼQ`, `Vdd i j = ∂ᵢ∂ⱼ∂ₜQ`, `Qddd i j k = ∂ᵢ∂ⱼ∂ₖQ`. -/
structure C3Field where
  Q : ℝ → T3 → MetricRec
  V : ℝ → T3 → MetricRec
  A : ℝ → T3 → MetricRec
  At : ℝ → T3 → MetricRec
  Qd : ℝ → Fin 3 → T3 → MetricRec
  Vd : ℝ → Fin 3 → T3 → MetricRec
  Ad : ℝ → Fin 3 → T3 → MetricRec
  Qdd : ℝ → Fin 3 → Fin 3 → T3 → MetricRec
  Vdd : ℝ → Fin 3 → Fin 3 → T3 → MetricRec
  Qddd : ℝ → Fin 3 → Fin 3 → Fin 3 → T3 → MetricRec

namespace C3Field

variable (F : C3Field)

/-- The metric 3-jet of `g = η + Q` at `(t, x)` (inverse taken at type `Matrix`). -/
def jetAt (t : ℝ) (x : T3) : Jet3 (Fin 4) where
  g := Matrix.of (minkowski + F.Q t x)
  G := (Matrix.of (minkowski + F.Q t x))⁻¹
  dg := fun a => Matrix.of (metricJet (F.V t x, fun i => F.Qd t i x) a)
  ddg := fun a b => Matrix.of (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x) a b)
  dddg := fun a b c => Matrix.of (d3Arr (F.At t x) (fun i => F.Ad t i x) (fun i j => F.Vdd t i j x)
    (fun i j k => F.Qddd t i j k x) a b c)

/-- The hypotheses: continuity on the slab, symmetric records and derivative indices, the
classical derivative relations (time derivatives on `(0, T)`, spatial ones on `[0, T]`), the
small Lorentzian chart `|g^{μν} - η^{μν}| ≤ 1/10`, and the harmonic reduced equation
`eq:main-harmonic-normal-row` (all components). -/
structure Hyp (T : ℝ) : Prop where
  cQ : ContinuousOn (fun p : ℝ × T3 => F.Q p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cV : ContinuousOn (fun p : ℝ × T3 => F.V p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cA : ContinuousOn (fun p : ℝ × T3 => F.A p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cAt : ContinuousOn (fun p : ℝ × T3 => F.At p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cQd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Qd p.1 i p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cVd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Vd p.1 i p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cAd : ∀ i, ContinuousOn (fun p : ℝ × T3 => F.Ad p.1 i p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cQdd : ∀ i j, ContinuousOn (fun p : ℝ × T3 => F.Qdd p.1 i j p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cVdd : ∀ i j, ContinuousOn (fun p : ℝ × T3 => F.Vdd p.1 i j p.2) (Set.Icc 0 T ×ˢ Set.univ)
  cQddd : ∀ i j k, ContinuousOn (fun p : ℝ × T3 => F.Qddd p.1 i j k p.2) (Set.Icc 0 T ×ˢ Set.univ)
  sQ : ∀ t x μ ν, F.Q t x μ ν = F.Q t x ν μ
  sV : ∀ t x μ ν, F.V t x μ ν = F.V t x ν μ
  sA : ∀ t x μ ν, F.A t x μ ν = F.A t x ν μ
  sAt : ∀ t x μ ν, F.At t x μ ν = F.At t x ν μ
  sQd : ∀ t i x μ ν, F.Qd t i x μ ν = F.Qd t i x ν μ
  sVd : ∀ t i x μ ν, F.Vd t i x μ ν = F.Vd t i x ν μ
  sAd : ∀ t i x μ ν, F.Ad t i x μ ν = F.Ad t i x ν μ
  sQdd : ∀ t i j x μ ν, F.Qdd t i j x μ ν = F.Qdd t i j x ν μ
  sVdd : ∀ t i j x μ ν, F.Vdd t i j x μ ν = F.Vdd t i j x ν μ
  sQddd : ∀ t i j k x μ ν, F.Qddd t i j k x μ ν = F.Qddd t i j k x ν μ
  iQdd : ∀ t i j, F.Qdd t i j = F.Qdd t j i
  iVdd : ∀ t i j, F.Vdd t i j = F.Vdd t j i
  iQddd1 : ∀ t i j k, F.Qddd t i j k = F.Qddd t j i k
  iQddd2 : ∀ t i j k, F.Qddd t i j k = F.Qddd t i k j
  tQ : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.Q τ x) (F.V t x) t
  tV : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.V τ x) (F.A t x) t
  tA : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasDerivAt (fun τ => F.A τ x) (F.At t x) t
  tQd : ∀ t ∈ Set.Ioo 0 T, ∀ i x, HasDerivAt (fun τ => F.Qd τ i x) (F.Vd t i x) t
  tVd : ∀ t ∈ Set.Ioo 0 T, ∀ i x, HasDerivAt (fun τ => F.Vd τ i x) (F.Ad t i x) t
  tQdd : ∀ t ∈ Set.Ioo 0 T, ∀ i j x, HasDerivAt (fun τ => F.Qdd τ i j x) (F.Vdd t i j x) t
  xQ : ∀ t ∈ Set.Icc 0 T, ∀ i, IsLineDeriv i (F.Q t) (F.Qd t i)
  xV : ∀ t ∈ Set.Icc 0 T, ∀ i, IsLineDeriv i (F.V t) (F.Vd t i)
  xA : ∀ t ∈ Set.Icc 0 T, ∀ i, IsLineDeriv i (F.A t) (F.Ad t i)
  xQd : ∀ t ∈ Set.Icc 0 T, ∀ i j, IsLineDeriv i (F.Qd t j) (F.Qdd t i j)
  xVd : ∀ t ∈ Set.Icc 0 T, ∀ i j, IsLineDeriv i (F.Vd t j) (F.Vdd t i j)
  xQdd : ∀ t ∈ Set.Icc 0 T, ∀ i j k, IsLineDeriv i (F.Qdd t j k) (F.Qddd t i j k)
  chart : ∀ t ∈ Set.Icc 0 T, ∀ x μ ν,
    |(Matrix.of (minkowski + F.Q t x))⁻¹ μ ν - minkowski μ ν| ≤ 1 / 10
  row : ∀ t ∈ Set.Icc 0 T, ∀ x μ ν, normalRow (F.Q t x) (F.V t x) (F.A t x) (fun i => F.Qd t i x)
    (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x) μ ν = 0

variable {F} {T : ℝ}

theorem minkowski_symm (μ ν : Fin 4) : minkowski μ ν = minkowski ν μ := by
  unfold minkowski
  by_cases h : μ = ν
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem Hyp.det_ne (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) :
    (Matrix.of (minkowski + F.Q t x)).det ≠ 0 := by
  intro h0
  have h1 := h.chart t ht x 0 0
  rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero, not_not]; exact h0)] at h1
  simp [minkowski] at h1
  norm_num at h1

theorem Hyp.valid (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) : (F.jetAt t x).Valid where
  gG := Matrix.mul_nonsing_inv _ (Ne.isUnit (h.det_ne ht x))
  g_symm := by
    ext μ ν
    simp [jetAt, Matrix.transpose_apply, h.sQ t x μ ν, minkowski_symm μ ν]
  G_symm := by
    have hT : Matrix.transpose (Matrix.of (minkowski + F.Q t x)) =
        Matrix.of (minkowski + F.Q t x) := by
      ext μ ν; simp [Matrix.transpose_apply, h.sQ t x μ ν, minkowski_symm μ ν]
    simp only [jetAt]
    rw [Matrix.transpose_nonsing_inv, hT]
  dg_symm := fun a => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [jetAt, metricJet, h.sV t x μ ν]
    · simp [jetAt, metricJet, h.sQd t i x μ ν]
  ddg_symm := fun a b => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      simp [jetAt, h.sA t x μ ν, h.sVd t _ x μ ν, h.sQdd t _ _ x μ ν]
  ddg_comm := fun a b => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      simp [jetAt, h.iQdd t]
  dddg_symm := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [jetAt, h.sAt t x μ ν, h.sAd t _ x μ ν, h.sVdd t _ _ x μ ν, h.sQddd t _ _ _ x μ ν]
  dddg_comm1 := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [jetAt, h.iVdd t, h.iQddd1 t]
  dddg_comm2 := fun a b c => by
    ext μ ν
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c <;>
      simp [jetAt, h.iVdd t, h.iQddd2 t]

/-- Entrywise derivative of a record-valued function. -/
theorem mhasDeriv_of_rec {f : ℝ → MetricRec} {f' : MetricRec} {s : ℝ} (hf : HasDerivAt f f' s) :
    MHasDeriv (fun s => Matrix.of (f s)) (Matrix.of f') s :=
  fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) j

theorem mhasDeriv_of_rec_add {f : ℝ → MetricRec} {f' : MetricRec} {s : ℝ} (c : MetricRec)
    (hf : HasDerivAt f f' s) : MHasDeriv (fun s => Matrix.of (c + f s)) (Matrix.of f') s :=
  fun i j => by
    have := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) j).const_add (c i j)
    simpa using this

/-- **Time paths are consistent**: for `t ∈ (0, T)`, `τ ↦ jetAt τ x` is a consistent jet path
in direction `0`. -/
theorem Hyp.pathDeriv_time (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : T3) :
    Jet3.PathDeriv (fun τ => F.jetAt τ x) 0 t where
  g := mhasDeriv_of_rec_add minkowski (h.tQ t ht x)
  G := mhasDeriv_inv (mhasDeriv_of_rec_add minkowski (h.tQ t ht x))
    (h.det_ne (Set.Ioo_subset_Icc_self ht) x)
  dg := fun a => by
    refine Fin.cases ?_ (fun i => ?_) a
    · exact mhasDeriv_of_rec (h.tV t ht x)
    · exact mhasDeriv_of_rec (h.tQd t ht i x)
  ddg := fun a b => by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact mhasDeriv_of_rec (h.tA t ht x)
    · exact mhasDeriv_of_rec (h.tVd t ht j x)
    · exact mhasDeriv_of_rec (h.tVd t ht i x)
    · exact mhasDeriv_of_rec (h.tQdd t ht i j x)

theorem jetAt_shift_zero (F : C3Field) (t : ℝ) (x : T3) (k : Fin 3) :
    F.jetAt t (x + TorusSobolevTransfer.lineShift k 0) = F.jetAt t x := by
  rw [TorusSobolevTransfer.lineShift_zero, add_zero]

/-- **Spatial paths are consistent**: for `t ∈ [0, T]`, `σ ↦ jetAt t (x + σ e_k)` is a consistent
jet path in direction `k + 1` at `σ = 0`. -/
theorem hasDerivAt_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : Fin 3}
    {G G' : T3 → E} (hG : IsLineDeriv i G G') (x : T3) :
    HasDerivAt (fun σ => G (x + lineShift i σ)) (G' (x + lineShift i 0)) 0 := by
  rw [lineShift_zero, add_zero]; exact hG x

/-- **Spatial paths are consistent**: for `t ∈ [0, T]`, `σ ↦ jetAt t (x + σ e_k)` is a consistent
jet path in direction `k + 1` at `σ = 0`. -/
theorem Hyp.pathDeriv_space (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) (k : Fin 3) :
    Jet3.PathDeriv (fun σ => F.jetAt t (x + lineShift k σ)) k.succ 0 where
  g := mhasDeriv_of_rec_add minkowski (hasDerivAt_shift (h.xQ t ht k) x)
  G := mhasDeriv_inv (mhasDeriv_of_rec_add minkowski (hasDerivAt_shift (h.xQ t ht k) x))
    (by rw [lineShift_zero, add_zero]; exact h.det_ne ht x)
  dg := fun a => by
    refine Fin.cases ?_ (fun i => ?_) a
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xV t ht k) x)
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xQd t ht k i) x)
  ddg := fun a b => by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xA t ht k) x)
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xVd t ht k j) x)
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xVd t ht k i) x)
    · exact mhasDeriv_of_rec (hasDerivAt_shift (h.xQdd t ht k i j) x)

end C3Field


namespace C3Field

variable {F : C3Field} {T : ℝ}

/-- The jet of the field agrees with the `HarmonicDefect` arrays on the 2-jet. -/
theorem resM_jetAt_eq (t : ℝ) (x : T3) (a b : Fin 4) :
    (F.jetAt t x).resM (F.jetAt t x).gc (F.jetAt t x).dgc a b =
      (ofArrays (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
        (metricJet (F.V t x, fun i => F.Qd t i x))
        (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x))).resM
      (ofArrays (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
        (metricJet (F.V t x, fun i => F.Qd t i x))
        (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x))).gc
      (ofArrays (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
        (metricJet (F.V t x, fun i => F.Qd t i x))
        (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x))).dgc a b := rfl

/-- **The reduced residual of a solution vanishes**: `r = G - 𝓗(g, c(g)) = 0` on `[0, T] × 𝕋³`. -/
theorem Hyp.resM_eq_zero (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) :
    (F.jetAt t x).resM (F.jetAt t x).gc (F.jetAt t x).dgc = 0 := by
  have hdet := h.det_ne ht x
  have hg : ∀ μ ν, (minkowski + F.Q t x) μ ν = (minkowski + F.Q t x) ν μ := by
    intro μ ν; simp only [Pi.add_apply, h.sQ t x μ ν, minkowski_symm μ ν]
  have hvalid : ArraysValid (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
      (metricJet (F.V t x, fun i => F.Qd t i x))
      (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x)) := by
    refine ⟨recInv_hinv hdet, hg, recInv_symm hg, fun α a b => ?_, fun α β μ ν => ?_,
      fun α β μ ν => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) α
      · simp [metricJet, h.sV t x a b]
      · simp [metricJet, h.sQd t i x a b]
    · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
        simp [h.iQdd t]
    · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
        simp [h.sA t x μ ν, h.sVd t _ x μ ν, h.sQdd t _ _ x μ ν]
  ext a b
  rw [resM_jetAt_eq, resM_ofArrays hvalid, Matrix.zero_apply]
  exact reducedEinstein_eq_zero_of_normalRow _ _ _ _ _ _ (h.sQ t x) hdet (h.sA t x)
    (fun i => h.sVd t i x) (fun i j => h.sQdd t i j x) (fun i j => funext fun μ => funext fun ν => by
      rw [h.iQdd t i j]) (h.row t ht x) a b

/-- At interior times the formal derivatives of the residual vanish. -/
theorem Hyp.dresM_eq_zero (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : T3) (e : Fin 4) :
    (F.jetAt t x).dresM (F.jetAt t x).gc (F.jetAt t x).dgc (F.jetAt t x).ddgc e = 0 := by
  refine Fin.cases ?_ (fun k => ?_) e
  · refine (h.pathDeriv_time ht x).dresM_eq_zero ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
    exact h.resM_eq_zero (Set.Ioo_subset_Icc_self hτ) x
  · have := (h.pathDeriv_space (Set.Ioo_subset_Icc_self ht) x k).dresM_eq_zero
      (Eventually.of_forall fun σ => h.resM_eq_zero (Set.Ioo_subset_Icc_self ht) _)
    simpa only [jetAt_shift_zero] using this

/-- **The homogeneous subsidiary equation** `□c + Ric·c = 0` for the gauge covector of a solution,
at every interior point. -/
theorem Hyp.subsidiary (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : T3) (b : Fin 4) :
    (F.jetAt t x).boxC (F.jetAt t x).gc (F.jetAt t x).dgc (F.jetAt t x).ddgc b +
      (F.jetAt t x).ricC (F.jetAt t x).gc b = 0 :=
  Jet3.subsidiary_of_residual_zero (h.valid (Set.Ioo_subset_Icc_self ht) x)
    (h.resM_eq_zero (Set.Ioo_subset_Icc_self ht) x) (h.dresM_eq_zero ht x) b

end C3Field


/-! ### Continuity of the formal jets along a continuous family of jets -/

namespace JetFam

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [TopologicalSpace X]

/-- A continuous family of metric 3-jets. -/
structure JetCont (J : X → Jet3 n) : Prop where
  g : Continuous fun p => (J p).g
  G : Continuous fun p => (J p).G
  dg : ∀ a, Continuous fun p => (J p).dg a
  ddg : ∀ a b, Continuous fun p => (J p).ddg a b
  dddg : ∀ a b c, Continuous fun p => (J p).dddg a b c

namespace JetCont

variable {J : X → Jet3 n} (h : JetCont J)
include h

theorem low (a : n) : Continuous fun p => (J p).low a :=
  continuous_matrix fun k s => continuous_const.mul ((((h.dg a).matrix_elem k s).add
    ((h.dg s).matrix_elem k a)).sub ((h.dg k).matrix_elem a s))

theorem dlow (b a : n) : Continuous fun p => (J p).dlow b a :=
  continuous_matrix fun k s => continuous_const.mul ((((h.ddg b a).matrix_elem k s).add
    ((h.ddg b s).matrix_elem k a)).sub ((h.ddg b k).matrix_elem a s))

theorem ddlow (c b a : n) : Continuous fun p => (J p).ddlow c b a :=
  continuous_matrix fun k s => continuous_const.mul ((((h.dddg c b a).matrix_elem k s).add
    ((h.dddg c b s).matrix_elem k a)).sub ((h.dddg c b k).matrix_elem a s))

theorem chr (a : n) : Continuous fun p => (J p).chr a := h.G.matrix_mul (h.low a)

theorem dG (a : n) : Continuous fun p => (J p).dG a := ((h.G.matrix_mul (h.dg a)).matrix_mul h.G).neg

theorem dchr (b a : n) : Continuous fun p => (J p).dchr b a :=
  h.G.matrix_mul ((h.dlow b a).sub ((h.dg b).matrix_mul (h.chr a)))

theorem ddchr (c b a : n) : Continuous fun p => (J p).ddchr c b a :=
  h.G.matrix_mul ((((h.ddlow c b a).sub ((h.ddg c b).matrix_mul (h.chr a))).sub
    ((h.dg c).matrix_mul (h.dchr b a))).sub ((h.dg b).matrix_mul (h.dchr c a)))

theorem riem (a b : n) : Continuous fun p => (J p).riem a b :=
  (((h.dchr a b).sub (h.dchr b a)).add ((h.chr a).matrix_mul (h.chr b))).sub
    ((h.chr b).matrix_mul (h.chr a))

theorem ricM : Continuous fun p => (J p).ricM :=
  continuous_matrix fun s b => continuous_finsetSum _ fun l _ => (h.riem l b).matrix_elem l s

theorem ddG (e f : n) : Continuous fun p => (J p).ddG e f :=
  ((((h.dG e).matrix_mul (h.dg f)).matrix_mul h.G).add
    ((h.G.matrix_mul (h.ddg e f)).matrix_mul h.G) |>.add
    ((h.G.matrix_mul (h.dg f)).matrix_mul (h.dG e))).neg

theorem gcUp (k : n) : Continuous fun p => (J p).gcUp k :=
  continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (h.G.matrix_elem a b).mul ((h.chr a).matrix_elem k b)

theorem dgcUp (e k : n) : Continuous fun p => (J p).dgcUp e k :=
  continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (((h.dG e).matrix_elem a b).mul ((h.chr a).matrix_elem k b)).add
      ((h.G.matrix_elem a b).mul ((h.dchr e a).matrix_elem k b))

theorem ddgcUp (e f k : n) : Continuous fun p => (J p).ddgcUp e f k :=
  continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (((((h.ddG e f).matrix_elem a b).mul ((h.chr a).matrix_elem k b)).add
      (((h.dG f).matrix_elem a b).mul ((h.dchr e a).matrix_elem k b))).add
      (((h.dG e).matrix_elem a b).mul ((h.dchr f a).matrix_elem k b))).add
      ((h.G.matrix_elem a b).mul ((h.ddchr e f a).matrix_elem k b))

theorem gc (b : n) : Continuous fun p => (J p).gc b :=
  continuous_finsetSum _ fun k _ => (h.g.matrix_elem b k).mul (h.gcUp k)

theorem dgc : Continuous fun p => (J p).dgc :=
  continuous_matrix fun e b => continuous_finsetSum _ fun k _ =>
    (((h.dg e).matrix_elem b k).mul (h.gcUp k)).add ((h.g.matrix_elem b k).mul (h.dgcUp e k))

theorem ddgc (e : n) : Continuous fun p => (J p).ddgc e :=
  continuous_matrix fun f b => continuous_finsetSum _ fun k _ =>
    (((((h.ddg e f).matrix_elem b k).mul (h.gcUp k)).add
      (((h.dg f).matrix_elem b k).mul (h.dgcUp e k))).add
      (((h.dg e).matrix_elem b k).mul (h.dgcUp f k))).add
      ((h.g.matrix_elem b k).mul (h.ddgcUp e f k))

theorem einM : Continuous fun p => (J p).einM :=
  h.ricM.sub ((continuous_const.mul (h.G.matrix_mul h.ricM.matrix_transpose).matrix_trace).smul h.g)

end JetCont

/-- The lower-order part of the subsidiary operator with independent `(c, ∂c)` (zero second jet):
`Σ_{ea} G^{ea} (∇_e∇_a c_b)|_{∂∂c = 0} + Ric^l{}_b c_l`. -/
def lowerOp (J : Jet3 n) (c : n → ℝ) (dc : n → n → ℝ) (b : n) : ℝ :=
  ∑ e, ∑ a, J.G e a * J.nnc c (Matrix.of dc) (fun _ => 0) e a b + J.ricC c b

theorem nnc_sub_ddc (J : Jet3 n) (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ)
    (e a b : n) : J.nnc c dc ddc e a b - ddc e a b = J.nnc c dc (fun _ => 0) e a b := by
  simp only [Jet3.nnc, Jet3.dnc, Matrix.sub_apply, Matrix.zero_apply]
  ring

theorem chrC_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) : J.chrC (r • c) = r • J.chrC c := by
  ext a b
  simp only [Jet3.chrC, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem nc_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) (dc : Matrix n n ℝ) :
    J.nc (r • c) (r • dc) = r • J.nc c dc := by
  rw [Jet3.nc, Jet3.nc, chrC_smul, smul_sub]

theorem dnc_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) (dc : Matrix n n ℝ) (e : n) :
    J.dnc (r • c) (r • dc) (fun _ => 0) e = r • J.dnc c dc (fun _ => 0) e := by
  ext a b
  simp only [Jet3.dnc, Matrix.sub_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.zero_apply, zero_sub, Matrix.neg_apply, Matrix.of_apply, mul_neg, Finset.mul_sum,
    neg_inj]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem nnc_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) (dc : Matrix n n ℝ) (e : n) :
    J.nnc (r • c) (r • dc) (fun _ => 0) e = r • J.nnc c dc (fun _ => 0) e := by
  rw [Jet3.nnc, Jet3.nnc, dnc_smul, nc_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_sub]

theorem ricC_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) (b : n) : J.ricC (r • c) b = r * J.ricC c b := by
  simp only [Jet3.ricC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem lowerOp_smul (J : Jet3 n) (r : ℝ) (c : n → ℝ) (dc : n → n → ℝ) (b : n) :
    lowerOp J (r • c) (r • dc) b = r * lowerOp J c dc b := by
  have e : Matrix.of (r • dc) = r • Matrix.of dc := rfl
  simp only [lowerOp, e, nnc_smul, ricC_smul, Matrix.smul_apply, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => by ring

end JetFam


namespace JetFam

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Type*} [TopologicalSpace X]

theorem JetCont.lowerOp {J : X → Jet3 n} (h : JetCont J) {c : X → n → ℝ} {dc : X → n → n → ℝ}
    (hc : Continuous c) (hdc : Continuous dc) (b : n) :
    Continuous fun p => lowerOp (J p) (c p) (dc p) b := by
  have hc' : ∀ l, Continuous fun p => c p l := fun l => (continuous_apply l).comp hc
  have hdc' : ∀ e l, Continuous fun p => dc p e l := fun e l =>
    (continuous_apply l).comp ((continuous_apply e).comp hdc)
  have hchrC : Continuous fun p => (J p).chrC (c p) :=
    continuous_matrix fun a b => continuous_finsetSum _ fun l _ =>
      ((h.chr a).matrix_elem l b).mul (hc' l)
  have hnc : Continuous fun p => (J p).nc (c p) (Matrix.of (dc p)) :=
    (continuous_matrix fun e l => hdc' e l).sub hchrC
  have hdnc : ∀ e, Continuous fun p => (J p).dnc (c p) (Matrix.of (dc p)) (fun _ => 0) e :=
    fun e => continuous_const.sub (continuous_matrix fun a b => continuous_finsetSum _ fun l _ =>
      (((h.dchr e a).matrix_elem l b).mul (hc' l)).add (((h.chr a).matrix_elem l b).mul (hdc' e l)))
  have hnnc : ∀ e, Continuous fun p => (J p).nnc (c p) (Matrix.of (dc p)) (fun _ => 0) e :=
    fun e => ((hdnc e).sub ((h.chr e).matrix_transpose.matrix_mul hnc)).sub (hnc.matrix_mul (h.chr e))
  unfold JetFam.lowerOp Jet3.ricC
  exact (continuous_finsetSum _ fun e _ => continuous_finsetSum _ fun a _ =>
    (h.G.matrix_elem e a).mul ((hnnc e).matrix_elem a b)).add
    (continuous_finsetSum _ fun l _ => (continuous_finsetSum _ fun k _ =>
      (h.G.matrix_elem l k).mul (h.ricM.matrix_elem k b)).mul (hc' l))

theorem JetCont.comp {Y : Type*} [TopologicalSpace Y] {J : X → Jet3 n} (h : JetCont J) {f : Y → X}
    (hf : Continuous f) : JetCont (fun y => J (f y)) :=
  ⟨h.g.comp hf, h.G.comp hf, fun a => (h.dg a).comp hf, fun a b => (h.ddg a b).comp hf,
    fun a b c => (h.dddg a b c).comp hf⟩

end JetFam

/-- A continuous function, homogeneous of degree one in a finite-dimensional variable, is
bounded by `C ‖e‖` uniformly on a compact parameter set. -/
theorem bound_of_homogeneous {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set X} (hK : IsCompact K) {φ : X → E → ℝ}
    (hφ : Continuous fun p : X × E => φ p.1 p.2) (hhom : ∀ x (r : ℝ) e, φ x (r • e) = r * φ x e) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ e, |φ x e| ≤ C * ‖e‖ := by
  obtain ⟨C0, hC0⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max C0 0, le_max_right _ _, fun x hx e => ?_⟩
  by_cases he : e = 0
  · subst he
    have := hhom x 0 0
    rw [zero_smul, zero_mul] at this
    rw [this]; simp
  · have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
    have hs : ‖e‖⁻¹ • e ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hC0 (x, ‖e‖⁻¹ • e) ⟨hx, hs⟩
    have h2 : φ x e = ‖e‖ * φ x (‖e‖⁻¹ • e) := by
      rw [hhom, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    rw [h2, abs_mul, abs_of_pos hn, mul_comm]
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) hn.le

/-- The clamp `t ↦ max 0 (min T t)` onto `[0, T]`. -/
def clampT (T t : ℝ) : ℝ := max 0 (min T t)

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

theorem clampT_of_mem {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampT T t = t := by
  unfold clampT; rw [min_eq_right ht.2, max_eq_right ht.1]

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) := by unfold clampT; fun_prop

theorem eventually_clampT {T t : ℝ} (ht : t ∈ Set.Ioo 0 T) : ∀ᶠ s in 𝓝 t, clampT T s = s := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact clampT_of_mem (Set.Ioo_subset_Icc_self hs)

/-- `γ^{ij}ξᵢξⱼ ≥ (7/10)|ξ|²` for a `3 × 3` matrix within `1/10` of the identity. -/
theorem coercive_of_near_id (e : Fin 3 → Fin 3 → ℝ)
    (he : ∀ i j, |e i j - if i = j then 1 else 0| ≤ 1 / 10) (ξ : Fin 3 → ℝ) :
    7 / 10 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, e i j * ξ i * ξ j := by
  have hd : ∀ i j, -(e i j - if i = j then 1 else 0) * ξ i * ξ j ≤
      1 / 10 * (ξ i ^ 2 + ξ j ^ 2) / 2 := fun i j =>
    TorusWaveEnergy.WaveData.abs_mul_le_half _ _ _ _ (by rw [abs_neg]; exact he i j)
  have h00 := hd 0 0; have h01 := hd 0 1; have h02 := hd 0 2
  have h10 := hd 1 0; have h11 := hd 1 1; have h12 := hd 1 2
  have h20 := hd 2 0; have h21 := hd 2 1; have h22 := hd 2 2
  simp only [Fin.sum_univ_three] at *
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  nlinarith

theorem minkowski_succ_succ (i j : Fin 3) :
    minkowski i.succ j.succ = if i = j then 1 else 0 := by
  unfold minkowski
  by_cases h : i = j
  · subst h; simp [Fin.succ_ne_zero]
  · simp [h, Fin.succ_inj]

theorem minkowski_zero_zero : minkowski 0 0 = -1 := by simp [minkowski]


/-! ### The subsidiary system as a linear wave system on `𝕋³` -/

namespace C3Field

variable {F : C3Field} {T : ℝ}

/-- The clamped jet family `p ↦ jetAt (clamp p.1) p.2`. -/
def jc (F : C3Field) (T : ℝ) (p : ℝ × T3) : Jet3 (Fin 4) := F.jetAt (clampT T p.1) p.2

theorem cont_clamp (hT : 0 ≤ T) {f : ℝ → T3 → MetricRec}
    (hf : ContinuousOn (fun p : ℝ × T3 => f p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)) :
    Continuous fun p : ℝ × T3 => f (clampT T p.1) p.2 :=
  hf.comp_continuous (((continuous_clampT T).comp continuous_fst).prodMk continuous_snd)
    fun p => ⟨clampT_mem hT p.1, Set.mem_univ _⟩

theorem Hyp.jetCont (h : F.Hyp T) (hT : 0 ≤ T) : JetFam.JetCont (F.jc T) := by
  have cl := fun {f : ℝ → T3 → MetricRec} hf => cont_clamp hT (f := f) hf
  have hQ := cl h.cQ
  have hg : Continuous fun p : ℝ × T3 => minkowski + F.Q (clampT T p.1) p.2 :=
    continuous_const.add hQ
  refine ⟨hg, ?_, fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun p => ?_
    have hd := h.det_ne (clampT_mem hT p.1) p.2
    exact ContinuousAt.comp (g := fun g : MetricRec => (Matrix.of g)⁻¹ i j)
      ((analyticAt_inv_entry _ hd i j).continuousAt) hg.continuousAt
  · refine Fin.cases ?_ (fun i => ?_) a
    · exact cl h.cV
    · exact cl (f := fun t x => F.Qd t i x) (h.cQd i)
  · refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · exact cl h.cA
    · exact cl (f := fun t x => F.Vd t j x) (h.cVd j)
    · exact cl (f := fun t x => F.Vd t i x) (h.cVd i)
    · exact cl (f := fun t x => F.Qdd t i j x) (h.cQdd i j)
  · refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
      refine Fin.cases ?_ (fun k => ?_) c
    · exact cl h.cAt
    · exact cl (f := fun t x => F.Ad t k x) (h.cAd k)
    · exact cl (f := fun t x => F.Ad t j x) (h.cAd j)
    · exact cl (f := fun t x => F.Vdd t j k x) (h.cVdd j k)
    · exact cl (f := fun t x => F.Ad t i x) (h.cAd i)
    · exact cl (f := fun t x => F.Vdd t i k x) (h.cVdd i k)
    · exact cl (f := fun t x => F.Vdd t i j x) (h.cVdd i j)
    · exact cl (f := fun t x => F.Qddd t i j k x) (h.cQddd i j k)

/-- The gauge covector `c = c(g)` of a field as a linear wave system on `𝕋³` (time clamped to
`[0, T]`): `a = -g^{00}`, `βⁱ = g^{0i}`, `γ^{ij} = g^{ij}`. -/
def waveData (F : C3Field) (T : ℝ) : TorusWaveEnergy.WaveData (Fin 4) where
  u t x b := (F.jc T (t, x)).gc b
  ut t x b := (F.jc T (t, x)).dgc 0 b
  utt t x b := (F.jc T (t, x)).ddgc 0 0 b
  ux t i x b := (F.jc T (t, x)).dgc i.succ b
  uxt t i x b := (F.jc T (t, x)).ddgc i.succ 0 b
  uxx t i j x b := (F.jc T (t, x)).ddgc i.succ j.succ b
  a t x := -(F.jc T (t, x)).G 0 0
  at' t x := -((F.jc T (t, x)).dG 0) 0 0
  β t i x := (F.jc T (t, x)).G 0 i.succ
  βdiv t i x := ((F.jc T (t, x)).dG i.succ) 0 i.succ
  γ t i j x := (F.jc T (t, x)).G i.succ j.succ
  γt t i j x := ((F.jc T (t, x)).dG 0) i.succ j.succ
  γx t i j x := ((F.jc T (t, x)).dG i.succ) i.succ j.succ
  L t x b := JetFam.lowerOp (F.jc T (t, x)) (F.jc T (t, x)).gc (fun e b => (F.jc T (t, x)).dgc e b) b

theorem jc_eq {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) : F.jc T (t, x) = F.jetAt t x := by
  simp only [jc, clampT_of_mem ht]

theorem jc_eventually {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : T3) :
    ∀ᶠ s in 𝓝 t, F.jc T (s, x) = F.jetAt s x := by
  filter_upwards [eventually_clampT ht] with s hs
  simp only [jc, hs]

/-- Principal decomposition of the subsidiary operator. -/
theorem principal_split {J : Jet3 (Fin 4)} (hv : J.Valid) (b : Fin 4)
    (hsub : J.boxC J.gc J.dgc J.ddgc b + J.ricC J.gc b = 0) :
    -J.G 0 0 * J.ddgc 0 0 b = 2 * ∑ i : Fin 3, J.G 0 i.succ * J.ddgc i.succ 0 b +
      ∑ i : Fin 3, ∑ j : Fin 3, J.G i.succ j.succ * J.ddgc i.succ j.succ b +
      JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b := by
  have hsplit : J.boxC J.gc J.dgc J.ddgc b = ∑ e, ∑ a, J.G e a * J.ddgc e a b +
      ∑ e, ∑ a, J.G e a * J.nnc J.gc J.dgc (fun _ => 0) e a b := by
    unfold Jet3.boxC
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← JetFam.nnc_sub_ddc]
    ring
  have hlow : JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b =
      ∑ e, ∑ a, J.G e a * J.nnc J.gc J.dgc (fun _ => 0) e a b + J.ricC J.gc b := rfl
  have hGs : ∀ i : Fin 3, J.G i.succ 0 = J.G 0 i.succ := fun i => by
    have := congrFun (congrFun hv.G_symm 0) i.succ
    simpa [Matrix.transpose_apply] using this
  have hds : ∀ i : Fin 3, J.ddgc 0 i.succ b = J.ddgc i.succ 0 b := fun i =>
    congrFun (Jet3.ddgc_swap hv 0 i.succ) b
  have hpr : ∑ e, ∑ a, J.G e a * J.ddgc e a b = J.G 0 0 * J.ddgc 0 0 b +
      2 * ∑ i : Fin 3, J.G 0 i.succ * J.ddgc i.succ 0 b +
      ∑ i : Fin 3, ∑ j : Fin 3, J.G i.succ j.succ * J.ddgc i.succ j.succ b := by
    simp only [Fin.sum_univ_succ (n := 3), hGs, hds, Finset.sum_add_distrib]
    ring
  rw [hsplit, hpr] at hsub
  rw [hlow]
  linarith

end C3Field


namespace C3Field

variable {F : C3Field} {T : ℝ}

theorem norm_le_sqrt_size (c : Fin 4 → ℝ) (dc : Fin 4 → Fin 4 → ℝ) :
    ‖((c, dc) : (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ))‖ ≤
      Real.sqrt (∑ b, (dc 0 b ^ 2 + ∑ i : Fin 3, dc i.succ b ^ 2 + c b ^ 2)) := by
  set S := ∑ b, (dc 0 b ^ 2 + ∑ i : Fin 3, dc i.succ b ^ 2 + c b ^ 2)
  have hterm : ∀ b, dc 0 b ^ 2 + ∑ i : Fin 3, dc i.succ b ^ 2 + c b ^ 2 ≤ S := fun b =>
    Finset.single_le_sum (f := fun b => dc 0 b ^ 2 + ∑ i : Fin 3, dc i.succ b ^ 2 + c b ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ b)
  have hsum : ∀ b, 0 ≤ ∑ i : Fin 3, dc i.succ b ^ 2 := fun b =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    have := hterm b; have := hsum b; have := sq_nonneg (dc 0 b); linarith
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun e => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    refine Fin.cases ?_ (fun i => ?_) e
    · have := hterm b; have := hsum b; have := sq_nonneg (c b); linarith
    · have h1 := Finset.single_le_sum (f := fun i : Fin 3 => dc i.succ b ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      have := hterm b; have := sq_nonneg (c b); have := sq_nonneg (dc 0 b)
      linarith

/-- The size of the coefficient derivatives `∂ₜg^{00}`, `∂ᵢg^{0i}`, `∂ₜg^{ij}`, `∂ᵢg^{ij}`. -/
def coefBound (F : C3Field) (T : ℝ) (p : ℝ × T3) : ℝ :=
  |((F.jc T p).dG 0) 0 0| + ∑ i : Fin 3, |((F.jc T p).dG i.succ) 0 i.succ|
    + ∑ i : Fin 3, ∑ j : Fin 3, |((F.jc T p).dG 0) i.succ j.succ|
    + ∑ i : Fin 3, ∑ j : Fin 3, |((F.jc T p).dG i.succ) i.succ j.succ|

theorem continuous_coefBound {F : C3Field} {T : ℝ} (hJ : JetFam.JetCont (F.jc T)) :
    Continuous (coefBound F T) := by
  have := hJ.dG
  unfold coefBound
  exact (((((this 0).matrix_elem 0 0).abs).add (continuous_finsetSum _ fun i _ =>
    ((this i.succ).matrix_elem 0 i.succ).abs)).add (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((this 0).matrix_elem i.succ j.succ).abs)).add
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((this i.succ).matrix_elem i.succ j.succ).abs)

theorem coefBound_parts (F : C3Field) (T : ℝ) (p : ℝ × T3) :
    0 ≤ ∑ i : Fin 3, |((F.jc T p).dG i.succ) 0 i.succ| ∧
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, |((F.jc T p).dG 0) i.succ j.succ| ∧
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, |((F.jc T p).dG i.succ) i.succ j.succ| :=
  ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _⟩

theorem coefBound_nonneg (F : C3Field) (T : ℝ) (p : ℝ × T3) : 0 ≤ coefBound F T p := by
  obtain ⟨h1, h2, h3⟩ := coefBound_parts F T p
  unfold coefBound
  have := abs_nonneg (((F.jc T p).dG 0) 0 0)
  linarith

theorem abs_dG00_le (F : C3Field) (T : ℝ) (p : ℝ × T3) :
    |((F.jc T p).dG 0) 0 0| ≤ coefBound F T p := by
  obtain ⟨h1, h2, h3⟩ := coefBound_parts F T p
  unfold coefBound; linarith

theorem abs_βdiv_le (F : C3Field) (T : ℝ) (p : ℝ × T3) (i : Fin 3) :
    |((F.jc T p).dG i.succ) 0 i.succ| ≤ coefBound F T p := by
  obtain ⟨h1, h2, h3⟩ := coefBound_parts F T p
  have h4 := Finset.single_le_sum (f := fun i : Fin 3 => |((F.jc T p).dG i.succ) 0 i.succ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have := abs_nonneg (((F.jc T p).dG 0) 0 0)
  unfold coefBound; linarith

theorem abs_γt_le (F : C3Field) (T : ℝ) (p : ℝ × T3) (i j : Fin 3) :
    |((F.jc T p).dG 0) i.succ j.succ| ≤ coefBound F T p := by
  obtain ⟨h1, h2, h3⟩ := coefBound_parts F T p
  have h4 := Finset.single_le_sum (f := fun j : Fin 3 => |((F.jc T p).dG 0) i.succ j.succ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h5 := Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3,
    |((F.jc T p).dG 0) i.succ j.succ|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)
  have := abs_nonneg (((F.jc T p).dG 0) 0 0)
  unfold coefBound; linarith

theorem abs_γx_le (F : C3Field) (T : ℝ) (p : ℝ × T3) (i j : Fin 3) :
    |((F.jc T p).dG i.succ) i.succ j.succ| ≤ coefBound F T p := by
  obtain ⟨h1, h2, h3⟩ := coefBound_parts F T p
  have h4 := Finset.single_le_sum (f := fun j : Fin 3 => |((F.jc T p).dG i.succ) i.succ j.succ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h5 := Finset.single_le_sum (f := fun i : Fin 3 => ∑ j : Fin 3,
    |((F.jc T p).dG i.succ) i.succ j.succ|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)
  have := abs_nonneg (((F.jc T p).dG 0) 0 0)
  unfold coefBound; linarith

theorem Hyp.lowerOp_bound (h : F.Hyp T) (hT : 0 ≤ T) (b : Fin 4) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ Set.Icc 0 T ×ˢ (Set.univ : Set T3),
      ∀ e : (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ), |JetFam.lowerOp (F.jc T p) e.1 e.2 b| ≤ C * ‖e‖ := by
  have hJ := h.jetCont hT
  have hc : Continuous fun q : (ℝ × T3) × ((Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ)) =>
      JetFam.lowerOp (F.jc T q.1) q.2.1 q.2.2 b :=
    JetFam.JetCont.lowerOp
        (J := fun q : (ℝ × T3) × ((Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ)) => F.jc T q.1)
        (c := fun q => q.2.1) (dc := fun q => q.2.2) (hJ.comp continuous_fst)
        continuous_snd.fst continuous_snd.snd b
  have hhom : ∀ (p : ℝ × T3) (r : ℝ) (e : (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ)),
      JetFam.lowerOp (F.jc T p) (r • e).1 (r • e).2 b = r * JetFam.lowerOp (F.jc T p) e.1 e.2 b :=
    fun p r e => JetFam.lowerOp_smul _ r _ _ b
  have hK : IsCompact (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set T3)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC0, hC⟩ := bound_of_homogeneous (E := (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ)) hK
    (φ := fun p e => JetFam.lowerOp (F.jc T p) e.1 e.2 b) hc hhom
  exact ⟨C, hC0, fun p hp e => hC p hp e⟩

set_option maxHeartbeats 1000000 in
/-- **The subsidiary system of a solution is a linear wave system with uniform bounds.** -/
theorem Hyp.waveSolves (h : F.Hyp T) (hT : 0 ≤ T) :
    ∃ M, (F.waveData T).Solves T (9 / 10) (7 / 10) M := by
  have hJ := h.jetCont hT
  have hK : IsCompact (Set.Icc 0 T ×ˢ (Set.univ : Set T3)) := isCompact_Icc.prod isCompact_univ
  have hmem : ∀ t ∈ Set.Icc 0 T, ∀ x : T3, ((t, x) : ℝ × T3) ∈ Set.Icc 0 T ×ˢ Set.univ :=
    fun t ht x => ⟨ht, Set.mem_univ _⟩
  -- coefficient bounds
  obtain ⟨M1, hM1b⟩ := hK.exists_bound_of_continuousOn (f := coefBound F T)
    (continuous_coefBound hJ).continuousOn
  have hB : ∀ t ∈ Set.Icc 0 T, ∀ x, coefBound F T (t, x) ≤ M1 := fun t ht x =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM1b (t, x) (hmem t ht x))
  have hφ := fun b => h.lowerOp_bound hT b
  choose C hC0 hC using hφ
  set M2 := ∑ b, C b ^ 2
  have hM2 : 0 ≤ M2 := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hM1 : 0 ≤ M1 := (coefBound_nonneg F T (0, 0)).trans (hB 0 ⟨le_rfl, hT⟩ 0)
  refine ⟨M1 + M2, ?_⟩
  -- interior identities
  have hval : ∀ t ∈ Set.Icc 0 T, ∀ x, (F.jc T (t, x)).Valid := fun t ht x => by
    rw [jc_eq ht]; exact h.valid ht x
  have hvalc : ∀ t x, (F.jc T (t, x)).Valid := fun t x => h.valid (clampT_mem hT t) x
  exact {
    cont_u := fun b => hJ.gc b
    cont_ut := fun b => hJ.dgc.matrix_elem 0 b
    cont_utt := fun b => (hJ.ddgc 0).matrix_elem 0 b
    cont_ux := fun i b => hJ.dgc.matrix_elem i.succ b
    cont_uxt := fun i b => (hJ.ddgc i.succ).matrix_elem 0 b
    cont_uxx := fun i j b => (hJ.ddgc i.succ).matrix_elem j.succ b
    cont_a := (hJ.G.matrix_elem 0 0).neg
    cont_at := ((hJ.dG 0).matrix_elem 0 0).neg
    cont_β := fun i => hJ.G.matrix_elem 0 i.succ
    cont_βdiv := fun i => (hJ.dG i.succ).matrix_elem 0 i.succ
    cont_γ := fun i j => hJ.G.matrix_elem i.succ j.succ
    cont_γt := fun i j => (hJ.dG 0).matrix_elem i.succ j.succ
    cont_γx := fun i j => (hJ.dG i.succ).matrix_elem i.succ j.succ
    cont_L := fun b => (hJ.lowerOp (continuous_pi fun b => hJ.gc b) hJ.dgc b)
    dt_u := fun t ht x b => by
      have := (h.pathDeriv_time ht x).gc b
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((jc_eventually (F := F) ht x).mono fun s hs => by simp only [hs])
    dt_ut := fun t ht x b => by
      have := (h.pathDeriv_time ht x).dgc 0 b
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((jc_eventually (F := F) ht x).mono fun s hs => by simp only [hs])
    dt_ux := fun t ht i x b => by
      have := (h.pathDeriv_time ht x).dgc i.succ b
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      rw [← congrFun (Jet3.ddgc_swap (h.valid (Set.Ioo_subset_Icc_self ht) x) 0 i.succ) b]
      exact this.congr_of_eventuallyEq ((jc_eventually (F := F) ht x).mono fun s hs => by simp only [hs])
    dt_a := fun t ht x => by
      have := ((h.pathDeriv_time ht x).G 0 0).neg
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((jc_eventually (F := F) ht x).mono fun s hs => by simp only [hs, Pi.neg_apply])
    dt_γ := fun t ht i j x => by
      have := (h.pathDeriv_time ht x).G i.succ j.succ
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      exact this.congr_of_eventuallyEq ((jc_eventually (F := F) ht x).mono fun s hs => by simp only [hs])
    dx_u := fun t ht i b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).gc b
      simpa only [waveData, jc, jetAt_shift_zero] using this
    dx_ut := fun t ht i b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).dgc 0 b
      simpa only [waveData, jc, jetAt_shift_zero] using this
    dx_ux := fun t ht i j b x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).dgc j.succ b
      simpa only [waveData, jc, jetAt_shift_zero] using this
    dx_β := fun t ht i x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).G 0 i.succ
      simpa only [waveData, jc, jetAt_shift_zero] using this
    dx_γ := fun t ht i j x => by
      have := (h.pathDeriv_space (clampT_mem hT t) x i).G i.succ j.succ
      simpa only [waveData, jc, jetAt_shift_zero] using this
    γ_symm := fun t i j x => by
      have := congrFun (congrFun (hvalc t x).G_symm i.succ) j.succ
      simpa [waveData, Matrix.transpose_apply] using this.symm
    eqn := fun t ht x b => by
      have hsub := h.subsidiary ht x b
      have := principal_split (h.valid (Set.Ioo_subset_Icc_self ht) x) b hsub
      simp only [waveData, jc_eq (Set.Ioo_subset_Icc_self ht)]
      linarith
    coer_a := fun t ht x => by
      have := h.chart t ht x 0 0
      simp only [waveData, jc_eq ht]
      rw [minkowski_zero_zero] at this
      have := (abs_le.mp this).2
      show 9 / 10 ≤ -(F.jetAt t x).G 0 0
      simp only [jetAt]
      linarith
    coer_γ := fun t ht x ξ => by
      simp only [waveData, jc_eq ht]
      exact coercive_of_near_id (fun i j => (F.jetAt t x).G i.succ j.succ)
        (fun i j => by
          have := h.chart t ht x i.succ j.succ
          rwa [minkowski_succ_succ] at this) ξ
    bnd_at := fun t ht x => by
      simp only [waveData, abs_neg]
      exact (abs_dG00_le F T (t, x)).trans ((hB t ht x).trans (le_add_of_nonneg_right hM2))
    bnd_βdiv := fun t ht i x =>
      (abs_βdiv_le F T (t, x) i).trans ((hB t ht x).trans (le_add_of_nonneg_right hM2))
    bnd_γt := fun t ht i j x =>
      (abs_γt_le F T (t, x) i j).trans ((hB t ht x).trans (le_add_of_nonneg_right hM2))
    bnd_γx := fun t ht i j x =>
      (abs_γx_le F T (t, x) i j).trans ((hB t ht x).trans (le_add_of_nonneg_right hM2))
    bnd_L := fun t ht x => by
      set J := F.jc T (t, x)
      set S := ∑ b, (J.dgc 0 b ^ 2 + ∑ i : Fin 3, J.dgc i.succ b ^ 2 + J.gc b ^ 2)
      have hS : 0 ≤ S := Finset.sum_nonneg fun b _ => by positivity
      have hn := norm_le_sqrt_size J.gc (fun e b => J.dgc e b)
      have hLb : ∀ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2 ≤ C b ^ 2 * S := by
        intro b
        have h1 := hC b (t, x) (hmem t ht x) (J.gc, fun e b => J.dgc e b)
        have h2 : |JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b| ≤ C b * Real.sqrt S :=
          h1.trans (mul_le_mul_of_nonneg_left hn (hC0 b))
        have h3 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
        rw [mul_pow, Real.sq_sqrt hS] at h3
        exact h3
      have : ∑ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2 ≤ M2 * S := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun b _ => hLb b
      simp only [waveData]
      calc ∑ b, (JetFam.lowerOp J J.gc (fun e b => J.dgc e b) b) ^ 2 ≤ M2 * S := this
        _ ≤ (M1 + M2) * S := by nlinarith }

end C3Field


/-! ### Harmonic gauge propagation and the vacuum equation -/

namespace C3Field

variable {F : C3Field} {T : ℝ}

theorem jet3_eq_of_twoJet {n : Type*} {J J' : Jet3 n} (hg : J.g = J'.g) (hG : J.G = J'.G)
    (hdg : J.dg = J'.dg) (hddg : J.ddg = J'.ddg) : J = ⟨J'.g, J'.G, J'.dg, J'.ddg, J.dddg⟩ := by
  cases J; cases J'; simp_all

/-- The jet at `t = 0` is a unit-lapse zero-shift slice jet of the slice data `S`
(on the 2-jet). -/
def SliceAt (F : C3Field) (S : SliceData) (x : T3) : Prop :=
  (F.jetAt 0 x).g = S.jet.g ∧ (F.jetAt 0 x).G = S.jet.G ∧ (F.jetAt 0 x).dg = S.jet.dg ∧
    (F.jetAt 0 x).ddg = S.jet.ddg

/-- Initial data: at every point the initial jet is the slice jet of valid data satisfying the
harmonic initialization `eq:supp-open-harmonic-initial` and the vacuum constraints of
`eq:main-open-data-class`. -/
def InitData (F : C3Field) : Prop :=
  ∀ x, ∃ S : SliceData, S.Valid ∧ S.HarmonicInit ∧ S.hamC = 0 ∧ (∀ i, S.momC i = 0) ∧
    F.SliceAt S x

theorem gc_slice {S : SliceData} {x : T3} (hx : F.SliceAt S x) : (F.jetAt 0 x).gc = S.jet.gc := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rw [jet3_eq_of_twoJet h1 h2 h3 h4]
  rfl

theorem dgc_slice {S : SliceData} {x : T3} (hx : F.SliceAt S x) :
    (F.jetAt 0 x).hM = S.jet.hM ∧ (F.jetAt 0 x).einM = S.jet.einM := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rw [jet3_eq_of_twoJet h1 h2 h3 h4]
  exact ⟨rfl, rfl⟩

theorem hM_zero_covector {n : Type*} [Fintype n] [DecidableEq n] (J : Jet3 n) :
    J.hM (fun _ => 0) 0 = 0 := by
  have hc : J.chrC (fun _ => 0) = 0 := by ext a b; simp [Jet3.chrC]
  have hn : J.nc (fun _ => 0) 0 = 0 := by rw [Jet3.nc, hc, sub_zero]
  simp [Jet3.hM, Jet3.trN, hn]

/-- **Initial gauge**: the harmonic initialization and the constraints give `c(0) = 0` and
`∂ₜc(0) = 0`. -/
theorem Hyp.initial_gauge (h : F.Hyp T) (hT : 0 ≤ T) (hI : F.InitData) (x : T3) :
    (∀ b, (F.jetAt 0 x).gc b = 0) ∧ ∀ b, (F.jetAt 0 x).dgc 0 b = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hc0 : ∀ y b, (F.jetAt 0 y).gc b = 0 := by
    intro y b
    obtain ⟨S, hS, hH, -, -, hy⟩ := hI y
    rw [gc_slice hy]
    exact SliceData.gc_harmonicInit hS hH b
  refine ⟨hc0 x, ?_⟩
  obtain ⟨S, hS, hH, hham, hmom, hx⟩ := hI x
  -- tangential derivatives vanish
  have htan : ∀ (k : Fin 3) b, (F.jetAt 0 x).dgc k.succ b = 0 := by
    intro k b
    have h1 := (h.pathDeriv_space h0 x k).gc b
    have h2 : HasDerivAt (fun σ => (F.jetAt 0 (x + lineShift k σ)).gc b) 0 0 := by
      simp only [hc0]; exact hasDerivAt_const _ _
    have := h1.unique h2
    simpa only [jetAt_shift_zero] using this
  -- `𝓗₀_b = G₀_b` since the residual vanishes
  have hres := h.resM_eq_zero h0 x
  have hHE : ∀ b, (F.jetAt 0 x).hM (F.jetAt 0 x).gc (F.jetAt 0 x).dgc 0 b =
      (F.jetAt 0 x).einM 0 b := by
    intro b
    have := congrFun (congrFun hres 0) b
    simp only [Jet3.resM, Matrix.sub_apply, Matrix.zero_apply] at this
    linarith
  obtain ⟨ehM, eein⟩ := dgc_slice hx
  have hc : (F.jetAt 0 x).gc = fun _ => 0 := funext fun b => hc0 x b
  intro b
  refine Fin.cases ?_ (fun k => ?_) b
  · have e1 := hHE 0
    rw [ehM, eein, SliceData.einM_zero_zero hS, hham, SliceData.hM_zero_zero, hc] at e1
    simp only [htan, mul_zero, Finset.sum_const_zero, mul_zero, add_zero] at e1
    linarith
  · have e1 := hHE k.succ
    rw [ehM, eein, SliceData.einM_zero_succ hS, hmom, SliceData.hM_zero_succ hS, hc] at e1
    simp only [htan, mul_zero, Finset.sum_const_zero, add_zero, sub_zero, neg_zero] at e1
    linarith

/-- **Propagation of the harmonic gauge**: the gauge covector of a classical solution of the
harmonic reduced equation with harmonic initial data satisfying the vacuum constraints vanishes on
`[0, T] × 𝕋³`. -/
theorem Hyp.gc_eq_zero (h : F.Hyp T) (hT : 0 ≤ T) (hI : F.InitData) :
    ∀ t ∈ Set.Icc 0 T, ∀ x b, (F.jetAt t x).gc b = 0 := by
  obtain ⟨M, hM⟩ := h.waveSolves hT
  have hz := TorusWaveEnergy.WaveData.eq_zero_of_zero_data hM (by norm_num) (by norm_num)
    (fun x b => by
      simp only [waveData, jc_eq (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Set.Icc 0 T)]
      exact (h.initial_gauge hT hI x).1 b)
    (fun x b => by
      simp only [waveData, jc_eq (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Set.Icc 0 T)]
      exact (h.initial_gauge hT hI x).2 b)
  intro t ht x b
  have := hz t ht x b
  simpa only [waveData, jc_eq ht] using this

/-- **The vacuum Einstein equation** `G(g) = 0` on `[0, T] × 𝕋³` (and `c(g) = 0`). -/
theorem Hyp.einM_eq_zero (h : F.Hyp T) (hT : 0 < T) (hI : F.InitData) :
    ∀ t ∈ Set.Icc 0 T, ∀ x, (F.jetAt t x).einM = 0 := by
  have hc := h.gc_eq_zero hT.le hI
  -- interior points
  have hint : ∀ t ∈ Set.Ioo 0 T, ∀ x, (F.jetAt t x).einM = 0 := by
    intro t ht x
    have htc := Set.Ioo_subset_Icc_self ht
    have hdc : (F.jetAt t x).dgc = 0 := by
      ext e b
      refine Fin.cases ?_ (fun k => ?_) e
      · have h1 := (h.pathDeriv_time ht x).gc b
        have h2 : HasDerivAt (fun τ => (F.jetAt τ x).gc b) 0 t := by
          refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
          filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
          exact hc τ (Set.Ioo_subset_Icc_self hτ) x b
        exact h1.unique h2
      · have h1 := (h.pathDeriv_space htc x k).gc b
        have h2 : HasDerivAt (fun σ => (F.jetAt t (x + lineShift k σ)).gc b) 0 0 := by
          simp only [hc t htc]; exact hasDerivAt_const _ _
        have := h1.unique h2
        simp only [jetAt_shift_zero] at this
        rw [this, Matrix.zero_apply]
    have hgc : (F.jetAt t x).gc = fun _ => 0 := funext fun b => hc t htc x b
    have hres := h.resM_eq_zero htc x
    rw [Jet3.resM, hgc, hdc, hM_zero_covector, sub_zero] at hres
    exact hres
  -- closure in time
  intro t ht x
  have hJ := h.jetCont hT.le
  have hcont : Continuous fun τ : ℝ => (F.jc T (τ, x)).einM :=
    hJ.einM.comp (continuous_id.prodMk continuous_const)
  have heq : Set.EqOn (fun τ : ℝ => (F.jc T (τ, x)).einM) (fun _ => 0) (Set.Ioo 0 T) :=
    fun τ hτ => by
      simp only
      rw [jc_eq (Set.Ioo_subset_Icc_self hτ)]
      exact hint τ hτ x
  have hcl := heq.closure hcont continuous_const
  rw [closure_Ioo hT.ne] at hcl
  have := hcl ht
  simp only at this
  rwa [jc_eq ht] at this

end C3Field


/-! ### Symmetry of the Ricci tensor and of the normal row -/

namespace JetFam

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The first Bianchi identity `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0` (torsion-free jet). -/
theorem riem_cyclic {J : Jet3 n} (hv : J.Valid) (μ ν σ ρ : n) :
    J.riem μ ν ρ σ + J.riem ν σ ρ μ + J.riem σ μ ρ ν = 0 := by
  simp only [Jet3.riem, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  rw [Jet3.dchr_apply_comm hv μ ν ρ σ, Jet3.dchr_apply_comm hv ν μ ρ σ,
    Jet3.dchr_apply_comm hv ν σ ρ μ, Jet3.dchr_apply_comm hv σ ν ρ μ]
  have e1 : ∑ m, J.chr μ ρ m * J.chr ν m σ = ∑ m, J.chr μ ρ m * J.chr σ m ν :=
    Finset.sum_congr rfl fun m _ => by rw [Jet3.chr_apply_comm hv ν m σ]
  have e2 : ∑ m, J.chr ν ρ m * J.chr μ m σ = ∑ m, J.chr ν ρ m * J.chr σ m μ :=
    Finset.sum_congr rfl fun m _ => by rw [Jet3.chr_apply_comm hv μ m σ]
  have e3 : ∑ m, J.chr σ ρ m * J.chr ν m μ = ∑ m, J.chr σ ρ m * J.chr μ m ν :=
    Finset.sum_congr rfl fun m _ => by rw [Jet3.chr_apply_comm hv ν m μ]
  rw [e1, e2, e3]
  ring

theorem trace_riem {J : Jet3 n} (hv : J.Valid) (a b : n) : Matrix.trace (J.riem a b) = 0 := by
  have hR : J.riem a b = J.G * J.lowRiem a b := by
    rw [← Jet3.metric_mul_riem hv, ← Matrix.mul_assoc, hv.Gg, Matrix.one_mul]
  have hP := Jet3.lowRiem_antisymm hv a b
  have h1 : Matrix.trace (J.G * J.lowRiem a b) = -Matrix.trace (J.G * J.lowRiem a b) := by
    calc Matrix.trace (J.G * J.lowRiem a b)
        = Matrix.trace ((J.G * J.lowRiem a b)ᵀ) := (Matrix.trace_transpose _).symm
      _ = Matrix.trace ((J.lowRiem a b)ᵀ * J.Gᵀ) := by rw [Matrix.transpose_mul]
      _ = -Matrix.trace (J.G * J.lowRiem a b) := by
          rw [hP, hv.G_symm, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  rw [hR]; linarith

/-- **The Ricci tensor of a metric jet is symmetric.** -/
theorem ricM_symm {J : Jet3 n} (hv : J.Valid) (s b : n) : J.ricM s b = J.ricM b s := by
  have h := fun l => riem_cyclic hv l b s l
  have hs : ∑ l, (J.riem l b l s + J.riem b s l l + J.riem s l l b) = 0 :=
    Finset.sum_eq_zero fun l _ => h l
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have htr : ∑ l, J.riem b s l l = 0 := by
    have := trace_riem hv b s
    simpa [Matrix.trace, Matrix.diag] using this
  have hneg : ∑ l, J.riem s l l b = -∑ l, J.riem l s l b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Jet3.riem_antisymm, Matrix.neg_apply]
  simp only [Jet3.ricM, Matrix.of_apply]
  linarith

end JetFam

/-- The normal row is symmetric for symmetric jets: the ten upper components determine it. -/
theorem normalRow_symm (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (hq : ∀ μ ν, q μ ν = q ν μ)
    (hdet : (Matrix.of (minkowski + q)).det ≠ 0) (hv : ∀ μ ν, v μ ν = v ν μ)
    (hqd : ∀ i μ ν, qd i μ ν = qd i ν μ)
    (hw : ∀ μ ν, w μ ν = w ν μ) (hvd : ∀ i μ ν, vd i μ ν = vd i ν μ)
    (hqdd : ∀ i j μ ν, qdd i j μ ν = qdd i j ν μ) (hqdd' : ∀ i j, qdd i j = qdd j i) (μ ν : Fin 4) :
    normalRow q v w qd vd qdd μ ν = normalRow q v w qd vd qdd ν μ := by
  have hg : ∀ μ ν, (minkowski + q) μ ν = (minkowski + q) ν μ := by
    intro μ ν; simp only [Pi.add_apply, hq μ ν, C3Field.minkowski_symm μ ν]
  have hvalid : ArraysValid (minkowski + q) (recInv (minkowski + q)) (metricJet (v, qd))
      (ddArr w vd qdd) := by
    refine ⟨recInv_hinv hdet, hg, recInv_symm hg, fun α a b => ?_, fun α β μ ν => ?_,
      fun α β μ ν => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) α
      · simp [metricJet, hv a b]
      · simp [metricJet, hqd i a b]
    · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
        simp [hqdd']
    · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
        simp [hw μ ν, hvd _ μ ν, hqdd _ _ μ ν]
  rw [normalRow_eq q v w qd vd qdd hq hdet hw hvd hqdd hqdd' μ ν,
    normalRow_eq q v w qd vd qdd hq hdet hw hvd hqdd hqdd' ν μ,
    ← ricM_ofArrays hvalid, ← ricM_ofArrays hvalid, JetFam.ricM_symm hvalid.valid μ ν]
  simp only [symDefect]
  ring


namespace C3Field

variable {F : C3Field} {T : ℝ}

theorem Hyp.arraysValid (h : F.Hyp T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : T3) :
    ArraysValid (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
      (metricJet (F.V t x, fun i => F.Qd t i x))
      (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x)) := by
  have hdet := h.det_ne ht x
  have hg : ∀ μ ν, (minkowski + F.Q t x) μ ν = (minkowski + F.Q t x) ν μ := by
    intro μ ν; simp only [Pi.add_apply, h.sQ t x μ ν, minkowski_symm μ ν]
  refine ⟨recInv_hinv hdet, hg, recInv_symm hg, fun α a b => ?_, fun α β μ ν => ?_,
    fun α β μ ν => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) α
    · simp [metricJet, h.sV t x a b]
    · simp [metricJet, h.sQd t i x a b]
  · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
      simp [h.iQdd t]
  · refine Fin.cases ?_ (fun i => ?_) α <;> refine Fin.cases ?_ (fun j => ?_) β <;>
      simp [h.sA t x μ ν, h.sVd t _ x μ ν, h.sQdd t _ _ x μ ν]

/-- **The vacuum Einstein equation for the metric 2-jet of the field** (in the conventions of
`HarmonicDefect.einstein`): `G_{μν}(g) = 0` on `[0, T] × 𝕋³`. -/
theorem Hyp.einstein_eq_zero (h : F.Hyp T) (hT : 0 < T) (hI : F.InitData) :
    ∀ t ∈ Set.Icc 0 T, ∀ x μ ν, einstein (minkowski + F.Q t x) (recInv (minkowski + F.Q t x))
      (metricJet (F.V t x, fun i => F.Qd t i x))
      (ddArr (F.A t x) (fun i => F.Vd t i x) (fun i j => F.Qdd t i j x)) μ ν = 0 := by
  intro t ht x μ ν
  rw [← einM_ofArrays (h.arraysValid ht x)]
  have := congrFun (congrFun (h.einM_eq_zero hT hI t ht x) μ) ν
  exact this

end C3Field

end

end RenewalGeometry.HarmonicGaugePropagation
