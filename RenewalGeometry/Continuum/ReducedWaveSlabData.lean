/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabCoefficientCalculus

/-!
# The reduced harmonic-gauge wave system on `[0, T] × 𝕋³` and its normal form

Encoding of `eq:reduced-wave` of the Einstein–Standard-Model action-closure manuscript (section
"Common-slab metric stability", `thm:hyperbolic`), and the single-metric consequences of the
hypotheses of `thm:hyperbolic` used by the difference estimate.

## Encoding (`Σ = 𝕋³` disclosed; fields smooth and `ℤ³`-periodic on `ℝ^{1+3}`)

* A metric is a family `g : Idx → ℝ^{1+3} → ℝ`, `Idx = Fin 4 × Fin 4` (`g (a, b) = g_{ab}`), with an
  inverse-metric field `gi a b = g^{ab}` (`MetricHyp.inv`: `g · g⁻¹ = 1` on the slab).
* The nonlinearity `𝒩(g, ∂g)` is a **polynomial** `Np c` in the inverse metric entries, the metric
  entries, the first derivatives `∂_μ g_c` and finitely many fixed smooth periodic background fields
  `θ` (the fixed background-connection terms), evaluated pointwise (`Nfield`) — the reduced
  Einstein(-matter) operator is of this form (`g^{-1} g^{-1} ∂g ∂g` plus background terms).
* `MetricHyp`: the reduced wave equation `g^{αβ}∂_α∂_β g_c = 𝒩_c(g, ∂g) + 𝒮_c` on the slab
  (`eq:reduced-wave`); uniform hyperbolicity with respect to the common time function `t = x⁰`
  (`g^{00} ≤ -a₀`, `g^{ij}ξᵢξⱼ ≥ λ|ξ|²`: `∂ₜ` uniformly timelike and the slices uniformly
  spacelike), the uniform inverse-metric bound `|g^{αβ}| ≤ Λ`, and the a-priori bound
  `eq:hyperbolic-bound` `Q_s(g_c)(t) ≤ K₀`, `Q_{s-1}(∂ₜg_c)(t) ≤ K₀` (classical `L^∞_t H^s`,
  `L^∞_t H^{s-1}` bounds).

## Consequences

* `lapseInv g⁻¹ = cutInv a₀ ∘ g^{00}` (a smooth function equal to `1/g^{00}` on the slab),
  `betaF`, `gammaF`: the normal-form coefficients `βⁱ = -½ q (g^{0i} + g^{i0})`,
  `γ^{ij} = -½ q (g^{ij} + g^{ji})`; **`normal_form`**: on the slab
  `∂ₜ²g_c = 2βⁱ∂ᵢ∂ₜg_c + γ^{ij}∂ᵢ∂ⱼg_c + q(𝒩_c + 𝒮_c)`.
* `MetricHyp.derivBound_g`, `derivBound_gi`, `derivBound_q`, `derivBound_beta`,
  `derivBound_gamma`: `L^∞_t W^{s-2,∞}_x` bounds with constants depending only on the common
  constants; `MetricHyp.coer_gamma`: `γ` is `λ/Λ`-coercive; `MetricHyp.abs_pd_gamma_time`: a bound
  for `∂ₜγ`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

/-- Space-time `ℝ^{1+3}`. -/
abbrev X := ST 3

/-- Metric components `g_{ab}`. -/
abbrev Idx := Fin 4 × Fin 4

/-- The variables of the nonlinearity: inverse-metric entries, metric entries, first derivatives
`∂_μ g_c`, background fields. -/
abbrev NV (κ : Type) := (Fin 4 × Fin 4) ⊕ (Idx ⊕ ((Idx × Fin 4) ⊕ κ))

variable {κ : Type} [Fintype κ]

/-- The values of the variables of the nonlinearity. -/
def nvals (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (θ : κ → X → ℝ) : NV κ → X → ℝ
  | .inl ab => gi ab.1 ab.2
  | .inr (.inl c) => g c
  | .inr (.inr (.inl cμ)) => pd (g cμ.1) cμ.2
  | .inr (.inr (.inr j)) => θ j

/-- The nonlinearity `𝒩_c(g, ∂g)`: a polynomial in `g^{-1}`, `g`, `∂g` and fixed background
fields, evaluated pointwise. -/
def Nfield (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ) (g : Idx → X → ℝ)
    (gi : Fin 4 → Fin 4 → X → ℝ) (c : Idx) : X → ℝ :=
  evalF (nvals g gi θ) (Np c)

/-- The slab `[0, T] × ℝ³`. -/
def InSlab (T : ℝ) (x : X) : Prop := x 0 ∈ Icc 0 T

/-- **The hypotheses of `thm:hyperbolic` on one metric**, with the common constants:
`s` the Sobolev order, `T` the slab length, `a₀, λ` the hyperbolicity constants, `Λ` the
inverse-metric bound, `K₀` the a-priori `H^s` bound. -/
structure MetricHyp (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ) (s : ℕ)
    (T a0 lam Λ K0 : ℝ) (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (S : Idx → X → ℝ) :
    Prop where
  sg : ∀ c, ContDiff ℝ ∞ (g c)
  sgi : ∀ a b, ContDiff ℝ ∞ (gi a b)
  sS : ∀ c, ContDiff ℝ ∞ (S c)
  sθ : ∀ j, ContDiff ℝ ∞ (θ j)
  pg : ∀ c, IsSPeriodic (g c)
  pgi : ∀ a b, IsSPeriodic (gi a b)
  pS : ∀ c, IsSPeriodic (S c)
  pθ : ∀ j, IsSPeriodic (θ j)
  /-- `g · g⁻¹ = 1` on the slab. -/
  inv : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, ∑ c, g (a, c) x * gi c b x = if a = b then 1 else 0
  /-- `∂ₜ` is uniformly timelike: `g^{00} ≤ -a₀`. -/
  hyp0 : ∀ x : X, x 0 ∈ Icc 0 T → gi 0 0 x ≤ -a0
  /-- The slices are uniformly spacelike: `g^{ij}ξᵢξⱼ ≥ λ|ξ|²`. -/
  hypS : ∀ x : X, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j
  /-- The uniform inverse-metric bound. -/
  bnd : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, |gi a b x| ≤ Λ
  /-- `eq:hyperbolic-bound`: `‖g‖_{L^∞_t H^s} + ‖∂ₜg‖_{L^∞_t H^{s-1}} ≤ K₀` (squared classical
  norms on the slices). -/
  hsg : ∀ t ∈ Icc 0 T, ∀ c, Q s (g c) t ≤ K0
  hst : ∀ t ∈ Icc 0 T, ∀ c, Q (s - 1) (pd (g c) 0) t ≤ K0
  /-- `eq:reduced-wave`: `g^{αβ}∂_α∂_β g_c = 𝒩_c(g, ∂g) + 𝒮_c` on the slab. -/
  eqn : ∀ x : X, x 0 ∈ Icc 0 T → ∀ c,
    ∑ α : Fin 4, ∑ β : Fin 4, gi α β x * pd (pd (g c) β) α x = Nfield Np θ g gi c x + S c x

/-! ### The normal-form coefficients -/

/-- `q = 1/g^{00}` on the slab (a smooth cut-off reciprocal, `a₀ > 0`). -/
def lapseInv (a0 : ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (x : X) : ℝ := cutInv a0 (gi 0 0 x)

/-- `βⁱ = -½ q (g^{0i} + g^{i0})`. -/
def betaF (q : X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (i : Fin 3) (x : X) : ℝ :=
  -(1 / 2) * (q x * (gi 0 i.succ x + gi i.succ 0 x))

/-- `γ^{ij} = -½ q (g^{ij} + g^{ji})`. -/
def gammaF (q : X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (i j : Fin 3) (x : X) : ℝ :=
  -(1 / 2) * (q x * (gi i.succ j.succ x + gi j.succ i.succ x))

theorem gammaF_symm (q : X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (i j : Fin 3) (x : X) :
    gammaF q gi i j x = gammaF q gi j i x := by
  unfold gammaF; ring

/-- The algebra of the normal form. -/
theorem normal_form_alg (q g00 utt R : ℝ) (b0 bi0 uti : Fin 3 → ℝ) (G U : Fin 3 → Fin 3 → ℝ)
    (hU : ∀ i j, U i j = U j i) (hq : q * g00 = 1)
    (h : g00 * utt + ∑ j, b0 j * uti j + ∑ i, bi0 i * uti i + ∑ i, ∑ j, G i j * U i j = R) :
    utt = 2 * ∑ i, (-(1 / 2) * (q * (b0 i + bi0 i))) * uti i +
      ∑ i, ∑ j, (-(1 / 2) * (q * (G i j + G j i))) * U i j + q * R := by
  have hswap : ∑ i, ∑ j, G j i * U i j = ∑ i, ∑ j, G i j * U i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hU]
  have e1 : ∑ i, ∑ j, (-(1 / 2) * (q * (G i j + G j i))) * U i j =
      -(1 / 2) * q * (∑ i, ∑ j, G i j * U i j + ∑ i, ∑ j, G j i * U i j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : 2 * ∑ i, (-(1 / 2) * (q * (b0 i + bi0 i))) * uti i =
      -q * (∑ j, b0 j * uti j + ∑ i, bi0 i * uti i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, hswap]
  have : utt = q * (g00 * utt) := by rw [← mul_assoc, hq, one_mul]
  rw [this, ← h]
  ring

namespace MetricHyp

variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {s : ℕ} {T a0 lam Λ K0 : ℝ}
  {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}

theorem sq (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) :
    ContDiff ℝ ∞ (lapseInv a0 gi) :=
  (contDiff_cutInv ha).comp (h.sgi 0 0)

theorem pq (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) : IsSPeriodic (lapseInv a0 gi) :=
  fun k x => by simp only [lapseInv, h.pgi 0 0 k x]

theorem q_eq (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {x : X}
    (hx : x 0 ∈ Icc 0 T) : lapseInv a0 gi x = (gi 0 0 x)⁻¹ :=
  cutInv_eq ha (h.hyp0 x hx)

theorem q_mul (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {x : X}
    (hx : x 0 ∈ Icc 0 T) : lapseInv a0 gi x * gi 0 0 x = 1 := by
  rw [h.q_eq ha hx]
  exact inv_mul_cancel₀ (by have := h.hyp0 x hx; linarith)

theorem abs_q_le (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {x : X}
    (hx : x 0 ∈ Icc 0 T) : |lapseInv a0 gi x| ≤ 1 / a0 := by
  rw [h.q_eq ha hx, abs_inv, one_div]
  have := h.hyp0 x hx
  exact inv_anti₀ ha (by rw [abs_of_neg (by linarith)]; linarith)

theorem neg_q_ge (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {x : X}
    (hx : x 0 ∈ Icc 0 T) : 1 / Λ ≤ -lapseInv a0 gi x := by
  rw [h.q_eq ha hx]
  have h0 := h.hyp0 x hx
  have hb := h.bnd x hx 0 0
  have hneg : gi 0 0 x < 0 := by linarith
  rw [abs_of_neg hneg] at hb
  rw [← inv_neg, one_div]
  exact inv_anti₀ (by linarith) hb

theorem Λ_pos (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) (hT : 0 ≤ T) :
    a0 ≤ Λ := by
  have hx : (Fin.cons 0 0 : X) 0 ∈ Icc 0 T := by simp [hT]
  have h0 := h.hyp0 _ hx
  have hb := h.bnd _ hx 0 0
  rw [abs_of_neg (by linarith)] at hb
  linarith

theorem sbeta (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) (i : Fin 3) :
    ContDiff ℝ ∞ (betaF (lapseInv a0 gi) gi i) := by
  unfold betaF
  exact contDiff_const.mul ((h.sq ha).mul ((h.sgi _ _).add (h.sgi _ _)))

theorem sgamma (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) (i j : Fin 3) :
    ContDiff ℝ ∞ (gammaF (lapseInv a0 gi) gi i j) := by
  unfold gammaF
  exact contDiff_const.mul ((h.sq ha).mul ((h.sgi _ _).add (h.sgi _ _)))

theorem pbeta (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (i : Fin 3) :
    IsSPeriodic (betaF (lapseInv a0 gi) gi i) := fun k x => by
  simp only [betaF, h.pq k x, h.pgi _ _ k x]

theorem pgamma (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (i j : Fin 3) :
    IsSPeriodic (gammaF (lapseInv a0 gi) gi i j) := fun k x => by
  simp only [gammaF, h.pq k x, h.pgi _ _ k x]

theorem sN (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (c : Idx) :
    ContDiff ℝ ∞ (Nfield Np θ g gi c) := by
  refine contDiff_evalF (fun v => ?_) _
  rcases v with ab | c' | cμ | j
  · exact h.sgi _ _
  · exact h.sg c'
  · exact contDiff_pd_top (h.sg _) _
  · exact h.sθ j

theorem pN (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (c : Idx) :
    IsSPeriodic (Nfield Np θ g gi c) := by
  refine isSPeriodic_evalF (fun v => ?_) _
  rcases v with ab | c' | cμ | j
  · exact h.pgi _ _
  · exact h.pg c'
  · exact isSPeriodic_pd (h.pg _) _
  · exact h.pθ j

/-- **The normal form of `eq:reduced-wave`** on the slab:
`∂ₜ²g_c = 2βⁱ∂ᵢ∂ₜg_c + γ^{ij}∂ᵢ∂ⱼg_c + q(𝒩_c + 𝒮_c)`. -/
theorem normal_form (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {x : X}
    (hx : x 0 ∈ Icc 0 T) (c : Idx) :
    pd (pd (g c) 0) 0 x =
      2 * ∑ i : Fin 3, betaF (lapseInv a0 gi) gi i x * pd (pd (g c) 0) i.succ x +
      ∑ i : Fin 3, ∑ j : Fin 3, gammaF (lapseInv a0 gi) gi i j x *
        pd (pd (g c) j.succ) i.succ x +
      lapseInv a0 gi x * (Nfield Np θ g gi c x + S c x) := by
  have he := h.eqn x hx c
  rw [Fin.sum_univ_succ] at he
  simp only [Fin.sum_univ_succ (f := fun β : Fin 4 => gi _ β x * pd (pd (g c) β) _ x)] at he
  have hsw : ∀ j : Fin 3, pd (pd (g c) j.succ) 0 x = pd (pd (g c) 0) j.succ x := fun j =>
    pd_pd_comm ((h.sg c).of_le (by norm_cast)) j.succ 0 x
  simp only [hsw] at he
  have := normal_form_alg (lapseInv a0 gi x) (gi 0 0 x) (pd (pd (g c) 0) 0 x)
    (Nfield Np θ g gi c x + S c x) (fun j => gi 0 j.succ x) (fun i => gi i.succ 0 x)
    (fun i => pd (pd (g c) 0) i.succ x) (fun i j => gi i.succ j.succ x)
    (fun i j => pd (pd (g c) j.succ) i.succ x)
    (fun i j => pd_pd_comm ((h.sg c).of_le (by norm_cast)) j.succ i.succ x)
    (h.q_mul ha hx) (by rw [← he]; simp only [Finset.sum_add_distrib]; ring)
  rw [this]
  simp only [betaF, gammaF]

/-- `γ` is uniformly coercive on the slab, with constant `λ/Λ`. -/
theorem coer_gamma (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) (hlam : 0 ≤ lam)
    {x : X} (hx : x 0 ∈ Icc 0 T) (ξ : Fin 3 → ℝ) :
    lam / Λ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, gammaF (lapseInv a0 gi) gi i j x * ξ i * ξ j := by
  have hq := h.neg_q_ge ha hx
  set q := lapseInv a0 gi x
  have hsym : ∑ i, ∑ j, gi j.succ i.succ x * ξ i * ξ j = ∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e : ∑ i, ∑ j, gammaF (lapseInv a0 gi) gi i j x * ξ i * ξ j =
      (-q) * ∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j := by
    have : ∑ i, ∑ j, gammaF (lapseInv a0 gi) gi i j x * ξ i * ξ j =
        -(1 / 2) * q * (∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j +
          ∑ i, ∑ j, gi j.succ i.succ x * ξ i * ξ j) := by
      simp only [gammaF, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, hsym]; ring
  rw [e]
  have hS := h.hypS x hx ξ
  have hΛ : 0 < Λ := lt_of_lt_of_le ha (by
    have h0 := h.hyp0 x hx; have hb := h.bnd x hx 0 0
    rw [abs_of_neg (by linarith)] at hb; linarith)
  have hξ : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : lam / Λ * ∑ i, ξ i ^ 2 = 1 / Λ * (lam * ∑ i, ξ i ^ 2) := by ring
  rw [h1]
  have h2 : 0 ≤ lam * ∑ i, ξ i ^ 2 := mul_nonneg hlam hξ
  calc 1 / Λ * (lam * ∑ i, ξ i ^ 2) ≤ (-q) * (lam * ∑ i, ξ i ^ 2) :=
        mul_le_mul_of_nonneg_right hq h2
    _ ≤ (-q) * ∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j :=
        mul_le_mul_of_nonneg_left hS (le_trans (by positivity) hq)

/-! ### `W^{s-2,∞}` bounds -/

/-- The Sobolev constant of order `2` on `𝕋³`. -/
theorem exists_CS : ∃ CS : ℝ, 0 ≤ CS ∧ ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f →
    ∀ (t : ℝ) (y : Fin 3 → ℝ), f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t :=
  exists_sup_sq_le (d := 3) (m := 2) (by norm_num)

theorem derivBound_g (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (c : Idx) :
    DerivBound T (s - 2) (g c) (Real.sqrt (CS * K0)) :=
  derivBound_of_Q (m := 2) hCS hsup (h.sg c) (h.pg c) fun t ht => by
    rw [Nat.sub_add_cancel hs]; exact h.hsg t ht c

/-- The constant of `derivBound_gi`. -/
def Cgi (s : ℕ) (CS K0 Λ : ℝ) : ℝ := invC 4 (Real.sqrt (CS * K0)) Λ (s - 2)

theorem derivBound_gi (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (hΛ : 0 ≤ Λ) (a b : Fin 4) :
    DerivBound T (s - 2) (gi a b) (Cgi s CS K0 Λ) :=
  derivBound_inv (G := fun a c => g (a, c)) (fun a c => h.sg (a, c)) h.sgi h.inv
    (Real.sqrt_nonneg _) hΛ h.bnd (s - 2) (fun a c => h.derivBound_g hCS hsup hs (a, c)) a b

/-- The constant of `derivBound_q`. -/
def Cq (s : ℕ) (CS K0 Λ a0 : ℝ) : ℝ := invC 1 (Cgi s CS K0 Λ) (1 / a0) (s - 2)

theorem derivBound_q (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (hΛ : 0 ≤ Λ) :
    DerivBound T (s - 2) (lapseInv a0 gi) (Cq s CS K0 Λ a0) := by
  have hCgi : 0 ≤ Cgi s CS K0 Λ := invC_nonneg 4 hΛ _
  have := derivBound_inv (n := 1) (T := T) (G := fun _ _ => gi 0 0) (H := fun _ _ => lapseInv a0 gi)
    (fun _ _ => h.sgi 0 0) (fun _ _ => h.sq ha)
    (fun x hx a b => by
      simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; rw [mul_comm]; exact h.q_mul ha hx)
    hCgi (by positivity) (fun x hx _ _ => h.abs_q_le ha hx) (s - 2)
    (fun _ _ => h.derivBound_gi hCS hsup hs hΛ 0 0) 0 0
  exact this

/-- The constant of `derivBound_beta`/`derivBound_gamma`. -/
def Cbg (s : ℕ) (CS K0 Λ a0 : ℝ) : ℝ :=
  |(-(1 / 2) : ℝ)| * (2 ^ (s - 2) * (Cq s CS K0 Λ a0 * (Cgi s CS K0 Λ + Cgi s CS K0 Λ)))

theorem derivBound_beta (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (hΛ : 0 ≤ Λ) (i : Fin 3) :
    DerivBound T (s - 2) (betaF (lapseInv a0 gi) gi i) (Cbg s CS K0 Λ a0) := by
  have hCq : 0 ≤ Cq s CS K0 Λ a0 := invC_nonneg 1 (by positivity) _
  have h1 := derivBound_mul (h.derivBound_q ha hCS hsup hs hΛ)
    (derivBound_add (h.derivBound_gi hCS hsup hs hΛ 0 i.succ)
      (h.derivBound_gi hCS hsup hs hΛ i.succ 0) (h.sgi _ _) (h.sgi _ _))
    (h.sq ha) ((h.sgi _ _).add (h.sgi _ _)) hCq
  exact derivBound_const_mul h1 ((h.sq ha).mul ((h.sgi _ _).add (h.sgi _ _))) (-(1 / 2))

theorem derivBound_gamma (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (hΛ : 0 ≤ Λ) (i j : Fin 3) :
    DerivBound T (s - 2) (gammaF (lapseInv a0 gi) gi i j) (Cbg s CS K0 Λ a0) := by
  have hCq : 0 ≤ Cq s CS K0 Λ a0 := invC_nonneg 1 (by positivity) _
  have h1 := derivBound_mul (h.derivBound_q ha hCS hsup hs hΛ)
    (derivBound_add (h.derivBound_gi hCS hsup hs hΛ i.succ j.succ)
      (h.derivBound_gi hCS hsup hs hΛ j.succ i.succ) (h.sgi _ _) (h.sgi _ _))
    (h.sq ha) ((h.sgi _ _).add (h.sgi _ _)) hCq
  exact derivBound_const_mul h1 ((h.sq ha).mul ((h.sgi _ _).add (h.sgi _ _))) (-(1 / 2))

/-- The time-derivative bound of `γ`: the constant. -/
def Ct (CS K0 Λ a0 : ℝ) : ℝ :=
  1 / 2 * ((1 / a0) ^ 2 * (16 * (Λ ^ 2 * Real.sqrt (CS * K0))) * (2 * Λ) +
    1 / a0 * (2 * (16 * (Λ ^ 2 * Real.sqrt (CS * K0)))))

/-- `|∂ₜg^{ab}| ≤ 16 Λ² √(C_S K₀)` on the slab (`T > 0`). -/
theorem abs_pd_gi_time (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 3 ≤ s) (hT : 0 < T) (hΛ : 0 ≤ Λ)
    {x : X} (hx : x 0 ∈ Icc 0 T) (a b : Fin 4) :
    |pd (gi a b) 0 x| ≤ 16 * (Λ ^ 2 * Real.sqrt (CS * K0)) := by
  rw [pd_inv_eq (G := fun a c => g (a, c)) (fun a c => h.sg (a, c)) h.sgi h.inv 0 (Or.inr hT) hx,
    abs_neg]
  have hg : ∀ e c, |pd (g (e, c)) 0 x| ≤ Real.sqrt (CS * K0) := fun e c =>
    abs_le_of_Q hCS hsup (contDiff_pd_top (h.sg _) 0) (isSPeriodic_pd (h.pg _) 0)
      (fun t ht => (Q_mono (by omega) _ t).trans (h.hst t ht (e, c))) hx
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ e c, |gi a e x * pd (g (e, c)) 0 x * gi c b x| ≤ Λ ^ 2 * Real.sqrt (CS * K0) := by
    intro e c
    rw [abs_mul, abs_mul]
    have h1 := h.bnd x hx a e; have h2 := h.bnd x hx c b; have h3 := hg e c
    have := Real.sqrt_nonneg (CS * K0)
    calc |gi a e x| * |pd (g (e, c)) 0 x| * |gi c b x| ≤ Λ * Real.sqrt (CS * K0) * Λ := by
          gcongr
      _ = _ := by ring
  calc ∑ e, |∑ c, gi a e x * pd (g (e, c)) 0 x * gi c b x| ≤
      ∑ _e : Fin 4, ∑ _c : Fin 4, Λ ^ 2 * Real.sqrt (CS * K0) :=
        Finset.sum_le_sum fun e _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun c _ => hterm e c)
    _ = _ := by simp; ring

/-- `|∂ₜγ^{ij}| ≤ C_t` on the slab. -/
theorem abs_pd_gamma_time (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 3 ≤ s) (hT : 0 < T) (hΛ : 0 ≤ Λ)
    {x : X} (hx : x 0 ∈ Icc 0 T) (i j : Fin 3) :
    |pd (gammaF (lapseInv a0 gi) gi i j) 0 x| ≤ Ct CS K0 Λ a0 := by
  set q := lapseInv a0 gi
  have hq := h.sq ha
  -- derivative of `γ` along time
  have hd : HasDerivAt (fun s : ℝ => gammaF q gi i j (x + s • ev 0))
      (-(1 / 2) * (pd q 0 x * (gi i.succ j.succ x + gi j.succ i.succ x) +
        q x * (pd (gi i.succ j.succ) 0 x + pd (gi j.succ i.succ) 0 x))) 0 := by
    have h1 := hasDerivAt_line_pd hq x 0
    have h2 := (hasDerivAt_line_pd (h.sgi i.succ j.succ) x 0).fun_add
      (hasDerivAt_line_pd (h.sgi j.succ i.succ) x 0)
    have := (h1.fun_mul h2).const_mul (-(1 / 2))
    simp only [zero_smul, add_zero] at this
    exact this
  rw [(hasDerivAt_line_pd (h.sgamma ha i j) x 0).unique hd]
  -- the time derivative of `q`
  have hqt : pd q 0 x = -(q x * pd (gi 0 0) 0 x * q x) := by
    have := pd_inv_eq (n := 1) (T := T) (G := fun _ _ => gi 0 0) (H := fun _ _ => q)
      (fun _ _ => h.sgi 0 0) (fun _ _ => hq)
      (fun x hx a b => by
        simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; rw [mul_comm]; exact h.q_mul ha hx) 0 (Or.inr hT) hx 0 0
    simpa using this
  have hqb := h.abs_q_le ha hx
  set P := 16 * (Λ ^ 2 * Real.sqrt (CS * K0))
  have hP : 0 ≤ P := by positivity
  have hgt := fun a b => h.abs_pd_gi_time hCS hsup hs hT hΛ hx a b
  have hqt' : |pd q 0 x| ≤ (1 / a0) ^ 2 * P := by
    rw [hqt, abs_neg, abs_mul, abs_mul]
    have := hgt 0 0
    calc |q x| * |pd (gi 0 0) 0 x| * |q x| ≤ (1 / a0) * P * (1 / a0) := by gcongr
      _ = _ := by ring
  have hs1 : |gi i.succ j.succ x + gi j.succ i.succ x| ≤ 2 * Λ := by
    have := h.bnd x hx i.succ j.succ; have := h.bnd x hx j.succ i.succ
    exact (abs_add_le _ _).trans (by linarith)
  have hs2 : |pd (gi i.succ j.succ) 0 x + pd (gi j.succ i.succ) 0 x| ≤ 2 * P := by
    have := hgt i.succ j.succ; have := hgt j.succ i.succ
    exact (abs_add_le _ _).trans (by linarith)
  rw [abs_mul, abs_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)]
  unfold Ct
  have := (abs_add_le _ _).trans (add_le_add
    (by rw [abs_mul]; exact mul_le_mul hqt' hs1 (abs_nonneg _) (by positivity) :
      |pd q 0 x * (gi i.succ j.succ x + gi j.succ i.succ x)| ≤ (1 / a0) ^ 2 * P * (2 * Λ))
    (by rw [abs_mul]; exact mul_le_mul hqb hs2 (abs_nonneg _) (by positivity) :
      |q x * (pd (gi i.succ j.succ) 0 x + pd (gi j.succ i.succ) 0 x)| ≤ 1 / a0 * (2 * P)))
  linarith

end MetricHyp

end ReducedWaveStab

end RenewalGeometry
