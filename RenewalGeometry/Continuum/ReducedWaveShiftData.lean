/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabDifference
import RenewalGeometry.Continuum.SlabWaveShiftEnergy

/-!
# Uniform hyperbolicity with a common time function (nonzero shift) for the reduced wave system

`thm:hyperbolic` of the Einstein–Standard-Model action-closure manuscript ("Common-slab metric
stability") assumes *uniform hyperbolicity with a common time function*: the slices `{t = const}`
are uniformly spacelike and `dt` is uniformly timelike, with bounded lapse and shift (the proof:
"The uniformly spacelike slices and bounded lapse and shift give a positive wave energy").  A
nonzero shift `g^{0i}` is allowed, so `∂ₜ` need not be timelike and the inverse spatial block
`g^{ij}` need not be positive.

* `MetricHypSh` — the hypotheses of `thm:hyperbolic` on one metric with this hyperbolicity
  condition: `g` symmetric, `g^{00} ≤ -a₀` (`dt` uniformly timelike), `g_{ij}ξⁱξʲ ≥ λ_S|ξ|²`
  (the slices are uniformly spacelike), `|g^{ab}| ≤ Λ`, `eq:hyperbolic-bound`, `eq:reduced-wave`.
  `MetricHypSh.toMetricHyp`: it implies `ReducedWaveStab.MetricHyp` with the (vacuous) constant
  `-3Λ` in place of the positivity of `g^{ij}`, so every lemma of the reduced-wave chain that does
  not use that positivity applies.
* **`shift_coer_alg`**, **`MetricHypSh.coer_acoef`** — for the normal-form coefficients
  `βⁱ = -q g^{0i}`, `γ^{ij} = -q g^{ij}` (`q = 1/g^{00}`) the matrix `a = γ + ββ`
  (`= N² h^{ij}`) is uniformly positive: `a(ξ, ξ) ≥ λ_S/(9Λ(C_S K₀ + 1)) |ξ|²`.  (With
  `V = g⁻¹(-qp, ξ)`, `p = g^{0j}ξⱼ`: `V⁰ = 0`, `ξᵢ = g_{ij}Vʲ` and `a(ξ, ξ) = -q g_{ij}VⁱVʲ`.)
* `abs_pd_beta_time` — `|∂ₜβⁱ| ≤ C_t`.
* `diffSys_hyp_any` — the difference system satisfies `SlabWaveHk.SysHyp` with the vacuous
  `γ`-coercivity constant `-3M` (no positivity of `g^{ij}` used).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg ReducedWaveStab SlabWaveShift

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- **The hypotheses of `thm:hyperbolic` on one metric, with uniform hyperbolicity with respect
to the common time function `t = x⁰`** (nonzero shift allowed): `s` the Sobolev order, `T` the slab
length, `a₀` (`g^{00} ≤ -a₀`: `dt` uniformly timelike), `λ_S` (the slices `{t = const}` are
uniformly spacelike: `g_{ij}ξⁱξʲ ≥ λ_S|ξ|²`), `Λ` the inverse-metric bound, `K₀` the a-priori
bound `eq:hyperbolic-bound`. -/
structure MetricHypSh (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ) (s : ℕ)
    (T a0 lamS Λ K0 : ℝ) (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (S : Idx → X → ℝ) :
    Prop where
  sg : ∀ c, ContDiff ℝ ∞ (g c)
  sgi : ∀ a b, ContDiff ℝ ∞ (gi a b)
  sS : ∀ c, ContDiff ℝ ∞ (S c)
  sθ : ∀ j, ContDiff ℝ ∞ (θ j)
  pg : ∀ c, IsSPeriodic (g c)
  pgi : ∀ a b, IsSPeriodic (gi a b)
  pS : ∀ c, IsSPeriodic (S c)
  pθ : ∀ j, IsSPeriodic (θ j)
  /-- the metric is symmetric -/
  symm : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, g (a, b) x = g (b, a) x
  /-- `g · g⁻¹ = 1` on the slab -/
  inv : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, ∑ c, g (a, c) x * gi c b x = if a = b then 1 else 0
  /-- `dt` is uniformly timelike: `g^{00} ≤ -a₀` -/
  hyp0 : ∀ x : X, x 0 ∈ Icc 0 T → gi 0 0 x ≤ -a0
  /-- the slices `{t = const}` are uniformly spacelike: `g_{ij}ξⁱξʲ ≥ λ_S|ξ|²` -/
  slices : ∀ x : X, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
    lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, g (i.succ, j.succ) x * ξ i * ξ j
  /-- the uniform inverse-metric bound -/
  bnd : ∀ x : X, x 0 ∈ Icc 0 T → ∀ a b, |gi a b x| ≤ Λ
  /-- `eq:hyperbolic-bound` (squared classical slice norms) -/
  hsg : ∀ t ∈ Icc 0 T, ∀ c, Q s (g c) t ≤ K0
  hst : ∀ t ∈ Icc 0 T, ∀ c, Q (s - 1) (pd (g c) 0) t ≤ K0
  /-- `eq:reduced-wave` -/
  eqn : ∀ x : X, x 0 ∈ Icc 0 T → ∀ c,
    ∑ α : Fin 4, ∑ β : Fin 4, gi α β x * pd (pd (g c) β) α x = Nfield Np θ g gi c x + S c x

namespace MetricHypSh

variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {s : ℕ} {T a0 lamS Λ K0 : ℝ}
  {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}

/-- `-3Λ|ξ|² ≤ g^{ij}ξᵢξⱼ` from the inverse-metric bound alone. -/
theorem neg_three_le (h : MetricHypSh Np θ s T a0 lamS Λ K0 g gi S) {x : X} (hx : x 0 ∈ Icc 0 T)
    (ξ : Fin 3 → ℝ) : -(3 * Λ) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, gi i.succ j.succ x * ξ i * ξ j := by
  have h1 : ∀ i j : Fin 3, -(Λ * (ξ i ^ 2 + ξ j ^ 2) / 2) ≤ gi i.succ j.succ x * ξ i * ξ j := by
    intro i j
    have := TorusWaveEnergy.WaveData.abs_mul_le_half (-(gi i.succ j.succ x)) (ξ i) (ξ j) Λ
      (by rw [abs_neg]; exact h.bnd x hx _ _)
    linarith
  calc -(3 * Λ) * ∑ i, ξ i ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3, -(Λ * (ξ i ^ 2 + ξ j ^ 2) / 2) := by
        simp only [Fin.sum_univ_three]; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j

/-- **The paper's hypotheses imply the chain's `MetricHyp`** with the vacuous constant `-3Λ` for
the inverse spatial block (no positivity of `g^{ij}`). -/
theorem toMetricHyp (h : MetricHypSh Np θ s T a0 lamS Λ K0 g gi S) :
    MetricHyp Np θ s T a0 (-(3 * Λ)) Λ K0 g gi S where
  sg := h.sg
  sgi := h.sgi
  sS := h.sS
  sθ := h.sθ
  pg := h.pg
  pgi := h.pgi
  pS := h.pS
  pθ := h.pθ
  inv := h.inv
  hyp0 := h.hyp0
  hypS := fun x hx ξ => h.neg_three_le hx ξ
  bnd := h.bnd
  hsg := h.hsg
  hst := h.hst
  eqn := h.eqn

/-- The inverse metric is symmetric on the slab. -/
theorem gi_symm (h : MetricHypSh Np θ s T a0 lamS Λ K0 g gi S) {x : X} (hx : x 0 ∈ Icc 0 T)
    (a b : Fin 4) : gi a b x = gi b a x := by
  set G : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun a c => g (a, c) x
  set H : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun a b => gi a b x
  have hGH : G * H = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, G, H]
    exact h.inv x hx a b
  have hHG : H * G = 1 := mul_eq_one_comm.mp hGH
  have hGt : Matrix.transpose G = G := by
    ext a b; simp only [Matrix.transpose_apply, Matrix.of_apply, G]; exact h.symm x hx b a
  have hHt : Matrix.transpose H * G = 1 := by
    have := congrArg Matrix.transpose hGH
    rwa [Matrix.transpose_mul, Matrix.transpose_one, hGt] at this
  have hHH : Matrix.transpose H = H := by
    calc Matrix.transpose H = Matrix.transpose H * (G * H) := by rw [hGH, mul_one]
      _ = (Matrix.transpose H * G) * H := by rw [mul_assoc]
      _ = H := by rw [hHt, one_mul]
  have := congrFun (congrFun hHH b) a
  simpa [H] using this

end MetricHypSh

/-! ### Positivity of `a = γ + ββ` -/

/-- **The pointwise algebra of the shift coercivity**: for a symmetric `4 × 4` matrix `H = G⁻¹`
with `q H₀₀ = 1`, `-q ≥ c ≥ 0`, uniformly positive spatial block `G_{ij} ≥ λ_S` with entries
bounded by `B`, the normal-form matrix `a = γ + ββ`, `γ^{ij} = -½q(H^{ij} + H^{ji})`,
`βⁱ = -½q(H^{0i} + H^{i0})`, satisfies `a(ξ, ξ) ≥ c λ_S/(9(B² + 1)) |ξ|²`. -/
theorem shift_coer_alg (G H : Fin 4 → Fin 4 → ℝ)
    (hinv : ∀ a b, ∑ c, G a c * H c b = if a = b then 1 else 0)
    (hHs : ∀ a b, H a b = H b a) {q c lamS B : ℝ} (hq : q * H 0 0 = 1) (hc : c ≤ -q)
    (hc0 : 0 ≤ c) (hlamS : 0 ≤ lamS)
    (hsl : ∀ V : Fin 3 → ℝ, lamS * ∑ i, V i ^ 2 ≤ ∑ i, ∑ j, G i.succ j.succ * V i * V j)
    (hB : ∀ i j : Fin 3, |G i.succ j.succ| ≤ B) (ξ : Fin 3 → ℝ) :
    c * lamS / (9 * (B ^ 2 + 1)) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, ((-(1 / 2) * (q * (H i.succ j.succ + H j.succ i.succ))) +
        (-(1 / 2) * (q * (H 0 i.succ + H i.succ 0))) *
          (-(1 / 2) * (q * (H 0 j.succ + H j.succ 0)))) * ξ i * ξ j := by
  set p := ∑ j : Fin 3, H 0 j.succ * ξ j
  set η : Fin 4 → ℝ := Fin.cons (-(q * p)) ξ
  set V : Fin 4 → ℝ := fun a => ∑ e, H a e * η e
  have hV0 : V 0 = 0 := by
    have e : V 0 = H 0 0 * -(q * p) + p := by
      show ∑ e, H 0 e * η e = _
      rw [Fin.sum_univ_succ]
      simp only [η, Fin.cons_zero, Fin.cons_succ]
      rfl
    rw [e]; linear_combination (-p) * hq
  have hGV : ∀ a, ∑ b, G a b * V b = η a := by
    intro a
    simp only [V, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hinv]
    simp
  have hξ : ∀ i : Fin 3, ξ i = ∑ j : Fin 3, G i.succ j.succ * V j.succ := by
    intro i
    have := hGV i.succ
    rw [Fin.sum_univ_succ, hV0, mul_zero, zero_add] at this
    calc ξ i = η i.succ := by simp [η]
      _ = _ := this.symm
  set W : Fin 3 → ℝ := fun i => V i.succ
  have hW : ∀ i : Fin 3, W i = H i.succ 0 * -(q * p) + ∑ j : Fin 3, H i.succ j.succ * ξ j := by
    intro i; simp only [W, V, Fin.sum_univ_succ, η, Fin.cons_zero, Fin.cons_succ]
  -- the quadratic form in terms of `W`
  have hquad : ∑ i, ∑ j, ((-(1 / 2) * (q * (H i.succ j.succ + H j.succ i.succ))) +
        (-(1 / 2) * (q * (H 0 i.succ + H i.succ 0))) *
          (-(1 / 2) * (q * (H 0 j.succ + H j.succ 0)))) * ξ i * ξ j =
      -q * ∑ i, ξ i * W i := by
    simp only [hW]
    simp only [p, Fin.sum_univ_three]
    simp only [hHs (Fin.succ 1) (Fin.succ 0), hHs (Fin.succ 2) (Fin.succ 0),
      hHs (Fin.succ 2) (Fin.succ 1), hHs (Fin.succ 0) 0, hHs (Fin.succ 1) 0, hHs (Fin.succ 2) 0]
    ring
  have hpos : lamS * ∑ i, W i ^ 2 ≤ ∑ i, ξ i * W i := by
    have e : ∑ i, ξ i * W i = ∑ i, ∑ j, G i.succ j.succ * W i * W j := by
      simp only [hξ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [W]; ring
    rw [e]; exact hsl W
  have hbd : ∑ i, ξ i ^ 2 ≤ 9 * (B ^ 2 + 1) * ∑ i, W i ^ 2 := by
    have h1 : ∀ i : Fin 3, ξ i ^ 2 ≤ 3 * (B ^ 2 * ∑ j, W j ^ 2) := by
      intro i
      rw [hξ i]
      refine (ShL2Hyp.sq_sum3_le _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (sq_le_sq' (neg_le_of_abs_le (hB i j))
        (le_of_abs_le (hB i j))) (sq_nonneg _)
    have hW0 : 0 ≤ ∑ j, W j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ∑ i, ξ i ^ 2 ≤ ∑ _i : Fin 3, 3 * (B ^ 2 * ∑ j, W j ^ 2) := Finset.sum_le_sum fun i _ => h1 i
      _ = 9 * B ^ 2 * ∑ j, W j ^ 2 := by simp; ring
      _ ≤ 9 * (B ^ 2 + 1) * ∑ i, W i ^ 2 := by nlinarith
  rw [hquad]
  have hW0 : 0 ≤ ∑ i, W i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB1 : 0 < 9 * (B ^ 2 + 1) := by positivity
  have hξ0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c * lamS / (9 * (B ^ 2 + 1)) * ∑ i, ξ i ^ 2 ≤ c * lamS * ∑ i, W i ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hB1]
    have := mul_nonneg hc0 hlamS
    nlinarith
  have h3 : c * (lamS * ∑ i, W i ^ 2) ≤ -q * ∑ i, ξ i * W i :=
    mul_le_mul hc hpos (mul_nonneg hlamS hW0) (le_trans hc0 hc)
  linarith

namespace MetricHypSh

variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {s : ℕ} {T a0 lamS Λ K0 : ℝ}
  {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}

/-- The coercivity constant of `a = γ + ββ`. -/
def lamA (lamS Λ CS K0 : ℝ) : ℝ := 1 / Λ * lamS / (9 * (Real.sqrt (CS * K0) ^ 2 + 1))

/-- **`a = γ + ββ` is uniformly positive on the slab** (uniformly spacelike slices, bounded lapse
and shift), with constant `lamA` depending only on the common constants. -/
theorem coer_acoef (h : MetricHypSh Np θ s T a0 lamS Λ K0 g gi S) (ha : 0 < a0)
    (hlamS : 0 ≤ lamS) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) {x : X} (hx : x 0 ∈ Icc 0 T)
    (ξ : Fin 3 → ℝ) :
    lamA lamS Λ CS K0 * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, acoef (betaF (lapseInv a0 gi) gi) (gammaF (lapseInv a0 gi) gi) i j x *
        ξ i * ξ j := by
  have hM := h.toMetricHyp
  have hΛ : 0 < Λ := by
    have h0 := h.hyp0 x hx; have hb := h.bnd x hx 0 0
    rw [abs_of_neg (by linarith)] at hb; linarith
  have hgb : ∀ i j : Fin 3, |g (i.succ, j.succ) x| ≤ Real.sqrt (CS * K0) := fun i j =>
    abs_le_of_Q hCS hsup (h.sg _) (h.pg _) (fun t ht => (Q_mono hs _ t).trans (h.hsg t ht _)) hx
  have := shift_coer_alg (fun a b => g (a, b) x) (fun a b => gi a b x) (h.inv x hx)
    (fun a b => h.gi_symm hx a b) (hM.q_mul ha hx) (hM.neg_q_ge ha hx) (by positivity) hlamS
    (h.slices x hx) hgb ξ
  unfold lamA
  simpa only [acoef, betaF, gammaF] using this

end MetricHypSh

/-! ### The time derivative of `β` -/

/-- `|∂ₜ(-½ q (g^{ab} + g^{ba}))| ≤ C_t` on the slab (`T > 0`). -/
theorem abs_pd_qpair_time {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {s : ℕ} {T a0 lam Λ K0 : ℝ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 3 ≤ s) (hT : 0 < T) (hΛ : 0 ≤ Λ)
    {x : X} (hx : x 0 ∈ Icc 0 T) (a b : Fin 4) :
    |pd (fun x => -(1 / 2) * (lapseInv a0 gi x * (gi a b x + gi b a x))) 0 x| ≤
      MetricHyp.Ct CS K0 Λ a0 := by
  set q := lapseInv a0 gi
  have hq := h.sq ha
  have hsm : ContDiff ℝ ∞ (fun x => -(1 / 2) * (q x * (gi a b x + gi b a x))) :=
    contDiff_const.mul (hq.mul ((h.sgi a b).add (h.sgi b a)))
  have hd : HasDerivAt (fun s : ℝ => -(1 / 2) * (q (x + s • ev 0) *
      (gi a b (x + s • ev 0) + gi b a (x + s • ev 0))))
      (-(1 / 2) * (pd q 0 x * (gi a b x + gi b a x) +
        q x * (pd (gi a b) 0 x + pd (gi b a) 0 x))) 0 := by
    have h1 := hasDerivAt_line_pd hq x 0
    have h2 := (hasDerivAt_line_pd (h.sgi a b) x 0).fun_add (hasDerivAt_line_pd (h.sgi b a) x 0)
    have := (h1.fun_mul h2).const_mul (-(1 / 2))
    simp only [zero_smul, add_zero] at this
    exact this
  rw [(hasDerivAt_line_pd hsm x 0).unique hd]
  have hqt : pd q 0 x = -(q x * pd (gi 0 0) 0 x * q x) := by
    have := pd_inv_eq (n := 1) (T := T) (G := fun _ _ => gi 0 0) (H := fun _ _ => q)
      (fun _ _ => h.sgi 0 0) (fun _ _ => hq)
      (fun x hx a b => by
        simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; rw [mul_comm]; exact h.q_mul ha hx)
      0 (Or.inr hT) hx 0 0
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
  have hs1 : |gi a b x + gi b a x| ≤ 2 * Λ := by
    have := h.bnd x hx a b; have := h.bnd x hx b a
    exact (abs_add_le _ _).trans (by linarith)
  have hs2 : |pd (gi a b) 0 x + pd (gi b a) 0 x| ≤ 2 * P := by
    have := hgt a b; have := hgt b a
    exact (abs_add_le _ _).trans (by linarith)
  rw [abs_mul, abs_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)]
  unfold MetricHyp.Ct
  have := (abs_add_le _ _).trans (add_le_add
    (by rw [abs_mul]; exact mul_le_mul hqt' hs1 (abs_nonneg _) (by positivity) :
      |pd q 0 x * (gi a b x + gi b a x)| ≤ (1 / a0) ^ 2 * P * (2 * Λ))
    (by rw [abs_mul]; exact mul_le_mul hqb hs2 (abs_nonneg _) (by positivity) :
      |q x * (pd (gi a b) 0 x + pd (gi b a) 0 x)| ≤ 1 / a0 * (2 * P)))
  linarith

/-- `|∂ₜβⁱ| ≤ C_t` on the slab. -/
theorem abs_pd_beta_time {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {s : ℕ} {T a0 lam Λ K0 : ℝ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 3 ≤ s) (hT : 0 < T) (hΛ : 0 ≤ Λ)
    {x : X} (hx : x 0 ∈ Icc 0 T) (i : Fin 3) :
    |pd (betaF (lapseInv a0 gi) gi i) 0 x| ≤ MetricHyp.Ct CS K0 Λ a0 :=
  abs_pd_qpair_time h ha hCS hsup hs hT hΛ hx 0 i.succ

/-! ### The difference system without positivity of `g^{ij}` -/

theorem abs_gamma_le {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {s : ℕ} {T a0 lam Λ K0 : ℝ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) {CS : ℝ}
    (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) (hs : 2 ≤ s) (hΛ : 0 ≤ Λ) {x : X}
    (hx : x 0 ∈ Icc 0 T) (i j : Fin 3) :
    |gammaF (lapseInv a0 gi) gi i j x| ≤ MetricHyp.Cbg s CS K0 Λ a0 :=
  h.derivBound_gamma ha hCS hsup hs hΛ i j [] (Nat.zero_le _) x hx

/-- **The difference system satisfies `SysHyp` at order `s - 2`** with the vacuous coercivity
constant `-3 M_diff` (the positivity of `g^{ij}` is not used) and the coefficient bound
`M_diff`. -/
theorem diffSys_hyp_any {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {s : ℕ}
    {T a0 lam Λ K0 : ℝ} {g g' : Idx → X → ℝ} {gi gi' : Fin 4 → Fin 4 → X → ℝ}
    {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (h' : MetricHyp Np θ s T a0 lam Λ K0 g' gi' S')
    (hs : 3 ≤ s) (hT : 0 < T) (ha : 0 < a0) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) :
    SysHyp (diffSys a0 gi) (wdiff g g') (fdiff a0 gi g g') T (-(3 * Mdiff s CS K0 Λ a0))
      (Mdiff s CS K0 Λ a0) (s - 2) := by
  have hΛ : 0 ≤ Λ := le_trans ha.le (h.Λ_pos ha hT.le)
  have hM1 : MetricHyp.Cbg s CS K0 Λ a0 ≤ Mdiff s CS K0 Λ a0 :=
    le_add_of_nonneg_right (Ct_nonneg ha hΛ)
  have hM2 : MetricHyp.Ct CS K0 Λ a0 ≤ Mdiff s CS K0 Λ a0 :=
    le_add_of_nonneg_left (Cbg_nonneg s hΛ ha)
  have hM0 : 0 ≤ Mdiff s CS K0 Λ a0 := add_nonneg (Cbg_nonneg s hΛ ha) (Ct_nonneg ha hΛ)
  have sw := contDiff_wdiff h.sg h'.sg
  refine
    { su := sw
      sF := fun c => ?_
      sβ := h.sbeta ha
      sγ := h.sgamma ha
      sA := fun _ _ => contDiff_const
      sB := fun _ _ _ => contDiff_const
      sC := fun _ _ => contDiff_const
      pu := fun c k x => by simp only [wdiff, h.pg c k x, h'.pg c k x]
      pF := fun c => ?_
      pβ := h.pbeta
      pγ := h.pgamma
      pA := fun _ _ => isSPeriodic_const 0
      pB := fun _ _ _ => isSPeriodic_const 0
      pC := fun _ _ => isSPeriodic_const 0
      eqn := fun x _ c => by
        rw [lower_diffSys]; unfold fdiff; ring
      γ_symm := fun i j x => gammaF_symm _ _ i j x
      coer := fun x hx ξ => ?_
      M_nonneg := hM0
      bβ := fun i => (h.derivBound_beta ha hCS hsup (by omega) hΛ i).mono hM1
      bγ := fun i j => (h.derivBound_gamma ha hCS hsup (by omega) hΛ i j).mono hM1
      bA := fun _ _ => DerivBound.zero hM0
      bB := fun _ _ _ => DerivBound.zero hM0
      bC := fun _ _ => DerivBound.zero hM0
      bβx := fun x hx i j => ?_
      bγ1 := fun x hx i j μ => ?_ }
  · unfold fdiff WaveSys.princ diffSys
    have h1 := contDiff_pd_top (contDiff_pd_top (sw c) 0) 0
    have h2 : ContDiff ℝ ∞ fun x => 2 * ∑ i : Fin 3, betaF (lapseInv a0 gi) gi i x *
        pd (pd (wdiff g g' c) 0) i.succ x :=
      contDiff_const.mul (ContDiff.sum fun i _ => (h.sbeta ha i).mul
        (contDiff_pd_top (contDiff_pd_top (sw c) 0) _))
    have h3 : ContDiff ℝ ∞ fun x => ∑ i : Fin 3, ∑ j : Fin 3, gammaF (lapseInv a0 gi) gi i j x *
        pd (pd (wdiff g g' c) j.succ) i.succ x :=
      ContDiff.sum fun i _ => ContDiff.sum fun j _ => (h.sgamma ha i j).mul
        (contDiff_pd_top (contDiff_pd_top (sw c) _) _)
    exact h1.sub (h2.add h3)
  · have pw : IsSPeriodic (wdiff g g' c) := fun k x => by
      simp only [wdiff, h.pg c k x, h'.pg c k x]
    intro k x
    unfold fdiff WaveSys.princ diffSys
    simp only [isSPeriodic_pd (isSPeriodic_pd pw 0) 0 k x, h.pbeta _ k x, h.pgamma _ _ k x,
      fun i => isSPeriodic_pd (isSPeriodic_pd pw 0) (Fin.succ i) k x,
      fun i j => isSPeriodic_pd (isSPeriodic_pd pw (Fin.succ j)) (Fin.succ i) k x]
  · have h1 : ∀ i j : Fin 3, -(Mdiff s CS K0 Λ a0 * (ξ i ^ 2 + ξ j ^ 2) / 2) ≤
        (diffSys a0 gi).γ i j x * ξ i * ξ j := by
      intro i j
      have := TorusWaveEnergy.WaveData.abs_mul_le_half (-((diffSys a0 gi).γ i j x)) (ξ i) (ξ j)
        (Mdiff s CS K0 Λ a0) (by
          rw [abs_neg]
          exact (abs_gamma_le h ha hCS hsup (by omega) hΛ hx i j).trans hM1)
      linarith
    calc -(3 * Mdiff s CS K0 Λ a0) * ∑ i, ξ i ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, -(Mdiff s CS K0 Λ a0 * (ξ i ^ 2 + ξ j ^ 2) / 2) := by
          simp only [Fin.sum_univ_three]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
  · exact ((h.derivBound_beta ha hCS hsup (by omega) hΛ i) [j] (by simp; omega) x hx).trans hM1
  · induction μ using Fin.cases with
    | zero => exact (h.abs_pd_gamma_time ha hCS hsup hs hT hΛ hx i j).trans hM2
    | succ k =>
      exact ((h.derivBound_gamma ha hCS hsup (by omega) hΛ i j) [k] (by simp; omega) x hx).trans
        hM1

end RenewalGeometry.ReducedWaveShift
