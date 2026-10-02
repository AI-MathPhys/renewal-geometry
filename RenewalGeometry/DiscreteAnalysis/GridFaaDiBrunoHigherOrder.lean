/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridFaaDiBrunoProlongation

/-!
# `C^r_ℓ` global error of characteristic Strang splitting for smooth semilinear systems
  (infrastructure for `prop:supp-gowdy-residual-control`, `eq:supp-gowdy-state-error` for every
  `r`; emergent-spacetime supplement)

A **smooth characteristic setup** `SmoothSetup V p` packages a semilinear characteristic system
on a normed space `V` (complementary projections `Π±, Π₀`, a source field `F`, densities `g±`
depending only on their own characteristic part) together with a smooth `2π`-periodic reference
solution `(Z, λ)` on a slab `[t₀, t₁]`, a convex chart `K` containing the `δ`-tube around the
reference, and uniform derivative bounds of order `≤ m` (`p : Params` collects the numbers
`t₀, t₁, δ, M, D, R, m`).

* `SmoothSetup.toStrang`: for `m ≥ 3` it is a `CharacteristicSplitting.StrangSetup` with explicit
  constants depending only on `p`.
* `SmoothSetup.prol`: **its difference-quotient prolongation is again a smooth characteristic
  setup**, on `V × V`, with parameters `p.prol` that do not depend on the spacing `ℓ ∈ (0,1]`
  (uniform discrete Faà di Bruno bound `derivBound_diffQuot`; the prolonged reference
  `(Z, ℓ⁻¹(Z(·, · + ℓ) - Z))` is again an exact solution of the prolonged system).
* `SmoothSetup.oneStepK` (by induction on `k`, applying the `k = 0` result to the `k`-fold
  prolongation): every numerical split step `X → A → B` whose stages satisfy the `C^k_ℓ` envelope
  `EnvK k` obeys
  `distK k (B, 𝖲X_*(τ+ℓ)) ≤ (1 + K_k ℓ) distK k (X, 𝖲X_*(τ)) + C_k ℓ³`.
* `SmoothSetup.global_error_crNorm`: the discrete Grönwall assembly: for numerical histories
  `X_{n+1} = Φ_h(X_n) + r_n` realised by split steps in the `C^r_ℓ` envelope,
  `‖X_n - 𝖲_ℓX_*(t_n)‖_{r,∞,ℓ} ≤ 3 (‖X₀ - 𝖲_ℓX_*(t₀)‖_{r,∞,ℓ} + Σ_{k<n} ‖r_k‖_{r,∞,ℓ}
    + C T ℓ²) e^{K T}` with `C, K` depending only on `p` and `r`.
-/

open Set Finset
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GridFaaDiBruno

noncomputable section

open IteratedDerivBounds CharacteristicSplitting

/-! ### Parameters -/

/-- The numerical parameters of a smooth characteristic setup: slab `[t₀, t₁]`, tube radius
`δ`, derivative bounds `M` (field and densities) and `D` (reference), envelope radius `R` and
order `m`. -/
structure Params where
  t₀ : ℝ
  t₁ : ℝ
  δ : ℝ
  M : ℝ
  D : ℝ
  R : ℝ
  m : ℕ

namespace Params

/-- The parameters of the prolonged setup. -/
def prol (p : Params) : Params :=
  ⟨p.t₀, p.t₁, p.δ / 2, p.M + p.M * (p.R + 1 + p.m) * 2 ^ p.m, 2 * p.D, 2 * p.R, p.m - 1⟩

/-- Sign conditions on the parameters. -/
structure Good (p : Params) : Prop where
  δ_pos : 0 < p.δ
  δ_le : p.δ ≤ 1
  M_nonneg : 0 ≤ p.M
  D_nonneg : 0 ≤ p.D
  R_ge : p.D + 1 ≤ p.R

theorem Good.prol {p : Params} (h : p.Good) : p.prol.Good where
  δ_pos := by simp only [Params.prol]; linarith [h.δ_pos]
  δ_le := by simp only [Params.prol]; linarith [h.δ_le]
  M_nonneg := by
    simp only [Params.prol]
    have hM := h.M_nonneg; have := h.D_nonneg; have := h.R_ge
    have h1 : 0 ≤ p.R + 1 + p.m := by
      have : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
      linarith
    exact add_nonneg hM (mul_nonneg (mul_nonneg hM h1) (by positivity))
  D_nonneg := by simp only [Params.prol]; linarith [h.D_nonneg]
  R_ge := by simp only [Params.prol]; linarith [h.R_ge]

theorem Good.iterate {p : Params} (h : p.Good) (k : ℕ) : (Params.prol^[k] p).Good := by
  induction k generalizing p with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih h.prol

/-- The `h³` coefficient of the state part of the local error. -/
def stateC (p : Params) : ℝ :=
  9 * (p.D / 24 + p.M * (p.D + p.M / 2) ^ 2 / 2 + p.M * p.D * (1 + p.M) / 8) +
    9 * (p.M ^ 2 * p.M / 32) + p.M ^ 2 * p.M / 16

/-- The `h³` coefficient of the background part of the local error. -/
def lamC (p : Params) : ℝ :=
  p.D / 24 + p.M * p.M * p.M / 4 + (p.M * (p.D + p.M) ^ 2 +
    2 * p.M * (p.D / 8 + p.M * p.D / 4) + p.M * p.D / 4)

/-- Level-zero consistency constant. -/
def cons0 (p : Params) : ℝ := max p.stateC p.lamC

/-- Level-zero Lipschitz rate `9L + 8L_g` with `L = L_g = M`. -/
def rate0 (p : Params) : ℝ := 9 * p.M + 8 * p.M

/-- Level-zero step threshold. -/
def step0 (p : Params) : ℝ := min (p.δ / (3 * p.M + 6 * p.D + 1)) (1 / (3 * p.M + 1))

/-- Level-`k` Lipschitz rate. -/
def rate (k : ℕ) (p : Params) : ℝ := (Params.prol^[k] p).rate0

/-- Level-`k` consistency constant. -/
def cons (k : ℕ) (p : Params) : ℝ := (Params.prol^[k] p).cons0

/-- Level-`k` step threshold `min_{i ≤ k} step0 (prolⁱ p)`. -/
def step : ℕ → Params → ℝ
  | 0, p => p.step0
  | k + 1, p => min p.step0 (step k p.prol)

theorem rate_succ (k : ℕ) (p : Params) : rate (k + 1) p = rate k p.prol := by
  simp only [rate, Function.iterate_succ_apply]

theorem cons_succ (k : ℕ) (p : Params) : cons (k + 1) p = cons k p.prol := by
  simp only [cons, Function.iterate_succ_apply]

theorem rate0_nonneg {p : Params} (h : p.Good) : 0 ≤ p.rate0 := by
  unfold rate0; linarith [h.M_nonneg]

theorem cons0_nonneg {p : Params} (h : p.Good) : 0 ≤ p.cons0 := by
  have := h.M_nonneg; have := h.D_nonneg
  exact (by unfold stateC; positivity : 0 ≤ p.stateC).trans (le_max_left _ _)

theorem rate_nonneg {p : Params} (h : p.Good) (k : ℕ) : 0 ≤ rate k p :=
  rate0_nonneg (h.iterate k)

theorem cons_nonneg {p : Params} (h : p.Good) (k : ℕ) : 0 ≤ cons k p :=
  cons0_nonneg (h.iterate k)

theorem step0_pos {p : Params} (h : p.Good) : 0 < p.step0 := by
  have := h.M_nonneg; have := h.D_nonneg; have := h.δ_pos
  unfold step0; exact lt_min (by positivity) (by positivity)

theorem step0_le_one {p : Params} (h : p.Good) : p.step0 ≤ 1 := by
  have := h.M_nonneg
  refine (min_le_right _ _).trans ?_
  rw [div_le_one (by positivity)]; linarith

theorem step_pos {p : Params} (h : p.Good) (k : ℕ) : 0 < step k p := by
  induction k generalizing p with
  | zero => exact step0_pos h
  | succ k ih => exact lt_min (step0_pos h) (ih h.prol)

theorem step_le_step0 (k : ℕ) (p : Params) : step k p ≤ p.step0 := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact min_le_left _ _

theorem step_succ_le (k : ℕ) (p : Params) : step (k + 1) p ≤ step k p := by
  induction k generalizing p with
  | zero => exact min_le_left _ _
  | succ k ih => exact min_le_min le_rfl (ih p.prol)

theorem step_anti {k k' : ℕ} (h : k ≤ k') (p : Params) : step k' p ≤ step k p := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (step_succ_le _ p).trans ih

end Params

/-! ### Smooth characteristic setups -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A **smooth characteristic setup** with parameters `p`: characteristic data with complementary
contractive projections, densities depending only on their own characteristic part, `C^∞`
field and densities with derivatives of order `≤ m` bounded by `M` on open convex sets
`U_F ⊇ K` and `U_g ⊇ K ∪ Π±K`, and a `C^∞`, `2π`-periodic reference solution `(Z, λ)` of the
characteristic system on the slab `[t₀, t₁]` with derivatives of orders `1, …, m` bounded by `D`,
whose `δ`-tube lies in the convex chart `K`. -/
structure SmoothSetup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Params) where
  c : CharData V
  K : Set V
  UF : Set V
  Ug : Set V
  Z : ℝ × ℝ → V
  lam : ℝ × ℝ → ℝ
  proj : c.Proj
  gp_proj : ∀ v, c.gp (c.Pp v) = c.gp v
  gm_proj : ∀ v, c.gm (c.Pm v) = c.gm v
  UF_open : IsOpen UF
  UF_convex : Convex ℝ UF
  Ug_open : IsOpen Ug
  Ug_convex : Convex ℝ Ug
  K_convex : Convex ℝ K
  K_UF : K ⊆ UF
  K_Ug : K ⊆ Ug
  Pp_K : ∀ v ∈ K, c.Pp v ∈ Ug
  Pm_K : ∀ v ∈ K, c.Pm v ∈ Ug
  F_bd : DerivBound c.F UF p.m p.M
  gp_bd : DerivBound c.gp Ug p.m p.M
  gm_bd : DerivBound c.gm Ug p.m p.M
  Z_smooth : ContDiff ℝ ∞ Z
  lam_smooth : ContDiff ℝ ∞ lam
  Z_per : ∀ q : ℝ × ℝ, Z (q.1, q.2 + 2 * Real.pi) = Z q
  lam_per : ∀ q : ℝ × ℝ, lam (q.1, q.2 + 2 * Real.pi) = lam q
  Z_bd : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ → ∀ i, 1 ≤ i → i ≤ p.m →
    ‖iteratedFDeriv ℝ i Z q‖ ≤ p.D
  lam_bd : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ → ∀ i, 1 ≤ i → i ≤ p.m →
    ‖iteratedFDeriv ℝ i lam q‖ ≤ p.D
  char_plus : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ →
    c.Pp (fderiv ℝ Z q (1, -1)) = c.Pp (c.F (Z q))
  char_minus : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ →
    c.Pm (fderiv ℝ Z q (1, 1)) = c.Pm (c.F (Z q))
  char_zero : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ →
    c.P0 (fderiv ℝ Z q (1, 0)) = c.P0 (c.F (Z q))
  char_lam : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ →
    fderiv ℝ lam q (1, 0) = c.gp (Z q) + c.gm (Z q)
  tube : ∀ q : ℝ × ℝ, q.1 ∈ Icc p.t₀ p.t₁ → ∀ v, ‖v - Z q‖ ≤ p.δ → v ∈ K
  good : p.Good

namespace SmoothSetup

variable {p : Params} (S : SmoothSetup V p)

/-- A smooth characteristic setup of order `m ≥ 3` is a characteristic Strang setup, with
`B = L = M_F = L_g = M_g = M`. -/
def toStrang (hm : 3 ≤ p.m) : StrangSetup V where
  Z := S.Z
  lam := S.lam
  F := S.c.F
  gp := S.c.gp
  gm := S.c.gm
  Pp := S.c.Pp
  Pm := S.c.Pm
  P0 := S.c.P0
  K := S.K
  t₀ := p.t₀
  t₁ := p.t₁
  δ := p.δ
  B := p.M
  L := p.M
  M := p.M
  Lg := p.M
  Mg := p.M
  D := p.D
  proj_sum := S.proj.sum
  norm_Pp := S.proj.norm_Pp
  norm_Pm := S.proj.norm_Pm
  norm_P0 := S.proj.norm_P0
  Z_smooth := contDiff_infty.1 S.Z_smooth 3
  lam_smooth := contDiff_infty.1 S.lam_smooth 3
  Z_bound1 q hq := S.Z_bd q hq 1 le_rfl (by omega)
  Z_bound2 q hq := S.Z_bd q hq 2 (by norm_num) (by omega)
  Z_bound3 q hq := S.Z_bd q hq 3 (by norm_num) hm
  lam_bound3 q hq := S.lam_bd q hq 3 (by norm_num) hm
  char_plus := S.char_plus
  char_minus := S.char_minus
  char_zero := S.char_zero
  char_lam := S.char_lam
  δ_pos := S.good.δ_pos
  tube := S.tube
  convex := S.K_convex
  F_bound x hx := S.F_bd.norm_le (S.K_UF hx)
  F_lip x hx y hy := lipschitz_of_derivBound S.UF_open S.UF_convex S.F_bd (by omega)
    (S.K_UF hx) (S.K_UF hy)
  F_symm x hx y hy := symm_of_derivBound S.UF_open S.UF_convex S.F_bd (by omega)
    (S.K_UF hx) (S.K_UF hy)
  gp_lip x hx y hy := by
    rw [← S.gp_proj x, ← S.gp_proj y, map_sub]
    have := lipschitz_of_derivBound S.Ug_open S.Ug_convex S.gp_bd (by omega) (S.Pp_K x hx)
      (S.Pp_K y hy)
    rwa [Real.norm_eq_abs] at this
  gm_lip x hx y hy := by
    rw [← S.gm_proj x, ← S.gm_proj y, map_sub]
    have := lipschitz_of_derivBound S.Ug_open S.Ug_convex S.gm_bd (by omega) (S.Pm_K x hx)
      (S.Pm_K y hy)
    rwa [Real.norm_eq_abs] at this
  gp_symm x hx y hy := by
    have := symm_of_derivBound S.Ug_open S.Ug_convex S.gp_bd (by omega) (S.K_Ug hx) (S.K_Ug hy)
    simpa [Real.norm_eq_abs, smul_eq_mul] using this
  gm_symm x hx y hy := by
    have := symm_of_derivBound S.Ug_open S.Ug_convex S.gm_bd (by omega) (S.K_Ug hx) (S.K_Ug hy)
    simpa [Real.norm_eq_abs, smul_eq_mul] using this
  B_nonneg := S.good.M_nonneg
  L_nonneg := S.good.M_nonneg
  M_nonneg := S.good.M_nonneg
  Lg_nonneg := S.good.M_nonneg
  Mg_nonneg := S.good.M_nonneg
  D_nonneg := S.good.D_nonneg

theorem data_toStrang (hm : 3 ≤ p.m) : StrangCharData.data (S.toStrang hm) = S.c := rfl

variable {N : ℕ} [NeZero N]

/-- **Level-zero one-step error** of a smooth characteristic setup. -/
theorem oneStep0 [CompleteSpace V] (hm : 3 ≤ p.m) (hN : 2 * Real.pi / N ≤ p.step0) (τ : ℝ)
    (hτ : p.t₀ ≤ τ) (hτh : τ + 2 * Real.pi / N ≤ p.t₁) (X A B : CGrid V N)
    (hs : S.c.IsSplit (2 * Real.pi / N) X A B) (he : S.c.Env0 S.K (2 * Real.pi / N) X A B) :
    S.c.dist0 B (sampleGrid S.Z S.lam N (τ + 2 * Real.pi / N)) ≤
      (1 + p.rate0 * (2 * Real.pi / N)) * S.c.dist0 X (sampleGrid S.Z S.lam N τ) +
        p.cons0 * (2 * Real.pi / N) ^ 3 := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hM := S.good.M_nonneg
  have hD := S.good.D_nonneg
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have h2 : ℓ ≤ 1 / (3 * p.M + 1) := hN.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2
  have hstep : ℓ ≤ (S.toStrang hm).stepBound := by
    show ℓ ≤ min (p.δ / (3 * p.M + 6 * p.D + 1)) (1 / (p.M + 1))
    refine le_min (hN.trans (min_le_left _ _)) ?_
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hL : 3 * ℓ * (S.toStrang hm).L ≤ 1 := by show 3 * ℓ * p.M ≤ 1; nlinarith
  have hLg : 2 * (S.toStrang hm).Lg * ℓ ≤ 1 := by show 2 * p.M * ℓ ≤ 1; nlinarith
  exact oneStep_strang (S.toStrang hm) S.proj S.Z_per hstep hL hLg τ hτ hτh X A B hs he

/-! ### The prolonged setup -/

theorem diffQuot_const_le {M R : ℝ} {m : ℕ} (hM : 0 ≤ M) (hR : 0 ≤ R + 1) :
    M * (R + 1 + ((m - 1 : ℕ) : ℝ)) * 2 ^ (m - 1) ≤ M + M * (R + 1 + m) * 2 ^ m := by
  have hc : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le _ _
  have h2m : (2 : ℝ) ^ (m - 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h0 : 0 ≤ R + 1 + ((m - 1 : ℕ) : ℝ) := by positivity
  have hA : (R + 1 + ((m - 1 : ℕ) : ℝ)) * 2 ^ (m - 1) ≤ (R + 1 + m) * 2 ^ m :=
    mul_le_mul (by linarith) h2m (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hA hM
  nlinarith

/-- The chart of the prolonged setup. -/
def prolK (K : Set V) (R ℓ : ℝ) : Set (V × V) := {x | x.1 ∈ K ∧ x.1 + ℓ • x.2 ∈ K ∧ ‖x.2‖ ≤ R}

theorem convex_prolK {K : Set V} (hK : Convex ℝ K) (R ℓ : ℝ) : Convex ℝ (prolK K R ℓ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · simpa using hK hx.1 hy.1 ha hb hab
  · have := hK hx.2.1 hy.2.1 ha hb hab
    convert this using 1
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
    module
  · have := (convex_closedBall (0 : V) R) (mem_closedBall_zero_iff.2 hx.2.2)
      (mem_closedBall_zero_iff.2 hy.2.2) ha hb hab
    simpa using mem_closedBall_zero_iff.1 this

/-- The difference quotient of a smooth map along the `θ`-direction. -/
def thetaQuot {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (ℓ : ℝ) (Z : ℝ × ℝ → G) :
    ℝ × ℝ → G :=
  fun q => ℓ⁻¹ • (Z (q + ((0 : ℝ), ℓ)) - Z q)

theorem thetaQuot_spec {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (Z : ℝ × ℝ → G) (q : ℝ × ℝ) : Z q + ℓ • thetaQuot ℓ Z q = Z (q + ((0 : ℝ), ℓ)) := by
  simp only [thetaQuot, smul_smul, mul_inv_cancel₀ hℓ, one_smul]; abel

theorem fst_of_mem_segment {q z : ℝ × ℝ} {ℓ : ℝ} (hz : z ∈ segment ℝ q (q + ((0 : ℝ), ℓ))) :
    z.1 = q.1 := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, -, rfl⟩ := hz
  simp

/-- **Derivative bounds of the `θ`-difference quotient**: `‖Dⁱ (ℓ⁻¹(Z(· + (0,ℓ)) - Z))(q)‖ ≤ D`
whenever `‖D^{i+1} Z‖ ≤ D` at all points with the same time coordinate. -/
theorem norm_iteratedFDeriv_thetaQuot_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Z : ℝ × ℝ → G} (hZ : ContDiff ℝ ∞ Z) {ℓ D : ℝ} (hℓ : 0 < ℓ) (i : ℕ) {q : ℝ × ℝ}
    (hD : ∀ z : ℝ × ℝ, z.1 = q.1 → ‖iteratedFDeriv ℝ (i + 1) Z z‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (thetaQuot ℓ Z) q‖ ≤ D := by
  have hZs : ContDiff ℝ ∞ (fun q => Z (q + ((0 : ℝ), ℓ))) := hZ.comp (contDiff_id.add contDiff_const)
  have e : iteratedFDeriv ℝ i (thetaQuot ℓ Z) q =
      ℓ⁻¹ • (iteratedFDeriv ℝ i Z (q + ((0 : ℝ), ℓ)) - iteratedFDeriv ℝ i Z q) := by
    unfold thetaQuot
    rw [iteratedFDeriv_const_smul_apply' ((hZs.sub hZ).contDiffAt.of_le
      (by exact_mod_cast le_top))]
    congr 1
    have := iteratedFDeriv_sub_apply (f := fun q => Z (q + ((0 : ℝ), ℓ))) (g := Z) (x := q) (i := i)
      (hZs.contDiffAt.of_le (by exact_mod_cast le_top))
      (hZ.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [iteratedFDeriv_comp_add_right] at this
    exact this
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
  have hmv := (convex_segment q (q + ((0 : ℝ), ℓ))).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := iteratedFDeriv ℝ i Z) (C := D)
    (fun z _ => (hZ.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) z)
    (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hD z (fst_of_mem_segment hz))
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hn : ‖q + ((0 : ℝ), ℓ) - q‖ = ℓ := by
    rw [add_sub_cancel_left, Prod.norm_def]; simp [abs_of_pos hℓ, hℓ.le]
  rw [hn] at hmv
  calc ℓ⁻¹ * ‖iteratedFDeriv ℝ i Z (q + ((0 : ℝ), ℓ)) - iteratedFDeriv ℝ i Z q‖
      ≤ ℓ⁻¹ * (D * ℓ) := mul_le_mul_of_nonneg_left hmv (inv_nonneg.2 hℓ.le)
    _ = D := by field_simp

theorem hasFDerivAt_thetaQuot {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {Z : ℝ × ℝ → G} (hZ : ContDiff ℝ ∞ Z) (ℓ : ℝ) (q : ℝ × ℝ) :
    HasFDerivAt (thetaQuot ℓ Z)
      (ℓ⁻¹ • (fderiv ℝ Z (q + ((0 : ℝ), ℓ)) - fderiv ℝ Z q)) q := by
  have hd : ∀ z, HasFDerivAt Z (fderiv ℝ Z z) z := fun z =>
    ((hZ.differentiable (by simp)) z).hasFDerivAt
  have h1 : HasFDerivAt (fun q => Z (q + ((0 : ℝ), ℓ))) (fderiv ℝ Z (q + ((0 : ℝ), ℓ))) q :=
    (hasFDerivAt_comp_add_right ((0 : ℝ), ℓ)).2 (hd _)
  exact (h1.sub (hd q)).const_smul ℓ⁻¹

/-- **The difference-quotient prolongation of a smooth characteristic setup**, for a spacing
`0 < ℓ ≤ 1` and `m ≥ 1`: data `CharData.prol ℓ`, chart `prolK K R ℓ`, reference
`(Z, ℓ⁻¹(Z(·, · + ℓ) - Z))`, `(ℓ⁻¹(λ(·, · + ℓ) - λ))`, parameters `p.prol`. -/
def prol (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 1 ≤ p.m) : SmoothSetup (V × V) p.prol where
  c := S.c.prol ℓ
  K := prolK S.K p.R ℓ
  UF := diffDom S.UF ℓ (p.R + 1)
  Ug := diffDom S.Ug ℓ (p.R + 1)
  Z q := (S.Z q, thetaQuot ℓ S.Z q)
  lam := thetaQuot ℓ S.lam
  proj := CharData.prol_proj S.proj ℓ
  gp_proj v := by
    simp only [CharData.prol, LinearMap.prodMap_apply]
    rw [← map_smul, ← map_add, S.gp_proj, S.gp_proj]
  gm_proj v := by
    simp only [CharData.prol, LinearMap.prodMap_apply]
    rw [← map_smul, ← map_add, S.gm_proj, S.gm_proj]
  UF_open := isOpen_diffDom S.UF_open ℓ _
  UF_convex := convex_diffDom S.UF_convex ℓ _
  Ug_open := isOpen_diffDom S.Ug_open ℓ _
  Ug_convex := convex_diffDom S.Ug_convex ℓ _
  K_convex := convex_prolK S.K_convex _ _
  K_UF x hx := ⟨S.K_UF hx.1, S.K_UF hx.2.1, by linarith [hx.2.2]⟩
  K_Ug x hx := ⟨S.K_Ug hx.1, S.K_Ug hx.2.1, by linarith [hx.2.2]⟩
  Pp_K x hx := by
    refine ⟨S.Pp_K _ hx.1, ?_, ?_⟩
    · show S.c.Pp x.1 + ℓ • S.c.Pp x.2 ∈ S.Ug
      rw [← map_smul, ← map_add]; exact S.Pp_K _ hx.2.1
    · show ‖S.c.Pp x.2‖ < p.R + 1
      linarith [S.proj.norm_Pp x.2, hx.2.2]
  Pm_K x hx := by
    refine ⟨S.Pm_K _ hx.1, ?_, ?_⟩
    · show S.c.Pm x.1 + ℓ • S.c.Pm x.2 ∈ S.Ug
      rw [← map_smul, ← map_add]; exact S.Pm_K _ hx.2.1
    · show ‖S.c.Pm x.2‖ < p.R + 1
      linarith [S.proj.norm_Pm x.2, hx.2.2]
  F_bd := by
    have hm' : p.m = (p.m - 1) + 1 := by omega
    have hR : 0 ≤ p.R + 1 := by linarith [S.good.R_ge, S.good.D_nonneg]
    have hM := S.good.M_nonneg
    have hF : DerivBound S.c.F S.UF ((p.m - 1) + 1) p.M := by rw [← hm']; exact S.F_bd
    have h1 : DerivBound (fun x : V × V => S.c.F x.1) (diffDom S.UF ℓ (p.R + 1)) (p.m - 1) p.M := by
      have := (S.F_bd.mono (K' := p.m - 1) (by omega) le_rfl).comp_clm S.UF_open
        (ContinuousLinearMap.fst ℝ V V) (U := diffDom S.UF ℓ (p.R + 1)) (fun x hx => hx.1)
      refine (this.congr fun x => rfl).mono le_rfl ?_
      have : max 1 ‖ContinuousLinearMap.fst ℝ V V‖ = 1 :=
        max_eq_left (ContinuousLinearMap.norm_fst_le ℝ V V)
      rw [this, one_pow, mul_one]
    have h2 := derivBound_diffQuot S.UF_open S.UF_convex hF hℓ hℓ1 hR
    have h3 := h1.prod h2 (isOpen_diffDom S.UF_open ℓ _) hM (by positivity)
    refine h3.mono le_rfl ?_
    show p.M + p.M * (p.R + 1 + ↑(p.m - 1)) * 2 ^ (p.m - 1) ≤
      p.M + p.M * (p.R + 1 + p.m) * 2 ^ p.m
    have h4 := diffQuot_const_le (m := p.m) hM hR
    have h5 : p.M * (p.R + 1 + ↑(p.m - 1)) * 2 ^ (p.m - 1) ≤ p.M * (p.R + 1 + p.m) * 2 ^ p.m := by
      have hc : ((p.m - 1 : ℕ) : ℝ) ≤ p.m := by exact_mod_cast Nat.sub_le _ _
      have h2m : (2 : ℝ) ^ (p.m - 1) ≤ 2 ^ p.m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have h0 : 0 ≤ p.R + 1 + ((p.m - 1 : ℕ) : ℝ) := by positivity
      have hA : (p.R + 1 + ((p.m - 1 : ℕ) : ℝ)) * 2 ^ (p.m - 1) ≤ (p.R + 1 + p.m) * 2 ^ p.m :=
        mul_le_mul (by linarith) h2m (by positivity) (by linarith)
      have := mul_le_mul_of_nonneg_left hA hM
      linarith [show p.M * (p.R + 1 + ↑(p.m - 1)) * 2 ^ (p.m - 1) =
        p.M * ((p.R + 1 + ↑(p.m - 1)) * 2 ^ (p.m - 1)) by ring,
        show p.M * (p.R + 1 + ↑p.m) * 2 ^ p.m = p.M * ((p.R + 1 + ↑p.m) * 2 ^ p.m) by ring]
    linarith
  gp_bd := by
    have hm' : p.m = (p.m - 1) + 1 := by omega
    have hR : 0 ≤ p.R + 1 := by linarith [S.good.R_ge, S.good.D_nonneg]
    have hM := S.good.M_nonneg
    have hg : DerivBound S.c.gp S.Ug ((p.m - 1) + 1) p.M := by rw [← hm']; exact S.gp_bd
    have h2 := derivBound_diffQuot S.Ug_open S.Ug_convex hg hℓ hℓ1 hR
    refine (h2.congr fun x => smul_eq_mul _ _).mono le_rfl ?_
    exact diffQuot_const_le hM hR
  gm_bd := by
    have hm' : p.m = (p.m - 1) + 1 := by omega
    have hR : 0 ≤ p.R + 1 := by linarith [S.good.R_ge, S.good.D_nonneg]
    have hM := S.good.M_nonneg
    have hg : DerivBound S.c.gm S.Ug ((p.m - 1) + 1) p.M := by rw [← hm']; exact S.gm_bd
    have h2 := derivBound_diffQuot S.Ug_open S.Ug_convex hg hℓ hℓ1 hR
    refine (h2.congr fun x => smul_eq_mul _ _).mono le_rfl ?_
    exact diffQuot_const_le hM hR
  Z_smooth := S.Z_smooth.prodMk
    (((S.Z_smooth.comp (contDiff_id.add contDiff_const)).sub S.Z_smooth).const_smul ℓ⁻¹)
  lam_smooth := ((S.lam_smooth.comp (contDiff_id.add contDiff_const)).sub S.lam_smooth).const_smul
    ℓ⁻¹
  Z_per q := by
    have e : ((q.1, q.2 + 2 * Real.pi) : ℝ × ℝ) + ((0 : ℝ), ℓ) =
        ((q + ((0 : ℝ), ℓ)).1, (q + ((0 : ℝ), ℓ)).2 + 2 * Real.pi) := by
      ext <;> simp; ring
    simp only [thetaQuot, e, S.Z_per]
  lam_per q := by
    have e : ((q.1, q.2 + 2 * Real.pi) : ℝ × ℝ) + ((0 : ℝ), ℓ) =
        ((q + ((0 : ℝ), ℓ)).1, (q + ((0 : ℝ), ℓ)).2 + 2 * Real.pi) := by
      ext <;> simp; ring
    simp only [thetaQuot, e, S.lam_per]
  Z_bd q hq i hi1 him := by
    have him' : i + 1 ≤ p.m := by simp only [Params.prol] at him; omega
    have hW : ContDiff ℝ ∞ (thetaQuot ℓ S.Z) :=
      ((S.Z_smooth.comp (contDiff_id.add contDiff_const)).sub S.Z_smooth).const_smul ℓ⁻¹
    have e : (fun q => (S.Z q, thetaQuot ℓ S.Z q)) = fun q =>
        ContinuousLinearMap.inl ℝ V V (S.Z q) + ContinuousLinearMap.inr ℝ V V (thetaQuot ℓ S.Z q) := by
      funext q; simp
    have hadd : iteratedFDeriv ℝ i (fun q =>
        ContinuousLinearMap.inl ℝ V V (S.Z q) + ContinuousLinearMap.inr ℝ V V (thetaQuot ℓ S.Z q)) q =
        iteratedFDeriv ℝ i (fun q => ContinuousLinearMap.inl ℝ V V (S.Z q)) q +
          iteratedFDeriv ℝ i (fun q => ContinuousLinearMap.inr ℝ V V (thetaQuot ℓ S.Z q)) q :=
      iteratedFDeriv_add_apply
        (((ContinuousLinearMap.inl ℝ V V).contDiff.comp S.Z_smooth).contDiffAt.of_le
          (by exact_mod_cast le_top))
        (((ContinuousLinearMap.inr ℝ V V).contDiff.comp hW).contDiffAt.of_le
          (by exact_mod_cast le_top))
    rw [e, hadd]
    have h1 : ‖iteratedFDeriv ℝ i (fun q => ContinuousLinearMap.inl ℝ V V (S.Z q)) q‖ ≤
        ‖ContinuousLinearMap.inl ℝ V V‖ * ‖iteratedFDeriv ℝ i S.Z q‖ :=
      (ContinuousLinearMap.inl ℝ V V).norm_iteratedFDeriv_comp_left (n := i)
        (S.Z_smooth.contDiffAt (x := q)) (by exact_mod_cast le_top)
    have h2 : ‖iteratedFDeriv ℝ i (fun q => ContinuousLinearMap.inr ℝ V V (thetaQuot ℓ S.Z q)) q‖ ≤
        ‖ContinuousLinearMap.inr ℝ V V‖ * ‖iteratedFDeriv ℝ i (thetaQuot ℓ S.Z) q‖ :=
      (ContinuousLinearMap.inr ℝ V V).norm_iteratedFDeriv_comp_left (n := i)
        (hW.contDiffAt (x := q)) (by exact_mod_cast le_top)
    have b1 : ‖iteratedFDeriv ℝ i S.Z q‖ ≤ p.D := S.Z_bd q hq i hi1 (by omega)
    have b2 : ‖iteratedFDeriv ℝ i (thetaQuot ℓ S.Z) q‖ ≤ p.D :=
      norm_iteratedFDeriv_thetaQuot_le S.Z_smooth hℓ i fun z hz =>
        S.Z_bd z (by rw [hz]; exact hq) (i + 1) (by omega) him'
    have n1 := ContinuousLinearMap.norm_inl_le_one ℝ V V
    have n2 := ContinuousLinearMap.norm_inr_le_one ℝ V V
    show _ ≤ 2 * p.D
    refine (norm_add_le _ _).trans ?_
    have := mul_le_mul n1 b1 (norm_nonneg _) zero_le_one
    have := mul_le_mul n2 b2 (norm_nonneg _) zero_le_one
    linarith
  lam_bd q hq i hi1 him := by
    have him' : i + 1 ≤ p.m := by simp only [Params.prol] at him; omega
    have := norm_iteratedFDeriv_thetaQuot_le S.lam_smooth hℓ i (q := q) fun z hz =>
      S.lam_bd z (by rw [hz]; exact hq) (i + 1) (by omega) him'
    show _ ≤ 2 * p.D
    linarith [S.good.D_nonneg]
  char_plus q hq := by
    have hq' : (q + ((0 : ℝ), ℓ)).1 ∈ Icc p.t₀ p.t₁ := by
      simp only [Prod.fst_add, add_zero]; exact hq
    have hd := (((S.Z_smooth.differentiable (by simp)) q).hasFDerivAt.prodMk
      (hasFDerivAt_thetaQuot S.Z_smooth ℓ q)).fderiv
    rw [hd]
    simp only [CharData.prol, LinearMap.prodMap_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, map_smul, map_sub]
    rw [S.char_plus q hq, S.char_plus _ hq', thetaQuot_spec hℓ.ne']
  char_minus q hq := by
    have hq' : (q + ((0 : ℝ), ℓ)).1 ∈ Icc p.t₀ p.t₁ := by
      simp only [Prod.fst_add, add_zero]; exact hq
    have hd := (((S.Z_smooth.differentiable (by simp)) q).hasFDerivAt.prodMk
      (hasFDerivAt_thetaQuot S.Z_smooth ℓ q)).fderiv
    rw [hd]
    simp only [CharData.prol, LinearMap.prodMap_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, map_smul, map_sub]
    rw [S.char_minus q hq, S.char_minus _ hq', thetaQuot_spec hℓ.ne']
  char_zero q hq := by
    have hq' : (q + ((0 : ℝ), ℓ)).1 ∈ Icc p.t₀ p.t₁ := by
      simp only [Prod.fst_add, add_zero]; exact hq
    have hd := (((S.Z_smooth.differentiable (by simp)) q).hasFDerivAt.prodMk
      (hasFDerivAt_thetaQuot S.Z_smooth ℓ q)).fderiv
    rw [hd]
    simp only [CharData.prol, LinearMap.prodMap_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, map_smul, map_sub]
    rw [S.char_zero q hq, S.char_zero _ hq', thetaQuot_spec hℓ.ne']
  char_lam q hq := by
    have hq' : (q + ((0 : ℝ), ℓ)).1 ∈ Icc p.t₀ p.t₁ := by
      simp only [Prod.fst_add, add_zero]; exact hq
    rw [(hasFDerivAt_thetaQuot S.lam_smooth ℓ q).fderiv]
    simp only [CharData.prol, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      smul_eq_mul]
    rw [S.char_lam q hq, S.char_lam _ hq', thetaQuot_spec hℓ.ne']
    ring
  tube q hq v hv := by
    have hq' : (q + ((0 : ℝ), ℓ)).1 ∈ Icc p.t₀ p.t₁ := by
      simp only [Prod.fst_add, add_zero]; exact hq
    have hδ1 := S.good.δ_le
    have hδ0 := S.good.δ_pos
    have hv' : ‖v - (S.Z q, thetaQuot ℓ S.Z q)‖ ≤ p.δ / 2 := hv
    rw [Prod.norm_def] at hv'
    simp only [Prod.fst_sub, Prod.snd_sub] at hv'
    have h1 : ‖v.1 - S.Z q‖ ≤ p.δ / 2 := (le_max_left _ _).trans hv'
    have h2 : ‖v.2 - thetaQuot ℓ S.Z q‖ ≤ p.δ / 2 := (le_max_right _ _).trans hv'
    refine ⟨S.tube q hq _ (by linarith), S.tube _ hq' _ ?_, ?_⟩
    · have e : v.1 + ℓ • v.2 - S.Z (q + ((0 : ℝ), ℓ)) =
          (v.1 - S.Z q) + ℓ • (v.2 - thetaQuot ℓ S.Z q) := by
        rw [← thetaQuot_spec hℓ.ne' S.Z q, smul_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
      have := mul_le_mul hℓ1 h2 (norm_nonneg _) zero_le_one
      linarith
    · have hW : ‖thetaQuot ℓ S.Z q‖ ≤ p.D := by
        have := norm_iteratedFDeriv_thetaQuot_le S.Z_smooth hℓ 0 (q := q) fun z hz =>
          S.Z_bd z (by rw [hz]; exact hq) 1 le_rfl (by omega)
        rwa [norm_iteratedFDeriv_zero] at this
      have := norm_le_norm_add_norm_sub' v.2 (thetaQuot ℓ S.Z q)
      linarith [S.good.R_ge]
  good := S.good.prol

theorem prol_c (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 1 ≤ p.m) :
    (S.prol ℓ hℓ hℓ1 hm).c = S.c.prol ℓ := rfl

theorem prol_K (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hm : 1 ≤ p.m) :
    (S.prol ℓ hℓ hℓ1 hm).K = prolK S.K p.R ℓ := rfl

/-- The sampling of the prolonged reference is the prolongation of the sampling. -/
theorem sample_prol (hℓ : 0 < 2 * Real.pi / N) (hℓ1 : 2 * Real.pi / N ≤ 1) (hm : 1 ≤ p.m)
    (τ : ℝ) :
    sampleGrid (S.prol _ hℓ hℓ1 hm).Z (S.prol _ hℓ hℓ1 hm).lam N τ =
      (sampleGrid S.Z S.lam N τ).prol (2 * Real.pi / N) := by
  have eZ : ∀ j : ZMod N, S.Z ((τ, GowdyStaggered.sampleAngle N j) + ((0 : ℝ), 2 * Real.pi / N)) =
      S.Z (τ, GowdyStaggered.sampleAngle N (j + 1)) := by
    intro j
    rw [GowdyStaggered.sample_succ S.Z S.Z_per N τ j]; simp
  have el : ∀ j : ZMod N, S.lam ((τ, GowdyStaggered.sampleAngle N j) +
      ((0 : ℝ), 2 * Real.pi / N)) = S.lam (τ, GowdyStaggered.sampleAngle N (j + 1)) := by
    intro j
    rw [GowdyStaggered.sample_succ S.lam S.lam_per N τ j]; simp
  ext j
  · rfl
  · simp only [sampleGrid, prol, CGrid.prol, prolArr, thetaQuot, PeriodicGridResidual.fwdDiff]
    rw [eZ]
  · simp only [sampleGrid, prol, CGrid.prol, thetaQuot, PeriodicGridResidual.fwdDiff]
    rw [el]

end SmoothSetup

/-! ### The `C^k_ℓ` envelope -/

namespace CharData

variable {c : CharData V} {N : ℕ}

/-- The midpoint array `j ↦ (X_j + A_j)/2`. -/
def midA (X A : CGrid V N) : ZMod N → V := fun j => (1 / 2 : ℝ) • (X.site j + A.site j)

variable (c) in
/-- The `C^k_ℓ` envelope of a split step `X → A → B`: the stage midpoints and the transported
inputs lie in `K` and their forward differences of orders `1, …, k` have sup norm `≤ R`. -/
def EnvK [NeZero N] (k : ℕ) (K : Set V) (R ℓ : ℝ) (X A B : CGrid V N) : Prop :=
  c.Env0 K ℓ X A B ∧ ∀ i, 1 ≤ i → i ≤ k →
    ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (midA X A)‖ ≤ R ∧
    ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] A.site‖ ≤ R ∧
    ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (midA (c.transport ℓ A) B)‖ ≤ R

theorem midA_prol (ℓ : ℝ) (X A : CGrid V N) :
    midA (X.prol ℓ) (A.prol ℓ) = prolArr ℓ (midA X A) := by
  funext j
  simp only [midA, CGrid.prol, prolArr, PeriodicGridResidual.fwdDiff, Prod.mk_add_mk,
    Prod.smul_mk]
  congr 1
  module

theorem EnvK.mono [NeZero N] {k k' : ℕ} (hk : k ≤ k') {K : Set V} {R ℓ : ℝ} {X A B : CGrid V N}
    (h : c.EnvK k' K R ℓ X A B) : c.EnvK k K R ℓ X A B :=
  ⟨h.1, fun i h1 h2 => h.2 i h1 (h2.trans hk)⟩

theorem prolArr_mem_prolK [NeZero N] {ℓ R : ℝ} (hℓ : ℓ ≠ 0) {K : Set V} {v : ZMod N → V}
    (hv : ∀ j, v j ∈ K) (hd : ‖PeriodicGridResidual.fwdDiff ℓ v‖ ≤ R) (j : ZMod N) :
    prolArr ℓ v j ∈ SmoothSetup.prolK K R ℓ :=
  ⟨hv j, by
    show v j + ℓ • PeriodicGridResidual.fwdDiff ℓ v j ∈ K
    rw [add_smul_fwdDiff hℓ]; exact hv (j + 1),
    (norm_le_pi_norm _ j).trans hd⟩

theorem norm_iterate_prolArr_le [NeZero N] {ℓ R : ℝ} {v : ZMod N → V} {i : ℕ}
    (h1 : ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖ ≤ R)
    (h2 : ‖(PeriodicGridResidual.fwdDiff ℓ)^[i + 1] v‖ ≤ R) :
    ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (prolArr ℓ v)‖ ≤ R := by
  rw [iterate_fwdDiff_prolArr]
  refine norm_pair_le h1 ?_
  rwa [← Function.iterate_succ_apply' (PeriodicGridResidual.fwdDiff ℓ)]

/-- **The envelope is inherited by the prolongation**: `EnvK (k+1)` of a split step implies
`EnvK k` of its prolongation, in the prolonged chart. -/
theorem envK_prol [NeZero N] {k : ℕ} {K : Set V} {R R' ℓ : ℝ} (hℓ : ℓ ≠ 0) (hRR : R ≤ R')
    {X A B : CGrid V N} (h : c.EnvK (k + 1) K R ℓ X A B) :
    (c.prol ℓ).EnvK k (SmoothSetup.prolK K R ℓ) R' ℓ (X.prol ℓ) (A.prol ℓ) (B.prol ℓ) := by
  obtain ⟨h0, hd⟩ := h
  have hd1 := hd 1 le_rfl (by omega)
  have htr : (c.prol ℓ).transport ℓ (A.prol ℓ) = (c.transport ℓ A).prol ℓ :=
    (prol_transport hℓ A).symm
  refine ⟨fun j => ⟨?_, ?_, ?_⟩, fun i hi1 hik => ⟨?_, ?_, ?_⟩⟩
  · have := prolArr_mem_prolK hℓ (v := midA X A) (fun j => (h0 j).1) hd1.1 j
    rwa [← midA_prol] at this
  · exact prolArr_mem_prolK hℓ (v := A.site) (fun j => (h0 j).2.1) hd1.2.1 j
  · rw [htr]
    have := prolArr_mem_prolK hℓ (v := midA (c.transport ℓ A) B) (fun j => (h0 j).2.2)
      hd1.2.2 j
    rwa [← midA_prol] at this
  · show ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (midA (X.prol ℓ) (A.prol ℓ))‖ ≤ R'
    rw [midA_prol]
    exact (norm_iterate_prolArr_le (hd i hi1 (by omega)).1 (hd (i + 1) (by omega)
      (by omega)).1).trans hRR
  · exact (norm_iterate_prolArr_le (hd i hi1 (by omega)).2.1 (hd (i + 1) (by omega)
      (by omega)).2.1).trans hRR
  · show ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (midA ((c.prol ℓ).transport ℓ (A.prol ℓ))
      (B.prol ℓ))‖ ≤ R'
    rw [htr, midA_prol]
    exact (norm_iterate_prolArr_le (hd i hi1 (by omega)).2.2 (hd (i + 1) (by omega)
      (by omega)).2.2).trans hRR

end CharData

/-! ### The one-step error at every level -/

open CharData

/-- **One-step error in the characteristic `C^k_ℓ` distance**, for every `k` with `m ≥ 3 + k`:
`distK k (B, 𝖲X_*(τ+ℓ)) ≤ (1 + K_k ℓ) distK k (X, 𝖲X_*(τ)) + C_k ℓ³`, with `K_k, C_k` depending
only on the parameters (proof: the `k`-fold prolongation and the level-zero estimate). -/
theorem SmoothSetup.oneStepK (k : ℕ) : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {p : Params} (S : SmoothSetup V p), 3 + k ≤ p.m →
    ∀ {N : ℕ} [NeZero N], 2 * Real.pi / N ≤ Params.step k p → ∀ τ : ℝ, p.t₀ ≤ τ →
    τ + 2 * Real.pi / N ≤ p.t₁ → ∀ X A B : CGrid V N,
    S.c.IsSplit (2 * Real.pi / N) X A B → S.c.EnvK k S.K p.R (2 * Real.pi / N) X A B →
    S.c.distK k (2 * Real.pi / N) B (sampleGrid S.Z S.lam N (τ + 2 * Real.pi / N)) ≤
      (1 + Params.rate k p * (2 * Real.pi / N)) *
        S.c.distK k (2 * Real.pi / N) X (sampleGrid S.Z S.lam N τ) +
        Params.cons k p * (2 * Real.pi / N) ^ 3 := by
  induction k with
  | zero =>
    intro V _ _ _ p S hm N _ hN τ hτ hτh X A B hs he
    exact S.oneStep0 (by omega) hN τ hτ hτh X A B hs he.1
  | succ k ih =>
    intro V _ _ _ p S hm N _ hN τ hτ hτh X A B hs he
    set ℓ := 2 * Real.pi / N with hℓdef
    have hℓ : 0 < ℓ := by
      have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
      positivity
    have hℓ1 : ℓ ≤ 1 := hN.trans ((Params.step_le_step0 _ p).trans (Params.step0_le_one S.good))
    have hm1 : 1 ≤ p.m := by omega
    have hN' : ℓ ≤ Params.step k p.prol := hN.trans (min_le_right _ _)
    have hm' : 3 + k ≤ p.prol.m := by simp only [Params.prol]; omega
    have h := ih (S.prol ℓ hℓ hℓ1 hm1) hm' hN' τ hτ hτh (X.prol ℓ) (A.prol ℓ) (B.prol ℓ)
      (prol_isSplit hℓ.ne' hs) (envK_prol hℓ.ne' (by
        show p.R ≤ 2 * p.R; linarith [S.good.R_ge, S.good.D_nonneg]) he)
    rw [S.sample_prol hℓ hℓ1 hm1, S.sample_prol hℓ hℓ1 hm1, SmoothSetup.prol_c, distK_prol,
      distK_prol] at h
    rw [Params.rate_succ, Params.cons_succ]
    exact h

/-! ### The global error -/

/-- Discrete Grönwall on a finite horizon. -/
theorem gronwall_finite' {u b : ℕ → ℝ} {c : ℝ} {n₀ : ℕ} (hc : 0 ≤ c) (hb : ∀ m, 0 ≤ b m)
    (hstep : ∀ m < n₀, u (m + 1) ≤ (1 + c) * u m + b m) (hu : ∀ m, 0 ≤ u m) :
    ∀ n ≤ n₀, u n ≤ (u 0 + ∑ k ∈ range n, b k) * Real.exp (n * c) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have h1 : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
    have hS : 0 ≤ u 0 + ∑ k ∈ range n, b k :=
      add_nonneg (hu 0) (Finset.sum_nonneg fun k _ => hb k)
    have hE : Real.exp ((n + 1 : ℕ) * c) = Real.exp c * Real.exp (n * c) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hE1 : 1 ≤ Real.exp ((n + 1 : ℕ) * c) := Real.one_le_exp (by positivity)
    calc u (n + 1) ≤ (1 + c) * u n + b n := hstep n (by omega)
      _ ≤ Real.exp c * ((u 0 + ∑ k ∈ range n, b k) * Real.exp (n * c)) +
            b n * Real.exp ((n + 1 : ℕ) * c) := by
          refine add_le_add ?_ (le_mul_of_one_le_right (hb n) hE1)
          exact mul_le_mul h1 ih (hu n) (Real.exp_pos c).le
      _ = (u 0 + ∑ k ∈ range (n + 1), b k) * Real.exp ((n + 1 : ℕ) * c) := by
          rw [Finset.sum_range_succ, hE]; ring

namespace SmoothSetup

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {p : Params}
  (S : SmoothSetup V p) {N : ℕ} [NeZero N]

/-- **Global error at level `k`** (discrete Grönwall): for a numerical history realised by split
steps `X_n → A_n → B_n` in the `C^k_ℓ` envelope, with arbitrary next states `X_{n+1}`,
`distK k (X_n, 𝖲X_*(τ₀+nℓ)) ≤ (distK k (X₀, 𝖲X_*(τ₀)) + Σ_{i<n} distK k (X_{i+1}, B_i)
  + C_k (t₁ - t₀) ℓ²) e^{K_k (t₁ - t₀)}`. -/
theorem global_error_distK (k : ℕ) (hm : 3 + k ≤ p.m) (hN : 2 * Real.pi / N ≤ Params.step k p)
    (τ₀ : ℝ) (n₀ : ℕ) (hτ₀ : p.t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ p.t₁)
    (X A B : ℕ → CGrid V N)
    (hstep : ∀ n < n₀, S.c.IsSplit (2 * Real.pi / N) (X n) (A n) (B n) ∧
      S.c.EnvK k S.K p.R (2 * Real.pi / N) (X n) (A n) (B n)) :
    ∀ n ≤ n₀, S.c.distK k (2 * Real.pi / N) (X n)
        (sampleGrid S.Z S.lam N (τ₀ + n * (2 * Real.pi / N))) ≤
      (S.c.distK k (2 * Real.pi / N) (X 0) (sampleGrid S.Z S.lam N τ₀) +
        ∑ i ∈ range n, S.c.distK k (2 * Real.pi / N) (X (i + 1)) (B i) +
        Params.cons k p * (p.t₁ - p.t₀) * (2 * Real.pi / N) ^ 2) *
        Real.exp (Params.rate k p * (p.t₁ - p.t₀)) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  set K := Params.rate k p
  have hK : 0 ≤ K := Params.rate_nonneg S.good k
  set C := Params.cons k p
  have hC : 0 ≤ C := Params.cons_nonneg S.good k
  set u : ℕ → ℝ := fun m => S.c.distK k ℓ (X m) (sampleGrid S.Z S.lam N (τ₀ + m * ℓ))
  set b : ℕ → ℝ := fun m => S.c.distK k ℓ (X (m + 1)) (B m) + C * ℓ ^ 3
  have hrec : ∀ m < n₀, u (m + 1) ≤ (1 + K * ℓ) * u m + b m := by
    intro m hm'
    have hτm : p.t₀ ≤ τ₀ + m * ℓ := by
      have : 0 ≤ (m : ℝ) * ℓ := by positivity
      linarith
    have hm'' : ((m + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hm'
    have hτh : τ₀ + m * ℓ + ℓ ≤ p.t₁ := by
      have : ((m + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right hm'' hℓpos.le
      push_cast at this
      linarith
    have h1 := S.oneStepK k hm hN (τ₀ + m * ℓ) hτm hτh (X m) (A m) (B m) (hstep m hm').1
      (hstep m hm').2
    have e : τ₀ + ((m + 1 : ℕ) : ℝ) * ℓ = τ₀ + m * ℓ + ℓ := by push_cast; ring
    show S.c.distK k ℓ (X (m + 1)) (sampleGrid S.Z S.lam N (τ₀ + ((m + 1 : ℕ) : ℝ) * ℓ)) ≤ _
    rw [e]
    have ht := distK_triangle (c := S.c) k ℓ (X (m + 1)) (B m)
      (sampleGrid S.Z S.lam N (τ₀ + m * ℓ + ℓ))
    simp only [u, b]
    linarith
  have hb0 : ∀ m, 0 ≤ b m := fun m => add_nonneg (distK_nonneg _ _ _ _) (by positivity)
  have hg := gronwall_finite' (u := u) (b := b) (c := K * ℓ) (n₀ := n₀) (by positivity)
    hb0 hrec (fun m => distK_nonneg _ _ _ _)
  intro n hn
  have hgn := hg n hn
  have hu0 : u 0 = S.c.distK k ℓ (X 0) (sampleGrid S.Z S.lam N τ₀) := by simp [u]
  have hnl : (n : ℝ) * ℓ ≤ p.t₁ - p.t₀ := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
    have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
    linarith
  have hsum : ∑ i ∈ range n, b i ≤ ∑ i ∈ range n, S.c.distK k ℓ (X (i + 1)) (B i) +
      C * (p.t₁ - p.t₀) * ℓ ^ 2 := by
    simp only [b, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (n : ℝ) * (C * ℓ ^ 3) ≤ C * (p.t₁ - p.t₀) * ℓ ^ 2 := by
      have : (n : ℝ) * (C * ℓ ^ 3) = C * ℓ ^ 2 * ((n : ℝ) * ℓ) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hnl (by positivity : 0 ≤ C * ℓ ^ 2)
      linarith
    linarith
  have hexp : Real.exp (n * (K * ℓ)) ≤ Real.exp (K * (p.t₁ - p.t₀)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hnl hK
    linarith
  have hS0 : 0 ≤ u 0 + ∑ i ∈ range n, b i :=
    add_nonneg (distK_nonneg _ _ _ _) (Finset.sum_nonneg fun i _ => hb0 i)
  calc u n ≤ (u 0 + ∑ i ∈ range n, b i) * Real.exp (n * (K * ℓ)) := hgn
    _ ≤ (u 0 + ∑ i ∈ range n, b i) * Real.exp (K * (p.t₁ - p.t₀)) :=
        mul_le_mul_of_nonneg_left hexp hS0
    _ ≤ _ := by
        rw [hu0] at hS0 ⊢
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith

theorem crNorm_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r : ℕ} (h : k ≤ r)
    (ℓ : ℝ) (v : ZMod N → E) :
    PeriodicGridResidual.crNorm k ℓ v ≤ PeriodicGridResidual.crNorm r ℓ v :=
  Finset.sup'_le _ _ fun i hi => Finset.le_sup' (fun i => ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖)
    (mem_range.2 (lt_of_lt_of_le (mem_range.1 hi) (Nat.succ_le_succ h)))

/-- The combined rate `Σ_{k ≤ r} K_k`. -/
def rateR (r : ℕ) (p : Params) : ℝ := ∑ k ∈ range (r + 1), Params.rate k p

/-- The combined consistency constant `Σ_{k ≤ r} C_k`. -/
def consR (r : ℕ) (p : Params) : ℝ := ∑ k ∈ range (r + 1), Params.cons k p

/-- **The `C^r_ℓ` global error of characteristic Strang splitting** (`eq:supp-gowdy-state-error`
for a smooth characteristic setup of order `m ≥ 3 + r`): for a numerical history realised by
split steps in the `C^r_ℓ` envelope, with residual arrays `r_i = X_{i+1} - B_i`,
`‖X_n - 𝖲X_*(τ₀+nℓ)‖_{r,∞,ℓ} ≤ 3 (‖X₀ - 𝖲X_*(τ₀)‖_{r,∞,ℓ} + Σ_{i<n} ‖r_i‖_{r,∞,ℓ}
  + C (t₁ - t₀) ℓ²) e^{K (t₁ - t₀)}`, `C = consR r p`, `K = rateR r p`. -/
theorem global_error_crNorm (r : ℕ) (hm : 3 + r ≤ p.m) (hN : 2 * Real.pi / N ≤ Params.step r p)
    (τ₀ : ℝ) (n₀ : ℕ) (hτ₀ : p.t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ p.t₁)
    (X A B : ℕ → CGrid V N)
    (hstep : ∀ n < n₀, S.c.IsSplit (2 * Real.pi / N) (X n) (A n) (B n) ∧
      S.c.EnvK r S.K p.R (2 * Real.pi / N) (X n) (A n) (B n)) :
    ∀ n ≤ n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
        (errA (X n) (sampleGrid S.Z S.lam N (τ₀ + n * (2 * Real.pi / N)))) ≤
      3 * ((PeriodicGridResidual.crNorm r (2 * Real.pi / N)
          (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
        ∑ i ∈ range n, PeriodicGridResidual.crNorm r (2 * Real.pi / N) (errA (X (i + 1)) (B i)) +
        consR r p * (p.t₁ - p.t₀) * (2 * Real.pi / N) ^ 2) *
        Real.exp (rateR r p * (p.t₁ - p.t₀))) := by
  set ℓ := 2 * Real.pi / N with hℓ
  intro n hn
  have hT : 0 ≤ p.t₁ - p.t₀ := by
    have hℓpos : 0 < ℓ := by
      have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
      positivity
    have : 0 ≤ (n₀ : ℝ) * ℓ := by positivity
    linarith
  refine crNorm_le_distK S.proj r ℓ _ _ fun k hk => ?_
  have hk' : k ∈ range (r + 1) := mem_range.2 (Nat.lt_succ_of_le hk)
  have h := S.global_error_distK k (by omega) (hN.trans (Params.step_anti hk p)) τ₀ n₀ hτ₀ hn₀
    X A B (fun n hn => ⟨(hstep n hn).1, (hstep n hn).2.mono hk⟩) n hn
  refine h.trans ?_
  have hK : Params.rate k p ≤ rateR r p :=
    Finset.single_le_sum (f := fun k => Params.rate k p)
      (fun k _ => Params.rate_nonneg S.good k) hk'
  have hC : Params.cons k p ≤ consR r p :=
    Finset.single_le_sum (f := fun k => Params.cons k p)
      (fun k _ => Params.cons_nonneg S.good k) hk'
  have he : Real.exp (Params.rate k p * (p.t₁ - p.t₀)) ≤ Real.exp (rateR r p * (p.t₁ - p.t₀)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hK hT)
  have h0 : S.c.distK k ℓ (X 0) (sampleGrid S.Z S.lam N τ₀) ≤
      PeriodicGridResidual.crNorm r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) :=
    (distK_le_crNorm S.proj k ℓ _ _).trans (crNorm_mono hk ℓ _)
  have hs : ∑ i ∈ range n, S.c.distK k ℓ (X (i + 1)) (B i) ≤
      ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) :=
    Finset.sum_le_sum fun i _ => (distK_le_crNorm S.proj k ℓ _ _).trans (crNorm_mono hk ℓ _)
  have hc : Params.cons k p * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ consR r p * (p.t₁ - p.t₀) * ℓ ^ 2 := by
    gcongr
  have hpos : 0 ≤ S.c.distK k ℓ (X 0) (sampleGrid S.Z S.lam N τ₀) +
      ∑ i ∈ range n, S.c.distK k ℓ (X (i + 1)) (B i) +
      Params.cons k p * (p.t₁ - p.t₀) * ℓ ^ 2 := by
    have := Params.cons_nonneg S.good k
    have : 0 ≤ ∑ i ∈ range n, S.c.distK k ℓ (X (i + 1)) (B i) :=
      Finset.sum_nonneg fun i _ => distK_nonneg _ _ _ _
    have := distK_nonneg (c := S.c) k ℓ (X 0) (sampleGrid S.Z S.lam N τ₀)
    positivity
  exact mul_le_mul (by linarith) he (Real.exp_pos _).le (by linarith)

end SmoothSetup

end

end RenewalGeometry.GridFaaDiBruno
