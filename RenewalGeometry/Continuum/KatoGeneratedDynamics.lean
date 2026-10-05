/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinSecondRate
import RenewalGeometry.Continuum.KatoGalerkinSharpRate

/-!
# The fully finite approximation branch: rates of the generated dynamics

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript, assembling the cutoff-uniform estimates of the
spectral Galerkin and implicit-midpoint discretizations of a quasilinear symmetric hyperbolic
system `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d` into the rates of the theorem, **with general finite
initial data** `U_{0,N}` (`eq:generated-initial-rate`), in the Fourier form of the Sobolev norms.

* `galerkin_uniform_data` — the semidiscrete system from any finite datum `‖U_{0,N}‖_{H^q} ≤ R₀`
  exists on a cutoff-independent interval in the `H^q` ball of radius `2R₀ + 1`.
* **`galerkin_stable_hm`** — `H^m` stability of the semidiscrete system in the data:
  `‖U_N(t) - V_N(t)‖_{H^m} ≤ e^{Kt} ‖U_N(0) - V_N(0)‖_{H^m}` (`m ≥ 1`, `m_s + m + 1 ≤ q`),
  uniformly in the cutoff.
* `sum_sq_triangle` — the triangle inequality for weighted coefficient sums.
* **`generated_dynamics_rates`** — `thm:generated-dynamics` (rates, Fourier form) for
  `q = s + p + 8` and every smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀`: the Kato solution
  `U` (with `∂_tU = G(U)`) has a second time derivative `D₂` in coefficients
  (`eq:generated-Galerkin-rate`, `a = 2`); for every cutoff `N`, every step with
  `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and every finite datum `U_{0,N}` with `‖U_{0,N}‖_{H^q} ≤ R₀` and
  `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`, the fully finite midpoint recursion exists on `[0, T]` with the
  uniform bound `R` and
  - (`eq:generated-time-rate`) `‖U^j - U(t_j)‖_{H^{s+4}} ≤ C(τ² + δ + N^{-p})`;
  - (`eq:generated-Hermite`, state level) the cubic Hermite readout `z` of the record satisfies
    `‖z - U‖_{H^{s+2}} + ‖∂_tz - ∂_tU‖_{H^{s+2}} ≤ C(τ² + δ + N^{-p})` and
    `‖∂_t²z - ∂_t²U‖_{H^s} ≤ C(τ + δ + N^{-p})` on every time cell.
  With the paper's data (`δ ≤ C N^{-p}`, `eq:generated-initial-rate`) these are the rates
  `C(N^{-p} + τ²)`, `C(N^{-p} + τ)` of the theorem.

Disclosed rendering: `Σ = 𝕋^d`; smooth data with `H^q` bounds; Sobolev norms on the Fourier
(Hartley) side (`wq`), finite mode sets `S` (the bounds are uniform in `S`); `N^{-p}` is
`(N+1)^{-p}`; the generic index `m_s > d/2` with `2m_s ≤ s + 1`, `m_s ≤ p + 3` (for `d = 3`,
`m_s = 2`: `s ≥ 3`).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoGenDyn

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin KatoSecond
  KatoTimeRate KatoRate2
open KatoCausal (hmS hmS_apply hmS_add hmS_smul hmS_sub norm_hmS_sq cf_GN cf_sub')

set_option linter.unusedSectionVars false

variable {d n : ℕ}
variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-! ### The semidiscrete system from general finite data -/

/-- **The semidiscrete system from any finite datum** exists on a cutoff-independent interval
`[0, T]`, in the `H^q` ball of radius `2R₀ + 1` (`q ≥ 2m_s`, `m_s > d/2`). -/
theorem galerkin_uniform_data {ms q : ℕ} (hms : (d : ℝ) / 2 < ms) (hq : 2 * ms ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∀ (N : ℕ) (a₀ : GS d n N), ‖a₀‖ ≤ R₀ →
      ∃ γ : ℝ → GS d n N, γ 0 = a₀ ∧ GalCurve A F q T (2 * R₀ + 1) γ := by
  set R := 2 * R₀ + 1 with hR
  have hRpos : 0 < R := by linarith
  obtain ⟨K, hK0, hK⟩ := inner_GN_le (d := d) (n := n) hms hq hA hsym hF (R := 2 * R)
    (by linarith)
  have hratio : 1 < (1 + R ^ 2) / (1 + R₀ ^ 2) := by
    rw [one_lt_div (by positivity)]; nlinarith
  set T := Real.log ((1 + R ^ 2) / (1 + R₀ ^ 2)) / (2 * K + 1) with hT
  have hTpos : 0 < T := div_pos (Real.log_pos hratio) (by linarith)
  refine ⟨T, hTpos, fun N a₀ ha₀ => ?_⟩
  have h0 : Real.exp (2 * K * T) * (1 + ‖a₀‖ ^ 2) ≤ 1 + R ^ 2 := by
    have h1 : Real.exp (2 * K * T) ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) := by
      calc Real.exp (2 * K * T) ≤ Real.exp ((2 * K + 1) * T) :=
            Real.exp_le_exp.2 (by nlinarith)
        _ = (1 + R ^ 2) / (1 + R₀ ^ 2) := by
            rw [hT, mul_div_cancel₀ _ (by linarith : (2 * K + 1) ≠ 0),
              Real.exp_log (by positivity)]
    have ha2 : ‖a₀‖ ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha₀ 2
    calc Real.exp (2 * K * T) * (1 + ‖a₀‖ ^ 2)
        ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) * (1 + R₀ ^ 2) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 1 + R ^ 2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨γ, hγ0, hγ⟩ := SpectralGalerkin.galerkin_exists (contDiff_GN hA hF q N) hRpos
    hTpos.le (fun w hw => hK N w hw.le) h0 hK0
  exact ⟨γ, hγ0, ⟨fun t ht => (hγ t ht).1, fun t ht => (hγ t ht).2.1⟩⟩

/-- **`H^m` stability of the semidiscrete system in the data**, uniformly in the cutoff:
`‖U_N(t) - V_N(t)‖_{H^m} ≤ e^{Kt} ‖U_N(0) - V_N(0)‖_{H^m}` for two Galerkin trajectories in the
`H^q` ball of radius `R` (`m ≥ 1`, `m_s + m + 1 ≤ q`). -/
theorem galerkin_stable_hm {ms m q : ℕ} (hms : (d : ℝ) / 2 < ms) (hm1 : 1 ≤ m)
    (hq : ms + m + 1 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (T : ℝ) (γ₁ γ₂ : ℝ → GS d n N), GalCurve A F q T R γ₁ →
      GalCurve A F q T R γ₂ → ∀ t ∈ Icc 0 T,
        ‖hmS m q (γ₁ t - γ₂ t)‖ ≤ Real.exp (K * t) * ‖hmS m q (γ₁ 0 - γ₂ 0)‖ := by
  obtain ⟨K, hK0, hK⟩ := KatoCausal.inner_GN_sub_le (d := d) (n := n) hA hsym hF hms hm1 hq hR
  refine ⟨K, hK0, fun N T γ₁ γ₂ h₁ h₂ => ?_⟩
  set e : ℝ → GS d n N := fun t => hmS m q (γ₁ t) - hmS m q (γ₂ t) with he
  have hed : ∀ t ∈ Icc 0 T, HasDerivWithinAt e
      (hmS m q (GN A F q (γ₁ t)) - hmS m q (GN A F q (γ₂ t))) (Icc 0 T) t := fun t ht =>
    (hasDerivWithinAt_hmS (h₁.deriv t ht) m q).sub (hasDerivWithinAt_hmS (h₂.deriv t ht) m q)
  have hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => ‖e s‖ ^ 2)
      (2 * ⟪e t, hmS m q (GN A F q (γ₁ t)) - hmS m q (GN A F q (γ₂ t))⟫) (Icc 0 T) t :=
    fun t ht => (hed t ht).norm_sq
  have hc : ContinuousOn (fun s => ‖e s‖ ^ 2) (Icc 0 T) :=
    fun t ht => (hd t ht).continuousWithinAt
  have key := SpectralGalerkin.le_gronwall_scalar (f := fun s => ‖e s‖ ^ 2) (K := 2 * K)
    (ε := 0) hc
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have := hK N (γ₁ t) (γ₂ t) (h₁.bound t ht') (h₂.bound t ht')
      rw [real_inner_comm]
      simp only [he] at this ⊢
      linarith)
  intro t ht
  have h1 := key t ht
  rw [gronwallBound_ε0] at h1
  have h2 : ‖e t‖ ^ 2 ≤ (Real.exp (K * t) * ‖e 0‖) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (K * t) = 2 * K * t := by push_cast; ring
    rw [this]; linarith
  have h3 := abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  simp only [he, ← hmS_sub] at h3
  exact h3

/-! ### Weighted coefficient sums -/

/-- **Triangle inequality for weighted coefficient sums**: if
`Σ w(x - y)² ≤ a²` and `Σ w(y - z)² ≤ b²` then `Σ w(x - z)² ≤ (a + b)²`. -/
theorem sum_sq_triangle {ι : Type*} (S : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x y z : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy : ∑ i ∈ S, w i * (x i - y i) ^ 2 ≤ a ^ 2)
    (hyz : ∑ i ∈ S, w i * (y i - z i) ^ 2 ≤ b ^ 2) :
    ∑ i ∈ S, w i * (x i - z i) ^ 2 ≤ (a + b) ^ 2 := by
  set f : ι → ℝ := fun i => Real.sqrt (w i) * (x i - y i)
  set g : ι → ℝ := fun i => Real.sqrt (w i) * (y i - z i)
  have hf2 : ∀ i, f i ^ 2 = w i * (x i - y i) ^ 2 := fun i => by
    simp only [f]; rw [mul_pow, Real.sq_sqrt (hw i)]
  have hg2 : ∀ i, g i ^ 2 = w i * (y i - z i) ^ 2 := fun i => by
    simp only [g]; rw [mul_pow, Real.sq_sqrt (hw i)]
  have hfg : ∀ i, w i * (x i - y i) * (y i - z i) = f i * g i := fun i => by
    have e : f i * g i = (Real.sqrt (w i) * Real.sqrt (w i)) * ((x i - y i) * (y i - z i)) := by
      simp only [f, g]; ring
    rw [e, Real.mul_self_sqrt (hw i)]; ring
  have hF2 : ∑ i ∈ S, f i ^ 2 ≤ a ^ 2 := by
    calc ∑ i ∈ S, f i ^ 2 = ∑ i ∈ S, w i * (x i - y i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hf2 i
      _ ≤ a ^ 2 := hxy
  have hG2 : ∑ i ∈ S, g i ^ 2 ≤ b ^ 2 := by
    calc ∑ i ∈ S, g i ^ 2 = ∑ i ∈ S, w i * (y i - z i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hg2 i
      _ ≤ b ^ 2 := hyz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have hcs' : ∑ i ∈ S, f i * g i ≤ a * b := by
    have h1 : (∑ i ∈ S, f i * g i) ^ 2 ≤ (a * b) ^ 2 := by
      rw [mul_pow]
      exact hcs.trans (mul_le_mul hF2 hG2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (sq_nonneg _))
    exact (abs_le_of_sq_le_sq' h1 (mul_nonneg ha hb)).2
  have e : ∑ i ∈ S, w i * (x i - z i) ^ 2 = ∑ i ∈ S, w i * (x i - y i) ^ 2 +
      2 * ∑ i ∈ S, f i * g i + ∑ i ∈ S, w i * (y i - z i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hfg i]; ring
  rw [e]
  nlinarith

/-- The double-sum form of `sum_sq_triangle`. -/
theorem sum2_sq_triangle (S : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x y z : Fin n → (Fin d → ℤ) → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy : ∑ c, ∑ k ∈ S, w k * (x c k - y c k) ^ 2 ≤ a ^ 2)
    (hyz : ∑ c, ∑ k ∈ S, w k * (y c k - z c k) ^ 2 ≤ b ^ 2) :
    ∑ c, ∑ k ∈ S, w k * (x c k - z c k) ^ 2 ≤ (a + b) ^ 2 := by
  have e : ∀ u v : Fin n → (Fin d → ℤ) → ℝ, ∑ c, ∑ k ∈ S, w k * (u c k - v c k) ^ 2 =
      ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ S, w p.2 * (u p.1 p.2 - v p.1 p.2) ^ 2 :=
    fun u v => by rw [Finset.sum_product]
  rw [e] at hxy hyz ⊢
  exact sum_sq_triangle _ (fun p : Fin n × (Fin d → ℤ) => w p.2) (fun p => hw p.2)
    (fun p : Fin n × (Fin d → ℤ) => x p.1 p.2) (fun p : Fin n × (Fin d → ℤ) => y p.1 p.2)
    (fun p : Fin n × (Fin d → ℤ) => z p.1 p.2) ha hb hxy hyz

/-- A Galerkin difference controls the coefficient difference over every mode set. -/
theorem sum_cf_sub_le_hmS (ρ q : ℕ) {N : ℕ} (a a' : GS d n N) (S : Finset (Fin d → ℤ)) :
    ∑ c, ∑ k ∈ S, wq ρ k * (cf q a c k - cf q a' c k) ^ 2 ≤ ‖hmS ρ q (a - a')‖ ^ 2 := by
  refine le_trans (le_of_eq ?_) (sum_wq_cf_le_hmS ρ q (a - a') S)
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => by rw [cf_sub']

/-! ### Rate functions -/

theorem antitone_rate {Cr : ℝ} (hCr : 0 ≤ Cr) (k : ℕ) :
    Antitone fun N : ℕ => Cr / ((N : ℝ) + 1) ^ k := fun N M hNM => by
  refine div_le_div_of_nonneg_left hCr (by positivity) ?_
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hNM 1) k

theorem tendsto_rate {Cr : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => Cr / ((N : ℝ) + 1) ^ k) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ k) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact h1.const_div_atTop Cr |> fun h => by simpa using h

theorem rate_le {Cr : ℝ} (hCr : 0 ≤ Cr) {k j : ℕ} (hjk : j ≤ k) (N : ℕ) :
    Cr / ((N : ℝ) + 1) ^ k ≤ Cr / ((N : ℝ) + 1) ^ j := by
  refine div_le_div_of_nonneg_left hCr (by positivity) ?_
  exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) hjk

/-! ### Assembly helpers -/

theorem galCurve_mono {q N : ℕ} {T T' R R' : ℝ} {γ : ℝ → GS d n N}
    (h : GalCurve A F q T' R γ) (hT : T ≤ T') (hR : R ≤ R') : GalCurve A F q T R' γ :=
  ⟨fun t ht => (h.deriv t ⟨ht.1, ht.2.trans hT⟩).mono (Icc_subset_Icc le_rfl hT),
    fun t ht => (h.bound t ⟨ht.1, ht.2.trans hT⟩).trans hR⟩

/-- Three-term version of `sum2_sq_triangle`. -/
theorem sum2_sq_triangle3 (S : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x y z u : Fin n → (Fin d → ℤ) → ℝ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hxy : ∑ i, ∑ k ∈ S, w k * (x i k - y i k) ^ 2 ≤ a ^ 2)
    (hyz : ∑ i, ∑ k ∈ S, w k * (y i k - z i k) ^ 2 ≤ b ^ 2)
    (hzu : ∑ i, ∑ k ∈ S, w k * (z i k - u i k) ^ 2 ≤ c ^ 2) :
    ∑ i, ∑ k ∈ S, w k * (x i k - u i k) ^ 2 ≤ (a + b + c) ^ 2 :=
  sum2_sq_triangle S w hw x z u (add_nonneg ha hb) hc
    (sum2_sq_triangle S w hw x y z ha hb hxy hyz) hzu

theorem sq_le_sq_of_le' {X Y : ℝ} (h0 : 0 ≤ X) (h : X ≤ Y) : X ^ 2 ≤ Y ^ 2 :=
  pow_le_pow_left₀ h0 h 2

/-- `Cr/(N+1)^k ≤ (√Cr (N+1)^{-p})²` for `2p ≤ k`. -/
theorem rate_le_sq {Cr : ℝ} (hCr : 0 ≤ Cr) {k p : ℕ} (hk : 2 * p ≤ k) (N : ℕ) :
    Cr / ((N : ℝ) + 1) ^ k ≤ (Real.sqrt Cr * (1 / ((N : ℝ) + 1) ^ p)) ^ 2 := by
  rw [mul_pow, Real.sq_sqrt hCr, div_pow, one_pow, ← pow_mul, mul_one_div, mul_comm p 2]
  exact rate_le hCr hk N

theorem cf_GN_ite (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (k : Fin d → ℤ) :
    cf q (GN A F q a) b k = if k ∈ KatoGalerkin.box N then coef (genG A F (fld q a) b) 0 k
      else 0 := by
  split_ifs with hk
  · exact cf_GN q a b hk
  · exact cf_eq_zero _ b hk

/-- The `H^m` distance of a finite datum to the truncated continuum datum. -/
theorem norm_hmS_sub_P0_sq (m q : ℕ) {N : ℕ} (a₀ : GS d n N) (U₀ : Fin n → ST d → ℝ) :
    ‖hmS m q (a₀ - P0 q N U₀)‖ ^ 2 =
      ∑ b, ∑ k ∈ KatoGalerkin.box N, wq m k * (cf q a₀ b k - coef (U₀ b) 0 k) ^ 2 := by
  rw [norm_hmS_sq_eq_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k hk => ?_
  rw [cf_sub', cf_P0, if_pos hk]

theorem one_div_two_pi_pow_le_rate {j p : ℕ} (hj : p ≤ j) (N : ℕ) :
    1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j ≤ 1 / ((N : ℝ) + 1) ^ (2 * p) := by
  have h1 : (N : ℝ) + 1 ≤ 2 * π * ((N : ℝ) + 1) := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h2 : ((N : ℝ) + 1) ^ (2 * p) ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j := by
    rw [pow_mul, show ((N : ℝ) + 1) ^ 2 = ((N : ℝ) + 1) ^ 2 from rfl]
    calc (((N : ℝ) + 1) ^ 2) ^ p ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ p :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2) p
      _ ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j :=
          pow_le_pow_right₀ (by nlinarith [one_le_two_pi_succ N]) hj
  exact one_div_le_one_div_of_le (by positivity) h2

/-! ### The generated dynamics -/

/-- **The rate package of the fully finite approximation branch** (`thm:generated-dynamics`,
Fourier form; `q = s + p + 8`): there are `T > 0`, `R`, `c_* > 0`, `τ_* > 0`, `C` such that every
smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` has a classical solution `U` on `[0, T] × 𝕋^d`
(spatial derivatives `P`, `∂_tU = G(U)`), with coefficients twice differentiable in time
(`d/dt c_k(U) = c_k(G(U))`, `d/dt c_k(G(U)) = D₂`), and for every cutoff `N`, step `τ` with
`τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and every finite datum `U_{0,N}` (`‖U_{0,N}‖_{H^q} ≤ R₀`,
`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`) the midpoint recursion exists on `[0, T]` with `‖U^j‖_{H^q} ≤ R`,
`‖U^j - U(jτ)‖_{H^{s+4}} ≤ C(τ² + δ + ν)` and, on every cell, the Hermite readout satisfies
`‖z - U‖_{H^{s+2}}, ‖∂_tz - ∂_tU‖_{H^{s+2}} ≤ C(τ² + δ + ν)`, `‖∂_t²z - ∂_t²U‖_{H^s} ≤ C(τ + δ + ν)`
(`ν = (N+1)^{-p}`; all norms in Fourier form over arbitrary finite mode sets). -/
def GeneratedRates (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (s p : ℕ) (R₀ : ℝ) : Prop :=
    ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∃ C ≥ 0,
      ∀ U₀ : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) →
      energyQ (s + p + 8) U₀ 0 ≤ R₀ ^ 2 →
      ∃ (U : Fin n → ST d → ℝ) (P : Fin n → Fin d → ST d → ℝ)
        (D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ),
        (∀ b, Continuous (U b)) ∧ (∀ b, IsSPeriodic (U b)) ∧
        (∀ b y, U b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y)) ∧
        (∀ b (i : Fin d) x, HasDerivAt (fun σ : ℝ => U b (x + σ • ev i.succ)) (P b i x) 0) ∧
        (∀ b, ∀ t ∈ Icc 0 T, ∀ y, HasDerivWithinAt (fun σ => U b (Fin.cons σ y))
          (genP A F U P b (Fin.cons t y)) (Icc 0 T) t) ∧
        (∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun σ => coef (U b) σ k)
          (coef (genP A F U P b) t k) (Icc 0 T) t) ∧
        (∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun σ => coef (genP A F U P b) σ k)
          (D₂ b k t) (Icc 0 T) t) ∧
        ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar →
        ∀ (a₀ : GS d n N) (δ : ℝ), ‖a₀‖ ≤ R₀ → 0 ≤ δ →
        (∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S,
          wq (s + 4) k * (cf (s + p + 8) a₀ b k - coef (U₀ b) 0 k) ^ 2 ≤ δ ^ 2) →
        ∃ Ud : ℕ → GS d n N, Ud 0 = a₀ ∧
          (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
            Ud (j + 1) = Ud j + τ • GN A F (s + p + 8) (SpectralGalerkin.mid (Ud j) (Ud (j + 1))))) ∧
          (∀ j : ℕ, (j : ℝ) * τ ≤ T → ∀ S : Finset (Fin d → ℤ),
            ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (Ud j) b k - coef (U b) (j * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
          (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T → ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin d → ℤ),
            (∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (SpectralGalerkin.hermite τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                coef (U b) (j * τ + θ * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
            (∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (SpectralGalerkin.hermiteD τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                coef (genP A F U P b) (j * τ + θ * τ) k) ^ 2 ≤
              (C * (τ ^ 2 + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2) ∧
            (∑ b, ∑ k ∈ S, wq s k * (cf (s + p + 8) (SpectralGalerkin.hermiteDD τ (Ud j)
                (Ud (j + 1)) (GN A F (s + p + 8) (Ud j)) (GN A F (s + p + 8) (Ud (j + 1))) θ) b k -
                D₂ b k (j * τ + θ * τ)) ^ 2 ≤
              (C * (τ + δ + 1 / ((N : ℝ) + 1) ^ p)) ^ 2))

set_option maxHeartbeats 8000000 in
/-- **The fully finite approximation branch: rates** (`thm:generated-dynamics`,
`eq:generated-Galerkin-rate`, `eq:generated-time-rate`, `eq:generated-Hermite`; Fourier form).
Let `m_s > d/2`, `2m_s ≤ s + 1`, `1 ≤ p`, `m_s ≤ p + 3`, `q = s + p + 8`, `A^i` smooth real
symmetric, `F` smooth.  For every data radius `R₀` there are `T > 0`, `R`, `c_* > 0`, `τ_* > 0`
and `C` such that every smooth periodic datum `U₀` with `‖U₀‖_{H^q} ≤ R₀` has a classical solution
`U` on `[0, T] × 𝕋^d` (spatial derivatives `P`, `∂_tU = G(U) = F(U) - Σ_i A^i(U)P_i`) whose
coefficients are twice differentiable in time: `d/dt c_k(U) = c_k(G(U))`, `d/dt c_k(G(U)) = D₂`;
and for every cutoff `N`, step `τ > 0` with `τ(N+1) ≤ c_*`, `τ ≤ τ_*`, and every finite datum
`U_{0,N}` with `‖U_{0,N}‖_{H^q} ≤ R₀` and `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`, the implicit midpoint
recursion `U^{j+1} = U^j + τ G_N((U^j + U^{j+1})/2)`, `U^0 = U_{0,N}`, exists for `jτ ≤ T` with
`‖U^j‖_{H^q} ≤ R`, and (with `ν = (N+1)^{-p}`, for every finite mode set `S`):
* `‖U^j - U(jτ)‖_{H^{s+4}} ≤ C (τ² + δ + ν)`;
* on every cell `[jτ, (j+1)τ] ⊆ [0, T]`, the cubic Hermite readout `z` of the record (nodal values
  `U^j`, nodal slopes `G_N(U^j)`) satisfies, at `t = jτ + θτ`,
  `‖z - U(t)‖_{H^{s+2}} ≤ C (τ² + δ + ν)`, `‖∂_tz - ∂_tU(t)‖_{H^{s+2}} ≤ C (τ² + δ + ν)`,
  `‖∂_t²z - ∂_t²U(t)‖_{H^s} ≤ C (τ + δ + ν)` (`∂_tz = hermiteD`, `∂_t²z = hermiteDD`,
  `SpectralGalerkin.hasDerivAt_hermite`). -/
theorem generated_dynamics_rates {ms s p : ℕ} (hms : (d : ℝ) / 2 < ms) (hs : 2 * ms ≤ s + 1)
    (hp : 1 ≤ p) (hmsp : ms ≤ p + 3) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hsym : ∀ i a b v, A i a b v = A i b a v) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) :
    GeneratedRates A F s p R₀ := by
  unfold GeneratedRates
  have hms1 : 1 ≤ ms := by
    have : (0 : ℝ) < ms := lt_of_le_of_lt (by positivity) hms
    exact_mod_cast this
  -- Kato's theorem with the sharp rates, the midpoint scheme and the Galerkin data family
  obtain ⟨T₁, hT₁, RK, hRK, CK, hCK, Cdt, hCdt, hK⟩ := KatoRates.kato_sharp_rates_dt (d := d)
    (n := n) (ms := ms) (r := s + p + 7) hms (by omega) (by omega) hA hsym hF hR₀
  obtain ⟨T₂, hT₂, Rm, hRm, cstar, hc, τs, hτs, CM, -, hmid⟩ := KatoCFL.midpoint_uniform_cfl
    (d := d) (n := n) (m := ms) (q := s + p + 8) hms (by omega) hA hsym hF hR₀
  obtain ⟨T₃, hT₃, hgal⟩ := galerkin_uniform_data (d := d) (n := n) (ms := ms) (q := s + p + 8)
    hms (by omega) hA hsym hF hR₀
  set R := RK + Rm + (2 * R₀ + 1) with hRdef
  have hR : 0 ≤ R := by positivity
  have hRKR : RK ≤ R := by rw [hRdef]; linarith
  have hRmR : Rm ≤ R := by rw [hRdef]; linarith
  have hR₀R : 2 * R₀ + 1 ≤ R := by rw [hRdef]; linarith
  set T := min T₁ (min T₂ T₃) with hTdef
  have hT : 0 < T := lt_min hT₁ (lt_min hT₂ hT₃)
  have hTT₁ : T ≤ T₁ := min_le_left _ _
  have hTT₂ : T ≤ T₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hTT₃ : T ≤ T₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hsub₁ : Icc 0 T ⊆ Icc 0 T₁ := Icc_subset_Icc le_rfl hTT₁
  -- the cutoff-uniform constants
  obtain ⟨K₁, hK₁0, h₁⟩ := midpoint_time_rate (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (m := s + 4) (q := s + p + 8) hms (by omega) (by omega) (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁ T hT.le
  obtain ⟨K₂, hK₂0, h₂⟩ := hermite_semidiscrete (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s + 2) (q := s + p + 8) hms (by omega) (by omega) (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂ T hT.le
  obtain ⟨K₃, hK₃0, h₃⟩ := hermite_semidiscrete (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s) (q := s + p + 8) hms (by omega) hs (by omega) (by omega) hA hsym hF hR
  obtain ⟨C₃, hC₃0, hC₃⟩ := h₃ T hT.le
  obtain ⟨Ks, hKs0, hstab⟩ := galerkin_stable_hm (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (m := s + 4) (q := s + p + 8) hms (by omega) (by omega) hA hsym hF hR
  obtain ⟨L₂, hL₂0, hL₂⟩ := GN_lip_hm (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s + 2)
    hms (by omega) hA hF hR
  obtain ⟨L₁, hL₁0, hL₁⟩ := GN_lip_hm (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s + 1)
    hms (by omega) hA hF hR
  obtain ⟨LD, hLD0, hLD⟩ := DGN_bound (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    hms hs hA hF hR
  obtain ⟨LL, hLL0, hLL⟩ := DGN_lip (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    hms hs hA hF hR
  obtain ⟨MA, hMA0, hMA⟩ := curve_lip (d := d) (n := n) (A := A) (F := F) (ms := ms)
    (ρ := s + 1) (q := s + p + 8) hms (by omega) (by omega) hA hF hR
  obtain ⟨C₄, hC₄0, h₄⟩ := second_limit (d := d) (n := n) (A := A) (F := F) (ms := ms) (ρ := s)
    (q := s + p + 8) hms hs (by omega) hA hF hR
  -- the overall constants
  set E := Real.exp (Ks * T) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set A₀ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 1) * CK + RK ^ 2 with hA₀
  set A₂ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 2) * CK + RK ^ 2 with hA₂
  set A₄ := (1 + 4 * π ^ 2 * (d : ℝ)) ^ (s + 4) * CK + RK ^ 2 with hA₄
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hA₄0 : 0 ≤ A₄ := by positivity
  set B₄ := C₄ * (A₀ + Cdt (s + 1) + 1) with hB₄
  have hB₄0 : 0 ≤ B₄ := by have := hCdt (s + 1); positivity
  set Lstab := 1 + L₂ + LD * L₁ + LL * MA with hLstab
  have hLstab1 : 1 ≤ Lstab := by
    have := mul_nonneg hLD0 hL₁0
    have := mul_nonneg hLL0 hMA0
    rw [hLstab]; linarith
  set C := C₁ + C₂ + C₃ + E * Lstab + Real.sqrt A₄ + Real.sqrt A₂ + Real.sqrt (Cdt (s + 2)) +
    Real.sqrt B₄ with hCdef
  have hs4 := Real.sqrt_nonneg A₄
  have hs2 := Real.sqrt_nonneg A₂
  have hsd := Real.sqrt_nonneg (Cdt (s + 2))
  have hsB := Real.sqrt_nonneg B₄
  have hELs : 0 ≤ E * Lstab := mul_nonneg hE0 (by linarith)
  have hC1 : C₁ ≤ C := by rw [hCdef]; linarith
  have hC2 : C₂ ≤ C := by rw [hCdef]; linarith
  have hC3 : C₃ ≤ C := by rw [hCdef]; linarith
  have hCE : E * Lstab ≤ C := by rw [hCdef]; linarith
  have hC4 : Real.sqrt A₄ ≤ C := by rw [hCdef]; linarith
  have hC5 : Real.sqrt A₂ ≤ C := by rw [hCdef]; linarith
  have hC6 : Real.sqrt (Cdt (s + 2)) ≤ C := by rw [hCdef]; linarith
  have hC7 : Real.sqrt B₄ ≤ C := by rw [hCdef]; linarith
  have hC0 : 0 ≤ C := hC1.trans' hC₁0
  have hEL1 : E ≤ C := (le_mul_of_one_le_right hE0 hLstab1).trans hCE
  have hL₂L : L₂ ≤ Lstab := by
    have := mul_nonneg hLD0 hL₁0
    have := mul_nonneg hLL0 hMA0
    rw [hLstab]; linarith
  have hL₃L : LD * L₁ + LL * MA ≤ Lstab := by
    rw [hLstab]; linarith
  have hEL2 : E * L₂ ≤ C := le_trans (mul_le_mul_of_nonneg_left hL₂L hE0) hCE
  have hEL3 : E * (LD * L₁ + LL * MA) ≤ C := le_trans (mul_le_mul_of_nonneg_left hL₃L hE0) hCE
  set τstar := min τs (1 / (K₁ + K₂ + K₃ + 1)) with hτstar
  refine ⟨T, hT, R, hR, cstar, hc, τstar, lt_min hτs (by positivity), C, hC0,
    fun U₀ hU₀ hUp hE₀ => ?_⟩
  obtain ⟨U, P, γ, hG, hUc, hUper, hU0, hP, hUt, hcoef, -, hr0, hr1⟩ := hK U₀ hU₀ hUp hE₀
  have hGc : ∀ N, GalCurve A F (s + p + 8) T R (γ N) := fun N =>
    galCurve_mono (q := s + p + 8) ⟨hG.deriv N, hG.bound N⟩ hTT₁ hRKR
  -- the second time derivative of the limit
  obtain ⟨D₂, hD₂d, hD₂r⟩ := h₄ T γ hGc (fun b k t => coef (U b) t k)
    (fun b k t => coef (genP A F U P b) t k)
    (fun N => A₀ / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1)) + 1))
    (fun N => Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1 + 1)) + 1))
    (antitone_rate hA₀0 _) (antitone_rate (hCdt _) _) (tendsto_rate (by omega))
    (tendsto_rate (by omega))
    (fun N t ht S => hr0 (s + 1) (by omega) N t (hsub₁ ht) S)
    (fun N t ht S => by
      simp only [cf_GN_ite]
      exact hr1 (s + 1) (by omega) (by omega) N t (hsub₁ ht) S)
  refine ⟨U, P, D₂, hUc, hUper, hU0, hP,
    fun b t ht y => (hUt b t (hsub₁ ht) y).mono hsub₁,
    fun b k t ht => (hcoef b k t (hsub₁ ht)).mono hsub₁, hD₂d,
    fun N τ hτ hcfl hτst a₀ δ ha₀ hδ hdata => ?_⟩
  -- the step restrictions
  have hτs' : τ ≤ τs := hτst.trans (min_le_left _ _)
  have hτK : τ * (K₁ + K₂ + K₃ + 1) ≤ 1 := by
    have h1 : τ ≤ 1 / (K₁ + K₂ + K₃ + 1) := hτst.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have eK : τ * (K₁ + K₂ + K₃ + 1) = τ * K₁ + τ * K₂ + τ * K₃ + τ := by ring
  have pK₁ := mul_nonneg hτ.le hK₁0
  have pK₂ := mul_nonneg hτ.le hK₂0
  have pK₃ := mul_nonneg hτ.le hK₃0
  have hτK₁ : τ * K₁ ≤ 1 := by linarith
  have hτK₂ : τ * K₂ ≤ 1 := by linarith
  have hτK₃ : τ * K₃ ≤ 1 := by linarith
  -- the midpoint record and the Galerkin trajectory from the same finite datum
  obtain ⟨Ud, hUd0, hUd⟩ := hmid N τ hτ hcfl hτs' a₀ ha₀
  obtain ⟨γa, hγa0, hGa⟩ := hgal N a₀ ha₀
  have hGa' : GalCurve A F (s + p + 8) T R γa := galCurve_mono hGa hTT₃ hR₀R
  have hGN : GalCurve A F (s + p + 8) T R (γ N) := hGc N
  have hUdR : ∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖Ud j‖ ≤ R := fun j hj =>
    (hUd j (hj.trans hTT₂)).1.trans hRmR
  have hUdrec : ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T →
      Ud (j + 1) = Ud j + τ • GN A F (s + p + 8) (SpectralGalerkin.mid (Ud j) (Ud (j + 1))) :=
    fun j hj => ((hUd j (by linarith [show ((j : ℝ) + 1) * τ = (j : ℝ) * τ + τ by ring])).2
      (hj.trans hTT₂)).1
  -- the data error and the Galerkin stability
  have hγN0 : γ N 0 = P0 (s + p + 7 + 1) N U₀ := hG.init N
  have hδ0 : ‖hmS (s + 4) (s + p + 8) (a₀ - γ N 0)‖ ≤ δ := by
    rw [hγN0]
    have h1 := norm_hmS_sub_P0_sq (s + 4) (s + p + 8) a₀ U₀
    have h2 := hdata (KatoGalerkin.box N)
    rw [← h1] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ two_ne_zero).1 h2
  have hst : ∀ t ∈ Icc 0 T, ‖hmS (s + 4) (s + p + 8) (γa t - γ N t)‖ ≤ E * δ := by
    intro t ht
    refine (hstab N T γa (γ N) hGa' hGN t ht).trans ?_
    rw [hγa0]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hKs0)) hδ0
      (norm_nonneg _) (Real.exp_pos _).le
  have hlow : ∀ ρ, ρ ≤ s + 4 → ∀ t ∈ Icc 0 T, ‖hmS ρ (s + p + 8) (γa t - γ N t)‖ ≤ E * δ :=
    fun ρ hρ t ht => (norm_hmS_mono hρ _).trans (hst t ht)
  set ν := 1 / ((N : ℝ) + 1) ^ p with hν
  have hν0 : 0 ≤ ν := by positivity
  have hδ0' : ‖hmS (s + 3) (s + p + 8) (Ud 0 - γa 0)‖ = 0 := by
    rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero]
  have hδ0'' : ‖hmS (s + 1) (s + p + 8) (Ud 0 - γa 0)‖ = 0 := by
    rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero]
  refine ⟨Ud, hUd0, fun j hj => ⟨hUdR j hj, fun hj1 => hUdrec j hj1⟩, fun j hj S => ?_,
    fun j hj θ hθ S => ?_⟩
  · -- the time rate
    have ht : (j : ℝ) * τ ∈ Icc 0 T := ⟨by positivity, hj⟩
    have k1 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (Ud j) b k -
        cf (s + p + 8) (γa (j * τ)) b k) ^ 2 ≤ (C₁ * τ ^ 2) ^ 2 := by
      refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
      have h := hC₁ N τ hτ hτK₁ γa Ud hGa' hUdR hUdrec j hj
      rw [hUd0, hγa0, sub_self, hmS_zero, norm_zero, zero_add] at h
      exact h
    have k2 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (γa (j * τ)) b k -
        cf (s + p + 8) (γ N (j * τ)) b k) ^ 2 ≤ (E * δ) ^ 2 :=
      (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) (hst _ ht))
    have k3 : ∑ b, ∑ k ∈ S, wq (s + 4) k * (cf (s + p + 8) (γ N (j * τ)) b k -
        coef (U b) (j * τ) k) ^ 2 ≤ (Real.sqrt A₄ * ν) ^ 2 :=
      (hr0 (s + 4) (by omega) N _ (hsub₁ ht) S).trans (rate_le_sq hA₄0 (by omega) N)
    refine (sum2_sq_triangle3 S (wq (s + 4)) (fun k => wq_nonneg _ _)
      (fun b k => cf (s + p + 8) (Ud j) b k) (fun b k => cf (s + p + 8) (γa (j * τ)) b k)
      (fun b k => cf (s + p + 8) (γ N (j * τ)) b k) (fun b k => coef (U b) (j * τ) k)
      (by positivity) (by positivity) (by positivity) k1 k2 k3).trans
      (sq_le_sq_of_le' (by positivity) ?_)
    rw [mul_add, mul_add]
    linarith [mul_le_mul_of_nonneg_right hC1 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL1 hδ,
      mul_le_mul_of_nonneg_right hC4 hν0]
  · -- the Hermite readout
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθτ : θ * τ ≤ τ := mul_le_of_le_one_left hτ.le hθ1
    have ht : (j : ℝ) * τ + θ * τ ∈ Icc 0 T :=
      ⟨by positivity, by linarith [show ((j : ℝ) + 1) * τ = (j : ℝ) * τ + τ by ring]⟩
    obtain ⟨g1, g2, -⟩ := hC₂ N τ hτ hτK₂ γa Ud hGa' hUdR hUdrec j hj θ ⟨hθ0, hθ1⟩
    obtain ⟨-, -, g3⟩ := hC₃ N τ hτ hτK₃ γa Ud hGa' hUdR hUdrec j hj θ ⟨hθ0, hθ1⟩
    rw [hδ0', zero_add] at g1 g2
    rw [hδ0'', zero_div, zero_add] at g3
    set t := (j : ℝ) * τ + θ * τ with htdef
    refine ⟨?_, ?_, ?_⟩
    · have k2 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (γa t) b k -
          cf (s + p + 8) (γ N t) b k) ^ 2 ≤ (E * δ) ^ 2 :=
        (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _)
          (hlow (s + 2) (by omega) t ht))
      have k3 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (γ N t) b k -
          coef (U b) t k) ^ 2 ≤ (Real.sqrt A₂ * ν) ^ 2 :=
        (hr0 (s + 2) (by omega) N _ (hsub₁ ht) S).trans (rate_le_sq hA₂0 (by omega) N)
      refine (sum2_sq_triangle3 S (wq (s + 2)) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (γa t) b k) (fun b k => cf (s + p + 8) (γ N t) b k)
        (fun b k => coef (U b) t k) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g1)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL1 hδ,
        mul_le_mul_of_nonneg_right hC5 hν0]
    · have k2 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (GN A F (s + p + 8) (γa t)) b k -
          cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k) ^ 2 ≤ (E * L₂ * δ) ^ 2 := by
        refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
        refine (hL₂ (s + p + 8) N _ _ (hGa'.ball (by omega) t ht) (hGN.ball (by omega) t ht)).trans ?_
        have := hlow (s + 3) (by omega) t ht
        calc L₂ * ‖hmS (s + 2 + 1) (s + p + 8) (γa t - γ N t)‖ ≤ L₂ * (E * δ) :=
              mul_le_mul_of_nonneg_left this hL₂0
          _ = E * L₂ * δ := by ring
      have k3 : ∑ b, ∑ k ∈ S, wq (s + 2) k * (cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k -
          coef (genP A F U P b) t k) ^ 2 ≤ (Real.sqrt (Cdt (s + 2)) * ν) ^ 2 := by
        simp only [cf_GN_ite]
        exact (hr1 (s + 2) (by omega) (by omega) N _ (hsub₁ ht) S).trans
          (rate_le_sq (hCdt _) (by omega) N)
      refine (sum2_sq_triangle3 S (wq (s + 2)) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (GN A F (s + p + 8) (γa t)) b k)
        (fun b k => cf (s + p + 8) (GN A F (s + p + 8) (γ N t)) b k)
        (fun b k => coef (genP A F U P b) t k) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g2)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC2 (sq_nonneg τ), mul_le_mul_of_nonneg_right hEL2 hδ,
        mul_le_mul_of_nonneg_right hC6 hν0]
    · have k2 : ∑ b, ∑ k ∈ S, wq s k *
          (cf (s + p + 8) (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t))) b k -
          cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k) ^ 2 ≤
          (E * (LD * L₁ + LL * MA) * δ) ^ 2 := by
        refine (sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) ?_)
        have e : DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t)) -
            DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t)) =
            DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t) - GN A F (s + p + 8) (γ N t)) +
              (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γ N t)) -
                DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) := by
          rw [DGN_sub_right]; abel
        rw [e, hmS_add]
        have b1 := hGa'.ball (ρ := s + 1) (by omega) t ht
        have b2 := hGN.ball (ρ := s + 1) (by omega) t ht
        have b3 := hGa'.ball (ρ := s + 2) (by omega) t ht
        have b4 := hGN.ball (ρ := s + 2) (by omega) t ht
        have f1 := (hLD (s + p + 8) N (γa t) _ b1).trans (mul_le_mul_of_nonneg_left
          ((hL₁ (s + p + 8) N _ _ b3 b4).trans (mul_le_mul_of_nonneg_left
            (hlow (s + 2) (by omega) t ht) hL₁0)) hLD0)
        have f2 := (hLL (s + p + 8) N (γa t) (γ N t) (GN A F (s + p + 8) (γ N t)) b1 b2).trans
          (mul_le_mul (mul_le_mul_of_nonneg_left (hlow (s + 1) (by omega) t ht) hLL0)
            ((hMA N T (γ N) hGN).1 t ht) (norm_nonneg _) (by positivity))
        calc _ ≤ _ := norm_add_le _ _
          _ ≤ LD * (L₁ * (E * δ)) + LL * (E * δ) * MA := add_le_add f1 f2
          _ = E * (LD * L₁ + LL * MA) * δ := by ring
      have k3 : ∑ b, ∑ k ∈ S, wq s k *
          (cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k -
          D₂ b k t) ^ 2 ≤ (Real.sqrt B₄ * ν) ^ 2 := by
        refine (hD₂r N t ht S).trans ?_
        have hsq : (Real.sqrt B₄ * ν) ^ 2 = C₄ * (A₀ + Cdt (s + 1) + 1) *
            (1 / ((N : ℝ) + 1) ^ (2 * p)) := by
          rw [mul_pow, Real.sq_sqrt hB₄0, hν, div_pow, one_pow, ← pow_mul, mul_comm p 2, hB₄]
        rw [hsq]
        have r1 := rate_le hA₀0 (j := 2 * p) (k := 2 * (s + p + 7 - (s + 1)) + 1) (by omega) N
        have r2 := rate_le (hCdt (s + 1)) (j := 2 * p)
          (k := 2 * (s + p + 7 - (s + 1 + 1)) + 1) (by omega) N
        have r3 := one_div_two_pi_pow_le_rate (j := s + p + 8 - 2 - s) (p := p) (by omega) N
        have e2 : A₀ / ((N : ℝ) + 1) ^ (2 * p) = A₀ * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
        have e3 : Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * p) =
            Cdt (s + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
        rw [e2] at r1; rw [e3] at r2
        calc C₄ * (A₀ / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1)) + 1) +
              Cdt (s + 1) / ((N : ℝ) + 1) ^ (2 * (s + p + 7 - (s + 1 + 1)) + 1) +
              1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (s + p + 8 - 2 - s))
            ≤ C₄ * (A₀ * (1 / ((N : ℝ) + 1) ^ (2 * p)) +
              Cdt (s + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) + 1 / ((N : ℝ) + 1) ^ (2 * p)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC₄0
          _ = C₄ * (A₀ + Cdt (s + 1) + 1) * (1 / ((N : ℝ) + 1) ^ (2 * p)) := by ring
      refine (sum2_sq_triangle3 S (wq s) (fun k => wq_nonneg _ _) _
        (fun b k => cf (s + p + 8) (DGN A F (s + p + 8) (γa t) (GN A F (s + p + 8) (γa t))) b k)
        (fun b k => cf (s + p + 8) (DGN A F (s + p + 8) (γ N t) (GN A F (s + p + 8) (γ N t))) b k)
        (fun b k => D₂ b k t) (by positivity) (by positivity) (by positivity)
        ((sum_cf_sub_le_hmS _ _ _ _ S).trans (sq_le_sq_of_le' (norm_nonneg _) g3)) k2 k3).trans
        (sq_le_sq_of_le' (by positivity) ?_)
      rw [mul_add, mul_add]
      linarith [mul_le_mul_of_nonneg_right hC3 hτ.le, mul_le_mul_of_nonneg_right hEL3 hδ,
        mul_le_mul_of_nonneg_right hC7 hν0]

end RenewalGeometry.KatoGenDyn
