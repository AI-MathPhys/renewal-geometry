/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoMidpointTimeRate

/-!
# The second time derivative of the spectral Galerkin limit (`eq:generated-Galerkin-rate`, `a = 2`)

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript, clause `a = 2` of `eq:generated-Galerkin-rate`:
`‖∂_t²(U_N - U)‖_{C_tH^{s+2}} ≤ C N^{-p}`.  Setting of `KatoGalerkinODE` (`𝕋^d`, smooth `A^i`,
`F`, Galerkin spaces `GS d n N`, coefficients `cf`, `H^ρ` weights `wq ρ`).

* `lift` — the inclusion `Ran P_N ⊆ Ran P_M` (`N ≤ M`) in Galerkin coordinates; it preserves
  coefficients, fields and `H^ρ` norms (`cf_lift`, `fld_lift`, `norm_hmS_lift`).
* `cf_DGN_lift` — the derivative of the projected generator does not depend on the cutoff on the
  common modes: `c_k(DG_M(a)[w]) = c_k(DG_N(a)[w])` for `k ∈ KatoGalerkin.box N` (both are
  `d/dh c_k(G(U + hW))|_{h=0}`).
* **`second_cauchy`** — the cross-cutoff estimate for the second time derivatives
  `U_N'' = DG_N(U_N)[G_N(U_N)]` of two Galerkin trajectories (`N ≤ M`):
  `Σ_{k ∈ S} wq_ρ(k) (c_k(U_N'') - c_k(U_M''))² ≤ C (‖U_N - U_M‖²_{H^{ρ+1}}
    + ‖U_N' - U_M'‖²_{H^{ρ+1}} + (2π(N+1))^{-2(q-2-ρ)})` (`KatoSecond.DGN_bound`, `DGN_lip`, and the
  `H^{q-2}` bound of `U_M''` for the high modes).
* **`second_limit`** — if Galerkin trajectories converge to coefficient functions `c₀` (state)
  and `c₁` (time derivative) with rates `e₀(N)`, `e₁(N)` in `H^{ρ+1}`, then the second
  derivatives converge: there are `D₂` with `d/dt c₁(t) = D₂(t)` on `[0, T]` and
  `Σ_{k ∈ S} wq_ρ(k) (c_k(U_N''(t)) - D₂(t))² ≤ C (e₀(N) + e₁(N) + (2π(N+1))^{-2(q-2-ρ)})`.
  Combined with `KatoRates.kato_sharp_rates_dt` this is the clause `a = 2` (Fourier form).
* `hasDerivWithinAt_of_sq_bound` — a quadratic Taylor remainder bound gives the derivative.

Disclosed rendering: `Σ = 𝕋^d`; Sobolev norms on the Fourier (Hartley) side.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoRate2

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin KatoSecond
  KatoTimeRate
open KatoCausal (hmS hmS_apply hmS_add hmS_smul hmS_sub norm_hmS_sq cf_GN cf_sub')

set_option linter.unusedSectionVars false

variable {d n : ℕ}
variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-! ### Coefficients, norms and the lift between cutoffs -/

theorem cf_add_smul (q : ℕ) {N : ℕ} (a w : GS d n N) (h : ℝ) (b : Fin n) (k : Fin d → ℤ) :
    cf q (a + h • w) b k = cf q a b k + h * cf q w b k := by
  unfold cf
  split_ifs with hk
  · rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  · ring

theorem tfs_add_smul (S : Finset (Fin d → ℤ)) (c c' : (Fin d → ℤ) → ℝ) (h : ℝ) (x : ST d) :
    tfs S (fun k => c k + h * c' k) x = tfs S c x + h * tfs S c' x := by
  unfold tfs
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem fld_add_smul (q : ℕ) {N : ℕ} (a w : GS d n N) (h : ℝ) :
    fld q (a + h • w) = fun b x => fld q a b x + h * fld q w b x := by
  funext b x
  rw [fld, fld, fld, ← tfs_add_smul]
  congr 1
  funext k
  exact cf_add_smul q a w h b k

/-- `‖x‖²_{H^ρ} = Σ_b Σ_{k ∈ KatoGalerkin.box N} wq_ρ(k) c_k(x)²`. -/
theorem norm_hmS_sq_eq_sum (ρ q : ℕ) {N : ℕ} (a : GS d n N) :
    ‖hmS ρ q a‖ ^ 2 = ∑ b, ∑ k ∈ KatoGalerkin.box N, wq ρ k * cf q a b k ^ 2 := by
  rw [norm_hmS_sq ρ q a 0, energyQ]
  exact Finset.sum_congr rfl fun b _ => by rw [fld, Q_tfs]

/-- **Coefficient sums over any finite mode set are bounded by the `H^ρ` norm.** -/
theorem sum_wq_cf_le_hmS (ρ q : ℕ) {N : ℕ} (a : GS d n N) (S : Finset (Fin d → ℤ)) :
    ∑ b, ∑ k ∈ S, wq ρ k * cf q a b k ^ 2 ≤ ‖hmS ρ q a‖ ^ 2 := by
  rw [norm_hmS_sq_eq_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ KatoGalerkin.box N) (fun k _ hk => by
    by_contra h; exact hk (by rw [cf_eq_zero a b h]; ring))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
    fun k _ _ => mul_nonneg (wq_nonneg _ _) (sq_nonneg _)

theorem abs_cf_le_hmS (ρ q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) (k : Fin d → ℤ) :
    |cf q a b k| ≤ ‖hmS ρ q a‖ := by
  have h := sum_wq_cf_le_hmS ρ q a {k}
  simp only [Finset.sum_singleton] at h
  have h1 : wq ρ k * cf q a b k ^ 2 ≤ ∑ b, wq ρ k * cf q a b k ^ 2 :=
    Finset.single_le_sum (f := fun b => wq ρ k * cf q a b k ^ 2)
      (fun b _ => mul_nonneg (wq_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ b)
  have h2 : cf q a b k ^ 2 ≤ wq ρ k * cf q a b k ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) (one_le_wq ρ k)
  have h3 : cf q a b k ^ 2 ≤ ‖hmS ρ q a‖ ^ 2 := by linarith
  exact abs_le.2 (abs_le_of_sq_le_sq' h3 (norm_nonneg _))

/-- The inclusion `Ran P_N ⊆ Ran P_M` in Galerkin coordinates. -/
def lift (q : ℕ) {N M : ℕ} (a : GS d n N) : GS d n M :=
  WithLp.toLp 2 fun p => Real.sqrt (wq q p.2.1) * cf q a p.1 p.2.1

theorem cf_lift (q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (b : Fin n) (k : Fin d → ℤ) :
    cf q (lift q (M := M) a) b k = cf q a b k := by
  by_cases hk : k ∈ KatoGalerkin.box M
  · rw [cf, dif_pos hk]
    show Real.sqrt (wq q k) * cf q a b k / Real.sqrt (wq q k) = cf q a b k
    field_simp [sqrt_wq_ne q k]
  · rw [cf, dif_neg hk, cf_eq_zero a b (fun h => hk (box_mono hNM h))]

theorem fld_lift (q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a : GS d n N) :
    fld q (lift q (M := M) a) = fld q a := by
  funext b x
  rw [fld_eq_tfs hNM a b, fld]
  congr 1
  funext k
  exact cf_lift q hNM a b k

theorem norm_hmS_lift (ρ q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a : GS d n N) :
    ‖hmS ρ q (lift q (M := M) a)‖ = ‖hmS ρ q a‖ := by
  have h1 := norm_hmS_sq ρ q (lift q (M := M) a) 0
  have h2 := norm_hmS_sq ρ q a 0
  rw [fld_lift q hNM] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem lift_add_smul (q : ℕ) {N M : ℕ} (_hNM : N ≤ M) (a w : GS d n N) (h : ℝ) :
    lift q (M := M) (a + h • w) = lift q a + h • lift q w := by
  refine PiLp.ext fun p => ?_
  simp only [lift, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  show Real.sqrt (wq q p.2.1) * cf q (a + h • w) p.1 p.2.1 =
    Real.sqrt (wq q p.2.1) * cf q a p.1 p.2.1 + h * (Real.sqrt (wq q p.2.1) * cf q w p.1 p.2.1)
  rw [cf_add_smul]; ring

theorem cf_lift_sub (q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (a' : GS d n M) (b : Fin n)
    (k : Fin d → ℤ) : cf q (lift q a - a') b k = cf q a b k - cf q a' b k := by
  rw [cf_sub', cf_lift q hNM]

/-- `‖P_N a - b‖²_{H^ρ}` (computed on the larger box) in coefficients. -/
theorem norm_hmS_lift_sub_sq (ρ q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a : GS d n N) (a' : GS d n M) :
    ‖hmS ρ q (lift q a - a')‖ ^ 2 =
      ∑ b, ∑ k ∈ KatoGalerkin.box M, wq ρ k * (cf q a b k - cf q a' b k) ^ 2 := by
  rw [norm_hmS_sq_eq_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by
    rw [cf_lift_sub q hNM]

/-! ### The derivative of the projected generator on the common modes -/

theorem cf_eq_proj (q : ℕ) {N : ℕ} (b : Fin n) {k : Fin d → ℤ} (hk : k ∈ KatoGalerkin.box N) (x : GS d n N) :
    cf q x b k = (EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × KatoGalerkin.box (d := d) N) x) /
      Real.sqrt (wq q k) := by
  rw [cf, dif_pos hk]; rfl

theorem hasDerivWithinAt_cf_of {q N : ℕ} {f : ℝ → GS d n N} {f' : GS d n N} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) (b : Fin n) {k : Fin d → ℤ} (hk : k ∈ KatoGalerkin.box N) :
    HasDerivWithinAt (fun t => cf q (f t) b k) (cf q f' b k) s t := by
  have h1 := ((EuclideanSpace.proj (𝕜 := ℝ) ((b, ⟨k, hk⟩) : Fin n × KatoGalerkin.box (d := d) N)).hasFDerivAt
    |>.comp_hasDerivWithinAt t h).div_const (Real.sqrt (wq q k))
  simp only [Function.comp_def] at h1
  rw [cf_eq_proj q b hk]
  simp only [cf_eq_proj q b hk]
  exact h1

theorem hasDerivAt_cf_GN_line (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (q : ℕ) {N : ℕ} (a w : GS d n N) (b : Fin n)
    {k : Fin d → ℤ} (hk : k ∈ KatoGalerkin.box N) :
    HasDerivAt (fun h : ℝ => cf q (GN A F q (a + h • w)) b k) (cf q (DGN A F q a w) b k) 0 := by
  have hl : HasDerivAt (fun t : ℝ => a + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
  have hd : HasDerivAt (fun t : ℝ => GN A F q (a + t • w)) (DGN A F q a w) 0 :=
    (hasFDerivAt_GN hA hF q a).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h1 := hasDerivWithinAt_cf_of (q := q) hd.hasDerivWithinAt (s := univ) b hk
  rw [hasDerivWithinAt_univ] at h1
  exact h1

/-- **The derivative of the projected generator does not depend on the cutoff on the common
modes**: `c_k(DG_M(P_N a)[P_N w]) = c_k(DG_N(a)[w])` for `k ∈ KatoGalerkin.box N ⊆ KatoGalerkin.box M`. -/
theorem cf_DGN_lift (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N M : ℕ} (hNM : N ≤ M) (a w : GS d n N) (b : Fin n) {k : Fin d → ℤ}
    (hk : k ∈ KatoGalerkin.box N) :
    cf q (DGN A F q (lift q (M := M) a) (lift q w)) b k = cf q (DGN A F q a w) b k := by
  have hkM : k ∈ KatoGalerkin.box M := box_mono hNM hk
  have h1 := hasDerivAt_cf_GN_line hA hF q (lift q (M := M) a) (lift q w) b hkM
  have h2 := hasDerivAt_cf_GN_line hA hF q a w b hk
  have e : (fun h : ℝ => cf q (GN A F q (lift q (M := M) a + h • lift q w)) b k) =
      fun h : ℝ => cf q (GN A F q (a + h • w)) b k := by
    funext h
    rw [cf_GN q _ b hkM, cf_GN q _ b hk, ← lift_add_smul q hNM, fld_lift q hNM]
  rw [e] at h1
  exact h1.unique h2

/-! ### The cross-cutoff estimate of the second time derivatives -/

/-- `(x - z)² ≤ 2(x - y)² + 2(y - z)²`, summed with weights. -/
theorem sum_sq_sub_le (S : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (x y z : Fin n → (Fin d → ℤ) → ℝ) :
    ∑ b, ∑ k ∈ S, w k * (x b k - z b k) ^ 2 ≤
      2 * ∑ b, ∑ k ∈ S, w k * (x b k - y b k) ^ 2 + 2 * ∑ b, ∑ k ∈ S, w k * (y b k - z b k) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have := hw k
  nlinarith [sq_nonneg (x b k - 2 * y b k + z b k), mul_nonneg this (sq_nonneg (x b k - 2 * y b k + z b k))]

set_option maxHeartbeats 1000000 in
/-- **Cross-cutoff estimate of the second time derivatives** of Galerkin trajectories (`N ≤ M`):
`Σ_{k ∈ S} wq_ρ(k) (c_k(U_N''(t)) - c_k(U_M''(t)))² ≤ C (‖P_N U_N - U_M‖²_{H^{ρ+1}}
  + ‖P_N U_N' - U_M'‖²_{H^{ρ+1}} + (2π(N+1))^{-2(q-2-ρ)})`. -/
theorem second_cauchy {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hq : ρ + 3 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N M : ℕ), N ≤ M → ∀ (T : ℝ) (γN : ℝ → GS d n N) (γM : ℝ → GS d n M),
      GalCurve A F q T R γN → GalCurve A F q T R γM → ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, wq ρ k * (cf q (DGN A F q (γN t) (GN A F q (γN t))) b k -
          cf q (DGN A F q (γM t) (GN A F q (γM t))) b k) ^ 2 ≤
        C * (‖hmS (ρ + 1) q (lift q (γN t) - γM t)‖ ^ 2 +
          ‖hmS (ρ + 1) q (lift q (GN A F q (γN t)) - GN A F q (γM t))‖ ^ 2 +
          1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (q - 2 - ρ)) := by
  obtain ⟨LD, hLD0, hLD⟩ := DGN_bound (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨LL, hLL0, hLL⟩ := DGN_lip (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨MA, hMA0, hMA⟩ := curve_lip (d := d) (n := n) (ρ := ρ + 1) (q := q) hms (by omega)
    (by omega) hA hF hR
  obtain ⟨MB, hMB0, hMB⟩ := curve_lip2 (d := d) (n := n) (ρ := q - 2) (q := q) hms (by omega)
    (by omega) hA hF hR
  refine ⟨2 * LD ^ 2 + 2 * LL ^ 2 * MA ^ 2 + MB ^ 2, by positivity,
    fun N M hNM T γN γM hGN hGM t ht S => ?_⟩
  set a := γN t
  set w := GN A F q (γN t)
  set a' := γM t
  set w' := GN A F q (γM t)
  set X := DGN A F q (lift q (M := M) a) (lift q w) - DGN A F q a' w' with hX
  set s := ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (q - 2 - ρ) with hs
  have hspos : 0 < s := by positivity
  -- the bound of `X`
  have hball : ‖hmS (ρ + 1) q (lift q (M := M) a)‖ ≤ R := by
    rw [norm_hmS_lift _ _ hNM]; exact hGN.ball (by omega) t ht
  have hball' : ‖hmS (ρ + 1) q a'‖ ≤ R := hGM.ball (by omega) t ht
  have hw' : ‖hmS (ρ + 1) q w'‖ ≤ MA := (hMA M T γM hGM).1 t ht
  have hXb : ‖hmS ρ q X‖ ≤ LD * ‖hmS (ρ + 1) q (lift q w - w')‖ +
      LL * ‖hmS (ρ + 1) q (lift q a - a')‖ * MA := by
    have e : X = DGN A F q (lift q (M := M) a) (lift q w - w') +
        (DGN A F q (lift q (M := M) a) w' - DGN A F q a' w') := by
      rw [hX, DGN_sub_right]; abel
    rw [e, hmS_add]
    refine (norm_add_le _ _).trans (add_le_add (hLD q M _ _ hball) ?_)
    exact (hLL q M _ _ w' hball hball').trans
      (mul_le_mul_of_nonneg_left hw' (by positivity))
  have hXsq : ‖hmS ρ q X‖ ^ 2 ≤ 2 * LD ^ 2 * ‖hmS (ρ + 1) q (lift q w - w')‖ ^ 2 +
      2 * LL ^ 2 * MA ^ 2 * ‖hmS (ρ + 1) q (lift q a - a')‖ ^ 2 := by
    have h0 := norm_nonneg (hmS ρ q X)
    have := pow_le_pow_left₀ h0 hXb 2
    nlinarith [sq_nonneg (LD * ‖hmS (ρ + 1) q (lift q w - w')‖ -
      LL * ‖hmS (ρ + 1) q (lift q a - a')‖ * MA)]
  -- the high modes of `U_M''`
  have hhigh : ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k *
      cf q (DGN A F q a' w') b k ^ 2 ≤ MB ^ 2 / s := by
    rw [le_div_iff₀ hspos, Finset.sum_mul]
    have hB := sum_wq_cf_le_hmS (q - 2) q (DGN A F q a' w') (S.filter (fun k => k ∉ KatoGalerkin.box N))
    have hB' : ‖hmS (q - 2) q (DGN A F q a' w')‖ ^ 2 ≤ MB ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((hMB M T γM hGM).1 t ht) 2
    refine le_trans ?_ (hB.trans hB')
    refine Finset.sum_le_sum fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := wq_tail (Finset.mem_filter.1 hk).2 ρ (q - 2 - ρ)
    rw [show ρ + (q - 2 - ρ) = q - 2 by omega] at h1
    nlinarith [sq_nonneg (cf q (DGN A F q a' w') b k)]
  -- split the modes
  have hsplit : ∀ b, ∑ k ∈ S, wq ρ k * (cf q (DGN A F q a w) b k -
      cf q (DGN A F q a' w') b k) ^ 2 = ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k *
        cf q X b k ^ 2 + ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k *
        cf q (DGN A F q a' w') b k ^ 2 := by
    intro b
    rw [← Finset.sum_filter_add_sum_filter_not S (fun k => k ∈ KatoGalerkin.box N)]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkN := (Finset.mem_filter.1 hk).2
      rw [hX, cf_sub', cf_DGN_lift hA hF q hNM a w b hkN]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkN := (Finset.mem_filter.1 hk).2
      rw [cf_eq_zero _ b hkN]; ring
  have hlow : ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * cf q X b k ^ 2 ≤
      ‖hmS ρ q X‖ ^ 2 := sum_wq_cf_le_hmS ρ q X _
  calc ∑ b, ∑ k ∈ S, wq ρ k * (cf q (DGN A F q a w) b k - cf q (DGN A F q a' w') b k) ^ 2
      = ∑ b, ∑ k ∈ S.filter (fun k => k ∈ KatoGalerkin.box N), wq ρ k * cf q X b k ^ 2 +
        ∑ b, ∑ k ∈ S.filter (fun k => k ∉ KatoGalerkin.box N), wq ρ k * cf q (DGN A F q a' w') b k ^ 2 := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => hsplit b
    _ ≤ (2 * LD ^ 2 * ‖hmS (ρ + 1) q (lift q w - w')‖ ^ 2 +
          2 * LL ^ 2 * MA ^ 2 * ‖hmS (ρ + 1) q (lift q a - a')‖ ^ 2) + MB ^ 2 / s :=
        add_le_add (hlow.trans hXsq) hhigh
    _ ≤ (2 * LD ^ 2 + 2 * LL ^ 2 * MA ^ 2 + MB ^ 2) *
          (‖hmS (ρ + 1) q (lift q a - a')‖ ^ 2 + ‖hmS (ρ + 1) q (lift q w - w')‖ ^ 2 + 1 / s) := by
        have h1 := sq_nonneg ‖hmS (ρ + 1) q (lift q w - w')‖
        have h2 := sq_nonneg ‖hmS (ρ + 1) q (lift q a - a')‖
        have h3 : 0 ≤ 1 / s := by positivity
        have e : MB ^ 2 / s = MB ^ 2 * (1 / s) := by ring
        rw [e]
        nlinarith [mul_nonneg (sq_nonneg LD) h2, mul_nonneg (sq_nonneg LD) h3,
          mul_nonneg (mul_nonneg (sq_nonneg LL) (sq_nonneg MA)) h1,
          mul_nonneg (mul_nonneg (sq_nonneg LL) (sq_nonneg MA)) h3,
          mul_nonneg (sq_nonneg MB) h1, mul_nonneg (sq_nonneg MB) h2]

/-! ### The limit of the second time derivatives -/

/-- **A quadratic Taylor remainder bound gives the derivative** within a set. -/
theorem hasDerivWithinAt_of_sq_bound {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {t L : ℝ}
    (h : ∀ x ∈ s, |f x - f t - (x - t) * f'| ≤ L * (x - t) ^ 2) :
    HasDerivWithinAt f f' s t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ x in 𝓝 t, |x - t| < c / (|L| + 1) := by
    have h1 : Tendsto (fun x => |x - t|) (𝓝 t) (𝓝 0) := by
      have := ((continuous_id.sub (continuous_const (y := t))).abs).tendsto t
      simpa using this
    exact h1.eventually (gt_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with x hx hx'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  have h1 := h x hx
  have hL1 : 0 < |L| + 1 := by positivity
  have h2 : (|L| + 1) * |x - t| ≤ c := by
    rw [lt_div_iff₀ hL1] at hx'; linarith
  have h3 : L * (x - t) ^ 2 ≤ (|L| + 1) * |x - t| * |x - t| := by
    have e : (x - t) ^ 2 = |x - t| * |x - t| := by rw [← sq, sq_abs]
    rw [e]
    have := abs_nonneg (x - t)
    nlinarith [le_abs_self L, mul_nonneg this this]
  calc |f x - f t - (x - t) * f'| ≤ (|L| + 1) * |x - t| * |x - t| := h1.trans h3
    _ ≤ c * |x - t| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

/-- Pointwise convergence of coefficients from a coefficient rate. -/
theorem tendsto_of_sum_le {ρ : ℕ} {y : ℕ → Fin n → (Fin d → ℤ) → ℝ}
    {z : Fin n → (Fin d → ℤ) → ℝ} {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ M, ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq ρ k * (y M b k - z b k) ^ 2 ≤ e M)
    (b : Fin n) (k : Fin d → ℤ) : Tendsto (fun M => y M b k) atTop (𝓝 (z b k)) := by
  have hb : ∀ M, (y M b k - z b k) ^ 2 ≤ e M := fun M => by
    have h1 := h M {k}
    simp only [Finset.sum_singleton] at h1
    have h2 : wq ρ k * (y M b k - z b k) ^ 2 ≤ ∑ b, wq ρ k * (y M b k - z b k) ^ 2 :=
      Finset.single_le_sum (f := fun b => wq ρ k * (y M b k - z b k) ^ 2)
        (fun b _ => mul_nonneg (wq_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ b)
    have h3 : (y M b k - z b k) ^ 2 ≤ wq ρ k * (y M b k - z b k) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_wq ρ k)
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) (by
    simpa using (Real.continuous_sqrt.tendsto 0).comp he)
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (hb M)

theorem one_div_two_pi_pow_le {j : ℕ} (hj : 1 ≤ j) (N : ℕ) :
    1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j ≤ 1 / ((N : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ 2 * π * ((N : ℝ) + 1) := one_le_two_pi_succ N
  have h2 : (N : ℝ) + 1 ≤ 2 * π * ((N : ℝ) + 1) := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h3 : 2 * π * ((N : ℝ) + 1) ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j := by
    calc 2 * π * ((N : ℝ) + 1) ≤ (2 * π * ((N : ℝ) + 1)) ^ 2 := by nlinarith
      _ = ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j := pow_le_pow_right₀ (by nlinarith) hj
  exact one_div_le_one_div_of_le (by positivity) (h2.trans h3)

theorem tendsto_one_div_two_pi_pow {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun N : ℕ => 1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ j) atTop (𝓝 0) :=
  squeeze_zero (fun N => by positivity) (fun N => one_div_two_pi_pow_le hj N)
    tendsto_one_div_add_atTop_nhds_zero_nat

set_option maxHeartbeats 2000000 in
/-- **The second time derivative of the Galerkin limit and its rate** (`eq:generated-Galerkin-rate`,
`a = 2`, Fourier form): for `2m_s ≤ ρ + 1`, `ρ + 3 ≤ q` and every radius `R` there is `C` such
that for every family of Galerkin trajectories `U_N` on `[0, T]` in the `H^q` ball of radius `R`
which converges to coefficient functions `c₀` (state) and `c₁` (time derivative) in `H^{ρ+1}` with
antitone rates `e₀(N), e₁(N) → 0`, there are coefficient functions `D₂` with
* `d/dt c₁(t) = D₂(t)` on `[0, T]` (the second time derivative of the limit), and
* `Σ_b Σ_{k ∈ S} wq_ρ(k) (c_k(U_N''(t)) - D₂(t))² ≤ C (e₀(N) + e₁(N) + (2π(N+1))^{-2(q-2-ρ)})`
  for every finite mode set `S` (`U_N'' = DG_N(U_N)[G_N(U_N)]`). -/
theorem second_limit {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hq : ρ + 3 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (γ : (N : ℕ) → ℝ → GS d n N),
      (∀ N, GalCurve A F q T R (γ N)) →
      ∀ (c₀ c₁ : Fin n → (Fin d → ℤ) → ℝ → ℝ) (e₀ e₁ : ℕ → ℝ),
      Antitone e₀ → Antitone e₁ → Tendsto e₀ atTop (𝓝 0) → Tendsto e₁ atTop (𝓝 0) →
      (∀ N, ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
        ∑ b, ∑ k ∈ S, wq (ρ + 1) k * (cf q (γ N t) b k - c₀ b k t) ^ 2 ≤ e₀ N) →
      (∀ N, ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
        ∑ b, ∑ k ∈ S, wq (ρ + 1) k * (cf q (GN A F q (γ N t)) b k - c₁ b k t) ^ 2 ≤ e₁ N) →
      ∃ D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ,
        (∀ b k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => c₁ b k s) (D₂ b k t) (Icc 0 T) t) ∧
        ∀ N, ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
          ∑ b, ∑ k ∈ S, wq ρ k * (cf q (DGN A F q (γ N t) (GN A F q (γ N t))) b k -
            D₂ b k t) ^ 2 ≤
          C * (e₀ N + e₁ N + 1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (q - 2 - ρ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := second_cauchy (d := d) (n := n) hms hρ hq hA hF hR
  obtain ⟨MC, hMC0, hMC⟩ := curve_lip3 (d := d) (n := n) (ρ := ρ) (q := q) hms hρ hq hA hF hR
  refine ⟨4 * C₀, by positivity, fun T γ hG c₀ c₁ e₀ e₁ ha₀ ha₁ ht₀ ht₁ h₀ h₁ => ?_⟩
  have hj : 1 ≤ q - 2 - ρ := by omega
  set sN : ℕ → ℝ := fun N => 1 / ((2 * π * ((N : ℝ) + 1)) ^ 2) ^ (q - 2 - ρ) with hsN
  have hsN0 : ∀ N, 0 ≤ sN N := fun N => by simp only [hsN]; positivity
  have he₀0 : ∀ N, 0 ≤ e₀ N := fun N => ha₀.le_of_tendsto ht₀ N
  have he₁0 : ∀ N, 0 ≤ e₁ N := fun N => ha₁.le_of_tendsto ht₁ N
  set x : (N : ℕ) → ℝ → Fin n → (Fin d → ℤ) → ℝ := fun N t b k =>
    cf q (DGN A F q (γ N t) (GN A F q (γ N t))) b k with hx
  -- the lifted differences
  have hdiff0 : ∀ N M, N ≤ M → ∀ t ∈ Icc 0 T,
      ‖hmS (ρ + 1) q (lift q (M := M) (γ N t) - γ M t)‖ ^ 2 ≤ 2 * e₀ N + 2 * e₀ M := by
    intro N M hNM t ht
    rw [norm_hmS_lift_sub_sq _ _ hNM]
    refine (sum_sq_sub_le (KatoGalerkin.box M) (wq (ρ + 1)) (fun k => wq_nonneg _ _)
      (fun b k => cf q (γ N t) b k) (fun b k => c₀ b k t)
      (fun b k => cf q (γ M t) b k)).trans ?_
    have h1 := h₀ N t ht (KatoGalerkin.box M)
    have h2 := h₀ M t ht (KatoGalerkin.box M)
    have e : ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k * (c₀ b k t - cf q (γ M t) b k) ^ 2 =
        ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k * (cf q (γ M t) b k - c₀ b k t) ^ 2 :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    linarith
  have hdiff1 : ∀ N M, N ≤ M → ∀ t ∈ Icc 0 T,
      ‖hmS (ρ + 1) q (lift q (M := M) (GN A F q (γ N t)) - GN A F q (γ M t))‖ ^ 2 ≤
        2 * e₁ N + 2 * e₁ M := by
    intro N M hNM t ht
    rw [norm_hmS_lift_sub_sq _ _ hNM]
    refine (sum_sq_sub_le (KatoGalerkin.box M) (wq (ρ + 1)) (fun k => wq_nonneg _ _)
      (fun b k => cf q (GN A F q (γ N t)) b k) (fun b k => c₁ b k t)
      (fun b k => cf q (GN A F q (γ M t)) b k)).trans ?_
    have h1 := h₁ N t ht (KatoGalerkin.box M)
    have h2 := h₁ M t ht (KatoGalerkin.box M)
    have e : ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k *
        (c₁ b k t - cf q (GN A F q (γ M t)) b k) ^ 2 =
        ∑ b, ∑ k ∈ KatoGalerkin.box M, wq (ρ + 1) k *
          (cf q (GN A F q (γ M t)) b k - c₁ b k t) ^ 2 :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    linarith
  -- the Cauchy bound
  set B : ℕ → ℝ := fun N => C₀ * (4 * e₀ N + 4 * e₁ N + sN N) with hBdef
  have hcau : ∀ N M, N ≤ M → ∀ t ∈ Icc 0 T, ∀ S : Finset (Fin d → ℤ),
      ∑ b, ∑ k ∈ S, wq ρ k * (x N t b k - x M t b k) ^ 2 ≤ B N := by
    intro N M hNM t ht S
    refine (hC₀ N M hNM T (γ N) (γ M) (hG N) (hG M) t ht S).trans ?_
    have k1 := hdiff0 N M hNM t ht
    have k2 := hdiff1 N M hNM t ht
    have k3 := ha₀ hNM
    have k4 := ha₁ hNM
    exact mul_le_mul_of_nonneg_left (by simp only [hsN]; linarith) hC₀0
  have hB : Tendsto B atTop (𝓝 0) := by
    have := (((ht₀.const_mul 4).add (ht₁.const_mul 4)).add
      (tendsto_one_div_two_pi_pow hj)).const_mul C₀
    simpa [hBdef, hsN] using this
  have hpt : ∀ N M, N ≤ M → ∀ t ∈ Icc 0 T, ∀ b k, (x N t b k - x M t b k) ^ 2 ≤ B N := by
    intro N M hNM t ht b k
    have h1 := hcau N M hNM t ht {k}
    simp only [Finset.sum_singleton] at h1
    have h2 : wq ρ k * (x N t b k - x M t b k) ^ 2 ≤
        ∑ b, wq ρ k * (x N t b k - x M t b k) ^ 2 :=
      Finset.single_le_sum (f := fun b => wq ρ k * (x N t b k - x M t b k) ^ 2)
        (fun b _ => mul_nonneg (wq_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ b)
    have h3 : (x N t b k - x M t b k) ^ 2 ≤ wq ρ k * (x N t b k - x M t b k) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_wq ρ k)
    linarith
  have hcs : ∀ t ∈ Icc 0 T, ∀ b k, CauchySeq (fun M => x M t b k) := by
    intro t ht b k
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hB.eventually (gt_mem_nhds (by positivity :
      (0 : ℝ) < ε ^ 2)))
    refine ⟨N₀, fun M hM => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_lt_of_sq_lt_sq ((hpt N₀ M hM t ht b k).trans_lt (hN₀ N₀ le_rfl)) hε.le
  set D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ := fun b k t => limUnder atTop (fun M => x M t b k)
    with hD₂
  have hD : ∀ t ∈ Icc 0 T, ∀ b k, Tendsto (fun M => x M t b k) atTop (𝓝 (D₂ b k t)) :=
    fun t ht b k => (hcs t ht b k).tendsto_limUnder
  refine ⟨D₂, fun b k t ht => ?_, fun N t ht S => ?_⟩
  · -- the derivative
    obtain ⟨Mk, hMk⟩ := KatoGalerkin.exists_mem_box k
    set f : ℕ → ℝ → ℝ := fun M s => cf q (GN A F q (γ M s)) b k with hf
    have hfd : ∀ M, Mk ≤ M → ∀ s ∈ Icc 0 T, HasDerivWithinAt (f M) (x M s b k) (Icc 0 T) s :=
      fun M hM s hs => hasDerivWithinAt_cf_of ((hG M).deriv2 hA hF s hs) b (box_mono hM hMk)
    have hxl : ∀ M, ∀ s ∈ Icc 0 T, ∀ u ∈ Icc 0 T, |x M s b k - x M u b k| ≤ MC * |s - u| := by
      intro M s hs u hu
      simp only [hx]
      rw [← cf_sub']
      exact (abs_cf_le_hmS ρ q _ b k).trans (hMC M T (γ M) (hG M) s hs u hu)
    have htay : ∀ M, Mk ≤ M → ∀ s ∈ Icc 0 T,
        |f M s - f M t - (s - t) * x M t b k| ≤ 3 / 2 * MC * (s - t) ^ 2 := by
      intro M hM s hs
      have hlipM : ∀ y ∈ Icc 0 T, ∀ z ∈ Icc 0 T,
          ‖x M y b k - x M z b k‖ ≤ MC * |y - z| := fun y hy z hz => by
        rw [Real.norm_eq_abs]; exact hxl M y hy z hz
      rcases le_total t s with hts | hst
      · have h1 := HermiteLip.taylor_lip1 (F := ℝ) (g := f M) (g' := fun s => x M s b k)
          (hfd M hM) hlipM ht.1 (sub_nonneg.2 hts) (by rw [add_sub_cancel]; exact hs.2)
        rw [add_sub_cancel, Real.norm_eq_abs, smul_eq_mul] at h1
        nlinarith [sq_nonneg (s - t)]
      · have h1 := HermiteLip.taylor_lip1 (F := ℝ) (g := f M) (g' := fun s => x M s b k)
          (hfd M hM) hlipM hs.1 (sub_nonneg.2 hst) (by rw [add_sub_cancel]; exact ht.2)
        rw [add_sub_cancel, Real.norm_eq_abs, smul_eq_mul] at h1
        have h2 := hxl M t ht s hs
        have e : f M s - f M t - (s - t) * x M t b k =
            -(f M t - f M s - (t - s) * x M s b k) + (t - s) * (x M t b k - x M s b k) := by ring
        rw [e]
        have hts' : |t - s| = t - s := abs_of_nonneg (by linarith)
        calc |-(f M t - f M s - (t - s) * x M s b k) + (t - s) * (x M t b k - x M s b k)|
            ≤ |f M t - f M s - (t - s) * x M s b k| + (t - s) * |x M t b k - x M s b k| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_neg, abs_mul, hts']
          _ ≤ MC * (t - s) ^ 2 / 2 + (t - s) * (MC * (t - s)) := by
              rw [hts'] at h2
              exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
          _ = 3 / 2 * MC * (s - t) ^ 2 := by ring
    have hlimf : ∀ s ∈ Icc 0 T, Tendsto (fun M => f M s) atTop (𝓝 (c₁ b k s)) := fun s hs =>
      tendsto_of_sum_le (ρ := ρ + 1) (y := fun M b k => cf q (GN A F q (γ M s)) b k)
        (z := fun b k => c₁ b k s) ht₁ (fun M S => h₁ M s hs S) b k
    refine hasDerivWithinAt_of_sq_bound (L := 3 / 2 * MC) fun s hs => ?_
    have hlim : Tendsto (fun M => |f M s - f M t - (s - t) * x M t b k|) atTop
        (𝓝 |c₁ b k s - c₁ b k t - (s - t) * D₂ b k t|) :=
      (((hlimf s hs).sub (hlimf t ht)).sub ((hD t ht b k).const_mul (s - t))).abs
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨Mk, fun M hM => htay M hM s hs⟩)
  · -- the rate
    have hlim : Tendsto (fun M => ∑ b, ∑ k ∈ S, wq ρ k * (x N t b k - x M t b k) ^ 2) atTop
        (𝓝 (∑ b, ∑ k ∈ S, wq ρ k * (x N t b k - D₂ b k t) ^ 2)) :=
      tendsto_finset_sum _ fun b _ => tendsto_finset_sum _ fun k _ =>
        ((tendsto_const_nhds.sub (hD t ht b k)).pow 2).const_mul _
    have hle : ∑ b, ∑ k ∈ S, wq ρ k * (x N t b k - D₂ b k t) ^ 2 ≤ B N :=
      le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun M hM => hcau N M hM t ht S⟩)
    refine hle.trans ?_
    simp only [hBdef]
    have h1 := hsN0 N
    have h2 := he₀0 N
    have h3 := he₁0 N
    have h4 : 4 * e₀ N + 4 * e₁ N + sN N ≤ 4 * (e₀ N + e₁ N + sN N) := by linarith
    calc C₀ * (4 * e₀ N + 4 * e₁ N + sN N) ≤ C₀ * (4 * (e₀ N + e₁ N + sN N)) :=
          mul_le_mul_of_nonneg_left h4 hC₀0
      _ = 4 * C₀ * (e₀ N + e₁ N + sN N) := by ring

end RenewalGeometry.KatoRate2
