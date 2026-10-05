/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoSecondDifference
import RenewalGeometry.Continuum.HermiteLipschitzReadout

/-!
# The `O(τ²)` time rate of the spectral midpoint scheme and its Hermite readout

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript: `eq:generated-time-rate` ("Applying this
estimate to the local truncation residual of the exact semidiscrete solution yields
`max_j ‖U^j - U_N(t_j)‖_{H^{s+4}} ≤ Cτ²`") and the semidiscrete half of `eq:generated-Hermite`.
Setting of `KatoGalerkinODE`: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d`, smooth real symmetric `A^i`,
smooth `F`, Galerkin space `GS d n N` (Euclidean norm = `H^q` norm), `H^ρ` coordinates
`KatoCausal.hmS ρ q`.

* `GalCurve` — a semidiscrete (Galerkin) trajectory `U_N' = G_N(U_N)` on `[0, T]` in the `H^q` ball;
  `GalCurve.deriv2`: `U_N'' = DG_N(U_N)[G_N(U_N)]` (within `[0, T]`).
* **Cutoff-uniform regularity in time**: `curve_lip` (`U_N` Lipschitz in `H^ρ`, `ρ + 1 ≤ q`),
  `curve_lip2` (`U_N'` Lipschitz and `U_N''` bounded in `H^ρ`, `ρ + 2 ≤ q`), `curve_lip3`
  (`U_N''` Lipschitz in `H^ρ`, `ρ + 3 ≤ q`); all constants depend only on the `H^q` radius
  (`KatoSecond.DGN_bound`, `KatoSecond.DGN_lip`).
* **`residual_bound`** — the local truncation residual of the semidiscrete solution in the midpoint
  scheme, `r_j = τ⁻¹(U_N(t_{j+1}) - U_N(t_j)) - G_N((U_N(t_j) + U_N(t_{j+1}))/2)`, satisfies
  `‖r_j‖_{H^ρ} ≤ C τ²` (`ρ + 3 ≤ q`).
* **`midpoint_time_rate`** (`eq:generated-time-rate`, first half) — for the midpoint recursion
  `U^j` and a Galerkin trajectory `U_N` (both in the `H^q` ball):
  `‖U^j - U_N(t_j)‖_{H^m} ≤ C (‖U^0 - U_N(0)‖_{H^m} + τ²)` for `jτ ≤ T`, uniformly in `N` and `τ`
  (`τK ≤ 1`; `m ≥ 1`, `m_s + m + 1 ≤ q`, `m + 3 ≤ q`), by `KatoCausal.midpoint_causal_Hm`.
* **`hermite_semidiscrete`** (`eq:generated-Hermite`, semidiscrete comparison) — the cubic Hermite
  readout of the midpoint record (nodal values `U^j`, nodal slopes `G_N(U^j)`) differs from the
  semidiscrete solution by `O(δ₀ + τ²)` in `H^ρ` (values and first time derivatives) and by
  `O(δ₀/τ + τ)` in `H^ρ` (second time derivatives), `δ₀ = ‖U^0 - U_N(0)‖_{H^{ρ+1}}`, `ρ + 4 ≤ q`.

Disclosed rendering: `Σ = 𝕋^d`; smooth coefficients on all of `ℝ^n` (a chart enters by a smooth
cutoff extension); the semidiscrete trajectory is differentiable within `[0, T]`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoTimeRate

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin KatoSecond
open KatoCausal (hmS hmS_apply hmS_add hmS_smul hmS_sub hmS_mid norm_hmS_sq)

set_option linter.unusedSectionVars false

variable {d n : ℕ}
variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-! ### Bounds of the projected generator -/

theorem hmS_zero (m q N : ℕ) : hmS m q (0 : GS d n N) = 0 := PiLp.ext fun p => by
  simp [hmS_apply]

theorem genG_zero_fun' (b : Fin n) (x : ST d) :
    genG A F (fun _ _ => (0 : ℝ)) b x = F b 0 := by
  simp only [genG, compF]
  have h0 : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
  have hpd : ∀ i : Fin d, pd (fun _ : ST d => (0 : ℝ)) i.succ x = 0 := fun i => by
    simp [SobolevOpen.pd]
  simp [hpd, h0]

theorem norm_hmS_GN_zero_sq_le (ρ q N : ℕ) :
    ‖hmS ρ q (GN A F q (0 : GS d n N))‖ ^ 2 ≤ ∑ b, F b 0 ^ 2 := by
  have hG : ∀ b, genG A F (fld q (0 : GS d n N)) b = fun _ => F b 0 := fun b => by
    funext x; rw [KatoCFL.fld_zero]; exact genG_zero_fun' b x
  refine (norm_hmS_sq_le_of_coef ρ q _ (fun b _ => F b 0) (fun b => contDiff_const)
    (fun b _ _ => rfl) (fun p => by rw [GN_apply, hG p.1])).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun b _ => Q_const ρ (F b 0) 0

/-- **Cutoff-uniform `H^ρ` bound of the projected generator** on the `H^{ρ+1}` ball. -/
theorem GN_bound_hm {ms ρ : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (q N : ℕ) (a : GS d n N), ‖hmS (ρ + 1) q a‖ ≤ R →
      ‖hmS ρ q (GN A F q a)‖ ≤ M := by
  obtain ⟨L, hL0, hL⟩ := GN_lip_hm (d := d) (n := n) hms hρ hA hF hR
  refine ⟨L * R + Real.sqrt (∑ b, F b 0 ^ 2), by positivity, fun q N a ha => ?_⟩
  have h0 : ‖hmS ρ q (GN A F q (0 : GS d n N))‖ ≤ Real.sqrt (∑ b, F b 0 ^ 2) :=
    Real.le_sqrt_of_sq_le (norm_hmS_GN_zero_sq_le ρ q N)
  have h1 := hL q N a 0 ha (by rw [hmS_zero, norm_zero]; exact hR)
  rw [sub_zero] at h1
  calc ‖hmS ρ q (GN A F q a)‖
      = ‖hmS ρ q (GN A F q a - GN A F q 0) + hmS ρ q (GN A F q 0)‖ := by
        rw [← hmS_add, sub_add_cancel]
    _ ≤ ‖hmS ρ q (GN A F q a - GN A F q 0)‖ + ‖hmS ρ q (GN A F q (0 : GS d n N))‖ :=
        norm_add_le _ _
    _ ≤ L * R + Real.sqrt (∑ b, F b 0 ^ 2) :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left ha hL0)) h0

/-! ### Galerkin trajectories -/

/-- **A Galerkin trajectory** `U_N' = G_N(U_N)` on `[0, T]` (derivative within `[0, T]`) in the
`H^q` ball of radius `R`. -/
structure GalCurve (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ)
    (q : ℕ) {N : ℕ} (T R : ℝ) (γ : ℝ → GS d n N) : Prop where
  deriv : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (GN A F q (γ t)) (Icc 0 T) t
  bound : ∀ t ∈ Icc 0 T, ‖γ t‖ ≤ R

theorem hasDerivWithinAt_hmS {N : ℕ} {f : ℝ → GS d n N} {f' : GS d n N} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt f f' s t) (m q : ℕ) :
    HasDerivWithinAt (fun t => hmS m q (f t)) (hmS m q f') s t :=
  (hmSL (d := d) (n := n) m q).hasFDerivAt.comp_hasDerivWithinAt t h

/-- **The second time derivative of a Galerkin trajectory**: `U_N'' = DG_N(U_N)[G_N(U_N)]`. -/
theorem GalCurve.deriv2 {q N : ℕ} {T R : ℝ} {γ : ℝ → GS d n N} (hG : GalCurve A F q T R γ)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => GN A F q (γ t))
      (DGN A F q (γ t) (GN A F q (γ t))) (Icc 0 T) t := fun t ht =>
  (hasFDerivAt_GN hA hF q (γ t)).comp_hasDerivWithinAt t (hG.deriv t ht)

theorem GalCurve.ball {ρ q N : ℕ} (hq : ρ ≤ q) {T R : ℝ} {γ : ℝ → GS d n N}
    (hG : GalCurve A F q T R γ) : ∀ t ∈ Icc 0 T, ‖hmS ρ q (γ t)‖ ≤ R := fun t ht =>
  (norm_hmS_le hq _).trans (hG.bound t ht)

/-- **Galerkin trajectories are Lipschitz in `H^ρ`** (`ρ + 1 ≤ q`), with `‖U_N'‖_{H^ρ} ≤ M`,
uniformly in the cutoff. -/
theorem curve_lip {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1) (hq : ρ + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (T : ℝ) (γ : ℝ → GS d n N), GalCurve A F q T R γ →
      (∀ t ∈ Icc 0 T, ‖hmS ρ q (GN A F q (γ t))‖ ≤ M) ∧
      ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ‖hmS ρ q (γ t - γ s)‖ ≤ M * |t - s| := by
  obtain ⟨M, hM0, hM⟩ := GN_bound_hm (d := d) (n := n) hms hρ hA hF hR
  refine ⟨M, hM0, fun N T γ hG => ?_⟩
  have hb : ∀ t ∈ Icc 0 T, ‖hmS ρ q (GN A F q (γ t))‖ ≤ M := fun t ht =>
    hM q N (γ t) (hG.ball hq t ht)
  refine ⟨hb, fun t ht s hs => ?_⟩
  rw [hmS_sub]
  exact HermiteLip.lip_of_deriv_bound (g := fun t => hmS ρ q (γ t))
    (fun x hx => hasDerivWithinAt_hmS (hG.deriv x hx) ρ q) hb t ht s hs

/-- **Lipschitz first and bounded second time derivatives in `H^ρ`** (`ρ + 2 ≤ q`). -/
theorem curve_lip2 {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1) (hq : ρ + 2 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (T : ℝ) (γ : ℝ → GS d n N), GalCurve A F q T R γ →
      (∀ t ∈ Icc 0 T, ‖hmS ρ q (DGN A F q (γ t) (GN A F q (γ t)))‖ ≤ M) ∧
      ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
        ‖hmS ρ q (GN A F q (γ t) - GN A F q (γ s))‖ ≤ M * |t - s| := by
  obtain ⟨L, hL0, hL⟩ := GN_lip_hm (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨LD, hLD0, hLD⟩ := DGN_bound (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨MA, hMA0, hMA⟩ := curve_lip (d := d) (n := n) (ρ := ρ + 1) (q := q) hms (by omega)
    (by omega) hA hF hR
  refine ⟨L * MA + LD * MA, by positivity, fun N T γ hG => ⟨fun t ht => ?_, fun t ht s hs => ?_⟩⟩
  · have h := (hLD q N (γ t) (GN A F q (γ t)) (hG.ball (by omega) t ht)).trans
      (mul_le_mul_of_nonneg_left ((hMA N T γ hG).1 t ht) hLD0)
    have : 0 ≤ L * MA := by positivity
    linarith
  · have h := hL q N (γ t) (γ s) (hG.ball (by omega) t ht) (hG.ball (by omega) s hs)
    have h2 := (hMA N T γ hG).2 t ht s hs
    calc ‖hmS ρ q (GN A F q (γ t) - GN A F q (γ s))‖ ≤ L * (MA * |t - s|) :=
          h.trans (mul_le_mul_of_nonneg_left h2 hL0)
      _ ≤ (L * MA + LD * MA) * |t - s| := by
          have : 0 ≤ LD * MA * |t - s| := by positivity
          nlinarith

theorem DGN_sub_right {q N : ℕ} (a w w' : GS d n N) :
    DGN A F q a (w - w') = DGN A F q a w - DGN A F q a w' := by
  unfold DGN; exact map_sub _ w w'

/-- **The second time derivative of a Galerkin trajectory is Lipschitz in `H^ρ`**
(`ρ + 3 ≤ q`), uniformly in the cutoff. -/
theorem curve_lip3 {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1) (hq : ρ + 3 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (T : ℝ) (γ : ℝ → GS d n N), GalCurve A F q T R γ →
      ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
        ‖hmS ρ q (DGN A F q (γ t) (GN A F q (γ t)) - DGN A F q (γ s) (GN A F q (γ s)))‖ ≤
          M * |t - s| := by
  obtain ⟨LD, hLD0, hLD⟩ := DGN_bound (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨LL, hLL0, hLL⟩ := DGN_lip (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨MA, hMA0, hMA⟩ := curve_lip (d := d) (n := n) (ρ := ρ + 1) (q := q) hms (by omega)
    (by omega) hA hF hR
  obtain ⟨MB, hMB0, hMB⟩ := curve_lip2 (d := d) (n := n) (ρ := ρ + 1) (q := q) hms (by omega)
    (by omega) hA hF hR
  refine ⟨LD * MB + LL * MA * MA, by positivity, fun N T γ hG t ht s hs => ?_⟩
  have e : DGN A F q (γ t) (GN A F q (γ t)) - DGN A F q (γ s) (GN A F q (γ s)) =
      DGN A F q (γ t) (GN A F q (γ t) - GN A F q (γ s)) +
        (DGN A F q (γ t) (GN A F q (γ s)) - DGN A F q (γ s) (GN A F q (γ s))) := by
    rw [DGN_sub_right]; abel
  rw [e, hmS_add]
  have h1 := (hLD q N (γ t) (GN A F q (γ t) - GN A F q (γ s)) (hG.ball (by omega) t ht)).trans
    (mul_le_mul_of_nonneg_left ((hMB N T γ hG).2 t ht s hs) hLD0)
  have h2 := hLL q N (γ t) (γ s) (GN A F q (γ s)) (hG.ball (by omega) t ht)
    (hG.ball (by omega) s hs)
  have h3 := (hMA N T γ hG).2 t ht s hs
  have h4 := (hMA N T γ hG).1 s hs
  have h5 : LL * ‖hmS (ρ + 1) q (γ t - γ s)‖ * ‖hmS (ρ + 1) q (GN A F q (γ s))‖ ≤
      LL * (MA * |t - s|) * MA :=
    mul_le_mul (mul_le_mul_of_nonneg_left h3 hLL0) h4 (norm_nonneg _) (by positivity)
  calc _ ≤ ‖hmS ρ q (DGN A F q (γ t) (GN A F q (γ t) - GN A F q (γ s)))‖ +
        ‖hmS ρ q (DGN A F q (γ t) (GN A F q (γ s)) - DGN A F q (γ s) (GN A F q (γ s)))‖ :=
        norm_add_le _ _
    _ ≤ LD * (MB * |t - s|) + LL * (MA * |t - s|) * MA := add_le_add h1 (h2.trans h5)
    _ = (LD * MB + LL * MA * MA) * |t - s| := by ring

/-! ### The local truncation residual -/

theorem norm_mid_le {N : ℕ} {R : ℝ} {a b : GS d n N} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖SpectralGalerkin.mid a b‖ ≤ R := by
  unfold SpectralGalerkin.mid
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := norm_add_le a b
  linarith

/-- **The local truncation residual of the semidiscrete solution is `O(τ²)` in `H^ρ`**
(`ρ + 3 ≤ q`): `‖τ⁻¹(U_N(t+τ) - U_N(t)) - G_N((U_N(t) + U_N(t+τ))/2)‖_{H^ρ} ≤ C τ²`, uniformly
in the cutoff. -/
theorem residual_bound {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hq : ρ + 3 ≤ q) (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T : ℝ) (γ : ℝ → GS d n N), GalCurve A F q T R γ →
      ∀ t τ : ℝ, 0 ≤ t → 0 < τ → t + τ ≤ T →
        ‖hmS ρ q (τ⁻¹ • (γ (t + τ) - γ t) -
          GN A F q (SpectralGalerkin.mid (γ t) (γ (t + τ))))‖ ≤ C * τ ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := GN_lip_hm (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨MB, hMB0, hMB⟩ := curve_lip2 (d := d) (n := n) (ρ := ρ + 1) (q := q) hms (by omega)
    (by omega) hA hF hR
  obtain ⟨MC, hMC0, hMC⟩ := curve_lip3 (d := d) (n := n) (ρ := ρ) (q := q) hms hρ hq hA hF hR
  refine ⟨7 * MC / 24 + L * (3 * MB / 8), by positivity, fun N T γ hG t τ ht hτ htτ => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have htm : t + τ / 2 ∈ Icc 0 T := ⟨by linarith, by linarith⟩
  have ht0 : t ∈ Icc 0 T := ⟨ht, by linarith⟩
  have ht1 : t + τ ∈ Icc 0 T := ⟨by linarith, htτ⟩
  -- the step estimate in `H^ρ`
  have hstep := HermiteLip.midpoint_step_lip (z := fun t => hmS ρ q (γ t))
    (z' := fun t => hmS ρ q (GN A F q (γ t)))
    (z'' := fun t => hmS ρ q (DGN A F q (γ t) (GN A F q (γ t)))) (a := 0) (b := T)
    (fun x hx => hasDerivWithinAt_hmS (hG.deriv x hx) ρ q)
    (fun x hx => hasDerivWithinAt_hmS (hG.deriv2 hA hF x hx) ρ q)
    (fun x hx y hy => by rw [← hmS_sub]; exact hMC N T γ hG x hx y hy) ht hτ.le htτ
  -- the averaging estimate in `H^{ρ+1}`
  have havg := HermiteLip.midpoint_avg_lip (z := fun t => hmS (ρ + 1) q (γ t))
    (z' := fun t => hmS (ρ + 1) q (GN A F q (γ t))) (a := 0) (b := T)
    (fun x hx => hasDerivWithinAt_hmS (hG.deriv x hx) (ρ + 1) q)
    (fun x hx y hy => by rw [← hmS_sub]; exact (hMB N T γ hG).2 x hx y hy) ht hτ.le htτ
  have hτ0 : τ ≠ 0 := hτ.ne'
  have e : τ⁻¹ • (γ (t + τ) - γ t) - GN A F q (SpectralGalerkin.mid (γ t) (γ (t + τ))) =
      τ⁻¹ • (γ (t + τ) - γ t - τ • GN A F q (γ (t + τ / 2))) +
        (GN A F q (γ (t + τ / 2)) - GN A F q (SpectralGalerkin.mid (γ t) (γ (t + τ)))) := by
    rw [smul_sub (τ⁻¹) (γ (t + τ) - γ t), smul_smul, inv_mul_cancel₀ hτ0, one_smul]; abel
  rw [e, hmS_add, hmS_smul]
  have h1 : ‖τ⁻¹ • hmS ρ q (γ (t + τ) - γ t - τ • GN A F q (γ (t + τ / 2)))‖ ≤
      7 * MC / 24 * τ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hτ, hmS_sub, hmS_sub, hmS_smul]
    calc τ⁻¹ * ‖hmS ρ q (γ (t + τ)) - hmS ρ q (γ t) - τ • hmS ρ q (GN A F q (γ (t + τ / 2)))‖
        ≤ τ⁻¹ * (7 * MC * τ ^ 3 / 24) := mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 7 * MC / 24 * τ ^ 2 := by field_simp
  have hmidR : ‖hmS (ρ + 1) q (SpectralGalerkin.mid (γ t) (γ (t + τ)))‖ ≤ R :=
    (norm_hmS_le (by omega) _).trans (norm_mid_le (hG.bound t ht0) (hG.bound _ ht1))
  have h2 := hL q N (γ (t + τ / 2)) (SpectralGalerkin.mid (γ t) (γ (t + τ)))
    (hG.ball (by omega) _ htm) hmidR
  have h3 : ‖hmS (ρ + 1) q (γ (t + τ / 2) - SpectralGalerkin.mid (γ t) (γ (t + τ)))‖ ≤
      3 * MB * τ ^ 2 / 8 := by
    rw [hmS_sub, hmS_mid, norm_sub_rev]
    unfold SpectralGalerkin.mid
    exact havg
  calc ‖τ⁻¹ • hmS ρ q (γ (t + τ) - γ t - τ • GN A F q (γ (t + τ / 2))) +
        hmS ρ q (GN A F q (γ (t + τ / 2)) - GN A F q (SpectralGalerkin.mid (γ t) (γ (t + τ))))‖
      ≤ 7 * MC / 24 * τ ^ 2 + L * (3 * MB * τ ^ 2 / 8) :=
        (norm_add_le _ _).trans (add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hL0)))
    _ = (7 * MC / 24 + L * (3 * MB / 8)) * τ ^ 2 := by ring

/-! ### The time rate of the midpoint scheme -/

theorem cast_succ_mul (j : ℕ) (τ : ℝ) : ((j + 1 : ℕ) : ℝ) * τ = (j : ℝ) * τ + τ := by
  push_cast; ring

set_option maxHeartbeats 1000000 in
/-- **The `O(τ²)` time rate of the midpoint scheme against a Galerkin trajectory**
(`eq:generated-time-rate`, first half): for `m ≥ 1`, `m_s > d/2`, `m_s + m + 1 ≤ q`, `m + 3 ≤ q`,
`2m_s ≤ m + 1` and every radius `R` there is `K` such that for every horizon `T` there is `C` with:
for every cutoff `N`, every step `0 < τ` with `τK ≤ 1`, every Galerkin trajectory `U_N` on `[0, T]`
and every midpoint recursion `U^j` in the `H^q` ball of radius `R`,
`‖U^j - U_N(jτ)‖_{H^m} ≤ C (‖U^0 - U_N(0)‖_{H^m} + τ²)` for all `jτ ≤ T`. -/
theorem midpoint_time_rate {ms m q : ℕ} (hms : (d : ℝ) / 2 < ms) (hm1 : 1 ≤ m)
    (hmq : ms + m + 1 ≤ q) (hm3 : m + 3 ≤ q) (hm2 : 2 * ms ≤ m + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * K ≤ 1 → ∀ (γ : ℝ → GS d n N) (U : ℕ → GS d n N),
      GalCurve A F q T R γ → (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖U j‖ ≤ R) →
      (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T →
        U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) →
      ∀ j : ℕ, (j : ℝ) * τ ≤ T →
        ‖hmS m q (U j - γ (j * τ))‖ ≤ C * (‖hmS m q (U 0 - γ 0)‖ + τ ^ 2) := by
  obtain ⟨K, hK0, hcaus⟩ := KatoCausal.midpoint_causal_Hm (d := d) (n := n) hA hsym hF hms hm1
    hmq hR
  obtain ⟨Cr, hCr0, hres⟩ := residual_bound (d := d) (n := n) hms hm2 hm3 hA hF hR
  refine ⟨K, hK0, fun T hT => ⟨Real.exp (2 * K * T) * (1 + 2 * T * Cr), by positivity,
    fun N τ hτ hτK γ U hG hU hrec j hj => ?_⟩⟩
  set V : ℕ → GS d n N := fun i => γ ((i : ℝ) * τ) with hV
  set r : ℕ → GS d n N := fun i => τ⁻¹ • (V (i + 1) - V i) -
    GN A F q (SpectralGalerkin.mid (V i) (V (i + 1))) with hr
  have hiT : ∀ i ≤ j, (i : ℝ) * τ ≤ T := fun i hi =>
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hτ.le).trans hj
  have hUR : ∀ i ≤ j, ‖U i‖ ≤ R := fun i hi => hU i (hiT i hi)
  have hVR : ∀ i ≤ j, ‖V i‖ ≤ R := fun i hi =>
    hG.bound _ ⟨by positivity, hiT i hi⟩
  have hUrec : ∀ i < j, U (i + 1) = U i + τ • GN A F q (SpectralGalerkin.mid (U i) (U (i + 1))) :=
    fun i hi => hrec i (by have := hiT (i + 1) hi; push_cast at this; exact this)
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hVrec : ∀ i < j, V (i + 1) = V i + τ • (GN A F q (SpectralGalerkin.mid (V i) (V (i + 1))) +
      r i) := fun i _ => by
    simp only [hr]
    rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hτ0, one_smul, add_sub_cancel]
  have hc := hcaus N τ hτ.le hτK U V r j hUR hVR hUrec hVrec
  have hri : ∀ i < j, ‖hmS m q (r i)‖ ≤ Cr * τ ^ 2 := fun i hi => by
    have h1 := hres N T γ hG ((i : ℝ) * τ) τ (by positivity) hτ
      (by rw [← cast_succ_mul]; exact hiT (i + 1) hi)
    simp only [hr, hV]
    rw [cast_succ_mul]
    exact h1
  have hsum : ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖ ≤ j * (Cr * τ ^ 2) := by
    have := Finset.sum_le_sum fun i (hi : i ∈ Finset.range j) => hri i (Finset.mem_range.mp hi)
    simpa using this
  have hV0 : V 0 = γ 0 := by simp [hV]
  rw [hV0] at hc
  have hexp : Real.exp (2 * K * (j * τ)) ≤ Real.exp (2 * K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hj (by positivity))
  have h2 : 2 * τ * ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖ ≤ 2 * T * Cr * τ ^ 2 := by
    calc 2 * τ * ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖ ≤ 2 * τ * (j * (Cr * τ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * ((j : ℝ) * τ) * Cr * τ ^ 2 := by ring
      _ ≤ 2 * T * Cr * τ ^ 2 := by gcongr
  have hδ' : ‖hmS m q (U 0) - hmS m q (γ 0)‖ = ‖hmS m q (U 0 - γ 0)‖ := by rw [hmS_sub]
  rw [hδ'] at hc
  have hδ0 : 0 ≤ ‖hmS m q (U 0 - γ 0)‖ := norm_nonneg _
  have hs0 : 0 ≤ 2 * τ * ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖ :=
    mul_nonneg (mul_nonneg zero_le_two hτ.le) (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have k1 : ‖hmS m q (U 0 - γ 0)‖ + 2 * τ * ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖ ≤
      (1 + 2 * T * Cr) * (‖hmS m q (U 0 - γ 0)‖ + τ ^ 2) := by
    have h3 : 0 ≤ 2 * T * Cr * ‖hmS m q (U 0 - γ 0)‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hT) hCr0) hδ0
    have h4 : (1 + 2 * T * Cr) * (‖hmS m q (U 0 - γ 0)‖ + τ ^ 2) = ‖hmS m q (U 0 - γ 0)‖ +
        τ ^ 2 + 2 * T * Cr * ‖hmS m q (U 0 - γ 0)‖ + 2 * T * Cr * τ ^ 2 := by ring
    have h5 := sq_nonneg τ
    linarith
  rw [hmS_sub]
  calc ‖hmS m q (U j) - hmS m q (γ (j * τ))‖
      ≤ Real.exp (2 * K * (j * τ)) * (‖hmS m q (U 0 - γ 0)‖ +
          2 * τ * ∑ i ∈ Finset.range j, ‖hmS m q (r i)‖) := hc
    _ ≤ Real.exp (2 * K * T) * ((1 + 2 * T * Cr) * (‖hmS m q (U 0 - γ 0)‖ + τ ^ 2)) :=
        mul_le_mul hexp k1 (add_nonneg hδ0 hs0) (Real.exp_pos _).le
    _ = Real.exp (2 * K * T) * (1 + 2 * T * Cr) * (‖hmS m q (U 0 - γ 0)‖ + τ ^ 2) := by ring

/-! ### The Hermite readout of the midpoint record -/

theorem hmS_hermite (ρ q : ℕ) {N : ℕ} (τ : ℝ) (a b c e : GS d n N) (θ : ℝ) :
    hmS ρ q (SpectralGalerkin.hermite τ a b c e θ) =
      SpectralGalerkin.hermite τ (hmS ρ q a) (hmS ρ q b) (hmS ρ q c) (hmS ρ q e) θ := by
  simp only [SpectralGalerkin.hermite, hmS_add, hmS_smul]

theorem hmS_hermiteD (ρ q : ℕ) {N : ℕ} (τ : ℝ) (a b c e : GS d n N) (θ : ℝ) :
    hmS ρ q (SpectralGalerkin.hermiteD τ a b c e θ) =
      SpectralGalerkin.hermiteD τ (hmS ρ q a) (hmS ρ q b) (hmS ρ q c) (hmS ρ q e) θ := by
  simp only [SpectralGalerkin.hermiteD, hmS_add, hmS_smul]

theorem hmS_hermiteDD (ρ q : ℕ) {N : ℕ} (τ : ℝ) (a b c e : GS d n N) (θ : ℝ) :
    hmS ρ q (SpectralGalerkin.hermiteDD τ a b c e θ) =
      SpectralGalerkin.hermiteDD τ (hmS ρ q a) (hmS ρ q b) (hmS ρ q c) (hmS ρ q e) θ := by
  simp only [SpectralGalerkin.hermiteDD, hmS_add, hmS_smul]

set_option maxHeartbeats 4000000 in
/-- **The Hermite readout of the midpoint record against the semidiscrete solution**
(`eq:generated-Hermite`, semidiscrete part): for `ρ ≥ 1`, `2m_s ≤ ρ + 1`, `m_s + ρ + 2 ≤ q`,
`ρ + 4 ≤ q` and every radius `R` there is `K` such that for every horizon `T` there is `C` with:
for every cutoff `N`, step `0 < τ` with `τK ≤ 1`, Galerkin trajectory `U_N` and midpoint
recursion `U^j` in the `H^q` ball of radius `R`, on every cell `[jτ, (j+1)τ] ⊆ [0, T]` the cubic
Hermite readout `z(θ) = hermite(U^j, U^{j+1}, G_N(U^j), G_N(U^{j+1}); θ)` satisfies, with
`δ₀ = ‖U^0 - U_N(0)‖_{H^{ρ+1}}` and `t = (j + θ)τ`,
`‖z - U_N(t)‖_{H^ρ} + ‖∂_tz - U_N'(t)‖_{H^ρ} ≤ C(δ₀ + τ²)` and
`‖∂_t²z - U_N''(t)‖_{H^ρ} ≤ C(δ₀/τ + τ)` (`U_N' = G_N(U_N)`, `U_N'' = DG_N(U_N)[G_N(U_N)]`). -/
theorem hermite_semidiscrete {ms ρ q : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ1 : 1 ≤ ρ)
    (hρ : 2 * ms ≤ ρ + 1) (hmsq : ms + ρ + 2 ≤ q) (hq4 : ρ + 4 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * K ≤ 1 → ∀ (γ : ℝ → GS d n N) (U : ℕ → GS d n N),
      GalCurve A F q T R γ → (∀ j : ℕ, (j : ℝ) * τ ≤ T → ‖U j‖ ≤ R) →
      (∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T →
        U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) →
      ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ T → ∀ θ ∈ Icc (0 : ℝ) 1,
        ‖hmS ρ q (SpectralGalerkin.hermite τ (U j) (U (j + 1)) (GN A F q (U j))
            (GN A F q (U (j + 1))) θ - γ (j * τ + θ * τ))‖ ≤
          C * (‖hmS (ρ + 1) q (U 0 - γ 0)‖ + τ ^ 2) ∧
        ‖hmS ρ q (SpectralGalerkin.hermiteD τ (U j) (U (j + 1)) (GN A F q (U j))
            (GN A F q (U (j + 1))) θ - GN A F q (γ (j * τ + θ * τ)))‖ ≤
          C * (‖hmS (ρ + 1) q (U 0 - γ 0)‖ + τ ^ 2) ∧
        ‖hmS ρ q (SpectralGalerkin.hermiteDD τ (U j) (U (j + 1)) (GN A F q (U j))
            (GN A F q (U (j + 1))) θ -
              DGN A F q (γ (j * τ + θ * τ)) (GN A F q (γ (j * τ + θ * τ))))‖ ≤
          C * (‖hmS (ρ + 1) q (U 0 - γ 0)‖ / τ + τ) := by
  obtain ⟨K, hK0, hrate⟩ := midpoint_time_rate (d := d) (n := n) (m := ρ + 1) (q := q) hms
    (by omega) (by omega) (by omega) (by omega) hA hsym hF hR
  obtain ⟨L, hL0, hL⟩ := GN_lip_hm (d := d) (n := n) hms hρ hA hF hR
  obtain ⟨Cr, hCr0, hres⟩ := residual_bound (d := d) (n := n) (ρ := ρ) (q := q) hms hρ
    (by omega) hA hF hR
  obtain ⟨M₂, hM₂0, hM₂⟩ := curve_lip2 (d := d) (n := n) (ρ := ρ) (q := q) hms hρ (by omega)
    hA hF hR
  obtain ⟨M₃, hM₃0, hM₃⟩ := curve_lip3 (d := d) (n := n) (ρ := ρ) (q := q) hms hρ (by omega)
    hA hF hR
  refine ⟨K, hK0, fun T hT => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := hrate T hT
  -- the constant
  set P := L * C₁ + Cr with hP
  have hP0 : 0 ≤ P := by positivity
  set C := 2 * C₁ + T * 2 * (L * C₁) + 2 * M₂ + (3 / 2 * P + 2 * (L * C₁) + 2 * M₃) +
    (6 * P + 8 * (L * C₁) + 4 * M₃) + 1 with hC
  refine ⟨C, by positivity, fun N τ hτ hτK γ U hG hU hrec j hj θ hθ => ?_⟩
  have hτT : τ ≤ T := by
    have : (0 : ℝ) ≤ j * τ := by positivity
    nlinarith
  set t₀ := (j : ℝ) * τ with ht₀
  have ht₀0 : 0 ≤ t₀ := by positivity
  have ht₀T : t₀ + τ ≤ T := by rw [ht₀]; linarith
  have hcell : Icc t₀ (t₀ + τ) ⊆ Icc 0 T := Icc_subset_Icc ht₀0 ht₀T
  set δ := ‖hmS (ρ + 1) q (U 0 - γ 0)‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- nodal errors
  have hj0 : (j : ℝ) * τ ≤ T := by linarith
  have hj1 : ((j + 1 : ℕ) : ℝ) * τ ≤ T := by rw [cast_succ_mul]; exact ht₀T
  have e0 : ‖hmS (ρ + 1) q (U j - γ t₀)‖ ≤ C₁ * (δ + τ ^ 2) :=
    hC₁ N τ hτ hτK γ U hG hU hrec j hj0
  have e1 : ‖hmS (ρ + 1) q (U (j + 1) - γ (t₀ + τ))‖ ≤ C₁ * (δ + τ ^ 2) := by
    have := hC₁ N τ hτ hτK γ U hG hU hrec (j + 1) hj1
    rwa [cast_succ_mul] at this
  have hlow : ∀ z : GS d n N, ‖hmS ρ q z‖ ≤ ‖hmS (ρ + 1) q z‖ := fun z =>
    norm_hmS_mono (Nat.le_succ ρ) z
  -- slope errors
  have ht₀m : t₀ ∈ Icc 0 T := ⟨ht₀0, by linarith⟩
  have ht₁m : t₀ + τ ∈ Icc 0 T := ⟨by linarith, ht₀T⟩
  have hUj : ‖U j‖ ≤ R := hU j hj0
  have hUj1 : ‖U (j + 1)‖ ≤ R := hU (j + 1) hj1
  have s0 : ‖hmS ρ q (GN A F q (U j) - GN A F q (γ t₀))‖ ≤ L * (C₁ * (δ + τ ^ 2)) :=
    (hL q N _ _ ((norm_hmS_le (by omega) _).trans hUj) (hG.ball (by omega) _ ht₀m)).trans
      (mul_le_mul_of_nonneg_left e0 hL0)
  have s1 : ‖hmS ρ q (GN A F q (U (j + 1)) - GN A F q (γ (t₀ + τ)))‖ ≤
      L * (C₁ * (δ + τ ^ 2)) :=
    (hL q N _ _ ((norm_hmS_le (by omega) _).trans hUj1) (hG.ball (by omega) _ ht₁m)).trans
      (mul_le_mul_of_nonneg_left e1 hL0)
  -- the increment of the nodal error
  have hinc : ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖ ≤ τ * (P * (δ + τ ^ 2)) := by
    have hrec' := hrec j (by rw [ht₀] at ht₀T; linarith)
    have hres' := hres N T γ hG t₀ τ ht₀0 hτ ht₀T
    have hτ0 : τ ≠ 0 := hτ.ne'
    have e : (U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀) =
        τ • ((GN A F q (SpectralGalerkin.mid (U j) (U (j + 1))) -
          GN A F q (SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ)))) -
          (τ⁻¹ • (γ (t₀ + τ) - γ t₀) - GN A F q (SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ))))) := by
      rw [smul_sub, smul_sub, smul_sub, smul_smul, mul_inv_cancel₀ hτ0, one_smul]
      conv_lhs => rw [hrec']
      abel
    rw [e, hmS_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, hmS_sub]
    refine mul_le_mul_of_nonneg_left ?_ hτ.le
    refine (norm_sub_le _ _).trans ?_
    have hm1 : ‖hmS (ρ + 1) q (SpectralGalerkin.mid (U j) (U (j + 1)))‖ ≤ R :=
      (norm_hmS_le (by omega) _).trans (norm_mid_le hUj hUj1)
    have hm2 : ‖hmS (ρ + 1) q (SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ)))‖ ≤ R :=
      (norm_hmS_le (by omega) _).trans (norm_mid_le (hG.bound _ ht₀m) (hG.bound _ ht₁m))
    have hmid : ‖hmS (ρ + 1) q (SpectralGalerkin.mid (U j) (U (j + 1)) -
        SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ)))‖ ≤ C₁ * (δ + τ ^ 2) := by
      rw [hmS_sub, hmS_mid, hmS_mid]
      unfold SpectralGalerkin.mid
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have e2 : hmS (ρ + 1) q (U j) + hmS (ρ + 1) q (U (j + 1)) -
          (hmS (ρ + 1) q (γ t₀) + hmS (ρ + 1) q (γ (t₀ + τ))) =
          hmS (ρ + 1) q (U j - γ t₀) + hmS (ρ + 1) q (U (j + 1) - γ (t₀ + τ)) := by
        rw [hmS_sub, hmS_sub]; abel
      rw [e2]
      have := norm_add_le (hmS (ρ + 1) q (U j - γ t₀)) (hmS (ρ + 1) q (U (j + 1) - γ (t₀ + τ)))
      linarith
    have k1 := (hL q N _ _ hm1 hm2).trans (mul_le_mul_of_nonneg_left hmid hL0)
    calc ‖hmS ρ q (GN A F q (SpectralGalerkin.mid (U j) (U (j + 1))) -
          GN A F q (SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ))))‖ +
        ‖hmS ρ q (τ⁻¹ • (γ (t₀ + τ) - γ t₀) -
          GN A F q (SpectralGalerkin.mid (γ t₀) (γ (t₀ + τ))))‖
        ≤ L * (C₁ * (δ + τ ^ 2)) + Cr * τ ^ 2 := add_le_add k1 hres'
      _ ≤ P * (δ + τ ^ 2) := by rw [hP]; nlinarith [mul_nonneg hCr0 hδ0]
  -- the Hermite error estimate in `H^ρ`
  have herr := HermiteLip.hermite_error_lip (F := GS d n N) (θ := θ)
    (z := fun t => hmS ρ q (γ t)) (z' := fun t => hmS ρ q (GN A F q (γ t)))
    (z'' := fun t => hmS ρ q (DGN A F q (γ t) (GN A F q (γ t)))) (t₀ := t₀) (τ := τ)
    (M₂ := M₂) (M₃ := M₃) hτ hθ
    (fun x hx => (hasDerivWithinAt_hmS (hG.deriv x (hcell hx)) ρ q).mono hcell)
    (fun x hx => (hasDerivWithinAt_hmS (hG.deriv2 hA hF x (hcell hx)) ρ q).mono hcell)
    (fun x hx y hy => by rw [← hmS_sub]; exact (hM₂ N T γ hG).2 x (hcell hx) y (hcell hy))
    (fun x hx y hy => by rw [← hmS_sub]; exact hM₃ N T γ hG x (hcell hx) y (hcell hy))
    (hmS ρ q (U j)) (hmS ρ q (U (j + 1))) (hmS ρ q (GN A F q (U j)))
    (hmS ρ q (GN A F q (U (j + 1))))
  obtain ⟨h1, h2, h3⟩ := herr
  simp only [← hmS_sub] at h1 h2 h3
  rw [← hmS_hermite, ← hmS_sub] at h1
  rw [← hmS_hermiteD, ← hmS_sub] at h2
  rw [← hmS_hermiteDD, ← hmS_sub] at h3
  have hθτ : t₀ + θ * τ = (j : ℝ) * τ + θ * τ := by rw [ht₀]
  rw [hθτ] at h1 h2 h3
  have e0' := (hlow _).trans e0
  have e1' := (hlow _).trans e1
  have hDτ : 0 ≤ δ + τ ^ 2 := by positivity
  set D := δ + τ ^ 2 with hD
  have hτ2D : τ ^ 2 ≤ D := by rw [hD]; linarith
  have hC1 : 2 * C₁ + T * 2 * (L * C₁) + 2 * M₂ ≤ C := by
    rw [hC]
    have : 0 ≤ 3 / 2 * P + 2 * (L * C₁) + 2 * M₃ := by positivity
    have : 0 ≤ 6 * P + 8 * (L * C₁) + 4 * M₃ := by positivity
    linarith
  have hC2 : 3 / 2 * P + 2 * (L * C₁) + 2 * M₃ ≤ C := by
    rw [hC]
    have : 0 ≤ 2 * C₁ + T * 2 * (L * C₁) + 2 * M₂ := by positivity
    have : 0 ≤ 6 * P + 8 * (L * C₁) + 4 * M₃ := by positivity
    linarith
  have hC3 : 6 * P + 8 * (L * C₁) + 4 * M₃ ≤ C := by
    rw [hC]
    have : 0 ≤ 2 * C₁ + T * 2 * (L * C₁) + 2 * M₂ := by positivity
    have : 0 ≤ 3 / 2 * P + 2 * (L * C₁) + 2 * M₃ := by positivity
    linarith
  have hss := add_le_add s0 s1
  have hinc' : τ⁻¹ * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖ ≤ P * D :=
    (inv_mul_le_iff₀ hτ).2 hinc
  refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
  · have k1 : τ * (‖hmS ρ q (GN A F q (U j) - GN A F q (γ t₀))‖ +
        ‖hmS ρ q (GN A F q (U (j + 1)) - GN A F q (γ (t₀ + τ)))‖) ≤
        T * (L * (C₁ * D) + L * (C₁ * D)) :=
      mul_le_mul hτT hss (by positivity) hT
    have k2 : 2 * M₂ * τ ^ 2 ≤ 2 * M₂ * D := mul_le_mul_of_nonneg_left hτ2D (by positivity)
    have k3 : (2 * C₁ + T * 2 * (L * C₁) + 2 * M₂) * D ≤ C * D :=
      mul_le_mul_of_nonneg_right hC1 (by positivity)
    have k4 : C₁ * D + C₁ * D + T * (L * (C₁ * D) + L * (C₁ * D)) + 2 * M₂ * D =
        (2 * C₁ + T * 2 * (L * C₁) + 2 * M₂) * D := by ring
    linarith [e0', e1']
  · have k2 : 2 * M₃ * τ ^ 2 ≤ 2 * M₃ * D := mul_le_mul_of_nonneg_left hτ2D (by positivity)
    have k3 : (3 / 2 * P + 2 * (L * C₁) + 2 * M₃) * D ≤ C * D :=
      mul_le_mul_of_nonneg_right hC2 (by positivity)
    have k4 : 3 / 2 * τ⁻¹ * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖ =
        3 / 2 * (τ⁻¹ * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖) := by ring
    have k5 : 3 / 2 * (P * D) + (L * (C₁ * D) + L * (C₁ * D)) + 2 * M₃ * D =
        (3 / 2 * P + 2 * (L * C₁) + 2 * M₃) * D := by ring
    linarith
  · have hX : τ⁻¹ * D = δ / τ + τ := by rw [hD]; field_simp
    have hX0 : 0 ≤ δ / τ + τ := by positivity
    have hτi : 0 ≤ τ⁻¹ := (inv_pos.2 hτ).le
    have k1 : 6 * τ⁻¹ ^ 2 * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖ ≤
        6 * P * (δ / τ + τ) := by
      have := mul_le_mul_of_nonneg_left hinc' hτi
      calc 6 * τ⁻¹ ^ 2 * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖ =
            6 * (τ⁻¹ * (τ⁻¹ * ‖hmS ρ q ((U (j + 1) - γ (t₀ + τ)) - (U j - γ t₀))‖)) := by ring
        _ ≤ 6 * (τ⁻¹ * (P * D)) := by linarith
        _ = 6 * P * (τ⁻¹ * D) := by ring
        _ = 6 * P * (δ / τ + τ) := by rw [hX]
    have k2 : 4 * τ⁻¹ * (‖hmS ρ q (GN A F q (U j) - GN A F q (γ t₀))‖ +
        ‖hmS ρ q (GN A F q (U (j + 1)) - GN A F q (γ (t₀ + τ)))‖) ≤
        8 * (L * C₁) * (δ / τ + τ) := by
      have := mul_le_mul_of_nonneg_left hss hτi
      calc 4 * τ⁻¹ * (‖hmS ρ q (GN A F q (U j) - GN A F q (γ t₀))‖ +
            ‖hmS ρ q (GN A F q (U (j + 1)) - GN A F q (γ (t₀ + τ)))‖) ≤
            4 * (τ⁻¹ * (L * (C₁ * D) + L * (C₁ * D))) := by linarith
        _ = 8 * (L * C₁) * (τ⁻¹ * D) := by ring
        _ = 8 * (L * C₁) * (δ / τ + τ) := by rw [hX]
    have k3 : 4 * M₃ * τ ≤ 4 * M₃ * (δ / τ + τ) := by
      have : τ ≤ δ / τ + τ := by have := div_nonneg hδ0 hτ.le; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have k4 : (6 * P + 8 * (L * C₁) + 4 * M₃) * (δ / τ + τ) ≤ C * (δ / τ + τ) :=
      mul_le_mul_of_nonneg_right hC3 hX0
    have k5 : 6 * P * (δ / τ + τ) + 8 * (L * C₁) * (δ / τ + τ) + 4 * M₃ * (δ / τ + τ) =
        (6 * P + 8 * (L * C₁) + 4 * M₃) * (δ / τ + τ) := by ring
    linarith

end RenewalGeometry.KatoTimeRate
