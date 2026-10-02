/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLimitRegularity
import RenewalGeometry.Gravity.OpenWriterLawJetComparison

/-!
# The complete reduced residual of the interpolated writer state is `O(h)` in `H^{s-2}`
  (`lem:supp-open-reduced-consistency`, undifferentiated clause; `eq:supp-open-reduced-residual`;
  emergent-spacetime manuscript)

For the interpolated metric `g_h = η + 𝓘_h q`, the reduced residual
`r_h = G(g_h) - 𝓗(g_h, c(g_h))` (`eq:supp-open-reduced-residual`; `reducedEinstein`) is the
trace reversal of half the harmonic normal row (`eq:main-harmonic-normal-row`):

* `traceRev_traceRev` — trace reversal is an involution in dimension four;
* `reducedEinstein_eq_traceRev_normalRow` — pointwise, at every symmetric nondegenerate metric
  2-jet, `Ĝ_{ab} = (ρ/2)_{ab} - ½ g_{ab} g^{cd} (ρ/2)_{cd}` with `ρ` the normal row (the "bounded
  analytic pointwise trace-reversal map" of the manuscript);
* `reduced_residual_of_rows` — the multiplier step: on the small chart, `H^{s-2}` bounds `M` on the
  ten normal-row components of an interpolant jet give `‖Ĝ_{ab}‖_{H^{s-2}} ≤ (1/2 + 4K) M`;
* `interp_reduced_residual_small_law` — the same `O(h)` bound for the `B`-writer
  (`eq:supp-law-family`), uniformly in marks `‖B‖_op ≤ b ≤ 1`: the extra row
  `a(g_h) 𝓘_h(-a⁻¹ h² B Λ_h² q)` is `O(h b ‖X‖)` by `Fnorm_lawForce_mesh`;
* `interp_reduced_residual_small` — **the undifferentiated half of
  `eq:supp-open-reduced-rate`** (central writer): for `s ≥ 5`, with mesh-independent `δ, C`, every symmetric
  record `X = (q, v)` with `‖X‖_{X^s_h} ≤ δ` has, for the interpolant jet
  `(𝓘_h q, 𝓘_h v, 𝓘_h V_{0,h}(q, v), ∂𝓘_h q, ∂𝓘_h v, ∂²𝓘_h q)` (for an unforced writer solution
  `∂ₜ²g_h = 𝓘_h V_{0,h}`), every component of the reduced residual in `H^{s-2}` with
  `‖r_{h,ab}‖_{H^{s-2}} ≤ C h ‖X‖_{X^s_h}`.  Proof: `interp_row_small` (the normal row is
  `O(h)` in `H^{s-2}`) and the multiplier bound `coef_mul_family` for the analytic coefficients
  `g_{ab} g^{cd}` of the trace reversal.

Not covered here: the time-differentiated half `‖∂ₜr_h‖_{H^{s-3}} ≤ C h ε` of
`eq:supp-open-reduced-rate`, which needs a time-differentiated (Lipschitz) version of
`sampled_row_consistency`.
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterReducedResidual

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum HarmonicGaugePropagation HarmonicDefect
  PeriodicGridSobolev.Composition OpenWriterGridBridge RootParityConnector HarmonicWriter
  OpenWriterLimitRegularity

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Trace reversal is an involution; the reduced residual is the reversed half row -/

/-- **Trace reversal is an involution in dimension four.** -/
theorem traceRev_traceRev {n : Type*} [Fintype n] [DecidableEq n] (g gi : n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a) (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hcard : Fintype.card n = 4) (X : n → n → ℝ) (a b : n) :
    traceRev g gi (traceRev g gi X) a b = X a b := by
  have h := trG_traceRev g gi hgi hinv hcard X
  have e : traceRev g gi (traceRev g gi X) a b =
      traceRev g gi X a b - (1 / 2) * g a b * trG gi (traceRev g gi X) := rfl
  rw [e, h]
  unfold traceRev
  ring

theorem minkowski_add_symm {q : MetricRec} (hq : ∀ μ ν, q μ ν = q ν μ) (μ ν : Fin 4) :
    (minkowski + q) μ ν = (minkowski + q) ν μ := by
  simp only [Pi.add_apply, hq μ ν, C3Field.minkowski_symm μ ν]

/-- **The reduced residual is the trace reversal of half the normal row**:
`Ĝ_{ab} = G_{ab} - 𝓗_{ab} = traceRev(ρ/2)_{ab}` at every symmetric nondegenerate 2-jet. -/
theorem reducedEinstein_eq_traceRev_normalRow (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (hq : ∀ μ ν, q μ ν = q ν μ)
    (hdet : (Matrix.of (minkowski + q)).det ≠ 0)
    (hw : ∀ μ ν, w μ ν = w ν μ) (hvd : ∀ i μ ν, vd i μ ν = vd i ν μ)
    (hqdd : ∀ i j μ ν, qdd i j μ ν = qdd i j ν μ) (hqdd' : ∀ i j, qdd i j = qdd j i) (a b : Fin 4) :
    reducedEinstein (minkowski + q) (recInv (minkowski + q)) (metricJet (v, qd)) (ddArr w vd qdd)
      a b = traceRev (minkowski + q) (recInv (minkowski + q))
        (fun c d => normalRow q v w qd vd qdd c d / 2) a b := by
  have hgi := recInv_symm (minkowski_add_symm hq)
  have hinv := recInv_hinv hdet
  set g := minkowski + q
  set gi := recInv g
  set dg := metricJet (v, qd)
  set ddg := ddArr w vd qdd
  -- `traceRev Ĝ = R - ∇_(C) = ρ/2`
  have hrev : ∀ c d, traceRev g gi (fun a b => reducedEinstein g gi dg ddg a b) c d =
      normalRow q v w qd vd qdd c d / 2 := by
    intro c d
    have h1 := harmonic_residual_trace_reversal g gi dg ddg hgi hinv (by simp) (fun _ _ => 0) 0 0 c d
    simp only [zero_mul, add_zero, sub_zero] at h1
    have h2 : traceRev g gi (fun a b => HarmonicDefect.einstein g gi dg ddg a b) c d = HarmonicDefect.ricci gi dg ddg c d := by
      have htr : trG gi (fun a b => HarmonicDefect.einstein g gi dg ddg a b) = -trG gi (HarmonicDefect.ricci gi dg ddg) := by
        have e : (fun a b => HarmonicDefect.einstein g gi dg ddg a b) = fun a b => 1 * HarmonicDefect.ricci gi dg ddg a b +
            (-(1 / 2) * trG gi (HarmonicDefect.ricci gi dg ddg)) * g a b + 0 * g a b := by
          funext a b; unfold HarmonicDefect.einstein; ring
        rw [e, trG_comb, trG_metric g gi hgi hinv]
        simp; ring
      unfold traceRev
      rw [htr]
      unfold HarmonicDefect.einstein
      ring
    have h3 := normalRow_eq q v w qd vd qdd hq hdet hw hvd hqdd hqdd' c d
    rw [h1, h2, h3]
    ring
  have hfun : (fun c d => normalRow q v w qd vd qdd c d / 2) =
      traceRev g gi (fun a b => reducedEinstein g gi dg ddg a b) := by
    funext c d; rw [hrev]
  rw [hfun, traceRev_traceRev g gi hgi hinv (by simp)]

/-- The explicit form of the trace reversal: `X^tr_{ab} = X_{ab} - ½ g_{ab} Σ_{cd} g^{cd} X_{cd}`. -/
theorem traceRev_apply' {n : Type*} [Fintype n] (g gi X : n → n → ℝ) (a b : n) :
    traceRev g gi X a b = X a b - (1 / 2) * ∑ c, ∑ d, (g a b * gi c d) * X c d := by
  unfold traceRev trG
  rw [mul_sum]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun d _ => by ring

/-! ### The interpolant jet -/

variable {N : ℕ} [NeZero N]

theorem interpDD_comm (u : Grid N → MetricRec) (i j : Fin 3) : interpDD u i j = interpDD u j i := by
  simp only [interpDD, specD_comm i j]

/-- The analytic coefficients `g_{ab} g^{cd}` of the trace reversal, `g = η + Q`. -/
def trCoef (k : Fin 4 × Fin 4 × Fin 4 × Fin 4) (g : MetricRec) : ℝ :=
  g k.1 k.2.1 * recInv g k.2.2.1 k.2.2.2

theorem analyticAt_trCoef (k : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    AnalyticAt ℝ (trCoef k) minkowski := by
  have h1 : AnalyticAt ℝ (fun g : MetricRec => g k.1 k.2.1) minkowski := by fun_prop
  have h2 : AnalyticAt ℝ (fun g : MetricRec => recInv g k.2.2.1 k.2.2.2) minkowski :=
    analyticAt_inv_entry minkowski det_minkowski_ne _ _
  exact h1.mul h2

/-- The upper index pair `(min c d, max c d)`. -/
def upperOfPair (c d : Fin 4) : Upper := ⟨(min c d, max c d), min_le_max⟩

theorem upperOfPair_rowF {Q V W : C(T3, MetricRec)} {Qd Vd : Fin 3 → C(T3, MetricRec)}
    {Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)}
    (hsymm : ∀ y c d, normalRow (Q y) (V y) (W y) (fun i => Qd i y) (fun i => Vd i y)
      (fun i j => Qdd i j y) c d = normalRow (Q y) (V y) (W y) (fun i => Qd i y)
      (fun i => Vd i y) (fun i j => Qdd i j y) d c) (c d : Fin 4) :
    rowF Q V W Qd Vd Qdd (upperOfPair c d).1.1 (upperOfPair c d).1.2 = rowF Q V W Qd Vd Qdd c d := by
  funext y
  simp only [upperOfPair, rowF]
  rcases le_total c d with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, hsymm y d c]

/-- **Reduced residual from the normal row** (the trace-reversal multiplier step).  For `s ≥ 5`
there are `δ > 0`, `K`, independent of the mesh, such that for every symmetric record `(q, v)`
with `‖(q, v)‖_{X^s_h} ≤ δ` and every symmetric acceleration array `w`, the metric `η + 𝓘_h q` is
nondegenerate, and whenever every upper component of the continuum normal row of the interpolant
jet `(𝓘_h q, 𝓘_h v, 𝓘_h w, ∂𝓘_h q, ∂𝓘_h v, ∂²𝓘_h q)` lies in `H^{s-2}` with norm `≤ M`, every
component of the reduced residual `G - 𝓗` of that jet lies in `H^{s-2}` with norm
`≤ (1/2 + 4K) M`. -/
theorem reduced_residual_of_rows (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (q v w : Grid N → MetricRec), IsSymRec q →
      IsSymRec v → IsSymRec w → Xnorm s q v ≤ δ →
      (∀ y, (Matrix.of (minkowski + interpRec q y)).det ≠ 0) ∧
      ∀ M : ℝ, (∀ κ : Upper, ∃ R : CT, ⇑R = rowF (interpRec q) (interpRec v) (interpRec w)
          (interpD q) (interpD v) (interpDD q) κ.1.1 κ.1.2 ∧ MemH (s - 2) ⇑R ∧
          sn (s - 2) ⇑R ≤ M) →
      ∀ a b : Fin 4, ∃ R : CT,
        (∀ y, R y = ((reducedEinstein (minkowski + interpRec q y)
            (recInv (minkowski + interpRec q y))
            (metricJet (interpRec v y, fun i => interpD q i y))
            (ddArr (interpRec w y) (fun i => interpD v i y) (fun i j => interpDD q i j y))
            a b : ℝ) : ℂ)) ∧
        MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ (1 / 2 + 4 * K) * M := by
  obtain ⟨δm, hδm, K, hK, hmul⟩ := coef_mul_family (s - 2) (by omega) trCoef analyticAt_trCoef
  obtain ⟨r₁, hr₁, hinv⟩ := exists_inv_chart
  set Ct : ℝ := 16 * Real.sqrt (pc (s - 2))
  have hCt : 0 ≤ Ct := by positivity
  set B : ℝ := 1 + ∑ j, ‖bM j‖
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set L : ℝ := B * Real.sqrt cEmb * Ct
  have hL : 0 ≤ L := by positivity
  set δ : ℝ := min (δm / (Ct + 1)) (r₁ / (2 * (L + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, K, hK, fun N _ q v w hq hv hw hX => ?_⟩
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  set Q := interpRec q
  have hQm : ∀ k, MemH (s - 2) ⇑(ccoord bM Q k) := fun k => (memH_interpRec _ _ k).1
  have hQs : ccoordSum (s - 2) bM Q ≤ Ct * X := ccoordSum_interpRec_le (s - 2) s hq v (by omega)
  -- nondegeneracy
  have hdet : ∀ y, (Matrix.of (minkowski + Q y)).det ≠ 0 := by
    intro y
    have h1 := norm_le_ccoordSum (s - 2) (by omega) bM norm_bM_le Q hQm y
    have h2 : X ≤ r₁ / (2 * (L + 1)) := hX.trans (min_le_right _ _)
    have h3 : B * (Real.sqrt cEmb * ccoordSum (s - 2) bM Q) ≤ L * X := by
      have := mul_le_mul_of_nonneg_left hQs (mul_nonneg hB0 (Real.sqrt_nonneg cEmb))
      simp only [L]; nlinarith
    have h4 : L * X < r₁ := by
      have hLX : L * X ≤ L * (r₁ / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h2 hL
      have : L * (r₁ / (2 * (L + 1))) < r₁ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have hsm : ‖(minkowski + Q y) - minkowski‖ < r₁ := by
      rw [add_sub_cancel_left]; linarith
    exact (hinv _ hsm).1
  refine ⟨hdet, fun M hrows a b => ?_⟩
  set W := interpRec w
  have hsymm : ∀ y c d, normalRow (Q y) (interpRec v y) (W y) (fun i => interpD q i y)
      (fun i => interpD v i y) (fun i j => interpDD q i j y) c d =
      normalRow (Q y) (interpRec v y) (W y) (fun i => interpD q i y)
      (fun i => interpD v i y) (fun i j => interpDD q i j y) d c := by
    intro y c d
    exact normalRow_symm _ _ _ _ _ _ (interpRec_symm hq y) (hdet y) (interpRec_symm hv y)
      (fun i => interpD_symm hq i y) (interpRec_symm hw y) (fun i => interpD_symm hv i y)
      (fun i j => interpDD_symm hq i j y) (fun i j => by rw [interpDD_comm]) c d
  choose Rκ hRκ hRκm hRκs using hrows
  set ρ : Fin 4 → Fin 4 → CT := fun c d => Rκ (upperOfPair c d)
  have hρ : ∀ c d, ⇑(ρ c d) = rowF Q (interpRec v) W (interpD q) (interpD v) (interpDD q) c d :=
    fun c d => (hRκ (upperOfPair c d)).trans (upperOfPair_rowF hsymm c d)
  have hρm : ∀ c d, MemH (s - 2) ⇑(ρ c d) := fun c d => hRκm _
  have hρs : ∀ c d, sn (s - 2) ⇑(ρ c d) ≤ M := fun c d => hRκs _
  -- the trace-reversal products
  have hsmall : ccoordSum (s - 2) bM Q ≤ δm := by
    have h2 : X ≤ δm / (Ct + 1) := hX.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith
  have hP := fun c d => hmul (a, b, c, d) Q hQm hsmall (ρ c d) (hρm c d)
  choose P hPy hPm hPs using hP
  set R : CT := (2⁻¹ : ℂ) • ρ a b - (4⁻¹ : ℂ) • ∑ c, ∑ d, P c d
  have hS1 : ∀ c, MemH (s - 2) ⇑(∑ d, P c d) ∧ sn (s - 2) ⇑(∑ d, P c d) ≤ ∑ d, sn (s - 2) ⇑(P c d) :=
    fun c => sn_sum_le' univ fun d => hPm c d
  have hS2 := sn_sum_le' univ fun c => (hS1 c).1
  refine ⟨R, fun y => ?_, ?_, ?_⟩
  · -- pointwise identification
    have e := reducedEinstein_eq_traceRev_normalRow (Q y) (interpRec v y) (W y)
      (fun i => interpD q i y) (fun i => interpD v i y) (fun i j => interpDD q i j y)
      (interpRec_symm hq y) (hdet y) (interpRec_symm hw y) (fun i => interpD_symm hv i y)
      (fun i j => interpDD_symm hq i j y) (fun i j => by rw [interpDD_comm]) a b
    rw [e, traceRev_apply']
    have hρy : ∀ c d, ρ c d y = ((normalRow (Q y) (interpRec v y) (W y) (fun i => interpD q i y)
        (fun i => interpD v i y) (fun i j => interpDD q i j y) c d : ℝ) : ℂ) := by
      intro c d; rw [hρ]; rfl
    simp only [R, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, smul_eq_mul, hPy, hρy, trCoef]
    push_cast
    rw [mul_sum, mul_sum]
    simp only [mul_sum]
    ring_nf
  · exact memH_sub (memH_smul _ (hρm a b)) (memH_smul _ hS2.1)
  · have h1 := sn_sub_le' (memH_smul (2⁻¹ : ℂ) (hρm a b)) (memH_smul (4⁻¹ : ℂ) hS2.1)
    rw [sn_smul, sn_smul] at h1
    have hn2 : ‖(2⁻¹ : ℂ)‖ = 1 / 2 := by rw [norm_inv]; norm_num
    have hn4 : ‖(4⁻¹ : ℂ)‖ = 1 / 4 := by rw [norm_inv]; norm_num
    rw [hn2, hn4] at h1
    have hsum : sn (s - 2) ⇑(∑ c, ∑ d, P c d) ≤ 16 * (K * M) := by
      refine hS2.2.trans ?_
      calc ∑ c, sn (s - 2) ⇑(∑ d, P c d) ≤ ∑ c : Fin 4, ∑ d : Fin 4, K * M := by
            refine sum_le_sum fun c _ => (hS1 c).2.trans (sum_le_sum fun d _ => ?_)
            exact (hPs c d).trans (mul_le_mul_of_nonneg_left (hρs c d) hK)
        _ = 16 * (K * M) := by simp; ring
    have hab := hρs a b
    calc sn (s - 2) ⇑R ≤ 1 / 2 * sn (s - 2) ⇑(ρ a b) + 1 / 4 * sn (s - 2) ⇑(∑ c, ∑ d, P c d) := h1
      _ ≤ 1 / 2 * M + 1 / 4 * (16 * (K * M)) := by gcongr
      _ = (1 / 2 + 4 * K) * M := by ring

/-- **The reduced residual of the interpolated central writer state is `O(h)` in `H^{s-2}`** (the
undifferentiated half of `eq:supp-open-reduced-rate`, `lem:supp-open-reduced-consistency`).
For `s ≥ 5` there are `δ, C`, independent of the mesh `h = 1/N`, such that for every symmetric
record `X = (q, v)` with `‖X‖_{X^s_h} ≤ δ`, the metric `g_h = η + 𝓘_h q` is nondegenerate and
every component of the complete reduced residual `r_h = G(g_h) - 𝓗(g_h, c(g_h))` of the
interpolant jet — position `𝓘_h q`, velocity `𝓘_h v`, acceleration `𝓘_h V_{0,h}(q, v)` (the
interpolated writer acceleration; `∂ₜ²g_h` along an unforced writer solution), classical spatial
derivatives `∂𝓘_h q`, `∂𝓘_h v`, `∂²𝓘_h q` — lies in `H^{s-2}` with
`‖r_{h,ab}‖_{H^{s-2}} ≤ C h ‖X‖_{X^s_h}`. -/
theorem interp_reduced_residual_small (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → (∀ y, (Matrix.of (minkowski + interpRec q y)).det ≠ 0) ∧
      ∀ a b : Fin 4, ∃ R : CT,
        (∀ y, R y = ((reducedEinstein (minkowski + interpRec q y)
            (recInv (minkowski + interpRec q y))
            (metricJet (interpRec v y, fun i => interpD q i y))
            (ddArr (interpRec (symRec (harmonicWriterAcceleration q v)) y)
              (fun i => interpD v i y) (fun i j => interpDD q i j y)) a b : ℝ) : ℂ)) ∧
        MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨δ0, hδ0, K, hK, hcore⟩ := reduced_residual_of_rows s hs
  obtain ⟨δr, hδr, Cr, hCr, hrow⟩ := interp_row_small s hs
  refine ⟨min δ0 δr, lt_min hδ0 hδr, (1 / 2 + 4 * K) * Cr, by positivity,
    fun N _ q v hq hv hX => ?_⟩
  obtain ⟨hdet, hres⟩ := hcore N q v _ hq hv (isSymRec_symRec _) (hX.trans (min_le_left _ _))
  refine ⟨hdet, fun a b => ?_⟩
  obtain ⟨R, hR, hRm, hRs⟩ := hres (Cr * (N : ℝ)⁻¹ * Xnorm s q v)
    (fun κ => hrow N q v hq hv (hX.trans (min_le_right _ _)) κ) a b
  exact ⟨R, hR, hRm, hRs.trans (le_of_eq (by ring))⟩

theorem interpRec_add (u w : Grid N → MetricRec) :
    interpRec (u + w) = interpRec u + interpRec w := by
  ext y μ ν
  have e : cx (comp (u + w) μ ν) = cx (comp u μ ν) + cx (comp w μ ν) := by
    funext x; simp [cx, comp]
  simp only [interpRec, reField_apply, ContinuousMap.add_apply, Pi.add_apply, e,
    interp_add, Complex.add_re]

theorem symRec_add (u w : Grid N → MetricRec) : symRec (u + w) = symRec u + symRec w := rfl

/-- The normal row is affine in the acceleration slot, with slope `a(g) = -g^{00}`. -/
theorem normalRow_add_w (q v w w' : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (μ ν : Fin 4) :
    normalRow q v (w + w') qd vd qdd μ ν =
      normalRow q v w qd vd qdd μ ν + harmA (minkowski + q) * w' μ ν := by
  simp only [normalRow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smul_add]
  ring

/-- **The `B`-writer clause** of `lem:supp-open-reduced-consistency`, undifferentiated half: the
same estimate holds uniformly for the law family `eq:supp-law-family`.  For `s ≥ 5` there are
`δ, C`, independent of the mesh and of the mark, such that for every mark `B` with
`‖B‖_op ≤ b ≤ 1` and every symmetric record `X = (q, v)` with `‖X‖_{X^s_h} ≤ δ`, the reduced
residual of the interpolant jet with the `B`-writer acceleration `𝓘_h V_{B,h}(q, v)` satisfies
`‖r_{h,ab}‖_{H^{s-2}} ≤ C h ‖X‖_{X^s_h}`.  The extra residual `a(g_h) 𝓘_h(-a⁻¹ h² B Λ_h² q)` is
`O(h b ‖X‖)` in `H^{s-2}` by the `h`-gaining multiplier bound `Fnorm_lawForce_mesh`. -/
theorem interp_reduced_residual_small_law (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (β : ℝ) (B : Upper → Upper → ℝ), IsMark β B → β ≤ 1 →
      ∀ (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v →
      Xnorm s q v ≤ δ → (∀ y, (Matrix.of (minkowski + interpRec q y)).det ≠ 0) ∧
      ∀ a b : Fin 4, ∃ R : CT,
        (∀ y, R y = ((reducedEinstein (minkowski + interpRec q y)
            (recInv (minkowski + interpRec q y))
            (metricJet (interpRec v y, fun i => interpD q i y))
            (ddArr (interpRec (symRec (lawAccel B q v)) y)
              (fun i => interpD v i y) (fun i j => interpDD q i j y)) a b : ℝ) : ℂ)) ∧
        MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨δ0, hδ0, K, hK, hcore⟩ := reduced_residual_of_rows s hs
  obtain ⟨δr, hδr, Cr, hCr, hrow⟩ := interp_row_small s hs
  obtain ⟨δa, hδa, Ka, hKa, hmulA⟩ := coef_mul_family (s - 2) (by omega)
    (fun _ : Unit => harmA) (fun _ => analyticAt_harmA)
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := Fnorm_lawForce_mesh (s - 2) (by omega)
  set Ct : ℝ := 16 * Real.sqrt (pc (s - 2))
  have hCt : 0 ≤ Ct := by positivity
  set δ : ℝ := min (min δ0 δr) (min (δa / (Ct + 1)) δF)
  have hδ : 0 < δ := lt_min (lt_min hδ0 hδr) (lt_min (by positivity) hδF)
  set Cx : ℝ := Cr + Ka * (Real.sqrt (pc (s - 2)) * CF)
  refine ⟨δ, hδ, (1 / 2 + 4 * K) * Cx, by positivity,
    fun N _ b' B hB hb1 q v hq hv hX => ?_⟩
  have hb0 := hB.nonneg
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  obtain ⟨hdet, hres⟩ := hcore N q v _ hq hv (isSymRec_symRec _)
    (hX.trans ((min_le_left _ _).trans (min_le_left _ _)))
  refine ⟨hdet, fun a b => ?_⟩
  set V0 := harmonicWriterAcceleration q v
  set Fc := lawForce B q
  have hsplit : interpRec (symRec (lawAccel B q v)) =
      interpRec (symRec V0) + interpRec (symRec Fc) := by
    rw [show lawAccel B q v = V0 + Fc from rfl, symRec_add, interpRec_add]
  -- the extra rows
  have hQm : ∀ k, MemH (s - 2) ⇑(ccoord bM (interpRec q) k) := fun k => (memH_interpRec _ _ k).1
  have hQs : ccoordSum (s - 2) bM (interpRec q) ≤ δa := by
    have h1 := ccoordSum_interpRec_le (s - 2) s hq v (by omega)
    have h2 : X ≤ δa / (Ct + 1) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h2
    have : ccoordSum (s - 2) bM (interpRec q) ≤ Ct * X := h1
    nlinarith
  have hFb : Fnorm (s - 2) Fc ≤ CF * (N : ℝ)⁻¹ * b' * X := by
    have h := hF N b' B q v hB hq (by
      rw [show s - 2 + 2 = s by omega]; exact hX.trans ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [show s - 2 + 2 = s by omega] at h
  have hrowsB : ∀ κ : Upper, ∃ R : CT, ⇑R = rowF (interpRec q) (interpRec v)
      (interpRec (symRec (lawAccel B q v))) (interpD q) (interpD v) (interpDD q) κ.1.1 κ.1.2 ∧
      MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ Cx * (N : ℝ)⁻¹ * X := by
    intro κ
    obtain ⟨R0, hR0, hR0m, hR0s⟩ := hrow N q v hq hv
      (hX.trans ((min_le_left _ _).trans (min_le_right _ _))) κ
    obtain ⟨hGm, hGs⟩ := memH_interpRec (s - 2) (symRec Fc) ⟨κ.1.1, κ.1.2⟩
    rw [ccoord_bM] at hGm hGs
    obtain ⟨P, hPy, hPm, hPs⟩ := hmulA () (interpRec q) hQm hQs _ hGm
    refine ⟨R0 + P, ?_, memH_add hR0m hPm, ?_⟩
    · funext y
      rw [ContinuousMap.add_apply, hPy y, hR0, hsplit]
      simp only [rowF, ContinuousMap.add_apply, normalRow_add_w, cmp_apply]
      push_cast
      ring
    · have hc : PeriodicGridSobolev.sobNorm (s - 2) (cx (comp (symRec Fc) κ.1.1 κ.1.2)) ≤
          CF * (N : ℝ)⁻¹ * b' * X := by
        have e : comp (symRec Fc) κ.1.1 κ.1.2 = comp Fc κ.1.1 κ.1.2 := by
          funext x; exact symRec_upper Fc x κ
        rw [e]
        exact (sobNorm_le_Fnorm (s - 2) Fc κ).trans hFb
      have hPs' : sn (s - 2) ⇑P ≤ Ka * (Real.sqrt (pc (s - 2)) * (CF * (N : ℝ)⁻¹ * X)) := by
        refine hPs.trans (mul_le_mul_of_nonneg_left (hGs.trans ?_) hKa)
        refine mul_le_mul_of_nonneg_left (hc.trans ?_) (Real.sqrt_nonneg _)
        have : CF * (N : ℝ)⁻¹ * b' * X ≤ CF * (N : ℝ)⁻¹ * 1 * X := by gcongr
        linarith
      refine (sn_add_le' hR0m hPm).trans ?_
      have : sn (s - 2) ⇑R0 + sn (s - 2) ⇑P ≤
          Cr * (N : ℝ)⁻¹ * X + Ka * (Real.sqrt (pc (s - 2)) * (CF * (N : ℝ)⁻¹ * X)) :=
        add_le_add hR0s hPs'
      refine this.trans (le_of_eq ?_)
      simp only [Cx]; ring
  obtain ⟨R, hR, hRm, hRs⟩ := hres (Cx * (N : ℝ)⁻¹ * X) hrowsB a b
  exact ⟨R, hR, hRm, hRs.trans (le_of_eq (by ring))⟩

/-- Non-vacuity: the flat record lies in every chart of the theorems above. -/
example (s : ℕ) (N : ℕ) [NeZero N] :
    IsSymRec (0 : Grid N → MetricRec) ∧ Xnorm s (0 : Grid N → MetricRec) 0 = 0 :=
  ⟨fun _ _ _ => rfl, Xnorm_zero' N s⟩

end

end RenewalGeometry.OpenWriterReducedResidual
