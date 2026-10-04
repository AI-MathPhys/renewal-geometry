/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusTrigReconstruction
import RenewalGeometry.Analysis.NormedAlgebraLogBCH

/-!
# Compactness of discrete `H¹`-bounded families and link coefficients on the periodic grid

The continuum clauses of `lem:native-critical-grid` of the Einstein–SM action-closure manuscript
(`papers/einstein_sm_action_closure`, Appendix `app:native-critical-closure`), in the unit-torus
rendering of `Continuum/TorusTrigReconstruction.lean` (grid `(ℤ/N)^d`, mesh `h = 1/N`, nodal norm
`gridNorm`, forward difference `Dp`; the paper's box of side `2π` is its dilation by `2π`).

* `tendsto_inner_of_coeff` (generic): a bounded sequence in `L²(𝕋^d)` whose Fourier coefficients
  converge pointwise converges weakly (against every `g ∈ L²`) to the function with the limit
  coefficients.
* `gridNorm_shift_sub_le`: the discrete translation modulus `‖T_{μ,m}u - u‖_{2,h} ≤ m h ‖D⁺_μ u‖_{2,h}`.
* `exists_subseq_tendsto_pcLp` (**discrete Rellich**): a family bounded in the discrete `H¹` norm
  has a subsequence along which `R_h^0 u_h` converges strongly in `L²` (via
  `lem:native-discrete-KR`, `TorusPiecewiseConstantTranslation.native_discrete_KR`).
* `weak_limit_of_bounded`: along any such subsequence the limit `u` lies in `H¹`, the forward
  differences `R_h^0 D⁺_μ u_h` converge weakly in `L²` to `∂_μ u`, and the trigonometric
  reconstructions converge strongly in `L²`, stay bounded in `H¹` and their derivatives converge
  weakly in `L²` (weak `H¹` convergence).
* `native_critical_grid_compactness`: the packaged compactness clause of `lem:native-critical-grid`.
* Link coefficients (`eq:native-link-coeff`, four dimensions): `tendsto_meshSup`
  (`h ‖A_h‖_{∞,h} → 0` when `R_h^0 A_h → A` strongly in `L⁴`) and `tendsto_linkCoeff`
  (`R_h^0 B^ρ_h → ρ(A)` strongly in `L⁴`, `B^ρ_h = (e^{h ρ(A_h)} - 1)/h`), with the pointwise
  bounds `norm_linkCoeff_sub_le`, `norm_linkCoeff_le` (the exact identity
  `B^ρ = ∫₀¹ e^{thρ(A)} ρ(A) dt` is replaced by the equivalent Taylor bound
  `‖e^{X} - 1 - X‖ ≤ ‖X‖² e^{‖X‖}`).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeCriticalGrid

open TorusTrigReconstruction LatticeTorusPlancherel TorusCellEmbedding
  TorusPiecewiseConstantTranslation TorusSobolev

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Weak convergence from Fourier coefficients -/

section Weak

variable {d : ℕ}

theorem toLp_trigPoly (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ (trigPoly S c) =
      ∑ m ∈ S, c m • mFourierLp 2 m := by
  simp only [trigPoly, map_sum, map_smul]

theorem inner_toLp_trigPoly (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (H : L²(UnitAddTorus (Fin d))) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ (trigPoly S c)) H =
      ∑ m ∈ S, (starRingEnd ℂ) (c m) * mFourierCoeff H m := by
  rw [toLp_trigPoly, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_smul_left, mFourierCoeff_eq_inner']

/-- **Weak convergence from coefficients.**  If `‖F_k‖ ≤ B` and `F̂_k(m) → F̂₀(m)` for every `m`,
then `⟪g, F_k⟫ → ⟪g, F₀⟫` for every `g ∈ L²(𝕋^d)`. -/
theorem tendsto_inner_of_coeff {F : ℕ → L²(UnitAddTorus (Fin d))} {F₀ : L²(UnitAddTorus (Fin d))}
    {B : ℝ} (hB : ∀ k, ‖F k‖ ≤ B)
    (hc : ∀ m, Tendsto (fun k => mFourierCoeff (F k) m) atTop (𝓝 (mFourierCoeff F₀ m)))
    (g : L²(UnitAddTorus (Fin d))) :
    Tendsto (fun k => inner ℂ g (F k)) atTop (𝓝 (inner ℂ g F₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [← inner_sub_right]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set C := B + ‖F₀‖ + 1
  have hC : 0 < C := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := ((tendsto_order.1 (tendsto_norm_sub_trigPoly_box g)).2 (ε / (2 * C))
    (by positivity)).exists
  set P := ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box R) (mFourierCoeff g))
  -- the finitely many low modes
  have hlow : Tendsto (fun k => inner ℂ P (F k - F₀)) atTop (𝓝 0) := by
    simp only [P, inner_toLp_trigPoly, mFourierCoeff_Lp_sub]
    simpa using tendsto_finset_sum (TorusSobolev.box R) fun m _ =>
      ((hc m).sub_const (mFourierCoeff F₀ m)).const_mul ((starRingEnd ℂ) (mFourierCoeff g m))
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hlow) (ε / 2) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  rw [dist_zero_right, norm_norm]
  have hsplit : inner ℂ g (F k - F₀) = inner ℂ (g - P) (F k - F₀) + inner ℂ P (F k - F₀) := by
    rw [inner_sub_left]; ring
  rw [hsplit]
  have h1 : ‖inner ℂ (g - P) (F k - F₀)‖ ≤ ε / (2 * C) * C := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul hR.le ?_ (norm_nonneg _) (by positivity))
    calc ‖F k - F₀‖ ≤ ‖F k‖ + ‖F₀‖ := norm_sub_le _ _
      _ ≤ C := by linarith [hB k]
  have h2 := hK k hk
  rw [dist_zero_right] at h2
  have e : ε / (2 * C) * C = ε / 2 := by field_simp
  calc ‖inner ℂ (g - P) (F k - F₀) + inner ℂ P (F k - F₀)‖
      ≤ ‖inner ℂ (g - P) (F k - F₀)‖ + ‖inner ℂ P (F k - F₀)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end Weak

/-! ### Discrete Rellich -/

section Rellich

variable {d N : ℕ} [NeZero N]

theorem gridNorm_smul (c : ℂ) (u : Grid d N → ℂ) : gridNorm (c • u) = ‖c‖ * gridNorm u := by
  unfold gridNorm
  have : ∑ x, ‖(c • u) x‖ ^ 2 = ‖c‖ ^ 2 * ∑ x, ‖u x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, norm_smul, mul_pow]
  rw [this, mul_left_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem shift_add_one (μ : Fin d) (m : ℕ) (u : Grid d N → ℂ) :
    TorusPiecewiseConstantTranslation.shift μ ((m + 1 : ℕ) : ℤ) u =
      TorusPiecewiseConstantTranslation.shift μ (m : ℤ)
        (TorusPiecewiseConstantTranslation.shift μ ((1 : ℕ) : ℤ) u) := by
  funext g
  simp only [TorusPiecewiseConstantTranslation.shift]
  congr 1
  rw [add_assoc, ← Pi.single_add]
  push_cast
  ring_nf

theorem Dp_eq_smul (μ : Fin d) (u : Grid d N → ℂ) :
    Dp μ u = (N : ℂ) • (TorusPiecewiseConstantTranslation.shift μ ((1 : ℕ) : ℤ) u - u) := by
  funext x
  simp [Dp_apply, TorusPiecewiseConstantTranslation.shift]

/-- **The discrete translation modulus**: `‖T_{μ,m} u - u‖_{2,h} ≤ (m/N) ‖D⁺_μ u‖_{2,h}`. -/
theorem gridNorm_shift_sub_le (μ : Fin d) (u : Grid d N → ℂ) (m : ℕ) :
    gridNorm (TorusPiecewiseConstantTranslation.shift μ (m : ℤ) u - u) ≤
      m / N * gridNorm (Dp μ u) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : gridNorm (TorusPiecewiseConstantTranslation.shift μ ((1 : ℕ) : ℤ) u - u) =
      gridNorm (Dp μ u) / N := by
    rw [Dp_eq_smul, gridNorm_smul, Complex.norm_natCast]
    field_simp
  induction m with
  | zero =>
      simp only [Nat.cast_zero, TorusPiecewiseConstantTranslation.shift_zero, sub_self,
        gridNorm_zero, zero_div, zero_mul, le_refl]
  | succ m ih =>
      have hsplit : TorusPiecewiseConstantTranslation.shift μ ((m + 1 : ℕ) : ℤ) u - u =
          TorusPiecewiseConstantTranslation.shift μ (m : ℤ)
            (TorusPiecewiseConstantTranslation.shift μ ((1 : ℕ) : ℤ) u - u) +
          (TorusPiecewiseConstantTranslation.shift μ (m : ℤ) u - u) := by
        rw [shift_add_one]
        funext g
        simp [TorusPiecewiseConstantTranslation.shift]
      rw [hsplit]
      refine (gridNorm_add_le _ _).trans ?_
      have e : gridNorm (TorusPiecewiseConstantTranslation.shift μ (m : ℤ)
          (TorusPiecewiseConstantTranslation.shift μ ((1 : ℕ) : ℤ) u - u)) =
          gridNorm (Dp μ u) / N := by
        rw [gridNorm_shift_sub_comm, h1]
      rw [e]
      have : ((m + 1 : ℕ) : ℝ) / N * gridNorm (Dp μ u) =
          gridNorm (Dp μ u) / N + m / N * gridNorm (Dp μ u) := by
        push_cast; field_simp; ring
      rw [this]
      linarith

/-- **Discrete Rellich** (first compactness clause of `lem:native-critical-grid`): a family
bounded in the discrete `H¹` norm has a subsequence along which `R_h^0 u_h` converges strongly
in `L²(𝕋^d)`. -/
theorem exists_subseq_tendsto_pcLp {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (u : ∀ k, Grid d (n k) → ℂ) {B : ℝ} (hB : ∀ k, gridNorm (u k) ≤ B)
    (hD : ∀ k μ, gridNorm (Dp μ (u k)) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L²(UnitAddTorus (Fin d)),
      Tendsto (fun k => ‖pcLp (u (φ k)) - f‖) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (gridNorm_nonneg _).trans (hB 0)
  have htb : TotallyBounded (range fun k => pcLp (u k)) := by
    refine native_discrete_KR n hn u ⟨B, hB⟩ fun ε hε => ⟨ε / (B + 1), by positivity, ?_⟩
    refine Eventually.of_forall fun k μ m _ hm => ?_
    refine (gridNorm_shift_sub_le μ (u k) m).trans ?_
    calc (m : ℝ) / (n k) * gridNorm (Dp μ (u k)) ≤ ε / (B + 1) * B :=
          mul_le_mul hm (hD k μ) (gridNorm_nonneg _) (by positivity)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hcpt : IsCompact (closure (range fun k => pcLp (u k))) :=
    htb.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨f, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq fun k => subset_closure (mem_range_self k)
  exact ⟨φ, hφ, f, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩

end Rellich

/-! ### Weak limits of forward differences and weak `H¹` compactness -/

section WeakLimits

variable {d : ℕ}

/-- `|F̂(m) - coef w m| ≤ (2π|m|₁/N) ‖w‖_{2,h}` for `F = R^0 w` on the represented range. -/
theorem norm_mFourierCoeff_pcLp_sub_coef_le {N : ℕ} [NeZero N] (w : Grid d N → ℂ)
    {m : Fin d → ℤ} (hm : ∀ i, 2 * |m i| < N) :
    ‖mFourierCoeff (pcLp w) m - coef w m‖ ≤ 2 * π * (∑ i, |(m i : ℝ)|) / N * gridNorm w := by
  rw [coef_eq, if_pos (signedRep_zcast hm), norm_sub_rev]
  have := norm_dft_sub_mFourierCoeff_le w (pcLp w) m
  rwa [sub_self, norm_zero, add_zero] at this

theorem norm_weakDeriv_sq_le {F : L²(UnitAddTorus (Fin d))} (hF : MemH 1 F) (μ : Fin d) :
    ‖weakDeriv μ F‖ ^ 2 ≤ sobSq 1 F := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (weakDeriv μ F)
  rw [← h.tsum_eq]
  unfold sobSq coeffSobSq
  simp only [Real.rpow_one, mFourierCoeff_weakDeriv hF]
  refine Summable.tsum_le_tsum (fun m => ?_)
    (by simpa only [mFourierCoeff_weakDeriv hF] using h.summable)
    (by simpa [MemH, CoeffMemH] using hF)
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_symbol_sq_le μ m) (sq_nonneg _)

theorem memH_trigLp {N : ℕ} [NeZero N] (u : Grid d N → ℂ) : MemH 1 (trigLp u) := by
  unfold MemH CoeffMemH
  simp only [Real.rpow_one, mFourierCoeff_trigLp]
  exact summable_mul_coef _ u

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **Weak limits along a strongly convergent subsequence** (second and third compactness clauses
of `lem:native-critical-grid`).  Let `‖D⁺_μ u_h‖_{2,h} ≤ B` and `R_h^0 u_h → f` strongly in
`L²(𝕋^d)`.  Then `f ∈ H¹`; for every `μ`, `R_h^0 D⁺_μ u_h ⇀ ∂_μ f` weakly in `L²`; and the
trigonometric reconstructions satisfy `𝓘_h u_h → f` strongly in `L²`, `‖𝓘_h u_h‖²_{H¹} ≤
B'² + (π/2)² d B²` (`B' = sup ‖u_h‖_{2,h}`) and `∂_μ 𝓘_h u_h ⇀ ∂_μ f` weakly in `L²`
(i.e. `𝓘_h u_h ⇀ f` weakly in `H¹`). -/
theorem weak_limit_of_bounded (hn : Tendsto n atTop atTop) {u : ∀ k, Grid d (n k) → ℂ}
    {f : L²(UnitAddTorus (Fin d))} {B : ℝ} (hB : ∀ k, gridNorm (u k) ≤ B)
    (hD : ∀ k μ, gridNorm (Dp μ (u k)) ≤ B)
    (hu : Tendsto (fun k => ‖pcLp (u k) - f‖) atTop (𝓝 0)) :
    MemH 1 f ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))), Tendsto (fun k => inner ℂ g (pcLp (Dp μ (u k))))
        atTop (𝓝 (inner ℂ g (weakDeriv μ f)))) ∧
      Tendsto (fun k => ‖trigLp (u k) - f‖) atTop (𝓝 0) ∧
      (∀ k, sobSq 1 (trigLp (u k)) ≤ gridNorm (u k) ^ 2 + (π / 2) ^ 2 * (d * B ^ 2)) ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))), Tendsto (fun k => inner ℂ g (weakDeriv μ (trigLp (u k))))
        atTop (𝓝 (inner ℂ g (weakDeriv μ f)))) := by
  have hB0 : ∀ k μ, 0 ≤ B := fun k μ => (gridNorm_nonneg _).trans (hD k μ)
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  -- coefficients of the raw forward differences
  have hcoefD : ∀ μ m, Tendsto (fun k => mFourierCoeff (pcLp (Dp μ (u k))) m) atTop
      (𝓝 (2 * π * Complex.I * m μ * mFourierCoeff f m)) := by
    intro μ m
    have h1 : Tendsto (fun k => coef (Dp μ (u k)) m) atTop
        (𝓝 (2 * π * Complex.I * m μ * mFourierCoeff f m)) := by
      simp_rw [coef_Dp]
      exact (tendsto_sym hn μ m).mul (tendsto_coef_of_tendsto_pcLp hn hu m)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    have h2 : Tendsto (fun k => 2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ) * B) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := 2 * π * (∑ i, |(m i : ℝ)|))).div_atTop hn').mul_const B
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by simpa using h2.add h1)
    filter_upwards [eventually_two_abs_lt hn m] with k hk
    calc ‖mFourierCoeff (pcLp (Dp μ (u k))) m - 2 * π * Complex.I * m μ * mFourierCoeff f m‖
        = ‖(mFourierCoeff (pcLp (Dp μ (u k))) m - coef (Dp μ (u k)) m) +
            (coef (Dp μ (u k)) m - 2 * π * Complex.I * m μ * mFourierCoeff f m)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add ((norm_mFourierCoeff_pcLp_sub_coef_le _ hk).trans
          (mul_le_mul_of_nonneg_left (hD k μ) (by positivity))) le_rfl
  -- `f ∈ H¹` by Fatou on finite sets
  have hfH : MemH 1 f := by
    unfold MemH CoeffMemH
    simp only [Real.rpow_one, TorusTrigReconstruction.sobWeight_mul_eq]
    refine (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff f).summable.add
      (summable_sum fun μ _ => ?_)
    refine summable_of_sum_le (c := B ^ 2) (fun m => sq_nonneg _) fun S => ?_
    refine le_of_tendsto (tendsto_finset_sum S fun m _ => ((hcoefD μ m).norm).pow 2)
      (Eventually.of_forall fun k => ?_)
    have hb := sum_le_hasSum S (fun m _ => sq_nonneg _)
      (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (pcLp (Dp μ (u k))))
    rw [norm_pcLp] at hb
    exact hb.trans (pow_le_pow_left₀ (gridNorm_nonneg _) (hD k μ) 2)
  have hS : ∀ k, sobSq 1 (trigLp (u k)) ≤ gridNorm (u k) ^ 2 + (π / 2) ^ 2 * (d * B ^ 2) := by
    intro k
    have e : sobSq 1 (trigLp (u k)) = sobSq 1 (trigInterp (u k)) := by
      unfold sobSq; congr 1; funext m; exact mFourierCoeff_toLp _ m
    rw [e]
    refine (sobSq_trigInterp_le (u k)).trans ?_
    gcongr
    calc ∑ μ, gridNorm (Dp μ (u k)) ^ 2 ≤ ∑ _μ : Fin d, B ^ 2 :=
          Finset.sum_le_sum fun μ _ => pow_le_pow_left₀ (gridNorm_nonneg _) (hD k μ) 2
      _ = d * B ^ 2 := by simp
  refine ⟨hfH, fun μ g => ?_, ?_, hS, fun μ g => ?_⟩
  · refine tendsto_inner_of_coeff (B := B) (fun k => by rw [norm_pcLp]; exact hD k μ)
      (fun m => ?_) g
    rw [mFourierCoeff_weakDeriv hfH]
    exact hcoefD μ m
  · have h := tendsto_tsum_coef_sub_sq hn hu
    simp only [← norm_trigLp_sub_sq] at h
    have := h.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  · have hbd : ∀ k, ‖weakDeriv μ (trigLp (u k))‖ ≤
        Real.sqrt (B ^ 2 + (π / 2) ^ 2 * (d * B ^ 2)) := by
      intro k
      rw [← Real.sqrt_sq (norm_nonneg _)]
      refine Real.sqrt_le_sqrt ((norm_weakDeriv_sq_le (memH_trigLp _) μ).trans ?_)
      refine (hS k).trans ?_
      have := pow_le_pow_left₀ (gridNorm_nonneg _) (hB k) 2
      linarith
    refine tendsto_inner_of_coeff hbd (fun m => ?_) g
    rw [mFourierCoeff_weakDeriv hfH]
    simp_rw [mFourierCoeff_weakDeriv (memH_trigLp _), mFourierCoeff_trigLp]
    exact tendsto_const_nhds.mul (tendsto_coef_of_tendsto_pcLp hn hu m)

end WeakLimits

/-! ### The packaged compactness clause -/

section Packaged

variable {d : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **`lem:native-critical-grid`, compactness clause** (unit-torus rendering).  A family bounded in
the discrete `H¹` norm (`‖u_h‖_{2,h}, ‖D⁺_μ u_h‖_{2,h} ≤ B`) has a subsequence along which
`R_h^0 u_h → u` strongly in `L²`, `u ∈ H¹`, the forward differences `R_h^0 D⁺_μ u_h` converge
weakly in `L²` to `∂_μ u`, and the trigonometric reconstructions are bounded in `H¹` and converge
weakly in `H¹` to `u` (strongly in `L²`, derivatives weakly in `L²`).  The strong upgrade under
strong convergence of the forward differences is
`TorusTrigReconstruction.native_reconstruction_identification`. -/
theorem native_critical_grid_compactness (hn : Tendsto n atTop atTop) (u : ∀ k, Grid d (n k) → ℂ)
    {B : ℝ} (hB : ∀ k, gridNorm (u k) ≤ B) (hD : ∀ k μ, gridNorm (Dp μ (u k)) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L²(UnitAddTorus (Fin d)), MemH 1 f ∧
      Tendsto (fun k => ‖pcLp (u (φ k)) - f‖) atTop (𝓝 0) ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))), Tendsto (fun k => inner ℂ g (pcLp (Dp μ (u (φ k)))))
        atTop (𝓝 (inner ℂ g (weakDeriv μ f)))) ∧
      Tendsto (fun k => ‖trigLp (u (φ k)) - f‖) atTop (𝓝 0) ∧
      (∀ k, sobSq 1 (trigLp (u (φ k))) ≤ B ^ 2 + (π / 2) ^ 2 * (d * B ^ 2)) ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))),
        Tendsto (fun k => inner ℂ g (weakDeriv μ (trigLp (u (φ k)))))
          atTop (𝓝 (inner ℂ g (weakDeriv μ f)))) := by
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_pcLp hn u hB hD
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  obtain ⟨h1, h2, h3, h4, h5⟩ := weak_limit_of_bounded (n := fun k => n (φ k)) hnφ
    (u := fun k => u (φ k)) (fun k => hB (φ k)) (fun k μ => hD (φ k) μ) hf
  refine ⟨φ, hφ, f, h1, hf, h2, h3, fun k => (h4 k).trans ?_, h5⟩
  have := pow_le_pow_left₀ (gridNorm_nonneg _) (hB (φ k)) 2
  linarith

end Packaged


/-! ### Finitely many components: one common subsequence -/

section Family

variable {d : ℕ}

/-- **Discrete Rellich for finitely many components** (bundle components in a fixed frame): one
common subsequence along which all `R_h^0 u^j_h` converge strongly in `L²`. -/
theorem exists_subseq_tendsto_pcLp_family (r : ℕ) :
    ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)], Tendsto n atTop atTop →
      ∀ (u : Fin r → ∀ k, Grid d (n k) → ℂ) {B : ℝ}, (∀ j k, gridNorm (u j k) ≤ B) →
        (∀ j k μ, gridNorm (Dp μ (u j k)) ≤ B) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Fin r → L²(UnitAddTorus (Fin d)),
          ∀ j, Tendsto (fun k => ‖pcLp (u j (φ k)) - f j‖) atTop (𝓝 0) := by
  induction r with
  | zero =>
      intro n _ _ u B _ _
      exact ⟨id, strictMono_id, fun j => j.elim0, fun j => j.elim0⟩
  | succ r ih =>
      intro n _ hn u B hB hD
      obtain ⟨φ₁, hφ₁, f₁, hf₁⟩ := ih hn (fun j => u (Fin.castSucc j)) (fun j k => hB _ k)
        (fun j k μ => hD _ k μ)
      have hnφ : Tendsto (fun k => n (φ₁ k)) atTop atTop := hn.comp hφ₁.tendsto_atTop
      obtain ⟨φ₂, hφ₂, g, hg⟩ := exists_subseq_tendsto_pcLp (n := fun k => n (φ₁ k)) hnφ
        (fun k => u (Fin.last r) (φ₁ k)) (fun k => hB _ _) (fun k μ => hD _ _ μ)
      refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, Fin.lastCases g f₁, fun j => ?_⟩
      induction j using Fin.lastCases with
      | last => simpa using hg
      | cast i =>
        simp only [Fin.lastCases_castSucc, Function.comp_apply]
        exact (hf₁ i).comp hφ₂.tendsto_atTop

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **`lem:native-critical-grid`, compactness clause for bundle-valued families** (finitely many
complex components in a fixed frame): one common subsequence carries all the conclusions of
`native_critical_grid_compactness` for every component. -/
theorem native_critical_grid_compactness_family (hn : Tendsto n atTop atTop) {r : ℕ}
    (u : Fin r → ∀ k, Grid d (n k) → ℂ) {B : ℝ} (hB : ∀ j k, gridNorm (u j k) ≤ B)
    (hD : ∀ j k μ, gridNorm (Dp μ (u j k)) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Fin r → L²(UnitAddTorus (Fin d)), ∀ j, MemH 1 (f j) ∧
      Tendsto (fun k => ‖pcLp (u j (φ k)) - f j‖) atTop (𝓝 0) ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))), Tendsto (fun k => inner ℂ g (pcLp (Dp μ (u j (φ k)))))
        atTop (𝓝 (inner ℂ g (weakDeriv μ (f j))))) ∧
      Tendsto (fun k => ‖trigLp (u j (φ k)) - f j‖) atTop (𝓝 0) ∧
      (∀ k, sobSq 1 (trigLp (u j (φ k))) ≤ B ^ 2 + (π / 2) ^ 2 * (d * B ^ 2)) ∧
      (∀ μ (g : L²(UnitAddTorus (Fin d))),
        Tendsto (fun k => inner ℂ g (weakDeriv μ (trigLp (u j (φ k)))))
          atTop (𝓝 (inner ℂ g (weakDeriv μ (f j))))) := by
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_pcLp_family r hn u hB hD
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop := hn.comp hφ.tendsto_atTop
  refine ⟨φ, hφ, f, fun j => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := weak_limit_of_bounded (n := fun k => n (φ k)) hnφ
    (u := fun k => u j (φ k)) (fun k => hB j (φ k)) (fun k μ => hD j (φ k) μ) (hf j)
  refine ⟨h1, hf j, h2, h3, fun k => (h4 k).trans ?_, h5⟩
  have := pow_le_pow_left₀ (gridNorm_nonneg _) (hB j (φ k)) 2
  linarith

end Family
/-! ### Link coefficients: `eq:native-link-coeff` -/

section Link

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scaled sup norm `h ‖A‖_{∞,h} = max_g N⁻¹ |A(g)|` on `(ℤ/N)⁴`. -/
def meshSup {N : ℕ} [NeZero N] (A : Grid 4 N → E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun g => (N : ℝ)⁻¹ * ‖A g‖

theorem le_meshSup {N : ℕ} [NeZero N] (A : Grid 4 N → E) (g : Grid 4 N) :
    (N : ℝ)⁻¹ * ‖A g‖ ≤ meshSup A :=
  Finset.le_sup' (fun g => (N : ℝ)⁻¹ * ‖A g‖) (Finset.mem_univ g)

theorem meshSup_nonneg {N : ℕ} [NeZero N] (A : Grid 4 N → E) : 0 ≤ meshSup A :=
  (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹ * ‖A 0‖).trans (le_meshSup A 0)

theorem indicator_cellD_pc {N : ℕ} [NeZero N] (A : Grid 4 N → E) (g : Grid 4 N) :
    (cellD g).indicator (pc A) = (cellD g).indicator fun _ => A g := by
  funext y
  by_cases hy : y ∈ cellD g
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    simp only [pc, (mem_cellD_iff g y).1 hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

/-- A single cell carries `‖R^0 A 1_{Q_g}‖_{L⁴} = N⁻¹ |A(g)|` (four dimensions). -/
theorem eLpNorm_indicator_cellD_pc {N : ℕ} [NeZero N] (A : Grid 4 N → E) (g : Grid 4 N) :
    eLpNorm ((cellD g).indicator (pc A)) 4 (volume : Measure (UnitAddTorus (Fin 4))) =
      ENNReal.ofReal ((N : ℝ)⁻¹ * ‖A g‖) := by
  rw [indicator_cellD_pc, eLpNorm_indicator_const (measurableSet_cellD g) (by norm_num)
    ENNReal.ofNat_ne_top, volume_cellD, Fintype.card_fin]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  rw [ENNReal.ofReal_mul (by positivity)]

theorem volume_cellD_four {N : ℕ} [NeZero N] (g : Grid 4 N) :
    (volume : Measure (UnitAddTorus (Fin 4))) (cellD g) = ENNReal.ofReal ((1 / (N : ℝ)) ^ 4) := by
  rw [volume_cellD, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **`eq:native-link-coeff`, first assertion**: if `R_h^0 A_h → A` strongly in `L⁴(𝕋⁴)`, then
`h ‖A_h‖_{∞,h} → 0` (uniform integrability of the fourth powers; a cell has volume `h⁴`). -/
theorem tendsto_meshSup (hn : Tendsto n atTop atTop) {A : ∀ k, Grid 4 (n k) → E}
    {A₀ : UnitAddTorus (Fin 4) → E} (hA₀ : MemLp A₀ 4 volume)
    (hA : Tendsto (fun k => eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume) atTop (𝓝 0)) :
    Tendsto (fun k => meshSup (A k)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hind⟩ := hA₀.eLpNorm_indicator_le (by norm_num) ENNReal.ofNat_ne_top
    (ε := ε / 2) (by positivity)
  have hn' : Tendsto (fun k => ((n k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hsmall : ∀ᶠ k in atTop, (1 / (n k : ℝ)) ^ 4 ≤ δ := by
    have : Tendsto (fun k => (1 / (n k : ℝ)) ^ 4) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => (1 / (n k : ℝ))) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn'
      have := h0.pow 4
      rwa [zero_pow (by norm_num)] at this
    exact (tendsto_order.1 this).2 δ hδ |>.mono fun k hk => hk.le
  have hconv : ∀ᶠ k in atTop, eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume ≤
      ENNReal.ofReal (ε / 4) :=
    (ENNReal.tendsto_nhds_zero.1 hA) _ (by simp; positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hsmall.and hconv)
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hK k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (meshSup_nonneg _)]
  have hcell : ∀ g, (n k : ℝ)⁻¹ * ‖A k g‖ ≤ 3 * ε / 4 := by
    intro g
    have hm1 : AEStronglyMeasurable (fun y => pc (A k) y - A₀ y) volume :=
      (stronglyMeasurable_pc _).aestronglyMeasurable.sub hA₀.1
    have hsplit : (cellD g).indicator (pc (A k)) =
        (cellD g).indicator (fun y => pc (A k) y - A₀ y) + (cellD g).indicator A₀ := by
      funext y; by_cases hy : y ∈ cellD g <;> simp [hy]
    have hle : ENNReal.ofReal ((n k : ℝ)⁻¹ * ‖A k g‖) ≤
        ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) := by
      rw [← eLpNorm_indicator_cellD_pc, hsplit]
      refine (eLpNorm_add_le (hm1.indicator (measurableSet_cellD g))
        (hA₀.1.indicator (measurableSet_cellD g)) (by norm_num)).trans (add_le_add ?_ ?_)
      · exact (eLpNorm_indicator_le _).trans h2
      · exact hind _ (measurableSet_cellD g) (by
          rw [volume_cellD_four]; exact ENNReal.ofReal_le_ofReal h1)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    linarith
  calc meshSup (A k) ≤ 3 * ε / 4 := Finset.sup'_le _ _ fun g _ => hcell g
    _ < ε := by linarith

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The link coefficient `B^ρ = (e^{h X} - 1)/h` of a Lie-algebra element `X = ρ(A)` at mesh
`h = 1/N` (`U = e^{hA}`, `ρ(U) = e^{h ρ(A)}`). -/
def linkCoeff (N : ℕ) (X : 𝔸) : 𝔸 := (N : ℝ) • (NormedSpace.exp ((N : ℝ)⁻¹ • X) - 1)

/-- `‖B^ρ - X‖ ≤ ‖X‖ · (h‖X‖ e^{h‖X‖})`. -/
theorem norm_linkCoeff_sub_le {N : ℕ} [NeZero N] (X : 𝔸) :
    ‖linkCoeff N X - X‖ ≤ ‖X‖ * ((N : ℝ)⁻¹ * ‖X‖ * Real.exp ((N : ℝ)⁻¹ * ‖X‖)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have e : linkCoeff N X - X = (N : ℝ) • (NormedSpace.exp ((N : ℝ)⁻¹ • X) - 1 - (N : ℝ)⁻¹ • X) := by
    rw [linkCoeff, smul_sub, smul_sub, smul_sub, smul_smul, mul_inv_cancel₀ hN.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg hN.le]
  have h := LogBCH.norm_exp_sub_linear_le ((N : ℝ)⁻¹ • X)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h
  calc (N : ℝ) * ‖NormedSpace.exp ((N : ℝ)⁻¹ • X) - 1 - (N : ℝ)⁻¹ • X‖
      ≤ N * (((N : ℝ)⁻¹ * ‖X‖) ^ 2 * Real.exp ((N : ℝ)⁻¹ * ‖X‖)) :=
        mul_le_mul_of_nonneg_left h hN.le
    _ = ‖X‖ * ((N : ℝ)⁻¹ * ‖X‖ * Real.exp ((N : ℝ)⁻¹ * ‖X‖)) := by field_simp

/-- `‖B^ρ‖ ≤ ‖X‖ (1 + h‖X‖ e^{h‖X‖})`; in particular `‖B^ρ‖ ≤ (1 + e) ‖X‖` once `h‖X‖ ≤ 1`. -/
theorem norm_linkCoeff_le {N : ℕ} [NeZero N] (X : 𝔸) :
    ‖linkCoeff N X‖ ≤ ‖X‖ * (1 + (N : ℝ)⁻¹ * ‖X‖ * Real.exp ((N : ℝ)⁻¹ * ‖X‖)) := by
  have h := norm_linkCoeff_sub_le (N := N) X
  have : ‖linkCoeff N X‖ ≤ ‖linkCoeff N X - X‖ + ‖X‖ := by
    have := norm_add_le (linkCoeff N X - X) X; rwa [sub_add_cancel] at this
  nlinarith

theorem mul_exp_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a * Real.exp a ≤ b * Real.exp b :=
  mul_le_mul hab (Real.exp_le_exp.2 hab) (Real.exp_pos _).le (ha.trans hab)

/-- **`eq:native-link-coeff`, second assertion**: if `R_h^0 A_h → A` strongly in `L⁴(𝕋⁴)` and
`ρ` is a (bounded linear) Lie-algebra representation, then `R_h^0 B^ρ_h → ρ(A)` strongly in
`L⁴`, `B^ρ_h = (e^{h ρ(A_h)} - 1)/h`. -/
theorem tendsto_linkCoeff (hn : Tendsto n atTop atTop) (ρ : E →L[ℝ] 𝔸)
    {A : ∀ k, Grid 4 (n k) → E} {A₀ : UnitAddTorus (Fin 4) → E} (hA₀ : MemLp A₀ 4 volume)
    (hA : Tendsto (fun k => eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun y => pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (A₀ y))
      4 volume) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun k => ‖ρ‖ * meshSup (A k)
  have hs : Tendsto s atTop (𝓝 0) := by simpa using (tendsto_meshSup hn hA₀ hA).const_mul ‖ρ‖
  set c : ℕ → ℝ := fun k => ‖ρ‖ * (s k * Real.exp (s k))
  have hc : Tendsto c atTop (𝓝 0) := by
    have : Tendsto (fun k => s k * Real.exp (s k)) atTop (𝓝 (0 * Real.exp 0)) :=
      hs.mul ((Real.continuous_exp.tendsto 0).comp hs)
    simpa [c] using this.const_mul ‖ρ‖
  have hs0 : ∀ k, 0 ≤ s k := fun k => mul_nonneg (norm_nonneg _) (meshSup_nonneg _)
  have hc0 : ∀ k, 0 ≤ c k := fun k => mul_nonneg (norm_nonneg _)
    (mul_nonneg (hs0 k) (Real.exp_pos _).le)
  -- pointwise bound on the defect
  have hpt : ∀ k y, ‖pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (pc (A k) y)‖ ≤
      c k * ‖pc (A k) y‖ := by
    intro k y
    simp only [pc]
    set a := A k (TorusPiecewiseConstantTranslation.index (n k) y)
    have hρa : ‖ρ a‖ ≤ ‖ρ‖ * ‖a‖ := ρ.le_opNorm a
    have ht : ((n k : ℝ))⁻¹ * ‖ρ a‖ ≤ s k := by
      calc ((n k : ℝ))⁻¹ * ‖ρ a‖ ≤ ((n k : ℝ))⁻¹ * (‖ρ‖ * ‖a‖) :=
            mul_le_mul_of_nonneg_left hρa (by positivity)
        _ = ‖ρ‖ * (((n k : ℝ))⁻¹ * ‖a‖) := by ring
        _ ≤ s k := mul_le_mul_of_nonneg_left (le_meshSup _ _) (norm_nonneg _)
    refine (norm_linkCoeff_sub_le (ρ a)).trans ?_
    calc ‖ρ a‖ * (((n k : ℝ))⁻¹ * ‖ρ a‖ * Real.exp (((n k : ℝ))⁻¹ * ‖ρ a‖))
        ≤ (‖ρ‖ * ‖a‖) * (s k * Real.exp (s k)) :=
          mul_le_mul hρa (mul_exp_mono (by positivity) ht) (by positivity) (by positivity)
      _ = c k * ‖a‖ := by ring
  have hmA : ∀ k, AEStronglyMeasurable (pc (A k)) (volume : Measure (UnitAddTorus (Fin 4))) :=
    fun k => (stronglyMeasurable_pc _).aestronglyMeasurable
  have hF : ∀ k, eLpNorm (fun y => pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (pc (A k) y))
      4 volume ≤ ENNReal.ofReal (c k) * (eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume +
        eLpNorm A₀ 4 volume) := by
    intro k
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall (hpt k)) 4).trans ?_
    gcongr
    have e : pc (A k) = (fun y => pc (A k) y - A₀ y) + A₀ := by funext y; simp
    conv_lhs => rw [e]
    exact eLpNorm_add_le (p := 4) ((hmA k).sub hA₀.1) hA₀.1 (by norm_num)
  have hG : ∀ k, eLpNorm (fun y => ρ (pc (A k) y) - ρ (A₀ y)) 4 volume ≤
      ENNReal.ofReal ‖ρ‖ * eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume := by
    intro k
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun y => ?_) 4
    rw [← map_sub]
    exact ρ.le_opNorm _
  have hsplit : ∀ k, (fun y => pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (A₀ y)) =
      (fun y => pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (pc (A k) y)) +
        fun y => ρ (pc (A k) y) - ρ (A₀ y) := by
    intro k; funext y; simp
  have hmF : ∀ k, AEStronglyMeasurable
      (fun y => pc (fun g => linkCoeff (n k) (ρ (A k g))) y - ρ (pc (A k) y)) volume :=
    fun k => (stronglyMeasurable_pc _).aestronglyMeasurable.sub
      (ρ.continuous.comp_aestronglyMeasurable (hmA k))
  have hmG : ∀ k, AEStronglyMeasurable (fun y => ρ (pc (A k) y) - ρ (A₀ y)) volume :=
    fun k => (ρ.continuous.comp_aestronglyMeasurable (hmA k)).sub
      (ρ.continuous.comp_aestronglyMeasurable hA₀.1)
  have hup : Tendsto (fun k => ENNReal.ofReal (c k) * (eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume +
      eLpNorm A₀ 4 volume) + ENNReal.ofReal ‖ρ‖ * eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (c k)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hc
    have h2 : Tendsto (fun k => eLpNorm (fun y => pc (A k) y - A₀ y) 4 volume +
        eLpNorm A₀ 4 volume) atTop (𝓝 (0 + eLpNorm A₀ 4 volume)) := hA.add tendsto_const_nhds
    have h3 := ENNReal.Tendsto.mul h1 (Or.inr (by simpa using hA₀.2.ne)) h2 (Or.inr ENNReal.zero_ne_top)
    have h4 := ENNReal.Tendsto.const_mul hA (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal ‖ρ‖)
    simpa using h3.add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
    fun k => ?_
  rw [hsplit k]
  exact (eLpNorm_add_le (hmF k) (hmG k) (by norm_num)).trans (add_le_add (hF k) (hG k))

end Link

/-! ### The graph-norm consequence on the paper's box -/

section GraphNorm

open GridSobolev

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- `‖h⁻¹ (e^{hX} - 1)‖ ≤ ‖X‖ (1 + h‖X‖ e^{h‖X‖})` for `h > 0` (any mesh). -/
theorem norm_hinv_exp_sub_one_le {h : ℝ} (hh : 0 < h) (X : 𝔸) :
    ‖h⁻¹ • (NormedSpace.exp (h • X) - 1)‖ ≤ ‖X‖ * (1 + h * ‖X‖ * Real.exp (h * ‖X‖)) := by
  have hlin := LogBCH.norm_exp_sub_linear_le (h • X)
  rw [norm_smul, Real.norm_of_nonneg hh.le] at hlin
  have e : h⁻¹ • (NormedSpace.exp (h • X) - 1) = h⁻¹ • (NormedSpace.exp (h • X) - 1 - h • X) + X := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  have : h⁻¹ * ‖NormedSpace.exp (h • X) - 1 - h • X‖ ≤ ‖X‖ * (h * ‖X‖ * Real.exp (h * ‖X‖)) := by
    calc h⁻¹ * ‖NormedSpace.exp (h • X) - 1 - h • X‖ ≤ h⁻¹ * ((h * ‖X‖) ^ 2 * Real.exp (h * ‖X‖)) :=
          mul_le_mul_of_nonneg_left hlin (inv_nonneg.2 hh.le)
      _ = ‖X‖ * (h * ‖X‖ * Real.exp (h * ‖X‖)) := by field_simp
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

theorem gridL4Norm_le_mul {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {h c : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c)
    {u : (ι → ZMod n) → F} {v : (ι → ZMod n) → G} (huv : ∀ x, ‖u x‖ ≤ c * ‖v x‖) :
    gridL4Norm h u ≤ c * gridL4Norm h v := by
  unfold gridL4Norm
  have hS : h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4 ≤ c ^ 4 * (h ^ Fintype.card ι * ∑ x, ‖v x‖ ^ 4) := by
    calc h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4 ≤ h ^ Fintype.card ι * ∑ x, c ^ 4 * ‖v x‖ ^ 4 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (pow_nonneg hh _)
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (huv x) 4
      _ = c ^ 4 * (h ^ Fintype.card ι * ∑ x, ‖v x‖ ^ 4) := by rw [← Finset.mul_sum]; ring
  calc (h ^ Fintype.card ι * ∑ x, ‖u x‖ ^ 4) ^ ((1 : ℝ) / 4)
      ≤ (c ^ 4 * (h ^ Fintype.card ι * ∑ x, ‖v x‖ ^ 4)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hS (by norm_num)
    _ = c * (h ^ Fintype.card ι * ∑ x, ‖v x‖ ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hc]
        norm_num

/-- **`‖B^ρ_h‖_{4,h} ≤ (1 + e) ‖ρ‖ ‖A_h‖_{4,h}`** in the regime `h ‖ρ‖ ‖A_h‖_{∞} ≤ 1` (which holds
eventually under strong `L⁴` convergence of the connections, `tendsto_meshSup`). -/
theorem gridL4Norm_linkCoeff_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E →L[ℝ] 𝔸) {h : ℝ} (hh : 0 < h) (A : (ι → ZMod n) → E)
    (hA : ∀ x, h * (‖ρ‖ * ‖A x‖) ≤ 1) :
    gridL4Norm h (fun x => h⁻¹ • (NormedSpace.exp (h • ρ (A x)) - 1)) ≤
      (1 + Real.exp 1) * ‖ρ‖ * gridL4Norm h A := by
  refine gridL4Norm_le_mul hh.le (by positivity) fun x => ?_
  refine (norm_hinv_exp_sub_one_le hh (ρ (A x))).trans ?_
  have hρ : ‖ρ (A x)‖ ≤ ‖ρ‖ * ‖A x‖ := ρ.le_opNorm _
  have ht : h * ‖ρ (A x)‖ ≤ 1 := (mul_le_mul_of_nonneg_left hρ hh.le).trans (hA x)
  have h1 : h * ‖ρ (A x)‖ * Real.exp (h * ‖ρ (A x)‖) ≤ 1 * Real.exp 1 :=
    mul_exp_mono (by positivity) ht
  calc ‖ρ (A x)‖ * (1 + h * ‖ρ (A x)‖ * Real.exp (h * ‖ρ (A x)‖))
      ≤ (‖ρ‖ * ‖A x‖) * (1 + Real.exp 1) :=
        mul_le_mul hρ (by linarith) (by positivity) (by positivity)
    _ = (1 + Real.exp 1) * ‖ρ‖ * ‖A x‖ := by ring

/-- **The graph-norm consequence of `lem:native-critical-grid`** on the paper's box `L = n h = 2π`:
for unitary links `R_i(x) = e^{h ρ(A_i(x))}` with `h ‖ρ‖ ‖A‖_∞ ≤ 1`,
`‖D⁺_i u‖_{2,h} ≤ ‖D^U_i u‖_{2,h} + 3 (1 + e) ‖ρ‖ ‖A_i‖_{4,h} (‖u‖_{2,h} + Σ_j ‖D^U_j u‖_{2,h})`:
a bounded positive graph norm together with a bounded `L⁴_h` connection controls the ordinary
discrete `H¹` norm. -/
theorem gridFwd_le_graphNorm_connection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] [CompleteSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hι : Fintype.card ι = 4) {h : ℝ} (hh : 0 < h) (hL : (n : ℝ) * h = 2 * Real.pi)
    (ρ : V →L[ℝ] (E →L[ℝ] E)) (A : (ι → ZMod n) → ι → V)
    (hR : ∀ x i v, ‖NormedSpace.exp (h • ρ (A x i)) v‖ = ‖v‖)
    (hA : ∀ x i, h * (‖ρ‖ * ‖A x i‖) ≤ 1) (i : ι) (u : (ι → ZMod n) → E) :
    gridL2Norm h (gridFwd h i u) ≤
      gridL2Norm h (gridCovFwd h (fun x j => ((NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E) : E → E)) i u) +
        3 * ((1 + Real.exp 1) * ‖ρ‖ * gridL4Norm h (fun x => A x i)) *
          (gridL2Norm h u + ∑ j, gridL2Norm h
            (gridCovFwd h (fun x j => ((NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E) : E → E)) j u)) := by
  have h1 := gridFwd_le_graphNorm hι hh hL
    (fun x j => (NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E)) hR i u
  have h2 := gridL4Norm_linkCoeff_le ρ hh (fun x => A x i) (fun x => hA x i)
  have h3 : 0 ≤ gridL2Norm h u + ∑ j, gridL2Norm h
      (gridCovFwd h (fun x j => ((NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E) : E → E)) j u) :=
    add_nonneg (gridL2Norm_nonneg _ _) (Finset.sum_nonneg fun _ _ => gridL2Norm_nonneg _ _)
  have h4 : gridL4Norm h (fun x => h⁻¹ • (NormedSpace.exp (h • ρ (A x i)) - 1)) *
      (gridL2Norm h u + ∑ j, gridL2Norm h
        (gridCovFwd h (fun x j => ((NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E) : E → E)) j u)) ≤
      (1 + Real.exp 1) * ‖ρ‖ * gridL4Norm h (fun x => A x i) *
        (gridL2Norm h u + ∑ j, gridL2Norm h
          (gridCovFwd h (fun x j => ((NormedSpace.exp (h • ρ (A x j)) : E →L[ℝ] E) : E → E)) j u)) :=
    mul_le_mul_of_nonneg_right h2 h3
  linarith

end GraphNorm

end

end RenewalGeometry.NativeCriticalGrid
