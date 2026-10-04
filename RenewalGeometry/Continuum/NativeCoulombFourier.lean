/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeCoulombAbsorption

/-!
# Fourier calculus for raw reconstructions and the critical embedding `H¹(𝕋⁴) ⊂ L⁴`

Generic infrastructure (no renewal notions) for the limit clauses of `thm:native-discrete-Coulomb`
of the Einstein–SM action-closure manuscript (unit-torus rendering, grid `(ℤ/N)⁴`, mesh `1/N`).

* `mFourierCoeff_comp_add` : `(f(· + z))^(m) = e_m(z) f̂(m)` for vector-valued `f`;
* `mFourierCoeff_pc_DpV`, `mFourierCoeff_pc_DmV` : the forward and backward differences of a raw
  reconstruction are **exact** Fourier multipliers, `sym_N(m) = N(e^{2πi m_μ/N} - 1)` and
  `symB_N(m) = N(1 - e^{-2πi m_μ/N})`, both tending to `2πi m_μ` (`tendsto_symB`) — the discrete
  summation by parts against continuum characters;
* `tendsto_mFourierCoeff_of_lpTendsto_one` : strong `L¹` convergence gives convergence of every
  Fourier coefficient;
* `eLpNorm_four_trigPoly_le` (**critical Sobolev inequality for trigonometric polynomials**,
  obtained from the uniform discrete Sobolev inequality by sampling on finer and finer grids):
  `‖P‖_{L⁴} ≤ 3 Σ_μ ‖∂_μ P‖_{L²} + 4 ‖P‖_{L²}` on `𝕋⁴`;
* `tendsto_eLpNorm_four_trunc` (**the critical embedding `H¹(𝕋⁴) ⊂ L⁴`**): for `f ∈ H¹(𝕋⁴)` the
  Fourier truncations `Σ_{m ∈ box R} f̂(m) e_m` converge to `f` strongly in `L⁴` (in particular
  `f ∈ L⁴`);
* `vtrig`, `vtrigTest` : vector-valued trigonometric polynomials and the `C¹` gauge tests they
  define.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.NativeCoulomb

open TorusTrigReconstruction NativeCriticalGrid TorusPiecewiseConstantTranslation
  NativeYMIdentification NativeYMVariation NativeGridLp NativeHiggs TorusSobolev

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

local instance fact_one_le_four_f : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance fact_one_le_two_f : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-! ### Fourier coefficients of translates and of grid differences -/

section Translation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `(f(· + z))^(m) = e_m(z) f̂(m)`. -/
theorem mFourierCoeff_comp_add (f : UnitAddTorus (Fin 4) → F) (z : UnitAddTorus (Fin 4))
    (m : Fin 4 → ℤ) :
    mFourierCoeff (fun y => f (y + z)) m = mFourier m z • mFourierCoeff f m := by
  have h2 := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus (Fin 4))))
    (fun s => mFourier (-m) (s - z) • f s) z
  simp only [add_sub_cancel_right] at h2
  rw [mFourierCoeff, h2, mFourierCoeff, ← integral_smul]
  congr 1
  funext s
  rw [sub_eq_add_neg, KolmogorovRieszTorus.mFourier_add_apply, KolmogorovRieszTorus.mFourier_neg_neg,
    smul_smul, mul_comm]

theorem integrable_pc {N : ℕ} [NeZero N] (u : LatticeTorusPlancherel.Grid 4 N → F) :
    Integrable (pc u) (volume : Measure (UnitAddTorus (Fin 4))) :=
  (memLp_pc_gen (E := F) u 1).integrable le_rfl

theorem mFourierCoeff_sub' {f g : UnitAddTorus (Fin 4) → F} (hf : Integrable f volume)
    (hg : Integrable g volume) (m : Fin 4 → ℤ) :
    mFourierCoeff (f - g) m = mFourierCoeff f m - mFourierCoeff g m := by
  have hint : ∀ {u : UnitAddTorus (Fin 4) → F}, Integrable u volume →
      Integrable (fun t => mFourier (-m) t • u t) volume := fun hu =>
    hu.bdd_smul 1 (mFourier (-m)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [TorusSobolev.norm_mFourier_apply])
  simp only [mFourierCoeff, Pi.sub_apply, smul_sub]
  exact integral_sub (hint hf) (hint hg)

theorem mFourierCoeff_real_smul (c : ℝ) (f : UnitAddTorus (Fin 4) → F) (m : Fin 4 → ℤ) :
    mFourierCoeff (fun y => c • f y) m = (c : ℂ) • mFourierCoeff f m := by
  simp only [mFourierCoeff]
  rw [← integral_smul]
  congr 1; funext t
  rw [← Complex.coe_smul, smul_comm]

variable {N : ℕ} [NeZero N]

theorem pc_shift_eq (u : LatticeTorusPlancherel.Grid 4 N → F) (μ : Fin 4) (j : ℤ)
    (y : UnitAddTorus (Fin 4)) :
    pc (fun x => u (x + Pi.single μ (j : ZMod N))) y =
      pc u (y + KolmogorovRieszTorus.coordPt μ ((j : ℝ) / N)) := by
  rw [pc_add_coordPt_int u y μ j]; rfl

/-- The backward difference `D⁻_μ v(x) = N (v(x) - v(x - e_μ))`. -/
def DmV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Fin 4)
    (v : LatticeTorusPlancherel.Grid 4 N → E) (x : LatticeTorusPlancherel.Grid 4 N) : E :=
  (N : ℝ) • (v x - v (x - Pi.single μ 1))

/-- The backward symbol `N (1 - e^{-2πi m_μ/N})`. -/
def symB (N : ℕ) (μ : Fin 4) (m : Fin 4 → ℤ) : ℂ :=
  (N : ℂ) * (1 - Complex.exp (-(2 * π * Complex.I * (m μ : ℂ) / N)))

theorem mFourier_coordPt_inv (m : Fin 4 → ℤ) (μ : Fin 4) (j : ℤ) :
    mFourier m (KolmogorovRieszTorus.coordPt μ ((j : ℝ) / N)) =
      Complex.exp (2 * π * Complex.I * (m μ : ℂ) * j / N) := by
  rw [KolmogorovRieszTorus.mFourier_coordPt]
  congr 1
  push_cast
  ring

/-- The forward difference is the exact multiplier `sym N μ m = N (e^{2πi m_μ/N} - 1)`. -/
theorem mFourierCoeff_pc_DpV (u : LatticeTorusPlancherel.Grid 4 N → F) (μ : Fin 4)
    (m : Fin 4 → ℤ) :
    mFourierCoeff (pc (DpV μ u)) m = sym N μ m • mFourierCoeff (pc u) m := by
  have e : pc (DpV μ u) = fun y => (N : ℝ) • (pc (fun x => u (x + Pi.single μ ((1 : ℤ) : ZMod N))) y -
      pc u y) := by
    funext y; simp [pc, DpV]
  rw [e, mFourierCoeff_real_smul]
  have hsub : (fun y => pc (fun x => u (x + Pi.single μ ((1 : ℤ) : ZMod N))) y - pc u y) =
      pc (fun x => u (x + Pi.single μ ((1 : ℤ) : ZMod N))) - pc u := rfl
  rw [hsub, mFourierCoeff_sub' (integrable_pc _) (integrable_pc _)]
  have htr : mFourierCoeff (pc (fun x => u (x + Pi.single μ ((1 : ℤ) : ZMod N)))) m =
      mFourier m (KolmogorovRieszTorus.coordPt μ (((1 : ℤ) : ℝ) / N)) • mFourierCoeff (pc u) m := by
    rw [← mFourierCoeff_comp_add]
    congr 1; funext y; exact pc_shift_eq u μ 1 y
  rw [htr, mFourier_coordPt_inv, show ∀ (e : ℂ) (v : F), e • v - v = (e - 1) • v from
    fun e v => by rw [sub_smul, one_smul], smul_smul, sym]
  congr 1
  push_cast
  ring_nf

/-- The backward difference is the exact multiplier `symB N μ m = N (1 - e^{-2πi m_μ/N})`. -/
theorem mFourierCoeff_pc_DmV (u : LatticeTorusPlancherel.Grid 4 N → F) (μ : Fin 4)
    (m : Fin 4 → ℤ) :
    mFourierCoeff (pc (DmV μ u)) m = symB N μ m • mFourierCoeff (pc u) m := by
  have e : pc (DmV μ u) = fun y => (N : ℝ) • (pc u y -
      pc (fun x => u (x + Pi.single μ ((-1 : ℤ) : ZMod N))) y) := by
    funext y; simp [pc, DmV, sub_eq_add_neg, Pi.single_neg]
  rw [e, mFourierCoeff_real_smul]
  have hsub : (fun y => pc u y - pc (fun x => u (x + Pi.single μ ((-1 : ℤ) : ZMod N))) y) =
      pc u - pc (fun x => u (x + Pi.single μ ((-1 : ℤ) : ZMod N))) := rfl
  rw [hsub, mFourierCoeff_sub' (integrable_pc _) (integrable_pc _)]
  have htr : mFourierCoeff (pc (fun x => u (x + Pi.single μ ((-1 : ℤ) : ZMod N)))) m =
      mFourier m (KolmogorovRieszTorus.coordPt μ (((-1 : ℤ) : ℝ) / N)) • mFourierCoeff (pc u) m := by
    rw [← mFourierCoeff_comp_add]
    congr 1; funext y; exact pc_shift_eq u μ (-1) y
  rw [htr, mFourier_coordPt_inv, show ∀ (e : ℂ) (v : F), v - e • v = (1 - e) • v from
    fun e v => by rw [sub_smul, one_smul], smul_smul, symB]
  congr 1
  push_cast
  ring_nf

end Translation

theorem tendsto_symB {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ : Fin 4) (m : Fin 4 → ℤ) :
    Tendsto (fun k => symB (n k) μ m) atTop (𝓝 (2 * π * Complex.I * m μ)) := by
  have h := tendsto_sym hn μ (-m)
  have e : ∀ k, symB (n k) μ m = -sym (n k) μ (-m) := by
    intro k; simp only [symB, sym, Pi.neg_apply, Int.cast_neg]; ring_nf
  simp only [e]
  have := h.neg
  simpa [Pi.neg_apply] using this

/-! ### Convergence of Fourier coefficients under strong `L¹` convergence -/

section L1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_mFourierCoeff_le (f : UnitAddTorus (Fin 4) → F) (hf : AEStronglyMeasurable f volume)
    (m : Fin 4 → ℤ) : ‖mFourierCoeff f m‖ ≤ (eLpNorm f 1 volume).toReal := by
  rw [mFourierCoeff]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm
    (f := fun t => mFourier (-m) t • f t) (((mFourier (-m)).continuous.aestronglyMeasurable).smul hf)]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [enorm_smul, ← ofReal_norm_eq_enorm (mFourier (-m) t), TorusSobolev.norm_mFourier_apply,
    ENNReal.ofReal_one, one_mul]

/-- Strong `L¹` convergence gives convergence of every Fourier coefficient. -/
theorem tendsto_mFourierCoeff_of_lpTendsto_one {g : ℕ → UnitAddTorus (Fin 4) → F}
    {g₀ : UnitAddTorus (Fin 4) → F} (h : LpTendsto volume 1 g g₀) (m : Fin 4 → ℤ) :
    Tendsto (fun k => mFourierCoeff (g k) m) atTop (𝓝 (mFourierCoeff g₀ m)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k => (eLpNorm (g k - g₀) 1 volume).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.tendsto
    rwa [ENNReal.toReal_zero] at this
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h0
  rw [← mFourierCoeff_sub' ((h.memLp k).integrable le_rfl) (h.memLp_lim.integrable le_rfl)]
  exact norm_mFourierCoeff_le _ ((h.memLp k).1.sub h.memLp_lim.1) m

end L1

/-! ### The critical Sobolev inequality for trigonometric polynomials -/

section Critical

/-- Parseval for trigonometric polynomials: `‖Σ_{m∈S} c_m e_m‖²_{L²} = Σ_{m∈S} |c_m|²`. -/
theorem norm_toLp_trigPoly_sq (S : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → ℂ) :
    ‖ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖ ^ 2 = ∑ m ∈ S, ‖c m‖ ^ 2 := by
  have h := KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff
    (ContinuousMap.toLp 2 volume ℂ (trigPoly S c))
  simp only [mFourierCoeff_toLp, mFourierCoeff_trigPoly] at h
  have e : (fun m => ‖if m ∈ S then c m else 0‖ ^ 2) = fun m => if m ∈ S then ‖c m‖ ^ 2 else 0 := by
    funext m; split_ifs <;> simp
  rw [e] at h
  have h2 : HasSum (fun m => if m ∈ S then ‖c m‖ ^ 2 else 0) (∑ m ∈ S, if m ∈ S then ‖c m‖ ^ 2 else 0) :=
    hasSum_sum_of_ne_finset_zero (s := S) (fun m hm => if_neg hm)
  rw [Finset.sum_congr rfl fun m hm => if_pos hm] at h2
  exact h.unique h2

/-- **Critical Sobolev inequality for trigonometric polynomials on `𝕋⁴`**, from the uniform discrete
Sobolev inequality by sampling: `‖P‖_{L⁴} ≤ 3 Σ_μ ‖∂_μ P‖_{L²} + 4 ‖P‖_{L²}`. -/
theorem eLpNorm_four_trigPoly_le (S : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → ℂ) :
    eLpNorm (trigPoly S c) 4 volume ≤ ENNReal.ofReal (3 * ∑ μ, ‖ContinuousMap.toLp 2 volume ℂ
      (trigPoly S (fun m => 2 * π * Complex.I * m μ * c m))‖ +
        4 * ‖ContinuousMap.toLp 2 volume ℂ (trigPoly S c)‖) := by
  set P := trigPoly S c
  set n : ℕ → ℕ := fun k => k + 1
  have hn : Tendsto n atTop atTop := tendsto_add_atTop_nat 1
  set R : ℝ := 3 * ∑ μ, ‖ContinuousMap.toLp 2 volume ℂ
      (trigPoly S (fun m => 2 * π * Complex.I * m μ * c m))‖ +
        4 * ‖ContinuousMap.toLp 2 volume ℂ P‖
  set Rk : ℕ → ℝ := fun k => 3 * ∑ μ, gridNorm (Dp μ (samp (n k) P)) + 4 * gridNorm (samp (n k) P)
  set bk : ℕ → ℝ := fun k => ∑ m ∈ S, ‖c m‖ * (2 * π * (∑ i, |(m i : ℝ)|) / (n k : ℝ))
  have hbk : Tendsto bk atTop (𝓝 0) := tendsto_bound_samp hn S c
  have hbk0 : ∀ k, 0 ≤ bk k := fun k => Finset.sum_nonneg fun m _ => by positivity
  have hnorm : ∀ {a : ℕ → L²(UnitAddTorus (Fin 4))} {b : L²(UnitAddTorus (Fin 4))},
      Tendsto (fun k => ‖a k - b‖) atTop (𝓝 0) → Tendsto (fun k => ‖a k‖) atTop (𝓝 ‖b‖) := by
    intro a b h
    have := (tendsto_iff_norm_sub_tendsto_zero.2 h).norm
    exact this
  have hRk : Tendsto Rk atTop (𝓝 R) := by
    have h1 : ∀ μ, Tendsto (fun k => gridNorm (Dp μ (samp (n k) P))) atTop
        (𝓝 ‖ContinuousMap.toLp 2 volume ℂ (trigPoly S (fun m => 2 * π * Complex.I * m μ * c m))‖) :=
      fun μ => by
        have := hnorm (tendsto_pcLp_Dp_samp hn μ S c)
        simpa only [norm_pcLp] using this
    have h2 : Tendsto (fun k => gridNorm (samp (n k) P)) atTop
        (𝓝 ‖ContinuousMap.toLp 2 volume ℂ P‖) := by
      have := hnorm (tendsto_pcLp_samp hn S c)
      simpa only [norm_pcLp] using this
    exact ((tendsto_finsetSum (Finset.univ : Finset (Fin 4)) fun μ _ => h1 μ).const_mul 3).add
      (h2.const_mul 4)
  have hP4 : eLpNorm P 4 volume ≠ ∞ := (memLp_continuousMap P 4).2.ne
  have hRk0 : ∀ k, 0 ≤ Rk k := fun k => add_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => gridNorm_nonneg _)) (mul_nonneg (by norm_num) (gridNorm_nonneg _))
  have hle : ∀ k, (eLpNorm P 4 volume).toReal ≤ Rk k + bk k := by
    intro k
    have hs := eLpNorm_pc_four_le (samp (n k) P)
    have hd : eLpNorm (fun y => P y - pc (samp (n k) P) y) 4 volume ≤ ENNReal.ofReal (bk k) :=
      (eLpNorm_le_of_ae_bound (Eventually.of_forall fun y => by
        rw [norm_sub_rev]; exact norm_pc_samp_sub_le S c y)).trans (le_of_eq (by simp; rfl))
    have hsplit : (P : UnitAddTorus (Fin 4) → ℂ) = pc (samp (n k) P) +
        fun y => P y - pc (samp (n k) P) y := by funext y; simp
    have htot : eLpNorm P 4 volume ≤ ENNReal.ofReal (Rk k + bk k) := by
      calc eLpNorm P 4 volume = eLpNorm (pc (samp (n k) P) +
            fun y => P y - pc (samp (n k) P) y) 4 volume := by rw [← hsplit]
        _ ≤ eLpNorm (pc (samp (n k) P)) 4 volume +
            eLpNorm (fun y => P y - pc (samp (n k) P) y) 4 volume :=
            eLpNorm_add_le (stronglyMeasurable_pc _).aestronglyMeasurable
              (P.continuous.aestronglyMeasurable.sub (stronglyMeasurable_pc _).aestronglyMeasurable)
              (by norm_num)
        _ ≤ ENNReal.ofReal (Rk k) + ENNReal.ofReal (bk k) := add_le_add hs hd
        _ = ENNReal.ofReal (Rk k + bk k) := by
            rw [ENNReal.ofReal_add (hRk0 k) (hbk0 k)]
    exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (hRk0 k) (hbk0 k)) htot
  have hlim := hRk.add hbk
  rw [add_zero] at hlim
  have := ge_of_tendsto' hlim hle
  rw [← ENNReal.ofReal_toReal hP4]
  exact ENNReal.ofReal_le_ofReal this

/-- The `H¹` tail beyond the TorusSobolev.box of radius `R`. -/
def h1Tail (f : L²(UnitAddTorus (Fin 4))) (R : ℕ) : ℝ :=
  ∑' m, if m ∈ TorusSobolev.box R then 0 else sobWeight m * ‖mFourierCoeff f m‖ ^ 2

theorem summable_h1 {f : L²(UnitAddTorus (Fin 4))} (hf : MemH 1 f) :
    Summable fun m => sobWeight m * ‖mFourierCoeff f m‖ ^ 2 := by
  have := hf
  unfold MemH CoeffMemH at this
  simpa only [Real.rpow_one] using this

theorem sobWeight_nonneg' (m : Fin 4 → ℤ) : 0 ≤ sobWeight m := by
  unfold sobWeight; positivity

theorem tendsto_h1Tail {f : L²(UnitAddTorus (Fin 4))} (hf : MemH 1 f) :
    Tendsto (h1Tail f) atTop (𝓝 0) := by
  have hs := summable_h1 hf
  have h1 : Tendsto (fun R : ℕ => ∑ m ∈ TorusSobolev.box R, sobWeight m * ‖mFourierCoeff f m‖ ^ 2) atTop
      (𝓝 (∑' m, sobWeight m * ‖mFourierCoeff f m‖ ^ 2)) :=
    hs.hasSum.comp tendsto_box
  have e : ∀ R, h1Tail f R = ∑' m, sobWeight m * ‖mFourierCoeff f m‖ ^ 2 -
      ∑ m ∈ TorusSobolev.box R, sobWeight m * ‖mFourierCoeff f m‖ ^ 2 := fun R =>
    tsum_ite_eq_sub hs (TorusSobolev.box R)
  rw [show h1Tail f = fun R => ∑' m, sobWeight m * ‖mFourierCoeff f m‖ ^ 2 -
      ∑ m ∈ TorusSobolev.box R, sobWeight m * ‖mFourierCoeff f m‖ ^ 2 from funext e]
  have := (tendsto_const_nhds (x := ∑' m, sobWeight m * ‖mFourierCoeff f m‖ ^ 2)).sub h1
  rwa [sub_self] at this

theorem trigPoly_box_sub {R S : ℕ} (hRS : R ≤ S) (c : (Fin 4 → ℤ) → ℂ) :
    trigPoly (TorusSobolev.box S) c - trigPoly (TorusSobolev.box R) c =
      trigPoly (TorusSobolev.box S) (fun m => if m ∈ TorusSobolev.box R then 0 else c m) := by
  have hsub : (TorusSobolev.box R : Finset (Fin 4 → ℤ)) ⊆ TorusSobolev.box S := box_mono hRS
  unfold trigPoly
  have h : ∀ m : Fin 4 → ℤ, (if m ∈ TorusSobolev.box R then 0 else c m) • mFourier m =
      c m • mFourier m - (if m ∈ TorusSobolev.box R then c m • mFourier m else 0) := by
    intro m; split_ifs
    · rw [sub_self]; exact zero_smul ℂ (mFourier m)
    · rw [sub_zero]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]

theorem sum_sq_le_h1Tail (f : L²(UnitAddTorus (Fin 4))) (hf : MemH 1 f) (R S : ℕ)
    (w : (Fin 4 → ℤ) → ℂ) (hw : ∀ m, ‖w m‖ ^ 2 ≤ sobWeight m) :
    ∑ m ∈ TorusSobolev.box S, ‖w m * (if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m)‖ ^ 2 ≤ h1Tail f R := by
  have hs := summable_h1 hf
  have hs' : Summable fun m =>
      if m ∈ TorusSobolev.box R then (0 : ℝ) else sobWeight m * ‖mFourierCoeff f m‖ ^ 2 :=
    summable_ite_compl hs (TorusSobolev.box R)
  refine le_trans ?_ (hs'.sum_le_tsum (TorusSobolev.box S) (fun m _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sobWeight_nonneg' m) (sq_nonneg _)))
  refine Finset.sum_le_sum fun m _ => ?_
  split_ifs
  · simp
  · rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hw m) (sq_nonneg _)

theorem norm_symbol_sq_le (μ : Fin 4) (m : Fin 4 → ℤ) :
    ‖(2 * π * Complex.I * m μ : ℂ)‖ ^ 2 ≤ sobWeight m := by
  rw [TorusSobolev.norm_symbol_sq]
  unfold sobWeight
  have := TorusSobolev.sq_le_sum_sq m μ
  nlinarith [Real.pi_pos]

theorem one_le_sobWeight (m : Fin 4 → ℤ) : ‖(1 : ℂ)‖ ^ 2 ≤ sobWeight m := by
  unfold sobWeight; simp; positivity

/-- **The critical embedding `H¹(𝕋⁴) ⊂ L⁴`**: for `f ∈ H¹(𝕋⁴)`, `f ∈ L⁴` and the Fourier
truncations `Σ_{m ∈ TorusSobolev.box R} f̂(m) e_m` converge to `f` strongly in `L⁴`; quantitatively
`‖f - Σ_{TorusSobolev.box R}‖_{L⁴} ≤ 16 (Σ_{m ∉ TorusSobolev.box R} ⟨m⟩² |f̂(m)|²)^{1/2}`. -/
theorem tendsto_eLpNorm_four_trunc {f : L²(UnitAddTorus (Fin 4))} (hf : MemH 1 f) :
    MemLp (f : UnitAddTorus (Fin 4) → ℂ) 4 volume ∧
      Tendsto (fun R : ℕ => eLpNorm (fun y => trigPoly (TorusSobolev.box R) (mFourierCoeff f) y - f y) 4 volume)
        atTop (𝓝 0) := by
  -- the bound on the differences of truncations
  have hdiff : ∀ R S, R ≤ S → eLpNorm (fun y => trigPoly (TorusSobolev.box S) (mFourierCoeff f) y -
      trigPoly (TorusSobolev.box R) (mFourierCoeff f) y) 4 volume ≤ ENNReal.ofReal (16 * √(h1Tail f R)) := by
    intro R S hRS
    have e : (fun y => trigPoly (TorusSobolev.box S) (mFourierCoeff f) y - trigPoly (TorusSobolev.box R) (mFourierCoeff f) y) =
        ⇑(trigPoly (TorusSobolev.box S) (fun m => if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m)) := by
      rw [← trigPoly_box_sub hRS]; rfl
    rw [e]
    refine (eLpNorm_four_trigPoly_le _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hb : ∀ w : (Fin 4 → ℤ) → ℂ, (∀ m, ‖w m‖ ^ 2 ≤ sobWeight m) →
        ‖ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box S)
          (fun m => w m * (if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m)))‖ ≤ √(h1Tail f R) := by
      intro w hw
      rw [← Real.sqrt_sq (norm_nonneg _), norm_toLp_trigPoly_sq]
      exact Real.sqrt_le_sqrt (sum_sq_le_h1Tail f hf R S w hw)
    have h1 : ∀ μ, ‖ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box S)
        (fun m => 2 * π * Complex.I * m μ * (if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m)))‖ ≤
        √(h1Tail f R) := fun μ => hb _ (norm_symbol_sq_le μ)
    have h2 : ‖ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box S)
        (fun m => if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m))‖ ≤ √(h1Tail f R) := by
      have := hb (fun _ => 1) (fun m => one_le_sobWeight m)
      simpa using this
    have hsum : ∑ μ : Fin 4, ‖ContinuousMap.toLp 2 volume ℂ (trigPoly (TorusSobolev.box S)
        (fun m => 2 * π * Complex.I * m μ * (if m ∈ TorusSobolev.box R then 0 else mFourierCoeff f m)))‖ ≤
        4 * √(h1Tail f R) := by
      calc _ ≤ ∑ _μ : Fin 4, √(h1Tail f R) := Finset.sum_le_sum fun μ _ => h1 μ
        _ = 4 * √(h1Tail f R) := by simp
    linarith
  -- passing to the limit `S → ∞`
  have hbound : ∀ R, eLpNorm (fun y => f y - trigPoly (TorusSobolev.box R) (mFourierCoeff f) y) 4 volume ≤
      ENNReal.ofReal (16 * √(h1Tail f R)) := by
    intro R
    have hconv : LpTendsto volume 2 (fun S y => trigPoly (TorusSobolev.box (S + R)) (mFourierCoeff f) y -
        trigPoly (TorusSobolev.box R) (mFourierCoeff f) y)
        (fun y => f y - trigPoly (TorusSobolev.box R) (mFourierCoeff f) y) := by
      refine ⟨fun S => ?_, (Lp.memLp f).sub (memLp_continuousMap _ 2), ?_⟩
      · exact (memLp_continuousMap _ 2).sub (memLp_continuousMap _ 2)
      · have h := (tendsto_norm_sub_trigPoly_box f).comp (tendsto_add_atTop_nat R)
        have e : ∀ S, eLpNorm ((fun y => trigPoly (TorusSobolev.box (S + R)) (mFourierCoeff f) y -
            trigPoly (TorusSobolev.box R) (mFourierCoeff f) y) -
              fun y => f y - trigPoly (TorusSobolev.box R) (mFourierCoeff f) y)
            2 volume = ENNReal.ofReal ‖f - ContinuousMap.toLp 2 volume ℂ
              (trigPoly (TorusSobolev.box (S + R)) (mFourierCoeff f))‖ := by
          intro S
          rw [← TorusSobolev.eLpNorm_coe_sub_eq, ← eLpNorm_neg]
          refine eLpNorm_congr_ae ?_
          filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
            (trigPoly (TorusSobolev.box (S + R)) (mFourierCoeff f))] with y hy
          simp only [Pi.sub_apply, Pi.neg_apply, hy]
          abel
        simp only [e]
        simpa using ENNReal.tendsto_ofReal h
    exact hconv.eLpNorm_le_of_bound (by norm_num) fun S => hdiff R (S + R) (Nat.le_add_left R S)
  refine ⟨?_, ?_⟩
  · have h0 : MemLp (fun y => f y - trigPoly (TorusSobolev.box 0) (mFourierCoeff f) y) 4 volume :=
      ⟨(Lp.memLp f).1.sub (trigPoly (TorusSobolev.box 0) (mFourierCoeff f)).continuous.aestronglyMeasurable,
        (hbound 0).trans_lt ENNReal.ofReal_lt_top⟩
    have := h0.add (memLp_continuousMap (trigPoly (TorusSobolev.box 0) (mFourierCoeff f)) 4)
    refine this.ae_eq (Eventually.of_forall fun y => ?_)
    simp
  · have hlim : Tendsto (fun R => ENNReal.ofReal (16 * √(h1Tail f R))) atTop (𝓝 0) := by
      have := ((tendsto_h1Tail hf).sqrt.const_mul 16)
      simpa using ENNReal.tendsto_ofReal this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun R => zero_le)
      fun R => ?_
    rw [← eLpNorm_neg]
    refine le_trans (le_of_eq ?_) (hbound R)
    congr 1; funext y; simp

end Critical

/-! ### Vector-valued trigonometric polynomials as `C¹` gauge tests -/

section VTrig

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The vector-valued trigonometric polynomial `Σ_{m ∈ S} e_m a_m`. -/
def vtrig (S : Finset (Fin 4 → ℤ)) (a : (Fin 4 → ℤ) → F) : C(UnitAddTorus (Fin 4), F) where
  toFun y := ∑ m ∈ S, mFourier m y • a m
  continuous_toFun := continuous_finset_sum _ fun m _ => (mFourier m).continuous.smul continuous_const

theorem vtrig_apply (S : Finset (Fin 4 → ℤ)) (a : (Fin 4 → ℤ) → F) (y : UnitAddTorus (Fin 4)) :
    vtrig S a y = ∑ m ∈ S, mFourier m y • a m := rfl

/-- The derivative coefficients `(2πi m_μ) a_m`. -/
def dco (μ : Fin 4) (a : (Fin 4 → ℤ) → F) : (Fin 4 → ℤ) → F :=
  fun m => (2 * π * Complex.I * m μ) • a m

theorem hasDerivAt_exp_line (w : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * w)) w 0 := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) (1 * w) 0 :=
    (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const w
  have h2 := h1.cexp
  simpa using h2

theorem mFourier_add_coordPt (m : Fin 4 → ℤ) (y : UnitAddTorus (Fin 4)) (μ : Fin 4) (s : ℝ) :
    mFourier m (y + KolmogorovRieszTorus.coordPt μ s) =
      mFourier m y * Complex.exp ((s : ℂ) * (2 * π * Complex.I * m μ)) := by
  rw [KolmogorovRieszTorus.mFourier_add_apply, KolmogorovRieszTorus.mFourier_coordPt]
  congr 2
  push_cast
  ring

/-- The coordinate-line derivative of a vector trigonometric polynomial. -/
theorem hasDerivAt_vtrig_line (S : Finset (Fin 4 → ℤ)) (a : (Fin 4 → ℤ) → F) (μ : Fin 4)
    (y : UnitAddTorus (Fin 4)) :
    HasDerivAt (fun s : ℝ => vtrig S a (y + KolmogorovRieszTorus.coordPt μ s))
      (vtrig S (dco μ a) y) 0 := by
  simp only [vtrig_apply, mFourier_add_coordPt, dco]
  refine HasDerivAt.fun_sum fun m _ => ?_
  have h := ((hasDerivAt_exp_line (2 * π * Complex.I * m μ)).const_mul (mFourier m y)).smul_const
    (a m)
  convert h using 1
  rw [smul_smul, mul_comm (mFourier m y)]

/-- The `C¹` gauge test defined by vector trigonometric polynomials `a_ν = Σ_{m∈S} e_m a_{ν,m}`. -/
def vtrigTest (S : Finset (Fin 4 → ℤ)) (a : Fin 4 → (Fin 4 → ℤ) → F) : C1Test F where
  a := fun ν => vtrig S (a ν)
  da := fun μ ν => vtrig S (dco μ (a ν))
  hasDerivAt := fun μ ν y => hasDerivAt_vtrig_line S (a ν) μ y

end VTrig

end

end RenewalGeometry.NativeCoulomb
