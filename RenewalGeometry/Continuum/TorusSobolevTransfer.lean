/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridCompositionConsistency
import RenewalGeometry.DiscreteAnalysis.PeriodicGridMoserComposition

/-!
# Grid-to-continuum transfer of Sobolev estimates on `𝕋³`
  (continuum layer of `lem:supp-open-continuum-comparison`, `thm:supp-open-einstein`;
  emergent-spacetime manuscript)

The trigonometric Sobolev norms `‖f‖²_{H^r} = trigSobSq r f = Σ_n W_r(n) |f̂(n)|²` on the unit
torus `𝕋³ = UnitAddTorus (Fin 3)` are compared with the grid norms `‖·‖_{r,h}` of
`PeriodicGridSobolevCalculus` through grid sampling `𝒮_h` and the trigonometric interpolant
`𝓘_h` (`𝒫_h = 𝓘_h 𝒮_h`).

* `norm_dft_le`, `dft_sample_mFourier`, `freqVec_zcast`: elementary facts on the DFT of samples.
* `tendsto_dft_sample` (**Riemann-sum convergence of the discrete Fourier coefficients**): for
  every continuous `F` and every `n ∈ ℤ³`, the grid Fourier coefficient of `𝒮_h F` at `n mod N`
  tends to `F̂(n)` as `N → ∞`.  Proof by density of trigonometric polynomials
  (`span_mFourier_closure_eq_top`), exactness on single modes, and the uniform bounds
  `|dft| ≤ ‖F‖_∞`, `|F̂(n)| ≤ ‖F‖_∞`.
* `trigSobSq_le_of_proj_le` (**Fatou transfer**): if `‖𝒫_h F‖²_{H^r} ≤ B` for every mesh, then
  `F ∈ H^r` and `‖F‖²_{H^r} ≤ B`.  Every mesh-uniform grid estimate for sampled continuous
  functions therefore passes to the continuum, with no a priori summability (`transfer_of_grid`).
* Continuum calculus for general continuous fields (not only trigonometric polynomials): the
  product algebra `memH_mul` (`r ≥ 2`), the embedding `H² ⊂ C⁰` (`norm_apply_le_sn_two`), and the
  **continuum Moser estimates** `cont_moser`, `cont_moser_lipschitz` for analytic compositions
  `A(c + Q)` of `E`-valued fields (coordinates in a basis), all transferred from the grid.
* Classical coordinate derivatives on `𝕋³`: `IsLineDeriv` (`t ↦ F(x + t eᵢ)` differentiable),
  the translation rule `mFourierCoeff_comp_add`, the **Fourier rule of a classical derivative**
  `mFourierCoeff_of_isLineDeriv` (`F̂'(n) = 2πi nᵢ F̂(n)`, by dominated convergence), the cost of a
  derivative `memH_of_isLineDeriv`, and product/chain rules (`IsLineDeriv.mul`, `IsLineDeriv.comp`).
* Grid points as torus points (`samplePt_add`, `samplePt_add_unit`) and the **sampled difference
  consistency** `sample_Dp_sub_le`, `sample_Dm_sub_le`, `sample_D0_sub_le`:
  `‖D_i 𝒮_h F - 𝒮_h ∂ᵢF‖_{r,h} ≤ C h ‖F‖_{H^{r+2}}` for continuous `F` with classical derivative.
-/

open Finset Filter Topology ComplexConjugate UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.TorusSobolevTransfer

open PeriodicGridSobolev LatticeTorusPlancherel Sampling Composition

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

/-- The `H^r(𝕋³)` membership predicate: summable weighted squared Fourier coefficients. -/
abbrev MemH (r : ℕ) (f : UnitAddTorus (Fin 3) → ℂ) : Prop :=
  Summable fun n => trigWeight r n * ‖mFourierCoeff f n‖ ^ 2

/-! ### The DFT of samples -/

section DFT

variable {N : ℕ} [NeZero N]

theorem card_grid : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 3 := by
  simp [PeriodicGridSobolev.Grid, LatticeTorusPlancherel.Grid, ZMod.card]

theorem norm_dft_le (u : Grid N → ℂ) (M : ℝ) (hu : ∀ x, ‖u x‖ ≤ M) (k : Grid N) :
    ‖dft u k‖ ≤ M := by
  have hN : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  unfold dft
  rw [norm_smul]
  have h1 : ‖∑ x, conj (latticeChar k x) • u x‖ ≤ ∑ _x : Grid N, M := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
    rw [norm_smul, Complex.norm_conj, norm_latticeChar, one_mul]
    exact hu x
  rw [sum_const, card_univ, nsmul_eq_mul, card_grid] at h1
  have e : ‖((N : ℂ) ^ 3)⁻¹‖ = ((N : ℝ) ^ 3)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [e]
  calc ((N : ℝ) ^ 3)⁻¹ * ‖∑ x, conj (latticeChar k x) • u x‖
      ≤ ((N : ℝ) ^ 3)⁻¹ * ((N : ℝ) ^ 3 * M) := by gcongr
    _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]

theorem norm_dft_sample_le (F : C(UnitAddTorus (Fin 3), ℂ)) (k : Grid N) :
    ‖dft (sample N ⇑F) k‖ ≤ ‖F‖ :=
  norm_dft_le _ _ (fun x => F.norm_coe_le_norm _) k

theorem sample_add (F G : UnitAddTorus (Fin 3) → ℂ) :
    sample N (F + G) = sample N F + sample N G := rfl

theorem sample_sub (F G : UnitAddTorus (Fin 3) → ℂ) :
    sample N (F - G) = sample N F - sample N G := rfl

theorem sample_smul (c : ℂ) (F : UnitAddTorus (Fin 3) → ℂ) :
    sample N (c • F) = c • sample N F := rfl

theorem sample_mul (F G : UnitAddTorus (Fin 3) → ℂ) :
    sample N (F * G) = sample N F * sample N G := rfl

theorem dft_sample_mFourier (m : Fin 3 → ℤ) (k : Grid N) :
    dft (sample N ⇑(mFourier m)) k = if zcast N m = k then 1 else 0 := by
  have e : sample N ⇑(mFourier m) = fun x => latticeChar (zcast N m) x :=
    funext fun x => mFourier_samplePt_eq m x
  rw [e, dft_latticeChar]

theorem mFourierCoeff_mFourier (m n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(mFourier m) n = if m = n then 1 else 0 := by
  have h := mFourierCoeff_trigSum ({m} : Finset (Fin 3 → ℤ)) (fun _ => (1 : ℂ)) id n
  simp only [Finset.sum_singleton, one_smul, id] at h
  exact h

/-- A small integer is determined by its residue. -/
theorem int_eq_of_cast_eq {a b : ℤ} (ha : 2 * |a| < N) (hb : 2 * |b| < N)
    (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
  have hd : (N : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp h
  have hlt : |b - a| < N := by
    have := abs_sub b a
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

theorem zcast_eq_iff (m n : Fin 3 → ℤ) (hm : ∀ i, 2 * |m i| < N) (hn : ∀ i, 2 * |n i| < N) :
    zcast N m = zcast N n ↔ m = n := by
  constructor
  · intro h
    funext i
    exact int_eq_of_cast_eq (hm i) (hn i) (congrFun h i)
  · rintro rfl; rfl

theorem freqVec_zcast (n : Fin 3 → ℤ) (hn : ∀ i, 2 * |n i| < N) : freqVec (zcast N n) = n := by
  funext i
  have hle : 2 * |freq i (zcast N n)| ≤ N := by
    unfold freq
    have := ZMod.natAbs_valMinAbs_le (n := N) (zcast N n i)
    have h2 : |((zcast N n i).valMinAbs : ℤ)| = (((zcast N n i).valMinAbs).natAbs : ℤ) :=
      Int.abs_eq_natAbs _
    rw [h2]
    have : 2 * ((zcast N n i).valMinAbs.natAbs) ≤ N := by omega
    exact_mod_cast this
  have hd := dvd_sub_freq_zcast (N := N) n i
  have hlt : |n i - freq i (zcast N n)| < N := by
    have := abs_sub (n i) (freq i (zcast N n))
    have := hn i
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  show freq i (zcast N n) = n i
  linarith

end DFT

/-! ### Riemann-sum convergence of the discrete Fourier coefficients -/

/-- On a trigonometric polynomial (an element of the span of the modes), the DFT of the samples at
`n mod N` is eventually exactly `P̂(n)`. -/
theorem eventually_dft_sample_eq_of_mem_span (n : Fin 3 → ℤ) (P : C(UnitAddTorus (Fin 3), ℂ))
    (hP : P ∈ Submodule.span ℂ (Set.range (mFourier (d := Fin 3)))) :
    ∀ᶠ N : ℕ in atTop, dft (sample (N + 1) ⇑P) (zcast (N + 1) n) = mFourierCoeff ⇑P n := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    set M : ℕ := 2 * (∑ i, (m i).natAbs + ∑ i, (n i).natAbs) + 1
    refine eventually_atTop.mpr ⟨M, fun N hN => ?_⟩
    have hsmall : ∀ (a : Fin 3 → ℤ), (∑ i, (a i).natAbs ≤ ∑ i, (m i).natAbs + ∑ i, (n i).natAbs)
        → ∀ i, 2 * |a i| < ((N + 1 : ℕ) : ℤ) := by
      intro a ha i
      have h1 : (a i).natAbs ≤ ∑ i, (a i).natAbs :=
        single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
      have h2 : 2 * (a i).natAbs < N + 1 := by omega
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
    rw [dft_sample_mFourier, mFourierCoeff_mFourier]
    have hiff := zcast_eq_iff (N := N + 1) m n (hsmall m (by omega)) (hsmall n (by omega))
    by_cases hmn : m = n
    · rw [if_pos (hiff.mpr hmn), if_pos hmn]
    · rw [if_neg (mt hiff.mp hmn), if_neg hmn]
  | zero =>
    refine Eventually.of_forall fun N => ?_
    have e : sample (N + 1) ⇑(0 : C(UnitAddTorus (Fin 3), ℂ)) = 0 := rfl
    rw [e]
    have h0 : mFourierCoeff ⇑(0 : C(UnitAddTorus (Fin 3), ℂ)) n = 0 := by
      simpa using mFourierCoeff_smul' 0 (0 : C(UnitAddTorus (Fin 3), ℂ)) n
    rw [h0]
    simp [dft]
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with N h1 h2
    have e : sample (N + 1) ⇑(x + y) = sample (N + 1) ⇑x + sample (N + 1) ⇑y := rfl
    rw [e, dft_add, h1, h2, mFourierCoeff_add]
  | smul c x _ hx =>
    filter_upwards [hx] with N h1
    have e : sample (N + 1) ⇑(c • x) = c • sample (N + 1) ⇑x := rfl
    rw [e, dft_smul, h1, mFourierCoeff_smul']

/-- **Riemann-sum convergence of the discrete Fourier coefficients.**  For every continuous `F` on
`𝕋³` and every `n ∈ ℤ³`, `dft(𝒮_h F)(n mod N) → F̂(n)` as `N → ∞`. -/
theorem tendsto_dft_sample (F : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    Tendsto (fun N : ℕ => dft (sample (N + 1) ⇑F) (zcast (N + 1) n)) atTop
      (𝓝 (mFourierCoeff ⇑F n)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : F ∈ (Submodule.span ℂ (Set.range (mFourier (d := Fin 3)))).topologicalClosure := by
    rw [span_mFourier_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hF
  obtain ⟨P, hP, hFP⟩ := hF (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_dft_sample_eq_of_mem_span n P hP)
  refine ⟨N₀, fun N hN => ?_⟩
  rw [dist_eq_norm] at hFP ⊢
  have e : dft (sample (N + 1) ⇑F) (zcast (N + 1) n) - mFourierCoeff ⇑F n =
      dft (sample (N + 1) ⇑(F - P)) (zcast (N + 1) n) +
        (dft (sample (N + 1) ⇑P) (zcast (N + 1) n) - mFourierCoeff ⇑P n) +
        mFourierCoeff ⇑(P - F) n := by
    have e1 : sample (N + 1) ⇑(F - P) = sample (N + 1) ⇑F - sample (N + 1) ⇑P := rfl
    rw [e1, dft_sub, mFourierCoeff_sub]
    ring
  rw [e, hN₀ N hN, sub_self, add_zero]
  have h1 := norm_dft_sample_le (N := N + 1) (F - P) (zcast (N + 1) n)
  have h2 := norm_mFourierCoeff_le (P - F) n
  have h3 : ‖P - F‖ = ‖F - P‖ := norm_sub_rev _ _
  calc ‖dft (sample (N + 1) ⇑(F - P)) (zcast (N + 1) n) + mFourierCoeff ⇑(P - F) n‖
      ≤ ‖F - P‖ + ‖F - P‖ := (norm_add_le _ _).trans (add_le_add h1 (h2.trans h3.le))
    _ < ε := by linarith

/-! ### Fatou transfer -/

/-- **Fatou transfer.**  If the sampling projections of a continuous `F` obey a mesh-uniform bound
`‖𝒫_h F‖²_{H^r} ≤ B`, then `F ∈ H^r(𝕋³)` and `‖F‖²_{H^r} ≤ B`. -/
theorem trigSobSq_le_of_proj_le (r : ℕ) (F : C(UnitAddTorus (Fin 3), ℂ)) (B : ℝ)
    (h : ∀ N : ℕ, trigSobSq r ⇑(proj (N + 1) ⇑F) ≤ B) :
    MemH r ⇑F ∧ trigSobSq r ⇑F ≤ B := by
  have hfin : ∀ S : Finset (Fin 3 → ℤ),
      ∑ n ∈ S, trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 ≤ B := by
    intro S
    have hlim : Tendsto (fun N : ℕ => ∑ n ∈ S, trigWeight r n *
        ‖dft (sample (N + 1) ⇑F) (zcast (N + 1) n)‖ ^ 2) atTop
        (𝓝 (∑ n ∈ S, trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2)) :=
      tendsto_finsetSum _ fun n _ =>
        ((tendsto_dft_sample F n).norm.pow 2).const_mul _
    refine le_of_tendsto hlim (eventually_atTop.mpr ⟨2 * ∑ n ∈ S, ∑ i, (n i).natAbs + 1,
      fun N hN => ?_⟩)
    have hsmall : ∀ n ∈ S, ∀ i, 2 * |n i| < ((N + 1 : ℕ) : ℤ) := by
      intro n hn i
      have h1 : (n i).natAbs ≤ ∑ i, (n i).natAbs :=
        single_le_sum (f := fun i => (n i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
      have h2 : ∑ i, (n i).natAbs ≤ ∑ n ∈ S, ∑ i, (n i).natAbs :=
        single_le_sum (f := fun n => ∑ i, (n i).natAbs) (fun _ _ => Nat.zero_le _) hn
      rw [Int.abs_eq_natAbs]
      have : 2 * (n i).natAbs < N + 1 := by omega
      exact_mod_cast this
    have hinj : Set.InjOn (zcast (N + 1)) (S : Set (Fin 3 → ℤ)) := by
      intro a ha b hb hab
      exact (zcast_eq_iff a b (hsmall a ha) (hsmall b hb)).mp hab
    calc ∑ n ∈ S, trigWeight r n * ‖dft (sample (N + 1) ⇑F) (zcast (N + 1) n)‖ ^ 2
        = ∑ k ∈ S.image (zcast (N + 1)), trigWeight r (freqVec k) *
            ‖dft (sample (N + 1) ⇑F) k‖ ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun n hn => ?_
          rw [freqVec_zcast n (hsmall n hn)]
      _ ≤ ∑ k, trigWeight r (freqVec k) * ‖dft (sample (N + 1) ⇑F) k‖ ^ 2 :=
          sum_le_univ_sum_of_nonneg fun k =>
            mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
      _ = trigSobSq r ⇑(proj (N + 1) ⇑F) := (trigSobSq_interp r _).symm
      _ ≤ B := h N
  have hnn : ∀ n, 0 ≤ trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2 := fun n =>
    mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)
  have hs : MemH r ⇑F := summable_of_sum_le hnn hfin
  exact ⟨hs, tsum_le_of_sum_le' (by simpa using hfin ∅) hfin⟩

/-! ### Sampling norms and the transfer of grid bounds -/

/-- Shorthand for continuous complex functions on `𝕋³`. -/
abbrev CT := C(UnitAddTorus (Fin 3), ℂ)

/-- The norm-equivalence constant `(π/2)^{2r}`. -/
def pc (r : ℕ) : ℝ := ((π / 2) ^ 2) ^ r

theorem pc_pos (r : ℕ) : 0 < pc r := by unfold pc; positivity

theorem trigSobSq_proj_le_sobSq {N : ℕ} [NeZero N] (r : ℕ) (F : UnitAddTorus (Fin 3) → ℂ) :
    trigSobSq r ⇑(proj N F) ≤ pc r * sobSq r (sample N F) := by
  have h := trigSobSq_interp_le_sobSq r (sample N F)
  have hc : ((2 / π) ^ 2) ^ r * pc r = 1 := by
    unfold pc
    rw [← mul_pow, ← mul_pow, div_mul_div_comm, mul_comm (2 : ℝ) π,
      div_self (by positivity), one_pow, one_pow]
  calc trigSobSq r ⇑(proj N F)
      = pc r * (((2 / π) ^ 2) ^ r * trigSobSq r ⇑(interp (sample N F))) := by
        rw [← mul_assoc, mul_comm (pc r), hc, one_mul]; rfl
    _ ≤ pc r * sobSq r (sample N F) := mul_le_mul_of_nonneg_left h (pc_pos r).le

/-- **Transfer of a mesh-uniform grid bound**: if `‖𝒮_h F‖²_{r,h} ≤ B` for every mesh, then
`F ∈ H^r` and `‖F‖²_{H^r} ≤ (π/2)^{2r} B`. -/
theorem transfer_of_grid (r : ℕ) (F : CT) (B : ℝ)
    (h : ∀ N : ℕ, sobSq r (sample (N + 1) ⇑F) ≤ B) :
    MemH r ⇑F ∧ trigSobSq r ⇑F ≤ pc r * B :=
  trigSobSq_le_of_proj_le r F _ fun N =>
    (trigSobSq_proj_le_sobSq r _).trans (mul_le_mul_of_nonneg_left (h N) (pc_pos r).le)

/-- Sampling is mesh-uniformly bounded `H^r → H^r_h` for `r ≥ 2`. -/
theorem sobSq_sample_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (F : CT), MemH r ⇑F →
      sobSq r (sample N ⇑F) ≤ C * trigSobSq r ⇑F := by
  obtain ⟨C, hC, hs⟩ := sampling_stable r hr
  exact ⟨C, hC, fun N _ F hF => (sobSq_le_trigSobSq_interp r _).trans (hs N F hF).2⟩

theorem sobNorm_sample_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (F : CT), MemH r ⇑F →
      sobNorm r (sample N ⇑F) ≤ C * sn r ⇑F := by
  obtain ⟨C, hC, hs⟩ := sobSq_sample_le r hr
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun N _ F hF => ?_⟩
  unfold sobNorm sn
  rw [← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hs N F hF)

theorem trigSobSq_nonneg (r : ℕ) (F : UnitAddTorus (Fin 3) → ℂ) : 0 ≤ trigSobSq r F :=
  trigSobSq_nonneg' r F

theorem sn_sq (r : ℕ) (F : UnitAddTorus (Fin 3) → ℂ) : sn r F ^ 2 = trigSobSq r F :=
  Real.sq_sqrt (trigSobSq_nonneg r F)

/-- Square-root form of the transfer. -/
theorem transfer_of_grid_norm (r : ℕ) (F : CT) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ N : ℕ, sobNorm r (sample (N + 1) ⇑F) ≤ B) :
    MemH r ⇑F ∧ sn r ⇑F ≤ Real.sqrt (pc r) * B := by
  obtain ⟨h1, h2⟩ := transfer_of_grid r F (B ^ 2) fun N => by
    rw [← sobNorm_sq]
    exact pow_le_pow_left₀ (Moser.sobNorm_nonneg _ _) (h N) 2
  refine ⟨h1, ?_⟩
  unfold sn
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (pc_pos r).le]
  exact Real.sqrt_le_sqrt h2

/-! ### Continuum algebra and embedding -/

theorem memH_add {r : ℕ} {F G : CT} (hF : MemH r ⇑F) (hG : MemH r ⇑G) : MemH r ⇑(F + G) :=
  (trigSobSq_add_le r F G hF hG).1

theorem memH_smul {r : ℕ} (c : ℂ) {F : CT} (hF : MemH r ⇑F) : MemH r ⇑(c • F) := by
  unfold MemH
  have e : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑(c • F) n‖ ^ 2 =
      ‖c‖ ^ 2 * (trigWeight r n * ‖mFourierCoeff ⇑F n‖ ^ 2) := by
    intro n; rw [mFourierCoeff_smul', smul_eq_mul, norm_mul]; ring
  simp only [e]
  exact hF.mul_left _

theorem memH_neg {r : ℕ} {F : CT} (hF : MemH r ⇑F) : MemH r ⇑(-F) := by
  have := memH_smul (-1) hF
  simpa using this

theorem memH_sub {r : ℕ} {F G : CT} (hF : MemH r ⇑F) (hG : MemH r ⇑G) : MemH r ⇑(F - G) := by
  rw [sub_eq_add_neg]; exact memH_add hF (memH_neg hG)

theorem mFourierCoeff_zero' (n : Fin 3 → ℤ) :
    mFourierCoeff (0 : UnitAddTorus (Fin 3) → ℂ) n = 0 := by
  simp [mFourierCoeff]

theorem memH_zero (r : ℕ) : MemH r ⇑(0 : CT) := by
  unfold MemH
  simp only [ContinuousMap.coe_zero, mFourierCoeff_zero', norm_zero]
  simpa using summable_zero

theorem memH_mono {r r' : ℕ} (h : r ≤ r') {F : CT} (hF : MemH r' ⇑F) : MemH r ⇑F :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (trigWeight_mono h n) (sq_nonneg _)) hF

theorem sn_mono' {r r' : ℕ} (h : r ≤ r') {F : CT} (hF : MemH r' ⇑F) : sn r ⇑F ≤ sn r' ⇑F := by
  unfold sn trigSobSq
  exact Real.sqrt_le_sqrt ((memH_mono h hF).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (trigWeight_mono h n) (sq_nonneg _)) hF)

theorem sn_add_le' {r : ℕ} {F G : CT} (hF : MemH r ⇑F) (hG : MemH r ⇑G) :
    sn r ⇑(F + G) ≤ sn r ⇑F + sn r ⇑G := by
  have h := norm_add_le (wseq r F hF) (wseq r G hG)
  rw [← wseq_add r F G hF hG (memH_add hF hG), norm_wseq, norm_wseq, norm_wseq] at h
  exact h

theorem sn_neg (r : ℕ) (F : CT) : sn r ⇑(-F) = sn r ⇑F := by
  have := sn_smul r (-1) F
  simpa using this

theorem sn_sub_le' {r : ℕ} {F G : CT} (hF : MemH r ⇑F) (hG : MemH r ⇑G) :
    sn r ⇑(F - G) ≤ sn r ⇑F + sn r ⇑G := by
  rw [sub_eq_add_neg]
  exact (sn_add_le' hF (memH_neg hG)).trans (by rw [sn_neg])

/-- **Continuum product algebra** on `H^r(𝕋³)`, `r ≥ 2`, for continuous functions (no
trigonometric-polynomial restriction), transferred from the grid algebra. -/
theorem memH_mul (r : ℕ) (hr : 2 ≤ r) :
    ∃ K ≥ 0, ∀ F G : CT, MemH r ⇑F → MemH r ⇑G →
      MemH r ⇑(F * G) ∧ sn r ⇑(F * G) ≤ K * sn r ⇑F * sn r ⇑G := by
  obtain ⟨C, hC, hs⟩ := sobNorm_sample_le r hr
  set A := Moser.algConst r
  have hA := Moser.algConst_pos r
  refine ⟨Real.sqrt (pc r) * (A * C * C), by positivity, fun F G hF hG => ?_⟩
  have hFn := sn_nonneg r ⇑F
  have hGn := sn_nonneg r ⇑G
  obtain ⟨h1, h2⟩ := transfer_of_grid_norm r (F * G) (A * (C * sn r ⇑F) * (C * sn r ⇑G))
    (by positivity) fun N => by
      have e : sample (N + 1) ⇑(F * G) = sample (N + 1) ⇑F * sample (N + 1) ⇑G := rfl
      rw [e]
      refine (Moser.sobNorm_mul_le r hr _ _).trans ?_
      have hF' := hs (N + 1) F hF
      have hG' := hs (N + 1) G hG
      have := Moser.sobNorm_nonneg r (sample (N + 1) ⇑F)
      have := Moser.sobNorm_nonneg r (sample (N + 1) ⇑G)
      gcongr
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

theorem norm_mFourier_apply' (n : Fin 3 → ℤ) (x : UnitAddTorus (Fin 3)) :
    ‖mFourier n x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod]
  exact Finset.prod_eq_one fun i _ => by
    rw [fourier_apply]; exact Circle.norm_coe _

/-- **Uniform embedding `H² ⊂ C⁰`** for continuous functions:
`|F(x)| ≤ √c ‖F‖_{H²}`. -/
theorem norm_apply_le_sn_two (F : CT) (hF : MemH 2 ⇑F) (x : UnitAddTorus (Fin 3)) :
    ‖F x‖ ≤ Real.sqrt cEmb * sn 2 ⇑F := by
  have hsum : Summable (mFourierCoeff ⇑F) := summable_of_trigWeight le_rfl hF
  have hx := hasSum_mFourier_series_apply_of_summable hsum x
  have hW : ∀ n, 0 < trigWeight 2 n := fun n => trigWeight_pos 2 n
  obtain ⟨-, hb⟩ := norm_tsum_sq_le (fun n => mFourierCoeff ⇑F n • mFourier n x)
    (fun n => (trigWeight 2 n)⁻¹) (fun n => trigWeight 2 n * ‖mFourierCoeff ⇑F n‖ ^ 2)
    (fun n => (inv_pos.mpr (hW n)).le) (fun n => mul_nonneg (hW n).le (sq_nonneg _))
    (fun n => by
      rw [norm_smul, norm_mFourier_apply', mul_one, ← mul_assoc, inv_mul_cancel₀ (hW n).ne',
        one_mul])
    (summable_inv_trigWeight 2 le_rfl) hF
  rw [hx.tsum_eq] at hb
  have hb' : ‖F x‖ ^ 2 ≤ cEmb * trigSobSq 2 ⇑F := hb
  unfold sn
  rw [← Real.sqrt_mul cEmb_nonneg]
  exact Real.le_sqrt_of_sq_le hb'

theorem norm_apply_le_sn (r : ℕ) (hr : 2 ≤ r) (F : CT) (hF : MemH r ⇑F)
    (x : UnitAddTorus (Fin 3)) : ‖F x‖ ≤ Real.sqrt cEmb * sn r ⇑F :=
  (norm_apply_le_sn_two F (memH_mono hr hF) x).trans
    (mul_le_mul_of_nonneg_left (sn_mono' hr hF) (Real.sqrt_nonneg _))

/-! ### Continuum Moser estimates for analytic compositions -/

section Moser

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- The complexified `j`-th coordinate function `x ↦ b.repr (Q x) j` of a continuous `E`-valued
field on `𝕋³`. -/
def ccoord (b : Module.Basis ι ℝ E) (Q : C(UnitAddTorus (Fin 3), E)) (j : ι) : CT :=
  ⟨fun x => ((b.repr (Q x) j : ℝ) : ℂ), by
    have : FiniteDimensional ℝ E := Module.Finite.of_basis b
    have hc : Continuous fun v : E => b.repr v j := (b.coord j).continuous_of_finiteDimensional
    exact Complex.continuous_ofReal.comp (hc.comp Q.continuous)⟩

@[simp] theorem ccoord_apply (b : Module.Basis ι ℝ E) (Q : C(UnitAddTorus (Fin 3), E)) (j : ι)
    (x : UnitAddTorus (Fin 3)) : ccoord b Q j x = ((b.repr (Q x) j : ℝ) : ℂ) := rfl

/-- The continuum coordinate size `Σ_j ‖Q_j‖_{H^r}`. -/
def ccoordSum (r : ℕ) (b : Module.Basis ι ℝ E) (Q : C(UnitAddTorus (Fin 3), E)) : ℝ :=
  ∑ j, sn r ⇑(ccoord b Q j)

theorem ccoordSum_nonneg (r : ℕ) (b : Module.Basis ι ℝ E) (Q : C(UnitAddTorus (Fin 3), E)) :
    0 ≤ ccoordSum r b Q := sum_nonneg fun _ _ => sn_nonneg _ _

theorem ccoord_sub (b : Module.Basis ι ℝ E) (Q P : C(UnitAddTorus (Fin 3), E)) (j : ι) :
    ccoord b (Q - P) j = ccoord b Q j - ccoord b P j := by
  ext x; simp

theorem coordArr_sample {N : ℕ} [NeZero N] (b : Module.Basis ι ℝ E)
    (Q : C(UnitAddTorus (Fin 3), E)) (j : ι) :
    Moser.coordArr b (fun x : Grid N => Q (samplePt x)) j = sample N ⇑(ccoord b Q j) := rfl

theorem coordSum_sample_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (b : Module.Basis ι ℝ E) (Q : C(UnitAddTorus (Fin 3), E)),
      (∀ j, MemH r ⇑(ccoord b Q j)) →
      Moser.coordSum r b (fun x : Grid N => Q (samplePt x)) ≤ C * ccoordSum r b Q := by
  obtain ⟨C, hC, hs⟩ := sobNorm_sample_le r hr
  refine ⟨C, hC, fun N _ b Q hQ => ?_⟩
  unfold Moser.coordSum ccoordSum
  rw [mul_sum]
  exact sum_le_sum fun j _ => by rw [coordArr_sample]; exact hs N _ (hQ j)

theorem norm_le_ccoordSum (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {B : ℝ}
    (hB : ∀ j, ‖b j‖ ≤ B) (Q : C(UnitAddTorus (Fin 3), E)) (hQ : ∀ j, MemH r ⇑(ccoord b Q j))
    (x : UnitAddTorus (Fin 3)) : ‖Q x‖ ≤ B * (Real.sqrt cEmb * ccoordSum r b Q) := by
  calc ‖Q x‖ = ‖∑ j, b.repr (Q x) j • b j‖ := by rw [b.sum_repr]
    _ ≤ ∑ j, ‖ccoord b Q j x‖ * B := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_smul, ccoord_apply, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
    _ ≤ ∑ j, Real.sqrt cEmb * sn r ⇑(ccoord b Q j) * B := by
        refine sum_le_sum fun j _ => ?_
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB j)
        exact mul_le_mul_of_nonneg_right (norm_apply_le_sn r hr _ (hQ j) x) hB0
    _ = B * (Real.sqrt cEmb * ccoordSum r b Q) := by
        rw [ccoordSum, mul_sum, mul_sum]
        exact sum_congr rfl fun _ _ => by ring

/-- **Continuum Moser estimate**: for `A : E → ℝ` with a power series at `c` and `r ≥ 2` there
are `δ, C` such that every continuous field `Q` with coordinates in `H^r` and
`Σ_j ‖Q_j‖_{H^r} ≤ δ` stays in the ball of convergence, `A(c + Q) - A(c)` is continuous and in
`H^r`, and `‖A(c + Q) - A(c)‖_{H^r} ≤ C Σ_j ‖Q_j‖_{H^r}`. -/
theorem cont_moser (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ} {c : E}
    {p : FormalMultilinearSeries ℝ E ℝ} {R : ENNReal} (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ Q : C(UnitAddTorus (Fin 3), E), (∀ j, MemH r ⇑(ccoord b Q j)) →
      ccoordSum r b Q ≤ δ →
      (∀ x, c + Q x ∈ EMetric.ball c R) ∧
      ∃ F : CT, (∀ x, F x = ((A (c + Q x) - A c : ℝ) : ℂ)) ∧ MemH r ⇑F ∧
        sn r ⇑F ≤ C * ccoordSum r b Q := by
  obtain ⟨δg, hδg, Cg, hCg, hg⟩ := Moser.moser_composition r hr b hA
  obtain ⟨Cs, hCs, hs⟩ := coordSum_sample_le (E := E) (ι := ι) r hr
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hA.r_pos
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  set B : ℝ := 1 + ∑ j, ‖b j‖ with hBdef
  have hB : ∀ j, ‖b j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖b j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ j, ‖b j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have he := cEmb_nonneg
  set δ : ℝ := min (δg / (Cs + 1)) (ρ / (2 * (B * Real.sqrt cEmb + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, Real.sqrt (pc r) * (Cg * Cs), by positivity, fun Q hQ hQδ => ?_⟩
  have hS0 := ccoordSum_nonneg r b Q
  -- the field stays in the analytic ball
  have hball : ∀ x, c + Q x ∈ EMetric.ball c R := by
    intro x
    have h1 := norm_le_ccoordSum r hr b hB Q hQ x
    have h2 : B * (Real.sqrt cEmb * ccoordSum r b Q) ≤ B * (Real.sqrt cEmb * δ) := by
      gcongr
    have h3 : B * (Real.sqrt cEmb * δ) < ρ := by
      have hδ2 : δ ≤ ρ / (2 * (B * Real.sqrt cEmb + 1)) := min_le_right _ _
      have hpos : 0 < 2 * (B * Real.sqrt cEmb + 1) := by positivity
      rw [le_div_iff₀ hpos] at hδ2
      nlinarith [Real.sqrt_nonneg cEmb]
    change edist (c + Q x) c < R
    rw [edist_eq_enorm_sub, add_sub_cancel_left]
    refine lt_of_lt_of_le ?_ hρR.le
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hρ)).mpr (by linarith)
  refine ⟨hball, ?_⟩
  have hcont : Continuous fun x => ((A (c + Q x) - A c : ℝ) : ℂ) := by
    have h1 : Continuous fun x => A (c + Q x) :=
      hA.continuousOn.comp_continuous (continuous_const.add Q.continuous) hball
    exact Complex.continuous_ofReal.comp (h1.sub continuous_const)
  set F : CT := ⟨fun x => ((A (c + Q x) - A c : ℝ) : ℂ), hcont⟩
  refine ⟨F, fun x => rfl, ?_⟩
  obtain ⟨h1, h2⟩ := transfer_of_grid_norm r F (Cg * (Cs * ccoordSum r b Q)) (by positivity)
    fun N => by
      have hu := hs (N + 1) b Q hQ
      have hu' : Moser.coordSum r b (fun x : Grid (N + 1) => Q (samplePt x)) ≤ δg := by
        refine hu.trans ?_
        have : Cs * ccoordSum r b Q ≤ Cs * δ := mul_le_mul_of_nonneg_left hQδ hCs
        have h4 : Cs * δ ≤ δg := by
          have hδ1 : δ ≤ δg / (Cs + 1) := min_le_left _ _
          rw [le_div_iff₀ (by positivity)] at hδ1
          nlinarith
        linarith
      have := hg (N + 1) (fun x => Q (samplePt x)) hu'
      exact this.trans (mul_le_mul_of_nonneg_left hu hCg)
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

/-- **Lipschitz continuum Moser estimate**:
`‖A(c + Q) - A(c + P)‖_{H^r} ≤ C Σ_j ‖Q_j - P_j‖_{H^r}` on the small chart. -/
theorem cont_moser_lipschitz (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) {A : E → ℝ} {c : E}
    {p : FormalMultilinearSeries ℝ E ℝ} {R : ENNReal} (hA : HasFPowerSeriesOnBall A p c R) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ Q P : C(UnitAddTorus (Fin 3), E), (∀ j, MemH r ⇑(ccoord b Q j)) →
      (∀ j, MemH r ⇑(ccoord b P j)) → ccoordSum r b Q ≤ δ → ccoordSum r b P ≤ δ →
      ∃ F : CT, (∀ x, F x = ((A (c + Q x) - A (c + P x) : ℝ) : ℂ)) ∧ MemH r ⇑F ∧
        sn r ⇑F ≤ C * ccoordSum r b (Q - P) := by
  obtain ⟨δg, hδg, Cg, hCg, hg⟩ := Moser.moser_lipschitz r hr b hA
  obtain ⟨Cs, hCs, hs⟩ := coordSum_sample_le (E := E) (ι := ι) r hr
  obtain ⟨δ1, hδ1, C1, hC1, hm⟩ := cont_moser r hr b hA
  set δ : ℝ := min δ1 (δg / (Cs + 1))
  have hδ : 0 < δ := lt_min hδ1 (by positivity)
  refine ⟨δ, hδ, Real.sqrt (pc r) * (Cg * Cs), by positivity, fun Q P hQ hP hQδ hPδ => ?_⟩
  have hQb := (hm Q hQ (hQδ.trans (min_le_left _ _))).1
  have hPb := (hm P hP (hPδ.trans (min_le_left _ _))).1
  have hcont : Continuous fun x => ((A (c + Q x) - A (c + P x) : ℝ) : ℂ) := by
    have h1 : Continuous fun x => A (c + Q x) :=
      hA.continuousOn.comp_continuous (continuous_const.add Q.continuous) hQb
    have h2 : Continuous fun x => A (c + P x) :=
      hA.continuousOn.comp_continuous (continuous_const.add P.continuous) hPb
    exact Complex.continuous_ofReal.comp (h1.sub h2)
  set F : CT := ⟨fun x => ((A (c + Q x) - A (c + P x) : ℝ) : ℂ), hcont⟩
  refine ⟨F, fun x => rfl, ?_⟩
  have hQP : ∀ j, MemH r ⇑(ccoord b (Q - P) j) := fun j => by
    rw [ccoord_sub]; exact memH_sub (hQ j) (hP j)
  have hsmall : ∀ (W : C(UnitAddTorus (Fin 3), E)), (∀ j, MemH r ⇑(ccoord b W j)) →
      ccoordSum r b W ≤ δ → ∀ N : ℕ,
      Moser.coordSum r b (fun x : Grid (N + 1) => W (samplePt x)) ≤ δg := by
    intro W hW hWδ N
    refine (hs (N + 1) b W hW).trans ?_
    have : Cs * ccoordSum r b W ≤ Cs * δ := mul_le_mul_of_nonneg_left hWδ hCs
    have h4 : Cs * δ ≤ δg := by
      have hδ1 : δ ≤ δg / (Cs + 1) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at hδ1
      nlinarith
    linarith
  obtain ⟨h1, h2⟩ := transfer_of_grid_norm r F (Cg * (Cs * ccoordSum r b (Q - P)))
    (by have := ccoordSum_nonneg r b (Q - P); positivity) fun N => by
      have := hg (N + 1) (fun x => Q (samplePt x)) (fun x => P (samplePt x))
        (hsmall Q hQ hQδ N) (hsmall P hP hPδ N)
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hCg)
      exact hs (N + 1) b (Q - P) hQP
  exact ⟨h1, h2.trans (le_of_eq (by ring))⟩

end Moser

/-! ### Translations, line derivatives and their Fourier coefficients -/

theorem mFourier_add_apply (n : Fin 3 → ℤ) (x y : UnitAddTorus (Fin 3)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem mFourier_neg_neg (n : Fin 3 → ℤ) (a : UnitAddTorus (Fin 3)) :
    mFourier (-n) (-a) = mFourier n a := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, neg_smul, smul_neg, neg_neg]

theorem continuous_integrable {f : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f) :
    MeasureTheory.Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Fourier coefficients of a translate**: `(F(· + a))^(n) = e_n(a) F̂(n)`. -/
theorem mFourierCoeff_comp_add (F : UnitAddTorus (Fin 3) → ℂ) (a : UnitAddTorus (Fin 3))
    (n : Fin 3 → ℤ) :
    mFourierCoeff (fun x => F (x + a)) n = mFourier n a * mFourierCoeff F n := by
  unfold mFourierCoeff
  have key : ∫ x, mFourier (-n) x • F (x + a) = ∫ y, mFourier (-n) (y - a) • F y := by
    have := MeasureTheory.integral_add_left_eq_self
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin 3))))
      (fun y => mFourier (-n) (y - a) • F y) a
    have e1 : ∀ x, (fun y => mFourier (-n) (y - a) • F y) (a + x) =
        mFourier (-n) x • F (x + a) := by
      intro x; simp only [add_comm a x, add_sub_cancel_right]
    simp only [e1] at this
    exact this
  rw [key]
  have e : ∀ y, mFourier (-n) (y - a) • F y = mFourier n a • (mFourier (-n) y • F y) := by
    intro y
    rw [sub_eq_add_neg, mFourier_add_apply, mFourier_neg_neg, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  simp_rw [e]
  rw [MeasureTheory.integral_smul, smul_eq_mul]

/-- The coordinate line `t ↦ t e_i` in `𝕋³`. -/
def lineShift (i : Fin 3) (t : ℝ) : UnitAddTorus (Fin 3) := Pi.single i (t : UnitAddCircle)

theorem lineShift_add (i : Fin 3) (s t : ℝ) :
    lineShift i (s + t) = lineShift i s + lineShift i t := by
  unfold lineShift
  rw [← Pi.single_add]
  rfl

theorem lineShift_zero (i : Fin 3) : lineShift i 0 = 0 := by
  unfold lineShift
  simp

theorem mFourier_lineShift (n : Fin 3 → ℤ) (i : Fin 3) (t : ℝ) :
    mFourier n (lineShift i t) = Complex.exp (2 * π * Complex.I * n i * t) := by
  simp only [mFourier, ContinuousMap.coe_mk, lineShift]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, fourier_coe_apply]
    congr 1
    push_cast
    ring
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one]
  · intro h; exact absurd (mem_univ i) h

/-- `F'` is the classical partial derivative of `F` in the `i`-th coordinate direction:
`t ↦ F(x + t e_i)` has derivative `F'(x)` at `t = 0`, for every `x ∈ 𝕋³`. -/
def IsLineDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin 3)
    (F F' : UnitAddTorus (Fin 3) → E) : Prop :=
  ∀ x, HasDerivAt (fun t : ℝ => F (x + lineShift i t)) (F' x) 0

theorem IsLineDeriv.hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : Fin 3}
    {F F' : UnitAddTorus (Fin 3) → E} (h : IsLineDeriv i F F') (x : UnitAddTorus (Fin 3))
    (s : ℝ) : HasDerivAt (fun t : ℝ => F (x + lineShift i t)) (F' (x + lineShift i s)) s := by
  have h1 := h (x + lineShift i s)
  have h2 : HasDerivAt (fun t : ℝ => F (x + lineShift i s + lineShift i (t - s)))
      (F' (x + lineShift i s)) s := by
    have h1' : HasDerivAt (fun t : ℝ => F (x + lineShift i s + lineShift i t))
        (F' (x + lineShift i s)) (s - s) := by rw [sub_self]; exact h1
    exact h1'.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [add_assoc, ← lineShift_add, add_sub_cancel]

/-- **Fourier coefficients of a classical partial derivative**: if `F'` is the continuous line
derivative of the continuous function `F` in direction `i`, then `F̂'(n) = 2πi nᵢ F̂(n)`. -/
theorem mFourierCoeff_of_isLineDeriv (i : Fin 3) (F F' : CT) (h : IsLineDeriv i ⇑F ⇑F')
    (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑F' n = (2 * π * Complex.I * n i) * mFourierCoeff ⇑F n := by
  set c : ℂ := 2 * π * Complex.I * n i
  -- the integrands of the difference quotients
  set G : ℝ → UnitAddTorus (Fin 3) → ℂ := fun t x =>
    mFourier (-n) x • ((t : ℂ)⁻¹ * (F (x + lineShift i t) - F x))
  have hGint : ∀ t, t ≠ 0 → ∫ x, G t x = (t : ℂ)⁻¹ * (Complex.exp (c * t) - 1) *
      mFourierCoeff ⇑F n := by
    intro t _
    have hc1 : Continuous fun x => mFourier (-n) x • F (x + lineShift i t) :=
      (mFourier (-n)).continuous.smul (F.continuous.comp (continuous_id.add continuous_const))
    have hc2 : Continuous fun x => mFourier (-n) x • F x :=
      (mFourier (-n)).continuous.smul F.continuous
    have e : ∀ x, G t x = (t : ℂ)⁻¹ • (mFourier (-n) x • F (x + lineShift i t) -
        mFourier (-n) x • F x) := by
      intro x; simp only [G, smul_eq_mul]; ring
    simp_rw [e]
    rw [MeasureTheory.integral_smul, MeasureTheory.integral_sub (continuous_integrable hc1)
      (continuous_integrable hc2)]
    have h1 : ∫ x, mFourier (-n) x • F (x + lineShift i t) =
        mFourier n (lineShift i t) * mFourierCoeff ⇑F n :=
      mFourierCoeff_comp_add (⇑F) (lineShift i t) n
    have h2 : ∫ x, mFourier (-n) x • F x = mFourierCoeff ⇑F n := rfl
    rw [h1, h2, mFourier_lineShift, smul_eq_mul]
    simp only [c]
    ring_nf
  -- the limit of the right-hand side
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) c 0 := by
    have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
    simpa using h1.cexp
  have hR : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * (Complex.exp (c * t) - 1) * mFourierCoeff ⇑F n)
      (𝓝[≠] 0) (𝓝 (c * mFourierCoeff ⇑F n)) := by
    have hs := hexp.tendsto_slope_zero
    have e : ∀ t : ℝ, t⁻¹ • (Complex.exp (c * ↑(0 + t)) - Complex.exp (c * ↑(0 : ℝ))) =
        (t : ℂ)⁻¹ * (Complex.exp (c * t) - 1) := by
      intro t; simp [Complex.real_smul]
    simp only [e] at hs
    exact hs.mul_const _
  -- the limit of the left-hand side, by dominated convergence
  have hL : Tendsto (fun t : ℝ => ∫ x, G t x) (𝓝[≠] 0)
      (𝓝 (∫ x, mFourier (-n) x • F' x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => ‖F'‖)
      (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
      (MeasureTheory.integrable_const _) (Eventually.of_forall fun x => ?_)
    · exact (((mFourier (-n)).continuous.smul (continuous_const.mul
        ((F.continuous.comp (continuous_id.add continuous_const)).sub F.continuous))).aestronglyMeasurable)
    · refine Eventually.of_forall fun x => ?_
      simp only [G]
      rw [norm_smul, norm_mFourier_apply', one_mul]
      by_cases ht : t = 0
      · simp [ht]
      · have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun s : ℝ => F (x + lineShift i s)) (f' := fun s => F' (x + lineShift i s))
          (s := Set.univ) (x := 0) (y := t) (C := ‖F'‖)
          (fun s _ => (h.hasDerivAt x s).hasDerivWithinAt) (fun s _ => F'.norm_coe_le_norm _)
          convex_univ (Set.mem_univ _) (Set.mem_univ _)
        simp only [lineShift_zero, add_zero, sub_zero, Real.norm_eq_abs] at hmv
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        have hpos : 0 < |t| := abs_pos.mpr ht
        rw [inv_mul_le_iff₀ hpos, mul_comm]
        exact hmv
    · have hd := (h x).tendsto_slope_zero
      have e : ∀ t : ℝ, t⁻¹ • (F (x + lineShift i (0 + t)) - F (x + lineShift i 0)) =
          (t : ℂ)⁻¹ * (F (x + lineShift i t) - F x) := by
        intro t; simp [lineShift_zero, Complex.real_smul]
      simp only [e] at hd
      exact hd.const_smul _
  have hEq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ x, G t x =
      (t : ℂ)⁻¹ * (Complex.exp (c * t) - 1) * mFourierCoeff ⇑F n :=
    eventually_nhdsWithin_of_forall fun t ht => hGint t ht
  have hL' := hL.congr' hEq
  have := tendsto_nhds_unique hL' hR
  exact this

/-! ### Grid points as torus points -/

section GridPoints

variable {N : ℕ} [NeZero N]

theorem coe_intCast_unitAddCircle (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 := by
  have : ((k : ℝ)) = k • (1 : ℝ) := by simp
  rw [this, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

theorem coe_val_add (a b : ZMod N) :
    ((((a + b).val : ℝ) / N : ℝ) : UnitAddCircle) =
      (((a.val : ℝ) / N : ℝ) : UnitAddCircle) + (((b.val : ℝ) / N : ℝ) : UnitAddCircle) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [← AddCircle.coe_add, ZMod.val_add]
  have h := Nat.mod_add_div (a.val + b.val) N
  set q : ℕ := (a.val + b.val) / N
  set m : ℕ := (a.val + b.val) % N
  have e : (m : ℝ) / N = ((a.val : ℝ) / N + (b.val : ℝ) / N) - ((q : ℤ) : ℝ) := by
    have h' : (m : ℝ) + N * (q : ℝ) = (a.val : ℝ) + b.val := by exact_mod_cast h
    rw [Int.cast_natCast]
    field_simp
    linarith
  rw [e, AddCircle.coe_sub, coe_intCast_unitAddCircle, sub_zero]

theorem samplePt_add (x y : Grid N) : samplePt (x + y) = samplePt x + samplePt y := by
  funext j
  simp only [samplePt, Pi.add_apply]
  exact coe_val_add (x j) (y j)

theorem samplePt_neg (x : Grid N) : samplePt (-x) = -samplePt x := by
  have h := samplePt_add x (-x)
  rw [add_neg_cancel] at h
  have h0 : samplePt (0 : Grid N) = 0 := by
    funext j; simp [samplePt]
  rw [h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem samplePt_unit (i : Fin 3) : samplePt (unit i : Grid N) = lineShift i (N : ℝ)⁻¹ := by
  funext j
  simp only [samplePt, lineShift, unit]
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.single_eq_same]
    by_cases h1 : N = 1
    · subst h1
      have : (1 : ZMod 1).val = 0 := rfl
      rw [this]
      simp only [Nat.cast_zero, zero_div, Nat.cast_one, inv_one]
      rw [AddCircle.coe_period]; rfl
    · haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
      rw [ZMod.val_one]
      simp
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj]
    simp

theorem samplePt_add_unit (x : Grid N) (i : Fin 3) :
    samplePt (x + unit i) = samplePt x + lineShift i (N : ℝ)⁻¹ := by
  rw [samplePt_add, samplePt_unit]

theorem samplePt_sub_unit (x : Grid N) (i : Fin 3) :
    samplePt (x - unit i) = samplePt x + lineShift i (-(N : ℝ)⁻¹) := by
  have e : lineShift i (-(N : ℝ)⁻¹) = -lineShift i (N : ℝ)⁻¹ := by
    have := lineShift_add i (-(N : ℝ)⁻¹) (N : ℝ)⁻¹
    rw [neg_add_cancel, lineShift_zero] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  rw [sub_eq_add_neg, samplePt_add, samplePt_neg, samplePt_unit, e]

end GridPoints

/-! ### Sampled differences versus sampled derivatives -/

/-- `|e^{iθ} - 1 - iθ| ≤ θ²` for every real `θ`. -/
theorem norm_exp_I_mul_sub_one_sub_le' (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ≤ θ ^ 2 := by
  by_cases hθ : |θ| ≤ π
  · exact norm_exp_I_mul_sub_one_sub_le hθ
  · push_neg at hθ
    have h1 : ‖Complex.exp (Complex.I * θ)‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
    have h2 : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖
        ≤ ‖Complex.exp (Complex.I * θ)‖ + ‖(1 : ℂ)‖ + ‖Complex.I * (θ : ℂ)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = 2 + |θ| := by rw [h1, h2, norm_one]; ring
      _ ≤ θ ^ 2 := by
          have hp := Real.pi_gt_three
          have : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
          nlinarith [abs_nonneg θ]

/-- The translate `F(· + a)` as a continuous function. -/
def transl (F : CT) (a : UnitAddTorus (Fin 3)) : CT :=
  F.comp ⟨fun x => x + a, continuous_id.add continuous_const⟩

@[simp] theorem transl_apply (F : CT) (a x : UnitAddTorus (Fin 3)) : transl F a x = F (x + a) :=
  rfl

theorem mFourierCoeff_transl (F : CT) (a : UnitAddTorus (Fin 3)) (n : Fin 3 → ℤ) :
    mFourierCoeff ⇑(transl F a) n = mFourier n a * mFourierCoeff ⇑F n :=
  mFourierCoeff_comp_add ⇑F a n

/-- The generic `O(h)` bound: a continuous `G` whose coefficients satisfy
`|Ĝ(n)| ≤ (2π nᵢ)²/N |F̂(n)|` is in `H^r` with `‖G‖²_{H^r} ≤ N^{-2} ‖F‖²_{H^{r+2}}`. -/
theorem trigSobSq_le_of_coeff_le (r : ℕ) (i : Fin 3) (N : ℕ) (hN : 0 < N) (F G : CT)
    (hF : MemH (r + 2) ⇑F)
    (hG : ∀ n, ‖mFourierCoeff ⇑G n‖ ≤ (2 * π * n i) ^ 2 / N * ‖mFourierCoeff ⇑F n‖) :
    MemH r ⇑G ∧ trigSobSq r ⇑G ≤ ((N : ℝ) ^ 2)⁻¹ * trigSobSq (r + 2) ⇑F := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2 ≤
      ((N : ℝ) ^ 2)⁻¹ * (trigWeight (r + 2) n * ‖mFourierCoeff ⇑F n‖ ^ 2) := by
    intro n
    have hW := trigWeight_nonneg r n
    have h1 : ‖mFourierCoeff ⇑G n‖ ^ 2 ≤
        ((2 * π * n i) ^ 2 / N) ^ 2 * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hG n) 2
    have h2 := trigWeight_mul_pow_four_le r n i
    calc trigWeight r n * ‖mFourierCoeff ⇑G n‖ ^ 2
        ≤ trigWeight r n * (((2 * π * n i) ^ 2 / N) ^ 2 * ‖mFourierCoeff ⇑F n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hW
      _ = ((N : ℝ) ^ 2)⁻¹ * ((trigWeight r n * ((2 * π * n i) ^ 2) ^ 2) *
            ‖mFourierCoeff ⇑F n‖ ^ 2) := by field_simp
      _ ≤ ((N : ℝ) ^ 2)⁻¹ * (trigWeight (r + 2) n * ‖mFourierCoeff ⇑F n‖ ^ 2) := by
          gcongr
  have hS : Summable fun n => ((N : ℝ) ^ 2)⁻¹ *
      (trigWeight (r + 2) n * ‖mFourierCoeff ⇑F n‖ ^ 2) := hF.mul_left _
  have hs : MemH r ⇑G := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) hpt hS
  refine ⟨hs, ?_⟩
  unfold trigSobSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hpt hS

theorem dp_sample_eq {N : ℕ} [NeZero N] (i : Fin 3) (F : CT) :
    Dp i (sample N ⇑F) = sample N ⇑((N : ℂ) • (transl F (lineShift i (N : ℝ)⁻¹) - F)) := by
  funext x
  rw [Dp_apply]
  simp only [sample, ContinuousMap.coe_smul, ContinuousMap.coe_sub, Pi.smul_apply,
    Pi.sub_apply, transl_apply, smul_eq_mul, samplePt_add_unit]

theorem dm_sample_eq {N : ℕ} [NeZero N] (i : Fin 3) (F : CT) :
    Dm i (sample N ⇑F) = sample N ⇑((N : ℂ) • (F - transl F (lineShift i (-(N : ℝ)⁻¹)))) := by
  funext x
  rw [Dm_apply]
  simp only [sample, ContinuousMap.coe_smul, ContinuousMap.coe_sub, Pi.smul_apply,
    Pi.sub_apply, transl_apply, smul_eq_mul, samplePt_sub_unit]

/-- Symbol of the forward difference against `∂ᵢ`. -/
theorem norm_fwd_symbol_sub_le (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ‖(N : ℂ) * (Complex.exp (2 * π * Complex.I * m * ((N : ℝ)⁻¹ : ℝ)) - 1) -
        2 * π * Complex.I * m‖ ≤ (2 * π * m) ^ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set θ : ℝ := 2 * π * m / N
  have e : (N : ℂ) * (Complex.exp (2 * π * Complex.I * m * ((N : ℝ)⁻¹ : ℝ)) - 1) -
      2 * π * Complex.I * m = (N : ℂ) * (Complex.exp (Complex.I * θ) - 1 - Complex.I * θ) := by
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN'.ne'
    simp only [θ]
    push_cast
    field_simp
  rw [e, norm_mul, Complex.norm_natCast]
  calc (N : ℝ) * ‖Complex.exp (Complex.I * θ) - 1 - Complex.I * θ‖ ≤ N * θ ^ 2 :=
        mul_le_mul_of_nonneg_left (norm_exp_I_mul_sub_one_sub_le' θ) hN'.le
    _ = (2 * π * m) ^ 2 / N := by simp only [θ]; field_simp

/-- Symbol of the backward difference against `∂ᵢ`. -/
theorem norm_bwd_symbol_sub_le (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ‖(N : ℂ) * (1 - Complex.exp (2 * π * Complex.I * m * ((-(N : ℝ)⁻¹ : ℝ)))) -
        2 * π * Complex.I * m‖ ≤ (2 * π * m) ^ 2 / N := by
  have h := norm_fwd_symbol_sub_le N hN (-m)
  have e : (N : ℂ) * (1 - Complex.exp (2 * π * Complex.I * m * ((-(N : ℝ)⁻¹ : ℝ)))) -
      2 * π * Complex.I * m = -((N : ℂ) * (Complex.exp (2 * π * Complex.I * ((-m : ℤ) : ℂ) *
        ((N : ℝ)⁻¹ : ℝ)) - 1) - 2 * π * Complex.I * ((-m : ℤ) : ℂ)) := by
    push_cast; ring_nf
  rw [e, norm_neg]
  convert h using 2
  push_cast; ring

/-- **Sampled forward differences approximate sampled derivatives**: for `r ≥ 2` there is `C`,
independent of the mesh, with `‖D_i⁺ 𝒮_h F - 𝒮_h ∂ᵢF‖_{r,h} ≤ C h ‖F‖_{H^{r+2}}`, for every
continuous `F ∈ H^{r+2}` with continuous classical partial derivative `∂ᵢF`. -/
theorem sample_Dp_sub_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (i : Fin 3) (F F' : CT), IsLineDeriv i ⇑F ⇑F' →
      MemH (r + 2) ⇑F →
      sobNorm r (Dp i (sample N ⇑F) - sample N ⇑F') ≤ C * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by
  obtain ⟨C, hC, hs⟩ := sobNorm_sample_le r hr
  refine ⟨C, hC, fun N _ i F F' hd hF => ?_⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G : CT := (N : ℂ) • (transl F (lineShift i (N : ℝ)⁻¹) - F) - F'
  have hcoef : ∀ n, ‖mFourierCoeff ⇑G n‖ ≤ (2 * π * n i) ^ 2 / N * ‖mFourierCoeff ⇑F n‖ := by
    intro n
    have e : mFourierCoeff ⇑G n = ((N : ℂ) * (Complex.exp (2 * π * Complex.I * n i *
        ((N : ℝ)⁻¹ : ℝ)) - 1) - 2 * π * Complex.I * n i) * mFourierCoeff ⇑F n := by
      simp only [G]
      rw [mFourierCoeff_sub, mFourierCoeff_smul', mFourierCoeff_sub, mFourierCoeff_transl,
        mFourier_lineShift, mFourierCoeff_of_isLineDeriv i F F' hd n, smul_eq_mul]
      ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_fwd_symbol_sub_le N hN (n i)) (norm_nonneg _)
  obtain ⟨hGm, hGb⟩ := trigSobSq_le_of_coeff_le r i N hN F G hF hcoef
  have e : Dp i (sample N ⇑F) - sample N ⇑F' = sample N ⇑G := by
    rw [dp_sample_eq]; rfl
  rw [e]
  refine (hs N G hGm).trans ?_
  have hsn : sn r ⇑G ≤ (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by
    unfold sn
    rw [show (N : ℝ)⁻¹ = Real.sqrt (((N : ℝ) ^ 2)⁻¹) by
      rw [Real.sqrt_inv, Real.sqrt_sq hN'.le], ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hGb
  calc C * sn r ⇑G ≤ C * ((N : ℝ)⁻¹ * sn (r + 2) ⇑F) := mul_le_mul_of_nonneg_left hsn hC
    _ = C * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by ring

/-- **Sampled backward differences approximate sampled derivatives.** -/
theorem sample_Dm_sub_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (i : Fin 3) (F F' : CT), IsLineDeriv i ⇑F ⇑F' →
      MemH (r + 2) ⇑F →
      sobNorm r (Dm i (sample N ⇑F) - sample N ⇑F') ≤ C * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by
  obtain ⟨C, hC, hs⟩ := sobNorm_sample_le r hr
  refine ⟨C, hC, fun N _ i F F' hd hF => ?_⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G : CT := (N : ℂ) • (F - transl F (lineShift i (-(N : ℝ)⁻¹))) - F'
  have hcoef : ∀ n, ‖mFourierCoeff ⇑G n‖ ≤ (2 * π * n i) ^ 2 / N * ‖mFourierCoeff ⇑F n‖ := by
    intro n
    have e : mFourierCoeff ⇑G n = ((N : ℂ) * (1 - Complex.exp (2 * π * Complex.I * n i *
        ((-(N : ℝ)⁻¹ : ℝ)))) - 2 * π * Complex.I * n i) * mFourierCoeff ⇑F n := by
      simp only [G]
      rw [mFourierCoeff_sub, mFourierCoeff_smul', mFourierCoeff_sub, mFourierCoeff_transl,
        mFourier_lineShift, mFourierCoeff_of_isLineDeriv i F F' hd n, smul_eq_mul]
      ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_bwd_symbol_sub_le N hN (n i)) (norm_nonneg _)
  obtain ⟨hGm, hGb⟩ := trigSobSq_le_of_coeff_le r i N hN F G hF hcoef
  have e : Dm i (sample N ⇑F) - sample N ⇑F' = sample N ⇑G := by
    rw [dm_sample_eq]; rfl
  rw [e]
  refine (hs N G hGm).trans ?_
  have hsn : sn r ⇑G ≤ (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by
    unfold sn
    rw [show (N : ℝ)⁻¹ = Real.sqrt (((N : ℝ) ^ 2)⁻¹) by
      rw [Real.sqrt_inv, Real.sqrt_sq hN'.le], ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hGb
  calc C * sn r ⇑G ≤ C * ((N : ℝ)⁻¹ * sn (r + 2) ⇑F) := mul_le_mul_of_nonneg_left hsn hC
    _ = C * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by ring

/-- **Sampled central differences approximate sampled derivatives.** -/
theorem sample_D0_sub_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (i : Fin 3) (F F' : CT), IsLineDeriv i ⇑F ⇑F' →
      MemH (r + 2) ⇑F →
      sobNorm r (D0 i (sample N ⇑F) - sample N ⇑F') ≤ C * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by
  obtain ⟨Cp, hCp, hp⟩ := sample_Dp_sub_le r hr
  obtain ⟨Cm, hCm, hm⟩ := sample_Dm_sub_le r hr
  refine ⟨(Cp + Cm) / 2, by positivity, fun N _ i F F' hd hF => ?_⟩
  have e : D0 i (sample N ⇑F) - sample N ⇑F' =
      (2 : ℂ)⁻¹ • ((Dp i (sample N ⇑F) - sample N ⇑F') + (Dm i (sample N ⇑F) - sample N ⇑F')) := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, D0_apply, smul_eq_mul]
    ring
  rw [e, Moser.sobNorm_smul]
  have h1 := hp N i F F' hd hF
  have h2 := hm N i F F' hd hF
  have h3 := Moser.sobNorm_add_le r (Dp i (sample N ⇑F) - sample N ⇑F')
    (Dm i (sample N ⇑F) - sample N ⇑F')
  have hn : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by rw [norm_inv]; norm_num
  rw [hn]
  have := sn_nonneg (r + 2) ⇑F
  calc 1 / 2 * sobNorm r ((Dp i (sample N ⇑F) - sample N ⇑F') +
        (Dm i (sample N ⇑F) - sample N ⇑F'))
      ≤ 1 / 2 * (Cp * (N : ℝ)⁻¹ * sn (r + 2) ⇑F + Cm * (N : ℝ)⁻¹ * sn (r + 2) ⇑F) := by
        gcongr; linarith
    _ = (Cp + Cm) / 2 * (N : ℝ)⁻¹ * sn (r + 2) ⇑F := by ring

/-! ### Calculus rules for line derivatives -/

section LineCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsLineDeriv.mul {i : Fin 3} {F F' G G' : UnitAddTorus (Fin 3) → ℝ}
    (hF : IsLineDeriv i F F') (hG : IsLineDeriv i G G') :
    IsLineDeriv i (fun x => F x * G x) (fun x => F' x * G x + F x * G' x) := by
  intro x
  have := (hF x).fun_mul (hG x)
  simpa [lineShift_zero] using this

theorem IsLineDeriv.comp {i : Fin 3} {Q Q' : UnitAddTorus (Fin 3) → E} (hQ : IsLineDeriv i Q Q')
    {A : E → ℝ} (hA : ∀ x, DifferentiableAt ℝ A (Q x)) :
    IsLineDeriv i (fun x => A (Q x)) (fun x => fderiv ℝ A (Q x) (Q' x)) := by
  intro x
  have h1 := hQ x
  have h2 : HasFDerivAt A (fderiv ℝ A (Q (x + lineShift i 0))) (Q (x + lineShift i 0)) := by
    rw [lineShift_zero, add_zero]; exact (hA x).hasFDerivAt
  have := h2.comp_hasDerivAt (0 : ℝ) h1
  simpa [lineShift_zero, Function.comp_def] using this

theorem IsLineDeriv.const_add {i : Fin 3} {Q Q' : UnitAddTorus (Fin 3) → E} (c : E)
    (hQ : IsLineDeriv i Q Q') : IsLineDeriv i (fun x => c + Q x) Q' := by
  intro x
  exact (hQ x).const_add c

theorem IsLineDeriv.ofReal {i : Fin 3} {F F' : UnitAddTorus (Fin 3) → ℝ} (hF : IsLineDeriv i F F') :
    IsLineDeriv i (fun x => (F x : ℂ)) (fun x => (F' x : ℂ)) := by
  intro x
  exact (hF x).ofReal_comp

theorem IsLineDeriv.apply {ι' : Type*} [Fintype ι'] {i : Fin 3}
    {Q Q' : UnitAddTorus (Fin 3) → ι' → ℝ} (hQ : IsLineDeriv i Q Q') (j : ι') :
    IsLineDeriv i (fun x => Q x j) (fun x => Q' x j) := by
  intro x
  exact hasDerivAt_pi.mp (hQ x) j

end LineCalculus

/-! ### Sobolev norm of a classical derivative -/

/-- `W_r(n) (2π nᵢ)² ≤ W_{r+1}(n)`. -/
theorem trigWeight_mul_sq_le (r : ℕ) (n : Fin 3 → ℤ) (i : Fin 3) :
    trigWeight r n * (2 * π * n i) ^ 2 ≤ trigWeight (r + 1) n := by
  classical
  unfold trigWeight
  rw [sum_mul]
  have hshift : ∀ α : Fin 3 → ℕ, tsymSq α n * (2 * π * n i) ^ 2 =
      tsymSq (α + Pi.single i 1) n := by
    intro α
    fin_cases i <;> simp [tsymSq, pow_add] <;> ring
  simp_rw [hshift]
  rw [← sum_image (f := fun β => tsymSq β n) (s := multiIndices r)
    (g := fun α => α + Pi.single i 1) (fun a _ b _ h => add_right_cancel h)]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun β _ _ => tsymSq_nonneg β n)
  intro β hβ
  obtain ⟨α, hα, rfl⟩ := mem_image.mp hβ
  rw [mem_multiIndices] at hα ⊢
  have : deg (α + Pi.single i 1) = deg α + 1 := by
    simp only [deg, Pi.add_apply]; fin_cases i <;> simp <;> ring
  omega

/-- **A classical derivative costs one Sobolev order**: if `F'` is the continuous line derivative
of `F ∈ H^{r+1}` in direction `i`, then `F' ∈ H^r` and `‖F'‖_{H^r} ≤ ‖F‖_{H^{r+1}}`. -/
theorem memH_of_isLineDeriv {r : ℕ} {i : Fin 3} {F F' : CT} (h : IsLineDeriv i ⇑F ⇑F')
    (hF : MemH (r + 1) ⇑F) : MemH r ⇑F' ∧ sn r ⇑F' ≤ sn (r + 1) ⇑F := by
  have hpt : ∀ n, trigWeight r n * ‖mFourierCoeff ⇑F' n‖ ^ 2 ≤
      trigWeight (r + 1) n * ‖mFourierCoeff ⇑F n‖ ^ 2 := by
    intro n
    rw [mFourierCoeff_of_isLineDeriv i F F' h n, norm_mul]
    have e : ‖(2 * π * Complex.I * n i : ℂ)‖ = |2 * π * n i| := by
      rw [show (2 * π * Complex.I * n i : ℂ) = ((2 * π * n i : ℝ) : ℂ) * Complex.I by
        push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [e, mul_pow, sq_abs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (trigWeight_mul_sq_le r n i) (sq_nonneg _)
  have hs : MemH r ⇑F' := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (trigWeight_nonneg _ _) (sq_nonneg _)) hpt hF
  refine ⟨hs, ?_⟩
  unfold sn trigSobSq
  exact Real.sqrt_le_sqrt (hs.tsum_le_tsum hpt hF)

/-! ### Continuity of analytic compositions -/

theorem continuous_comp_analyticOnNhd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : E → ℝ} {U : Set E} (hA : AnalyticOnNhd ℝ A U)
    {Q : UnitAddTorus (Fin 3) → E} (hQc : Continuous Q) (hQ : ∀ y, Q y ∈ U) :
    Continuous (fun y => A (Q y)) ∧ Continuous (fun y => fderiv ℝ A (Q y)) :=
  ⟨hA.continuousOn.comp_continuous hQc hQ, hA.fderiv.continuousOn.comp_continuous hQc hQ⟩

end

end RenewalGeometry.TorusSobolevTransfer
