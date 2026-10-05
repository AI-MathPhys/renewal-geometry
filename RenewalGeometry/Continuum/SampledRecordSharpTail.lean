/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.GaugeReaderSobolevTail
import RenewalGeometry.Analysis.PeriodicTrigInterpolation
import RenewalGeometry.Action.DiscreteEulerConsistency

/-!
# Sharp measured tails of nodal samples of smooth periodic records (`eq:app-sharp-tail`)

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty` (proof: "the
bound `τ_{h,j} ≤ C_q K_h^{2-q}` from `eq:app-sharp-tail`, for sufficiently large `q`") and
`eq:app-sharp-tail` (`app:native-reader-proof`).

Generic infrastructure (no renewal notions).  Let `Y : ℝ⁴ → V` be a smooth field with period `2π`
in every coordinate, with values in a finite-dimensional real normed space, and let
`u_h = 𝖲_h Y` be its nodal samples on the periodic grid `(ℤ/n)⁴`, `h = 2π/n`.  If
`‖D^r Y‖ ≤ M` for `r ≤ q`, then the measured tails of `eq:native-tail`
(`TrigInterp.tau`, real Fourier coefficient pairs) satisfy, **uniformly in `n`**,
`τ_{h,j}(K) ≤ C_{q,j,V} M K^{2-q}` for every real `K ≥ 1` and `q > j + 2`.

## Main results

* `stepDiff`, `cDiff`: forward differences `Δ_μ f(z) = f(z + h e_μ) - f(z)` of a field and their
  iterates along a word; `norm_cDiff_le`: `‖Δ_w f‖ ≤ |h|^{|w|} sup ‖D^{|w|} f‖` (iterated mean
  value inequality).
* `iterDiff_samp`: the normalised grid differences `δ_w` of the samples
  (`GaugeReaderTail.iterDiff`) are `h^{-|w|} Δ_w f` at the nodes (periodicity handles the seam
  of the grid).
* `diffEnergy_samp_le`: the discrete `H^q` difference energy of the samples is at most
  `(2π)⁴ (q+1) 4^q M²`, uniformly in `n`.
* `coefMode_re`, `coefMode_im`: the complex DFT coefficient of a scalar functional of the record is
  `φ(a_ℓ) - i φ(b_ℓ)` in terms of the real coefficient pair of `TrigInterp.coefOf`.
* **`tau_samp_le`** (`eq:app-sharp-tail` for sampled smooth records).
-/

open Finset
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.SampledTail

open DiscreteEulerConsistency (R4 pos samp IsPeriodic evec realVec castVec)
open ShiftedJetAction (Grid unitVec)

set_option linter.unusedSectionVars false

/-! ### Forward differences of fields -/

section Diff

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The forward step `Δ_μ f(z) = f(z + h e_μ) - f(z)`. -/
def stepDiff (h : ℝ) (μ : Fin 4) (f : R4 → W) : R4 → W := fun z => f (z + Pi.single μ h) - f z

/-- Iterated forward steps along a word: `Δ_{j :: w} f = Δ_j (Δ_w f)`. -/
def cDiff (h : ℝ) : List (Fin 4) → (R4 → W) → R4 → W
  | [], f => f
  | j :: w, f => stepDiff h j (cDiff h w f)

theorem contDiff_stepDiff {f : R4 → W} (hf : ContDiff ℝ ∞ f) (h : ℝ) (μ : Fin 4) :
    ContDiff ℝ ∞ (stepDiff h μ f) :=
  (hf.comp (contDiff_id.add contDiff_const)).sub hf

theorem stepDiff_comm (h : ℝ) (i j : Fin 4) (f : R4 → W) :
    stepDiff h i (stepDiff h j f) = stepDiff h j (stepDiff h i f) := by
  funext z
  simp only [stepDiff, add_right_comm z (Pi.single i h) (Pi.single j h)]
  abel

theorem stepDiff_cDiff (h : ℝ) (j : Fin 4) :
    ∀ (w : List (Fin 4)) (f : R4 → W), stepDiff h j (cDiff h w f) = cDiff h w (stepDiff h j f)
  | [], _ => rfl
  | i :: w, f => by
    show stepDiff h j (stepDiff h i (cDiff h w f)) = stepDiff h i (cDiff h w (stepDiff h j f))
    rw [stepDiff_comm, stepDiff_cDiff h j w f]

theorem contDiff_cDiff (h : ℝ) :
    ∀ (w : List (Fin 4)) {f : R4 → W}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (cDiff h w f)
  | [], _, hf => hf
  | j :: w, _, hf => contDiff_stepDiff (contDiff_cDiff h w hf) h j

/-- `D^r(Δ_μ f)(z) = D^r f(z + h e_μ) - D^r f(z)`. -/
theorem iteratedFDeriv_stepDiff {f : R4 → W} (hf : ContDiff ℝ ∞ f) (h : ℝ) (μ : Fin 4) (r : ℕ)
    (z : R4) :
    iteratedFDeriv ℝ r (stepDiff h μ f) z =
      iteratedFDeriv ℝ r f (z + Pi.single μ h) - iteratedFDeriv ℝ r f z := by
  have h1 : ContDiffAt ℝ r (fun z => f (z + Pi.single μ h)) z :=
    ((hf.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ r f z := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : stepDiff h μ f = (fun z => f (z + Pi.single μ h)) - f := rfl
  rw [e, iteratedFDeriv_sub_apply h1 h2, iteratedFDeriv_comp_add_right]

/-- **One step of the mean value inequality**: `sup ‖D^r Δ_μ f‖ ≤ |h| sup ‖D^{r+1} f‖`. -/
theorem norm_iteratedFDeriv_stepDiff_le {f : R4 → W} (hf : ContDiff ℝ ∞ f) (h : ℝ) (μ : Fin 4)
    (r : ℕ) {M : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ (r + 1) f z‖ ≤ M) (z : R4) :
    ‖iteratedFDeriv ℝ r (stepDiff h μ f) z‖ ≤ |h| * M := by
  rw [iteratedFDeriv_stepDiff hf]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ r f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (fun x _ => hd x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hM x) convex_univ
    (Set.mem_univ z) (Set.mem_univ (z + Pi.single μ h))
  rw [add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs] at hmv
  linarith

/-- **The iterated mean value inequality**: if `‖D^{|w|} f‖ ≤ M` everywhere, then
`‖Δ_w f(z)‖ ≤ |h|^{|w|} M`. -/
theorem norm_cDiff_le (h : ℝ) :
    ∀ (w : List (Fin 4)) {f : R4 → W} {M : ℝ}, ContDiff ℝ ∞ f →
      (∀ z, ‖iteratedFDeriv ℝ w.length f z‖ ≤ M) → ∀ z, ‖cDiff h w f z‖ ≤ |h| ^ w.length * M
  | [], f, M, _, hM, z => by
    have := hM z
    rw [List.length_nil, norm_iteratedFDeriv_zero] at this
    simp only [cDiff, List.length_nil, pow_zero, one_mul]
    exact this
  | j :: w, f, M, hf, hM, z => by
    show ‖stepDiff h j (cDiff h w f) z‖ ≤ _
    rw [stepDiff_cDiff]
    have hstep : ∀ z, ‖iteratedFDeriv ℝ w.length (stepDiff h j f) z‖ ≤ |h| * M :=
      norm_iteratedFDeriv_stepDiff_le hf h j w.length (fun z => by simpa using hM z)
    have := norm_cDiff_le h w (contDiff_stepDiff hf h j) hstep z
    rw [List.length_cons, pow_succ]
    linarith

theorem isPeriodic_stepDiff {L : ℝ} {f : R4 → W} (hf : IsPeriodic L f) (h : ℝ) (μ : Fin 4) :
    IsPeriodic L (stepDiff h μ f) := fun z ν => by
  simp only [stepDiff]
  rw [add_right_comm, hf, hf]

theorem isPeriodic_cDiff {L : ℝ} {f : R4 → W} (hf : IsPeriodic L f) (h : ℝ) :
    ∀ w : List (Fin 4), IsPeriodic L (cDiff h w f)
  | [] => hf
  | j :: w => isPeriodic_stepDiff (isPeriodic_cDiff hf h w) h j

end Diff

/-! ### Grid differences of samples -/

section Grid

variable {n : ℕ} [NeZero n]

/-- The scalar complex record `x ↦ f(h x̃)` of a real field. -/
def sampC (h : ℝ) (f : R4 → ℝ) : LatticeTorusPlancherel.Grid 4 n → ℂ := fun x => ((f (pos h x) : ℝ) : ℂ)

theorem pos_add_single {h : ℝ} {F : R4 → ℝ} (hF : IsPeriodic ((n : ℝ) * h) F)
    (x : LatticeTorusPlancherel.Grid 4 n) (j : Fin 4) :
    F (pos h (x + Pi.single j 1)) = F (pos h x + Pi.single j h) := by
  have e1 : (Pi.single j 1 : LatticeTorusPlancherel.Grid 4 n) = castVec (Pi.single j 1) := by
    rw [DiscreteEulerConsistency.castVec_single]; rfl
  have e2 : h • realVec (Pi.single j 1) = Pi.single j h := by
    rw [DiscreteEulerConsistency.realVec_single, evec, ← Pi.single_smul', smul_eq_mul, mul_one]
  have := DiscreteEulerConsistency.samp_add_castVec hF x (Pi.single j 1)
  rw [← e1, e2] at this
  exact this

/-- **Grid differences of samples are field differences**: with `h⁻¹`-normalised forward
differences `δ_w` (`GaugeReaderTail.iterDiff`) and `F` of period `n h`,
`δ_w(𝖲_h F)(x) = h^{-|w|} Δ_w F(h x̃)`. -/
theorem iterDiff_samp {h : ℝ} {f : R4 → ℝ} (hf : IsPeriodic ((n : ℝ) * h) f) :
    ∀ (w : List (Fin 4)) (x : LatticeTorusPlancherel.Grid 4 n),
      GaugeReaderTail.iterDiff h w (sampC h f) x =
        (((h⁻¹) ^ w.length * cDiff h w f (pos h x) : ℝ) : ℂ)
  | [], x => by simp [GaugeReaderTail.iterDiff, cDiff, sampC]
  | j :: w, x => by
    rw [GaugeReaderTail.iterDiff]
    simp only [GaugeReaderTail.fwdDiff]
    rw [iterDiff_samp hf w (x + Pi.single j 1), iterDiff_samp hf w x,
      pos_add_single (isPeriodic_cDiff hf h w) x j]
    simp only [cDiff, stepDiff, List.length_cons]
    push_cast
    ring

/-- `‖v‖²_{2,h} ≤ (2π)⁴ B²` for a record bounded by `B` on the grid of mesh `h = 2π/n`. -/
theorem gridSq_le {h : ℝ} (hh : h = 2 * π / n) {v : LatticeTorusPlancherel.Grid 4 n → ℂ} {B : ℝ}
    (hB : ∀ x, ‖v x‖ ≤ B) : GaugeReaderTail.gridSq h v ≤ (2 * π) ^ 4 * B ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold GaugeReaderTail.gridSq
  have hs : ∑ x, ‖v x‖ ^ 2 ≤ ∑ _x : LatticeTorusPlancherel.Grid 4 n, B ^ 2 :=
    Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hcard : ∑ _x : LatticeTorusPlancherel.Grid 4 n, B ^ 2 = (n : ℝ) ^ 4 * B ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp [LatticeTorusPlancherel.Grid, ZMod.card]
  have hh4 : 0 ≤ h ^ 4 := by positivity
  calc h ^ 4 * ∑ x, ‖v x‖ ^ 2 ≤ h ^ 4 * ((n : ℝ) ^ 4 * B ^ 2) :=
        mul_le_mul_of_nonneg_left (hs.trans hcard.le) hh4
    _ = (2 * π) ^ 4 * B ^ 2 := by rw [hh]; field_simp

/-- **The discrete `H^q` difference energy of the samples** of a smooth field of period `2π` with
`‖D^r f‖ ≤ M` (`r ≤ q`) is at most `(2π)⁴ (q+1) 4^q M²`, uniformly in `n`. -/
theorem diffEnergy_samp_le {h : ℝ} (hh : h = 2 * π / n) {f : R4 → ℝ} (hfs : ContDiff ℝ ∞ f)
    (hf : IsPeriodic ((n : ℝ) * h) f) (q : ℕ) {M : ℝ}
    (hM : ∀ r ≤ q, ∀ z, ‖iteratedFDeriv ℝ r f z‖ ≤ M) :
    GaugeReaderTail.diffEnergy h q (sampC (n := n) h f) ≤ (2 * π) ^ 4 * ((q + 1) * 4 ^ q) * M ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hword : ∀ r ≤ q, ∀ w : Fin r → Fin 4,
      GaugeReaderTail.gridSq h (GaugeReaderTail.iterDiff h (List.ofFn w) (sampC (n := n) h f)) ≤
        (2 * π) ^ 4 * M ^ 2 := by
    intro r hr w
    refine gridSq_le hh fun x => ?_
    rw [iterDiff_samp hf, Complex.norm_real, Real.norm_eq_abs, List.length_ofFn, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ h⁻¹ ^ r)]
    have hc := norm_cDiff_le h (List.ofFn w) hfs (M := M)
      (fun z => by rw [List.length_ofFn]; exact hM r hr z) (pos h x)
    rw [List.length_ofFn, Real.norm_eq_abs, abs_of_pos hh0] at hc
    calc h⁻¹ ^ r * |cDiff h (List.ofFn w) f (pos h x)| ≤ h⁻¹ ^ r * (h ^ r * M) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = M := by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hh0.ne', one_pow, one_mul]
  unfold GaugeReaderTail.diffEnergy
  have hM2 : 0 ≤ (2 * π) ^ 4 * M ^ 2 := by positivity
  calc ∑ r ∈ range (q + 1), ∑ w : Fin r → Fin 4,
        GaugeReaderTail.gridSq h (GaugeReaderTail.iterDiff h (List.ofFn w) (sampC (n := n) h f))
      ≤ ∑ r ∈ range (q + 1), ∑ _w : Fin r → Fin 4, (2 * π) ^ 4 * M ^ 2 := by
        refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun w _ => ?_
        exact hword r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) w
    _ = ∑ r ∈ range (q + 1), (4 : ℝ) ^ r * ((2 * π) ^ 4 * M ^ 2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
    _ ≤ ∑ _r ∈ range (q + 1), (4 : ℝ) ^ q * ((2 * π) ^ 4 * M ^ 2) := by
        refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_right ?_ hM2
        exact pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
    _ = (2 * π) ^ 4 * ((q + 1) * 4 ^ q) * M ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end Grid

/-! ### Complex DFT coefficients and the real coefficient pairs -/

section Coef

variable {n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The lattice character of a centred mode at a node is `e^{iℓ·(h x̃)}`, `h = 2π/n`. -/
theorem latticeChar_castMode (ℓ : Fin 4 → ℤ) (x : LatticeTorusPlancherel.Grid 4 n) :
    LatticeTorusPlancherel.latticeChar (GaugeReaderTail.castMode ℓ) x =
      Complex.exp ((VecTrig.phase ℓ (TrigInterp.gpos n x) : ℂ) * Complex.I) := by
  unfold LatticeTorusPlancherel.latticeChar GaugeReaderTail.castMode
  have hμ : ∀ μ, ZMod.stdAddChar (((ℓ μ : ℤ) : ZMod n) * x μ) =
      Complex.exp ((((ℓ μ : ℝ) * ((2 * π / n) * ((x μ).val : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    intro μ
    have hx : ((ℓ μ : ℤ) : ZMod n) * x μ = (((ℓ μ * ((x μ).val : ℤ)) : ℤ) : ZMod n) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hx, ZMod.stdAddChar_coe]
    congr 1
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    push_cast
    field_simp
  simp_rw [hμ]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  unfold VecTrig.phase TrigInterp.gpos
  push_cast
  rfl

theorem conj_latticeChar_castMode (ℓ : Fin 4 → ℤ) (x : LatticeTorusPlancherel.Grid 4 n) :
    (starRingEnd ℂ) (LatticeTorusPlancherel.latticeChar (GaugeReaderTail.castMode ℓ) x) =
      (Real.cos (VecTrig.phase ℓ (TrigInterp.gpos n x)) : ℂ) -
        (Real.sin (VecTrig.phase ℓ (TrigInterp.gpos n x)) : ℂ) * Complex.I := by
  rw [latticeChar_castMode, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The DFT coefficient of a scalar functional `φ ∘ u` of a record is `φ(a_ℓ) - i φ(b_ℓ)`:
real part. -/
theorem coefMode_re (u : (Fin 4 → ZMod n) → V) (φ : V →L[ℝ] ℝ) (ℓ : Fin 4 → ℤ) :
    (GaugeReaderTail.coefMode (fun x : LatticeTorusPlancherel.Grid 4 n => ((φ (u x) : ℝ) : ℂ))
      ℓ).re = φ (TrigInterp.coefOf n u ℓ).1 := by
  unfold GaugeReaderTail.coefMode LatticeTorusPlancherel.dft TrigInterp.coefOf
  simp_rw [conj_latticeChar_castMode]
  rw [map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hn : ((n : ℂ) ^ 4)⁻¹ = ((((n : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hn, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The DFT coefficient of a scalar functional `φ ∘ u` of a record is `φ(a_ℓ) - i φ(b_ℓ)`:
imaginary part. -/
theorem coefMode_im (u : (Fin 4 → ZMod n) → V) (φ : V →L[ℝ] ℝ) (ℓ : Fin 4 → ℤ) :
    (GaugeReaderTail.coefMode (fun x : LatticeTorusPlancherel.Grid 4 n => ((φ (u x) : ℝ) : ℂ))
      ℓ).im = -φ (TrigInterp.coefOf n u ℓ).2 := by
  unfold GaugeReaderTail.coefMode LatticeTorusPlancherel.dft TrigInterp.coefOf
  simp_rw [conj_latticeChar_castMode]
  rw [map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hn : ((n : ℂ) ^ 4)⁻¹ = ((((n : ℝ) ^ 4)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hn, Complex.im_ofReal_mul, Complex.im_sum, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem abs_coef_fst_le (u : (Fin 4 → ZMod n) → V) (φ : V →L[ℝ] ℝ) (ℓ : Fin 4 → ℤ) :
    |φ (TrigInterp.coefOf n u ℓ).1| ≤
      ‖GaugeReaderTail.coefMode (fun x : LatticeTorusPlancherel.Grid 4 n => ((φ (u x) : ℝ) : ℂ)) ℓ‖ := by
  rw [← coefMode_re]; exact Complex.abs_re_le_norm _

theorem abs_coef_snd_le (u : (Fin 4 → ZMod n) → V) (φ : V →L[ℝ] ℝ) (ℓ : Fin 4 → ℤ) :
    |φ (TrigInterp.coefOf n u ℓ).2| ≤
      ‖GaugeReaderTail.coefMode (fun x : LatticeTorusPlancherel.Grid 4 n => ((φ (u x) : ℝ) : ℂ)) ℓ‖ := by
  rw [← abs_neg, ← coefMode_im]; exact Complex.abs_im_le_norm _

end Coef

/-! ### Coordinates of a finite-dimensional space -/

section Coord

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coordinate functionals of a fixed basis of `V`, as continuous linear maps. -/
def coordL (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((Module.finBasis ℝ V).equivFunL : V →L[ℝ] Fin (Module.finrank ℝ V) → ℝ)

/-- Norm equivalence: `‖v‖ ≤ C Σ_i |λ_i(v)|` for the coordinate functionals. -/
theorem exists_norm_le_sum_coord :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V, ‖v‖ ≤ C * ∑ i, |coordL V i v| := by
  set e := (Module.finBasis ℝ V).equivFunL
  refine ⟨‖(e.symm : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] V)‖, norm_nonneg _, fun v => ?_⟩
  have h1 : ‖v‖ ≤ ‖(e.symm : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] V)‖ * ‖e v‖ := by
    have := (e.symm : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] V).le_opNorm (e v)
    simpa using this
  have h2 : ‖e v‖ ≤ ∑ i, |coordL V i v| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |coordL V i v|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

end Coord

/-! ### The sharp tail of sampled records -/

section Tail

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem two_mul_half_lt (n : ℕ) [NeZero n] : 2 * TrigInterp.half n < n := by
  have := Nat.pos_of_ne_zero (NeZero.ne n)
  unfold TrigInterp.half; omega

theorem mem_sobolevBox_of_mem_box {n : ℕ} {ℓ : Fin 4 → ℤ} (hℓ : ℓ ∈ TrigInterp.box n 4) :
    ℓ ∈ SobolevReader.box (TrigInterp.half n) := by
  unfold TrigInterp.box at hℓ
  unfold SobolevReader.box
  exact hℓ

/-- The tail frequencies `|ℓ|_∞ > K` (real `K ≥ 1`) lie in the integer-cutoff tail `⌊K⌋ < |ℓ|_∞`
of the centred box. -/
theorem tailBox_subset {n : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    TrigInterp.tailBox (d := 4) n K ⊆
      (SobolevReader.box (TrigInterp.half n)).filter (fun ℓ => ⌊K⌋₊ < SobolevReader.linf ℓ) := by
  intro ℓ hℓ
  unfold TrigInterp.tailBox at hℓ
  rw [Finset.mem_filter] at hℓ ⊢
  refine ⟨mem_sobolevBox_of_mem_box hℓ.1, ?_⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, K < |(ℓ μ : ℝ)| := by
    by_contra hc; push Not at hc; exact hℓ.2 hc
  have hle : (ℓ μ).natAbs ≤ SobolevReader.linf ℓ :=
    Finset.le_sup (f := fun μ => (ℓ μ).natAbs) (Finset.mem_univ μ)
  have h1 : (⌊K⌋₊ : ℝ) < (ℓ μ).natAbs := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact lt_of_le_of_lt (Nat.floor_le (by linarith)) hμ
  have : ⌊K⌋₊ < (ℓ μ).natAbs := by exact_mod_cast h1
  omega

/-- The tail is empty once the integer cutoff exceeds the box. -/
theorem tailBox_eq_empty {n : ℕ} {K : ℝ} (hK : 1 ≤ K) (hr : TrigInterp.half n < ⌊K⌋₊) :
    TrigInterp.tailBox (d := 4) n K = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ℓ hℓ => ?_
  have h := tailBox_subset hK hℓ
  rw [Finset.mem_filter, SobolevReader.mem_box] at h
  omega

/-- **`eq:app-sharp-tail` for nodal samples of smooth periodic records.**  For `q > j + 2` there
is `C` (depending on `q`, `j` and `V`) such that for every grid size `n` (`h = 2π/n`), every smooth
field `Y : ℝ⁴ → V` of period `2π` with `‖D^r Y‖ ≤ M` for `r ≤ q`, and every real `K ≥ 1`, the
measured tail of the samples `u_h = 𝖲_h Y` satisfies `τ_{h,j}(K) ≤ C M K^{2-q}`. -/
theorem tau_samp_le (j q : ℕ) (hjq : (j : ℝ) + 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (Y : R4 → V) (M : ℝ), ContDiff ℝ ∞ Y →
      IsPeriodic (2 * π) Y → (∀ r ≤ q, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M) →
      ∀ K : ℝ, 1 ≤ K → TrigInterp.tau n K j (samp (n := n) (2 * π / n) Y) ≤
        C * M * K ^ (2 - (q : ℝ)) := by
  obtain ⟨Cb, hCb, hbasis⟩ := exists_norm_le_sum_coord V
  set Ct : ℝ := Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) with hCt
  set Ce : ℝ := Real.sqrt ((π ^ 2 / 2) ^ q * ((q + 1) * 4 ^ q)) with hCe
  set Λ : ℝ := ∑ i, ‖coordL V i‖ with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hq2 : (0 : ℝ) ≤ q - 2 := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  refine ⟨2 * Cb * Ct * Ce * Λ * 2 ^ ((q : ℝ) - 2), by positivity, ?_⟩
  intro n _ Y M hY hper hM K hK
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hK0 : 0 < K := by linarith
  set h : ℝ := 2 * π / n with hh
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hper' : IsPeriodic ((n : ℝ) * h) Y := by
    rw [hh, mul_div_cancel₀ _ hn0]; exact hper
  set u : ShiftedJetAction.Grid n → V := samp (n := n) h Y with hu
  set Kn : ℕ := ⌊K⌋₊ with hKn
  have hKn1 : 1 ≤ Kn := Nat.le_floor (by exact_mod_cast hK)
  have hKn0 : (0 : ℝ) < Kn := by exact_mod_cast hKn1
  have hKnK : (Kn : ℝ) ≤ K := Nat.floor_le hK0.le
  have hRHS0 : 0 ≤ 2 * Cb * Ct * Ce * Λ * 2 ^ ((q : ℝ) - 2) * M * K ^ (2 - (q : ℝ)) := by
    positivity
  by_cases hKr : Kn ≤ TrigInterp.half n
  swap
  · rw [TrigInterp.tau, tailBox_eq_empty hK (by omega), Finset.sum_empty]; exact hRHS0
  -- the scalar records
  set F : Fin (Module.finrank ℝ V) → R4 → ℝ := fun i z => coordL V i (Y z) with hF
  have hFs : ∀ i, ContDiff ℝ ∞ (F i) := fun i => (coordL V i).contDiff.comp hY
  have hFp : ∀ i, IsPeriodic ((n : ℝ) * h) (F i) := fun i z μ => by
    simp only [hF]; rw [hper' z μ]
  have hFM : ∀ i, ∀ r ≤ q, ∀ z, ‖iteratedFDeriv ℝ r (F i) z‖ ≤ ‖coordL V i‖ * M := by
    intro i r hr z
    have := (coordL V i).norm_iteratedFDeriv_comp_left (hY.contDiffAt (x := z))
      (n := r) (by exact_mod_cast le_top)
    exact this.trans (mul_le_mul_of_nonneg_left (hM r hr z) (norm_nonneg _))
  have hg : ∀ i, (fun x : LatticeTorusPlancherel.Grid 4 n => ((coordL V i (u x) : ℝ) : ℂ)) =
      sampC (n := n) h (F i) := fun i => rfl
  -- coefficient size through the coordinates
  have hcn : ∀ ℓ, VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤
      2 * Cb * ∑ i, ‖GaugeReaderTail.coefMode (sampC (n := n) h (F i)) ℓ‖ := by
    intro ℓ
    unfold VecTrig.cn
    have h1 := hbasis (TrigInterp.coefOf n u ℓ).1
    have h2 := hbasis (TrigInterp.coefOf n u ℓ).2
    have e1 : ∑ i, |coordL V i (TrigInterp.coefOf n u ℓ).1| ≤
        ∑ i, ‖GaugeReaderTail.coefMode (sampC (n := n) h (F i)) ℓ‖ :=
      Finset.sum_le_sum fun i _ => by rw [← hg i]; exact abs_coef_fst_le u (coordL V i) ℓ
    have e2 : ∑ i, |coordL V i (TrigInterp.coefOf n u ℓ).2| ≤
        ∑ i, ‖GaugeReaderTail.coefMode (sampC (n := n) h (F i)) ℓ‖ :=
      Finset.sum_le_sum fun i _ => by rw [← hg i]; exact abs_coef_snd_le u (coordL V i) ℓ
    have := mul_le_mul_of_nonneg_left e1 hCb
    have := mul_le_mul_of_nonneg_left e2 hCb
    linarith
  -- the tail of each scalar record
  have htail : ∀ i, SobolevReader.tail (SobolevReader.box (TrigInterp.half n)) j Kn
      (GaugeReaderTail.coefMode (sampC (n := n) h (F i))) ≤
        Ct * (Kn : ℝ) ^ (2 - (q : ℝ)) * (Ce * (‖coordL V i‖ * M)) := by
    intro i
    have h1 := GaugeReaderTail.tail_le_diffEnergy (n := n) hh (two_mul_half_lt n) (q := q) (m := j)
      (K := Kn) hjq hKn1 hKr (sampC (n := n) h (F i))
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hE := diffEnergy_samp_le hh (hFs i) (hFp i) q (hFM i)
    have hπ : (0 : ℝ) < (2 * π) ^ 4 := by positivity
    calc Real.sqrt ((π ^ 2 / 2) ^ q / (2 * π) ^ 4 *
          GaugeReaderTail.diffEnergy h q (sampC (n := n) h (F i)))
        ≤ Real.sqrt ((π ^ 2 / 2) ^ q / (2 * π) ^ 4 *
          ((2 * π) ^ 4 * ((q + 1) * 4 ^ q) * (‖coordL V i‖ * M) ^ 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE (by positivity))
      _ = Ce * (‖coordL V i‖ * M) := by
          rw [hCe, ← Real.sqrt_sq (by positivity : 0 ≤ ‖coordL V i‖ * M), ← Real.sqrt_mul
            (by positivity)]
          congr 1
          field_simp
          rw [Real.sq_sqrt (by positivity)]
  -- assemble
  have hstep1 : TrigInterp.tau n K j u ≤
      2 * Cb * ∑ i, SobolevReader.tail (SobolevReader.box (TrigInterp.half n)) j Kn
        (GaugeReaderTail.coefMode (sampC (n := n) h (F i))) := by
    calc TrigInterp.tau n K j u = ∑ ℓ ∈ TrigInterp.tailBox n K, (1 + VecTrig.l1 ℓ / K) ^ j *
          VecTrig.cn (TrigInterp.coefOf n u) ℓ := rfl
      _ ≤ ∑ ℓ ∈ TrigInterp.tailBox n K, (1 + SobolevReader.l1 ℓ / Kn) ^ j *
          (2 * Cb * ∑ i, ‖GaugeReaderTail.coefMode (sampC (n := n) h (F i)) ℓ‖) := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          have hl : VecTrig.l1 ℓ = SobolevReader.l1 ℓ := rfl
          have hl0 : 0 ≤ SobolevReader.l1 ℓ := SobolevReader.l1_nonneg ℓ
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) ?_ j) (hcn ℓ)
            (VecTrig.cn_nonneg _ _) (by positivity)
          rw [hl]
          gcongr
      _ ≤ ∑ ℓ ∈ (SobolevReader.box (TrigInterp.half n)).filter
            (fun ℓ => Kn < SobolevReader.linf ℓ),
          (1 + SobolevReader.l1 ℓ / Kn) ^ j *
          (2 * Cb * ∑ i, ‖GaugeReaderTail.coefMode (sampC (n := n) h (F i)) ℓ‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg (tailBox_subset hK) fun ℓ _ _ => by
            have := SobolevReader.l1_nonneg ℓ
            positivity
      _ = 2 * Cb * ∑ i, SobolevReader.tail (SobolevReader.box (TrigInterp.half n)) j Kn
            (GaugeReaderTail.coefMode (sampC (n := n) h (F i))) := by
          unfold SobolevReader.tail
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ℓ _ => ?_
          ring
  have hKpow : (Kn : ℝ) ^ (2 - (q : ℝ)) ≤ 2 ^ ((q : ℝ) - 2) * K ^ (2 - (q : ℝ)) := by
    have hK2 : K / 2 ≤ Kn := by
      have := Nat.lt_floor_add_one K
      have h1 : (1 : ℝ) ≤ Kn := by exact_mod_cast hKn1
      linarith
    have h1 : (Kn : ℝ) ^ (2 - (q : ℝ)) ≤ (K / 2) ^ (2 - (q : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hK2 (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [Real.div_rpow hK0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    rw [neg_sub]; ring
  calc TrigInterp.tau n K j u
      ≤ 2 * Cb * ∑ i, SobolevReader.tail (SobolevReader.box (TrigInterp.half n)) j Kn
        (GaugeReaderTail.coefMode (sampC (n := n) h (F i))) := hstep1
    _ ≤ 2 * Cb * ∑ i, Ct * (Kn : ℝ) ^ (2 - (q : ℝ)) * (Ce * (‖coordL V i‖ * M)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => htail i) (by positivity)
    _ = 2 * Cb * Ct * Ce * Λ * M * (Kn : ℝ) ^ (2 - (q : ℝ)) := by
        rw [hΛ]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 2 * Cb * Ct * Ce * Λ * M * (2 ^ ((q : ℝ) - 2) * K ^ (2 - (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = 2 * Cb * Ct * Ce * Λ * 2 ^ ((q : ℝ) - 2) * M * K ^ (2 - (q : ℝ)) := by ring

end Tail

end RenewalGeometry.SampledTail
