/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.FrobeniusCoulombNormalization
import RenewalGeometry.GaugeTheory.CoulombTraceConstraint
import RenewalGeometry.Analysis.MatrixDetExp

/-!
# Finite Coulomb normalization for `SU(N)`
  (`thm:finite-Coulomb-normalization` for a determinant-constrained gauge group)

For traceless skew-Hermitian seeds, the Coulomb homotopy keeps the logarithmic links traceless
(`CoulombTrace.trace_linkA_of_solution` with `τ = tr`).  Then `det(q_x) det(q_{x+μ})^* = 1`
on every link (`det e^{hA} = e^{tr hA} = 1`), so `det q` is constant on the connected periodic
grid, and a constant central phase `λ`, `λ^N = (det q)⁻¹`, produces an `SU(N)` gauge with the
same Coulomb representative.  This yields `finite_coulomb_normalization_special_unitary`: the
theorem with the gauge group `SU(N)` (the gauge `q` has `det q_x = 1`, the connection is
traceless).  The same argument applies verbatim to `S(U(3) × U(2))` with
`τ = tr₃ + tr₂` and `det = det₃ · det₂`.
-/

open NormedSpace Finset Set

namespace RenewalGeometry.SpecialUnitaryCoulomb

open scoped Matrix.Norms.L2Operator
open FiniteCoulomb CoulombApriori FrobeniusCoulomb CoulombTrace SeriesLogChart GridSobolev

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The trace as a real-linear continuous map `Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ`. -/
def trCLM (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin N) ℝ ℂ)

theorem trCLM_apply (X : Matrix (Fin N) (Fin N) ℂ) : trCLM N X = X.trace := rfl

theorem trCLM_mul_comm (X Y : Matrix (Fin N) (Fin N) ℂ) : trCLM N (X * Y) = trCLM N (Y * X) :=
  Matrix.trace_mul_comm X Y

/-- `Re tr` as a real continuous linear functional. -/
def trRe (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := Complex.reCLM.comp (trCLM N)

/-- `Im tr` as a real continuous linear functional. -/
def trIm (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ := Complex.imCLM.comp (trCLM N)

theorem trRe_apply (X : Matrix (Fin N) (Fin N) ℂ) : trRe N X = X.trace.re := rfl

theorem trIm_apply (X : Matrix (Fin N) (Fin N) ℂ) : trIm N X = X.trace.im := rfl

theorem trRe_mul_comm (X Y : Matrix (Fin N) (Fin N) ℂ) : trRe N (X * Y) = trRe N (Y * X) := by
  rw [trRe_apply, trRe_apply, Matrix.trace_mul_comm]

theorem trIm_mul_comm (X Y : Matrix (Fin N) (Fin N) ℂ) : trIm N (X * Y) = trIm N (Y * X) := by
  rw [trIm_apply, trIm_apply, Matrix.trace_mul_comm]

theorem det_unitary_mul_star {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ unitary _) :
    u.det * star u.det = 1 := by
  have := congrArg Matrix.det (Unitary.mul_star_self_of_mem hu)
  rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one]
    at this

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- **`thm:finite-Coulomb-normalization` for `SU(N)`** (Frobenius metric): for traceless
skew-Hermitian seeds the normalizing gauge can be chosen in `SU(N)` and the Coulomb representative
is traceless. -/
theorem finite_coulomb_normalization_special_unitary (N : ℕ) [NeZero N]
    (hι : Fintype.card ι = 4) {L : ℝ} (hL : 0 < L) {εstar : ℝ} (hεstar : 0 < εstar) :
    ∃ εc Cc : ℝ, 0 < εc ∧ 0 < Cc ∧ ∀ (n : ℕ) [NeZero n] (h : ℝ), 0 < h → (n : ℝ) * h = L →
      ∀ B : ι → (ι → ZMod n) → Matrix (Fin N) (Fin N) ℂ, (∀ μ x, star (B μ x) = -B μ x) →
      (∀ μ x, (B μ x).trace = 0) →
      oneL4 h (frobT (Fin N)) B + curvL2 h (frobT (Fin N)) B ≤ εc →
      ∃ q : (ι → ZMod n) → Matrix (Fin N) (Fin N) ℂ,
        (∀ x, q x ∈ unitary (Matrix (Fin N) (Fin N) ℂ) ∧ (q x).det = 1) ∧
        (∀ μ x, star (linkA h B 1 q μ x) = -linkA h B 1 q μ x) ∧
        (∀ μ x, (linkA h B 1 q μ x).trace = 0) ∧
        periodicHodgeCodiff h gridStep (bar (frobT (Fin N)) (linkA h B 1 q)) = 0 ∧
        oneH1 h (frobT (Fin N)) (linkA h B 1 q) + oneL4 h (frobT (Fin N)) (linkA h B 1 q) ≤
          Cc * (oneL2 h (frobT (Fin N)) B + curvL2 h (frobT (Fin N)) B +
            oneL4 h (frobT (Fin N)) B ^ 2) ∧
        oneL4 h (frobT (Fin N)) (linkA h B 1 q) ≤ εstar := by
  obtain ⟨εc, Cc, hεc, hCc, H⟩ := finite_coulomb_normalization_unitary (ι := ι) N hι hL hεstar
  refine ⟨εc, Cc, hεc, hCc, fun n _ h hh hnh B hB htrB hs => ?_⟩
  obtain ⟨q, hu, -, hskew, hcod, hest, hsmall, γ, hγ0, hγ1, hO, hd⟩ := H n h hh hnh B hB hs
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- tracelessness of the Coulomb representative
  have hreB : ∀ μ x, trRe N (B μ x) = 0 := fun μ x => by
    rw [trRe_apply, htrB μ x, Complex.zero_re]
  have himB : ∀ μ x, trIm N (B μ x) = 0 := fun μ x => by
    rw [trIm_apply, htrB μ x, Complex.zero_im]
  have hre1 := trace_linkA_of_solution (T := 1) (γ := γ) frobE (trRe N) hι trRe_mul_comm hh hB
    hreB hγ0
  have hre2 := hre1 hO
  have hre3 := hre2 hd
  have hre := hre3 1 h1mem
  have him1 := trace_linkA_of_solution (T := 1) (γ := γ) frobE (trIm N) hι trIm_mul_comm hh hB
    himB hγ0
  have him2 := him1 hO
  have him3 := him2 hd
  have him := him3 1 h1mem
  rw [hγ1] at hre him
  have htrA : ∀ μ x, (linkA h B 1 q μ x).trace = 0 := by
    intro μ x
    apply Complex.ext
    · rw [← trRe_apply]; exact hre μ x
    · rw [← trIm_apply]; exact him μ x
  -- `det q` is constant
  have hp := hO 1 h1mem
  rw [hγ1] at hp
  have hlink : ∀ μ x, (q x).det * star (q (x + gridStep μ)).det = 1 := by
    intro μ x
    have hexp : exp (h • linkA h B 1 q μ x) = linkP h B 1 q μ x := by
      rw [h_smul_linkA hh.ne', exp_logChart (hp.1 μ x)]
    have hd1 : (exp (h • linkA h B 1 q μ x)).det = 1 := by
      have := MatrixDetExp.det_exp_eq_complex_exp_trace (h • linkA h B 1 q μ x)
      rw [Matrix.trace_smul, htrA, smul_zero, Complex.exp_zero] at this
      convert this using 2
    have hd2 : (exp ((1 : ℝ) • (h • B μ x))).det = 1 := by
      have := MatrixDetExp.det_exp_eq_complex_exp_trace ((1 : ℝ) • (h • B μ x))
      rw [Matrix.trace_smul, Matrix.trace_smul, htrB, smul_zero, smul_zero,
        Complex.exp_zero] at this
      convert this using 2
    rw [hexp, linkP, Matrix.det_mul, Matrix.det_mul, hd2, mul_one, Matrix.star_eq_conjTranspose,
      Matrix.det_conjTranspose] at hd1
    exact hd1
  have hstep : ∀ μ x, (q (x + gridStep μ)).det = (q x).det := by
    intro μ x
    have h1 := hlink μ x
    have h2 := det_unitary_mul_star (hu (x + gridStep μ))
    calc (q (x + gridStep μ)).det = (q x).det * star (q (x + gridStep μ)).det *
          (q (x + gridStep μ)).det := by rw [h1, one_mul]
      _ = (q x).det * ((q (x + gridStep μ)).det * star (q (x + gridStep μ)).det) := by ring
      _ = (q x).det := by rw [h2, mul_one]
  have hconst : ∀ x, (q x).det = (q 0).det := fun x =>
    FaddeevPopov.eq_const_of_fwd_zero (fun y => (q y).det) (fun i y => hstep i y) x
  -- the central correction
  set d := (q 0).det
  have hd : d * star d = 1 := det_unitary_mul_star (hu 0)
  have hd0 : d ≠ 0 := by intro h0; rw [h0, zero_mul] at hd; exact zero_ne_one hd
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq d⁻¹ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hnd : Complex.normSq d = 1 := by
    have := hd
    rw [Complex.star_def, Complex.mul_conj] at this
    exact_mod_cast this
  have hnc : Complex.normSq c = 1 := by
    have := congrArg Complex.normSq hc
    rw [map_pow, map_inv₀, hnd, inv_one] at this
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg c) (NeZero.ne N)).1 this
  have hcabs : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hnc, Complex.ofReal_one]
  have hcabs' : star c * c = 1 := by rw [mul_comm, hcabs]
  set q' : (ι → ZMod n) → Matrix (Fin N) (Fin N) ℂ := fun x => c • q x with hq'
  have hlinkP : ∀ μ x, linkP h B 1 q' μ x = linkP h B 1 q μ x := by
    intro μ x
    simp only [linkP, hq', star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hcabs', one_smul]
  have hA : linkA h B 1 q' = linkA h B 1 q := by
    funext μ x; simp only [linkA, hlinkP]
  refine ⟨q', fun x => ⟨?_, ?_⟩, by rw [hA]; exact hskew, by rw [hA]; exact htrA,
    by rw [hA]; exact hcod, by rw [hA]; exact hest, by rw [hA]; exact hsmall⟩
  · rw [Unitary.mem_iff]
    have hu' := Unitary.mem_iff.1 (hu x)
    simp only [hq', star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu'.1, hu'.2]
    exact ⟨by rw [hcabs, one_smul], by rw [hcabs', one_smul]⟩
  · rw [hq', Matrix.det_smul, Fintype.card_fin, hc, hconst x, inv_mul_cancel₀ hd0]

end

end RenewalGeometry.SpecialUnitaryCoulomb
