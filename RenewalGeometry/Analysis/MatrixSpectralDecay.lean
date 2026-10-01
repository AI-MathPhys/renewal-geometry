/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovExponentialGrowth

/-!
# Exponential decay of `exp (-s J)` for a matrix with spectrum in the open right half-plane

Let `J` be a real square matrix whose complex spectrum (the spectrum of `J` viewed as a complex
matrix) lies in the open right half-plane `{Re z > 0}`.  We prove:

* `exp_mulVec_of_mulVec_eq_smul`: the matrix exponential acts on an eigenvector of `A` with
  eigenvalue `c` by the scalar `exp c`;
* `mem_spectrum_exp_neg`: every point of the spectrum of `exp (-Jc)` is `exp (-c)` for some `c`
  in the spectrum of `Jc` (the needed half of the spectral mapping theorem, via a common
  eigenvector of the commuting matrices `Jc` and `exp (-Jc)`);
* `tendsto_norm_exp_neg_pow`: by **Gelfand's formula**, `‖exp (-Jc) ^ k‖ → 0`;
* `exists_norm_exp_neg_smul_le_half`: for the real operator `A = toEuclideanCLM J` on
  `EuclideanSpace ℝ n` there is `T > 0` with `‖exp (-T • A)‖ ≤ 1/2`;
* `matrix_lyapunov_exponential_growth`: hence (by `LyapunovGrowth.lyapunov_exponential_growth`)
  there are `ε, c, μ > 0` such that every solution of `v' = N(s) v` with `‖N(s) - J‖ ≤ ε`
  (operator norm) satisfies `c e^{μ s} ‖v 0‖ ≤ ‖v s‖ ≤ e^{(‖J‖+ε) s} ‖v 0‖`.

This supplies the rapid normal growth of `prop:supp-exact-normal-growth`
(emergent-spacetime manuscript), where the paper's proof uses the Lyapunov matrix
`W = ∫₀^∞ e^{-rJ*} e^{-rJ} dr`; here the finite-horizon Gramian of
`RenewalGeometry/Analysis/LyapunovExponentialGrowth.lean` is used instead, which needs only the
decay `‖e^{-TJ}‖ ≤ 1/2` at one time `T`.
-/

open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator NNReal ENNReal

namespace RenewalGeometry

namespace MatrixSpectralDecay

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem algebraMap_mulVec (μ : ℂ) (w : n → ℂ) :
    algebraMap ℂ (Matrix n n ℂ) μ *ᵥ w = μ • w := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- The matrix exponential acts on an eigenvector by the exponential of the eigenvalue. -/
theorem exp_mulVec_of_mulVec_eq_smul (A : Matrix n n ℂ) (u : n → ℂ) (c : ℂ)
    (h : A *ᵥ u = c • u) : NormedSpace.exp A *ᵥ u = Complex.exp c • u := by
  have hpow : ∀ k : ℕ, (A ^ k) *ᵥ u = c ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]
  have h1 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k)) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  let Φ : Matrix n n ℂ →+ (n → ℂ) :=
    { toFun := fun B => B *ᵥ u
      map_zero' := Matrix.zero_mulVec u
      map_add' := fun B C => Matrix.add_mulVec B C u }
  have hΦ : Continuous Φ := Continuous.matrix_mulVec continuous_id continuous_const
  have h2 := h1.map Φ hΦ
  have h3 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ * c ^ k) • u) (Complex.exp c • u) := by
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa [smul_eq_mul] using this.smul_const u
  have h4 : (Φ ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k)) =
      fun k : ℕ => ((k.factorial : ℂ)⁻¹ * c ^ k) • u := by
    funext k
    simp only [Function.comp_apply, Φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Matrix.smul_mulVec, hpow, smul_smul]
  rw [h4] at h2
  exact h2.unique h3

/-- Spectral inclusion for the exponential: every spectral value of `exp (-Jc)` has the form
`exp (-c)` with `c` in the spectrum of `Jc`. -/
theorem mem_spectrum_exp_neg {Jc : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (NormedSpace.exp (-Jc))) :
    ∃ c ∈ spectrum ℂ Jc, μ = Complex.exp (-c) := by
  set E := NormedSpace.exp (-Jc) with hE
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨u0, hu0, hu0'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  set B := algebraMap ℂ (Matrix n n ℂ) μ - E with hB
  have hcommE : Commute Jc E := ((Commute.refl Jc).neg_right).exp_right
  have hcommB : Commute B Jc := by
    rw [hB]
    exact (Algebra.commute_algebraMap_left μ Jc).sub_left hcommE.symm
  let K : Submodule ℂ (n → ℂ) := LinearMap.ker (Matrix.toLin' B)
  have hmemK : ∀ w, w ∈ K ↔ B *ᵥ w = 0 := fun w => by
    simp [K, Matrix.toLin'_apply]
  have hK : ∀ w ∈ K, Matrix.toLin' Jc w ∈ K := by
    intro w hw
    rw [hmemK] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcommB.eq, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  let f : Module.End ℂ K := (Matrix.toLin' Jc).restrict hK
  have : Nontrivial K := ⟨⟨⟨u0, (hmemK u0).2 hu0'⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hfw : f w = c • w := hw.apply_eq_smul
  have hw0 : (w : n → ℂ) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hJw : Jc *ᵥ (w : n → ℂ) = c • (w : n → ℂ) := by
    have := congrArg Subtype.val hfw
    simpa [f, Matrix.toLin'_apply] using this
  have hBw : B *ᵥ (w : n → ℂ) = 0 := (hmemK w).1 w.2
  have hEw : E *ᵥ (w : n → ℂ) = μ • (w : n → ℂ) := by
    rw [hB, Matrix.sub_mulVec, algebraMap_mulVec, sub_eq_zero] at hBw
    exact hBw.symm
  have hEw' : E *ᵥ (w : n → ℂ) = Complex.exp (-c) • (w : n → ℂ) :=
    exp_mulVec_of_mulVec_eq_smul (-Jc) w (-c) (by rw [Matrix.neg_mulVec, hJw, neg_smul])
  refine ⟨c, ?_, ?_⟩
  · rw [spectrum.mem_iff]
    intro hunit
    have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hunit
    apply hw0
    apply hinj
    rw [Matrix.sub_mulVec, algebraMap_mulVec, hJw, sub_self, Matrix.mulVec_zero]
  · have : (μ - Complex.exp (-c)) • (w : n → ℂ) = 0 := by
      rw [sub_smul, ← hEw, ← hEw', sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hw0

/-- `exp (k • x) = exp x ^ k` in a complex Banach algebra. -/
theorem exp_nsmul_eq_pow {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (x : 𝔸) (k : ℕ) : NormedSpace.exp (k • x) = NormedSpace.exp x ^ k := by
  have hrad := NormedSpace.expSeries_radius_eq_top ℂ 𝔸
  induction k with
  | zero => simp [NormedSpace.exp_zero]
  | succ k ih =>
    rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
      ((Commute.refl x).smul_left k) (hrad.symm ▸ edist_lt_top _ _)
      (hrad.symm ▸ edist_lt_top _ _), ih, pow_succ]

/-- **Gelfand decay.**  If the spectrum of `Jc` lies in the open right half-plane, then
`‖exp (-Jc) ^ k‖ → 0` (operator norm on `EuclideanSpace ℂ n`). -/
theorem tendsto_norm_exp_neg_pow (Jc : Matrix n n ℂ) (h : ∀ c ∈ spectrum ℂ Jc, 0 < c.re) :
    Tendsto (fun k : ℕ => ‖NormedSpace.exp (-Jc) ^ k‖) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : ∀ k : ℕ, ‖NormedSpace.exp (-Jc) ^ k‖ = 0 := fun k => by
      rw [Subsingleton.elim (NormedSpace.exp (-Jc) ^ k) 0, norm_zero]
    simp only [this]
    exact tendsto_const_nhds
  set a := NormedSpace.exp (-Jc)
  have hρ : spectralRadius ℂ a < 1 := by
    have := spectrum.spectralRadius_lt_of_forall_lt a (r := 1) (fun z hz => by
      obtain ⟨c, hc, rfl⟩ := mem_spectrum_exp_neg hz
      have h1 : ‖Complex.exp (-c)‖ < 1 := by
        rw [Complex.norm_exp, Complex.neg_re]
        calc Real.exp (-c.re) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith [h c hc])
          _ = 1 := Real.exp_zero
      exact_mod_cast h1)
    simpa using this
  obtain ⟨θ, hρθ, hθ1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hρ
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
    (gt_mem_nhds hρθ)
  have hbound : ∀ᶠ k : ℕ in atTop, ‖a ^ k‖ ≤ (θ : ℝ) ^ k := by
    filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
    have hk' : ‖a ^ k‖ ^ (1 / k : ℝ) < θ := by
      have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top).1 hk
      simpa using this
    have hkne : k ≠ 0 := by omega
    have hpow := pow_le_pow_left₀ (by positivity) hk'.le k
    rwa [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hkne] at hpow
  have hθ0 : Tendsto (fun k : ℕ => (θ : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one θ.2 hθ1'
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hθ0

/-- The real operator norm is bounded by the norm of the complexified matrix. -/
theorem norm_toEuclideanCLM_le_map_ofReal (B : Matrix n n ℝ) :
    ‖toEuclideanCLM (𝕜 := ℝ) B‖ ≤ ‖B.map (algebraMap ℝ ℂ)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  let xc : EuclideanSpace ℂ n := WithLp.toLp 2 (fun i => (x.ofLp i : ℂ))
  have hx : ‖xc‖ = ‖x‖ := by
    simp [xc, EuclideanSpace.norm_eq, Complex.norm_real]
  have hy : ‖toEuclideanCLM (𝕜 := ℝ) B x‖ = ‖toEuclideanCLM (𝕜 := ℂ) (B.map (algebraMap ℝ ℂ)) xc‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM]
    have h' : ((B *ᵥ x.ofLp) i : ℂ) =
        (B.map (algebraMap ℝ ℂ) *ᵥ fun j => (x.ofLp j : ℂ)) i := by
      simpa [Function.comp_def] using RingHom.map_mulVec (algebraMap ℝ ℂ) B x.ofLp i
    simp only [xc]
    rw [← h', Complex.norm_real]
  rw [hy, ← hx]
  exact (toEuclideanCLM (𝕜 := ℂ) (B.map (algebraMap ℝ ℂ))).le_opNorm xc

theorem continuous_toEuclideanCLM_real :
    Continuous (toEuclideanCLM (n := n) (𝕜 := ℝ)) :=
  AddMonoidHomClass.continuous_of_bound (toEuclideanCLM (n := n) (𝕜 := ℝ)) 1
    (fun B => by rw [one_mul]; exact le_of_eq rfl)

/-- **Decay at one time.**  If the complex spectrum of the real matrix `J` lies in the open right
half-plane, there is `T > 0` with `‖exp (-T • A)‖ ≤ 1/2` for `A = toEuclideanCLM J`. -/
theorem exists_norm_exp_neg_smul_le_half (J : Matrix n n ℝ)
    (h : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re) :
    ∃ T : ℝ, 0 < T ∧ ‖NormedSpace.exp ((-T) • toEuclideanCLM (𝕜 := ℝ) J)‖ ≤ 1 / 2 := by
  set Jc := J.map (algebraMap ℝ ℂ)
  have hev := (tendsto_norm_exp_neg_pow Jc h).eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 2))
  obtain ⟨k, hk, hk1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  refine ⟨k, by exact_mod_cast hk1, ?_⟩
  have hradR := NormedSpace.expSeries_radius_eq_top ℝ (Matrix n n ℝ)
  have hmap1 : NormedSpace.exp ((-(k : ℝ)) • toEuclideanCLM (𝕜 := ℝ) J) =
      toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp ((-(k : ℝ)) • J)) := by
    rw [NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) toEuclideanCLM continuous_toEuclideanCLM_real _
      (hradR.symm ▸ edist_lt_top _ _), map_smul]
  have hmap2 : (NormedSpace.exp ((-(k : ℝ)) • J)).map (algebraMap ℝ ℂ) =
      NormedSpace.exp (-Jc) ^ k := by
    have hf : Continuous fun M : Matrix n n ℝ => M.map (algebraMap ℝ ℂ) :=
      continuous_id.matrix_map Complex.continuous_ofReal
    have := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) ((algebraMap ℝ ℂ).mapMatrix) hf
      ((-(k : ℝ)) • J) (hradR.symm ▸ edist_lt_top _ _)
    rw [RingHom.mapMatrix_apply] at this
    rw [this, ← exp_nsmul_eq_pow]
    congr 1
    ext i j
    simp [Jc]
  calc ‖NormedSpace.exp ((-(k : ℝ)) • toEuclideanCLM (𝕜 := ℝ) J)‖
      = ‖toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp ((-(k : ℝ)) • J))‖ := by rw [hmap1]
    _ ≤ ‖(NormedSpace.exp ((-(k : ℝ)) • J)).map (algebraMap ℝ ℂ)‖ :=
        norm_toEuclideanCLM_le_map_ofReal _
    _ = ‖NormedSpace.exp (-Jc) ^ k‖ := by rw [hmap2]
    _ ≤ 1 / 2 := hk.le


/-- **Rapid Lyapunov growth for matrices.**  Let `J` be a real `n × n` matrix whose complex
spectrum lies in the open right half-plane.  There are `ε, c, μ > 0` such that for every `S`,
every matrix path `N` with `‖N s - J‖ ≤ ε` (operator norm) on `[0, S]`, and every solution of
`v' = N(s) v` on `[0, S]`,
`c e^{μ s} ‖v 0‖ ≤ ‖v s‖ ≤ e^{(‖J‖ + ε) s} ‖v 0‖`. -/
theorem matrix_lyapunov_exponential_growth (J : Matrix n n ℝ)
    (h : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re) :
    ∃ ε > 0, ∃ c > 0, ∃ μ > 0, ∀ (S : ℝ) (v : ℝ → EuclideanSpace ℝ n) (N : ℝ → Matrix n n ℝ),
      (∀ s ∈ Icc 0 S, HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℝ) (N s) (v s)) (Icc 0 S) s) →
      (∀ s ∈ Icc 0 S, ‖N s - J‖ ≤ ε) →
      ∀ s ∈ Icc 0 S, c * Real.exp (μ * s) * ‖v 0‖ ≤ ‖v s‖ ∧
        ‖v s‖ ≤ Real.exp ((‖J‖ + ε) * s) * ‖v 0‖ := by
  obtain ⟨T, hT, hdec⟩ := exists_norm_exp_neg_smul_le_half J h
  obtain ⟨ε, hε, c, hc, μ, hμ, H⟩ :=
    LyapunovGrowth.lyapunov_exponential_growth (toEuclideanCLM (𝕜 := ℝ) J) hT hdec
  refine ⟨ε, hε, c, hc, μ, hμ, fun S v N hv hN => ?_⟩
  have hN' : ∀ s ∈ Icc 0 S, ‖toEuclideanCLM (𝕜 := ℝ) (N s) - toEuclideanCLM (𝕜 := ℝ) J‖ ≤ ε :=
    fun s hs => by rw [← map_sub, ← Matrix.cstar_norm_def]; exact hN s hs
  intro s hs
  obtain ⟨h1, h2⟩ := H S v (fun s => toEuclideanCLM (𝕜 := ℝ) (N s)) hv hN' s hs
  refine ⟨h1, ?_⟩
  rwa [← Matrix.cstar_norm_def] at h2

end MatrixSpectralDecay

end RenewalGeometry
