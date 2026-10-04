/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevChainRule
import RenewalGeometry.Analysis.CovariantGradientCompactness

/-!
# The Kato inequality for unitary connections and the Kato–Sobolev graph estimate

Generic infrastructure (no renewal notions) for `lem:critical-positive-graph` of the
Einstein–Standard-Model action-closure manuscript.

Setting.  Sections are `m`-component complex fields `u = (u_c)_{c < m}` on an open set
`Ω ⊂ ℝ^ι`, with components in `W^{1,2}(Ω)` (`MemW12`, weak gradients `dU c μ`), and a
connection is given by its matrix entries `𝒜 μ c e : ℝ^ι → ℂ`; the covariant derivative is
`(∇^𝒜 u)_{cμ} = ∂_μ u_c + Σ_e 𝒜_{μce} u_e` (`covD` of `CovariantGradientCompactness.lean`).
The connection is **unitary** (metric compatible for the standard Hermitian fibre metric) when
every `𝒜_μ(x)` is skew-Hermitian (`IsSkewHermitianConn`).  The fibre norm is the Euclidean
(Hermitian) one, `|v| = (Σ_c |v_c|²)^{1/2}` (`fibreNorm`).

* `HasWeakPartial.re`, `HasWeakPartial.im`, `MemW12.re`, `MemW12.im`: real and imaginary parts
  of `W^{1,2}` functions;
* `re_sum_conj_mul_skew_eq_zero`, `kato_identity` (**pointwise Kato identity**): for a
  skew-Hermitian connection `Re⟨u, ∂_μ u⟩ = Re⟨u, ∇^𝒜_μ u⟩` pointwise;
* `memW12_regMod`: the regularised modulus `(|u|² + ε²)^{1/2}` lies in `W^{1,2}(Ω)` with weak
  gradient `Re⟨u, ∂_μ u⟩ / (|u|² + ε²)^{1/2}` (the weak chain rule `MemW12.comp` of
  `SobolevChainRule.lean` applied to the real and imaginary parts);
* `kato_regMod` (**Kato inequality, regularised form**): that weak gradient is bounded pointwise
  by `|∇^𝒜_μ u|`;
* `kato_sobolev_box` (**Kato–Sobolev**, `eq:critical-Kato-Sobolev`): on a coordinate box
  `Q ⊂ ℝ⁴`, `‖u_c‖_{L⁴(Q)} ≤ C_Q (Σ_e ‖u_e‖_{L²(Q)} + Σ_{e,μ} ‖∇^𝒜_μ u_e‖_{L²(Q)})` for every
  unitary connection — the constant does not depend on the connection;
* `covariant_graph_box` (**vector graph estimate**, `eq:critical-vector-graph`): for
  `𝒜 = Γ + A` with a bounded skew-Hermitian reference part `|Γ| ≤ G` and a skew-Hermitian
  `L⁴` part `‖A_{μce}‖_{L⁴(Q)} ≤ M_A`,
  `‖u_c‖_{W^{1,2}(Q)} ≤ C_{Q,G} (1 + M_A) (Σ_e ‖u_e‖_2 + Σ_{e,μ} ‖∇^𝒜_μ u_e‖_2)`;
* `dualConn`, `isSkewHermitianConn_dualConn`: the dual representation `-𝒜ᵀ` is again unitary,
  so both estimates hold for it (`kato_sobolev_box_dual`, `covariant_graph_box_dual`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Real and imaginary parts of `W^{1,2}` functions -/

/-- The real part of a function with weak partial `g` has weak partial `Re g`. -/
theorem HasWeakPartial.re {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (hu : LocallyIntegrableOn u Ω) (hg : LocallyIntegrableOn g Ω) :
    HasWeakPartial Ω i (fun x => (((u x).re : ℝ) : ℂ)) (fun x => (((g x).re : ℝ) : ℂ)) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have i1 := hφ.integrable_mul (ψ := pd φ i) (continuous_pd hφ1 i) (tsupport_pd_subset φ i) hu
  have i2 := hφ.integrable_mul (ψ := φ) hφ1.continuous subset_rfl hg
  have key := congrArg Complex.re (h φ hφ)
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * (((u x).re : ℝ) : ℂ)) =
      fun x => (((((pd φ i x : ℝ) : ℂ) * u x).re : ℝ) : ℂ) := by
    funext x; simp
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * (((g x).re : ℝ) : ℂ)) =
      fun x => (((((φ x : ℝ) : ℂ) * g x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e1, e2, integral_complex_ofReal, integral_complex_ofReal]
  have r1 := integral_re (𝕜 := ℂ) i1
  have r2 := integral_re (𝕜 := ℂ) i2
  simp only [RCLike.re_to_complex] at r1 r2
  rw [r1, r2, key, Complex.neg_re, Complex.ofReal_neg]

/-- The imaginary part of a function with weak partial `g` has weak partial `Im g`. -/
theorem HasWeakPartial.im {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (hu : LocallyIntegrableOn u Ω) (hg : LocallyIntegrableOn g Ω) :
    HasWeakPartial Ω i (fun x => (((u x).im : ℝ) : ℂ)) (fun x => (((g x).im : ℝ) : ℂ)) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have i1 := hφ.integrable_mul (ψ := pd φ i) (continuous_pd hφ1 i) (tsupport_pd_subset φ i) hu
  have i2 := hφ.integrable_mul (ψ := φ) hφ1.continuous subset_rfl hg
  have key := congrArg Complex.im (h φ hφ)
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * (((u x).im : ℝ) : ℂ)) =
      fun x => (((((pd φ i x : ℝ) : ℂ) * u x).im : ℝ) : ℂ) := by
    funext x; simp
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * (((g x).im : ℝ) : ℂ)) =
      fun x => (((((φ x : ℝ) : ℂ) * g x).im : ℝ) : ℂ) := by
    funext x; simp
  rw [e1, e2, integral_complex_ofReal, integral_complex_ofReal]
  have r1 := integral_im (𝕜 := ℂ) i1
  have r2 := integral_im (𝕜 := ℂ) i2
  simp only [RCLike.im_to_complex] at r1 r2
  rw [r1, r2, key, Complex.neg_im, Complex.ofReal_neg]

theorem MemW12.re {Ω : Set (ι → ℝ)} {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 Ω u g) :
    MemW12 Ω (fun x => (((u x).re : ℝ) : ℂ)) (fun i x => (((g i x).re : ℝ) : ℂ)) := by
  refine ⟨?_, fun i => ?_, fun i => (hW.weak i).re (locallyIntegrableOn_of_memLp hW.memLp)
    (locallyIntegrableOn_of_memLp (hW.memLp_grad i))⟩
  · exact hW.memLp.re.ofReal
  · exact (hW.memLp_grad i).re.ofReal

theorem MemW12.im {Ω : Set (ι → ℝ)} {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 Ω u g) :
    MemW12 Ω (fun x => (((u x).im : ℝ) : ℂ)) (fun i x => (((g i x).im : ℝ) : ℂ)) := by
  refine ⟨?_, fun i => ?_, fun i => (hW.weak i).im (locallyIntegrableOn_of_memLp hW.memLp)
    (locallyIntegrableOn_of_memLp (hW.memLp_grad i))⟩
  · exact hW.memLp.im.ofReal
  · exact (hW.memLp_grad i).im.ofReal

/-! ### Fibre algebra: unitary connections and the pointwise Kato identity -/

/-- A connection (given by matrix entries `𝒜 μ c e`) is **unitary** (compatible with the standard
Hermitian fibre metric): every `𝒜_μ(x)` is skew-Hermitian. -/
def IsSkewHermitianConn {m : ℕ} (𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ) : Prop :=
  ∀ μ c e x, 𝒜 μ e c x = -star (𝒜 μ c e x)

/-- The Euclidean (Hermitian) fibre norm `|v| = (Σ_c |v_c|²)^{1/2}` on `ℂ^m`. -/
def fibreNorm {m : ℕ} (v : Fin m → ℂ) : ℝ := √(∑ c, ‖v c‖ ^ 2)

theorem fibreNorm_nonneg {m : ℕ} (v : Fin m → ℂ) : 0 ≤ fibreNorm v := Real.sqrt_nonneg _

theorem fibreNorm_le_sum {m : ℕ} (v : Fin m → ℂ) : fibreNorm v ≤ ∑ c, ‖v c‖ := by
  unfold fibreNorm
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _

theorem norm_le_fibreNorm {m : ℕ} (v : Fin m → ℂ) (c : Fin m) : ‖v c‖ ≤ fibreNorm v := by
  unfold fibreNorm
  rw [← Real.sqrt_sq (norm_nonneg (v c))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => ‖v c‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ c))

/-- `Re⟨v, M v⟩ = 0` for a skew-Hermitian matrix `M`. -/
theorem re_sum_conj_mul_skew_eq_zero {m : ℕ} (M : Fin m → Fin m → ℂ)
    (hM : ∀ c e, M e c = -star (M c e)) (v : Fin m → ℂ) :
    (∑ c, conj (v c) * ∑ e, M c e * v e).re = 0 := by
  set S := ∑ c, conj (v c) * ∑ e, M c e * v e with hS
  have hc : ∀ c e, conj (M c e) = -M e c := by
    intro c e; rw [hM c e]; simp
  have h : conj S = -S := by
    have e1 : conj S = ∑ c, ∑ e, v c * (-M e c) * conj (v e) := by
      simp only [hS, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, hc]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
    have e2 : S = ∑ e, ∑ c, conj (v e) * (M e c * v c) := by
      simp only [hS, Finset.mul_sum]
    rw [e1, e2, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => by ring
  have := congrArg Complex.re h
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith

/-- **Pointwise Kato identity.**  For a unitary connection,
`Re⟨u, ∂_μ u⟩ = Re⟨u, ∇^𝒜_μ u⟩` at every point. -/
theorem kato_identity {m : ℕ} {dU : Fin m → ι → (ι → ℝ) → ℂ}
    {𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ} (h𝒜 : IsSkewHermitianConn 𝒜)
    (u : Fin m → (ι → ℝ) → ℂ) (μ : ι) (x : ι → ℝ) :
    (∑ c, conj (u c x) * dU c μ x).re = (∑ c, conj (u c x) * covD dU 𝒜 u c μ x).re := by
  have h0 := re_sum_conj_mul_skew_eq_zero (fun c e => 𝒜 μ c e x) (fun c e => h𝒜 μ c e x)
    (fun c => u c x)
  simp only [covD, mul_add, Finset.sum_add_distrib, Complex.add_re, h0, add_zero]

/-- Cauchy–Schwarz in the fibre: `|Re⟨a, b⟩| ≤ |a| |b|`. -/
theorem abs_re_sum_conj_mul_le {m : ℕ} (a b : Fin m → ℂ) :
    |(∑ c, conj (a c) * b c).re| ≤ fibreNorm a * fibreNorm b := by
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  simp only [norm_mul, Complex.norm_conj]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-! ### The regularised modulus -/

/-- Real and imaginary parts of `v ∈ ℂ^m` as a vector of `ℝ^{m × 2}`. -/
def reIm {m : ℕ} (v : Fin m → ℂ) : Fin m × Bool → ℝ :=
  fun k => bif k.2 then (v k.1).re else (v k.1).im

theorem sum_sq_reIm {m : ℕ} (v : Fin m → ℂ) : ∑ k, reIm v k ^ 2 = ∑ c, ‖v c‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [reIm, Bool.cond_true, Bool.cond_false]
  ring

/-- The regularised modulus `R_ε(y) = (Σ_k y_k² + ε²)^{1/2}` on `ℝ^κ`. -/
def regMod {κ : Type*} [Fintype κ] (ε : ℝ) (y : κ → ℝ) : ℝ := √(∑ k, y k ^ 2 + ε ^ 2)

section RegMod

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem regMod_sq_pos {ε : ℝ} (hε : ε ≠ 0) (y : κ → ℝ) : 0 < ∑ k, y k ^ 2 + ε ^ 2 := by
  have := Finset.sum_nonneg (s := Finset.univ) fun k (_ : k ∈ Finset.univ) => sq_nonneg (y k)
  have := pow_pos (abs_pos.mpr hε) 2
  rw [sq_abs] at this
  linarith

theorem regMod_pos {ε : ℝ} (hε : ε ≠ 0) (y : κ → ℝ) : 0 < regMod ε y :=
  Real.sqrt_pos.mpr (regMod_sq_pos hε y)

theorem hasFDerivAt_regMod {ε : ℝ} (hε : ε ≠ 0) (y : κ → ℝ) :
    HasFDerivAt (regMod ε) ((1 / (2 * regMod ε y)) •
      ∑ k, ((2 : ℕ) • y k ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k) y := by
  have hq : HasFDerivAt (fun z : κ → ℝ => ∑ k, z k ^ 2 + ε ^ 2)
      (∑ k, ((2 : ℕ) • y k ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k) y := by
    have := HasFDerivAt.sum (u := Finset.univ) fun k _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) k y).pow 2
    exact (this.add_const (ε ^ 2)).congr_of_eventuallyEq (Eventually.of_forall fun z => by simp)
  exact hq.sqrt (regMod_sq_pos hε y).ne'

theorem fderiv_regMod_single {ε : ℝ} (hε : ε ≠ 0) (y : κ → ℝ) (k : κ) :
    fderiv ℝ (regMod ε) y (Pi.single k 1) = y k / regMod ε y := by
  rw [(hasFDerivAt_regMod hε y).fderiv]
  have h0 := (regMod_pos hε y).ne'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

theorem contDiff_regMod {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (regMod (κ := κ) ε) := by
  unfold regMod
  refine ContDiff.sqrt ?_ fun y => (regMod_sq_pos hε y).ne'
  exact (ContDiff.sum fun k _ => (contDiff_apply ℝ ℝ k).pow 2).add contDiff_const

theorem abs_le_regMod (ε : ℝ) (y : κ → ℝ) (k : κ) : |y k| ≤ regMod ε y := by
  unfold regMod
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have := Finset.single_le_sum (f := fun k => y k ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ k)
  nlinarith [sq_nonneg ε]

theorem norm_fderiv_regMod_le {ε : ℝ} (hε : ε ≠ 0) (y : κ → ℝ) :
    ‖fderiv ℝ (regMod ε) y‖ ≤ (Fintype.card κ : ℝ≥0) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [clm_apply_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ k, ‖v k * fderiv ℝ (regMod ε) y (Pi.single k 1)‖ ≤ ‖v‖ := by
    intro k
    rw [fderiv_regMod_single hε, norm_mul, Real.norm_eq_abs (y k / _), abs_div,
      abs_of_pos (regMod_pos hε y)]
    have h1 : |y k| / regMod ε y ≤ 1 :=
      (div_le_one (regMod_pos hε y)).mpr (abs_le_regMod ε y k)
    calc ‖v k‖ * (|y k| / regMod ε y) ≤ ‖v k‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖v‖ := by rw [mul_one]; exact norm_le_pi_norm v k
  refine (Finset.sum_le_sum fun k _ => hb k).trans ?_
  simp

end RegMod

theorem regMod_reIm {m : ℕ} (ε : ℝ) (v : Fin m → ℂ) :
    regMod ε (reIm v) = √(∑ c, ‖v c‖ ^ 2 + ε ^ 2) := by
  unfold regMod; rw [sum_sq_reIm]

/-- **The regularised modulus is `W^{1,2}`.**  For `u_c ∈ W^{1,2}(Ω)` (`Ω` open, of finite
measure) and `ε ≠ 0`, `(|u|² + ε²)^{1/2} ∈ W^{1,2}(Ω)` with weak gradient
`Re⟨u, ∂_μ u⟩ / (|u|² + ε²)^{1/2}`. -/
theorem memW12_regMod {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) (hΩf : volume Ω ≠ ⊤) {m : ℕ}
    {u : Fin m → (ι → ℝ) → ℂ} {dU : Fin m → ι → (ι → ℝ) → ℂ} (hW : ∀ c, MemW12 Ω (u c) (dU c))
    {ε : ℝ} (hε : ε ≠ 0) :
    MemW12 Ω (fun x => ((√(∑ c, ‖u c x‖ ^ 2 + ε ^ 2) : ℝ) : ℂ))
      (fun μ x => (((∑ c, conj (u c x) * dU c μ x).re / √(∑ c, ‖u c x‖ ^ 2 + ε ^ 2) : ℝ) :
        ℂ)) := by
  set g : Fin m × Bool → ι → (ι → ℝ) → ℂ := fun k μ x =>
    bif k.2 then (((dU k.1 μ x).re : ℝ) : ℂ) else (((dU k.1 μ x).im : ℝ) : ℂ)
  have hWk : ∀ k : Fin m × Bool,
      MemW12 Ω (fun x => ((reIm (fun c => u c x) k : ℝ) : ℂ)) (g k) := by
    rintro ⟨c, b⟩
    cases b
    · exact (hW c).im
    · exact (hW c).re
  have h := MemW12.comp hΩ hΩf (u := fun k x => reIm (fun c => u c x) k) hWk
    (contDiff_regMod hε) (fun y => norm_fderiv_regMod_le hε y)
  have e1 : (fun x => ((regMod ε (fun k => reIm (fun c => u c x) k) : ℝ) : ℂ)) =
      fun x => ((√(∑ c, ‖u c x‖ ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [show (fun k => reIm (fun c => u c x) k) = reIm (fun c => u c x) from rfl, regMod_reIm]
  have e2 : (fun μ x => ((∑ k, fderiv ℝ (regMod ε) (fun k => reIm (fun c => u c x) k)
        (Pi.single k 1) * (g k μ x).re : ℝ) : ℂ)) =
      fun μ x => (((∑ c, conj (u c x) * dU c μ x).re / √(∑ c, ‖u c x‖ ^ 2 + ε ^ 2) : ℝ) :
        ℂ) := by
    funext μ x
    congr 1
    simp only [fderiv_regMod_single hε]
    rw [show (fun k => reIm (fun c => u c x) k) = reIm (fun c => u c x) from rfl, regMod_reIm,
      Fintype.sum_prod_type, Complex.re_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_bool]
    simp only [g, reIm, Bool.cond_true, Bool.cond_false, Complex.ofReal_re, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [e1, e2] at h
  exact h

/-- **Kato inequality (regularised form).**  For a unitary connection the weak gradient of the
regularised modulus satisfies `|∂_μ (|u|² + ε²)^{1/2}| ≤ |∇^𝒜_μ u|` pointwise. -/
theorem kato_regMod {m : ℕ} {dU : Fin m → ι → (ι → ℝ) → ℂ}
    {𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ} (h𝒜 : IsSkewHermitianConn 𝒜)
    (u : Fin m → (ι → ℝ) → ℂ) {ε : ℝ} (hε : ε ≠ 0) (μ : ι) (x : ι → ℝ) :
    ‖(∑ c, conj (u c x) * dU c μ x).re / √(∑ c, ‖u c x‖ ^ 2 + ε ^ 2)‖ ≤
      fibreNorm (fun c => covD dU 𝒜 u c μ x) := by
  have hpos : 0 < √(∑ c, ‖u c x‖ ^ 2 + ε ^ 2) := by
    rw [← regMod_reIm]; exact regMod_pos hε _
  rw [kato_identity h𝒜 u μ x, Real.norm_eq_abs, abs_div, abs_of_pos hpos,
    div_le_iff₀ hpos]
  refine (abs_re_sum_conj_mul_le (fun c => u c x) _).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (fibreNorm_nonneg _)
  unfold fibreNorm
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

/-! ### The Kato–Sobolev inequality on a box -/

/-- `ε`-absorption in `ℝ≥0∞`: `a ≤ b + K ε` for all `ε > 0` with `K < ∞` gives `a ≤ b`. -/
theorem le_of_forall_pos_le_add_mul' {a b K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ ε : ℝ≥0, 0 < ε → a ≤ b + K * ε) : a ≤ b := by
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set Kn := K.toNNReal
  have hKe : K = Kn := (ENNReal.coe_toNNReal hK).symm
  have hε : 0 < δ / (Kn + 1) := div_pos hδ (by positivity)
  refine (h _ hε).trans (add_le_add le_rfl ?_)
  rw [hKe, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_mul,
    NNReal.coe_div, NNReal.coe_add, NNReal.coe_one]
  have h1 : (0 : ℝ) ≤ Kn := Kn.2
  have h2 : (0 : ℝ) ≤ δ := δ.2
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- A pointwise bound by a finite sum of norms gives the `Lᵖ` triangle bound. -/
theorem eLpNorm_le_sum_of_le {X : Type*} [MeasurableSpace X] {ν : Measure X} {E : Type*}
    [NormedAddCommGroup E] {κ : Type*} [Fintype κ] {F : X → E} {G : κ → X → ℂ}
    (hG : ∀ k, AEStronglyMeasurable (G k) ν) (h : ∀ x, ‖F x‖ ≤ ∑ k, ‖G k x‖) {p : ℝ≥0∞}
    (hp : 1 ≤ p) : eLpNorm F p ν ≤ ∑ k, eLpNorm (G k) p ν := by
  have h1 : eLpNorm F p ν ≤ eLpNorm (∑ k, fun x => ‖G k x‖) p ν := by
    refine eLpNorm_mono fun x => ?_
    rw [Finset.sum_apply, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact h x
  refine h1.trans ((eLpNorm_sum_le (fun k _ => (hG k).norm) hp).trans ?_)
  simp only [eLpNorm_norm, le_refl]

/-- **Kato–Sobolev inequality on a box** (`eq:critical-Kato-Sobolev`).  On a coordinate box
`Q ⊂ ℝ⁴` there is `C_Q` such that for **every** unitary connection `𝒜` (measurable matrix
entries) and every section `u` with components in `W^{1,2}(Q)`,
`‖u_c‖_{L⁴(Q)} ≤ C_Q (Σ_e ‖u_e‖_{L²(Q)} + Σ_{e,μ} ‖∇^𝒜_μ u_e‖_{L²(Q)})`.
Proof: scalar Sobolev for `(|u|² + ε²)^{1/2}` (`memW12_regMod`, `exists_sobolev_L4_box`),
Kato (`kato_regMod`), and `ε ↓ 0`. -/
theorem kato_sobolev_box (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    ∃ C : ℝ≥0, ∀ (m : ℕ) (𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (u : Fin m → (ι → ℝ) → ℂ)
      (dU : Fin m → ι → (ι → ℝ) → ℂ), IsSkewHermitianConn 𝒜 →
      (∀ μ c e, AEStronglyMeasurable (𝒜 μ c e) (volume.restrict (box a b))) →
      (∀ c, MemW12 (box a b) (u c) (dU c)) →
      ∀ c, eLpNorm (u c) 4 (volume.restrict (box a b)) ≤
        C * (∑ e, eLpNorm (u e) 2 (volume.restrict (box a b)) +
          ∑ e, ∑ μ, eLpNorm (covD dU 𝒜 u e μ) 2 (volume.restrict (box a b))) := by
  obtain ⟨CS, hCS⟩ := exists_sobolev_L4_box hd hab
  refine ⟨CS, fun m 𝒜 u dU h𝒜 h𝒜m hW c => ?_⟩
  set ν := volume.restrict (box a b)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (volume_box_ne_top a b)
  set V := eLpNorm (fun _ : ι → ℝ => (1 : ℂ)) 2 ν
  have hV : V ≠ ⊤ := (memLp_const (1 : ℂ)).eLpNorm_ne_top
  set P := ∑ e, eLpNorm (u e) 2 ν
  set Q := ∑ e, ∑ μ, eLpNorm (covD dU 𝒜 u e μ) 2 ν
  have hum : ∀ e, AEStronglyMeasurable (u e) ν := fun e => (hW e).memLp.1
  have hdUm : ∀ e μ, AEStronglyMeasurable (dU e μ) ν := fun e μ => ((hW e).memLp_grad μ).1
  have hcm : ∀ e μ, AEStronglyMeasurable (covD dU 𝒜 u e μ) ν :=
    aestronglyMeasurable_covD hdUm h𝒜m hum
  refine le_of_forall_pos_le_add_mul' (K := CS * V) (ENNReal.mul_ne_top ENNReal.coe_ne_top hV)
    fun ε hε => ?_
  have hε0 : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  have hf := memW12_regMod (isOpen_box a b) (volume_box_ne_top a b) hW hε0
  have hS := hCS _ _ hf
  -- `|u_c| ≤ (|u|² + ε²)^{1/2}`
  have h1 : eLpNorm (u c) 4 ν ≤
      eLpNorm (fun x => ((√(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ)) 4 ν := by
    refine eLpNorm_mono fun x => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (norm_le_fibreNorm (fun e => u e x) c).trans
      (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _)))
  -- `‖(|u|² + ε²)^{1/2}‖_2 ≤ Σ ‖u_e‖_2 + ε ‖1‖_2`
  have h2 : eLpNorm (fun x => ((√(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ)) 2 ν ≤
      P + V * ε := by
    have hpt : ∀ x, ‖((√(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ)‖ ≤
        ∑ k : Option (Fin m), ‖(Option.elim k (fun _ => ((ε : ℝ) : ℂ)) u) x‖ := by
      intro x
      rw [Fintype.sum_option, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hn : ‖((ε : ℝ) : ℂ)‖ = ε := by simp
      simp only [Option.elim_none, Option.elim_some, hn]
      rw [Real.sqrt_le_left (by positivity)]
      have h3 := fibreNorm_le_sum (fun e => u e x)
      have h4 : ∑ e, ‖u e x‖ ^ 2 = fibreNorm (fun e => u e x) ^ 2 := by
        unfold fibreNorm
        rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have h5 := fibreNorm_nonneg (fun e => u e x)
      rw [h4]
      nlinarith [ε.2]
    have hGm : ∀ k : Option (Fin m),
        AEStronglyMeasurable (Option.elim k (fun _ => ((ε : ℝ) : ℂ)) u) ν := by
      rintro (_ | e)
      · exact aestronglyMeasurable_const
      · exact hum e
    refine (eLpNorm_le_sum_of_le hGm hpt (by norm_num)).trans ?_
    rw [Fintype.sum_option, add_comm]
    simp only [Option.elim_none, Option.elim_some]
    refine add_le_add le_rfl (le_of_eq ?_)
    have e1 : (fun _ : ι → ℝ => ((ε : ℝ) : ℂ)) = ((ε : ℝ) : ℂ) • fun _ : ι → ℝ => (1 : ℂ) := by
      funext x; simp
    rw [e1, eLpNorm_const_smul, mul_comm]
    congr 1
    rw [← ofReal_norm, show ‖((ε : ℝ) : ℂ)‖ = (ε : ℝ) by simp, ENNReal.ofReal_coe_nnreal]
  -- `‖∂_μ (|u|² + ε²)^{1/2}‖_2 ≤ Σ_e ‖∇^𝒜_μ u_e‖_2`
  have h3 : ∀ μ, eLpNorm (fun x => (((∑ e, conj (u e x) * dU e μ x).re /
      √(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ)) 2 ν ≤
      ∑ e, eLpNorm (covD dU 𝒜 u e μ) 2 ν := by
    intro μ
    refine eLpNorm_le_sum_of_le (fun e => hcm e μ) (fun x => ?_) (by norm_num)
    rw [Complex.norm_real]
    exact (kato_regMod h𝒜 u hε0 μ x).trans (fibreNorm_le_sum _)
  calc eLpNorm (u c) 4 ν
      ≤ CS * w12Norm (box a b) (fun x => ((√(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ))
          (fun μ x => (((∑ e, conj (u e x) * dU e μ x).re /
            √(∑ e, ‖u e x‖ ^ 2 + (ε : ℝ) ^ 2) : ℝ) : ℂ)) := h1.trans hS
    _ ≤ CS * ((P + V * ε) + ∑ μ, ∑ e, eLpNorm (covD dU 𝒜 u e μ) 2 ν) := by
        unfold w12Norm
        gcongr with μ
        all_goals first | exact h2 | exact h3 μ
    _ = CS * (P + Q) + CS * V * ε := by
        rw [Finset.sum_comm]; ring

/-! ### The vector graph estimate -/

theorem IsSkewHermitianConn.add {m : ℕ} {Γ A : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    (hΓ : IsSkewHermitianConn Γ) (hA : IsSkewHermitianConn A) :
    IsSkewHermitianConn (fun μ c e x => Γ μ c e x + A μ c e x) := by
  intro μ c e x
  simp only [hΓ μ c e x, hA μ c e x, star_add, neg_add]

/-- A bounded multiplier: `‖Γ w‖_2 ≤ G ‖w‖_2` when `|Γ| ≤ G`. -/
theorem eLpNorm_mul_le_of_bound {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {Γ w : X → ℂ} {G : ℝ≥0} (hΓ : ∀ x, ‖Γ x‖ ≤ G) :
    eLpNorm (fun x => Γ x * w x) 2 ν ≤ G * eLpNorm w 2 ν := by
  refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2).trans
    le_rfl
  rw [nnnorm_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hΓ x) zero_le

/-- **Vector graph estimate on a box** (`eq:critical-vector-graph`).  On a coordinate box
`Q ⊂ ℝ⁴`, for a fibre of rank `m` and a bound `G` on a reference connection, there is `C` such
that for every `M_A`, every bounded skew-Hermitian reference connection `Γ` (`|Γ_{μce}| ≤ G`),
every skew-Hermitian `L⁴` connection `A` with `‖A_{μce}‖_{L⁴(Q)} ≤ M_A` and every section `u`
with components in `W^{1,2}(Q)`,
`‖u_c‖_{W^{1,2}(Q)} ≤ C (1 + M_A) (Σ_e ‖u_e‖_{L²(Q)} + Σ_{e,μ} ‖∇^{Γ+A}_μ u_e‖_{L²(Q)})`.
No smallness of `M_A` is needed.  Proof: `∂u = ∇^{Γ+A} u - Γ u - A u`, Hölder
`‖A u‖_2 ≤ ‖A‖_4 ‖u‖_4` and the Kato–Sobolev bound for `‖u‖_4` (`kato_sobolev_box`). -/
theorem covariant_graph_box (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    (m : ℕ) (G : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (MA : ℝ≥0) (Γ A : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
      (u : Fin m → (ι → ℝ) → ℂ) (dU : Fin m → ι → (ι → ℝ) → ℂ),
      IsSkewHermitianConn Γ → IsSkewHermitianConn A →
      (∀ μ c e, AEStronglyMeasurable (Γ μ c e) (volume.restrict (box a b))) →
      (∀ μ c e x, ‖Γ μ c e x‖ ≤ G) →
      (∀ μ c e, AEStronglyMeasurable (A μ c e) (volume.restrict (box a b))) →
      (∀ μ c e, eLpNorm (A μ c e) 4 (volume.restrict (box a b)) ≤ MA) →
      (∀ c, MemW12 (box a b) (u c) (dU c)) →
      ∀ c, w12Norm (box a b) (u c) (dU c) ≤ C * (1 + MA) *
        (∑ e, eLpNorm (u e) 2 (volume.restrict (box a b)) +
          ∑ e, ∑ μ, eLpNorm (covD dU (fun μ c e x => Γ μ c e x + A μ c e x) u e μ) 2
            (volume.restrict (box a b))) := by
  obtain ⟨CK, hCK⟩ := kato_sobolev_box hd hab
  set d : ℝ≥0 := (Fintype.card ι : ℝ≥0)
  refine ⟨1 + d + d * m * G + d * m * CK,
    fun MA Γ A u dU hΓ hA hΓm hΓG hAm hAM hW c => ?_⟩
  set ν := volume.restrict (box a b)
  set 𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ := fun μ c e x => Γ μ c e x + A μ c e x
  have h𝒜 : IsSkewHermitianConn 𝒜 := hΓ.add hA
  have h𝒜m : ∀ μ c e, AEStronglyMeasurable (𝒜 μ c e) ν := fun μ c e =>
    (hΓm μ c e).add (hAm μ c e)
  set R := ∑ e, eLpNorm (u e) 2 ν + ∑ e, ∑ μ, eLpNorm (covD dU 𝒜 u e μ) 2 ν
  have hK : ∀ e, eLpNorm (u e) 4 ν ≤ CK * R := hCK m 𝒜 u dU h𝒜 h𝒜m hW
  have hu2 : ∀ e, eLpNorm (u e) 2 ν ≤ R := fun e =>
    (Finset.single_le_sum (f := fun e => eLpNorm (u e) 2 ν) (fun _ _ => zero_le)
      (Finset.mem_univ e)).trans le_self_add
  have hcov : ∀ e μ, eLpNorm (covD dU 𝒜 u e μ) 2 ν ≤ R := fun e μ =>
    ((Finset.single_le_sum (f := fun μ => eLpNorm (covD dU 𝒜 u e μ) 2 ν) (fun _ _ => zero_le)
      (Finset.mem_univ μ)).trans (Finset.single_le_sum
        (f := fun e => ∑ μ, eLpNorm (covD dU 𝒜 u e μ) 2 ν) (fun _ _ => zero_le)
        (Finset.mem_univ e))).trans le_add_self
  have hum : ∀ e, AEStronglyMeasurable (u e) ν := fun e => (hW e).memLp.1
  have hmul : ∀ μ c e, eLpNorm (fun x => 𝒜 μ c e x * u e x) 2 ν ≤
      G * R + MA * (CK * R) := by
    intro μ c e
    have hs : (fun x => 𝒜 μ c e x * u e x) =
        (fun x => Γ μ c e x * u e x) + fun x => A μ c e x * u e x := by
      funext x; simp [𝒜, add_mul]
    rw [hs]
    refine (eLpNorm_add_le ((hΓm μ c e).mul (hum e)) ((hAm μ c e).mul (hum e))
      (by norm_num)).trans (add_le_add ?_ ?_)
    · exact (eLpNorm_mul_le_of_bound (hΓG μ c e)).trans (by gcongr; exact hu2 e)
    · exact (eLpNorm_mul_le_L4 (hAm μ c e) (hum e)).trans (by gcongr; exacts [hAM μ c e, hK e])
  have hgrad : ∀ μ, eLpNorm (dU c μ) 2 ν ≤ R + m * (G * R + MA * (CK * R)) := by
    intro μ
    refine (eLpNorm_grad_le_covD (fun c μ => ((hW c).memLp_grad μ).1) h𝒜m hum c μ).trans ?_
    refine add_le_add (hcov c μ) ?_
    refine (Finset.sum_le_sum fun e _ => hmul μ c e).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hX : ((1 + d + d * m * G : ℝ≥0) : ℝ≥0∞) ≤
      ((1 + d + d * m * G + d * m * CK : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_self_add
  have hY : ((d * m * CK : ℝ≥0) : ℝ≥0∞) ≤
      ((1 + d + d * m * G + d * m * CK : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_add_self
  calc w12Norm (box a b) (u c) (dU c)
      = eLpNorm (u c) 2 ν + ∑ μ, eLpNorm (dU c μ) 2 ν := rfl
    _ ≤ R + ∑ _μ : ι, (R + m * (G * R + MA * (CK * R))) :=
        add_le_add (hu2 c) (Finset.sum_le_sum fun μ _ => hgrad μ)
    _ = ((1 + d + d * m * G : ℝ≥0) : ℝ≥0∞) * R + ((d * m * CK : ℝ≥0) : ℝ≥0∞) * MA * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, d]
        push_cast
        ring
    _ ≤ ((1 + d + d * m * G + d * m * CK : ℝ≥0) : ℝ≥0∞) * R +
          ((1 + d + d * m * G + d * m * CK : ℝ≥0) : ℝ≥0∞) * MA * R :=
        add_le_add (mul_le_mul_left hX R) (mul_le_mul_left (mul_le_mul_left hY _) R)
    _ = ((1 + d + d * m * G + d * m * CK : ℝ≥0) : ℝ≥0∞) * (1 + MA) * R := by ring

/-! ### The dual representation -/

/-- The **dual connection** `𝒜^∨_μ = -𝒜_μᵀ`; on dual sections `v` it gives
`(∇^∨_μ v)_c = ∂_μ v_c - Σ_e v_e 𝒜_{μec}` (`covD` with `dualConn 𝒜`). -/
def dualConn {m : ℕ} (𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ) :
    ι → Fin m → Fin m → (ι → ℝ) → ℂ :=
  fun μ c e x => -𝒜 μ e c x

/-- The dual of a unitary connection is unitary. -/
theorem isSkewHermitianConn_dualConn {m : ℕ} {𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ}
    (h : IsSkewHermitianConn 𝒜) : IsSkewHermitianConn (dualConn 𝒜) := by
  intro μ c e x
  simp only [dualConn]
  rw [h μ e c x]
  simp

theorem eLpNorm_dualConn {m : ℕ} (𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
    (μ : ι) (c e : Fin m) {p : ℝ≥0∞} {ν : Measure (ι → ℝ)} :
    eLpNorm (dualConn 𝒜 μ c e) p ν = eLpNorm (𝒜 μ e c) p ν := by
  have : dualConn 𝒜 μ c e = -𝒜 μ e c := rfl
  rw [this, eLpNorm_neg]

/-- **Kato–Sobolev for the dual representation.** -/
theorem kato_sobolev_box_dual (hd : Fintype.card ι = 4) {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    ∃ C : ℝ≥0, ∀ (m : ℕ) (𝒜 : ι → Fin m → Fin m → (ι → ℝ) → ℂ) (v : Fin m → (ι → ℝ) → ℂ)
      (dV : Fin m → ι → (ι → ℝ) → ℂ), IsSkewHermitianConn 𝒜 →
      (∀ μ c e, AEStronglyMeasurable (𝒜 μ c e) (volume.restrict (box a b))) →
      (∀ c, MemW12 (box a b) (v c) (dV c)) →
      ∀ c, eLpNorm (v c) 4 (volume.restrict (box a b)) ≤
        C * (∑ e, eLpNorm (v e) 2 (volume.restrict (box a b)) +
          ∑ e, ∑ μ, eLpNorm (covD dV (dualConn 𝒜) v e μ) 2 (volume.restrict (box a b))) := by
  obtain ⟨C, hC⟩ := kato_sobolev_box hd hab
  exact ⟨C, fun m 𝒜 v dV h h𝒜m hW => hC m (dualConn 𝒜) v dV (isSkewHermitianConn_dualConn h)
    (fun μ c e => (h𝒜m μ e c).neg) hW⟩

/-- **Vector graph estimate for the dual representation.** -/
theorem covariant_graph_box_dual (hd : Fintype.card ι = 4) {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (m : ℕ) (G : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (MA : ℝ≥0) (Γ A : ι → Fin m → Fin m → (ι → ℝ) → ℂ)
      (v : Fin m → (ι → ℝ) → ℂ) (dV : Fin m → ι → (ι → ℝ) → ℂ),
      IsSkewHermitianConn Γ → IsSkewHermitianConn A →
      (∀ μ c e, AEStronglyMeasurable (Γ μ c e) (volume.restrict (box a b))) →
      (∀ μ c e x, ‖Γ μ c e x‖ ≤ G) →
      (∀ μ c e, AEStronglyMeasurable (A μ c e) (volume.restrict (box a b))) →
      (∀ μ c e, eLpNorm (A μ c e) 4 (volume.restrict (box a b)) ≤ MA) →
      (∀ c, MemW12 (box a b) (v c) (dV c)) →
      ∀ c, w12Norm (box a b) (v c) (dV c) ≤ C * (1 + MA) *
        (∑ e, eLpNorm (v e) 2 (volume.restrict (box a b)) +
          ∑ e, ∑ μ, eLpNorm (covD dV (fun μ c e x => dualConn Γ μ c e x + dualConn A μ c e x)
            v e μ) 2 (volume.restrict (box a b))) := by
  obtain ⟨C, hC⟩ := covariant_graph_box hd hab m G
  refine ⟨C, fun MA Γ A v dV hΓ hA hΓm hΓG hAm hAM hW => ?_⟩
  exact hC MA (dualConn Γ) (dualConn A) v dV (isSkewHermitianConn_dualConn hΓ)
    (isSkewHermitianConn_dualConn hA) (fun μ c e => (hΓm μ e c).neg)
    (fun μ c e x => by simpa [dualConn] using hΓG μ e c x) (fun μ c e => (hAm μ e c).neg)
    (fun μ c e => by rw [eLpNorm_dualConn A]; exact hAM μ e c) hW

/-- Non-vacuity of `covariant_graph_box`: the zero connection and the constant section `1` on
the unit box of `ℝ⁴`. -/
example : ∃ C : ℝ≥0, w12Norm (box (0 : Fin 4 → ℝ) 1) (fun _ => (1 : ℂ)) (fun _ _ => 0) ≤
    C * (1 + 0) * eLpNorm (fun _ : Fin 4 → ℝ => (1 : ℂ)) 2 (volume.restrict (box 0 1)) := by
  obtain ⟨C, hC⟩ := covariant_graph_box (ι := Fin 4) (by simp) (a := 0) (b := 1)
    (fun _ => zero_lt_one) 1 0
  refine ⟨C, ?_⟩
  have h := hC 0 (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ => (1 : ℂ)) (fun _ _ _ => 0)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ => aestronglyMeasurable_const)
    (fun _ _ _ _ => by simp) (fun _ _ _ => aestronglyMeasurable_const) (fun _ _ _ => by simp)
    (fun _ => memW12_const_box 0 1 1) 0
  simpa [covD_def] using h

end RenewalGeometry.SobolevOpen
