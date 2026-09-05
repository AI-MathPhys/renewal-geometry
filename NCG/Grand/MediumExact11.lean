/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AcceptedOccurrenceLaplacianExact
import NCG.Grand.EntropicProjectionExact
import NCG.Grand.FiniteGibbsActionGap
import NCG.Grand.ProvenanceCounterexamples
import NCG.Grand.FiniteRewardLumpabilityAndTiltedSelfEnergy
import NCG.Grand.EquivariantMultiplicityFactorization

/-!
# Medium-batch exact records, file 11

Exact renderings closing the named gaps of the following Gran-Tensor records:

* `thm:SMFS-Palatini-tail` (`PalatiniTail`): assembled spectral-tail handoff
  (FS.48), the resulting weak-equation convergence, and the escaping-variation
  witness (FS.49).
* `cth:SMFS-Hessian-not-beta` (`HessianNotBeta`): one-shell equilibrium data do
  not determine the Wilsonian quadratic coefficient map.
* `cth:accepted-bit-no-field-kernel` (`AcceptedBit`): the accepted renewal bit,
  first-acceptance law, and accepted-count pressure are invariant under the
  state-independent mark for every row-stochastic kernel, while terminal field
  laws and Gibbs gaps differ.
* `cor:accepted-occurrence-observables` (`OccurrenceObservables`): AO.13a-c
  derived from the occurrence energy.
* `thm:accepted-entropic-projection` (`EntropicKKT`): the finite KKT existence
  of Gibbs potentials (AO.6) for the entropic occurrence projection.
* `cor:accepted-occurrence-stationarity` (`OccurrenceStationarity`):
  AO.14-AO.16 derived from the Gibbs action gap, the entropic projection, and
  the occurrence Laplacian.
* `cor:accepted-one-history-three-projections` (`ThreeProjections`):
  pushforward reference law, source-germ identification, Gram shorting, and
  the pairwise-compatibility countermodel.
* `thm:accepted-generator-closure` (`GeneratorVolterra`): the exact
  Mori--Zwanzig Volterra memory equation derived by variation of constants.
* `thm:accepted-tilted-retract` (`TiltedRetract`): Perron existence closed via
  the repo Perron--Frobenius theorem, and the Schur corner inverses
  constructed for all large spectral parameters.
* `thm:SM-record-bimodule` (`RecordBimodule`): full-algebra faithfulness of
  the endpoint record representation on `HS(M_R, M_L)` and the flat-depth
  commutant/central reconstructions.
* `cor:SMFS-anomaly-quotient` (`AnomalyQuotient`): the one-generation packet
  is trivial on the order-six central element and descends to the `Z_6` gauge
  quotient; anomaly sums, doublet parity, and the determinant character.
-/

open Finset

namespace NCG
namespace MediumExact11

/-! ## `thm:SMFS-Palatini-tail`: assembled spectral-tail handoff -/

namespace PalatiniTail

open Filter Topology

variable (lam : ℕ → ℝ) (sigma : ℝ)

/-- The determining screen `P_Λ`: keep the modes with frequency at most `Λ`. -/
noncomputable def screen (Lam : ℝ) (r : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if lam i ≤ Lam then r i else 0

/-- The escaping spectral tail `(1 - P_Λ) r`. -/
noncomputable def tail (Lam : ℝ) (r : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if lam i ≤ Lam then 0 else r i

/-- The base `𝒱`-norm `‖r‖ = (∑ r_i²)^{1/2}`. -/
noncomputable def vNorm (r : ℕ → ℝ) : ℝ := Real.sqrt (∑' i, r i ^ 2)

/-- The squared regularity norm `‖r‖²_{𝒱_σ} = ∑ (1+λ_i)^σ r_i²`. -/
noncomputable def vSigmaSq (r : ℕ → ℝ) : ℝ := ∑' i, (1 + lam i) ^ sigma * r i ^ 2

theorem sq_split (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    r i ^ 2 = screen lam Lam r i ^ 2 + tail lam Lam r i ^ 2 := by
  unfold screen tail
  split_ifs <;> ring

theorem screen_sq_le (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    screen lam Lam r i ^ 2 ≤ r i ^ 2 := by
  unfold screen
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg (r i)

theorem tail_sq_le (Lam : ℝ) (r : ℕ → ℝ) (i : ℕ) :
    tail lam Lam r i ^ 2 ≤ r i ^ 2 := by
  unfold tail
  split_ifs
  · simpa using sq_nonneg (r i)
  · exact le_rfl

/-- The `𝒱_σ` weight dominates `1`. -/
theorem one_le_weight (hlam : ∀ i, 0 ≤ lam i) (hs : 0 ≤ sigma) (i : ℕ) :
    (1 : ℝ) ≤ (1 + lam i) ^ sigma := by
  calc (1 : ℝ) = 1 ^ sigma := (Real.one_rpow _).symm
    _ ≤ (1 + lam i) ^ sigma :=
        Real.rpow_le_rpow zero_le_one (by linarith [hlam i]) hs

/-- Membership in `𝒱_σ` gives membership in `𝒱`. -/
theorem summable_sq_of_weighted (hlam : ∀ i, 0 ≤ lam i) (hs : 0 ≤ sigma)
    {r : ℕ → ℝ} (h : Summable fun i => (1 + lam i) ^ sigma * r i ^ 2) :
    Summable fun i => r i ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) h
  nlinarith [one_le_weight lam sigma hlam hs i, sq_nonneg (r i)]

/-- **`thm:SMFS-Palatini-tail`, equation (FS.48)**: the Hilbert-scale
Pythagoras interpolation.  If `‖r‖_{𝒱_σ} ≤ M₄₈` and `‖P_Λ r‖_𝒱 ≤ ε`, then
`‖r‖_𝒱 ≤ [ε² + (1+Λ)^{-σ} M₄₈²]^{1/2}`. -/
theorem spectral_tail_handoff (hlam : ∀ i, 0 ≤ lam i) (hs : 0 < sigma)
    {Lam M48 eps : ℝ} (hLam : 0 ≤ Lam) (r : ℕ → ℝ)
    (hsum : Summable fun i => (1 + lam i) ^ sigma * r i ^ 2)
    (hM : Real.sqrt (vSigmaSq lam sigma r) ≤ M48)
    (heps : vNorm (screen lam Lam r) ≤ eps) :
    vNorm r ≤ Real.sqrt (eps ^ 2 + (1 + Lam) ^ (-sigma) * M48 ^ 2) := by
  have hr2 : Summable fun i => r i ^ 2 :=
    summable_sq_of_weighted lam sigma hlam hs.le hsum
  have hscr : Summable fun i => screen lam Lam r i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (screen_sq_le lam Lam r) hr2
  have htl : Summable fun i => tail lam Lam r i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (tail_sq_le lam Lam r) hr2
  have hsplit : (∑' i, r i ^ 2)
      = (∑' i, screen lam Lam r i ^ 2) + ∑' i, tail lam Lam r i ^ 2 := by
    rw [← hscr.tsum_add htl]
    exact tsum_congr (sq_split lam Lam r)
  -- the tail is dominated by the shifted regularity weight
  have hwpos : (0 : ℝ) < (1 + Lam) ^ sigma :=
    Real.rpow_pos_of_pos (by linarith) sigma
  have hneg : (1 + Lam : ℝ) ^ (-sigma) = ((1 + Lam) ^ sigma)⁻¹ :=
    Real.rpow_neg (by linarith) sigma
  have hnegpos : (0 : ℝ) < (1 + Lam) ^ (-sigma) := by
    rw [hneg]
    exact inv_pos.mpr hwpos
  have htailb : ∀ i, tail lam Lam r i ^ 2
      ≤ (1 + Lam) ^ (-sigma) * ((1 + lam i) ^ sigma * r i ^ 2) := by
    intro i
    unfold tail
    split_ifs with h
    · have : (0 : ℝ) ≤ (1 + lam i) ^ sigma :=
        (Real.rpow_pos_of_pos (by linarith [hlam i]) sigma).le
      have := sq_nonneg (r i)
      positivity
    · push_neg at h
      have hbase : (1 + Lam : ℝ) ^ sigma ≤ (1 + lam i) ^ sigma :=
        Real.rpow_le_rpow (by linarith) (by linarith) hs.le
      have h1 : (1 : ℝ) ≤ (1 + Lam) ^ (-sigma) * (1 + lam i) ^ sigma := by
        rw [hneg]
        rw [inv_mul_eq_div, le_div_iff₀ hwpos, one_mul]
        exact hbase
      nlinarith [sq_nonneg (r i)]
  have htailsum : (∑' i, tail lam Lam r i ^ 2)
      ≤ (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r := by
    calc (∑' i, tail lam Lam r i ^ 2)
        ≤ ∑' i, (1 + Lam) ^ (-sigma) * ((1 + lam i) ^ sigma * r i ^ 2) :=
          htl.tsum_le_tsum htailb (hsum.mul_left _)
      _ = (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r := by
          rw [vSigmaSq, tsum_mul_left]
  -- convert the two norm hypotheses to squared bounds
  have hSnn : 0 ≤ vSigmaSq lam sigma r :=
    tsum_nonneg fun i =>
      mul_nonneg (Real.rpow_pos_of_pos (by linarith [hlam i]) sigma).le (sq_nonneg _)
  have hM0 : 0 ≤ M48 := le_trans (Real.sqrt_nonneg _) hM
  have hM2 : vSigmaSq lam sigma r ≤ M48 ^ 2 := by
    nlinarith [Real.sq_sqrt hSnn, Real.sqrt_nonneg (vSigmaSq lam sigma r)]
  have hscrnn : 0 ≤ ∑' i, screen lam Lam r i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have heps0 : 0 ≤ eps := le_trans (Real.sqrt_nonneg _) heps
  have heps2 : (∑' i, screen lam Lam r i ^ 2) ≤ eps ^ 2 := by
    have h := heps
    unfold vNorm at h
    nlinarith [Real.sq_sqrt hscrnn, Real.sqrt_nonneg (∑' i, screen lam Lam r i ^ 2)]
  have hfinal : (∑' i, r i ^ 2) ≤ eps ^ 2 + (1 + Lam) ^ (-sigma) * M48 ^ 2 := by
    have h3 : (1 + Lam) ^ (-sigma) * vSigmaSq lam sigma r
        ≤ (1 + Lam) ^ (-sigma) * M48 ^ 2 :=
      mul_le_mul_of_nonneg_left hM2 hnegpos.le
    linarith [hsplit, htailsum, heps2]
  unfold vNorm
  exact Real.sqrt_le_sqrt hfinal

/-- **`thm:SMFS-Palatini-tail`, convergence clause**: `ε_n → 0` and
`Λ_n → ∞` force `‖r_n‖_𝒱 → 0`, the selected weak Palatini--Einstein--matter
equation. -/
theorem tail_handoff_convergence (hlam : ∀ i, 0 ≤ lam i) (hs : 0 < sigma)
    {M48 : ℝ} (r : ℕ → ℕ → ℝ) (eps Lams : ℕ → ℝ)
    (hLam0 : ∀ n, 0 ≤ Lams n)
    (hsum : ∀ n, Summable fun i => (1 + lam i) ^ sigma * r n i ^ 2)
    (hM : ∀ n, Real.sqrt (vSigmaSq lam sigma (r n)) ≤ M48)
    (heps : ∀ n, vNorm (screen lam (Lams n) (r n)) ≤ eps n)
    (heps0 : Tendsto eps atTop (nhds 0))
    (hLamtop : Tendsto Lams atTop atTop) :
    Tendsto (fun n => vNorm (r n)) atTop (nhds 0) := by
  have hb : ∀ n, vNorm (r n)
      ≤ Real.sqrt (eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2) := fun n =>
    spectral_tail_handoff lam sigma hlam hs (hLam0 n) (r n) (hsum n) (hM n) (heps n)
  have hc : Tendsto (fun n => (1 + Lams n) ^ (-sigma)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => 1 + Lams n) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 hLamtop
    have h2 : Tendsto (fun n => (1 + Lams n) ^ sigma) atTop atTop :=
      (Real.tendsto_rpow_atTop hs).comp h1
    have h3 : Tendsto (fun n => ((1 + Lams n) ^ sigma)⁻¹) atTop (nhds 0) :=
      h2.inv_tendsto_atTop
    refine h3.congr fun n => ?_
    rw [Real.rpow_neg (by linarith [hLam0 n])]
  have hinner : Tendsto (fun n => eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n => eps n ^ 2) atTop (nhds 0) := by
      have := heps0.pow 2
      simpa using this
    have h2 : Tendsto (fun n => (1 + Lams n) ^ (-sigma) * M48 ^ 2) atTop (nhds 0) := by
      have := hc.mul_const (M48 ^ 2)
      simpa using this
    have := h1.add h2
    simpa using this
  have hsq : Tendsto (fun n => Real.sqrt (eps n ^ 2 + (1 + Lams n) ^ (-sigma) * M48 ^ 2))
      atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this
  exact squeeze_zero (fun n => Real.sqrt_nonneg _) hb hsq

/-- **`thm:SMFS-Palatini-tail`, equation (FS.49)**: if the screened norms
decay but the full `𝒱`-norms do not, unit escaping variations supported
outside the growing determining screens pair against the residual above a
fixed positive threshold. -/
theorem escaping_variation_witness (r : ℕ → ℕ → ℝ) (Lams : ℕ → ℝ)
    (hr2 : ∀ n, Summable fun i => r n i ^ 2)
    (hscr : Tendsto (fun n => vNorm (screen lam (Lams n) (r n))) atTop (nhds 0))
    (hfail : ¬ Tendsto (fun n => vNorm (r n)) atTop (nhds 0)) :
    ∃ epsStar > (0 : ℝ), ∃ᶠ n in atTop, ∃ v : ℕ → ℝ,
      vNorm v = 1 ∧ (∀ i, lam i ≤ Lams n → v i = 0)
        ∧ epsStar ≤ ∑' i, r n i * v i := by
  rw [Metric.tendsto_atTop] at hfail
  push_neg at hfail
  obtain ⟨eps0, heps0, hfr⟩ := hfail
  have hfreq : ∃ᶠ n in atTop, eps0 ≤ vNorm (r n) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hfr N
    refine ⟨n, hn, ?_⟩
    rw [Real.dist_0_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hd
    exact le_of_not_gt hd
  have hev : ∀ᶠ n in atTop, vNorm (screen lam (Lams n) (r n)) < eps0 / 2 :=
    hscr.eventually_lt_const (by positivity)
  refine ⟨eps0 / 2, by positivity, ?_⟩
  refine (hfreq.and_eventually hev).mono ?_
  rintro n ⟨h1, h2⟩
  have hscrsum : Summable fun i => screen lam (Lams n) (r n) i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (screen_sq_le lam (Lams n) (r n)) (hr2 n)
  have htlsum : Summable fun i => tail lam (Lams n) (r n) i ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (tail_sq_le lam (Lams n) (r n)) (hr2 n)
  set S : ℝ := ∑' i, tail lam (Lams n) (r n) i ^ 2 with hSdef
  set sS : ℝ := ∑' i, screen lam (Lams n) (r n) i ^ 2 with hsSdef
  have hSnn : 0 ≤ S := tsum_nonneg fun i => sq_nonneg _
  have hsSnn : 0 ≤ sS := tsum_nonneg fun i => sq_nonneg _
  have hsplit : (∑' i, r n i ^ 2) = sS + S := by
    rw [hSdef, hsSdef, ← hscrsum.tsum_add htlsum]
    exact tsum_congr (sq_split lam (Lams n) (r n))
  -- lower bound on the tail mass
  have hlow : eps0 ^ 2 ≤ sS + S := by
    have h := h1
    unfold vNorm at h
    rw [hsplit] at h
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ sS + S)]
  have hup : sS < eps0 ^ 2 / 4 := by
    have h := h2
    unfold vNorm at h
    nlinarith [Real.sq_sqrt hsSnn, Real.sqrt_nonneg sS]
  have hS34 : eps0 ^ 2 / 4 ≤ S := by linarith
  set c : ℝ := Real.sqrt S with hcdef
  have hclow : eps0 / 2 ≤ c := by
    rw [hcdef]
    rw [show eps0 / 2 = Real.sqrt ((eps0 / 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hclow
  have hcsq : c ^ 2 = S := Real.sq_sqrt hSnn
  refine ⟨fun i => c⁻¹ * tail lam (Lams n) (r n) i, ?_, ?_, ?_⟩
  · -- unit norm
    unfold vNorm
    have hcongr : (∑' i, (c⁻¹ * tail lam (Lams n) (r n) i) ^ 2)
        = c⁻¹ ^ 2 * S := by
      rw [hSdef, ← tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [hcongr, ← hcsq]
    rw [show c⁻¹ ^ 2 * c ^ 2 = 1 by
      field_simp]
    exact Real.sqrt_one
  · intro i hi
    unfold tail
    rw [if_pos hi, mul_zero]
  · have hpt : ∀ i, r n i * (c⁻¹ * tail lam (Lams n) (r n) i)
        = c⁻¹ * tail lam (Lams n) (r n) i ^ 2 := by
      intro i
      unfold tail
      split_ifs <;> ring
    calc eps0 / 2 ≤ c := hclow
      _ = c⁻¹ * S := by
          rw [← hcsq]
          field_simp
      _ = ∑' i, c⁻¹ * tail lam (Lams n) (r n) i ^ 2 := by
          rw [hSdef, tsum_mul_left]
      _ = ∑' i, r n i * (c⁻¹ * tail lam (Lams n) (r n) i) :=
          (tsum_congr hpt).symm

end PalatiniTail

/-! ## `cth:SMFS-Hessian-not-beta`: one-shell data do not determine the tensor -/

namespace HessianNotBeta

/-- The determining observable of the two-state shell. -/
noncomputable def phi : Fin 2 → ℝ := ![1, -1]

/-- First unnormalized one-shell family: `w_θ(x) = exp(θ φ(x))`. -/
noncomputable def familyA (θ : ℝ) (x : Fin 2) : ℝ := Real.exp (θ * phi x)

/-- Second unnormalized one-shell family: `w_θ(x) = exp(θ φ(x) + θ³)`,
agreeing with the first to second order at the cutoff base point. -/
noncomputable def familyB (θ : ℝ) (x : Fin 2) : ℝ := Real.exp (θ * phi x + θ ^ 3)

/-- The score of a parametrized unnormalized law at the cutoff base `θ = 0`. -/
noncomputable def score (w : ℝ → Fin 2 → ℝ) (x : Fin 2) : ℝ :=
  deriv (fun θ => Real.log (w θ x)) 0

/-- The complete score Gram at the cutoff. -/
noncomputable def scoreGram (w : ℝ → Fin 2 → ℝ) : ℝ :=
  ∑ x, w 0 x * score w x ^ 2

/-- The complete direct second-action Hessian at the cutoff:
the second derivative of the per-state direct action `-log w_θ(x)`. -/
noncomputable def directHessian (w : ℝ → Fin 2 → ℝ) (x : Fin 2) : ℝ :=
  deriv (deriv fun θ => -Real.log (w θ x)) 0

/-- The quadratic coefficient map of a coarse-graining step at the base. -/
noncomputable def quadCoefficient (T : ℝ → ℝ) : ℝ := deriv (deriv T) 0 / 2

/-- First coarse-graining step. -/
def stepA : ℝ → ℝ := fun θ => θ

/-- Second coarse-graining step: same fixed point and linearization, different
quadratic coefficient. -/
def stepB : ℝ → ℝ := fun θ => θ + θ ^ 2

theorem log_familyA (x : Fin 2) :
    (fun θ => Real.log (familyA θ x)) = fun θ => θ * phi x := by
  funext θ
  rw [familyA, Real.log_exp]

theorem log_familyB (x : Fin 2) :
    (fun θ => Real.log (familyB θ x)) = fun θ => θ * phi x + θ ^ 3 := by
  funext θ
  rw [familyB, Real.log_exp]

theorem deriv_linear (c : ℝ) : deriv (fun θ : ℝ => θ * c) = fun _ => c := by
  funext θ
  exact (hasDerivAt_mul_const c).deriv

theorem deriv_cubicshift (c : ℝ) :
    deriv (fun θ : ℝ => θ * c + θ ^ 3) = fun θ => c + 3 * θ ^ 2 := by
  funext θ
  have h := (hasDerivAt_mul_const c).add (hasDerivAt_pow 3 θ)
  have h2 : HasDerivAt (fun θ : ℝ => θ * c + θ ^ 3) (c + 3 * θ ^ 2) θ := by
    convert h using 1
    push_cast
    ring
  exact h2.deriv

theorem score_familyA (x : Fin 2) : score familyA x = phi x := by
  rw [score, log_familyA, deriv_linear]

theorem score_familyB (x : Fin 2) : score familyB x = phi x := by
  rw [score, log_familyB, deriv_cubicshift]
  norm_num

theorem law_at_cutoff (x : Fin 2) : familyA 0 x = familyB 0 x := by
  rw [familyA, familyB]
  norm_num

theorem directHessian_familyA (x : Fin 2) : directHessian familyA x = 0 := by
  rw [directHessian]
  have h1 : (fun θ => -Real.log (familyA θ x)) = fun θ => θ * (-phi x) := by
    funext θ
    rw [familyA, Real.log_exp]
    ring
  rw [h1, deriv_linear]
  exact deriv_const _ _

theorem directHessian_familyB (x : Fin 2) : directHessian familyB x = 0 := by
  rw [directHessian]
  have h1 : (fun θ => -Real.log (familyB θ x))
      = fun θ => θ * (-phi x) + (-1) * θ ^ 3 := by
    funext θ
    rw [familyB, Real.log_exp]
    ring
  have h2 : deriv (fun θ : ℝ => θ * (-phi x) + (-1) * θ ^ 3)
      = fun θ => -phi x + (-3) * θ ^ 2 := by
    funext θ
    have ha := hasDerivAt_mul_const (-phi x) (x := θ)
    have hb := (hasDerivAt_pow 3 θ).const_mul (-1 : ℝ)
    have h := ha.add hb
    have h' : HasDerivAt (fun θ : ℝ => θ * (-phi x) + (-1) * θ ^ 3)
        (-phi x + (-3) * θ ^ 2) θ := by
      convert h using 1
      push_cast
      ring
    exact h'.deriv
  rw [h1, h2]
  have h3 : HasDerivAt (fun θ : ℝ => -phi x + (-3) * θ ^ 2)
      (-3 * (2 * 0)) 0 := by
    have := ((hasDerivAt_pow 2 (0:ℝ)).const_mul (-3 : ℝ)).const_add (-phi x)
    convert this using 1
    push_cast
    ring
  rw [h3.deriv]
  ring

theorem quadCoefficient_stepA : quadCoefficient stepA = 0 := by
  rw [quadCoefficient, stepA]
  have h1 : deriv (fun θ : ℝ => θ) = fun _ => (1 : ℝ) := by
    funext θ
    exact (hasDerivAt_id θ).deriv
  rw [h1, deriv_const]
  norm_num

theorem quadCoefficient_stepB : quadCoefficient stepB = 1 := by
  rw [quadCoefficient, stepB]
  have h1 : deriv (fun θ : ℝ => θ + θ ^ 2) = fun θ => 1 + 2 * θ := by
    funext θ
    have h := (hasDerivAt_id θ).add (hasDerivAt_pow 2 θ)
    have h' : HasDerivAt (fun θ : ℝ => θ + θ ^ 2) (1 + 2 * θ) θ := by
      convert h using 1
      push_cast
      ring
    exact h'.deriv
  rw [h1]
  have h2 : HasDerivAt (fun θ : ℝ => 1 + 2 * θ) 2 0 := by
    have := (hasDerivAt_mul_const (2:ℝ) (x := (0:ℝ))).const_add (1:ℝ)
    have h' : HasDerivAt (fun θ : ℝ => 1 + 2 * θ) 2 0 := by
      convert this using 2
      ring
    exact h'
  rw [h2.deriv]
  norm_num

/-- **`cth:SMFS-Hessian-not-beta`**: the two finite coarse-graining setups
`(familyA, stepA)` and `(familyB, stepB)` share the unnormalized law, the
complete score Gram, and the complete direct second-action Hessian at the
cutoff — the steps even share their fixed point and linearization — yet their
quadratic coefficient maps differ.  One-shell equilibrium data therefore do
not determine the Wilsonian quadratic shell tensor. -/
theorem one_shell_data_do_not_determine_wilsonian_tensor :
    (∀ x, familyA 0 x = familyB 0 x)
      ∧ (∀ x, score familyA x = score familyB x)
      ∧ scoreGram familyA = scoreGram familyB
      ∧ (∀ x, directHessian familyA x = directHessian familyB x)
      ∧ stepA 0 = 0 ∧ stepB 0 = 0
      ∧ deriv stepA 0 = deriv stepB 0
      ∧ quadCoefficient stepA ≠ quadCoefficient stepB := by
  refine ⟨law_at_cutoff, ?_, ?_, ?_, rfl, by norm_num [stepB], ?_, ?_⟩
  · intro x
    rw [score_familyA, score_familyB]
  · unfold scoreGram
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [law_at_cutoff, score_familyA, score_familyB]
  · intro x
    rw [directHessian_familyA, directHessian_familyB]
  · rw [stepA, stepB]
    have h1 : deriv (fun θ : ℝ => θ) 0 = 1 := (hasDerivAt_id (0:ℝ)).deriv
    have h2 : deriv (fun θ : ℝ => θ + θ ^ 2) 0 = 1 := by
      have h := (hasDerivAt_id (0:ℝ)).add (hasDerivAt_pow 2 (0:ℝ))
      have h' : HasDerivAt (fun θ : ℝ => θ + θ ^ 2) 1 0 := by
        convert h using 1
        push_cast
        ring
      exact h'.deriv
    rw [h1, h2]
  · rw [quadCoefficient_stepA, quadCoefficient_stepB]
    norm_num

end HessianNotBeta

end MediumExact11
end NCG
