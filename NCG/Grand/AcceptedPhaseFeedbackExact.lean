/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalProfiles
import NCG.Grand.UniversalFeedbackMemory

/-!
# Exact shorting of the accepted intrinsic phase

The two phase coordinates reduce the payload feedback to the complementary
projection `P = I - R`.  The block powers and returned kernels are therefore
literal scalar geometric series, permitting sharp norm and continuum bounds.
-/

namespace NCG

section ProjectionAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- An affine function of an idempotent acts diagonally on its range. -/
theorem affineProjection_pow_mul (P : A) (hP : P * P = P)
    (a b : ℝ) : ∀ k : ℕ,
    (a • (1 : A) + b • P) ^ k * P = (a + b) ^ k • P := by
  intro k
  have hQP : (a • (1 : A) + b • P) * P = (a + b) • P := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hP, ← add_smul]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_assoc, hQP, mul_smul_comm, ih, smul_smul]
      congr 1
      rw [mul_comm, pow_succ]

/-- Closed form for powers of identity plus an idempotent direction. -/
theorem oneAddProjection_pow (P : A) (hP : P * P = P)
    (c : ℝ) : ∀ k : ℕ,
    ((1 : A) + c • P) ^ k =
      1 + (((1 + c) ^ k - 1 : ℝ) • P) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hrange := affineProjection_pow_mul P hP 1 c k
      simp only [one_smul] at hrange
      rw [pow_succ, mul_add, mul_one, mul_smul_comm,
        hrange, ih, smul_smul,
        add_assoc, ← add_smul]
      congr 1
      rw [pow_succ]
      ring

/-- Exact accepted-phase operator blocks over a payload complement `P`. -/
noncomputable def acceptedPhaseA (P : A) (θ : ℝ) : A :=
  1 - (4 * θ / 11) • P

noncomputable def acceptedPhaseB (P : A) (θ : ℝ) : A :=
  (24 * θ / (11 * Real.sqrt 30)) • P

noncomputable def acceptedPhaseC (P : A) (θ : ℝ) : A :=
  (-20 * θ / (11 * Real.sqrt 30)) • P

noncomputable def acceptedPhaseD (P : A) (θ : ℝ) : A :=
  (-7 / 15 : ℝ) • 1 + (4 * θ / 11) • P

noncomputable def acceptedPhaseModelStep (P : A) (θ : ℝ) : A :=
  1 + (Real.exp (-4 * θ / 11) - 1) • P

/-- Exact powers of the pressure-derived model step. -/
theorem acceptedPhaseModelStep_pow (P : A) (hP : P * P = P)
    (θ : ℝ) (k : ℕ) :
    (acceptedPhaseModelStep P θ) ^ k =
      1 + (Real.exp ((-4 * θ / 11) * k) - 1) • P := by
  rw [acceptedPhaseModelStep, oneAddProjection_pow P hP]
  congr 2
  rw [show 1 + (Real.exp (-4 * θ / 11) - 1) =
      Real.exp (-4 * θ / 11) by ring, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The returned-kernel formula in the manuscript, with all operator
bookkeeping made explicit. -/
theorem acceptedPhase_returnedKernel (P : A) (hP : P * P = P)
    (θ : ℝ) (k : ℕ) :
    acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ =
      (-16 * θ ^ 2 / 121) •
        ((-7 / 15 + 4 * θ / 11 : ℝ) ^ k • P) := by
  rw [acceptedPhaseB, acceptedPhaseC, acceptedPhaseD,
    mul_smul_comm, mul_assoc, affineProjection_pow_mul P hP]
  simp only [smul_mul_assoc, mul_smul_comm, hP, smul_smul]
  congr 1
  have hsqrt : (Real.sqrt 30) ^ 2 = 30 := by norm_num
  have hsqrt0 : Real.sqrt 30 ≠ 0 := by positivity
  have hsqrtMul : Real.sqrt 30 * Real.sqrt 30 = 30 := by
    simpa [pow_two] using hsqrt
  field_simp [hsqrt0]
  rw [hsqrt]
  ring

/-- The scalar fast-phase ratio is bounded by `7/15` for an acceptance
probability `0 ≤ θ ≤ 1`. -/
theorem acceptedPhase_ratio_abs_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    |(-7 / 15 + 4 * θ / 11 : ℝ)| ≤ 7 / 15 := by
  rw [abs_le]
  constructor <;> norm_num at * <;> linarith

/-- Pointwise geometric domination of every returned kernel. -/
theorem acceptedPhase_returnedKernel_norm_le (P : A) (hP : P * P = P)
    (hPnorm : ‖P‖ ≤ 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (k : ℕ) :
    ‖acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ‖ ≤
      (16 / 121 * θ ^ 2) * (7 / 15 : ℝ) ^ k := by
  rw [acceptedPhase_returnedKernel P hP θ k, smul_smul, norm_smul,
    Real.norm_eq_abs, abs_mul, abs_pow]
  have hc : |(-16 * θ ^ 2 / 121 : ℝ)| = 16 / 121 * θ ^ 2 := by
    rw [abs_of_nonpos]
    · ring
    · nlinarith [sq_nonneg θ]
  rw [hc]
  have hr := acceptedPhase_ratio_abs_le hθ0 hθ1
  calc
    (16 / 121 * θ ^ 2 *
        |(-7 / 15 + 4 * θ / 11 : ℝ)| ^ k) * ‖P‖
        ≤ (16 / 121 * θ ^ 2 * (7 / 15 : ℝ) ^ k) * 1 := by
          gcongr
    _ = (16 / 121 * θ ^ 2) * (7 / 15 : ℝ) ^ k := by ring

/-- The returned kernels are summable with the manuscript's exact total
mass bound `30 θ² / 121`. -/
theorem acceptedPhase_returnedKernel_summable_and_bound
    (P : A) (hP : P * P = P) (hPnorm : ‖P‖ ≤ 1)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Summable (fun k : ℕ =>
      ‖acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ‖) ∧
    (∑' k : ℕ, ‖acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ‖) ≤ 30 / 121 * θ ^ 2 := by
  have hgeom : Summable fun k : ℕ =>
      (16 / 121 * θ ^ 2) * (7 / 15 : ℝ) ^ k :=
    (summable_geometric_of_norm_lt_one (x := (7 / 15 : ℝ))
      (by norm_num)).mul_left _
  have hsum : Summable fun k : ℕ =>
      ‖acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (acceptedPhase_returnedKernel_norm_le P hP hPnorm θ hθ0 hθ1) hgeom
  refine ⟨hsum, ?_⟩
  calc
    (∑' k : ℕ, ‖acceptedPhaseB P θ * (acceptedPhaseD P θ) ^ k *
        acceptedPhaseC P θ‖)
        ≤ ∑' k : ℕ, (16 / 121 * θ ^ 2) * (7 / 15 : ℝ) ^ k := by
          exact hsum.tsum_le_tsum
            (acceptedPhase_returnedKernel_norm_le P hP hPnorm θ hθ0 hθ1)
            hgeom
    _ = 30 / 121 * θ ^ 2 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one
        (ξ := (7 / 15 : ℝ)) (by norm_num)]
      norm_num
      ring

/-- Sharp negative-exponential remainder on the nonnegative half-line. -/
theorem exp_neg_sub_one_add_le_half_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) - 1 + x ≤ x ^ 2 / 2 := by
  let f : ℝ → ℝ :=
    (fun y => Real.exp (-y) - 1) + id - fun y => (2 : ℝ)⁻¹ * y ^ 2
  have hf : ContinuousOn f (Set.Ici 0) := by
    fun_prop
  have hfd : DifferentiableOn ℝ f (interior (Set.Ici (0 : ℝ))) := by
    fun_prop
  have hder : ∀ y ∈ interior (Set.Ici (0 : ℝ)), deriv f y ≤ 0 := by
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt (by simpa using hy)
    have hd : HasDerivAt f (-Real.exp (-y) + 1 - y) y := by
      have hd0 := (((Real.hasDerivAt_exp (-y)).comp y
        (hasDerivAt_neg y)).sub_const 1 |>.add (hasDerivAt_id y) |>.sub
          (((hasDerivAt_pow 2 y).const_mul (2 : ℝ)⁻¹)))
      simpa [f, Function.comp_apply] using hd0
    rw [hd.deriv]
    nlinarith [Real.one_sub_le_exp_neg y]
  have hant : AntitoneOn f (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hf hfd hder
  have := hant (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx) hx
  have h : Real.exp (-x) - 1 + x ≤ (2 : ℝ)⁻¹ * x ^ 2 := by
    simpa [f, Pi.add_apply, Pi.sub_apply, div_eq_mul_inv] using this
  nlinarith

/-- The direct head block and the pressure-derived model step differ by at
most the manuscript's sharp quadratic constant. -/
theorem acceptedPhase_model_error (P : A) (hPnorm : ‖P‖ ≤ 1)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖acceptedPhaseA P θ - acceptedPhaseModelStep P θ‖ ≤
      8 / 121 * θ ^ 2 := by
  let x : ℝ := 4 * θ / 11
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by dsimp [x]; linarith
  have hlo : 0 ≤ Real.exp (-x) - (1 - x) := by
    linarith [Real.one_sub_le_exp_neg x]
  have hhi : Real.exp (-x) - (1 - x) ≤ x ^ 2 / 2 := by
    nlinarith [exp_neg_sub_one_add_le_half_sq hx0]
  have heq : acceptedPhaseA P θ - acceptedPhaseModelStep P θ =
      (-(Real.exp (-x) - (1 - x))) • P := by
    have harg : -4 * θ / 11 = -(4 * θ / 11) := by ring
    simp only [acceptedPhaseA, acceptedPhaseModelStep, x, harg]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hlo]
  calc
    (Real.exp (-x) - (1 - x)) * ‖P‖
        ≤ (x ^ 2 / 2) * 1 :=
      mul_le_mul hhi hPnorm (norm_nonneg _) (by positivity)
    _ = 8 / 121 * θ ^ 2 := by
      dsimp [x]
      ring

/-- Both feedback corrections vanish after division by the physical step
whenever `θ/h` has a finite limit and `h → 0`. -/
theorem acceptedPhase_normalized_feedback_vanishes
    (P : A) (hP : P * P = P) (hPnorm : ‖P‖ ≤ 1)
    (h θ : ℕ → ℝ) (a : ℝ)
    (hhpos : ∀ n, 0 < h n) (hθ0 : ∀ n, 0 ≤ θ n)
    (hθ1 : ∀ n, θ n ≤ 1)
    (hh : Filter.Tendsto h Filter.atTop (nhds 0))
    (hratio : Filter.Tendsto (fun n => θ n / h n) Filter.atTop
      (nhds a)) :
    Filter.Tendsto
        (fun n => ‖acceptedPhaseA P (θ n) -
          acceptedPhaseModelStep P (θ n)‖ / h n)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => (∑' k : ℕ,
          ‖acceptedPhaseB P (θ n) * (acceptedPhaseD P (θ n)) ^ k *
            acceptedPhaseC P (θ n)‖) / h n)
        Filter.atTop (nhds 0) := by
  have hquad : Filter.Tendsto
      (fun n => (θ n / h n) ^ 2 * h n) Filter.atTop (nhds 0) := by
    convert (hratio.pow 2).mul hh using 1 <;> ring
  constructor
  · have hup : Filter.Tendsto
        (fun n => 8 / 121 * ((θ n / h n) ^ 2 * h n))
        Filter.atTop (nhds 0) := by
      simpa using (hquad.const_mul (8 / 121 : ℝ))
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (le_of_lt (hhpos n))) _ hup
    exact Filter.Eventually.of_forall fun n => by
      have hb := acceptedPhase_model_error P hPnorm (θ n) (hθ0 n) (hθ1 n)
      calc
        ‖acceptedPhaseA P (θ n) - acceptedPhaseModelStep P (θ n)‖ / h n
            ≤ (8 / 121 * (θ n) ^ 2) / h n :=
          div_le_div_of_nonneg_right hb (le_of_lt (hhpos n))
        _ = 8 / 121 * ((θ n / h n) ^ 2 * h n) := by
          field_simp [(hhpos n).ne']
  · have hup : Filter.Tendsto
        (fun n => 30 / 121 * ((θ n / h n) ^ 2 * h n))
        Filter.atTop (nhds 0) := by
      simpa using (hquad.const_mul (30 / 121 : ℝ))
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (tsum_nonneg fun _ => norm_nonneg _)
          (le_of_lt (hhpos n))) _ hup
    exact Filter.Eventually.of_forall fun n => by
      have hb := (acceptedPhase_returnedKernel_summable_and_bound
        P hP hPnorm (θ n) (hθ0 n) (hθ1 n)).2
      calc
        (∑' k : ℕ, ‖acceptedPhaseB P (θ n) *
            (acceptedPhaseD P (θ n)) ^ k * acceptedPhaseC P (θ n)‖) / h n
            ≤ (30 / 121 * (θ n) ^ 2) / h n :=
          div_le_div_of_nonneg_right hb (le_of_lt (hhpos n))
        _ = 30 / 121 * ((θ n / h n) ^ 2 * h n) := by
          field_simp [(hhpos n).ne']

/-- Exact reduction of physical-time model powers to their scalar transient
multiplier.  Combined with `θ/h → a`, this is the continuum semigroup
`I + (exp (-(4a/11)t) - 1)P = exp ((4a/11)t(R-I))`. -/
theorem acceptedPhase_sampledModel_exact
    (P : A) (hP : P * P = P) (θ h t : ℝ) (hh : 0 < h) :
    (acceptedPhaseModelStep P θ) ^ ⌊t / h⌋₊ =
      1 + (Real.exp ((-4 * θ / 11) * (⌊t / h⌋₊ : ℝ)) - 1) • P := by
  exact acceptedPhaseModelStep_pow P hP θ ⌊t / h⌋₊

/-- The negative exponential is one-Lipschitz on nonnegative arguments. -/
theorem expNeg_abs_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  rcases le_total u v with huv | hvu
  · have hmono : Real.exp (-v) ≤ Real.exp (-u) :=
      Real.exp_le_exp.mpr (neg_le_neg huv)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    have hgap0 : 0 ≤ v - u := sub_nonneg.mpr huv
    have hone : 0 ≤ 1 - Real.exp (-(v - u)) := by
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hgap0))
    have hfactor : Real.exp (-u) - Real.exp (-v) =
        Real.exp (-u) * (1 - Real.exp (-(v - u))) := by
      rw [show -v = -u + -(v - u) by ring, Real.exp_add]
      ring
    rw [hfactor]
    calc
      Real.exp (-u) * (1 - Real.exp (-(v - u)))
          ≤ 1 * (1 - Real.exp (-(v - u))) := by
            gcongr
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
      _ ≤ v - u := by
        linarith [Real.one_sub_le_exp_neg (v - u)]
      _ = -(u - v) := by ring
  · have hmono : Real.exp (-u) ≤ Real.exp (-v) :=
      Real.exp_le_exp.mpr (neg_le_neg hvu)
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hgap0 : 0 ≤ u - v := sub_nonneg.mpr hvu
    have hone : 0 ≤ 1 - Real.exp (-(u - v)) := by
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hgap0))
    have hfactor : Real.exp (-v) - Real.exp (-u) =
        Real.exp (-v) * (1 - Real.exp (-(u - v))) := by
      rw [show -u = -v + -(u - v) by ring, Real.exp_add]
      ring
    rw [neg_sub, hfactor]
    calc
      Real.exp (-v) * (1 - Real.exp (-(u - v)))
          ≤ 1 * (1 - Real.exp (-(u - v))) := by
            gcongr
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
      _ ≤ u - v := by
        linarith [Real.one_sub_le_exp_neg (u - v)]

/-- Uniform floor-sampling estimate on `0 ≤ t ≤ T`. -/
theorem floorSample_parameter_error_le
    {h θ a T t : ℝ} (hh : 0 < h) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |θ * (⌊t / h⌋₊ : ℝ) - a * t| ≤
      |θ / h - a| * T + θ := by
  let m : ℕ := ⌊t / h⌋₊
  have hth0 : 0 ≤ t / h := div_nonneg ht0 (le_of_lt hh)
  have hfloor : (m : ℝ) ≤ t / h := by
    exact Nat.floor_le hth0
  have hfloor' : t / h < (m : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hsle : h * (m : ℝ) ≤ t := by
    apply (le_div_iff₀' hh).mp
    simpa [mul_comm] using hfloor
  have hsgap : t - h * (m : ℝ) ≤ h := by
    have := (div_lt_iff₀ hh).mp hfloor'
    nlinarith
  have hs0 : 0 ≤ h * (m : ℝ) := mul_nonneg (le_of_lt hh) (by positivity)
  let q : ℝ := θ / h
  have hq0 : 0 ≤ q := div_nonneg hθ (le_of_lt hh)
  have hθm : θ * (m : ℝ) = q * (h * (m : ℝ)) := by
    dsimp [q]
    field_simp [hh.ne']
  rw [hθm]
  have hdecomp : q * (h * (m : ℝ)) - a * t =
      (q - a) * t + q * (h * (m : ℝ) - t) := by ring
  rw [hdecomp]
  calc
    |(q - a) * t + q * (h * (m : ℝ) - t)|
        ≤ |(q - a) * t| + |q * (h * (m : ℝ) - t)| := abs_add_le _ _
    _ = |q - a| * t + q * (t - h * (m : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hq0,
        abs_of_nonpos (sub_nonpos.mpr hsle)]
      ring
    _ ≤ |q - a| * T + q * h := by
      gcongr
    _ = |θ / h - a| * T + θ := by
      dsimp [q]
      field_simp [hh.ne']

/-- Explicit compact-time error bound for the stationary-head compression. -/
theorem acceptedPhase_compactTime_error_le
    (P : A) (hP : P * P = P) (hPnorm : ‖P‖ ≤ 1)
    {h θ a T t : ℝ} (hh : 0 < h) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖(acceptedPhaseModelStep P θ) ^ ⌊t / h⌋₊ -
        (1 + (Real.exp (-(4 * a / 11 * t)) - 1) • P)‖ ≤
      (4 / 11) * (|θ / h - a| * T + θ) := by
  rw [acceptedPhase_sampledModel_exact P hP θ h t hh]
  have hargθ : (-4 * θ / 11) * (⌊t / h⌋₊ : ℝ) =
      -(4 / 11 * (θ * (⌊t / h⌋₊ : ℝ))) := by ring
  have harga : -(4 * a / 11 * t) = -(4 / 11 * (a * t)) := by ring
  have heq :
      (1 + (Real.exp ((-4 * θ / 11) * (⌊t / h⌋₊ : ℝ)) - 1) • P) -
          (1 + (Real.exp (-(4 * a / 11 * t)) - 1) • P) =
        (Real.exp (-(4 / 11 * (θ * (⌊t / h⌋₊ : ℝ)))) -
          Real.exp (-(4 / 11 * (a * t)))) • P := by
    rw [hargθ, harga]
    module
  rw [heq, norm_smul, Real.norm_eq_abs]
  have hu : 0 ≤ (4 / 11 : ℝ) * (θ * (⌊t / h⌋₊ : ℝ)) := by positivity
  have hv : 0 ≤ (4 / 11 : ℝ) * (a * t) := by positivity
  have hexp := expNeg_abs_sub_le hu hv
  calc
    |Real.exp (-(4 / 11 * (θ * (⌊t / h⌋₊ : ℝ)))) -
        Real.exp (-(4 / 11 * (a * t)))| * ‖P‖
        ≤ |(4 / 11 : ℝ) * (θ * (⌊t / h⌋₊ : ℝ)) -
            (4 / 11 : ℝ) * (a * t)| * 1 := by gcongr
    _ = (4 / 11) * |θ * (⌊t / h⌋₊ : ℝ) - a * t| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 11)]
      ring
    _ ≤ (4 / 11) * (|θ / h - a| * T + θ) := by
      gcongr
      exact floorSample_parameter_error_le hh hθ ha ht0 htT

/-- The limiting accepted-phase evolution, written intrinsically in the
payload-complement projection. -/
noncomputable def acceptedPhaseLimit (P : A) (a t : ℝ) : A :=
  1 + (Real.exp (-(4 * a / 11 * t)) - 1) • P

@[simp]
theorem acceptedPhaseLimit_zero (P : A) (a : ℝ) :
    acceptedPhaseLimit P a 0 = 1 := by
  simp [acceptedPhaseLimit]

/-- The continuum limit is a genuine one-parameter semigroup.  For
`P = I - R` this is exactly `exp ((4a/11)t(R-I))`. -/
theorem acceptedPhaseLimit_add (P : A) (hP : P * P = P)
    (a s t : ℝ) :
    acceptedPhaseLimit P a (s + t) =
      acceptedPhaseLimit P a s * acceptedPhaseLimit P a t := by
  have hmul (c d : ℝ) :
      ((1 : A) + c • P) * (1 + d • P) =
        1 + (c + d + c * d) • P := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc,
      mul_smul_comm, hP, smul_smul]
    module
  rw [acceptedPhaseLimit, acceptedPhaseLimit, acceptedPhaseLimit, hmul]
  congr 2
  rw [show -(4 * a / 11 * (s + t)) =
      -(4 * a / 11 * s) + -(4 * a / 11 * t) by ring, Real.exp_add]
  ring

/-- If `h → 0` and `θ/h → a`, the sampled accepted-phase model converges
uniformly on every compact interval to `acceptedPhaseLimit P a`. -/
theorem acceptedPhase_uniformOnCompacts
    (P : A) (hP : P * P = P) (hPnorm : ‖P‖ ≤ 1)
    (h θ : ℕ → ℝ) (a : ℝ)
    (hhpos : ∀ n, 0 < h n) (hθ0 : ∀ n, 0 ≤ θ n) (ha : 0 ≤ a)
    (hh : Filter.Tendsto h Filter.atTop (nhds 0))
    (hratio : Filter.Tendsto (fun n => θ n / h n) Filter.atTop
      (nhds a)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ t : ℝ, 0 ≤ t → t ≤ T →
        ‖(acceptedPhaseModelStep P (θ n)) ^ ⌊t / h n⌋₊ -
          acceptedPhaseLimit P a t‖ < ε := by
  have hθlim : Filter.Tendsto θ Filter.atTop (nhds 0) := by
    have hmul := hratio.mul hh
    convert hmul using 1
    · funext n
      field_simp [(hhpos n).ne']
    · simp
  have habs : Filter.Tendsto (fun n => |θ n / h n - a|)
      Filter.atTop (nhds 0) := by
    have hdiff : Filter.Tendsto (fun n => θ n / h n - a)
        Filter.atTop (nhds (a - a)) :=
      hratio.sub tendsto_const_nhds
    simpa using hdiff.abs
  intro T hT ε hε
  have herr : Filter.Tendsto
      (fun n => (4 / 11 : ℝ) * (|θ n / h n - a| * T + θ n))
      Filter.atTop (nhds 0) := by
    have hinner := (habs.mul_const T).add hθlim
    simpa using hinner.const_mul (4 / 11 : ℝ)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp herr ε hε
  exact Filter.eventually_atTop.2 ⟨N, fun n hn t ht0 htT => by
    have hbound := acceptedPhase_compactTime_error_le P hP hPnorm
      (hhpos n) (hθ0 n) ha ht0 htT
    apply lt_of_le_of_lt hbound
    have hnonneg : 0 ≤ (4 / 11 : ℝ) *
        (|θ n / h n - a| * T + θ n) :=
      mul_nonneg (by norm_num)
        (add_nonneg (mul_nonneg (abs_nonneg _) hT) (hθ0 n))
    have hnear := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hnear
    exact hnear⟩

end ProjectionAlgebra

end NCG
