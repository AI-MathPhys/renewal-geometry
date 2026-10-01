/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Tangential stationarity, the normal row, and residual-preserving extension
  (`prop:normal-source`, `prop:constraint-extension`, Einstein–SM action closure)

## `prop:normal-source`

On real normed spaces `X_h` (states), `Z_h` (constraint values) and `P`
(physical tests), with `S_h : X_h → ℝ`, `C_h : X_h → Z_h`, a right inverse
`B_h` of `DC_h(x_h)` and a lift `I_h : P → X_h`:

* `constraintNormalProjector` — `P_h = I - B_h DC_h(x_h)`;
  `constraintNormalProjector_mem_ker` and `constraintNormalProjector_decomp`
  give `DC_h P_h w = 0` and `w = P_h w + B_h DC_h w`;
* `normalSource_bound` — `eq:normal-source-bound` for every test with
  `‖v‖ ≤ 1`, and `normalSource_iSup_bound` — the supremum form;
* `normalSource_counterexample` — `S(x,y) = x² + y`, `C(x,y) = y`: `DS(0,0)`
  vanishes on `ker DC(0,0)` (the restriction to `C = 0` is stationary) while
  `DS(0,0)[(0,1)] = 1`.

Surjectivity of `DC_h(x_h)` follows from the right inverse and is not assumed
separately; the finite-dimensional Hilbert structure is not needed.  Scoped
hypotheses disclosed: `a_h, b_h ≥ 0` (implicit for the constants of the two
covector bounds).

## `prop:constraint-extension`

Chart coordinates `(s, c) ∈ E_s × E_c` (real normed spaces), `J : E_s × E_c → F`
a `C¹` map into a complete normed space `F` (matrix-valued maps are the case
`F = Matrix n n ℝ` with any normed structure); the normal derivative is
`D_cJ(s,c) = fderiv ℝ (fun c' => J (s, c')) c`.

* `constraintExtension_ftc` — `eq:constraint-extension`
  `J(s,c) = J(s,0) + ∫₀¹ D_cJ(s,tc)[c] dt`;
* `constraintTracking_le` — Gronwall for the tracking equation
  `ċ = A(t) c + r(t)` on `[0,T]`: `‖c(t)‖ ≤ e^M (‖c(0)‖ + ∫₀ᵀ‖r‖)` when
  `∫₀ᵀ ‖A‖ ≤ M`; `constraintTracking` — `eq:constraint-tracking`
  `sup_{[0,T]} ‖c_a‖ ≤ C e^M a^p` from `‖c_a(0)‖ + ‖r_a‖_{L¹} ≤ C a^p`;
* `constraintExtension_matrix_estimate` — a uniform bound `‖D_cJ‖ ≤ L` gives
  `‖J(s(t),c(t)) - J(s(t),0)‖ ≤ L C e^M a^p` along such paths.

Scoped hypotheses disclosed: the tracking equation holds classically
(`c` continuous on `[0,T]` with right derivative `A(t)c(t) + r(t)` on
`[0,T)`, `A` and `r` continuous on `[0,T]`), rather than in the
Carathéodory/`L¹` sense.  The closing caveat about an independent state-only
source `f(s,c)` is commentary (a constant `J` imposes no restriction on `f`)
and is not formalized.
-/

namespace RenewalGeometry

open Set MeasureTheory intervalIntegral

section NormalSource

variable {X Z P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- `prop:normal-source`: the tangential projector `P_h = I - B_h DC_h(x_h)`. -/
noncomputable def constraintNormalProjector (DC : X →L[ℝ] Z) (B : Z →L[ℝ] X) : X →L[ℝ] X :=
  ContinuousLinearMap.id ℝ X - B.comp DC

/-- Since `DC_h B_h = I`, `P_h w` lies in the tangent kernel `ker DC_h(x_h)`. -/
theorem constraintNormalProjector_mem_ker (DC : X →L[ℝ] Z) (B : Z →L[ℝ] X)
    (hB : ∀ q, DC (B q) = q) (w : X) : DC (constraintNormalProjector DC B w) = 0 := by
  simp [constraintNormalProjector, hB]

/-- `w = P_h w + B_h DC_h(x_h) w`. -/
theorem constraintNormalProjector_decomp (DC : X →L[ℝ] Z) (B : Z →L[ℝ] X) (w : X) :
    w = constraintNormalProjector DC B w + B (DC w) := by
  simp [constraintNormalProjector]

/-- A right inverse makes the constraint derivative surjective. -/
theorem constraintNormal_surjective (DC : X →L[ℝ] Z) (B : Z →L[ℝ] X)
    (hB : ∀ q, DC (B q) = q) : Function.Surjective DC :=
  fun q => ⟨B q, hB q⟩

/-- `prop:normal-source`, `eq:normal-source-bound` (pointwise form): with
`B_h` a right inverse of `DC_h(x_h)`, `P_h = I - B_h DC_h(x_h)`,
`‖P_h I_h v‖ ≤ L^tan`, `‖DC_h(x_h) I_h v‖ ≤ L^nor` for unit tests,
`|DS_h(x_h)[w]| ≤ a_h ‖w‖` on `ker DC_h(x_h)` and `|DS_h(x_h)[B_h q]| ≤ b_h ‖q‖`,
every unit test satisfies `|DS_h(x_h)[I_h v]| ≤ a_h L^tan + b_h L^nor`. -/
theorem normalSource_bound (S : X → ℝ) (C : X → Z) (x : X) (B : Z →L[ℝ] X)
    (hB : ∀ q, fderiv ℝ C x (B q) = q) (I : P →L[ℝ] X) {Ltan Lnor a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htan : ∀ v, ‖v‖ ≤ 1 → ‖constraintNormalProjector (fderiv ℝ C x) B (I v)‖ ≤ Ltan)
    (hnor : ∀ v, ‖v‖ ≤ 1 → ‖fderiv ℝ C x (I v)‖ ≤ Lnor)
    (hker : ∀ w, fderiv ℝ C x w = 0 → |fderiv ℝ S x w| ≤ a * ‖w‖)
    (hnormal : ∀ q, |fderiv ℝ S x (B q)| ≤ b * ‖q‖) :
    ∀ v, ‖v‖ ≤ 1 → |fderiv ℝ S x (I v)| ≤ a * Ltan + b * Lnor := by
  intro v hv
  set DC := fderiv ℝ C x
  set DS := fderiv ℝ S x
  have hdec := constraintNormalProjector_decomp DC B (I v)
  have hk := constraintNormalProjector_mem_ker DC B hB (I v)
  calc |DS (I v)| = |DS (constraintNormalProjector DC B (I v)) + DS (B (DC (I v)))| := by
        conv_lhs => rw [hdec]
        rw [map_add]
    _ ≤ |DS (constraintNormalProjector DC B (I v))| + |DS (B (DC (I v)))| := abs_add_le _ _
    _ ≤ a * ‖constraintNormalProjector DC B (I v)‖ + b * ‖DC (I v)‖ :=
        add_le_add (hker _ hk) (hnormal _)
    _ ≤ a * Ltan + b * Lnor :=
        add_le_add (mul_le_mul_of_nonneg_left (htan v hv) ha)
          (mul_le_mul_of_nonneg_left (hnor v hv) hb)

/-- `prop:normal-source`, `eq:normal-source-bound` (supremum form):
`sup_{‖v‖ ≤ 1} |DS_h(x_h)[I_h v]| ≤ a_h L^tan + b_h L^nor`. -/
theorem normalSource_iSup_bound (S : X → ℝ) (C : X → Z) (x : X) (B : Z →L[ℝ] X)
    (hB : ∀ q, fderiv ℝ C x (B q) = q) (I : P →L[ℝ] X) {Ltan Lnor a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htan : ∀ v, ‖v‖ ≤ 1 → ‖constraintNormalProjector (fderiv ℝ C x) B (I v)‖ ≤ Ltan)
    (hnor : ∀ v, ‖v‖ ≤ 1 → ‖fderiv ℝ C x (I v)‖ ≤ Lnor)
    (hker : ∀ w, fderiv ℝ C x w = 0 → |fderiv ℝ S x w| ≤ a * ‖w‖)
    (hnormal : ∀ q, |fderiv ℝ S x (B q)| ≤ b * ‖q‖) :
    ⨆ v : {v : P // ‖v‖ ≤ 1}, |fderiv ℝ S x (I v)| ≤ a * Ltan + b * Lnor := by
  have : Nonempty {v : P // ‖v‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  exact ciSup_le fun v =>
    normalSource_bound S C x B hB I ha hb htan hnor hker hnormal v.1 v.2

/-- `prop:normal-source`, failure of the unrestricted implication:
for `S(x,y) = x² + y` and `C(x,y) = y`, the derivative `DS(0,0)` vanishes on
`ker DC(0,0)` (the restriction of `S` to `C = 0` is stationary at the origin),
whereas `DS(0,0)[(0,1)] = 1`. -/
theorem normalSource_counterexample :
    (∀ w : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => p.2) 0 w = 0 →
        fderiv ℝ (fun p : ℝ × ℝ => p.1 * p.1 + p.2) 0 w = 0) ∧
      fderiv ℝ (fun p : ℝ × ℝ => p.1 * p.1 + p.2) 0 (0, 1) = 1 := by
  have hC : fderiv ℝ (fun p : ℝ × ℝ => p.2) 0 = ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (hasFDerivAt_snd).fderiv
  have hS : fderiv ℝ (fun p : ℝ × ℝ => p.1 * p.1 + p.2) 0 = ContinuousLinearMap.snd ℝ ℝ ℝ := by
    have h := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).mul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ)))).add (hasFDerivAt_snd (p := (0 : ℝ × ℝ)))
    rw [show (fun p : ℝ × ℝ => p.1 * p.1 + p.2) = (Prod.fst * Prod.fst + Prod.snd) from rfl,
      h.fderiv]
    ext <;> simp
  rw [hC, hS]
  exact ⟨fun w hw => hw, rfl⟩

end NormalSource

section ConstraintExtension

variable {Es Ec F : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Ec] [NormedSpace ℝ Ec] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `prop:constraint-extension`, `eq:constraint-extension`: for a `C¹` map
`J(s,c)`, `J(s,c) = J(s,0) + ∫₀¹ D_cJ(s,tc)[c] dt`, where
`D_cJ(s,c) = fderiv ℝ (fun c' => J (s, c')) c`. -/
theorem constraintExtension_ftc [CompleteSpace F] (J : Es × Ec → F) (hJ : ContDiff ℝ 1 J)
    (s : Es) (c : Ec) :
    J (s, c) = J (s, 0) + ∫ t in (0 : ℝ)..1, fderiv ℝ (fun c' => J (s, c')) (t • c) c := by
  set G : Ec → F := fun c' => J (s, c')
  have hG : ContDiff ℝ 1 G := hJ.comp (contDiff_const.prodMk contDiff_id)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => G (t • c)) (fderiv ℝ G (t • c) c) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t • c) ((1 : ℝ) • c) t := (hasDerivAt_id t).smul_const c
    have h2 := ((hG.differentiable one_ne_zero) (t • c)).hasFDerivAt.comp_hasDerivAt t h1
    simpa [Function.comp_def] using h2
  have hcont : Continuous fun t : ℝ => fderiv ℝ G (t • c) c :=
    ((hG.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const
  have hint := integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable 0 1)
  rw [hint]
  simp [G]

omit [NormedAddCommGroup Es] [NormedSpace ℝ Es] [NormedAddCommGroup Ec] [NormedSpace ℝ Ec] in
/-- Gronwall for the tracking equation `ċ = A(t) c + r(t)` on `[0,T]`:
if `∫₀ᵀ ‖A‖ ≤ M`, then `‖c(t)‖ ≤ e^M (‖c(0)‖ + ∫₀ᵀ ‖r‖)` on `[0,T]`. -/
theorem constraintTracking_le {T M : ℝ} (hT : 0 ≤ T) (c : ℝ → F) (A : ℝ → F →L[ℝ] F)
    (r : ℝ → F) (hA : ContinuousOn A (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hc : ContinuousOn c (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt c (A t (c t) + r t) (Ici t) t)
    (hM : ∫ t in (0 : ℝ)..T, ‖A t‖ ≤ M) :
    ∀ t ∈ Icc 0 T, ‖c t‖ ≤ Real.exp M * (‖c 0‖ + ∫ t in (0 : ℝ)..T, ‖r t‖) := by
  -- continuous extensions of `A` and `r` to the whole line
  set Ae : ℝ → F →L[ℝ] F := fun t => A (projIcc 0 T hT t)
  set re : ℝ → F := fun t => r (projIcc 0 T hT t)
  have hAe : Continuous Ae := hA.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (projIcc 0 T hT t).2)
  have hre : Continuous re := hr.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (projIcc 0 T hT t).2)
  have hAeq : ∀ t ∈ Icc 0 T, Ae t = A t := fun t ht => by simp [Ae, projIcc_of_mem hT ht]
  have hreq : ∀ t ∈ Icc 0 T, re t = r t := fun t ht => by simp [re, projIcc_of_mem hT ht]
  have hnA : Continuous fun t => ‖Ae t‖ := hAe.norm
  have hnr : Continuous fun t => ‖re t‖ := hre.norm
  set α : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ‖Ae s‖
  set ρ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ‖re s‖
  have hα' : ∀ t, HasDerivAt α ‖Ae t‖ t := fun t => (hnA.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hρ' : ∀ t, HasDerivAt ρ ‖re t‖ t := fun t => (hnr.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hα0 : ∀ t, 0 ≤ t → 0 ≤ α t := fun t ht =>
    integral_nonneg ht fun s _ => norm_nonneg _
  -- monotone bounds on `[0,T]`
  have hsplitA : ∀ t, α T = α t + ∫ s in t..T, ‖Ae s‖ := fun t =>
    (integral_add_adjacent_intervals (hnA.intervalIntegrable 0 t)
      (hnA.intervalIntegrable t T)).symm
  have hsplitr : ∀ t, ρ T = ρ t + ∫ s in t..T, ‖re s‖ := fun t =>
    (integral_add_adjacent_intervals (hnr.intervalIntegrable 0 t)
      (hnr.intervalIntegrable t T)).symm
  have hαT : α T = ∫ t in (0 : ℝ)..T, ‖A t‖ :=
    integral_congr fun t ht => by
      rw [uIcc_of_le hT] at ht
      simp only [hAeq t ht]
  have hρT : ρ T = ∫ t in (0 : ℝ)..T, ‖r t‖ :=
    integral_congr fun t ht => by
      rw [uIcc_of_le hT] at ht
      simp only [hreq t ht]
  have hαle : ∀ t ∈ Icc 0 T, α t ≤ M := fun t ht => by
    have := integral_nonneg (μ := volume) ht.2 fun s _ => norm_nonneg (Ae s)
    linarith [hsplitA t]
  have hρle : ∀ t ∈ Icc 0 T, ρ t ≤ ∫ t in (0 : ℝ)..T, ‖r t‖ := fun t ht => by
    have := integral_nonneg (μ := volume) ht.2 fun s _ => norm_nonneg (re s)
    linarith [hsplitr t]
  -- the ε-perturbed comparison function
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T,
      ‖c t‖ ≤ Real.exp (α t) * (‖c 0‖ + ε + ρ t + ε * t) := by
    intro ε hε
    set Q : ℝ → ℝ := fun t => ‖c 0‖ + ε + ρ t + ε * t
    have hQ' : ∀ t, HasDerivAt Q (‖re t‖ + ε) t := fun t =>
      (((hasDerivAt_const t (‖c 0‖ + ε)).add (hρ' t)).add
        ((hasDerivAt_id t).const_mul ε)).congr_deriv (by simp)
    have hB' : ∀ t, HasDerivAt (fun t => Real.exp (α t) * Q t)
        (Real.exp (α t) * ‖Ae t‖ * Q t + Real.exp (α t) * (‖re t‖ + ε)) t := fun t =>
      (((hα' t).exp).mul (hQ' t)).congr_deriv (by ring)
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary hc hode ?_ hB' ?_
    · simp [α, ρ]
      linarith
    · intro t ht heq
      have ht' : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hexp : 1 ≤ Real.exp (α t) := Real.one_le_exp (hα0 t ht.1)
      calc ‖A t (c t) + r t‖ ≤ ‖A t (c t)‖ + ‖r t‖ := norm_add_le _ _
        _ ≤ ‖A t‖ * ‖c t‖ + ‖r t‖ := add_le_add ((A t).le_opNorm _) le_rfl
        _ = ‖Ae t‖ * (Real.exp (α t) * Q t) + ‖re t‖ := by
            rw [hAeq t ht', hreq t ht', heq]
        _ < Real.exp (α t) * ‖Ae t‖ * Q t + Real.exp (α t) * (‖re t‖ + ε) := by
            have : ‖re t‖ < Real.exp (α t) * (‖re t‖ + ε) := by
              nlinarith [norm_nonneg (re t)]
            nlinarith
  intro t ht
  set R := ∫ t in (0 : ℝ)..T, ‖r t‖
  have hρt0 : 0 ≤ ρ t := integral_nonneg ht.1 fun s _ => norm_nonneg _
  have hexpM : Real.exp (α t) ≤ Real.exp M := Real.exp_le_exp.2 (hαle t ht)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Real.exp M * (1 + T)) with hεdef
  have hden : 0 < Real.exp M * (1 + T) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have h1 := key ε hε t ht
  have hQnn : 0 ≤ ‖c 0‖ + ε + ρ t + ε * t := by
    have := mul_nonneg hε.le ht.1
    linarith [norm_nonneg (c 0)]
  have h2 : Real.exp (α t) * (‖c 0‖ + ε + ρ t + ε * t) ≤
      Real.exp M * (‖c 0‖ + ε + ρ t + ε * t) :=
    mul_le_mul_of_nonneg_right hexpM hQnn
  have h3 : ‖c 0‖ + ε + ρ t + ε * t ≤ (‖c 0‖ + R) + ε * (1 + T) := by
    have := mul_le_mul_of_nonneg_left ht.2 hε.le
    linarith [hρle t ht]
  have h4 : Real.exp M * (ε * (1 + T)) = δ := by
    rw [hεdef]; field_simp
  calc ‖c t‖ ≤ Real.exp M * (‖c 0‖ + ε + ρ t + ε * t) := h1.trans h2
    _ ≤ Real.exp M * ((‖c 0‖ + R) + ε * (1 + T)) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos M).le
    _ = Real.exp M * (‖c 0‖ + R) + δ := by rw [mul_add, h4]

omit [NormedAddCommGroup Es] [NormedSpace ℝ Es] [NormedAddCommGroup Ec] [NormedSpace ℝ Ec] in
/-- `prop:constraint-extension`, `eq:constraint-tracking`: if `c_a` satisfies
the exact tracking equation `ċ_a = A_a(t) c_a + r_a(t)` on `[0,T]` with
`∫₀ᵀ ‖A_a‖ ≤ M` and `‖c_a(0)‖ + ‖r_a‖_{L¹(0,T)} ≤ C a^p`, then
`sup_{0 ≤ t ≤ T} ‖c_a(t)‖ ≤ C e^M a^p`. -/
theorem constraintTracking {T M C a p : ℝ} (hT : 0 ≤ T) (c : ℝ → F) (A : ℝ → F →L[ℝ] F)
    (r : ℝ → F) (hA : ContinuousOn A (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hc : ContinuousOn c (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt c (A t (c t) + r t) (Ici t) t)
    (hM : ∫ t in (0 : ℝ)..T, ‖A t‖ ≤ M)
    (hdata : ‖c 0‖ + ∫ t in (0 : ℝ)..T, ‖r t‖ ≤ C * a ^ p) :
    ∀ t ∈ Icc 0 T, ‖c t‖ ≤ C * Real.exp M * a ^ p := by
  intro t ht
  calc ‖c t‖ ≤ Real.exp M * (‖c 0‖ + ∫ t in (0 : ℝ)..T, ‖r t‖) :=
        constraintTracking_le hT c A r hA hr hc hode hM t ht
    _ ≤ Real.exp M * (C * a ^ p) := mul_le_mul_of_nonneg_left hdata (Real.exp_pos M).le
    _ = C * Real.exp M * a ^ p := by ring

/-- `prop:constraint-extension`, matrix estimate: a uniform bound
`‖D_cJ‖ ≤ L` together with `eq:constraint-tracking` gives
`‖J(s(t), c(t)) - J(s(t), 0)‖ ≤ L · C e^M a^p` on `[0,T]` (an `O(a^p)`
difference between the full and constrained principal matrices). -/
theorem constraintExtension_matrix_estimate (J : Es × Ec → F) (hJ : ContDiff ℝ 1 J) {L : ℝ}
    (hL : ∀ s c', ‖fderiv ℝ (fun c'' => J (s, c'')) c'‖ ≤ L)
    {T M C a p : ℝ} (hT : 0 ≤ T) (sp : ℝ → Es) (c : ℝ → Ec) (A : ℝ → Ec →L[ℝ] Ec)
    (r : ℝ → Ec) (hA : ContinuousOn A (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hc : ContinuousOn c (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt c (A t (c t) + r t) (Ici t) t)
    (hM : ∫ t in (0 : ℝ)..T, ‖A t‖ ≤ M)
    (hdata : ‖c 0‖ + ∫ t in (0 : ℝ)..T, ‖r t‖ ≤ C * a ^ p) :
    ∀ t ∈ Icc 0 T, ‖J (sp t, c t) - J (sp t, 0)‖ ≤ L * (C * Real.exp M * a ^ p) := by
  intro t ht
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL (sp t) 0)
  set G : Ec → F := fun c' => J (sp t, c')
  have hG : ContDiff ℝ 1 G := hJ.comp (contDiff_const.prodMk contDiff_id)
  have hmv := (convex_univ : Convex ℝ (univ : Set Ec)).norm_image_sub_le_of_norm_fderiv_le
    (f := G) (fun x _ => (hG.differentiable one_ne_zero) x) (fun x _ => hL (sp t) x)
    (mem_univ 0) (mem_univ (c t))
  rw [sub_zero] at hmv
  calc ‖J (sp t, c t) - J (sp t, 0)‖ ≤ L * ‖c t‖ := hmv
    _ ≤ L * (C * Real.exp M * a ^ p) :=
        mul_le_mul_of_nonneg_left (constraintTracking hT c A r hA hr hc hode hM hdata t ht) hL0

end ConstraintExtension

end RenewalGeometry
