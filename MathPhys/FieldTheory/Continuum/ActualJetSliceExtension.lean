/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Gravity.ActualJetFieldBridge

/-!
# Second-order Taylor extensions of Cauchy slice data

Generic infrastructure (no renewal notions) for the Cauchy-data completion of
`prop:generated-initial` (Einstein–Standard-Model action-closure manuscript,
`app:generated-dynamics`): from slice fields `a, b, c` on `ℝ³` (the value, the first and the
second time derivative on `t = 0`) we build a smooth space-time field on `ℝ × ℝ³` with exactly
these normal jets on the slice and a uniformly small deviation from `a` at all times:

`textn ε a b c (t, y) = a(y) + φ₁(t) b(y) + φ₂(t) c(y)`,
`φ₁(t) = ε sin(t/ε)`, `φ₂(t) = ε²(1 - cos(t/ε))`.

* `sep α β (t, y) = α(t) β(y)` and its partial derivatives (`pd_sep_zero`, `pd_sep_succ`);
* `contDiff_textn`, `isSPeriodic_textn`;
* the slice jets (`textn_slice`, `pd_textn_zero_slice`, `pd_textn_succ_slice`,
  `pd_pd_textn_zero_zero_slice`, `pd_pd_textn_*_slice`): value `a`, normal derivative `b`, second
  normal derivative `c`, tangential derivatives those of `a`, mixed derivatives those of `b`;
* `norm_textn_sub_le`: `‖textn ε a b c (t, y) - a(y)‖ ≤ ε ‖b(y)‖ + 2ε² ‖c(y)‖` for all `t`.
-/

open Set
open scoped ContDiff

noncomputable section

namespace MathPhys.SliceExt

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk ActualJetBridge

set_option linter.unusedSectionVars false

/-! ### The time profiles -/

/-- `φ₁(t) = ε sin(t/ε)`: `φ₁(0) = 0`, `φ₁'(0) = 1`, `φ₁''(0) = 0`, `|φ₁| ≤ ε`. -/
def φ1 (ε t : ℝ) : ℝ := ε * Real.sin (t / ε)

/-- `φ₂(t) = ε²(1 - cos(t/ε))`: `φ₂(0) = φ₂'(0) = 0`, `φ₂''(0) = 1`, `|φ₂| ≤ 2ε²`. -/
def φ2 (ε t : ℝ) : ℝ := ε ^ 2 * (1 - Real.cos (t / ε))

theorem hasDerivAt_φ1 {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (φ1 ε) (Real.cos (t / ε)) t := by
  have h := ((hasDerivAt_id' t).div_const ε).sin.const_mul ε
  exact h.congr_deriv (by field_simp)

theorem hasDerivAt_dφ1 {ε : ℝ} (t : ℝ) :
    HasDerivAt (fun t => Real.cos (t / ε)) (-(Real.sin (t / ε)) / ε) t := by
  have h := ((hasDerivAt_id' t).div_const ε).cos
  exact h.congr_deriv (by ring)

theorem hasDerivAt_φ2 {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (φ2 ε) (ε * Real.sin (t / ε)) t := by
  have h := (((hasDerivAt_id' t).div_const ε).cos.const_sub 1).const_mul (ε ^ 2)
  exact h.congr_deriv (by field_simp)

theorem hasDerivAt_dφ2 {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => ε * Real.sin (t / ε)) (Real.cos (t / ε)) t := by
  have h := ((hasDerivAt_id' t).div_const ε).sin.const_mul ε
  exact h.congr_deriv (by field_simp)

theorem contDiff_φ1 (ε : ℝ) : ContDiff ℝ ∞ (φ1 ε) := by
  unfold φ1; fun_prop

theorem contDiff_φ2 (ε : ℝ) : ContDiff ℝ ∞ (φ2 ε) := by
  unfold φ2; fun_prop

theorem abs_φ1_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : |φ1 ε t| ≤ ε := by
  unfold φ1
  rw [abs_mul, abs_of_nonneg hε]
  exact mul_le_of_le_one_right hε (Real.abs_sin_le_one _)

theorem abs_φ2_le (ε t : ℝ) : |φ2 ε t| ≤ 2 * ε ^ 2 := by
  unfold φ2
  rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
  have h1 := Real.neg_one_le_cos (t / ε)
  have h2 := Real.cos_le_one (t / ε)
  have : |1 - Real.cos (t / ε)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith [sq_nonneg ε]

/-! ### Separated fields -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The separated field `(t, y) ↦ α(t) β(y)`. -/
def sep (α : ℝ → ℝ) (β : (Fin 3 → ℝ) → E) : ST 3 → E := fun x => α (x 0) • β (Fin.tail x)

theorem contDiff_tail : ContDiff ℝ ∞ (fun x : ST 3 => (Fin.tail x : Fin 3 → ℝ)) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ

theorem contDiff_sep {α : ℝ → ℝ} {β : (Fin 3 → ℝ) → E} (hα : ContDiff ℝ ∞ α)
    (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (sep α β) :=
  (hα.comp (contDiff_apply ℝ ℝ 0)).smul (hβ.comp contDiff_tail)

theorem tail_add_ev_zero (x : ST 3) (s : ℝ) : Fin.tail (x + s • ev 0) = Fin.tail x := by
  funext i; simp [Fin.tail, ev, Pi.single_apply, Fin.succ_ne_zero]

theorem add_ev_zero_zero (x : ST 3) (s : ℝ) : (x + s • ev (0 : Fin 4) : ST 3) 0 = x 0 + s := by
  simp [ev]

theorem tail_add_ev_succ (x : ST 3) (s : ℝ) (j : Fin 3) :
    Fin.tail (x + s • ev j.succ) = Fin.tail x + s • Pi.single j 1 := by
  funext i; simp [Fin.tail, ev, Pi.single_apply, Fin.succ_inj]

theorem add_ev_succ_zero (x : ST 3) (s : ℝ) (j : Fin 3) :
    (x + s • ev j.succ : ST 3) 0 = x 0 := by
  simp [ev, Pi.single_apply, (Fin.succ_ne_zero j).symm]

/-- `∂_t (α β) = α' β`. -/
theorem pd_sep_zero {α α' : ℝ → ℝ} {β : (Fin 3 → ℝ) → E} (hα : ContDiff ℝ ∞ α)
    (hα' : ∀ t, HasDerivAt α (α' t) t) (hβ : ContDiff ℝ ∞ β) (x : ST 3) :
    pd (sep α β) 0 x = sep α' β x := by
  refine pd_eq_of_line ((contDiff_sep hα hβ).differentiable (by simp) x) ?_
  have e : (fun s : ℝ => sep α β (x + s • ev 0)) = fun s => α (x 0 + s) • β (Fin.tail x) := by
    funext s; simp only [sep, tail_add_ev_zero]; congr 2; simp [ev]
  rw [e]
  have h := (hα' (x 0 + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (x 0))
  simp only [add_zero, mul_one] at h
  exact h.smul_const (β (Fin.tail x))

/-- `∂_j (α β) = α ∂_jβ`. -/
theorem pd_sep_succ {α : ℝ → ℝ} {β : (Fin 3 → ℝ) → E} (hα : ContDiff ℝ ∞ α)
    (hβ : ContDiff ℝ ∞ β) (j : Fin 3) (x : ST 3) :
    pd (sep α β) j.succ x = sep α (pd β j) x := by
  refine pd_eq_of_line ((contDiff_sep hα hβ).differentiable (by simp) x) ?_
  have e : (fun s : ℝ => sep α β (x + s • ev j.succ)) =
      fun s => α (x 0) • β (Fin.tail x + s • ev j) := by
    funext s; simp only [sep, tail_add_ev_succ, add_ev_succ_zero]
  rw [e]
  have h := hasDerivAt_line (f := β) (x := Fin.tail x) j (s := 0)
    ((hβ.differentiable (by simp)) _)
  simp only [zero_smul, add_zero] at h
  exact h.const_smul (α (x 0))

theorem pd_add_fun {f g : ST 3 → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin 4) :
    pd (f + g) μ = pd f μ + pd g μ := by
  funext x
  unfold SobolevOpen.pd
  rw [fderiv_add ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)]
  rfl

theorem pd_add3 {f g h : ST 3 → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) (μ : Fin 4) : pd (f + g + h) μ = pd f μ + pd g μ + pd h μ := by
  rw [pd_add_fun (f := f + g) (hf.add hg) hh, pd_add_fun hf hg]

theorem contDiff_pd3 {β : (Fin 3 → ℝ) → E} (hβ : ContDiff ℝ ∞ β) (j : Fin 3) :
    ContDiff ℝ ∞ (pd β j) := by
  unfold SobolevOpen.pd
  exact (hβ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### The Taylor extension -/

/-- **The second-order Taylor extension** `a + φ₁ b + φ₂ c`. -/
def textn (ε : ℝ) (a b c : (Fin 3 → ℝ) → E) : ST 3 → E :=
  sep (fun _ => 1) a + sep (φ1 ε) b + sep (φ2 ε) c

theorem textn_apply (ε : ℝ) (a b c : (Fin 3 → ℝ) → E) (x : ST 3) :
    textn ε a b c x = a (Fin.tail x) + φ1 ε (x 0) • b (Fin.tail x) +
      φ2 ε (x 0) • c (Fin.tail x) := by
  simp [textn, sep]

variable {a b c : (Fin 3 → ℝ) → E}

theorem contDiff_textn (ε : ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (textn ε a b c) :=
  ((contDiff_sep contDiff_const ha).add (contDiff_sep (contDiff_φ1 ε) hb)).add
    (contDiff_sep (contDiff_φ2 ε) hc)

theorem isSPeriodic_textn (ε : ℝ) (ha : IsZPeriodic a) (hb : IsZPeriodic b)
    (hc : IsZPeriodic c) : IsSPeriodic (textn ε a b c) := by
  intro k x
  have h0 : (x + sshift k) 0 = x 0 := by simp [sshift]
  have ht : Fin.tail (x + sshift k) = Fin.tail x + zvec k := by
    funext i; simp [sshift, Fin.tail]
  rw [textn_apply, textn_apply, h0, ht, ha, hb, hc]

/-- The first partial derivatives of the extension as fields. -/
theorem pd_textn_zero {ε : ℝ} (hε : ε ≠ 0) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) :
    pd (textn ε a b c) 0 =
      sep (fun _ => 0) a + sep (fun t => Real.cos (t / ε)) b +
        sep (fun t => ε * Real.sin (t / ε)) c := by
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (1 : ℝ))) ha
  have h2 := contDiff_sep (contDiff_φ1 ε) hb
  have h3 := contDiff_sep (contDiff_φ2 ε) hc
  unfold textn
  rw [pd_add3 h1 h2 h3]
  funext x
  simp only [Pi.add_apply]
  rw [pd_sep_zero contDiff_const (fun t => hasDerivAt_const t (1 : ℝ)) ha,
    pd_sep_zero (contDiff_φ1 ε) (hasDerivAt_φ1 hε) hb,
    pd_sep_zero (contDiff_φ2 ε) (hasDerivAt_φ2 hε) hc]

theorem pd_textn_succ (ε : ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (j : Fin 3) :
    pd (textn ε a b c) j.succ =
      sep (fun _ => 1) (pd a j) + sep (φ1 ε) (pd b j) + sep (φ2 ε) (pd c j) := by
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (1 : ℝ))) ha
  have h2 := contDiff_sep (contDiff_φ1 ε) hb
  have h3 := contDiff_sep (contDiff_φ2 ε) hc
  unfold textn
  rw [pd_add3 h1 h2 h3]
  funext x
  simp only [Pi.add_apply]
  rw [pd_sep_succ contDiff_const ha, pd_sep_succ (contDiff_φ1 ε) hb,
    pd_sep_succ (contDiff_φ2 ε) hc]

/-! ### The slice jets -/

theorem tail_cons0 (y : Fin 3 → ℝ) : Fin.tail (Fin.cons (0 : ℝ) y : ST 3) = y := rfl

@[simp] theorem cons0_zero (y : Fin 3 → ℝ) : (Fin.cons (0 : ℝ) y : ST 3) 0 = 0 := rfl

theorem textn_slice (ε : ℝ) (y : Fin 3 → ℝ) : textn ε a b c (Fin.cons 0 y) = a y := by
  rw [textn_apply]; simp [φ1, φ2]

theorem pd_textn_zero_slice {ε : ℝ} (hε : ε ≠ 0) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (y : Fin 3 → ℝ) : pd (textn ε a b c) 0 (Fin.cons 0 y) = b y := by
  rw [pd_textn_zero hε ha hb hc]; simp [sep]

theorem pd_textn_succ_slice (ε : ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (j : Fin 3) (y : Fin 3 → ℝ) :
    pd (textn ε a b c) j.succ (Fin.cons 0 y) = pd a j y := by
  rw [pd_textn_succ ε ha hb hc]; simp [sep, φ1, φ2]

/-- `∂_t∂_t` of the extension on the slice is `c`. -/
theorem pd_pd_textn_zero_zero_slice {ε : ℝ} (hε : ε ≠ 0) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c) (y : Fin 3 → ℝ) :
    pd (pd (textn ε a b c) 0) 0 (Fin.cons 0 y) = c y := by
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (0 : ℝ))) ha
  have hc1 : ContDiff ℝ ∞ (fun t : ℝ => Real.cos (t / ε)) := by fun_prop
  have hs1 : ContDiff ℝ ∞ (fun t : ℝ => ε * Real.sin (t / ε)) := by fun_prop
  have h2 := contDiff_sep hc1 hb
  have h3 := contDiff_sep hs1 hc
  rw [pd_textn_zero hε ha hb hc, pd_add3 h1 h2 h3]
  simp only [Pi.add_apply]
  rw [pd_sep_zero contDiff_const (fun t => hasDerivAt_const t (0 : ℝ)) ha,
    pd_sep_zero hc1 (fun t => hasDerivAt_dφ1 t) hb, pd_sep_zero hs1 (hasDerivAt_dφ2 hε) hc]
  simp [sep]

/-- `∂_j∂_t` of the extension on the slice is `∂_j b`. -/
theorem pd_pd_textn_zero_succ_slice {ε : ℝ} (hε : ε ≠ 0) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c) (j : Fin 3) (y : Fin 3 → ℝ) :
    pd (pd (textn ε a b c) 0) j.succ (Fin.cons 0 y) = pd b j y := by
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (0 : ℝ))) ha
  have hc1 : ContDiff ℝ ∞ (fun t : ℝ => Real.cos (t / ε)) := by fun_prop
  have hs1 : ContDiff ℝ ∞ (fun t : ℝ => ε * Real.sin (t / ε)) := by fun_prop
  have h2 := contDiff_sep hc1 hb
  have h3 := contDiff_sep hs1 hc
  rw [pd_textn_zero hε ha hb hc, pd_add3 h1 h2 h3]
  simp only [Pi.add_apply]
  rw [pd_sep_succ contDiff_const ha j, pd_sep_succ hc1 hb j, pd_sep_succ hs1 hc j]
  simp [sep]

/-- `∂_t∂_j` of the extension on the slice is `∂_j b`. -/
theorem pd_pd_textn_succ_zero_slice {ε : ℝ} (hε : ε ≠ 0) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c) (j : Fin 3) (y : Fin 3 → ℝ) :
    pd (pd (textn ε a b c) j.succ) 0 (Fin.cons 0 y) = pd b j y := by
  have ha' := contDiff_pd3 ha j
  have hb' := contDiff_pd3 hb j
  have hc' := contDiff_pd3 hc j
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (1 : ℝ))) ha'
  have h2 := contDiff_sep (contDiff_φ1 ε) hb'
  have h3 := contDiff_sep (contDiff_φ2 ε) hc'
  rw [pd_textn_succ ε ha hb hc j, pd_add3 h1 h2 h3]
  simp only [Pi.add_apply]
  rw [pd_sep_zero contDiff_const (fun t => hasDerivAt_const t (1 : ℝ)) ha',
    pd_sep_zero (contDiff_φ1 ε) (hasDerivAt_φ1 hε) hb',
    pd_sep_zero (contDiff_φ2 ε) (hasDerivAt_φ2 hε) hc']
  simp [sep]

/-- `∂_k∂_j` of the extension on the slice is `∂_k∂_j a`. -/
theorem pd_pd_textn_succ_succ_slice (ε : ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (j k : Fin 3) (y : Fin 3 → ℝ) :
    pd (pd (textn ε a b c) j.succ) k.succ (Fin.cons 0 y) = pd (pd a j) k y := by
  have ha' := contDiff_pd3 ha j
  have hb' := contDiff_pd3 hb j
  have hc' := contDiff_pd3 hc j
  have h1 := contDiff_sep (E := E) (contDiff_const (c := (1 : ℝ))) ha'
  have h2 := contDiff_sep (contDiff_φ1 ε) hb'
  have h3 := contDiff_sep (contDiff_φ2 ε) hc'
  rw [pd_textn_succ ε ha hb hc j, pd_add3 h1 h2 h3]
  simp only [Pi.add_apply]
  rw [pd_sep_succ contDiff_const ha' k, pd_sep_succ (contDiff_φ1 ε) hb' k,
    pd_sep_succ (contDiff_φ2 ε) hc' k]
  simp [sep, φ1, φ2]

/-- **Uniform smallness of the deviation**: `‖textn - a‖ ≤ ε‖b‖ + 2ε²‖c‖` at every time. -/
theorem norm_textn_sub_le {ε : ℝ} (hε : 0 ≤ ε) (x : ST 3) :
    ‖textn ε a b c x - a (Fin.tail x)‖ ≤ ε * ‖b (Fin.tail x)‖ + 2 * ε ^ 2 * ‖c (Fin.tail x)‖ := by
  rw [textn_apply, add_assoc, add_sub_cancel_left]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  gcongr
  · exact abs_φ1_le hε _
  · exact abs_φ2_le ε _

end MathPhys.SliceExt
