/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabSobolevAlgebra

/-!
# Coefficient calculus on `[0, T] × 𝕋^d`: slab identities, `W^{k,∞}` bounds, inverses,
  polynomial Lipschitz estimates

Generic infrastructure (no renewal notions) for the quasilinear difference estimate of
`thm:hyperbolic` of the Einstein–Standard-Model action-closure manuscript, continuing
`Continuum/SlabSobolevAlgebra.lean`.

* `hasDeriv_line_eq_zero_of_slab`, `sd_congr_slab`, `Q_congr_slab`, `pd_congr_slab` — identities
  holding on the closed slab `[0, T] × ℝ^d` can be differentiated: in every spatial direction,
  and in time when `T > 0` (one-sided derivatives at the boundary slices).
* `derivBound_mul`, `derivBound_sum`, … — `L^∞_t W^{r,∞}_x` bounds (`SlabWaveHk.DerivBound`) of
  products and sums (Leibniz); `derivBound_of_Q` — the Sobolev embedding gives
  `W^{r,∞}` bounds from `L^∞_t H^{r+m}` bounds.
* `pd_inv_eq`, **`derivBound_inv`** — for a matrix field `G` with a smooth inverse field `H` on the
  slab, `∂H = -H (∂G) H` and `W^{r,∞}` bounds of `G` together with `|H| ≤ Λ` give `W^{r,∞}` bounds of
  `H` with constants depending only on `(n, r, A, Λ)` (the uniform inverse-metric bound).
* `cutInv`, `cutInv_eq` — a smooth function equal to `x⁻¹` for `x ≤ -a` (`a > 0`).
* `evalF`, **`evalF_lip`** — fields obtained by evaluating a multivariate polynomial on smooth
  periodic fields are smooth, periodic, bounded in `H^k` and Lipschitz in `H^k` (for `k ≥ 2m - 1`,
  `m > d/2`), with constants depending only on the polynomial and the `H^k` bound of the inputs.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SlabSobAlg

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Differentiating identities that hold on the closed slab -/

theorem line_zero_coord (x : ST d) (s : ℝ) : (x + s • ev (0 : Fin (d + 1))) 0 = x 0 + s := by
  simp [Pi.single_apply]

/-- If `φ` is constant on the closed slab `[0, T] × ℝ^d`, its line derivative at a slab point
vanishes in every spatial direction, and in the time direction when `T > 0`. -/
theorem hasDeriv_line_eq_zero_of_slab {T : ℝ} {φ : ST d → ℝ} {c : ℝ}
    (hconst : ∀ y : ST d, y 0 ∈ Icc 0 T → φ y = c) {x : ST d} (hx : x 0 ∈ Icc 0 T)
    (μ : Fin (d + 1)) (hμ : μ ≠ 0 ∨ 0 < T) {D : ℝ}
    (hD : HasDerivAt (fun s : ℝ => φ (x + s • ev μ)) D 0) : D = 0 := by
  by_cases h0 : μ = 0
  · subst h0
    have hT : 0 < T := hμ.resolve_left (fun h => h rfl)
    set S := Icc (-x 0) (T - x 0)
    have hS : (0 : ℝ) ∈ S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hu : UniqueDiffWithinAt ℝ S 0 := uniqueDiffOn_Icc (by linarith) 0 hS
    have h2 : HasDerivWithinAt (fun s : ℝ => φ (x + s • ev 0)) 0 S 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) S c).congr (fun s hs => ?_) ?_
      · exact hconst _ (by rw [line_zero_coord]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      · exact hconst _ (by simpa using hx)
    exact hu.eq_deriv S hD.hasDerivWithinAt h2
  · have hc : (fun s : ℝ => φ (x + s • ev μ)) = fun _ => c := funext fun s => hconst _ (by
      simpa [Pi.single_apply, h0] using hx)
    rw [hc] at hD
    exact hD.unique (hasDerivAt_const 0 c)

/-- Line derivatives of a smooth function at a point equal its partial derivatives. -/
theorem hasDerivAt_line_pd {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (x : ST d) (μ : Fin (d + 1)) :
    HasDerivAt (fun s : ℝ => f (x + s • ev μ)) (pd f μ x) 0 := hasDerivAt_line0 hf x μ

/-- Two smooth functions agreeing on the slab have equal partial derivatives on the slab, in every
spatial direction and (when `T > 0`) in time. -/
theorem pd_congr_slab {T : ℝ} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : ∀ x : ST d, x 0 ∈ Icc 0 T → f x = g x) (μ : Fin (d + 1)) (hμ : μ ≠ 0 ∨ 0 < T) :
    ∀ x : ST d, x 0 ∈ Icc 0 T → pd f μ x = pd g μ x := by
  intro x hx
  have h1 := (hasDerivAt_line_pd hf x μ).sub (hasDerivAt_line_pd hg x μ)
  have := hasDeriv_line_eq_zero_of_slab (φ := fun y => f y - g y) (c := 0)
    (fun y hy => by rw [h y hy, sub_self]) hx μ hμ h1
  linarith

/-- Spatial word derivatives of smooth functions agreeing on the slab agree on the slab. -/
theorem sd_congr_slab {T : ℝ} : ∀ (w : List (Fin d)) {f g : ST d → ℝ}, ContDiff ℝ ∞ f →
    ContDiff ℝ ∞ g → (∀ x : ST d, x 0 ∈ Icc 0 T → f x = g x) →
    ∀ x : ST d, x 0 ∈ Icc 0 T → sd w f x = sd w g x
  | [], _, _, _, _, h => h
  | i :: w, _, _, hf, hg, h => by
    simp only [sd_cons]
    exact sd_congr_slab w (contDiff_pd_top hf _) (contDiff_pd_top hg _)
      (pd_congr_slab hf hg h i.succ (Or.inl (Fin.succ_ne_zero i)))

theorem cons_zero_eq (t : ℝ) (y : Fin d → ℝ) : (Fin.cons t y : ST d) 0 = t := rfl

/-- `Q_k` at a time of the slab only sees the slab values. -/
theorem Q_congr_slab {T : ℝ} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : ∀ x : ST d, x 0 ∈ Icc 0 T → f x = g x) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Q k f t = Q k g t :=
  Q_congr fun w _ y => sd_congr_slab w hf hg h _ (by rw [cons_zero_eq]; exact ht)

theorem sd_sum (w : List (Fin d)) {κ : Type*} (s : Finset κ) {f : κ → ST d → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    sd w (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, sd w (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sd_const_mul w (contDiff_const (c := (0 : ℝ))) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [sd_add w (hf a) (ContDiff.sum fun i _ => hf i), ih]

/-! ### `W^{r,∞}` bounds on the slab -/

theorem list_abs_sum_le {α : Type*} (L : List α) (F : α → ℝ) :
    |(L.map F).sum| ≤ (L.map fun p => |F p|).sum := by
  rw [← Fin.sum_univ_fun_getElem L F, ← Fin.sum_univ_fun_getElem L (fun p => |F p|)]
  exact Finset.abs_sum_le_sum_abs _ _

theorem derivBound_nonneg {T : ℝ} (hT : 0 ≤ T) {r : ℕ} {f : ST d → ℝ} {A : ℝ}
    (h : DerivBound T r f A) : 0 ≤ A :=
  (abs_nonneg _).trans (h [] (Nat.zero_le _) 0 (by simp [hT]))

/-- **Leibniz for `W^{r,∞}` bounds**. -/
theorem derivBound_mul {T : ℝ} {r : ℕ} {f g : ST d → ℝ} {A B : ℝ} (hf : DerivBound T r f A)
    (hg : DerivBound T r g B) (sf : ContDiff ℝ ∞ f) (sg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) :
    DerivBound T r (fun x => f x * g x) (2 ^ r * (A * B)) := by
  intro w hw x hx
  show |sd w (fun x => f x * g x) x| ≤ _
  rw [sd_mul w sf sg x]
  refine (list_abs_sum_le _ _).trans ?_
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg [] (Nat.zero_le _) x hx)
  refine (list_sum_const_le _ (c := A * B) fun p hp => ?_).trans ?_
  · have hl := length_of_mem_splits hp
    rw [abs_mul]
    exact mul_le_mul (hf p.1 (by omega) x hx) (hg p.2 (by omega) x hx) (abs_nonneg _) hA
  · rw [length_splits]
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (mul_nonneg hA hB)

theorem derivBound_add {T : ℝ} {r : ℕ} {f g : ST d → ℝ} {A B : ℝ} (hf : DerivBound T r f A)
    (hg : DerivBound T r g B) (sf : ContDiff ℝ ∞ f) (sg : ContDiff ℝ ∞ g) :
    DerivBound T r (fun x => f x + g x) (A + B) := by
  intro w hw x hx
  show |sd w (fun x => f x + g x) x| ≤ _
  rw [sd_add w sf sg]
  exact (abs_add_le _ _).trans (add_le_add (hf w hw x hx) (hg w hw x hx))

theorem derivBound_const_mul {T : ℝ} {r : ℕ} {f : ST d → ℝ} {A : ℝ} (hf : DerivBound T r f A)
    (sf : ContDiff ℝ ∞ f) (c : ℝ) : DerivBound T r (fun x => c * f x) (|c| * A) := by
  intro w hw x hx
  show |sd w (fun x => c * f x) x| ≤ _
  rw [sd_const_mul w sf c, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf w hw x hx) (abs_nonneg _)

theorem derivBound_neg {T : ℝ} {r : ℕ} {f : ST d → ℝ} {A : ℝ} (hf : DerivBound T r f A)
    (sf : ContDiff ℝ ∞ f) : DerivBound T r (fun x => -f x) A := by
  have := derivBound_const_mul hf sf (-1)
  simpa using this

theorem derivBound_sum {T : ℝ} {r : ℕ} {κ : Type*} (s : Finset κ) {f : κ → ST d → ℝ}
    {A : κ → ℝ} (hf : ∀ i ∈ s, DerivBound T r (f i) (A i)) (sf : ∀ i, ContDiff ℝ ∞ (f i)) :
    DerivBound T r (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, A i) := by
  intro w hw x hx
  show |sd w (fun x => ∑ i ∈ s, f i x) x| ≤ _
  rw [sd_sum w s sf]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hf i hi w hw x hx)

theorem derivBound_congr {T : ℝ} {r : ℕ} {f g : ST d → ℝ} {A : ℝ} (hg : DerivBound T r g A)
    (sf : ContDiff ℝ ∞ f) (sg : ContDiff ℝ ∞ g) (h : ∀ x : ST d, x 0 ∈ Icc 0 T → f x = g x) :
    DerivBound T r f A := fun w hw x hx => by
  have := sd_congr_slab (T := T) w sf sg h x hx
  show |sd w f x| ≤ A
  rw [this]; exact hg w hw x hx

theorem cons_self_tail' (x : ST d) : (Fin.cons (x 0) (Fin.tail x) : ST d) = x :=
  Fin.cons_self_tail x

/-- **`W^{r,∞}` bounds from `L^∞_t H^{r+m}` bounds** (Sobolev embedding on slices). -/
theorem derivBound_of_Q {m r : ℕ} {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {T K : ℝ} {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f)
    (hK : ∀ t ∈ Icc 0 T, Q (r + m) f t ≤ K) : DerivBound T r f (Real.sqrt (CS * K)) := by
  intro w hw x hx
  show |sd w f x| ≤ _
  rw [← cons_self_tail' x]
  have h1 := hsup _ (contDiff_sd w hf) (isSPeriodic_sd w hp) (x 0) (Fin.tail x)
  have h2 : Q m (sd w f) (x 0) ≤ K := (Q_sd_le (by omega) f (x 0)).trans (hK _ hx)
  have h3 : sd w f (Fin.cons (x 0) (Fin.tail x)) ^ 2 ≤ CS * K :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hCS)
  exact Real.abs_le_sqrt h3

/-- A pointwise bound from a slice Sobolev bound. -/
theorem abs_le_of_Q {m : ℕ} {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {T K : ℝ} {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f)
    (hK : ∀ t ∈ Icc 0 T, Q m f t ≤ K) {x : ST d} (hx : x 0 ∈ Icc 0 T) :
    |f x| ≤ Real.sqrt (CS * K) := by
  have := derivBound_of_Q (r := 0) hCS hsup hf hp (by simpa using hK) [] (Nat.zero_le _) x hx
  exact this

/-- `DerivBound` gives a slice bound usable by `Q_le_of_bound` / `Q_mul_le_of_bound`. -/
theorem slice_bound_of_derivBound {T : ℝ} {r : ℕ} {f : ST d → ℝ} {A : ℝ}
    (h : DerivBound T r f A) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ w : List (Fin d), w.length ≤ r → ∀ y, |sd w f (Fin.cons t y)| ≤ A :=
  fun w hw y => h w hw _ (by rw [cons_zero_eq]; exact ht)

/-! ### Inverse matrix fields -/

/-- The derivative of a matrix inverse on the slab: if `G H = 1` on the slab, then
`∂_μ H = -H (∂_μ G) H` there (spatial `μ`, or `μ = 0` when `T > 0`). -/
theorem pd_inv_eq {n : ℕ} {T : ℝ} {G H : Fin n → Fin n → ST d → ℝ}
    (sG : ∀ a b, ContDiff ℝ ∞ (G a b)) (sH : ∀ a b, ContDiff ℝ ∞ (H a b))
    (hGH : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ a b,
      ∑ c, G a c x * H c b x = if a = b then 1 else 0)
    (μ : Fin (d + 1)) (hμ : μ ≠ 0 ∨ 0 < T) {x : ST d} (hx : x 0 ∈ Icc 0 T) (a b : Fin n) :
    pd (H a b) μ x = -∑ e, ∑ c, H a e x * pd (G e c) μ x * H c b x := by
  -- the derivative of the identity `G H = 1`
  have hder : ∀ a b, ∑ c, (pd (G a c) μ x * H c b x + G a c x * pd (H c b) μ x) = 0 := by
    intro a b
    have hd : HasDerivAt (fun s : ℝ => ∑ c, G a c (x + s • ev μ) * H c b (x + s • ev μ))
        (∑ c, (pd (G a c) μ x * H c b x + G a c x * pd (H c b) μ x)) 0 := by
      refine HasDerivAt.fun_sum fun c _ => ?_
      have := (hasDerivAt_line_pd (sG a c) x μ).fun_mul (hasDerivAt_line_pd (sH c b) x μ)
      simpa using this
    exact hasDeriv_line_eq_zero_of_slab (φ := fun y => ∑ c, G a c y * H c b y)
      (c := if a = b then 1 else 0) (fun y hy => hGH y hy a b) hx μ hμ hd
  -- matrix algebra
  set Gm : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => G a b x
  set Hm : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => H a b x
  set dG : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => pd (G a b) μ x
  set dH : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => pd (H a b) μ x
  have h1 : Gm * Hm = 1 := by
    ext a b
    simp only [Gm, Hm, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hGH x hx a b
  have h2 : Hm * Gm = 1 := mul_eq_one_comm.mp h1
  have h3 : dG * Hm + Gm * dH = 0 := by
    ext a b
    simp only [dG, Hm, Gm, dH, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.zero_apply, ← Finset.sum_add_distrib]
    exact hder a b
  have h4 : dH = -(Hm * dG * Hm) := by
    have : Hm * (dG * Hm + Gm * dH) = 0 := by rw [h3, Matrix.mul_zero]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact this
  have h5 := congrFun (congrFun h4 a) b
  simp only [dH, Hm, dG, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply] at h5
  rw [h5]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]

/-- The recursive constant of `derivBound_inv`. -/
def invC (n : ℕ) (A Λ : ℝ) : ℕ → ℝ
  | 0 => Λ
  | r + 1 => max Λ ((n : ℝ) ^ 2 * (2 ^ r * (2 ^ r * (invC n A Λ r * A) * invC n A Λ r)))

theorem invC_nonneg (n : ℕ) {A Λ : ℝ} (hΛ : 0 ≤ Λ) : ∀ r, 0 ≤ invC n A Λ r
  | 0 => hΛ
  | _ + 1 => le_max_of_le_left hΛ

/-- **`W^{r,∞}` bounds of the inverse matrix field**: if `G H = 1` on the slab, `|H| ≤ Λ` there and
all entries of `G` satisfy `DerivBound T r · A`, then all entries of `H` satisfy
`DerivBound T r · (invC n A Λ r)`. -/
theorem derivBound_inv {n : ℕ} {T : ℝ} {G H : Fin n → Fin n → ST d → ℝ}
    (sG : ∀ a b, ContDiff ℝ ∞ (G a b)) (sH : ∀ a b, ContDiff ℝ ∞ (H a b))
    (hGH : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ a b,
      ∑ c, G a c x * H c b x = if a = b then 1 else 0)
    {A Λ : ℝ} (hA : 0 ≤ A) (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x : ST d, x 0 ∈ Icc 0 T → ∀ a b, |H a b x| ≤ Λ) :
    ∀ r : ℕ, (∀ a b, DerivBound T r (G a b) A) → ∀ a b, DerivBound T r (H a b) (invC n A Λ r)
  | 0, _, a, b => fun w hw x hx => by
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
    subst this
    exact hΛ x hx a b
  | r + 1, hG, a, b => by
    have ih := derivBound_inv sG sH hGH hA hΛ0 hΛ r fun a b => (hG a b).of_succ
    have hCr := invC_nonneg n (A := A) hΛ0 r
    intro w hw x hx
    cases w with
    | nil => exact (hΛ x hx a b).trans (le_max_left _ _)
    | cons i v =>
      have hv : v.length ≤ r := by simp only [List.length_cons] at hw; omega
      show |sd v (pd (H a b) i.succ) x| ≤ _
      -- the derivative identity on the slab
      set R : ST d → ℝ := fun y => -∑ e, ∑ c, H a e y * pd (G e c) i.succ y * H c b y
      have sR : ContDiff ℝ ∞ R := by
        refine (ContDiff.sum fun e _ => ContDiff.sum fun c _ => ?_).neg
        exact ((sH a e).mul (contDiff_pd_top (sG e c) _)).mul (sH c b)
      have hRe : ∀ y : ST d, y 0 ∈ Icc 0 T → pd (H a b) i.succ y = R y := fun y hy =>
        pd_inv_eq sG sH hGH i.succ (Or.inl (Fin.succ_ne_zero i)) hy a b
      have hbR : DerivBound T r R ((n : ℝ) ^ 2 * (2 ^ r * (2 ^ r * (invC n A Λ r * A) *
          invC n A Λ r))) := by
        have hterm : ∀ e c, DerivBound T r (fun y => H a e y * pd (G e c) i.succ y * H c b y)
            (2 ^ r * (2 ^ r * (invC n A Λ r * A) * invC n A Λ r)) := fun e c =>
          derivBound_mul (derivBound_mul (ih a e) ((hG e c).pd i) (sH a e)
            (contDiff_pd_top (sG e c) _) hCr) (ih c b) ((sH a e).mul (contDiff_pd_top (sG e c) _))
            (sH c b) (by positivity)
        have hs := derivBound_neg (derivBound_sum (T := T) (r := r) Finset.univ
          (f := fun e y => ∑ c, H a e y * pd (G e c) i.succ y * H c b y)
          (fun e _ => derivBound_sum Finset.univ (fun c _ => hterm e c)
            (fun c => ((sH a e).mul (contDiff_pd_top (sG e c) _)).mul (sH c b)))
          (fun e => ContDiff.sum fun c _ => ((sH a e).mul (contDiff_pd_top (sG e c) _)).mul
            (sH c b))) (ContDiff.sum fun e _ => ContDiff.sum fun c _ =>
              ((sH a e).mul (contDiff_pd_top (sG e c) _)).mul (sH c b))
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        convert hs using 1
        ring
      have := derivBound_congr hbR (contDiff_pd_top (sH a b) _) sR hRe v hv x hx
      exact this.trans (le_max_right _ _)

/-! ### A smooth cut-off inverse -/

/-- The smooth denominator `D_a(x) = x χ(x) - (a/2)(1 - χ(x))`, with `χ = 1` on `x ≤ -a` and
`χ = 0` on `x ≥ -a/2`. -/
def cutDen (a x : ℝ) : ℝ :=
  x * Real.smoothTransition ((-x - a / 2) / (a / 2)) -
    a / 2 * (1 - Real.smoothTransition ((-x - a / 2) / (a / 2)))

/-- A smooth function equal to `x⁻¹` for `x ≤ -a`. -/
def cutInv (a x : ℝ) : ℝ := (cutDen a x)⁻¹

theorem cutDen_le {a : ℝ} (ha : 0 < a) (x : ℝ) : cutDen a x ≤ -(a / 2) := by
  unfold cutDen
  set χ := Real.smoothTransition ((-x - a / 2) / (a / 2))
  have h0 : 0 ≤ χ := Real.smoothTransition.nonneg _
  have h1 : χ ≤ 1 := Real.smoothTransition.le_one _
  by_cases hx : x ≤ -(a / 2)
  · nlinarith
  · have : (-x - a / 2) / (a / 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have hχ : χ = 0 := Real.smoothTransition.zero_of_nonpos this
    rw [hχ]; linarith

theorem cutDen_eq {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≤ -a) : cutDen a x = x := by
  unfold cutDen
  have : 1 ≤ (-x - a / 2) / (a / 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  rw [Real.smoothTransition.one_of_one_le this]; ring

theorem cutInv_eq {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≤ -a) : cutInv a x = x⁻¹ := by
  unfold cutInv; rw [cutDen_eq ha hx]

theorem contDiff_cutInv {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (cutInv a) := by
  have hD : ContDiff ℝ ∞ (cutDen a) := by
    unfold cutDen
    have hs : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition ((-x - a / 2) / (a / 2)) :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.neg.sub contDiff_const).div_const _)
    exact (contDiff_id.mul hs).sub (contDiff_const.mul (contDiff_const.sub hs))
  exact hD.inv fun x => by have := cutDen_le ha x; linarith

/-! ### Polynomial expressions in smooth periodic fields -/

/-- The field obtained by evaluating a polynomial on a family of fields. -/
def evalF {σ : Type*} (v : σ → ST d → ℝ) (P : MvPolynomial σ ℝ) (x : ST d) : ℝ :=
  MvPolynomial.eval (fun i => v i x) P

theorem evalF_add {σ : Type*} (v : σ → ST d → ℝ) (p q : MvPolynomial σ ℝ) :
    evalF v (p + q) = fun x => evalF v p x + evalF v q x := by
  funext x; simp [evalF]

theorem evalF_mul_X {σ : Type*} (v : σ → ST d → ℝ) (p : MvPolynomial σ ℝ) (i : σ) :
    evalF v (p * MvPolynomial.X i) = fun x => evalF v p x * v i x := by
  funext x; simp [evalF]

theorem evalF_C {σ : Type*} (v : σ → ST d → ℝ) (a : ℝ) :
    evalF v (MvPolynomial.C a) = fun _ => a := by
  funext x; simp [evalF]

theorem contDiff_evalF {σ : Type*} {v : σ → ST d → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (P : MvPolynomial σ ℝ) : ContDiff ℝ ∞ (evalF v P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [evalF_C]; exact contDiff_const
  | add p q hp hq => rw [evalF_add]; exact hp.add hq
  | mul_X p i hp => rw [evalF_mul_X]; exact hp.mul (hv i)

theorem isSPeriodic_evalF {σ : Type*} {v : σ → ST d → ℝ} (hv : ∀ i, IsSPeriodic (v i))
    (P : MvPolynomial σ ℝ) : IsSPeriodic (evalF v P) := fun k x => by
  unfold evalF
  have e : (fun i => v i (x + sshift k)) = fun i => v i x := funext fun i => hv i k x
  rw [e]

/-- **Polynomial expressions are bounded and Lipschitz in `H^k`** (`k ≥ 2m - 1`, `m > d/2`): for
every polynomial `P` and every bound `B` there are `B', L` such that, for all smooth periodic
families `v, v'` with `Q_k(vᵢ), Q_k(v'ᵢ) ≤ B` and `Q_k(vᵢ - v'ᵢ) ≤ D` at time `t`,
`Q_k(P(v)) ≤ B'` and `Q_k(P(v) - P(v')) ≤ L D`. -/
theorem evalF_lip {σ : Type*} {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    (P : MvPolynomial σ ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ B' L : ℝ, 0 ≤ B' ∧ 0 ≤ L ∧ ∀ (v v' : σ → ST d → ℝ) (t D : ℝ),
      (∀ i, ContDiff ℝ ∞ (v i)) → (∀ i, ContDiff ℝ ∞ (v' i)) → (∀ i, IsSPeriodic (v i)) →
      (∀ i, IsSPeriodic (v' i)) → (∀ i, Q k (v i) t ≤ B) → (∀ i, Q k (v' i) t ≤ B) → 0 ≤ D →
      (∀ i, Q k (fun x => v i x - v' i x) t ≤ D) →
      Q k (evalF v P) t ≤ B' ∧ Q k (fun x => evalF v P x - evalF v' P x) t ≤ L * D := by
  set Ca := algC d k CS
  have hCa : 0 ≤ Ca := algC_nonneg k hCS
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a ^ 2, 0, sq_nonneg _, le_rfl, fun v v' t D _ _ _ _ _ _ hD _ => ⟨?_, ?_⟩⟩
    · rw [evalF_C, Q_const]
    · rw [evalF_C, evalF_C]
      simp only [sub_self, Q_const]
      simp
  | add p q hp hq =>
    obtain ⟨Bp, Lp, hBp, hLp, hp⟩ := hp
    obtain ⟨Bq, Lq, hBq, hLq, hq⟩ := hq
    refine ⟨2 * Bp + 2 * Bq, 2 * Lp + 2 * Lq, by positivity, by positivity,
      fun v v' t D sv sv' pv pv' bv bv' hD hdv => ?_⟩
    obtain ⟨h1, h2⟩ := hp v v' t D sv sv' pv pv' bv bv' hD hdv
    obtain ⟨h3, h4⟩ := hq v v' t D sv sv' pv pv' bv bv' hD hdv
    have cp := contDiff_evalF sv p
    have cq := contDiff_evalF sv q
    have cp' := contDiff_evalF sv' p
    have cq' := contDiff_evalF sv' q
    refine ⟨?_, ?_⟩
    · rw [evalF_add]
      exact (Q_add_le k cp cq t).trans (by linarith)
    · rw [evalF_add, evalF_add]
      have e : (fun x => evalF v p x + evalF v q x - (evalF v' p x + evalF v' q x)) =
          fun x => (evalF v p x - evalF v' p x) + (evalF v q x - evalF v' q x) := by
        funext x; ring
      rw [e]
      refine (Q_add_le k (cp.sub cp') (cq.sub cq') t).trans ?_
      nlinarith
  | mul_X p i hp =>
    obtain ⟨Bp, Lp, hBp, hLp, hp⟩ := hp
    refine ⟨Ca * Bp * B, 2 * Ca * (Lp * B + Bp), by positivity, by positivity,
      fun v v' t D sv sv' pv pv' bv bv' hD hdv => ?_⟩
    obtain ⟨h1, h2⟩ := hp v v' t D sv sv' pv pv' bv bv' hD hdv
    obtain ⟨h1', _⟩ := hp v' v t D sv' sv pv' pv bv' bv hD (fun j => by
      rw [Q_sub_comm k (sv' j) (sv j)]; exact hdv j)
    have cp := contDiff_evalF sv p
    have cp' := contDiff_evalF sv' p
    have pp := isSPeriodic_evalF pv p
    have pp' := isSPeriodic_evalF pv' p
    refine ⟨?_, ?_⟩
    · rw [evalF_mul_X]
      refine (Q_mul_le hk hCS hsup cp (sv i) pp (pv i) t).trans ?_
      have := Q_nonneg k (evalF v p) t
      have := Q_nonneg k (v i) t
      calc Ca * Q k (evalF v p) t * Q k (v i) t ≤ Ca * Bp * B := by gcongr; exact bv i
        _ = _ := rfl
    · rw [evalF_mul_X, evalF_mul_X]
      have e : (fun x => evalF v p x * v i x - evalF v' p x * v' i x) =
          fun x => (evalF v p x - evalF v' p x) * v i x + evalF v' p x * (v i x - v' i x) := by
        funext x; ring
      rw [e]
      have hdp := (cp.sub cp')
      refine (Q_add_le k (hdp.mul (sv i)) (cp'.mul ((sv i).sub (sv' i))) t).trans ?_
      have m1 := Q_mul_le hk hCS hsup hdp (sv i) (fun k' x => by
        simp only [pp k' x, pp' k' x]) (pv i) t
      have m2 := Q_mul_le hk hCS hsup cp' ((sv i).sub (sv' i)) pp' (fun k' x => by
        simp only [pv i k' x, pv' i k' x]) t
      have q1 := Q_nonneg k (fun x => evalF v p x - evalF v' p x) t
      have q2 := Q_nonneg k (v i) t
      have q3 := Q_nonneg k (evalF v' p) t
      have q4 := Q_nonneg k (fun x => v i x - v' i x) t
      have b1 : Ca * Q k (fun x => evalF v p x - evalF v' p x) t * Q k (v i) t ≤
          Ca * (Lp * D) * B := by gcongr; exact bv i
      have b2 : Ca * Q k (evalF v' p) t * Q k (fun x => v i x - v' i x) t ≤ Ca * Bp * D := by
        gcongr; exact hdv i
      nlinarith

end SlabSobAlg

end RenewalGeometry
