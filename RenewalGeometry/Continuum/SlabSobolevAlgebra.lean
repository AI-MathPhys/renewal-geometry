/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SlabWaveEnergyHk
import RenewalGeometry.Analysis.SobolevBoxCrEmbedding

/-!
# Classical `H^k` calculus on the slices of `[0, T] × 𝕋^d`: Leibniz, Sobolev, products

Generic infrastructure (no renewal notions) for the quasilinear difference estimate of
`thm:hyperbolic` (common-slab metric stability) of the Einstein–Standard-Model action-closure
manuscript.  Fields are smooth functions on `ℝ^{1+d}` (`SlabWaveHk.ST d`) that are `ℤ^d`-periodic
in space (`SymHypEnergy.IsSPeriodic`); spatial integrals are over the unit cube `[0,1]^d`.

* `sd w f` — the iterated spatial derivative along a word `w : List (Fin d)`;
  `wordsLE d k` — the finite set of words of length `≤ k` (`mem_wordsLE`).
* `Q k f t = Σ_{|w| ≤ k} ∫_{[0,1]^d} |∂^w f(t, y)|² dy` — the squared classical `H^k` norm of the
  slice at time `t`.
* `sd_mul` — the **Leibniz rule** `∂^w(fg) = Σ_{(a,b) ∈ splits w} ∂^a f ∂^b g`
  (`2^{|w|}` terms, `|a| + |b| = |w|`).
* **`exists_sup_sq_le`** — the **Sobolev embedding on slices**: for `m > d/2`,
  `f(t, y)² ≤ C_S Q_m(f)(t)` (from `SobolevBoxCr.exists_norm_iteratedFDeriv_le_periodic`).
* **`Q_mul_le_of`** — the general product estimate `Q_k(fg) ≤ C Q_{k₁}(f) Q_{k₂}(g)` whenever
  every split `a + b ≤ k` has `a + m ≤ k₁, b ≤ k₂` or `a ≤ k₁, b + m ≤ k₂`; instances
  **`Q_mul_le`** (`H^k` is an algebra for `k ≥ 2m - 1`, i.e. `k ≥ 3` on `𝕋³`) and
  **`Q_mul_le_succ`** (`H^{k+1} · H^k ⊂ H^k` for `k ≥ 2m - 2`, i.e. `k ≥ 2` on `𝕋³`).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.SlabSobAlg

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Spatial words -/

/-- The iterated spatial derivative along a word (innermost letter first). -/
def sd (w : List (Fin d)) (f : ST d → ℝ) : ST d → ℝ := dW (w.map Fin.succ) f

@[simp] theorem sd_nil (f : ST d → ℝ) : sd [] f = f := rfl

theorem sd_cons (i : Fin d) (w : List (Fin d)) (f : ST d → ℝ) :
    sd (i :: w) f = sd w (pd f i.succ) := rfl

theorem dW_append : ∀ (a b : List (Fin (d + 1))) (f : ST d → ℝ), dW (a ++ b) f = dW b (dW a f)
  | [], _, _ => rfl
  | μ :: a, b, f => dW_append a b (pd f μ)

theorem sd_append (a b : List (Fin d)) (f : ST d → ℝ) : sd (a ++ b) f = sd b (sd a f) := by
  unfold sd; rw [List.map_append, dW_append]

theorem sd_append_single (a : List (Fin d)) (i : Fin d) (f : ST d → ℝ) :
    sd (a ++ [i]) f = pd (sd a f) i.succ := by
  rw [sd_append]; rfl

theorem contDiff_dW : ∀ (w : List (Fin (d + 1))) {f : ST d → ℝ}, ContDiff ℝ ∞ f →
    ContDiff ℝ ∞ (dW w f)
  | [], _, hf => hf
  | μ :: w, _, hf => contDiff_dW w (contDiff_pd_top hf μ)

theorem contDiff_sd (w : List (Fin d)) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sd w f) := contDiff_dW _ hf

theorem isSPeriodic_dW : ∀ (w : List (Fin (d + 1))) {f : ST d → ℝ}, IsSPeriodic f →
    IsSPeriodic (dW w f)
  | [], _, hf => hf
  | μ :: w, _, hf => isSPeriodic_dW w (isSPeriodic_pd hf μ)

theorem isSPeriodic_sd (w : List (Fin d)) {f : ST d → ℝ} (hf : IsSPeriodic f) :
    IsSPeriodic (sd w f) := isSPeriodic_dW _ hf

theorem sd_lincomb (w : List (Fin d)) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    sd w (fun x => a * f x + b * g x) = fun x => a * sd w f x + b * sd w g x :=
  dW_lincomb _ hf hg a b

theorem sd_add (w : List (Fin d)) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : sd w (fun x => f x + g x) = fun x => sd w f x + sd w g x := by
  have := sd_lincomb w hf hg 1 1
  simp only [one_mul] at this
  exact this

theorem sd_sub (w : List (Fin d)) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : sd w (fun x => f x - g x) = fun x => sd w f x - sd w g x := by
  have := sd_lincomb w hf hg 1 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

theorem sd_const_mul (w : List (Fin d)) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    sd w (fun x => a * f x) = fun x => a * sd w f x := by
  have := sd_lincomb w hf (contDiff_const (c := (0 : ℝ))) a 0
  simp only [zero_mul, add_zero] at this
  exact this

theorem sd_const_nonempty : ∀ (w : List (Fin d)), w ≠ [] → ∀ c : ℝ,
    sd w (fun _ : ST d => c) = fun _ => 0
  | [], h, _ => absurd rfl h
  | i :: w, _, c => by
    rw [sd_cons, pd_const]
    exact dW_zero _

/-- The finite set of words of length `≤ k`. -/
def wordsLE (d : ℕ) : ℕ → Finset (List (Fin d))
  | 0 => {[]}
  | k + 1 => insert [] ((Finset.univ ×ˢ wordsLE d k).image fun p => p.1 :: p.2)

theorem mem_wordsLE : ∀ {k : ℕ} {w : List (Fin d)}, w ∈ wordsLE d k ↔ w.length ≤ k
  | 0, w => by simp [wordsLE, List.length_eq_zero_iff]
  | k + 1, [] => by simp [wordsLE]
  | k + 1, i :: w => by
    simp only [wordsLE, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
      Finset.mem_product, Finset.mem_univ, true_and, Prod.exists, List.cons.injEq,
      List.length_cons]
    constructor
    · rintro ⟨a, b, hb, rfl, rfl⟩
      have := (mem_wordsLE (k := k)).mp hb
      omega
    · intro h
      exact ⟨i, w, (mem_wordsLE (k := k)).mpr (by omega), rfl, rfl⟩

theorem wordsLE_mono {k k' : ℕ} (h : k ≤ k') : wordsLE d k ⊆ wordsLE d k' := fun w hw =>
  mem_wordsLE.mpr ((mem_wordsLE.mp hw).trans h)

theorem nil_mem_wordsLE (k : ℕ) : ([] : List (Fin d)) ∈ wordsLE d k :=
  mem_wordsLE.mpr (Nat.zero_le _)

/-! ### The squared slice norms -/

/-- The squared classical `H^k` norm of the slice at time `t`:
`Q k f t = Σ_{|w| ≤ k} ∫_{[0,1]^d} |∂^w f(t, y)|² dy`. -/
def Q (k : ℕ) (f : ST d → ℝ) (t : ℝ) : ℝ :=
  ∑ w ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2

theorem term_nonneg (w : List (Fin d)) (f : ST d → ℝ) (t : ℝ) :
    0 ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2 :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem Q_nonneg (k : ℕ) (f : ST d → ℝ) (t : ℝ) : 0 ≤ Q k f t :=
  Finset.sum_nonneg fun w _ => term_nonneg w f t

theorem term_le_Q {k : ℕ} {w : List (Fin d)} (hw : w.length ≤ k) (f : ST d → ℝ) (t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2 ≤ Q k f t :=
  Finset.single_le_sum (f := fun w => ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2)
    (fun w _ => term_nonneg w f t) (mem_wordsLE.mpr hw)

theorem Q_mono {k k' : ℕ} (h : k ≤ k') (f : ST d → ℝ) (t : ℝ) : Q k f t ≤ Q k' f t :=
  Finset.sum_le_sum_of_subset_of_nonneg (wordsLE_mono h) fun w _ _ => term_nonneg w f t

theorem integral_sq_le_Q (k : ℕ) (f : ST d → ℝ) (t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) ^ 2 ≤ Q k f t :=
  term_le_Q (w := []) (Nat.zero_le _) f t

/-- `Q` depends only on the slice: if all derivatives along words of length `≤ k` agree on the
slice, the norms agree. -/
theorem Q_congr {k : ℕ} {f g : ST d → ℝ} {t : ℝ}
    (h : ∀ w : List (Fin d), w.length ≤ k → ∀ y, sd w f (Fin.cons t y) = sd w g (Fin.cons t y)) :
    Q k f t = Q k g t :=
  Finset.sum_congr rfl fun w hw => by
    simp only [h w (mem_wordsLE.mp hw)]

theorem integrableOn_sq {f : ST d → ℝ} (hf : Continuous f) (t : ℝ) :
    IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2) (Icc 0 1) :=
  integrableOn_slice (f := fun x => f x ^ 2) (hf.pow 2) t

theorem continuous_Q (k : ℕ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) : Continuous (Q k f) := by
  unfold Q
  refine continuous_finsetSum _ fun w _ => ?_
  exact continuous_sliceInt (f := fun x => sd w f x ^ 2) ((contDiff_sd w hf).continuous.pow 2)

/-- `Q_k(af + bg) ≤ 2a²Q_k(f) + 2b²Q_k(g)`. -/
theorem Q_lincomb_le (k : ℕ) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (t : ℝ) :
    Q k (fun x => a * f x + b * g x) t ≤ 2 * a ^ 2 * Q k f t + 2 * b ^ 2 * Q k g t := by
  unfold Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [sd_lincomb w hf hg a b]
  have cf := (contDiff_sd w hf).continuous
  have cg := (contDiff_sd w hg).continuous
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (integrableOn_sq cf t |>.const_mul _)
    (integrableOn_sq cg t |>.const_mul _)]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
  · exact integrableOn_slice (f := fun x => (a * sd w f x + b * sd w g x) ^ 2) (by fun_prop) t
  · exact ((integrableOn_sq cf t).const_mul _).add ((integrableOn_sq cg t).const_mul _)
  · nlinarith [sq_nonneg (a * sd w f (Fin.cons t y) - b * sd w g (Fin.cons t y))]

theorem Q_add_le (k : ℕ) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    Q k (fun x => f x + g x) t ≤ 2 * Q k f t + 2 * Q k g t := by
  have := Q_lincomb_le k hf hg 1 1 t
  simp only [one_mul, one_pow, mul_one] at this
  exact this

theorem Q_sub_le (k : ℕ) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    Q k (fun x => f x - g x) t ≤ 2 * Q k f t + 2 * Q k g t := by
  have := Q_lincomb_le k hf hg 1 (-1) t
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, one_pow, mul_one, neg_one_sq] at this
  exact this

theorem Q_const_mul (k : ℕ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (a t : ℝ) :
    Q k (fun x => a * f x) t = a ^ 2 * Q k f t := by
  unfold Q
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sd_const_mul w hf a, ← integral_const_mul]
  congr 1; funext y; ring

theorem Q_neg (k : ℕ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Q k (fun x => -f x) t = Q k f t := by
  have := Q_const_mul k hf (-1) t
  simp only [neg_one_mul, neg_one_sq, one_mul] at this
  exact this

theorem Q_sub_comm (k : ℕ) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) : Q k (fun x => f x - g x) t = Q k (fun x => g x - f x) t := by
  rw [← Q_neg k (hg.sub hf)]
  congr 1; funext x; ring

/-- `Q` of a constant: only the empty word contributes. -/
theorem Q_const (k : ℕ) (c t : ℝ) : Q k (fun _ : ST d => c) t = c ^ 2 := by
  unfold Q
  rw [Finset.sum_eq_single_of_mem [] (nil_mem_wordsLE k)]
  · simp [Measure.real, Real.volume_Icc_pi]
  · intro w _ hw
    rw [sd_const_nonempty w hw c]
    simp

/-- Pointwise `(Σ_{i ∈ s} a_i)² ≤ |s| Σ a_i²`, integrated: `Q_k(Σ fᵢ) ≤ |s| Σ Q_k(fᵢ)`. -/
theorem Q_sum_le (k : ℕ) {κ : Type*} (s : Finset κ) {f : κ → ST d → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (t : ℝ) :
    Q k (fun x => ∑ i ∈ s, f i x) t ≤ s.card * ∑ i ∈ s, Q k (f i) t := by
  classical
  have hsd : ∀ w : List (Fin d), sd w (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, sd w (f i) x := by
    intro w
    induction s using Finset.induction_on with
    | empty => simpa using (sd_const_mul w (contDiff_const (c := (0 : ℝ))) 0)
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [sd_add w (hf a) (ContDiff.sum fun i _ => hf i), ih]
  unfold Q
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [hsd w, ← integral_finsetSum _ fun i _ => integrableOn_sq (contDiff_sd w (hf i)).continuous t,
    ← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
  · exact integrableOn_slice (f := fun x => (∑ i ∈ s, sd w (f i) x) ^ 2)
      ((continuous_finsetSum _ fun i _ => (contDiff_sd w (hf i)).continuous).pow 2) t
  · exact (integrable_finsetSum _ fun i _ =>
      integrableOn_sq (contDiff_sd w (hf i)).continuous t).const_mul _
  · exact sq_sum_le_card_mul_sum_sq

/-- Translating derivatives: `Q_m(∂^a f) ≤ Q_k(f)` for `|a| + m ≤ k`. -/
theorem Q_sd_le {a : List (Fin d)} {m k : ℕ} (h : a.length + m ≤ k) (f : ST d → ℝ) (t : ℝ) :
    Q m (sd a f) t ≤ Q k f t := by
  unfold Q
  have hinj : Set.InjOn (fun v : List (Fin d) => a ++ v) (wordsLE d m : Set (List (Fin d))) :=
    fun v _ v' _ hv => List.append_cancel_left hv
  calc ∑ v ∈ wordsLE d m, ∫ y in Icc (0 : Fin d → ℝ) 1, sd v (sd a f) (Fin.cons t y) ^ 2 =
      ∑ u ∈ (wordsLE d m).image (fun v => a ++ v),
        ∫ y in Icc (0 : Fin d → ℝ) 1, sd u f (Fin.cons t y) ^ 2 := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun v _ => by rw [sd_append]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => term_nonneg w f t
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        rw [mem_wordsLE] at hv ⊢
        simp only [List.length_append]
        omega

theorem Q_pd_le {k : ℕ} (i : Fin d) (f : ST d → ℝ) (t : ℝ) :
    Q k (pd f i.succ) t ≤ Q (k + 1) f t := by
  have := Q_sd_le (a := [i]) (m := k) (k := k + 1) (by simp; omega) f t
  simpa [sd_cons] using this

/-! ### The Leibniz rule along words -/

/-- The `2^{|w|}` splittings of a word into two complementary subwords. -/
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | μ :: w => (splits w).map (fun p => (μ :: p.1, p.2)) ++
      (splits w).map (fun p => (p.1, μ :: p.2))

theorem length_splits {α : Type*} : ∀ w : List α, (splits w).length = 2 ^ w.length
  | [] => rfl
  | μ :: w => by
    simp only [splits, List.length_append, List.length_map, length_splits w, List.length_cons,
      pow_succ]
    ring

theorem length_of_mem_splits {α : Type*} : ∀ {w : List α} {p : List α × List α},
    p ∈ splits w → p.1.length + p.2.length = w.length
  | [], p, hp => by simp [splits] at hp; subst hp; rfl
  | μ :: w, p, hp => by
    simp only [splits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := length_of_mem_splits hq
      simp only [List.length_cons]; omega
    · have := length_of_mem_splits hq
      simp only [List.length_cons]; omega

/-- **The Leibniz rule** `∂^w(fg) = Σ_{(a,b) ∈ splits w} ∂^a f ∂^b g`. -/
theorem sd_mul : ∀ (w : List (Fin d)) {f g : ST d → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ x, sd w (fun x => f x * g x) x = ((splits w).map fun p => sd p.1 f x * sd p.2 g x).sum
  | [], f, g, _, _, x => by simp [splits]
  | i :: w, f, g, hf, hg, x => by
    have hpd : pd (fun x => f x * g x) i.succ =
        fun x => pd f i.succ x * g x + f x * pd g i.succ x :=
      funext fun x => SobolevOpen.pd_mul (hf.of_le (by norm_cast)) (hg.of_le (by norm_cast)) _ x
    have h1 : ContDiff ℝ ∞ (fun x => pd f i.succ x * g x) := (contDiff_pd_top hf _).mul hg
    have h2 : ContDiff ℝ ∞ (fun x => f x * pd g i.succ x) := hf.mul (contDiff_pd_top hg _)
    rw [sd_cons, hpd, sd_add w h1 h2]
    beta_reduce
    rw [sd_mul w (contDiff_pd_top hf _) hg x, sd_mul w hf (contDiff_pd_top hg _) x]
    simp only [splits, List.map_append, List.map_map, List.sum_append]
    rfl

/-- `(Σ_{p ∈ L} a_p)² ≤ |L| Σ_{p ∈ L} a_p²` for lists. -/
theorem list_sum_sq_le {α : Type*} (L : List α) (F : α → ℝ) :
    (L.map F).sum ^ 2 ≤ L.length * (L.map fun p => F p ^ 2).sum := by
  rw [← Fin.sum_univ_fun_getElem L F, ← Fin.sum_univ_fun_getElem L (fun p => F p ^ 2)]
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin L.length)))
    (f := fun i => F L[i.1])
  simpa using this

/-- Integral of a list sum of slice functions. -/
theorem integral_list_sum_slice {α : Type*} (L : List α) {F : α → ST d → ℝ}
    (hF : ∀ p, Continuous (F p)) (t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, (L.map fun p => F p (Fin.cons t y)).sum =
      (L.map fun p => ∫ y in Icc (0 : Fin d → ℝ) 1, F p (Fin.cons t y)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (integrableOn_slice (hF p) t), ih]
    have : ∀ y, (L.map fun p => F p (Fin.cons t y)).sum =
        ∑ i : Fin L.length, F L[i.1] (Fin.cons t y) := fun y =>
      (Fin.sum_univ_fun_getElem L (fun p => F p (Fin.cons t y))).symm
    simp_rw [this]
    exact integrable_finsetSum _ fun i _ => integrableOn_slice (hF _) t

theorem list_sum_le_of_le {α : Type*} (L : List α) {F G : α → ℝ} (h : ∀ p ∈ L, F p ≤ G p) :
    (L.map F).sum ≤ (L.map G).sum := List.sum_le_sum (by simpa using h)

theorem list_sum_const_le {α : Type*} (L : List α) {F : α → ℝ} {c : ℝ} (h : ∀ p ∈ L, F p ≤ c) :
    (L.map F).sum ≤ L.length * c := by
  have := list_sum_le_of_le L (G := fun _ => c) h
  simpa using this

/-! ### Sobolev embedding on slices -/

theorem isPeriodic_slice {f : ST d → ℝ} (hf : IsSPeriodic f) (t : ℝ) :
    SobolevBoxCr.IsPeriodic (fun y : Fin d → ℝ => f (Fin.cons t y)) := fun n y =>
  hf.slice t n y

theorem iterPd_slice {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) : ∀ {m : ℕ} (w : Fin m → Fin d)
    (y : Fin d → ℝ), SobolevBoxCr.iterPd (fun y : Fin d → ℝ => f (Fin.cons t y)) w y =
      sd (List.ofFn w).reverse f (Fin.cons t y)
  | 0, w, y => by simp [SobolevBoxCr.iterPd]
  | m + 1, w, y => by
    have ih : SobolevBoxCr.iterPd (fun y : Fin d → ℝ => f (Fin.cons t y)) (Fin.tail w) =
        fun y => sd (List.ofFn (Fin.tail w)).reverse f (Fin.cons t y) :=
      funext fun y => iterPd_slice hf t (Fin.tail w) y
    simp only [SobolevBoxCr.iterPd]
    rw [ih, pd_slice (w 0) ((contDiff_sd _ hf).differentiable (by simp) _)]
    rw [List.ofFn_succ, List.reverse_cons, sd_append_single]
    rfl

theorem unitCube_ae_eq_Icc :
    (SobolevOpen.unitCube : Set (Fin d → ℝ)) =ᵐ[volume] Icc (0 : Fin d → ℝ) 1 := by
  have h1 : (SobolevOpen.unitCube : Set (Fin d → ℝ)) = boxIoc 0 := by
    ext y; simp [SobolevOpen.unitCube, boxIoc]
  have := boxIoc_ae_eq (ι := Fin d) 0
  rw [h1]
  simpa using this

/-- **Sobolev embedding on slices**: for `m > d/2` there is `C_S` with
`f(t, y)² ≤ C_S Q_m(f)(t)` for every smooth spatially periodic `f`, every `t` and `y`. -/
theorem exists_sup_sq_le {m : ℕ} (hm : (d : ℝ) / 2 < m) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ)
      (y : Fin d → ℝ), f (Fin.cons t y) ^ 2 ≤ CS * Q m f t := by
  have hm' : (Fintype.card (Fin d) : ℝ) / 2 + (0 : ℕ) < m := by simpa using hm
  obtain ⟨C, hC0, hC⟩ := SobolevBoxCr.exists_norm_iteratedFDeriv_le_periodic (d := Fin d) ℝ hm'
  refine ⟨C ^ 2 * (1 + (d : ℝ) ^ m), by positivity, fun f hf hp t y => ?_⟩
  set g : (Fin d → ℝ) → ℝ := fun y => f (Fin.cons t y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_cons t)
  have hgp := isPeriodic_slice hp t
  have h1 := hC g hg hgp y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  set A := ∫ z in SobolevOpen.unitCube, ‖g z‖ ^ 2
  set B := ∫ z in SobolevOpen.unitCube, ‖iteratedFDeriv ℝ m g z‖ ^ 2
  have hcont : ∀ w : Fin m → Fin d, Continuous (SobolevBoxCr.iterPd g w) := fun w =>
    (SobolevBoxCr.contDiff_iterPd hg w).continuous
  have hA : A ≤ Q m f t := by
    have : A = ∫ z in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t z) ^ 2 := by
      simp only [A, Real.norm_eq_abs, sq_abs]
      exact setIntegral_congr_set unitCube_ae_eq_Icc
    rw [this]; exact integral_sq_le_Q m f t
  have hB : B ≤ (d : ℝ) ^ m * Q m f t := by
    have hpt : ∀ z, ‖iteratedFDeriv ℝ m g z‖ ^ 2 ≤
        (d : ℝ) ^ m * ∑ w : Fin m → Fin d, SobolevBoxCr.iterPd g w z ^ 2 := by
      intro z
      have h2 := SobolevBoxCr.norm_le_sum_single (d := Fin d) (iteratedFDeriv ℝ m g z)
      simp only [SobolevBoxCr.iteratedFDeriv_single hg, Real.norm_eq_abs] at h2
      have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Fin d)))
        (f := fun w => |SobolevBoxCr.iterPd g w z|)
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, sq_abs] at h3
      calc ‖iteratedFDeriv ℝ m g z‖ ^ 2 ≤ (∑ w : Fin m → Fin d, |SobolevBoxCr.iterPd g w z|) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ ≤ _ := by exact_mod_cast h3
    have hint : B ≤ ∫ z in Icc (0 : Fin d → ℝ) 1,
        (d : ℝ) ^ m * ∑ w : Fin m → Fin d, SobolevBoxCr.iterPd g w z ^ 2 := by
      rw [← setIntegral_congr_set unitCube_ae_eq_Icc]
      refine setIntegral_mono_on ?_ ?_ SobolevOpen.measurableSet_unitCube fun z _ => hpt z
      · exact SobolevBoxCr.integrableOn_unitCube
          ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2)
      · exact SobolevBoxCr.integrableOn_unitCube
          (continuous_const.mul (continuous_finsetSum _ fun w _ => (hcont w).pow 2))
    refine hint.trans ?_
    rw [integral_const_mul, integral_finsetSum (s := Finset.univ)
      (f := fun w z => SobolevBoxCr.iterPd g w z ^ 2) fun w _ =>
      (integrableOn_cube_of_continuousOn ((hcont w).pow 2).continuousOn)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : ∀ (w : Fin m → Fin d) (z : Fin d → ℝ), SobolevBoxCr.iterPd g w z =
        sd (List.ofFn w).reverse f (Fin.cons t z) := fun w z => iterPd_slice hf t w z
    simp_rw [e]
    have hinj : Set.InjOn (fun w : Fin m → Fin d => (List.ofFn w).reverse)
        (Finset.univ : Finset (Fin m → Fin d)) := fun w _ w' _ h =>
      List.ofFn_injective (List.reverse_injective h)
    unfold Q
    calc ∑ w : Fin m → Fin d, ∫ z in Icc (0 : Fin d → ℝ) 1,
          sd (List.ofFn w).reverse f (Fin.cons t z) ^ 2 =
        ∑ u ∈ (Finset.univ : Finset (Fin m → Fin d)).image (fun w => (List.ofFn w).reverse),
          ∫ z in Icc (0 : Fin d → ℝ) 1, sd u f (Fin.cons t z) ^ 2 := by
          rw [Finset.sum_image hinj]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => term_nonneg w f t
          intro u hu
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hu
          rw [mem_wordsLE]; simp
  have hQ := Q_nonneg m f t
  have hAB0 : 0 ≤ A + B := add_nonneg (setIntegral_nonneg SobolevOpen.measurableSet_unitCube
    fun _ _ => sq_nonneg _) (setIntegral_nonneg SobolevOpen.measurableSet_unitCube
    fun _ _ => sq_nonneg _)
  have h4 : g y ^ 2 ≤ C ^ 2 * (A + B) := by
    have h5 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hAB0] at h5
    exact h5
  calc f (Fin.cons t y) ^ 2 = g y ^ 2 := rfl
    _ ≤ C ^ 2 * (A + B) := h4
    _ ≤ C ^ 2 * (Q m f t + (d : ℝ) ^ m * Q m f t) := by gcongr
    _ = C ^ 2 * (1 + (d : ℝ) ^ m) * Q m f t := by ring

/-! ### Product estimates -/

/-- **The core of the product estimates**: if every split `(a, b)` of every word of length `≤ k`
has `∫ |∂^a f ∂^b g|² ≤ P` on the slice, then `Q_k(fg) ≤ |W_k| 4^k P`. -/
theorem Q_mul_le_core {k : ℕ} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) {P : ℝ} (hP : 0 ≤ P)
    (hsplit : ∀ w : List (Fin d), w.length ≤ k → ∀ p ∈ splits w, ∫ y in Icc (0 : Fin d → ℝ) 1,
      (sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y)) ^ 2 ≤ P) :
    Q k (fun x => f x * g x) t ≤ ((wordsLE d k).card * 4 ^ k) * P := by
  have hw : ∀ w ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1, sd w (fun x => f x * g x)
      (Fin.cons t y) ^ 2 ≤ 4 ^ k * P := by
    intro w hwk
    have hwk' := mem_wordsLE.mp hwk
    have hL := length_splits w
    have hc : ∀ p : List (Fin d) × List (Fin d), Continuous fun x =>
        (sd p.1 f x * sd p.2 g x) ^ 2 := fun p =>
      (((contDiff_sd p.1 hf).continuous).mul ((contDiff_sd p.2 hg).continuous)).pow 2
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, sd w (fun x => f x * g x) (Fin.cons t y) ^ 2
        ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, (2 : ℝ) ^ w.length *
            ((splits w).map fun p : List (Fin d) × List (Fin d) =>
              (sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y)) ^ 2).sum := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
          · exact integrableOn_sq (contDiff_sd w (hf.mul hg)).continuous t
          · refine Integrable.const_mul ?_ _
            have : ∀ y, ((splits w).map fun p : List (Fin d) × List (Fin d) =>
                (sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y)) ^ 2).sum =
                ∑ i : Fin (splits w).length, (sd (splits w)[i.1].1 f (Fin.cons t y) *
                  sd (splits w)[i.1].2 g (Fin.cons t y)) ^ 2 :=
              fun y => (Fin.sum_univ_fun_getElem _ (fun p : List (Fin d) × List (Fin d) =>
                (sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y)) ^ 2)).symm
            simp_rw [this]
            exact integrable_finsetSum _ fun i _ => integrableOn_slice (hc _) t
          · rw [sd_mul w hf hg]
            have := list_sum_sq_le (splits w) (fun p : List (Fin d) × List (Fin d) =>
              sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y))
            rw [hL] at this
            exact_mod_cast this
      _ = (2 : ℝ) ^ w.length * ((splits w).map fun p : List (Fin d) × List (Fin d) =>
            ∫ y in Icc (0 : Fin d → ℝ) 1, (sd p.1 f (Fin.cons t y) * sd p.2 g (Fin.cons t y)) ^ 2).sum := by
          rw [integral_const_mul, integral_list_sum_slice (splits w)
            (F := fun p x => (sd p.1 f x * sd p.2 g x) ^ 2) hc t]
      _ ≤ (2 : ℝ) ^ w.length * ((splits w).length * P) :=
          mul_le_mul_of_nonneg_left (list_sum_const_le _ (hsplit w hwk')) (by positivity)
      _ = (4 : ℝ) ^ w.length * P := by
          rw [hL]; push_cast
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
      _ ≤ 4 ^ k * P := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hwk') hP
  calc Q k (fun x => f x * g x) t ≤ ∑ _w ∈ wordsLE d k, 4 ^ k * P := Finset.sum_le_sum hw
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A split term with a pointwise bound on the first factor. -/
theorem split_int_le_left {a b : List (Fin d)} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {t S : ℝ} (hS : ∀ y, sd a f (Fin.cons t y) ^ 2 ≤ S) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, (sd a f (Fin.cons t y) * sd b g (Fin.cons t y)) ^ 2 ≤
      S * ∫ y in Icc (0 : Fin d → ℝ) 1, sd b g (Fin.cons t y) ^ 2 := by
  have hcf := (contDiff_sd a hf).continuous
  have hcg := (contDiff_sd b hg).continuous
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => ?_
  · exact integrableOn_slice (f := fun x => (sd a f x * sd b g x) ^ 2) ((hcf.mul hcg).pow 2) t
  · exact (integrableOn_sq hcg t).const_mul _
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hS y) (sq_nonneg _)

/-- A split term with a pointwise bound on the second factor. -/
theorem split_int_le_right {a b : List (Fin d)} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {t S : ℝ} (hS : ∀ y, sd b g (Fin.cons t y) ^ 2 ≤ S) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, (sd a f (Fin.cons t y) * sd b g (Fin.cons t y)) ^ 2 ≤
      S * ∫ y in Icc (0 : Fin d → ℝ) 1, sd a f (Fin.cons t y) ^ 2 := by
  have := split_int_le_left (a := b) (b := a) hg hf hS (t := t)
  simpa only [mul_comm (sd b g _)] using this

/-- **The general product estimate on slices.** If `C_S` is a Sobolev constant of order `m`
(`f(t,y)² ≤ C_S Q_m(f)(t)`) and every split `a + b ≤ k` satisfies `a + m ≤ k₁ ∧ b ≤ k₂` or
`a ≤ k₁ ∧ b + m ≤ k₂`, then `Q_k(fg) ≤ |W_k| 4^k C_S Q_{k₁}(f) Q_{k₂}(g)`. -/
theorem Q_mul_le_of {k k₁ k₂ m : ℕ} {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    (hsplit : ∀ a b : ℕ, a + b ≤ k → (a + m ≤ k₁ ∧ b ≤ k₂) ∨ (a ≤ k₁ ∧ b + m ≤ k₂))
    {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hpf : IsSPeriodic f)
    (hpg : IsSPeriodic g) (t : ℝ) :
    Q k (fun x => f x * g x) t ≤
      ((wordsLE d k).card * 4 ^ k * CS) * Q k₁ f t * Q k₂ g t := by
  have hQf := Q_nonneg k₁ f t
  have hQg := Q_nonneg k₂ g t
  have h := Q_mul_le_core (k := k) hf hg t (P := CS * Q k₁ f t * Q k₂ g t) (by positivity)
    fun w hw p hp => by
      have hl := length_of_mem_splits hp
      rcases hsplit p.1.length p.2.length (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine (split_int_le_left hf hg (S := CS * Q k₁ f t) fun y =>
          (hsup _ (contDiff_sd p.1 hf) (isSPeriodic_sd p.1 hpf) t y).trans
            (mul_le_mul_of_nonneg_left (Q_sd_le h1 f t) hCS)).trans ?_
        exact mul_le_mul_of_nonneg_left (term_le_Q h2 g t) (by positivity)
      · refine (split_int_le_right hf hg (S := CS * Q k₂ g t) fun y =>
          (hsup _ (contDiff_sd p.2 hg) (isSPeriodic_sd p.2 hpg) t y).trans
            (mul_le_mul_of_nonneg_left (Q_sd_le h2 g t) hCS)).trans ?_
        have := mul_le_mul_of_nonneg_left (term_le_Q h1 f t) (mul_nonneg hCS hQg)
        calc _ ≤ CS * Q k₂ g t * Q k₁ f t := this
          _ = CS * Q k₁ f t * Q k₂ g t := by ring
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The algebra constant `|W_k| 4^k C_S`. -/
def algC (d k : ℕ) (CS : ℝ) : ℝ := (wordsLE d k).card * 4 ^ k * CS

theorem algC_nonneg (k : ℕ) {CS : ℝ} (hCS : 0 ≤ CS) : 0 ≤ algC d k CS := by
  unfold algC; positivity

/-- **`H^k(𝕋^d)` is an algebra for `k ≥ 2m - 1`** (`m > d/2`; on `𝕋³`: `m = 2`, `k ≥ 3`):
`Q_k(fg) ≤ C Q_k(f) Q_k(g)`. -/
theorem Q_mul_le {k m : ℕ} (hk : 2 * m ≤ k + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hpf : IsSPeriodic f)
    (hpg : IsSPeriodic g) (t : ℝ) :
    Q k (fun x => f x * g x) t ≤ algC d k CS * Q k f t * Q k g t :=
  Q_mul_le_of hCS hsup (fun a b hab => by
    by_cases h : a + m ≤ k
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩) hf hg hpf hpg t

/-- **`H^{k+1} · H^k ⊂ H^k` for `k ≥ 2m - 2`** (on `𝕋³`: `k ≥ 2`):
`Q_k(fg) ≤ C Q_{k+1}(f) Q_k(g)`. -/
theorem Q_mul_le_succ {k m : ℕ} (hk : 2 * m ≤ k + 2) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hpf : IsSPeriodic f)
    (hpg : IsSPeriodic g) (t : ℝ) :
    Q k (fun x => f x * g x) t ≤ algC d k CS * Q (k + 1) f t * Q k g t :=
  Q_mul_le_of hCS hsup (fun a b hab => by
    by_cases h : a + m ≤ k + 1
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩) hf hg hpf hpg t

/-- **`W^{k,∞} · H^k ⊂ H^k`**: if all derivatives of order `≤ k` of `f` are bounded by `A` on the
slice, `Q_k(fg) ≤ |W_k| 4^k A² Q_k(g)` (no Sobolev embedding needed). -/
theorem Q_mul_le_of_bound {k : ℕ} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {t A : ℝ} (hA : ∀ w : List (Fin d), w.length ≤ k → ∀ y, |sd w f (Fin.cons t y)| ≤ A) :
    Q k (fun x => f x * g x) t ≤ ((wordsLE d k).card * 4 ^ k) * (A ^ 2 * Q k g t) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA [] (Nat.zero_le _) 0)
  refine Q_mul_le_core hf hg t (by have := Q_nonneg k g t; positivity) fun w hw p hp => ?_
  have hl := length_of_mem_splits hp
  refine (split_int_le_left hf hg (S := A ^ 2) fun y => ?_).trans ?_
  · have := pow_le_pow_left₀ (abs_nonneg _) (hA p.1 (by omega) y) 2
    rwa [sq_abs] at this
  · exact mul_le_mul_of_nonneg_left (term_le_Q (by omega) g t) (sq_nonneg _)

/-- A pointwise bound on all derivatives of order `≤ k` gives `Q_k(f) ≤ |W_k| A²`. -/
theorem Q_le_of_bound {k : ℕ} {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) {t A : ℝ}
    (hA : ∀ w : List (Fin d), w.length ≤ k → ∀ y, |sd w f (Fin.cons t y)| ≤ A) :
    Q k f t ≤ (wordsLE d k).card * A ^ 2 := by
  unfold Q
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA [] (Nat.zero_le _) 0)
  calc ∑ w ∈ wordsLE d k, ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2 ≤
      ∑ _w ∈ wordsLE d k, A ^ 2 := Finset.sum_le_sum fun w hw => by
        have hw' := mem_wordsLE.mp hw
        calc ∫ y in Icc (0 : Fin d → ℝ) 1, sd w f (Fin.cons t y) ^ 2 ≤
            ∫ _y in Icc (0 : Fin d → ℝ) 1, A ^ 2 := by
              refine setIntegral_mono_on (integrableOn_sq (contDiff_sd w hf).continuous t)
                (integrableOn_const (by simp [Real.volume_Icc_pi]) (by simp)) measurableSet_Icc
                fun y _ => ?_
              · have := hA w hw' y
                nlinarith [abs_nonneg (sd w f (Fin.cons t y)), sq_abs (sd w f (Fin.cons t y))]
          _ = A ^ 2 := by simp [Measure.real, Real.volume_Icc_pi]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end SlabSobAlg

end RenewalGeometry
