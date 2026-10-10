/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.WeakNormalizedReaderHierarchy

/-!
# Mixed space–time difference norms on a forward time window

Generic discrete calculus (no gauge notions) used to assemble `cor:gauge-robust-reader` of the
Einstein–SM action-closure manuscript (`app:gauge-reader`).  A *time family* is a function
`f : ℕ → Y → 𝔸` (time steps `j : ℕ`, spatial sites in an additive group `Y` with steps `e_k`,
values in a normed `ℝ`-algebra).  Forward time differences `tD f j = h⁻¹(f(j+1) - f(j))` only look
forward, so mixed space–time difference bounds can be stated on a **forward window** `0 ≤ j ≤ N`
without any periodicity in time:

* `TB N k f B` — every mixed difference word with `r` time letters and `≤ k - r` spatial letters
  is bounded by `B` at all times `j` with `j + r ≤ N` (recursive definition: spatial `C_h^k` bounds
  `Bnd` on every slice `j ≤ N`, and `TB (N-1) (k-1)` for `tD f`).
* The calculus: `TB.mono`, `TB.down`, `TB.window`, `TB.congr`, `TB.add`, `TB.sub`, `TB.neg`,
  `TB.smul`, `TB.tsh` (time shift), `TB.sdiff` / `TB.sshift` (spatial differences and shifts),
  **`TB_mul`** (`TB` is a Banach algebra with the constant `2^k`, as `Bnd_mul`), `TB_const`,
  `TB.star` (quaternions), **`TB_tsum`** (absolutely convergent series of time families).
* `TB_scalar` — the time family of a sampled real function `t ↦ φ(jh)`: if every iterated forward
  difference quotient of `φ` is bounded by `M`, the family is `TB` by `M`;
  **`abs_iterDQ_le`**: iterated forward difference quotients of a `C^r` function are bounded by the
  sup of its `r`-th derivative (mean value theorem, iterated).

The lift of a time family that vanishes near both ends of `[0, n)` to the periodic grid
`ZMod n × Y` is in `GaugeRobustReaderClosed`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.TimeSlab

open WeakNormReader

set_option linter.unusedSectionVars false

section Calculus

variable {Y κ : Type*} [AddCommGroup Y] (e : κ → Y) (h : ℝ)
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The forward time difference `tD f j = h⁻¹(f(j+1) - f(j))`. -/
def tD (f : ℕ → Y → 𝔸) : ℕ → Y → 𝔸 := fun j y => h⁻¹ • (f (j + 1) y - f j y)

/-- The time shift `(tsh f) j = f (j+1)`. -/
def tsh (f : ℕ → Y → 𝔸) : ℕ → Y → 𝔸 := fun j => f (j + 1)

/-- **Mixed difference bounds on the forward window `[0, N]`**: `TB N k f B` iff every slice
`f j`, `j ≤ N`, is `C_h^k`-bounded by `B` in space, and (if `N ≥ 1`) the time difference `tD f` is
`TB (N-1) (k-1)`.  Equivalently: every difference word with `r` time letters and at most `k - r`
spatial letters is bounded by `B` at every time `j` with `j + r ≤ N`. -/
def TB : ℕ → ℕ → (ℕ → Y → 𝔸) → ℝ → Prop
  | N, 0, f, B => ∀ j ≤ N, Bnd e h 0 (f j) B
  | N, k + 1, f, B => (∀ j ≤ N, Bnd e h (k + 1) (f j) B) ∧ (1 ≤ N → TB (N - 1) k (tD h f) B)

variable {e h}

theorem TB.slice : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → ∀ j ≤ N,
    Bnd e h k (f j) B
  | _, 0, _, _, hf => hf
  | _, _ + 1, _, _, hf => hf.1

theorem TB.time {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ} (hf : TB e h N (k + 1) f B) (hN : 1 ≤ N) :
    TB e h (N - 1) k (tD h f) B := hf.2 hN

theorem TB.mono : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B B' : ℝ}, TB e h N k f B → B ≤ B' →
    TB e h N k f B'
  | _, 0, _, _, _, hf, hB => fun j hj => (hf j hj).mono hB
  | _, _ + 1, _, _, _, hf, hB => ⟨fun j hj => (hf.1 j hj).mono hB, fun hN => (hf.2 hN).mono hB⟩

/-- Lowering the order. -/
theorem TB.down : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N (k + 1) f B → TB e h N k f B
  | _, 0, _, _, hf => fun j hj => (hf.1 j hj).of_le (Nat.zero_le _)
  | _, _ + 1, _, _, hf => ⟨fun j hj => (hf.1 j hj).of_le (Nat.le_succ _), fun hN => (hf.2 hN).down⟩

theorem TB.of_le {N k k' : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ} (hf : TB e h N k' f B) (hk : k ≤ k') :
    TB e h N k f B := by
  induction k', hk using Nat.le_induction with
  | base => exact hf
  | succ k' _ ih => exact ih hf.down

/-- Shrinking the window. -/
theorem TB.window : ∀ {N N' k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → N' ≤ N →
    TB e h N' k f B
  | _, _, 0, _, _, hf, hN => fun j hj => hf j (hj.trans hN)
  | _, _, _ + 1, _, _, hf, hN => ⟨fun j hj => hf.1 j (hj.trans hN),
      fun hN' => (hf.2 (hN'.trans hN)).window (Nat.sub_le_sub_right hN 1)⟩

/-- `TB N` only depends on the slices `j ≤ N`. -/
theorem TB.congr : ∀ {N k : ℕ} {f g : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B →
    (∀ j ≤ N, f j = g j) → TB e h N k g B
  | _, 0, _, _, _, hf, hfg => fun j hj => hfg j hj ▸ hf j hj
  | N, _ + 1, f, g, _, hf, hfg => ⟨fun j hj => hfg j hj ▸ hf.1 j hj, fun hN => by
      refine (hf.2 hN).congr fun j hj => ?_
      funext y
      simp only [tD, hfg j (by omega), hfg (j + 1) (by omega)]⟩

theorem tD_add (f g : ℕ → Y → 𝔸) : tD h (f + g) = tD h f + tD h g := by
  funext j y; simp only [tD, Pi.add_apply]; rw [← smul_add]; congr 1; abel

theorem tD_neg (f : ℕ → Y → 𝔸) : tD h (-f) = -tD h f := by
  funext j y; simp only [tD, Pi.neg_apply]; rw [← smul_neg]; congr 1; abel

theorem tD_smul (c : ℝ) (f : ℕ → Y → 𝔸) : tD h (c • f) = c • tD h f := by
  funext j y; simp only [tD, Pi.smul_apply, ← smul_sub, smul_smul, mul_comm c]

theorem TB.add : ∀ {N k : ℕ} {f g : ℕ → Y → 𝔸} {B₁ B₂ : ℝ}, TB e h N k f B₁ → TB e h N k g B₂ →
    TB e h N k (f + g) (B₁ + B₂)
  | _, 0, _, _, _, _, hf, hg => fun j hj => (hf j hj).add (hg j hj)
  | _, _ + 1, _, _, _, _, hf, hg => ⟨fun j hj => (hf.1 j hj).add (hg.1 j hj), fun hN => by
      rw [tD_add]; exact (hf.2 hN).add (hg.2 hN)⟩

theorem TB.neg : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → TB e h N k (-f) B
  | _, 0, _, _, hf => fun j hj => (hf j hj).neg
  | _, _ + 1, _, _, hf => ⟨fun j hj => (hf.1 j hj).neg, fun hN => by rw [tD_neg]; exact (hf.2 hN).neg⟩

theorem TB.sub {N k : ℕ} {f g : ℕ → Y → 𝔸} {B₁ B₂ : ℝ} (hf : TB e h N k f B₁)
    (hg : TB e h N k g B₂) : TB e h N k (f - g) (B₁ + B₂) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem dW_smul' : ∀ (α : List κ) (c : ℝ) (f : Y → 𝔸), dW e h α (c • f) = c • dW e h α f
  | [], _, _ => rfl
  | i :: α, c, f => by
    have : dlt e h i (c • f) = c • dlt e h i f := by
      funext x; simp only [dlt, Pi.smul_apply, ← smul_sub, smul_smul, mul_comm c]
    simp only [dW, this, dW_smul' α]

theorem bnd_smul {k : ℕ} {f : Y → 𝔸} {B : ℝ} (hf : Bnd e h k f B) (c : ℝ) :
    Bnd e h k (c • f) (|c| * B) := fun α hα x => by
  rw [dW_smul', Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf α hα x) (abs_nonneg _)

theorem TB.smul : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → ∀ c : ℝ,
    TB e h N k (c • f) (|c| * B)
  | _, 0, _, _, hf, c => fun j hj => bnd_smul (hf j hj) c
  | _, _ + 1, _, _, hf, c => ⟨fun j hj => bnd_smul (hf.1 j hj) c, fun hN => by
      rw [tD_smul]; exact (hf.2 hN).smul c⟩

theorem tD_tsh (f : ℕ → Y → 𝔸) : tD h (tsh f) = tsh (tD h f) := rfl

/-- The time shift. -/
theorem TB.tsh : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → 1 ≤ N →
    TB e h (N - 1) k (tsh f) B
  | _, 0, _, _, hf, hN => fun j hj => hf (j + 1) (by omega)
  | N, k + 1, f, _, hf, hN => ⟨fun j hj => hf.1 (j + 1) (by omega), fun hN' => by
      rw [tD_tsh]
      have := (hf.2 hN).tsh (by omega)
      exact this⟩

/-- Spatial differences commute with time differences. -/
theorem tD_sdiff (i : κ) (f : ℕ → Y → 𝔸) :
    tD h (fun j => dlt e h i (f j)) = fun j => dlt e h i (tD h f j) := by
  funext j y; simp only [tD, dlt, ← smul_sub, smul_smul]; congr 1; abel

/-- A spatial difference costs one order. -/
theorem TB.sdiff : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N (k + 1) f B → ∀ i : κ,
    TB e h N k (fun j => dlt e h i (f j)) B
  | _, 0, _, _, hf, i => fun j hj => (hf.1 j hj).diff i
  | _, _ + 1, _, _, hf, i => ⟨fun j hj => (hf.1 j hj).diff i, fun hN => by
      rw [tD_sdiff]; exact (hf.2 hN).sdiff i⟩

theorem tD_sshift (i : κ) (f : ℕ → Y → 𝔸) :
    tD h (fun j => sh e i (f j)) = fun j => sh e i (tD h f j) := rfl

/-- Spatial shifts. -/
theorem TB.sshift : ∀ {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ}, TB e h N k f B → ∀ i : κ,
    TB e h N k (fun j => sh e i (f j)) B
  | _, 0, _, _, hf, i => fun j hj => (hf j hj).shift i
  | _, _ + 1, _, _, hf, i => ⟨fun j hj => (hf.1 j hj).shift i, fun hN => by
      rw [tD_sshift]; exact (hf.2 hN).sshift i⟩

theorem TB.nonneg {N k : ℕ} {f : ℕ → Y → 𝔸} {B : ℝ} [Nonempty Y] (hf : TB e h N k f B) :
    0 ≤ B := (hf.slice 0 (Nat.zero_le _)).nonneg

/-- The discrete Leibniz rule in time `tD(fg) = tD f · tsh g + f · tD g`. -/
theorem tD_mul (f g : ℕ → Y → 𝔸) : tD h (f * g) = tD h f * tsh g + f * tD h g := by
  funext j y
  simp only [tD, tsh, Pi.mul_apply, Pi.add_apply, smul_mul_assoc, mul_smul_comm, ← smul_add]
  congr 1
  noncomm_ring

/-- **The mixed difference norms form a Banach algebra**: `‖fg‖ ≤ 2^k ‖f‖ ‖g‖`. -/
theorem TB_mul : ∀ (k : ℕ) {N : ℕ} {f g : ℕ → Y → 𝔸} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
    TB e h N k f B₁ → TB e h N k g B₂ → TB e h N k (f * g) (2 ^ k * (B₁ * B₂))
  | 0, _, _, _, _, _, h1, h2, hf, hg => fun j hj => Bnd_mul 0 h1 h2 (hf j hj) (hg j hj)
  | k + 1, N, f, g, B₁, B₂, h1, h2, hf, hg => by
    refine ⟨fun j hj => Bnd_mul (k + 1) h1 h2 (hf.1 j hj) (hg.1 j hj), fun hN => ?_⟩
    rw [tD_mul]
    have e1 := TB_mul k h1 h2 (hf.2 hN) (hg.tsh hN).down
    have e2 := TB_mul k h1 h2 (hf.window (Nat.sub_le N 1)).down (hg.2 hN)
    refine (e1.add e2).mono (le_of_eq ?_)
    ring

end Calculus

/-! ### Quaternion-valued families: constants, conjugation, series -/

section Quaternion

open scoped Quaternion

variable {Y κ : Type*} [AddCommGroup Y] {e : κ → Y} {h : ℝ}

theorem TB_const : ∀ (N k : ℕ) (c : ℍ), TB e h N k (fun _ _ => c) ‖c‖
  | _, 0, c => fun _ _ => Bnd_const 0 c
  | N, k + 1, c => ⟨fun _ _ => Bnd_const (k + 1) c, fun _ => by
      have : tD h (fun (_ : ℕ) (_ : Y) => c) = fun _ _ => 0 := by funext j y; simp [tD]
      rw [this]
      exact (TB_const (N - 1) k 0).mono (by simp)⟩

theorem tD_star (f : ℕ → Y → ℍ) :
    tD h (fun j => star ∘ f j) = fun j => star ∘ tD h f j := by
  funext j y
  simp only [tD, Function.comp_apply, Quaternion.star_smul, star_sub]

theorem TB.star : ∀ {N k : ℕ} {f : ℕ → Y → ℍ} {B : ℝ}, TB e h N k f B →
    TB e h N k (fun j => star ∘ f j) B
  | _, 0, _, _, hf => fun j hj => (hf j hj).star
  | _, _ + 1, _, _, hf => ⟨fun j hj => (hf.1 j hj).star, fun hN => by
      rw [tD_star]; exact (hf.2 hN).star⟩

/-- `1 + h f` in the mixed norms. -/
theorem TB.one_add {N k : ℕ} {f : ℕ → Y → ℍ} {B : ℝ} (hh : 0 < h) (hf : TB e h N k f B) :
    TB e h N k ((fun _ _ => (1 : ℍ)) + h • f) (1 + h * B) := by
  have := (TB_const (e := e) (h := h) N k 1).add (hf.smul h)
  rwa [norm_one, abs_of_pos hh] at this

/-! #### Absolutely convergent series -/

theorem summable_of_Bnd {f : ℕ → Y → ℍ} {B : ℕ → ℝ} {k : ℕ} (hf : ∀ n, Bnd e h k (f n) (B n))
    (hB : Summable B) (α : List κ) (hα : α.length ≤ k) (y : Y) :
    Summable fun n => dW e h α (f n) y :=
  Summable.of_norm_bounded hB fun n => hf n α hα y

theorem dW_tsum {f : ℕ → Y → ℍ} {B : ℕ → ℝ} {k : ℕ} (hf : ∀ n, Bnd e h k (f n) (B n))
    (hB : Summable B) : ∀ (α : List κ), α.length ≤ k →
    dW e h α (fun y => ∑' n, f n y) = fun y => ∑' n, dW e h α (f n) y
  | [], _ => rfl
  | i :: α, hα => by
    have hk : 1 ≤ k := by simp at hα; omega
    have hs : ∀ y, Summable fun n => f n y := fun y =>
      summable_of_Bnd hf hB [] (Nat.zero_le _) y
    have e1 : dlt e h i (fun y => ∑' n, f n y) = fun y => ∑' n, dlt e h i (f n) y := by
      funext y
      simp only [dlt]
      rw [← (hs (y + e i)).tsum_sub (hs y), ← tsum_const_smul'']
    have hf' : ∀ n, Bnd e h (k - 1) (dlt e h i (f n)) (B n) := fun n β hβ y =>
      hf n (i :: β) (by simp; omega) y
    simp only [dW, e1]
    exact dW_tsum hf' hB α (by simp at hα; omega)

theorem Bnd_tsum {f : ℕ → Y → ℍ} {B : ℕ → ℝ} {k : ℕ} (hf : ∀ n, Bnd e h k (f n) (B n))
    (hB : Summable B) : Bnd e h k (fun y => ∑' n, f n y) (∑' n, B n) := by
  intro α hα y
  rw [dW_tsum hf hB α hα]
  refine (norm_tsum_le_tsum_norm (summable_of_Bnd hf hB α hα y).norm).trans ?_
  exact (summable_of_Bnd hf hB α hα y).norm.tsum_le_tsum (fun n => hf n α hα y) hB |>.trans
    le_rfl

theorem TB_tsum : ∀ {N k : ℕ} {f : ℕ → ℕ → Y → ℍ} {B : ℕ → ℝ}, (∀ n, TB e h N k (f n) (B n)) →
    Summable B → TB e h N k (fun j y => ∑' n, f n j y) (∑' n, B n)
  | _, 0, _, _, hf, hB => fun j hj => Bnd_tsum (fun n => (hf n) j hj) hB
  | N, k + 1, f, B, hf, hB => by
    refine ⟨fun j hj => Bnd_tsum (fun n => (hf n).1 j hj) hB, fun hN => ?_⟩
    have hs : ∀ j ≤ N, ∀ y, Summable fun n => f n j y := fun j hj y =>
      summable_of_Bnd (fun n => (hf n).1 j hj) hB [] (Nat.zero_le _) y
    have hT := TB_tsum (fun n => (hf n).2 hN) hB
    refine hT.congr fun j hj => ?_
    funext y
    simp only [tD]
    rw [← (hs (j + 1) (by omega) y).tsum_sub (hs j (by omega) y), ← tsum_const_smul'']

end Quaternion

/-! ### Sampled scalar functions and iterated difference quotients -/

section Scalar

/-- The forward difference quotient `Δ_h φ(t) = h⁻¹(φ(t + h) - φ(t))`. -/
def dq (h : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun t => h⁻¹ * (φ (t + h) - φ t)

theorem hasDerivAt_iter_dq (h : ℝ) :
    ∀ (r : ℕ) (φ φ' : ℝ → ℝ), (∀ t, HasDerivAt φ (φ' t) t) →
      ∀ t, HasDerivAt ((dq h)^[r] φ) ((dq h)^[r] φ' t) t
  | 0, _, _, hφ, t => hφ t
  | r + 1, φ, φ', hφ, t => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine hasDerivAt_iter_dq h r (dq h φ) (dq h φ') (fun s => ?_) t
    have h1 : HasDerivAt (fun t => φ (t + h)) (φ' (s + h)) s := (hφ (s + h)).comp_add_const s h
    exact (h1.sub (hφ s)).const_mul h⁻¹

/-- The mean value bound for one difference quotient. -/
theorem abs_dq_le {h : ℝ} (hh : 0 < h) {φ φ' : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (φ' t) t) {M : ℝ}
    (hM : ∀ t, |φ' t| ≤ M) (t : ℝ) : |dq h φ t| ≤ M := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (f' := φ') (C := M)
    (a := t) (b := t + h) (fun s _ => (hφ s).hasDerivWithinAt) (fun s _ => hM s) (t + h)
    (Set.right_mem_Icc.2 (by linarith))
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at this
  rw [dq, abs_mul, abs_inv, abs_of_pos hh]
  calc h⁻¹ * |φ (t + h) - φ t| ≤ h⁻¹ * (M * h) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = M := by field_simp

/-- **Iterated difference quotients of a smooth function are bounded by its derivatives**:
`|Δ_h^r φ(t)| ≤ sup |φ^{(r)}|` for `φ ∈ C^r`. -/
theorem abs_iterDQ_le {h : ℝ} (hh : 0 < h) :
    ∀ (r : ℕ) (φ : ℝ → ℝ), ContDiff ℝ r φ → ∀ {M : ℝ}, (∀ t, |iteratedDeriv r φ t| ≤ M) →
      ∀ t, |(dq h)^[r] φ t| ≤ M
  | 0, φ, _, M, hM, t => by simpa using hM t
  | r + 1, φ, hφ, M, hM, t => by
    have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hφ' : ContDiff ℝ r (deriv φ) := by
      have h1 : ContDiff ℝ ((r : WithTop ℕ∞) + 1) φ := by exact_mod_cast hφ
      exact (contDiff_succ_iff_deriv.1 h1).2.2
    have hM' : ∀ t, |iteratedDeriv r (deriv φ) t| ≤ M := fun t => by
      rw [← iteratedDeriv_succ']; exact hM t
    rw [Function.iterate_succ_apply']
    refine abs_dq_le hh (φ' := (dq h)^[r] (deriv φ))
      (hasDerivAt_iter_dq h r φ (deriv φ) (fun s => (hd s).hasDerivAt)) ?_ t
    exact abs_iterDQ_le hh r (deriv φ) hφ' hM'

variable {Y κ : Type*} [AddCommGroup Y] {e : κ → Y} {h : ℝ}

open scoped Quaternion

/-- The time family of a sampled real function, `j ↦ φ(jh)` (constant in space). -/
def sampled (h : ℝ) (φ : ℝ → ℝ) : ℕ → Y → ℍ := fun j _ => ((φ (j * h) : ℝ) : ℍ)

theorem tD_sampled (hh : h ≠ 0) (φ : ℝ → ℝ) :
    tD h (sampled (Y := Y) h φ) = sampled h (dq h φ) := by
  funext j y
  simp only [tD, sampled, dq]
  rw [show ((j + 1 : ℕ) : ℝ) * h = j * h + h by push_cast; ring, Algebra.smul_def]
  simp

/-- **Sampled scalar functions**: if `|Δ_h^r φ| ≤ M` for `r ≤ k`, the sampled family is `TB`
by `M`. -/
theorem TB_sampled (hh : 0 < h) : ∀ (N k : ℕ) (φ : ℝ → ℝ) {M : ℝ},
    (∀ r ≤ k, ∀ t, |(dq h)^[r] φ t| ≤ M) → TB e h N k (sampled h φ) M
  | _, 0, φ, M, hM => fun j _ => by
    have := Bnd_const (e := e) (h := h) 0 (((φ (j * h) : ℝ) : ℍ))
    refine this.mono ?_
    rw [Quaternion.norm_coe, Real.norm_eq_abs]; simpa using hM 0 le_rfl (j * h)
  | N, k + 1, φ, M, hM => ⟨fun j _ => by
      have := Bnd_const (e := e) (h := h) (k + 1) (((φ (j * h) : ℝ) : ℍ))
      refine this.mono ?_
      rw [Quaternion.norm_coe, Real.norm_eq_abs]; simpa using hM 0 (Nat.zero_le _) (j * h),
    fun _ => by
      rw [tD_sampled hh.ne']
      refine TB_sampled hh (N - 1) k (dq h φ) fun r hr t => ?_
      rw [← Function.iterate_succ_apply]
      exact hM (r + 1) (by omega) t⟩

end Scalar

end RenewalGeometry.TimeSlab
