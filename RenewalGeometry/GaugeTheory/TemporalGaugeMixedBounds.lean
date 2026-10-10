/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TimeSlabDifferenceCalculus
import RenewalGeometry.GaugeTheory.WeakTemporalGaugeHierarchy
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# Mixed space–time control of the causal temporal gauge and of the logarithmic link chart

Clause of `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript, `app:gauge-reader`,
`eq:gauge-temporal`: "Iterated product rules and discrete Gronwall show that one additional
covariant derivative controls the transformed spatial logarithmic links through order `s` on a
fixed physical-time interval.  All transformed matter fields retain the same order of control").

`WeakTemporalGauge.temporal_hierarchy` controls the causal gauge `g_j` and the transformed links
`a'_k(j) = h⁻¹(w'_k - 1)` in *spatial* difference norms on each time slice.  The reader needs
*mixed* space–time differences.  This file supplies them on a forward time window
(`TimeSlab.TB`), and passes to the logarithmic coordinate `h⁻¹ log w'_k`:

* `tD_gT` (`δ_t g = g a_0`), `tD_aTF` (`δ_t a'_k = g (p/h) ḡ w'_k`), `pF_eq` (the plaquette
  coordinate `p/h` through one more derivative of the normalized links, `pT_eq`);
* `TB_pF` — mixed bounds of `p/h` at order `k` from order `k + 1` of the normalized links;
* **`temporal_TB`** — if the normalized temporal and spatial link coordinates have mixed bounds
  `A` at order `K + 1` on every window, then `g` and `a'_k` have mixed bounds `gC A T K k` at every
  order `k ≤ K` on every window `[0, N]` with `Nh ≤ T` (no smallness of the links);
* **`TB_logChart`** — the logarithmic chart `h⁻¹ log(1 + h a) = Σ_n (-1)^n h^n a^{n+1}/(n+1)`
  (the analytic branch `SeriesLogChart.logChart` of `w = 1 + h a`) has mixed bound `2C` whenever
  `a` has mixed bound `C` and `h 2^K C ≤ 1/2` (absolutely convergent series in the Banach algebra
  of mixed difference norms, `TB_mul`, `TB_tsum`).
-/

open Finset

noncomputable section

namespace RenewalGeometry.TemporalMixed

open scoped Quaternion
open WeakNormReader WeakTemporalGauge TimeSlab

set_option linter.unusedSectionVars false

variable {Y κ : Type*} [AddCommGroup Y] {e : κ → Y} {h : ℝ}
variable {w0 : ℕ → Y → ℍ} {w : ℕ → κ → Y → ℍ}

/-- The normalized temporal link coordinate as a time family. -/
def a0F (h : ℝ) (w0 : ℕ → Y → ℍ) : ℕ → Y → ℍ := fun j => a0 h w0 j

/-- The normalized spatial link coordinate as a time family. -/
def aSF (h : ℝ) (w : ℕ → κ → Y → ℍ) (k : κ) : ℕ → Y → ℍ := fun j => aS h w j k

/-- The transformed spatial link coordinate `a'_k` as a time family. -/
def aTF (e : κ → Y) (h : ℝ) (w0 : ℕ → Y → ℍ) (w : ℕ → κ → Y → ℍ) (k : κ) : ℕ → Y → ℍ :=
  fun j => aT e h w0 w j k

/-- The plaquette coordinate divided by the mesh, `p/h`, as a time family. -/
def pF (e : κ → Y) (h : ℝ) (w0 : ℕ → Y → ℍ) (w : ℕ → κ → Y → ℍ) (k : κ) : ℕ → Y → ℍ :=
  fun j => h⁻¹ • pT e h w0 w j k

/-- `δ_t g = g a_0`. -/
theorem tD_gT : tD h (gT w0) = gT w0 * a0F h w0 := by
  funext j y
  simp only [tD, gT, a0F, a0, Pi.mul_apply, mul_smul_comm, mul_sub, mul_one]

/-- `δ_t a'_k = g (p/h) ḡ w'_k`. -/
theorem tD_aTF (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (k : κ) :
    tD h (aTF e h w0 w k) = gT w0 * pF e h w0 w k * (fun j => star ∘ gT w0 j) *
      (fun j => wT e w0 w j k) := by
  funext j y
  have := congrFun (aT_succ (e := e) (h := h) hw0 hw j k) y
  simp only [aTF, tD, pF, Pi.mul_apply, Pi.add_apply, Function.comp_apply] at this ⊢
  rw [this, add_sub_cancel_left]
  simp only [Pi.smul_apply, smul_mul_assoc, mul_smul_comm]

/-- The plaquette coordinate through the normalized links (`pT_eq`). -/
theorem pF_eq (hh : h ≠ 0) (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (k : κ) :
    pF e h w0 w k = (tD h (aSF h w k) - (fun j => dlt e h k (a0F h w0 j)) +
      a0F h w0 * TimeSlab.tsh (aSF h w k) - aSF h w k * (fun j => sh e k (a0F h w0 j))) *
        (fun j => star ∘ sh e k (w0 j)) * (fun j => star ∘ w j k) := by
  funext j y
  have := congrFun (pT_eq (e := e) hh hw0 hw j k) y
  simp only [pF, Pi.smul_apply] at this ⊢
  rw [this, smul_smul, inv_mul_cancel₀ hh, one_smul]
  rfl

theorem w0_eq (hh : h ≠ 0) : (fun j => w0 j) = (fun _ _ => (1 : ℍ)) + h • a0F h w0 := by
  funext j y; simp [a0F, a0, smul_smul, mul_inv_cancel₀ hh]

theorem w_eq (hh : h ≠ 0) (k : κ) : (fun j => w j k) = (fun _ _ => (1 : ℍ)) + h • aSF h w k := by
  funext j y; simp [aSF, aS, smul_smul, mul_inv_cancel₀ hh]

theorem wT_eqF (hh : h ≠ 0) (k : κ) :
    (fun j => wT e w0 w j k) = (fun _ _ => (1 : ℍ)) + h • aTF e h w0 w k := by
  funext j y; simp [aTF, aT, smul_smul, mul_inv_cancel₀ hh]

theorem plaqC_nonneg {A : ℝ} (hA : 0 ≤ A) (K : ℕ) : 0 ≤ plaqC K A := by
  unfold plaqC; positivity

/-- **One more derivative of the normalized links controls `p/h` in the mixed norms.** -/
theorem TB_pF (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : ∀ j x, ‖w0 j x‖ = 1)
    (hw : ∀ j k x, ‖w j k x‖ = 1) {A : ℝ} (hA0 : 0 ≤ A) {k : ℕ}
    (ha0 : ∀ N, TB e h N (k + 1) (a0F h w0) A) (k' : κ)
    (haS : ∀ N, TB e h N (k + 1) (aSF h w k') A) (N : ℕ) :
    TB e h N k (pF e h w0 w k') (plaqC k A) := by
  rw [pF_eq hh0.ne' hw0 hw k']
  have hdt : TB e h N k (tD h (aSF h w k')) A := by
    have := (haS (N + 1)).time (by omega); simpa using this
  have hdx : TB e h N k (fun j => dlt e h k' (a0F h w0 j)) A := (ha0 N).sdiff k'
  have hm1 := TB_mul k hA0 hA0 (ha0 N).down ((haS (N + 1)).down.tsh (by omega) |>.window
    (by omega))
  have hm2 := TB_mul k hA0 hA0 (haS N).down ((ha0 N).down.sshift k')
  have hS := ((hdt.sub hdx).add hm1).sub hm2
  have hW0 : TB e h N k (fun j => star ∘ sh e k' (w0 j)) (1 + A) := by
    have h1 := (((ha0 N).down.one_add hh0).sshift k').star
    refine (h1.congr fun j _ => ?_).mono (by nlinarith)
    rw [show w0 j = (((fun _ _ => (1 : ℍ)) + h • a0F h w0 : ℕ → Y → ℍ)) j from congrFun (w0_eq hh0.ne') j]
  have hW : TB e h N k (fun j => star ∘ w j k') (1 + A) := by
    have h1 := ((haS N).down.one_add hh0).star
    refine (h1.congr fun j _ => ?_).mono (by nlinarith)
    rw [show w j k' = (((fun _ _ => (1 : ℍ)) + h • aSF h w k' : ℕ → Y → ℍ)) j from
      congrFun (w_eq hh0.ne' k') j]
  have h1 := TB_mul k (by positivity) (by positivity) hS hW0
  have h2 := TB_mul k (by positivity) (by positivity) h1 hW
  exact h2.mono (le_of_eq (by unfold plaqC; ring))

/-! ### Mixed bounds of the causal gauge and of the transformed links -/

/-- The mixed temporal-gauge constants. -/
def gC (A T : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => tempC A (plaqC K A) T 0
  | k + 1 => max (tempC A (plaqC K A) T (k + 1)) (max (2 ^ k * (gC A T K k * A))
      (2 ^ k * (2 ^ k * (2 ^ k * (gC A T K k * plaqC k A) * gC A T K k) * (1 + gC A T K k))))

theorem tempC_le_gC (A T : ℝ) (K : ℕ) : ∀ k, tempC A (plaqC K A) T k ≤ gC A T K k
  | 0 => le_rfl
  | _ + 1 => le_max_left _ _

theorem gC_nonneg {A T : ℝ} (hA : 0 ≤ A) (K : ℕ) (k : ℕ) : 0 ≤ gC A T K k :=
  (tempC_nonneg A (plaqC K A) T hA k).trans (tempC_le_gC A T K k)

/-- **Mixed space–time control of the causal temporal gauge** (`eq:gauge-temporal`, all mixed
orders): for `0 < h ≤ 1`, unit normalized links whose temporal and spatial coordinates `a_0, a_k`
have mixed bounds `A` at order `K + 1` on every forward window, the causal gauge `g` and the
transformed spatial links `a'_k = h⁻¹(g w_k ḡ⁺ - 1)` have mixed bounds `gC A T K k` at every order
`k ≤ K` on every window `[0, N]` with `Nh ≤ T`.  The constants depend only on `A, T, K, k`. -/
theorem temporal_TB (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : ∀ j x, ‖w0 j x‖ = 1)
    (hw : ∀ j k x, ‖w j k x‖ = 1) {A T : ℝ} (hA0 : 0 ≤ A) (hT : 0 ≤ T) {K : ℕ}
    (ha0 : ∀ N, TB e h N (K + 1) (a0F h w0) A) (haS : ∀ k N, TB e h N (K + 1) (aSF h w k) A) :
    ∀ k ≤ K, ∀ N : ℕ, (N : ℝ) * h ≤ T →
      TB e h N k (gT w0) (gC A T K k) ∧ ∀ k', TB e h N k (aTF e h w0 w k') (gC A T K k) := by
  -- the per-slice spatial hierarchy
  have hA : ∀ j k, Bnd e h K (aS h w j k) A := fun j k =>
    ((haS k j).slice j le_rfl).of_le (Nat.le_succ K)
  have hp : ∀ j k, Bnd e h K (pT e h w0 w j k) (h * plaqC K A) := by
    intro j k
    have hdt : Bnd e h K (h⁻¹ • (aS h w (j + 1) k - aS h w j k)) A := by
      have := ((haS k (j + 1)).time (by omega)).slice j (by omega)
      exact this
    exact pT_bound hh0 hh1 hw0 hw hA0 j k hdt ((ha0 j).slice j le_rfl) (hA j k) (hA (j + 1) k)
  have hier := temporal_hierarchy hh0 hh1 hw0 hw hA0 (plaqC_nonneg hA0 K) hT hA hp
  intro k
  induction k with
  | zero =>
    intro hk N hN
    have hs : ∀ j ≤ N, (j : ℝ) * h ≤ T := fun j hj =>
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh0.le).trans hN
    exact ⟨fun j hj => (hier 0 hk j (hs j hj)).1, fun k' j hj => (hier 0 hk j (hs j hj)).2 k'⟩
  | succ k ih =>
    intro hk N hN
    have hs : ∀ j ≤ N, (j : ℝ) * h ≤ T := fun j hj =>
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh0.le).trans hN
    have hC0 := gC_nonneg (T := T) hA0 K k
    refine ⟨⟨fun j hj => ((hier (k + 1) hk j (hs j hj)).1).mono (tempC_le_gC A T K (k + 1)),
      fun hN1 => ?_⟩, fun k' => ⟨fun j hj => ((hier (k + 1) hk j (hs j hj)).2 k').mono
        (tempC_le_gC A T K (k + 1)), fun hN1 => ?_⟩⟩
    · have hN' : ((N - 1 : ℕ) : ℝ) * h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) hh0.le).trans hN
      obtain ⟨ihg, -⟩ := ih (by omega) (N - 1) hN'
      rw [tD_gT]
      refine (TB_mul k hC0 hA0 ihg ((ha0 (N - 1)).of_le (by omega))).mono ?_
      exact le_max_of_le_right (le_max_left _ _)
    · have hN' : ((N - 1 : ℕ) : ℝ) * h ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) hh0.le).trans hN
      obtain ⟨ihg, iha⟩ := ih (by omega) (N - 1) hN'
      rw [tD_aTF hw0 hw k']
      have hP := TB_pF (k := k) hh0 hh1 hw0 hw hA0 (fun N => (ha0 N).of_le (by omega)) k'
        (fun N => (haS k' N).of_le (by omega)) (N - 1)
      have hwT : TB e h (N - 1) k (fun j => wT e w0 w j k') (1 + gC A T K k) := by
        rw [wT_eqF hh0.ne' k']
        exact ((iha k').one_add hh0).mono (by nlinarith)
      have h1 := TB_mul k hC0 (plaqC_nonneg hA0 k) ihg hP
      have hP0 := plaqC_nonneg hA0 k
      have h2 := TB_mul k (by positivity) hC0 h1 ihg.star
      have h3 := TB_mul k (by positivity) (by positivity) h2 hwT
      exact h3.mono (le_max_of_le_right (le_max_right _ _))

/-! ### The logarithmic link chart -/

open ShiftedPlaquette SeriesLogChart

theorem TB_pow {N K : ℕ} {a : ℕ → Y → ℍ} {C : ℝ} (hC : 0 ≤ C) (ha : TB e h N K a C) :
    ∀ n : ℕ, TB e h N K (a ^ (n + 1)) ((2 ^ K) ^ n * C ^ (n + 1))
  | 0 => by simpa using ha
  | n + 1 => by
    have ih := TB_pow hC ha n
    rw [pow_succ]
    refine (TB_mul K (by positivity) hC ih ha).mono (le_of_eq ?_)
    ring

/-- **The logarithmic link chart in the mixed norms**: if `a` has mixed bound `C` at order `K` on
`[0, N]` and `h 2^K C ≤ 1/2`, then `h⁻¹ log(1 + h a) = Σ_n (-1)^n h^n a^{n+1}/(n+1)` has mixed bound
`2C` (`log` is the analytic branch `logOneAdd` near the identity). -/
theorem TB_logChart (hh : 0 < h) {N K : ℕ} {a : ℕ → Y → ℍ} {C : ℝ} (hC : 0 ≤ C)
    (ha : TB e h N K a C) (hsmall : h * (2 ^ K * C) ≤ 1 / 2) :
    TB e h N K (fun j y => h⁻¹ • logOneAdd (h • a j y)) (2 * C) := by
  set f : ℕ → ℕ → Y → ℍ := fun n => (logQuotientCoeff n * h ^ n) • a ^ (n + 1) with hf
  have hq : 0 ≤ h * 2 ^ K := by positivity
  have hfB : ∀ n, TB e h N K (f n) (C * (1 / 2) ^ n) := by
    intro n
    refine ((TB_pow hC ha n).smul _).mono ?_
    rw [abs_mul, abs_pow, abs_of_pos hh]
    have hc : |logQuotientCoeff n| ≤ 1 := by
      have := norm_logQuotientCoeff n
      rw [Real.norm_eq_abs] at this
      rw [this, div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have e1 : h ^ n * ((2 ^ K) ^ n * C ^ (n + 1)) = C * (h * (2 ^ K * C)) ^ n := by ring
    have e2 : C * (h * (2 ^ K * C)) ^ n ≤ C * (1 / 2) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall n) hC
    calc |logQuotientCoeff n| * h ^ n * ((2 ^ K) ^ n * C ^ (n + 1))
        ≤ 1 * h ^ n * ((2 ^ K) ^ n * C ^ (n + 1)) := by gcongr
      _ = C * (h * (2 ^ K * C)) ^ n := by rw [one_mul, e1]
      _ ≤ _ := e2
  have hsum : Summable fun n : ℕ => C * (1 / 2 : ℝ) ^ n :=
    (summable_geometric_two).mul_left C
  have htsum : ∑' n : ℕ, C * (1 / 2 : ℝ) ^ n = 2 * C := by
    rw [tsum_mul_left, tsum_geometric_two]; ring
  have hT := TB_tsum hfB hsum
  rw [htsum] at hT
  refine hT.congr fun j hj => ?_
  funext y
  have hsl : ‖a j y‖ ≤ C := (ha.slice j hj).sup y
  have hz : ‖h • a j y‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have : h * C ≤ 1 / 2 := by
      have h2 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      nlinarith
    nlinarith
  have hs := (hasSum_logOneAdd hz).const_smul h⁻¹
  refine (hs.tsum_eq.symm.trans ?_).symm
  congr 1
  funext n
  simp only [hf, Pi.smul_apply, Pi.pow_apply, smul_pow, smul_smul]
  congr 1
  rw [pow_succ]
  field_simp

end RenewalGeometry.TemporalMixed
