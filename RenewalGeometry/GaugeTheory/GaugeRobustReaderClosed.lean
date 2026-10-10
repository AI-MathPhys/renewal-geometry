/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.TemporalGaugeMixedBounds
import RenewalGeometry.GaugeTheory.GaugeReaderSobolevTail

/-!
# The weak-sector reader certificate (`cor:gauge-robust-reader`, assembled)

Einstein–SM action-closure manuscript, `cor:gauge-robust-reader` (and `app:gauge-reader`): on a
nonvanishing Higgs chart of the weak `SU(2)` sector, a cutoff-uniform bound on the finite covariant
jet energy yields, after algebraic Higgs normalization and a causal finite temporal gauge, a
bounded all-mode `H^q` reader and hence the tail estimate `τ_{h,m}(K) ≤ C K^{2-q}`, `q > m + 2`.

**Setting** (quaternion model of `WeakNormReader`): the periodic grid `(ℤ/n)⁴` of side `2π`
(`h = 2π/n`), direction `0` = time, unit quaternion links `u_μ(x)` (the `SU(2)` action on
`ℂ² ≅ ℍ`), the Higgs field `H` with `|H| ≥ ρ_*`, matter fields `F_b`.

**The record that is read.**  Algebraic Higgs normalization `W_μ = q̄_x u_μ(x) q_{x+e_μ}` and the
causal temporal gauge `g_0 = 1`, `g_{j+1} = g_j W_0(j)` (`temporal_links_trivial`: the transformed
temporal links are the identity); the transformed spatial links `W'_k = g W_k ḡ⁺` in the
logarithmic chart `h⁻¹ log W'_k` (`exp_linkCoord`: it is the logarithm), the transformed Higgs
field `g|H|` and matter fields `g Q^*F_b`.  **Disclosed rendering / manuscript correction**: the
causal temporal gauge is not time periodic (`g_n ≠ g_0` in general: the Polyakov loop), while
`eq:app-sharp-tail` applies the periodic four-dimensional Fourier reader.  We therefore read the
record **after a smooth time cut-off** `χ(t)` (`TimeCutoff`: `χ ∈ C^q`, `χ = 0` near `t = 0` and
`t = 2π`; e.g. `bumpCutoff`, which is `≡ 1` on `[π/2, 3π/2]`, where the read record is the
transformed record itself, `readerRecord_eq_of_cutoff_one`).  The cut-off costs only the constant
(the `C^q` norm of `χ`).

**Main theorem** `gauge_robust_reader`: for `q > m + 2`, `ρ_* > 0`, `R ≥ 0`, a cut-off `χ` and a
finite matter index set there are `n₀` and `C` (depending only on `q, m, ρ_*, R, χ` and the number
of matter fields) such that for **every** `n ≥ n₀`, unit links, `|H| ≥ ρ_*`,
`J_{h,q+5}(H;U) ≤ R` and `J_{h,q+3}(F_b;U) ≤ R`, the reader tail of the cut-off normalized
temporal-gauge record satisfies `τ_{h,m}(K) ≤ C K^{2-q}` for all `1 ≤ K ≤ r`, `2r < n` — without
derivatives of the original frame or smallness of the original links.

Proof: `gauge_normalized_reader` (normalized links in `C_h^{q+1}`), pull-back to time families
(`TB_pull`), `TemporalMixed.temporal_TB` (mixed bounds of the causal gauge and transformed links on
the window `[0, n + q]`), `TemporalMixed.TB_logChart` (logarithmic coordinates, for `n ≥ n₀`),
products (`TB_mul`), the sampled cut-off (`TB_sampled`, `abs_iterDQ_le`), the periodic lift of a
family vanishing near the seam (`Bnd_lift`), the sup-to-energy bound `diffEnergy_le` and
`GaugeReaderTail.tail_le_diffEnergy`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.GaugeRobustReader

open scoped Quaternion Real
open WeakNormReader WeakTemporalGauge TimeSlab TemporalMixed GaugeCovEmbed GridSobolev

set_option linter.unusedSectionVars false

/-! ### Time slices of the four-dimensional grid -/

section Slices

variable {n : ℕ} [NeZero n]

/-- The time slice `j` of a field on `(ℤ/n)⁴` as a field on `(ℤ/n)³`. -/
def pull (F : (Fin 4 → ZMod n) → ℍ) : ℕ → (Fin 3 → ZMod n) → ℍ :=
  fun j y => F (Fin.cons (j : ZMod n) y)

theorem cons_add_step0 (a : ZMod n) (y : Fin 3 → ZMod n) :
    (Fin.cons a y : Fin 4 → ZMod n) + gridStep 0 = Fin.cons (a + 1) y := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [gridStep]
  · simp [gridStep, Pi.single_apply, Fin.succ_ne_zero]

theorem cons_add_stepSucc (a : ZMod n) (y : Fin 3 → ZMod n) (k : Fin 3) :
    (Fin.cons a y : Fin 4 → ZMod n) + gridStep k.succ = Fin.cons a (y + gridStep k) := by
  funext i
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [gridStep, Pi.single_apply, (Fin.succ_ne_zero k).symm]
  · simp [gridStep, Pi.single_apply, Fin.succ_inj]

theorem dlt_pull (h : ℝ) (F : (Fin 4 → ZMod n) → ℍ) (k : Fin 3) (j : ℕ) :
    dlt gridStep h k (pull F j) = pull (dlt gridStep h k.succ F) j := by
  funext y; simp only [dlt, pull, cons_add_stepSucc]

theorem dW_pull (h : ℝ) : ∀ (α : List (Fin 3)) (F : (Fin 4 → ZMod n) → ℍ) (j : ℕ),
    dW gridStep h α (pull F j) = pull (dW gridStep h (α.map Fin.succ) F) j
  | [], _, _ => rfl
  | k :: α, F, j => by
    simp only [dW, List.map_cons]
    rw [dlt_pull, dW_pull h α]

theorem Bnd_pull {h : ℝ} {k : ℕ} {F : (Fin 4 → ZMod n) → ℍ} {B : ℝ}
    (hF : Bnd gridStep h k F B) (j : ℕ) : Bnd gridStep h k (pull F j) B := fun α hα y => by
  rw [dW_pull]; exact hF _ (by simpa using hα) _

theorem tD_pull (h : ℝ) (F : (Fin 4 → ZMod n) → ℍ) :
    tD h (pull F) = pull (dlt gridStep h 0 F) := by
  funext j y
  simp only [tD, dlt, pull, cons_add_step0, Nat.cast_succ]

/-- **Pull-back of four-dimensional difference bounds to mixed time-family bounds.** -/
theorem TB_pull {h : ℝ} : ∀ (k : ℕ) {F : (Fin 4 → ZMod n) → ℍ} {B : ℝ},
    Bnd gridStep h k F B → ∀ N, TB gridStep h N k (pull F) B
  | 0, _, _, hF, _ => fun j _ => Bnd_pull hF j
  | k + 1, F, _, hF, N => ⟨fun j _ => Bnd_pull hF j, fun _ => by
      rw [tD_pull]; exact TB_pull k (hF.diff 0) _⟩

end Slices

/-! ### The periodic lift of a family vanishing near the seam -/

section Lift

variable {n : ℕ} [NeZero n]

/-- The lift of a time family to `(ℤ/n)⁴`: `Ψ(x) = ψ(x₀)(x₁, x₂, x₃)` (`x₀ ∈ {0, …, n-1}`). -/
def lift (ψ : ℕ → (Fin 3 → ZMod n) → ℍ) : (Fin 4 → ZMod n) → ℍ :=
  fun x => ψ (x 0).val (Fin.tail x)

theorem val_add_one (a : ZMod n) : (a + 1).val = (a.val + 1) % n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [← Nat.cast_succ, ZMod.val_natCast]

theorem add_step0_zero (x : Fin 4 → ZMod n) : (x + gridStep 0 : Fin 4 → ZMod n) 0 = x 0 + 1 := by
  simp [gridStep]

theorem tail_add_step0 (x : Fin 4 → ZMod n) : Fin.tail (x + gridStep 0) = Fin.tail x := by
  funext k; simp [Fin.tail, gridStep, Pi.single_apply, Fin.succ_ne_zero]

theorem add_stepSucc_zero (x : Fin 4 → ZMod n) (k : Fin 3) :
    (x + gridStep k.succ : Fin 4 → ZMod n) 0 = x 0 := by
  simp [gridStep, Pi.single_apply, (Fin.succ_ne_zero k).symm]

theorem tail_add_stepSucc (x : Fin 4 → ZMod n) (k : Fin 3) :
    Fin.tail (x + gridStep k.succ) = Fin.tail x + gridStep k := by
  funext m; simp [Fin.tail, gridStep, Pi.single_apply, Fin.succ_inj]

/-- **The periodic lift of a time family vanishing near both ends of `[0, n)`**: if `ψ` has
mixed bounds `B` of order `k` on the window `[0, N]`, `N ≥ n + k`, and `ψ(j) = 0` for `j ≤ k` and
for `j ≥ n - k - 1`, then its lift to `(ℤ/n)⁴` has all difference words of length `≤ k` (in all
four directions, across the seam) bounded by `B`. -/
theorem Bnd_lift {h : ℝ} : ∀ (k : ℕ) {N : ℕ} {ψ : ℕ → (Fin 3 → ZMod n) → ℍ} {B : ℝ}, 0 ≤ B →
    n + k ≤ N → TB gridStep h N k ψ B → (∀ j, (j ≤ k ∨ n ≤ j + k + 1) → ψ j = 0) →
    Bnd gridStep h k (lift ψ) B
  | 0, N, ψ, B, _, hN, hψ, _ => by
    intro α hα x
    have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
    subst this
    have hv := ZMod.val_lt (x 0)
    exact (hψ (x 0).val (by omega)).sup _
  | k + 1, N, ψ, B, hB, hN, hψ, hz => by
    have hv : ∀ x : Fin 4 → ZMod n, (x 0).val < n := fun x => ZMod.val_lt _
    refine Bnd.succ (fun x => (hψ.1 (x 0).val (by have := hv x; omega)).sup _) (fun i => ?_)
    have key0 : Bnd gridStep h k (dlt gridStep h (0 : Fin 4) (lift ψ)) B := by
      have heq : dlt gridStep h (0 : Fin 4) (lift ψ) = lift (tD h ψ) := by
        funext x
        simp only [dlt, lift, tD, add_step0_zero, tail_add_step0, val_add_one]
        by_cases hlt : (x 0).val + 1 < n
        · rw [Nat.mod_eq_of_lt hlt]
        · have he : (x 0).val + 1 = n := by have := hv x; omega
          rw [he, Nat.mod_self, hz 0 (Or.inl (Nat.zero_le _)), hz n (Or.inr (by omega))]
      rw [heq]
      refine Bnd_lift k hB (N := N - 1) (by omega) (hψ.2 (by omega)) (fun j hj => ?_)
      funext y
      simp only [tD]
      rcases hj with hj | hj
      · rw [hz j (Or.inl (by omega)), hz (j + 1) (Or.inl (by omega))]; simp
      · rw [hz j (Or.inr (by omega)), hz (j + 1) (Or.inr (by omega))]; simp
    have keyS : ∀ m : Fin 3, Bnd gridStep h k
        (dlt (gridStep (ι := Fin 4) (n := n)) h m.succ (lift ψ)) B := by
      intro m
      have heq : dlt (gridStep (ι := Fin 4) (n := n)) h m.succ (lift ψ) =
          lift (fun j => dlt gridStep h m (ψ j)) := by
        funext x
        simp only [dlt, lift, add_stepSucc_zero, tail_add_stepSucc]
      rw [heq]
      refine Bnd_lift k hB (N := N) (by omega) (hψ.sdiff m) (fun j hj => ?_)
      rw [hz j (by omega)]
      funext y; simp [dlt]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
    · exact key0
    · exact keyS m

end Lift

/-! ### Bundling the record and the sup-to-energy bound -/

section Bundle

variable {n : ℕ} [NeZero n]

/-- The complex coordinates of a quaternion: `q ↦ (re + i·imI, imJ + i·imK)` (`ℍ ≅ ℂ²`). -/
def qC (q : ℍ) : Fin 2 → ℂ := ![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩]

theorem qC_dlt (r : ℝ) (a b : ℍ) (i : Fin 2) :
    qC (r • (a - b)) i = (r : ℂ) * (qC a i - qC b i) := by
  fin_cases i <;> apply Complex.ext <;> simp [qC]

theorem sum_norm_qC_sq (q : ℍ) : ∑ i, ‖qC q i‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [sq ‖q‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [qC, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_mk]
  ring

/-- The bundled record `x ↦ (complex coordinates of Ψ_c(x))_c` in `EuclideanSpace ℂ (σ × Fin 2)`. -/
def bundle {σ : Type*} (Ψ : σ → (Fin 4 → ZMod n) → ℍ) :
    (Fin 4 → ZMod n) → EuclideanSpace ℂ (σ × Fin 2) :=
  fun x => WithLp.toLp 2 fun p => qC (Ψ p.1 x) p.2

theorem norm_bundle_sq {σ : Type*} [Fintype σ] (Ψ : σ → (Fin 4 → ZMod n) → ℍ) (x) :
    ‖bundle Ψ x‖ ^ 2 = ∑ c, ‖Ψ c x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← sum_norm_qC_sq]
  rfl

theorem dW_append {h : ℝ} : ∀ (α β : List (Fin 4)) (f : (Fin 4 → ZMod n) → ℍ),
    dW gridStep h (α ++ β) f = dW gridStep h β (dW gridStep h α f)
  | [], _, _ => rfl
  | i :: α, β, f => by simp only [List.cons_append, dW, dW_append α β]

theorem fwdDiff_bundle {σ : Type*} [Fintype σ] (h : ℝ) (j : Fin 4) (Ψ : σ → (Fin 4 → ZMod n) → ℍ) :
    GaugeReaderTail.fwdDiff h j (bundle Ψ) = bundle fun c => dlt gridStep h j (Ψ c) := by
  funext x
  ext p
  simp only [GaugeReaderTail.fwdDiff, bundle, dlt, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.toLp_apply, qC_dlt, Complex.real_smul, gridStep]
  push_cast
  rfl

theorem iterDiff_bundle {σ : Type*} [Fintype σ] (h : ℝ) : ∀ (w : List (Fin 4)) (Ψ : σ → (Fin 4 → ZMod n) → ℍ),
    GaugeReaderTail.iterDiff h w (bundle Ψ) = bundle fun c => dW gridStep h w.reverse (Ψ c)
  | [], _ => rfl
  | j :: w, Ψ => by
    change GaugeReaderTail.fwdDiff h j (GaugeReaderTail.iterDiff h w (bundle Ψ)) = _
    rw [iterDiff_bundle h w, fwdDiff_bundle, List.reverse_cons]
    congr 1
    funext c
    rw [dW_append]
    rfl

/-- **Sup bounds give the difference energy**: if every component has all difference words of
length `≤ q` bounded by `M`, then `E_q(ξ) ≤ (nh)⁴ |σ| M² Σ_{r ≤ q} 4^r`. -/
theorem diffEnergy_le {σ : Type*} [Fintype σ] {h : ℝ} (hh : 0 ≤ h) {q : ℕ}
    {Ψ : σ → (Fin 4 → ZMod n) → ℍ} {M : ℝ} (hΨ : ∀ c, Bnd gridStep h q (Ψ c) M) :
    GaugeReaderTail.diffEnergy h q (bundle Ψ) ≤
      (n * h) ^ 4 * (Fintype.card σ * M ^ 2) * ∑ r ∈ range (q + 1), (4 : ℝ) ^ r := by
  unfold GaugeReaderTail.diffEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hrq : r ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have hterm : ∀ w : Fin r → Fin 4, GaugeReaderTail.gridSq h
      (GaugeReaderTail.iterDiff h (List.ofFn w) (bundle Ψ)) ≤
        (n * h) ^ 4 * (Fintype.card σ * M ^ 2) := by
    intro w
    rw [iterDiff_bundle, GaugeReaderTail.gridSq]
    have hpt : ∀ x, ‖bundle (fun c => dW gridStep h (List.ofFn w).reverse (Ψ c)) x‖ ^ 2 ≤
        Fintype.card σ * M ^ 2 := by
      intro x
      rw [norm_bundle_sq]
      have : ∀ c, ‖dW gridStep h (List.ofFn w).reverse (Ψ c) x‖ ^ 2 ≤ M ^ 2 := fun c =>
        pow_le_pow_left₀ (norm_nonneg _) (hΨ c _ (by simpa using hrq) x) 2
      calc ∑ c, ‖dW gridStep h (List.ofFn w).reverse (Ψ c) x‖ ^ 2 ≤ ∑ _c : σ, M ^ 2 :=
            Finset.sum_le_sum fun c _ => this c
        _ = _ := by simp
    have hcard : (Fintype.card (Fin 4 → ZMod n) : ℝ) = (n : ℝ) ^ 4 := by
      simp [Fintype.card_fun, ZMod.card]
    calc h ^ 4 * ∑ x, ‖bundle (fun c => dW gridStep h (List.ofFn w).reverse (Ψ c)) x‖ ^ 2
        ≤ h ^ 4 * ∑ _x : Fin 4 → ZMod n, (Fintype.card σ * M ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
      _ = (n * h) ^ 4 * (Fintype.card σ * M ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
  calc ∑ w : Fin r → Fin 4, GaugeReaderTail.gridSq h
        (GaugeReaderTail.iterDiff h (List.ofFn w) (bundle Ψ))
      ≤ ∑ _w : Fin r → Fin 4, (n * h) ^ 4 * (Fintype.card σ * M ^ 2) :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = _ := by simp [Finset.card_univ, Fintype.card_fun]; ring

end Bundle


/-! ### The time cut-off -/

/-- **A smooth time cut-off** on the time circle `[0, 2π)`: `χ ∈ C^q`, `χ = 0` on `t ≤ a` and on
`t ≥ 2π - a`, with `|χ^{(r)}| ≤ M` for `r ≤ q`.  It renders the periodic four-dimensional reader
applicable to the causal (non-periodic) temporal gauge. -/
structure TimeCutoff (q : ℕ) where
  /-- the cut-off function -/
  χ : ℝ → ℝ
  /-- the margin at both ends -/
  a : ℝ
  a_pos : 0 < a
  smooth : ContDiff ℝ q χ
  vanish : ∀ t, (t ≤ a ∨ 2 * π - a ≤ t) → χ t = 0
  /-- the `C^q` bound -/
  M : ℝ
  deriv_le : ∀ r ≤ q, ∀ t, |iteratedDeriv r χ t| ≤ M

theorem TimeCutoff.M_nonneg {q : ℕ} (c : TimeCutoff q) : 0 ≤ c.M :=
  (abs_nonneg _).trans (c.deriv_le 0 (Nat.zero_le _) 0)

/-- The smooth bump centred at `π` with `χ = 1` on `[π/2, 3π/2]` and support in `[π/4, 7π/4]`. -/
def bump : ContDiffBump (π : ℝ) := ⟨π / 2, 3 * π / 4, by positivity, by nlinarith [Real.pi_pos]⟩

theorem exists_bound_iteratedDeriv_bump (r : ℕ) : ∃ C, ∀ t, |iteratedDeriv r bump t| ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv r (bump : ℝ → ℝ)) := by
    rw [iteratedDeriv_eq_iterate]
    induction r with
    | zero => exact bump.hasCompactSupport
    | succ r ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous
    ((bump.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedDeriv r (by exact_mod_cast le_top))
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

/-- **A concrete cut-off** (non-vacuity of `TimeCutoff`): the smooth bump `bump`, which is `≡ 1`
on `[π/2, 3π/2]`, with margin `a = π/8`. -/
def bumpCutoff (q : ℕ) : TimeCutoff q where
  χ := bump
  a := π / 8
  a_pos := by positivity
  smooth := bump.contDiff
  vanish := by
    intro t ht
    refine bump.zero_of_le_dist ?_
    show 3 * π / 4 ≤ dist t π
    rw [Real.dist_eq]
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith [Real.pi_pos])]; linarith [Real.pi_pos]
    · rw [abs_of_nonneg (by linarith [Real.pi_pos])]; linarith [Real.pi_pos]
  M := ∑ r ∈ range (q + 1), max (Classical.choose (exists_bound_iteratedDeriv_bump r)) 0
  deriv_le := by
    intro r hr t
    have h1 := (Classical.choose_spec (exists_bound_iteratedDeriv_bump r)) t
    have h2 := le_max_left (Classical.choose (exists_bound_iteratedDeriv_bump r)) 0
    have h3 := Finset.single_le_sum (f := fun r => max (Classical.choose
      (exists_bound_iteratedDeriv_bump r)) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hr))
    exact h1.trans (h2.trans h3)

theorem bumpCutoff_eq_one {q : ℕ} {t : ℝ} (ht1 : π / 2 ≤ t) (ht2 : t ≤ 3 * π / 2) :
    (bumpCutoff q).χ t = 1 := by
  refine bump.one_of_mem_closedBall ?_
  show dist t π ≤ π / 2
  rw [Real.dist_eq, abs_le]; constructor <;> linarith

/-! ### The normalized temporal-gauge record -/

section Record

variable {n : ℕ} [NeZero n] {β : Type*}

/-- The normalized temporal links `W_0(j, y)` as a time family. -/
def w0P (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ) :
    ℕ → (Fin 3 → ZMod n) → ℍ :=
  pull (nW gridStep u H 0)

/-- The normalized spatial links `W_k(j, y)` as a time family. -/
def wP (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ) :
    ℕ → Fin 3 → (Fin 3 → ZMod n) → ℍ :=
  fun j k => pull (nW gridStep u H k.succ) j

/-- **The logarithmic link coordinate** `h⁻¹ log W'_k` of the transformed spatial links
`W'_k = g_j W_k ḡ_j⁺` (series branch of the logarithm, `linkCoord_eq_logChart`). -/
def linkCoord (h : ℝ) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ) (k : Fin 3) :
    ℕ → (Fin 3 → ZMod n) → ℍ :=
  fun j y => h⁻¹ • ShiftedPlaquette.logOneAdd (h • aT gridStep h (w0P u H) (wP u H) j k y)

/-- **The components of the normalized temporal-gauge record**: the logarithmic spatial links
`h⁻¹ log W'_k` (`inr k`), the transformed Higgs field `g|H|` (`inl none`) and the transformed matter
fields `g Q^*F_b` (`inl (some b)`); the transformed temporal links are the identity
(`temporal_links_trivial`). -/
def recFam (h : ℝ) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ)
    (Fb : β → (Fin 4 → ZMod n) → ℍ) : Option β ⊕ Fin 3 → ℕ → (Fin 3 → ZMod n) → ℍ
  | Sum.inr k => linkCoord h u H k
  | Sum.inl none => gT (w0P u H) * pull (eta H)
  | Sum.inl (some b) => gT (w0P u H) * pull (nJ gridStep h u H (Fb b) [])

/-- **The read record**: the normalized temporal-gauge record after the time cut-off `χ`, lifted
to the periodic grid and bundled in `EuclideanSpace ℂ`. -/
def readerRecord [Fintype β] (h : ℝ) (χ : ℝ → ℝ) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ)
    (H : (Fin 4 → ZMod n) → ℍ) (Fb : β → (Fin 4 → ZMod n) → ℍ) :
    (Fin 4 → ZMod n) → EuclideanSpace ℂ ((Option β ⊕ Fin 3) × Fin 2) :=
  bundle fun c => lift (sampled h χ * recFam h u H Fb c)

theorem norm_nW {u : (Fin 4 → ZMod n) → Fin 4 → ℍ} {H : (Fin 4 → ZMod n) → ℍ}
    (hu : ∀ x i, ‖u x i‖ = 1) (hH : ∀ x, H x ≠ 0) (i : Fin 4) (x : Fin 4 → ZMod n) :
    ‖nW gridStep u H i x‖ = 1 := by
  simp only [nW, norm_mul, Quaternion.norm_star, norm_qf (hH x), norm_qf (hH _), hu, one_mul]

/-- The causal gauge sets the transformed temporal links to the identity:
`g_j W_0(j) ḡ_{j+1} = 1`. -/
theorem temporal_links_trivial {u : (Fin 4 → ZMod n) → Fin 4 → ℍ} {H : (Fin 4 → ZMod n) → ℍ}
    (hu : ∀ x i, ‖u x i‖ = 1) (hH : ∀ x, H x ≠ 0) (j : ℕ) (y : Fin 3 → ZMod n) :
    gT (w0P u H) j y * w0P u H j y * star (gT (w0P u H) (j + 1) y) = 1 := by
  have hw0 : ∀ j y, ‖w0P u H j y‖ = 1 := fun j y => norm_nW hu hH 0 _
  rw [show gT (w0P u H) (j + 1) y = gT (w0P u H) j y * w0P u H j y from rfl]
  exact unit_mul_star (by rw [norm_mul, norm_gT hw0, hw0, one_mul])

/-- The link coordinate is `h⁻¹` times the analytic logarithm of the transformed link. -/
theorem linkCoord_eq_logChart (h : ℝ) (hh : h ≠ 0) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ)
    (H : (Fin 4 → ZMod n) → ℍ) (k : Fin 3) (j : ℕ) (y : Fin 3 → ZMod n) :
    linkCoord h u H k j y =
      h⁻¹ • SeriesLogChart.logChart (wT gridStep (w0P u H) (wP u H) j k y) := by
  simp only [linkCoord, SeriesLogChart.logChart, aT, smul_smul, mul_inv_cancel₀ hh, one_smul]

/-- On the chart `‖W' - 1‖ < 1`, `exp(h · linkCoord) = W'`: the coordinate is the logarithm. -/
theorem exp_linkCoord (h : ℝ) (hh : h ≠ 0) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ)
    (H : (Fin 4 → ZMod n) → ℍ) (k : Fin 3) (j : ℕ) (y : Fin 3 → ZMod n)
    (hc : ‖wT gridStep (w0P u H) (wP u H) j k y - 1‖ < 1) :
    NormedSpace.exp (h • linkCoord h u H k j y) = wT gridStep (w0P u H) (wP u H) j k y := by
  rw [linkCoord_eq_logChart h hh, smul_smul, mul_inv_cancel₀ hh, one_smul,
    SeriesLogChart.exp_logChart hc]

/-- Where the cut-off equals one, the read record is the normalized temporal-gauge record. -/
theorem readerRecord_eq_of_cutoff_one [Fintype β] (h : ℝ) (χ : ℝ → ℝ)
    (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ) (Fb : β → (Fin 4 → ZMod n) → ℍ)
    (x : Fin 4 → ZMod n) (hx : χ ((x 0).val * h) = 1) :
    readerRecord h χ u H Fb x = bundle (fun c => lift (recFam h u H Fb c)) x := by
  simp only [readerRecord, bundle, lift, sampled, Pi.mul_apply, hx, Quaternion.coe_one, one_mul]

end Record

theorem jetEnergy_mono {ι V : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (h : ℝ)
    (ρU : (ι → ZMod n) → ι → V →L[ℝ] V) (L : ℕ) (F : (ι → ZMod n) → V) :
    jetEnergy h ρU L F ≤ jetEnergy h ρU (L + 1) F := by
  unfold jetEnergy
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (Nat.le_succ _)) fun _ _ _ => ?_)
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _


/-! ### Assembly -/

section Main

variable {n : ℕ} [NeZero n] {β : Type*}

/-- The record constant. -/
def recC (A Am T : ℝ) (q : ℕ) : ℝ :=
  max (2 * gC A T q q) (max (2 ^ q * (gC A T q q * A)) (2 ^ q * (gC A T q q * Am)))

theorem a0F_w0P (h : ℝ) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ) :
    a0F h (w0P u H) = pull (na gridStep h u H 0) := rfl

theorem aSF_wP (h : ℝ) (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ)
    (k : Fin 3) : aSF h (wP u H) k = pull (na gridStep h u H k.succ) := rfl

/-- **Mixed bounds of the normalized temporal-gauge record** on a window `[0, N]`, `Nh ≤ T`, from
`C_h^{q+1}` bounds `A` of the normalized links, `C_h^q` bounds of `|H|` (`A`) and of the
normalized matter fields (`A_m`), when `h 2^q gC ≤ 1/2` (logarithmic chart). -/
theorem recFam_TB {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) {u : (Fin 4 → ZMod n) → Fin 4 → ℍ}
    {H : (Fin 4 → ZMod n) → ℍ} (hu : ∀ x i, ‖u x i‖ = 1) (hH0 : ∀ x, H x ≠ 0)
    {Fb : β → (Fin 4 → ZMod n) → ℍ} {q : ℕ} {A Am T : ℝ} (hA : 0 ≤ A) (hAm : 0 ≤ Am)
    (hT : 0 ≤ T) (hna : ∀ i, Bnd gridStep h (q + 1) (na gridStep h u H i) A)
    (heta : Bnd gridStep h q (eta H) A) (hmat : ∀ b, Bnd gridStep h q (nJ gridStep h u H (Fb b) []) Am)
    {N : ℕ} (hN : (N : ℝ) * h ≤ T) (hsmall : h * (2 ^ q * gC A T q q) ≤ 1 / 2) :
    ∀ c, TB gridStep h N q (recFam h u H Fb c) (recC A Am T q) := by
  have hw0 : ∀ j x, ‖w0P u H j x‖ = 1 := fun j x => norm_nW hu hH0 0 _
  have hw : ∀ j k x, ‖wP u H j k x‖ = 1 := fun j k x => norm_nW hu hH0 k.succ _
  have ha0 : ∀ N, TB gridStep h N (q + 1) (a0F h (w0P u H)) A := fun N => by
    rw [a0F_w0P]; exact TB_pull (q + 1) (hna 0) N
  have haS : ∀ k N, TB gridStep h N (q + 1) (aSF h (wP u H) k) A := fun k N => by
    rw [aSF_wP]; exact TB_pull (q + 1) (hna k.succ) N
  obtain ⟨hg, hat⟩ := temporal_TB hh0 hh1 hw0 hw hA hT ha0 haS q le_rfl N hN
  have hG := gC_nonneg (T := T) hA q q
  intro c
  rcases c with (_ | b) | k
  · exact (TB_mul q hG hA hg (TB_pull q heta N)).mono
      (le_max_of_le_right (le_max_left _ _))
  · exact (TB_mul q hG hAm hg (TB_pull q (hmat b) N)).mono
      (le_max_of_le_right (le_max_right _ _))
  · exact (TB_logChart hh0 hG (hat k) (by linarith)).mono (le_max_left _ _)

theorem recC_nonneg {A Am T : ℝ} (hA : 0 ≤ A) (q : ℕ) : 0 ≤ recC A Am T q :=
  le_max_of_le_left (by have := gC_nonneg (T := T) hA q q; linarith)

/-- **The bounded all-mode reader energy** (`cor:gauge-robust-reader`, energy form): for `q`,
`ρ_* > 0`, `R ≥ 0`, a time cut-off `χ` and finitely many matter fields there are `n₀` and `E`
(depending only on `q, ρ_*, R, χ, |β|`) such that for every `n ≥ n₀`, unit links, `|H| ≥ ρ_*`,
`J_{h,q+5}(H;U) ≤ R` and `J_{h,q+3}(F_b;U) ≤ R`, the discrete `H^q` difference energy of the
cut-off normalized temporal-gauge record is at most `E`. -/
theorem readerRecord_energy {q : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) (cut : TimeCutoff q)
    (β : Type*) [Fintype β] :
    ∃ n₀ : ℕ, ∃ E : ℝ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ)
        (Fb : β → (Fin 4 → ZMod n) → ℍ),
        (∀ x i, ‖u x i‖ = 1) → (∀ x, ρ ≤ ‖H x‖) →
        jetEnergy (2 * π / n) (rhoL u) (q + 5) H ≤ R →
        (∀ b, jetEnergy (2 * π / n) (rhoL u) (q + 3) (Fb b) ≤ R) →
          GaugeReaderTail.diffEnergy (2 * π / n) q (readerRecord (2 * π / n) cut.χ u H Fb) ≤ E := by
  set B₀ := embC (2 * π) * R with hB₀
  have hB₀0 : 0 ≤ B₀ := mul_nonneg (embC_nonneg (by positivity)) hR
  set A := hierC ρ B₀ (q + 2) with hAdef
  have hA : 0 ≤ A := hierC_nonneg ρ B₀ hρ hB₀0 _
  set Am := matC ρ B₀ B₀ q with hAmdef
  have hAm : 0 ≤ Am := matC_nonneg ρ B₀ hB₀0 q
  set T : ℝ := 2 * π + 1 with hTdef
  have hT : 0 ≤ T := by positivity
  set G := gC A T q q with hGdef
  have hG : 0 ≤ G := gC_nonneg hA q q
  set Mrec := recC A Am T q with hMrec
  have hMrec0 : 0 ≤ Mrec := recC_nonneg hA q
  set M := 2 ^ q * (cut.M * Mrec) with hMdef
  have hM0 : 0 ≤ M := by have := cut.M_nonneg; positivity
  set card : ℝ := (Fintype.card (Option β ⊕ Fin 3) : ℝ) with hcard
  set S : ℝ := ∑ r ∈ range (q + 1), (4 : ℝ) ^ r with hS
  set D : ℝ := 2 * π + 2 * π * q + 4 * π * (2 ^ q * G) + 2 * π * (q + 1) / cut.a with hD
  refine ⟨⌈D⌉₊ + 1, (2 * π) ^ 4 * (card * M ^ 2) * S, fun n _ hn u H Fb hu hH hJH hJF => ?_⟩
  -- the mesh
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hDn : D ≤ n := by
    have h1 : (⌈D⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith [Nat.le_ceil D]
  rw [hD] at hDn
  have hπ := Real.pi_pos
  have ha := cut.a_pos
  have hpos1 : 0 ≤ 2 * π * q := by positivity
  have hpos2 : 0 ≤ 4 * π * (2 ^ q * G) := by positivity
  have hpos3 : 0 ≤ 2 * π * (q + 1) / cut.a := by positivity
  set h := 2 * π / n with hhdef
  have hh0 : 0 < h := by positivity
  have hnh : (n : ℝ) * h = 2 * π := by rw [hhdef]; field_simp
  have hh1 : h ≤ 1 := by
    rw [hhdef, div_le_one hn0]; linarith
  have hqh : (q : ℝ) * h ≤ 1 := by
    rw [hhdef, ← mul_div_assoc, div_le_one hn0]; linarith
  have hsmall : h * (2 ^ q * G) ≤ 1 / 2 := by
    rw [hhdef, div_mul_eq_mul_div, div_le_iff₀ hn0]; linarith
  have hqa : ((q : ℝ) + 1) * h ≤ cut.a := by
    have : 2 * π * (q + 1) / cut.a ≤ n := by linarith
    rw [div_le_iff₀ ha] at this
    rw [hhdef, ← mul_div_assoc, div_le_iff₀ hn0]; linarith
  -- the normalized reader
  have hH0 : ∀ x, H x ≠ 0 := fun x h0 => by
    have := hH x; rw [h0, norm_zero] at this; linarith
  have hJH5 : jetEnergy h (rhoL u) (q + 1 + 4) H ≤ R := by
    rw [show q + 1 + 4 = q + 5 by omega]; exact hJH
  have hJH4 : jetEnergy h (rhoL u) (q + 4) H ≤ R :=
    (jetEnergy_mono h (rhoL u) (q + 4) H).trans hJH
  obtain ⟨hη, hna, -⟩ := gauge_normalized_reader (ι := Fin 4) (n := n) (by simp) hh0 hh1 hu hρ hH
    (s := q + 1) hR hJH5 (β := Empty) (fun b => b.elim) (fun b => b.elim)
  obtain ⟨-, -, hmat⟩ := gauge_normalized_reader (ι := Fin 4) (n := n) (by simp) hh0 hh1 hu hρ hH
    (s := q) hR hJH4 Fb hJF
  rw [hnh] at hη hna hmat
  have hrec := recFam_TB (Fb := Fb) hh0 hh1 hu hH0 hA hAm hT hna (hη.of_le (by omega)) hmat
    (N := n + q) (by push_cast; nlinarith) hsmall
  -- the cut-off
  have hχ : TB gridStep h (n + q) q (sampled (Y := Fin 3 → ZMod n) h cut.χ) cut.M :=
    TB_sampled hh0 (n + q) q cut.χ fun r hr t =>
      abs_iterDQ_le hh0 r cut.χ (cut.smooth.of_le (by exact_mod_cast hr)) (cut.deriv_le r hr) t
  have hprod : ∀ c, TB gridStep h (n + q) q (sampled h cut.χ * recFam h u H Fb c) M := fun c =>
    TB_mul q cut.M_nonneg hMrec0 hχ (hrec c)
  have hvan : ∀ c, ∀ j, (j ≤ q ∨ n ≤ j + q + 1) →
      (sampled h cut.χ * recFam h u H Fb c : ℕ → (Fin 3 → ZMod n) → ℍ) j = 0 := by
    intro c j hj
    have hz : cut.χ (j * h) = 0 := by
      refine cut.vanish _ ?_
      rcases hj with hj | hj
      · left
        have : (j : ℝ) ≤ q := by exact_mod_cast hj
        nlinarith
      · right
        have : (n : ℝ) ≤ j + q + 1 := by exact_mod_cast hj
        nlinarith
    funext y
    simp [sampled, hz]
  have hlift : ∀ c, Bnd gridStep h q (lift (sampled h cut.χ * recFam h u H Fb c)) M := fun c =>
    Bnd_lift q hM0 le_rfl (hprod c) (hvan c)
  -- energy and tail
  have hE := diffEnergy_le hh0.le hlift
  rw [hnh] at hE
  exact hE

/-- **`cor:gauge-robust-reader`** (weak sector, quaternion model of `SU(2)` on `ℂ²`, disclosed time
cut-off).  Let `q > m + 2`, `ρ_* > 0`, `R ≥ 0`, a time cut-off `χ` (`TimeCutoff q`) and a finite set
`β` of matter fields.  There are `n₀` and `C` — depending only on `q, m, ρ_*, R, χ, |β|` — such that
for every grid `(ℤ/n)⁴` of side `2π` with `n ≥ n₀` (`h = 2π/n`), all unit links `u`, every Higgs
field with `|H| ≥ ρ_*` and all matter fields `F_b` with covariant-jet energies
`J_{h,q+5}(H;U) ≤ R`, `J_{h,q+3}(F_b;U) ≤ R`, the reader tail of the normalized causal
temporal-gauge record (logarithmic transformed spatial links, transformed Higgs and matter fields,
read after the time cut-off) obeys `τ_{h,m}(K) ≤ C K^{2-q}` for all `1 ≤ K ≤ r`, `2r < n`.  No
derivative of the original frame and no smallness of the original links is assumed. -/
theorem gauge_robust_reader {q m : ℕ} (hqm : (m : ℝ) + 2 < q) {ρ R : ℝ} (hρ : 0 < ρ)
    (hR : 0 ≤ R) (cut : TimeCutoff q) (β : Type*) [Fintype β] :
    ∃ n₀ : ℕ, ∃ C : ℝ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ)
        (Fb : β → (Fin 4 → ZMod n) → ℍ),
        (∀ x i, ‖u x i‖ = 1) → (∀ x, ρ ≤ ‖H x‖) →
        jetEnergy (2 * π / n) (rhoL u) (q + 5) H ≤ R →
        (∀ b, jetEnergy (2 * π / n) (rhoL u) (q + 3) (Fb b) ≤ R) →
        ∀ r K : ℕ, 2 * r < n → 1 ≤ K → K ≤ r →
          SobolevReader.tail (SobolevReader.box r) m K
            (GaugeReaderTail.coefMode (readerRecord (2 * π / n) cut.χ u H Fb)) ≤
            C * (K : ℝ) ^ (2 - (q : ℝ)) := by
  obtain ⟨n₀, E, hE⟩ := readerRecord_energy (q := q) hρ hR cut β
  refine ⟨n₀, Real.sqrt (80 * 25 ^ m / (2 * q - 2 * m - 4)) *
    Real.sqrt ((π ^ 2 / 2) ^ q / (2 * π) ^ 4 * E),
    fun n _ hn u H Fb hu hH hJH hJF r K hr hK hKr => ?_⟩
  have htail := GaugeReaderTail.tail_le_diffEnergy (n := n) (h := 2 * π / n) rfl hr hqm hK hKr
    (readerRecord (2 * π / n) cut.χ u H Fb)
  have h2 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hE n hn u H Fb hu hH hJH hJF)
    (by positivity : (0 : ℝ) ≤ (π ^ 2 / 2) ^ q / (2 * π) ^ 4))
  calc _ ≤ _ := htail
    _ ≤ Real.sqrt (80 * 25 ^ m / (2 * q - 2 * m - 4)) * (K : ℝ) ^ (2 - (q : ℝ)) *
        Real.sqrt ((π ^ 2 / 2) ^ q / (2 * π) ^ 4 * E) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- **The bounded all-mode `H^q` reader** (`cor:gauge-robust-reader`): under the hypotheses of
`gauge_robust_reader`, `Σ_{|ℓ|_∞ ≤ r} (1 + |ℓ|²)^q ‖ξ̂(ℓ)‖² ≤ C` for the cut-off normalized
temporal-gauge record, with `C` independent of `n` and of the links. -/
theorem gauge_robust_sobolev {q : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) (cut : TimeCutoff q)
    (β : Type*) [Fintype β] :
    ∃ n₀ : ℕ, ∃ C : ℝ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ (u : (Fin 4 → ZMod n) → Fin 4 → ℍ) (H : (Fin 4 → ZMod n) → ℍ)
        (Fb : β → (Fin 4 → ZMod n) → ℍ),
        (∀ x i, ‖u x i‖ = 1) → (∀ x, ρ ≤ ‖H x‖) →
        jetEnergy (2 * π / n) (rhoL u) (q + 5) H ≤ R →
        (∀ b, jetEnergy (2 * π / n) (rhoL u) (q + 3) (Fb b) ≤ R) →
        ∀ r : ℕ, 2 * r < n →
          SobolevReader.sobolevSq (SobolevReader.box r) q
            (GaugeReaderTail.coefMode (readerRecord (2 * π / n) cut.χ u H Fb)) ≤ C := by
  obtain ⟨n₀, E, hE⟩ := readerRecord_energy (q := q) hρ hR cut β
  refine ⟨n₀, (π ^ 2 / 2) ^ q / (2 * π) ^ 4 * E, fun n _ hn u H Fb hu hH hJH hJF r hr => ?_⟩
  have := GaugeReaderTail.sobolevSq_le_diffEnergy (n := n) (h := 2 * π / n) rfl hr q
    (readerRecord (2 * π / n) cut.χ u H Fb)
  exact this.trans (mul_le_mul_of_nonneg_left (hE n hn u H Fb hu hH hJH hJF) (by positivity))

end Main

/-! ### Non-vacuity -/

section NonVacuity

variable {n : ℕ} [NeZero n]

theorem covWord_const_trivial (h : ℝ) (c : ℍ) : ∀ (I : List (Fin 4)), I ≠ [] →
    covWord h (rhoL (n := n) fun _ _ => (1 : ℍ)) I (fun _ => c) = fun _ => 0
  | [], hI => absurd rfl hI
  | [i], _ => by
    funext x
    simp [covWord, WeakReader.covDiff, WeakReader.covShift, rhoL]
  | i :: j :: I, _ => by
    have ih := covWord_const_trivial h c (j :: I) (List.cons_ne_nil _ _)
    simp only [covWord] at ih ⊢
    rw [ih]
    funext x
    simp [WeakReader.covDiff, WeakReader.covShift, rhoL]

/-- The trivial configuration (unit links, `H ≡ 1`) has covariant jet energy `(nh)²` at every
order. -/
theorem jetEnergy_trivial (h : ℝ) (hh : 0 ≤ h) (L : ℕ) :
    jetEnergy h (rhoL (n := n) fun _ _ => (1 : ℍ)) L (fun _ : Fin 4 → ZMod n => (1 : ℍ)) =
      ((n : ℝ) * h) ^ 2 := by
  unfold jetEnergy
  rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun ℓ _ => Finset.sum_eq_zero fun I _ => by
    rw [covWord_const_trivial h 1 (List.ofFn I) (by simp)]
    simp [gridL2Norm, periodicHodgeNormSq])]
  simp only [zero_add, Finset.univ_unique, Finset.sum_singleton]
  have hI : ∀ I : Fin 0 → Fin 4, List.ofFn I = [] := fun I => by simp
  rw [hI]
  simp only [covWord, gridL2Norm, periodicHodgeNormSq, norm_one, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Real.sq_sqrt (by positivity), Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  push_cast
  ring

/-- **Non-vacuity of `gauge_robust_reader`**: with `R = 4π²` (the jet energy of the trivial
configuration on the grid of side `2π`), the bump cut-off and no matter field, the theorem applies
to the trivial configuration (unit links, `H ≡ 1`) on every sufficiently fine grid. -/
example : ∃ n₀ : ℕ, ∃ C : ℝ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ r K : ℕ, 2 * r < n → 1 ≤ K →
    K ≤ r → SobolevReader.tail (SobolevReader.box r) 1 K (GaugeReaderTail.coefMode
      (readerRecord (2 * π / n) (bumpCutoff 4).χ (fun (_ : Fin 4 → ZMod n) _ => (1 : ℍ))
        (fun _ => (1 : ℍ)) (fun b : Empty => b.elim))) ≤ C * (K : ℝ) ^ (2 - ((4 : ℕ) : ℝ)) := by
  obtain ⟨n₀, C, hC⟩ := gauge_robust_reader (q := 4) (m := 1) (by norm_num) (ρ := 1)
    (R := (2 * π) ^ 2) one_pos (by positivity) (bumpCutoff 4) Empty
  refine ⟨n₀, C, fun n _ hn r K hr hK hKr => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnh : (n : ℝ) * (2 * π / n) = 2 * π := by field_simp
  refine hC n hn _ _ _ (fun _ _ => by simp) (fun _ => by simp) ?_ (fun b => b.elim) r K hr hK hKr
  rw [jetEnergy_trivial _ (by positivity), hnh]

end NonVacuity
end RenewalGeometry.GaugeRobustReader
