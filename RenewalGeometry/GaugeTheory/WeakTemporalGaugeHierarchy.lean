/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.WeakNormalizedReaderHierarchy

/-!
# Higher-order control of the causal temporal gauge (`eq:gauge-temporal`, all orders)

Clause of `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript, `app:gauge-reader`:
"The algebraic Higgs frame need not be temporal gauge.  Starting with `g_{0,x} = I` and defining
causally `g_{j+1,x} = g_{j,x} W_0(j,x)` sets the transformed temporal links to the identity.
Iterated product rules and discrete Gronwall show that one additional covariant derivative
controls the transformed spatial logarithmic links through order `s` on a fixed physical-time
interval.  All transformed matter fields retain the same order of control").

Quaternion model of `WeakNormReader` (unit quaternions acting on `ℍ ≅ ℂ²`).  Time steps `j : ℕ`,
spatial sites in any additive group `Y` with spatial steps `e_k`; the normalized temporal links
`w₀(j, x)` and spatial links `w_k(j, x)` are unit quaternions, `a_k = h⁻¹(w_k - 1)`.

* `gT` (the causal gauge `g_0 = 1`, `g_{j+1} = g_j w₀(j)`), `wT` (the transformed spatial links
  `w'_k = g_j w_k g_j(x + e_k)⁻¹`), `aT = h⁻¹(w' - 1)`, `plaq` (the temporal–spatial plaquette),
  `pT = h⁻¹(P - 1)`.
* Exact identities: `aT_succ` (`a'(j+1) = a'(j) + g p ḡ w'(j)`), `dlt_gT`
  (`δ_k g_j = w̄'_k(g a_k - a'_k g)`, no loss of derivatives), `aT_zero` (`a'(0) = a(0)`),
  and the plaquette expansion `pT_eq` (`p = h(δ_t a_k - δ_k a_0 + a_0 a_k⁺ - a_k T_k a_0) T_kw̄₀ w̄_k`:
  one additional derivative of the normalized links controls `p/h`).
* **`temporal_hierarchy`** — if `‖a_k(j)‖_{C_h^K} ≤ A` and `‖p(j)‖_{C_h^K} ≤ hP` (spatial
  difference norms) for `jh ≤ T`, then `‖g_j‖_{C_h^K}` and `‖a'_k(j)‖_{C_h^K}` are bounded on
  `jh ≤ T` by a constant depending only on `K, A, P, T` (discrete Grönwall order by order), with
  no smallness of the original links; `pT_bound` derives the plaquette hypothesis from `C^{K}`
  bounds of the normalized links and of their first temporal differences.

Disclosed: the link coordinate is `h⁻¹(W' - 1)` (not `h⁻¹ log W'`), `0 < h ≤ 1`; spatial
difference norms on each time slice.
-/

open Finset

noncomputable section

namespace RenewalGeometry.WeakTemporalGauge

open scoped Quaternion
open WeakNormReader

set_option linter.unusedSectionVars false

variable {Y κ : Type*} [AddCommGroup Y] (e : κ → Y) (h : ℝ)
variable (w0 : ℕ → Y → ℍ) (w : ℕ → κ → Y → ℍ)

/-- The causal temporal gauge `g_0 = 1`, `g_{j+1} = g_j w₀(j)`. -/
def gT : ℕ → Y → ℍ
  | 0 => fun _ => 1
  | j + 1 => fun x => gT j x * w0 j x

/-- The transformed spatial links `w'_k(j, x) = g_j(x) w_k(j, x) ḡ_j(x + e_k)`. -/
def wT (j : ℕ) (k : κ) : Y → ℍ := fun x => gT w0 j x * w j k x * star (gT w0 j (x + e k))

/-- `a'_k = h⁻¹(w'_k - 1)`. -/
def aT (j : ℕ) (k : κ) : Y → ℍ := fun x => h⁻¹ • (wT e w0 w j k x - 1)

/-- `a_k = h⁻¹(w_k - 1)`. -/
def aS (j : ℕ) (k : κ) : Y → ℍ := fun x => h⁻¹ • (w j k x - 1)

/-- `a_0 = h⁻¹(w₀ - 1)`. -/
def a0 (j : ℕ) : Y → ℍ := fun x => h⁻¹ • (w0 j x - 1)

/-- The temporal–spatial plaquette `P = w₀ w_k(j+1) T_kw̄₀ w̄_k`. -/
def plaq (j : ℕ) (k : κ) : Y → ℍ :=
  fun x => w0 j x * w (j + 1) k x * star (w0 j (x + e k)) * star (w j k x)

/-- `p = h⁻¹(P - 1)`. -/
def pT (j : ℕ) (k : κ) : Y → ℍ := fun x => h⁻¹ • (plaq e w0 w j k x - 1)

variable {e h w0 w}

theorem unit_mul_star {q : ℍ} (hq : ‖q‖ = 1) : q * star q = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hq, mul_one]; rfl

theorem unit_star_mul {q : ℍ} (hq : ‖q‖ = 1) : star q * q = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hq, mul_one]; rfl

theorem norm_gT (hw0 : ∀ j x, ‖w0 j x‖ = 1) : ∀ j x, ‖gT w0 j x‖ = 1
  | 0, _ => by simp [gT]
  | j + 1, x => by rw [gT, norm_mul, norm_gT hw0 j x, hw0, one_mul]

theorem norm_wT (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (j : ℕ) (k : κ)
    (x : Y) : ‖wT e w0 w j k x‖ = 1 := by
  rw [wT, norm_mul, norm_mul, Quaternion.norm_star, norm_gT hw0, norm_gT hw0, hw, one_mul,
    one_mul]

/-- `a'(0) = a(0)`: the gauge starts at the identity. -/
theorem aT_zero (k : κ) : aT e h w0 w 0 k = aS h w 0 k := by
  funext x; simp [aT, aS, wT, gT]

theorem unit_cancel {q : ℍ} (hq : ‖q‖ = 1) (X : ℍ) : star q * (q * X) = X := by
  rw [← mul_assoc, unit_star_mul hq, one_mul]

theorem unit_cancel' {q : ℍ} (hq : ‖q‖ = 1) (X : ℍ) : q * (star q * X) = X := by
  rw [← mul_assoc, unit_mul_star hq, one_mul]

/-- **The exact recursion of the transformed spatial links**:
`a'(j+1) = a'(j) + g_j p ḡ_j w'(j)`. -/
theorem aT_succ (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (j : ℕ) (k : κ) :
    aT e h w0 w (j + 1) k =
      aT e h w0 w j k + gT w0 j * pT e h w0 w j k * (star ∘ gT w0 j) * wT e w0 w j k := by
  funext x
  have c1 := unit_cancel (norm_gT hw0 j x)
  have c2 := unit_cancel (hw j k x)
  have c3 := unit_star_mul (norm_gT hw0 j x)
  have c4 := unit_star_mul (hw j k x)
  simp only [aT, wT, pT, plaq, gT, Pi.add_apply, Pi.mul_apply, Function.comp_apply, star_mul,
    smul_mul_assoc, mul_smul_comm, ← smul_add]
  congr 1
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, c1, c2, c3, c4]
  abel

/-- **Spatial differences of the gauge transformation** (no loss of derivatives):
`δ_k g_j = w̄'_k (g_j a_k - a'_k g_j)`. -/
theorem dlt_gT (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (j : ℕ) (k : κ) :
    dlt e h k (gT w0 j) =
      (star ∘ wT e w0 w j k) * (gT w0 j * aS h w j k - aT e h w0 w j k * gT w0 j) := by
  funext x
  have c1 := unit_cancel (norm_gT hw0 j x)
  have c2 := unit_cancel (hw j k x)
  have c3 := unit_star_mul (norm_gT hw0 j x)
  have c4 := unit_star_mul (hw j k x)
  have c5 := unit_star_mul (norm_gT hw0 j (x + e k))
  have c6 := unit_cancel (norm_gT hw0 j (x + e k))
  have c7 := unit_cancel' (norm_gT hw0 j (x + e k))
  simp only [dlt, aS, aT, wT, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, star_mul,
    star_star, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  congr 1
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, c1, c2, c3, c4, c6, c7]
  abel


/-- **The plaquette expansion**: `p = h⁻¹(P - 1) = h (δ_t a_k - δ_k a_0 + a_0 a_k⁺ - a_k T_ka_0)
T_kw̄₀ w̄_k`, so that `p/h` is controlled by one additional derivative of the normalized links. -/
theorem pT_eq (hh : h ≠ 0) (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) (j : ℕ)
    (k : κ) :
    pT e h w0 w j k = h • ((h⁻¹ • (aS h w (j + 1) k - aS h w j k) - dlt e h k (a0 h w0 j) +
      a0 h w0 j * aS h w (j + 1) k - aS h w j k * sh e k (a0 h w0 j)) *
        (star ∘ sh e k (w0 j)) * (star ∘ w j k)) := by
  funext x
  have hu : w j k x * w0 j (x + e k) * star (w0 j (x + e k)) * star (w j k x) = 1 := by
    rw [mul_assoc (w j k x), unit_mul_star (hw0 j (x + e k)), mul_one, unit_mul_star (hw j k x)]
  have key : h⁻¹ • (w0 j x * w (j + 1) k x * star (w0 j (x + e k)) * star (w j k x) - 1) =
      h • ((h⁻¹ • (h⁻¹ • (w (j + 1) k x - 1) - h⁻¹ • (w j k x - 1)) -
        h⁻¹ • (h⁻¹ • (w0 j (x + e k) - 1) - h⁻¹ • (w0 j x - 1)) +
        h⁻¹ • (w0 j x - 1) * h⁻¹ • (w (j + 1) k x - 1) -
        h⁻¹ • (w j k x - 1) * h⁻¹ • (w0 j (x + e k) - 1)) * star (w0 j (x + e k)) *
          star (w j k x)) +
      h⁻¹ • (w j k x * w0 j (x + e k) * star (w0 j (x + e k)) * star (w j k x) - 1) := by
    simp only [smul_sub, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub,
      add_mul, one_mul, mul_one]
    field_simp
    module
  rw [hu, sub_self, smul_zero, add_zero] at key
  simp only [pT, plaq, aS, a0, dlt, sh, Pi.mul_apply, Pi.sub_apply, Pi.add_apply,
    Function.comp_apply, Pi.smul_apply]
  exact key

theorem dW_smul : ∀ (α : List κ) (c : ℝ) (f : Y → ℍ), dW e h α (c • f) = c • dW e h α f
  | [], _, _ => rfl
  | i :: α, c, f => by
    have : dlt e h i (c • f) = c • dlt e h i f := by
      funext x; simp only [dlt, Pi.smul_apply, smul_sub, smul_smul, mul_comm c]
    simp only [dW, this, dW_smul α]

theorem Bnd_smul {K : ℕ} {f : Y → ℍ} {B : ℝ} (hf : Bnd e h K f B) (c : ℝ) :
    Bnd e h K (c • f) (|c| * B) := fun α hα x => by
  rw [dW_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf α hα x) (abs_nonneg _)

theorem wT_eq (hh : h ≠ 0) (j : ℕ) (k : κ) :
    wT e w0 w j k = (fun _ => (1 : ℍ)) + h • aT e h w0 w j k := by
  funext x; simp [aT, smul_smul, mul_inv_cancel₀ hh]

theorem aS_eq (hh : h ≠ 0) (j : ℕ) (k : κ) :
    w j k = (fun _ => (1 : ℍ)) + h • aS h w j k := by
  funext x; simp [aS, smul_smul, mul_inv_cancel₀ hh]

/-- `‖1 + h a‖_{C^K} ≤ 1 + h‖a‖_{C^K}`. -/
theorem Bnd_one_add {K : ℕ} {f : Y → ℍ} {B : ℝ} (hh0 : 0 < h) (hf : Bnd e h K f B) :
    Bnd e h K ((fun _ => (1 : ℍ)) + h • f) (1 + h * B) := by
  have h1 := (Bnd_const (e := e) (h := h) K (1 : ℍ)).add (Bnd_smul hf h)
  rw [norm_one, abs_of_pos hh0] at h1
  exact h1

/-- A discrete Grönwall inequality: `m_{j+1} ≤ m_j + hc(1 + m_j)` gives
`1 + m_j ≤ (1 + m_0) e^{c jh}`. -/
theorem gronwall_disc {m : ℕ → ℝ} {h c : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c) (hm0 : ∀ j, 0 ≤ m j)
    (hstep : ∀ j, m (j + 1) ≤ m j + h * c * (1 + m j)) :
    ∀ j : ℕ, 1 + m j ≤ (1 + m 0) * Real.exp (c * (j * h))
  | 0 => by simp
  | j + 1 => by
    have ih := gronwall_disc hh hc hm0 hstep j
    have hmj := hm0 j
    have h1 : 1 + m (j + 1) ≤ (1 + h * c) * (1 + m j) := by nlinarith [hstep j]
    have h2 : 1 + h * c ≤ Real.exp (c * h) := by
      have := Real.add_one_le_exp (c * h); nlinarith
    have hpos : 0 ≤ 1 + h * c := by positivity
    calc 1 + m (j + 1) ≤ (1 + h * c) * (1 + m j) := h1
      _ ≤ Real.exp (c * h) * ((1 + m 0) * Real.exp (c * (j * h))) :=
          mul_le_mul h2 ih (by linarith) (Real.exp_pos _).le
      _ = (1 + m 0) * Real.exp (c * (((j + 1 : ℕ) : ℝ) * h)) := by
          rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; push_cast; ring_nf

/-- **Order-zero control of the transformed links** (no smallness of the links):
`‖a'_k(j)‖_∞ ≤ ‖a_k(0)‖_∞ + j h P` when `‖p‖_∞ ≤ hP`. -/
theorem aT_sup_le (hw0 : ∀ j x, ‖w0 j x‖ = 1) (hw : ∀ j k x, ‖w j k x‖ = 1) {A P : ℝ}
    (hA0 : ∀ k x, ‖aS h w 0 k x‖ ≤ A) (hp : ∀ j k x, ‖pT e h w0 w j k x‖ ≤ h * P) (k : κ) :
    ∀ j : ℕ, ∀ x, ‖aT e h w0 w j k x‖ ≤ A + j * (h * P)
  | 0, x => by rw [aT_zero]; simpa using hA0 k x
  | j + 1, x => by
    rw [aT_succ hw0 hw j k]
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_gT hw0, Quaternion.norm_star, norm_gT hw0,
      norm_wT hw0 hw, one_mul, mul_one, mul_one]
    have := aT_sup_le hw0 hw hA0 hp k j x
    have := hp j k x
    push_cast
    linarith

/-! ### The temporal hierarchy -/

section Hierarchy

variable (A P T : ℝ)

/-- The gauge-difference constant `Γ_k` at level `k` from the level-`k` bound `C`. -/
def gamC (k : ℕ) (C : ℝ) : ℝ :=
  max 1 (2 ^ k * ((1 + C) * (2 ^ k * (C * A) + 2 ^ k * (C * C))))

/-- The Grönwall rate at level `k + 1`. -/
def rateC (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ (k + 1) * (2 ^ (k + 1) * (2 ^ (k + 1) * (gamC A k C * P) * gamC A k C))

/-- The temporal hierarchy constants. -/
def tempC : ℕ → ℝ
  | 0 => max 1 (A + T * P)
  | k + 1 => max (gamC A k (tempC k)) ((1 + A) * Real.exp (rateC A P k (tempC k) * T))

theorem gamC_one_le (k : ℕ) (C : ℝ) : 1 ≤ gamC A k C := le_max_left _ _

theorem tempC_nonneg (hA : 0 ≤ A) : ∀ k, 0 ≤ tempC A P T k
  | 0 => le_max_of_le_left zero_le_one
  | k + 1 => le_max_of_le_left (zero_le_one.trans (gamC_one_le A k _))

/-- The sequence of the Grönwall step. -/
def mseq (h c : ℝ) : ℕ → ℝ
  | 0 => A
  | j + 1 => mseq h c j + h * c * (1 + mseq h c j)

theorem mseq_nonneg {h c : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h) (hc : 0 ≤ c) :
    ∀ j, 0 ≤ mseq A h c j
  | 0 => hA
  | j + 1 => by
    have := mseq_nonneg hA hh hc j
    simp only [mseq]; positivity

variable {A P T}

/-- **Higher-order control of the causal temporal gauge** (`eq:gauge-temporal`, all orders): for
`0 < h ≤ 1`, unit normalized links, spatial `C_h^K` bounds `‖a_k(j)‖_{C^K} ≤ A` of the normalized
spatial links and `‖p(j)‖_{C^K} ≤ hP` of the temporal–spatial plaquette coordinate (one further
derivative of the normalized links, `pT_eq`), the causal gauge `g_j` and the transformed spatial
link coordinates `a'_k(j) = h⁻¹(w'_k - 1)` satisfy `‖g_j‖_{C^{k'}}, ‖a'_k(j)‖_{C^{k'}} ≤ tempC k'`
for all `k' ≤ K` and `jh ≤ T`; the constants depend only on `k', A, P, T` (discrete Grönwall order
by order; no smallness of the original links). -/
theorem temporal_hierarchy (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : ∀ j x, ‖w0 j x‖ = 1)
    (hw : ∀ j k x, ‖w j k x‖ = 1) {K : ℕ} (hA0 : 0 ≤ A) (hP0 : 0 ≤ P) (hT : 0 ≤ T)
    (hA : ∀ j k, Bnd e h K (aS h w j k) A) (hp : ∀ j k, Bnd e h K (pT e h w0 w j k) (h * P)) :
    ∀ k', k' ≤ K → ∀ j : ℕ, (j : ℝ) * h ≤ T →
      Bnd e h k' (gT w0 j) (tempC A P T k') ∧ ∀ k, Bnd e h k' (aT e h w0 w j k) (tempC A P T k') := by
  intro k'
  induction k' with
  | zero =>
    intro _ j hj
    refine ⟨fun α hα x => ?_, fun k α hα x => ?_⟩
    · have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
      subst this
      simp only [dW, tempC, norm_gT hw0]
      exact le_max_left _ _
    · have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
      subst this
      simp only [dW, tempC]
      have h1 := aT_sup_le hw0 hw (fun k x => (hA 0 k).sup x) (fun j k x => (hp j k).sup x) k j x
      have h2 : (j : ℝ) * (h * P) ≤ T * P := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hj hP0
      exact le_max_of_le_right (by linarith)
  | succ k' ih =>
    intro hk
    set C := tempC A P T k' with hC
    have hC0 : 0 ≤ C := tempC_nonneg A P T hA0 k'
    set Γ := gamC A k' C with hΓ
    have hΓ1 : 1 ≤ Γ := gamC_one_le A k' C
    set c := rateC A P k' C with hc
    have hc0 : 0 ≤ c := by simp only [hc, rateC]; positivity
    -- the gauge at level `k' + 1`
    have hg : ∀ j : ℕ, (j : ℝ) * h ≤ T → Bnd e h (k' + 1) (gT w0 j) Γ := by
      intro j hj
      obtain ⟨ihg, iha⟩ := ih (by omega) j hj
      refine Bnd.succ (fun x => ?_) (fun m => ?_)
      · rw [norm_gT hw0]; exact hΓ1
      · rw [dlt_gT hw0 hw j m]
        have hwT : Bnd e h k' (star ∘ wT e w0 w j m) (1 + C) := by
          rw [wT_eq hh0.ne']
          refine ((Bnd_one_add hh0 (iha m)).star).mono ?_
          nlinarith
        have h1 := Bnd_mul k' hC0 hA0 ihg ((hA j m).of_le (by omega))
        have h2 := Bnd_mul k' hC0 hC0 (iha m) ihg
        have h3 := Bnd_mul k' (by positivity) (by positivity) hwT (h1.sub h2)
        exact h3.mono (le_max_right _ _)
    -- the transformed links at level `k' + 1` (Grönwall)
    have ha : ∀ k, ∀ j : ℕ, (j : ℝ) * h ≤ T → Bnd e h (k' + 1) (aT e h w0 w j k) (mseq A h c j) := by
      intro k j
      induction j with
      | zero =>
        intro _
        rw [aT_zero]
        exact (hA 0 k).of_le hk
      | succ j ihj =>
        intro hj
        have hj' : (j : ℝ) * h ≤ T := by
          have : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h := by
            push_cast; nlinarith
          linarith
        have hm := ihj hj'
        have hm0 := mseq_nonneg A hA0 hh0.le hc0 j
        rw [aT_succ hw0 hw j k]
        have hgj := hg j hj'
        have hpj : Bnd e h (k' + 1) (pT e h w0 w j k) (h * P) := (hp j k).of_le hk
        have hwj : Bnd e h (k' + 1) (wT e w0 w j k) (1 + h * mseq A h c j) := by
          rw [wT_eq hh0.ne']; exact Bnd_one_add hh0 hm
        have e1 := Bnd_mul (k' + 1) (by positivity) (by positivity) hgj hpj
        have e2 := Bnd_mul (k' + 1) (by positivity) (by positivity) e1 hgj.star
        have e3 := Bnd_mul (k' + 1) (by positivity) (by positivity) e2 hwj
        refine (hm.add e3).mono ?_
        have hcdef : c = 2 ^ (k' + 1) * (2 ^ (k' + 1) * (2 ^ (k' + 1) * (Γ * P) * Γ)) := rfl
        have hms : mseq A h c (j + 1) = mseq A h c j + h * c * (1 + mseq A h c j) := rfl
        refine le_trans ?_ hms.symm.le
        have hle : 1 + h * mseq A h c j ≤ 1 + mseq A h c j := by nlinarith
        have e4 : 2 ^ (k' + 1) * (2 ^ (k' + 1) * (2 ^ (k' + 1) * (Γ * (h * P)) * Γ) *
            (1 + h * mseq A h c j)) = h * c * (1 + h * mseq A h c j) := by rw [hcdef]; ring
        rw [e4]
        have := mul_le_mul_of_nonneg_left hle (mul_nonneg hh0.le hc0)
        linarith
    intro j hj
    refine ⟨(hg j hj).mono (le_max_left _ _), fun k => (ha k j hj).mono ?_⟩
    have hgr := gronwall_disc (m := mseq A h c) hh0.le hc0 (mseq_nonneg A hA0 hh0.le hc0)
      (fun j => le_of_eq rfl) j
    simp only [mseq] at hgr
    have hexp : Real.exp (c * (j * h)) ≤ Real.exp (c * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hj hc0)
    have : mseq A h c j ≤ (1 + A) * Real.exp (c * T) := by
      have h1 : (1 + A) * Real.exp (c * (j * h)) ≤ (1 + A) * Real.exp (c * T) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      linarith
    exact this.trans (le_max_right _ _)

end Hierarchy

/-! ### The plaquette hypothesis from the normalized links -/

/-- The plaquette constant. -/
def plaqC (K : ℕ) (A : ℝ) : ℝ :=
  2 ^ K * (2 ^ K * ((A + A + 2 ^ K * (A * A) + 2 ^ K * (A * A)) * (1 + A)) * (1 + A))

/-- **One additional derivative controls the plaquette coordinate**: if the normalized links and
their first temporal differences are bounded in `C_h^K` and the temporal link `a_0` in `C_h^{K+1}`
(all by `A`), then `‖p(j)‖_{C_h^K} ≤ h · plaqC K A` (via the expansion `pT_eq`). -/
theorem pT_bound (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : ∀ j x, ‖w0 j x‖ = 1)
    (hw : ∀ j k x, ‖w j k x‖ = 1) {K : ℕ} {A : ℝ} (hA0 : 0 ≤ A) (j : ℕ) (k : κ)
    (hdt : Bnd e h K (h⁻¹ • (aS h w (j + 1) k - aS h w j k)) A)
    (ha0 : Bnd e h (K + 1) (a0 h w0 j) A) (ha : Bnd e h K (aS h w j k) A)
    (ha' : Bnd e h K (aS h w (j + 1) k) A) :
    Bnd e h K (pT e h w0 w j k) (h * plaqC K A) := by
  rw [pT_eq hh0.ne' hw0 hw j k]
  have hw0e : w0 j = (fun _ => (1 : ℍ)) + h • a0 h w0 j := by
    funext x; simp [a0, smul_smul, mul_inv_cancel₀ hh0.ne']
  have hS1 := (hdt.sub (ha0.diff k)).add (Bnd_mul K hA0 hA0 (ha0.of_le (Nat.le_succ K)) ha')
  have hS := hS1.sub (Bnd_mul K hA0 hA0 ha ((ha0.of_le (Nat.le_succ K)).shift k))
  have hW0 : Bnd e h K (star ∘ sh e k (w0 j)) (1 + A) := by
    rw [hw0e]
    refine ((Bnd_one_add hh0 (ha0.of_le (Nat.le_succ K))).shift k).star.mono ?_
    nlinarith
  have hW : Bnd e h K (star ∘ w j k) (1 + A) := by
    rw [aS_eq (w := w) hh0.ne' j k]
    refine (Bnd_one_add hh0 ha).star.mono ?_
    nlinarith
  have h1 := Bnd_mul K (by positivity) (by positivity) hS hW0
  have h2 := Bnd_mul K (by positivity) (by positivity) h1 hW
  have h3 := Bnd_smul h2 h
  rw [abs_of_pos hh0] at h3
  exact h3.mono (le_of_eq (by unfold plaqC; ring))

/-- **Non-vacuity of `temporal_hierarchy`**: trivial normalized links on `ℤ/3` (one spatial
direction), `h = 1`. -/
example : ∀ j : ℕ, (j : ℝ) * 1 ≤ 1 →
    Bnd (fun _ : Fin 1 => (1 : ZMod 3)) 1 2 (gT (fun (_ : ℕ) (_ : ZMod 3) => (1 : ℍ)) j)
      (tempC 0 0 1 2) := by
  intro j hj
  have hz : ∀ (j : ℕ) (k : Fin 1),
      aS 1 (fun (_ : ℕ) (_ : Fin 1) (_ : ZMod 3) => (1 : ℍ)) j k = fun _ => (0 : ℍ) := by
    intro j k; funext x; simp [aS]
  have hp : ∀ (j : ℕ) (k : Fin 1), pT (fun _ : Fin 1 => (1 : ZMod 3)) 1
      (fun (_ : ℕ) (_ : ZMod 3) => (1 : ℍ))
      (fun (_ : ℕ) (_ : Fin 1) (_ : ZMod 3) => (1 : ℍ)) j k = fun _ => (0 : ℍ) := by
    intro j k; funext x; simp [pT, plaq]
  have hA : ∀ (j : ℕ) (k : Fin 1), Bnd (fun _ : Fin 1 => (1 : ZMod 3)) 1 2
      (aS 1 (fun (_ : ℕ) (_ : Fin 1) (_ : ZMod 3) => (1 : ℍ)) j k) 0 := by
    intro j k
    rw [hz]
    simpa using Bnd_const (e := fun _ : Fin 1 => (1 : ZMod 3)) (h := 1) 2 (0 : ℍ)
  have hP : ∀ (j : ℕ) (k : Fin 1), Bnd (fun _ : Fin 1 => (1 : ZMod 3)) 1 2
      (pT (fun _ : Fin 1 => (1 : ZMod 3)) 1 (fun (_ : ℕ) (_ : ZMod 3) => (1 : ℍ))
        (fun (_ : ℕ) (_ : Fin 1) (_ : ZMod 3) => (1 : ℍ)) j k) (1 * 0) := by
    intro j k
    rw [hp]
    simpa using Bnd_const (e := fun _ : Fin 1 => (1 : ZMod 3)) (h := 1) 2 (0 : ℍ)
  have := temporal_hierarchy (e := fun _ : Fin 1 => (1 : ZMod 3)) (h := 1)
    (w0 := fun (_ : ℕ) (_ : ZMod 3) => (1 : ℍ))
    (w := fun (_ : ℕ) (_ : Fin 1) (_ : ZMod 3) => (1 : ℍ)) one_pos le_rfl
    (fun _ _ => by simp) (fun _ _ _ => by simp) (K := 2) (A := 0) (P := 0) (T := 1) le_rfl le_rfl
    zero_le_one hA hP 2 le_rfl j hj
  exact this.1

end RenewalGeometry.WeakTemporalGauge
