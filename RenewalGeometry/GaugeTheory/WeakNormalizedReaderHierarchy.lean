/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.GaugeCovariantEmbedding

/-!
# The normalized chain-rule hierarchy of the weak-sector reader (`eq:gauge-normalized-reader`)

Clause of `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript, `app:gauge-reader`:
"On a fixed lower-radius chart, repeated finite-difference chain rules therefore give
`J_{h,s+4}(H;U) + Σ_b J_{h,s+3}(F_b;U) ≤ R ⇒ ‖|H|‖_{C_h^{s+1}} + Σ_i ‖h⁻¹ log W_i‖_{C_h^s}
+ Σ_b ‖Q^*F_b‖_{C_h^s} ≤ C_{s,ρ_*,R}`.  No derivative of the original `Q_x` and no smallness of
the original links is assumed").

**Model.** The weak `SU(2)` sector acting on the Higgs doublet `ℂ²` is realised as the unit
quaternions acting on `ℍ ≅ ℂ²` by left multiplication (the fundamental representation,
realified).  The algebraic Higgs frame `Q_x` sending `e_1 = 1` to `H_x/|H_x|` is left
multiplication by the unit quaternion `q_x = H_x/|H_x|`; the normalized links are
`W_i(x) = q̄_x u_i(x) q_{x+e_i}`, `a_i = h⁻¹(W_i - 1)`, the normalized jets `J_I = q̄ D_I^U H`.

## Main results

* Discrete calculus on any additive group of sites with steps `e_i` and values in a normed
  `ℝ`-algebra: `dlt` (forward difference `δ_i`), `dW` (ordered difference words), `Bnd k f B`
  (`‖δ^α f‖_∞ ≤ B` for all words `|α| ≤ k`, i.e. `‖f‖_{C_h^k} ≤ B`), the Leibniz rule
  `dlt_mul`, **`Bnd_mul`** (`C_h^k` is an algebra: `‖fg‖_{C^k} ≤ 2^k‖f‖_{C^k}‖g‖_{C^k}`) and
  **`Bnd_inv`** (the quotient rule in a normed division ring, with denominators `≥ ρ > 0`).
* The exact identities (`eq:gauge-closed` in the quaternion model): `dlt_J`
  (`δ_iJ_I = J_{iI} - a_i T_iJ_I`), `J_nil` (`J_∅ = |H|`), `norm_shift_eq`
  (`|H_{x+e_i}| = | |H_x| + hJ_i(x) |`), `a_eq` (`a_i = (J_i - δ_i|H|)(T_i|H|)⁻¹`) and `dlt_eta`
  (`δ_i|H| = (|H|(J_i + J̄_i) + hJ_iJ̄_i)(T_i|H| + |H|)⁻¹`), which close the ordinary difference
  hierarchy in terms of covariant jets.
* **`normalized_hierarchy`** — for `0 < h ≤ 1`, `|H| ≥ ρ_* > 0` and sup bounds
  `‖D_I^U H‖_∞ ≤ B` (`|I| ≤ L`): `‖|H|‖_{C_h^L}`, `‖a_i‖_{C_h^{L-1}}` and `‖J_I‖_{C_h^{L-|I|}}` are
  bounded by a constant depending only on `L, ρ_*, B` — no derivative of `q_x` and no smallness
  of the links; **`normalized_matter`** — the same for every matter field (`Q^*F_b` in `C_h^{L'}`
  from `‖D_I^U F_b‖_∞ ≤ B`, `|I| ≤ L' ≤ L`).
* **`gauge_normalized_reader`** (`eq:gauge-normalized-reader`, `h⁻¹(W_i - 1)` form) on the periodic
  grid `(ℤ/n)⁴`: `J_{h,s+4}(H;U) ≤ R`, `J_{h,s+3}(F_b;U) ≤ R`, `|H| ≥ ρ_*` imply
  `‖|H|‖_{C_h^{s+1}}, ‖h⁻¹(W_i - 1)‖_{C_h^s}, ‖Q^*F_b‖_{C_h^s} ≤ C(s, ρ_*, R, nh)` (through the
  link-independent embedding `GaugeCovEmbed.gauge_cov_embed_words`).

Disclosed: the link coordinate is `h⁻¹(W_i - 1)` rather than `h⁻¹ log W_i` (the two are uniformly
equivalent on the chart `h‖a_i‖ ≤ c`, `eq:gauge-log-source`; the difference bounds for the
logarithm are not formalised); `0 < h ≤ 1`; the representation is the quaternion model of
`SU(2)` on `ℂ²`.
-/

open Finset

noncomputable section

namespace RenewalGeometry.WeakNormReader

set_option linter.unusedSectionVars false

/-! ### Discrete calculus -/

section Calculus

variable {X ι : Type*} [AddCommGroup X] (e : ι → X) (h : ℝ)
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The shift `T_i f(x) = f(x + e_i)`. -/
def sh (i : ι) (f : X → 𝔸) : X → 𝔸 := fun x => f (x + e i)

/-- The forward difference `δ_i f(x) = h⁻¹(f(x + e_i) - f(x))`. -/
def dlt (i : ι) (f : X → 𝔸) : X → 𝔸 := fun x => h⁻¹ • (f (x + e i) - f x)

/-- Ordered difference words `δ^α`, innermost first: `δ^{i :: α} f = δ^α(δ_i f)`. -/
def dW : List ι → (X → 𝔸) → X → 𝔸
  | [], f => f
  | i :: α, f => dW α (dlt e h i f)

/-- `‖f‖_{C_h^k} ≤ B`: every difference word of length `≤ k` is bounded by `B`. -/
def Bnd (k : ℕ) (f : X → 𝔸) (B : ℝ) : Prop :=
  ∀ α : List ι, α.length ≤ k → ∀ x, ‖dW e h α f x‖ ≤ B

variable {e h}

theorem dW_add : ∀ (α : List ι) (f g : X → 𝔸), dW e h α (f + g) = dW e h α f + dW e h α g
  | [], _, _ => rfl
  | i :: α, f, g => by
    have : dlt e h i (f + g) = dlt e h i f + dlt e h i g := by
      funext x; simp only [dlt, Pi.add_apply]; rw [← smul_add]; congr 1; abel
    simp only [dW, this, dW_add α]

theorem dW_neg : ∀ (α : List ι) (f : X → 𝔸), dW e h α (-f) = -dW e h α f
  | [], _ => rfl
  | i :: α, f => by
    have : dlt e h i (-f) = -dlt e h i f := by
      funext x; simp only [dlt, Pi.neg_apply]; rw [← smul_neg]; congr 1; abel
    simp only [dW, this, dW_neg α]

theorem dW_sub (α : List ι) (f g : X → 𝔸) : dW e h α (f - g) = dW e h α f - dW e h α g := by
  rw [sub_eq_add_neg, dW_add, dW_neg, ← sub_eq_add_neg]

theorem dlt_sh (i j : ι) (f : X → 𝔸) : dlt e h i (sh e j f) = sh e j (dlt e h i f) := by
  funext x; simp only [dlt, sh, add_right_comm]

theorem dW_sh : ∀ (α : List ι) (j : ι) (f : X → 𝔸), dW e h α (sh e j f) = sh e j (dW e h α f)
  | [], _, _ => rfl
  | i :: α, j, f => by simp only [dW, dlt_sh, dW_sh α]

/-- **Discrete Leibniz rule** `δ_i(fg) = δ_if · T_ig + f · δ_ig`. -/
theorem dlt_mul (i : ι) (f g : X → 𝔸) :
    dlt e h i (f * g) = dlt e h i f * sh e i g + f * dlt e h i g := by
  funext x
  simp only [dlt, sh, Pi.mul_apply, Pi.add_apply, smul_mul_assoc, mul_smul_comm, ← smul_add]
  congr 1
  noncomm_ring

theorem Bnd.mono {k : ℕ} {f : X → 𝔸} {B B' : ℝ} (hf : Bnd e h k f B) (hB : B ≤ B') :
    Bnd e h k f B' := fun α hα x => (hf α hα x).trans hB

theorem Bnd.of_le {k k' : ℕ} {f : X → 𝔸} {B : ℝ} (hf : Bnd e h k' f B) (hk : k ≤ k') :
    Bnd e h k f B := fun α hα x => hf α (hα.trans hk) x

theorem Bnd.nonneg {k : ℕ} {f : X → 𝔸} {B : ℝ} [Nonempty X] (hf : Bnd e h k f B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf [] (Nat.zero_le _) (Classical.arbitrary X))

theorem Bnd.sup {k : ℕ} {f : X → 𝔸} {B : ℝ} (hf : Bnd e h k f B) (x : X) : ‖f x‖ ≤ B :=
  hf [] (Nat.zero_le _) x

theorem Bnd.shift {k : ℕ} {f : X → 𝔸} {B : ℝ} (hf : Bnd e h k f B) (j : ι) :
    Bnd e h k (sh e j f) B := fun α hα x => by
  rw [dW_sh]; exact hf α hα _

theorem Bnd.diff {k : ℕ} {f : X → 𝔸} {B : ℝ} (hf : Bnd e h (k + 1) f B) (i : ι) :
    Bnd e h k (dlt e h i f) B := fun α hα x => hf (i :: α) (by simp; omega) x

theorem Bnd.add {k : ℕ} {f g : X → 𝔸} {B₁ B₂ : ℝ} (hf : Bnd e h k f B₁) (hg : Bnd e h k g B₂) :
    Bnd e h k (f + g) (B₁ + B₂) := fun α hα x => by
  rw [dW_add]; exact (norm_add_le _ _).trans (add_le_add (hf α hα x) (hg α hα x))

theorem Bnd.neg {k : ℕ} {f : X → 𝔸} {B : ℝ} (hf : Bnd e h k f B) : Bnd e h k (-f) B :=
  fun α hα x => by rw [dW_neg, Pi.neg_apply, norm_neg]; exact hf α hα x

theorem Bnd.sub {k : ℕ} {f g : X → 𝔸} {B₁ B₂ : ℝ} (hf : Bnd e h k f B₁) (hg : Bnd e h k g B₂) :
    Bnd e h k (f - g) (B₁ + B₂) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- **The difference operator characterisation**: `Bnd (k+1) f B` iff `f` is bounded by `B` and
every first difference is `Bnd k` by `B`. -/
theorem Bnd.succ {k : ℕ} {f : X → 𝔸} {B : ℝ} (h0 : ∀ x, ‖f x‖ ≤ B)
    (h1 : ∀ i, Bnd e h k (dlt e h i f) B) : Bnd e h (k + 1) f B := by
  intro α hα x
  cases α with
  | nil => exact h0 x
  | cons i α => exact h1 i α (by simp at hα; omega) x

/-- **`C_h^k` is a Banach algebra**: `‖fg‖_{C^k} ≤ 2^k ‖f‖_{C^k} ‖g‖_{C^k}`. -/
theorem Bnd_mul : ∀ (k : ℕ) {f g : X → 𝔸} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
    Bnd e h k f B₁ → Bnd e h k g B₂ → Bnd e h k (f * g) (2 ^ k * (B₁ * B₂))
  | 0, f, g, B₁, B₂, h1, h2, hf, hg => by
    intro α hα x
    have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
    subst this
    simp only [dW, pow_zero, one_mul, Pi.mul_apply]
    exact (norm_mul_le _ _).trans (mul_le_mul (hf.sup x) (hg.sup x) (norm_nonneg _) h1)
  | k + 1, f, g, B₁, B₂, h1, h2, hf, hg => by
    refine Bnd.succ (fun x => ?_) (fun i => ?_)
    · refine (norm_mul_le _ _).trans ((mul_le_mul (hf.sup x) (hg.sup x) (norm_nonneg _)
        h1).trans ?_)
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith [mul_nonneg h1 h2]
    · rw [dlt_mul]
      have e1 := Bnd_mul k h1 h2 (hf.diff i) ((hg.of_le (Nat.le_succ k)).shift i)
      have e2 := Bnd_mul k h1 h2 (hf.of_le (Nat.le_succ k)) (hg.diff i)
      refine (e1.add e2).mono (le_of_eq ?_)
      ring

end Calculus


/-! ### The quotient rule -/

section Inverse

variable {X ι : Type*} [AddCommGroup X] {e : ι → X} {h : ℝ}
variable {𝔸 : Type*} [NormedDivisionRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The constant of the quotient rule. -/
def invC (ρ M : ℝ) : ℕ → ℝ
  | 0 => ρ⁻¹
  | k + 1 => max ρ⁻¹ (2 ^ k * (2 ^ k * (invC ρ M k * M) * invC ρ M k))

theorem invC_nonneg {ρ M : ℝ} (hρ : 0 < ρ) : ∀ k, 0 ≤ invC ρ M k
  | 0 => (inv_pos.2 hρ).le
  | k + 1 => le_max_of_le_left (inv_pos.2 hρ).le

theorem invC_mono {ρ M M' : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hMM : M ≤ M') :
    ∀ k, invC ρ M k ≤ invC ρ M' k
  | 0 => le_rfl
  | k + 1 => by
    have ih := invC_mono hρ hM hMM k
    have h0 := invC_nonneg (M := M) hρ k
    simp only [invC]
    refine max_le_max le_rfl ?_
    have : invC ρ M k * M * invC ρ M k ≤ invC ρ M' k * M' * invC ρ M' k := by
      have h1 : invC ρ M k * M ≤ invC ρ M' k * M' := mul_le_mul ih hMM hM (h0.trans ih)
      exact mul_le_mul h1 ih h0 ((mul_nonneg h0 hM).trans h1)
    have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h2]

theorem dlt_inv (i : ι) (g : X → 𝔸) (hg : ∀ x, g x ≠ 0) :
    dlt e h i (fun x => (g x)⁻¹) =
      -((fun x => (g x)⁻¹) * dlt e h i g * sh e i (fun x => (g x)⁻¹)) := by
  funext x
  simp only [dlt, sh, Pi.mul_apply, Pi.neg_apply, smul_mul_assoc, mul_smul_comm, ← smul_neg]
  congr 1
  rw [mul_sub, sub_mul, inv_mul_cancel₀ (hg x), one_mul, mul_assoc, mul_inv_cancel₀ (hg _),
    mul_one]
  abel

/-- **The quotient rule**: if `‖g‖ ≥ ρ > 0` and `‖g‖_{C^k} ≤ M`, then
`‖g⁻¹‖_{C^k} ≤ invC ρ M k`. -/
theorem Bnd_inv {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) {g : X → 𝔸} (hg : ∀ x, ρ ≤ ‖g x‖) :
    ∀ k, Bnd e h k g M → Bnd e h k (fun x => (g x)⁻¹) (invC ρ M k)
  | 0, hb => by
    intro α hα x
    have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
    subst this
    simp only [dW, invC, norm_inv]
    exact inv_anti₀ hρ (hg x)
  | k + 1, hb => by
    have hg0 : ∀ x, g x ≠ 0 := fun x h0 => by
      have := hg x; rw [h0, norm_zero] at this; linarith
    refine Bnd.succ (fun x => ?_) (fun i => ?_)
    · rw [norm_inv]
      exact (inv_anti₀ hρ (hg x)).trans (le_max_left _ _)
    · have ih := Bnd_inv hρ hM hg k (hb.of_le (Nat.le_succ k))
      rw [dlt_inv i g hg0]
      have h0 := invC_nonneg (M := M) hρ k
      have e1 := Bnd_mul k h0 hM ih (hb.diff i)
      have e2 := Bnd_mul k (by positivity) h0 e1 (ih.shift i)
      exact e2.neg.mono (le_max_right _ _)

end Inverse

/-! ### The quaternion model of the weak sector -/

section Quaternion

open scoped Quaternion

variable {X ι : Type*} [AddCommGroup X] (e : ι → X) (h : ℝ) (u : X → ι → ℍ)

/-- The covariant difference `D_i^U F(x) = h⁻¹(u_i(x) F(x + e_i) - F(x))`. -/
def cD (i : ι) (F : X → ℍ) : X → ℍ := fun x => h⁻¹ • (u x i * F (x + e i) - F x)

/-- Covariant words `D_I^U`, outermost first: `D_{i :: I} = D_i D_I`. -/
def cW : List ι → (X → ℍ) → X → ℍ
  | [], F => F
  | i :: I, F => cD e h u i (cW I F)

variable (H : X → ℍ)

/-- The algebraic Higgs frame `q_x = H_x/|H_x|`. -/
def qf (x : X) : ℍ := (‖H x‖⁻¹ : ℝ) • H x

/-- The normalized jets `J_I = q̄ D_I^U F`. -/
def nJ (F : X → ℍ) (I : List ι) : X → ℍ := fun x => star (qf H x) * cW e h u I F x

/-- The normalized links `W_i(x) = q̄_x u_i(x) q_{x+e_i}`. -/
def nW (i : ι) : X → ℍ := fun x => star (qf H x) * u x i * qf H (x + e i)

/-- The normalized link coordinates `a_i = h⁻¹(W_i - 1)`. -/
def na (i : ι) : X → ℍ := fun x => h⁻¹ • (nW e u H i x - 1)

/-- The Higgs modulus `|H|` as a (real) quaternion field. -/
def eta : X → ℍ := fun x => ((‖H x‖ : ℝ) : ℍ)

variable {e h u H}

theorem norm_qf {x : X} (hx : H x ≠ 0) : ‖qf H x‖ = 1 := by
  rw [qf, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

theorem star_qf_mul_self {x : X} (hx : H x ≠ 0) : star (qf H x) * qf H x = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, norm_qf hx, mul_one]
  rfl

theorem qf_mul_star {x : X} (hx : H x ≠ 0) : qf H x * star (qf H x) = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, norm_qf hx, mul_one]
  rfl

/-- `q̄_x H_x = |H_x|`: the normalized Higgs field is real (`J_∅ = |H|`). -/
theorem nJ_nil (x : X) (hx : H x ≠ 0) : nJ e h u H H [] x = eta H x := by
  have e1 : nJ e h u H H [] x = ‖H x‖⁻¹ • (star (H x) * H x) := by
    simp only [nJ, cW, qf]
    rw [Quaternion.star_smul, smul_mul_assoc]
  rw [e1, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, Quaternion.smul_coe, eta]
  congr 1
  field_simp [norm_ne_zero_iff.2 hx]

/-- **`eq:gauge-closed`, first identity**: `δ_iJ_I = J_{iI} - a_i T_iJ_I`. -/
theorem dlt_nJ (hH : ∀ x, H x ≠ 0) (F : X → ℍ) (I : List ι) (i : ι) :
    dlt e h i (nJ e h u H F I) = nJ e h u H F (i :: I) - na e h u H i * sh e i (nJ e h u H F I) := by
  funext x
  simp only [dlt, nJ, na, nW, sh, cW, cD, Pi.sub_apply, Pi.mul_apply, smul_mul_assoc,
    mul_smul_comm, ← smul_sub]
  congr 1
  have hq := qf_mul_star (H := H) (hH (x + e i))
  rw [sub_mul, one_mul, mul_assoc (star (qf H x) * u x i), ← mul_assoc (qf H (x + e i)), hq,
    one_mul, mul_sub]
  noncomm_ring

/-- **`eq:gauge-closed`, second identity**: `|H_{x+e_i}| = | |H_x| + h J_i(x) |` for unit links. -/
theorem norm_shift_eq (hh : h ≠ 0) (hH : ∀ x, H x ≠ 0) (hu : ∀ x i, ‖u x i‖ = 1) (x : X) (i : ι) :
    ‖H (x + e i)‖ = ‖eta H x + h • nJ e h u H H [i] x‖ := by
  have e1 : eta H x + h • nJ e h u H H [i] x = star (qf H x) * (u x i * H (x + e i)) := by
    rw [← nJ_nil (e := e) (h := h) (u := u) x (hH x)]
    simp only [nJ, cW, cD, smul_smul, mul_inv_cancel₀ hh, one_smul, mul_smul_comm, mul_sub]
    abel
  rw [e1, norm_mul, norm_mul, Quaternion.norm_star, norm_qf (hH x), hu, one_mul, one_mul]

theorem eta_ne (hH : ∀ x, H x ≠ 0) (x : X) : eta H x ≠ 0 := by
  intro h0
  have := congrArg QuaternionAlgebra.re h0
  simp only [eta, Quaternion.re_coe, Quaternion.re_zero, norm_eq_zero] at this
  exact hH x this

theorem norm_eta (x : X) : ‖eta H x‖ = ‖H x‖ := by
  simp only [eta, Quaternion.norm_coe, Real.norm_eq_abs, abs_norm]

/-- The normalized link coordinate from the jets: `a_i = (J_i - δ_i|H|)(T_i|H|)⁻¹`. -/
theorem na_eq (hH : ∀ x, H x ≠ 0) (i : ι) :
    na e h u H i = (nJ e h u H H [i] - dlt e h i (eta H)) * sh e i (fun x => (eta H x)⁻¹) := by
  have hJ0 : nJ e h u H H [] = eta H := funext fun x => nJ_nil x (hH x)
  have h1 := dlt_nJ (e := e) (h := h) (u := u) hH H [] i
  rw [hJ0] at h1
  funext x
  have h1x := congrFun h1 x
  simp only [Pi.sub_apply, Pi.mul_apply, sh] at h1x ⊢
  rw [h1x, sub_sub_cancel, mul_assoc, mul_inv_cancel₀ (eta_ne hH _), mul_one]

/-- **The difference of the Higgs modulus in terms of jets**:
`δ_i|H| = (|H|(J_i + J̄_i) + h J_iJ̄_i)(T_i|H| + |H|)⁻¹`. -/
theorem dlt_eta (hh : h ≠ 0) (hH : ∀ x, H x ≠ 0) (hu : ∀ x i, ‖u x i‖ = 1) (i : ι) :
    dlt e h i (eta H) = (eta H * (nJ e h u H H [i] + star ∘ nJ e h u H H [i]) +
      (fun _ => (h : ℍ)) * (nJ e h u H H [i] * star ∘ nJ e h u H H [i])) *
        (fun x => (sh e i (eta H) x + eta H x)⁻¹) := by
  funext x
  set j := nJ e h u H H [i] x with hj
  set η := ‖H x‖ with hη
  set η' := ‖H (x + e i)‖ with hη'
  have hpos : 0 < η' + η := by
    have := norm_pos_iff.2 (hH x); have := norm_nonneg (H (x + e i)); linarith
  have hsq : η' ^ 2 = η ^ 2 + h * (2 * η * j.re + h * Quaternion.normSq j) := by
    rw [hη', norm_shift_eq hh hH hu x i, sq, ← Quaternion.normSq_eq_norm_mul_self]
    simp only [eta, Quaternion.normSq_def', Quaternion.re_add, Quaternion.re_coe,
      Quaternion.re_smul, Quaternion.imI_add, Quaternion.imI_coe, Quaternion.imI_smul,
      Quaternion.imJ_add, Quaternion.imJ_coe, Quaternion.imJ_smul, Quaternion.imK_add,
      Quaternion.imK_coe, Quaternion.imK_smul, smul_eq_mul, ← hj]
    ring
  have hL : dlt e h i (eta H) x = ((h⁻¹ * (η' - η) : ℝ) : ℍ) := by
    simp only [dlt, eta]
    rw [← Quaternion.coe_sub, Quaternion.smul_coe]
  have key : (h⁻¹ * (η' - η) : ℝ) =
      (η * (2 * j.re) + h * Quaternion.normSq j) * (η' + η)⁻¹ := by
    field_simp
    nlinarith [hsq]
  rw [hL, key]
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, sh, eta, ← hj]
  rw [Quaternion.self_add_star, Quaternion.self_mul_star, ← Quaternion.coe_add,
    ← Quaternion.coe_inv]
  rw [← hη, ← hη']
  have h2 : ((2 : ℝ) : ℍ) = 2 := QuaternionAlgebra.coe_ofNat
  simp only [Quaternion.coe_mul, Quaternion.coe_add, Quaternion.coe_inv, h2]

end Quaternion

/-! ### The normalized hierarchy -/

section Hierarchy

open scoped Quaternion

variable {X ι : Type*} [AddCommGroup X] {e : ι → X} {h : ℝ}

theorem dW_zero : ∀ (α : List ι), dW e h α (fun _ : X => (0 : ℍ)) = fun _ => 0
  | [] => rfl
  | i :: α => by
    have : dlt e h i (fun _ : X => (0 : ℍ)) = fun _ => 0 := by funext x; simp [dlt]
    simp only [dW, this, dW_zero α]

theorem Bnd_const (k : ℕ) (c : ℍ) : Bnd e h k (fun _ : X => c) ‖c‖ := by
  intro α hα x
  cases α with
  | nil => exact le_rfl
  | cons i α =>
    have : dlt e h i (fun _ : X => c) = fun _ => 0 := by funext x; simp [dlt]
    simp only [dW, this, dW_zero]
    simp

theorem dW_star : ∀ (α : List ι) (f : X → ℍ), dW e h α (star ∘ f) = star ∘ dW e h α f
  | [], _ => rfl
  | i :: α, f => by
    have : dlt e h i (star ∘ f) = star ∘ dlt e h i f := by
      funext x
      simp only [dlt, Function.comp_apply, Quaternion.star_smul, star_sub]
    simp only [dW, this, dW_star α]

theorem Bnd.star {k : ℕ} {f : X → ℍ} {B : ℝ} (hf : Bnd e h k f B) :
    Bnd e h k (star ∘ f) B := fun α hα x => by
  rw [dW_star, Function.comp_apply, Quaternion.norm_star]; exact hf α hα x

variable (ρ B : ℝ)

/-- The bound on `δ_i|H|` at level `k` in terms of the level-`k` bound `M`. -/
def dEtaC (k : ℕ) (M : ℝ) : ℝ :=
  2 ^ k * ((2 ^ k * (M * (M + M)) + 2 ^ k * (1 * (2 ^ k * (M * M)))) *
    invC (2 * ρ) (M + M) k)

/-- The bound on `a_i` at level `k`. -/
def aC (k : ℕ) (M : ℝ) : ℝ := 2 ^ k * ((M + dEtaC ρ k M) * invC ρ M k)

theorem dEtaC_nonneg {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (k : ℕ) : 0 ≤ dEtaC ρ k M := by
  unfold dEtaC
  have := invC_nonneg (M := M + M) (by positivity : (0 : ℝ) < 2 * ρ) k
  positivity

theorem aC_nonneg {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (k : ℕ) : 0 ≤ aC ρ k M := by
  unfold aC
  have := invC_nonneg (M := M) hρ k
  have := dEtaC_nonneg hρ hM k
  positivity

/-- The hierarchy constants: `M_0 = B`, `M_{k+1}` dominates `M_k`, the bound on `δ|H|`, on `a_i`
and on the differences of the normalized jets. -/
def hierC : ℕ → ℝ
  | 0 => B
  | k + 1 => max (hierC k) (max (dEtaC ρ k (hierC k))
      (max (aC ρ k (hierC k)) (hierC k + 2 ^ k * (aC ρ k (hierC k) * hierC k))))

theorem invC_nonneg' {ρ' M : ℝ} (hρ : 0 < ρ') (k : ℕ) : 0 ≤ invC ρ' M k := invC_nonneg hρ k

theorem hierC_nonneg (hρ : 0 < ρ) (hB : 0 ≤ B) : ∀ k, 0 ≤ hierC ρ B k
  | 0 => hB
  | k + 1 => le_max_of_le_left (hierC_nonneg hρ hB k)

theorem hierC_mono (k : ℕ) : hierC ρ B k ≤ hierC ρ B (k + 1) := le_max_left _ _

theorem hierC_mono' (hρ : 0 < ρ) (hB : 0 ≤ B) {k k' : ℕ} (hk : k ≤ k') :
    hierC ρ B k ≤ hierC ρ B k' := by
  induction k', hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact ih.trans (hierC_mono ρ B k')

theorem B_le_hierC (hρ : 0 < ρ) (hB : 0 ≤ B) (k : ℕ) : B ≤ hierC ρ B k :=
  hierC_mono' ρ B hρ hB (Nat.zero_le k)

variable {u : X → ι → ℍ} {H : X → ℍ}

/-- The difference of the Higgs modulus at level `k`. -/
theorem Bnd_dlt_eta {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hH : ∀ x, ρ ≤ ‖H x‖) (hu : ∀ x i, ‖u x i‖ = 1) {k : ℕ} (i : ι)
    (hη : Bnd e h k (eta H) M) (hj : Bnd e h k (nJ e h u H H [i]) M) :
    Bnd e h k (dlt e h i (eta H)) (dEtaC ρ k M) := by
  have hH0 : ∀ x, H x ≠ 0 := fun x h0 => by
    have := hH x; rw [h0, norm_zero] at this; linarith
  rw [dlt_eta hh0.ne' hH0 hu i]
  have hjj : Bnd e h k (nJ e h u H H [i] + star ∘ nJ e h u H H [i]) (M + M) := hj.add hj.star
  have h1 := Bnd_mul k hM (by positivity) hη hjj
  have hc : Bnd e h k (fun _ : X => (h : ℍ)) 1 := by
    refine (Bnd_const k (h : ℍ)).mono ?_
    rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_pos hh0]; exact hh1
  have h2 := Bnd_mul k hM hM hj hj.star
  have h3 := Bnd_mul k zero_le_one (by positivity) hc h2
  have hden : ∀ x, 2 * ρ ≤ ‖sh e i (eta H) x + eta H x‖ := by
    intro x
    simp only [sh, eta, ← Quaternion.coe_add, Quaternion.norm_coe, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    linarith [hH x, hH (x + e i)]
  have hsum : Bnd e h k (fun x => sh e i (eta H) x + eta H x) (M + M) := (hη.shift i).add hη
  have hinv := Bnd_inv (by positivity : (0 : ℝ) < 2 * ρ) (by positivity) hden k hsum
  have h4 := Bnd_mul k (by positivity) (invC_nonneg (by positivity) k) (h1.add h3) hinv
  exact h4

/-- The normalized link coordinate at level `k`. -/
theorem Bnd_na {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hH : ∀ x, ρ ≤ ‖H x‖) (hu : ∀ x i, ‖u x i‖ = 1) {k : ℕ} (i : ι)
    (hη : Bnd e h k (eta H) M) (hη1 : Bnd e h k (dlt e h i (eta H)) (dEtaC ρ k M))
    (hj : Bnd e h k (nJ e h u H H [i]) M) :
    Bnd e h k (na e h u H i) (aC ρ k M) := by
  have hH0 : ∀ x, H x ≠ 0 := fun x h0 => by
    have := hH x; rw [h0, norm_zero] at this; linarith
  rw [na_eq hH0 i]
  have hnorm : ∀ x, ρ ≤ ‖eta H x‖ := fun x => by rw [norm_eta]; exact hH x
  have hinv := Bnd_inv hρ hM hnorm k hη
  have hd : 0 ≤ dEtaC ρ k M := dEtaC_nonneg hρ hM k
  exact Bnd_mul k (by positivity) (invC_nonneg hρ k) (hj.sub hη1) (hinv.shift i)

/-- **The normalized hierarchy** (`eq:gauge-normalized-reader`, Higgs part): for `0 < h ≤ 1`,
unit links, `|H| ≥ ρ > 0` and `‖D_I^U H‖_∞ ≤ B` for all covariant words `|I| ≤ L`:
* `‖|H|‖_{C_h^k} ≤ M_k` for `k ≤ L`;
* `‖J_I‖_{C_h^k} ≤ M_k` for `|I| + k ≤ L`;
* `‖a_i‖_{C_h^k} ≤ M_{k+1}` for `k + 1 ≤ L`, `a_i = h⁻¹(W_i - 1)`;
with `M_k = hierC ρ B k` depending only on `ρ, B, k` — not on the links, the frame or `h`. -/
theorem normalized_hierarchy (hρ : 0 < ρ) (hB : 0 ≤ B) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hH : ∀ x, ρ ≤ ‖H x‖) (hu : ∀ x i, ‖u x i‖ = 1) {L : ℕ}
    (hJB : ∀ I : List ι, I.length ≤ L → ∀ x, ‖cW e h u I H x‖ ≤ B) :
    ∀ k, (k ≤ L → Bnd e h k (eta H) (hierC ρ B k)) ∧
      (∀ I : List ι, I.length + k ≤ L → Bnd e h k (nJ e h u H H I) (hierC ρ B k)) ∧
      (k + 1 ≤ L → ∀ i, Bnd e h k (na e h u H i) (hierC ρ B (k + 1))) := by
  have hH0 : ∀ x, H x ≠ 0 := fun x h0 => by
    have := hH x; rw [h0, norm_zero] at this; linarith
  have hq : ∀ x, ‖star (qf H x)‖ = 1 := fun x => by rw [Quaternion.norm_star, norm_qf (hH0 x)]
  -- levels `η, J` (statement `P k`)
  have P : ∀ k, (k ≤ L → Bnd e h k (eta H) (hierC ρ B k)) ∧
      (∀ I : List ι, I.length + k ≤ L → Bnd e h k (nJ e h u H H I) (hierC ρ B k)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => ?_, fun I hI => ?_⟩
      · intro α hα x
        have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
        subst this
        simp only [dW, hierC]
        rw [norm_eta]; exact hJB [] (Nat.zero_le _) x
      · intro α hα x
        have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
        subst this
        simp only [dW, hierC, nJ]
        rw [norm_mul, hq, one_mul]; exact hJB I (by omega) x
    | succ k ih =>
      obtain ⟨ihη, ihJ⟩ := ih
      have hM := hierC_nonneg ρ B hρ hB k
      have hBk := B_le_hierC ρ B hρ hB (k + 1)
      refine ⟨fun hk => ?_, fun I hI => ?_⟩
      · refine Bnd.succ (fun x => ?_) (fun i => ?_)
        · rw [norm_eta]; exact (hJB [] (Nat.zero_le _) x).trans hBk
        · refine (Bnd_dlt_eta hρ hM hh0 hh1 hH hu i (ihη (by omega)) (ihJ [i] (by simp; omega))).mono
            ?_
          simp only [hierC]
          exact le_max_of_le_right (le_max_left _ _)
      · have hη1 : Bnd e h (k + 1) (eta H) (hierC ρ B (k + 1)) := by
          refine Bnd.succ (fun x => ?_) (fun i => ?_)
          · rw [norm_eta]; exact (hJB [] (Nat.zero_le _) x).trans hBk
          · refine (Bnd_dlt_eta hρ hM hh0 hh1 hH hu i (ihη (by omega))
              (ihJ [i] (by simp; omega))).mono ?_
            simp only [hierC]
            exact le_max_of_le_right (le_max_left _ _)
        refine Bnd.succ (fun x => ?_) (fun i => ?_)
        · simp only [nJ]; rw [norm_mul, hq, one_mul]; exact (hJB I (by omega) x).trans hBk
        · rw [dlt_nJ hH0 H I i]
          have ha := Bnd_na hρ hM hh0 hh1 hH hu i (ihη (by omega))
            (Bnd_dlt_eta hρ hM hh0 hh1 hH hu i (ihη (by omega)) (ihJ [i] (by simp; omega)))
            (ihJ [i] (by simp; omega))
          have hJi := ihJ (i :: I) (by simp; omega)
          have hJI := ihJ I (by omega)
          have hmul := Bnd_mul k (aC_nonneg hρ hM k) hM ha (hJI.shift i)
          refine (hJi.sub hmul).mono ?_
          simp only [hierC]
          exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine fun k => ⟨(P k).1, (P k).2, fun hk i => ?_⟩
  have hM := hierC_nonneg ρ B hρ hB k
  have ihη := (P k).1 (by omega)
  have hj := (P k).2 [i] (by simp; omega)
  refine (Bnd_na hρ hM hh0 hh1 hH hu i ihη (Bnd_dlt_eta hρ hM hh0 hh1 hH hu i ihη hj) hj).mono ?_
  simp only [hierC]
  exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

/-- The matter constants. -/
def matC (BF : ℝ) : ℕ → ℝ
  | 0 => BF
  | k + 1 => max (matC BF k) (matC BF k + 2 ^ k * (hierC ρ B (k + 1) * matC BF k))

theorem matC_nonneg {BF : ℝ} (hBF : 0 ≤ BF) : ∀ k, 0 ≤ matC ρ B BF k
  | 0 => hBF
  | k + 1 => le_max_of_le_left (matC_nonneg hBF k)

theorem BF_le_matC {BF : ℝ} : ∀ k, BF ≤ matC ρ B BF k
  | 0 => le_rfl
  | k + 1 => (BF_le_matC k).trans (le_max_left _ _)

/-- **The normalized hierarchy for matter fields** (`eq:gauge-normalized-reader`, `Q^*F_b` part):
under the hypotheses of `normalized_hierarchy` with `L' ≤ L` and `‖D_I^U F‖_∞ ≤ B_F` for
`|I| ≤ L'`, `‖q̄ D_I^U F‖_{C_h^k} ≤ matC k` for `|I| + k ≤ L'` (in particular
`‖Q^*F‖_{C_h^{L'}}` is bounded). -/
theorem normalized_matter (hρ : 0 < ρ) (hB : 0 ≤ B) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hH : ∀ x, ρ ≤ ‖H x‖) (hu : ∀ x i, ‖u x i‖ = 1) {L L' : ℕ} (hLL : L' ≤ L)
    (hJB : ∀ I : List ι, I.length ≤ L → ∀ x, ‖cW e h u I H x‖ ≤ B) {F : X → ℍ} {BF : ℝ}
    (hBF : 0 ≤ BF) (hFB : ∀ I : List ι, I.length ≤ L' → ∀ x, ‖cW e h u I F x‖ ≤ BF) :
    ∀ k, ∀ I : List ι, I.length + k ≤ L' → Bnd e h k (nJ e h u H F I) (matC ρ B BF k) := by
  have hH0 : ∀ x, H x ≠ 0 := fun x h0 => by
    have := hH x; rw [h0, norm_zero] at this; linarith
  have hq : ∀ x, ‖star (qf H x)‖ = 1 := fun x => by rw [Quaternion.norm_star, norm_qf (hH0 x)]
  have hier := normalized_hierarchy ρ B hρ hB hh0 hh1 hH hu hJB
  intro k
  induction k with
  | zero =>
    intro I hI α hα x
    have : α = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hα)
    subst this
    simp only [dW, matC, nJ]
    rw [norm_mul, hq, one_mul]; exact hFB I (by omega) x
  | succ k ih =>
    intro I hI
    have hM := matC_nonneg ρ B hBF k
    refine Bnd.succ (fun x => ?_) (fun i => ?_)
    · simp only [nJ]; rw [norm_mul, hq, one_mul]
      exact (hFB I (by omega) x).trans (BF_le_matC ρ B (k + 1))
    · rw [dlt_nJ hH0 F I i]
      have ha := (hier k).2.2 (by omega) i
      have hmul := Bnd_mul k (hierC_nonneg ρ B hρ hB (k + 1)) hM ha ((ih I (by omega)).shift i)
      refine ((ih (i :: I) (by simp; omega)).sub hmul).mono ?_
      simp only [matC]
      exact le_max_right _ _

end Hierarchy

/-! ### The normalized reader on the periodic grid -/

section Grid

open scoped Quaternion
open GaugeCovEmbed GridSobolev

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

/-- The represented links `ρ(U_i(x))` = left multiplication by the unit quaternion `u_i(x)`. -/
def rhoL (u : (ι → ZMod n) → ι → ℍ) : (ι → ZMod n) → ι → ℍ →L[ℝ] ℍ :=
  fun x i => ContinuousLinearMap.mul ℝ ℍ (u x i)

theorem rhoL_iso {u : (ι → ZMod n) → ι → ℍ} (hu : ∀ x i, ‖u x i‖ = 1) (x : ι → ZMod n) (i : ι)
    (v : ℍ) : ‖rhoL u x i v‖ = ‖v‖ := by
  simp only [rhoL, ContinuousLinearMap.mul_apply', norm_mul, hu, one_mul]

/-- The covariant words of `GaugeCovEmbed` are the quaternion covariant words. -/
theorem covWord_eq_cW (h : ℝ) (u : (ι → ZMod n) → ι → ℍ) :
    ∀ (I : List ι) (F : (ι → ZMod n) → ℍ),
      covWord h (rhoL u) I F = cW (gridStep (n := n)) h u I F
  | [], _ => rfl
  | i :: I, F => by
    simp only [covWord, cW, covWord_eq_cW h u I F]
    rfl

theorem embC_nonneg {Lb : ℝ} (hLb : 0 < Lb) : 0 ≤ embC Lb := by
  unfold embC
  have h1 := two_rpow_quarter_gt_one
  have h2 : 0 ≤ Lb ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hLb.le _
  have h3 : 0 ≤ (2 / Lb) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have h4 : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) - 1 := by linarith
  positivity

/-- **The normalized weak-sector reader** (`eq:gauge-normalized-reader`, `cor:gauge-robust-reader`)
on the periodic grid `(ℤ/n)⁴` with mesh `0 < h ≤ 1`, unit quaternion links (the `SU(2)` action on
`ℂ² ≅ ℍ`) and a Higgs field on the chart `|H| ≥ ρ_* > 0`: if
`J_{h,s+4}(H;U) ≤ R` and `J_{h,s+3}(F_b;U) ≤ R` for the matter fields, then
`‖|H|‖_{C_h^{s+1}} ≤ M_{s+1}`, `‖h⁻¹(W_i - 1)‖_{C_h^s} ≤ M_{s+1}` and `‖Q^*F_b‖_{C_h^s} ≤ M'_s`,
with `M, M'` depending only on `s`, `ρ_*`, `R` and the box side `nh` — no derivative of the
original frame and no smallness of the original links. -/
theorem gauge_normalized_reader (hι : Fintype.card ι = 4) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    {u : (ι → ZMod n) → ι → ℍ} (hu : ∀ x i, ‖u x i‖ = 1) {H : (ι → ZMod n) → ℍ} {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ∀ x, ρ ≤ ‖H x‖) {s : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hJH : jetEnergy h (rhoL u) (s + 4) H ≤ R) {β : Type*} (Fb : β → (ι → ZMod n) → ℍ)
    (hJF : ∀ b, jetEnergy h (rhoL u) (s + 3) (Fb b) ≤ R) :
    Bnd gridStep h (s + 1) (eta H) (hierC ρ (embC (n * h) * R) (s + 1)) ∧
      (∀ i, Bnd gridStep h s (na gridStep h u H i) (hierC ρ (embC (n * h) * R) (s + 1))) ∧
      (∀ b, Bnd gridStep h s (nJ gridStep h u H (Fb b) [])
        (matC ρ (embC (n * h) * R) (embC (n * h) * R) s)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hE := embC_nonneg (mul_pos hn hh0)
  set B := embC (n * h) * R with hBdef
  have hB : 0 ≤ B := mul_nonneg hE hR
  have hiso := rhoL_iso hu
  have hJB : ∀ I : List ι, I.length ≤ s + 1 → ∀ x, ‖cW gridStep h u I H x‖ ≤ B := by
    intro I hI x
    rw [← covWord_eq_cW]
    exact (gauge_cov_embed_words hι hh0 hiso (s + 4) H I (by omega) x).trans
      (mul_le_mul_of_nonneg_left hJH hE)
  have hFB : ∀ b, ∀ I : List ι, I.length ≤ s → ∀ x, ‖cW gridStep h u I (Fb b) x‖ ≤ B := by
    intro b I hI x
    rw [← covWord_eq_cW]
    exact (gauge_cov_embed_words hι hh0 hiso (s + 3) (Fb b) I (by omega) x).trans
      (mul_le_mul_of_nonneg_left (hJF b) hE)
  have hier := normalized_hierarchy ρ B hρ hB hh0 hh1 hH hu hJB
  refine ⟨(hier (s + 1)).1 le_rfl, fun i => (hier s).2.2 le_rfl i, fun b => ?_⟩
  exact normalized_matter ρ B hρ hB hh0 hh1 hH hu (Nat.le_succ s) hJB hB (hFB b) s [] (by simp)

/-- **Non-vacuity of `gauge_normalized_reader`**: on `(ℤ/3)⁴` with `h = 1`, trivial links and the
constant Higgs field `H = 1` (`|H| = 1`) the hypotheses hold with `R` the jet energy itself. -/
example : Bnd (gridStep (ι := Fin 4) (n := 3)) 1 1
    (eta (fun _ : Fin 4 → ZMod 3 => (1 : ℍ)))
    (hierC 1 (embC ((3 : ℕ) * 1) * jetEnergy 1 (rhoL (ι := Fin 4) (n := 3) fun _ _ => (1 : ℍ))
      (0 + 4) (fun _ => (1 : ℍ))) (0 + 1)) :=
  (gauge_normalized_reader (ι := Fin 4) (n := 3) (by simp) one_pos le_rfl
    (u := fun _ _ => 1) (fun _ _ => by simp) (H := fun _ => 1) one_pos (fun _ => by simp)
    (s := 0) (Real.sqrt_nonneg _) le_rfl (β := Empty) (fun b => b.elim) (fun b => b.elim)).1

end Grid
end RenewalGeometry.WeakNormReader
