/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.QuadraticPacketDefect

/-!
# Pointwise algebra of the Yang–Mills and Higgs stress tensors
  (Einstein–SM action closure, `eq:YM-stress`, `eq:H-stress`, `eq:YM-timelike-energy`,
  `eq:H-timelike-energy`, `eq:timelike-defect-coercivity`)

Pointwise (at one point of the chart) finite algebra used by the stress-defect records
`prop:YM-defect`, `thm:higgs-defect` and `thm:zero-defect-characterization`.

* Metrics are component arrays `G : Fin 4 → Fin 4 → ℝ` (`mat G` the matrix), with inverse
  `(mat G)⁻¹` and volume density `vol G = √|det G|`.
* The gauge field strength is realified in an orthonormal basis of the fixed invariant inner product
  of each simple factor of the gauge Lie algebra; the positive invariant Lie-algebra metric of the
  action (coefficients `g_j^{-2}`) is then the diagonal weight `w : κ → ℝ`, and
  `lieIp w u v = Σ_a w_a u_a v_a`.
* `ymStress G w F μ ν = Σ_{αβ} g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼ g_{μν} Σ g^{αγ} g^{βδ} ⟨F_{αβ}, F_{γδ}⟩`
  (`eq:YM-stress`); `higgsKin G Y μ ν = 2⟨Y_μ, Y_ν⟩ - g_{μν} g^{αβ}⟨Y_α, Y_β⟩` and
  `higgsStress = higgsKin - g_{μν} λ(|H|² - v²)²` (`eq:H-stress`, realified Higgs).
* `qf_ymCoef`, `qf_kinCoef`: these stresses (times a volume factor) are the quadratic forms
  `qf` of explicit coefficient arrays in the realified components (used to apply the quadratic
  packet-defect calculus of `QuadraticPacketDefect.lean`).
* `timelike_kin`, `timelike_ym`: for `g(n, n) = -1` (and antisymmetric `F`),
  `T^{H,kin}(n, n) = h^{αβ}⟨Y_α, Y_β⟩` and `T^{YM}(n, n) = ¼ h^{αγ} h^{βδ}⟨F_{αβ}, F_{γδ}⟩` with
  `h^{-1} = g^{-1} + 2 n ⊗ n`.
* `frame_hinv`: for a `g`-orthonormal frame `E` with time leg `n` (`Eᵀ g E = η`, `E e₀ = n`),
  `g^{-1} + 2 n ⊗ n = E Eᵀ`; hence `T^{H,kin}(n,n) = Σ_k |Y(e_k)|²` and
  `T^{YM}(n,n) = ¼ Σ_{kl} |F(e_k, e_l)|²` (`eq:H-timelike-energy`, `eq:YM-timelike-energy`), and the
  two-sided bounds `frame_kin_bounds`, `frame_ym_bounds` in terms of `Σ E²` and `Σ (E⁻¹)²`.
-/

open Matrix Finset

namespace RenewalGeometry

namespace BosonicStress

open QuadraticPacketDefect

/-! ## Metrics, inverses and volume -/

/-- The matrix of a component array. -/
def mat (G : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of G

@[simp] theorem mat_apply (G : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : mat G i j = G i j := rfl

/-- The inverse metric components `g^{μν}`. -/
noncomputable def ginv (G : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := fun i j => (mat G)⁻¹ i j

/-- The volume density `√|det g|`. -/
noncomputable def vol (G : Fin 4 → Fin 4 → ℝ) : ℝ := Real.sqrt |(mat G).det|

theorem continuous_det : Continuous fun G : Fin 4 → Fin 4 → ℝ => (mat G).det :=
  Continuous.matrix_det (A := fun G : Fin 4 → Fin 4 → ℝ => mat G) continuous_id

theorem continuous_vol : Continuous vol :=
  Real.continuous_sqrt.comp (continuous_abs.comp continuous_det)

theorem vol_nonneg (G : Fin 4 → Fin 4 → ℝ) : 0 ≤ vol G := Real.sqrt_nonneg _

theorem vol_pos {G : Fin 4 → Fin 4 → ℝ} (h : (mat G).det ≠ 0) : 0 < vol G :=
  Real.sqrt_pos.2 (abs_pos.2 h)

/-! ## Stress tensors -/

variable {κ : Type*} [Fintype κ]

/-- The positive invariant Lie-algebra metric, diagonal with weights `w_a = g_{j(a)}^{-2}`. -/
def lieIp (w : κ → ℝ) (u v : κ → ℝ) : ℝ := ∑ a, w a * (u a * v a)

/-- The Yang–Mills Hilbert stress `eq:YM-stress`:
`T_{μν} = Σ_{αβ} g^{αβ}⟨F_{μα}, F_{νβ}⟩ - ¼ g_{μν} Σ_{αβγδ} g^{αγ} g^{βδ}⟨F_{αβ}, F_{γδ}⟩`. -/
noncomputable def ymStress (G : Fin 4 → Fin 4 → ℝ) (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ)
    (μ ν : Fin 4) : ℝ :=
  ∑ α, ∑ β, ginv G α β * lieIp w (F μ α) (F ν β) -
    (1 / 4) * G μ ν * ∑ α, ∑ β, ∑ γ, ∑ δ, ginv G α γ * ginv G β δ * lieIp w (F α β) (F γ δ)

/-- The kinetic Higgs stress `2 Re⟨D_μH, D_νH⟩ - g_{μν} |D_A H|²_g` (realified Higgs components
`Y_μ : κ → ℝ`, `Re⟨·,·⟩` the Euclidean inner product). -/
noncomputable def higgsKin (G : Fin 4 → Fin 4 → ℝ) (Y : Fin 4 → κ → ℝ) (μ ν : Fin 4) : ℝ :=
  2 * ∑ a, Y μ a * Y ν a - G μ ν * ∑ α, ∑ β, ginv G α β * ∑ a, Y α a * Y β a

/-- The Higgs potential `V(H) = λ(|H|² - v²)²`. -/
def higgsPot (lam v : ℝ) (H2 : ℝ) : ℝ := lam * (H2 - v ^ 2) ^ 2

/-- The Higgs stress `eq:H-stress`: `T^H_{μν} = 2 Re⟨D_μH, D_νH⟩ - g_{μν}(|D_A H|²_g + V(H))`,
with `H2 = |H|²`. -/
noncomputable def higgsStress (G : Fin 4 → Fin 4 → ℝ) (lam v : ℝ) (Y : Fin 4 → κ → ℝ) (H2 : ℝ)
    (μ ν : Fin 4) : ℝ :=
  higgsKin G Y μ ν - G μ ν * higgsPot lam v H2

/-! ## Quadratic-form representation in the realified components -/

/-- Block-diagonal coefficient `b((p,a),(q,c)) = β(p,q) w_a δ_{ac}`. -/
def diagCoef {A : Type*} [DecidableEq κ] (w : κ → ℝ) (β : A → A → ℝ) : A × κ → A × κ → ℝ :=
  fun p q => β p.1 q.1 * (if p.2 = q.2 then w p.2 else 0)

theorem qf_diagCoef {A : Type*} [Fintype A] [DecidableEq κ] (w : κ → ℝ) (β : A → A → ℝ)
    (z : A × κ → ℝ) :
    qf (diagCoef w β) z = ∑ p, ∑ q, β p q * lieIp w (fun a => z (p, a)) (fun a => z (q, a)) := by
  simp only [qf, diagCoef, lieIp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]; ring
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

/-- Realification of a vector-component family into a packet indexed by `A × κ`. -/
def flat {A : Type*} (F : A → κ → ℝ) : A × κ → ℝ := fun p => F p.1 p.2

/-- The scalar part of the Yang–Mills stress coefficient, indexed by pairs `(α, β)`. -/
noncomputable def ymBeta (G : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ :=
  fun p q => (if p.1 = μ ∧ q.1 = ν then ginv G p.2 q.2 else 0) -
    (1 / 4) * G μ ν * (ginv G p.1 q.1 * ginv G p.2 q.2)

/-- The Yang–Mills stress coefficient (times a volume factor `V`). -/
noncomputable def ymCoef [DecidableEq κ] (G : Fin 4 → Fin 4 → ℝ) (w : κ → ℝ) (V : ℝ) (μ ν : Fin 4) :
    (Fin 4 × Fin 4) × κ → (Fin 4 × Fin 4) × κ → ℝ :=
  V • diagCoef w (ymBeta G μ ν)

theorem qf_ymCoef [DecidableEq κ] (G : Fin 4 → Fin 4 → ℝ) (w : κ → ℝ) (V : ℝ)
    (F : Fin 4 → Fin 4 → κ → ℝ) (μ ν : Fin 4) :
    qf (ymCoef G w V μ ν) (flat fun p : Fin 4 × Fin 4 => F p.1 p.2) =
      V * ymStress G w F μ ν := by
  rw [ymCoef, qf_smul_left, qf_diagCoef]
  congr 1
  simp only [ymBeta, flat, sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type, ymStress]
  congr 1
  · simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_single μ]
    · refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_eq_single ν]
      · simp
      · intro c _ hc; simp [hc]
      · simp
    · intro c _ hc
      simp [hc]
    · simp
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
    ring

/-- The scalar part of the kinetic Higgs stress coefficient, indexed by `α`. -/
noncomputable def kinBeta (G : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun α β => (if α = μ ∧ β = ν then 2 else 0) - G μ ν * ginv G α β

/-- The kinetic Higgs stress coefficient (times a volume factor `V`). -/
noncomputable def kinCoef [DecidableEq κ] (G : Fin 4 → Fin 4 → ℝ) (V : ℝ) (μ ν : Fin 4) :
    Fin 4 × κ → Fin 4 × κ → ℝ :=
  V • diagCoef (fun _ => 1) (kinBeta G μ ν)

theorem qf_kinCoef [DecidableEq κ] (G : Fin 4 → Fin 4 → ℝ) (V : ℝ) (Y : Fin 4 → κ → ℝ)
    (μ ν : Fin 4) : qf (kinCoef (κ := κ) G V μ ν) (flat Y) = V * higgsKin G Y μ ν := by
  rw [kinCoef, qf_smul_left, qf_diagCoef]
  congr 1
  simp only [kinBeta, flat, lieIp, one_mul, sub_mul, Finset.sum_sub_distrib, higgsKin]
  congr 1
  · simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_single μ]
    · rw [Finset.sum_eq_single ν]
      · simp [Finset.mul_sum]
      · intro c _ hc; simp [hc]
      · simp
    · intro c _ hc
      simp [hc]
    · simp
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-! ## Timelike contractions -/

/-- `g(n, n) = Σ g_{μν} n^μ n^ν`. -/
def gnn (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) : ℝ := ∑ μ, ∑ ν, G μ ν * n μ * n ν

/-- The positive (Euclideanized) inverse metric `h^{αβ} = g^{αβ} + 2 n^α n^β`. -/
noncomputable def hinv (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun α β => ginv G α β + 2 * (n α * n β)

/-- **`eq:H-timelike-energy`, algebraic form**: for `g(n, n) = -1`,
`T^{H,kin}(n, n) = h^{αβ}⟨Y_α, Y_β⟩` with `h^{-1} = g^{-1} + 2 n ⊗ n`. -/
theorem timelike_kin (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) (hn : gnn G n = -1)
    (Y : Fin 4 → κ → ℝ) :
    ∑ μ, ∑ ν, n μ * n ν * higgsKin G Y μ ν =
      ∑ α, ∑ β, hinv G n α β * ∑ a, Y α a * Y β a := by
  set X := ∑ α, ∑ β, ginv G α β * ∑ a, Y α a * Y β a
  have hpt : ∀ μ ν, n μ * n ν * higgsKin G Y μ ν =
      2 * (n μ * n ν * ∑ a, Y μ a * Y ν a) - (G μ ν * n μ * n ν) * X := by
    intro μ ν; simp only [higgsKin, X]; ring
  have hpt2 : ∀ α β, hinv G n α β * ∑ a, Y α a * Y β a =
      ginv G α β * ∑ a, Y α a * Y β a + 2 * (n α * n β * ∑ a, Y α a * Y β a) := by
    intro α β; simp only [hinv]; ring
  simp only [hpt, hpt2, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  have : ∑ μ, ∑ ν, G μ ν * n μ * n ν = gnn G n := rfl
  rw [this, hn]
  simp only [X]
  ring

/-- The bilinear expression `TT(a, b) = Σ a^{αγ} b^{βδ} ⟨F_{αβ}, F_{γδ}⟩`. -/
noncomputable def TT (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (a b : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ α, ∑ β, ∑ γ, ∑ δ, a α γ * b β δ * lieIp w (F α β) (F γ δ)

theorem lieIp_sum (w : κ → ℝ) (c d : Fin 4 → ℝ) (u v : Fin 4 → κ → ℝ) :
    lieIp w (∑ μ, c μ • u μ) (∑ ν, d ν • v ν) =
      ∑ μ, ∑ ν, c μ * d ν * lieIp w (u μ) (v ν) := by
  simp only [lieIp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ a, w a * ((∑ μ, c μ * u μ a) * (∑ ν, d ν * v ν a)) =
      ∑ μ, ∑ ν, c μ * d ν * (w a * (u μ a * v ν a)) := by
    intro a
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum]

theorem lieIp_neg (w : κ → ℝ) (u v : κ → ℝ) : lieIp w (-u) (-v) = lieIp w u v := by
  simp [lieIp]

theorem TT_add_left (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (a a' b : Fin 4 → Fin 4 → ℝ) :
    TT w F (a + a') b = TT w F a b + TT w F a' b := by
  simp only [TT, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem TT_add_right (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (a b b' : Fin 4 → Fin 4 → ℝ) :
    TT w F a (b + b') = TT w F a b + TT w F a b' := by
  simp only [TT, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem TT_smul_left (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (c : ℝ) (a b : Fin 4 → Fin 4 → ℝ) :
    TT w F (c • a) b = c * TT w F a b := by
  simp only [TT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  ring

theorem TT_smul_right (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (c : ℝ) (a b : Fin 4 → Fin 4 → ℝ) :
    TT w F a (c • b) = c * TT w F a b := by
  simp only [TT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
  ring

/-- The contraction `N_β = F(n, ·)_β = Σ_μ n^μ F_{μβ}`. -/
def nCon (n : Fin 4 → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (β : Fin 4) : κ → ℝ := ∑ μ, n μ • F μ β

theorem TT_nn_left (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (n : Fin 4 → ℝ)
    (b : Fin 4 → Fin 4 → ℝ) :
    TT w F (fun α γ => n α * n γ) b = ∑ β, ∑ δ, b β δ * lieIp w (nCon n F β) (nCon n F δ) := by
  simp only [nCon, lieIp_sum, TT, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  conv_lhs => enter [2, α]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun γ _ => ?_
  ring

theorem TT_nn_right (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (n : Fin 4 → ℝ)
    (hF : ∀ α β, F β α = -F α β) (a : Fin 4 → Fin 4 → ℝ) :
    TT w F a (fun β δ => n β * n δ) = ∑ α, ∑ γ, a α γ * lieIp w (nCon n F α) (nCon n F γ) := by
  have hM : ∀ α, (∑ β, n β • F α β) = -nCon n F α := by
    intro α
    simp only [nCon, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [hF α β, smul_neg, neg_neg]
  have h2 : ∀ α γ, lieIp w (nCon n F α) (nCon n F γ) =
      ∑ β, ∑ δ, n β * n δ * lieIp w (F α β) (F γ δ) := by
    intro α γ
    rw [← lieIp_neg, ← hM, ← hM, lieIp_sum]
  simp only [h2, TT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun δ _ => ?_
  ring

theorem TT_nn_nn (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (n : Fin 4 → ℝ)
    (hF : ∀ α β, F β α = -F α β) :
    TT w F (fun α γ => n α * n γ) (fun β δ => n β * n δ) = 0 := by
  rw [TT_nn_left]
  have hS : (∑ β, n β • nCon n F β) = 0 := by
    have e : (∑ β, n β • nCon n F β) = ∑ β, ∑ μ, (n β * n μ) • F μ β := by
      simp only [nCon, Finset.smul_sum, smul_smul]
    have e2 : (∑ β, ∑ μ, (n β * n μ) • F μ β) = -∑ β, ∑ μ, (n β * n μ) • F μ β := by
      conv_lhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => ?_
      rw [hF μ β, smul_neg, mul_comm]
    rw [e]
    funext a
    have h := congrFun e2 a
    simp only [Pi.neg_apply] at h
    simp only [Pi.zero_apply]
    linarith
  have : lieIp w (∑ β, n β • nCon n F β) (∑ δ, n δ • nCon n F δ) =
      ∑ β, ∑ δ, n β * n δ * lieIp w (nCon n F β) (nCon n F δ) := lieIp_sum _ _ _ _ _
  rw [hS, show lieIp w 0 0 = 0 by simp [lieIp]] at this
  exact this.symm

/-- **`eq:YM-timelike-energy`, algebraic form**: for `g(n, n) = -1` and an antisymmetric `F`,
`T^{YM}(n, n) = ¼ h^{αγ} h^{βδ}⟨F_{αβ}, F_{γδ}⟩` with `h^{-1} = g^{-1} + 2 n ⊗ n`. -/
theorem timelike_ym (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) (hn : gnn G n = -1) (w : κ → ℝ)
    (F : Fin 4 → Fin 4 → κ → ℝ) (hF : ∀ α β, F β α = -F α β) :
    ∑ μ, ∑ ν, n μ * n ν * ymStress G w F μ ν = (1 / 4) * TT w F (hinv G n) (hinv G n) := by
  set gi := ginv G
  set nn : Fin 4 → Fin 4 → ℝ := fun α γ => n α * n γ
  have hh : hinv G n = gi + (2 : ℝ) • nn := by
    funext α β; simp [hinv, gi, nn]
  have hR : TT w F (hinv G n) (hinv G n) =
      TT w F gi gi + 2 * TT w F nn gi + 2 * TT w F gi nn + 4 * TT w F nn nn := by
    rw [hh, TT_add_left, TT_add_right, TT_add_right, TT_smul_left, TT_smul_left, TT_smul_right,
      TT_smul_right]
    ring
  have hgn : TT w F gi nn = TT w F nn gi := by
    rw [TT_nn_right w F n hF, TT_nn_left]
  have hnn : TT w F nn nn = 0 := TT_nn_nn w F n hF
  have hL : ∑ μ, ∑ ν, n μ * n ν * ymStress G w F μ ν =
      TT w F nn gi - (1 / 4) * gnn G n * TT w F gi gi := by
    have e1 : ∑ μ, ∑ ν, n μ * n ν * ∑ α, ∑ β, ginv G α β * lieIp w (F μ α) (F ν β) =
        TT w F nn gi := by
      simp only [TT, nn, gi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ =>
        Finset.sum_congr rfl fun δ _ => ?_
      ring
    have e2 : ∑ μ, ∑ ν, n μ * n ν * ((1 / 4) * G μ ν * TT w F gi gi) =
        (1 / 4) * gnn G n * TT w F gi gi := by
      simp only [gnn, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [ymStress, mul_sub]
    rfl
  rw [hL, hR, hgn, hnn, hn]
  ring

/-! ## Orthonormal frames with a prescribed time leg -/

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)`. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

theorem eta_mul_eta : eta * eta = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- `E` is a `g`-orthonormal frame (`Eᵀ g E = η`) whose time leg (column `0`) is `n`.  For a
Lorentzian metric `g`, the existence of such a frame is equivalent to `n` being a unit timelike
vector (`g(n, n) = -1`); it also records the signature `(-, +, +, +)` of `g`. -/
structure IsTimeFrame (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) (E : Matrix (Fin 4) (Fin 4) ℝ) :
    Prop where
  ortho : Eᵀ * mat G * E = eta
  time : ∀ μ, E μ 0 = n μ

section Frame

variable {G : Fin 4 → Fin 4 → ℝ} {n : Fin 4 → ℝ} {E : Matrix (Fin 4) (Fin 4) ℝ}

/-- A time leg is a unit timelike vector: `g(n, n) = -1`. -/
theorem IsTimeFrame.gnn_eq (hE : IsTimeFrame G n E) : gnn G n = -1 := by
  have h := congrFun (congrFun hE.ortho 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hE.time, mat_apply, eta,
    Matrix.diagonal_apply_eq] at h
  have e : gnn G n = ∑ ν, (∑ μ, n μ * G μ ν) * n ν := by
    simp only [gnn, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [e, h]
  simp

/-- The left inverse `M = η Eᵀ g` of the frame. -/
noncomputable def frameInv (G : Fin 4 → Fin 4 → ℝ) (E : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := eta * Eᵀ * mat G

theorem IsTimeFrame.frameInv_mul (hE : IsTimeFrame G n E) : frameInv G E * E = 1 := by
  rw [frameInv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hE.ortho, eta_mul_eta]

theorem IsTimeFrame.mul_frameInv (hE : IsTimeFrame G n E) : E * frameInv G E = 1 :=
  mul_eq_one_comm.1 hE.frameInv_mul

/-- The inverse metric in the frame: `g^{-1} = E η Eᵀ`. -/
theorem IsTimeFrame.inv_eq (hE : IsTimeFrame G n E) : (mat G)⁻¹ = E * eta * Eᵀ := by
  refine Matrix.inv_eq_left_inv ?_
  have : E * eta * Eᵀ * mat G = E * frameInv G E := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, hE.mul_frameInv]

/-- `h^{-1} = g^{-1} + 2 n ⊗ n = E Eᵀ` for a frame with time leg `n`. -/
theorem IsTimeFrame.hinv_eq (hE : IsTimeFrame G n E) (α β : Fin 4) :
    hinv G n α β = ∑ k, E α k * E β k := by
  simp only [hinv, ginv, hE.inv_eq, Matrix.mul_apply, Matrix.transpose_apply, eta, ← hE.time]
  simp only [Fin.sum_univ_four]
  simp
  ring

end Frame

/-! ## Moving finite sums -/

theorem sum4_comm {ι' : Type*} (s : Finset ι') (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ι' → ℝ) :
    ∑ α, ∑ β, ∑ γ, ∑ δ, ∑ k ∈ s, f α β γ δ k = ∑ k ∈ s, ∑ α, ∑ β, ∑ γ, ∑ δ, f α β γ δ k := by
  have h1 : ∀ α β γ, ∑ δ, ∑ k ∈ s, f α β γ δ k = ∑ k ∈ s, ∑ δ, f α β γ δ k :=
    fun _ _ _ => Finset.sum_comm
  have h2 : ∀ α β, ∑ γ, ∑ k ∈ s, ∑ δ, f α β γ δ k = ∑ k ∈ s, ∑ γ, ∑ δ, f α β γ δ k :=
    fun _ _ => Finset.sum_comm
  have h3 : ∀ α, ∑ β, ∑ k ∈ s, ∑ γ, ∑ δ, f α β γ δ k = ∑ k ∈ s, ∑ β, ∑ γ, ∑ δ, f α β γ δ k :=
    fun _ => Finset.sum_comm
  simp only [h1, h2, h3]
  exact Finset.sum_comm

theorem TT_sum_left {ι' : Type*} (s : Finset ι') (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ)
    (A : ι' → Fin 4 → Fin 4 → ℝ) (b : Fin 4 → Fin 4 → ℝ) :
    TT w F (fun α γ => ∑ k ∈ s, A k α γ) b = ∑ k ∈ s, TT w F (A k) b := by
  simp only [TT, Finset.sum_mul]
  exact sum4_comm s _

theorem TT_sum_right {ι' : Type*} (s : Finset ι') (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ)
    (a : Fin 4 → Fin 4 → ℝ) (B : ι' → Fin 4 → Fin 4 → ℝ) :
    TT w F a (fun β δ => ∑ k ∈ s, B k β δ) = ∑ k ∈ s, TT w F a (B k) := by
  simp only [TT, Finset.mul_sum, Finset.sum_mul]
  exact sum4_comm s _

/-- The frame components `F(e_k, e_l) = Σ_{μβ} E_{μk} E_{βl} F_{μβ}`. -/
def frameF (E : Matrix (Fin 4) (Fin 4) ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (k l : Fin 4) : κ → ℝ :=
  ∑ β, E β l • nCon (fun μ => E μ k) F β

/-- `h^{αγ} h^{βδ}⟨F_{αβ}, F_{γδ}⟩ = Σ_{kl} ⟨F(e_k, e_l), F(e_k, e_l)⟩` for `h^{-1} = E Eᵀ`. -/
theorem TT_frame (w : κ → ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (E : Matrix (Fin 4) (Fin 4) ℝ) :
    TT w F (fun α γ => ∑ k, E α k * E γ k) (fun β δ => ∑ l, E β l * E δ l) =
      ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l) := by
  rw [TT_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TT_sum_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TT_nn_left, frameF, lieIp_sum]

/-- The frame components `Y(e_k) = Σ_α E_{αk} Y_α`. -/
def frameY (E : Matrix (Fin 4) (Fin 4) ℝ) (Y : Fin 4 → κ → ℝ) (k : Fin 4) : κ → ℝ :=
  ∑ α, E α k • Y α

theorem kin_frame (E : Matrix (Fin 4) (Fin 4) ℝ) (Y : Fin 4 → κ → ℝ) :
    ∑ α, ∑ β, (∑ k, E α k * E β k) * lieIp (fun _ => 1) (Y α) (Y β) =
      ∑ k, lieIp (fun _ => 1) (frameY E Y k) (frameY E Y k) := by
  simp only [frameY, lieIp_sum, Finset.sum_mul]
  conv_lhs => enter [2, α]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

/-! ## Two-sided frame bounds -/

/-- `Σ_{αa} Y_{αa}²`. -/
def sqY (Y : Fin 4 → κ → ℝ) : ℝ := ∑ α, ∑ a, Y α a ^ 2

/-- `Σ_{αβa} F_{αβa}²`. -/
def sqF (F : Fin 4 → Fin 4 → κ → ℝ) : ℝ := ∑ α, ∑ β, ∑ a, F α β a ^ 2

/-- `Σ_{αk} E_{αk}²`. -/
def sqM (E : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∑ α, ∑ k, E α k ^ 2

theorem sqM_nonneg (E : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ sqM E :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqY_nonneg (Y : Fin 4 → κ → ℝ) : 0 ≤ sqY Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqF_nonneg (F : Fin 4 → Fin 4 → κ → ℝ) : 0 ≤ sqF F :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

theorem lieIp_one_self (u : κ → ℝ) : lieIp (fun _ => 1) u u = ∑ a, u a ^ 2 := by
  simp [lieIp, sq]

/-- Cauchy–Schwarz over pairs of indices. -/
theorem sq_sum_sum_le (f g : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, f i j * g i j) ^ 2 ≤ (∑ i, ∑ j, f i j ^ 2) * ∑ i, ∑ j, g i j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4 × Fin 4))
    (fun p => f p.1 p.2) (fun p => g p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

theorem frameY_apply (E : Matrix (Fin 4) (Fin 4) ℝ) (Y : Fin 4 → κ → ℝ) (k : Fin 4) (a : κ) :
    frameY E Y k a = ∑ α, E α k * Y α a := by
  simp [frameY, Finset.sum_apply]

theorem frameF_apply (E : Matrix (Fin 4) (Fin 4) ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) (k l : Fin 4)
    (a : κ) : frameF E F k l a = ∑ β, ∑ μ, (E β l * E μ k) * F μ β a := by
  simp [frameF, nCon, Finset.sum_apply, Finset.mul_sum, mul_assoc]

/-- Upper frame bound for the kinetic energy: `Σ_k |Y(e_k)|² ≤ (Σ E²) |Y|²`. -/
theorem kin_frame_upper (E : Matrix (Fin 4) (Fin 4) ℝ) (Y : Fin 4 → κ → ℝ) :
    ∑ k, lieIp (fun _ => 1) (frameY E Y k) (frameY E Y k) ≤ sqM E * sqY Y := by
  simp only [lieIp_one_self, frameY_apply]
  have h : ∀ k a, (∑ α, E α k * Y α a) ^ 2 ≤ (∑ α, E α k ^ 2) * ∑ α, Y α a ^ 2 :=
    fun k a => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ k, ∑ a, (∑ α, E α k * Y α a) ^ 2
      ≤ ∑ k, ∑ a, (∑ α, E α k ^ 2) * ∑ α, Y α a ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun a _ => h k a
    _ = sqM E * sqY Y := by
        simp only [sqM, sqY, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [Finset.sum_comm (f := fun α k => E α k ^ 2), Finset.sum_comm (f := fun α a => Y α a ^ 2)]

theorem frame_delta {E M : Matrix (Fin 4) (Fin 4) ℝ} (hEM : E * M = 1) (i j : Fin 4) :
    ∑ k, E i k * M k j = if i = j then 1 else 0 := by
  have := congrFun (congrFun hEM i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

/-- Lower frame bound for the kinetic energy: `|Y|² ≤ (Σ M²) Σ_k |Y(e_k)|²` for `E M = 1`. -/
theorem kin_frame_lower {E M : Matrix (Fin 4) (Fin 4) ℝ} (hEM : E * M = 1)
    (Y : Fin 4 → κ → ℝ) :
    sqY Y ≤ sqM Mᵀ * ∑ k, lieIp (fun _ => 1) (frameY E Y k) (frameY E Y k) := by
  simp only [lieIp_one_self]
  have hinv : ∀ α a, Y α a = ∑ k, M k α * frameY E Y k a := by
    intro α a
    simp only [frameY_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ β, ∑ k, M k α * (E β k * Y β a) = (∑ k, E β k * M k α) * Y β a := by
      intro β; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    simp only [this, frame_delta hEM]
    simp
  have h : ∀ α a, Y α a ^ 2 ≤ (∑ k, M k α ^ 2) * ∑ k, frameY E Y k a ^ 2 := by
    intro α a
    rw [hinv α a]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc sqY Y ≤ ∑ α, ∑ a, (∑ k, M k α ^ 2) * ∑ k, frameY E Y k a ^ 2 :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun a _ => h α a
    _ = sqM Mᵀ * ∑ k, ∑ a, frameY E Y k a ^ 2 := by
        simp only [sqM, Matrix.transpose_apply, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [Finset.sum_comm (f := fun k a => frameY E Y k a ^ 2)]

theorem sum_sq_col_le (E : Matrix (Fin 4) (Fin 4) ℝ) (l : Fin 4) : ∑ β, E β l ^ 2 ≤ sqM E :=
  Finset.sum_le_sum fun β _ => Finset.single_le_sum (f := fun k => E β k ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ l)

theorem sum_sum_sq_reorder (F : Fin 4 → Fin 4 → κ → ℝ) :
    ∑ a, ∑ β, ∑ μ, F μ β a ^ 2 = sqF F := by
  simp only [sqF]
  calc ∑ a, ∑ β, ∑ μ, F μ β a ^ 2 = ∑ β, ∑ a, ∑ μ, F μ β a ^ 2 := Finset.sum_comm
    _ = ∑ β, ∑ μ, ∑ a, F μ β a ^ 2 := Finset.sum_congr rfl fun β _ => Finset.sum_comm
    _ = ∑ μ, ∑ β, ∑ a, F μ β a ^ 2 := Finset.sum_comm

/-- Upper frame bound for the gauge energy: `Σ_{kl} |F(e_k, e_l)|² ≤ 16 (Σ E²)² |F|²`. -/
theorem ym_frame_upper (E : Matrix (Fin 4) (Fin 4) ℝ) (F : Fin 4 → Fin 4 → κ → ℝ) :
    ∑ k, ∑ l, ∑ a, frameF E F k l a ^ 2 ≤ 16 * sqM E ^ 2 * sqF F := by
  simp only [frameF_apply]
  have h : ∀ k l a, (∑ β, ∑ μ, (E β l * E μ k) * F μ β a) ^ 2 ≤
      sqM E ^ 2 * ∑ β, ∑ μ, F μ β a ^ 2 := by
    intro k l a
    refine (sq_sum_sum_le _ _).trans (mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have e : ∑ β, ∑ μ, (E β l * E μ k) ^ 2 = (∑ β, E β l ^ 2) * ∑ μ, E μ k ^ 2 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => ?_
      ring
    rw [e, sq]
    exact mul_le_mul (sum_sq_col_le E l) (sum_sq_col_le E k)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sqM_nonneg E)
  calc ∑ k, ∑ l, ∑ a, (∑ β, ∑ μ, (E β l * E μ k) * F μ β a) ^ 2
      ≤ ∑ k : Fin 4, ∑ l : Fin 4, ∑ a, sqM E ^ 2 * ∑ β, ∑ μ, F μ β a ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          Finset.sum_le_sum fun a _ => h k l a
    _ = 16 * sqM E ^ 2 * sqF F := by
        simp only [← Finset.mul_sum, sum_sum_sq_reorder, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The inversion formula `F_{μβ} = Σ_{kl} M_{kμ} M_{lβ} F(e_k, e_l)` for `E M = 1`. -/
theorem frameF_inv {E M : Matrix (Fin 4) (Fin 4) ℝ} (hEM : E * M = 1)
    (F : Fin 4 → Fin 4 → κ → ℝ) (μ β : Fin 4) (a : κ) :
    F μ β a = ∑ k, ∑ l, (M k μ * M l β) * frameF E F k l a := by
  simp only [frameF_apply, Finset.mul_sum]
  -- Σ_k Σ_l Σ_β' Σ_μ' (M k μ * M l β) * ((E β' l * E μ' k) * F μ' β' a)
  have e : ∀ k l, ∑ β', ∑ μ', M k μ * M l β * (E β' l * E μ' k * F μ' β' a) =
      ∑ μ', ∑ β', (E μ' k * M k μ) * (E β' l * M l β) * F μ' β' a := by
    intro k l
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ' _ => Finset.sum_congr rfl fun β' _ => ?_
    ring
  simp only [e]
  -- Σ_k Σ_l Σ_μ' Σ_β' → Σ_μ' Σ_β' Σ_k Σ_l
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, μ', 2, k]; rw [Finset.sum_comm]
  conv_rhs => enter [2, μ']; rw [Finset.sum_comm]
  have e2 : ∀ μ' β', ∑ k, ∑ l, (E μ' k * M k μ) * (E β' l * M l β) * F μ' β' a =
      (if μ' = μ then 1 else 0) * (if β' = β then 1 else 0) * F μ' β' a := by
    intro μ' β'
    rw [← frame_delta hEM, ← frame_delta hEM, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
  simp only [e2]
  simp

/-- Lower frame bound for the gauge energy: `|F|² ≤ (Σ M²)² Σ_{kl} |F(e_k, e_l)|²`. -/
theorem ym_frame_lower {E M : Matrix (Fin 4) (Fin 4) ℝ} (hEM : E * M = 1)
    (F : Fin 4 → Fin 4 → κ → ℝ) :
    sqF F ≤ sqM M ^ 2 * ∑ k, ∑ l, ∑ a, frameF E F k l a ^ 2 := by
  have h : ∀ μ β a, F μ β a ^ 2 ≤
      (∑ k, ∑ l, (M k μ * M l β) ^ 2) * ∑ k, ∑ l, frameF E F k l a ^ 2 := by
    intro μ β a
    rw [frameF_inv hEM F μ β a]
    exact sq_sum_sum_le _ _
  calc sqF F ≤ ∑ μ, ∑ β, ∑ a, (∑ k, ∑ l, (M k μ * M l β) ^ 2) *
        ∑ k, ∑ l, frameF E F k l a ^ 2 :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun β _ =>
          Finset.sum_le_sum fun a _ => h μ β a
    _ = (∑ μ, ∑ β, ∑ k, ∑ l, (M k μ * M l β) ^ 2) * ∑ a, ∑ k, ∑ l, frameF E F k l a ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = sqM M ^ 2 * ∑ k, ∑ l, ∑ a, frameF E F k l a ^ 2 := by
        congr 1
        · have e : ∀ μ β, ∑ k, ∑ l, (M k μ * M l β) ^ 2 =
              (∑ k, M k μ ^ 2) * ∑ l, M l β ^ 2 := by
            intro μ β
            rw [Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            ring
          simp only [e, ← Finset.mul_sum, ← Finset.sum_mul]
          rw [sq, sqM, Finset.sum_comm (f := fun α k => M α k ^ 2)]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]


/-! ## Timelike coercivity of the stress quadratic forms (pointwise) -/

theorem qf_sum_left {ι ι' : Type*} [Fintype ι] (s : Finset ι') (b : ι' → ι → ι → ℝ) (z : ι → ℝ) :
    qf (∑ k ∈ s, b k) z = ∑ k ∈ s, qf (b k) z := by
  simp only [qf, Finset.sum_apply, Finset.sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  exact Finset.sum_comm

/-- The `(n, n)` contraction of a family of coefficient arrays. -/
def nnCoef {ι : Type*} (n : Fin 4 → ℝ) (b : Fin 4 → Fin 4 → ι → ι → ℝ) : ι → ι → ℝ :=
  ∑ μ, ∑ ν, (n μ * n ν) • b μ ν

theorem qf_nnCoef {ι : Type*} [Fintype ι] (n : Fin 4 → ℝ) (b : Fin 4 → Fin 4 → ι → ι → ℝ)
    (z : ι → ℝ) : qf (nnCoef n b) z = ∑ μ, ∑ ν, n μ * n ν * qf (b μ ν) z := by
  simp only [nnCoef, qf_sum_left, qf_smul_left]

/-- `Σ_α h^{αα}` (equal to `Σ E²` for any frame with time leg `n`). -/
noncomputable def trH (G : Fin 4 → Fin 4 → ℝ) (n : Fin 4 → ℝ) : ℝ := ∑ α, hinv G n α α

/-- `Σ g_{μν}²`. -/
def sqG (G : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ μ, ∑ ν, G μ ν ^ 2

theorem sqG_nonneg (G : Fin 4 → Fin 4 → ℝ) : 0 ≤ sqG G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

section FrameBounds

variable {G : Fin 4 → Fin 4 → ℝ} {n : Fin 4 → ℝ} {E : Matrix (Fin 4) (Fin 4) ℝ}

theorem IsTimeFrame.sqM_eq (hE : IsTimeFrame G n E) : sqM E = trH G n := by
  simp only [sqM, trH, hE.hinv_eq, sq]

theorem sqM_transpose (M : Matrix (Fin 4) (Fin 4) ℝ) : sqM Mᵀ = sqM M := by
  simp only [sqM, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem sqM_frameInv_le (G : Fin 4 → Fin 4 → ℝ) (E : Matrix (Fin 4) (Fin 4) ℝ) :
    sqM (frameInv G E) ≤ sqM E * sqG G := by
  have hM : ∀ k α, frameInv G E k α ^ 2 = (∑ j, E j k * G j α) ^ 2 := by
    intro k α
    have : frameInv G E k α = (![-1, 1, 1, 1] : Fin 4 → ℝ) k * ∑ j, E j k * G j α := by
      simp only [frameInv, eta, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
        mat_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, mul_pow]
    have hd : ((![-1, 1, 1, 1] : Fin 4 → ℝ) k) ^ 2 = 1 := by fin_cases k <;> norm_num
    rw [hd, one_mul]
  have hb : ∀ k α, frameInv G E k α ^ 2 ≤ (∑ j, E j k ^ 2) * ∑ j, G j α ^ 2 := by
    intro k α
    rw [hM]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc sqM (frameInv G E) ≤ ∑ k, ∑ α, (∑ j, E j k ^ 2) * ∑ j, G j α ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun α _ => hb k α
    _ = sqM E * sqG G := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sqM, sqG]
        rw [Finset.sum_comm (f := fun α k => E α k ^ 2),
          Finset.sum_comm (f := fun μ ν => G μ ν ^ 2)]

end FrameBounds

/-- Unflattening of a realified two-form packet. -/
def unflatF (z : (Fin 4 × Fin 4) × κ → ℝ) : Fin 4 → Fin 4 → κ → ℝ := fun α β a => z ((α, β), a)

/-- Unflattening of a realified one-form packet. -/
def unflatY (z : Fin 4 × κ → ℝ) : Fin 4 → κ → ℝ := fun α a => z (α, a)

theorem flat_unflatF (z : (Fin 4 × Fin 4) × κ → ℝ) :
    (flat fun p : Fin 4 × Fin 4 => unflatF z p.1 p.2) = z := by
  funext p; rfl

theorem flat_unflatY (z : Fin 4 × κ → ℝ) : flat (unflatY z) = z := by
  funext p; rfl

theorem sum_sq_eq_sqF (z : (Fin 4 × Fin 4) × κ → ℝ) : ∑ p, z p ^ 2 = sqF (unflatF z) := by
  simp only [sqF, unflatF, Fintype.sum_prod_type]

theorem sum_sq_eq_sqY (z : Fin 4 × κ → ℝ) : ∑ p, z p ^ 2 = sqY (unflatY z) := by
  simp only [sqY, unflatY, Fintype.sum_prod_type]

theorem lieIp_le (w : κ → ℝ) {Cw : ℝ} (hw : ∀ a, w a ≤ Cw) (u : κ → ℝ) :
    lieIp w u u ≤ Cw * ∑ a, u a ^ 2 := by
  simp only [lieIp, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    rw [← sq]; exact mul_le_mul_of_nonneg_right (hw a) (sq_nonneg _)

theorem le_lieIp (w : κ → ℝ) {cw : ℝ} (hw : ∀ a, cw ≤ w a) (u : κ → ℝ) :
    cw * ∑ a, u a ^ 2 ≤ lieIp w u u := by
  simp only [lieIp, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => by
    rw [← sq]; exact mul_le_mul_of_nonneg_right (hw a) (sq_nonneg _)

/-- `(n,n)`-contracted Yang–Mills coefficient in the frame:
`qf(Σ nn B^{μν}) z = V · ¼ Σ_{kl} ⟨F(e_k, e_l), F(e_k, e_l)⟩`. -/
theorem qf_nn_ymCoef [DecidableEq κ] {G : Fin 4 → Fin 4 → ℝ} {n : Fin 4 → ℝ}
    {E : Matrix (Fin 4) (Fin 4) ℝ} (hE : IsTimeFrame G n E) (w : κ → ℝ) (V : ℝ)
    (z : (Fin 4 × Fin 4) × κ → ℝ) (hz : ∀ α β a, z ((β, α), a) = -z ((α, β), a)) :
    qf (nnCoef n fun μ ν => ymCoef G w V μ ν) z =
      V * ((1 / 4) * ∑ k, ∑ l, lieIp w (frameF E (unflatF z) k l) (frameF E (unflatF z) k l)) := by
  have hF : ∀ α β, unflatF z β α = -unflatF z α β := fun α β => by
    funext a; simp only [unflatF, Pi.neg_apply]; exact hz α β a
  rw [qf_nnCoef]
  conv_lhs => rw [← flat_unflatF z]
  simp only [qf_ymCoef]
  have : ∑ μ, ∑ ν, n μ * n ν * (V * ymStress G w (unflatF z) μ ν) =
      V * ∑ μ, ∑ ν, n μ * n ν * ymStress G w (unflatF z) μ ν := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [this, timelike_ym G n hE.gnn_eq w _ hF]
  have e : hinv G n = fun α γ => ∑ k, E α k * E γ k := by
    funext α γ; exact hE.hinv_eq α γ
  rw [e, TT_frame]

/-- `(n,n)`-contracted kinetic Higgs coefficient in the frame:
`qf(Σ nn B^{μν}) z = V Σ_k |Y(e_k)|²`. -/
theorem qf_nn_kinCoef [DecidableEq κ] {G : Fin 4 → Fin 4 → ℝ} {n : Fin 4 → ℝ}
    {E : Matrix (Fin 4) (Fin 4) ℝ} (hE : IsTimeFrame G n E) (V : ℝ) (z : Fin 4 × κ → ℝ) :
    qf (nnCoef n fun μ ν => kinCoef (κ := κ) G V μ ν) z =
      V * ∑ k, lieIp (fun _ => 1) (frameY E (unflatY z) k) (frameY E (unflatY z) k) := by
  rw [qf_nnCoef]
  conv_lhs => rw [← flat_unflatY z]
  simp only [qf_kinCoef]
  have : ∑ μ, ∑ ν, n μ * n ν * (V * higgsKin G (unflatY z) μ ν) =
      V * ∑ μ, ∑ ν, n μ * n ν * higgsKin G (unflatY z) μ ν := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [this, timelike_kin G n hE.gnn_eq, ← kin_frame]
  congr 1
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hE.hinv_eq]
  simp [lieIp]

section Coercive

variable [DecidableEq κ] {G : Fin 4 → Fin 4 → ℝ} {n : Fin 4 → ℝ} {E : Matrix (Fin 4) (Fin 4) ℝ}

theorem IsTimeFrame.trH_nonneg (hE : IsTimeFrame G n E) : 0 ≤ trH G n :=
  hE.sqM_eq ▸ sqM_nonneg E

/-- **Lower timelike bound, Yang–Mills** (`eq:timelike-defect-coercivity`, pointwise):
`V cw |z|² ≤ 4 (trH · Σ g²)² · qf(Σ n^μ n^ν B^{μν}_{YM}) z` on antisymmetric two-forms. -/
theorem ym_nn_lower (hE : IsTimeFrame G n E) (w : κ → ℝ) {cw : ℝ} (hcw : ∀ a, cw ≤ w a)
    (hcw0 : 0 ≤ cw) {V : ℝ} (hV : 0 ≤ V) (z : (Fin 4 × Fin 4) × κ → ℝ)
    (hz : ∀ α β a, z ((β, α), a) = -z ((α, β), a)) :
    V * cw * ∑ p, z p ^ 2 ≤
      4 * (trH G n * sqG G) ^ 2 * qf (nnCoef n fun μ ν => ymCoef G w V μ ν) z := by
  rw [qf_nn_ymCoef hE w V z hz, sum_sq_eq_sqF]
  set F := unflatF z
  set S := ∑ k, ∑ l, ∑ a, frameF E F k l a ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow : cw * S ≤ ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l) := by
    simp only [S, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
      rw [← Finset.mul_sum]; exact le_lieIp w hcw _
  have hL : sqF F ≤ sqM (frameInv G E) ^ 2 * S := ym_frame_lower hE.mul_frameInv F
  have hMb : sqM (frameInv G E) ≤ trH G n * sqG G := hE.sqM_eq ▸ sqM_frameInv_le G E
  have hMb2 : sqM (frameInv G E) ^ 2 ≤ (trH G n * sqG G) ^ 2 :=
    pow_le_pow_left₀ (sqM_nonneg _) hMb 2
  have h1 : sqF F ≤ (trH G n * sqG G) ^ 2 * S :=
    hL.trans (mul_le_mul_of_nonneg_right hMb2 hS0)
  have h2 : cw * sqF F ≤ (trH G n * sqG G) ^ 2 * ∑ k, ∑ l,
      lieIp w (frameF E F k l) (frameF E F k l) := by
    calc cw * sqF F ≤ cw * ((trH G n * sqG G) ^ 2 * S) := mul_le_mul_of_nonneg_left h1 hcw0
      _ = (trH G n * sqG G) ^ 2 * (cw * S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left h2 hV
  calc V * cw * sqF F = V * (cw * sqF F) := by ring
    _ ≤ V * ((trH G n * sqG G) ^ 2 * ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l)) := h3
    _ = _ := by ring

/-- **Upper timelike bound, Yang–Mills**: `qf(Σ n^μ n^ν B^{μν}_{YM}) z ≤ 4 Cw trH² V |z|²`. -/
theorem ym_nn_upper (hE : IsTimeFrame G n E) (w : κ → ℝ) {Cw : ℝ} (hCw : ∀ a, w a ≤ Cw)
    (hCw0 : 0 ≤ Cw) {V : ℝ} (hV : 0 ≤ V) (z : (Fin 4 × Fin 4) × κ → ℝ)
    (hz : ∀ α β a, z ((β, α), a) = -z ((α, β), a)) :
    qf (nnCoef n fun μ ν => ymCoef G w V μ ν) z ≤ 4 * Cw * trH G n ^ 2 * V * ∑ p, z p ^ 2 := by
  rw [qf_nn_ymCoef hE w V z hz, sum_sq_eq_sqF]
  set F := unflatF z
  set S := ∑ k, ∑ l, ∑ a, frameF E F k l a ^ 2
  have hupp : ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l) ≤ Cw * S := by
    simp only [S, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
      rw [← Finset.mul_sum]; exact lieIp_le w hCw _
  have hU : S ≤ 16 * trH G n ^ 2 * sqF F := hE.sqM_eq ▸ ym_frame_upper E F
  have h1 : ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l) ≤
      Cw * (16 * trH G n ^ 2 * sqF F) := hupp.trans (mul_le_mul_of_nonneg_left hU hCw0)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ V * (1 / 4))
  calc V * ((1 / 4) * ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l))
      = V * (1 / 4) * ∑ k, ∑ l, lieIp w (frameF E F k l) (frameF E F k l) := by ring
    _ ≤ V * (1 / 4) * (Cw * (16 * trH G n ^ 2 * sqF F)) := h2
    _ = 4 * Cw * trH G n ^ 2 * V * sqF F := by ring

/-- **Lower timelike bound, Higgs kinetic stress**:
`V |z|² ≤ trH · Σ g² · qf(Σ n^μ n^ν B^{μν}_{kin}) z`. -/
theorem kin_nn_lower (hE : IsTimeFrame G n E) {V : ℝ} (hV : 0 ≤ V) (z : Fin 4 × κ → ℝ) :
    V * ∑ p, z p ^ 2 ≤
      trH G n * sqG G * qf (nnCoef n fun μ ν => kinCoef (κ := κ) G V μ ν) z := by
  rw [qf_nn_kinCoef hE V z, sum_sq_eq_sqY]
  set Y := unflatY z
  set S := ∑ k, lieIp (fun _ => 1) (frameY E Y k) (frameY E Y k)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by
    rw [lieIp_one_self]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL : sqY Y ≤ sqM (frameInv G E)ᵀ * S := kin_frame_lower hE.mul_frameInv Y
  rw [sqM_transpose] at hL
  have hMb : sqM (frameInv G E) ≤ trH G n * sqG G := hE.sqM_eq ▸ sqM_frameInv_le G E
  have h1 : sqY Y ≤ trH G n * sqG G * S := hL.trans (mul_le_mul_of_nonneg_right hMb hS0)
  have h2 := mul_le_mul_of_nonneg_left h1 hV
  calc V * sqY Y ≤ V * (trH G n * sqG G * S) := h2
    _ = trH G n * sqG G * (V * S) := by ring

/-- **Upper timelike bound, Higgs kinetic stress**:
`qf(Σ n^μ n^ν B^{μν}_{kin}) z ≤ trH · V |z|²`. -/
theorem kin_nn_upper (hE : IsTimeFrame G n E) {V : ℝ} (hV : 0 ≤ V) (z : Fin 4 × κ → ℝ) :
    qf (nnCoef n fun μ ν => kinCoef (κ := κ) G V μ ν) z ≤ trH G n * V * ∑ p, z p ^ 2 := by
  rw [qf_nn_kinCoef hE V z, sum_sq_eq_sqY]
  have hU := kin_frame_upper E (unflatY z)
  rw [hE.sqM_eq] at hU
  have := mul_le_mul_of_nonneg_left hU hV
  calc V * ∑ k, lieIp (fun _ => 1) (frameY E (unflatY z) k) (frameY E (unflatY z) k)
      ≤ V * (trH G n * sqY (unflatY z)) := this
    _ = trH G n * V * sqY (unflatY z) := by ring

end Coercive

/-! ## Orthonormal frames from the Lorentzian signature -/

/-- The Lorentz boost `Λ` with `Λ e₀ = u` (for a future unit timelike `u`, `η(u,u) = -1`). -/
noncomputable def boost (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if i = 0 then u j else if j = 0 then u i else
    (if i = j then 1 else 0) + u i * u j / (1 + u 0)

theorem boost_ortho (u : Fin 4 → ℝ) (hu : -u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = -1)
    (h0 : 0 < u 0) : Matrix.transpose (boost u) * eta * boost u = eta := by
  have h1 : (1 + u 0) ≠ 0 := by linarith
  ext i j
  simp only [boost, eta, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
    (first
      | linear_combination (1) * hu
      | linear_combination (u 1) * hu
      | linear_combination (u 2) * hu
      | linear_combination (u 3) * hu
      | linear_combination (u 1 * u 2) * hu
      | linear_combination (u 1 * u 3) * hu
      | linear_combination (u 2 * u 3) * hu
      | linear_combination (u 1 ^ 2) * hu
      | linear_combination (u 2 ^ 2) * hu
      | linear_combination (u 3 ^ 2) * hu)

theorem boost_col0 (u : Fin 4 → ℝ) (k : Fin 4) : boost u k 0 = u k := by
  by_cases hk : k = 0
  · subst hk; simp [boost]
  · simp [boost, hk]

/-- **Frames from the signature**: if `g = Pᵀ η P` with `P` invertible (signature `(-,+,+,+)`)
and `g(n, n) = -1`, then `n` is the time leg of a `g`-orthonormal frame `E = P⁻¹ Λ` (`Λ` a boost,
composed with `-1` if `P n` is past-directed). -/
theorem exists_isTimeFrame {G : Fin 4 → Fin 4 → ℝ} {P : Matrix (Fin 4) (Fin 4) ℝ}
    (hP : IsUnit P.det) (hG : mat G = Matrix.transpose P * eta * P) {n : Fin 4 → ℝ}
    (hn : gnn G n = -1) : ∃ E, IsTimeFrame G n E := by
  set u : Fin 4 → ℝ := P.mulVec n
  have hGe : ∀ μ ν, G μ ν = ∑ a, P a μ * eta a a * P a ν := by
    intro μ ν
    have := congrFun (congrFun hG μ) ν
    simp only [mat_apply] at this
    rw [this]
    simp only [eta, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four]
    simp
  have hu : -u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = -1 := by
    rw [← hn]
    simp only [gnn, hGe, u, Matrix.mulVec, dotProduct, eta, Matrix.diagonal_apply,
      Fin.sum_univ_four]
    simp
    ring
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPPT : Matrix.transpose P⁻¹ * Matrix.transpose P = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hinvu : P⁻¹.mulVec u = n := by
    simp only [u, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]
  have key : ∀ Λ : Matrix (Fin 4) (Fin 4) ℝ, Matrix.transpose Λ * eta * Λ = eta →
      (∀ k, Λ k 0 = u k) → IsTimeFrame G n (P⁻¹ * Λ) := by
    intro Λ hΛ hcol
    refine ⟨?_, fun μ => ?_⟩
    · rw [hG, Matrix.transpose_mul]
      calc Matrix.transpose Λ * Matrix.transpose P⁻¹ * (Matrix.transpose P * eta * P) *
            (P⁻¹ * Λ)
          = Matrix.transpose Λ * (Matrix.transpose P⁻¹ * Matrix.transpose P) * eta *
              (P * P⁻¹) * Λ := by simp only [Matrix.mul_assoc]
        _ = eta := by rw [hPPT, hPP, Matrix.mul_one, Matrix.mul_one, hΛ]
    · rw [Matrix.mul_apply]
      simp only [hcol]
      have := congrFun hinvu μ
      simpa [Matrix.mulVec, dotProduct] using this
  have hu0 : u 0 ≠ 0 := by
    intro h0
    rw [h0] at hu
    nlinarith [sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · refine ⟨P⁻¹ * (-boost (-u)), key _ ?_ fun k => ?_⟩
    · have := boost_ortho (-u) (by simp only [Pi.neg_apply, neg_sq]; exact hu)
        (by simp only [Pi.neg_apply]; linarith)
      rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, this]
    · simp [boost_col0]
  · exact ⟨P⁻¹ * boost u, key _ (boost_ortho u hu hpos) fun k => boost_col0 u k⟩

end BosonicStress

end RenewalGeometry
