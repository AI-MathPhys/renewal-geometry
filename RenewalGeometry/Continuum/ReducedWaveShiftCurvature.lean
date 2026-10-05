/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabCurvature
import RenewalGeometry.Continuum.ReducedWaveShiftCauchy

/-!
# `thm:hyperbolic`, curvature clause, with a nonzero shift: `Riem(g_h)` is Cauchy in `L¹_tH^{s-3}`

The uniform Lipschitz calculus of `ReducedWaveSlabLipschitz.lean` and the curvature estimates of
`ReducedWaveSlabCurvature.lean` use the positivity of `g^{ij}` only through the smoothness of the
difference forcing; here they are restated (`CtxS`, `CtxS.Good` without a sign condition on the
`γ`-coercivity constant, admissible data `MetricHyp` with any constant, e.g. the vacuous `-3Λ` of
`MetricHypSh.toMetricHyp`) so that they apply under the paper's hypothesis (uniform hyperbolicity
with a common time function, any bounded shift).

* `CtxS.UHi`, `CtxS.ULo`, `CtxS.uhi_evalF`, `CtxS.ulo_D2`, `CtxS.uhi_Gam`, `CtxS.ulo_dGam`,
  `CtxS.ulo_Riem` — as in the original files;
* **`riem_cauchy_sh`** — `∫₀ᵀ ‖Riem(g_h) - Riem(g_j)‖_{H^{s-3}} dt → 0` under `MetricHypSh`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg ReducedWaveStab SlabWaveShift

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- The common data of `thm:hyperbolic`. -/
structure CtxS (κ : Type) [Fintype κ] where
  Np : Idx → MvPolynomial (NV κ) ℝ
  θ : κ → X → ℝ
  k : ℕ
  T : ℝ
  a0 : ℝ
  lam : ℝ
  Λ : ℝ
  K0 : ℝ

namespace CtxS

variable (C : CtxS κ)

/-- Admissible metric data. -/
def Adm (m : MD) : Prop :=
  MetricHyp C.Np C.θ (C.k + 2) C.T C.a0 C.lam C.Λ C.K0 m.1 m.2.1 m.2.2

/-- `Z(m) = ‖𝒮‖²_{H^k}`. -/
def Zs (m : MD) (t : ℝ) : ℝ := ∑ c, Q C.k (m.2.2 c) t

/-- `Δ(m, m') = W (1 + Z(m) + Z(m')) + ‖𝒮 - 𝒮'‖²_{H^k}`. -/
def Dl (m m' : MD) (t : ℝ) : ℝ :=
  Wn C.k m.1 m'.1 t * (1 + C.Zs m t + C.Zs m' t) + ∑ c, Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t

/-- The standing assumptions on the common constants. -/
structure Good : Prop where
  hk : 3 ≤ C.k
  hT : 0 < C.T
  ha : 0 < C.a0
  hθ : ∀ j, ContDiff ℝ ∞ (C.θ j)
  hK0 : 0 ≤ C.K0

/-- Uniformly bounded and Lipschitz in `H^k`. -/
def UHi (Φ : MD → X → ℝ) : Prop :=
  (∀ m, C.Adm m → ContDiff ℝ ∞ (Φ m)) ∧ (∀ m, C.Adm m → IsSPeriodic (Φ m)) ∧
  ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ m m', C.Adm m → C.Adm m' → ∀ t ∈ Icc 0 C.T,
    Q C.k (Φ m) t ≤ B ∧ Q C.k (fun x => Φ m x - Φ m' x) t ≤ L * Wn C.k m.1 m'.1 t

/-- Bounded and Lipschitz in `H^{k-1}`, with the source weights. -/
def ULo (Φ : MD → X → ℝ) : Prop :=
  (∀ m, C.Adm m → ContDiff ℝ ∞ (Φ m)) ∧ (∀ m, C.Adm m → IsSPeriodic (Φ m)) ∧
  ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ m m', C.Adm m → C.Adm m' → ∀ t ∈ Icc 0 C.T,
    Q (C.k - 1) (Φ m) t ≤ B * (1 + C.Zs m t) ∧
      Q (C.k - 1) (fun x => Φ m x - Φ m' x) t ≤ L * C.Dl m m' t

variable {C}

theorem Zs_nonneg (m : MD) (t : ℝ) : 0 ≤ C.Zs m t :=
  Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _

theorem Dl_nonneg (m m' : MD) (t : ℝ) : 0 ≤ C.Dl m m' t := by
  unfold Dl
  have := Zs_nonneg (C := C) m t; have := Zs_nonneg (C := C) m' t
  have := Wn_nonneg C.k m.1 m'.1 t
  have : 0 ≤ ∑ c, Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t :=
    Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  positivity

theorem W_le_Dl (m m' : MD) (t : ℝ) : Wn C.k m.1 m'.1 t ≤ C.Dl m m' t := by
  unfold Dl
  have := Zs_nonneg (C := C) m t; have := Zs_nonneg (C := C) m' t
  have := Wn_nonneg C.k m.1 m'.1 t
  have : 0 ≤ ∑ c, Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t :=
    Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  nlinarith

theorem WZ_le_Dl (m m' : MD) (t : ℝ) : Wn C.k m.1 m'.1 t * (1 + C.Zs m t) ≤ C.Dl m m' t := by
  unfold Dl
  have := Zs_nonneg (C := C) m t; have := Zs_nonneg (C := C) m' t
  have := Wn_nonneg C.k m.1 m'.1 t
  have : 0 ≤ ∑ c, Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t :=
    Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  nlinarith

theorem WZ'_le_Dl (m m' : MD) (t : ℝ) : Wn C.k m.1 m'.1 t * (1 + C.Zs m' t) ≤ C.Dl m m' t := by
  unfold Dl
  have := Zs_nonneg (C := C) m t; have := Zs_nonneg (C := C) m' t
  have := Wn_nonneg C.k m.1 m'.1 t
  have : 0 ≤ ∑ c, Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t :=
    Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
  nlinarith

theorem dS_le_Dl (m m' : MD) (t : ℝ) (c : Idx) :
    Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t ≤ C.Dl m m' t := by
  unfold Dl
  have := Zs_nonneg (C := C) m t; have := Zs_nonneg (C := C) m' t
  have := Wn_nonneg C.k m.1 m'.1 t
  have := Finset.single_le_sum (f := fun c => Q C.k (fun x => m.2.2 c x - m'.2.2 c x) t)
    (fun _ _ => Q_nonneg _ _ _) (Finset.mem_univ c)
  nlinarith

theorem Q_le_Zs (m : MD) (t : ℝ) (c : Idx) : Q C.k (m.2.2 c) t ≤ C.Zs m t :=
  Finset.single_le_sum (f := fun c => Q C.k (m.2.2 c) t) (fun _ _ => Q_nonneg _ _ _)
    (Finset.mem_univ c)

/-! ### Combinators -/

theorem UHi.add {Φ Ψ : MD → X → ℝ} (hΦ : C.UHi Φ) (hΨ : C.UHi Ψ) :
    C.UHi (fun m x => Φ m x + Ψ m x) := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  obtain ⟨s2, p2, B2, L2, hB2, hL2, h2⟩ := hΨ
  refine ⟨fun m hm => (s1 m hm).add (s2 m hm), fun m hm => isSPeriodic_add' (p1 m hm) (p2 m hm), 2 * B1 + 2 * B2, 2 * L1 + 2 * L2, by positivity,
    by positivity, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · obtain ⟨a1, _⟩ := h1 m m' hm hm' t ht
    obtain ⟨a2, _⟩ := h2 m m' hm hm' t ht
    exact (Q_add_le _ (s1 m hm) (s2 m hm) t).trans (by linarith)
  · obtain ⟨_, b1⟩ := h1 m m' hm hm' t ht
    obtain ⟨_, b2⟩ := h2 m m' hm hm' t ht
    have e : (fun x => Φ m x + Ψ m x - (Φ m' x + Ψ m' x)) =
        fun x => (Φ m x - Φ m' x) + (Ψ m x - Ψ m' x) := by funext x; ring
    rw [e]
    refine (Q_add_le _ ((s1 m hm).sub (s1 m' hm')) ((s2 m hm).sub (s2 m' hm')) t).trans ?_
    nlinarith [Wn_nonneg C.k m.1 m'.1 t]


theorem UHi.const_mul {Φ : MD → X → ℝ} (hΦ : C.UHi Φ) (a : ℝ) :
    C.UHi (fun m x => a * Φ m x) := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  refine ⟨fun m hm => contDiff_const.mul (s1 m hm), fun m hm => isSPeriodic_const_mul' (p1 m hm) a,
    a ^ 2 * B1, a ^ 2 * L1, by positivity, by positivity, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · rw [Q_const_mul _ (s1 m hm)]
    exact mul_le_mul_of_nonneg_left (h1 m m' hm hm' t ht).1 (sq_nonneg _)
  · have e : (fun x => a * Φ m x - a * Φ m' x) = fun x => a * (Φ m x - Φ m' x) := by
      funext x; ring
    rw [e, Q_const_mul _ ((s1 m hm).sub (s1 m' hm'))]
    calc a ^ 2 * Q C.k (fun x => Φ m x - Φ m' x) t ≤ a ^ 2 * (L1 * Wn C.k m.1 m'.1 t) :=
          mul_le_mul_of_nonneg_left (h1 m m' hm hm' t ht).2 (sq_nonneg _)
      _ = _ := by ring

theorem UHi.mul (hk : 3 ≤ C.k) {Φ Ψ : MD → X → ℝ} (hΦ : C.UHi Φ) (hΨ : C.UHi Ψ) :
    C.UHi (fun m x => Φ m x * Ψ m x) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hk2 : 2 * 2 ≤ C.k + 1 := by omega
  set Ca := algC 3 C.k CS
  have hCa : 0 ≤ Ca := algC_nonneg _ hCS
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  obtain ⟨s2, p2, B2, L2, hB2, hL2, h2⟩ := hΨ
  refine ⟨fun m hm => (s1 m hm).mul (s2 m hm), fun m hm => isSPeriodic_mul (p1 m hm) (p2 m hm),
    Ca * B1 * B2, 2 * Ca * (L1 * B2 + B1 * L2), by positivity, by positivity,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · refine (Q_mul_le hk2 hCS hsup (s1 m hm) (s2 m hm) (p1 m hm) (p2 m hm) t).trans ?_
    have q1 := (h1 m m' hm hm' t ht).1
    have q2 := (h2 m m' hm hm' t ht).1
    have n1 := Q_nonneg C.k (Φ m) t
    have n2 := Q_nonneg C.k (Ψ m) t
    have : Ca * Q C.k (Φ m) t * Q C.k (Ψ m) t ≤ Ca * B1 * B2 := by gcongr
    exact this
  · have e : (fun x => Φ m x * Ψ m x - Φ m' x * Ψ m' x) =
        fun x => (Φ m x - Φ m' x) * Ψ m x + Φ m' x * (Ψ m x - Ψ m' x) := by funext x; ring
    rw [e]
    have sd1 := (s1 m hm).sub (s1 m' hm')
    have sd2 := (s2 m hm).sub (s2 m' hm')
    refine (Q_add_le _ (sd1.mul (s2 m hm)) ((s1 m' hm').mul sd2) t).trans ?_
    have m1 := Q_mul_le hk2 hCS hsup sd1 (s2 m hm) (isSPeriodic_sub' (p1 m hm) (p1 m' hm'))
      (p2 m hm) t
    have m2 := Q_mul_le hk2 hCS hsup (s1 m' hm') sd2 (p1 m' hm')
      (isSPeriodic_sub' (p2 m hm) (p2 m' hm')) t
    obtain ⟨a1, b1⟩ := h1 m m' hm hm' t ht
    obtain ⟨a1', _⟩ := h1 m' m hm' hm t ht
    obtain ⟨a2, b2⟩ := h2 m m' hm hm' t ht
    have n1 := Q_nonneg C.k (fun x => Φ m x - Φ m' x) t
    have n2 := Q_nonneg C.k (Ψ m) t
    have n3 := Q_nonneg C.k (Φ m') t
    have n4 := Q_nonneg C.k (fun x => Ψ m x - Ψ m' x) t
    have hW := Wn_nonneg C.k m.1 m'.1 t
    have c1 : Ca * Q C.k (fun x => Φ m x - Φ m' x) t * Q C.k (Ψ m) t ≤
        Ca * (L1 * Wn C.k m.1 m'.1 t) * B2 := by gcongr
    have c2 : Ca * Q C.k (Φ m') t * Q C.k (fun x => Ψ m x - Ψ m' x) t ≤
        Ca * B1 * (L2 * Wn C.k m.1 m'.1 t) := by gcongr
    nlinarith

theorem UHi.sum {ι : Type*} [Fintype ι] {Φ : ι → MD → X → ℝ} (hΦ : ∀ i, C.UHi (Φ i)) :
    C.UHi (fun m x => ∑ i, Φ i m x) := by
  choose s1 p1 h1 using hΦ
  choose B L hB hL hb using h1
  refine ⟨fun m hm => ContDiff.sum fun i _ => s1 i m hm,
    fun m hm => isSPeriodic_sum' _ fun i => p1 i m hm,
    Fintype.card ι * ∑ i, B i, Fintype.card ι * ∑ i, L i,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hB i),
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hL i),
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · refine (Q_sum_le _ Finset.univ (fun i => s1 i m hm) t).trans ?_
    rw [Finset.card_univ]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hb i m m' hm hm' t ht).1)
      (Nat.cast_nonneg _)
  · have e : (fun x => ∑ i, Φ i m x - ∑ i, Φ i m' x) = fun x => ∑ i, (Φ i m x - Φ i m' x) := by
      funext x; rw [Finset.sum_sub_distrib]
    rw [e]
    refine (Q_sum_le _ Finset.univ (fun i => (s1 i m hm).sub (s1 i m' hm')) t).trans ?_
    rw [Finset.card_univ]
    calc (Fintype.card ι : ℝ) * ∑ i, Q C.k (fun x => Φ i m x - Φ i m' x) t ≤
        (Fintype.card ι : ℝ) * ∑ i, (L i * Wn C.k m.1 m'.1 t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hb i m m' hm hm' t ht).2)
            (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring

theorem UHi.toLo {Φ : MD → X → ℝ} (hΦ : C.UHi Φ) : C.ULo Φ := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  refine ⟨s1, p1, B1, L1, hB1, hL1, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · refine (Q_mono (Nat.sub_le _ _) _ t).trans ((h1 m m' hm hm' t ht).1.trans ?_)
    have := Zs_nonneg (C := C) m t
    nlinarith
  · refine (Q_mono (Nat.sub_le _ _) _ t).trans ((h1 m m' hm hm' t ht).2.trans ?_)
    exact mul_le_mul_of_nonneg_left (W_le_Dl m m' t) hL1

theorem ULo.add {Φ Ψ : MD → X → ℝ} (hΦ : C.ULo Φ) (hΨ : C.ULo Ψ) :
    C.ULo (fun m x => Φ m x + Ψ m x) := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  obtain ⟨s2, p2, B2, L2, hB2, hL2, h2⟩ := hΨ
  refine ⟨fun m hm => (s1 m hm).add (s2 m hm), fun m hm => isSPeriodic_add' (p1 m hm) (p2 m hm),
    2 * B1 + 2 * B2, 2 * L1 + 2 * L2, by positivity, by positivity,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · obtain ⟨a1, _⟩ := h1 m m' hm hm' t ht
    obtain ⟨a2, _⟩ := h2 m m' hm hm' t ht
    exact (Q_add_le _ (s1 m hm) (s2 m hm) t).trans (by nlinarith [Zs_nonneg (C := C) m t])
  · obtain ⟨_, b1⟩ := h1 m m' hm hm' t ht
    obtain ⟨_, b2⟩ := h2 m m' hm hm' t ht
    have e : (fun x => Φ m x + Ψ m x - (Φ m' x + Ψ m' x)) =
        fun x => (Φ m x - Φ m' x) + (Ψ m x - Ψ m' x) := by funext x; ring
    rw [e]
    refine (Q_add_le _ ((s1 m hm).sub (s1 m' hm')) ((s2 m hm).sub (s2 m' hm')) t).trans ?_
    nlinarith [Dl_nonneg (C := C) m m' t]

theorem ULo.const_mul {Φ : MD → X → ℝ} (hΦ : C.ULo Φ) (a : ℝ) :
    C.ULo (fun m x => a * Φ m x) := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  refine ⟨fun m hm => contDiff_const.mul (s1 m hm), fun m hm => isSPeriodic_const_mul' (p1 m hm) a,
    a ^ 2 * B1, a ^ 2 * L1, by positivity, by positivity, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · rw [Q_const_mul _ (s1 m hm)]
    calc a ^ 2 * Q (C.k - 1) (Φ m) t ≤ a ^ 2 * (B1 * (1 + C.Zs m t)) :=
          mul_le_mul_of_nonneg_left (h1 m m' hm hm' t ht).1 (sq_nonneg _)
      _ = _ := by ring
  · have e : (fun x => a * Φ m x - a * Φ m' x) = fun x => a * (Φ m x - Φ m' x) := by
      funext x; ring
    rw [e, Q_const_mul _ ((s1 m hm).sub (s1 m' hm'))]
    calc a ^ 2 * Q (C.k - 1) (fun x => Φ m x - Φ m' x) t ≤ a ^ 2 * (L1 * C.Dl m m' t) :=
          mul_le_mul_of_nonneg_left (h1 m m' hm hm' t ht).2 (sq_nonneg _)
      _ = _ := by ring

theorem ULo.sub {Φ Ψ : MD → X → ℝ} (hΦ : C.ULo Φ) (hΨ : C.ULo Ψ) :
    C.ULo (fun m x => Φ m x - Ψ m x) := by
  have := hΦ.add (hΨ.const_mul (-1))
  simpa [← sub_eq_add_neg] using this

theorem UHi.sub {Φ Ψ : MD → X → ℝ} (hΦ : C.UHi Φ) (hΨ : C.UHi Ψ) :
    C.UHi (fun m x => Φ m x - Ψ m x) := by
  have := hΦ.add (hΨ.const_mul (-1))
  simpa [← sub_eq_add_neg] using this

theorem ULo.sum {ι : Type*} [Fintype ι] {Φ : ι → MD → X → ℝ} (hΦ : ∀ i, C.ULo (Φ i)) :
    C.ULo (fun m x => ∑ i, Φ i m x) := by
  choose s1 p1 h1 using hΦ
  choose B L hB hL hb using h1
  refine ⟨fun m hm => ContDiff.sum fun i _ => s1 i m hm,
    fun m hm => isSPeriodic_sum' _ fun i => p1 i m hm,
    Fintype.card ι * ∑ i, B i, Fintype.card ι * ∑ i, L i,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hB i),
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hL i),
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · refine (Q_sum_le _ Finset.univ (fun i => s1 i m hm) t).trans ?_
    rw [Finset.card_univ, mul_assoc, Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hb i m m' hm hm' t ht).1)
      (Nat.cast_nonneg _)
  · have e : (fun x => ∑ i, Φ i m x - ∑ i, Φ i m' x) = fun x => ∑ i, (Φ i m x - Φ i m' x) := by
      funext x; rw [Finset.sum_sub_distrib]
    rw [e]
    refine (Q_sum_le _ Finset.univ (fun i => (s1 i m hm).sub (s1 i m' hm')) t).trans ?_
    rw [Finset.card_univ, mul_assoc, Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hb i m m' hm hm' t ht).2)
      (Nat.cast_nonneg _)

/-- **`H^k · H^{k-1} ⊂ H^{k-1}`** in the uniform Lipschitz form. -/
theorem ULo.mul_hi (hk : 3 ≤ C.k) {Φ Ψ : MD → X → ℝ} (hΦ : C.UHi Φ) (hΨ : C.ULo Ψ) :
    C.ULo (fun m x => Φ m x * Ψ m x) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hk2 : 2 * 2 ≤ C.k - 1 + 2 := by omega
  have hk1 : C.k - 1 + 1 = C.k := by omega
  set Ca := algC 3 (C.k - 1) CS
  have hCa : 0 ≤ Ca := algC_nonneg _ hCS
  have mul' : ∀ {f g : X → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → IsSPeriodic f → IsSPeriodic g →
      ∀ t, Q (C.k - 1) (fun x => f x * g x) t ≤ Ca * Q C.k f t * Q (C.k - 1) g t :=
    fun hf hg pf pg t => by
      have := Q_mul_le_succ hk2 hCS hsup hf hg pf pg t
      rwa [hk1] at this
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΦ
  obtain ⟨s2, p2, B2, L2, hB2, hL2, h2⟩ := hΨ
  refine ⟨fun m hm => (s1 m hm).mul (s2 m hm), fun m hm => isSPeriodic_mul (p1 m hm) (p2 m hm),
    Ca * B1 * B2, 2 * Ca * (L1 * B2 + B1 * L2), by positivity, by positivity,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · refine (mul' (s1 m hm) (s2 m hm) (p1 m hm) (p2 m hm) t).trans ?_
    have := Q_nonneg C.k (Φ m) t
    have := Q_nonneg (C.k - 1) (Ψ m) t
    calc Ca * Q C.k (Φ m) t * Q (C.k - 1) (Ψ m) t ≤ Ca * B1 * (B2 * (1 + C.Zs m t)) := by
          gcongr
          · exact (h1 m m' hm hm' t ht).1
          · exact (h2 m m' hm hm' t ht).1
      _ = _ := by ring
  · have e : (fun x => Φ m x * Ψ m x - Φ m' x * Ψ m' x) =
        fun x => (Φ m x - Φ m' x) * Ψ m x + Φ m' x * (Ψ m x - Ψ m' x) := by funext x; ring
    rw [e]
    have sd1 := (s1 m hm).sub (s1 m' hm')
    have sd2 := (s2 m hm).sub (s2 m' hm')
    refine (Q_add_le _ (sd1.mul (s2 m hm)) ((s1 m' hm').mul sd2) t).trans ?_
    have m1 := mul' sd1 (s2 m hm) (isSPeriodic_sub' (p1 m hm) (p1 m' hm')) (p2 m hm) t
    have m2 := mul' (s1 m' hm') sd2 (p1 m' hm') (isSPeriodic_sub' (p2 m hm) (p2 m' hm')) t
    obtain ⟨_, b1⟩ := h1 m m' hm hm' t ht
    obtain ⟨a1', _⟩ := h1 m' m hm' hm t ht
    obtain ⟨a2, b2⟩ := h2 m m' hm hm' t ht
    have n1 := Q_nonneg C.k (fun x => Φ m x - Φ m' x) t
    have n2 := Q_nonneg (C.k - 1) (Ψ m) t
    have n3 := Q_nonneg C.k (Φ m') t
    have n4 := Q_nonneg (C.k - 1) (fun x => Ψ m x - Ψ m' x) t
    have hW := Wn_nonneg C.k m.1 m'.1 t
    have hZ := Zs_nonneg (C := C) m t
    have hD := Dl_nonneg (C := C) m m' t
    have hWZ := WZ_le_Dl (C := C) m m' t
    have c1 : Ca * Q C.k (fun x => Φ m x - Φ m' x) t * Q (C.k - 1) (Ψ m) t ≤
        Ca * (L1 * Wn C.k m.1 m'.1 t) * (B2 * (1 + C.Zs m t)) := by gcongr
    have c2 : Ca * Q C.k (Φ m') t * Q (C.k - 1) (fun x => Ψ m x - Ψ m' x) t ≤
        Ca * B1 * (L2 * C.Dl m m' t) := by gcongr
    have c3 : Ca * (L1 * Wn C.k m.1 m'.1 t) * (B2 * (1 + C.Zs m t)) ≤
        Ca * L1 * B2 * C.Dl m m' t := by
      have : 0 ≤ Ca * L1 * B2 := by positivity
      calc _ = Ca * L1 * B2 * (Wn C.k m.1 m'.1 t * (1 + C.Zs m t)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hWZ this
    nlinarith

/-- Slab congruence for `UHi`. -/
theorem UHi.congr {Φ Ψ : MD → X → ℝ} (hΨ : C.UHi Ψ) (sΦ : ∀ m, C.Adm m → ContDiff ℝ ∞ (Φ m))
    (pΦ : ∀ m, C.Adm m → IsSPeriodic (Φ m))
    (heq : ∀ m, C.Adm m → ∀ x : X, x 0 ∈ Icc 0 C.T → Φ m x = Ψ m x) : C.UHi Φ := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΨ
  refine ⟨sΦ, pΦ, B1, L1, hB1, hL1, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · rw [Q_congr_slab (sΦ m hm) (s1 m hm) (heq m hm) _ ht]
    exact (h1 m m' hm hm' t ht).1
  · rw [Q_congr_slab ((sΦ m hm).sub (sΦ m' hm')) ((s1 m hm).sub (s1 m' hm'))
      (fun x hx => by rw [heq m hm x hx, heq m' hm' x hx]) _ ht]
    exact (h1 m m' hm hm' t ht).2

/-- Slab congruence for `ULo`. -/
theorem ULo.congr {Φ Ψ : MD → X → ℝ} (hΨ : C.ULo Ψ) (sΦ : ∀ m, C.Adm m → ContDiff ℝ ∞ (Φ m))
    (pΦ : ∀ m, C.Adm m → IsSPeriodic (Φ m))
    (heq : ∀ m, C.Adm m → ∀ x : X, x 0 ∈ Icc 0 C.T → Φ m x = Ψ m x) : C.ULo Φ := by
  obtain ⟨s1, p1, B1, L1, hB1, hL1, h1⟩ := hΨ
  refine ⟨sΦ, pΦ, B1, L1, hB1, hL1, fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · rw [Q_congr_slab (sΦ m hm) (s1 m hm) (heq m hm) _ ht]
    exact (h1 m m' hm hm' t ht).1
  · rw [Q_congr_slab ((sΦ m hm).sub (sΦ m' hm')) ((s1 m hm).sub (s1 m' hm'))
      (fun x hx => by rw [heq m hm x hx, heq m' hm' x hx]) _ ht]
    exact (h1 m m' hm hm' t ht).2

/-! ### Base cases -/

/-- **Polynomial expressions in `(q, g⁻¹, g, ∂g, θ)` are `UHi`.** -/
theorem uhi_evalF (G : C.Good) (P : MvPolynomial (Option (NV κ)) ℝ) :
    C.UHi (fun m => evalF (Vfam C.a0 C.θ m.1 m.2.1) P) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  obtain ⟨Bθ, hBθ0, hBθ⟩ := exists_Btheta (T := C.T) C.k G.hθ
  have hk2 : 2 * 2 ≤ C.k + 1 := by have := G.hk; omega
  have hB := BV_nonneg C.k (CS := CS) (Λ := C.Λ) (a0 := C.a0) G.hK0 hBθ0
  obtain ⟨B', L, hB', hL, hlip⟩ := evalF_lip (σ := Option (NV κ)) hk2 hCS hsup P hB
  set cd := cD κ C.k CS C.K0 C.Λ C.a0
  have hcd : 0 ≤ cd := by
    simp only [cd, cD]
    have := cq_nonneg C.k (K0 := C.K0) (Λ := C.Λ) (a0 := C.a0) hCS
    have := cgi_nonneg C.k (K0 := C.K0) (Λ := C.Λ) hCS
    positivity
  refine ⟨fun m hm => contDiff_evalF (MetricHyp.sV hm G.ha) P,
    fun m hm => isSPeriodic_evalF (MetricHyp.pV hm) P, B', L * cd, hB', by positivity,
    fun m m' hm hm' t ht => ?_⟩
  set V := Vfam C.a0 C.θ m.1 m.2.1
  set V' := Vfam C.a0 C.θ m'.1 m'.2.1
  set D := ∑ v, Q C.k (fun x => V v x - V' v x) t
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun v _ => Q_nonneg _ _ _
  have hDv : ∀ v, Q C.k (fun x => V v x - V' v x) t ≤ D := fun v =>
    Finset.single_le_sum (f := fun v => Q C.k (fun x => V v x - V' v x) t)
      (fun v _ => Q_nonneg _ _ _) (Finset.mem_univ v)
  have hDW : D ≤ cd * Wn C.k m.1 m'.1 t := DV_le G.hk hm hm' G.hT G.ha hCS hsup ht
  obtain ⟨h1, h2⟩ := hlip V V' t D (MetricHyp.sV hm G.ha) (MetricHyp.sV hm' G.ha)
    (MetricHyp.pV hm) (MetricHyp.pV hm') (MetricHyp.Vbound hm G.hT G.ha hCS hsup hBθ0 hBθ ht)
    (MetricHyp.Vbound hm' G.hT G.ha hCS hsup hBθ0 hBθ ht) hD0 hDv
  refine ⟨h1, h2.trans ?_⟩
  calc L * D ≤ L * (cd * Wn C.k m.1 m'.1 t) := mul_le_mul_of_nonneg_left hDW hL
    _ = _ := by ring

theorem evalF_X {σ : Type*} (v : σ → X → ℝ) (i : σ) : evalF v (MvPolynomial.X i) = v i := by
  funext x; simp [evalF]

/-- The variables themselves are `UHi`. -/
theorem uhi_var (G : C.Good) (v : Option (NV κ)) :
    C.UHi (fun m => Vfam C.a0 C.θ m.1 m.2.1 v) := by
  have := uhi_evalF G (MvPolynomial.X v)
  simpa only [evalF_X] using this

theorem uhi_gi (G : C.Good) (a b : Fin 4) : C.UHi (fun m => m.2.1 a b) :=
  uhi_var G (some (.inl (a, b)))

theorem uhi_g (G : C.Good) (c : Idx) : C.UHi (fun m => m.1 c) :=
  uhi_var G (some (.inr (.inl c)))

theorem uhi_dg (G : C.Good) (c : Idx) (μ : Fin 4) : C.UHi (fun m => pd (m.1 c) μ) :=
  uhi_var G (some (.inr (.inr (.inl (c, μ)))))

theorem uhi_q (G : C.Good) : C.UHi (fun m => lapseInv C.a0 m.2.1) :=
  uhi_var G none


end CtxS

namespace CtxS

variable {C : CtxS κ}

/-- Spatial-spatial second derivatives are `ULo`. -/
theorem ulo_D2_ss (G : C.Good) (c : Idx) (i j : Fin 3) :
    C.ULo (fun m => pd (pd (m.1 c) i.succ) j.succ) := by
  have hk1 : 1 ≤ C.k := by have := G.hk; omega
  refine ⟨fun m hm => contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _,
    fun m hm => isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) _) _, C.K0, 1, G.hK0, zero_le_one,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · have h1 := (Q_pd_le' hk1 j (pd (m.1 c) i.succ) t).trans ((Q_pd_le i (m.1 c) t).trans
      ((Q_mono (k := C.k + 1) (k' := C.k + 2) (by omega) _ t).trans (MetricHyp.hsg hm t ht c)))
    have := Zs_nonneg (C := C) m t
    nlinarith [G.hK0]
  · rw [← pd_pd_wdiff (MetricHyp.sg hm) (MetricHyp.sg hm') c i.succ j.succ]
    have h1 := (Q_pd_le' hk1 j _ t).trans ((Q_pd_le i _ t).trans (Q_w_le_Wn C.k m.1 m'.1 t c))
    rw [one_mul]
    exact h1.trans (W_le_Dl m m' t)

/-- Mixed second derivatives `∂ⱼ∂ₜg` are `ULo`. -/
theorem ulo_D2_ts (G : C.Good) (c : Idx) (j : Fin 3) :
    C.ULo (fun m => pd (pd (m.1 c) 0) j.succ) := by
  have hk1 : 1 ≤ C.k := by have := G.hk; omega
  refine ⟨fun m hm => contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _,
    fun m hm => isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) _) _, C.K0, 1, G.hK0, zero_le_one,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · have h1 := (Q_pd_le' hk1 j (pd (m.1 c) 0) t).trans
      ((Q_mono (k := C.k) (k' := C.k + 1) (by omega) _ t).trans (MetricHyp.hst' hm ht c))
    have := Zs_nonneg (C := C) m t
    nlinarith [G.hK0]
  · rw [← pd_pd_wdiff (MetricHyp.sg hm) (MetricHyp.sg hm') c 0 j.succ]
    have h1 := (Q_pd_le' hk1 j _ t).trans (Q_wt_le_Wn C.k m.1 m'.1 t c)
    rw [one_mul]
    exact h1.trans (W_le_Dl m m' t)

/-- `∂ₜ∂ᵢg` (the other order) is `ULo`. -/
theorem ulo_D2_st (G : C.Good) (c : Idx) (i : Fin 3) :
    C.ULo (fun m => pd (pd (m.1 c) i.succ) 0) :=
  (ulo_D2_ts G c i).congr (fun m hm => contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _)
    (fun m hm => isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) _) _)
    (fun m hm x _ => by rw [pd2_swap (MetricHyp.sg hm c) i.succ 0])

set_option maxHeartbeats 1600000 in
/-- **The time-time second derivative `∂ₜ²g` is `ULo`** (through the reduced equation). -/
theorem ulo_D2_tt (G : C.Good) (c : Idx) : C.ULo (fun m => pd (pd (m.1 c) 0) 0) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hk := G.hk
  have hk1 : 1 ≤ C.k := by omega
  have hk2 : 2 * 2 ≤ C.k + 1 := by omega
  have hk2' : 2 * 2 ≤ C.k - 1 + 2 := by omega
  have hkk : C.k - 1 + 1 = C.k := by omega
  set Ca := algC 3 C.k CS
  set Ca' := algC 3 (C.k - 1) CS
  have hCa : 0 ≤ Ca := algC_nonneg _ hCS
  have hCa' : 0 ≤ Ca' := algC_nonneg _ hCS
  set Bb := ((wordsLE 3 C.k).card : ℝ) * MetricHyp.Cbg (C.k + 2) CS C.K0 C.Λ C.a0 ^ 2
  have hBb : 0 ≤ Bb := by positivity
  set Bq := ((wordsLE 3 C.k).card : ℝ) * MetricHyp.Cq (C.k + 2) CS C.K0 C.Λ C.a0 ^ 2
  have hBq : 0 ≤ Bq := by positivity
  obtain ⟨_, _, Bψ, Lψ, hBψ, _, hψ⟩ := uhi_evalF G (psiP C.Np c)
  have hK0 := G.hK0
  obtain ⟨c₁, c₂, hc₁, hc₂, hF⟩ := forcing_Q_le_sh (Np := C.Np) (θ := C.θ) (Λ := C.Λ) (lam := C.lam) hk
    G.hT G.ha G.hθ G.hK0
  have mul' : ∀ {f g : X → ℝ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → IsSPeriodic f →
      IsSPeriodic g → ∀ t, Q (C.k - 1) (fun x => f x * g x) t ≤ Ca' * Q C.k f t *
        Q (C.k - 1) g t := fun hf hg pf pg t => by
    have := Q_mul_le_succ hk2' hCS hsup hf hg pf pg t
    rwa [hkk] at this
  refine ⟨fun m hm => contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _,
    fun m hm => isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) _) _,
    4 * (36 * Ca * Bb * C.K0) + 4 * (81 * Ca * Bb * C.K0) + 4 * Bψ + 4 * Ca * Bq,
    2 * (c₁ + c₂) + 144 * Ca' * Bb + 324 * Ca' * Bb, by positivity, by positivity,
    fun m m' hm hm' t ht => ⟨?_, ?_⟩⟩
  · -- the bound, through the normal form
    set q := lapseInv C.a0 m.2.1
    set g := m.1
    set gi := m.2.1
    set S := m.2.2
    have sβ := MetricHyp.sbeta hm G.ha
    have sγ := MetricHyp.sgamma hm G.ha
    have sU : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (pd (g c) 0) i.succ) := fun i =>
      contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) 0) _
    have sV : ∀ i j : Fin 3, ContDiff ℝ ∞ (pd (pd (g c) j.succ) i.succ) := fun i j =>
      contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _
    have pU : ∀ i : Fin 3, IsSPeriodic (pd (pd (g c) 0) i.succ) := fun i =>
      isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) 0) _
    have pV : ∀ i j : Fin 3, IsSPeriodic (pd (pd (g c) j.succ) i.succ) := fun i j =>
      isSPeriodic_pd (isSPeriodic_pd (MetricHyp.pg hm c) _) _
    set A : X → ℝ := fun x => 2 * ∑ i : Fin 3, betaF q gi i x * pd (pd (g c) 0) i.succ x
    set Bt : X → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, gammaF q gi i j x *
      pd (pd (g c) j.succ) i.succ x
    set Cp : X → ℝ := fun x => psiF C.a0 C.Np C.θ g gi c x + q x * S c x
    have sA : ContDiff ℝ ∞ A := contDiff_const.mul (ContDiff.sum fun i _ => (sβ i).mul (sU i))
    have sB : ContDiff ℝ ∞ Bt := ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (sγ i j).mul (sV i j)
    have sψ := MetricHyp.spsi hm G.ha c
    have sqS : ContDiff ℝ ∞ fun x => q x * S c x := (MetricHyp.sq hm G.ha).mul (MetricHyp.sS hm c)
    have sC : ContDiff ℝ ∞ Cp := sψ.add sqS
    have heq : ∀ x : X, x 0 ∈ Icc 0 C.T → pd (pd (g c) 0) 0 x = A x + Bt x + Cp x := by
      intro x hx
      rw [MetricHyp.normal_form hm G.ha hx c]
      simp only [A, Bt, Cp, psiF]
      ring
    have hQ : Q C.k (pd (pd (g c) 0) 0) t = Q C.k (fun x => A x + Bt x + Cp x) t :=
      Q_congr_slab (contDiff_pd_top (contDiff_pd_top (MetricHyp.sg hm c) _) _)
        ((sA.add sB).add sC) heq _ ht
    have e1 := Q_add_le C.k (sA.add sB) sC t
    have e2 := Q_add_le C.k sA sB t
    have hA : Q C.k A t ≤ 36 * Ca * Bb * C.K0 := by
      have e : Q C.k A t = 2 ^ 2 * Q C.k (fun x => ∑ i : Fin 3, betaF q gi i x *
          pd (pd (g c) 0) i.succ x) t :=
        Q_const_mul _ (ContDiff.sum fun i _ => (sβ i).mul (sU i)) 2 t
      rw [e]
      have hs := Q_sum_le C.k Finset.univ (fun i => (sβ i).mul (sU i)) t
      rw [Finset.card_univ, Fintype.card_fin] at hs
      have ht' : ∀ i : Fin 3, Q C.k (fun x => betaF q gi i x * pd (pd (g c) 0) i.succ x) t ≤
          Ca * Bb * C.K0 := fun i => by
        refine (Q_mul_le hk2 hCS hsup (sβ i) (sU i) (MetricHyp.pbeta hm i) (pU i) t).trans ?_
        have q1 := MetricHyp.Q_beta_le hm G.hT G.ha hCS hsup ht i
        have q2 := MetricHyp.Q_U_le hm ht c i
        have := Q_nonneg C.k (betaF q gi i) t
        have := Q_nonneg C.k (pd (pd (g c) 0) i.succ) t
        gcongr
      calc _ ≤ 2 ^ 2 * (3 * ∑ _i : Fin 3, Ca * Bb * C.K0) := by
            refine mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
            push_cast
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ht' i) (by norm_num)
        _ = _ := by simp; ring
    have hB : Q C.k Bt t ≤ 81 * Ca * Bb * C.K0 := by
      have hs := Q_sum_le C.k Finset.univ (fun i => ContDiff.sum (s := Finset.univ) fun j _ =>
        (sγ i j).mul (sV i j)) t
      rw [Finset.card_univ, Fintype.card_fin] at hs
      have ht' : ∀ i j : Fin 3, Q C.k (fun x => gammaF q gi i j x *
          pd (pd (g c) j.succ) i.succ x) t ≤ Ca * Bb * C.K0 := fun i j => by
        refine (Q_mul_le hk2 hCS hsup (sγ i j) (sV i j) (MetricHyp.pgamma hm i j) (pV i j) t).trans
          ?_
        have q1 := MetricHyp.Q_gamma_le hm G.hT G.ha hCS hsup ht i j
        have q2 := MetricHyp.Q_V_le hm ht c i j
        have := Q_nonneg C.k (gammaF q gi i j) t
        have := Q_nonneg C.k (pd (pd (g c) j.succ) i.succ) t
        gcongr
      calc Q C.k Bt t ≤ 3 * ∑ _i : Fin 3, (3 * ∑ _j : Fin 3, Ca * Bb * C.K0) := by
            refine hs.trans ?_
            push_cast
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
            have hs2 := Q_sum_le C.k Finset.univ (fun j => (sγ i j).mul (sV i j)) t
            rw [Finset.card_univ, Fintype.card_fin] at hs2
            refine hs2.trans ?_
            push_cast
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ht' i j) (by norm_num)
        _ = _ := by simp; ring
    have hC : Q C.k Cp t ≤ 2 * Bψ + 2 * Ca * Bq * C.Zs m t := by
      refine (Q_add_le C.k sψ sqS t).trans ?_
      have h1 : Q C.k (psiF C.a0 C.Np C.θ g gi c) t ≤ Bψ := by
        have := (hψ m m' hm hm' t ht).1
        beta_reduce at this
        rwa [evalF_psiP] at this
      have h2 : Q C.k (fun x => q x * S c x) t ≤ Ca * Bq * C.Zs m t := by
        refine (Q_mul_le hk2 hCS hsup (MetricHyp.sq hm G.ha) (MetricHyp.sS hm c) (MetricHyp.pq hm)
          (MetricHyp.pS hm c) t).trans ?_
        have q1 := MetricHyp.Q_q_le hm G.hT G.ha hCS hsup ht
        have q2 := Q_le_Zs (C := C) m t c
        have := Q_nonneg C.k q t
        have := Q_nonneg C.k (S c) t
        gcongr
      linarith
    have hZ := Zs_nonneg (C := C) m t
    have hfin : Q C.k (pd (pd (g c) 0) 0) t ≤
        (4 * (36 * Ca * Bb * C.K0) + 4 * (81 * Ca * Bb * C.K0) + 4 * Bψ + 4 * Ca * Bq) *
          (1 + C.Zs m t) := by
      rw [hQ]
      have : 0 ≤ (4 * (36 * Ca * Bb * C.K0) + 4 * (81 * Ca * Bb * C.K0) + 4 * Bψ) * C.Zs m t := by
        have := G.hK0
        positivity
      nlinarith
    exact (Q_mono (Nat.sub_le _ _) _ t).trans hfin
  · -- the difference, through the difference system
    have pw : ∀ c, IsSPeriodic (wdiff m.1 m'.1 c) := fun c k x => by
      unfold wdiff; rw [MetricHyp.pg hm c k x, MetricHyp.pg hm' c k x]
    set g := m.1
    set g' := m'.1
    set gi := m.2.1
    have sw := contDiff_wdiff (MetricHyp.sg hm) (MetricHyp.sg hm')
    rw [← pd_pd_wdiff (MetricHyp.sg hm) (MetricHyp.sg hm') c 0 0]
    set q := lapseInv C.a0 gi
    set Pβ : X → ℝ := fun x => ∑ i : Fin 3, betaF q gi i x * pd (pd (wdiff g g' c) 0) i.succ x
    set Pγ : X → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, gammaF q gi i j x *
      pd (pd (wdiff g g' c) j.succ) i.succ x
    have sβ := MetricHyp.sbeta hm G.ha
    have sγ := MetricHyp.sgamma hm G.ha
    have sX : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (pd (wdiff g g' c) 0) i.succ) := fun i =>
      contDiff_pd_top (contDiff_pd_top (sw c) 0) _
    have sY : ∀ i j : Fin 3, ContDiff ℝ ∞ (pd (pd (wdiff g g' c) j.succ) i.succ) := fun i j =>
      contDiff_pd_top (contDiff_pd_top (sw c) _) _
    have sPβ : ContDiff ℝ ∞ Pβ := ContDiff.sum fun i _ => (sβ i).mul (sX i)
    have sPγ : ContDiff ℝ ∞ Pγ := ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (sγ i j).mul (sY i j)
    have hsys := diffSys_hyp_any hm hm' (by omega) G.hT G.ha hCS hsup
    have sF := hsys.sF c
    have e : pd (pd (wdiff g g' c) 0) 0 = fun x => fdiff C.a0 gi g g' c x + (2 * Pβ x + Pγ x) := by
      funext x
      have hp : (diffSys C.a0 gi).princ (wdiff g g') c x = 2 * Pβ x + Pγ x := rfl
      show _ = (pd (pd (wdiff g g' c) 0) 0 x - (diffSys C.a0 gi).princ (wdiff g g') c x) + _
      rw [hp]; ring
    rw [e]
    refine (Q_add_le _ sF ((contDiff_const.mul sPβ).add sPγ) t).trans ?_
    have hFd : Q (C.k - 1) (fdiff C.a0 gi g g' c) t ≤ (c₁ + c₂) * C.Dl m m' t := by
      refine (Q_mono (Nat.sub_le _ _) _ t).trans ((hF g g' gi m'.2.1 m.2.2 m'.2.2 hm hm' t ht c).trans
        ?_)
      have h1 := WZ'_le_Dl (C := C) m m' t
      have h2 := dS_le_Dl (C := C) m m' t c
      have h3 : Q C.k (m'.2.2 c) t ≤ C.Zs m' t := Q_le_Zs m' t c
      have hW := Wn_nonneg C.k m.1 m'.1 t
      have h4 : c₁ * Wn C.k g g' t * (1 + Q C.k (m'.2.2 c) t) ≤ c₁ * C.Dl m m' t := by
        calc c₁ * Wn C.k g g' t * (1 + Q C.k (m'.2.2 c) t) ≤
            c₁ * (Wn C.k g g' t * (1 + C.Zs m' t)) := by
              rw [mul_assoc]; gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hc₁
      nlinarith
    have hX : ∀ i : Fin 3, Q (C.k - 1) (fun x => betaF q gi i x *
        pd (pd (wdiff g g' c) 0) i.succ x) t ≤ Ca' * Bb * Wn C.k g g' t := fun i => by
      refine (mul' (sβ i) (sX i) (MetricHyp.pbeta hm i)
        (isSPeriodic_pd (isSPeriodic_pd (pw c) 0) _) t).trans ?_
      have q1 := MetricHyp.Q_beta_le hm G.hT G.ha hCS hsup ht i
      have q2 := (Q_pd_le' hk1 i _ t).trans (Q_wt_le_Wn C.k g g' t c)
      have := Q_nonneg C.k (betaF q gi i) t
      have := Q_nonneg (C.k - 1) (pd (pd (wdiff g g' c) 0) i.succ) t
      gcongr
    have hY : ∀ i j : Fin 3, Q (C.k - 1) (fun x => gammaF q gi i j x *
        pd (pd (wdiff g g' c) j.succ) i.succ x) t ≤ Ca' * Bb * Wn C.k g g' t := fun i j => by
      refine (mul' (sγ i j) (sY i j) (MetricHyp.pgamma hm i j)
        (isSPeriodic_pd (isSPeriodic_pd (pw c) _) _) t).trans ?_
      have q1 := MetricHyp.Q_gamma_le hm G.hT G.ha hCS hsup ht i j
      have q2 := (Q_pd_le' hk1 i _ t).trans ((Q_pd_le j _ t).trans (Q_w_le_Wn C.k g g' t c))
      have := Q_nonneg C.k (gammaF q gi i j) t
      have := Q_nonneg (C.k - 1) (pd (pd (wdiff g g' c) j.succ) i.succ) t
      gcongr
    have hPβ : Q (C.k - 1) Pβ t ≤ 9 * (Ca' * Bb * Wn C.k g g' t) := by
      have hs := Q_sum_le (C.k - 1) Finset.univ (fun i => (sβ i).mul (sX i)) t
      rw [Finset.card_univ, Fintype.card_fin] at hs
      calc Q (C.k - 1) Pβ t ≤ 3 * ∑ _i : Fin 3, Ca' * Bb * Wn C.k g g' t := by
            refine hs.trans ?_
            push_cast
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hX i) (by norm_num)
        _ = _ := by simp; ring
    have hPγ : Q (C.k - 1) Pγ t ≤ 81 * (Ca' * Bb * Wn C.k g g' t) := by
      have hs := Q_sum_le (C.k - 1) Finset.univ (fun i => ContDiff.sum (s := Finset.univ)
        fun j _ => (sγ i j).mul (sY i j)) t
      rw [Finset.card_univ, Fintype.card_fin] at hs
      calc Q (C.k - 1) Pγ t ≤ 3 * ∑ _i : Fin 3, (3 * ∑ _j : Fin 3, Ca' * Bb * Wn C.k g g' t) := by
            refine hs.trans ?_
            push_cast
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
            have hs2 := Q_sum_le (C.k - 1) Finset.univ (fun j => (sγ i j).mul (sY i j)) t
            rw [Finset.card_univ, Fintype.card_fin] at hs2
            refine hs2.trans ?_
            push_cast
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hY i j) (by norm_num)
        _ = _ := by simp; ring
    have hpr : Q (C.k - 1) (fun x => 2 * Pβ x + Pγ x) t ≤
        (72 * Ca' * Bb + 162 * Ca' * Bb) * Wn C.k g g' t := by
      refine (Q_add_le _ (contDiff_const.mul sPβ) sPγ t).trans ?_
      rw [Q_const_mul _ sPβ]
      nlinarith
    have hWD := W_le_Dl (C := C) m m' t
    have hW := Wn_nonneg C.k m.1 m'.1 t
    have hD := Dl_nonneg (C := C) m m' t
    have : (72 * Ca' * Bb + 162 * Ca' * Bb) * Wn C.k g g' t ≤
        (72 * Ca' * Bb + 162 * Ca' * Bb) * C.Dl m m' t :=
      mul_le_mul_of_nonneg_left hWD (by have := mul_nonneg hCa' hBb; linarith)
    have h5 : 0 ≤ c₁ + c₂ := add_nonneg hc₁ hc₂
    nlinarith

/-- **All second derivatives `∂_μ∂_νg_c` are `ULo`.** -/
theorem ulo_D2 (G : C.Good) (c : Idx) (μ ν : Fin 4) : C.ULo (fun m => pd (pd (m.1 c) ν) μ) := by
  induction ν using Fin.cases with
  | zero =>
    induction μ using Fin.cases with
    | zero => exact ulo_D2_tt G c
    | succ j => exact ulo_D2_ts G c j
  | succ i =>
    induction μ using Fin.cases with
    | zero => exact ulo_D2_st G c i
    | succ j => exact ulo_D2_ss G c i j

end CtxS

namespace CtxS

variable {C : CtxS κ}

theorem uhi_Y (G : C.Good) (n i j : Fin 4) : C.UHi (fun m => Yf m.1 n i j) :=
  ((uhi_dg G (n, j) i).add (uhi_dg G (n, i) j)).sub (uhi_dg G (i, j) n)

/-- **The Christoffel symbols are `H^{s-2}`-Lipschitz.** -/
theorem uhi_Gam (G : C.Good) (c i j : Fin 4) : C.UHi (fun m => GamF m.1 m.2.1 c i j) :=
  (UHi.sum fun n => (uhi_gi G c n).mul G.hk (uhi_Y G n i j)).const_mul (1 / 2)

theorem ulo_dGamDec (G : C.Good) (e c i j : Fin 4) : C.ULo (fun m => dGamDec m e c i j) :=
  (ULo.sum fun n =>
    ((((UHi.sum fun a => UHi.sum fun b =>
      ((uhi_gi G c a).mul G.hk (uhi_dg G (a, b) e)).mul G.hk (uhi_gi G b n)).const_mul
        (-1)).mul G.hk (uhi_Y G n i j)).toLo).add
    (ULo.mul_hi G.hk (uhi_gi G c n) (((ulo_D2 G (n, j) e i).add (ulo_D2 G (n, i) e j)).sub
      (ulo_D2 G (i, j) e n)))).const_mul (1 / 2)

/-- **The derivatives of the Christoffel symbols are `ULo`.** -/
theorem ulo_dGam (G : C.Good) (e c i j : Fin 4) :
    C.ULo (fun m => pd (GamF m.1 m.2.1 c i j) e) := by
  refine (ulo_dGamDec G e c i j).congr
    (fun m hm => contDiff_pd_top (contDiff_GamF (MetricHyp.sg hm) (MetricHyp.sgi hm) c i j) e)
    (fun m hm => isSPeriodic_pd (isSPeriodic_GamF (MetricHyp.pg hm) (MetricHyp.pgi hm) c i j) e)
    (fun m hm x hx => ?_)
  rw [pd_GamF (MetricHyp.sg hm) (MetricHyp.sgi hm)]
  unfold dGamDec
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have he : e ≠ 0 ∨ 0 < C.T := Or.inr G.hT
  rw [pd_inv_eq (G := fun a b => m.1 (a, b)) (fun a b => MetricHyp.sg hm (a, b))
    (MetricHyp.sgi hm) (MetricHyp.inv hm) e he hx c n]
  ring

/-- **The Riemann tensor is `ULo`.** -/
theorem ulo_Riem (G : C.Good) (a b c d : Fin 4) :
    C.ULo (fun m => RiemF m.1 m.2.1 a b c d) :=
  (((ulo_dGam G c a d b).sub (ulo_dGam G d a c b)).add
    ((UHi.sum fun e => (uhi_Gam G a c e).mul G.hk (uhi_Gam G e d b)).toLo)).sub
    ((UHi.sum fun e => (uhi_Gam G a d e).mul G.hk (uhi_Gam G e c b)).toLo)

end CtxS

/-- **`thm:hyperbolic`, curvature clause (Cauchy form), with the paper's hyperbolicity hypothesis
(nonzero shift)**: under the hypotheses of `thm:hyperbolic` (`MetricHypSh`) (`Σ = 𝕋³`, `s ≥ 5`, common constants, initial data Cauchy in
`H^{s-1} × H^{s-2}`, sources Cauchy in `L¹_tH^{s-2}`), the Riemann tensors `Riem(g_h)` are Cauchy
in `L¹_tH^{s-3}`: `∫₀ᵀ ‖Riem(g_h) - Riem(g_j)‖_{H^{s-3}} dt → 0`. -/
theorem riem_cauchy_sh {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {T a0 lamS Λ K0 : ℝ}
    {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlamS : 0 < lamS)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (s - 3) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t)) atTop (𝓝 0) := by
  have hcau := common_slab_cauchy_sh hs hT ha hlamS hg hinit hsrc
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  have e3 : k + 2 - 3 = k - 1 := by omega
  simp only [e1, e2, e3] at hinit hsrc hcau ⊢
  set C : CtxS κ := ⟨Np, θ, k, T, a0, -(3 * Λ), Λ, K0⟩
  have G : C.Good := ⟨hk, hT, ha, (hg 0).sθ, (hg 0).toMetricHyp.K0_nonneg hT.le⟩
  have hadm : ∀ h, C.Adm (g h, gi h, S h) := fun h => (hg h).toMetricHyp
  -- the uniform Lipschitz constants of the curvature components
  have hR : ∀ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, ∃ L : ℝ, 0 ≤ L ∧ ∀ m m' : MD, C.Adm m →
      C.Adm m' → ∀ t ∈ Icc 0 T, Q (k - 1) (fun x => RiemF m.1 m.2.1 q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF m'.1 m'.2.1 q.1 q.2.1 q.2.2.1 q.2.2.2 x) t ≤ L * C.Dl m m' t := fun q => by
    obtain ⟨_, _, B, L, _, hL, h⟩ := CtxS.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2
    exact ⟨L, hL, fun m m' hm hm' t ht => (h m m' hm hm' t ht).2⟩
  choose L hL hRL using hR
  set Lt := ∑ q, L q
  have hLt : 0 ≤ Lt := Finset.sum_nonneg fun q _ => hL q
  obtain ⟨BS, hBS⟩ := sources_bounded (k := k) (fun h => (hg h).sS) hsrc hT.le
  have hBS0 : 0 ≤ BS := (intervalIntegral.integral_nonneg hT.le fun t _ =>
    Real.sqrt_nonneg _).trans (hBS 0)
  set A := Real.sqrt (256 * Lt)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  -- continuity of the integrands
  have hcR : ∀ p : ℕ × ℕ, Continuous fun t => Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) := fun p => by
    refine (continuous_finsetSum _ fun q _ => continuous_Q _ ?_).sqrt
    have h1 := (CtxS.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2).1 _ (hadm p.1)
    have h2 := (CtxS.ulo_Riem G q.1 q.2.1 q.2.2.1 q.2.2.2).1 _ (hadm p.2)
    exact h1.sub h2
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set η := δ / (4 * (A + 1) * (T + 2 * BS + 1))
  have hη : 0 < η := by positivity
  set ε2 := δ / (4 * (A + 1))
  have hε2 : 0 < ε2 := by positivity
  filter_upwards [hcau (η ^ 2) (by positivity),
    (Metric.tendsto_nhds.mp hsrc) ε2 hε2] with p hW hS
  have hS' : ∫ t in (0)..T, srcD k (S p.1) (S p.2) t < ε2 := by
    have := hS
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hI0 : 0 ≤ ∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) :=
    intervalIntegral.integral_nonneg hT.le fun t _ => Real.sqrt_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hI0]
  -- the pointwise bound
  have hpt : ∀ t ∈ Icc 0 T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t) ≤
      A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) + srcD k (S p.1) (S p.2) t) := by
    intro t ht
    set m : MD := (g p.1, gi p.1, S p.1)
    set m' : MD := (g p.2, gi p.2, S p.2)
    have hD := CtxS.Dl_nonneg (C := C) m m' t
    have h1 : ∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
        Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
          RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t ≤ 256 * Lt * C.Dl m m' t := by
      calc _ ≤ ∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4, Lt * C.Dl m m' t :=
            Finset.sum_le_sum fun q _ => (hRL q m m' (hadm _) (hadm _) t ht).trans
              (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := L) (fun q _ => hL q)
                (Finset.mem_univ q)) hD)
        _ = _ := by simp; ring
    have hW' : Wn k (g p.1) (g p.2) t ≤ η ^ 2 := by
      rw [Wn_eq (hg p.1).sg (hg p.2).sg]; exact hW t ht
    have hW0 := Wn_nonneg k (g p.1) (g p.2) t
    have hsW : Real.sqrt (Wn k (g p.1) (g p.2) t) ≤ η := by
      rw [show η = Real.sqrt (η ^ 2) from (Real.sqrt_sq hη.le).symm]
      exact Real.sqrt_le_sqrt hW'
    have hZ := CtxS.Zs_nonneg (C := C) m t
    have hZ' := CtxS.Zs_nonneg (C := C) m' t
    have hΔ : 0 ≤ ∑ c, Q k (fun x => S p.1 c x - S p.2 c x) t :=
      Finset.sum_nonneg fun _ _ => Q_nonneg _ _ _
    have h2 : Real.sqrt (C.Dl m m' t) ≤ η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
        srcD k (S p.1) (S p.2) t := by
      unfold CtxS.Dl
      refine (sqrt_add_le' (mul_nonneg hW0 (by linarith)) hΔ).trans ?_
      rw [Real.sqrt_mul hW0]
      have h3 : Real.sqrt (1 + C.Zs m t + C.Zs m' t) ≤ 1 + srcN k (S p.1) t + srcN k (S p.2) t := by
        refine (sqrt_add3_le zero_le_one hZ hZ').trans ?_
        rw [Real.sqrt_one]; rfl
      have := Real.sqrt_nonneg (1 + C.Zs m t + C.Zs m' t)
      have : 0 ≤ 1 + srcN k (S p.1) t + srcN k (S p.2) t := by
        unfold srcN; positivity
      have h4 : Real.sqrt (Wn k (g p.1) (g p.2) t) * Real.sqrt (1 + C.Zs m t + C.Zs m' t) ≤
          η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) :=
        mul_le_mul hsW h3 (Real.sqrt_nonneg _) hη.le
      unfold srcD
      linarith
    calc _ ≤ Real.sqrt (256 * Lt * C.Dl m m' t) := Real.sqrt_le_sqrt h1
      _ = A * Real.sqrt (C.Dl m m' t) := Real.sqrt_mul (by positivity) _
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hA
  have hc1 := continuous_srcN k (hg p.1).sS
  have hc2 := continuous_srcN k (hg p.2).sS
  have hc3 := continuous_srcD k (hg p.1).sS (hg p.2).sS
  have cR : Continuous fun t => A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
      srcD k (S p.1) (S p.2) t) := by fun_prop
  have hint : (∫ t in (0)..T, Real.sqrt (∑ q : Fin 4 × Fin 4 × Fin 4 × Fin 4,
      Q (k - 1) (fun x => RiemF (g p.1) (gi p.1) q.1 q.2.1 q.2.2.1 q.2.2.2 x -
        RiemF (g p.2) (gi p.2) q.1 q.2.1 q.2.2.1 q.2.2.2 x) t)) ≤
      ∫ t in (0)..T, A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
        srcD k (S p.1) (S p.2) t) :=
    intervalIntegral.integral_mono_on (μ := volume) hT.le ((hcR p).intervalIntegrable _ _)
      (cR.intervalIntegrable _ _) hpt
  have i1 : Continuous fun t => η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) := by fun_prop
  have i2 : Continuous fun t => 1 + srcN k (S p.1) t := by fun_prop
  have hval : ∫ t in (0)..T, A * (η * (1 + srcN k (S p.1) t + srcN k (S p.2) t) +
      srcD k (S p.1) (S p.2) t) = A * (η * (T + ((∫ t in (0)..T, srcN k (S p.1) t) +
        ∫ t in (0)..T, srcN k (S p.2) t)) + ∫ t in (0)..T, srcD k (S p.1) (S p.2) t) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (f := fun t => η * (1 + srcN k (S p.1) t + srcN k (S p.2) t))
      (g := fun t => srcD k (S p.1) (S p.2) t) (i1.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (f := fun t => 1 + srcN k (S p.1) t)
      (g := fun t => srcN k (S p.2) t) (i2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add (f := fun _ => (1 : ℝ)) (g := fun t => srcN k (S p.1) t)
      (continuous_const.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    ring
  rw [hval] at hint
  have hb1 := hBS p.1
  have hb2 := hBS p.2
  have hT0 := hT.le
  have hkey : η * (T + ((∫ t in (0)..T, srcN k (S p.1) t) + ∫ t in (0)..T, srcN k (S p.2) t)) ≤
      η * (T + 2 * BS + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hηv : η * (T + 2 * BS + 1) = δ / (4 * (A + 1)) := by
    simp only [η]; field_simp
  have hfin : A * (δ / (4 * (A + 1)) + ε2) < δ := by
    simp only [ε2]
    have : A * (δ / (4 * (A + 1)) + δ / (4 * (A + 1))) = δ / 2 * (A / (A + 1)) := by
      field_simp; ring
    rw [this]
    have : A / (A + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc _ ≤ _ := hint
    _ ≤ A * (δ / (4 * (A + 1)) + ε2) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        linarith
    _ < δ := hfin


end RenewalGeometry.ReducedWaveShift
