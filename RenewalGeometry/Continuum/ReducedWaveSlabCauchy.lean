/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabStability

/-!
# `thm:hyperbolic`: the difference energy inequality and the Cauchy property

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability".)
`Σ = 𝕋³`; the metrics `g_h` are smooth, spatially periodic and satisfy `MetricHyp` with common
constants (`eq:reduced-wave`, uniform hyperbolicity, uniform inverse-metric bounds,
`eq:hyperbolic-bound` at order `s = k + 2 ≥ 5`).

* `Ediff` — the differentiated wave energy `E_{h,j}` of `w = g_h - g_j` (order `s - 2`,
  coefficients of `g_h`); **`Ediff_equiv`**: it is uniformly equivalent to
  `W = ‖g_h - g_j‖²_{H^{s-1}} + ‖∂ₜg_h - ∂ₜg_j‖²_{H^{s-2}}`.
* **`hyperbolic_energy`** — `eq:hyperbolic-energy`:
  `E_{h,j}(t)^{1/2} ≤ (E_{h,j}(0)^{1/2} + C∫₀ᵗ‖𝒮ₕ - 𝒮ⱼ‖_{H^{s-2}}) exp(C∫₀ᵗ(1 + a_{h,j}))`,
  `a_{h,j} = (16 + ‖𝒮ⱼ‖²_{H^{s-2}})^{1/2}`; **`sources_bounded`**: `sup_j ∫₀ᵀ ‖𝒮ⱼ‖_{H^{s-2}} < ∞`
  when the sources are Cauchy in `L¹_tH^{s-2}` (so `sup ∫ a_{h,j} < ∞`).
* **`common_slab_cauchy`** — Cauchy initial data in `H^{s-1} × H^{s-2}` and Cauchy sources in
  `L¹_tH^{s-2}` make `(g_h)` Cauchy in `C_tH^{s-1}` and `(∂ₜg_h)` Cauchy in `C_tH^{s-2}`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]
variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {T a0 lam Λ K0 : ℝ}

/-- The differentiated wave energy of the difference (`k = s - 2`). -/
def Ediff (k : ℕ) (a0 : ℝ) (g g' : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (t : ℝ) : ℝ :=
  energyK k (diffSys a0 gi).γ (wdiff g g') t

/-- The `H^k` norm of a source family. -/
def srcN (k : ℕ) (S : Idx → X → ℝ) (t : ℝ) : ℝ := Real.sqrt (∑ c, Q k (S c) t)

/-- The `H^k` norm of a difference of source families. -/
def srcD (k : ℕ) (S S' : Idx → X → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∑ c, Q k (fun x => S c x - S' c x) t)

/-- The weight `a_{h,j} = (16 + ‖𝒮ⱼ‖²_{H^k})^{1/2}`. -/
def srcA (k : ℕ) (S : Idx → X → ℝ) (t : ℝ) : ℝ := Real.sqrt (16 + ∑ c, Q k (S c) t)

theorem continuous_srcN (k : ℕ) {S : Idx → X → ℝ} (hS : ∀ c, ContDiff ℝ ∞ (S c)) :
    Continuous (srcN k S) :=
  (continuous_finsetSum _ fun c _ => continuous_Q k (hS c)).sqrt

theorem continuous_srcD (k : ℕ) {S S' : Idx → X → ℝ} (hS : ∀ c, ContDiff ℝ ∞ (S c))
    (hS' : ∀ c, ContDiff ℝ ∞ (S' c)) : Continuous (srcD k S S') :=
  (continuous_finsetSum _ fun c _ => continuous_Q k ((hS c).sub (hS' c))).sqrt

theorem continuous_srcA (k : ℕ) {S : Idx → X → ℝ} (hS : ∀ c, ContDiff ℝ ∞ (S c)) :
    Continuous (srcA k S) :=
  (continuous_const.add (continuous_finsetSum _ fun c _ => continuous_Q k (hS c))).sqrt

theorem srcA_le (k : ℕ) (S : Idx → X → ℝ) (t : ℝ) : srcA k S t ≤ 4 + srcN k S t := by
  unfold srcA srcN
  refine (sqrt_add_le' (by norm_num) (Finset.sum_nonneg fun c _ => Q_nonneg _ _ _)).trans ?_
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem energyK_nonneg {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : 0 ≤ energyK k S.γ u t := by
  have hL := (SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)).toL2Hyp
  rw [prolongK_γ] at hL
  exact L2Hyp.energy_nonneg hL hlam ht

theorem lam_div_pos {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ} {s : ℕ}
    (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam) :
    0 < lam / Λ := div_pos hlam (lt_of_lt_of_le ha (h.Λ_pos ha hT.le))

/-- **The energy is uniformly equivalent to the squared difference norm**:
`W ≤ c_E E_{h,j}` and `E_{h,j} ≤ c_U W` on `[0, T]`, and `E_{h,j} ≥ 0`. -/
theorem Ediff_equiv {k : ℕ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam) :
    ∃ cE cU : ℝ, 0 ≤ cE ∧ 0 ≤ cU ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S →
      MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      0 ≤ Ediff k a0 g g' gi t ∧ Wn k g g' t ≤ cE * Ediff k a0 g g' gi t ∧
        Ediff k a0 g g' gi t ≤ cU * Wn k g g' t := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  set cE0 : ℝ := 16 * (((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) / L2Hyp.cmin (lam / Λ))
  set cU0 : ℝ := (1 + (3 : ℝ) ^ 2 * Mdiff (k + 2) CS K0 Λ a0) * (Fintype.card (PIdx 3 k Idx) : ℝ) * 4
  refine ⟨max cE0 0, max cU0 0, le_max_right _ _, le_max_right _ _,
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  have hsys := diffSys_hyp h h' (by omega) hT ha hlam.le hCS hsup
  simp only [Nat.add_sub_cancel] at hsys
  have hl := lam_div_pos h hT ha hlam
  have hE0 : 0 ≤ Ediff k a0 g g' gi t := energyK_nonneg hsys hl ht
  have hW0 := Wn_nonneg k g g' t
  refine ⟨hE0, ?_, ?_⟩
  · have hb : ∀ c, Q (k + 1) (wdiff g g' c) t + Q k (pd (wdiff g g' c) 0) t ≤
        ((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) / L2Hyp.cmin (lam / Λ) *
          Ediff k a0 g g' gi t := fun c => Q_le_energyK hsys hl ht c
    have : Wn k g g' t ≤ cE0 * Ediff k a0 g g' gi t := by
      unfold Wn
      calc _ ≤ ∑ _c : Idx, ((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) /
            L2Hyp.cmin (lam / Λ) * Ediff k a0 g g' gi t := Finset.sum_le_sum fun c _ => hb c
        _ = _ := by simp [cE0]; ring
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0)
  · have h1 := energyK_le_Q hsys ht
    have h2 : ∑ c, (Q k (pd (wdiff g g' c) 0) t + ((3 : ℕ) + 1) * Q (k + 1) (wdiff g g' c) t) ≤
        4 * Wn k g g' t := by
      unfold Wn
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have := Q_nonneg k (pd (wdiff g g' c) 0) t
      push_cast; linarith
    have hM := hsys.M_nonneg
    have : Ediff k a0 g g' gi t ≤ cU0 * Wn k g g' t := by
      refine h1.trans ?_
      simp only [cU0]
      have : 0 ≤ (1 + (3 : ℝ) ^ 2 * Mdiff (k + 2) CS K0 Λ a0) * Fintype.card (PIdx 3 k Idx) := by
        positivity
      calc _ ≤ (1 + (3 : ℝ) ^ 2 * Mdiff (k + 2) CS K0 Λ a0) * Fintype.card (PIdx 3 k Idx) *
            (4 * Wn k g g' t) := mul_le_mul_of_nonneg_left (by exact_mod_cast h2) this
        _ = _ := by ring
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0)

/-- **The forcing bound in energy form**: `‖F_{h,j}‖_{H^{s-2}} ≤ c_a a_{h,j} √E_{h,j} + c_σ
‖𝒮_h - 𝒮_j‖_{H^{s-2}}`. -/
theorem normK_fdiff_le {k : ℕ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ ca cσ : ℝ, 0 ≤ ca ∧ 0 ≤ cσ ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S →
      MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      normK k (fdiff a0 gi g g') t ≤
        ca * srcA k S' t * Real.sqrt (Ediff k a0 g g' gi t) + cσ * srcD k S S' t := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hF⟩ := forcing_Q_le (Np := Np) (θ := θ) (Λ := Λ) hk hT ha hlam.le hθ hK0
  obtain ⟨cE, cU, hcE, hcU, hEq⟩ := Ediff_equiv (Np := Np) (θ := θ) (Λ := Λ) (K0 := K0) hk hT ha
    hlam
  set NP : ℝ := ((Fintype.card (PIdx 3 k Idx) : ℕ) : ℝ)
  have hNP : 0 ≤ NP := Nat.cast_nonneg _
  refine ⟨Real.sqrt (NP * c₁ * cE), Real.sqrt (NP * c₂), Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hsys := diffSys_hyp h h' (by omega) hT ha hlam.le hCS hsup
  have hsF := hsys.sF
  refine (normK_le k hsF t).trans ?_
  obtain ⟨hE0, hWE, _⟩ := hEq g g' gi gi' S S' h h' t ht
  set E := Ediff k a0 g g' gi t
  set W := Wn k g g' t
  set A := ∑ c, Q k (S' c) t
  set B := ∑ c, Q k (fun x => S c x - S' c x) t
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun c _ => Q_nonneg _ _ _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun c _ => Q_nonneg _ _ _
  have hW0 := Wn_nonneg k g g' t
  have hsum : ∑ c, Q k (fdiff a0 gi g g' c) t ≤ c₁ * cE * E * (16 + A) + c₂ * B := by
    calc ∑ c, Q k (fdiff a0 gi g g' c) t ≤
        ∑ c, (c₁ * W * (1 + Q k (S' c) t) + c₂ * Q k (fun x => S c x - S' c x) t) :=
          Finset.sum_le_sum fun c _ => hF g g' gi gi' S S' h h' t ht c
      _ = c₁ * W * (16 + A) + c₂ * B := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, A, B]
          simp
      _ ≤ c₁ * cE * E * (16 + A) + c₂ * B := by
          have : c₁ * W ≤ c₁ * (cE * E) := mul_le_mul_of_nonneg_left hWE hc₁
          nlinarith
  calc Real.sqrt (NP * ∑ c, Q k (fdiff a0 gi g g' c) t) ≤
      Real.sqrt (NP * c₁ * cE * (16 + A) * E + NP * c₂ * B) := by
        refine Real.sqrt_le_sqrt ?_
        have := mul_le_mul_of_nonneg_left hsum hNP
        linarith
    _ ≤ Real.sqrt (NP * c₁ * cE * (16 + A) * E) + Real.sqrt (NP * c₂ * B) :=
        sqrt_add_le' (by positivity) (by positivity)
    _ = Real.sqrt (NP * c₁ * cE) * srcA k S' t * Real.sqrt E + Real.sqrt (NP * c₂) * srcD k S S' t := by
        unfold srcA srcD
        rw [Real.sqrt_mul (by positivity) E, Real.sqrt_mul (by positivity) (16 + A),
          Real.sqrt_mul (by positivity) B]

/-- **`eq:hyperbolic-energy`**: there is `C` (depending only on the common constants) with
`E_{h,j}(t)^{1/2} ≤ (E_{h,j}(0)^{1/2} + C∫₀ᵗ‖𝒮ₕ - 𝒮ⱼ‖_{H^{s-2}}) exp(C∫₀ᵗ(1 + a_{h,j}))`
for all pairs and `t ∈ [0, T]`, with `a_{h,j} = (16 + ‖𝒮ⱼ‖²_{H^{s-2}})^{1/2}`. -/
theorem hyperbolic_energy {k : ℕ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S →
      MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      Real.sqrt (Ediff k a0 g g' gi t) ≤
        (Real.sqrt (Ediff k a0 g g' gi 0) + C * ∫ s in (0)..t, srcD k S S' s) *
          Real.exp (C * ∫ s in (0)..t, (1 + srcA k S' s)) := by
  obtain ⟨ca, cσ, hca, hcσ, hN⟩ := normK_fdiff_le (Np := Np) (θ := θ) (Λ := Λ) hk hT ha hlam hθ hK0
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  -- the constants of the linear estimate (they depend on `Λ` only through `λ/Λ`, `Mdiff`)
  set c := L2Hyp.cmin (lam / Λ)
  set q := (Real.sqrt c)⁻¹
  have hq : 0 ≤ q := inv_nonneg.2 (Real.sqrt_nonneg _)
  set M := Mdiff (k + 2) CS K0 Λ a0
  set Kc := L2Hyp.kcoef 3 (Mk k M) (fun _ => mk 3 Idx k M) c 0
  refine ⟨max (q * cσ) (max (|Kc| / 2) (q * ca)), le_max_of_le_left (mul_nonneg hq hcσ),
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  set C := max (q * cσ) (max (|Kc| / 2) (q * ca))
  have hsys := diffSys_hyp h h' (by omega) hT ha hlam.le hCS hsup
  simp only [Nat.add_sub_cancel] at hsys
  have hl := lam_div_pos h hT ha hlam
  have hsA := continuous_srcA k h'.sS
  have hsD := continuous_srcD k h.sS h'.sS
  have hE := hk_energy_of_forcing k hsys hl (a := fun s => ca * srcA k S' s)
    (σ := fun s => cσ * srcD k S S' s) (continuous_const.mul hsA) (continuous_const.mul hsD)
    (fun s => mul_nonneg hca (Real.sqrt_nonneg _)) (fun s => mul_nonneg hcσ (Real.sqrt_nonneg _))
    (fun s hs => by
      have := hN g g' gi gi' S S' h h' s hs
      show _ ≤ ca * srcA k S' s * Real.sqrt (Ediff k a0 g g' gi s) + cσ * srcD k S S' s
      exact this) t ht
  refine hE.trans ?_
  have ht0 : 0 ≤ t := ht.1
  have hint1 : ∫ s in (0)..t, q * (cσ * srcD k S S' s) ≤ C * ∫ s in (0)..t, srcD k S S' s := by
    rw [show (fun s => q * (cσ * srcD k S S' s)) = fun s => (q * cσ) * srcD k S S' s from
      funext fun s => by ring, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _)
  have hint2 : (∫ s in (0)..t, (L2Hyp.kcoef 3 (Mk k M) (fun _ => mk 3 Idx k M) c s +
      2 * q * (ca * srcA k S' s))) / 2 ≤ C * ∫ s in (0)..t, (1 + srcA k S' s) := by
    have e1 : ∫ s in (0)..t, (L2Hyp.kcoef 3 (Mk k M) (fun _ => mk 3 Idx k M) c s +
        2 * q * (ca * srcA k S' s)) = t * Kc + 2 * (q * ca) * ∫ s in (0)..t, srcA k S' s := by
      have hkc : ∀ s, L2Hyp.kcoef 3 (Mk k M) (fun _ => mk 3 Idx k M) c s = Kc := fun s => rfl
      simp only [hkc]
      rw [intervalIntegral.integral_add (f := fun _ => Kc)
        (g := fun s => 2 * q * (ca * srcA k S' s)) (continuous_const.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_const.mul hsA)).intervalIntegrable _ _)]
      rw [show (fun s => 2 * q * (ca * srcA k S' s)) = fun s => (2 * (q * ca)) * srcA k S' s from
        funext fun s => by ring, intervalIntegral.integral_const_mul]
      simp
    have e2 : ∫ s in (0)..t, (1 + srcA k S' s) = t + ∫ s in (0)..t, srcA k S' s := by
      rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
        (hsA.intervalIntegrable _ _)]
      simp
    rw [e1, e2]
    have hIA : 0 ≤ ∫ s in (0)..t, srcA k S' s :=
      intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _
    have h1 : t * Kc / 2 ≤ C * t := by
      have : Kc / 2 ≤ C := le_trans (by
        have := le_abs_self Kc; linarith) (le_max_of_le_right (le_max_left _ _))
      nlinarith
    have h2 : q * ca * ∫ s in (0)..t, srcA k S' s ≤ C * ∫ s in (0)..t, srcA k S' s :=
      mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) hIA
    nlinarith
  have hX : 0 ≤ Real.sqrt (energyK k (diffSys a0 gi).γ (wdiff g g') 0) +
      ∫ s in (0)..t, q * (cσ * srcD k S S' s) :=
    add_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg ht0 fun s _ =>
      mul_nonneg hq (mul_nonneg hcσ (Real.sqrt_nonneg _)))
  refine mul_le_mul (by unfold Ediff; linarith) (Real.exp_le_exp.2 hint2) (Real.exp_pos _).le ?_
  have hI : 0 ≤ ∫ s in (0)..t, srcD k S S' s :=
    intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _
  have hC : 0 ≤ C := le_max_of_le_left (mul_nonneg hq hcσ)
  exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC hI)

/-- **Cauchy sources are bounded in `L¹_tH^k`**. -/
theorem sources_bounded {k : ℕ} {S : ℕ → Idx → X → ℝ} (hS : ∀ h c, ContDiff ℝ ∞ (S h c))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T, srcD k (S p.1) (S p.2) t) atTop (𝓝 0))
    (hT : 0 ≤ T) :
    ∃ BS : ℝ, ∀ j, ∫ t in (0)..T, srcN k (S j) t ≤ BS := by
  obtain ⟨⟨a, b⟩, hab⟩ := Filter.eventually_atTop.mp
    (hsrc.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  set N := max a b
  refine ⟨(∑ j ∈ Finset.range N, ∫ t in (0)..T, srcN k (S j) t) +
    Real.sqrt 2 * (1 + ∫ t in (0)..T, srcN k (S N) t), fun j => ?_⟩
  have hnn : ∀ j, 0 ≤ ∫ t in (0)..T, srcN k (S j) t := fun j =>
    intervalIntegral.integral_nonneg hT fun t _ => Real.sqrt_nonneg _
  by_cases hj : j < N
  · have h1 : (∫ t in (0)..T, srcN k (S j) t) ≤ ∑ j ∈ Finset.range N, ∫ t in (0)..T, srcN k (S j) t :=
      Finset.single_le_sum (f := fun j => ∫ t in (0)..T, srcN k (S j) t)
        (fun j _ => hnn j) (Finset.mem_range.mpr hj)
    have : 0 ≤ Real.sqrt 2 * (1 + ∫ t in (0)..T, srcN k (S N) t) := by
      have := hnn N; positivity
    linarith
  · push Not at hj
    have hp : (∫ t in (0)..T, srcD k (S j) (S N) t) < 1 := hab (j, N) ⟨le_trans (le_max_left _ _)
      hj, le_max_right _ _⟩
    -- pointwise: `‖S_j‖ ≤ √2 (‖S_j - S_N‖ + ‖S_N‖)`
    have hpt : ∀ t, srcN k (S j) t ≤ Real.sqrt 2 * (srcD k (S j) (S N) t + srcN k (S N) t) := by
      intro t
      unfold srcN srcD
      have hle : ∑ c, Q k (S j c) t ≤ 2 * ∑ c, Q k (fun x => S j c x - S N c x) t +
          2 * ∑ c, Q k (S N c) t := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun c _ => ?_
        have := Q_add_le k ((hS j c).sub (hS N c)) (hS N c) t
        simp only [sub_add_cancel] at this
        exact this
      calc Real.sqrt (∑ c, Q k (S j c) t) ≤ Real.sqrt (2 * ∑ c, Q k (fun x => S j c x - S N c x) t +
            2 * ∑ c, Q k (S N c) t) := Real.sqrt_le_sqrt hle
        _ ≤ Real.sqrt (2 * ∑ c, Q k (fun x => S j c x - S N c x) t) +
            Real.sqrt (2 * ∑ c, Q k (S N c) t) :=
          sqrt_add_le' (mul_nonneg zero_le_two (Finset.sum_nonneg fun c _ => Q_nonneg _ _ _))
            (mul_nonneg zero_le_two (Finset.sum_nonneg fun c _ => Q_nonneg _ _ _))
        _ = _ := by rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul zero_le_two]; ring
    have hcj := continuous_srcN k (hS j)
    have hcN := continuous_srcN k (hS N)
    have hcd := continuous_srcD k (hS j) (hS N)
    have hI : ∫ t in (0)..T, srcN k (S j) t ≤
        Real.sqrt 2 * ((∫ t in (0)..T, srcD k (S j) (S N) t) + ∫ t in (0)..T, srcN k (S N) t) := by
      rw [← intervalIntegral.integral_add (hcd.intervalIntegrable _ _) (hcN.intervalIntegrable _ _),
        ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hT (hcj.intervalIntegrable _ _)
        ((continuous_const.mul (hcd.add hcN)).intervalIntegrable _ _) fun t _ => hpt t
    have h1 := Finset.sum_nonneg fun j (_ : j ∈ Finset.range N) => hnn j
    have h2 : Real.sqrt 2 * ((∫ t in (0)..T, srcD k (S j) (S N) t) + ∫ t in (0)..T, srcN k (S N) t)
        ≤ Real.sqrt 2 * (1 + ∫ t in (0)..T, srcN k (S N) t) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    linarith

theorem Wn_eq {k : ℕ} {g g' : Idx → X → ℝ} (hg : ∀ c, ContDiff ℝ ∞ (g c))
    (hg' : ∀ c, ContDiff ℝ ∞ (g' c)) (t : ℝ) :
    Wn k g g' t = ∑ c, (Q (k + 1) (fun x => g c x - g' c x) t +
      Q k (fun x => pd (g c) 0 x - pd (g' c) 0 x) t) := by
  unfold Wn
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pd_wdiff hg hg' c 0]
  rfl

/-- **`thm:hyperbolic`, the first two limits (Cauchy form)**: for metrics `g_h` with the
hypotheses of `thm:hyperbolic` (common constants, `s ≥ 5`, `Σ = 𝕋³`), if the initial data are
Cauchy in `H^{s-1} × H^{s-2}` and the sources are Cauchy in `L¹_tH^{s-2}`, then `(g_h)` is Cauchy
in `C_tH^{s-1}` and `(∂ₜg_h)` is Cauchy in `C_tH^{s-2}` on `[0, T]`. -/
theorem common_slab_cauchy {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHyp Np θ s T a0 lam Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ p : ℕ × ℕ in atTop, ∀ t ∈ Icc 0 T,
      ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) t +
        Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) t) ≤ ε := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  simp only [e1, e2] at hinit hsrc ⊢
  have hθ := (hg 0).sθ
  have hK0 := (hg 0).K0_nonneg hT.le
  obtain ⟨ca, cσ, hca, hcσ, hN⟩ := normK_fdiff_le (Np := Np) (θ := θ) (Λ := Λ) hk hT ha hlam hθ hK0
  obtain ⟨cE, cU, hcE, hcU, hEq⟩ := Ediff_equiv (Np := Np) (θ := θ) (Λ := Λ) (K0 := K0) hk hT ha
    hlam
  obtain ⟨BS, hBS⟩ := sources_bounded (k := k) (fun h => (hg h).sS) hsrc hT.le
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hsys : ∀ i j, SysHyp (diffSys a0 (gi i)) (wdiff (g i) (g j)) (fdiff a0 (gi i) (g i) (g j))
      T (lam / Λ) (Mdiff (k + 2) CS K0 Λ a0) k := fun i j => by
    have := diffSys_hyp (hg i) (hg j) (by omega) hT ha hlam.le hCS hsup
    rwa [e2] at this
  have hl := lam_div_pos (hg 0) hT ha hlam
  -- the uniform bound of `∫ a`
  have hA : ∀ (i j : ℕ), ∫ t in (0)..T, ca * srcA k (S j) t ≤ ca * (4 * T + BS) := by
    intro i j
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hca
    have hcA := continuous_srcA k (hg j).sS
    have hcN := continuous_srcN k (hg j).sS
    calc ∫ t in (0)..T, srcA k (S j) t ≤ ∫ t in (0)..T, (4 + srcN k (S j) t) :=
          intervalIntegral.integral_mono_on hT.le (hcA.intervalIntegrable _ _)
            ((continuous_const.add hcN).intervalIntegrable _ _) fun t _ => srcA_le k (S j) t
      _ = 4 * T + ∫ t in (0)..T, srcN k (S j) t := by
          rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
            (hcN.intervalIntegrable _ _)]
          simp; ring
      _ ≤ 4 * T + BS := by linarith [hBS j]
  -- initial energies
  have h0 : Tendsto (fun p : ℕ × ℕ => energyK k (diffSys a0 (gi p.1)).γ (wdiff (g p.1) (g p.2)) 0)
      atTop (𝓝 0) := by
    have hW : Tendsto (fun p : ℕ × ℕ => cU * Wn k (g p.1) (g p.2) 0) atTop (𝓝 0) := by
      have := hinit.const_mul cU
      rw [mul_zero] at this
      refine this.congr fun p => ?_
      rw [Wn_eq (hg p.1).sg (hg p.2).sg]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hW (fun p => ?_)
      (fun p => ?_)
    · exact (hEq _ _ _ _ _ _ (hg p.1) (hg p.2) 0 ⟨le_rfl, hT.le⟩).1
    · exact (hEq _ _ _ _ _ _ (hg p.1) (hg p.2) 0 ⟨le_rfl, hT.le⟩).2.2
  have hσT : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T, cσ * srcD k (S p.1) (S p.2) t) atTop
      (𝓝 0) := by
    have := hsrc.const_mul cσ
    rw [mul_zero] at this
    refine this.congr fun p => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hmain := energyK_tendsto_zero k hsys hl hT.le (a := fun i j t => ca * srcA k (S j) t)
    (σ := fun i j t => cσ * srcD k (S i) (S j) t)
    (fun i j => continuous_const.mul (continuous_srcA k (hg j).sS))
    (fun i j => continuous_const.mul (continuous_srcD k (hg i).sS (hg j).sS))
    (fun i j t => mul_nonneg hca (Real.sqrt_nonneg _))
    (fun i j t => mul_nonneg hcσ (Real.sqrt_nonneg _))
    (fun i j t ht => hN _ _ _ _ _ _ (hg i) (hg j) t ht) hA h0 hσT
  intro ε hε
  have hε' : 0 < Real.sqrt (ε / (cE + 1)) := Real.sqrt_pos.2 (by positivity)
  filter_upwards [hmain _ hε'] with p hp t ht
  rw [← Wn_eq (hg p.1).sg (hg p.2).sg]
  obtain ⟨hE0, hWE, _⟩ := hEq _ _ _ _ _ _ (hg p.1) (hg p.2) t ht
  have h1 := hp t ht
  have h2 : Ediff k a0 (g p.1) (g p.2) (gi p.1) t ≤ ε / (cE + 1) := by
    have := (Real.sqrt_le_sqrt (le_refl _)).trans h1
    have h3 := Real.sq_sqrt hE0
    have h4 := Real.sq_sqrt (show 0 ≤ ε / (cE + 1) by positivity)
    unfold Ediff at h3 ⊢
    nlinarith [Real.sqrt_nonneg (energyK k (diffSys a0 (gi p.1)).γ (wdiff (g p.1) (g p.2)) t)]
  calc Wn k (g p.1) (g p.2) t ≤ cE * Ediff k a0 (g p.1) (g p.2) (gi p.1) t := hWE
    _ ≤ cE * (ε / (cE + 1)) := mul_le_mul_of_nonneg_left h2 hcE
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

/-! ### Non-vacuity: the flat metric -/

/-- The Minkowski metric `η = diag(-1, 1, 1, 1)` as constant fields. -/
def etaF (c : Idx) (_ : X) : ℝ := if c.1 = c.2 then (if c.1 = 0 then -1 else 1) else 0

/-- Its inverse. -/
def etaInv (a b : Fin 4) (_ : X) : ℝ := if a = b then (if a = 0 then -1 else 1) else 0

theorem pd_const_fun (c : ℝ) (μ : Fin 4) : pd (fun _ : X => c) μ = fun _ => 0 := pd_const c μ

/-- **The flat metric satisfies the hypotheses of `thm:hyperbolic`** (zero nonlinearity, no
background fields, zero source; constants `a₀ = λ = Λ = K₀ = 1`), for every order `s` and every
`T ≥ 0`. -/
theorem flat_metricHyp (s : ℕ) (T : ℝ) :
    MetricHyp (κ := Empty) (fun _ => 0) (fun j => j.elim) s T 1 1 1 1 etaF etaInv
      (fun _ _ => 0) where
  sg := fun _ => contDiff_const
  sgi := fun _ _ => contDiff_const
  sS := fun _ => contDiff_const
  sθ := fun j => j.elim
  pg := fun _ => isSPeriodic_const _
  pgi := fun _ _ => isSPeriodic_const _
  pS := fun _ => isSPeriodic_const _
  pθ := fun j => j.elim
  inv := fun x _ a b => by
    fin_cases a <;> fin_cases b <;> simp [etaF, etaInv, Fin.sum_univ_four]
  hyp0 := fun x _ => by simp [etaInv]
  hypS := fun x _ ξ => by
    simp only [etaInv, Fin.succ_inj, Fin.succ_ne_zero, if_false, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [sq]
  bnd := fun x _ a b => by
    unfold etaInv; split_ifs <;> simp
  hsg := fun t _ c => by
    show Q s (fun _ => etaF c 0) t ≤ 1
    rw [Q_const]
    unfold etaF; split_ifs <;> norm_num
  hst := fun t _ c => by
    show Q (s - 1) (pd (fun _ => etaF c 0) 0) t ≤ 1
    rw [pd_const_fun, Q_const]; norm_num
  eqn := fun x _ c => by
    have : ∀ α β : Fin 4, pd (pd (etaF c) β) α x = 0 := fun α β => by
      show pd (pd (fun _ => etaF c 0) β) α x = 0
      rw [pd_const_fun, pd_const_fun]
    simp [this, Nfield, evalF]

/-- Non-vacuity of `common_slab_cauchy` (the constant flat sequence, `s = 5`). -/
example (T : ℝ) (hT : 0 < T) :=
  common_slab_cauchy (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => etaF) (gi := fun _ => etaInv) (S := fun _ _ _ => 0)
    (fun _ => flat_metricHyp 5 T) (by simp [Q_const]) (by simp [Q_const])

end ReducedWaveStab

end RenewalGeometry
