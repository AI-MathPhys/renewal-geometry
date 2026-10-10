/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CNConvergence
import RenewalGeometry.Continuum.CoupledBootstrapSlabModel

/-!
# Slab Sobolev norms are controlled by uniform `C^k` convergence

Generic infrastructure for `cor:local-calibration-nonempty` of the Einstein–Standard-Model
action-closure manuscript: the slice norms `Q_k(f)(t) = Σ_{|w| ≤ k} ∫_{[0,1]^d} |∂^w f(t, y)|² dy`
of `SlabSobAlg` are bounded by the uniform norms of the derivatives of order `≤ k`, so uniform
`C^k` convergence (`CNConv.CN`) gives convergence of the initial `H^k` energy and of the
`L²_tH^k_x` norms on a slab.

* `norm_iteratedFDeriv_comp_clm_add_le` (generic) — `‖D^j(f(a + L·))(y)‖ ≤ ‖L‖^j ‖D^jf(a + Ly)‖`.
* `norm_iteratedFDeriv_slice_le` — derivatives of a time slice are bounded by the space-time
  derivatives.
* `Q_le_of_iteratedFDeriv`, `Q_le_of_slice_eq` — slice norms from uniform derivative bounds.
* **`tendsto_energyQ_of_CN`** — `‖U_i(t₀) - U₀(t₀)‖²_{H^k} → 0` under `C^k` convergence.
* **`tendsto_l2Sq_of_CN`** — `‖F_i‖²_{L²_tH^k_x([0,T])} → 0` when `F_i → F₀` in `C^k` and `F₀`
  vanishes on the slab `[0, T] × ℝ^d`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.CNConv

open SlabWaveHk SlabSobAlg QLEnergy CoupledBootstrap

/-- Derivatives of `y ↦ f(a + L y)`. -/
theorem norm_iteratedFDeriv_comp_clm_add_le {E' E G : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} (hf : ContDiff ℝ ∞ f) (L : E' →L[ℝ] E) (a : E) (j : ℕ)
    (y : E') : ‖iteratedFDeriv ℝ j (fun z => f (a + L z)) y‖ ≤
      ‖L‖ ^ j * ‖iteratedFDeriv ℝ j f (a + L y)‖ := by
  set g : E → G := fun z => f (a + z) with hg
  have hgs : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right L hgs y (i := j) (nat_le_inf j)
  rw [show (fun z => f (a + L z)) = g ∘ ⇑L from rfl, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin j, ‖L‖ = ‖L‖ ^ j := by simp
  rw [hprod, hg, iteratedFDeriv_comp_add_left, mul_comm]

variable {d : ℕ}

/-- The embedding `y ↦ (0, y)` of space into space-time. -/
def consL : (Fin d → ℝ) →L[ℝ] ST d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.cons 0 y
      map_add' := fun y y' => by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c y => by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }

theorem consL_apply (y : Fin d → ℝ) : consL y = (Fin.cons 0 y : ST d) := rfl

theorem norm_consL_le : ‖(consL : (Fin d → ℝ) →L[ℝ] ST d)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul, consL_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using norm_le_pi_norm y j

theorem cons_eq_add (t : ℝ) (y : Fin d → ℝ) :
    (Fin.cons t y : ST d) = (Fin.cons t 0 : ST d) + consL y := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [consL_apply]

/-- **Derivatives of a time slice** are bounded by the space-time derivatives. -/
theorem norm_iteratedFDeriv_slice_le {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (j : ℕ)
    (y : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ j (slice f t) y‖ ≤ ‖iteratedFDeriv ℝ j f (Fin.cons t y)‖ := by
  have e : slice f t = fun z => f ((Fin.cons t 0 : ST d) + consL z) :=
    funext fun z => by rw [← cons_eq_add]
  rw [e]
  refine (norm_iteratedFDeriv_comp_clm_add_le hf consL _ j y).trans ?_
  rw [← cons_eq_add]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) norm_consL_le)

/-- Slice norms from uniform space-time derivative bounds. -/
theorem Q_le_of_iteratedFDeriv {k : ℕ} {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) {t A : ℝ}
    (hA : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j f (Fin.cons t y)‖ ≤ A) :
    Q k f t ≤ (wordsLE d k).card * A ^ 2 :=
  Q_le_of_bound hf fun w hw y =>
    (abs_sd_le hf t w y).trans ((norm_iteratedFDeriv_slice_le hf t _ y).trans (hA _ hw y))

/-- Slice norms of `f` from derivative bounds of any smooth `g` agreeing with `f` on the slice. -/
theorem Q_le_of_slice_eq {k : ℕ} {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {t A : ℝ} (hfg : ∀ y, f (Fin.cons t y) = g (Fin.cons t y))
    (hA : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j g (Fin.cons t y)‖ ≤ A) :
    Q k f t ≤ (wordsLE d k).card * A ^ 2 := by
  have e : slice f t = slice g t := funext hfg
  refine Q_le_of_bound hf fun w hw y => (abs_sd_le hf t w y).trans ?_
  rw [e]
  exact (norm_iteratedFDeriv_slice_le hg t _ y).trans (hA _ hw y)

variable {ι : Type*} {l : Filter ι}

/-- **Uniform `C^k` convergence gives convergence of the `H^k` energy at every time.** -/
theorem tendsto_energyQ_of_CN {n k : ℕ} {U : ι → Fin n → ST d → ℝ} {U₀ : Fin n → ST d → ℝ}
    (h : ∀ a, CN k l (fun i => U i a) (U₀ a)) (t : ℝ) :
    Tendsto (fun i => energyQ k (fun a x => U i a x - U₀ a x) t) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := (n : ℝ) * (wordsLE d k).card + 1 with hc
  have hc0 : 0 < c := by positivity
  set δ : ℝ := Real.sqrt (ε / (2 * c)) with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδ2 : δ ^ 2 = ε / (2 * c) := Real.sq_sqrt (by positivity)
  have hev : ∀ᶠ i in l, ∀ a, ContDiff ℝ ∞ (U i a) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => U i a y - U₀ a y) x‖ ≤ δ := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [(h a).smooth, (h a).conv δ hδ0] with i h1 h2 using ⟨h1, h2⟩
  filter_upwards [hev] with i hi
  have hle : energyQ k (fun a x => U i a x - U₀ a x) t ≤ n * ((wordsLE d k).card * δ ^ 2) := by
    unfold energyQ
    calc ∑ a, Q k (fun x => U i a x - U₀ a x) t ≤ ∑ _a : Fin n, (wordsLE d k).card * δ ^ 2 :=
          Finset.sum_le_sum fun a _ => Q_le_of_iteratedFDeriv ((hi a).1.sub (h a).smooth₀)
            fun j hj y => (hi a).2 j hj _
      _ = n * ((wordsLE d k).card * δ ^ 2) := by simp
  have h0 : 0 ≤ energyQ k (fun a x => U i a x - U₀ a x) t := energyQ_nonneg k _ t
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  calc _ ≤ n * ((wordsLE d k).card * δ ^ 2) := hle
    _ ≤ c * δ ^ 2 := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = ε / 2 := by rw [hδ2]; field_simp
    _ < ε := by linarith

/-- **`L²_tH^k_x` norms on the slab tend to zero** when `F_i → F₀` in `C^k` and the limit vanishes
on the slab. -/
theorem tendsto_l2Sq_of_CN {κ : Type*} [Fintype κ] {k : ℕ} {F : ι → κ → ST 3 → ℝ}
    {F₀ : κ → ST 3 → ℝ} (h : ∀ c, CN k l (fun i => F i c) (F₀ c)) {T : ℝ} (hT : 0 ≤ T)
    (h0 : ∀ c x, x 0 ∈ Icc 0 T → F₀ c x = 0) :
    Tendsto (fun i => l2Sq k T (F i)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := (T + 1) * (Fintype.card κ * (wordsLE 3 k).card + 1) with hc
  have hc0 : 0 < c := by positivity
  set δ : ℝ := Real.sqrt (ε / (2 * c)) with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδ2 : δ ^ 2 = ε / (2 * c) := Real.sq_sqrt (by positivity)
  have hev : ∀ᶠ i in l, ∀ a, ContDiff ℝ ∞ (F i a) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => F i a y - F₀ a y) x‖ ≤ δ := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [(h a).smooth, (h a).conv δ hδ0] with i h1 h2 using ⟨h1, h2⟩
  filter_upwards [hev] with i hi
  have hQ : ∀ t ∈ Icc 0 T, ∑ a, Q k (F i a) t ≤ Fintype.card κ * ((wordsLE 3 k).card * δ ^ 2) := by
    intro t ht
    calc ∑ a, Q k (F i a) t ≤ ∑ _a : κ, (wordsLE 3 k).card * δ ^ 2 :=
          Finset.sum_le_sum fun a _ => Q_le_of_slice_eq (hi a).1 ((hi a).1.sub (h a).smooth₀)
            (fun y => by rw [h0 a _ (by simpa using ht), sub_zero])
            fun j hj y => (hi a).2 j hj _
      _ = _ := by simp
  have hint : l2Sq k T (F i) ≤ T * (Fintype.card κ * ((wordsLE 3 k).card * δ ^ 2)) := by
    unfold l2Sq
    have := intervalIntegral.integral_mono_on hT (intervalIntegrable_sumQ k T fun a => (hi a).1)
      intervalIntegrable_const hQ
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hnn : 0 ≤ l2Sq k T (F i) := l2Sq_nonneg k hT _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  calc _ ≤ T * (Fintype.card κ * ((wordsLE 3 k).card * δ ^ 2)) := hint
    _ ≤ c * δ ^ 2 := by
        rw [hc, ← mul_assoc, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ),
          Nat.cast_nonneg (α := ℝ) (wordsLE 3 k).card]
    _ = ε / 2 := by rw [hδ2]; field_simp
    _ < ε := by linarith

end RenewalGeometry.CNConv

end
