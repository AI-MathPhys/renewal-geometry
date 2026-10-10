/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHermiteRecord

/-!
# Jet readouts of smooth functionals on frozen slices

Generic infrastructure (no renewal notions) for `eq:generated-bosonic` and `eq:generated-Dirac`
(Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`): a residual, the
Riemann tensor, … is a smooth function of the space-time 2-jet (or 1-jet) of the state; on frozen
time slices its `H^r` distance between the record and the exact solution is controlled by the
`H^r` distance of the jets (Lipschitz composition, `KatoSecond.Q_compF_sub_le`), and the jet
distance is controlled by the Hermite rates of the values, first and second time derivatives.

* `J2I`, `J1I` — the index sets `{value} ⊕ {∂_μ} ⊕ {∂_β∂_α}` and `{value} ⊕ {∂_μ}`; `jop2`,
  `jop1` — the jet operators; `j2c W`, `j1c W` — the jet coordinate fields of a family `W`.
* **`jet2_energy_le`** — `Σ_{(i,b)} Q_r(∂^iW_b - ∂^iV_b) ≤ 21 (e₁ + e₂)` from
  `Σ_b Q_{r+2}(W_b - V_b) ≤ e₂`, `Σ_b Q_{r+2}(∂_tW_b - ∂_tV_b) ≤ e₂`,
  `Σ_b Q_r(∂_t²W_b - ∂_t²V_b) ≤ e₁` (spatial derivatives cost Sobolev orders, mixed derivatives
  commute); **`jet1_energy_le`** — the analogue for 1-jets in `H^{r+1}`.
* **`Q_compF_sub_le_idx`** — the Lipschitz composition estimate for any finite index type.
* `abs_sub_le_of_Q` — slice Sobolev embedding for the jet differences (chart margins).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenHermite

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Jet index sets and jet operators -/

variable (d) in
/-- The 2-jet indices: the value, the first derivatives `∂_μ`, the second derivatives
`∂_β∂_α` (`(β, α)`). -/
abbrev J2I := Unit ⊕ Fin (d + 1) ⊕ (Fin (d + 1) × Fin (d + 1))

variable (d) in
/-- The 1-jet indices. -/
abbrev J1I := Unit ⊕ Fin (d + 1)

/-- The 2-jet operators. -/
def jop2 : J2I d → (ST d → ℝ) → ST d → ℝ
  | .inl _ => fun f => f
  | .inr (.inl μ) => fun f => pd f μ
  | .inr (.inr p) => fun f => pd (pd f p.2) p.1

/-- The 1-jet operators. -/
def jop1 : J1I d → (ST d → ℝ) → ST d → ℝ
  | .inl _ => fun f => f
  | .inr μ => fun f => pd f μ

/-- The 2-jet coordinate fields of a family. -/
def j2c (W : Fin n → ST d → ℝ) (p : J2I d × Fin n) : ST d → ℝ := jop2 p.1 (W p.2)

/-- The 1-jet coordinate fields of a family. -/
def j1c (W : Fin n → ST d → ℝ) (p : J1I d × Fin n) : ST d → ℝ := jop1 p.1 (W p.2)

theorem contDiff_jop2 (i : J2I d) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (jop2 i f) := by
  rcases i with _ | μ | p
  · exact hf
  · exact contDiff_pd_top hf μ
  · exact contDiff_pd_top (contDiff_pd_top hf p.2) p.1

theorem contDiff_jop1 (i : J1I d) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (jop1 i f) := by
  rcases i with _ | μ
  · exact hf
  · exact contDiff_pd_top hf μ

theorem isSPeriodic_jop2 (i : J2I d) {f : ST d → ℝ} (hf : IsSPeriodic f) :
    IsSPeriodic (jop2 i f) := by
  rcases i with _ | μ | p
  · exact hf
  · exact isSPeriodic_pd hf μ
  · exact isSPeriodic_pd (isSPeriodic_pd hf p.2) p.1

theorem isSPeriodic_jop1 (i : J1I d) {f : ST d → ℝ} (hf : IsSPeriodic f) :
    IsSPeriodic (jop1 i f) := by
  rcases i with _ | μ
  · exact hf
  · exact isSPeriodic_pd hf μ

/-! ### Jet differences -/

theorem pd_sub_fun {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (μ : Fin (d + 1)) :
    pd (fun x => f x - g x) μ = fun x => pd f μ x - pd g μ x :=
  funext fun x => pd_sub_real hf hg μ x

theorem jop2_sub (i : J2I d) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (fun x => jop2 i f x - jop2 i g x) = jop2 i (fun x => f x - g x) := by
  rcases i with _ | μ | p
  · rfl
  · exact (pd_sub_fun hf hg μ).symm
  · show (fun x => pd (pd f p.2) p.1 x - pd (pd g p.2) p.1 x) = pd (pd (fun x => f x - g x) p.2) p.1
    rw [pd_sub_fun hf hg p.2, pd_sub_fun (contDiff_pd_top hf _) (contDiff_pd_top hg _) p.1]

theorem jop1_sub (i : J1I d) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (fun x => jop1 i f x - jop1 i g x) = jop1 i (fun x => f x - g x) := by
  rcases i with _ | μ
  · rfl
  · exact (pd_sub_fun hf hg μ).symm

/-- One component of the 2-jet energy, by the type of derivative. -/
theorem Q_jop2_le {r : ℕ} (i : J2I d) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    Q r (jop2 i f) t ≤ Q (r + 2) f t + Q (r + 2) (pd f 0) t + Q r (pd (pd f 0) 0) t := by
  have h0 := Q_nonneg (r + 2) f t
  have h1 := Q_nonneg (r + 2) (pd f 0) t
  have h2 := Q_nonneg r (pd (pd f 0) 0) t
  rcases i with _ | μ | ⟨β, α⟩
  · have := Q_mono (show r ≤ r + 2 by omega) f t
    show Q r f t ≤ _
    linarith
  · show Q r (pd f μ) t ≤ _
    induction μ using Fin.cases with
    | zero =>
      have := Q_mono (show r ≤ r + 2 by omega) (pd f 0) t
      linarith
    | succ i =>
      have := (Q_pd_le (k := r) i f t).trans (Q_mono (show r + 1 ≤ r + 2 by omega) f t)
      linarith
  · show Q r (pd (pd f α) β) t ≤ _
    induction α using Fin.cases with
    | zero =>
      induction β using Fin.cases with
      | zero => linarith
      | succ j =>
        have := (Q_pd_le (k := r) j (pd f 0) t).trans
          (Q_mono (show r + 1 ≤ r + 2 by omega) (pd f 0) t)
        linarith
    | succ i =>
      induction β using Fin.cases with
      | zero =>
        have hc : pd (pd f i.succ) 0 = pd (pd f 0) i.succ :=
          funext fun x => pd_pd_comm (hf.of_le (by norm_cast)) i.succ 0 x
        rw [hc]
        have := (Q_pd_le (k := r) i (pd f 0) t).trans
          (Q_mono (show r + 1 ≤ r + 2 by omega) (pd f 0) t)
        linarith
      | succ j =>
        have := (Q_pd_le (k := r) j (pd f i.succ) t).trans (Q_pd_le (k := r + 1) i f t)
        linarith

/-- One component of the 1-jet energy. -/
theorem Q_jop1_le {r : ℕ} (i : J1I d) (f : ST d → ℝ) (t : ℝ) :
    Q (r + 1) (jop1 i f) t ≤ Q (r + 2) f t + Q (r + 2) (pd f 0) t := by
  have h0 := Q_nonneg (r + 2) f t
  have h1 := Q_nonneg (r + 2) (pd f 0) t
  rcases i with _ | μ
  · have := Q_mono (show r + 1 ≤ r + 2 by omega) f t
    show Q (r + 1) f t ≤ _
    linarith
  · show Q (r + 1) (pd f μ) t ≤ _
    induction μ using Fin.cases with
    | zero =>
      have := Q_mono (show r + 1 ≤ r + 2 by omega) (pd f 0) t
      linarith
    | succ i =>
      have := Q_pd_le (k := r + 1) i f t
      linarith

/-- **The 2-jet energy of a difference** from the value, first and second time-derivative
bounds. -/
theorem jet2_energy_le {r : ℕ} {W V : Fin n → ST d → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (hV : ∀ b, ContDiff ℝ ∞ (V b)) {t e₁ e₂ : ℝ}
    (h0 : ∑ b, Q (r + 2) (fun x => W b x - V b x) t ≤ e₂)
    (h1 : ∑ b, Q (r + 2) (fun x => pd (W b) 0 x - pd (V b) 0 x) t ≤ e₂)
    (h2 : ∑ b, Q r (fun x => pd (pd (W b) 0) 0 x - pd (pd (V b) 0) 0 x) t ≤ e₁) :
    ∑ p : J2I d × Fin n, Q r (fun x => j2c W p x - j2c V p x) t ≤
      (Fintype.card (J2I d) : ℝ) * (e₁ + 2 * e₂) := by
  have hcomp : ∀ p : J2I d × Fin n, Q r (fun x => j2c W p x - j2c V p x) t ≤
      Q (r + 2) (fun x => W p.2 x - V p.2 x) t +
        Q (r + 2) (fun x => pd (W p.2) 0 x - pd (V p.2) 0 x) t +
        Q r (fun x => pd (pd (W p.2) 0) 0 x - pd (pd (V p.2) 0) 0 x) t := by
    intro p
    have hs := (hW p.2).sub (hV p.2)
    have e : (fun x => j2c W p x - j2c V p x) = jop2 p.1 (fun x => W p.2 x - V p.2 x) :=
      jop2_sub p.1 (hW p.2) (hV p.2)
    rw [e]
    refine (Q_jop2_le p.1 hs t).trans (le_of_eq ?_)
    rw [pd_sub_fun (hW p.2) (hV p.2) 0, pd_sub_fun (contDiff_pd_top (hW p.2) 0)
      (contDiff_pd_top (hV p.2) 0) 0]
  calc ∑ p : J2I d × Fin n, Q r (fun x => j2c W p x - j2c V p x) t
      ≤ ∑ p : J2I d × Fin n, (Q (r + 2) (fun x => W p.2 x - V p.2 x) t +
          Q (r + 2) (fun x => pd (W p.2) 0 x - pd (V p.2) 0 x) t +
          Q r (fun x => pd (pd (W p.2) 0) 0 x - pd (pd (V p.2) 0) 0 x) t) :=
        Finset.sum_le_sum fun p _ => hcomp p
    _ = ∑ _i : J2I d, (∑ b, Q (r + 2) (fun x => W b x - V b x) t +
          ∑ b, Q (r + 2) (fun x => pd (W b) 0 x - pd (V b) 0 x) t +
          ∑ b, Q r (fun x => pd (pd (W b) 0) 0 x - pd (pd (V b) 0) 0 x) t) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ∑ _i : J2I d, (e₁ + 2 * e₂) := Finset.sum_le_sum fun i _ => by linarith
    _ = (Fintype.card (J2I d) : ℝ) * (e₁ + 2 * e₂) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The 1-jet energy of a difference in `H^{r+1}`** from the value and first time-derivative
bounds in `H^{r+2}`. -/
theorem jet1_energy_le {r : ℕ} {W V : Fin n → ST d → ℝ} (hW : ∀ b, ContDiff ℝ ∞ (W b))
    (hV : ∀ b, ContDiff ℝ ∞ (V b)) {t e₂ : ℝ}
    (h0 : ∑ b, Q (r + 2) (fun x => W b x - V b x) t ≤ e₂)
    (h1 : ∑ b, Q (r + 2) (fun x => pd (W b) 0 x - pd (V b) 0 x) t ≤ e₂) :
    ∑ p : J1I d × Fin n, Q (r + 1) (fun x => j1c W p x - j1c V p x) t ≤
      (Fintype.card (J1I d) : ℝ) * (2 * e₂) := by
  have hcomp : ∀ p : J1I d × Fin n, Q (r + 1) (fun x => j1c W p x - j1c V p x) t ≤
      Q (r + 2) (fun x => W p.2 x - V p.2 x) t +
        Q (r + 2) (fun x => pd (W p.2) 0 x - pd (V p.2) 0 x) t := by
    intro p
    have e : (fun x => j1c W p x - j1c V p x) = jop1 p.1 (fun x => W p.2 x - V p.2 x) :=
      jop1_sub p.1 (hW p.2) (hV p.2)
    rw [e]
    refine (Q_jop1_le p.1 _ t).trans (le_of_eq ?_)
    rw [pd_sub_fun (hW p.2) (hV p.2) 0]
  calc ∑ p : J1I d × Fin n, Q (r + 1) (fun x => j1c W p x - j1c V p x) t
      ≤ ∑ p : J1I d × Fin n, (Q (r + 2) (fun x => W p.2 x - V p.2 x) t +
          Q (r + 2) (fun x => pd (W p.2) 0 x - pd (V p.2) 0 x) t) :=
        Finset.sum_le_sum fun p _ => hcomp p
    _ = ∑ _i : J1I d, (∑ b, Q (r + 2) (fun x => W b x - V b x) t +
          ∑ b, Q (r + 2) (fun x => pd (W b) 0 x - pd (V b) 0 x) t) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib]
    _ ≤ ∑ _i : J1I d, (2 * e₂) := Finset.sum_le_sum fun i _ => by linarith
    _ = (Fintype.card (J1I d) : ℝ) * (2 * e₂) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Composition with a general finite index set -/

/-- **Lipschitz composition estimate in `H^r` for any finite index set** (`2m ≤ r + 1`,
`m > d/2`): on the `H^r` ball of radius `R`,
`Q_r(Φ_k(u) - Φ_k(v)) ≤ K Σ_i Q_r(u_i - v_i)`. -/
theorem Q_compF_sub_le_idx {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] {Φ : κ → (ι → ℝ) → ℝ}
    (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, ∀ u v : ι → ST d → ℝ, (∀ i, ContDiff ℝ ∞ (u i)) →
      (∀ i, ContDiff ℝ ∞ (v i)) → (∀ i, IsSPeriodic (u i)) → (∀ i, IsSPeriodic (v i)) →
      ∀ t, ∑ i, Q r (u i) t ≤ R ^ 2 → ∑ i, Q r (v i) t ≤ R ^ 2 →
      Q r (fun x => Φ k (fun i => u i x) - Φ k (fun i => v i x)) t ≤
        K * ∑ i, Q r (fun x => u i x - v i x) t := by
  set e := Fintype.equivFin ι with he
  set p := Fintype.card ι
  set Ψ : κ → (Fin p → ℝ) → ℝ := fun k w => Φ k (fun i => w (e i)) with hΨ
  have hΨs : ∀ k, ContDiff ℝ ∞ (Ψ k) := fun k =>
    (hΦ k).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (e i))
  obtain ⟨K, hK0, hK⟩ := KatoSecond.Q_compF_sub_le (d := d) hm hr hΨs hR
  refine ⟨K, hK0, fun k u v hu hv hup hvp t hEu hEv => ?_⟩
  have hsum : ∀ w : ι → ST d → ℝ, energyQ r (fun j => w (e.symm j)) t = ∑ i, Q r (w i) t :=
    fun w => by
      unfold energyQ
      exact Equiv.sum_comp e.symm (fun i => Q r (w i) t)
  have h := hK k (fun j => u (e.symm j)) (fun j => v (e.symm j)) (fun j => hu _) (fun j => hv _)
    (fun j => hup _) (fun j => hvp _) t (by rw [hsum u]; exact hEu) (by rw [hsum v]; exact hEv)
  have e1 : (fun x => compF (Ψ k) (fun j => u (e.symm j)) x -
      compF (Ψ k) (fun j => v (e.symm j)) x) =
      fun x => Φ k (fun i => u i x) - Φ k (fun i => v i x) := by
    funext x
    simp [compF, hΨ]
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact hsum (fun i x => u i x - v i x)

/-! ### Slice Sobolev embedding for jet differences -/

/-- The jet differences are small pointwise when their `H^r` energy is small (`r ≥ m`,
`m > d/2`). -/
theorem abs_sub_le_of_Q {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hmr : m ≤ r) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {ι : Type*} [Fintype ι] (u v : ι → ST d → ℝ),
      (∀ i, ContDiff ℝ ∞ (u i)) → (∀ i, ContDiff ℝ ∞ (v i)) → (∀ i, IsSPeriodic (u i)) →
      (∀ i, IsSPeriodic (v i)) → ∀ (t E : ℝ), ∑ i, Q r (fun x => u i x - v i x) t ≤ E →
      ∀ y i, |u i (Fin.cons t y) - v i (Fin.cons t y)| ≤ Real.sqrt (CS * E) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  refine ⟨CS, hCS, fun {ι} _ u v hu hv hup hvp t E hE y i => ?_⟩
  have hsi : ContDiff ℝ ∞ (fun x => u i x - v i x) := (hu i).sub (hv i)
  have hpi : IsSPeriodic (fun x => u i x - v i x) := fun k x => by
    simp only [hup i k x, hvp i k x]
  have h1 := hsup _ hsi hpi t y
  have h2 : Q m (fun x => u i x - v i x) t ≤ E := by
    refine (Q_mono hmr _ t).trans ?_
    refine le_trans ?_ hE
    exact Finset.single_le_sum (f := fun i => Q r (fun x => u i x - v i x) t)
      (fun i _ => Q_nonneg _ _ _) (Finset.mem_univ i)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_left h2 hCS))

end RenewalGeometry.GenHermite
