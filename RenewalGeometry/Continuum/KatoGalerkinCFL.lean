/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoLocalExistence
import RenewalGeometry.Continuum.SlabMoserComposition

/-!
# The explicit CFL condition for the spectral midpoint scheme on `𝕋^d`

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript (`eq:generated-midpoint`, `eq:generated-CFL`,
`eq:generated-uniform`; `app:generated-dynamics`: "On `Ran P_N` the inverse inequality gives
`‖G_N(V) - G_N(W)‖_{H^q} ≤ C_R(N+1)‖V - W‖_{H^q}`.  Thus `eq:generated-CFL` makes the midpoint
fixed-point map a contraction").  Setting of `KatoGalerkinODE`: `∂_tU + Σ_i A^i(U)∂_iU = F(U)` on
`𝕋^d` with smooth real symmetric `A^i` and smooth `F`, Galerkin space `GS d n N` (box `|k_i| ≤ N`,
Euclidean norm = classical `H^q` norm), `G_N = P_N G`.

* `contDiff_integral_unit` — parametric integrals `x ↦ ∫₀¹ Φ(x, s) ds` of jointly smooth
  integrands are smooth; `hadQ`, **`hadamard`** — Hadamard's lemma
  `Φ(x) - Φ(y) = Σ_c (x_c - y_c) Ψ_c(x, y)` with smooth quotients `Ψ_c`.
* **`Q_genG_sub_le`** — the `H^{r+1} → H^r` Lipschitz estimate of the generator:
  `‖G(U) - G(V)‖²_{H^r} ≤ C_ρ ‖U - V‖²_{H^{r+1}}` on the `H^{r+1}` ball of radius `ρ`
  (`2m ≤ r + 1`, `m > d/2`; Hadamard + Moser composition `SlabMoser.Q_compF_le` + `H^r` algebra).
* `wq_succ_le_box` — the **inverse inequality** on the frequency box:
  `wq (r+1) k ≤ (1 + d(2πN)²) wq r k ≤ (1 + 4π²d)(N+1)² wq r k` for `|k_i| ≤ N`.
* **`GN_lip_cfl`**, **`GN_bound_cfl`** — `‖G_N(a) - G_N(a')‖_{H^q} ≤ C_ρ(N+1)‖a - a'‖_{H^q}` and
  `‖G_N(a)‖_{H^q} ≤ C_M(N+1)` on the `H^q` ball, for every cutoff `N` (`q ≥ 2m`).
* **`midpoint_uniform_cfl`** (`eq:generated-CFL` ⇒ `eq:generated-uniform`): there are `T > 0`,
  `R`, `c_* > 0`, `τ_* > 0` depending only on the data radius such that for every cutoff `N`,
  every step with `τ(N + 1) ≤ c_*` and `τ ≤ τ_*`, and every finite initial state
  `‖U_{0,N}‖_{H^q} ≤ R₀`, the implicit midpoint recursion exists on `[0, T]`, each step being the
  unique fixed point in the ball `‖V - U^j‖ ≤ τ C_M(N + 1)`, with `‖U^j‖_{H^q} ≤ R`;
  `midpoint_uniform_cfl_P0` for the truncated data `P_N U₀`.  This replaces the abstract step
  bound `τ ≤ τ_N` of `KatoGalerkin.midpoint_uniform` by the explicit CFL form.

Disclosed rendering (as in `KatoGalerkinODE`): `Σ = 𝕋^d` (`d = 3` in the manuscript), the
coefficients are smooth on all of `ℝ^n` (a chart is handled by a smooth cutoff extension).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.KatoCFL

universe u

set_option linter.unusedSectionVars false

section Param

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasFDerivAt_integral_unit {Φ : E × ℝ → F} (hΦ : ContDiff ℝ 1 Φ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ s in (0 : ℝ)..1, Φ (x, s))
      (∫ s in (0 : ℝ)..1, (fderiv ℝ Φ (x₀, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  set Φ' : E → ℝ → E →L[ℝ] F := fun x s =>
    (fderiv ℝ Φ (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ) with hΦ'
  have hcont : Continuous fun p : E × ℝ => Φ' p.1 p.2 :=
    (hΦ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hderiv : ∀ x s, HasFDerivAt (fun x => Φ (x, s)) (Φ' x s) x := fun x s =>
    ((hΦ.differentiable one_ne_zero (x, s)).hasFDerivAt).comp x (hasFDerivAt_prodMk_left x s)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_Icc (a := (0 : ℝ))
    (b := 1))).exists_bound_of_continuousOn hcont.continuousOn
  have hcΦ : Continuous Φ := hΦ.continuous
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun x s => Φ (x, s)) (F' := Φ') (bound := fun _ => C)
    (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      (hcΦ.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact (hcΦ.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun s hs x hx => ?_
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hs; exact Ioc_subset_Icc_self hs
    exact hC (x, s) ⟨Metric.ball_subset_closedBall hx, hs'⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun s _ x _ => hderiv x s

/-- **Parametric integrals of jointly smooth integrands are smooth**:
`x ↦ ∫₀¹ Φ(x, s) ds` is `C^∞` if `Φ` is (finite-dimensional parameter space). -/
theorem contDiff_integral_unit {Φ : E × ℝ → F} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun x => ∫ s in (0 : ℝ)..1, Φ (x, s)) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing F with
  | zero =>
    exact contDiff_zero.2 (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x s => Φ (x, s)) hΦ.continuous 0 1)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ s in (0 : ℝ)..1, (fderiv ℝ Φ (x, s)).comp
      (ContinuousLinearMap.inl ℝ E ℝ), ?_, fun x =>
        hasFDerivAt_integral_unit (hΦ.of_le (by exact_mod_cast le_top)) x⟩
    have hs : ContDiff ℝ ∞ fun p : E × ℝ =>
        (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ E ℝ) :=
      (hΦ.fderiv_right (m := ∞) le_rfl).clm_comp contDiff_const
    exact ih hs

end Param

/-! ### Hadamard's lemma -/

section Hadamard

variable {n : ℕ}

/-- The Hadamard quotient `Ψ_c(x, y) = ∫₀¹ ∂_cΦ(y + s(x - y)) ds`. -/
def hadQ (Φ : (Fin n → ℝ) → ℝ) (c : Fin n) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, fderiv ℝ Φ (p.2 + s • (p.1 - p.2)) (Pi.single c 1)

theorem contDiff_hadQ {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (c : Fin n) :
    ContDiff ℝ ∞ (hadQ Φ c) := by
  have h : ContDiff ℝ ∞ fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
      fderiv ℝ Φ (z.1.2 + z.2 • (z.1.1 - z.1.2)) (Pi.single c 1) := by
    have h1 : ContDiff ℝ ∞ fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
        z.1.2 + z.2 • (z.1.1 - z.1.2) := by fun_prop
    exact ((hΦ.fderiv_right (m := ∞) le_rfl).comp h1).clm_apply contDiff_const
  exact contDiff_integral_unit (Φ := fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
    fderiv ℝ Φ (z.1.2 + z.2 • (z.1.1 - z.1.2)) (Pi.single c 1)) h

/-- **Hadamard's lemma**: `Φ(x) - Φ(y) = Σ_c (x_c - y_c) Ψ_c(x, y)`. -/
theorem hadamard {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (x y : Fin n → ℝ) :
    Φ x - Φ y = ∑ c, (x c - y c) * hadQ Φ c (x, y) := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Φ (y + s • (x - y)))
      (fderiv ℝ Φ (y + s • (x - y)) (x - y)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) s := by
      simpa using ((hasDerivAt_id s).smul_const (x - y)).const_add y
    exact ((hΦ.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => fderiv ℝ Φ (y + s • (x - y)) (x - y) :=
    ((hΦ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hFTC
  rw [← hFTC]
  have hxy : x - y = ∑ c, (x c - y c) • (Pi.single c 1 : Fin n → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ p : Fin n → ℝ, fderiv ℝ Φ p (x - y) =
      ∑ c, (x c - y c) * fderiv ℝ Φ p (Pi.single c 1) := fun p => by
    rw [hxy, map_sum]
    simp [smul_eq_mul]
  have e : (fun s : ℝ => fderiv ℝ Φ (y + s • (x - y)) (x - y)) =
      fun s => ∑ c, (x c - y c) * fderiv ℝ Φ (y + s • (x - y)) (Pi.single c 1) := by
    funext s
    exact key _
  rw [e, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  · intro c _
    exact (continuous_const.mul (((hΦ.continuous_fderiv (by simp)).comp
      (by fun_prop)).clm_apply continuous_const)).intervalIntegrable _ _

end Hadamard


/-! ### The `H^{q-1}` Lipschitz estimate of the generator -/

section Lip

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy

variable {d n : ℕ}

/-- The pair field `(u, v)` with `2n` components. -/
def pairF (u v : Fin n → ST d → ℝ) : Fin (n + n) → ST d → ℝ := Fin.append u v

/-- A function of a pair of states as a function of the `2n` components. -/
def onPair (Ψ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (z : Fin (n + n) → ℝ) : ℝ :=
  Ψ (fun c => z (Fin.castAdd n c), fun c => z (Fin.natAdd n c))

theorem contDiff_onPair {Ψ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (onPair Ψ) := by
  unfold onPair
  refine hΨ.comp (ContDiff.prodMk ?_ ?_)
  · exact contDiff_pi.2 fun c => contDiff_apply ℝ ℝ (Fin.castAdd n c)
  · exact contDiff_pi.2 fun c => contDiff_apply ℝ ℝ (Fin.natAdd n c)

theorem compF_onPair (Ψ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (u v : Fin n → ST d → ℝ) (x : ST d) :
    compF (onPair Ψ) (pairF u v) x = Ψ (fun c => u c x, fun c => v c x) := by
  simp only [compF, onPair, pairF, Fin.append_left, Fin.append_right]

theorem energyQ_pairF (k : ℕ) (u v : Fin n → ST d → ℝ) (t : ℝ) :
    energyQ k (pairF u v) t = energyQ k u t + energyQ k v t := by
  simp only [energyQ, pairF, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem contDiff_pairF {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) : ∀ b, ContDiff ℝ ∞ (pairF u v b) := by
  intro b
  refine Fin.addCases (fun c => ?_) (fun c => ?_) b
  · simpa only [pairF, Fin.append_left] using hu c
  · simpa only [pairF, Fin.append_right] using hv c

theorem isSPeriodic_pairF {u v : Fin n → ST d → ℝ} (hu : ∀ b, IsSPeriodic (u b))
    (hv : ∀ b, IsSPeriodic (v b)) : ∀ b, IsSPeriodic (pairF u v b) := by
  intro b
  refine Fin.addCases (fun c => ?_) (fun c => ?_) b
  · simpa only [pairF, Fin.append_left] using hu c
  · simpa only [pairF, Fin.append_right] using hv c

/-- Moser composition for a finite family of smooth maps (uniform constant). -/
theorem Q_compF_family_le {p m r : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    {κ : Type*} [Fintype κ] {Φ : κ → (Fin p → ℝ) → ℝ} (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k)) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, ∀ u : Fin p → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, IsSPeriodic (u b)) → ∀ t, energyQ r u t ≤ R ^ 2 → Q r (compF (Φ k) u) t ≤ K := by
  have h := fun k => SlabMoser.Q_compF_le (d := d) hm hr (hΦ k) hR
  choose K hK0 hK using h
  refine ⟨∑ k, K k, Finset.sum_nonneg fun k _ => hK0 k, fun k u hu hup t hE => ?_⟩
  exact (hK k u hu hup t hE).trans (Finset.single_le_sum (f := K) (fun k _ => hK0 k)
    (Finset.mem_univ k))

/-- The pointwise Hadamard decomposition of the difference of generators. -/
theorem genG_sub_eq {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {u v : Fin n → ST d → ℝ} (hu : ∀ b, ContDiff ℝ ∞ (u b))
    (hv : ∀ b, ContDiff ℝ ∞ (v b)) (a : Fin n) (x : ST d) :
    genG A F u a x - genG A F v a x =
      ∑ c, (u c x - v c x) * compF (onPair (hadQ (F a) c)) (pairF u v) x -
        ∑ i, ∑ b, (compF (A i a b) u x * pd (fun y => u b y - v b y) i.succ x +
          ∑ c, (u c x - v c x) * (compF (onPair (hadQ (A i a b) c)) (pairF u v) x *
            pd (v b) i.succ x)) := by
  simp only [compF_onPair, genG]
  have hFa := hadamard (hF a) (fun c => u c x) (fun c => v c x)
  have hAa : ∀ i b, A i a b (fun c => u c x) - A i a b (fun c => v c x) =
      ∑ c, (u c x - v c x) * hadQ (A i a b) c ((fun c => u c x), (fun c => v c x)) :=
    fun i b => hadamard (hA i a b) _ _
  have hpd : ∀ i : Fin d, ∀ b, pd (fun y => u b y - v b y) i.succ x =
      pd (u b) i.succ x - pd (v b) i.succ x := fun i b => KatoGalerkin.pd_sub_real (hu b) (hv b) _ x
  simp only [hpd]
  rw [← hFa]
  have : ∀ i b, compF (A i a b) u x * pd (u b) i.succ x - compF (A i a b) v x * pd (v b) i.succ x
      = compF (A i a b) u x * (pd (u b) i.succ x - pd (v b) i.succ x) +
        ∑ c, (u c x - v c x) * (hadQ (A i a b) c ((fun c => u c x), (fun c => v c x)) *
          pd (v b) i.succ x) := by
    intro i b
    simp only [← mul_assoc, ← Finset.sum_mul, ← hAa i b, compF]
    ring
  simp only [← this, Finset.sum_sub_distrib]
  simp only [compF]
  ring

/-- **The `H^r` Lipschitz estimate of the generator** (`H^{r+1} → H^r`, one derivative lost):
for `m > d/2`, `2m ≤ r + 1`, smooth `A^i`, `F` and every radius `ρ`, there is `C` with
`‖G(U)_a - G(V)_a‖²_{H^r} ≤ C ‖U - V‖²_{H^{r+1}}` for smooth periodic `U, V` in the `H^{r+1}` ball
of radius `ρ` (Hadamard decomposition, Moser composition, `H^r` algebra). -/
theorem Q_genG_sub_le {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Fin n → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) →
      ∀ t, energyQ (r + 1) u t ≤ ρ ^ 2 → energyQ (r + 1) v t ≤ ρ ^ 2 → ∀ a,
      Q r (fun x => genG A F u a x - genG A F v a x) t ≤
        C * energyQ (r + 1) (fun b x => u b x - v b x) t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  set c := algC d r CS with hc
  have hc0 : 0 ≤ c := algC_nonneg r hCS
  have hR : 0 ≤ Real.sqrt 2 * ρ := by positivity
  -- uniform composition bounds on the pair field
  obtain ⟨K1, hK10, hK1⟩ := Q_compF_family_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin n × Fin n => onPair (hadQ (F k.1) k.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hF k.1) k.2)) hR
  obtain ⟨K2, hK20, hK2⟩ := Q_compF_family_le (d := d) (p := n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n => A k.1 k.2.1 k.2.2) (fun k => hA _ _ _) hρ
  obtain ⟨K3, hK30, hK3⟩ := Q_compF_family_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n × Fin n => onPair (hadQ (A k.1 k.2.1 k.2.2.1) k.2.2.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hA _ _ _) _)) hR
  set K := K1 + K2 + K3 with hK
  have hK0 : 0 ≤ K := by positivity
  set P := c * K + c * (c * K * ρ ^ 2) with hP
  have hP0 : 0 ≤ P := by positivity
  set C := (2 * (n * (n * P)) + 2 * (d * (d * (n * (n * (2 * P + 2 * (n * (n * P)))))))) with hC
  refine ⟨C, by positivity, fun u v hu hv hup hvp t hEu hEv a => ?_⟩
  set D : Fin n → ST d → ℝ := fun b x => u b x - v b x with hD
  have hDs : ∀ b, ContDiff ℝ ∞ (D b) := fun b => (hu b).sub (hv b)
  have hDp : ∀ b, IsSPeriodic (D b) := fun b k x => by simp only [hD, hup b k x, hvp b k x]
  set E := energyQ (r + 1) D t with hE
  have hE0 : 0 ≤ E := energyQ_nonneg _ _ _
  have hDr : ∀ b, Q r (D b) t ≤ E := fun b =>
    (Q_mono (Nat.le_succ r) _ _).trans (KatoGalerkin.Q_le_energyQ (r + 1) D t b)
  have hpdD : ∀ (i : Fin d) b, Q r (pd (D b) i.succ) t ≤ E := fun i b =>
    (Q_pd_le i (D b) t).trans (KatoGalerkin.Q_le_energyQ (r + 1) D t b)
  have hpdv : ∀ (i : Fin d) b, Q r (pd (v b) i.succ) t ≤ ρ ^ 2 := fun i b =>
    (Q_pd_le i (v b) t).trans ((KatoGalerkin.Q_le_energyQ (r + 1) v t b).trans hEv)
  have hEu' : energyQ r u t ≤ ρ ^ 2 := le_trans (Finset.sum_le_sum fun b _ =>
      Q_mono (Nat.le_succ r) (u b) t) hEu
  have hEv' : energyQ r v t ≤ ρ ^ 2 := le_trans (Finset.sum_le_sum fun b _ =>
      Q_mono (Nat.le_succ r) (v b) t) hEv
  have hEpair : energyQ r (pairF u v) t ≤ (Real.sqrt 2 * ρ) ^ 2 := by
    rw [energyQ_pairF, mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hws := contDiff_pairF hu hv
  have hwp := isSPeriodic_pairF hup hvp
  -- the three kinds of terms
  have hΨF : ∀ c', Q r (compF (onPair (hadQ (F a) c')) (pairF u v)) t ≤ K := fun c' =>
    (hK1 (a, c') _ hws hwp t hEpair).trans (by linarith)
  have hAu : ∀ (i : Fin d) b, Q r (compF (A i a b) u) t ≤ K := fun i b =>
    (hK2 (i, a, b) u hu hup t hEu').trans (by linarith)
  have hΨA : ∀ (i : Fin d) b c', Q r (compF (onPair (hadQ (A i a b) c')) (pairF u v)) t ≤ K :=
    fun i b c' => (hK3 (i, a, b, c') _ hws hwp t hEpair).trans (by linarith)
  have sF : ∀ c', ContDiff ℝ ∞ (compF (onPair (hadQ (F a) c')) (pairF u v)) := fun c' =>
    contDiff_compF (contDiff_onPair (contDiff_hadQ (hF a) c')) hws
  have sA : ∀ (i : Fin d) b, ContDiff ℝ ∞ (compF (A i a b) u) := fun i b =>
    contDiff_compF (hA i a b) hu
  have sΨA : ∀ (i : Fin d) b c', ContDiff ℝ ∞ (compF (onPair (hadQ (A i a b) c')) (pairF u v)) :=
    fun i b c' => contDiff_compF (contDiff_onPair (contDiff_hadQ (hA i a b) c')) hws
  have pF : ∀ c', IsSPeriodic (compF (onPair (hadQ (F a) c')) (pairF u v)) := fun c' =>
    isSPeriodic_compF _ hwp
  have pA : ∀ (i : Fin d) b, IsSPeriodic (compF (A i a b) u) := fun i b => isSPeriodic_compF _ hup
  have pΨA : ∀ (i : Fin d) b c', IsSPeriodic (compF (onPair (hadQ (A i a b) c')) (pairF u v)) :=
    fun i b c' => isSPeriodic_compF _ hwp
  have hcK : c * K * E ≤ P * E := by
    rw [hP]; nlinarith [mul_nonneg (mul_nonneg hc0 (mul_nonneg hc0 hK0)) (mul_nonneg (sq_nonneg ρ) hE0)]
  have t1 : ∀ c', Q r (fun x => D c' x * compF (onPair (hadQ (F a) c')) (pairF u v) x) t ≤ P * E :=
    fun c' => by
      refine (Q_mul_le hr hCS hsup (hDs c') (sF c') (hDp c') (pF c') t).trans ?_
      calc algC d r CS * Q r (D c') t * Q r _ t ≤ c * E * K :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hDr c') hc0) (hΨF c') (Q_nonneg _ _ _)
              (by positivity)
        _ = c * K * E := by ring
        _ ≤ P * E := hcK
  have t2 : ∀ (i : Fin d) b, Q r (fun x => compF (A i a b) u x * pd (D b) i.succ x) t ≤ P * E :=
    fun i b => by
      refine (Q_mul_le hr hCS hsup (sA i b) (contDiff_pd_top (hDs b) _) (pA i b)
        (isSPeriodic_pd (hDp b) _) t).trans ?_
      calc algC d r CS * Q r (compF (A i a b) u) t * Q r (pd (D b) i.succ) t ≤ c * K * E :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hAu i b) hc0) (hpdD i b) (Q_nonneg _ _ _)
              (by positivity)
        _ ≤ P * E := hcK
  have t3 : ∀ (i : Fin d) b c', Q r (fun x => D c' x *
      (compF (onPair (hadQ (A i a b) c')) (pairF u v) x * pd (v b) i.succ x)) t ≤ P * E :=
    fun i b c' => by
      have hs := (sΨA i b c').mul (contDiff_pd_top (hv b) i.succ)
      have hp : IsSPeriodic fun x => compF (onPair (hadQ (A i a b) c')) (pairF u v) x *
          pd (v b) i.succ x := fun k x => by
        simp only [pΨA i b c' k x, isSPeriodic_pd (hvp b) i.succ k x]
      have hin : Q r (fun x => compF (onPair (hadQ (A i a b) c')) (pairF u v) x *
          pd (v b) i.succ x) t ≤ c * K * ρ ^ 2 := by
        refine (Q_mul_le hr hCS hsup (sΨA i b c') (contDiff_pd_top (hv b) _) (pΨA i b c')
          (isSPeriodic_pd (hvp b) _) t).trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hΨA i b c') hc0) (hpdv i b) (Q_nonneg _ _ _)
          (by positivity)
      refine (Q_mul_le hr hCS hsup (hDs c') hs (hDp c') hp t).trans ?_
      calc algC d r CS * Q r (D c') t * Q r _ t ≤ c * E * (c * K * ρ ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hDr c') hc0) hin (Q_nonneg _ _ _)
              (by positivity)
        _ ≤ P * E := by rw [hP]; nlinarith [mul_nonneg (mul_nonneg hc0 hK0) hE0]
  -- assemble
  have heq : (fun x => genG A F u a x - genG A F v a x) = fun x =>
      (∑ c', D c' x * compF (onPair (hadQ (F a) c')) (pairF u v) x) -
        ∑ i, ∑ b, (compF (A i a b) u x * pd (D b) i.succ x +
          ∑ c', D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x *
            pd (v b) i.succ x)) := by
    funext x; exact genG_sub_eq hA hF hu hv a x
  rw [heq]
  have sT1 : ContDiff ℝ ∞ fun x => ∑ c', D c' x * compF (onPair (hadQ (F a) c')) (pairF u v) x :=
    ContDiff.sum fun c' _ => (hDs c').mul (sF c')
  have sZ : ∀ (i : Fin d) b, ContDiff ℝ ∞ fun x => compF (A i a b) u x * pd (D b) i.succ x +
      ∑ c', D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x * pd (v b) i.succ x) :=
    fun i b => ((sA i b).mul (contDiff_pd_top (hDs b) _)).add (ContDiff.sum fun c' _ =>
      (hDs c').mul ((sΨA i b c').mul (contDiff_pd_top (hv b) _)))
  have sT2 : ContDiff ℝ ∞ fun x => ∑ i, ∑ b, (compF (A i a b) u x * pd (D b) i.succ x +
      ∑ c', D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x * pd (v b) i.succ x)) :=
    ContDiff.sum fun i _ => ContDiff.sum fun b _ => sZ i b
  refine (Q_sub_le r sT1 sT2 t).trans ?_
  have hT1 : Q r (fun x => ∑ c', D c' x * compF (onPair (hadQ (F a) c')) (pairF u v) x) t ≤
      n * (n * (P * E)) := by
    refine (Q_sum_le r Finset.univ (fun c' => (hDs c').mul (sF c')) t).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ c', Q r _ t ≤ ∑ _c' : Fin n, P * E := Finset.sum_le_sum fun c' _ => t1 c'
      _ = n * (P * E) := by simp
  have hZ : ∀ (i : Fin d) b, Q r (fun x => compF (A i a b) u x * pd (D b) i.succ x +
      ∑ c', D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x * pd (v b) i.succ x)) t ≤
      2 * (P * E) + 2 * (n * (n * (P * E))) := by
    intro i b
    refine (Q_add_le r ((sA i b).mul (contDiff_pd_top (hDs b) _)) (ContDiff.sum fun c' _ =>
      (hDs c').mul ((sΨA i b c').mul (contDiff_pd_top (hv b) _))) t).trans ?_
    have h2 := (Q_sum_le r Finset.univ (fun c' => (hDs c').mul ((sΨA i b c').mul
      (contDiff_pd_top (hv b) i.succ))) t)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ∑ c', Q r (fun x => D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x *
        pd (v b) i.succ x)) t ≤ n * (P * E) := by
      calc _ ≤ ∑ _c' : Fin n, P * E := Finset.sum_le_sum fun c' _ => t3 i b c'
        _ = n * (P * E) := by simp
    have h4 := t2 i b
    have h5 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have hT2 : Q r (fun x => ∑ i, ∑ b, (compF (A i a b) u x * pd (D b) i.succ x +
      ∑ c', D c' x * (compF (onPair (hadQ (A i a b) c')) (pairF u v) x * pd (v b) i.succ x))) t ≤
      d * (d * (n * (n * (2 * (P * E) + 2 * (n * (n * (P * E))))))) := by
    refine (Q_sum_le r Finset.univ (fun i => ContDiff.sum fun b _ => sZ i b) t).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ i, Q r (fun x => ∑ b, _) t ≤
        ∑ _i : Fin d, n * (n * (2 * (P * E) + 2 * (n * (n * (P * E))))) :=
          Finset.sum_le_sum fun i _ => by
            refine (Q_sum_le r Finset.univ (fun b => sZ i b) t).trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            calc ∑ b, Q r _ t ≤ ∑ _b : Fin n, (2 * (P * E) + 2 * (n * (n * (P * E)))) :=
                  Finset.sum_le_sum fun b _ => hZ i b
              _ = _ := by simp; ring
      _ = _ := by simp
  have e : C * E = 2 * (n * (n * (P * E))) +
      2 * (d * (d * (n * (n * (2 * (P * E) + 2 * (n * (n * (P * E)))))))) := by
    rw [hC]; ring
  rw [e]
  linarith

end Lip

/-! ### The inverse inequality on the Galerkin space and the CFL midpoint scheme -/

section CFL

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin
open scoped RealInnerProductSpace

variable {d n : ℕ}

theorem sum_insert_le_of_nonneg {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ insert a s, f x ≤ f a + ∑ x ∈ s, f x := by
  by_cases h : a ∈ s
  · rw [Finset.insert_eq_of_mem h]; linarith [hf a]
  · rw [Finset.sum_insert h]

/-- **The inverse inequality for the `H^q` weights on the frequency box**: for `|k_i| ≤ N`,
`wq (r+1) k ≤ (1 + d (2πN)²) wq r k`. -/
theorem wq_succ_le_box {N : ℕ} {k : Fin d → ℤ} (hk : k ∈ KatoGalerkin.box N) (r : ℕ) :
    wq (r + 1) k ≤ (1 + d * (2 * π * N) ^ 2) * wq r k := by
  classical
  have hki : ∀ i, (2 * π * (k i : ℝ)) ^ 2 ≤ (2 * π * N) ^ 2 := by
    intro i
    have h1 : |(k i : ℝ)| ≤ N := by
      have := (mem_box.1 hk) i
      exact_mod_cast this
    have h2 : |2 * π * (k i : ℝ)| ≤ 2 * π * N := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc (2 * π * (k i : ℝ)) ^ 2 = |2 * π * (k i : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * π * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  unfold wq
  rw [show wordsLE d (r + 1) = insert [] ((Finset.univ ×ˢ wordsLE d r).image
    fun p => p.1 :: p.2) from rfl]
  refine (sum_insert_le_of_nonneg (fun L => muL_nonneg L k)).trans ?_
  have himg : ∑ L ∈ (Finset.univ ×ˢ wordsLE d r).image (fun p : Fin d × List (Fin d) => p.1 :: p.2),
      muL L k ≤ ∑ p ∈ Finset.univ ×ˢ wordsLE d r, muL (p.1 :: p.2) k :=
    Finset.sum_image_le_of_nonneg fun L _ => muL_nonneg L k
  have hprod : ∑ p ∈ Finset.univ ×ˢ wordsLE d r, muL (p.1 :: p.2) k ≤
      d * (2 * π * N) ^ 2 * ∑ L ∈ wordsLE d r, muL L k := by
    rw [Finset.sum_product]
    calc ∑ i : Fin d, ∑ L ∈ wordsLE d r, muL (i :: L) k
        ≤ ∑ _i : Fin d, (2 * π * N) ^ 2 * ∑ L ∈ wordsLE d r, muL L k :=
          Finset.sum_le_sum fun i _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun L _ => by
              rw [muL_cons]; exact mul_le_mul_of_nonneg_right (hki i) (muL_nonneg L k)
      _ = _ := by simp; ring
  have h1 : muL ([] : List (Fin d)) k ≤ ∑ L ∈ wordsLE d r, muL L k := by
    have := one_le_wq (d := d) r k
    rw [muL_nil]; exact this
  have hS : 0 ≤ ∑ L ∈ wordsLE d r, muL L k := Finset.sum_nonneg fun L _ => muL_nonneg L k
  nlinarith

theorem one_add_le_succ_sq (d N : ℕ) :
    1 + d * (2 * π * N) ^ 2 ≤ (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 := by
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hπ : 0 ≤ π ^ 2 := sq_nonneg π
  nlinarith [mul_nonneg (mul_nonneg hπ hd) h0, mul_nonneg hπ hd]

theorem cf_sub (q : ℕ) {N : ℕ} (a a' : GS d n N) (b : Fin n) (k : Fin d → ℤ) :
    cf q (a - a') b k = cf q a b k - cf q a' b k := by
  unfold cf
  split_ifs with hk
  · simp [sub_div]
  · simp

theorem fld_sub (q : ℕ) {N : ℕ} (a a' : GS d n N) :
    fld q (a - a') = fun b x => fld q a b x - fld q a' b x := by
  funext b x
  rw [fld, fld, fld, tfs_sub]
  congr 1; funext k; exact cf_sub q a a' b k

theorem fld_zero (q : ℕ) {N : ℕ} : fld q (0 : GS d n N) = fun _ _ => 0 := by
  funext b x
  have h0 : ∀ k, cf q (0 : GS d n N) b k = 0 := fun k => by
    unfold cf; split_ifs <;> simp
  simp [fld, tfs, h0]

/-- The squared norm of `G_N(a) - G_N(a')` in Fourier form. -/
theorem norm_GN_sub_sq {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b))
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (q : ℕ) {N : ℕ} (a a' : GS d n N) :
    ‖GN A F q a - GN A F q a'‖ ^ 2 = ∑ b, ∑ k ∈ box (d := d) N, wq q k *
      coef (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) 0 k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_coe_sort (box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PiLp.sub_apply, GN_apply, GN_apply, ← mul_sub,
    coef_sub (contDiff_genG hA hF (fun b => contDiff_fld q a b) b).continuous
      (contDiff_genG hA hF (fun b => contDiff_fld q a' b) b).continuous, mul_pow,
    Real.sq_sqrt (wq_nonneg q k.1)]

/-- **The CFL Lipschitz bound of the projected generator** (inverse inequality on `Ran P_N`):
for `m > d/2`, `q ≥ 2m` and every radius `ρ` there is `C_ρ` with
`‖G_N(a) - G_N(a')‖_{H^q} ≤ C_ρ (N + 1) ‖a - a'‖_{H^q}` for all cutoffs `N` and all Galerkin
states in the `H^q` ball of radius `ρ`. -/
theorem GN_lip_cfl {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (N : ℕ) (a a' : GS d n N), ‖a‖ ≤ ρ → ‖a'‖ ≤ ρ →
      ‖GN A F q a - GN A F q a'‖ ≤ CR * ((N : ℝ) + 1) * ‖a - a'‖ := by
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    exact_mod_cast this
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨C, hC0, hC⟩ := Q_genG_sub_le (d := d) (n := n) hm (by omega : 2 * m ≤ r + 1) hA hF hρ
  set c0 := (1 + 4 * π ^ 2 * d) * (n * C) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  refine ⟨Real.sqrt c0, Real.sqrt_nonneg _, fun N a a' ha ha' => ?_⟩
  have hEa : energyQ (r + 1) (fld (r + 1) a) 0 ≤ ρ ^ 2 := by
    rw [energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hEa' : energyQ (r + 1) (fld (r + 1) a') 0 ≤ ρ ^ 2 := by
    rw [energyQ_fld]; exact pow_le_pow_left₀ (norm_nonneg _) ha' 2
  have hsq : ‖GN A F (r + 1) a - GN A F (r + 1) a'‖ ^ 2 ≤
      c0 * ((N : ℝ) + 1) ^ 2 * ‖a - a'‖ ^ 2 := by
    rw [norm_GN_sub_sq hA hF]
    set g : Fin n → ST d → ℝ := fun b x =>
      genG A F (fld (r + 1) a) b x - genG A F (fld (r + 1) a') b x with hg
    have hgs : ∀ b, ContDiff ℝ ∞ (g b) := fun b =>
      (contDiff_genG hA hF (fun b => contDiff_fld _ a b) b).sub
        (contDiff_genG hA hF (fun b => contDiff_fld _ a' b) b)
    have hgp : ∀ b, IsSPeriodic (g b) := fun b k x => by
      simp only [hg, isSPeriodic_genG (fun b => isSPeriodic_fld _ a b) b k x,
        isSPeriodic_genG (fun b => isSPeriodic_fld _ a' b) b k x]
    have hb : ∀ b, ∑ k ∈ box (d := d) N, wq (r + 1) k * coef (g b) 0 k ^ 2 ≤
        (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 * (C * ‖a - a'‖ ^ 2) := by
      intro b
      calc ∑ k ∈ box (d := d) N, wq (r + 1) k * coef (g b) 0 k ^ 2
          ≤ ∑ k ∈ box (d := d) N, (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 *
              (wq r k * coef (g b) 0 k ^ 2) := Finset.sum_le_sum fun k hk => by
            have h1 := (wq_succ_le_box hk r).trans (mul_le_mul_of_nonneg_right
              (one_add_le_succ_sq d N) (wq_nonneg r k))
            nlinarith [sq_nonneg (coef (g b) 0 k)]
        _ = (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 *
              ∑ k ∈ box (d := d) N, wq r k * coef (g b) 0 k ^ 2 := by rw [Finset.mul_sum]
        _ ≤ (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 * Q r (g b) 0 :=
            mul_le_mul_of_nonneg_left (bessel_Hq r (box N) (hgs b) (hgp b) 0) (by positivity)
        _ ≤ (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 * (C * ‖a - a'‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have := hC _ _ (fun b => contDiff_fld _ a b) (fun b => contDiff_fld _ a' b)
              (fun b => isSPeriodic_fld _ a b) (fun b => isSPeriodic_fld _ a' b) 0 hEa hEa' b
            rwa [← fld_sub, energyQ_fld] at this
    calc ∑ b, ∑ k ∈ box (d := d) N, wq (r + 1) k * coef (g b) 0 k ^ 2
        ≤ ∑ _b : Fin n, (1 + 4 * π ^ 2 * d) * ((N : ℝ) + 1) ^ 2 * (C * ‖a - a'‖ ^ 2) :=
          Finset.sum_le_sum fun b _ => hb b
      _ = c0 * ((N : ℝ) + 1) ^ 2 * ‖a - a'‖ ^ 2 := by simp [hc0]; ring
  have hrhs : 0 ≤ Real.sqrt c0 * ((N : ℝ) + 1) * ‖a - a'‖ := by positivity
  refine abs_le_of_sq_le_sq' ?_ hrhs |>.2
  calc ‖GN A F (r + 1) a - GN A F (r + 1) a'‖ ^ 2 ≤ c0 * ((N : ℝ) + 1) ^ 2 * ‖a - a'‖ ^ 2 := hsq
    _ = (Real.sqrt c0 * ((N : ℝ) + 1) * ‖a - a'‖) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hc00]

/-- The projected generator at the zero state is bounded independently of the cutoff:
`‖G_N(0)‖² ≤ Σ_b F_b(0)²`. -/
theorem norm_GN_zero_sq_le {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ}
    {F : Fin n → (Fin n → ℝ) → ℝ} (q N : ℕ) :
    ‖GN A F q (0 : GS d n N)‖ ^ 2 ≤ ∑ b, F b 0 ^ 2 := by
  have hG : ∀ b, genG A F (fld q (0 : GS d n N)) b = fun _ => F b 0 := by
    intro b; funext x
    simp only [genG, fld_zero, compF]
    have h0 : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
    have hpd : ∀ i : Fin d, pd (fun _ : ST d => (0 : ℝ)) i.succ x = 0 := fun i => by
      simp [SobolevOpen.pd]
    simp [hpd, h0]
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := bessel_Hq (d := d) q (box N) (g := fun _ => F b 0) contDiff_const (fun _ _ => rfl) 0
  rw [Q_const] at h
  refine le_trans (le_of_eq ?_) h
  rw [← Finset.sum_coe_sort (box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GN_apply, hG b, mul_pow, Real.sq_sqrt (wq_nonneg q k.1)]

/-- **The CFL bound of the projected generator**: `‖G_N(a)‖_{H^q} ≤ C_M (N + 1)` on the `H^q`
ball of radius `ρ`, for all cutoffs. -/
theorem GN_bound_cfl {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (N : ℕ) (a : GS d n N), ‖a‖ ≤ ρ →
      ‖GN A F q a‖ ≤ CM * ((N : ℝ) + 1) := by
  obtain ⟨CR, hCR0, hCR⟩ := GN_lip_cfl (d := d) (n := n) hm hq hA hF hρ
  set M0 := Real.sqrt (∑ b, F b 0 ^ 2) with hM0
  refine ⟨CR * ρ + M0, by positivity, fun N a ha => ?_⟩
  have h0 : ‖GN A F q (0 : GS d n N)‖ ≤ M0 :=
    Real.le_sqrt_of_sq_le (norm_GN_zero_sq_le q N)
  have h1 := hCR N a 0 ha (by simpa using hρ)
  rw [sub_zero] at h1
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  calc ‖GN A F q a‖ ≤ ‖GN A F q a - GN A F q 0‖ + ‖GN A F q (0 : GS d n N)‖ := by
        simpa using norm_le_norm_sub_add (GN A F q a) (GN A F q 0)
    _ ≤ CR * ((N : ℝ) + 1) * ρ + M0 := by
        refine add_le_add (h1.trans ?_) h0
        exact mul_le_mul_of_nonneg_left ha (by positivity)
    _ ≤ (CR * ρ + M0) * ((N : ℝ) + 1) := by
        have : M0 ≤ M0 * ((N : ℝ) + 1) := le_mul_of_one_le_right (Real.sqrt_nonneg _) hN
        nlinarith

/-- **The fully finite midpoint recursion under the explicit CFL condition**
(`eq:generated-midpoint`, `eq:generated-CFL`, `eq:generated-uniform`): for `m > d/2`, `q ≥ 2m`,
smooth real symmetric `A^i`, smooth `F` and every data radius `R₀` there are `T > 0`, `R`,
`c_* > 0`, `τ_* > 0` and `C_M` (depending only on `R₀` and `A, F, q, m, d, n`) such that for
**every** cutoff `N`, every step `τ > 0` with `τ(N + 1) ≤ c_*` and `τ ≤ τ_*`, and every finite
initial state `U_{0,N} ∈ Ran P_N` with `‖U_{0,N}‖_{H^q} ≤ R₀`, the implicit midpoint recursion
`U^{j+1} = U^j + τ G_N((U^j + U^{j+1})/2)` exists for all `jτ ≤ T`, each step being the unique
solution in the ball `‖V - U^j‖ ≤ τ C_M (N + 1)` (contraction), with the cutoff- and
step-independent bound `‖U^j‖_{H^q} ≤ R`. -/
theorem midpoint_uniform_cfl {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∃ CM ≥ 0, ∀ (N : ℕ) (τ : ℝ), 0 < τ →
      τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar → ∀ a₀ : GS d n N, ‖a₀‖ ≤ R₀ →
      ∃ U : ℕ → GS d n N, U 0 = a₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
        ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
          U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1))) ∧
          ‖U (j + 1) - U j‖ ≤ τ * (CM * ((N : ℝ) + 1)) ∧
          ∀ V, ‖V - U j‖ ≤ τ * (CM * ((N : ℝ) + 1)) →
            V = U j + τ • GN A F q (SpectralGalerkin.mid (U j) V) → V = U (j + 1)) := by
  set R := 2 * R₀ + 1 with hR
  have hRpos : 0 < R := by linarith
  obtain ⟨K, hK0, hK⟩ := inner_GN_le (d := d) (n := n) hm hq hA hsym hF (R := 2 * R)
    (by linarith)
  obtain ⟨CR, hCR0, hCR⟩ := GN_lip_cfl (d := d) (n := n) hm hq hA hF (ρ := 2 * R) (by linarith)
  obtain ⟨CM, hCM0, hCM⟩ := GN_bound_cfl (d := d) (n := n) hm hq hA hF (ρ := 2 * R)
    (by linarith)
  have hratio : 1 < (1 + R ^ 2) / (1 + R₀ ^ 2) := by
    rw [one_lt_div (by positivity)]; nlinarith
  set T := Real.log ((1 + R ^ 2) / (1 + R₀ ^ 2)) / (4 * K + 1) with hT
  have hTpos : 0 < T := div_pos (Real.log_pos hratio) (by linarith)
  set cstar := min (R / (CM + 1)) (1 / (CR + 1)) with hcstar
  have hcpos : 0 < cstar := lt_min (div_pos hRpos (by linarith)) (div_pos one_pos (by linarith))
  set τstar := 1 / (2 * K + 1) with hτstar
  have hτspos : 0 < τstar := div_pos one_pos (by linarith)
  refine ⟨T, hTpos, R, hRpos.le, cstar, hcpos, τstar, hτspos, CM, hCM0,
    fun N τ hτ hcfl hτs a₀ ha₀ => ?_⟩
  set M := CM * ((N : ℝ) + 1) with hMdef
  set L := CR * ((N : ℝ) + 1) with hLdef
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hτM : τ * M ≤ R := by
    have h1 : τ * ((N : ℝ) + 1) ≤ R / (CM + 1) := hcfl.trans (min_le_left _ _)
    have h2 : τ * M = CM * (τ * ((N : ℝ) + 1)) := by rw [hMdef]; ring
    rw [h2]
    calc CM * (τ * ((N : ℝ) + 1)) ≤ CM * (R / (CM + 1)) := mul_le_mul_of_nonneg_left h1 hCM0
      _ ≤ (CM + 1) * (R / (CM + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = R := mul_div_cancel₀ _ (by linarith)
  have hτL : τ * L < 2 := by
    have h1 : τ * ((N : ℝ) + 1) ≤ 1 / (CR + 1) := hcfl.trans (min_le_right _ _)
    have h2 : τ * L = CR * (τ * ((N : ℝ) + 1)) := by rw [hLdef]; ring
    rw [h2]
    calc CR * (τ * ((N : ℝ) + 1)) ≤ CR * (1 / (CR + 1)) := mul_le_mul_of_nonneg_left h1 hCR0
      _ < 2 := by rw [mul_one_div, div_lt_iff₀ (by linarith)]; linarith
  have hτK : τ * K ≤ 1 / 2 := by
    rw [hτstar, le_div_iff₀ (by linarith)] at hτs; nlinarith
  have h0 : Real.exp (4 * K * T) * (1 + ‖a₀‖ ^ 2) ≤ 1 + R ^ 2 := by
    have h1 : Real.exp (4 * K * T) ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) := by
      calc Real.exp (4 * K * T) ≤ Real.exp ((4 * K + 1) * T) :=
            Real.exp_le_exp.2 (by nlinarith)
        _ = (1 + R ^ 2) / (1 + R₀ ^ 2) := by
            rw [hT, mul_div_cancel₀ _ (by linarith : (4 * K + 1) ≠ 0),
              Real.exp_log (by positivity)]
    have ha2 : ‖a₀‖ ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha₀ 2
    calc Real.exp (4 * K * T) * (1 + ‖a₀‖ ^ 2)
        ≤ (1 + R ^ 2) / (1 + R₀ ^ 2) * (1 + R₀ ^ 2) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 1 + R ^ 2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨U, hU0, hUj⟩ := SpectralGalerkin.midpoint_recursion hτ.le hM0 hL0 hK0 hRpos.le
    (fun w hw => hCM N w hw) (fun w w' hw hw' => hCR N w w' hw hw') (fun w hw => hK N w hw)
    hτM hτL hτK h0
  exact ⟨U, hU0, fun j hj => ⟨(hUj j hj).1, fun hj1 => (hUj j hj).2.2 hj1⟩⟩

/-- The CFL midpoint scheme started from the Fourier truncation `P_N U₀` of a smooth periodic
datum with `‖U₀‖_{H^q} ≤ R₀` (Bessel: `‖P_N U₀‖ ≤ ‖U₀‖_{H^q}`). -/
theorem midpoint_uniform_cfl_P0 {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hq : 2 * m ≤ q)
    {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ T > 0, ∃ R ≥ 0, ∃ cstar > 0, ∃ τstar > 0, ∀ (N : ℕ) (τ : ℝ), 0 < τ →
      τ * ((N : ℝ) + 1) ≤ cstar → τ ≤ τstar → ∀ U₀ : Fin n → ST d → ℝ,
      (∀ b, ContDiff ℝ ∞ (U₀ b)) → (∀ b, IsSPeriodic (U₀ b)) → energyQ q U₀ 0 ≤ R₀ ^ 2 →
      ∃ U : ℕ → GS d n N, U 0 = P0 q N U₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
        ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
          U (j + 1) = U j + τ • GN A F q (SpectralGalerkin.mid (U j) (U (j + 1)))) := by
  obtain ⟨T, hT, R, hR, cstar, hc, τstar, hτs, CM, -, h⟩ :=
    midpoint_uniform_cfl (d := d) (n := n) hm hq hA hsym hF hR₀
  refine ⟨T, hT, R, hR, cstar, hc, τstar, hτs, fun N τ hτ hcfl hτ' U₀ hU hUp hE => ?_⟩
  have hP0 : ‖P0 (d := d) q N U₀‖ ≤ R₀ := by
    have h1 := (norm_P0_sq_le q N hU hUp).trans hE
    exact abs_le_of_sq_le_sq' h1 hR₀ |>.2
  obtain ⟨U, hU0, hUj⟩ := h N τ hτ hcfl hτ' _ hP0
  exact ⟨U, hU0, fun j hj => ⟨(hUj j hj).1, fun hj1 => ((hUj j hj).2 hj1).1⟩⟩

end CFL

/-! ### Non-vacuity -/

/-- **Non-vacuity of `midpoint_uniform_cfl_P0`**: for the symmetric hyperbolic system
`∂_tU + σ₁∂_1U = -U` on `𝕋³` (`m = 2`, `q = 4`) the CFL midpoint recursion from the zero datum
exists for every cutoff and every admissible step. -/
example : ∃ cstar > 0, ∃ τstar > 0, ∀ (N : ℕ) (τ : ℝ), 0 < τ → τ * ((N : ℝ) + 1) ≤ cstar →
    τ ≤ τstar → ∃ U : ℕ → KatoGalerkin.GS 3 2 N, U 0 = KatoGalerkin.P0 4 N (fun _ _ => 0) := by
  obtain ⟨T, -, R, -, cstar, hc, τstar, hτs, h⟩ := midpoint_uniform_cfl_P0 (d := 3) (n := 2)
    (m := 2) (q := 4) (by norm_num) le_rfl (A := KatoGalerkin.exampleA) (F := fun a v => -v a)
    (fun _ _ _ => by unfold KatoGalerkin.exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold KatoGalerkin.exampleA
      by_cases h : a = b
      · subst h; rfl
      · simp [h, Ne.symm h])
    (fun a => (contDiff_apply ℝ ℝ a).neg) zero_le_one
  refine ⟨cstar, hc, τstar, hτs, fun N τ hτ hcfl hτ' => ?_⟩
  obtain ⟨U, hU0, -⟩ := h N τ hτ hcfl hτ' (fun _ _ => 0) (fun _ => contDiff_const)
    (fun _ _ _ => rfl) (by rw [KatoGalerkin.energyQ_zero]; norm_num)
  exact ⟨U, hU0⟩

end RenewalGeometry.KatoCFL
