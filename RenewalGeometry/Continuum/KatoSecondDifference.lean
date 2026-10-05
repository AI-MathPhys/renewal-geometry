/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.KatoGalerkinCausal

/-!
# Second differences of the quasilinear generator and the derivative of the projected generator

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript (`eq:generated-Galerkin-rate` with `a = 2`,
`eq:generated-time-rate`, `eq:generated-Hermite`).  Setting of `KatoGalerkinODE`:
`∂_tU + Σ_i A^i(U)∂_iU = F(U)` on `𝕋^d` (`ℤ^d`-periodic fields on slices), smooth `A^i`, `F`,
generator `G(U) = F(U) - Σ_i A^i(U)∂_iU` (`QLEnergy.genG`), Sobolev norms `Q_r` on slices.

* `Q_compF_sub_le` — **Lipschitz composition estimate** in `H^r` (`2m ≤ r + 1`, `m > d/2`):
  `‖Φ(U) - Φ(V)‖²_{H^r} ≤ K ‖U - V‖²_{H^r}` on the `H^r` ball (Hadamard + Moser + algebra).
* `Q_mul_sub_mul_le` — the product rule for differences in the `H^r` algebra.
* **`Q_genG_second_diff_le`** — **the mixed second-difference estimate of the generator**
  (`H^{r+1} → H^r`, one derivative lost):
  `‖G(u₁) - G(u₀) - G(v₁) + G(v₀)‖²_{H^r} ≤ C (‖(u₁ - u₀) - (v₁ - v₀)‖²_{H^{r+1}}
     + ‖v₁ - v₀‖²_{H^{r+1}} (‖u₀ - v₀‖²_{H^{r+1}} + ‖u₁ - v₁‖²_{H^{r+1}}))`
  on the `H^{r+1}` ball (the second-order analogue of `KatoCFL.Q_genG_sub_le`; it contains the
  symmetric second difference `G(a + b) + G(a - b) - 2G(a) = O(‖b‖²_{H^{r+1}})`).
* On the Galerkin space (`GS d n N`, Euclidean norm = `H^q` norm, `H^ρ` coordinates
  `KatoCausal.hmS ρ q`): `norm_hmS_GN_comb_sq_le` (Bessel for combinations of projected
  generators), `GN_lip_hm` (`‖G_N a - G_N b‖_{H^ρ} ≤ C ‖a - b‖_{H^{ρ+1}}`, cutoff-uniform),
  and for the derivative `DG_N(a) = fderiv G_N a`:
  **`DGN_bound`** (`‖DG_N(a)w‖_{H^ρ} ≤ C ‖w‖_{H^{ρ+1}}`) and **`DGN_lip`**
  (`‖DG_N(a)w - DG_N(b)w‖_{H^ρ} ≤ C ‖a - b‖_{H^{ρ+1}} ‖w‖_{H^{ρ+1}}`), with constants independent
  of the cutoff `N` (limits of difference quotients of the Lipschitz and second-difference
  estimates).

Disclosed rendering: `Σ = 𝕋^d`; smooth coefficients on all of `ℝ^n` (a chart is handled by a smooth
cutoff extension, as in `ActualJetKato.actual_jet_kato_realization`).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.KatoSecond

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoCFL

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Lipschitz composition and products of differences -/

/-- **Lipschitz composition estimate in `H^r`** (finite families, uniform constant): for
`m > d/2`, `2m ≤ r + 1` and smooth `Φ_k : ℝ^p → ℝ`, on the `H^r` ball of radius `R`,
`Q_r(Φ_k(U) - Φ_k(V)) ≤ K ‖U - V‖²_{H^r}`. -/
theorem Q_compF_sub_le {m r p : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    {κ : Type*} [Fintype κ] {Φ : κ → (Fin p → ℝ) → ℝ} (hΦ : ∀ k, ContDiff ℝ ∞ (Φ k)) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, ∀ u v : Fin p → ST d → ℝ, (∀ b, ContDiff ℝ ∞ (u b)) →
      (∀ b, ContDiff ℝ ∞ (v b)) → (∀ b, IsSPeriodic (u b)) → (∀ b, IsSPeriodic (v b)) →
      ∀ t, energyQ r u t ≤ R ^ 2 → energyQ r v t ≤ R ^ 2 →
      Q r (fun x => compF (Φ k) u x - compF (Φ k) v x) t ≤
        K * energyQ r (fun b x => u b x - v b x) t := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hR2 : 0 ≤ Real.sqrt 2 * R := by positivity
  obtain ⟨K1, hK10, hK1⟩ := Q_compF_family_le (d := d) (p := p + p) hm hr
    (Φ := fun kc : κ × Fin p => onPair (hadQ (Φ kc.1) kc.2))
    (fun kc => contDiff_onPair (contDiff_hadQ (hΦ kc.1) kc.2)) hR2
  have hc0 : 0 ≤ algC d r CS := algC_nonneg r hCS
  refine ⟨p * (algC d r CS * K1), by positivity, fun k u v hu hv hup hvp t hEu hEv => ?_⟩
  have hEpair : energyQ r (pairF u v) t ≤ (Real.sqrt 2 * R) ^ 2 := by
    rw [energyQ_pairF, mul_pow, Real.sq_sqrt (by norm_num)]; linarith
  have hws := contDiff_pairF hu hv
  have hwp := isSPeriodic_pairF hup hvp
  have heq : (fun x => compF (Φ k) u x - compF (Φ k) v x) = fun x =>
      ∑ c, (u c x - v c x) * compF (onPair (hadQ (Φ k) c)) (pairF u v) x := by
    funext x
    simp only [compF_onPair]
    exact hadamard (hΦ k) _ _
  rw [heq]
  have hDs : ∀ c, ContDiff ℝ ∞ (fun x => u c x - v c x) := fun c => (hu c).sub (hv c)
  have hDp : ∀ c, IsSPeriodic (fun x => u c x - v c x) := fun c j x => by
    simp only [hup c j x, hvp c j x]
  have sΨ : ∀ c, ContDiff ℝ ∞ (compF (onPair (hadQ (Φ k) c)) (pairF u v)) := fun c =>
    contDiff_compF (contDiff_onPair (contDiff_hadQ (hΦ k) c)) hws
  have pΨ : ∀ c, IsSPeriodic (compF (onPair (hadQ (Φ k) c)) (pairF u v)) := fun c =>
    isSPeriodic_compF _ hwp
  refine (Q_sum_le r Finset.univ (fun c => (hDs c).mul (sΨ c)) t).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ c, Q r (fun x => (u c x - v c x) * compF (onPair (hadQ (Φ k) c)) (pairF u v) x) t
      ≤ algC d r CS * K1 * Q r (fun x => u c x - v c x) t := fun c => by
    refine (Q_mul_le hr hCS hsup (hDs c) (sΨ c) (hDp c) (pΨ c) t).trans ?_
    have h1 : Q r (compF (onPair (hadQ (Φ k) c)) (pairF u v)) t ≤ K1 := hK1 (k, c) _ hws hwp t hEpair
    have h2 := Q_nonneg r (fun x => u c x - v c x) t
    calc algC d r CS * Q r (fun x => u c x - v c x) t *
          Q r (compF (onPair (hadQ (Φ k) c)) (pairF u v)) t
        ≤ algC d r CS * Q r (fun x => u c x - v c x) t * K1 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hc0 h2)
      _ = _ := by ring
  calc (p : ℝ) * ∑ c, Q r (fun x => (u c x - v c x) *
        compF (onPair (hadQ (Φ k) c)) (pairF u v) x) t
      ≤ p * ∑ c, algC d r CS * K1 * Q r (fun x => u c x - v c x) t :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hterm c) (Nat.cast_nonneg _)
    _ = p * (algC d r CS * K1) * energyQ r (fun b x => u b x - v b x) t := by
        rw [← Finset.mul_sum]; unfold energyQ; ring

/-- **Product rule for differences in the `H^r` algebra**:
`Q_r(fg - f'g') ≤ 2 c_r (Q_r(f) Q_r(g - g') + Q_r(f - f') Q_r(g'))`, in bound form. -/
theorem Q_mul_sub_mul_le {r m : ℕ} (hr : 2 * m ≤ r + 1) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : ST d → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin d → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q m f t)
    {f g f' g' : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hf' : ContDiff ℝ ∞ f')
    (hg' : ContDiff ℝ ∞ g') (pf : IsSPeriodic f) (pg : IsSPeriodic g) (pf' : IsSPeriodic f')
    (pg' : IsSPeriodic g') (t : ℝ) {Kf Kg Df Dg : ℝ} (hKf : Q r f t ≤ Kf)
    (hDg : Q r (fun x => g x - g' x) t ≤ Dg) (hDf : Q r (fun x => f x - f' x) t ≤ Df)
    (hKg : Q r g' t ≤ Kg) :
    Q r (fun x => f x * g x - f' x * g' x) t ≤ 2 * algC d r CS * (Kf * Dg + Df * Kg) := by
  have hc0 : 0 ≤ algC d r CS := algC_nonneg r hCS
  have e : (fun x => f x * g x - f' x * g' x) =
      fun x => f x * (g x - g' x) + (f x - f' x) * g' x := by funext x; ring
  rw [e]
  have sdg : ContDiff ℝ ∞ (fun x => g x - g' x) := hg.sub hg'
  have sdf : ContDiff ℝ ∞ (fun x => f x - f' x) := hf.sub hf'
  have pdg : IsSPeriodic (fun x => g x - g' x) := fun j x => by simp only [pg j x, pg' j x]
  have pdf : IsSPeriodic (fun x => f x - f' x) := fun j x => by simp only [pf j x, pf' j x]
  refine (Q_add_le r (hf.mul sdg) (sdf.mul hg') t).trans ?_
  have h1 := Q_mul_le hr hCS hsup hf sdg pf pdg t
  have h2 := Q_mul_le hr hCS hsup sdf hg' pdf pg' t
  have q1 := Q_nonneg r f t
  have q2 := Q_nonneg r (fun x => g x - g' x) t
  have q3 := Q_nonneg r (fun x => f x - f' x) t
  have q4 := Q_nonneg r g' t
  have k1 : algC d r CS * Q r f t * Q r (fun x => g x - g' x) t ≤ algC d r CS * Kf * Dg :=
    mul_le_mul (mul_le_mul_of_nonneg_left hKf hc0) hDg q2 (mul_nonneg hc0 (q1.trans hKf))
  have k2 : algC d r CS * Q r (fun x => f x - f' x) t * Q r g' t ≤ algC d r CS * Df * Kg :=
    mul_le_mul (mul_le_mul_of_nonneg_left hDf hc0) hKg q4 (mul_nonneg hc0 (q3.trans hDf))
  nlinarith

/-! ### Energies of pairs and differences -/

theorem energyQ_le_succ (r : ℕ) (u : Fin n → ST d → ℝ) (t : ℝ) :
    energyQ r u t ≤ energyQ (r + 1) u t :=
  Finset.sum_le_sum fun _ _ => Q_mono (Nat.le_succ r) _ _

theorem energyQ_pairF_sub (k : ℕ) (u₁ u₀ v₁ v₀ : Fin n → ST d → ℝ) (t : ℝ) :
    energyQ k (fun b x => pairF u₁ u₀ b x - pairF v₁ v₀ b x) t =
      energyQ k (fun b x => u₁ b x - v₁ b x) t + energyQ k (fun b x => u₀ b x - v₀ b x) t := by
  simp only [energyQ, pairF, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem aux_T1 (K Ed Ev E0 E1 : ℝ) : K * Ed + K * (E0 + E1) * Ev ≤ K * (Ed + Ev * (E0 + E1)) :=
  le_of_eq (by ring)

theorem aux_T2 {K Ed Ev E0 E1 : ℝ} (hK0 : 0 ≤ K) (hEv0 : 0 ≤ Ev) (hE00 : 0 ≤ E0) :
    K * Ed + K * E1 * Ev ≤ K * (Ed + Ev * (E0 + E1)) := by
  nlinarith [mul_nonneg (mul_nonneg hK0 hEv0) hE00]

theorem aux_T3 {c K Ed Ev E0 E1 : ℝ} (hc0 : 0 ≤ c) (hK0 : 0 ≤ K) (hEd0 : 0 ≤ Ed) (hEv0 : 0 ≤ Ev)
    (hE00 : 0 ≤ E0) (hE10 : 0 ≤ E1) :
    c * K * K * Ed + 2 * c * (K * E0 + K * (E0 + E1) * K) * Ev ≤
      (c * K * K + 2 * c * (K + K * K)) * (Ed + Ev * (E0 + E1)) := by
  have h1 : 0 ≤ c * K * K * (Ev * (E0 + E1)) := by positivity
  have h2 : 0 ≤ 2 * c * (K + K * K) * Ed := by positivity
  have h3 : 0 ≤ 2 * c * K * E1 * Ev := by positivity
  nlinarith

/-! ### The mixed second difference of the generator -/

section Second

open KatoCausal (dif psiF psiA contDiff_dif isSPeriodic_dif contDiff_psiF contDiff_psiA)

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The pointwise decomposition of the mixed second difference of the generator. -/
theorem genG_second_diff_eq (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    {u₀ u₁ v₀ v₁ : Fin n → ST d → ℝ} (hu₀ : ∀ b, ContDiff ℝ ∞ (u₀ b))
    (hu₁ : ∀ b, ContDiff ℝ ∞ (u₁ b)) (hv₀ : ∀ b, ContDiff ℝ ∞ (v₀ b))
    (hv₁ : ∀ b, ContDiff ℝ ∞ (v₁ b)) (a : Fin n) (x : ST d) :
    genG A F u₁ a x - genG A F u₀ a x - (genG A F v₁ a x - genG A F v₀ a x) =
      (∑ c, (dif u₁ u₀ c x * psiF F u₁ u₀ a c x - dif v₁ v₀ c x * psiF F v₁ v₀ a c x)) -
        ∑ i, ∑ b, ((compF (A i a b) u₁ x * pd (dif u₁ u₀ b) i.succ x -
            compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) +
          ∑ c, (dif u₁ u₀ c x * (psiA A u₁ u₀ i a b c x * pd (u₀ b) i.succ x) -
            dif v₁ v₀ c x * (psiA A v₁ v₀ i a b c x * pd (v₀ b) i.succ x))) := by
  rw [genG_sub_eq hA hF hu₁ hu₀ a x, genG_sub_eq hA hF hv₁ hv₀ a x]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

set_option maxHeartbeats 1600000 in
/-- **The mixed second-difference estimate of the generator** (`H^{r+1} → H^r`): for `m > d/2`,
`2m ≤ r + 1`, smooth `A^i`, `F` and every radius `ρ` there is `C` such that for smooth periodic
`u₀, u₁, v₀, v₁` in the `H^{r+1}` ball of radius `ρ`,
`Q_r(G(u₁) - G(u₀) - G(v₁) + G(v₀)) ≤ C (‖(u₁ - u₀) - (v₁ - v₀)‖²_{H^{r+1}}
  + ‖v₁ - v₀‖²_{H^{r+1}} (‖u₀ - v₀‖²_{H^{r+1}} + ‖u₁ - v₁‖²_{H^{r+1}}))`. -/
theorem Q_genG_second_diff_le {m r : ℕ} (hm : (d : ℝ) / 2 < m) (hr : 2 * m ≤ r + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₁ v₀ v₁ : Fin n → ST d → ℝ,
      (∀ b, ContDiff ℝ ∞ (u₀ b)) → (∀ b, ContDiff ℝ ∞ (u₁ b)) → (∀ b, ContDiff ℝ ∞ (v₀ b)) →
      (∀ b, ContDiff ℝ ∞ (v₁ b)) → (∀ b, IsSPeriodic (u₀ b)) → (∀ b, IsSPeriodic (u₁ b)) →
      (∀ b, IsSPeriodic (v₀ b)) → (∀ b, IsSPeriodic (v₁ b)) → ∀ t,
      energyQ (r + 1) u₀ t ≤ ρ ^ 2 → energyQ (r + 1) u₁ t ≤ ρ ^ 2 →
      energyQ (r + 1) v₀ t ≤ ρ ^ 2 → energyQ (r + 1) v₁ t ≤ ρ ^ 2 → ∀ a,
      Q r (fun x => genG A F u₁ a x - genG A F u₀ a x - (genG A F v₁ a x - genG A F v₀ a x)) t ≤
        C * (energyQ (r + 1) (fun b x => u₁ b x - u₀ b x - (v₁ b x - v₀ b x)) t +
          energyQ (r + 1) (fun b x => v₁ b x - v₀ b x) t *
            (energyQ (r + 1) (fun b x => u₀ b x - v₀ b x) t +
              energyQ (r + 1) (fun b x => u₁ b x - v₁ b x) t)) := by
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  set c := algC d r CS with hc
  have hc0 : 0 ≤ c := algC_nonneg r hCS
  have hρ2 : 0 ≤ Real.sqrt 2 * ρ := by positivity
  obtain ⟨KF, hKF0, hKF⟩ := Q_compF_family_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin n × Fin n => onPair (hadQ (F k.1) k.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hF k.1) k.2)) hρ2
  obtain ⟨KA, hKA0, hKA⟩ := Q_compF_family_le (d := d) (p := n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n => A k.1 k.2.1 k.2.2) (fun k => hA _ _ _) hρ
  obtain ⟨KΨ, hKΨ0, hKΨ⟩ := Q_compF_family_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n × Fin n => onPair (hadQ (A k.1 k.2.1 k.2.2.1) k.2.2.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hA _ _ _) _)) hρ2
  obtain ⟨LF, hLF0, hLF⟩ := Q_compF_sub_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin n × Fin n => onPair (hadQ (F k.1) k.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hF k.1) k.2)) hρ2
  obtain ⟨LA, hLA0, hLA⟩ := Q_compF_sub_le (d := d) (p := n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n => A k.1 k.2.1 k.2.2) (fun k => hA _ _ _) hρ
  obtain ⟨LΨ, hLΨ0, hLΨ⟩ := Q_compF_sub_le (d := d) (p := n + n) hm hr
    (Φ := fun k : Fin d × Fin n × Fin n × Fin n => onPair (hadQ (A k.1 k.2.1 k.2.2.1) k.2.2.2))
    (fun k => contDiff_onPair (contDiff_hadQ (hA _ _ _) _)) hρ2
  set K := KF + KA + KΨ + LF + LA + LΨ + ρ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKF1 : KF ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hKA1 : KA ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hKΨ1 : KΨ ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hLF1 : LF ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hLA1 : LA ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hLΨ1 : LΨ ≤ K := by
    rw [hK]; linarith [sq_nonneg ρ, hKF0, hKA0, hKΨ0, hLF0, hLA0, hLΨ0]
  have hρK : ρ ^ 2 ≤ K := by rw [hK]; linarith
  set P := 2 * c * K + 2 * c * (c * K * K + 2 * c * (K + K * K)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hP1 : 2 * c * K ≤ P := by
    rw [hP]; have : 0 ≤ 2 * c * (c * K * K + 2 * c * (K + K * K)) := by positivity
    linarith
  have hP2 : 2 * c * (c * K * K + 2 * c * (K + K * K)) ≤ P := by
    rw [hP]; have : 0 ≤ 2 * c * K := by positivity
    linarith
  set C := 2 * (n * (n * P)) + 2 * (d * (d * (n * (n * (2 * P + 2 * (n * (n * P))))))) with hCdef
  refine ⟨C, by positivity, fun u₀ u₁ v₀ v₁ hu₀ hu₁ hv₀ hv₁ pu₀ pu₁ pv₀ pv₁ t h0 h1 h2 h3 a => ?_⟩
  -- the energies
  set Ed := energyQ (r + 1) (fun b x => u₁ b x - u₀ b x - (v₁ b x - v₀ b x)) t with hEd
  set Ev := energyQ (r + 1) (fun b x => v₁ b x - v₀ b x) t with hEv
  set E0 := energyQ (r + 1) (fun b x => u₀ b x - v₀ b x) t with hE0
  set E1 := energyQ (r + 1) (fun b x => u₁ b x - v₁ b x) t with hE1
  have hEd0 : 0 ≤ Ed := energyQ_nonneg _ _ _
  have hEv0 : 0 ≤ Ev := energyQ_nonneg _ _ _
  have hE00 : 0 ≤ E0 := energyQ_nonneg _ _ _
  have hE10 : 0 ≤ E1 := energyQ_nonneg _ _ _
  set S := Ed + Ev * (E0 + E1) with hS
  have hS0 : 0 ≤ S := add_nonneg hEd0 (mul_nonneg hEv0 (add_nonneg hE00 hE10))
  have hEdS : Ed ≤ S := le_add_of_nonneg_right (mul_nonneg hEv0 (add_nonneg hE00 hE10))
  have hEvS : Ev * (E0 + E1) ≤ S := le_add_of_nonneg_left hEd0
  -- smoothness and periodicity of the pieces
  have sdu := contDiff_dif hu₁ hu₀
  have sdv := contDiff_dif hv₁ hv₀
  have pdu := isSPeriodic_dif pu₁ pu₀
  have pdv := isSPeriodic_dif pv₁ pv₀
  have sFu := contDiff_psiF hF hu₁ hu₀
  have sFv := contDiff_psiF hF hv₁ hv₀
  have sAu := contDiff_psiA hA hu₁ hu₀
  have sAv := contDiff_psiA hA hv₁ hv₀
  have pFu : ∀ a c', IsSPeriodic (psiF F u₁ u₀ a c') := fun a c' =>
    isSPeriodic_compF _ (isSPeriodic_pairF pu₁ pu₀)
  have pFv : ∀ a c', IsSPeriodic (psiF F v₁ v₀ a c') := fun a c' =>
    isSPeriodic_compF _ (isSPeriodic_pairF pv₁ pv₀)
  have pAu : ∀ i a b c', IsSPeriodic (psiA A u₁ u₀ i a b c') := fun i a b c' =>
    isSPeriodic_compF _ (isSPeriodic_pairF pu₁ pu₀)
  have pAv : ∀ i a b c', IsSPeriodic (psiA A v₁ v₀ i a b c') := fun i a b c' =>
    isSPeriodic_compF _ (isSPeriodic_pairF pv₁ pv₀)
  have sCu : ∀ i b, ContDiff ℝ ∞ (compF (A i a b) u₁) := fun i b => contDiff_compF (hA i a b) hu₁
  have sCv : ∀ i b, ContDiff ℝ ∞ (compF (A i a b) v₁) := fun i b => contDiff_compF (hA i a b) hv₁
  have pCu : ∀ i b, IsSPeriodic (compF (A i a b) u₁) := fun i b => isSPeriodic_compF _ pu₁
  have pCv : ∀ i b, IsSPeriodic (compF (A i a b) v₁) := fun i b => isSPeriodic_compF _ pv₁
  -- energy bounds at level `r`
  have hlev : ∀ w : Fin n → ST d → ℝ, energyQ (r + 1) w t ≤ ρ ^ 2 → energyQ r w t ≤ ρ ^ 2 :=
    fun w hw => (energyQ_le_succ r w t).trans hw
  have hpairE : ∀ w w' : Fin n → ST d → ℝ, energyQ (r + 1) w t ≤ ρ ^ 2 →
      energyQ (r + 1) w' t ≤ ρ ^ 2 → energyQ r (pairF w w') t ≤ (Real.sqrt 2 * ρ) ^ 2 := by
    intro w w' hw hw'
    rw [energyQ_pairF, mul_pow, Real.sq_sqrt (by norm_num)]
    have := hlev w hw; have := hlev w' hw'; linarith
  have hpairD : energyQ r (fun b x => pairF u₁ u₀ b x - pairF v₁ v₀ b x) t ≤ E0 + E1 := by
    rw [energyQ_pairF_sub]
    have := energyQ_le_succ r (fun b x => u₁ b x - v₁ b x) t
    have := energyQ_le_succ r (fun b x => u₀ b x - v₀ b x) t
    linarith
  -- component bounds
  have qd : ∀ b, Q r (fun x => dif u₁ u₀ b x - dif v₁ v₀ b x) t ≤ Ed := fun b =>
    (Q_mono (Nat.le_succ r) _ _).trans
      (KatoGalerkin.Q_le_energyQ (r + 1) (fun b x => u₁ b x - u₀ b x - (v₁ b x - v₀ b x)) t b)
  have qv : ∀ b, Q r (dif v₁ v₀ b) t ≤ Ev := fun b =>
    (Q_mono (Nat.le_succ r) _ _).trans
      (KatoGalerkin.Q_le_energyQ (r + 1) (fun b x => v₁ b x - v₀ b x) t b)
  have qpd : ∀ (i : Fin d) b, Q r (fun x => pd (dif u₁ u₀ b) i.succ x -
      pd (dif v₁ v₀ b) i.succ x) t ≤ Ed := fun i b => by
    have e : (fun x => pd (dif u₁ u₀ b) i.succ x - pd (dif v₁ v₀ b) i.succ x) =
        pd (fun x => dif u₁ u₀ b x - dif v₁ v₀ b x) i.succ := by
      funext x; rw [KatoGalerkin.pd_sub_real (sdu b) (sdv b)]
    rw [e]
    exact (Q_pd_le i _ t).trans
      (KatoGalerkin.Q_le_energyQ (r + 1) (fun b x => u₁ b x - u₀ b x - (v₁ b x - v₀ b x)) t b)
  have qpdv : ∀ (i : Fin d) b, Q r (pd (dif v₁ v₀ b) i.succ) t ≤ Ev := fun i b =>
    (Q_pd_le i _ t).trans (KatoGalerkin.Q_le_energyQ (r + 1) (fun b x => v₁ b x - v₀ b x) t b)
  have qpd0 : ∀ (i : Fin d) b, Q r (fun x => pd (u₀ b) i.succ x - pd (v₀ b) i.succ x) t ≤ E0 :=
    fun i b => by
      have e : (fun x => pd (u₀ b) i.succ x - pd (v₀ b) i.succ x) =
          pd (fun x => u₀ b x - v₀ b x) i.succ := by
        funext x; rw [KatoGalerkin.pd_sub_real (hu₀ b) (hv₀ b)]
      rw [e]
      exact (Q_pd_le i _ t).trans
        (KatoGalerkin.Q_le_energyQ (r + 1) (fun b x => u₀ b x - v₀ b x) t b)
  have qpv0 : ∀ (i : Fin d) b, Q r (pd (v₀ b) i.succ) t ≤ K := fun i b =>
    (Q_pd_le i _ t).trans ((KatoGalerkin.Q_le_energyQ (r + 1) v₀ t b).trans (h2.trans hρK))
  have qpu0 : ∀ (i : Fin d) b, Q r (pd (u₀ b) i.succ) t ≤ K := fun i b =>
    (Q_pd_le i _ t).trans ((KatoGalerkin.Q_le_energyQ (r + 1) u₀ t b).trans (h0.trans hρK))
  have qFu : ∀ c', Q r (psiF F u₁ u₀ a c') t ≤ K := fun c' =>
    (hKF (a, c') _ (contDiff_pairF hu₁ hu₀) (isSPeriodic_pairF pu₁ pu₀) t
      (hpairE u₁ u₀ h1 h0)).trans hKF1
  have qFv : ∀ c', Q r (psiF F v₁ v₀ a c') t ≤ K := fun c' =>
    (hKF (a, c') _ (contDiff_pairF hv₁ hv₀) (isSPeriodic_pairF pv₁ pv₀) t
      (hpairE v₁ v₀ h3 h2)).trans hKF1
  have qFd : ∀ c', Q r (fun x => psiF F u₁ u₀ a c' x - psiF F v₁ v₀ a c' x) t ≤ K * (E0 + E1) :=
    fun c' => (hLF (a, c') _ _ (contDiff_pairF hu₁ hu₀) (contDiff_pairF hv₁ hv₀)
      (isSPeriodic_pairF pu₁ pu₀) (isSPeriodic_pairF pv₁ pv₀) t (hpairE u₁ u₀ h1 h0)
      (hpairE v₁ v₀ h3 h2)).trans (mul_le_mul hLF1 hpairD (energyQ_nonneg _ _ _) hK0)
  have qCu : ∀ (i : Fin d) b, Q r (compF (A i a b) u₁) t ≤ K := fun i b =>
    (hKA (i, a, b) u₁ hu₁ pu₁ t (hlev u₁ h1)).trans hKA1
  have qCd : ∀ (i : Fin d) b, Q r (fun x => compF (A i a b) u₁ x - compF (A i a b) v₁ x) t ≤
      K * E1 := fun i b =>
    (hLA (i, a, b) u₁ v₁ hu₁ hv₁ pu₁ pv₁ t (hlev u₁ h1) (hlev v₁ h3)).trans
      (mul_le_mul hLA1 (energyQ_le_succ r _ t) (energyQ_nonneg _ _ _) hK0)
  have qAu : ∀ (i : Fin d) b c', Q r (psiA A u₁ u₀ i a b c') t ≤ K := fun i b c' =>
    (hKΨ (i, a, b, c') _ (contDiff_pairF hu₁ hu₀) (isSPeriodic_pairF pu₁ pu₀) t
      (hpairE u₁ u₀ h1 h0)).trans hKΨ1
  have qAd : ∀ (i : Fin d) b c', Q r (fun x => psiA A u₁ u₀ i a b c' x -
      psiA A v₁ v₀ i a b c' x) t ≤ K * (E0 + E1) := fun i b c' =>
    (hLΨ (i, a, b, c') _ _ (contDiff_pairF hu₁ hu₀) (contDiff_pairF hv₁ hv₀)
      (isSPeriodic_pairF pu₁ pu₀) (isSPeriodic_pairF pv₁ pv₀) t (hpairE u₁ u₀ h1 h0)
      (hpairE v₁ v₀ h3 h2)).trans (mul_le_mul hLΨ1 hpairD (energyQ_nonneg _ _ _) hK0)
  -- the three kinds of terms
  have T1 : ∀ c', Q r (fun x => dif u₁ u₀ c' x * psiF F u₁ u₀ a c' x -
      dif v₁ v₀ c' x * psiF F v₁ v₀ a c' x) t ≤ P * S := fun c' => by
    have e : (fun x => dif u₁ u₀ c' x * psiF F u₁ u₀ a c' x -
        dif v₁ v₀ c' x * psiF F v₁ v₀ a c' x) = fun x => psiF F u₁ u₀ a c' x * dif u₁ u₀ c' x -
        psiF F v₁ v₀ a c' x * dif v₁ v₀ c' x := by funext x; ring
    rw [e]
    refine (Q_mul_sub_mul_le hr hCS hsup (sFu a c') (sdu c') (sFv a c') (sdv c') (pFu a c')
      (pdu c') (pFv a c') (pdv c') t (qFu c') (qd c') (qFd c') (qv c')).trans ?_
    have k1 : K * Ed + K * (E0 + E1) * Ev ≤ K * S := aux_T1 K Ed Ev E0 E1
    calc 2 * c * (K * Ed + K * (E0 + E1) * Ev) ≤ 2 * c * (K * S) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg zero_le_two hc0)
      _ = 2 * c * K * S := by ring
      _ ≤ P * S := mul_le_mul_of_nonneg_right hP1 hS0
  have T2 : ∀ (i : Fin d) b, Q r (fun x => compF (A i a b) u₁ x * pd (dif u₁ u₀ b) i.succ x -
      compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) t ≤ P * S := fun i b => by
    refine (Q_mul_sub_mul_le hr hCS hsup (sCu i b) (contDiff_pd_top (sdu b) _) (sCv i b)
      (contDiff_pd_top (sdv b) _) (pCu i b) (isSPeriodic_pd (pdu b) _) (pCv i b)
      (isSPeriodic_pd (pdv b) _) t (qCu i b) (qpd i b) (qCd i b) (qpdv i b)).trans ?_
    have k1 : K * Ed + K * E1 * Ev ≤ K * S := aux_T2 hK0 hEv0 hE00
    calc 2 * c * (K * Ed + K * E1 * Ev) ≤ 2 * c * (K * S) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg zero_le_two hc0)
      _ = 2 * c * K * S := by ring
      _ ≤ P * S := mul_le_mul_of_nonneg_right hP1 hS0
  have T3 : ∀ (i : Fin d) b c', Q r (fun x =>
      dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
        dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x)) t ≤ P * S :=
    fun i b c' => by
      have e : (fun x => dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
          dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x)) =
          fun x => (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) * dif u₁ u₀ c' x -
            (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x) * dif v₁ v₀ c' x := by
        funext x; ring
      rw [e]
      have sfu := (sAu i a b c').mul (contDiff_pd_top (hu₀ b) i.succ)
      have sfv := (sAv i a b c').mul (contDiff_pd_top (hv₀ b) i.succ)
      have pfu : IsSPeriodic fun x => psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x :=
        fun j x => by simp only [pAu i a b c' j x, isSPeriodic_pd (pu₀ b) i.succ j x]
      have pfv : IsSPeriodic fun x => psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x :=
        fun j x => by simp only [pAv i a b c' j x, isSPeriodic_pd (pv₀ b) i.succ j x]
      have qf : Q r (fun x => psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) t ≤ c * K * K := by
        refine (Q_mul_le hr hCS hsup (sAu i a b c') (contDiff_pd_top (hu₀ b) i.succ)
          (pAu i a b c') (isSPeriodic_pd (pu₀ b) i.succ) t).trans ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left (qAu i b c') hc0) (qpu0 i b)
          (Q_nonneg _ _ _) (mul_nonneg hc0 hK0)
      have qfd : Q r (fun x => psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x -
          psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x) t ≤
          2 * c * (K * E0 + K * (E0 + E1) * K) :=
        Q_mul_sub_mul_le hr hCS hsup (sAu i a b c') (contDiff_pd_top (hu₀ b) i.succ)
          (sAv i a b c') (contDiff_pd_top (hv₀ b) i.succ) (pAu i a b c')
          (isSPeriodic_pd (pu₀ b) i.succ) (pAv i a b c') (isSPeriodic_pd (pv₀ b) i.succ) t
          (qAu i b c') (qpd0 i b) (qAd i b c') (qpv0 i b)
      refine (Q_mul_sub_mul_le hr hCS hsup sfu (sdu c') sfv (sdv c') pfu (pdu c') pfv (pdv c') t
        qf (qd c') qfd (qv c')).trans ?_
      have k2 : c * K * K * Ed + 2 * c * (K * E0 + K * (E0 + E1) * K) * Ev ≤
          (c * K * K + 2 * c * (K + K * K)) * S := aux_T3 hc0 hK0 hEd0 hEv0 hE00 hE10
      calc 2 * c * (c * K * K * Ed + 2 * c * (K * E0 + K * (E0 + E1) * K) * Ev)
          ≤ 2 * c * ((c * K * K + 2 * c * (K + K * K)) * S) :=
            mul_le_mul_of_nonneg_left k2 (mul_nonneg zero_le_two hc0)
        _ = 2 * c * (c * K * K + 2 * c * (K + K * K)) * S := by ring
        _ ≤ P * S := mul_le_mul_of_nonneg_right hP2 hS0
  -- assemble
  rw [show (fun x => genG A F u₁ a x - genG A F u₀ a x - (genG A F v₁ a x - genG A F v₀ a x)) =
    fun x => (∑ c', (dif u₁ u₀ c' x * psiF F u₁ u₀ a c' x - dif v₁ v₀ c' x * psiF F v₁ v₀ a c' x)) -
        ∑ i, ∑ b, ((compF (A i a b) u₁ x * pd (dif u₁ u₀ b) i.succ x -
            compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) +
          ∑ c', (dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
            dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x))) from
    funext fun x => genG_second_diff_eq hA hF hu₀ hu₁ hv₀ hv₁ a x]
  have s1 : ∀ c', ContDiff ℝ ∞ (fun x => dif u₁ u₀ c' x * psiF F u₁ u₀ a c' x -
      dif v₁ v₀ c' x * psiF F v₁ v₀ a c' x) := fun c' =>
    ((sdu c').mul (sFu a c')).sub ((sdv c').mul (sFv a c'))
  have s2 : ∀ (i : Fin d) b, ContDiff ℝ ∞ (fun x => compF (A i a b) u₁ x *
      pd (dif u₁ u₀ b) i.succ x - compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) :=
    fun i b => ((sCu i b).mul (contDiff_pd_top (sdu b) _)).sub
      ((sCv i b).mul (contDiff_pd_top (sdv b) _))
  have s3 : ∀ (i : Fin d) b c', ContDiff ℝ ∞ (fun x =>
      dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
        dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x)) := fun i b c' =>
    ((sdu c').mul ((sAu i a b c').mul (contDiff_pd_top (hu₀ b) _))).sub
      ((sdv c').mul ((sAv i a b c').mul (contDiff_pd_top (hv₀ b) _)))
  have s23 : ∀ (i : Fin d) b, ContDiff ℝ ∞ (fun x => (compF (A i a b) u₁ x *
      pd (dif u₁ u₀ b) i.succ x - compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) +
      ∑ c', (dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
        dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x))) := fun i b =>
    (s2 i b).add (ContDiff.sum fun c' _ => s3 i b c')
  refine (Q_sub_le r (ContDiff.sum fun c' _ => s1 c')
    (ContDiff.sum fun i _ => ContDiff.sum fun b _ => s23 i b) t).trans ?_
  have hX : Q r (fun x => ∑ c', (dif u₁ u₀ c' x * psiF F u₁ u₀ a c' x -
      dif v₁ v₀ c' x * psiF F v₁ v₀ a c' x)) t ≤ n * (n * (P * S)) := by
    refine (Q_sum_le r Finset.univ s1 t).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ c', Q r _ t ≤ ∑ _c' : Fin n, P * S := Finset.sum_le_sum fun c' _ => T1 c'
      _ = n * (P * S) := by simp
  have hZ : ∀ (i : Fin d) b, Q r (fun x => (compF (A i a b) u₁ x *
      pd (dif u₁ u₀ b) i.succ x - compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) +
      ∑ c', (dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
        dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x))) t ≤
      2 * (P * S) + 2 * (n * (n * (P * S))) := fun i b => by
    refine (Q_add_le r (s2 i b) (ContDiff.sum fun c' _ => s3 i b c') t).trans ?_
    have h4 := (Q_sum_le r Finset.univ (s3 i b) t)
    rw [Finset.card_univ, Fintype.card_fin] at h4
    have h5 : ∑ c', Q r (fun x => dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x *
        pd (u₀ b) i.succ x) - dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x)) t
        ≤ n * (P * S) := by
      calc _ ≤ ∑ _c' : Fin n, P * S := Finset.sum_le_sum fun c' _ => T3 i b c'
        _ = n * (P * S) := by simp
    have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) n)
    linarith [T2 i b]
  have hY : Q r (fun x => ∑ i, ∑ b, ((compF (A i a b) u₁ x * pd (dif u₁ u₀ b) i.succ x -
      compF (A i a b) v₁ x * pd (dif v₁ v₀ b) i.succ x) +
      ∑ c', (dif u₁ u₀ c' x * (psiA A u₁ u₀ i a b c' x * pd (u₀ b) i.succ x) -
        dif v₁ v₀ c' x * (psiA A v₁ v₀ i a b c' x * pd (v₀ b) i.succ x)))) t ≤
      d * (d * (n * (n * (2 * (P * S) + 2 * (n * (n * (P * S))))))) := by
    refine (Q_sum_le r Finset.univ (fun i => ContDiff.sum fun b _ => s23 i b) t).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ∑ i, Q r (fun x => ∑ b, _) t ≤
        ∑ _i : Fin d, n * (n * (2 * (P * S) + 2 * (n * (n * (P * S))))) :=
          Finset.sum_le_sum fun i _ => by
            refine (Q_sum_le r Finset.univ (fun b => s23 i b) t).trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            calc ∑ b, Q r _ t ≤ ∑ _b : Fin n, (2 * (P * S) + 2 * (n * (n * (P * S)))) :=
                  Finset.sum_le_sum fun b _ => hZ i b
              _ = _ := by simp; ring
      _ = _ := by simp
  have e : C * S = 2 * (n * (n * (P * S))) +
      2 * (d * (d * (n * (n * (2 * (P * S) + 2 * (n * (n * (P * S)))))))) := by
    rw [hCdef]; ring
  rw [e]
  linarith

end Second

/-! ### The Galerkin level: `H^ρ` bounds of the projected generator and of its derivative -/

section Galerkin

open KatoGalerkin
open KatoCausal (hmS hmS_apply hmS_add hmS_smul hmS_sub norm_hmS_sq)

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- `‖a‖_{H^m} ≤ ‖a‖_{H^q}` for `m ≤ q` on the Galerkin space. -/
theorem norm_hmS_le {m q : ℕ} (hmq : m ≤ q) {N : ℕ} (a : GS d n N) : ‖hmS m q a‖ ≤ ‖a‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun p _ => ?_)
  rw [hmS_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow, div_pow,
    Real.sq_sqrt (wq_nonneg _ _), Real.sq_sqrt (wq_nonneg _ _)]
  have h1 : wq m p.2.1 / wq q p.2.1 ≤ 1 := (div_le_one (wq_pos _ _)).2 (wq_mono hmq _)
  have h2 := sq_nonneg (a p)
  have h3 := div_nonneg (wq_nonneg m p.2.1) (wq_nonneg q p.2.1)
  nlinarith

/-- Monotonicity of the `H^m` norms on the Galerkin space. -/
theorem norm_hmS_mono {m m' q : ℕ} (hmm : m ≤ m') {N : ℕ} (a : GS d n N) :
    ‖hmS m q a‖ ≤ ‖hmS m' q a‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun p _ => ?_)
  rw [hmS_apply, hmS_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow,
    mul_pow, div_pow, div_pow, Real.sq_sqrt (wq_nonneg _ _), Real.sq_sqrt (wq_nonneg _ _),
    Real.sq_sqrt (wq_nonneg _ _)]
  have h1 := wq_mono (d := d) hmm p.2.1
  have h2 := sq_nonneg (a p)
  have h3 := wq_pos (d := d) q p.2.1
  have h4 : wq m p.2.1 / wq q p.2.1 ≤ wq m' p.2.1 / wq q p.2.1 :=
    div_le_div_of_nonneg_right h1 h3.le
  exact mul_le_mul_of_nonneg_right h4 h2

/-- **Bessel for projected fields**: a Galerkin vector whose entries are the (`√wq_q`-weighted)
Fourier coefficients of smooth periodic fields `g_b` has `‖·‖²_{H^ρ} ≤ Σ_b Q_ρ(g_b)`. -/
theorem norm_hmS_sq_le_of_coef (ρ q : ℕ) {N : ℕ} (z : GS d n N) (g : Fin n → ST d → ℝ)
    (hg : ∀ b, ContDiff ℝ ∞ (g b)) (hgp : ∀ b, IsSPeriodic (g b))
    (hz : ∀ p : Fin n × KatoGalerkin.box (d := d) N, z p = Real.sqrt (wq q p.2.1) * coef (g p.1) 0 p.2.1) :
    ‖hmS ρ q z‖ ^ 2 ≤ ∑ b, Q ρ (g b) 0 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun b _ => ?_
  refine le_trans (le_of_eq ?_) (bessel_Hq ρ (KatoGalerkin.box N) (hg b) (hgp b) 0)
  rw [← Finset.sum_coe_sort (KatoGalerkin.box N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmS_apply, hz, ← mul_assoc, div_mul_cancel₀ _ (sqrt_wq_ne q k.1), mul_pow,
    Real.sq_sqrt (wq_nonneg _ _)]

theorem contDiff_genG_fld (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) : ContDiff ℝ ∞ (genG A F (fld q a) b) :=
  contDiff_genG hA hF (fun b => contDiff_fld q a b) b

theorem isSPeriodic_genG_fld (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) :
    IsSPeriodic (genG A F (fld q a) b) :=
  isSPeriodic_genG (fun b => isSPeriodic_fld q a b) b

theorem GN_sub_apply (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a a' : GS d n N) (p : Fin n × KatoGalerkin.box (d := d) N) :
    (GN A F q a - GN A F q a') p = Real.sqrt (wq q p.2.1) *
      coef (fun x => genG A F (fld q a) p.1 x - genG A F (fld q a') p.1 x) 0 p.2.1 := by
  rw [PiLp.sub_apply, GN_apply, GN_apply, ← mul_sub,
    coef_sub (contDiff_genG_fld hA hF q a p.1).continuous
      (contDiff_genG_fld hA hF q a' p.1).continuous]

theorem GN_second_apply (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a₀ a₁ b₀ b₁ : GS d n N) (p : Fin n × KatoGalerkin.box (d := d) N) :
    (GN A F q a₁ - GN A F q a₀ - (GN A F q b₁ - GN A F q b₀)) p = Real.sqrt (wq q p.2.1) *
      coef (fun x => genG A F (fld q a₁) p.1 x - genG A F (fld q a₀) p.1 x -
        (genG A F (fld q b₁) p.1 x - genG A F (fld q b₀) p.1 x)) 0 p.2.1 := by
  have c1 := (contDiff_genG_fld hA hF q a₁ p.1).continuous
  have c0 := (contDiff_genG_fld hA hF q a₀ p.1).continuous
  have d1 := (contDiff_genG_fld hA hF q b₁ p.1).continuous
  have d0 := (contDiff_genG_fld hA hF q b₀ p.1).continuous
  have e1 := coef_sub (f := fun x => genG A F (fld q a₁) p.1 x - genG A F (fld q a₀) p.1 x)
    (g := fun x => genG A F (fld q b₁) p.1 x - genG A F (fld q b₀) p.1 x) (c1.sub c0) (d1.sub d0)
    0 p.2.1
  have e2 := coef_sub c1 c0 0 p.2.1
  have e3 := coef_sub d1 d0 0 p.2.1
  rw [PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, GN_apply, GN_apply, GN_apply, GN_apply, e1,
    e2, e3]
  ring

theorem fld_sub4 (q : ℕ) {N : ℕ} (a₀ a₁ b₀ b₁ : GS d n N) :
    fld q (a₁ - a₀ - (b₁ - b₀)) =
      fun b x => fld q a₁ b x - fld q a₀ b x - (fld q b₁ b x - fld q b₀ b x) := by
  rw [fld_sub, fld_sub, fld_sub]

/-- **Cutoff-uniform `H^{ρ+1} → H^ρ` Lipschitz bound of the projected generator**:
`‖G_N a - G_N a'‖_{H^ρ} ≤ L ‖a - a'‖_{H^{ρ+1}}` for Galerkin states in the `H^{ρ+1}` ball
(`2m_s ≤ ρ + 1`, `m_s > d/2`), uniformly in the cutoff `N` and the weight index `q`. -/
theorem GN_lip_hm {ms ρ : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (q N : ℕ) (a a' : GS d n N), ‖hmS (ρ + 1) q a‖ ≤ R →
      ‖hmS (ρ + 1) q a'‖ ≤ R →
      ‖hmS ρ q (GN A F q a - GN A F q a')‖ ≤ L * ‖hmS (ρ + 1) q (a - a')‖ := by
  obtain ⟨C, hC0, hC⟩ := Q_genG_sub_le (d := d) (n := n) hms hρ hA hF hR
  refine ⟨Real.sqrt (n * C), Real.sqrt_nonneg _, fun q N a a' ha ha' => ?_⟩
  have hE : ∀ z : GS d n N, ‖hmS (ρ + 1) q z‖ ≤ R → energyQ (ρ + 1) (fld q z) 0 ≤ R ^ 2 :=
    fun z hz => by rw [← norm_hmS_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hsq : ‖hmS ρ q (GN A F q a - GN A F q a')‖ ^ 2 ≤
      n * C * ‖hmS (ρ + 1) q (a - a')‖ ^ 2 := by
    refine (norm_hmS_sq_le_of_coef ρ q _ (fun b x => genG A F (fld q a) b x -
      genG A F (fld q a') b x) (fun b => (contDiff_genG_fld hA hF q a b).sub
        (contDiff_genG_fld hA hF q a' b)) (fun b j x => by
          simp only [isSPeriodic_genG_fld (A := A) (F := F) q a b j x,
            isSPeriodic_genG_fld (A := A) (F := F) q a' b j x])
      (GN_sub_apply hA hF q a a')).trans ?_
    have h := fun b => hC (fld q a) (fld q a') (fun b => contDiff_fld q a b)
      (fun b => contDiff_fld q a' b) (fun b => isSPeriodic_fld q a b)
      (fun b => isSPeriodic_fld q a' b) 0 (hE a ha) (hE a' ha') b
    have e : energyQ (ρ + 1) (fun b x => fld q a b x - fld q a' b x) 0 =
        ‖hmS (ρ + 1) q (a - a')‖ ^ 2 := by rw [norm_hmS_sq _ _ _ 0, fld_sub]
    calc ∑ b, Q ρ (fun x => genG A F (fld q a) b x - genG A F (fld q a') b x) 0
        ≤ ∑ _b : Fin n, C * ‖hmS (ρ + 1) q (a - a')‖ ^ 2 :=
          Finset.sum_le_sum fun b _ => by rw [← e]; exact h b
      _ = n * C * ‖hmS (ρ + 1) q (a - a')‖ ^ 2 := by simp; ring
  have hrhs : 0 ≤ Real.sqrt (n * C) * ‖hmS (ρ + 1) q (a - a')‖ := by positivity
  refine abs_le_of_sq_le_sq' ?_ hrhs |>.2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hsq

/-- **Cutoff-uniform mixed second-difference bound of the projected generator** (`H^{ρ+1} → H^ρ`):
`‖G_N a₁ - G_N a₀ - G_N b₁ + G_N b₀‖²_{H^ρ} ≤ C (‖a₁ - a₀ - b₁ + b₀‖²_{H^{ρ+1}}
  + ‖b₁ - b₀‖²_{H^{ρ+1}} (‖a₀ - b₀‖²_{H^{ρ+1}} + ‖a₁ - b₁‖²_{H^{ρ+1}}))`. -/
theorem GN_second_hm {ms ρ : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q N : ℕ) (a₀ a₁ b₀ b₁ : GS d n N), ‖hmS (ρ + 1) q a₀‖ ≤ R →
      ‖hmS (ρ + 1) q a₁‖ ≤ R → ‖hmS (ρ + 1) q b₀‖ ≤ R → ‖hmS (ρ + 1) q b₁‖ ≤ R →
      ‖hmS ρ q (GN A F q a₁ - GN A F q a₀ - (GN A F q b₁ - GN A F q b₀))‖ ^ 2 ≤
        C * (‖hmS (ρ + 1) q (a₁ - a₀ - (b₁ - b₀))‖ ^ 2 + ‖hmS (ρ + 1) q (b₁ - b₀)‖ ^ 2 *
          (‖hmS (ρ + 1) q (a₀ - b₀)‖ ^ 2 + ‖hmS (ρ + 1) q (a₁ - b₁)‖ ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := Q_genG_second_diff_le (d := d) (n := n) hms hρ hA hF hR
  refine ⟨n * C, by positivity, fun q N a₀ a₁ b₀ b₁ h0 h1 h2 h3 => ?_⟩
  have hE : ∀ z : GS d n N, ‖hmS (ρ + 1) q z‖ ≤ R → energyQ (ρ + 1) (fld q z) 0 ≤ R ^ 2 :=
    fun z hz => by rw [← norm_hmS_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have sm : ∀ (z : GS d n N) b, ContDiff ℝ ∞ (genG A F (fld q z) b) := fun z b =>
    contDiff_genG_fld hA hF q z b
  refine (norm_hmS_sq_le_of_coef ρ q _ (fun b x => genG A F (fld q a₁) b x -
      genG A F (fld q a₀) b x - (genG A F (fld q b₁) b x - genG A F (fld q b₀) b x))
      (fun b => ((sm a₁ b).sub (sm a₀ b)).sub ((sm b₁ b).sub (sm b₀ b))) (fun b j x => by
        simp only [isSPeriodic_genG_fld (A := A) (F := F) q a₁ b j x,
          isSPeriodic_genG_fld (A := A) (F := F) q a₀ b j x,
          isSPeriodic_genG_fld (A := A) (F := F) q b₁ b j x,
          isSPeriodic_genG_fld (A := A) (F := F) q b₀ b j x])
      (GN_second_apply hA hF q a₀ a₁ b₀ b₁)).trans ?_
  have h := fun b => hC (fld q a₀) (fld q a₁) (fld q b₀) (fld q b₁)
    (fun b => contDiff_fld q a₀ b) (fun b => contDiff_fld q a₁ b) (fun b => contDiff_fld q b₀ b)
    (fun b => contDiff_fld q b₁ b) (fun b => isSPeriodic_fld q a₀ b)
    (fun b => isSPeriodic_fld q a₁ b) (fun b => isSPeriodic_fld q b₀ b)
    (fun b => isSPeriodic_fld q b₁ b) 0 (hE a₀ h0) (hE a₁ h1) (hE b₀ h2) (hE b₁ h3) b
  have e1 : energyQ (ρ + 1) (fun b x => fld q a₁ b x - fld q a₀ b x -
      (fld q b₁ b x - fld q b₀ b x)) 0 = ‖hmS (ρ + 1) q (a₁ - a₀ - (b₁ - b₀))‖ ^ 2 := by
    rw [norm_hmS_sq _ _ _ 0, fld_sub4]
  have e2 : ∀ z z' : GS d n N, energyQ (ρ + 1) (fun b x => fld q z b x - fld q z' b x) 0 =
      ‖hmS (ρ + 1) q (z - z')‖ ^ 2 := fun z z' => by rw [norm_hmS_sq _ _ _ 0, fld_sub]
  rw [e1, e2, e2, e2] at h
  calc ∑ b, Q ρ (fun x => genG A F (fld q a₁) b x - genG A F (fld q a₀) b x -
        (genG A F (fld q b₁) b x - genG A F (fld q b₀) b x)) 0
      ≤ ∑ _b : Fin n, C * (‖hmS (ρ + 1) q (a₁ - a₀ - (b₁ - b₀))‖ ^ 2 +
          ‖hmS (ρ + 1) q (b₁ - b₀)‖ ^ 2 *
            (‖hmS (ρ + 1) q (a₀ - b₀)‖ ^ 2 + ‖hmS (ρ + 1) q (a₁ - b₁)‖ ^ 2)) :=
        Finset.sum_le_sum fun b _ => h b
    _ = _ := by simp; ring

/-! ### The derivative of the projected generator -/

/-- The derivative `DG_N(a)w` of the projected generator. -/
def DGN (A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ) (F : Fin n → (Fin n → ℝ) → ℝ) (q : ℕ)
    {N : ℕ} (a w : GS d n N) : GS d n N :=
  fderiv ℝ (GN A F q) a w

/-- The `H^m` coordinates as a continuous linear map. -/
def hmSL (m q : ℕ) {N : ℕ} : GS d n N →L[ℝ] GS d n N :=
  LinearMap.toContinuousLinearMap
    { toFun := hmS m q, map_add' := hmS_add m q, map_smul' := fun c x => hmS_smul m q c x }

theorem hmSL_apply (m q : ℕ) {N : ℕ} (a : GS d n N) : hmSL m q a = hmS m q a := rfl

theorem hasFDerivAt_GN (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a : GS d n N) :
    HasFDerivAt (GN A F q) (fderiv ℝ (GN (d := d) (n := n) A F q (N := N)) a) a :=
  ((contDiff_GN hA hF q N).differentiable (by simp) a).hasFDerivAt

/-- The derivative along a line as a limit of slopes. -/
theorem tendsto_slope_GN (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a w : GS d n N) :
    Tendsto (fun t : ℝ => t⁻¹ • (GN A F q (a + t • w) - GN A F q a)) (𝓝[≠] 0)
      (𝓝 (DGN A F q a w)) := by
  have hl : HasDerivAt (fun t : ℝ => a + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
  have hd : HasDerivAt (fun t : ℝ => GN A F q (a + t • w)) (DGN A F q a w) 0 :=
    (hasFDerivAt_GN hA hF q a).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have := hd.tendsto_slope_zero
  simpa using this

/-- A limit along `𝓝[≠] 0` of vectors with bounded `H^ρ` norm has the same bound. -/
theorem norm_hmS_le_of_tendsto (ρ q : ℕ) {N : ℕ} {g : ℝ → GS d n N} {l : GS d n N} {B : ℝ}
    (hg : Tendsto g (𝓝[≠] 0) (𝓝 l)) (hB : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖hmS ρ q (g t)‖ ≤ B) :
    ‖hmS ρ q l‖ ≤ B := by
  have h1 : Tendsto (fun t => ‖hmS ρ q (g t)‖) (𝓝[≠] 0) (𝓝 ‖hmS ρ q l‖) :=
    (((hmSL (d := d) (n := n) ρ q).continuous.tendsto l).comp hg).norm
  exact le_of_tendsto h1 hB

theorem eventually_small (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| * c ≤ 1 := by
  have h : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 / (c + 1) :=
    (continuous_abs.tendsto' 0 0 (by simp)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [nhdsWithin_le_nhds h] with t ht
  have h1 : |t| * (c + 1) < 1 := by rwa [lt_div_iff₀ (by linarith)] at ht
  nlinarith [abs_nonneg t]

/-- **Cutoff-uniform bound of the derivative of the projected generator**:
`‖DG_N(a)w‖_{H^ρ} ≤ L ‖w‖_{H^{ρ+1}}` for `‖a‖_{H^{ρ+1}} ≤ R`. -/
theorem DGN_bound {ms ρ : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (q N : ℕ) (a w : GS d n N), ‖hmS (ρ + 1) q a‖ ≤ R →
      ‖hmS ρ q (DGN A F q a w)‖ ≤ L * ‖hmS (ρ + 1) q w‖ := by
  obtain ⟨L, hL0, hL⟩ := GN_lip_hm (d := d) (n := n) hms hρ hA hF (R := R + 1) (by linarith)
  refine ⟨L, hL0, fun q N a w ha => ?_⟩
  refine norm_hmS_le_of_tendsto ρ q (tendsto_slope_GN hA hF q a w) ?_
  filter_upwards [eventually_small _ (norm_nonneg (hmS (ρ + 1) q w)), self_mem_nhdsWithin]
    with t ht ht0
  have ht0' : t ≠ 0 := ht0
  have hb : ‖hmS (ρ + 1) q (a + t • w)‖ ≤ R + 1 := by
    rw [hmS_add, hmS_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    linarith
  have h := hL q N (a + t • w) a hb (by linarith)
  rw [add_sub_cancel_left, hmS_smul, norm_smul, Real.norm_eq_abs] at h
  rw [hmS_smul, norm_smul, Real.norm_eq_abs, abs_inv]
  have hpos : 0 < |t| := abs_pos.2 ht0'
  calc |t|⁻¹ * ‖hmS ρ q (GN A F q (a + t • w) - GN A F q a)‖
      ≤ |t|⁻¹ * (L * (|t| * ‖hmS (ρ + 1) q w‖)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hpos.le)
    _ = L * ‖hmS (ρ + 1) q w‖ := by field_simp

/-- **Cutoff-uniform Lipschitz bound of the derivative of the projected generator in the base
point**: `‖DG_N(a)w - DG_N(b)w‖_{H^ρ} ≤ L ‖a - b‖_{H^{ρ+1}} ‖w‖_{H^{ρ+1}}` for
`‖a‖_{H^{ρ+1}}, ‖b‖_{H^{ρ+1}} ≤ R`. -/
theorem DGN_lip {ms ρ : ℕ} (hms : (d : ℝ) / 2 < ms) (hρ : 2 * ms ≤ ρ + 1)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (q N : ℕ) (a b w : GS d n N), ‖hmS (ρ + 1) q a‖ ≤ R →
      ‖hmS (ρ + 1) q b‖ ≤ R →
      ‖hmS ρ q (DGN A F q a w - DGN A F q b w)‖ ≤
        L * ‖hmS (ρ + 1) q (a - b)‖ * ‖hmS (ρ + 1) q w‖ := by
  obtain ⟨C, hC0, hC⟩ := GN_second_hm (d := d) (n := n) hms hρ hA hF (R := R + 1) (by linarith)
  refine ⟨Real.sqrt (2 * C), Real.sqrt_nonneg _, fun q N a b w ha hb => ?_⟩
  have hlim := (tendsto_slope_GN hA hF q a w).sub (tendsto_slope_GN hA hF q b w)
  refine norm_hmS_le_of_tendsto ρ q hlim ?_
  filter_upwards [eventually_small _ (norm_nonneg (hmS (ρ + 1) q w)), self_mem_nhdsWithin]
    with t ht ht0
  have ht0' : t ≠ 0 := ht0
  have hball : ∀ z : GS d n N, ‖hmS (ρ + 1) q z‖ ≤ R → ‖hmS (ρ + 1) q (z + t • w)‖ ≤ R + 1 := by
    intro z hz
    rw [hmS_add, hmS_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    linarith
  have h := hC q N a (a + t • w) b (b + t • w) (by linarith) (hball a ha) (by linarith)
    (hball b hb)
  have z1 : a + t • w - a - (b + t • w - b) = 0 := by abel
  have z2 : b + t • w - b = t • w := by abel
  have z3 : a + t • w - (b + t • w) = a - b := by abel
  rw [z1, z2, z3, hmS_smul, norm_smul, Real.norm_eq_abs] at h
  have hz : hmS (ρ + 1) q (0 : GS d n N) = 0 := PiLp.ext fun p => by simp [hmS_apply]
  rw [hz, norm_zero] at h
  have e : t⁻¹ • (GN A F q (a + t • w) - GN A F q a) - t⁻¹ • (GN A F q (b + t • w) - GN A F q b)
      = t⁻¹ • (GN A F q (a + t • w) - GN A F q a - (GN A F q (b + t • w) - GN A F q b)) :=
    (smul_sub _ _ _).symm
  rw [e, hmS_smul, norm_smul, Real.norm_eq_abs, abs_inv]
  have hpos : 0 < |t| := abs_pos.2 ht0'
  set X := ‖hmS ρ q (GN A F q (a + t • w) - GN A F q a - (GN A F q (b + t • w) - GN A F q b))‖
  set Y := |t| * ‖hmS (ρ + 1) q w‖
  set Z := ‖hmS (ρ + 1) q (a - b)‖
  have hX : X ≤ Real.sqrt (2 * C) * Z * Y := by
    have hrhs : 0 ≤ Real.sqrt (2 * C) * Z * Y := by positivity
    refine abs_le_of_sq_le_sq' ?_ hrhs |>.2
    have : X ^ 2 ≤ C * (0 ^ 2 + Y ^ 2 * (Z ^ 2 + Z ^ 2)) := h
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg Y, sq_nonneg Z]
  calc |t|⁻¹ * X ≤ |t|⁻¹ * (Real.sqrt (2 * C) * Z * Y) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.2 hpos.le)
    _ = Real.sqrt (2 * C) * Z * ‖hmS (ρ + 1) q w‖ := by
        simp only [Y]; field_simp

end Galerkin

end RenewalGeometry.KatoSecond
