/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabCauchy
import RenewalGeometry.Continuum.ReducedWaveShiftData

/-!
# `thm:hyperbolic` with a nonzero shift: the difference energy inequality and the Cauchy property

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability".)  The
hypotheses are the paper's: uniform hyperbolicity with a common time function (`MetricHypSh`:
`g^{00} ≤ -a₀`, uniformly spacelike slices `g_{ij} ≥ λ_S`, bounded inverse metric — no sign
of `g^{ij}`, i.e. any bounded shift), `eq:hyperbolic-bound`, `eq:reduced-wave`; `Σ = 𝕋³`.
The energy is the differentiated wave energy with the normal-derivative multiplier
(`SlabWaveShift.energySK`).

* `forcing_Q_le_sh` — the `H^{s-2}` forcing bound of `ReducedWaveSlabForcing.lean` without the
  positivity of `g^{ij}`;
* `Q_le_energySK`, `int_size_le_Q`, **`EdiffS_equiv`** — the shifted difference energy
  `E_{h,j}` is uniformly equivalent to `W = ‖g_h - g_j‖²_{H^{s-1}} + ‖∂ₜg_h - ∂ₜg_j‖²_{H^{s-2}}`;
* `normK_fdiff_le_sh`, **`hyperbolic_energy_sh`** (`eq:hyperbolic-energy`),
  **`common_slab_cauchy_sh`** (the first two limits, Cauchy form);
* `shifted_metricHypSh` — non-vacuity with a constant metric whose shift makes `∂ₜ` spacelike
  (`g^{11} < 0`, so the earlier `MetricHyp` rendering with positive `g^{ij}` fails).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg ReducedWaveStab SlabWaveShift

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]
variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {T a0 lam Λ K0 : ℝ}

set_option maxHeartbeats 1600000 in
/-- **The `H^{s-2}` forcing bound without positivity of `g^{ij}`** (`thm:hyperbolic`, proof; a copy
of `ReducedWaveStab.forcing_Q_le` for any constant `λ`): there are constants `c₁, c₂`,
depending only on the common constants, such that for any two metrics with the hypotheses,
`Q_k(F_c) ≤ c₁ W (1 + Q_k(𝒮ⱼ,c)) + c₂ Q_k(𝒮ₕ,c - 𝒮ⱼ,c)` on `[0, T]`. -/
theorem forcing_Q_le_sh {k : ℕ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0)
    (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHyp Np θ (k + 2) T a0 lam Λ K0 g gi S →
      MetricHyp Np θ (k + 2) T a0 lam Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T, ∀ c,
      Q k (fdiff a0 gi g g' c) t ≤
        c₁ * Wn k g g' t * (1 + Q k (S' c) t) + c₂ * Q k (fun x => S c x - S' c x) t := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  obtain ⟨Bθ, hBθ0, hBθ⟩ := exists_Btheta (T := T) k hθ
  have hk2 : 2 * 2 ≤ k + 1 := by omega
  set B := BV k CS K0 Λ a0 Bθ
  have hB : 0 ≤ B := BV_nonneg k hK0 hBθ0
  have lipβ := fun i : Fin 3 => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup (betaP i) hB
  have lipγ := fun ij : Fin 3 × Fin 3 => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup
    (gammaP ij.1 ij.2) hB
  have lipψ := fun c : Idx => evalF_lip (σ := Option (NV κ)) hk2 hCS hsup (psiP Np c) hB
  choose Bβ Lβ hBβ hLβ lβ using lipβ
  choose Bγ Lγ hBγ hLγ lγ using lipγ
  choose Bψ Lψ hBψ hLψ lψ using lipψ
  set Ca := algC 3 k CS
  have hCa : 0 ≤ Ca := algC_nonneg k hCS
  set LB := ∑ i, Lβ i
  set LG := ∑ ij, Lγ ij
  set LP := ∑ c, Lψ c
  have hLB : 0 ≤ LB := Finset.sum_nonneg fun i _ => hLβ i
  have hLG : 0 ≤ LG := Finset.sum_nonneg fun i _ => hLγ i
  have hLP : 0 ≤ LP := Finset.sum_nonneg fun i _ => hLψ i
  set cd := cD κ k CS K0 Λ a0
  have hcd : 0 ≤ cd := by
    simp only [cd, cD]
    have := cq_nonneg k (K0 := K0) (Λ := Λ) (a0 := a0) hCS
    have := cgi_nonneg k (K0 := K0) (Λ := Λ) hCS
    positivity
  set Bq := (wordsLE 3 k).card * MetricHyp.Cq (k + 2) CS K0 Λ a0 ^ 2
  have hBq : 0 ≤ Bq := by positivity
  set cqq := cq k CS K0 Λ a0
  have hcqq : 0 ≤ cqq := cq_nonneg k hCS
  refine ⟨8 * (36 * Ca * LB * cd * K0) + 8 * (81 * Ca * LG * cd * K0) + 4 * (LP * cd) +
      2 * (2 * Ca * cqq), 2 * (2 * Ca * Bq), by positivity, by positivity,
    fun g g' gi gi' S S' h h' t ht c => ?_⟩
  -- the inputs of the Lipschitz estimates
  set V := Vfam a0 θ g gi
  set V' := Vfam a0 θ g' gi'
  set D := ∑ v, Q k (fun x => V v x - V' v x) t
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun v _ => Q_nonneg _ _ _
  have hDv : ∀ v, Q k (fun x => V v x - V' v x) t ≤ D := fun v =>
    Finset.single_le_sum (f := fun v => Q k (fun x => V v x - V' v x) t)
      (fun v _ => Q_nonneg _ _ _) (Finset.mem_univ v)
  have hDW : D ≤ cd * Wn k g g' t := DV_le hk h h' hT ha hCS hsup ht
  have bV := h.Vbound hT ha hCS hsup hBθ0 hBθ ht
  have bV' := h'.Vbound hT ha hCS hsup hBθ0 hBθ ht
  have hW := Wn_nonneg k g g' t
  -- the four parts of the forcing
  have sβ := h.sbeta ha
  have sβ' := h'.sbeta ha
  have sγ := h.sgamma ha
  have sγ' := h'.sgamma ha
  have sU : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (pd (g' c) 0) i.succ) := fun i =>
    contDiff_pd_top (contDiff_pd_top (h'.sg c) 0) _
  have sVV : ∀ i j : Fin 3, ContDiff ℝ ∞ (pd (pd (g' c) j.succ) i.succ) := fun i j =>
    contDiff_pd_top (contDiff_pd_top (h'.sg c) _) _
  have pU : ∀ i : Fin 3, IsSPeriodic (pd (pd (g' c) 0) i.succ) := fun i =>
    isSPeriodic_pd (isSPeriodic_pd (h'.pg c) 0) _
  have pVV : ∀ i j : Fin 3, IsSPeriodic (pd (pd (g' c) j.succ) i.succ) := fun i j =>
    isSPeriodic_pd (isSPeriodic_pd (h'.pg c) _) _
  set A : X → ℝ := fun x => 2 * ∑ i : Fin 3, (betaF (lapseInv a0 gi) gi i x -
    betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x
  set Bf : X → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, (gammaF (lapseInv a0 gi) gi i j x -
    gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x
  set C : X → ℝ := fun x => psiF a0 Np θ g gi c x - psiF a0 Np θ g' gi' c x
  set Df : X → ℝ := fun x => lapseInv a0 gi x * S c x - lapseInv a0 gi' x * S' c x
  have sAi : ∀ i : Fin 3, ContDiff ℝ ∞ fun x => (betaF (lapseInv a0 gi) gi i x -
      betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x := fun i =>
    ((sβ i).sub (sβ' i)).mul (sU i)
  have sBij : ∀ i j : Fin 3, ContDiff ℝ ∞ fun x => (gammaF (lapseInv a0 gi) gi i j x -
      gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x := fun i j =>
    ((sγ i j).sub (sγ' i j)).mul (sVV i j)
  have sA : ContDiff ℝ ∞ A := contDiff_const.mul (ContDiff.sum fun i _ => sAi i)
  have sB : ContDiff ℝ ∞ Bf := ContDiff.sum fun i _ => ContDiff.sum fun j _ => sBij i j
  have sC : ContDiff ℝ ∞ C := (h.spsi ha c).sub (h'.spsi ha c)
  have sD : ContDiff ℝ ∞ Df := ((h.sq ha).mul (h.sS c)).sub ((h'.sq ha).mul (h'.sS c))
  -- the forcing equals `A + B + C + D` on the slab
  have hF : Q k (fdiff a0 gi g g' c) t = Q k (fun x => A x + Bf x + C x + Df x) t := by
    have sF := (diffSys_hyp_any h h' (by omega) hT ha hCS hsup).sF c
    exact Q_congr_slab sF (((sA.add sB).add sC).add sD) (fun x hx => fdiff_eq h h' ha hx c) k ht
  rw [hF]
  have e1 := Q_add_le k ((sA.add sB).add sC) sD t
  have e2 := Q_add_le k (sA.add sB) sC t
  have e3 := Q_add_le k sA sB t
  -- part A
  have hA : Q k A t ≤ 36 * Ca * LB * cd * K0 * Wn k g g' t := by
    have : Q k A t = 2 ^ 2 * Q k (fun x => ∑ i : Fin 3, (betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x) t :=
      Q_const_mul k (ContDiff.sum fun i _ => sAi i) 2 t
    rw [this]
    have hs := Q_sum_le k Finset.univ sAi t
    rw [Finset.card_univ, Fintype.card_fin] at hs
    have hterm : ∀ i : Fin 3, Q k (fun x => (betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) * pd (pd (g' c) 0) i.succ x) t ≤
        Ca * (LB * cd * Wn k g g' t) * K0 := by
      intro i
      have pβd : IsSPeriodic fun x => betaF (lapseInv a0 gi) gi i x -
          betaF (lapseInv a0 gi') gi' i x := fun k' x => by
        show betaF _ gi i _ - betaF _ gi' i _ = _
        rw [h.pbeta i k' x, h'.pbeta i k' x]
      have m := Q_mul_le hk2 hCS hsup ((sβ i).sub (sβ' i)) (sU i) pβd (pU i) t
      have hl := (lβ i V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
      rw [evalF_betaP, evalF_betaP] at hl
      have hLi : Lβ i ≤ LB := Finset.single_le_sum (f := Lβ) (fun i _ => hLβ i)
        (Finset.mem_univ i)
      have h1 : Q k (fun x => betaF (lapseInv a0 gi) gi i x - betaF (lapseInv a0 gi') gi' i x) t
          ≤ LB * cd * Wn k g g' t := by
        refine hl.trans ?_
        calc Lβ i * D ≤ LB * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLB
          _ = _ := by ring
      have h2 := h'.Q_U_le ht c i
      have n1 := Q_nonneg k (fun x => betaF (lapseInv a0 gi) gi i x -
        betaF (lapseInv a0 gi') gi' i x) t
      have n2 := Q_nonneg k (pd (pd (g' c) 0) i.succ) t
      calc _ ≤ Ca * Q k (fun x => betaF (lapseInv a0 gi) gi i x -
            betaF (lapseInv a0 gi') gi' i x) t * Q k (pd (pd (g' c) 0) i.succ) t := m
        _ ≤ Ca * (LB * cd * Wn k g g' t) * K0 := by gcongr
    calc _ ≤ 2 ^ 2 * (3 * ∑ i : Fin 3, Ca * (LB * cd * Wn k g g' t) * K0) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
          push_cast
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)
      _ = 36 * Ca * LB * cd * K0 * Wn k g g' t := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- part B
  have hBb : Q k Bf t ≤ 81 * Ca * LG * cd * K0 * Wn k g g' t := by
    have hterm : ∀ i j : Fin 3, Q k (fun x => (gammaF (lapseInv a0 gi) gi i j x -
        gammaF (lapseInv a0 gi') gi' i j x) * pd (pd (g' c) j.succ) i.succ x) t ≤
        Ca * (LG * cd * Wn k g g' t) * K0 := by
      intro i j
      have pγd : IsSPeriodic fun x => gammaF (lapseInv a0 gi) gi i j x -
          gammaF (lapseInv a0 gi') gi' i j x := fun k' x => by
        show gammaF _ gi i j _ - gammaF _ gi' i j _ = _
        rw [h.pgamma i j k' x, h'.pgamma i j k' x]
      have m := Q_mul_le hk2 hCS hsup ((sγ i j).sub (sγ' i j)) (sVV i j) pγd (pVV i j) t
      have hl := (lγ (i, j) V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
      rw [evalF_gammaP, evalF_gammaP] at hl
      have hLi : Lγ (i, j) ≤ LG := Finset.single_le_sum (f := Lγ) (fun i _ => hLγ i)
        (Finset.mem_univ (i, j))
      have h1 : Q k (fun x => gammaF (lapseInv a0 gi) gi i j x -
          gammaF (lapseInv a0 gi') gi' i j x) t ≤ LG * cd * Wn k g g' t := by
        refine hl.trans ?_
        calc Lγ (i, j) * D ≤ LG * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLG
          _ = _ := by ring
      have h2 := h'.Q_V_le ht c i j
      have n1 := Q_nonneg k (fun x => gammaF (lapseInv a0 gi) gi i j x -
        gammaF (lapseInv a0 gi') gi' i j x) t
      have n2 := Q_nonneg k (pd (pd (g' c) j.succ) i.succ) t
      calc _ ≤ Ca * Q k (fun x => gammaF (lapseInv a0 gi) gi i j x -
            gammaF (lapseInv a0 gi') gi' i j x) t * Q k (pd (pd (g' c) j.succ) i.succ) t := m
        _ ≤ Ca * (LG * cd * Wn k g g' t) * K0 := by gcongr
    have hs := Q_sum_le k Finset.univ (fun i => ContDiff.sum (s := Finset.univ) fun j _ => sBij i j) t
    rw [Finset.card_univ, Fintype.card_fin] at hs
    calc Q k Bf t ≤ 3 * ∑ i : Fin 3, (3 * ∑ j : Fin 3, Ca * (LG * cd * Wn k g g' t) * K0) := by
          refine hs.trans ?_
          push_cast
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
          have hs2 := Q_sum_le k Finset.univ (fun j => sBij i j) t
          rw [Finset.card_univ, Fintype.card_fin] at hs2
          refine hs2.trans ?_
          push_cast
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hterm i j) (by norm_num)
      _ = 81 * Ca * LG * cd * K0 * Wn k g g' t := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- part C
  have hC : Q k C t ≤ LP * cd * Wn k g g' t := by
    have hl := (lψ c V V' t D (h.sV ha) (h'.sV ha) h.pV h'.pV bV bV' hD0 hDv).2
    rw [evalF_psiP, evalF_psiP] at hl
    have hLi : Lψ c ≤ LP := Finset.single_le_sum (f := Lψ) (fun i _ => hLψ i) (Finset.mem_univ c)
    refine hl.trans ?_
    calc Lψ c * D ≤ LP * (cd * Wn k g g' t) := mul_le_mul hLi hDW hD0 hLP
      _ = _ := by ring
  -- part D
  have hDd : Q k Df t ≤ 2 * Ca * Bq * Q k (fun x => S c x - S' c x) t +
      2 * Ca * cqq * Wn k g g' t * Q k (S' c) t := by
    have e : Df = fun x => lapseInv a0 gi x * (S c x - S' c x) +
        (lapseInv a0 gi x - lapseInv a0 gi' x) * S' c x := by
      funext x; simp only [Df]; ring
    rw [e]
    have sΔ : ContDiff ℝ ∞ fun x => S c x - S' c x := (h.sS c).sub (h'.sS c)
    have pΔ : IsSPeriodic fun x => S c x - S' c x := fun k' x => by
      show S c _ - S' c _ = _; rw [h.pS c k' x, h'.pS c k' x]
    have sqd : ContDiff ℝ ∞ fun x => lapseInv a0 gi x - lapseInv a0 gi' x :=
      (h.sq ha).sub (h'.sq ha)
    have pqd : IsSPeriodic fun x => lapseInv a0 gi x - lapseInv a0 gi' x := fun k' x => by
      show lapseInv a0 gi _ - lapseInv a0 gi' _ = _; rw [h.pq k' x, h'.pq k' x]
    refine (Q_add_le k ((h.sq ha).mul sΔ) (sqd.mul (h'.sS c)) t).trans ?_
    have m1 := Q_mul_le hk2 hCS hsup (h.sq ha) sΔ h.pq pΔ t
    have m2 := Q_mul_le hk2 hCS hsup sqd (h'.sS c) pqd (h'.pS c) t
    have q1 := h.Q_q_le hT ha hCS hsup ht
    have q2 := Q_q_diff_le hk h h' hT ha hCS hsup ht
    have n1 := Q_nonneg k (fun x => S c x - S' c x) t
    have n2 := Q_nonneg k (S' c) t
    have n3 := Q_nonneg k (lapseInv a0 gi) t
    have n4 := Q_nonneg k (fun x => lapseInv a0 gi x - lapseInv a0 gi' x) t
    have b1 : Ca * Q k (lapseInv a0 gi) t * Q k (fun x => S c x - S' c x) t ≤
        Ca * Bq * Q k (fun x => S c x - S' c x) t := by gcongr
    have b2 : Ca * Q k (fun x => lapseInv a0 gi x - lapseInv a0 gi' x) t * Q k (S' c) t ≤
        Ca * (cqq * Wn k g g' t) * Q k (S' c) t := by gcongr
    nlinarith
  have nA := Q_nonneg k A t
  have nB := Q_nonneg k Bf t
  have nC := Q_nonneg k C t
  have nD := Q_nonneg k Df t
  have nS := Q_nonneg k (S' c) t
  have nΔ := Q_nonneg k (fun x => S c x - S' c x) t
  have hWS : 0 ≤ Wn k g g' t * Q k (S' c) t := mul_nonneg hW nS
  calc Q k (fun x => A x + Bf x + C x + Df x) t ≤
      8 * Q k A t + 8 * Q k Bf t + 4 * Q k C t + 2 * Q k Df t := by linarith
    _ ≤ 8 * (36 * Ca * LB * cd * K0 * Wn k g g' t) + 8 * (81 * Ca * LG * cd * K0 * Wn k g g' t) +
        4 * (LP * cd * Wn k g g' t) + 2 * (2 * Ca * Bq * Q k (fun x => S c x - S' c x) t +
          2 * Ca * cqq * Wn k g g' t * Q k (S' c) t) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ 8 * (36 * Ca * LB * cd * K0) + 8 * (81 * Ca * LG * cd * K0) + 4 * (LP * cd) :=
          by positivity
        nlinarith [mul_nonneg this hWS, mul_nonneg (mul_nonneg hCa hcqq) hW]


/-! ### The shifted energy controls and is controlled by the difference norm -/

/-- **The shifted energy controls the classical norms**: for a system with the shift hypotheses
at order `k`, `Q_{k+1}(u_b) + Q_k(∂ₜu_b) ≤ (|W_{k+1}| + |W_k|) C_W E_{S,k}`. -/
theorem Q_le_energySK {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} {S : WaveSys 3 ι}
    {u F : ι → X → ℝ} {T lam lamS M : ℝ} (h : SysHyp S u F T lam M k) (hlamS : 0 < lamS)
    (hco : ∀ x : X, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ,
      lamS * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, acoef S.β S.γ i j x * ξ i * ξ j)
    (hβt : ∀ x : X, x 0 ∈ Icc 0 T → ∀ i, |pd (S.β i) 0 x| ≤ M) {t : ℝ}
    (ht : t ∈ Icc 0 T) (b : ι) :
    Q (k + 1) (u b) t + Q k (pd (u b) 0) t ≤
      ((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) *
        (ShL2Hyp.Cw (Mk k M) lamS * energySK k S.β S.γ u t) := by
  set E := ShL2Hyp.Cw (Mk k M) lamS * energySK k S.β S.γ u t
  have hsu := h.su b
  have key : ∀ v : List (Fin 3), v.length ≤ k →
      ∫ y in Icc (0 : Fin 3 → ℝ) 1, (pd (sd v (u b)) 0 (Fin.cons t y) ^ 2 +
        ∑ i : Fin 3, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 + sd v (u b) (Fin.cons t y) ^ 2) ≤
        E := fun v hv => energySK_ge k h hlamS hco hβt ht b v hv
  have cont : ∀ v : List (Fin 3), Continuous fun x => pd (sd v (u b)) 0 x ^ 2 +
      ∑ i : Fin 3, pd (sd v (u b)) i.succ x ^ 2 + sd v (u b) x ^ 2 := fun v => by
    have := fun μ => (contDiff_pd_top (contDiff_sd v hsu) μ).continuous
    have := (contDiff_sd v hsu).continuous
    fun_prop
  have mono : ∀ (v : List (Fin 3)) (G : X → ℝ), Continuous G →
      (∀ x, G x ^ 2 ≤ pd (sd v (u b)) 0 x ^ 2 + ∑ i : Fin 3, pd (sd v (u b)) i.succ x ^ 2 +
        sd v (u b) x ^ 2) → v.length ≤ k →
      ∫ y in Icc (0 : Fin 3 → ℝ) 1, G (Fin.cons t y) ^ 2 ≤ E := fun v G hG hle hv =>
    (setIntegral_mono_on (integrableOn_sq hG t) (integrableOn_slice (cont v) t) measurableSet_Icc
      fun y _ => hle _).trans (key v hv)
  have hsq : ∀ v : List (Fin 3), ∀ x, ∀ i : Fin 3, pd (sd v (u b)) i.succ x ^ 2 ≤
      pd (sd v (u b)) 0 x ^ 2 + ∑ i : Fin 3, pd (sd v (u b)) i.succ x ^ 2 + sd v (u b) x ^ 2 :=
    fun v x i => by
      have := Finset.single_le_sum (f := fun i : Fin 3 => pd (sd v (u b)) i.succ x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [sq_nonneg (pd (sd v (u b)) 0 x), sq_nonneg (sd v (u b) x)]
  have h1 : Q (k + 1) (u b) t ≤ (wordsLE 3 (k + 1)).card * E := by
    unfold Q
    calc _ ≤ ∑ _w ∈ wordsLE 3 (k + 1), E := Finset.sum_le_sum fun w hw => by
          have hw' := mem_wordsLE.mp hw
          by_cases hwk : w.length ≤ k
          · exact mono w (sd w (u b)) (contDiff_sd w hsu).continuous (fun x => by
              nlinarith [sq_nonneg (pd (sd w (u b)) 0 x), Finset.sum_nonneg fun i (_ : i ∈
                (Finset.univ : Finset (Fin 3))) => sq_nonneg (pd (sd w (u b)) i.succ x)]) hwk
          · have hne : w ≠ [] := by rintro rfl; simp at hwk
            have e := List.dropLast_append_getLast hne
            have hl : w.dropLast.length ≤ k := by simp; omega
            rw [← e, sd_append_single]
            exact mono _ _ (contDiff_pd_top (contDiff_sd _ hsu) _).continuous
              (fun x => hsq _ x _) hl
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : Q k (pd (u b) 0) t ≤ (wordsLE 3 k).card * E := by
    unfold Q
    calc _ ≤ ∑ _w ∈ wordsLE 3 k, E := Finset.sum_le_sum fun w hw => by
          rw [sd_pd_time w hsu]
          exact mono w _ (contDiff_pd_top (contDiff_sd w hsu) 0).continuous (fun x => by
            nlinarith [sq_nonneg (sd w (u b) x), Finset.sum_nonneg fun i (_ : i ∈
              (Finset.univ : Finset (Fin 3))) => sq_nonneg (pd (sd w (u b)) i.succ x)])
            (mem_wordsLE.mp hw)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc _ ≤ (wordsLE 3 (k + 1)).card * E + (wordsLE 3 k).card * E := add_le_add h1 h2
    _ = _ := by ring

/-- **The classical jets of the prolongation are controlled by the classical norms**:
`∫ Σ_p size(∂^p u) ≤ |PIdx| Σ_b (Q_k(∂ₜu_b) + 4 Q_{k+1}(u_b))`. -/
theorem int_size_le_Q {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) {u : ι → X → ℝ}
    (su : ∀ b, ContDiff ℝ ∞ (u b)) (t : ℝ) :
    ∫ y in Icc (0 : Fin 3 → ℝ) 1, size (pUK k u) (Fin.cons t y) ≤
      Fintype.card (PIdx 3 k ι) * ∑ b, (Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t) := by
  have hcomp : ∀ p, ContDiff ℝ ∞ (pUK k u p) := fun p => by
    obtain ⟨b, v, _, he⟩ := exists_sd_eq_pUK k u p
    rw [he]; exact contDiff_sd v (su b)
  set G : PIdx 3 k ι → X → ℝ := fun p x => pd (pUK k u p) 0 x ^ 2 +
    ∑ i : Fin 3, pd (pUK k u p) i.succ x ^ 2 + pUK k u p x ^ 2
  have hG : ∀ p, Continuous (G p) := fun p => by
    have := fun μ => (contDiff_pd_top (hcomp p) μ).continuous
    have := (hcomp p).continuous
    fun_prop
  have hS : ∫ y in Icc (0 : Fin 3 → ℝ) 1, size (pUK k u) (Fin.cons t y) =
      ∑ p, ∫ y in Icc (0 : Fin 3 → ℝ) 1, G p (Fin.cons t y) := by
    rw [← integral_finsetSum _ fun p _ => integrableOn_slice (hG p) t]
    rfl
  rw [hS]
  have hp : ∀ p, ∫ y in Icc (0 : Fin 3 → ℝ) 1, G p (Fin.cons t y) ≤
      ∑ b, (Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t) := by
    intro p
    obtain ⟨b, v, hv, he⟩ := exists_sd_eq_pUK k u p
    have hsb := su b
    have hcv := contDiff_sd v hsb
    have iA := integrableOn_sq (contDiff_sd v (contDiff_pd_top hsb 0)).continuous t
    have iB : ∀ i : Fin 3, IntegrableOn (fun y => pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2)
        (Icc 0 1) := fun i => integrableOn_sq (contDiff_pd_top hcv _).continuous t
    have iSm := integrable_finsetSum (s := Finset.univ) (fun i _ => iB i)
    have iC := integrableOn_sq hcv.continuous t
    have iAB : IntegrableOn (fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin 3, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2) (Icc 0 1) := by
      have c1 := (contDiff_sd v (contDiff_pd_top hsb 0)).continuous
      have c2 := fun i : Fin 3 => (contDiff_pd_top hcv i.succ).continuous
      exact integrableOn_slice (f := fun x => sd v (pd (u b) 0) x ^ 2 +
        ∑ i : Fin 3, pd (sd v (u b)) i.succ x ^ 2) (by fun_prop) t
    have eG : ∀ y : Fin 3 → ℝ, G p (Fin.cons t y) = sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin 3, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 + sd v (u b) (Fin.cons t y) ^ 2 :=
      fun y => by simp only [G, he, ← sd_pd_time v hsb]
    simp_rw [eG]
    rw [integral_add (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
        (f := fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin 3, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2)
        (g := fun y => sd v (u b) (Fin.cons t y) ^ 2) iAB iC,
      integral_add (μ := volume.restrict (Icc (0 : Fin 3 → ℝ) 1))
        (f := fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2)
        (g := fun y => ∑ i : Fin 3, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2) iA iSm,
      integral_finsetSum _ fun i _ => iB i]
    have t1 := term_le_Q hv (pd (u b) 0) t
    have t2 : ∀ i : Fin 3, ∫ y in Icc (0 : Fin 3 → ℝ) 1, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2
        ≤ Q (k + 1) (u b) t := fun i => by
      rw [← sd_append_single]; exact term_le_Q (by simp; omega) _ t
    have t3 := term_le_Q (k := k + 1) (by omega) (u b) t (w := v)
    have t2' : ∑ i : Fin 3, ∫ y in Icc (0 : Fin 3 → ℝ) 1,
        pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 ≤ 3 * Q (k + 1) (u b) t := by
      calc _ ≤ ∑ _i : Fin 3, Q (k + 1) (u b) t := Finset.sum_le_sum fun i _ => t2 i
        _ = _ := by simp
    have hb : Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t ≤
        ∑ b, (Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t) :=
      Finset.single_le_sum (f := fun b => Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t)
        (fun b _ => add_nonneg (Q_nonneg _ _ _) (mul_nonneg (by norm_num) (Q_nonneg _ _ _)))
        (Finset.mem_univ b)
    linarith
  calc ∑ p, ∫ y in Icc (0 : Fin 3 → ℝ) 1, G p (Fin.cons t y) ≤
      ∑ _p : PIdx 3 k ι, ∑ b, (Q k (pd (u b) 0) t + 4 * Q (k + 1) (u b) t) :=
        Finset.sum_le_sum fun p _ => hp p
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### The difference energy -/

/-- The differentiated wave energy of the difference with the normal-derivative multiplier
(`k = s - 2`, coefficients of `g_h`). -/
def EdiffS (k : ℕ) (a0 : ℝ) (g g' : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (t : ℝ) : ℝ :=
  energySK k (diffSys a0 gi).β (diffSys a0 gi).γ (wdiff g g') t

/-- The common data of the difference systems: `SysHyp` (vacuous `γ`-coercivity), coercivity of
`a = γ + ββ` with the uniform constant `lamA`, and `|∂ₜβ| ≤ M_diff`. -/
theorem diff_shift_hyps {k : ℕ} {lamS : ℝ} {g g' : Idx → X → ℝ}
    {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g gi S)
    (h' : MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g' gi' S') (hk : 3 ≤ k) (hT : 0 < T)
    (ha : 0 < a0) (hlamS : 0 ≤ lamS) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) :
    SysHyp (diffSys a0 gi) (wdiff g g') (fdiff a0 gi g g') T
        (-(3 * Mdiff (k + 2) CS K0 Λ a0)) (Mdiff (k + 2) CS K0 Λ a0) k ∧
      (∀ x : X, x 0 ∈ Icc 0 T → ∀ ξ : Fin 3 → ℝ, MetricHypSh.lamA lamS Λ CS K0 * ∑ i, ξ i ^ 2 ≤
        ∑ i, ∑ j, acoef (diffSys a0 gi).β (diffSys a0 gi).γ i j x * ξ i * ξ j) ∧
      (∀ x : X, x 0 ∈ Icc 0 T → ∀ i, |pd ((diffSys a0 gi).β i) 0 x| ≤
        Mdiff (k + 2) CS K0 Λ a0) := by
  have hM := h.toMetricHyp
  have hΛ : 0 ≤ Λ := le_trans ha.le (hM.Λ_pos ha hT.le)
  have hsys := diffSys_hyp_any hM h'.toMetricHyp (by omega) hT ha hCS hsup
  simp only [Nat.add_sub_cancel] at hsys
  refine ⟨hsys, fun x hx ξ => h.coer_acoef ha hlamS hCS hsup (by omega) hx ξ, fun x hx i => ?_⟩
  exact (abs_pd_beta_time hM ha hCS hsup (by omega) hT hΛ hx i).trans
    (le_add_of_nonneg_left (Cbg_nonneg _ hΛ ha))

theorem lamA_pos {lamS Λ CS K0 : ℝ} (hlamS : 0 < lamS) (hΛ : 0 < Λ) :
    0 < MetricHypSh.lamA lamS Λ CS K0 := by
  unfold MetricHypSh.lamA; positivity

theorem Λ_pos_sh {s : ℕ} {lamS : ℝ} {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ}
    {S : Idx → X → ℝ} (h : MetricHypSh Np θ s T a0 lamS Λ K0 g gi S) (ha : 0 < a0)
    (hT : 0 ≤ T) : 0 < Λ :=
  lt_of_lt_of_le ha (h.toMetricHyp.Λ_pos ha hT)

/-- **The shifted difference energy is uniformly equivalent to the squared difference norm**:
`W ≤ c_E E_{h,j}`, `E_{h,j} ≤ c_U W` and `E_{h,j} ≥ 0` on `[0, T]`. -/
theorem EdiffS_equiv {k : ℕ} {lamS : ℝ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) :
    ∃ cE cU : ℝ, 0 ≤ cE ∧ 0 ≤ cU ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g gi S →
      MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      0 ≤ EdiffS k a0 g g' gi t ∧ Wn k g g' t ≤ cE * EdiffS k a0 g g' gi t ∧
        EdiffS k a0 g g' gi t ≤ cU * Wn k g g' t := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  set Md := Mdiff (k + 2) CS K0 Λ a0
  set lA := MetricHypSh.lamA lamS Λ CS K0
  set cE0 : ℝ := 16 * (((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) * ShL2Hyp.Cw (Mk k Md) lA)
  set cU0 : ℝ := ShL2Hyp.Cu (Mk k Md) * (Fintype.card (PIdx 3 k Idx) : ℝ) * 4
  refine ⟨max cE0 0, max cU0 0, le_max_right _ _, le_max_right _ _,
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  obtain ⟨hsys, hco, hβt⟩ := diff_shift_hyps h h' hk hT ha hlamS.le hCS hsup
  have hlA : 0 < lA := lamA_pos hlamS (Λ_pos_sh h ha hT.le)
  have hE0 : 0 ≤ EdiffS k a0 g g' gi t := energySK_nonneg k hsys hlA hco hβt ht
  have hW0 := Wn_nonneg k g g' t
  refine ⟨hE0, ?_, ?_⟩
  · have hb : ∀ c, Q (k + 1) (wdiff g g' c) t + Q k (pd (wdiff g g' c) 0) t ≤
        ((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) *
          (ShL2Hyp.Cw (Mk k Md) lA * EdiffS k a0 g g' gi t) := fun c =>
      Q_le_energySK hsys hlA hco hβt ht c
    have : Wn k g g' t ≤ cE0 * EdiffS k a0 g g' gi t := by
      unfold Wn
      calc _ ≤ ∑ _c : Idx, ((wordsLE 3 (k + 1)).card + (wordsLE 3 k).card) *
            (ShL2Hyp.Cw (Mk k Md) lA * EdiffS k a0 g g' gi t) := Finset.sum_le_sum fun c _ => hb c
        _ = _ := by simp [cE0]; ring
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0)
  · have h1 := energySK_le_size k hsys hlA hco hβt ht
    have h2 := int_size_le_Q k (u := wdiff g g') hsys.su t
    have h3 : ∑ c, (Q k (pd (wdiff g g' c) 0) t + 4 * Q (k + 1) (wdiff g g' c) t) ≤
        4 * Wn k g g' t := by
      unfold Wn
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have := Q_nonneg k (pd (wdiff g g' c) 0) t
      linarith
    have hCu : 0 ≤ ShL2Hyp.Cu (Mk k Md) := ShL2Hyp.Cu_nonneg (by
      have := hsys.M_nonneg; unfold Mk; positivity)
    have : EdiffS k a0 g g' gi t ≤ cU0 * Wn k g g' t := by
      unfold EdiffS
      refine h1.trans ?_
      calc ShL2Hyp.Cu (Mk k Md) * ∫ y in Icc (0 : Fin 3 → ℝ) 1, size (pUK k (wdiff g g'))
            (Fin.cons t y) ≤ ShL2Hyp.Cu (Mk k Md) * ((Fintype.card (PIdx 3 k Idx) : ℝ) *
              (4 * Wn k g g' t)) :=
            mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
              hCu
        _ = cU0 * Wn k g g' t := by simp only [cU0]; ring
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0)

/-- **The forcing bound in energy form**: `‖F_{h,j}‖_{H^{s-2}} ≤ c_a a_{h,j} √E_{h,j} + c_σ
‖𝒮_h - 𝒮_j‖_{H^{s-2}}`. -/
theorem normK_fdiff_le_sh {k : ℕ} {lamS : ℝ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ ca cσ : ℝ, 0 ≤ ca ∧ 0 ≤ cσ ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g gi S →
      MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      normK k (fdiff a0 gi g g') t ≤
        ca * srcA k S' t * Real.sqrt (EdiffS k a0 g g' gi t) + cσ * srcD k S S' t := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hF⟩ := forcing_Q_le_sh (Np := Np) (θ := θ) (Λ := Λ)
    (lam := -(3 * Λ)) hk hT ha hθ hK0
  obtain ⟨cE, cU, hcE, hcU, hEq⟩ := EdiffS_equiv (Np := Np) (θ := θ) (Λ := Λ) (K0 := K0) hk hT ha
    hlamS
  set NP : ℝ := ((Fintype.card (PIdx 3 k Idx) : ℕ) : ℝ)
  have hNP : 0 ≤ NP := Nat.cast_nonneg _
  refine ⟨Real.sqrt (NP * c₁ * cE), Real.sqrt (NP * c₂), Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hsys := diffSys_hyp_any h.toMetricHyp h'.toMetricHyp (by omega) hT ha hCS hsup
  have hsF := hsys.sF
  refine (normK_le k hsF t).trans ?_
  obtain ⟨hE0, hWE, _⟩ := hEq g g' gi gi' S S' h h' t ht
  set E := EdiffS k a0 g g' gi t
  set W := Wn k g g' t
  set A := ∑ c, Q k (S' c) t
  set B := ∑ c, Q k (fun x => S c x - S' c x) t
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun c _ => Q_nonneg _ _ _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun c _ => Q_nonneg _ _ _
  have hW0 := Wn_nonneg k g g' t
  have hsum : ∑ c, Q k (fdiff a0 gi g g' c) t ≤ c₁ * cE * E * (16 + A) + c₂ * B := by
    calc ∑ c, Q k (fdiff a0 gi g g' c) t ≤
        ∑ c, (c₁ * W * (1 + Q k (S' c) t) + c₂ * Q k (fun x => S c x - S' c x) t) :=
          Finset.sum_le_sum fun c _ => hF g g' gi gi' S S' h.toMetricHyp h'.toMetricHyp t ht c
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
    _ = Real.sqrt (NP * c₁ * cE) * srcA k S' t * Real.sqrt E +
          Real.sqrt (NP * c₂) * srcD k S S' t := by
        unfold srcA srcD
        rw [Real.sqrt_mul (by positivity) E, Real.sqrt_mul (by positivity) (16 + A),
          Real.sqrt_mul (by positivity) B]

/-- **`eq:hyperbolic-energy` with a nonzero shift**: there is `C` (depending only on the common
constants) with
`E_{h,j}(t)^{1/2} ≤ (E_{h,j}(0)^{1/2} + C∫₀ᵗ‖𝒮ₕ - 𝒮ⱼ‖_{H^{s-2}}) exp(C∫₀ᵗ(1 + a_{h,j}))`
for all pairs and `t ∈ [0, T]`, `a_{h,j} = (16 + ‖𝒮ⱼ‖²_{H^{s-2}})^{1/2}`, `E_{h,j}` the
differentiated wave energy with the normal-derivative multiplier. -/
theorem hyperbolic_energy_sh {k : ℕ} {lamS : ℝ} (hk : 3 ≤ k) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ)
      (S S' : Idx → X → ℝ), MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g gi S →
      MetricHypSh Np θ (k + 2) T a0 lamS Λ K0 g' gi' S' → ∀ t ∈ Icc 0 T,
      Real.sqrt (EdiffS k a0 g g' gi t) ≤
        (Real.sqrt (EdiffS k a0 g g' gi 0) + C * ∫ s in (0)..t, srcD k S S' s) *
          Real.exp (C * ∫ s in (0)..t, (1 + srcA k S' s)) := by
  obtain ⟨ca, cσ, hca, hcσ, hN⟩ := normK_fdiff_le_sh (Np := Np) (θ := θ) (Λ := Λ) hk hT ha
    hlamS hθ hK0
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  set Md := Mdiff (k + 2) CS K0 Λ a0
  set lA := MetricHypSh.lamA lamS Λ CS K0
  set Kc0 := ShL2Hyp.kS (Mk k Md) lA (fun _ => mk 3 Idx k Md) 0
  refine ⟨max cσ (max (|Kc0| / 2) ca), le_max_of_le_left hcσ,
    fun g g' gi gi' S S' h h' t ht => ?_⟩
  set C := max cσ (max (|Kc0| / 2) ca)
  obtain ⟨hsys, hco, hβt⟩ := diff_shift_hyps h h' hk hT ha hlamS.le hCS hsup
  have hlA : 0 < lA := lamA_pos hlamS (Λ_pos_sh h ha hT.le)
  have hsA := continuous_srcA k h'.sS
  have hsD := continuous_srcD k h.sS h'.sS
  have hE := hkS_energy_of_forcing k hsys hlA hco hβt (a := fun s => ca * srcA k S' s)
    (σ := fun s => cσ * srcD k S S' s) (continuous_const.mul hsA) (continuous_const.mul hsD)
    (fun s => mul_nonneg hca (Real.sqrt_nonneg _)) (fun s => mul_nonneg hcσ (Real.sqrt_nonneg _))
    (fun s hs => by
      have := hN g g' gi gi' S S' h h' s hs
      show _ ≤ ca * srcA k S' s * Real.sqrt (EdiffS k a0 g g' gi s) + cσ * srcD k S S' s
      exact this) t ht
  refine hE.trans ?_
  have ht0 : 0 ≤ t := ht.1
  have hint1 : ∫ s in (0)..t, cσ * srcD k S S' s ≤ C * ∫ s in (0)..t, srcD k S S' s := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _)
  have hint2 : (∫ s in (0)..t, (ShL2Hyp.kS (Mk k Md) lA (fun _ => mk 3 Idx k Md) s +
      2 * (ca * srcA k S' s))) / 2 ≤ C * ∫ s in (0)..t, (1 + srcA k S' s) := by
    have e1 : ∫ s in (0)..t, (ShL2Hyp.kS (Mk k Md) lA (fun _ => mk 3 Idx k Md) s +
        2 * (ca * srcA k S' s)) = t * Kc0 + 2 * ca * ∫ s in (0)..t, srcA k S' s := by
      have hkc : ∀ s, ShL2Hyp.kS (Mk k Md) lA (fun _ => mk 3 Idx k Md) s = Kc0 := fun s => rfl
      simp only [hkc]
      rw [intervalIntegral.integral_add (f := fun _ => Kc0)
        (g := fun s => 2 * (ca * srcA k S' s)) (continuous_const.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_const.mul hsA)).intervalIntegrable _ _)]
      rw [show (fun s => 2 * (ca * srcA k S' s)) = fun s => (2 * ca) * srcA k S' s from
        funext fun s => by ring, intervalIntegral.integral_const_mul]
      simp
    have e2 : ∫ s in (0)..t, (1 + srcA k S' s) = t + ∫ s in (0)..t, srcA k S' s := by
      rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
        (hsA.intervalIntegrable _ _)]
      simp
    rw [e1, e2]
    have hIA : 0 ≤ ∫ s in (0)..t, srcA k S' s :=
      intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _
    have h1 : t * Kc0 / 2 ≤ C * t := by
      have : Kc0 / 2 ≤ C := le_trans (by
        have := le_abs_self Kc0; linarith) (le_max_of_le_right (le_max_left _ _))
      nlinarith
    have h2 : ca * ∫ s in (0)..t, srcA k S' s ≤ C * ∫ s in (0)..t, srcA k S' s :=
      mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) hIA
    nlinarith
  have hX : 0 ≤ Real.sqrt (energySK k (diffSys a0 gi).β (diffSys a0 gi).γ (wdiff g g') 0) +
      ∫ s in (0)..t, cσ * srcD k S S' s :=
    add_nonneg (Real.sqrt_nonneg _) (intervalIntegral.integral_nonneg ht0 fun s _ =>
      mul_nonneg hcσ (Real.sqrt_nonneg _))
  refine mul_le_mul (by unfold EdiffS; linarith) (Real.exp_le_exp.2 hint2) (Real.exp_pos _).le ?_
  have hI : 0 ≤ ∫ s in (0)..t, srcD k S S' s :=
    intervalIntegral.integral_nonneg ht0 fun s _ => Real.sqrt_nonneg _
  have hC : 0 ≤ C := le_max_of_le_left hcσ
  exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC hI)

/-- **`thm:hyperbolic`, the first two limits (Cauchy form), with the paper's hyperbolicity
hypothesis** (common time function, uniformly spacelike slices, any bounded shift): Cauchy
initial data in `H^{s-1} × H^{s-2}` and Cauchy sources in `L¹_tH^{s-2}` make `(g_h)` Cauchy in
`C_tH^{s-1}` and `(∂ₜg_h)` Cauchy in `C_tH^{s-2}` on `[0, T]`. -/
theorem common_slab_cauchy_sh {s : ℕ} {lamS : ℝ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0)
    (hlamS : 0 < lamS) {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ}
    {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
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
  have hK0 := (hg 0).toMetricHyp.K0_nonneg hT.le
  obtain ⟨ca, cσ, hca, hcσ, hN⟩ := normK_fdiff_le_sh (Np := Np) (θ := θ) (Λ := Λ) hk hT ha
    hlamS hθ hK0
  obtain ⟨cE, cU, hcE, hcU, hEq⟩ := EdiffS_equiv (Np := Np) (θ := θ) (Λ := Λ) (K0 := K0) hk hT ha
    hlamS
  obtain ⟨BS, hBS⟩ := sources_bounded (k := k) (fun h => (hg h).sS) hsrc hT.le
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hall := fun i j => diff_shift_hyps (hg i) (hg j) hk hT ha hlamS.le hCS hsup
  have hlA : 0 < MetricHypSh.lamA lamS Λ CS K0 := lamA_pos hlamS (Λ_pos_sh (hg 0) ha hT.le)
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
  have h0 : Tendsto (fun p : ℕ × ℕ => energySK k (diffSys a0 (gi p.1)).β (diffSys a0 (gi p.1)).γ
      (wdiff (g p.1) (g p.2)) 0) atTop (𝓝 0) := by
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
  have hmain := energySK_tendsto_zero k (fun i j => (hall i j).1) hlA hT.le
    (fun i j => (hall i j).2.1) (fun i j => (hall i j).2.2)
    (a := fun i j t => ca * srcA k (S j) t)
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
  have h2 : EdiffS k a0 (g p.1) (g p.2) (gi p.1) t ≤ ε / (cE + 1) := by
    have h3 := Real.sq_sqrt hE0
    have h4 := Real.sq_sqrt (show 0 ≤ ε / (cE + 1) by positivity)
    unfold EdiffS at h3 ⊢
    nlinarith [Real.sqrt_nonneg (energySK k (diffSys a0 (gi p.1)).β (diffSys a0 (gi p.1)).γ
      (wdiff (g p.1) (g p.2)) t)]
  calc Wn k (g p.1) (g p.2) t ≤ cE * EdiffS k a0 (g p.1) (g p.2) (gi p.1) t := hWE
    _ ≤ cE * (ε / (cE + 1)) := mul_le_mul_of_nonneg_left h2 hcE
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

/-! ### Non-vacuity: a constant metric with a large shift -/

/-- The constant metric `g = -dt² + (dx¹ + 2dt)² + (dx²)² + (dx³)²` (lapse `1`, shift `β = (2,0,0)`,
`g₀₀ = 3 > 0`: `∂ₜ` is spacelike). -/
def gShift (c : Idx) (_ : X) : ℝ :=
  if c = (0, 0) then 3 else if c = (0, 1) ∨ c = (1, 0) then 2 else if c.1 = c.2 then 1 else 0

/-- Its inverse: `g^{00} = -1`, `g^{01} = 2`, `g^{11} = -3`, `g^{22} = g^{33} = 1`. -/
def giShift (a b : Fin 4) (_ : X) : ℝ :=
  if (a, b) = (0, 0) then -1 else if (a, b) = (0, 1) ∨ (a, b) = (1, 0) then 2 else
    if (a, b) = (1, 1) then -3 else if a = b then 1 else 0

/-- **The shifted constant metric satisfies the paper's hypotheses** (`MetricHypSh`, zero
nonlinearity and source, `a₀ = λ_S = 1`, `Λ = 3`, `K₀ = 9`). -/
theorem shifted_metricHypSh (s : ℕ) (T : ℝ) :
    MetricHypSh (κ := Empty) (fun _ => 0) (fun j => j.elim) s T 1 1 3 9 gShift giShift
      (fun _ _ => 0) where
  sg := fun _ => contDiff_const
  sgi := fun _ _ => contDiff_const
  sS := fun _ => contDiff_const
  sθ := fun j => j.elim
  pg := fun _ => isSPeriodic_const _
  pgi := fun _ _ => isSPeriodic_const _
  pS := fun _ => isSPeriodic_const _
  pθ := fun j => j.elim
  symm := fun x _ a b => by
    fin_cases a <;> fin_cases b <;> simp [gShift]
  inv := fun x _ a b => by
    fin_cases a <;> fin_cases b <;> simp [gShift, giShift, Fin.sum_univ_four] <;> norm_num
  hyp0 := fun x _ => by simp [giShift]
  slices := fun x _ ξ => by
    simp only [gShift, Fin.sum_univ_three]
    simp
    nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
  bnd := fun x _ a b => by
    fin_cases a <;> fin_cases b <;> simp [giShift] <;> norm_num
  hsg := fun t _ c => by
    show Q s (fun _ => gShift c 0) t ≤ 9
    rw [Q_const]
    unfold gShift; split_ifs <;> norm_num
  hst := fun t _ c => by
    show Q (s - 1) (pd (fun _ => gShift c 0) 0) t ≤ 9
    rw [pd_const_fun, Q_const]; norm_num
  eqn := fun x _ c => by
    have : ∀ α β : Fin 4, pd (pd (gShift c) β) α x = 0 := fun α β => by
      show pd (pd (fun _ => gShift c 0) β) α x = 0
      rw [pd_const_fun, pd_const_fun]
    simp [this, Nfield, evalF]

/-- **The shifted metric violates the earlier rendering**: no `MetricHyp` with `λ > 0` (positive
`g^{ij}`) holds for it, since `g^{11} = -3`. -/
theorem shifted_not_metricHyp (s : ℕ) {T : ℝ} (hT : 0 ≤ T) {a0 lam Λ K0 : ℝ} (hlam : 0 < lam) :
    ¬ MetricHyp (κ := Empty) (fun _ => 0) (fun j => j.elim) s T a0 lam Λ K0 gShift giShift
      (fun _ _ => 0) := by
  intro h
  have hx : (Fin.cons 0 0 : X) 0 ∈ Icc 0 T := by simp [hT]
  have := h.hypS _ hx (fun i => if i = 0 then 1 else 0)
  simp [giShift] at this
  linarith

/-- Non-vacuity of `common_slab_cauchy_sh` with a genuinely shifted metric (`∂ₜ` spacelike). -/
example (T : ℝ) (hT : 0 < T) :=
  common_slab_cauchy_sh (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => gShift) (gi := fun _ => giShift) (S := fun _ _ _ => 0)
    (fun _ => shifted_metricHypSh 5 T) (by simp [Q_const]) (by simp [Q_const])

end RenewalGeometry.ReducedWaveShift
