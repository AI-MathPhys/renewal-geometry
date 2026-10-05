/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabData

/-!
# The difference system of two solutions of the reduced wave system

For two metrics `g_h, g_j` satisfying the hypotheses of `thm:hyperbolic`
(`ReducedWaveStab.MetricHyp`, common constants), the difference `w = g_h - g_j` solves the linear
system `∂ₜ²w = 2βₕⁱ∂ᵢ∂ₜw + γₕ^{ij}∂ᵢ∂ⱼw + F` with the principal coefficients of `g_h` and the
forcing (`fdiff_eq`, on the slab)

`F = 2(βₕ - βⱼ)ⁱ∂ᵢ∂ₜgⱼ + (γₕ - γⱼ)^{ij}∂ᵢ∂ⱼgⱼ + (qₕ𝒩ₕ - qⱼ𝒩ⱼ) + (qₕ𝒮ₕ - qⱼ𝒮ⱼ)`

(`q = 1/g^{00}`), exactly the forcing of the manuscript's proof divided by `-g_h^{00}`.

* `diffSys_hyp` — the difference system satisfies the hypotheses `SlabWaveHk.SysHyp` of the
  linear `H^{s-2}` energy estimate, with constants depending only on the common constants.
* `Vfam`, `betaP`, `gammaP`, `psiP` — the coefficients `β, γ` and `q𝒩` are polynomial
  expressions in `(q, g⁻¹, g, ∂g, θ)` (`evalF_betaP`, …).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- The difference system: principal coefficients of `g_h`, zero lower-order part. -/
def diffSys (a0 : ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) : WaveSys 3 Idx :=
  ⟨betaF (lapseInv a0 gi) gi, gammaF (lapseInv a0 gi) gi, fun _ _ _ => 0, fun _ _ _ _ => 0,
    fun _ _ _ => 0⟩

/-- The difference of two metrics. -/
def wdiff (g g' : Idx → X → ℝ) : Idx → X → ℝ := fun c x => g c x - g' c x

/-- The forcing of the difference system. -/
def fdiff (a0 : ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (g g' : Idx → X → ℝ) : Idx → X → ℝ :=
  fun c x => pd (pd (wdiff g g' c) 0) 0 x - (diffSys a0 gi).princ (wdiff g g') c x

theorem lower_diffSys (a0 : ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (u : Idx → X → ℝ) (c : Idx)
    (x : X) : (diffSys a0 gi).lower u c x = 0 := by
  simp [WaveSys.lower, diffSys]

theorem contDiff_wdiff {g g' : Idx → X → ℝ} (hg : ∀ c, ContDiff ℝ ∞ (g c))
    (hg' : ∀ c, ContDiff ℝ ∞ (g' c)) (c : Idx) : ContDiff ℝ ∞ (wdiff g g' c) :=
  (hg c).sub (hg' c)

theorem pd_wdiff {g g' : Idx → X → ℝ} (hg : ∀ c, ContDiff ℝ ∞ (g c))
    (hg' : ∀ c, ContDiff ℝ ∞ (g' c)) (c : Idx) (μ : Fin 4) :
    pd (wdiff g g' c) μ = fun x => pd (g c) μ x - pd (g' c) μ x := by
  have := pd_lincomb (hg c) (hg' c) 1 (-1) μ
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

theorem pd_pd_wdiff {g g' : Idx → X → ℝ} (hg : ∀ c, ContDiff ℝ ∞ (g c))
    (hg' : ∀ c, ContDiff ℝ ∞ (g' c)) (c : Idx) (μ ν : Fin 4) :
    pd (pd (wdiff g g' c) μ) ν = fun x => pd (pd (g c) μ) ν x - pd (pd (g' c) μ) ν x := by
  rw [pd_wdiff hg hg' c μ]
  have := pd_lincomb (contDiff_pd_top (hg c) μ) (contDiff_pd_top (hg' c) μ) 1 (-1) ν
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

/-- The algebra of the difference forcing. -/
theorem diff_alg (tth ttj Rh Rj : ℝ) (βh βj Uh Uj : Fin 3 → ℝ) (γh γj Vh Vj : Fin 3 → Fin 3 → ℝ)
    (hh : tth = 2 * ∑ i, βh i * Uh i + ∑ i, ∑ j, γh i j * Vh i j + Rh)
    (hj : ttj = 2 * ∑ i, βj i * Uj i + ∑ i, ∑ j, γj i j * Vj i j + Rj) :
    (tth - ttj) - (2 * ∑ i, βh i * (Uh i - Uj i) + ∑ i, ∑ j, γh i j * (Vh i j - Vj i j)) =
      2 * ∑ i, (βh i - βj i) * Uj i + ∑ i, ∑ j, (γh i j - γj i j) * Vj i j + (Rh - Rj) := by
  have e1 : ∑ i, βh i * (Uh i - Uj i) = ∑ i, βh i * Uh i - ∑ i, βh i * Uj i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (βh i - βj i) * Uj i = ∑ i, βh i * Uj i - ∑ i, βj i * Uj i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ j, γh i j * (Vh i j - Vj i j) =
      ∑ i, ∑ j, γh i j * Vh i j - ∑ i, ∑ j, γh i j * Vj i j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ i, ∑ j, (γh i j - γj i j) * Vj i j =
      ∑ i, ∑ j, γh i j * Vj i j - ∑ i, ∑ j, γj i j * Vj i j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, e4, hh, hj]
  ring

/-- `q𝒩` as a field. -/
def psiF (a0 : ℝ) (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ) (g : Idx → X → ℝ)
    (gi : Fin 4 → Fin 4 → X → ℝ) (c : Idx) (x : X) : ℝ :=
  lapseInv a0 gi x * Nfield Np θ g gi c x

/-- The decomposed forcing. -/
def fdec (a0 : ℝ) (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ)
    (g g' : Idx → X → ℝ) (gi gi' : Fin 4 → Fin 4 → X → ℝ) (S S' : Idx → X → ℝ) (c : Idx)
    (x : X) : ℝ :=
  2 * ∑ i : Fin 3, (betaF (lapseInv a0 gi) gi i x - betaF (lapseInv a0 gi') gi' i x) *
      pd (pd (g' c) 0) i.succ x +
    ∑ i : Fin 3, ∑ j : Fin 3,
      (gammaF (lapseInv a0 gi) gi i j x - gammaF (lapseInv a0 gi') gi' i j x) *
        pd (pd (g' c) j.succ) i.succ x +
    (psiF a0 Np θ g gi c x - psiF a0 Np θ g' gi' c x) +
    (lapseInv a0 gi x * S c x - lapseInv a0 gi' x * S' c x)

variable {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ} {s : ℕ} {T a0 lam Λ K0 : ℝ}

/-- **The difference forcing on the slab** (`thm:hyperbolic`, proof). -/
theorem fdiff_eq {g g' : Idx → X → ℝ} {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (h' : MetricHyp Np θ s T a0 lam Λ K0 g' gi' S')
    (ha : 0 < a0) {x : X} (hx : x 0 ∈ Icc 0 T) (c : Idx) :
    fdiff a0 gi g g' c x = fdec a0 Np θ g g' gi gi' S S' c x := by
  unfold fdiff fdec WaveSys.princ diffSys
  simp only
  rw [pd_pd_wdiff h.sg h'.sg c 0 0]
  simp only [pd_pd_wdiff h.sg h'.sg c 0, pd_pd_wdiff h.sg h'.sg c]
  have := diff_alg _ _ _ _ _ _ _ _ _ _ _ _ (h.normal_form ha hx c) (h'.normal_form ha hx c)
  rw [this]
  unfold psiF
  ring

/-! ### The variables of the coefficient polynomials -/

/-- The variables `(q, g⁻¹, g, ∂g, θ)`. -/
def Vfam (a0 : ℝ) (θ : κ → X → ℝ) (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) :
    Option (NV κ) → X → ℝ
  | none => lapseInv a0 gi
  | some v => nvals g gi θ v

/-- The polynomial of `βⁱ`. -/
def betaP (i : Fin 3) : MvPolynomial (Option (NV κ)) ℝ :=
  MvPolynomial.C (-(1 / 2)) * (MvPolynomial.X none *
    (MvPolynomial.X (some (.inl (0, i.succ))) + MvPolynomial.X (some (.inl (i.succ, 0)))))

/-- The polynomial of `γ^{ij}`. -/
def gammaP (i j : Fin 3) : MvPolynomial (Option (NV κ)) ℝ :=
  MvPolynomial.C (-(1 / 2)) * (MvPolynomial.X none *
    (MvPolynomial.X (some (.inl (i.succ, j.succ))) + MvPolynomial.X (some (.inl (j.succ, i.succ)))))

/-- The polynomial of `q𝒩_c`. -/
def psiP (Np : Idx → MvPolynomial (NV κ) ℝ) (c : Idx) : MvPolynomial (Option (NV κ)) ℝ :=
  MvPolynomial.X none * MvPolynomial.rename some (Np c)

theorem evalF_betaP (a0 : ℝ) (θ : κ → X → ℝ) (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ)
    (i : Fin 3) : evalF (Vfam a0 θ g gi) (betaP i) = betaF (lapseInv a0 gi) gi i := by
  funext x; simp [evalF, betaP, betaF, Vfam, nvals]

theorem evalF_gammaP (a0 : ℝ) (θ : κ → X → ℝ) (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ)
    (i j : Fin 3) : evalF (Vfam a0 θ g gi) (gammaP i j) = gammaF (lapseInv a0 gi) gi i j := by
  funext x; simp [evalF, gammaP, gammaF, Vfam, nvals]

theorem evalF_psiP (a0 : ℝ) (Np : Idx → MvPolynomial (NV κ) ℝ) (θ : κ → X → ℝ)
    (g : Idx → X → ℝ) (gi : Fin 4 → Fin 4 → X → ℝ) (c : Idx) :
    evalF (Vfam a0 θ g gi) (psiP Np c) = psiF a0 Np θ g gi c := by
  funext x
  simp only [evalF, psiP, psiF, Nfield, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  rfl

namespace MetricHyp

variable {g : Idx → X → ℝ} {gi : Fin 4 → Fin 4 → X → ℝ} {S : Idx → X → ℝ}

theorem sV (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) :
    ∀ v, ContDiff ℝ ∞ (Vfam a0 θ g gi v)
  | none => h.sq ha
  | some (.inl _) => h.sgi _ _
  | some (.inr (.inl c)) => h.sg c
  | some (.inr (.inr (.inl _))) => contDiff_pd_top (h.sg _) _
  | some (.inr (.inr (.inr j))) => h.sθ j

theorem pV (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) :
    ∀ v, IsSPeriodic (Vfam a0 θ g gi v)
  | none => h.pq
  | some (.inl _) => h.pgi _ _
  | some (.inr (.inl c)) => h.pg c
  | some (.inr (.inr (.inl _))) => isSPeriodic_pd (h.pg _) _
  | some (.inr (.inr (.inr j))) => h.pθ j

theorem spsi (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (ha : 0 < a0) (c : Idx) :
    ContDiff ℝ ∞ (psiF a0 Np θ g gi c) := (h.sq ha).mul (h.sN c)

end MetricHyp

/-! ### The difference system satisfies the hypotheses of the linear estimate -/

/-- The coefficient bound of the difference system. -/
def Mdiff (s : ℕ) (CS K0 Λ a0 : ℝ) : ℝ := MetricHyp.Cbg s CS K0 Λ a0 + MetricHyp.Ct CS K0 Λ a0

theorem Cbg_nonneg (s : ℕ) {CS K0 Λ a0 : ℝ} (hΛ : 0 ≤ Λ) (ha : 0 < a0) :
    0 ≤ MetricHyp.Cbg s CS K0 Λ a0 := by
  unfold MetricHyp.Cbg
  have h1 : 0 ≤ MetricHyp.Cgi s CS K0 Λ := invC_nonneg 4 hΛ _
  have h2 : 0 ≤ MetricHyp.Cq s CS K0 Λ a0 := invC_nonneg 1 (by positivity) _
  positivity

theorem Ct_nonneg {CS K0 Λ a0 : ℝ} (ha : 0 < a0) (hΛ : 0 ≤ Λ) : 0 ≤ MetricHyp.Ct CS K0 Λ a0 := by
  unfold MetricHyp.Ct
  have := Real.sqrt_nonneg (CS * K0)
  positivity

/-- **The difference system satisfies `SysHyp` at order `s - 2`** with coercivity `λ/Λ` and the
coefficient bound `Mdiff`. -/
theorem diffSys_hyp {g g' : Idx → X → ℝ} {gi gi' : Fin 4 → Fin 4 → X → ℝ} {S S' : Idx → X → ℝ}
    (h : MetricHyp Np θ s T a0 lam Λ K0 g gi S) (h' : MetricHyp Np θ s T a0 lam Λ K0 g' gi' S')
    (hs : 3 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 ≤ lam) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) :
    SysHyp (diffSys a0 gi) (wdiff g g') (fdiff a0 gi g g') T (lam / Λ) (Mdiff s CS K0 Λ a0)
      (s - 2) := by
  have hΛ : 0 ≤ Λ := le_trans ha.le (h.Λ_pos ha hT.le)
  have hM1 : MetricHyp.Cbg s CS K0 Λ a0 ≤ Mdiff s CS K0 Λ a0 := le_add_of_nonneg_right (Ct_nonneg ha hΛ)
  have hM2 : MetricHyp.Ct CS K0 Λ a0 ≤ Mdiff s CS K0 Λ a0 := le_add_of_nonneg_left (Cbg_nonneg s hΛ ha)
  have hM0 : 0 ≤ Mdiff s CS K0 Λ a0 := add_nonneg (Cbg_nonneg s hΛ ha) (Ct_nonneg ha hΛ)
  have sw := contDiff_wdiff h.sg h'.sg
  have hs2 : 1 ≤ s - 2 := by omega
  refine
    { su := sw
      sF := fun c => ?_
      sβ := h.sbeta ha
      sγ := h.sgamma ha
      sA := fun _ _ => contDiff_const
      sB := fun _ _ _ => contDiff_const
      sC := fun _ _ => contDiff_const
      pu := fun c k x => by simp only [wdiff, h.pg c k x, h'.pg c k x]
      pF := fun c => ?_
      pβ := h.pbeta
      pγ := h.pgamma
      pA := fun _ _ => isSPeriodic_const 0
      pB := fun _ _ _ => isSPeriodic_const 0
      pC := fun _ _ => isSPeriodic_const 0
      eqn := fun x _ c => by
        rw [lower_diffSys]; unfold fdiff; ring
      γ_symm := fun i j x => gammaF_symm _ _ i j x
      coer := fun x hx ξ => h.coer_gamma ha hlam hx ξ
      M_nonneg := hM0
      bβ := fun i => (h.derivBound_beta ha hCS hsup (by omega) hΛ i).mono hM1
      bγ := fun i j => (h.derivBound_gamma ha hCS hsup (by omega) hΛ i j).mono hM1
      bA := fun _ _ => DerivBound.zero hM0
      bB := fun _ _ _ => DerivBound.zero hM0
      bC := fun _ _ => DerivBound.zero hM0
      bβx := fun x hx i j => ?_
      bγ1 := fun x hx i j μ => ?_ }
  · unfold fdiff WaveSys.princ diffSys
    have h1 := contDiff_pd_top (contDiff_pd_top (sw c) 0) 0
    have h2 : ContDiff ℝ ∞ fun x => 2 * ∑ i : Fin 3, betaF (lapseInv a0 gi) gi i x *
        pd (pd (wdiff g g' c) 0) i.succ x :=
      contDiff_const.mul (ContDiff.sum fun i _ => (h.sbeta ha i).mul
        (contDiff_pd_top (contDiff_pd_top (sw c) 0) _))
    have h3 : ContDiff ℝ ∞ fun x => ∑ i : Fin 3, ∑ j : Fin 3, gammaF (lapseInv a0 gi) gi i j x *
        pd (pd (wdiff g g' c) j.succ) i.succ x :=
      ContDiff.sum fun i _ => ContDiff.sum fun j _ => (h.sgamma ha i j).mul
        (contDiff_pd_top (contDiff_pd_top (sw c) _) _)
    exact h1.sub (h2.add h3)
  · have pw : IsSPeriodic (wdiff g g' c) := fun k x => by
      simp only [wdiff, h.pg c k x, h'.pg c k x]
    intro k x
    unfold fdiff WaveSys.princ diffSys
    simp only [isSPeriodic_pd (isSPeriodic_pd pw 0) 0 k x, h.pbeta _ k x, h.pgamma _ _ k x,
      fun i => isSPeriodic_pd (isSPeriodic_pd pw 0) (Fin.succ i) k x,
      fun i j => isSPeriodic_pd (isSPeriodic_pd pw (Fin.succ j)) (Fin.succ i) k x]
  · exact ((h.derivBound_beta ha hCS hsup (by omega) hΛ i) [j] (by simp; omega) x hx).trans hM1
  · induction μ using Fin.cases with
    | zero => exact (h.abs_pd_gamma_time ha hCS hsup hs hT hΛ hx i j).trans hM2
    | succ k =>
      exact ((h.derivBound_gamma ha hCS hsup (by omega) hΛ i j) [k] (by simp; omega) x hx).trans
        hM1

end ReducedWaveStab

end RenewalGeometry
