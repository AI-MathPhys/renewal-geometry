/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallLieCoordinates
import RenewalGeometry.Analysis.BallLinearizedCoulombIso

/-!
# The Coulomb gauge map on `H^s(B)` and its linearisation
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For a `𝔤`-valued connection `A = Σ a^b e_b` with coefficients `a ∈ H⁴(B)` and a `𝔤`-valued
infinitesimal gauge `ξ = Σ ξ^a e_a ∈ H⁵(B)`:
* `gaugeAct L a ξ` — the gauge transform `g A g⁻¹ - (∂g) g⁻¹`, `g = exp ξ` (Banach-algebra
  exponential of `H⁵(B, M_m(ℂ))`);
* `coulF L (a, ξ) = κ (d^*(g·A))` — the Coulomb functional in coordinates (`H³(B)^d`);
* `contDiff_coulF` — it is `C^∞` (the exponential is analytic);
* `hasFDerivAt_coulF_snd` — its partial derivative in `ξ` at `ξ = 0` is
  `η ↦ κ(Σ_μ ∂_μ([η, A_μ] - ∂_μ η))`, and `coulF_deriv_eq_linOpS` identifies it with
  `-linOpS (brkCoef L a)`, the linearised Coulomb operator of `BallLinearizedCoulombIso`.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

section GaugeMap

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-- **The gauge action** `g·A = g A g⁻¹ - (∂g) g⁻¹` with `g = exp ξ`, `ξ = Σ ξ^a e_a`,
`A_μ = Σ a_μ^b e_b`. -/
def gaugeAct (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4)
    (ξ : Fin d → SobAlg c r 5) (μ : Fin 4) : MatSob c r 4 m :=
  rhoML (exp (embX L ξ)) * embX L (a μ) * rhoML (exp (-embX L ξ)) -
    derM μ (exp (embX L ξ)) * rhoML (exp (-embX L ξ))

/-- **The Coulomb functional** `(a, ξ) ↦ κ(Σ_μ ∂_μ (g·A)_μ)`. -/
def coulF (L : LieBasis m d) (p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5)) :
    Fin d → SobAlg c r 3 :=
  coordL L (∑ μ, derM μ (gaugeAct L p.1 p.2 μ))

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_exp_matSob {s : ℕ} [Fact (3 ≤ s)] :
    ContDiff ℝ ∞ (exp : MatSob c r s m → MatSob c r s m) :=
  AnalyticOnNhd.contDiff fun x _ => NormedSpace.exp_analytic x

set_option backward.isDefEq.respectTransparency false in
/-- **The Coulomb functional is `C^∞`.** -/
theorem contDiff_coulF (L : LieBasis m d) : ContDiff ℝ ∞ (coulF (c := c) (r := r) L) := by
  have hE5 := (embXL (c := c) (r := r) (s := 5) (m := m) L).contDiff (n := ∞)
  have hE4 := (embXL (c := c) (r := r) (s := 4) (m := m) L).contDiff (n := ∞)
  have hρ := (rhoML (c := c) (r := r) (s := 4) (m := m)).contDiff (n := ∞)
  have hD4 : ∀ μ, ContDiff ℝ ∞ (derM (c := c) (r := r) (s := 4) (m := m) μ) := fun μ =>
    (derM (c := c) (r := r) (s := 4) (m := m) μ).contDiff
  have hD3 : ∀ μ, ContDiff ℝ ∞ (derM (c := c) (r := r) (s := 3) (m := m) μ) := fun μ =>
    (derM (c := c) (r := r) (s := 3) (m := m) μ).contDiff
  have hK := (coordL (c := c) (r := r) (s := 3) (m := m) L).contDiff (n := ∞)
  have hX : ContDiff ℝ ∞ fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      embX L p.2 := hE5.comp contDiff_snd
  have hg : ContDiff ℝ ∞ fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      exp (embX L p.2) := contDiff_exp_matSob.comp hX
  have hh : ContDiff ℝ ∞ fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      exp (-embX L p.2) := contDiff_exp_matSob.comp hX.neg
  have hA : ∀ μ, ContDiff ℝ ∞ fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      embX L (p.1 μ) := fun μ => hE4.comp ((contDiff_apply ℝ _ μ).comp contDiff_fst)
  have hG : ∀ μ, ContDiff ℝ ∞ fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      gaugeAct L p.1 p.2 μ := fun μ => by
    unfold gaugeAct
    exact (((hρ.comp hg).mul (hA μ)).mul (hρ.comp hh)).sub (((hD4 μ).comp hg).mul (hρ.comp hh))
  unfold coulF
  exact hK.comp (ContDiff.sum fun μ _ => (hD3 μ).comp (hG μ))

/-- The linearised gauge action at `ξ = 0`: `η ↦ [η, A_μ] - ∂_μ η`. -/
def linActL (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (μ : Fin 4) :
    (Fin d → SobAlg c r 5) →L[ℝ] MatSob c r 4 m :=
  ((ContinuousLinearMap.mul ℝ (MatSob c r 4 m)).flip (embX L (a μ))).comp
      ((rhoML (s := 4)).comp (embXL L)) -
    ((ContinuousLinearMap.mul ℝ (MatSob c r 4 m)) (embX L (a μ))).comp
      ((rhoML (s := 4)).comp (embXL L)) - (derM (s := 4) μ).comp (embXL L)

theorem linActL_apply (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (μ : Fin 4)
    (η : Fin d → SobAlg c r 5) :
    linActL L a μ η = rhoML (embX L η) * embX L (a μ) - embX L (a μ) * rhoML (embX L η) -
      derM μ (embX L η) := rfl

/-- The partial derivative of the Coulomb functional at `ξ = 0`. -/
def coulD (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    (Fin d → SobAlg c r 5) →L[ℝ] (Fin d → SobAlg c r 3) :=
  (coordL L).comp (∑ μ, (derM (s := 3) μ).comp (linActL L a μ))

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_exp_embX (L : LieBasis m d) :
    HasFDerivAt (fun ξ : Fin d → SobAlg c r 5 => exp (embX L ξ))
      (embXL (c := c) (r := r) (s := 5) (m := m) L) 0 := by
  have h := (hasStrictFDerivAt_exp_matSob_zero (c := c) (r := r) (s := 5) (m := m)).hasFDerivAt
  have h' : HasFDerivAt exp (1 : MatSob c r 5 m →L[ℝ] MatSob c r 5 m)
      ((embXL (c := c) (r := r) (s := 5) (m := m) L) 0) := by rw [map_zero]; exact h
  have := h'.comp (0 : Fin d → SobAlg c r 5) (embXL (c := c) (r := r) (s := 5) (m := m) L).hasFDerivAt
  have e1 : (1 : MatSob c r 5 m →L[ℝ] MatSob c r 5 m).comp
      (embXL (c := c) (r := r) (s := 5) (m := m) L) = embXL L := by
    ext1 u; rfl
  rw [e1] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_exp_neg_embX (L : LieBasis m d) :
    HasFDerivAt (fun ξ : Fin d → SobAlg c r 5 => exp (-embX L ξ))
      (-embXL (c := c) (r := r) (s := 5) (m := m) L) 0 := by
  have h := (hasStrictFDerivAt_exp_matSob_zero (c := c) (r := r) (s := 5) (m := m)).hasFDerivAt
  have h' : HasFDerivAt exp (1 : MatSob c r 5 m →L[ℝ] MatSob c r 5 m)
      ((-embXL (c := c) (r := r) (s := 5) (m := m) L) 0) := by rw [map_zero]; exact h
  have := h'.comp (0 : Fin d → SobAlg c r 5)
    (-embXL (c := c) (r := r) (s := 5) (m := m) L).hasFDerivAt
  have e1 : (1 : MatSob c r 5 m →L[ℝ] MatSob c r 5 m).comp
      (-embXL (c := c) (r := r) (s := 5) (m := m) L) =
        -embXL (c := c) (r := r) (s := 5) (m := m) L := by
    ext1 u; rfl
  rw [e1] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- **The partial derivative of the gauge action at `ξ = 0`.** -/
theorem hasFDerivAt_gaugeAct (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) (μ : Fin 4) :
    HasFDerivAt (fun ξ => gaugeAct L a ξ μ) (linActL L a μ) 0 := by
  have hg := hasFDerivAt_exp_embX (c := c) (r := r) (m := m) L
  have hh := hasFDerivAt_exp_neg_embX (c := c) (r := r) (m := m) L
  have hρg := (rhoML (c := c) (r := r) (s := 4) (m := m)).hasFDerivAt.comp _ hg
  have hρh := (rhoML (c := c) (r := r) (s := 4) (m := m)).hasFDerivAt.comp _ hh
  have hdg := (derM (c := c) (r := r) (s := 4) (m := m) μ).hasFDerivAt.comp _ hg
  have hA : HasFDerivAt (fun _ : Fin d → SobAlg c r 5 => embX L (a μ))
      (0 : (Fin d → SobAlg c r 5) →L[ℝ] MatSob c r 4 m) 0 := hasFDerivAt_const _ _
  have h1 := ((hρg.mul' hA).mul' hρh).sub (hdg.mul' hρh)
  have hval0 : exp (embX L (0 : Fin d → SobAlg c r 5)) = (1 : MatSob c r 5 m) := by
    rw [show embX L (0 : Fin d → SobAlg c r 5) = (0 : MatSob c r 5 m) from map_zero (embXL L),
      exp_zero]
  have hval1 : exp (-embX L (0 : Fin d → SobAlg c r 5)) = (1 : MatSob c r 5 m) := by
    rw [show embX L (0 : Fin d → SobAlg c r 5) = (0 : MatSob c r 5 m) from map_zero (embXL L),
      neg_zero, exp_zero]
  refine h1.congr_fderiv ?_
  ext1 η
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    hval0, hval1, linActL_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  have hρ1 : rhoML (1 : MatSob c r 5 m) = 1 := (rhoML_eq 1).trans (map_one _)
  simp only [Pi.mul_apply, Function.comp_apply, hval0, hval1, hρ1, derM_one, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, ContinuousLinearMap.neg_apply, map_neg, embXL_apply, mul_zero, zero_add,
    one_mul, mul_one, zero_mul]
  noncomm_ring

set_option backward.isDefEq.respectTransparency false in
/-- **The partial derivative of the Coulomb functional at `ξ = 0`.** -/
theorem hasFDerivAt_coulF_snd (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    HasFDerivAt (fun ξ => coulF L (a, ξ)) (coulD L a) 0 := by
  have h := HasFDerivAt.sum (u := Finset.univ) fun μ _ =>
    (derM (c := c) (r := r) (s := 3) (m := m) μ).hasFDerivAt.comp (0 : Fin d → SobAlg c r 5)
      (hasFDerivAt_gaugeAct L a μ)
  have h2 := (coordL (c := c) (r := r) (s := 3) (m := m) L).hasFDerivAt.comp
    (0 : Fin d → SobAlg c r 5) h
  refine h2.congr_fderiv ?_
  rfl

theorem embX_sum' {s : ℕ} [Fact (3 ≤ s)] (L : LieBasis m d) {ι : Type*} (t : Finset ι)
    (v : ι → Fin d → SobAlg c r s) : ∑ i ∈ t, embX L (v i) = embX L (∑ i ∈ t, v i) :=
  (map_sum (embXL (m := m) L) v t).symm

/-- The coefficients `A_ν^{kl} = -Σ_b f_{lbk} a_ν^b` of the linearised operator. -/
def brkCoef (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4) :
    Fin 4 → Fin d → Fin d → SobAlg c r 4 :=
  fun ν k l => -∑ b, L.f l b k • a ν b

theorem coulD_apply (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4)
    (η : Fin d → SobAlg c r 5) :
    coulD L a η = ∑ μ, ((fun k => derS μ (brk L (fun b => restrS (Nat.le_succ 4) (η b)) (a μ) k)) -
      fun k => derS μ (derS μ (η k))) := by
  have e : ∀ μ, linActL L a μ η =
      embX L (brk L (fun b => restrS (Nat.le_succ 4) (η b)) (a μ) - fun k => derS μ (η k)) := by
    intro μ
    rw [linActL_apply, rhoML_eq, rhoM_embX, embX_mul_sub, derM_embX, ← embXL_apply,
      ← embXL_apply, ← embXL_apply, ← map_sub]
  have e2 : ∀ μ, derM μ (linActL L a μ η) = embX L ((fun k => derS μ (brk L
      (fun b => restrS (Nat.le_succ 4) (η b)) (a μ) k)) - fun k => derS μ (derS μ (η k))) := by
    intro μ
    rw [e μ, derM_embX]
    rfl
  simp only [coulD, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
  simp only [e2]
  rw [embX_sum', coordL_embX]

/-- **The linearisation of the Coulomb functional is minus the linearised Coulomb operator.** -/
theorem coulD_eq_neg_linOpS (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4)
    (η : Fin d → SobAlg c r 5) : coulD L a η = -linOpS (brkCoef L a) η := by
  rw [coulD_apply]
  funext k
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.neg_apply, linOpS, lapS, divS, brkCoef, brk]
  have hR : ∑ l, ∑ ν, derS ν ((-∑ b, L.f l b k • a ν b) *
      restrS (s := 5) (s' := 4) (by norm_num) (η l)) =
      -∑ ν, derS ν (∑ l, ∑ b, L.f l b k • (restrS (s := 5) (s' := 4) (by norm_num) (η l) *
        a ν b)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← map_sum, ← map_neg]
    refine congrArg (derS ν) ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [neg_mul, Finset.sum_mul]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun b _ => ?_)
    rw [smul_mul_assoc, mul_comm]
  rw [hR, Finset.sum_sub_distrib]
  abel

end GaugeMap

end RenewalGeometry.BallAnalysis.BallAlg
