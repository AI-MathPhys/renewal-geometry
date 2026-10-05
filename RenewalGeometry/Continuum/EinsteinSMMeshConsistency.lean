/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMMeshStencils
import RenewalGeometry.Analysis.LipschitzRiemannSumError

/-!
# Smooth local action consistency (`prop:mesh-consistency`, `eq:mesh-C1`)

Einstein–Standard-Model action-closure manuscript, `prop:mesh-consistency`: for the smooth
comparison regulator of `app:reconstruction` (`EinsteinSMComparisonRegulator.lean`) and a bounded
smooth coframe/gauge/matter family with a common inverse-coframe bound,
`|D S_{b,h}[𝓘_h v] - D𝒮_{b,θ}(z_h)[v]| ≤ C_K h` uniformly on `‖v‖_{C^{r₀}} ≤ 1`, and the
reconstruction converges in the strong packet.

This file contains the bookkeeping layer: bilinear bounds, linearity and bounds of the continuum
packet variation `contJetDeriv`, linearity of the reconstruction on records.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus TransportPlaquetteConsistency TransportStencilVariation

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-! ### Elementary bilinear bounds -/

theorem norm_mmul_le (X Y : LieFibre) : ‖mmul X Y‖ ≤ 5 * ‖X‖ * ‖Y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  simp only [mmul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖X i k * Y k j‖ ≤ ∑ _k : Fin 5, ‖X‖ * ‖Y‖ := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul ((norm_le_pi_norm (X i) k).trans (norm_le_pi_norm X i))
          ((norm_le_pi_norm (Y k) j).trans (norm_le_pi_norm Y k)) (norm_nonneg _) (norm_nonneg _))
    _ = 5 * ‖X‖ * ‖Y‖ := by simp; ring

theorem norm_comm_le (X Y : LieFibre) : ‖comm X Y‖ ≤ 10 * ‖X‖ * ‖Y‖ := by
  refine (norm_sub_le _ _).trans ?_
  have := norm_mmul_le X Y; have := norm_mmul_le Y X
  nlinarith [norm_nonneg X, norm_nonneg Y]

theorem norm_higgsAct_le (X : LieFibre) (v : HiggsFibre) : ‖higgsAct X v‖ ≤ 2 * ‖X‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [higgsAct]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖X (Fin.natAdd 3 i) (Fin.natAdd 3 k) * v k‖ ≤ ∑ _k : Fin 2, ‖X‖ * ‖v‖ :=
        Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans (mul_le_mul
          ((norm_le_pi_norm (X _) _).trans (norm_le_pi_norm X _)) (norm_le_pi_norm v k)
          (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖X‖ * ‖v‖ := by simp; ring

theorem norm_pd_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4 → F) (μ : Fin 4)
    (x : E4) : ‖pd f μ x‖ ≤ ‖fderiv ℝ f x‖ :=
  ((fderiv ℝ f x).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (norm_unitE_le μ) (norm_nonneg _)).trans (by rw [mul_one]))

theorem fderiv_comp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → Fin 4 → F} {x : E4} (hf : DifferentiableAt ℝ f x) (ν : Fin 4) :
    fderiv ℝ (fun y => f y ν) x = (ContinuousLinearMap.proj ν).comp (fderiv ℝ f x) := by
  exact (hasFDerivAt_pi'.mp hf.hasFDerivAt ν).fderiv

theorem norm_pd_comp_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E4 → Fin 4 → F} {x : E4} (hf : DifferentiableAt ℝ f x) (ν μ : Fin 4) :
    ‖pd (fun y => f y ν) μ x‖ ≤ ‖fderiv ℝ f x‖ := by
  rw [pd_eq_fderiv_unitE, fderiv_comp_apply hf ν, ContinuousLinearMap.comp_apply]
  exact (norm_le_pi_norm (fderiv ℝ f x (unitE μ)) ν).trans (norm_pd_le f μ x)

/-! ### Linearity and bounds of the continuum packet variation -/

/-- The first-jet size of a direction at a point. -/
def jetSize (d : FieldTuple FC.C) (x : E4) : ℝ :=
  ‖d.e x‖ + ‖fderiv ℝ d.e x‖ + ‖d.A x‖ + ‖fderiv ℝ d.A x‖ + ‖d.H x‖ + ‖fderiv ℝ d.H x‖ +
    ‖d.Ψ x‖ + ‖fderiv ℝ d.Ψ x‖ + ‖d.Ψb x‖ + ‖fderiv ℝ d.Ψb x‖

theorem jetSize_nonneg (d : FieldTuple FC.C) (x : E4) : 0 ≤ jetSize FC d x := by
  unfold jetSize; positivity

theorem pd_sub_fun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E4 → F} {x : E4}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (μ : Fin 4) :
    pd (f - g) μ x = pd f μ x - pd g μ x := by
  unfold pd; rw [fderiv_sub hf hg]; rfl

theorem sjetOf_sub {d₁ d₂ : FieldTuple FC.C} {y : E4} (h₁ : DifferentiableAt ℝ d₁.e y)
    (h₂ : DifferentiableAt ℝ d₂.e y) (μ : Fin 4) :
    sjetOf FC (d₁ - d₂) μ y = sjetOf FC d₁ μ y - sjetOf FC d₂ μ y := by
  have hj : eJet (d₁ - d₂).e y = eJet d₁.e y - eJet d₂.e y := by
    funext i; exact pd_sub_fun h₁ h₂ i
  simp only [sjetOf, hj]
  rfl

theorem comm_sub_right (X Y Y' : LieFibre) : comm X (Y - Y') = comm X Y - comm X Y' := by
  funext i j
  simp only [comm, mmul, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem comm_sub_left (Y Y' X : LieFibre) : comm (Y - Y') X = comm Y X - comm Y' X := by
  funext i j
  simp only [comm, mmul, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem higgsAct_sub_left (X X' : LieFibre) (v : HiggsFibre) :
    higgsAct (X - X') v = higgsAct X v - higgsAct X' v := by
  funext i
  simp only [higgsAct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem higgsAct_sub_right (X : LieFibre) (v v' : HiggsFibre) :
    higgsAct X (v - v') = higgsAct X v - higgsAct X v' := by
  funext i
  simp only [higgsAct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **Linearity of the continuum packet variation in the direction.** -/
theorem contJetDeriv_sub (z : FieldTuple FC.C) {d₁ d₂ : FieldTuple FC.C} {x : E4}
    (h₁ : DiffAt FC d₁ x) (h₂ : DiffAt FC d₂ x) :
    contJetDeriv FC z d₁ x - contJetDeriv FC z d₂ x = contJetDeriv FC z (d₁ - d₂) x := by
  have hA : ∀ ν, DifferentiableAt ℝ (fun y => d₁.A y ν) x := fun ν =>
    differentiableAt_comp_apply h₁.A ν
  have hA' : ∀ ν, DifferentiableAt ℝ (fun y => d₂.A y ν) x := fun ν =>
    differentiableAt_comp_apply h₂.A ν
  have hAsub : ∀ ν μ, pd (fun y => (d₁ - d₂).A y ν) μ x =
      pd (fun y => d₁.A y ν) μ x - pd (fun y => d₂.A y ν) μ x := fun ν μ =>
    pd_sub_fun (f := fun y => d₁.A y ν) (g := fun y => d₂.A y ν) (hA ν) (hA' ν) μ
  have hH := pd_sub_fun h₁.H h₂.H
  have hΨ := pd_sub_fun h₁.Ψ h₂.Ψ
  have hΨb := pd_sub_fun h₁.Ψb h₂.Ψb
  have hs := sjetOf_sub FC h₁.e h₂.e
  simp only [contJetDeriv, rjet_mk_sub]
  congr 1
  case e_de => simp
  case e_A => simp
  case e_F =>
    funext μ ν
    show curvDeriv z.A d₁.A x μ ν - curvDeriv z.A d₂.A x μ ν = curvDeriv z.A (d₁ - d₂).A x μ ν
    unfold curvDeriv
    rw [hAsub ν μ, hAsub μ ν]
    show _ = _ - _ + comm (z.A x μ) (d₁.A x ν - d₂.A x ν) + comm (d₁.A x μ - d₂.A x μ) (z.A x ν)
    rw [comm_sub_right, comm_sub_left]
    abel
  case e_K =>
    funext μ
    show higgsDeriv z.A z.H d₁.A d₁.H x μ - higgsDeriv z.A z.H d₂.A d₂.H x μ =
      higgsDeriv z.A z.H (d₁ - d₂).A (d₁ - d₂).H x μ
    unfold higgsDeriv
    show _ = pd (d₁.H - d₂.H) μ x + higgsAct (d₁.A x μ - d₂.A x μ) (z.H x) +
      higgsAct (z.A x μ) (d₁.H x - d₂.H x)
    rw [hH, higgsAct_sub_left, higgsAct_sub_right]
    abel
  case e_dΨ =>
    funext μ
    show _ - _ = pd (d₁.Ψ - d₂.Ψ) μ x + spinConnDeriv FC z (d₁ - d₂) μ x (z.Ψ x) +
      spinConnection FC z μ x (d₁.Ψ x - d₂.Ψ x)
    simp only [spinConnDeriv]
    rw [hΨ, hs, map_sub, map_sub]
    simp only [ContinuousLinearMap.sub_apply]
    abel
  case e_dΨb =>
    funext μ
    show _ - _ = pd (d₁.Ψb - d₂.Ψb) μ x + cospinConnDeriv FC z (d₁ - d₂) μ x (z.Ψb x) +
      cospinConnection FC z μ x (d₁.Ψb x - d₂.Ψb x)
    simp only [cospinConnDeriv]
    rw [hΨb, hs, map_sub, map_sub]
    simp only [ContinuousLinearMap.sub_apply]
    abel


/-! ### Bounded Lipschitz calculus -/

/-- `f` is bounded by `M` and `M`-Lipschitz. -/
structure BL {X : Type*} [NormedAddCommGroup X] (f : E4 → X) (M : ℝ) : Prop where
  bound : ∀ y, ‖f y‖ ≤ M
  lip : ∀ y y', ‖f y - f y'‖ ≤ M * ‖y - y'‖

namespace BL

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  {f g : E4 → X} {M M' : ℝ}

theorem nonneg (hf : BL f M) : 0 ≤ M := (norm_nonneg _).trans (hf.bound 0)

theorem mono (hf : BL f M) (h : M ≤ M') : BL f M' :=
  ⟨fun y => (hf.bound y).trans h, fun y y' =>
    (hf.lip y y').trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))⟩

theorem congr (hf : BL f M) (h : ∀ y, f y = g y) : BL g M := by
  have e : f = g := funext h
  exact e ▸ hf

theorem add (hf : BL f M) (hg : BL g M') : BL (fun y => f y + g y) (M + M') :=
  ⟨fun y => (norm_add_le _ _).trans (add_le_add (hf.bound y) (hg.bound y)), fun y y' => by
    rw [add_sub_add_comm, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hf.lip y y') (hg.lip y y'))⟩

theorem sub (hf : BL f M) (hg : BL g M') : BL (fun y => f y - g y) (M + M') :=
  ⟨fun y => (norm_sub_le _ _).trans (add_le_add (hf.bound y) (hg.bound y)), fun y y' => by
    rw [sub_sub_sub_comm, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hf.lip y y') (hg.lip y y'))⟩

theorem zero : BL (fun _ : E4 => (0 : X)) 0 := ⟨fun _ => by simp, fun _ _ => by simp⟩

theorem const (c : X) : BL (fun _ : E4 => c) ‖c‖ :=
  ⟨fun _ => le_rfl, fun _ _ => by simp; positivity⟩

/-- Products by a bounded bilinear rule. -/
theorem bilin {β : X → Y → Z} {c : ℝ} (hc : 0 ≤ c) (hβ : ∀ a b, ‖β a b‖ ≤ c * ‖a‖ * ‖b‖)
    (hsub : ∀ a a' b b', β a b - β a' b' = β (a - a') b + β a' (b - b'))
    {g : E4 → Y} (hf : BL f M) (hg : BL g M') :
    BL (fun y => β (f y) (g y)) (2 * c * M * M') := by
  have hM := hf.nonneg; have hM' := hg.nonneg
  refine ⟨fun y => (hβ _ _).trans ?_, fun y y' => ?_⟩
  · have := mul_le_mul (mul_le_mul_of_nonneg_left (hf.bound y) hc) (hg.bound y) (norm_nonneg _)
      (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hc hM) hM']
  · rw [hsub]
    refine (norm_add_le _ _).trans ?_
    have h1 := hβ (f y - f y') (g y)
    have h2 := hβ (f y') (g y - g y')
    have e1 : c * ‖f y - f y'‖ * ‖g y‖ ≤ c * (M * ‖y - y'‖) * M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hf.lip y y') hc) (hg.bound y) (norm_nonneg _)
        (by positivity)
    have e2 : c * ‖f y'‖ * ‖g y - g y'‖ ≤ c * M * (M' * ‖y - y'‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hf.bound y') hc) (hg.lip y y') (norm_nonneg _)
        (by positivity)
    nlinarith [norm_nonneg (y - y')]

/-- Composition with a map bounded and Lipschitz on a set containing the values. -/
theorem comp {Φ : X → Y} {Kc : Set X} {M₀ L : ℝ} (hL : 0 ≤ L) (hb : ∀ p ∈ Kc, ‖Φ p‖ ≤ M₀)
    (hl : ∀ p ∈ Kc, ∀ p' ∈ Kc, ‖Φ p - Φ p'‖ ≤ L * ‖p - p'‖) (hf : BL f M) (hK : ∀ y, f y ∈ Kc) :
    BL (fun y => Φ (f y)) (max M₀ (L * M)) :=
  ⟨fun y => (hb _ (hK y)).trans (le_max_left _ _), fun y y' =>
    (hl _ (hK y) _ (hK y')).trans ((mul_le_mul_of_nonneg_left (hf.lip y y') hL).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))⟩

theorem proj {n : ℕ} {f : E4 → Fin n → X} (hf : BL f M) (i : Fin n) : BL (fun y => f y i) M :=
  ⟨fun y => (norm_le_pi_norm _ i).trans (hf.bound y), fun y y' =>
    (norm_le_pi_norm (f y - f y') i).trans (hf.lip y y')⟩

theorem pi {n : ℕ} {f : E4 → Fin n → X} (hM : 0 ≤ M) (hf : ∀ i, BL (fun y => f y i) M) :
    BL f M :=
  ⟨fun y => (pi_norm_le_iff_of_nonneg hM).mpr fun i => (hf i).bound y, fun y y' =>
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => (hf i).lip y y'⟩

end BL

section BLNormed

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] {M M' : ℝ}

theorem BL.apply {f : E4 → X →L[ℝ] Y} {g : E4 → X} (hf : BL f M) (hg : BL g M') :
    BL (fun y => f y (g y)) (2 * 1 * M * M') :=
  BL.bilin (β := fun (L : X →L[ℝ] Y) (v : X) => L v) zero_le_one
    (fun a b => by rw [one_mul]; exact a.le_opNorm b)
    (fun a a' b b' => by simp only [ContinuousLinearMap.sub_apply, map_sub]; abel) hf hg

theorem BL.clm (Λ : X →L[ℝ] Y) {f : E4 → X} (hf : BL f M) : BL (fun y => Λ (f y)) (‖Λ‖ * M) :=
  ⟨fun y => (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf.bound y) (norm_nonneg _)),
    fun y y' => by
      rw [← map_sub, mul_assoc]
      exact (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hf.lip y y') (norm_nonneg _))⟩

theorem norm_apply_unitE_le (L : E4 →L[ℝ] X) (μ : Fin 4) : ‖L (unitE μ)‖ ≤ ‖L‖ :=
  (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (norm_unitE_le μ) (norm_nonneg _)).trans
    (by rw [mul_one]))

theorem _root_.RenewalGeometry.C11Calculus.IsC11.bl {f : E4 → X} {B : ℝ} (hf : IsC11 f B) : BL f B := ⟨hf.norm_le, hf.lipschitz⟩

theorem _root_.RenewalGeometry.C11Calculus.IsC11.bl_pd {f : E4 → X} {B : ℝ} (hf : IsC11 f B) (μ : Fin 4) :
    BL (fun y => pd f μ y) B :=
  ⟨fun y => (norm_pd_le f μ y).trans (hf.norm_fderiv_le y), fun y y' => by
    show ‖fderiv ℝ f y (unitE μ) - fderiv ℝ f y' (unitE μ)‖ ≤ _
    rw [← ContinuousLinearMap.sub_apply]
    exact (norm_apply_unitE_le _ μ).trans (hf.lip y y')⟩

theorem _root_.RenewalGeometry.C11Calculus.IsC11.bl_pd_comp {f : E4 → Fin 4 → X} {B : ℝ} (hf : IsC11 f B) (ν μ : Fin 4) :
    BL (fun y => pd (fun y' => f y' ν) μ y) B := by
  have e : ∀ y, pd (fun y' => f y' ν) μ y = fderiv ℝ f y (unitE μ) ν := fun y => by
    rw [pd_eq_fderiv_unitE, fderiv_comp_apply (hf.differentiable y) ν]; rfl
  refine ⟨fun y => ?_, fun y y' => ?_⟩
  · rw [e]
    exact (norm_le_pi_norm _ ν).trans ((norm_apply_unitE_le _ μ).trans (hf.norm_fderiv_le y))
  · rw [e, e]
    refine (norm_le_pi_norm (fderiv ℝ f y (unitE μ) - fderiv ℝ f y' (unitE μ)) ν).trans ?_
    rw [← ContinuousLinearMap.sub_apply]
    exact (norm_apply_unitE_le _ μ).trans (hf.lip y y')

end BLNormed

theorem comm_sub4 (a a' b b' : LieFibre) :
    comm a b - comm a' b' = comm (a - a') b + comm a' (b - b') := by
  rw [comm_sub_left, comm_sub_right]; abel

theorem higgsAct_sub4 (a a' : LieFibre) (b b' : HiggsFibre) :
    higgsAct a b - higgsAct a' b' = higgsAct (a - a') b + higgsAct a' (b - b') := by
  rw [higgsAct_sub_left, higgsAct_sub_right]; abel

theorem BL.comm {f g : E4 → LieFibre} {M M' : ℝ} (hf : BL f M) (hg : BL g M') :
    BL (fun y => comm (f y) (g y)) (2 * 10 * M * M') :=
  BL.bilin (by norm_num) norm_comm_le comm_sub4 hf hg

theorem BL.higgsAct {f : E4 → LieFibre} {g : E4 → HiggsFibre} {M M' : ℝ} (hf : BL f M)
    (hg : BL g M') : BL (fun y => higgsAct (f y) (g y)) (2 * 2 * M * M') :=
  BL.bilin (by norm_num) norm_higgsAct_le higgsAct_sub4 hf hg

theorem BL.rjet {fe : E4 → CoframeFibre} {fde : E4 → CoframeJet} {fA : E4 → ConnFibre}
    {fF : E4 → Fin 4 → ConnFibre} {fH : E4 → HiggsFibre} {fK : E4 → Fin 4 → HiggsFibre}
    {fΨ : E4 → SpinorFibre FC.C} {fdΨ : E4 → Fin 4 → SpinorFibre FC.C}
    {fΨb : E4 → SpinorFibre FC.C} {fdΨb : E4 → Fin 4 → SpinorFibre FC.C}
    {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℝ} (h1 : BL fe c1) (h2 : BL fde c2) (h3 : BL fA c3)
    (h4 : BL fF c4) (h5 : BL fH c5) (h6 : BL fK c6) (h7 : BL fΨ c7) (h8 : BL fdΨ c8)
    (h9 : BL fΨb c9) (h10 : BL fdΨb c10) :
    BL (fun y => RJet.mk (fe y) (fde y) (fA y) (fF y) (fH y) (fK y) (fΨ y) (fdΨ y) (fΨb y)
      (fdΨb y)) (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10) := by
  have n1 := h1.nonneg; have n2 := h2.nonneg; have n3 := h3.nonneg; have n4 := h4.nonneg
  have n5 := h5.nonneg; have n6 := h6.nonneg; have n7 := h7.nonneg; have n8 := h8.nonneg
  have n9 := h9.nonneg; have n10 := h10.nonneg
  set S := c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10
  have k1 : BL fe S := h1.mono (by simp only [S]; linarith)
  have k2 : BL fde S := h2.mono (by simp only [S]; linarith)
  have k3 : BL fA S := h3.mono (by simp only [S]; linarith)
  have k4 : BL fF S := h4.mono (by simp only [S]; linarith)
  have k5 : BL fH S := h5.mono (by simp only [S]; linarith)
  have k6 : BL fK S := h6.mono (by simp only [S]; linarith)
  have k7 : BL fΨ S := h7.mono (by simp only [S]; linarith)
  have k8 : BL fdΨ S := h8.mono (by simp only [S]; linarith)
  have k9 : BL fΨb S := h9.mono (by simp only [S]; linarith)
  have k10 : BL fdΨb S := h10.mono (by simp only [S]; linarith)
  refine ⟨fun y => norm_rjet_le FC (k1.bound y) (k2.bound y) (k3.bound y) (k4.bound y)
    (k5.bound y) (k6.bound y) (k7.bound y) (k8.bound y) (k9.bound y) (k10.bound y),
    fun y y' => ?_⟩
  rw [rjet_mk_sub]
  exact norm_rjet_le FC (k1.lip y y') (k2.lip y y') (k3.lip y y') (k4.lip y y') (k5.lip y y')
    (k6.lip y y') (k7.lip y y') (k8.lip y y') (k9.lip y y') (k10.lip y y')


/-! ### Uniform chart data of the spin connection maps -/

/-- Uniform bound/Lipschitz data `M` of the spin and dual spin connection maps and of their
derivatives on the compact jet chart set `sjetBox Ke B`. -/
structure SpinChart (Ke : Set CoframeFibre) (B M : ℝ) : Prop where
  nonneg : 0 ≤ M
  bound : ∀ μ, ∀ p ∈ sjetBox Ke B, ‖spinConnMap FC μ p‖ ≤ M ∧ ‖cospinConnMap FC μ p‖ ≤ M
  dbound : ∀ μ, ∀ p ∈ sjetBox Ke B,
    ‖fderiv ℝ (spinConnMap FC μ) p‖ ≤ M ∧ ‖fderiv ℝ (cospinConnMap FC μ) p‖ ≤ M
  lip : ∀ μ, ∀ p ∈ sjetBox Ke B, ∀ p' ∈ sjetBox Ke B,
    ‖spinConnMap FC μ p - spinConnMap FC μ p'‖ ≤ M * ‖p - p'‖ ∧
      ‖cospinConnMap FC μ p - cospinConnMap FC μ p'‖ ≤ M * ‖p - p'‖
  dlip : ∀ μ, ∀ p ∈ sjetBox Ke B, ∀ p' ∈ sjetBox Ke B,
    ‖fderiv ℝ (spinConnMap FC μ) p - fderiv ℝ (spinConnMap FC μ) p'‖ ≤ M * ‖p - p'‖ ∧
      ‖fderiv ℝ (cospinConnMap FC μ) p - fderiv ℝ (cospinConnMap FC μ) p'‖ ≤ M * ‖p - p'‖

theorem exists_spinChart {Ke : Set CoframeFibre} (hKe : IsCompact Ke) (hKeGL : Ke ⊆ coframeGL)
    (B : ℝ) : ∃ M, SpinChart FC Ke B M := by
  have hS : ∀ μ : Fin 4, ∃ δ M₀ M₁ L₀ L₁ Cq : ℝ, ChartData (spinConnMap FC μ) (sjetBox Ke B)
      δ M₀ M₁ L₀ L₁ Cq := fun μ =>
    exists_chartData isOpen_sjetGL (contDiffOn_spinConnMap FC μ) (isCompact_sjetBox hKe B)
      (sjetBox_subset hKeGL B)
  have hC : ∀ μ : Fin 4, ∃ δ M₀ M₁ L₀ L₁ Cq : ℝ, ChartData (cospinConnMap FC μ) (sjetBox Ke B)
      δ M₀ M₁ L₀ L₁ Cq := fun μ =>
    exists_chartData isOpen_sjetGL (contDiffOn_cospinConnMap FC μ) (isCompact_sjetBox hKe B)
      (sjetBox_subset hKeGL B)
  choose δ M₀ M₁ L₀ L₁ Cq hd using hS
  choose δ' M₀' M₁' L₀' L₁' Cq' hd' using hC
  set a : Fin 4 → ℝ := fun μ => M₀ μ + M₁ μ + L₀ μ + L₁ μ + M₀' μ + M₁' μ + L₀' μ + L₁' μ
  have ha : ∀ μ, 0 ≤ a μ := fun μ => by
    have := (hd μ).M₀_nonneg; have := (hd μ).M₁_nonneg; have := (hd μ).L₀_nonneg
    have := (hd μ).L₁_nonneg; have := (hd' μ).M₀_nonneg; have := (hd' μ).M₁_nonneg
    have := (hd' μ).L₀_nonneg; have := (hd' μ).L₁_nonneg
    simp only [a]; linarith
  have hle : ∀ μ, a μ ≤ ∑ ν, a ν := fun μ =>
    Finset.single_le_sum (fun ν _ => ha ν) (Finset.mem_univ μ)
  have tri : ∀ μ, M₀ μ ≤ ∑ ν, a ν ∧ M₁ μ ≤ ∑ ν, a ν ∧ L₀ μ ≤ ∑ ν, a ν ∧ L₁ μ ≤ ∑ ν, a ν ∧
      M₀' μ ≤ ∑ ν, a ν ∧ M₁' μ ≤ ∑ ν, a ν ∧ L₀' μ ≤ ∑ ν, a ν ∧ L₁' μ ≤ ∑ ν, a ν := fun μ => by
    have := (hd μ).M₀_nonneg; have := (hd μ).M₁_nonneg; have := (hd μ).L₀_nonneg
    have := (hd μ).L₁_nonneg; have := (hd' μ).M₀_nonneg; have := (hd' μ).M₁_nonneg
    have := (hd' μ).L₀_nonneg; have := (hd' μ).L₁_nonneg
    have h := hle μ
    simp only [a] at h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have b0 : ∀ μ, ∀ p ∈ sjetBox Ke B, ‖spinConnMap FC μ p‖ ≤ M₀ μ := fun μ p hp => by
    simpa using (hd μ).bound p hp 0 (by simp [(hd μ).δ_pos.le])
  have b0' : ∀ μ, ∀ p ∈ sjetBox Ke B, ‖cospinConnMap FC μ p‖ ≤ M₀' μ := fun μ p hp => by
    simpa using (hd' μ).bound p hp 0 (by simp [(hd' μ).δ_pos.le])
  refine ⟨∑ ν, a ν, Finset.sum_nonneg fun ν _ => ha ν, fun μ p hp => ⟨(b0 μ p hp).trans
    (tri μ).1, (b0' μ p hp).trans (tri μ).2.2.2.2.1⟩, fun μ p hp => ⟨((hd μ).dbound p hp).trans
    (tri μ).2.1, ((hd' μ).dbound p hp).trans (tri μ).2.2.2.2.2.1⟩, fun μ p hp p' hp' => ⟨?_, ?_⟩,
    fun μ p hp p' hp' => ⟨?_, ?_⟩⟩
  · exact ((hd μ).lip p hp p' hp').trans (mul_le_mul_of_nonneg_right (tri μ).2.2.1 (norm_nonneg _))
  · exact ((hd' μ).lip p hp p' hp').trans
      (mul_le_mul_of_nonneg_right (tri μ).2.2.2.2.2.2.1 (norm_nonneg _))
  · exact ((hd μ).dlip p hp p' hp').trans
      (mul_le_mul_of_nonneg_right (tri μ).2.2.2.1 (norm_nonneg _))
  · exact ((hd' μ).dlip p hp p' hp').trans
      (mul_le_mul_of_nonneg_right (tri μ).2.2.2.2.2.2.2 (norm_nonneg _))

theorem FieldC11.bl_sjetOf {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) (μ : Fin 4) :
    BL (sjetOf FC z μ) B :=
  ⟨sjetOf_norm_le FC hz μ, sjetOf_lip FC hz μ⟩

theorem FieldC11.nonneg {z : FieldTuple FC.C} {B : ℝ} (hz : FieldC11 FC z B) : 0 ≤ B :=
  hz.e.nonneg

theorem FieldC11.mono {z : FieldTuple FC.C} {B B' : ℝ} (hz : FieldC11 FC z B) (h : B ≤ B') :
    FieldC11 FC z B' :=
  ⟨hz.e.mono h, hz.A.mono h, hz.H.mono h, hz.Ψ.mono h, hz.Ψb.mono h⟩

/-! ### The continuum packet and its variation are bounded and Lipschitz -/

theorem exists_bl_contJet {Ke : Set CoframeFibre} (hKeGL : Ke ⊆ coframeGL) {B M : ℝ}
    (hS : SpinChart FC Ke B M) (hB : 0 ≤ B) : ∃ C : ℝ, ∀ z : FieldTuple FC.C,
      FieldC11 FC z B → (∀ y, z.e y ∈ Ke) → BL (contJet FC z) C := by
  refine ⟨?_, fun z hz hzK => ?_⟩
  rotate_left
  have hM := hS.nonneg
  have hmem := sjetOf_mem FC hz hzK
  have sp : ∀ μ, BL (fun y => spinConnMap FC μ (sjetOf FC z μ y)) (max M (M * B)) := fun μ =>
    BL.comp hM (fun p hp => (hS.bound μ p hp).1) (fun p hp p' hp' => (hS.lip μ p hp p' hp').1)
      (hz.bl_sjetOf FC μ) (hmem μ)
  have csp : ∀ μ, BL (fun y => cospinConnMap FC μ (sjetOf FC z μ y)) (max M (M * B)) := fun μ =>
    BL.comp hM (fun p hp => (hS.bound μ p hp).2) (fun p hp p' hp' => (hS.lip μ p hp p' hp').2)
      (hz.bl_sjetOf FC μ) (hmem μ)
  have hc1 : ∀ y μ, spinConnection FC z μ y = spinConnMap FC μ (sjetOf FC z μ y) := fun y μ =>
    spinConnection_eq_map FC z μ (hz.e.differentiable y) (hKeGL (hzK y))
  have hc2 : ∀ y μ, cospinConnection FC z μ y = cospinConnMap FC μ (sjetOf FC z μ y) := fun y μ =>
    cospinConnection_eq_map FC z μ (hz.e.differentiable y) (hKeGL (hzK y))
  have hF : BL (fun y => curvatureF z.A y) (B + B + 2 * 10 * B * B) :=
    BL.pi (by positivity) fun μ => BL.pi (by positivity) fun ν =>
      ((hz.A.bl_pd_comp ν μ).sub (hz.A.bl_pd_comp μ ν)).add
        (BL.comm (hz.A.bl.proj μ) (hz.A.bl.proj ν))
  have hK : BL (fun y => covDerivHiggs z.A z.H y) (B + 2 * 2 * B * B) :=
    BL.pi (by positivity) fun μ => (hz.H.bl_pd μ).add (BL.higgsAct (hz.A.bl.proj μ) hz.H.bl)
  have hD : BL (fun y => covDerivSpinor FC z.e z.A z.Ψ y) (B + 2 * 1 * max M (M * B) * B) :=
    BL.pi (by positivity) fun μ => ((hz.Ψ.bl_pd μ).add (BL.apply (sp μ) hz.Ψ.bl)).congr
      fun y => by rw [covDerivSpinor_eq, hc1]
  have hDb : BL (fun y => covDerivCospinor FC z.e z.A z.Ψb y)
      (B + 2 * 1 * max M (M * B) * B) :=
    BL.pi (by positivity) fun μ => ((hz.Ψb.bl_pd μ).add (BL.apply (csp μ) hz.Ψb.bl)).congr
      fun y => by rw [covDerivCospinor_eq, hc2]
  exact BL.rjet FC hz.e.bl BL.zero BL.zero hF hz.H.bl hK hz.Ψ.bl hD hz.Ψb.bl hDb

theorem exists_bl_contJetDeriv {Ke : Set CoframeFibre} (hKeGL : Ke ⊆ coframeGL) {B M : ℝ}
    (hS : SpinChart FC Ke B M) (hB : 0 ≤ B) {Bd : ℝ} (hBd : 0 ≤ Bd) : ∃ C : ℝ,
      ∀ z d : FieldTuple FC.C, FieldC11 FC z B → FieldC11 FC d Bd → (∀ y, z.e y ∈ Ke) →
        BL (fun y => contJetDeriv FC z d y) C := by
  refine ⟨?_, fun z d hz hd hzK => ?_⟩
  rotate_left
  have hM := hS.nonneg
  have hmem := sjetOf_mem FC hz hzK
  have sp : ∀ μ, BL (fun y => spinConnMap FC μ (sjetOf FC z μ y)) (max M (M * B)) := fun μ =>
    BL.comp hM (fun p hp => (hS.bound μ p hp).1) (fun p hp p' hp' => (hS.lip μ p hp p' hp').1)
      (hz.bl_sjetOf FC μ) (hmem μ)
  have csp : ∀ μ, BL (fun y => cospinConnMap FC μ (sjetOf FC z μ y)) (max M (M * B)) := fun μ =>
    BL.comp hM (fun p hp => (hS.bound μ p hp).2) (fun p hp p' hp' => (hS.lip μ p hp p' hp').2)
      (hz.bl_sjetOf FC μ) (hmem μ)
  have dsp : ∀ μ, BL (fun y => fderiv ℝ (spinConnMap FC μ) (sjetOf FC z μ y)) (max M (M * B)) :=
    fun μ => BL.comp hM (fun p hp => (hS.dbound μ p hp).1)
      (fun p hp p' hp' => (hS.dlip μ p hp p' hp').1) (hz.bl_sjetOf FC μ) (hmem μ)
  have dcsp : ∀ μ, BL (fun y => fderiv ℝ (cospinConnMap FC μ) (sjetOf FC z μ y))
      (max M (M * B)) :=
    fun μ => BL.comp hM (fun p hp => (hS.dbound μ p hp).2)
      (fun p hp p' hp' => (hS.dlip μ p hp p' hp').2) (hz.bl_sjetOf FC μ) (hmem μ)
  have hc1 : ∀ y μ, spinConnection FC z μ y = spinConnMap FC μ (sjetOf FC z μ y) := fun y μ =>
    spinConnection_eq_map FC z μ (hz.e.differentiable y) (hKeGL (hzK y))
  have hc2 : ∀ y μ, cospinConnection FC z μ y = cospinConnMap FC μ (sjetOf FC z μ y) := fun y μ =>
    cospinConnection_eq_map FC z μ (hz.e.differentiable y) (hKeGL (hzK y))
  have hF : BL (fun y => curvDeriv z.A d.A y)
      (Bd + Bd + 2 * 10 * B * Bd + 2 * 10 * Bd * B) :=
    BL.pi (by positivity) fun μ => BL.pi (by positivity) fun ν =>
      (((hd.A.bl_pd_comp ν μ).sub (hd.A.bl_pd_comp μ ν)).add
        (BL.comm (hz.A.bl.proj μ) (hd.A.bl.proj ν))).add (BL.comm (hd.A.bl.proj μ) (hz.A.bl.proj ν))
  have hK : BL (fun y => higgsDeriv z.A z.H d.A d.H y) (Bd + 2 * 2 * Bd * B + 2 * 2 * B * Bd) :=
    BL.pi (by positivity) fun μ => ((hd.H.bl_pd μ).add (BL.higgsAct (hd.A.bl.proj μ) hz.H.bl)).add
      (BL.higgsAct (hz.A.bl.proj μ) hd.H.bl)
  have hD : BL (fun y μ => pd d.Ψ μ y + spinConnDeriv FC z d μ y (z.Ψ y) +
      spinConnection FC z μ y (d.Ψ y))
      (Bd + 2 * 1 * (2 * 1 * max M (M * B) * Bd) * B + 2 * 1 * max M (M * B) * Bd) :=
    BL.pi (by positivity) fun μ => (((hd.Ψ.bl_pd μ).add (BL.apply (BL.apply (dsp μ)
      (hd.bl_sjetOf FC μ)) hz.Ψ.bl)).add (BL.apply (sp μ) hd.Ψ.bl)).congr fun y => by
        simp only [spinConnDeriv, hc1]
  have hDb : BL (fun y μ => pd d.Ψb μ y + cospinConnDeriv FC z d μ y (z.Ψb y) +
      cospinConnection FC z μ y (d.Ψb y))
      (Bd + 2 * 1 * (2 * 1 * max M (M * B) * Bd) * B + 2 * 1 * max M (M * B) * Bd) :=
    BL.pi (by positivity) fun μ => (((hd.Ψb.bl_pd μ).add (BL.apply (BL.apply (dcsp μ)
      (hd.bl_sjetOf FC μ)) hz.Ψb.bl)).add (BL.apply (csp μ) hd.Ψb.bl)).congr fun y => by
        simp only [cospinConnDeriv, hc2]
  exact BL.rjet FC hd.e.bl BL.zero BL.zero hF hd.H.bl hK hd.Ψ.bl hD hd.Ψb.bl hDb


/-! ### Pointwise bound, locality and linearity of the packet variation -/

/-- Pointwise first-jet smallness of a direction: values and first derivatives of all five
components bounded by `s` at `x`. -/
structure PtSmall (d : FieldTuple FC.C) (x : E4) (s : ℝ) : Prop where
  e : ‖d.e x‖ ≤ s
  de : ‖fderiv ℝ d.e x‖ ≤ s
  A : ‖d.A x‖ ≤ s
  dA : ‖fderiv ℝ d.A x‖ ≤ s
  H : ‖d.H x‖ ≤ s
  dH : ‖fderiv ℝ d.H x‖ ≤ s
  Ψ : ‖d.Ψ x‖ ≤ s
  dΨ : ‖fderiv ℝ d.Ψ x‖ ≤ s
  Ψb : ‖d.Ψb x‖ ≤ s
  dΨb : ‖fderiv ℝ d.Ψb x‖ ≤ s

theorem PtSmall.nonneg {d : FieldTuple FC.C} {x : E4} {s : ℝ} (hs : PtSmall FC d x s) : 0 ≤ s :=
  (norm_nonneg _).trans hs.e

theorem PtSmall.sjetOf {d : FieldTuple FC.C} {x : E4} {s : ℝ} (hs : PtSmall FC d x s)
    (μ : Fin 4) : ‖sjetOf FC d μ x‖ ≤ s :=
  norm_prod_le_iff.mpr ⟨hs.e, norm_prod_le_iff.mpr ⟨(norm_eJet_le_fderiv x).trans hs.de,
    (norm_le_pi_norm _ μ).trans hs.A⟩⟩

/-- **Pointwise bound of the packet variation** by the first jet of the direction. -/
theorem norm_contJetDeriv_le {Ke : Set CoframeFibre} (hKeGL : Ke ⊆ coframeGL) {B M : ℝ}
    (hS : SpinChart FC Ke B M) {z d : FieldTuple FC.C} {x : E4} {s : ℝ} (hz : FieldC11 FC z B)
    (hzK : ∀ y, z.e y ∈ Ke) (hd : DiffAt FC d x) (hs : PtSmall FC d x s) :
    ‖contJetDeriv FC z d x‖ ≤ (2 + 24 * B + M * B + M) * s := by
  have hs0 := hs.nonneg
  have hB := hz.nonneg
  have hM := hS.nonneg
  have hBs : 0 ≤ B * s := mul_nonneg hB hs0
  have hMBs : 0 ≤ M * B * s := by positivity
  have hMs : 0 ≤ M * s := mul_nonneg hM hs0
  have hc0 : 0 ≤ (2 + 24 * B + M * B + M) * s := by positivity
  have hzA : ∀ μ, ‖z.A x μ‖ ≤ B := fun μ => (norm_le_pi_norm _ μ).trans (hz.A.norm_le x)
  have hdA : ∀ μ, ‖d.A x μ‖ ≤ s := fun μ => (norm_le_pi_norm _ μ).trans hs.A
  have hcomm : ∀ a b : LieFibre, ‖a‖ ≤ B → ‖b‖ ≤ s → ‖comm a b‖ ≤ 10 * B * s := fun a b ha hb =>
    (norm_comm_le a b).trans (by
      have := mul_le_mul ha hb (norm_nonneg b) hB; nlinarith)
  have hcomm' : ∀ a b : LieFibre, ‖a‖ ≤ s → ‖b‖ ≤ B → ‖comm a b‖ ≤ 10 * B * s := fun a b ha hb =>
    (norm_comm_le a b).trans (by
      have := mul_le_mul ha hb (norm_nonneg b) hs0; nlinarith)
  have hspin : ∀ μ, ‖spinConnection FC z μ x‖ ≤ M := fun μ => by
    rw [spinConnection_eq_map FC z μ (hz.e.differentiable x) (hKeGL (hzK x))]
    exact (hS.bound μ _ (sjetOf_mem FC hz hzK μ x)).1
  have hcospin : ∀ μ, ‖cospinConnection FC z μ x‖ ≤ M := fun μ => by
    rw [cospinConnection_eq_map FC z μ (hz.e.differentiable x) (hKeGL (hzK x))]
    exact (hS.bound μ _ (sjetOf_mem FC hz hzK μ x)).2
  have happ : ∀ (L : SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C) (v : SpinorFibre FC.C) (a b : ℝ),
      0 ≤ a → ‖L‖ ≤ a → ‖v‖ ≤ b → ‖L v‖ ≤ a * b := fun L v a b ha hL hv =>
    (L.le_opNorm v).trans (mul_le_mul hL hv (norm_nonneg _) ha)
  have hder : ∀ (Φ : SJet → SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C) (p q : SJet)
      (v : SpinorFibre FC.C), ‖fderiv ℝ Φ p‖ ≤ M → ‖q‖ ≤ s → ‖v‖ ≤ B →
      ‖fderiv ℝ Φ p q v‖ ≤ M * s * B := fun Φ p q v h1 h2 h3 =>
    happ _ v _ _ (by positivity) (((fderiv ℝ Φ p).le_opNorm q).trans
      (mul_le_mul h1 h2 (norm_nonneg _) hM)) h3
  have hzΨ : ‖z.Ψ x‖ ≤ B := hz.Ψ.norm_le x
  have hzΨb : ‖z.Ψb x‖ ≤ B := hz.Ψb.norm_le x
  have hzH : ‖z.H x‖ ≤ B := hz.H.norm_le x
  refine norm_rjet_le FC ?_ (by simpa using hc0) (by simpa using hc0)
    (norm_pi2_le hc0 fun μ ν => ?_) ?_ (norm_pi1_le hc0 fun μ => ?_) ?_
    (norm_pi1_le hc0 fun μ => ?_) ?_ (norm_pi1_le hc0 fun μ => ?_)
  · exact hs.e.trans (by nlinarith)
  · show ‖pd (fun y => d.A y ν) μ x - pd (fun y => d.A y μ) ν x + comm (z.A x μ) (d.A x ν) +
      comm (d.A x μ) (z.A x ν)‖ ≤ _
    have p1 := (norm_pd_comp_le hd.A ν μ).trans hs.dA
    have p2 := (norm_pd_comp_le hd.A μ ν).trans hs.dA
    have c1 := hcomm _ _ (hzA μ) (hdA ν)
    have c2 := hcomm' _ _ (hdA μ) (hzA ν)
    refine norm_add₃_le.trans ?_
    have t := norm_add₃_le (a := pd (fun y => d.A y ν) μ x - pd (fun y => d.A y μ) ν x)
      (b := comm (z.A x μ) (d.A x ν)) (c := comm (d.A x μ) (z.A x ν))
    have t2 := norm_sub_le (pd (fun y => d.A y ν) μ x) (pd (fun y => d.A y μ) ν x)
    nlinarith
  · exact hs.H.trans (by nlinarith)
  · show ‖pd d.H μ x + higgsAct (d.A x μ) (z.H x) + higgsAct (z.A x μ) (d.H x)‖ ≤ _
    have p1 := (norm_pd_le d.H μ x).trans hs.dH
    have h1 := norm_higgsAct_le (d.A x μ) (z.H x)
    have h2 := norm_higgsAct_le (z.A x μ) (d.H x)
    have e1 := mul_le_mul (hdA μ) hzH (norm_nonneg _) hs0
    have e2 := mul_le_mul (hzA μ) hs.H (norm_nonneg _) hB
    refine norm_add₃_le.trans ?_
    nlinarith
  · exact hs.Ψ.trans (by nlinarith)
  · show ‖pd d.Ψ μ x + spinConnDeriv FC z d μ x (z.Ψ x) + spinConnection FC z μ x (d.Ψ x)‖ ≤ _
    have p1 := (norm_pd_le d.Ψ μ x).trans hs.dΨ
    have q1 := hder _ (sjetOf FC z μ x) (sjetOf FC d μ x) (z.Ψ x)
      (hS.dbound μ _ (sjetOf_mem FC hz hzK μ x)).1 (hs.sjetOf FC μ) hzΨ
    have q2 := happ _ (d.Ψ x) _ _ hM (hspin μ) hs.Ψ
    refine norm_add₃_le.trans ?_
    simp only [spinConnDeriv] at *
    nlinarith
  · exact hs.Ψb.trans (by nlinarith)
  · show ‖pd d.Ψb μ x + cospinConnDeriv FC z d μ x (z.Ψb x) +
      cospinConnection FC z μ x (d.Ψb x)‖ ≤ _
    have p1 := (norm_pd_le d.Ψb μ x).trans hs.dΨb
    have q1 := hder _ (sjetOf FC z μ x) (sjetOf FC d μ x) (z.Ψb x)
      (hS.dbound μ _ (sjetOf_mem FC hz hzK μ x)).2 (hs.sjetOf FC μ) hzΨb
    have q2 := happ _ (d.Ψb x) _ _ hM (hcospin μ) hs.Ψb
    refine norm_add₃_le.trans ?_
    simp only [cospinConnDeriv] at *
    nlinarith

/-- **Locality** of the packet variation: it depends only on the germ of the direction. -/
theorem contJetDeriv_congr (z : FieldTuple FC.C) {d d' : FieldTuple FC.C} {x : E4}
    (he : d.e =ᶠ[𝓝 x] d'.e) (hA : d.A =ᶠ[𝓝 x] d'.A) (hH : d.H =ᶠ[𝓝 x] d'.H)
    (hΨ : d.Ψ =ᶠ[𝓝 x] d'.Ψ) (hΨb : d.Ψb =ᶠ[𝓝 x] d'.Ψb) :
    contJetDeriv FC z d x = contJetDeriv FC z d' x := by
  have hAν : ∀ ν, fderiv ℝ (fun y => d.A y ν) x = fderiv ℝ (fun y => d'.A y ν) x := fun ν =>
    (hA.fun_comp (fun a => a ν)).fderiv_eq
  have hsj : ∀ μ, sjetOf FC d μ x = sjetOf FC d' μ x := fun μ =>
    Prod.ext he.eq_of_nhds (Prod.ext (funext fun i => show fderiv ℝ d.e x (unitE i) =
      fderiv ℝ d'.e x (unitE i) by rw [he.fderiv_eq]) (congrFun hA.eq_of_nhds μ))
  have hcd : curvDeriv z.A d.A x = curvDeriv z.A d'.A x := by
    funext μ ν
    show pd (fun y => d.A y ν) μ x - pd (fun y => d.A y μ) ν x + comm (z.A x μ) (d.A x ν) +
        comm (d.A x μ) (z.A x ν) = pd (fun y => d'.A y ν) μ x - pd (fun y => d'.A y μ) ν x +
        comm (z.A x μ) (d'.A x ν) + comm (d'.A x μ) (z.A x ν)
    rw [pd_eq_fderiv_unitE, pd_eq_fderiv_unitE, pd_eq_fderiv_unitE, pd_eq_fderiv_unitE, hAν, hAν,
      hA.eq_of_nhds]
  have hhd : higgsDeriv z.A z.H d.A d.H x = higgsDeriv z.A z.H d'.A d'.H x := by
    funext μ
    show pd d.H μ x + higgsAct (d.A x μ) (z.H x) + higgsAct (z.A x μ) (d.H x) =
      pd d'.H μ x + higgsAct (d'.A x μ) (z.H x) + higgsAct (z.A x μ) (d'.H x)
    rw [pd_eq_fderiv_unitE, pd_eq_fderiv_unitE, hH.fderiv_eq, hA.eq_of_nhds, hH.eq_of_nhds]
  simp only [contJetDeriv, hcd, hhd, spinConnDeriv, cospinConnDeriv, hsj, pd,
    he.eq_of_nhds, hH.eq_of_nhds, hΨ.eq_of_nhds, hΨb.eq_of_nhds, hΨ.fderiv_eq, hΨb.fderiv_eq]

theorem contJetDeriv_zero (z : FieldTuple FC.C) (x : E4) :
    contJetDeriv FC z 0 x = 0 := by
  have h0 : DiffAt FC (0 : FieldTuple FC.C) x :=
    ⟨differentiableAt_const _, differentiableAt_const _, differentiableAt_const _,
      differentiableAt_const _, differentiableAt_const _⟩
  have := contJetDeriv_sub FC z h0 h0
  rw [sub_self, sub_self] at this
  exact this.symm

/-- **Linearity of the reconstruction**. -/
theorem reconFields_add_smul {h : ℝ} (hh : 0 < h) (q w : (Fin 4 → ℤ) → FieldVal FC.C) (t : ℝ) :
    reconFields FC h (q + t • w) = reconFields FC h q + t • reconFields FC h w := by
  have k : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (g₁ g₂ : (Fin 4 → ℤ) → W),
      recon h (g₁ + t • g₂) = recon h g₁ + t • recon h g₂ := fun g₁ g₂ => funext fun y => by
    rw [recon_add hh, recon_smul hh]; rfl
  exact Prod.ext (k _ _) (Prod.ext (k _ _) (Prod.ext (k _ _) (Prod.ext (k _ _) (k _ _))))


/-! ### Integration over the comparison box -/

section BoxIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compBox_zero_null : volume (compBox 0) = 0 :=
  measure_mono_null (fun x hx => le_antisymm (by simpa using hx.2 0) (by simpa using hx.1 0))
    (volume_coord_eq 0 0)

theorem e0_apply (i : Fin 4) : e0 i = if i = 0 then 1 else 0 := by
  simp [e0, Pi.single_apply]

theorem compBox_succ (P : ℕ) :
    compBox (P + 1) = compBox P ∪ Icc ((P : ℝ) • e0) ((P : ℝ) • e0 + 1) := by
  ext x
  simp only [compBox, mem_union, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.add_apply, Pi.smul_apply,
    e0_apply, Pi.one_apply, smul_eq_mul]
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  constructor
  · rintro ⟨h0, h1⟩
    by_cases hx : x 0 ≤ P
    · left
      refine ⟨h0, fun i => ?_⟩
      by_cases hi : i = 0
      · subst hi; simpa using hx
      · simpa [hi] using h1 i
    · right
      push_neg at hx
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i = 0
        · subst hi; simp; linarith
        · simpa [hi] using h0 i
      · by_cases hi : i = 0
        · subst hi; have := h1 0; simp at this ⊢; linarith
        · simpa [hi] using h1 i
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine ⟨h0, fun i => ?_⟩
      by_cases hi : i = 0
      · subst hi; have := h1 0; simp at this ⊢; linarith
      · simpa [hi] using h1 i
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i = 0
        · subst hi; have := h0 0; simp at this ⊢; linarith
        · simpa [hi] using h0 i
      · by_cases hi : i = 0
        · subst hi; have := h1 0; simp at this ⊢; linarith
        · simpa [hi] using h1 i

/-- Translation of the unit cube. -/
theorem setIntegral_Icc_translate (g : E4 → F) (c : E4) :
    ∫ x in Icc c (c + 1), g x = ∫ x in Icc (0 : E4) 1, g (c + x) := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc,
    ← integral_add_left_eq_self (μ := (volume : Measure E4)) _ c]
  congr 1
  funext x
  have hm : c + x ∈ Icc c (c + 1) ↔ x ∈ Icc 0 1 := by
    simp only [mem_Icc, le_add_iff_nonneg_right, add_le_add_iff_left]
  by_cases hx : x ∈ Icc (0 : E4) 1
  · simp only [Set.indicator, if_pos (hm.mpr hx), if_pos hx]
  · simp only [Set.indicator, if_neg (mt hm.mp hx), if_neg hx]

/-- **The comparison box is the union of `P` unit time cells**. -/
theorem integral_compBox {g : E4 → F} (hg : Continuous g) (P : ℕ) :
    ∫ x in compBox P, g x = ∑ k : Fin P, ∫ x in Icc (0 : E4) 1, g ((k : ℝ) • e0 + x) := by
  induction P with
  | zero => simp [setIntegral_measure_zero _ compBox_zero_null]
  | succ P ih =>
    have hcK : IsCompact (compBox P) := isCompact_Icc
    rw [Fin.sum_univ_castSucc, compBox_succ, setIntegral_union₀ ?_
      measurableSet_Icc.nullMeasurableSet (hg.continuousOn.integrableOn_compact hcK)
      (hg.continuousOn.integrableOn_compact isCompact_Icc), ih, setIntegral_Icc_translate]
    · simp
    · refine measure_mono_null (fun x hx => ?_) (volume_coord_eq 0 (P : ℝ))
      have h1 := hx.1.2 0
      have h2 := hx.2.1 0
      simp only [compBox, Pi.smul_apply, e0_apply, smul_eq_mul] at h1 h2
      simp at h1 h2
      exact le_antisymm h1 h2

/-- The integral over the open chart slab equals the integral over the comparison box, for
densities vanishing outside the time interval `[t₀, t₁]`. -/
theorem integral_slab_eq_compBox {g : E4 → F} {T t₀ t₁ : ℝ} (h0 : 0 < t₀) (h01 : t₀ < t₁)
    (h1 : t₁ < T) {P : ℕ} (hTP : T ≤ P) (hsupp : ∀ x : E4, x 0 ∉ Icc t₀ t₁ → g x = 0) :
    ∫ x in (slabChart t₀ t₁ h0 h01 h1 (T := T)).set, g x = ∫ x in compBox P, g x := by
  set a : E4 := Fin.cons t₀ 0
  set b : E4 := Fin.cons t₁ 1
  have hae : (slabChart t₀ t₁ h0 h01 h1 (T := T)).set =ᵐ[volume] Icc a b :=
    Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin 4 => (volume : Measure ℝ))
  rw [setIntegral_congr_set hae]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc ?_ ?_).symm
  · intro x hx
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := hx.1 i
      refine Fin.cases ?_ (fun j => ?_) i
      · have := hx.1 0; simp [a] at this ⊢; linarith
      · have := hx.1 j.succ; simpa [a] using this
    · refine Fin.cases ?_ (fun j => ?_) i
      · have := hx.2 0; simp [b, compBox] at this ⊢; linarith
      · have := hx.2 j.succ; simpa [b, compBox] using this
  · intro x hx
    refine hsupp x fun ht => hx.2 ⟨fun i => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa [a] using ht.1
      · have := hx.1.1 j.succ; simpa [a] using this
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa [b] using ht.2
      · have := hx.1.2 j.succ; simpa [b, compBox] using this

end BoxIntegral

end Comparison
end EinsteinSM
end RenewalGeometry
