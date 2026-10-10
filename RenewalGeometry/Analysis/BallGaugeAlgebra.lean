/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallGaugeLie

/-!
# The gauge algebra of Sobolev matrix fields on a ball: conjugation, gauge action, composition,
  curvature covariance and the gauge equation (stage D3 of the ball rendering of Uhlenbeck's
  small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `Cx.instStarRing` — conjugation `re + i im ↦ re - i im` on the complexification `Cx V`;
  hence `star` (conjugate transpose) on `MatSob c r s m` (`evM_star`: pointwise conjugate
  transpose, `derM_star`, `rhoM_star`);
* `derS_restrS`, `derS_comm` — derivatives commute with restriction and with each other
  (Schwarz for weak derivatives); `derM_rhoM`, `derM_comm`;
* `actM u v B μ = u B_μ v - (∂_μ u) v` — **the gauge action** of a gauge `u` with inverse `v`;
  `actM_one`, `actM_comp` (**composition law** `(e u)·B = e·(u·B)` for `u v = 1`),
  `gaugeAct_eq_actM` (the IFT gauge action is the case `u = e^X`, `v = e^{-X}`);
* `curvMS a μ ν = ∂_μ a_ν - ∂_ν a_μ + [a_μ, a_ν]` and `curvMS_actM` (**gauge covariance of
  the curvature**: `F_{u·B} = u F_B v`);
* `lapM_actM` (**the gauge equation**): if `a = u·B` is Coulomb (`Σ_μ ∂_μ a_μ = 0`) then
  `Δu = u (Σ B_μ B_μ + ∂_μ B_μ) - 2 Σ a_μ u B_μ + Σ a_μ a_μ u`.

The algebraic identities are proved in an arbitrary ring (`ring_curv_identity`,
`ring_comp_identity`, `ring_lap_identity`) and transported.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

/-! ### Conjugation on the complexification -/

namespace Cx

variable {V : Type*} [CommRing V]

instance instStar : Star (Cx V) := ⟨fun z => ⟨z.re, -z.im⟩⟩

@[simp] theorem star_re' (z : Cx V) : (star z).re = z.re := rfl
@[simp] theorem star_im' (z : Cx V) : (star z).im = -z.im := rfl

instance instStarRing : StarRing (Cx V) where
  star_involutive z := by ext <;> simp
  star_mul z w := by ext <;> simp <;> ring
  star_add z w := by ext <;> simp <;> ring

theorem norm_star' {W : Type*} [NormedCommRing W] [NormedAlgebra ℝ W] (z : Cx W) :
    ‖star z‖ = ‖z‖ := by
  rw [norm_def, norm_def]; simp

instance instContinuousStar {W : Type*} [NormedCommRing W] [NormedAlgebra ℝ W] :
    ContinuousStar (Cx W) where
  continuous_star := by
    refine (Isometry.of_dist_eq fun z w => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, norm_star']

end Cx

/-! ### Derivatives commute -/

section Commute

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)]

/-- Derivatives commute with restriction. -/
theorem derS_restrS (i : Fin 4) (F : SobAlg c r (s + 2)) :
    derS i (restrS (Nat.le_succ (s + 1)) F) = restrS (Nat.le_succ s) (derS i F) := by
  apply ext_fn
  have h1 := weak_derS (c := c) (r := r) i (restrS (Nat.le_succ (s + 1)) F)
  have h2 := weak_derS (c := c) (r := r) i F
  rw [fn_restrS] at h1
  have := weakR_ae_eq (isOpen_euclBall c r) h1 h2 (memLp_fn _) (memLp_fn _)
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_euclBall c r)]
  filter_upwards [this] with x hx hxB
  rw [hx hxB, fn_restrS]

/-- **Weak derivatives commute** (Schwarz). -/
theorem derS_comm (i j : Fin 4) (F : SobAlg c r (s + 2)) :
    derS i (derS j F) = derS j (derS i F) := by
  apply ext_fn
  refine ae_eq_of_integral_test (memLp_fn _) (memLp_fn _) fun φ hφ => ?_
  have key : ∀ i j : Fin 4, ∫ x, φ x * fn (derS i (derS j F)) x =
      ∫ x, pd (pd φ i) j x * fn F x := by
    intro i j
    have h1 := weak_derS (c := c) (r := r) i (derS j F) φ hφ
    have h2 := weak_derS (c := c) (r := r) j F (pd φ i) (isTest_pd hφ i)
    linarith
  rw [key i j, key j i]
  congr 1
  funext x
  rw [pd_pd_symm (hφ.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) j i x]

end Commute

/-! ### Matrix fields: conjugation and commuting derivatives -/

section Matrix

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m : ℕ}

theorem derM_star (μ : Fin 4) (X : MatSob c r (s + 1) m) :
    derM μ (star X) = star (derM μ X) := by
  ext i j <;> simp [derM_apply, Matrix.star_apply]

theorem rhoM_star (X : MatSob c r (s + 1) m) : rhoM (star X) = star (rhoM X) := by
  ext i j <;> simp [rhoM_apply, Matrix.star_apply]

theorem derM_rhoM (μ : Fin 4) (X : MatSob c r (s + 2) m) :
    derM μ (rhoM X) = rhoM (derM μ X) := by
  ext i j
  · exact derS_restrS μ (X i j).re
  · exact derS_restrS μ (X i j).im

theorem derM_comm (μ ν : Fin 4) (X : MatSob c r (s + 2) m) :
    derM μ (derM ν X) = derM ν (derM μ X) := by
  ext i j
  · exact derS_comm μ ν (X i j).re
  · exact derS_comm μ ν (X i j).im

theorem evC_star (z : Cx (SobAlg c r s)) :
    evC (star z) =ᵐ[volume.restrict (euclBall c r)] fun x => star (evC z x) := by
  filter_upwards [fn_neg z.im] with x hx
  simp only [evC, Cx.star_re', Cx.star_im', hx]
  apply Complex.ext <;> simp

theorem evM_star (X : MatSob c r s m) :
    evM (star X) =ᵐ[volume.restrict (euclBall c r)] fun x => star (evM X x) :=
  ae_matrix_of_entries fun i j => by
    filter_upwards [evC_star (X j i)] with x hx
    simp only [evM_apply, Matrix.star_apply]
    exact hx

end Matrix

/-! ### Ring identities -/

section RingIdentities

variable {R : Type*} [Ring R]

/-- The composition identity of the gauge action. -/
theorem ring_comp_identity (Pe Pu Pv Pe' B De Du : R) (h : Pu * Pv = 1) :
    Pe * Pu * B * (Pv * Pe') - (De * Pu + Pe * Du) * (Pv * Pe') =
      Pe * (Pu * B * Pv - Du * Pv) * Pe' - De * Pe' := by
  have key : De * Pu * (Pv * Pe') = De * Pe' := by
    rw [← mul_assoc, mul_assoc De, h, mul_one]
  rw [show Pe * Pu * B * (Pv * Pe') - (De * Pu + Pe * Du) * (Pv * Pe') =
      Pe * (Pu * B * Pv - Du * Pv) * Pe' - De * Pu * (Pv * Pe') by noncomm_ring, key]

/-- **The curvature identity** `F_{u·B} = u F_B v` in a ring, with `Q P = 1`, the derivative of
the inverse `∂v = -v (∂u) v` and symmetric second derivatives. -/
theorem ring_curv_identity (P Q : R) (U : Fin 4 → R) (B : Fin 4 → R) (dB ddU : Fin 4 → Fin 4 → R)
    (hQP : Q * P = 1) (μ ν : Fin 4) (hsym : ddU μ ν = ddU ν μ) :
    (U μ * B ν * Q + P * dB μ ν * Q + P * B ν * (-(Q * U μ * Q)) - ddU μ ν * Q -
        U ν * (-(Q * U μ * Q))) -
      (U ν * B μ * Q + P * dB ν μ * Q + P * B μ * (-(Q * U ν * Q)) - ddU ν μ * Q -
        U μ * (-(Q * U ν * Q))) +
      ((P * B μ * Q - U μ * Q) * (P * B ν * Q - U ν * Q) -
        (P * B ν * Q - U ν * Q) * (P * B μ * Q - U μ * Q)) =
      P * (dB μ ν - dB ν μ + (B μ * B ν - B ν * B μ)) * Q := by
  have hQP' : ∀ Y : R, Q * (P * Y) = Y := fun Y => by rw [← mul_assoc, hQP, one_mul]
  rw [hsym]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_neg, mul_assoc, hQP,
    hQP', mul_one]
  abel

/-- **The gauge equation** in a ring: with `Du_μ = P B_μ - a_μ P` and `Σ ∂_μ a_μ = 0`,
`Σ ∂_μ Du_μ = P Σ (B_μ B_μ + ∂_μ B_μ) - 2 Σ a_μ P B_μ + Σ a_μ a_μ P`. -/
theorem ring_lap_identity (P : R) (B a dB da : Fin 4 → R) (hdiv : ∑ μ, da μ = 0) :
    ∑ μ, ((P * B μ - a μ * P) * B μ + P * dB μ - (da μ * P + a μ * (P * B μ - a μ * P))) =
      P * ∑ μ, (B μ * B μ + dB μ) - 2 * ∑ μ, a μ * P * B μ + ∑ μ, a μ * a μ * P := by
  have h1 : ∑ μ, da μ * P = 0 := by rw [← Finset.sum_mul, hdiv, zero_mul]
  have e : ∑ μ, ((P * B μ - a μ * P) * B μ + P * dB μ - (da μ * P + a μ * (P * B μ - a μ * P))) =
      ∑ μ, (P * (B μ * B μ + dB μ) - 2 * (a μ * P * B μ) + a μ * a μ * P) - ∑ μ, da μ * P := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    noncomm_ring
  rw [e, h1, sub_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

end RingIdentities

/-! ### The gauge action -/

section Action

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m : ℕ}

/-- **The gauge action** `u·B = u B v - (∂u) v` of a gauge `u` with inverse `v`. -/
def actM (u v : MatSob c r (s + 1) m) (B : Fin 4 → MatSob c r s m) (μ : Fin 4) :
    MatSob c r s m :=
  rhoM u * B μ * rhoM v - derM μ u * rhoM v

theorem actM_one (B : Fin 4 → MatSob c r s m) : actM 1 1 B = B := by
  funext μ
  simp [actM, derM_one]

/-- **Composition law** of the gauge action: `(e u)·B = e·(u·B)` when `u v = 1`. -/
theorem actM_comp {u v : MatSob c r (s + 1) m} (huv : u * v = 1) (e e' : MatSob c r (s + 1) m)
    (B : Fin 4 → MatSob c r s m) :
    actM (e * u) (v * e') B = actM e e' (actM u v B) := by
  funext μ
  have h : rhoM u * rhoM v = 1 := by rw [← map_mul, huv, map_one]
  simp only [actM, map_mul, derM_mul]
  exact ring_comp_identity _ _ _ _ _ _ _ h

/-- The IFT gauge action is the gauge action of `e^X` with inverse `e^{-X}`. -/
theorem gaugeAct_eq_actM {d : ℕ} (L : LieBasis m d) (a : Fin 4 → Fin d → SobAlg c r 4)
    (ξ : Fin d → SobAlg c r 5) :
    gaugeAct L a ξ = actM (exp (embX L ξ)) (exp (-embX L ξ)) (fun μ => embX L (a μ)) := rfl

/-- The curvature `F_{μν} = ∂_μ a_ν - ∂_ν a_μ + [a_μ, a_ν]` of a matrix connection. -/
def curvMS (a : Fin 4 → MatSob c r (s + 1) m) (μ ν : Fin 4) : MatSob c r s m :=
  derM μ (a ν) - derM ν (a μ) + (rhoM (a μ) * rhoM (a ν) - rhoM (a ν) * rhoM (a μ))

/-- The derivative of the inverse: `∂v = -v (∂u) v` when `u v = 1`. -/
theorem derM_inv {u v : MatSob c r (s + 1) m} (huv : u * v = 1) (μ : Fin 4) :
    derM μ v = -(rhoM v * derM μ u * rhoM v) := by
  have hvu : v * u = 1 := mul_eq_one_comm.mp huv
  have h0 : derM μ u * rhoM v + rhoM u * derM μ v = 0 := by
    rw [← derM_mul, huv, derM_one]
  have hvu' : rhoM v * rhoM u = 1 := by rw [← map_mul, hvu, map_one]
  have : derM μ v = rhoM v * (rhoM u * derM μ v) := by rw [← mul_assoc, hvu', one_mul]
  rw [this, eq_neg_of_add_eq_zero_right h0]
  noncomm_ring

/-- **Gauge covariance of the curvature**: `F_{u·B} = u F_B v` when `u v = 1`. -/
theorem curvMS_actM {u v : MatSob c r (s + 2) m} (huv : u * v = 1)
    (B : Fin 4 → MatSob c r (s + 1) m) (μ ν : Fin 4) :
    curvMS (actM u v B) μ ν = rhoM (rhoM u) * curvMS B μ ν * rhoM (rhoM v) := by
  have hvu : v * u = 1 := mul_eq_one_comm.mp huv
  have hQP : rhoM (rhoM v) * rhoM (rhoM u) = 1 := by
    rw [← map_mul, ← map_mul, hvu, map_one, map_one]
  have hder : ∀ κ, derM κ (rhoM v) = -(rhoM (rhoM v) * rhoM (derM κ u) * rhoM (rhoM v)) := by
    intro κ
    rw [derM_rhoM, derM_inv huv κ, map_neg, map_mul, map_mul]
  have hsym : derM μ (derM ν u) = derM ν (derM μ u) := derM_comm μ ν u
  simp only [curvMS, actM, map_sub, map_mul, derM_mul, derM_rhoM, hder]
  have := ring_curv_identity (rhoM (rhoM u)) (rhoM (rhoM v)) (fun κ => rhoM (derM κ u))
    (fun κ => rhoM (B κ)) (fun κ κ' => derM κ (B κ')) (fun κ κ' => derM κ (derM κ' u)) hQP μ ν
    hsym
  rw [← this]
  noncomm_ring

/-- The Laplacian of a matrix field. -/
def lapM (u : MatSob c r (s + 2) m) : MatSob c r s m := ∑ μ, derM μ (derM μ u)

/-- `∂_μ u = u B_μ - a_μ u` for the gauge-transformed connection `a = u·B` (`u v = 1`). -/
theorem derM_eq_of_actM {u v : MatSob c r (s + 1) m} (huv : u * v = 1)
    (B : Fin 4 → MatSob c r s m) (μ : Fin 4) :
    derM μ u = rhoM u * B μ - actM u v B μ * rhoM u := by
  have hvu : v * u = 1 := mul_eq_one_comm.mp huv
  have hvu' : rhoM v * rhoM u = 1 := by rw [← map_mul, hvu, map_one]
  simp only [actM]
  have e1 : (rhoM u * B μ * rhoM v - derM μ u * rhoM v) * rhoM u =
      rhoM u * B μ * (rhoM v * rhoM u) - derM μ u * (rhoM v * rhoM u) := by noncomm_ring
  rw [e1, hvu', mul_one, mul_one]
  abel

/-- **The gauge equation**: for a Coulomb gauge-transformed connection `a = u·B`
(`Σ_μ ∂_μ a_μ = 0`, `u v = 1`),
`Δu = u Σ_μ (B_μ B_μ + ∂_μ B_μ) - 2 Σ_μ a_μ u B_μ + Σ_μ a_μ a_μ u`. -/
theorem lapM_actM {u v : MatSob c r (s + 2) m} (huv : u * v = 1)
    (B : Fin 4 → MatSob c r (s + 1) m) (hcoul : ∑ μ, derM μ (actM u v B μ) = 0) :
    lapM u = rhoM (rhoM u) * ∑ μ, (rhoM (B μ) * rhoM (B μ) + derM μ (B μ)) -
      2 * ∑ μ, rhoM (actM u v B μ) * rhoM (rhoM u) * rhoM (B μ) +
      ∑ μ, rhoM (actM u v B μ) * rhoM (actM u v B μ) * rhoM (rhoM u) := by
  have hD : ∀ μ, derM μ (derM μ u) = (rhoM (rhoM u) * rhoM (B μ) -
      rhoM (actM u v B μ) * rhoM (rhoM u)) * rhoM (B μ) + rhoM (rhoM u) * derM μ (B μ) -
      (derM μ (actM u v B μ) * rhoM (rhoM u) + rhoM (actM u v B μ) *
        (rhoM (rhoM u) * rhoM (B μ) - rhoM (actM u v B μ) * rhoM (rhoM u))) := by
    intro μ
    have h1 := derM_eq_of_actM huv B μ
    have h2 : rhoM (derM μ u) = rhoM (rhoM u) * rhoM (B μ) -
        rhoM (actM u v B μ) * rhoM (rhoM u) := by
      rw [h1, map_sub, map_mul, map_mul]
    rw [h1, map_sub, derM_mul, derM_mul, derM_rhoM, h2]
  unfold lapM
  simp_rw [hD]
  exact ring_lap_identity _ _ _ _ _ hcoul

end Action

end RenewalGeometry.BallAnalysis.BallAlg
