/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevExp
import RenewalGeometry.Analysis.BallSobolevDeriv

/-!
# Calculus on the matrix Banach algebras `H^s(B, M_m(ℂ))`
  (stage D1 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `Cx.mapL`, `Cx.mapRingHom` — componentwise continuous linear maps / ring homomorphisms on the
  complexification; `Cx.ofRe` — the real elements `u + i0`;
* `matMapL` — entrywise continuous linear maps of matrix algebras;
* `rhoM` (restriction `H^{s+1} → H^s`, a ring homomorphism), `derM μ` (the partial derivative, a
  derivation: `derM_mul`), `constM` (constant matrix fields: `derM_constM = 0`), on
  `MatSob c r s m`.
-/

open MeasureTheory Set Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

/-! ### Componentwise maps on the complexification -/

namespace Cx

variable {V W : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] [NormedCommRing W]
  [NormedAlgebra ℝ W]

/-- Componentwise application of a continuous linear map. -/
def mapL (L : V →L[ℝ] W) : Cx V →L[ℝ] Cx W :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨L z.re, L z.im⟩
      map_add' := fun z w => by ext <;> simp
      map_smul' := fun a z => by ext <;> simp }
    ‖L‖ fun z => by
      show ‖L z.re‖ + ‖L z.im‖ ≤ ‖L‖ * (‖z.re‖ + ‖z.im‖)
      rw [mul_add]
      exact add_le_add (L.le_opNorm _) (L.le_opNorm _)

@[simp] theorem mapL_re (L : V →L[ℝ] W) (z : Cx V) : (mapL L z).re = L z.re := rfl
@[simp] theorem mapL_im (L : V →L[ℝ] W) (z : Cx V) : (mapL L z).im = L z.im := rfl

/-- Componentwise application of a ring homomorphism. -/
def mapRingHom (f : V →+* W) : Cx V →+* Cx W where
  toFun z := ⟨f z.re, f z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp] theorem mapRingHom_re (f : V →+* W) (z : Cx V) : (mapRingHom f z).re = f z.re := rfl
@[simp] theorem mapRingHom_im (f : V →+* W) (z : Cx V) : (mapRingHom f z).im = f z.im := rfl

/-- The real elements `u + i0`. -/
def ofRe (u : V) : Cx V := ⟨u, 0⟩

@[simp] theorem ofRe_re (u : V) : (ofRe u).re = u := rfl
@[simp] theorem ofRe_im (u : V) : (ofRe u).im = 0 := rfl

theorem ofRe_mul (u v : V) : ofRe (u * v) = ofRe u * ofRe v := by ext <;> simp

theorem ofRe_mul_eq (u : V) (z : Cx V) : ofRe u * z = ⟨u * z.re, u * z.im⟩ := by
  ext <;> simp

end Cx

/-! ### Entrywise maps of matrices -/

section MatMap

variable {V W : Type*} [NormedCommRing V] [NormedAlgebra ℝ V] [NormedCommRing W]
  [NormedAlgebra ℝ W] {m : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Entrywise application of a continuous linear map to matrices. -/
def matMapL (L : V →L[ℝ] W) :
    Matrix (Fin m) (Fin m) (Cx V) →L[ℝ] Matrix (Fin m) (Fin m) (Cx W) where
  toFun M := M.map (Cx.mapL L)
  map_add' M N := Matrix.ext fun i j => by simp
  map_smul' a M := Matrix.ext fun i j => by simp
  cont := by
    have : Continuous fun M : Matrix (Fin m) (Fin m) (Cx V) => fun i j => Cx.mapL L (M i j) :=
      continuous_pi fun i => continuous_pi fun j =>
        (Cx.mapL L).continuous.comp ((continuous_apply j).comp (continuous_apply i))
    exact this

@[simp] theorem matMapL_apply (L : V →L[ℝ] W) (M : Matrix (Fin m) (Fin m) (Cx V)) (i j : Fin m) :
    matMapL L M i j = Cx.mapL L (M i j) := rfl

end MatMap

/-! ### Restriction and derivatives of matrix fields -/

section RhoDer

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {s : ℕ} [hs : Fact (3 ≤ s)] {m : ℕ}

/-- Restriction `H^{s+1} → H^s` of matrix fields (a ring homomorphism). -/
def rhoM : MatSob c r (s + 1) m →+* MatSob c r s m :=
  (Cx.mapRingHom (restrHom (Nat.le_succ s))).mapMatrix

/-- Restriction as a continuous linear map. -/
def rhoML : MatSob c r (s + 1) m →L[ℝ] MatSob c r s m := matMapL (restrS (Nat.le_succ s))

theorem rhoML_eq (M : MatSob c r (s + 1) m) : rhoML M = rhoM M := rfl

/-- The partial derivative `∂_μ : H^{s+1} → H^s` of matrix fields. -/
def derM (μ : Fin 4) : MatSob c r (s + 1) m →L[ℝ] MatSob c r s m := matMapL (derS μ)

theorem derM_apply (μ : Fin 4) (M : MatSob c r (s + 1) m) (i j : Fin m) :
    derM μ M i j = ⟨derS μ (M i j).re, derS μ (M i j).im⟩ := rfl

theorem rhoM_apply (M : MatSob c r (s + 1) m) (i j : Fin m) :
    rhoM M i j = ⟨restrS (Nat.le_succ s) (M i j).re, restrS (Nat.le_succ s) (M i j).im⟩ := rfl

/-- The derivative on the complexification is a derivation. -/
theorem derCx_mul (μ : Fin 4) (z w : Cx (SobAlg c r (s + 1))) :
    Cx.mapL (derS μ) (z * w) = Cx.mapL (derS μ) z * Cx.mapRingHom (restrHom (Nat.le_succ s)) w +
      Cx.mapRingHom (restrHom (Nat.le_succ s)) z * Cx.mapL (derS μ) w := by
  ext
  · simp only [Cx.mapL_re, Cx.mul_re, Cx.add_re, Cx.mapRingHom_re, Cx.mapRingHom_im, Cx.mapL_im,
      map_sub, derS_mul]
    simp only [restrHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    ring
  · simp only [Cx.mapL_im, Cx.mul_im, Cx.add_im, Cx.mapRingHom_re, Cx.mapRingHom_im, Cx.mapL_re,
      map_add, derS_mul]
    simp only [restrHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    ring

/-- **`∂_μ` is a derivation of the matrix algebras**: `∂(M N) = ∂M · N + M · ∂N`. -/
theorem derM_mul (μ : Fin 4) (M N : MatSob c r (s + 1) m) :
    derM μ (M * N) = derM μ M * rhoM N + rhoM M * derM μ N := by
  refine Matrix.ext fun i j => ?_
  simp only [derM, matMapL_apply, Matrix.mul_apply, map_sum, Matrix.add_apply, derCx_mul,
    Finset.sum_add_distrib]
  rfl

/-- Constant matrix fields. -/
def constM (s : ℕ) [Fact (3 ≤ s)] (X : Matrix (Fin m) (Fin m) ℂ) : MatSob c r s m :=
  Matrix.of fun i j => ⟨(X i j).re • (1 : SobAlg c r s), (X i j).im • (1 : SobAlg c r s)⟩

theorem derS_one (μ : Fin 4) : derS μ (1 : SobAlg c r (s + 1)) = 0 := by
  have h1 : (1 : SobAlg c r (s + 1)) = ofSmooth (fun _ => (1 : ℝ)) contDiff_const := rfl
  rw [h1, derS_ofSmooth]
  have h2 : pd (fun _ : Fin 4 → ℝ => (1 : ℝ)) μ = fun _ => 0 := by funext x; simp [pd]
  refine ext_fn ?_
  filter_upwards [fn_ofSmooth (c := c) (r := r) (s := s) (contDiff_pd (contDiff_const (c := (1:ℝ))) μ),
    fn_zero (c := c) (r := r) (s := s)] with x e1 e2
  rw [e1, e2, h2]

theorem derM_constM (μ : Fin 4) (X : Matrix (Fin m) (Fin m) ℂ) :
    derM μ (constM (c := c) (r := r) (s + 1) X) = 0 := by
  ext i j
  · simp [derM_apply, constM, derS_one]
  · simp [derM_apply, constM, derS_one]

theorem rhoM_constM (X : Matrix (Fin m) (Fin m) ℂ) :
    rhoM (constM (c := c) (r := r) (s + 1) X) = constM s X := by
  ext i j
  · simp only [rhoM_apply, constM, Matrix.of_apply, map_smul]
    rw [restrS_one]
  · simp only [rhoM_apply, constM, Matrix.of_apply, map_smul]
    rw [restrS_one]

theorem derM_one (μ : Fin 4) : derM μ (1 : MatSob c r (s + 1) m) = 0 := by
  ext i j
  · by_cases h : i = j
    · subst h; simp [derM_apply, derS_one]
    · simp [derM_apply, Matrix.one_apply_ne h]
  · by_cases h : i = j
    · subst h; simp [derM_apply]
    · simp [derM_apply, Matrix.one_apply_ne h]

end RhoDer

end RenewalGeometry.BallAnalysis.BallAlg
