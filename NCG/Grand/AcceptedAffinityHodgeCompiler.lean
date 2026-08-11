/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CycleProjector

/-!
# Finite accepted-affinity Hodge compiler

This module proves the exact finite Hodge package used by
thm:accepted-affinity-Hodge.  For an arbitrary oriented incidence matrix B,
the spectral Moore--Penrose inverse of B Bᴴ constructs the cut and cycle
projectors.  An edge affinity is a gradient exactly when its cycle projection
vanishes, equivalently when every cycle period vanishes.  The canonical
Moore--Penrose potential attains the least-squares lower bound.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace AcceptedAffinityHodgeCompiler

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq E]

/-- Every algebraic cycle has zero period against the edge cochain. -/
def CyclePeriodsVanish (B : Matrix V E ℂ) (ell : E → ℂ) : Prop :=
  ∀ z : E → ℂ, B *ᵥ z = 0 → star z ⬝ᵥ ell = 0

/-- Squared Euclidean edge norm, written without a choice of basis object. -/
def edgeEnergy (x : E → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

omit [DecidableEq E] in
theorem edgeEnergy_nonneg (x : E → ℂ) : 0 ≤ edgeEnergy x := by
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)

omit [DecidableEq E] in
theorem edgeEnergy_add_of_orthogonal
    (x y : E → ℂ) (hxy : star x ⬝ᵥ y = 0) :
    edgeEnergy (x + y) = edgeEnergy x + edgeEnergy y := by
  have hyx : star y ⬝ᵥ x = 0 := by
    have h := star_dotProduct x y
    rw [hxy] at h
    simpa using congrArg star h.symm
  have hcross :
      ∑ i, (x i * (starRingEnd ℂ) (y i)).re = 0 := by
    have hre := congrArg Complex.re hyx
    simpa [dotProduct, mul_comm] using hre
  simp only [edgeEnergy, Pi.add_apply, Complex.normSq_add,
    Finset.sum_add_distrib]
  have hcross2 :
      ∑ i, 2 * (x i * (starRingEnd ℂ) (y i)).re = 0 := by
    calc
      ∑ i, 2 * (x i * (starRingEnd ℂ) (y i)).re =
          2 * ∑ i, (x i * (starRingEnd ℂ) (y i)).re := by
            rw [Finset.mul_sum]
      _ = 0 := by rw [hcross, mul_zero]
  rw [hcross2]
  ring

omit [Fintype V] [DecidableEq E] in
/-- A spanning forest supplies a finite family of fundamental cycles spanning
the whole cycle space, so it suffices to audit only their periods. -/
theorem cyclePeriodsVanish_iff_fundamentalCyclePeriods
    {I : Type*} [Fintype I]
    (B : Matrix V E ℂ) (cycles : I → E → ℂ)
    (hcycles : ∀ i, B *ᵥ cycles i = 0)
    (hcomplete : ∀ z : E → ℂ, B *ᵥ z = 0 →
      ∃ c : I → ℂ, z = ∑ i, c i • cycles i)
    (ell : E → ℂ) :
    CyclePeriodsVanish B ell ↔
      ∀ i, star (cycles i) ⬝ᵥ ell = 0 := by
  constructor
  · intro h i
    exact h (cycles i) (hcycles i)
  · intro h z hz
    obtain ⟨c, rfl⟩ := hcomplete z hz
    simp only [dotProduct, Pi.star_apply, Finset.sum_apply,
      Pi.smul_apply, star_sum, smul_eq_mul, star_mul', Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    calc
      ∑ x, (starRingEnd ℂ) (c i) *
          (starRingEnd ℂ) (cycles i x) * ell x =
          (starRingEnd ℂ) (c i) *
            ∑ x, (starRingEnd ℂ) (cycles i x) * ell x := by
              simp only [mul_assoc, Finset.mul_sum]
      _ = 0 := by
        change (starRingEnd ℂ) (c i) * (star (cycles i) ⬝ᵥ ell) = 0
        rw [h i, mul_zero]

/-- Exact operator package for the accepted affinity Hodge theorem. -/
theorem acceptedAffinityHodgeCompiler (B : Matrix V E ℂ) :
    ∃ G : Matrix V V ℂ,
      let Pcut : Matrix E E ℂ := Bᴴ * G * B
      let Pcyc : Matrix E E ℂ := 1 - Pcut
      Gᴴ = G ∧
      Pcyc * Pcyc = Pcyc ∧
      Pcycᴴ = Pcyc ∧
      B * Pcyc = 0 ∧
      Pcyc * Bᴴ = 0 ∧
      (∀ ell : E → ℂ,
        (∃ F : V → ℂ, ell = -(Bᴴ *ᵥ F)) ↔ Pcyc *ᵥ ell = 0) ∧
      (∀ ell : E → ℂ,
        Pcyc *ᵥ ell = 0 ↔ CyclePeriodsVanish B ell) ∧
      (∀ ell : E → ℂ,
        let Fstar : V → ℂ := -(G *ᵥ (B *ᵥ ell))
        ell = -(Bᴴ *ᵥ Fstar) + Pcyc *ᵥ ell) ∧
      (∀ ell : E → ℂ,
        let Fstar : V → ℂ := -(G *ᵥ (B *ᵥ ell))
        (∀ F : V → ℂ,
          edgeEnergy (Pcyc *ᵥ ell) ≤
            edgeEnergy (ell + Bᴴ *ᵥ F)) ∧
        edgeEnergy (ell + Bᴴ *ᵥ Fstar) =
          edgeEnergy (Pcyc *ᵥ ell)) := by
  classical
  let L := B * Bᴴ
  have hL : L.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self B
  let G :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse L hL
  have hG : Gᴴ = G :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_isHermitian L hL
  have h1 : L * G * L = L :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_left L hL
  have h2 : G * L * G = G :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_right L hL
  obtain ⟨hP2, hPH, hBP, hfix, _⟩ :=
    cycle_projector B G hG (by simpa [L, Matrix.mul_assoc] using h1)
      (by simpa [L] using h2)
  let Pcut : Matrix E E ℂ := Bᴴ * G * B
  let Pcyc : Matrix E E ℂ := 1 - Pcut
  have hPBH : Pcyc * Bᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hBP
    simpa [Pcyc, hPH] using h
  have hgradIff : ∀ ell : E → ℂ,
      (∃ F : V → ℂ, ell = -(Bᴴ *ᵥ F)) ↔ Pcyc *ᵥ ell = 0 := by
    intro ell
    constructor
    · rintro ⟨F, rfl⟩
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hPBH,
        Matrix.zero_mulVec, neg_zero]
    · intro hell
      refine ⟨-(G *ᵥ (B *ᵥ ell)), ?_⟩
      have hzero :
          ell - Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell)) = 0 := by
        simpa [Pcyc, Pcut, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mul_assoc] using hell
      simpa [Matrix.mulVec_neg] using sub_eq_zero.mp hzero
  refine ⟨G, hG, hP2, hPH, hBP, hPBH, hgradIff, ?_, ?_, ?_⟩
  · intro ell
    constructor
    · intro hell z hz
      have hgrad :
          ∃ F : V → ℂ, ell = -(Bᴴ *ᵥ F) :=
        (hgradIff ell).2 hell
      obtain ⟨F, rfl⟩ := hgrad
      rw [dotProduct_neg, Matrix.dotProduct_mulVec,
        ← Matrix.star_mulVec, hz]
      simp
    · intro hperiod
      let z := Pcyc *ᵥ ell
      have hzcycle : B *ᵥ z = 0 := by
        dsimp only [z]
        rw [Matrix.mulVec_mulVec, hBP, Matrix.zero_mulVec]
      have hperiodz : star z ⬝ᵥ ell = 0 := hperiod z hzcycle
      have hnorm : star z ⬝ᵥ z = star z ⬝ᵥ ell := by
        dsimp only [z]
        rw [Matrix.star_mulVec, hPH]
        rw [← Matrix.dotProduct_mulVec]
        rw [Matrix.mulVec_mulVec, hP2]
        rw [Matrix.dotProduct_mulVec]
      have hself : star z ⬝ᵥ z = 0 := hnorm.trans hperiodz
      exact dotProduct_star_self_eq_zero.mp hself
  · intro ell
    dsimp only
    have hdecomp :
        ell = Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell)) + Pcyc *ᵥ ell := by
      simp [Pcyc, Pcut, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    simpa [Matrix.mulVec_neg] using hdecomp
  · intro ell
    dsimp only
    constructor
    · intro F
      let z := Pcyc *ᵥ ell
      let w := (1 - Pcyc) *ᵥ ell + Bᴴ *ᵥ F
      have hPw : Pcyc *ᵥ w = 0 := by
        dsimp only [w]
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec,
          Matrix.mul_sub, Matrix.mul_one, hP2, sub_self,
          Matrix.zero_mulVec, zero_add, Matrix.mulVec_mulVec,
          hPBH, Matrix.zero_mulVec]
      have horth : star z ⬝ᵥ w = 0 := by
        dsimp only [z]
        rw [Matrix.star_mulVec, hPH, ← Matrix.dotProduct_mulVec, hPw]
        simp
      have hsum : ell + Bᴴ *ᵥ F = z + w := by
        simp [z, w, Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [hsum, edgeEnergy_add_of_orthogonal z w horth]
      exact le_add_of_nonneg_right (edgeEnergy_nonneg w)
    · have hresidual :
          ell + Bᴴ *ᵥ (-(G *ᵥ (B *ᵥ ell))) = Pcyc *ᵥ ell := by
        have hdecomp :
            ell = Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell)) + Pcyc *ᵥ ell := by
          simp [Pcyc, Pcut, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
        rw [Matrix.mulVec_neg]
        calc
          ell + -(Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell))) =
              (Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell)) + Pcyc *ᵥ ell) +
                -(Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell))) :=
            congrArg (fun u => u + -(Bᴴ *ᵥ (G *ᵥ (B *ᵥ ell)))) hdecomp
          _ = Pcyc *ᵥ ell := by abel
      rw [hresidual]

end
end AcceptedAffinityHodgeCompiler
end NCG
