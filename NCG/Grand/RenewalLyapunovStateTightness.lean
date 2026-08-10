/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PhysicalRate
import NCG.Grand.StateTightness
import NCG.Upstream.PrimitiveWeight

/-!
# Renewal Lyapunov drift and spectral state tightness

This file supplies the finite-matrix operator-to-state and spectral-measure
layer of `thm:renewal-Lyapunov-tightness`.  It constructs the spectral law of
a Hermitian field in a density state, proves the CFC moment identity, and
combines the operator Lyapunov and screen inequalities with the manuscript's
uniform scalar bounds and finite Markov estimate.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace RenewalLyapunovStateTightness

open Upstream.PrimitiveWeight

/-- Evaluation of a matrix observable in a density-matrix state. -/
noncomputable def matrixStateValue {n : ℕ}
    (rho A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((rho * A).trace).re

theorem matrixStateValue_one {n : ℕ}
    {rho : Matrix (Fin n) (Fin n) ℂ} (hrho : rho ∈ densitySet n ℂ) :
    matrixStateValue rho 1 = 1 := by
  simp [matrixStateValue, hrho.2]

theorem matrixStateValue_add {n : ℕ}
    (rho A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixStateValue rho (A + B) =
      matrixStateValue rho A + matrixStateValue rho B := by
  simp [matrixStateValue, mul_add, trace_add, Complex.add_re]

theorem matrixStateValue_sub {n : ℕ}
    (rho A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixStateValue rho (A - B) =
      matrixStateValue rho A - matrixStateValue rho B := by
  simp [matrixStateValue, mul_sub, trace_sub, Complex.sub_re]

theorem matrixStateValue_real_smul {n : ℕ}
    (rho A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    matrixStateValue rho (((c : ℝ) : ℂ) • A) =
      c * matrixStateValue rho A := by
  simp [matrixStateValue, trace_smul, Complex.mul_re]

/-- Positive matrix order is respected by every density-matrix state. -/
theorem matrixStateValue_mono {n : ℕ}
    {rho A B : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hAB : (B - A).PosSemidef) :
    matrixStateValue rho A ≤ matrixStateValue rho B := by
  have hprod := trace_mul_psd_nonneg hrho.1 hAB
  have hre : 0 ≤ ((rho * (B - A)).trace).re :=
    (RCLike.nonneg_iff.mp hprod).1
  rw [mul_sub, trace_sub, Complex.sub_re] at hre
  exact sub_nonneg.mp hre

/-- The spectral weight of an eigenvalue in a density state: the corresponding
diagonal entry of the density matrix in the field eigenbasis. -/
noncomputable def spectralWeight {n : ℕ}
    (rho F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian)
    (i : Fin n) : ℝ :=
  let U : Matrix (Fin n) (Fin n) ℂ := hF.eigenvectorUnitary
  ((star U * rho * U) i i).re

theorem spectralWeight_nonneg {n : ℕ}
    {rho F : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hF : F.IsHermitian) (i : Fin n) :
    0 ≤ spectralWeight rho F hF i := by
  let U : Matrix (Fin n) (Fin n) ℂ := hF.eigenvectorUnitary
  have hU : IsUnit U := Unitary.isUnit_coe
  have hconj : (star U * rho * U).PosSemidef :=
    (hU.posSemidef_star_left_conjugate_iff).mpr hrho.1
  exact (RCLike.nonneg_iff.mp (hconj.diag_nonneg (i := i))).1

theorem spectralWeight_sum_one {n : ℕ}
    {rho F : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hF : F.IsHermitian) :
    ∑ i, spectralWeight rho F hF i = 1 := by
  let U : Matrix (Fin n) (Fin n) ℂ := hF.eigenvectorUnitary
  have hUU : U * star U = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hF.eigenvectorUnitary.2
  have htrace : (star U * rho * U).trace = 1 := by
    rw [trace_mul_cycle, hUU, one_mul, hrho.2]
  calc
    ∑ i, spectralWeight rho F hF i =
        ((star U * rho * U).trace).re := by
      simp only [spectralWeight, U]
      rw [Matrix.trace]
      change ∑ i, ((star U * rho * U) i i).re =
        Complex.reAddGroupHom (∑ i, (star U * rho * U) i i)
      rw [map_sum]
      simp [Complex.coe_reAddGroupHom]
    _ = 1 := by rw [htrace]; norm_num

/-- CFC expectations are exactly moments of the finite spectral law. -/
theorem matrixStateValue_cfc_eq_spectralSum {n : ℕ}
    (rho F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian)
    (f : ℝ → ℝ) :
    matrixStateValue rho (hF.cfc f) =
      ∑ i, spectralWeight rho F hF i * f (hF.eigenvalues i) := by
  let U : Matrix (Fin n) (Fin n) ℂ := hF.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (RCLike.ofReal ∘ f ∘ hF.eigenvalues)
  have hcfc : hF.cfc f = U * D * star U := by
    rfl
  rw [matrixStateValue, hcfc]
  have hcycle : (rho * (U * D * star U)).trace =
      ((star U * rho * U) * D).trace := by
    rw [show rho * (U * D * star U) = rho * U * D * star U by
      simp [Matrix.mul_assoc]]
    rw [trace_mul_cycle]
    simp [Matrix.mul_assoc]
  rw [hcycle]
  have hdiag : ((star U * rho * U) * D).trace =
      ∑ i, (star U * rho * U) i i * ((f (hF.eigenvalues i) : ℝ) : ℂ) := by
    simp [Matrix.trace, D]
  rw [hdiag]
  change Complex.reAddGroupHom
      (∑ i, (star U * rho * U) i i * ((f (hF.eigenvalues i) : ℝ) : ℂ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [spectralWeight, U, Complex.mul_re]

/-- The concrete spectral law of a Hermitian matrix in a density state is a
probability law. -/
theorem spectralLaw_probability {n : ℕ}
    {rho F : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hF : F.IsHermitian) :
    (∀ i, 0 ≤ spectralWeight rho F hF i) ∧
      ∑ i, spectralWeight rho F hF i = 1 :=
  ⟨spectralWeight_nonneg hrho hF, spectralWeight_sum_one hrho hF⟩

/-- A CFC `p`-moment bound gives the exact spectral tail estimate. -/
theorem matrixState_spectral_tightness {n : ℕ}
    {rho F : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hF : F.IsHermitian)
    (p R Cp : ℝ) (hp : 0 < p) (hR : 0 < R)
    (hmoment : matrixStateValue rho
      (hF.cfc (fun x ↦ |x| ^ p)) ≤ Cp) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ R < |hF.eigenvalues i|),
        spectralWeight rho F hF i ≤ Cp / R ^ p := by
  apply spectral_tightness Finset.univ
    (spectralWeight rho F hF) hF.eigenvalues p R Cp
  · intro i hi
    exact spectralWeight_nonneg hrho hF i
  · exact hR
  · exact hp
  · simpa [matrixStateValue_cfc_eq_spectralSum] using hmoment

/-- An operator Lyapunov inequality becomes the two boxed stationary state
bounds after applying a stationary density state. -/
theorem stationary_lyapunov_bound {n : ℕ}
    {rho V RV : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ)
    (hstationary : matrixStateValue rho RV = matrixStateValue rho V)
    (kappa b tau taumax : ℝ)
    (hkappa : 0 < kappa) (htau : 0 < tau) (htauMax : tau ≤ taumax)
    (hb : 0 ≤ b)
    (hdrift : (((Real.exp (-(kappa * tau)) : ℝ) : ℂ) • V +
      (((b * tau : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) - RV).PosSemidef) :
    matrixStateValue rho V ≤
        b * tau / (1 - Real.exp (-(kappa * tau))) ∧
      b * tau / (1 - Real.exp (-(kappa * tau))) ≤
        b * Real.exp (kappa * taumax) / kappa := by
  have hscalar : matrixStateValue rho V ≤
      Real.exp (-(kappa * tau)) * matrixStateValue rho V + b * tau := by
    have hm := matrixStateValue_mono hrho hdrift
    rw [matrixStateValue_add, matrixStateValue_real_smul,
      matrixStateValue_real_smul, matrixStateValue_one hrho, hstationary] at hm
    simpa using hm
  have h := renewal_lyapunov_tightness kappa b tau taumax
    (matrixStateValue rho V) hkappa htau htauMax hb hscalar
  exact ⟨h.1, h.2.1⟩

/-- Screen domination turns the uniform Lyapunov bound into the manuscript's
uniform compact-screen tail estimate. -/
theorem stationary_screen_tail_bound {n : ℕ}
    {rho V P : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ)
    (kappa b taumax psi C : ℝ)
    (hpsi : 0 < psi)
    (hVbound : matrixStateValue rho V ≤ C)
    (huniform : C ≤ b * Real.exp (kappa * taumax) / kappa)
    (hscreen : (V - (((psi : ℝ) : ℂ) •
      ((1 : Matrix (Fin n) (Fin n) ℂ) - P))).PosSemidef) :
    matrixStateValue rho ((1 : Matrix (Fin n) (Fin n) ℂ) - P) ≤
      b * Real.exp (kappa * taumax) / (kappa * psi) := by
  have hm := matrixStateValue_mono hrho hscreen
  rw [matrixStateValue_real_smul] at hm
  have htail : matrixStateValue rho ((1 : Matrix (Fin n) (Fin n) ℂ) - P)
      ≤ C / psi := by
    rw [le_div_iff₀ hpsi]
    nlinarith [hm.trans hVbound]
  calc
    matrixStateValue rho ((1 : Matrix (Fin n) (Fin n) ℂ) - P)
        ≤ C / psi := htail
    _ ≤ (b * Real.exp (kappa * taumax) / kappa) / psi :=
      div_le_div_of_nonneg_right huniform hpsi.le
    _ = b * Real.exp (kappa * taumax) / (kappa * psi) := by ring

/-- Operator moment domination plus a Lyapunov expectation bound yields a
uniformly tight concrete spectral law. -/
theorem dominated_field_spectral_tightness {n : ℕ}
    {rho V F : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (hF : F.IsHermitian)
    (a c C p R : ℝ) (ha : 0 ≤ a) (hp : 0 < p) (hR : 0 < R)
    (hVbound : matrixStateValue rho V ≤ C)
    (hdom : ((((a : ℝ) : ℂ) • V +
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) -
      hF.cfc (fun x ↦ |x| ^ p)).PosSemidef)) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ R < |hF.eigenvalues i|),
        spectralWeight rho F hF i ≤ (a * C + c) / R ^ p := by
  have hm := matrixStateValue_mono hrho hdom
  rw [matrixStateValue_add, matrixStateValue_real_smul,
    matrixStateValue_real_smul, matrixStateValue_one hrho] at hm
  have hmoment : matrixStateValue rho (hF.cfc (fun x ↦ |x| ^ p)) ≤
      a * C + c := by
    nlinarith [hm, mul_le_mul_of_nonneg_left hVbound ha]
  exact matrixState_spectral_tightness (rho := rho) (F := F)
    hrho hF p R (a * C + c) hp hR hmoment

end RenewalLyapunovStateTightness
end NCG
