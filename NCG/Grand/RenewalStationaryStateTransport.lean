/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StateTransport
import NCG.Grand.SummableCorrections
import NCG.Upstream.PrimitiveWeight

/-!
# Stationary renewal states and cutoff transport

This file supplies the finite-matrix state-space layer of
`thm:renewal-state-transport`.  A trace-preserving positive renewal map has a
stationary density by Cesàro compactness.  Strict contraction on traceless
Hermitian matrices makes that density unique.  A positive trace-preserving
cutoff restriction then transports stationary states exactly under exact
intertwining and with the sharp `δ / (1 - q)` bound under an approximate
intertwining estimate.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace RenewalStationaryStateTransport

open Upstream.PrimitiveWeight

variable {n : ℕ}

/-- The Hermitian trace norm satisfies the triangle inequality. -/
theorem trNorm_add_le {𝕜 : Type*} [RCLike 𝕜]
    {X Y : Matrix (Fin n) (Fin n) 𝕜}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    trNorm (X + Y) ≤ trNorm X + trNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  let P := posPart hX + posPart hY
  let Q := negPart hX + negPart hY
  have hP : P.PosSemidef :=
    (posPart_posSemidef hX).add (posPart_posSemidef hY)
  have hQ : Q.PosSemidef :=
    (negPart_posSemidef hX).add (negPart_posSemidef hY)
  have hdec : X + Y = P - Q := by
    dsimp [P, Q]
    calc
      X + Y = (posPart hX - negPart hX) +
          (posPart hY - negPart hY) := by
        congr 1
        · exact (posPart_sub_negPart hX).symm
        · exact (posPart_sub_negPart hY).symm
      _ = (posPart hX + posPart hY) -
          (negPart hX + negPart hY) := by abel
  refine (trNorm_le_of_sub hXY hP hQ hdec).trans_eq ?_
  dsimp [P, Q]
  simp only [trace_add, map_add]
  rw [trNorm_eq_re_trace_parts hX, trNorm_eq_re_trace_parts hY]
  ring

/-- Strict trace-norm contraction on the traceless Hermitian subspace makes a
stationary density unique. -/
theorem stationaryDensity_unique_of_contraction
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ) (hq : q < 1)
    (hcontr : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (T X) ≤ q * trNorm X)
    {rho eta : Matrix (Fin n) (Fin n) ℂ}
    (hrho : rho ∈ densitySet n ℂ) (heta : eta ∈ densitySet n ℂ)
    (hrhoFix : T rho = rho) (hetaFix : T eta = eta) : rho = eta := by
  have hHerm : (rho - eta).IsHermitian := hrho.1.1.sub heta.1.1
  have htrace : (rho - eta).trace = 0 := by
    rw [trace_sub, hrho.2, heta.2, sub_self]
  have hc := hcontr (rho - eta) hHerm htrace
  rw [map_sub, hrhoFix, hetaFix] at hc
  have hnonneg := trNorm_nonneg (rho - eta)
  have hz : trNorm (rho - eta) = 0 := by nlinarith
  exact sub_eq_zero.mp ((trNorm_eq_zero_iff hHerm).mp hz)

/-- Existence by Cesàro compactness together with contraction uniqueness. -/
theorem existsUnique_stationaryDensity_of_contraction
    (hn : 0 < n)
    (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (htr : ∀ A, (T A).trace = A.trace)
    (hpsd : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef → (T A).PosSemidef)
    (q : ℝ) (hq : q < 1)
    (hcontr : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (T X) ≤ q * trNorm X) :
    ∃! rho : Matrix (Fin n) (Fin n) ℂ, rho ∈ densitySet n ℂ ∧ T rho = rho := by
  obtain ⟨rho, hrho, hfix⟩ := exists_stationary_density hn htr hpsd
  refine ⟨rho, ⟨hrho, hfix⟩, ?_⟩
  rintro eta ⟨heta, hetaFix⟩
  exact stationaryDensity_unique_of_contraction T q hq hcontr heta hrho hetaFix hfix

/-- Approximate cutoff intertwining transports stationary densities with the
sharp geometric-series constant `δ / (1 - q)`. -/
theorem stationaryDensity_cutoff_bound
    {nX nY : ℕ}
    (TX : Matrix (Fin nX) (Fin nX) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (TY : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nY) (Fin nY) ℂ)
    (J : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (q delta : ℝ) (hq : q < 1)
    (hTXpsd : ∀ A : Matrix (Fin nX) (Fin nX) ℂ,
      A.PosSemidef → (TX A).PosSemidef)
    (hcontr : ∀ X : Matrix (Fin nX) (Fin nX) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (TX X) ≤ q * trNorm X)
    {rhoX : Matrix (Fin nX) (Fin nX) ℂ}
    {rhoY : Matrix (Fin nY) (Fin nY) ℂ}
    (hrhoX : rhoX ∈ densitySet nX ℂ) (hfixX : TX rhoX = rhoX)
    (hrhoY : rhoY ∈ densitySet nY ℂ) (hfixY : TY rhoY = rhoY)
    (hJstate : ∀ rho ∈ densitySet nY ℂ, J rho ∈ densitySet nX ℂ)
    (hdefect : ∀ rho ∈ densitySet nY ℂ,
      trNorm (J (TY rho) - TX (J rho)) ≤ delta) :
    trNorm (J rhoY - rhoX) ≤ delta / (1 - q) := by
  have hJrho := hJstate rhoY hrhoY
  let e := J rhoY - rhoX
  have heHerm : e.IsHermitian := hJrho.1.1.sub hrhoX.1.1
  have heTrace : e.trace = 0 := by
    dsimp [e]
    rw [trace_sub, hJrho.2, hrhoX.2, sub_self]
  have hTXeHerm : (TX e).IsHermitian := by
    simpa using pow_isHermitian hTXpsd 1 heHerm
  have hdHerm : (J rhoY - TX (J rhoY)).IsHermitian := by
    have hTXJ : (TX (J rhoY)).IsHermitian := by
      simpa using pow_isHermitian hTXpsd 1 hJrho.1.1
    exact hJrho.1.1.sub hTXJ
  have heSplit : e = TX e + (J rhoY - TX (J rhoY)) := by
    dsimp [e]
    rw [map_sub, hfixX]
    abel
  have hdef : trNorm (J rhoY - TX (J rhoY)) ≤ delta := by
    simpa [hfixY] using hdefect rhoY hrhoY
  have hbound : trNorm e ≤ q * trNorm e + delta := by
    calc
      trNorm e = trNorm (TX e + (J rhoY - TX (J rhoY))) :=
        congrArg trNorm heSplit
      _ ≤ trNorm (TX e) + trNorm (J rhoY - TX (J rhoY)) :=
        trNorm_add_le hTXeHerm hdHerm
      _ ≤ q * trNorm e + delta :=
        add_le_add (hcontr e heHerm heTrace) hdef
  have hgap : 0 < 1 - q := by linarith
  rw [le_div_iff₀ hgap]
  nlinarith

/-- Exact intertwining is the zero-defect specialization: restriction of the
fine stationary density equals the unique coarse stationary density. -/
theorem stationaryDensity_cutoff_exact
    {nX nY : ℕ}
    (TX : Matrix (Fin nX) (Fin nX) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (TY : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nY) (Fin nY) ℂ)
    (J : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (q : ℝ) (hq : q < 1)
    (hTXpsd : ∀ A : Matrix (Fin nX) (Fin nX) ℂ,
      A.PosSemidef → (TX A).PosSemidef)
    (hcontr : ∀ X : Matrix (Fin nX) (Fin nX) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (TX X) ≤ q * trNorm X)
    {rhoX : Matrix (Fin nX) (Fin nX) ℂ}
    {rhoY : Matrix (Fin nY) (Fin nY) ℂ}
    (hrhoX : rhoX ∈ densitySet nX ℂ) (hfixX : TX rhoX = rhoX)
    (hrhoY : rhoY ∈ densitySet nY ℂ) (hfixY : TY rhoY = rhoY)
    (hJstate : ∀ rho ∈ densitySet nY ℂ, J rho ∈ densitySet nX ℂ)
    (hintertwine : ∀ A, J (TY A) = TX (J A)) :
    J rhoY = rhoX := by
  have hzero := stationaryDensity_cutoff_bound TX TY J q 0 hq hTXpsd hcontr
    hrhoX hfixX hrhoY hfixY hJstate
    (fun rho _ ↦ by rw [hintertwine, sub_self,
      (trNorm_eq_zero_iff isHermitian_zero).mpr rfl])
  have hHerm : (J rhoY - rhoX).IsHermitian :=
    (hJstate rhoY hrhoY).1.1.sub hrhoX.1.1
  have hz : trNorm (J rhoY - rhoX) = 0 := by
    apply le_antisymm
    · simpa using hzero
    · exact trNorm_nonneg _
  exact sub_eq_zero.mp ((trNorm_eq_zero_iff hHerm).mp hz)

/-- Complete finite-stage package: stationary densities exist and are unique,
and every stationary fine density obeys the cutoff transport estimate. -/
theorem renewal_stationary_state_transport
    {nX nY : ℕ} (hnX : 0 < nX) (hnY : 0 < nY)
    (TX : Matrix (Fin nX) (Fin nX) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (TY : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nY) (Fin nY) ℂ)
    (J : Matrix (Fin nY) (Fin nY) ℂ →ₗ[ℂ]
      Matrix (Fin nX) (Fin nX) ℂ)
    (htrX : ∀ A, (TX A).trace = A.trace)
    (htrY : ∀ A, (TY A).trace = A.trace)
    (hpsdX : ∀ A : Matrix (Fin nX) (Fin nX) ℂ,
      A.PosSemidef → (TX A).PosSemidef)
    (hpsdY : ∀ A : Matrix (Fin nY) (Fin nY) ℂ,
      A.PosSemidef → (TY A).PosSemidef)
    (qX qY delta : ℝ) (hqX : qX < 1) (hqY : qY < 1)
    (hcontrX : ∀ X : Matrix (Fin nX) (Fin nX) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (TX X) ≤ qX * trNorm X)
    (hcontrY : ∀ X : Matrix (Fin nY) (Fin nY) ℂ,
      X.IsHermitian → X.trace = 0 → trNorm (TY X) ≤ qY * trNorm X)
    (hJstate : ∀ rho ∈ densitySet nY ℂ, J rho ∈ densitySet nX ℂ)
    (hdefect : ∀ rho ∈ densitySet nY ℂ,
      trNorm (J (TY rho) - TX (J rho)) ≤ delta) :
    ∃ rhoX rhoY,
      rhoX ∈ densitySet nX ℂ ∧ TX rhoX = rhoX ∧
      (∀ etaX, etaX ∈ densitySet nX ℂ → TX etaX = etaX → etaX = rhoX) ∧
      rhoY ∈ densitySet nY ℂ ∧ TY rhoY = rhoY ∧
      (∀ etaY, etaY ∈ densitySet nY ℂ → TY etaY = etaY → etaY = rhoY) ∧
      trNorm (J rhoY - rhoX) ≤ delta / (1 - qX) := by
  obtain ⟨rhoX, hX, huniqX⟩ :=
    existsUnique_stationaryDensity_of_contraction hnX TX htrX hpsdX qX hqX hcontrX
  obtain ⟨rhoY, hY, huniqY⟩ :=
    existsUnique_stationaryDensity_of_contraction hnY TY htrY hpsdY qY hqY hcontrY
  refine ⟨rhoX, rhoY, hX.1, hX.2, ?_, hY.1, hY.2, ?_, ?_⟩
  · intro etaX hetaX hfix
    exact huniqX etaX ⟨hetaX, hfix⟩
  · intro etaY hetaY hfix
    exact huniqY etaY ⟨hetaY, hfix⟩
  · exact stationaryDensity_cutoff_bound TX TY J qX delta hqX hpsdX hcontrX
      hX.1 hX.2 hY.1 hY.2 hJstate hdefect

end RenewalStationaryStateTransport
end NCG
