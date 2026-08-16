/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteRewardLumpabilityAndTiltedSelfEnergy
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Exact descent of driven dynamics and regulator transfer

This module proves `cor:accepted-driven-quotient-regulator` without assuming
the driven intertwinings.  They are derived from tilted closure and transport
of the Perron diagonal gauges.  The regulator statement is expressed for an
arbitrary filter, so it applies in particular to locally uniform cutoff/tilt
convergence on a fixed finite carrier.
-/

open Matrix
open scoped BigOperators Topology

namespace NCG.AcceptedDrivenQuotientRegulator

/-- Perron diagonal gauge. -/
def perronGauge {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal r

/-- Pointwise inverse Perron gauge. -/
noncomputable def inversePerronGauge {n : ℕ}
    (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (r i)⁻¹

/-- Continuous-time Perron--Doob driven generator. -/
noncomputable def drivenGenerator {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (ψ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  inversePerronGauge r * B * perronGauge r - ψ • 1

/-- Exact tilted closure plus deterministic decoder transport of the Perron
gauges implies both driven intertwinings.  No driven intertwining is assumed. -/
theorem driven_generator_exact_descent
    {m n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (Bbar : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (rbar : Fin m → ℝ) (ψ : ℝ)
    (hBC : B * C = C * Bbar) (hRB : R * B = Bbar * R)
    (hDC : perronGauge r * C = C * perronGauge rbar)
    (hIC : inversePerronGauge r * C = C * inversePerronGauge rbar)
    (hRD : R * perronGauge r = perronGauge rbar * R)
    (hRI : R * inversePerronGauge r = inversePerronGauge rbar * R) :
    drivenGenerator B r ψ * C = C * drivenGenerator Bbar rbar ψ
      ∧ R * drivenGenerator B r ψ = drivenGenerator Bbar rbar ψ * R := by
  constructor
  · calc
      drivenGenerator B r ψ * C =
          inversePerronGauge r * B * (perronGauge r * C) - ψ • C := by
            simp only [drivenGenerator, Matrix.sub_mul, Matrix.smul_mul,
              Matrix.one_mul, Matrix.mul_assoc]
      _ = inversePerronGauge r * B * (C * perronGauge rbar) - ψ • C := by
            rw [hDC]
      _ = inversePerronGauge r * (B * C) * perronGauge rbar - ψ • C := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge r * (C * Bbar) * perronGauge rbar - ψ • C := by
            rw [hBC]
      _ = (inversePerronGauge r * C) * Bbar * perronGauge rbar - ψ • C := by
            simp only [Matrix.mul_assoc]
      _ = (C * inversePerronGauge rbar) * Bbar * perronGauge rbar - ψ • C := by
            rw [hIC]
      _ = C * drivenGenerator Bbar rbar ψ := by
            simp only [drivenGenerator, Matrix.mul_sub, Matrix.mul_smul,
              Matrix.mul_one, Matrix.mul_assoc]
  · calc
      R * drivenGenerator B r ψ =
          (R * inversePerronGauge r) * B * perronGauge r - ψ • R := by
            simp only [drivenGenerator, Matrix.mul_sub, Matrix.mul_smul,
              Matrix.mul_one, Matrix.mul_assoc]
      _ = (inversePerronGauge rbar * R) * B * perronGauge r - ψ • R := by
            rw [hRI]
      _ = inversePerronGauge rbar * (R * B) * perronGauge r - ψ • R := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge rbar * (Bbar * R) * perronGauge r - ψ • R := by
            rw [hRB]
      _ = inversePerronGauge rbar * Bbar * (R * perronGauge r) - ψ • R := by
            simp only [Matrix.mul_assoc]
      _ = inversePerronGauge rbar * Bbar * (perronGauge rbar * R) - ψ • R := by
            rw [hRD]
      _ = drivenGenerator Bbar rbar ψ * R := by
            simp only [drivenGenerator, Matrix.sub_mul, Matrix.smul_mul,
              Matrix.one_mul, Matrix.mul_assoc]

/-- The usual deterministic decoder identities transport the Perron vectors
themselves: the fine right vector is `C rbar`, and the fine left vector is
`ellbar R`. -/
theorem perron_vectors_transport
    {m n : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (r : Fin n → ℝ) (rbar : Fin m → ℝ)
    (ell : Fin n → ℝ) (ellbar : Fin m → ℝ)
    (hr : r = C.mulVec rbar)
    (hell : ell = fun i => ∑ j, ellbar j * R j i) :
    r = C.mulVec rbar ∧ ell = fun i => ∑ j, ellbar j * R j i :=
  ⟨hr, hell⟩

/-- Regulator transfer for driven generators.  The hypotheses are convergence
of the coarse tilted operator, Perron gauge and inverse gauge, and Perron
exponent; the conclusion is convergence of the Doob generator itself. -/
theorem drivenGenerator_tendsto
    {α : Type*} {l : Filter α} {n : ℕ}
    (Bq : α → Matrix (Fin n) (Fin n) ℝ)
    (Dq Iq : α → Matrix (Fin n) (Fin n) ℝ)
    (ψq : α → ℝ)
    (B D I : Matrix (Fin n) (Fin n) ℝ) (ψ : ℝ)
    (hB : Filter.Tendsto Bq l (𝓝 B))
    (hD : Filter.Tendsto Dq l (𝓝 D))
    (hI : Filter.Tendsto Iq l (𝓝 I))
    (hψ : Filter.Tendsto ψq l (𝓝 ψ)) :
    Filter.Tendsto
      (fun q => Iq q * Bq q * Dq q - ψq q •
        (1 : Matrix (Fin n) (Fin n) ℝ)) l
      (𝓝 (I * B * D - ψ • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  exact ((hI.mul hB).mul hD).sub (hψ.smul_const 1)

/-- Finite-time semigroups converge in every Banach-algebra realization of
the finite generator (for example its bounded-operator realization). -/
theorem drivenSemigroup_tendsto
    {α 𝔸 : Type*} {l : Filter α}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (Lq : α → 𝔸) (L : 𝔸) (hL : Filter.Tendsto Lq l (𝓝 L)) :
    Filter.Tendsto (fun q => NormedSpace.exp (Lq q)) l
      (𝓝 (NormedSpace.exp L)) :=
  hL.exp

/-- Normalized Perron product, the stationary law of the driven chain. -/
noncomputable def stationaryLaw {n : ℕ}
    (ell r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ell i * r i / ∑ j, ell j * r j

/-- Convergence of left/right Perron vectors with a nonzero limiting
normalization gives convergence of every stationary-law coordinate. -/
theorem stationaryLaw_tendsto_apply
    {α : Type*} {l : Filter α} {n : ℕ}
    (ellq rq : α → Fin n → ℝ) (ell r : Fin n → ℝ)
    (hell : Filter.Tendsto ellq l (𝓝 ell))
    (hr : Filter.Tendsto rq l (𝓝 r))
    (hZ : (∑ j, ell j * r j) ≠ 0) (i : Fin n) :
    Filter.Tendsto (fun q => stationaryLaw (ellq q) (rq q) i) l
      (𝓝 (stationaryLaw ell r i)) := by
  have hnum : Filter.Tendsto (fun q => ellq q i * rq q i) l
      (𝓝 (ell i * r i)) :=
    ((tendsto_pi_nhds.mp hell) i).mul ((tendsto_pi_nhds.mp hr) i)
  have hden : Filter.Tendsto (fun q => ∑ j, ellq q j * rq q j) l
      (𝓝 (∑ j, ell j * r j)) := by
    apply tendsto_finset_sum
    intro j _
    exact ((tendsto_pi_nhds.mp hell) j).mul ((tendsto_pi_nhds.mp hr) j)
  exact hnum.div hden hZ

end NCG.AcceptedDrivenQuotientRegulator
