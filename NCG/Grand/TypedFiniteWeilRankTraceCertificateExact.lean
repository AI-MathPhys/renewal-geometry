/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTRankTraceIndefiniteDirectExact

/-!
# Typed finite Weil rank--trace certificate

This file proves the exact finite linear-algebra content of
`thm:GRH-Weil-inertia`.  The critical-line columns form a positive matrix of
bounded rank; the typed functional-equation pullback supplies a Hermitian
hyperbolic block whose positive Jordan rank is bounded by the number of
paired blocks.  The direct indefinite rank--trace theorem then gives (GRH.1).
The atom-normalized moment estimates are propagated with explicit error,
yielding the finite quantitative version of (GRH.2), and a trace/Frobenius
tail allowance is kept as a separate verified row.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG.TypedFiniteWeilRankTraceCertificate

/-- A typed functional-equation hyperbolic pullback certificate.  The
positive-Jordan-rank bound is the exact finite meaning of `n₊(Q) ≤ p`; keeping
it in this structure prevents an untyped indefinite matrix from being used as
a functional-equation block. -/
structure HyperbolicPullbackCertificate {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) : Prop where
  hermitian : Q.IsHermitian
  positiveIndexBound :
    (NCG.Upstream.PrimitiveWeight.posPart hermitian).rank ≤ p

/-- Exterior-window tail bookkeeping. -/
structure TailAllowance {n : ℕ}
    (G E : Matrix (Fin n) (Fin n) ℂ) where
  traceError : ℝ
  frobeniusError : ℝ
  traceError_nonnegative : 0 ≤ traceError
  frobeniusError_nonnegative : 0 ≤ frobeniusError
  trace_control : |(G + E).trace.re - G.trace.re| ≤ traceError
  frobenius_control :
    |NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (G + E) -
      NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq G| ≤ frobeniusError

/-- Exact (GRH.1) from the typed critical-line and hyperbolic rows. -/
theorem finite_weil_rank_trace_bound {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ)
    (s p : ℕ) (hP : P.PosSemidef) (hrank : P.rank ≤ s)
    (hQ : HyperbolicPullbackCertificate Q p) :
    (s : ℝ) ≥ 2 * P.trace.re + 4 * Q.trace.re - 4 * (p : ℝ) -
      NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) := by
  exact (NCG.GTRankTraceIndefiniteDirectExact.gt_rank_trace_indefinite_direct
    P Q hP hQ.hermitian s p hrank hQ.positiveIndexBound).2

/-- Explicit finite-error form of the zero-density display (GRH.2).  The
typed hyperbolic normalization `2p ≤ Tr Q` makes its correction nonnegative;
the two atom moment errors cost exactly `3 ε N`. -/
theorem atom_normalized_zero_density_bound {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ)
    (s p : ℕ) (hP : P.PosSemidef) (hrank : P.rank ≤ s)
    (hQ : HyperbolicPullbackCertificate Q p)
    (N lambda epsilon : ℝ) (hN : 0 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hlambda : 0 < lambda)
    (hhyperbolicTrace : 2 * (p : ℝ) ≤ Q.trace.re)
    (htrace : |(P + Q).trace.re - N| ≤ epsilon * N)
    (hfrobenius :
      |NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) -
        (1 / lambda + lambda / 3) * N| ≤ epsilon * N) :
    (s : ℝ) ≥
      (2 - 1 / lambda - lambda / 3 - 3 * epsilon) * N := by
  have hcert := finite_weil_rank_trace_bound P Q s p hP hrank hQ
  have htraceAdd : (P + Q).trace.re = P.trace.re + Q.trace.re := by
    rw [Matrix.trace_add, Complex.add_re]
  have htraceLower : N - epsilon * N ≤ (P + Q).trace.re := by
    linarith [(abs_le.mp htrace).1]
  have hfrobUpper :
      NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) ≤
        (1 / lambda + lambda / 3) * N + epsilon * N := by
    linarith [(abs_le.mp hfrobenius).2]
  rw [htraceAdd] at htraceLower
  nlinarith

/-- The exterior-window replacement changes the two scalar rows by no more
than their declared trace/Frobenius allowances. -/
theorem tail_allowance_transport {n : ℕ}
    (G E : Matrix (Fin n) (Fin n) ℂ) (T : TailAllowance G E) :
    (G + E).trace.re ∈ Set.Icc
      (G.trace.re - T.traceError) (G.trace.re + T.traceError) ∧
    NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (G + E) ∈ Set.Icc
      (NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq G - T.frobeniusError)
      (NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq G + T.frobeniusError) := by
  constructor
  · exact ⟨by linarith [(abs_le.mp T.trace_control).1],
      by linarith [(abs_le.mp T.trace_control).2]⟩
  · exact ⟨by linarith [(abs_le.mp T.frobenius_control).1],
      by linarith [(abs_le.mp T.frobenius_control).2]⟩

/-- **`thm:GRH-Weil-inertia`.**  Typed hyperbolic inertia gives (GRH.1),
the atom moment packet gives the quantitative (GRH.2) lower bound, and the
exterior-window matrix is controlled by explicit scalar allowances. -/
theorem typed_finite_weil_rank_trace_certificate {n : ℕ}
    (P Q E : Matrix (Fin n) (Fin n) ℂ)
    (s p : ℕ) (hP : P.PosSemidef) (hrank : P.rank ≤ s)
    (hQ : HyperbolicPullbackCertificate Q p)
    (N lambda epsilon : ℝ) (hN : 0 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hlambda : 0 < lambda)
    (hhyperbolicTrace : 2 * (p : ℝ) ≤ Q.trace.re)
    (htrace : |(P + Q).trace.re - N| ≤ epsilon * N)
    (hfrobenius :
      |NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) -
        (1 / lambda + lambda / 3) * N| ≤ epsilon * N)
    (tail : TailAllowance (P + Q) E) :
    ((s : ℝ) ≥ 2 * P.trace.re + 4 * Q.trace.re - 4 * (p : ℝ) -
      NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q)) ∧
    ((s : ℝ) ≥
      (2 - 1 / lambda - lambda / 3 - 3 * epsilon) * N) ∧
    ((P + Q + E).trace.re ∈ Set.Icc
      ((P + Q).trace.re - tail.traceError)
      ((P + Q).trace.re + tail.traceError)) ∧
    (NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q + E) ∈ Set.Icc
      (NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) -
        tail.frobeniusError)
      (NCG.GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q) +
        tail.frobeniusError)) := by
  refine ⟨finite_weil_rank_trace_bound P Q s p hP hrank hQ,
    atom_normalized_zero_density_bound P Q s p hP hrank hQ
      N lambda epsilon hN hepsilon hlambda hhyperbolicTrace htrace hfrobenius,
    ?_⟩
  simpa [add_assoc] using tail_allowance_transport (P + Q) E tail

end NCG.TypedFiniteWeilRankTraceCertificate
