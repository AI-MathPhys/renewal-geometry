/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DeterminantIncidenceExact
import NCG.Grand.CliffordTwirlMatterAudit
import NCG.Grand.OneDoubletOddTangentClassification

/-!
# One typed determinant--Clifford odd word

This file assembles the determinant alternation, protected Clifford route, and
one-doublet finite-Dirac incidence statements on one same-history word.  It is
the final paragraph of `thm:SM-active-determinant-incidence`.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- A single typed word with positive Clifford and determinant shadows and
zero odd-provenance defect simultaneously reconstructs the protected matter
route, the nonzero determinant seed, and one rank-one weak/finite-Dirac line.
-/
theorem determinantIncidence_oneTypedOddWord
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (J : CliffordTwirlMatterAudit.Block
      (CliffordTwirlMatterAudit.CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hpCl : (0 : ℂ) < CliffordTwirlMatterAudit.cliffordProbability J
      CliffordTwirlMatterAudit.representedAxis)
    (Tu : DetIncidence.Shadow) (hTu : DetIncidence.FullyAlternating Tu)
    (hdet : 0 < DetIncidence.mdet Tu)
    {h e k : ℕ} (line : Matrix (Fin h) (Fin 1) ℂ)
    (selected : Matrix (Fin h) (Fin e) ℂ)
    (completeOdd : Matrix (Fin h) (Fin k) ℂ)
    (hline : ∃ coefficients : Matrix (Fin 1) (Fin e) ℂ,
      selected = line * coefficients)
    (hprov : oddProvenanceDefect selected completeOdd = 0)
    (hoddNonzero : completeOdd ≠ 0) :
    CliffordTwirlMatterAudit.HasProtectedMatterRoute J ∧
      (∃ τ : ℂ, τ ≠ 0 ∧ Tu = DetIncidence.theta τ) ∧
      (∃ coefficients : Matrix (Fin 1) (Fin k) ℂ,
        completeOdd = line * coefficients ∧ completeOdd.rank ≤ 1) ∧
      completeOdd ≠ 0 := by
  have hfive := CliffordTwirlMatterAudit.positiveMatter_five_way J hJH hJ2
  have hroute : ∃ μ,
      CliffordTwirlMatterAudit.axisCrossBlock J
        (CliffordTwirlMatterAudit.representedAxis μ) ≠ 0 :=
    hfive.2.1.mp (hfive.1.mp hpCl)
  have hseed := (DetIncidence.mdet_pos_iff hTu).mp hdet
  have hdoublet := zeroOddProvenance_commonWeakLine_rankOne
    line selected completeOdd hline hprov
  exact ⟨hroute, hseed, hdoublet, hoddNonzero⟩

end NCG
