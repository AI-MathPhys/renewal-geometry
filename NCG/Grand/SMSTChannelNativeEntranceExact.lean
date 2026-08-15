/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SMSTCompiledChannelGeneratorExact

/-!
# Channel-native entrance (exact)

Exact formalization of the entrance clause of
`cor:SMST-channel-native-entrance`: under the connected-graph
branch conditions, the compiled channel's projected Hamiltonian
converges in Hilbert–Schmidt norm to the direct or bracket
matter target, and — because that target is a **nonzero**
grading-changing generator — the compiled Hamiltonian is
eventually nonzero: the channel entrance genuinely reconstructs
a nonzero Hamiltonian generator on the source core.

`channel_native_entrance` derives both conclusions from the
branch-estimate input (`Snorm → 0` along `h → 0⁺`, supplied by
the proved direct/bracket compilers of
`thm:SMST-channel-direct-bracket` through
`thm:SMST-compiled-channel-generator`):

* the Hilbert–Schmidt convergence `H_h ⟶ D_tl`
  (`compiled_generator_hs_tendsto`), and
* eventual nonvanishing `H_h ≠ 0`, from strict positivity of
  the Hilbert–Schmidt norm of the nonzero target
  (`hsFrobSq_eq_zero_iff`).

The second clause of the corollary (finite-Dirac promotion of
the complete odd generator when the relation/provenance
residuals vanish and the relative Howe Gram is positive, with
its typed residue blocks and multiplicity commutant) is carried
by the separately proved records
`thm:SMST-relative-Howe-certificate`,
`prop:SM-typed-transition-audit`,
`thm:SMST-support-polar-commutant`, and
`thm:SMST-quiver-commutant`.
-/

open Filter Set Matrix

namespace NCG
namespace SMSTChannel

variable {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]

omit [DecidableEq d] [Nonempty d] in
/-- The Hilbert–Schmidt norm of a nonzero matrix is strictly
positive. -/
theorem matrixHSNorm_pos (Dtl : Matrix d d ℂ) (hD : Dtl ≠ 0) :
    0 < matrixHSNorm Dtl := by
  rw [matrixHSNorm]
  refine Real.sqrt_pos.mpr ?_
  have hne : hsFrobSq Dtl ≠ 0 := fun h =>
    hD ((hsFrobSq_eq_zero_iff Dtl).mp h)
  exact lt_of_le_of_ne (hsFrobSq_nonneg Dtl) (Ne.symm hne)

omit [DecidableEq d] [Nonempty d] in
/-- The Hilbert–Schmidt norm is invariant under negation. -/
theorem matrixHSNorm_neg (A : Matrix d d ℂ) :
    matrixHSNorm (-A) = matrixHSNorm A := by
  rw [matrixHSNorm, matrixHSNorm]
  congr 1
  simp [hsFrobSq]

/-- **Channel-native entrance**
(`cor:SMST-channel-native-entrance`, entrance clause): under
the branch conditions (`Snorm → 0` as `h → 0⁺`, supplied by the
proved direct/bracket compiled-channel estimates), the compiled
projected Hamiltonian converges in Hilbert–Schmidt norm to the
nonzero matter target — and is therefore eventually a nonzero
grading-changing generator on the source core. -/
theorem channel_native_entrance
    (Hh : ℝ → Matrix d d ℂ) (Dtl : Matrix d d ℂ) (cd : ℝ)
    (Snorm : ℝ → ℝ)
    (hS : Tendsto Snorm (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hHerm : ∀ h, (Hh h - Dtl)ᴴ = Hh h - Dtl)
    (htr : ∀ h, (Hh h - Dtl).trace = 0)
    (hproj : ∀ h, adSuperHSNorm (Hh h - Dtl) ≤ cd * Snorm h)
    (hD0 : Dtl ≠ 0) :
    Tendsto (fun h => matrixHSNorm (Hh h - Dtl))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
    ∧ ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0), Hh h ≠ 0 := by
  have hconv := compiled_generator_hs_tendsto Hh Dtl cd
    Snorm hS hHerm htr hproj
  refine ⟨hconv, ?_⟩
  have hpos : 0 < matrixHSNorm Dtl := matrixHSNorm_pos Dtl hD0
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
      matrixHSNorm (Hh h - Dtl) < matrixHSNorm Dtl :=
    hconv.eventually_lt_const hpos
  refine hev.mono ?_
  intro h hlt h0
  rw [h0, zero_sub, matrixHSNorm_neg] at hlt
  exact lt_irrefl _ hlt

end SMSTChannel
end NCG
