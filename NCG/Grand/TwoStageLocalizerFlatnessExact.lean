/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.KrylovLocalizerFlatnessExact
import NCG.Grand.MomentLeakageUnwhitening

/-!
# Exact two-stage localizer flatness

This assembles the finite Krylov stabilization theorem with the unwhitened
moment-leakage identity.  It is the complete finite-dimensional content of
`cor:GT-two-stage-localizer-flatness`: leakage rank is the new Krylov rank,
the chain terminates, and its stable carrier reduces the symmetric localizer
and contains every visible source moment.
-/

open Matrix Submodule
open scoped ComplexOrder Norms.L2Operator

namespace NCG

/-- `cor:GT-two-stage-localizer-flatness`, exact assembled form. -/
theorem two_stage_localizer_flatness_exact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (Tlin : E →ₗ[ℂ] E) (hTlin : Tlin.IsSymmetric)
    (Vsrc : Submodule ℂ E)
    {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq h] [DecidableEq k]
    (C : Matrix h k ℂ) (R : Matrix k k ℂ) (T : Matrix h h ℂ)
    (hR : Rᴴ = R) (hwhite : R * (Cᴴ * C) * R = 1)
    (hTH : Tᴴ = T) :
    (∃ n, 1 ≤ n ∧ n ≤ Module.finrank ℂ E + 1
      ∧ KrylovLocalizerFlatness.krylov Tlin Vsrc (n + 1)
          = KrylovLocalizerFlatness.krylov Tlin Vsrc n
      ∧ (KrylovLocalizerFlatness.krylov Tlin Vsrc n).map Tlin
          ≤ KrylovLocalizerFlatness.krylov Tlin Vsrc n
      ∧ (KrylovLocalizerFlatness.krylov Tlin Vsrc n).orthogonal.map Tlin
          ≤ (KrylovLocalizerFlatness.krylov Tlin Vsrc n).orthogonal
      ∧ (∀ j, Vsrc.map (Tlin ^ j)
          ≤ KrylovLocalizerFlatness.krylov Tlin Vsrc n)
      ∧ ∀ M : Submodule ℂ E, Vsrc ≤ M → M.map Tlin ≤ M →
          KrylovLocalizerFlatness.krylov Tlin Vsrc n ≤ M)
    ∧ (let H1 := Cᴴ * T * C
       let H2 := Cᴴ * (T * T) * C
       let W := C * R
       let A := R * H1 * R
       let L := R * H2 * R - A * A
       let X := (1 - W * Wᴴ) * T * W
       L = Xᴴ * X
       ∧ L.PosSemidef
       ∧ ‖L‖ = ‖X‖ ^ 2
       ∧ L.rank = Module.finrank ℂ (momentLeakageNewComponent W T)
       ∧ L.rank = (Matrix.fromCols W (T * W)).rank - W.rank
       ∧ (L = 0 ↔ X = 0)) := by
  constructor
  · obtain ⟨n, hn, hbound, hstable⟩ :=
      KrylovLocalizerFlatness.exists_stable_index Tlin Vsrc
    obtain ⟨hinv, hinvOrth⟩ :=
      KrylovLocalizerFlatness.krylov_reduces Tlin hTlin Vsrc hn hstable
    obtain ⟨hmom, hmin⟩ :=
      KrylovLocalizerFlatness.krylov_stable_eq_minimal Tlin Vsrc hn hstable
    exact ⟨n, hn, hbound, hstable, hinv, hinvOrth, hmom, hmin⟩
  · exact universal_moment_leakage_exact C R T hR hwhite hTH

end NCG
