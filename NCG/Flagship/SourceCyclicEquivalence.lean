/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.KalmanRealization

/-!
# Finite source-cyclic realization equivalence
  (`thm:source-cyclic-equivalence-master`, flagship manuscript)

Two finite self-adjoint source realizations `(T₁,S₁)`, `(T₂,S₂)`
with equal source moments `S₁*T₁ⁿS₁ = S₂*T₂ⁿS₂` and a
source-minimal (stabilized) Krylov packet are related by a
unitary with the boxed intertwining `US₁ = S₂`, `UT₁ = T₂U`
(`source_cyclic_equivalence`, delegating to the explicit Gram
factorization `U = K'K*(KK*)⁻¹` of
`NCG.physical_source_uniqueness`); the intertwiner is unique on
the stabilized source-cyclic packet (`source_cyclic_unique`).

Disclosures: both realizations are carried on one finite index
type (two abstract finite Hilbert spaces of equal stabilized
packet dimension embed there); moments are assumed at all orders
(the manuscript's finite window `0 ≤ n ≤ 2r+1` recovers all
orders by Cayley–Hamilton, cited as standard); stabilization at
depth `r` enters as surjectivity of the depth-`d` Krylov matrix.
-/

namespace NCG

open Matrix

variable {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]
  [DecidableEq p]

omit [DecidableEq p] in
/-- `thm:source-cyclic-equivalence-master`, boxed intertwining:
equal source moments on a stabilized packet give a unitary `U`
with `US₁ = S₂` and `UT₁ = T₂U`. -/
theorem source_cyclic_equivalence
    (T1 T2 : Matrix u u ℂ) (S1 S2 : Matrix u p ℂ)
    (hT1 : T1ᴴ = T1) (hT2 : T2ᴴ = T2)
    (d : ℕ) (hd : 0 < d)
    (hmin : Function.Surjective (krylovMat T1 S1 d).mulVec)
    (hmom : ∀ n : ℕ, S1ᴴ * T1 ^ n * S1 = S2ᴴ * T2 ^ n * S2) :
    ∃ U : Matrix u u ℂ, Uᴴ * U = 1 ∧ U * S1 = S2
      ∧ U * T1 = T2 * U :=
  physical_source_uniqueness T1 T2 S1 S2 hT1 hT2 d hd hmin hmom

omit [Fintype p] [DecidableEq u] [DecidableEq p] in
/-- Uniqueness on the stabilized source-cyclic packet: two
intertwiners with the same action on the Krylov data agree on the
packet. -/
theorem source_cyclic_unique {q : Type*}
    (K K' : Matrix u q ℂ) (U1 U2 : Matrix u u ℂ)
    (h1 : U1 * K = K') (h2 : U2 * K = K') :
    (U1 - U2) * K = 0 := by
  rw [Matrix.sub_mul, h1, h2, sub_self]

end NCG
