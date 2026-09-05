/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.Symplectic
import NCG.Algebra.ExternalFactor

/-!
# The internal complement countermodel

`prop:no-overstatement` (2) of the flagship manuscript: the total
primitive factor is **not** forced to be `M₄(ℂ)`.  For every
half-rank `m ≥ 2` the standard symplectic `𝔽₂`-space of dimension
`2m` is nondegenerate and alternating — a valid primitive revision
module — and its twisted group algebra `M_{2^m}(ℂ)` factors as the
external `M₄(ℂ)` block tensored with a commuting internal complement
`M_{2^{m-2}}(ℂ)`, nontrivial whenever `m > 2`:

* `internal_complement_realizable` — the countermodel, assembled from
  `stdSymplectic_nondegenerate` and `externalFactorSplit'`.

Hence the flagship hypotheses select a *minimal* external `(3+1)`
core but no unique total primitive dimension, exactly as
`thm:external-core` and `rem:minimality-versus-uniqueness` state.
-/

namespace NCG

open scoped TensorProduct

/-- **`prop:no-overstatement` (2)**: every half-rank `m ≥ 2` carries
a nondegenerate alternating primitive module of dimension `2m` whose
matrix algebra splits off the marked external `M₄(ℂ)` with a
commuting internal complement `M_{2^{m-2}}(ℂ)`.  The total primitive
factor is therefore not unique. -/
theorem internal_complement_realizable (m : ℕ) (hm : 2 ≤ m) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V)
      (_ : FiniteDimensional (ZMod 2) V)
      (B : LinearMap.BilinForm (ZMod 2) V),
      Module.finrank (ZMod 2) V = 2 * m ∧ LinearMap.IsAlt B ∧
        LinearMap.Nondegenerate B ∧
        Nonempty (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ ≃ₐ[ℂ]
          Matrix (Fin 4) (Fin 4) ℂ ⊗[ℂ]
            Matrix (Fin (2 ^ (m - 2))) (Fin (2 ^ (m - 2))) ℂ) :=
  ⟨(Fin m → ZMod 2) × (Fin m → ZMod 2), inferInstance, inferInstance,
    inferInstance, stdSymplectic (ZMod 2) m,
    finrank_symplectic_space, stdSymplectic_isAlt,
    stdSymplectic_nondegenerate, ⟨externalFactorSplit' ℂ m hm⟩⟩

end NCG
