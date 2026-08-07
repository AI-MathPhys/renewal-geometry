/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Physical-shell localization of the Hankel source
  (`thm:YM-physical-shell-master`, flagship manuscript)

For a nearest-neighbour physical filtration `𝒢₁ ⊆ 𝒢₂ ⊆ ⋯` with
`T𝒢_k ⊆ 𝒢_{k+1}` and source `S ⊆ 𝒢₁`:

* `krylov_power_confined` / `krylov_confined`: the boxed first
  inclusion — every Krylov power `T^j(Ran S)` lies in `𝒢_{j+1}`,
  so the Krylov head `𝒦_n(S) = Σ_{j<n} T^j(Ran S)` lies in `𝒢_n`;
* `leakage_confined`: the boxed leakage inclusion — for
  `x ∈ 𝒦_n(S)`, the exact Hankel leakage
  `Tx - P_{𝒦_n}(Tx)` lies in `𝒢_{n+1} ⊓ 𝒦_n(S)ᗮ`; when the
  shell atlas is source cyclic (`𝒦_n(S) = 𝒢_n`) this is the
  shell `ℰ_n = 𝒢_{n+1} ⊓ 𝒢_nᗮ` — the first missing source is a
  predeclared local physical history, not an abstract Ritz
  vector.

Rendering disclosed: the geometric `R₀`-collar support statement
is the same induction applied to supports (the manuscript's
locality bookkeeping on the ambient lattice).
-/

namespace NCG

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- Each Krylov power is confined to its shell:
`T^j(Ran S) ⊆ 𝒢_{j+1}`. -/
theorem krylov_power_confined (G : ℕ → Submodule ℂ E)
    (T : E →ₗ[ℂ] E) (S : Submodule ℂ E) (hS : S ≤ G 1)
    (hnn : ∀ k, Submodule.map T (G k) ≤ G (k + 1)) :
    ∀ j, Submodule.map (T ^ j) S ≤ G (j + 1) := by
  intro j
  induction j with
  | zero =>
    rw [pow_zero]
    simpa [Module.End.one_eq_id, Submodule.map_id] using hS
  | succ j ih =>
    calc Submodule.map (T ^ (j + 1)) S
        = Submodule.map T (Submodule.map (T ^ j) S) := by
          rw [pow_succ', Module.End.mul_eq_comp,
            Submodule.map_comp]
      _ ≤ Submodule.map T (G (j + 1)) :=
          Submodule.map_mono ih
      _ ≤ G (j + 2) := hnn (j + 1)

omit [FiniteDimensional ℂ E] in
/-- Boxed first inclusion: the Krylov head lies in its shell,
`𝒦_n(S) ⊆ 𝒢_n` for `n ≥ 1`. -/
theorem krylov_confined (G : ℕ → Submodule ℂ E)
    (T : E →ₗ[ℂ] E) (S : Submodule ℂ E) (hS : S ≤ G 1)
    (hmono : ∀ k, G k ≤ G (k + 1))
    (hnn : ∀ k, Submodule.map T (G k) ≤ G (k + 1)) (n : ℕ) :
    (⨆ j ∈ Finset.range (n + 1), Submodule.map (T ^ j) S)
      ≤ G (n + 1) := by
  have hGmono : Monotone G := monotone_nat_of_le_succ hmono
  refine iSup_le fun j => iSup_le fun hj => ?_
  refine le_trans (krylov_power_confined G T S hS hnn j) ?_
  exact hGmono (Nat.succ_le_succ
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

/-- Boxed leakage inclusion: the exact Hankel leakage of a head
vector lies in the next shell and orthogonal to the head:
`Tx - P_{𝒦}(Tx) ∈ 𝒢_{n+1} ⊓ 𝒦ᗮ`. -/
theorem leakage_confined (Gnext : Submodule ℂ E)
    (T : E →ₗ[ℂ] E) (K : Submodule ℂ E)
    (hKG : K ≤ Gnext)
    (hTK : Submodule.map T K ≤ Gnext)
    (x : E) (hx : x ∈ K) :
    T x - K.starProjection (T x) ∈ Gnext ⊓ Kᗮ := by
  constructor
  · have hTx : T x ∈ Gnext :=
      hTK ⟨x, hx, rfl⟩
    have hP : K.starProjection (T x) ∈ Gnext :=
      hKG (K.starProjection_apply_mem (T x))
    exact Submodule.sub_mem _ hTx hP
  · exact K.sub_starProjection_mem_orthogonal (T x)

end NCG
