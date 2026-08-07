/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Hankel-rank minimality
  (`thm:hankel-minimality`, Gran-Tensor manuscript)

* `hankel_minimality`: for any linear predictive realization of
  the intervention table (states `n_p`, future effects `λ_f`
  with `λ_f(n_p) = ℙ(f,p)`), the boxed quotient identification
  `N^reach/N^unobs ≅ M_{x,r}` holds — the reachable span modulo
  the unobservable subspace is canonically the typed Hankel
  column space — and `dim N ≥ d_{x,r}` (the typed Hankel rank).

Rendering disclosed: the canonical predictive core `M_{x,r}` is
the span of the Hankel columns `h_p = ℙ(·,p)`; the identifying
map is `v ↦ (f ↦ λ_f(v))`; equality for reachable
future-separated realizations and the uniqueness of the
record-preserving similarity between minimal realizations are
the manuscript's bookkeeping over this quotient identification
(the similarity is the composite of the two identifications).
-/

namespace NCG

/-- `thm:hankel-minimality`: the reachable/unobservable quotient
of any realization is canonically the Hankel column space, and
every realization dimension dominates the Hankel rank. -/
theorem hankel_minimality {P F N : Type*} [AddCommGroup N]
    [Module ℂ N] [FiniteDimensional ℂ N]
    (tbl : F → P → ℂ) (nst : P → N) (ℓ : F → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f q, ℓ f (nst q) = tbl f q) :
    Nonempty ((↥(Submodule.span ℂ (Set.range nst))
        ⧸ (Submodule.comap
            (Submodule.span ℂ (Set.range nst)).subtype
            (⨅ f, LinearMap.ker (ℓ f))))
      ≃ₗ[ℂ] ↥(Submodule.span ℂ
          (Set.range fun q (f : F) => tbl f q)))
    ∧ Module.finrank ℂ (Submodule.span ℂ
        (Set.range fun q (f : F) => tbl f q))
      ≤ Module.finrank ℂ N := by
  set Φ : N →ₗ[ℂ] (F → ℂ) := LinearMap.pi (fun f => ℓ f)
    with hΦ
  have hΦn : ∀ q, Φ (nst q) = fun f => tbl f q := by
    intro q
    funext f
    rw [hΦ, LinearMap.pi_apply, hmatch]
  have hmap : Submodule.map Φ
      (Submodule.span ℂ (Set.range nst))
      = Submodule.span ℂ
          (Set.range fun q (f : F) => tbl f q) := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext q
    exact hΦn q
  have hker : LinearMap.ker Φ = ⨅ f, LinearMap.ker (ℓ f) := by
    ext v
    rw [LinearMap.mem_ker, Submodule.mem_iInf]
    constructor
    · intro h f
      rw [LinearMap.mem_ker]
      have hval := congrFun h f
      rw [hΦ, LinearMap.pi_apply] at hval
      simpa using hval
    · intro h
      have : Φ v = fun f => ℓ f v := by
        funext f
        rw [hΦ, LinearMap.pi_apply]
      rw [this]
      funext f
      exact LinearMap.mem_ker.mp (h f)
  constructor
  · set reach := Submodule.span ℂ (Set.range nst) with hreach
    set Φr := Φ.domRestrict reach with hΦr
    have hkerr : LinearMap.ker Φr
        = Submodule.comap reach.subtype
            (⨅ f, LinearMap.ker (ℓ f)) := by
      rw [hΦr, LinearMap.ker_domRestrict, hker]
    have hranger : LinearMap.range Φr
        = Submodule.span ℂ
            (Set.range fun q (f : F) => tbl f q) := by
      rw [hΦr, LinearMap.range_domRestrict, hmap]
    exact ⟨(Submodule.quotEquivOfEq _ _ hkerr.symm).trans
      ((Φr.quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ hranger))⟩
  · rw [← hmap]
    calc Module.finrank ℂ (Submodule.map Φ
          (Submodule.span ℂ (Set.range nst)))
        ≤ Module.finrank ℂ (LinearMap.range Φ) := by
          apply Submodule.finrank_mono
          rw [Submodule.map_le_iff_le_comap]
          intro v _
          rw [Submodule.mem_comap]
          exact LinearMap.mem_range_self Φ v
      _ ≤ Module.finrank ℂ N := LinearMap.finrank_range_le Φ

end NCG
