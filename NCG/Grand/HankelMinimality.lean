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

/-! ## The minimal (reachable and observable) case

The quotient statement above is useful even for nonminimal realizations.  The
manuscript also needs the equality case as an actual canonical map, together
with its uniqueness and naturality for the primitive transitions.  The next
definitions package those clauses without choosing bases.
-/

/-- The intrinsic Hankel response space associated with a scalar table. -/
abbrev HankelCore (P F : Type*) (tbl : F → P → ℂ) : Submodule ℂ (F → ℂ) :=
  Submodule.span ℂ (Set.range fun p (f : F) => tbl f p)

/-- A reachable and future-separated realization is canonically equivalent to
its Hankel response space. -/
noncomputable def hankelCoreEquiv {P F N : Type*} [AddCommGroup N]
    [Module ℂ N] (tbl : F → P → ℂ) (nst : P → N)
    (ℓ : F → N →ₗ[ℂ] ℂ) (hmatch : ∀ f p, ℓ f (nst p) = tbl f p)
    (hreach : Submodule.span ℂ (Set.range nst) = ⊤)
    (hsep : ∀ v : N, (∀ f, ℓ f v = 0) → v = 0) :
    N ≃ₗ[ℂ] HankelCore P F tbl := by
  let Φ : N →ₗ[ℂ] (F → ℂ) := LinearMap.pi (fun f => ℓ f)
  have hΦn : ∀ p, Φ (nst p) = fun f => tbl f p := by
    intro p
    funext f
    exact hmatch f p
  have hmap : Submodule.map Φ (Submodule.span ℂ (Set.range nst)) =
      HankelCore P F tbl := by
    rw [Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext p
    exact hΦn p
  let toCore : N →ₗ[ℂ] HankelCore P F tbl :=
    LinearMap.codRestrict (HankelCore P F tbl) Φ fun v => by
      rw [← hmap, hreach]
      exact ⟨v, by simp, rfl⟩
  refine LinearEquiv.ofBijective toCore ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hsep
    intro f
    have hz : toCore (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact congrFun (congrArg Subtype.val hz) f
  · intro y
    have hy : (y : F → ℂ) ∈
        Submodule.map Φ (Submodule.span ℂ (Set.range nst)) := by
      rw [hmap]
      exact y.property
    rw [hreach] at hy
    obtain ⟨v, _, hv⟩ := hy
    refine ⟨v, Subtype.ext ?_⟩
    exact hv

@[simp]
theorem hankelCoreEquiv_state {P F N : Type*} [AddCommGroup N]
    [Module ℂ N] (tbl : F → P → ℂ) (nst : P → N)
    (ℓ : F → N →ₗ[ℂ] ℂ) (hmatch : ∀ f p, ℓ f (nst p) = tbl f p)
    (hreach : Submodule.span ℂ (Set.range nst) = ⊤)
    (hsep : ∀ v : N, (∀ f, ℓ f v = 0) → v = 0) (p : P) :
    ((hankelCoreEquiv tbl nst ℓ hmatch hreach hsep (nst p) :
        HankelCore P F tbl) : F → ℂ) = fun f => tbl f p := by
  funext f
  exact hmatch f p

/-- The canonical record-preserving similarity between two minimal
realizations of the same operational table. -/
noncomputable def minimalRealizationSimilarity
    {P F N₁ N₂ : Type*} [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (tbl : F → P → ℂ) (n₁ : P → N₁) (n₂ : P → N₂)
    (ℓ₁ : F → N₁ →ₗ[ℂ] ℂ) (ℓ₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p)
    (hmatch₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p)
    (hreach₁ : Submodule.span ℂ (Set.range n₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range n₂) = ⊤)
    (hsep₁ : ∀ v : N₁, (∀ f, ℓ₁ f v = 0) → v = 0)
    (hsep₂ : ∀ v : N₂, (∀ f, ℓ₂ f v = 0) → v = 0) :
    N₁ ≃ₗ[ℂ] N₂ :=
  (hankelCoreEquiv tbl n₁ ℓ₁ hmatch₁ hreach₁ hsep₁).trans
    (hankelCoreEquiv tbl n₂ ℓ₂ hmatch₂ hreach₂ hsep₂).symm

@[simp]
theorem minimalRealizationSimilarity_state
    {P F N₁ N₂ : Type*} [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (tbl : F → P → ℂ) (n₁ : P → N₁) (n₂ : P → N₂)
    (ℓ₁ : F → N₁ →ₗ[ℂ] ℂ) (ℓ₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p)
    (hmatch₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p)
    (hreach₁ : Submodule.span ℂ (Set.range n₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range n₂) = ⊤)
    (hsep₁ : ∀ v : N₁, (∀ f, ℓ₁ f v = 0) → v = 0)
    (hsep₂ : ∀ v : N₂, (∀ f, ℓ₂ f v = 0) → v = 0) (p : P) :
    minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hmatch₁ hmatch₂
      hreach₁ hreach₂ hsep₁ hsep₂ (n₁ p) = n₂ p := by
  simp only [minimalRealizationSimilarity, LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  exact (hankelCoreEquiv_state tbl n₁ ℓ₁ hmatch₁ hreach₁ hsep₁ p).trans
    (hankelCoreEquiv_state tbl n₂ ℓ₂ hmatch₂ hreach₂ hsep₂ p).symm

/-- The canonical similarity is the unique linear map preserving all past
states.  Reachability is the essential uniqueness input. -/
theorem minimalRealizationSimilarity_unique
    {P F N₁ N₂ : Type*} [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (tbl : F → P → ℂ) (n₁ : P → N₁) (n₂ : P → N₂)
    (ℓ₁ : F → N₁ →ₗ[ℂ] ℂ) (ℓ₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p)
    (hmatch₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p)
    (hreach₁ : Submodule.span ℂ (Set.range n₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range n₂) = ⊤)
    (hsep₁ : ∀ v : N₁, (∀ f, ℓ₁ f v = 0) → v = 0)
    (hsep₂ : ∀ v : N₂, (∀ f, ℓ₂ f v = 0) → v = 0)
    (S : N₁ →ₗ[ℂ] N₂) (hS : ∀ p, S (n₁ p) = n₂ p) :
    S = (minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hmatch₁ hmatch₂
      hreach₁ hreach₂ hsep₁ hsep₂ : N₁ →ₗ[ℂ] N₂) := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span ℂ (Set.range n₁) := by
    rw [hreach₁]
    trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      simpa using hS p
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- Primitive transitions are intertwined by the canonical similarity. -/
theorem minimalRealizationSimilarity_intertwines
    {P F N₁ N₂ : Type*} [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (tbl : F → P → ℂ) (n₁ : P → N₁) (n₂ : P → N₂)
    (ℓ₁ : F → N₁ →ₗ[ℂ] ℂ) (ℓ₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p)
    (hmatch₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p)
    (hreach₁ : Submodule.span ℂ (Set.range n₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range n₂) = ⊤)
    (hsep₁ : ∀ v : N₁, (∀ f, ℓ₁ f v = 0) → v = 0)
    (hsep₂ : ∀ v : N₂, (∀ f, ℓ₂ f v = 0) → v = 0)
    (next : P → P) (A₁ : N₁ →ₗ[ℂ] N₁) (A₂ : N₂ →ₗ[ℂ] N₂)
    (hA₁ : ∀ p, A₁ (n₁ p) = n₁ (next p))
    (hA₂ : ∀ p, A₂ (n₂ p) = n₂ (next p)) :
    (minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hmatch₁ hmatch₂
      hreach₁ hreach₂ hsep₁ hsep₂ : N₁ →ₗ[ℂ] N₂).comp A₁ =
      A₂.comp (minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hmatch₁ hmatch₂
        hreach₁ hreach₂ hsep₁ hsep₂ : N₁ →ₗ[ℂ] N₂) := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span ℂ (Set.range n₁) := by
    rw [hreach₁]
    trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      simp [LinearMap.comp_apply, hA₁, hA₂]
  | zero => simp
  | add x y _ _ hx hy =>
      simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
  | smul c x _ hx =>
      simpa only [map_smul, LinearMap.comp_apply] using congrArg (c • ·) hx

/-- Future effects are transported by the canonical similarity. -/
theorem minimalRealizationSimilarity_future
    {P F N₁ N₂ : Type*} [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (tbl : F → P → ℂ) (n₁ : P → N₁) (n₂ : P → N₂)
    (ℓ₁ : F → N₁ →ₗ[ℂ] ℂ) (ℓ₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch₁ : ∀ f p, ℓ₁ f (n₁ p) = tbl f p)
    (hmatch₂ : ∀ f p, ℓ₂ f (n₂ p) = tbl f p)
    (hreach₁ : Submodule.span ℂ (Set.range n₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range n₂) = ⊤)
    (hsep₁ : ∀ v : N₁, (∀ f, ℓ₁ f v = 0) → v = 0)
    (hsep₂ : ∀ v : N₂, (∀ f, ℓ₂ f v = 0) → v = 0)
    (f : F) (v : N₁) :
    ℓ₂ f (minimalRealizationSimilarity tbl n₁ n₂ ℓ₁ ℓ₂ hmatch₁ hmatch₂
      hreach₁ hreach₂ hsep₁ hsep₂ v) = ℓ₁ f v := by
  have hv : v ∈ Submodule.span ℂ (Set.range n₁) := by
    rw [hreach₁]
    trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      rw [minimalRealizationSimilarity_state]
      exact (hmatch₂ f p).trans (hmatch₁ f p).symm
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x _ hx => simpa only [map_smul] using congrArg (c • ·) hx

/-- Reachability and future separation characterize the equality case in the
Hankel dimension bound. -/
theorem hankel_minimality_finrank_eq {P F N : Type*} [AddCommGroup N]
    [Module ℂ N] [FiniteDimensional ℂ N]
    (tbl : F → P → ℂ) (nst : P → N) (ℓ : F → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f p, ℓ f (nst p) = tbl f p)
    (hreach : Submodule.span ℂ (Set.range nst) = ⊤)
    (hsep : ∀ v : N, (∀ f, ℓ f v = 0) → v = 0) :
    Module.finrank ℂ N = Module.finrank ℂ (HankelCore P F tbl) :=
  (hankelCoreEquiv tbl nst ℓ hmatch hreach hsep).finrank_eq

end NCG
