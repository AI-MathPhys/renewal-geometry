/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical typed Hankel realization over a general field, with the equality case
  (`thm:supp-hankel`, emergent-spacetime manuscript)

For one typed operational sector `(x, z)` let `P` be the pasts, `F` the futures
and `𝕡(f, p)` the Hankel table, with values in any field `K` (the manuscript uses
`K = ℝ`).  The Hankel column space is `M = span_K {h_p}`, `h_p = 𝕡(·, p)`.

* `HankelSpace`, `hankelState`, `hankelEffect`: `M`, its states `h_p ∈ M` and
  evaluation effects `λ_f(m) = m(f)`, with `λ_f(h_p) = 𝕡(f,p)`
  (`hankelEffect_state`).
* `hankelSpace_reachable`, `hankelSpace_separated`: `M` is reachable (the
  states span `M`) and future separated (the effects separate `M`).
* `hankelTransition`: for a primitive event `a` with past map `p ↦ a∘p` and
  future map `f ↦ f∘a` satisfying `𝕡'(f, a∘p) = 𝕡(f∘a, p)`, the linear map
  `A_a : M → M'` with `A_a h_p = h_{a∘p}` and `λ_f A_a = λ_{f∘a}`
  (`hankelTransition_state`, `hankelEffect_comp_hankelTransition`), unique
  (`hankelTransition_unique`).
* `hankel_reach_quot_unobs_equiv`: for any linear realization (states `n_p ∈ N`,
  effects `μ_f` with `μ_f(n_p) = 𝕡(f,p)`), `N^reach / N^unobs ≃ M`.
* `hankel_finrank_le`: `dim M ≤ dim N`.
* `hankel_finrank_eq_iff`: **equality exactly on the reachable future-separated
  branch**: `dim N = dim M ↔ (span{n_p} = N ∧ ⋂_f ker μ_f = 0)`.
* `typed_hankel_realization_field`: the bundled theorem.

This supersedes, over an arbitrary field, the `ℂ`-valued
`RenewalGeometry.hankel_minimality` and `RenewalGeometry.typed_hankel_realization`
and adds the converse direction of the equality case.
-/

namespace RenewalGeometry

namespace HankelField

variable {K : Type*} [Field K]

section Core

variable {P F : Type*} (tbl : F → P → K)

/-- The Hankel column space `M = span {h_p}` inside `F → K`. -/
abbrev HankelSpace : Submodule K (F → K) :=
  Submodule.span K (Set.range fun p (f : F) => tbl f p)

/-- The Hankel state of a past: `h_p = 𝕡(·, p) ∈ M`. -/
def hankelState (p : P) : HankelSpace tbl :=
  ⟨fun f => tbl f p, Submodule.subset_span ⟨p, rfl⟩⟩

/-- The evaluation effect of a future: `λ_f(m) = m(f)`. -/
def hankelEffect (f : F) : HankelSpace tbl →ₗ[K] K :=
  (LinearMap.proj f).comp (HankelSpace tbl).subtype

theorem hankelEffect_apply (f : F) (m : HankelSpace tbl) :
    hankelEffect tbl f m = (m : F → K) f := rfl

/-- `𝕡(f, p) = λ_f(h_p)`. -/
theorem hankelEffect_state (f : F) (p : P) :
    hankelEffect tbl f (hankelState tbl p) = tbl f p := rfl

/-- The Hankel realization is reachable: its states span `M`. -/
theorem hankelSpace_reachable :
    Submodule.span K (Set.range (hankelState tbl)) = ⊤ := by
  apply Submodule.map_injective_of_injective (HankelSpace tbl).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

/-- The Hankel realization is future separated: a vector killed by every
effect is zero. -/
theorem hankelSpace_separated (m : HankelSpace tbl)
    (hm : ∀ f, hankelEffect tbl f m = 0) : m = 0 := by
  apply Subtype.ext
  funext f
  exact hm f

end Core

section Transition

variable {P F P' F' : Type*} (tbl : F → P → K) (tbl' : F' → P' → K)
  (ca : P → P') (fa : F' → F)

/-- Precomposition with a primitive event maps Hankel columns into Hankel
columns, hence `M` into `M'`. -/
theorem precomp_mem_hankelSpace (hcompat : ∀ f' q, tbl' f' (ca q) = tbl (fa f') q)
    (g : F → K) (hg : g ∈ HankelSpace tbl) :
    (fun f' => g (fa f')) ∈ HankelSpace tbl' := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨q, rfl⟩ := hg
      refine Submodule.subset_span ⟨ca q, ?_⟩
      funext f'
      exact hcompat f' q
  | zero => exact (HankelSpace tbl').zero_mem
  | add g₁ g₂ _ _ h₁ h₂ => exact (HankelSpace tbl').add_mem h₁ h₂
  | smul c g _ h => exact (HankelSpace tbl').smul_mem c h

/-- Precomposition with the primitive event on futures, restricted to the
Hankel spaces: `A_a : M → M'`. -/
def hankelTransition (hcompat : ∀ f' q, tbl' f' (ca q) = tbl (fa f') q) :
    HankelSpace tbl →ₗ[K] HankelSpace tbl' :=
  LinearMap.codRestrict (HankelSpace tbl')
    (((LinearMap.funLeft K K fa)).comp (HankelSpace tbl).subtype)
    (fun m => precomp_mem_hankelSpace tbl tbl' ca fa hcompat m m.property)

variable (hcompat : ∀ f' q, tbl' f' (ca q) = tbl (fa f') q)

/-- `A_a h_p = h_{a∘p}`. -/
theorem hankelTransition_state (p : P) :
    hankelTransition tbl tbl' ca fa hcompat (hankelState tbl p) =
      hankelState tbl' (ca p) := by
  apply Subtype.ext
  funext f'
  exact (hcompat f' p).symm

/-- `λ_f A_a = λ_{f∘a}`. -/
theorem hankelEffect_comp_hankelTransition (f' : F') :
    (hankelEffect tbl' f').comp (hankelTransition tbl tbl' ca fa hcompat) =
      hankelEffect tbl (fa f') := rfl

/-- Uniqueness of `A_a`: any linear map with `A h_p = h_{a∘p}` is `A_a`. -/
theorem hankelTransition_unique (A : HankelSpace tbl →ₗ[K] HankelSpace tbl')
    (hA : ∀ p, A (hankelState tbl p) = hankelState tbl' (ca p)) :
    A = hankelTransition tbl tbl' ca fa hcompat := by
  apply LinearMap.ext_on_range (hankelSpace_reachable tbl)
  intro p
  rw [hA, hankelTransition_state]

end Transition

section Minimality

variable {P F N : Type*} [AddCommGroup N] [Module K N]
  (tbl : F → P → K) (nst : P → N) (μ : F → N →ₗ[K] K)

/-- The response map `n ↦ (f ↦ μ_f(n))` of a linear realization. -/
def responseMap : N →ₗ[K] (F → K) := LinearMap.pi μ

theorem responseMap_apply (v : N) (f : F) : responseMap μ v f = μ f v := rfl

theorem responseMap_ker : LinearMap.ker (responseMap μ) = ⨅ f, LinearMap.ker (μ f) := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  constructor
  · intro h f
    exact congrFun h f
  · intro h
    funext f
    exact h f

variable {tbl nst μ}

theorem responseMap_map_reach (hmatch : ∀ f p, μ f (nst p) = tbl f p) :
    Submodule.map (responseMap μ) (Submodule.span K (Set.range nst)) = HankelSpace tbl := by
  have hcomp : (responseMap μ) ∘ nst = fun p f => tbl f p := by
    funext p f
    exact hmatch f p
  rw [Submodule.map_span, ← Set.range_comp, hcomp]

/-- `N^reach / N^unobs ≃ M` for every linear realization. -/
noncomputable def hankel_reach_quot_unobs_equiv (hmatch : ∀ f p, μ f (nst p) = tbl f p) :
    (Submodule.span K (Set.range nst) ⧸
        Submodule.comap (Submodule.span K (Set.range nst)).subtype
          (⨅ f, LinearMap.ker (μ f))) ≃ₗ[K] HankelSpace tbl :=
  let reach := Submodule.span K (Set.range nst)
  let Φr := (responseMap μ).domRestrict reach
  have hker : LinearMap.ker Φr =
      Submodule.comap reach.subtype (⨅ f, LinearMap.ker (μ f)) := by
    rw [LinearMap.ker_domRestrict, responseMap_ker]
  have hrange : LinearMap.range Φr = HankelSpace tbl := by
    rw [LinearMap.range_domRestrict, responseMap_map_reach hmatch]
  (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (Φr.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

/-- The identification sends the class of `n_p` to `h_p`. -/
theorem hankel_reach_quot_unobs_equiv_state (hmatch : ∀ f p, μ f (nst p) = tbl f p)
    (p : P) :
    hankel_reach_quot_unobs_equiv hmatch
        (Submodule.Quotient.mk ⟨nst p, Submodule.subset_span ⟨p, rfl⟩⟩) =
      hankelState tbl p := by
  apply Subtype.ext
  funext f
  exact hmatch f p

variable [FiniteDimensional K N]

/-- Every linear realization has dimension at least `dim M`. -/
theorem hankel_finrank_le (hmatch : ∀ f p, μ f (nst p) = tbl f p) :
    Module.finrank K (HankelSpace tbl) ≤ Module.finrank K N := by
  rw [← responseMap_map_reach hmatch]
  exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_le _)

/-- **Equality case.**  A linear realization has the Hankel dimension exactly
when it is reachable and future separated. -/
theorem hankel_finrank_eq_iff (hmatch : ∀ f p, μ f (nst p) = tbl f p) :
    Module.finrank K N = Module.finrank K (HankelSpace tbl) ↔
      (Submodule.span K (Set.range nst) = ⊤ ∧
        ∀ v : N, (∀ f, μ f v = 0) → v = 0) := by
  have hmap := responseMap_map_reach hmatch
  constructor
  · intro heq
    -- dim M = dim Φ(reach) ≤ dim reach ≤ dim N = dim M
    have h1 : Module.finrank K (HankelSpace tbl) ≤
        Module.finrank K (Submodule.span K (Set.range nst)) := by
      rw [← hmap]; exact Submodule.finrank_map_le _ _
    have h2 := Submodule.finrank_le (Submodule.span K (Set.range nst))
    have hreach : Submodule.span K (Set.range nst) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by omega)
    refine ⟨hreach, ?_⟩
    have hrange : LinearMap.range (responseMap μ) = HankelSpace tbl := by
      rw [LinearMap.range_eq_map, ← hreach, hmap]
    have hrn := LinearMap.finrank_range_add_finrank_ker (responseMap μ)
    rw [hrange, ← heq] at hrn
    have hk0 : Module.finrank K (LinearMap.ker (responseMap μ)) = 0 := by omega
    have hker : LinearMap.ker (responseMap μ) = ⊥ := Submodule.finrank_eq_zero.mp hk0
    intro v hv
    have : v ∈ LinearMap.ker (responseMap μ) := by
      rw [LinearMap.mem_ker]
      funext f
      exact hv f
    rw [hker] at this
    exact (Submodule.mem_bot K).mp this
  · rintro ⟨hreach, hsep⟩
    have hrange : LinearMap.range (responseMap μ) = HankelSpace tbl := by
      rw [LinearMap.range_eq_map, ← hreach, hmap]
    have hker : LinearMap.ker (responseMap μ) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker] at hv
      exact (Submodule.mem_bot K).mpr (hsep v fun f => congrFun hv f)
    have hrn := LinearMap.finrank_range_add_finrank_ker (responseMap μ)
    rw [hrange, hker, finrank_bot] at hrn
    omega

end Minimality

/-- `thm:supp-hankel`, bundled over an arbitrary field (in particular `ℝ`).
For one sector with Hankel table `𝕡`, the canonical realization `M` is reachable
and future separated, every primitive event acts by the unique `A_a` with
`A_a h_p = h_{a∘p}` and `λ_f A_a = λ_{f∘a}`; for every finite-dimensional linear
realization `N`: `N^reach/N^unobs ≃ M`, `dim M ≤ dim N`, with equality exactly
when `N` is reachable and future separated. -/
theorem typed_hankel_realization_field {P F P' F' N : Type*} [AddCommGroup N]
    [Module K N] [FiniteDimensional K N]
    (tbl : F → P → K) (tbl' : F' → P' → K) (ca : P → P') (fa : F' → F)
    (hcompat : ∀ f' q, tbl' f' (ca q) = tbl (fa f') q)
    (nst : P → N) (μ : F → N →ₗ[K] K) (hmatch : ∀ f p, μ f (nst p) = tbl f p) :
    -- reachability and separation of `M`
    (Submodule.span K (Set.range (hankelState tbl)) = ⊤
      ∧ ∀ m : HankelSpace tbl, (∀ f, hankelEffect tbl f m = 0) → m = 0)
    -- the transition `A_a`
    ∧ (∃! A : HankelSpace tbl →ₗ[K] HankelSpace tbl',
        ∀ p, A (hankelState tbl p) = hankelState tbl' (ca p))
    ∧ (∀ f' : F', (hankelEffect tbl' f').comp (hankelTransition tbl tbl' ca fa hcompat) =
        hankelEffect tbl (fa f'))
    -- minimality
    ∧ Nonempty ((Submodule.span K (Set.range nst) ⧸
        Submodule.comap (Submodule.span K (Set.range nst)).subtype
          (⨅ f, LinearMap.ker (μ f))) ≃ₗ[K] HankelSpace tbl)
    ∧ Module.finrank K (HankelSpace tbl) ≤ Module.finrank K N
    ∧ (Module.finrank K N = Module.finrank K (HankelSpace tbl) ↔
        (Submodule.span K (Set.range nst) = ⊤ ∧ ∀ v : N, (∀ f, μ f v = 0) → v = 0)) :=
  ⟨⟨hankelSpace_reachable tbl, hankelSpace_separated tbl⟩,
    ⟨hankelTransition tbl tbl' ca fa hcompat, hankelTransition_state tbl tbl' ca fa hcompat,
      fun A hA => hankelTransition_unique tbl tbl' ca fa hcompat A hA⟩,
    hankelEffect_comp_hankelTransition tbl tbl' ca fa hcompat,
    ⟨hankel_reach_quot_unobs_equiv hmatch⟩, hankel_finrank_le hmatch,
    hankel_finrank_eq_iff hmatch⟩

/-! ### Non-vacuity -/

/-- A two-state real table: pasts and futures `Fin 2`, table = identity.
The canonical realization `M = ℝ²` is reachable/separated; a padded
realization `N = ℝ³` (extra unobservable direction) is strictly bigger and,
by the equality case, not separated. -/
example :
    let tbl : Fin 2 → Fin 2 → ℝ := fun f p => if f = p then 1 else 0
    Module.finrank ℝ (HankelSpace tbl) = 2 ∧
      ¬ (Submodule.span ℝ (Set.range (fun p : Fin 2 => (Pi.single (p.castSucc) 1 : Fin 3 → ℝ)))
          = ⊤ ∧ ∀ v : Fin 3 → ℝ,
            (∀ f : Fin 2, (LinearMap.proj (f.castSucc) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) v = 0) → v = 0) := by
  intro tbl
  have hM : HankelSpace tbl = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have : v = ∑ p : Fin 2, v p • (fun f => tbl f p) := by
      funext f
      fin_cases f <;> simp [tbl]
    rw [this]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have h2 : Module.finrank ℝ (HankelSpace tbl) = 2 := by
    rw [hM, finrank_top, Module.finrank_fin_fun]
  refine ⟨h2, fun h => ?_⟩
  have hmatch : ∀ (f p : Fin 2),
      (LinearMap.proj (f.castSucc) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
        ((Pi.single (p.castSucc) 1 : Fin 3 → ℝ)) = tbl f p := by
    intro f p
    fin_cases f <;> fin_cases p <;> simp [tbl]
  have := (hankel_finrank_eq_iff (K := ℝ) (tbl := tbl) hmatch).2 h
  rw [h2, Module.finrank_fin_fun] at this
  omega

end HankelField

end RenewalGeometry
