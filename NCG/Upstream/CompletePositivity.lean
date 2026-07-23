/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CPMap

/-!
# Context-stable positivity, the UCP renewal memory, and tomography

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `def:complete-operational-positivity` — a unital linear predictive
  map is completely operationally positive when every operational
  matrix-ancilla extension preserves the operationally realized
  positive cone; per `ass:operator-system` these cones are the
  canonical matrix cones of the operator-system realization,
  formalized here by quadratic-form positivity (`NCG.MatrixQF`);
* `thm:context-stable-cp` — completely operationally positive maps
  are completely positive (and UCP when unital), and conversely;
* `thm:emergent-ucp-memory` — the elementary renewal maps become
  UCP channels; the accumulated maps form a UCP monoid, finite
  whenever they are induced by transformations of a finite
  deterministic predictive set, while finitely many linear
  generators on a finite-dimensional space can generate an
  infinite monoid (explicit witness `halfMix`);
* `prop:tomographic-channel-equality` — under process tomography
  (spanning preparations, separating effects), transformation-level
  operational equality is exactly equality of accumulated linear
  maps, equivalently of their Heisenberg duals.
-/

namespace NCG.Upstream

open NCG

variable {S : Type*} [Ring S] [PartialOrder S] [StarRing S]
  [StarOrderedRing S] [Algebra ℂ S]

/-- **Definition `def:complete-operational-positivity`**: every
matrix-ancilla amplification preserves the operationally realized
positive cones (identified with the canonical matrix cones by
`ass:operator-system`). -/
def IsCompletelyOperationallyPositive (Φ : S →ₗ[ℂ] S) : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) S),
    MatrixQF M → MatrixQF (M.map Φ)

/-- **Theorem `thm:context-stable-cp` (equivalence)**: under the
operator-system identification of operational ancillary cones with
matrix cones, complete operational positivity *is* complete
positivity — requiring cone preservation at every matrix level is
the definition of a completely positive operator-system map. -/
theorem completelyOperationallyPositive_iff (Φ : S →ₗ[ℂ] S) :
    IsCompletelyOperationallyPositive Φ ↔ IsCompletelyPositive Φ :=
  Iff.rfl

/-- **Theorem `thm:context-stable-cp` (UCP)**: a unital completely
operationally positive map is UCP. -/
def contextStableUCP (Φ : S →ₗ[ℂ] S) (hu : Φ 1 = 1)
    (hcp : IsCompletelyOperationallyPositive Φ) : UCPMap S where
  toLinearMap := Φ
  map_one' := hu
  completelyPositive' := hcp

/-- **Theorem `thm:context-stable-cp` (converse)**: every UCP map is
positive in every operational matrix-ancilla context. -/
theorem ucp_operationallyPositive (φ : UCPMap S) :
    IsCompletelyOperationallyPositive φ.toLinearMap :=
  φ.completelyPositive

/-- **Theorem `thm:emergent-ucp-memory` (elementary channels)**: an
elementary renewal update whose Heisenberg map is unital and stable
under all operational matrix ancillas (hypothesis U4) is a UCP
channel. -/
def emergentUCP (Φ : S →ₗ[ℂ] S) (hu : Φ 1 = 1)
    (hstable : IsCompletelyOperationallyPositive Φ) : UCPMap S :=
  contextStableUCP Φ hu hstable

/-- **Theorem `thm:emergent-ucp-memory` (monoid law)**: accumulated
UCP maps compose to UCP maps (the UCP renewal monoid). -/
theorem emergentUCP_comp (φ ψ : UCPMap S) (a : S) :
    (φ * ψ) a = ψ (φ a) :=
  UCPMap.mul_apply φ ψ a

/-- **Theorem `thm:emergent-ucp-memory` (finiteness)**: a UCP
renewal monoid induced by a homomorphism from a finite monoid of
transformations of the finite deterministic predictive set (the
finite renewal monoid of `cor:finite-renewal-monoid`) is finite. -/
theorem emergentUCP_finite {M : Type*} [Monoid M] [Finite M]
    (ρ : M →* UCPMap S) : Finite (MonoidHom.mrange ρ) := by
  have hfin : ((MonoidHom.mrange ρ : Submonoid (UCPMap S))
      : Set (UCPMap S)).Finite := by
    rw [MonoidHom.coe_mrange]
    exact Set.finite_range ρ
  exact hfin.to_subtype

section InfiniteMonoid

/-- The mixing map `(x, y) ↦ (x, (x+y)/2)` — a unital positive
linear map on the ordered plane. -/
noncomputable def halfMix : Module.End ℝ (ℝ × ℝ) where
  toFun p := (p.1, (p.1 + p.2) / 2)
  map_add' p q := by
    apply Prod.ext <;> simp <;> ring
  map_smul' c p := by
    apply Prod.ext <;> simp <;> ring

theorem halfMix_apply (p : ℝ × ℝ) :
    halfMix p = (p.1, (p.1 + p.2) / 2) := rfl

/-- `halfMix` is unital for the order unit `(1,1)`. -/
theorem halfMix_unital : halfMix ((1 : ℝ), (1 : ℝ)) = (1, 1) := by
  rw [halfMix_apply]
  norm_num

/-- `halfMix` preserves the coordinatewise positive cone. -/
theorem halfMix_positive {p : ℝ × ℝ} (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2) :
    0 ≤ (halfMix p).1 ∧ 0 ≤ (halfMix p).2 :=
  ⟨h1, by rw [halfMix_apply]; dsimp; linarith⟩

theorem halfMix_pow_apply (n : ℕ) :
    ∀ y : ℝ, (halfMix ^ n) ((0 : ℝ), y) = (0, y / 2 ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    rw [pow_succ, Module.End.mul_apply]
    have h1 : halfMix ((0 : ℝ), y) = (0, y / 2) := by
      rw [halfMix_apply]
      norm_num
    have h2 : y / 2 / 2 ^ n = y / 2 ^ (n + 1) := by
      rw [pow_succ]
      ring
    rw [h1, ih (y / 2), h2]

/-- **Theorem `thm:emergent-ucp-memory` (no-go)**: distinct powers —
a single unital positive linear generator on a two-dimensional
ordered space generates an infinite monoid, so finite dimensionality
and a finite alphabet alone do not force a finite channel monoid. -/
theorem halfMix_pow_injective :
    Function.Injective (fun n : ℕ => halfMix ^ n) := by
  intro m n hmn
  have h := congrArg (fun f : Module.End ℝ (ℝ × ℝ) =>
    (f ((0 : ℝ), (1 : ℝ))).2) hmn
  simp only [halfMix_pow_apply] at h
  have h2 : ((2 : ℝ) ^ m)⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
    simpa [one_div] using h
  have h3 := inv_injective h2
  have hmono : StrictMono (fun k : ℕ => (2 : ℝ) ^ k) :=
    fun a b hab => pow_lt_pow_right₀ one_lt_two hab
  exact hmono.injective h3

-- elaborating the closure subtype needs a higher heartbeat budget
set_option maxHeartbeats 800000 in
/-- **Theorem `thm:emergent-ucp-memory` (no-go, packaged)**: the
monoid generated by `halfMix` is infinite. -/
theorem halfMix_closure_infinite :
    Infinite
      (Submonoid.closure ({halfMix} : Set (Module.End ℝ (ℝ × ℝ)))) := by
  have hmem : ∀ n : ℕ, halfMix ^ n
      ∈ Submonoid.closure ({halfMix} : Set (Module.End ℝ (ℝ × ℝ))) :=
    fun n => pow_mem (Submonoid.subset_closure (Set.mem_singleton _)) n
  exact Infinite.of_injective
    (fun n : ℕ => ⟨halfMix ^ n, hmem n⟩)
    fun m n h => halfMix_pow_injective (congrArg Subtype.val h)

end InfiniteMonoid

section Tomography

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Proposition `prop:tomographic-channel-equality`**: under
process tomography — spanning preparations and separating effects —
two transformations have identical operational profiles iff their
accumulated linear maps are equal. -/
theorem tomographic_channel_equality
    (prep : Set V) (hspan : Submodule.span ℝ prep = ⊤)
    (effects : Set (Module.Dual ℝ V))
    (hsep : ∀ w w' : V, (∀ a ∈ effects, a w = a w') → w = w')
    (T T' : V →ₗ[ℝ] V) :
    (∀ v ∈ prep, ∀ a ∈ effects, a (T v) = a (T' v)) ↔ T = T' := by
  constructor
  · intro hpair
    apply LinearMap.ext_on hspan
    intro v hv
    exact hsep _ _ fun a ha => hpair v hv a ha
  · rintro rfl
    exact fun _ _ _ _ => rfl

/-- **Proposition `prop:tomographic-channel-equality` (Heisenberg
form)**: with separating effects, equality of the accumulated state
maps is equality of their Heisenberg duals. -/
theorem tomographic_heisenberg_equality
    (effects : Set (Module.Dual ℝ V))
    (hsep : ∀ w w' : V, (∀ a ∈ effects, a w = a w') → w = w')
    (T T' : V →ₗ[ℝ] V) :
    T = T' ↔ T.dualMap = T'.dualMap := by
  constructor
  · rintro rfl; rfl
  · intro hdual
    apply LinearMap.ext
    intro v
    refine hsep _ _ fun a _ => ?_
    exact congrFun (congrArg DFunLike.coe
      (congrFun (congrArg DFunLike.coe hdual) a)) v

end Tomography

end NCG.Upstream
