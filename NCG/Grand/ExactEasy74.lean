import NCG.Grand.SealedProvenanceQuotient

/-!
# Exact EASY 74: unique similarity of minimal passive realizations

The sealed-provenance quotient already supplies the invariant reachable
carrier, invariant Read-null subspace, exact quotient sequence, descended
letters, and response factorization.  This file proves the remaining
minimal-realization statement: two source-reachable and Read-observable
realizations of the same complete table are uniquely linearly similar.
-/

namespace NCG

/-- The complete observation map of a family of Reads. -/
def completeObservation {F N : Type*} [AddCommMonoid N] [Module ℂ N]
    (read : F → N →ₗ[ℂ] ℂ) : N →ₗ[ℂ] (F → ℂ) :=
  LinearMap.pi read

/-- Source-reachable, Read-observable realizations of the same complete table
have a unique source-fixing similarity.  It intertwines every letter whose
action is specified on the reachable source family, and it intertwines every
Read. -/
theorem reachable_observable_unique_similarity
    {P F N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂]
    (src₁ : P → N₁) (src₂ : P → N₂)
    (read₁ : F → N₁ →ₗ[ℂ] ℂ) (read₂ : F → N₂ →ₗ[ℂ] ℂ)
    (hmatch : ∀ f p, read₁ f (src₁ p) = read₂ f (src₂ p))
    (hreach₁ : Submodule.span ℂ (Set.range src₁) = ⊤)
    (hreach₂ : Submodule.span ℂ (Set.range src₂) = ⊤)
    (hobs₁ : (⨅ f, LinearMap.ker (read₁ f)) = ⊥)
    (hobs₂ : (⨅ f, LinearMap.ker (read₂ f)) = ⊥) :
    ∃ E : N₁ ≃ₗ[ℂ] N₂,
      (∀ p, E (src₁ p) = src₂ p)
      ∧ (∀ f x, read₂ f (E x) = read₁ f x)
      ∧ (∀ G : N₁ ≃ₗ[ℂ] N₂,
          (∀ p, G (src₁ p) = src₂ p) → G = E)
      ∧ (∀ (next : P → P) (A₁ : N₁ →ₗ[ℂ] N₁)
            (A₂ : N₂ →ₗ[ℂ] N₂),
          (∀ p, A₁ (src₁ p) = src₁ (next p)) →
          (∀ p, A₂ (src₂ p) = src₂ (next p)) →
          ∀ x, E (A₁ x) = A₂ (E x)) := by
  let Φ₁ : N₁ →ₗ[ℂ] (F → ℂ) := completeObservation read₁
  let Φ₂ : N₂ →ₗ[ℂ] (F → ℂ) := completeObservation read₂
  have hΦ₁_apply : ∀ x f, Φ₁ x f = read₁ f x := by
    intro x f
    rfl
  have hΦ₂_apply : ∀ x f, Φ₂ x f = read₂ f x := by
    intro x f
    rfl
  have hΦ₁_inj : Function.Injective Φ₁ := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot, Φ₁,
      completeObservation]
    constructor
    · intro hx
      have hxker : x ∈ ⨅ f, LinearMap.ker (read₁ f) := by
        rw [Submodule.mem_iInf]
        intro f
        rw [LinearMap.mem_ker]
        exact congrFun hx f
      rw [hobs₁] at hxker
      exact hxker
    · rintro rfl
      simp
  have hΦ₂_inj : Function.Injective Φ₂ := by
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot, Φ₂,
      completeObservation]
    constructor
    · intro hx
      have hxker : x ∈ ⨅ f, LinearMap.ker (read₂ f) := by
        rw [Submodule.mem_iInf]
        intro f
        rw [LinearMap.mem_ker]
        exact congrFun hx f
      rw [hobs₂] at hxker
      exact hxker
    · rintro rfl
      simp
  have hsrc : ∀ p, Φ₁ (src₁ p) = Φ₂ (src₂ p) := by
    intro p
    funext f
    exact hmatch f p
  have hrange₁ : LinearMap.range Φ₁ =
      Submodule.span ℂ (Set.range fun p => Φ₁ (src₁ p)) := by
    rw [← Submodule.map_top, ← hreach₁, Submodule.map_span]
    congr 2
    ext y
    simp
  have hrange₂ : LinearMap.range Φ₂ =
      Submodule.span ℂ (Set.range fun p => Φ₂ (src₂ p)) := by
    rw [← Submodule.map_top, ← hreach₂, Submodule.map_span]
    congr 2
    ext y
    simp
  have hrange : LinearMap.range Φ₁ = LinearMap.range Φ₂ := by
    rw [hrange₁, hrange₂]
    congr 2
    funext p
    exact hsrc p
  let E : N₁ ≃ₗ[ℂ] N₂ :=
    (LinearEquiv.ofInjective Φ₁ hΦ₁_inj).trans
      ((LinearEquiv.ofEq _ _ hrange).trans
        (LinearEquiv.ofInjective Φ₂ hΦ₂_inj).symm)
  have hΦE : ∀ x, Φ₂ (E x) = Φ₁ x := by
    intro x
    let z : LinearMap.range Φ₂ :=
      (LinearEquiv.ofEq (LinearMap.range Φ₁) (LinearMap.range Φ₂)
        hrange) ((LinearEquiv.ofInjective Φ₁ hΦ₁_inj) x)
    have hz := congrArg Subtype.val
      ((LinearEquiv.ofInjective Φ₂ hΦ₂_inj).apply_symm_apply z)
    simpa only [E, LinearEquiv.trans_apply, z,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply] using hz
  have hEsrc : ∀ p, E (src₁ p) = src₂ p := by
    intro p
    apply hΦ₂_inj
    rw [hΦE]
    exact hsrc p
  refine ⟨E, hEsrc, ?_, ?_, ?_⟩
  · intro f x
    have h := congrFun (hΦE x) f
    exact h
  · intro G hG
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range src₁) := by
      rw [hreach₁]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        rw [hG p, hEsrc p]
    | zero => simp
    | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
    | smul c x _ hx => simpa using congrArg (c • ·) hx
  · intro next A₁ A₂ hA₁ hA₂ x
    have hx : x ∈ Submodule.span ℂ (Set.range src₁) := by
      rw [hreach₁]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        rw [hA₁ p, hEsrc (next p), hEsrc p, hA₂ p]
    | zero => simp
    | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
    | smul c x _ hx => simpa using congrArg (c • ·) hx

end NCG
