/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Minimality of successor refinement

Proposition `prop:successor-refinement` of `manuscripts/renewal_emergence/renewal_emergence.tex`.

The successor refinement of `constr:successor-refinement` redirects
each resolved branch to the class of its **conditional future
profile** (`profile : B → P`, the normalized-output profile in a
reduced future-tomographic realization, where equal profiles mean
equal reference target states by `thm:predictive-reference-renewal`).
We prove:

* `succMk_eq_iff` — two branches receive the same refined target
  exactly when their conditional profiles agree, so the refined graph
  is reference renewing (`succProfile` is the well-defined common
  profile of a refined vertex, `succProfile_mk`);
* `succClass_factors` — **coarseness/minimality**: for every
  relabelling `r` whose classes are reference renewing (constant
  conditional profile), the successor quotient factors uniquely
  through `r`; hence the successor refinement is the coarsest
  reference-renewing relabelling;
* `succClass_finite` — the refinement is finite whenever the
  reachable conditional predictive rank is finite.
-/

namespace NCG.Upstream.Successor

variable {B P : Type*} (profile : B → P)

/-- The successor-refinement setoid: branches are identified exactly
when their conditional future profiles agree. -/
def succSetoid : Setoid B := Setoid.ker profile

/-- The refined target vertices. -/
def SuccClass : Type _ := Quotient (succSetoid profile)

/-- The refinement map: a branch is redirected to its own class. -/
def succMk (b : B) : SuccClass profile :=
  Quotient.mk (succSetoid profile) b

/-- **Reference renewal of the refined graph**: the conditional
profile descends to the refined vertices. -/
def succProfile : SuccClass profile → P :=
  Quotient.lift profile (fun _ _ h => h)

@[simp] theorem succProfile_mk (b : B) :
    succProfile profile (succMk profile b) = profile b := rfl

/-- Two branches are redirected to the same refined vertex iff their
conditional future profiles agree. -/
theorem succMk_eq_iff (b b' : B) :
    succMk profile b = succMk profile b' ↔ profile b = profile b' := by
  constructor
  · intro h
    have h1 := congrArg (succProfile profile) h
    simpa using h1
  · intro h
    exact Quotient.sound h

/-- **Proposition `prop:successor-refinement` (coarseness)**: every
relabelling `r` for which each class is reference renewing (constant
conditional profile) factors the successor quotient uniquely through
itself — the successor refinement is the coarsest reference-renewing
relabelling of the resolved branches. -/
theorem succClass_factors {Y : Type*} (r : B → Y)
    (hr : ∀ b b', r b = r b' → profile b = profile b') :
    ∃! h : Set.range r → SuccClass profile,
      ∀ b, h ⟨r b, Set.mem_range_self b⟩ = succMk profile b := by
  classical
  refine ⟨fun y => succMk profile y.2.choose, ?_, ?_⟩
  · intro b
    have h1 : r (Set.mem_range_self (f := r) b).choose = r b :=
      (Set.mem_range_self (f := r) b).choose_spec
    exact (succMk_eq_iff profile _ _).mpr (hr _ _ h1)
  · intro h' hh'
    funext y
    obtain ⟨y, hy⟩ := y
    have h2 : y = r hy.choose := hy.choose_spec.symm
    have h3 : (⟨y, hy⟩ : Set.range r)
        = ⟨r hy.choose, Set.mem_range_self _⟩ :=
      Subtype.ext h2
    rw [h3, hh' hy.choose]
    have h4 : r ((Set.mem_range_self (f := r) hy.choose).choose)
        = r hy.choose :=
      (Set.mem_range_self (f := r) hy.choose).choose_spec
    exact ((succMk_eq_iff profile _ _).mpr (hr _ _ h4)).symm

/-- The descended profile separates refined vertices. -/
theorem succProfile_injective :
    Function.Injective (succProfile profile) := by
  intro x y
  induction x using Quotient.ind with | _ b =>
  induction y using Quotient.ind with | _ b' =>
  intro h
  exact Quotient.sound (h : profile b = profile b')

/-- **Proposition `prop:successor-refinement` (finiteness)**: the
refinement is finite whenever the conditional predictive rank is. -/
theorem succClass_finite [Finite P] : Finite (SuccClass profile) :=
  Finite.of_injective _ (succProfile_injective profile)

end NCG.Upstream.Successor
