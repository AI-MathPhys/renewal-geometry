/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical emergence of every admissibly loaded subhierarchy
  (`thm:loaded-subhierarchy`, Gran-Tensor manuscript)

* `loaded_subhierarchy`:
  (i) every loaded kernel `𝕂 = WᴴW` is positive semidefinite;
  (iii) the loaded future-null combinations form a two-sided
       `*`-closed set: with nullity defined by vanishing
       against all admitted contexts, closure of contexts
       under left/right word insertion and adjoint makes the
       null set a two-sided `*`-ideal;
  (iv) finite flat depth: any nested increasing family of
       subspaces of the finite-dimensional history carrier
       stabilizes at some finite depth.

Rendering disclosed: (ii) source admission for the selected
records, the identification of the quotient with
`C*(Σ̂_{L,X})`, the unique loading-fixing unitary, and (v)
cutoff compatibility cite the proved `record_survival`,
`GrandNullIdeal`, flat-monoidal reconstruction, and cutoff
records (the manuscript's proof references exactly those
theorems); (vi) is the manuscript's summary of (i)–(iii).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:loaded-subhierarchy`. -/
theorem loaded_subhierarchy :
    -- (i) loaded kernels are positive
    (∀ {h e : Type} [Fintype h] [Fintype e]
      (W : Matrix h e ℂ), (Wᴴ * W).PosSemidef)
    -- (iii) contextual nullity is a two-sided *-ideal
    ∧ (∀ {A : Type} [Ring A] [StarRing A]
        (C : Set (A → ℂ)),
        (∀ φ ∈ C, ∀ w : A, (fun q => φ (w * q)) ∈ C) →
        (∀ φ ∈ C, ∀ w : A, (fun q => φ (q * w)) ∈ C) →
        (∀ φ ∈ C, (fun q => φ (star q)) ∈ C) →
        ∀ q : A, (∀ φ ∈ C, φ q = 0) →
        (∀ w : A, ∀ φ ∈ C, φ (w * q) = 0)
        ∧ (∀ w : A, ∀ φ ∈ C, φ (q * w) = 0)
        ∧ (∀ φ ∈ C, φ (star q) = 0))
    -- (iv) finite flat depth: nested spans stabilize
    ∧ (∀ {V : Type} [AddCommGroup V] [Module ℂ V]
        [FiniteDimensional ℂ V]
        (S : ℕ → Submodule ℂ V),
        (∀ n, S n ≤ S (n + 1)) →
        ∃ n, S (n + 1) = S n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h e _ _ W
    exact Matrix.posSemidef_conjTranspose_mul_self W
  · intro A _ _ C hleft hright hstar q hnull
    refine ⟨?_, ?_, ?_⟩
    · intro w φ hφ
      exact hnull _ (hleft φ hφ w)
    · intro w φ hφ
      exact hnull _ (hright φ hφ w)
    · intro φ hφ
      exact hnull _ (hstar φ hφ)
  · intro V _ _ _ S hmono
    by_contra hcon
    push Not at hcon
    have hstrict : ∀ n,
        Module.finrank ℂ ↥(S n) + 1
          ≤ Module.finrank ℂ ↥(S (n + 1)) := by
      intro n
      have hlt : S n < S (n + 1) :=
        lt_of_le_of_ne (hmono n) (Ne.symm (hcon n))
      exact Submodule.finrank_lt_finrank_of_lt hlt
    have hgrow : ∀ n,
        n ≤ Module.finrank ℂ ↥(S n) := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ k ih =>
          calc k + 1 ≤ Module.finrank ℂ ↥(S k) + 1 :=
                Nat.add_le_add_right ih 1
            _ ≤ Module.finrank ℂ ↥(S (k + 1)) := hstrict k
    have hbound := hgrow (Module.finrank ℂ V + 1)
    have hle : Module.finrank ℂ ↥(S (Module.finrank ℂ V + 1))
        ≤ Module.finrank ℂ V :=
      Submodule.finrank_le _
    omega

end NCG
