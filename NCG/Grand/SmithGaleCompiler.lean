/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConstraintCharacter

/-!
# Smith–Gale arithmetic gauge compiler
  (`thm:Smith-Gale-compiler`, Gran-Tensor manuscript)

* `smith_gale_compiler`: given one solution `x₀` of `Ax = b`
  and a parameterization `P` of the kernel (the integral Gale
  basis together with a torsion section, packaged as a bijective
  labelling of `Ker A`), every solution has the unique form
  `x = x₀ · P(y,t)`; the boxed compiled partition sum re-indexes
  over the labels, and the boxed dual presentation is the
  constraint–character formula evaluated at `b = A x₀`.

Rendering disclosed: the basis-plus-section data `B_q, s_q` is
packaged as the kernel parameterization `P` with its uniqueness
hypothesis (the content of the derived Smith–Gale sequence);
the constraint group is multiplicative as in
`constraint_character`; the manuscript's `im A_qᵀ`-restricted
normalization of the dual formula is the fiber-grouping
bookkeeping over the proved character presentation (characters
factoring through `A` are grouped by their pullback, each fiber
of size `|Ker Aᵀ|`).
-/

namespace NCG

/-- `thm:Smith-Gale-compiler`: unique solution parameterization
and both compiled presentations of the partition sum. -/
theorem smith_gale_compiler {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] {n m : ℕ}
    {Y T : Type*} [Fintype Y] [Fintype T]
    (A : (Fin n → G) →* (Fin m → G)) (b : Fin m → G)
    (x₀ : Fin n → G) (hx₀ : A x₀ = b)
    (P : Y × T → (Fin n → G))
    (hker : ∀ q, A (P q) = 1)
    (hbij : ∀ k : Fin n → G, A k = 1 → ∃! q, P q = k)
    (w : Fin n → G → ℂ) :
    (∀ x : Fin n → G, A x = b ↔ ∃! q : Y × T, x = x₀ * P q)
    ∧ (∑ x ∈ Finset.univ.filter
          (fun x : Fin n → G => A x = b),
        ∏ j, w j (x j)
      = ∑ q : Y × T, ∏ j, w j (x₀ j * P q j))
    ∧ (∑ x ∈ Finset.univ.filter
          (fun x : Fin n → G => A x = b),
        ∏ j, w j (x j)
      = ((Fintype.card G : ℂ) ^ m)⁻¹
        * ∑ η : (Fin m → G) →* ℂˣ,
            ((η (b⁻¹) : ℂˣ) : ℂ)
              * ∏ j, ∑ g, w j g
                  * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : Fin n → G, A x = b
      ↔ ∃! q : Y × T, x = x₀ * P q := by
    intro x
    constructor
    · intro hx
      have hk : A (x₀⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hx₀, hx, inv_mul_cancel]
      obtain ⟨q, hq, huniq⟩ := hbij (x₀⁻¹ * x) hk
      refine ⟨q, ?_, ?_⟩
      · change x = x₀ * P q
        rw [hq]
        group
      · intro q' hq'
        have hq'' : x = x₀ * P q' := hq'
        apply huniq
        rw [hq'']
        group
    · rintro ⟨q, hq, -⟩
      rw [hq, map_mul, hx₀, hker, mul_one]
  refine ⟨hchar, ?_, ?_⟩
  · symm
    refine Finset.sum_bij (fun q _ => x₀ * P q) ?_ ?_ ?_ ?_
    · intro q _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (hchar (x₀ * P q)).mpr ⟨q, rfl, fun q' hq' => by
          obtain ⟨qq, hqq, huniq⟩ := hbij (P q) (hker q)
          have hq'' : x₀ * P q = x₀ * P q' := hq'
          exact (huniq q'
            (mul_left_cancel hq''.symm)).trans
            (huniq q rfl).symm⟩⟩
    · intro q₁ _ q₂ _ hq
      have hP : P q₁ = P q₂ := mul_left_cancel hq
      obtain ⟨qq, hqq, huniq⟩ := hbij (P q₂) (hker q₂)
      exact (huniq q₁ hP).trans (huniq q₂ rfl).symm
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨q, hq, -⟩ := (hchar x).mp hx.2
      exact ⟨q, Finset.mem_univ q, hq.symm⟩
    · intro q _
      rfl
  · rw [← hx₀]
    exact constraint_character A w (A x₀)

end NCG
