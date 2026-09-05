/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The physical dark-parity fork over `𝔽₂`
  (`thm:v5-physical-dark-criterion`, `thm:v5-odd-character-coset`,
   `thm:v5-reduced-determinant`, SM_emergence)

For the deck group `D_phys` (an elementary `2`-group, i.e. a
finite-dimensional `𝔽₂` space `V`), the charged character span
`S_ch ⊆ V*`, and its kernel `K_ch = S_ch^⊥ ⊆ V`:

* `f2_fiber_card` — a nonzero `𝔽₂` functional on a
  `d`-dimensional space has exactly `2^{d-1}` odd points;
* `dark_parity_criterion` — `n` admits a physical dark parity iff
  `n ∉ S_ch` iff some `x ∈ K_ch` has `n(x) = 1`
  (double-annihilator duality with a dimension count);
* `dark_parity_count` — for `n ∉ S_ch` the number of such parities
  is `2^{b-r-1}`, `b = dim D_phys`, `r = dim S_ch`;
* `odd_character_coset` / `odd_character_card` — the odd
  characters of a fixed `x ≠ 0` form the coset `n₀ + x^⊥`, of
  cardinality `2^{b-1}` (`= 4` at `b = 3`);
* `reduced_determinant_fork` — at `b = 3`:
  `|K_ch| = 2 ↔ dim S_ch = 2` and `|K_ch| = 1 ↔ dim S_ch = 3`.

The τ-labelled coset refinement (triangle versus edge classes) and
the identification of the reduced determinant `d_det` with the
fork are the declared model layer.
-/

namespace NCG

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A nonzero `𝔽₂` functional on a `d`-dimensional space has
exactly `2^{d-1}` odd points. -/
theorem f2_fiber_card {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (phi : W →ₗ[ZMod 2] ZMod 2) (w0 : W) (hw0 : phi w0 = 1) :
    Nat.card {w : W // phi w = 1}
      = 2 ^ (Module.finrank (ZMod 2) W - 1) := by
  classical
  have hbij : {w : W // phi w = 1} ≃ LinearMap.ker phi :=
    { toFun := fun w => ⟨w.val - w0, by
        rw [LinearMap.mem_ker, map_sub, w.property, hw0, sub_self]⟩
      invFun := fun w => ⟨w.val + w0, by
        rw [map_add, LinearMap.mem_ker.mp w.property, hw0,
          zero_add]⟩
      left_inv := fun w => by simp
      right_inv := fun w => by simp }
  rw [Nat.card_congr hbij, Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have hrange : LinearMap.range phi = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with hc | hc
    · exact ⟨0, by rw [map_zero, hc]⟩
    · exact ⟨w0, by rw [hw0, hc]⟩
  have hrk : Module.finrank (ZMod 2) (LinearMap.range phi) = 1 := by
    rw [hrange]
    simp
  have hnull := LinearMap.finrank_range_add_finrank_ker phi
  rw [hrk] at hnull
  rw [Nat.card_zmod]
  congr 1
  omega

/-- The double annihilator of the charged span: in finite
dimension, `(S^⊥)^⊥ = S`. -/
theorem charged_span_double_annihilator
    (S : Subspace (ZMod 2) (Module.Dual (ZMod 2) V)) :
    (S.dualCoannihilator).dualAnnihilator = S := by
  have hle : S ≤ (S.dualCoannihilator).dualAnnihilator :=
    Submodule.le_dualAnnihilator_iff_le_dualCoannihilator.mpr le_rfl
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (S.dualCoannihilator)
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

/-- `thm:v5-physical-dark-criterion` (criterion): a character `n`
admits a physical dark parity iff `n ∉ S_ch`, iff some
`x ∈ K_ch = S_ch^⊥` has `n(x) = 1`. -/
theorem dark_parity_criterion
    (S : Subspace (ZMod 2) (Module.Dual (ZMod 2) V))
    (n : Module.Dual (ZMod 2) V) :
    n ∉ S ↔ ∃ x ∈ S.dualCoannihilator, n x = 1 := by
  constructor
  · intro hn
    rw [← charged_span_double_annihilator S,
      Submodule.mem_dualAnnihilator] at hn
    push Not at hn
    obtain ⟨x, hx, hne⟩ := hn
    refine ⟨x, hx, ?_⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (n x)
      with hc | hc
    · exact absurd hc hne
    · exact hc
  · rintro ⟨x, hx, hone⟩
    rw [← charged_span_double_annihilator S,
      Submodule.mem_dualAnnihilator]
    push Not
    exact ⟨x, hx, by rw [hone]; decide⟩

/-- `thm:v5-physical-dark-criterion` (count): for `n ∉ S_ch` the
number of dark parities is `2^{b-r-1}`. -/
theorem dark_parity_count
    (S : Subspace (ZMod 2) (Module.Dual (ZMod 2) V))
    (n : Module.Dual (ZMod 2) V) (hn : n ∉ S) :
    Nat.card {x : V // x ∈ S.dualCoannihilator ∧ n x = 1}
      = 2 ^ (Module.finrank (ZMod 2) V
        - Module.finrank (ZMod 2) S - 1) := by
  classical
  obtain ⟨x0, hx0K, hx0⟩ := (dark_parity_criterion S n).mp hn
  have hbij : {x : V // x ∈ S.dualCoannihilator ∧ n x = 1}
      ≃ {y : S.dualCoannihilator //
          (n.comp (S.dualCoannihilator).subtype) y = 1} :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun y => ⟨y.val.val, y.val.property, y.property⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr hbij,
    f2_fiber_card (n.comp (S.dualCoannihilator).subtype)
      ⟨x0, hx0K⟩ hx0]
  congr 1
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- `thm:v5-odd-character-coset` (coset structure): the odd
characters of `x` form the coset `n₀ + x^⊥`. -/
theorem odd_character_coset (x : V)
    (n0 : Module.Dual (ZMod 2) V) (h0 : n0 x = 1) :
    {n : Module.Dual (ZMod 2) V | n x = 1}
      = (fun m => n0 + m) '' {m : Module.Dual (ZMod 2) V |
          m x = 0} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hn
    refine ⟨n - n0, ?_, by abel⟩
    simp only [LinearMap.sub_apply, hn, h0, sub_self]
  · rintro ⟨m, hm, rfl⟩
    simp only [LinearMap.add_apply, h0, hm, add_zero]

/-- `thm:v5-odd-character-coset` (count): the odd characters of a
nonzero `x` number `2^{b-1}` — four for `b = 3`. -/
theorem odd_character_card (x : V) (hx : x ≠ 0) :
    Nat.card {n : Module.Dual (ZMod 2) V // n x = 1}
      = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  classical
  obtain ⟨n0, hn0⟩ : ∃ n : Module.Dual (ZMod 2) V, n x = 1 := by
    have hev : (Module.Dual.eval (ZMod 2) V) x ≠ 0 := by
      intro hzero
      exact hx ((Module.evalEquiv (ZMod 2) V).map_eq_zero_iff.mp
        (by exact hzero))
    obtain ⟨n, hn⟩ : ∃ n, (Module.Dual.eval (ZMod 2) V) x n ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hev (LinearMap.ext hall)
    refine ⟨n, ?_⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1)
      ((Module.Dual.eval (ZMod 2) V) x n) with hc | hc
    · exact absurd hc hn
    · exact hc
  have h := f2_fiber_card (Module.Dual.eval (ZMod 2) V x) n0 hn0
  rw [Subspace.dual_finrank_eq] at h
  exact h

/-- `thm:v5-reduced-determinant` (𝔽₂ fork): at `b = 3`, the kernel
has two elements iff the charged span is a plane, and is trivial
iff the charged span is everything. -/
theorem reduced_determinant_fork
    (S : Subspace (ZMod 2) (Module.Dual (ZMod 2) V))
    (hb : Module.finrank (ZMod 2) V = 3) :
    (Nat.card S.dualCoannihilator = 2
        ↔ Module.finrank (ZMod 2) S = 2)
      ∧ (Nat.card S.dualCoannihilator = 1
        ↔ Module.finrank (ZMod 2) S = 3) := by
  have hcard : Nat.card S.dualCoannihilator
      = 2 ^ Module.finrank (ZMod 2) S.dualCoannihilator := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  have hSle : Module.finrank (ZMod 2) S ≤ 3 := by
    have := Subspace.dual_finrank_eq (K := ZMod 2) (V := V)
    have hle := Submodule.finrank_le S
    omega
  constructor
  · rw [hcard]
    constructor
    · intro h
      have : Module.finrank (ZMod 2) S.dualCoannihilator = 1 := by
        rcases Nat.lt_or_ge
          (Module.finrank (ZMod 2) S.dualCoannihilator) 2 with hlt | hge
        · interval_cases (Module.finrank (ZMod 2) S.dualCoannihilator)
          · simp at h
          · rfl
        · exfalso
          have : (2:ℕ) ^ 2 ≤ 2 ^ Module.finrank (ZMod 2)
              S.dualCoannihilator :=
            Nat.pow_le_pow_right (by norm_num) hge
          omega
      omega
    · intro h
      have : Module.finrank (ZMod 2) S.dualCoannihilator = 1 := by
        omega
      rw [this]
      norm_num
  · rw [hcard]
    constructor
    · intro h
      have : Module.finrank (ZMod 2) S.dualCoannihilator = 0 := by
        by_contra hne
        have h1 : 1 ≤ Module.finrank (ZMod 2)
            S.dualCoannihilator := by omega
        have : (2:ℕ) ^ 1 ≤ 2 ^ Module.finrank (ZMod 2)
            S.dualCoannihilator :=
          Nat.pow_le_pow_right (by norm_num) h1
        omega
      omega
    · intro h
      have : Module.finrank (ZMod 2) S.dualCoannihilator = 0 := by
        omega
      rw [this]
      norm_num

end NCG
