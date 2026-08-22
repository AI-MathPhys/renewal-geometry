/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BoundedWriterComparison

/-!
# Target sandwich: the sharp positive-extension interval

Completes `thm:GT-target-sandwich` (and hence
`thm:arithmetic-order-interval`) on top of
`BoundedWriterComparison.target_sandwich`:

for a finite unital real writer system `S` on a finite event space
`Ω` and an order-positive functional `Φ` on `S`, among all positive
extensions of `Φ` to `C(Ω) = (Ω → ℝ)` the compatible interval for a
writer `w` is

`J_low(w) = sup {Φ f : f ∈ S, f ≤ w}`,
`J_high(w) = inf {Φ g : g ∈ S, g ≥ w}`,

* `extension_value_mem_interval`: every positive extension lies in
  `[J_low, J_high]` (weak duality);
* `exists_extension_attaining_low` / `exists_extension_attaining_high`:
  both endpoints are **attained** by positive extensions — proved by
  M. Riesz's extension theorem applied to the cone of nonnegative
  writers and the partial functional `Φ ⊕ (w ↦ J_low)`;
* `identified_iff_interval_collapses`: the target is identified by all
  positive extensions exactly when the two endpoints coincide.

Positive extensions are linear functionals on `Ω → ℝ` nonnegative on
nonnegative writers and agreeing with `Φ` on `S`; on a finite event
space these are exactly the positive measures extending `Φ`
(`extension_eq_measure`).
-/

open Finset

-- finiteness is used only inside proofs (extremal constants)
set_option linter.unusedFintypeInType false

namespace NCG
namespace BoundedWriterComparison

variable {Ω : Type*} [Fintype Ω]

/-- The cone of nonnegative writers. -/
abbrev nonnegCone (Ω : Type*) : PointedCone ℝ (Ω → ℝ) :=
  PointedCone.positive ℝ (Ω → ℝ)

/-- A positive extension of `Φ : S → ℝ` to all writers. -/
structure IsPositiveExtension (S : Submodule ℝ (Ω → ℝ))
    (Φ : S →ₗ[ℝ] ℝ) (g : (Ω → ℝ) →ₗ[ℝ] ℝ) : Prop where
  agrees : ∀ f : S, g f = Φ f
  nonneg : ∀ f : Ω → ℝ, 0 ≤ f → 0 ≤ g f

/-- Lower endpoint `sup {Φ f : f ∈ S, f ≤ w}`. -/
noncomputable def lowEnd (S : Submodule ℝ (Ω → ℝ)) (Φ : S →ₗ[ℝ] ℝ)
    (w : Ω → ℝ) : ℝ :=
  sSup (Set.range fun f : {f : S // (f : Ω → ℝ) ≤ w} => Φ f.1)

/-- Upper endpoint `inf {Φ g : g ∈ S, g ≥ w}`. -/
noncomputable def highEnd (S : Submodule ℝ (Ω → ℝ)) (Φ : S →ₗ[ℝ] ℝ)
    (w : Ω → ℝ) : ℝ :=
  sInf (Set.range fun g : {g : S // w ≤ (g : Ω → ℝ)} => Φ g.1)

/-- Order positivity: `f ≤ g` in `S` implies `Φ f ≤ Φ g`. -/
def OrderPositive (S : Submodule ℝ (Ω → ℝ)) (Φ : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ f : S, 0 ≤ (f : Ω → ℝ) → 0 ≤ Φ f

omit [Fintype Ω] in
theorem OrderPositive.mono {S : Submodule ℝ (Ω → ℝ)} {Φ : S →ₗ[ℝ] ℝ}
    (hΦ : OrderPositive S Φ) {f g : S} (h : (f : Ω → ℝ) ≤ (g : Ω → ℝ)) :
    Φ f ≤ Φ g := by
  have := hΦ (g - f) (by
    intro ω
    simp only [Submodule.coe_sub, Pi.sub_apply, Pi.zero_apply]
    linarith [h ω])
  rw [map_sub] at this
  linarith

/-- The constant writers. -/
def constWriter (c : ℝ) : Ω → ℝ := fun _ => c

section Unital

variable (S : Submodule ℝ (Ω → ℝ)) (Φ : S →ₗ[ℝ] ℝ)
  (hunit : constWriter (1 : ℝ) ∈ S) (hΦ : OrderPositive S Φ)
  (w : Ω → ℝ) [Nonempty Ω]

/-- The constant `c` as an element of a unital writer system. -/
def constS (c : ℝ) : S := ⟨c • constWriter 1, S.smul_mem c hunit⟩

omit [Fintype Ω] [Nonempty Ω] in
theorem constS_coe (c : ℝ) : ((constS S hunit c : S) : Ω → ℝ) = fun _ => c := by
  funext ω
  simp [constS, constWriter]

include hunit in
/-- Minorants exist: the constant `min w`. -/
theorem exists_minorant :
    ∃ f : S, (f : Ω → ℝ) ≤ w := by
  refine ⟨constS S hunit (Finset.univ.inf' Finset.univ_nonempty w), ?_⟩
  intro ω
  rw [constS_coe]
  exact Finset.inf'_le _ (Finset.mem_univ ω)

include hunit in
theorem exists_majorant :
    ∃ g : S, w ≤ (g : Ω → ℝ) := by
  refine ⟨constS S hunit (Finset.univ.sup' Finset.univ_nonempty w), ?_⟩
  intro ω
  rw [constS_coe]
  exact Finset.le_sup' _ (Finset.mem_univ ω)

omit [Fintype Ω] [Nonempty Ω] in
include hΦ in
/-- Every minorant value is below every majorant value. -/
theorem minorant_le_majorant (f g : S) (hf : (f : Ω → ℝ) ≤ w)
    (hg : w ≤ (g : Ω → ℝ)) : Φ f ≤ Φ g :=
  hΦ.mono (le_trans hf hg)

include hunit hΦ in
theorem lowEnd_bddAbove :
    BddAbove (Set.range fun f : {f : S // (f : Ω → ℝ) ≤ w} => Φ f.1) := by
  obtain ⟨g, hg⟩ := exists_majorant S hunit w
  refine ⟨Φ g, ?_⟩
  rintro _ ⟨f, rfl⟩
  exact minorant_le_majorant S Φ hΦ w f.1 g f.2 hg

include hunit hΦ in
theorem highEnd_bddBelow :
    BddBelow (Set.range fun g : {g : S // w ≤ (g : Ω → ℝ)} => Φ g.1) := by
  obtain ⟨f, hf⟩ := exists_minorant S hunit w
  refine ⟨Φ f, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact minorant_le_majorant S Φ hΦ w f g.1 hf g.2

include hunit hΦ in
theorem le_lowEnd (f : S) (hf : (f : Ω → ℝ) ≤ w) : Φ f ≤ lowEnd S Φ w :=
  le_csSup (lowEnd_bddAbove S Φ hunit hΦ w) ⟨⟨f, hf⟩, rfl⟩

include hunit hΦ in
theorem highEnd_le (g : S) (hg : w ≤ (g : Ω → ℝ)) : highEnd S Φ w ≤ Φ g :=
  csInf_le (highEnd_bddBelow S Φ hunit hΦ w) ⟨⟨g, hg⟩, rfl⟩

include hunit hΦ in
theorem lowEnd_le_of_majorant (g : S) (hg : w ≤ (g : Ω → ℝ)) :
    lowEnd S Φ w ≤ Φ g := by
  obtain ⟨f₀, hf₀⟩ := exists_minorant S hunit w
  refine csSup_le ⟨Φ f₀, ⟨⟨f₀, hf₀⟩, rfl⟩⟩ ?_
  rintro _ ⟨f, rfl⟩
  exact minorant_le_majorant S Φ hΦ w f.1 g f.2 hg

include hunit hΦ in
theorem lowEnd_le_highEnd : lowEnd S Φ w ≤ highEnd S Φ w := by
  obtain ⟨g₀, hg₀⟩ := exists_majorant S hunit w
  refine le_csInf ⟨Φ g₀, ⟨⟨g₀, hg₀⟩, rfl⟩⟩ ?_
  rintro _ ⟨g, rfl⟩
  exact lowEnd_le_of_majorant S Φ hunit hΦ w g.1 g.2

/-! ### Weak duality -/

include hunit in
/-- **Weak duality**: every positive extension evaluates `w` inside the
interval `[J_low, J_high]`. -/
theorem extension_value_mem_interval (g : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hg : IsPositiveExtension S Φ g) :
    lowEnd S Φ w ≤ g w ∧ g w ≤ highEnd S Φ w := by
  constructor
  · obtain ⟨f₀, hf₀⟩ := exists_minorant S hunit w
    refine csSup_le ⟨Φ f₀, ⟨⟨f₀, hf₀⟩, rfl⟩⟩ ?_
    rintro _ ⟨f, rfl⟩
    have := hg.nonneg (w - f.1) (by
      intro ω
      simp only [Pi.sub_apply, Pi.zero_apply]
      linarith [f.2 ω])
    rw [map_sub, hg.agrees] at this
    linarith
  · obtain ⟨g₀, hg₀⟩ := exists_majorant S hunit w
    refine le_csInf ⟨Φ g₀, ⟨⟨g₀, hg₀⟩, rfl⟩⟩ ?_
    rintro _ ⟨h, rfl⟩
    have := hg.nonneg (h.1 - w) (by
      intro ω
      simp only [Pi.sub_apply, Pi.zero_apply]
      linarith [h.2 ω])
    rw [map_sub, hg.agrees] at this
    linarith

/-! ### Attainment by Riesz extension -/

include hunit hΦ in
/-- **Sharpness (lower endpoint)**: some positive extension attains
`J_low(w)`.  Proof by M. Riesz's extension theorem on the cone of
nonnegative writers. -/
theorem exists_extension_attaining_low :
    ∃ g : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g ∧ g w = lowEnd S Φ w := by
  classical
  by_cases hw : w ∈ S
  · -- `w` is itself a writer: the interval is `{Φ w}`
    have hlow : lowEnd S Φ w = Φ ⟨w, hw⟩ := by
      apply le_antisymm
      · exact lowEnd_le_of_majorant S Φ hunit hΦ w ⟨w, hw⟩ le_rfl
      · exact le_lowEnd S Φ hunit hΦ w ⟨w, hw⟩ le_rfl
    obtain ⟨g, hgS, hgpos⟩ := riesz_extension (nonnegCone Ω)
      (⟨S, Φ⟩ : (Ω → ℝ) →ₗ.[ℝ] ℝ)
      (fun x hx => hΦ x hx)
      (fun y => ⟨⟨(Finset.univ.sum fun ω => |y ω|) • constWriter 1,
        S.smul_mem _ hunit⟩, by
          intro ω
          simp only [Pi.add_apply, Pi.smul_apply, constWriter, smul_eq_mul,
            mul_one, Pi.zero_apply]
          have : |y ω| ≤ Finset.univ.sum fun ω' => |y ω'| :=
            Finset.single_le_sum (fun ω' _ => abs_nonneg (y ω'))
              (Finset.mem_univ ω)
          linarith [neg_abs_le (y ω)]⟩)
    refine ⟨g, ⟨fun f => hgS f, fun f hf => hgpos f hf⟩, ?_⟩
    rw [hlow]
    exact hgS ⟨w, hw⟩
  · -- extend `Φ` by `w ↦ J_low` and apply Riesz
    set J := lowEnd S Φ w with hJ
    let f' : (Ω → ℝ) →ₗ.[ℝ] ℝ := (⟨S, Φ⟩ : (Ω → ℝ) →ₗ.[ℝ] ℝ).supSpanSingleton w J hw
    have hdom : f'.domain = S ⊔ Submodule.span ℝ {w} :=
      LinearPMap.domain_supSpanSingleton _ w J hw
    have hnonneg : ∀ x : f'.domain, (x : Ω → ℝ) ∈ nonnegCone Ω → 0 ≤ f' x := by
      rintro ⟨x, hx⟩ hxpos
      have hx' := hx
      rw [hdom, Submodule.mem_sup] at hx'
      obtain ⟨s, hs, z, hz, rfl⟩ := hx'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hval : f' ⟨s + c • w, hx⟩ = Φ ⟨s, hs⟩ + c * J := by
        simp only [f']
        rw [LinearPMap.supSpanSingleton_apply_mk (hx' := hs)]
        simp
      rw [hval]
      have hpos : ∀ ω, 0 ≤ s ω + c * w ω := fun ω => by
        have := hxpos ω
        simpa using this
      rcases lt_trichotomy c 0 with hc | hc | hc
      · -- `c < 0`: `w ≤ -s/c`, so `J ≤ Φ(-s/c)`
        have hmaj : w ≤ ((((-c)⁻¹ : ℝ) • ⟨s, hs⟩ : S) : Ω → ℝ) := by
          intro ω
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          have hcneg : 0 < -c := by linarith
          rw [le_inv_mul_iff₀ hcneg]
          linarith [hpos ω]
        have := lowEnd_le_of_majorant S Φ hunit hΦ w _ hmaj
        rw [map_smul, smul_eq_mul] at this
        have hcne : c ≠ 0 := ne_of_lt hc
        have : c * J ≥ c * ((-c)⁻¹ * Φ ⟨s, hs⟩) :=
          mul_le_mul_of_nonpos_left this hc.le
        have h2 : c * ((-c)⁻¹ * Φ ⟨s, hs⟩) = -Φ ⟨s, hs⟩ := by
          field_simp
        linarith
      · subst hc
        simp only [zero_mul, add_zero]
        exact hΦ ⟨s, hs⟩ (fun ω => by simpa using hpos ω)
      · -- `c > 0`: `-s/c ≤ w`, so `Φ(-s/c) ≤ J`
        have hmin : ((((-c⁻¹ : ℝ)) • ⟨s, hs⟩ : S) : Ω → ℝ) ≤ w := by
          intro ω
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
          have : -c⁻¹ * s ω = -(s ω / c) := by ring
          rw [this, neg_le_iff_add_nonneg]
          have key : w ω + s ω / c = (s ω + c * w ω) / c := by
            rw [eq_div_iff (ne_of_gt hc), add_mul, div_mul_cancel₀ _ (ne_of_gt hc)]
            ring
          rw [key]
          exact div_nonneg (hpos ω) hc.le
        have := le_lowEnd S Φ hunit hΦ w _ hmin
        rw [map_smul, smul_eq_mul] at this
        have : c * (-c⁻¹ * Φ ⟨s, hs⟩) ≤ c * J :=
          mul_le_mul_of_nonneg_left this hc.le
        have h2 : c * (-c⁻¹ * Φ ⟨s, hs⟩) = -Φ ⟨s, hs⟩ := by
          field_simp
        linarith
    have hdense : ∀ y, ∃ x : f'.domain, (x : Ω → ℝ) + y ∈ nonnegCone Ω := by
      intro y
      refine ⟨⟨(Finset.univ.sum fun ω => |y ω|) • constWriter 1, ?_⟩, ?_⟩
      · rw [hdom]
        exact Submodule.mem_sup_left (S.smul_mem _ hunit)
      · intro ω
        simp only [Pi.add_apply, Pi.smul_apply, constWriter, smul_eq_mul,
          mul_one, Pi.zero_apply]
        have : |y ω| ≤ Finset.univ.sum fun ω' => |y ω'| :=
          Finset.single_le_sum (fun ω' _ => abs_nonneg (y ω'))
            (Finset.mem_univ ω)
        linarith [neg_abs_le (y ω)]
    obtain ⟨g, hgf, hgpos⟩ := riesz_extension (nonnegCone Ω) f' hnonneg hdense
    refine ⟨g, ⟨fun f => ?_, fun f hf => hgpos f hf⟩, ?_⟩
    · have := hgf ⟨f, by
        rw [hdom]
        exact Submodule.mem_sup_left f.2⟩
      rw [this]
      simp only [f']
      rw [LinearPMap.supSpanSingleton_apply_mk_of_mem]
      rfl
    · have := hgf ⟨w, by
        rw [hdom]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)⟩
      rw [this]
      simp only [f']
      rw [LinearPMap.supSpanSingleton_apply_self]

include hunit hΦ in
/-- `J_high(w) = -J_low(-w)`. -/
theorem highEnd_eq_neg_lowEnd_neg :
    highEnd S Φ w = -lowEnd S Φ (-w) := by
  apply le_antisymm
  · rw [le_neg]
    obtain ⟨f₀, hf₀⟩ := exists_minorant S hunit (-w)
    refine csSup_le ⟨Φ f₀, ⟨⟨f₀, hf₀⟩, rfl⟩⟩ ?_
    rintro _ ⟨f, rfl⟩
    have hmaj : w ≤ ((-f.1 : S) : Ω → ℝ) := by
      intro ω
      have := f.2 ω
      simp only [Submodule.coe_neg, Pi.neg_apply] at this ⊢
      linarith
    have := highEnd_le S Φ hunit hΦ w (-f.1) hmaj
    rw [map_neg] at this
    linarith
  · obtain ⟨g₀, hg₀⟩ := exists_majorant S hunit w
    refine le_csInf ⟨Φ g₀, ⟨⟨g₀, hg₀⟩, rfl⟩⟩ ?_
    rintro _ ⟨g, rfl⟩
    have hmin : ((-g.1 : S) : Ω → ℝ) ≤ -w := by
      intro ω
      have := g.2 ω
      simp only [Submodule.coe_neg, Pi.neg_apply]
      linarith
    have := le_lowEnd S Φ hunit hΦ (-w) (-g.1) hmin
    rw [map_neg] at this
    linarith

include hunit hΦ in
/-- **Sharpness (upper endpoint)**: some positive extension attains
`J_high(w)`. -/
theorem exists_extension_attaining_high :
    ∃ g : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g ∧ g w = highEnd S Φ w := by
  obtain ⟨g, hg, hgw⟩ := exists_extension_attaining_low S Φ hunit hΦ (-w)
  refine ⟨g, hg, ?_⟩
  rw [highEnd_eq_neg_lowEnd_neg S Φ hunit hΦ w, ← hgw, map_neg, neg_neg]

include hunit hΦ in
/-- **Identification criterion**: the target `w` has one value under all
positive extensions exactly when the sharp interval collapses. -/
theorem identified_iff_interval_collapses :
    (∀ g₁ g₂ : (Ω → ℝ) →ₗ[ℝ] ℝ, IsPositiveExtension S Φ g₁ →
        IsPositiveExtension S Φ g₂ → g₁ w = g₂ w)
      ↔ lowEnd S Φ w = highEnd S Φ w := by
  constructor
  · intro h
    obtain ⟨g₁, hg₁, hw₁⟩ := exists_extension_attaining_low S Φ hunit hΦ w
    obtain ⟨g₂, hg₂, hw₂⟩ := exists_extension_attaining_high S Φ hunit hΦ w
    rw [← hw₁, ← hw₂]
    exact h g₁ g₂ hg₁ hg₂
  · intro h g₁ g₂ hg₁ hg₂
    obtain ⟨l₁, u₁⟩ := extension_value_mem_interval S Φ hunit w g₁ hg₁
    obtain ⟨l₂, u₂⟩ := extension_value_mem_interval S Φ hunit w g₂ hg₂
    linarith

end Unital

/-- On a finite event space a positive extension is integration against a
nonnegative weight row. -/
theorem extension_eq_measure (g : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hg : ∀ f : Ω → ℝ, 0 ≤ f → 0 ≤ g f) :
    ∃ μ : Ω → ℝ, (∀ ω, 0 ≤ μ ω) ∧ ∀ f, g f = expectation μ f := by
  classical
  refine ⟨fun ω => g (Pi.single ω 1), fun ω => hg _ ?_, fun f => ?_⟩
  · intro ω'
    by_cases h : ω' = ω <;> simp [h]
  · have hf : f = ∑ ω, f ω • Pi.single ω (1 : ℝ) := by
      funext ω'
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hf]
    rw [map_sum]
    unfold expectation
    exact Finset.sum_congr rfl fun ω _ => by
      rw [map_smul, smul_eq_mul]; exact mul_comm _ _

end BoundedWriterComparison
end NCG
