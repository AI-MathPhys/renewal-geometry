/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Ordered predictive realization
  (`thm:ordered-memory`, Gran-Tensor manuscript)

* `ordered_memory`: on each finite response space, the
  future-pointwise cone is closed, pointed, and generating;
  precomposition transitions are positive; and every complete
  instrument preserves the normalization functional — the boxed
  identity `u(Σ_o A_{a_o} m) = u(m)`.

Rendering disclosed: response spaces are rendered as functions
on the finite declared futures with the pointwise cone (the
intersection of the future half-spaces); "physical columns
belong to the cone and span" is the operational-table
hypothesis; instrument completeness is the operational axiom
`Σ_o m(a_o f) = m(f)` taken as the hypothesis it is.
-/

namespace NCG

/-- `thm:ordered-memory`. -/
theorem ordered_memory {F : Type*} :
    -- (1) the future cone is closed
    IsClosed {m : F → ℝ | ∀ f, 0 ≤ m f}
    -- (2) pointed
    ∧ (∀ m : F → ℝ, (∀ f, 0 ≤ m f) → (∀ f, 0 ≤ -m f) →
        m = 0)
    -- (3) generating
    ∧ (∀ m : F → ℝ, ∃ p q : F → ℝ,
        (∀ f, 0 ≤ p f) ∧ (∀ f, 0 ≤ q f) ∧ m = p - q)
    -- (4) precomposition transitions are positive
    ∧ (∀ (a : F → F) (m : F → ℝ), (∀ f, 0 ≤ m f) →
        ∀ f, 0 ≤ (m ∘ a) f)
    -- (5) complete instruments preserve normalization
    ∧ (∀ {O : Type*} [Fintype O] (a : O → F → F)
        (m : F → ℝ) (e : F),
        (∀ f, ∑ o, m (a o f) = m f) →
        (∑ o, (m ∘ a o)) e = m e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : {m : F → ℝ | ∀ f, 0 ≤ m f}
        = ⋂ f, {m : F → ℝ | 0 ≤ m f} := by
      ext m
      simp
    rw [this]
    refine isClosed_iInter fun f => ?_
    exact isClosed_le continuous_const (continuous_apply f)
  · intro m h1 h2
    funext f
    have := h1 f
    have := h2 f
    simp only [Pi.zero_apply]
    linarith [h1 f, h2 f]
  · intro m
    refine ⟨fun f => max (m f) 0, fun f => max (-m f) 0,
      fun f => le_max_right _ _, fun f => le_max_right _ _, ?_⟩
    funext f
    simp only [Pi.sub_apply]
    rcases le_total (m f) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  · intro a m hm f
    exact hm (a f)
  · intro O _ a m e hcomp
    have := hcomp e
    simpa using this

end NCG

namespace NCG

/-! ## The actual table-native response cone -/

/-- The real response space spanned by the physical past columns of a table. -/
abbrev RealHankelCore (P F : Type*) (tbl : F → P → ℝ) :
    Submodule ℝ (F → ℝ) :=
  Submodule.span ℝ (Set.range fun p (f : F) => tbl f p)

/-- A physical past as an element of the response space. -/
def realHankelColumn {P F : Type*} (tbl : F → P → ℝ) (p : P) :
    RealHankelCore P F tbl :=
  ⟨fun f => tbl f p, Submodule.subset_span (Set.mem_range_self p)⟩

@[simp] theorem realHankelColumn_apply {P F : Type*}
    (tbl : F → P → ℝ) (p : P) (f : F) :
    (realHankelColumn tbl p : F → ℝ) f = tbl f p := rfl

/-- Positivity is inherited from every admitted positive future coordinate. -/
def ResponsePositive {P F : Type*} {tbl : F → P → ℝ}
    (m : RealHankelCore P F tbl) : Prop := ∀ f, 0 ≤ (m : F → ℝ) f

theorem responsePositive_zero {P F : Type*} {tbl : F → P → ℝ} :
    ResponsePositive (0 : RealHankelCore P F tbl) := by simp [ResponsePositive]

theorem ResponsePositive.add {P F : Type*} {tbl : F → P → ℝ}
    {m n : RealHankelCore P F tbl}
    (hm : ResponsePositive m) (hn : ResponsePositive n) :
    ResponsePositive (m + n) := fun f => add_nonneg (hm f) (hn f)

theorem ResponsePositive.smul_nonneg {P F : Type*} {tbl : F → P → ℝ}
    {m : RealHankelCore P F tbl} (hm : ResponsePositive m)
    {c : ℝ} (hc : 0 ≤ c) : ResponsePositive (c • m) :=
  fun f => mul_nonneg hc (hm f)

/-- Physical columns span the response space, now as vectors of the subtype. -/
theorem realHankelColumn_span {P F : Type*} (tbl : F → P → ℝ) :
    Submodule.span ℝ (Set.range (realHankelColumn tbl)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff
    (RealHankelCore P F tbl)
    (fun p => Submodule.subset_span (Set.mem_range_self p))).2
  rfl

/-- The actual response cone is generating when every physical column is
nonnegative. -/
theorem realHankelCone_generating {P F : Type*} (tbl : F → P → ℝ)
    (htable : ∀ f p, 0 ≤ tbl f p) (m : RealHankelCore P F tbl) :
    ∃ a b : RealHankelCore P F tbl,
      ResponsePositive a ∧ ResponsePositive b ∧ m = a - b := by
  have hm : m ∈ Submodule.span ℝ (Set.range (realHankelColumn tbl)) := by
    rw [realHankelColumn_span]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact ⟨realHankelColumn tbl p, 0, fun f => htable f p,
        responsePositive_zero, by simp⟩
  | zero => exact ⟨0, 0, responsePositive_zero, responsePositive_zero, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨ax, bx, hax, hbx, rfl⟩ := hx
      obtain ⟨ay, byv, hay, hby, rfl⟩ := hy
      exact ⟨ax + ay, bx + byv, hax.add hay, hbx.add hby, by abel⟩
  | smul c x _ hx =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hx
      rcases le_total 0 c with hc | hc
      · exact ⟨c • a, c • b, ha.smul_nonneg hc, hb.smul_nonneg hc, by
          module⟩
      · exact ⟨(-c) • b, (-c) • a, hb.smul_nonneg (neg_nonneg.mpr hc),
          ha.smul_nonneg (neg_nonneg.mpr hc), by module⟩

/-- Precomposition by an admitted primitive letter, restricted to the two
Hankel response spaces. -/
noncomputable def realHankelTransition {P F P' F' : Type*}
    (tbl : F → P → ℝ) (tbl' : F' → P' → ℝ)
    (past : P → P') (future : F' → F)
    (hcompat : ∀ f p, tbl' f (past p) = tbl (future f) p) :
    RealHankelCore P F tbl →ₗ[ℝ] RealHankelCore P' F' tbl' where
  toFun m := ⟨fun f => (m : F → ℝ) (future f), by
    refine Submodule.span_induction
      (p := fun x _ => (fun f => x (future f)) ∈ RealHankelCore P' F' tbl')
      ?_ ?_ ?_ ?_ m.property
    · intro x hx
      obtain ⟨p, rfl⟩ := hx
      have heq : (fun f => tbl (future f) p) =
          (fun f => tbl' f (past p)) := by
        funext f
        exact (hcompat f p).symm
      rw [heq]
      exact Submodule.subset_span (Set.mem_range_self (past p))
    · convert (Submodule.zero_mem (RealHankelCore P' F' tbl')) using 1
      funext f
      rfl
    · intro x y hx hy ihx ihy
      convert Submodule.add_mem (RealHankelCore P' F' tbl') ihx ihy using 1
      funext f
      rfl
    · intro c x hx ihx
      convert Submodule.smul_mem (RealHankelCore P' F' tbl') c ihx using 1
      funext f
      rfl⟩
  map_add' x y := by ext f; rfl
  map_smul' c x := by ext f; rfl

theorem realHankelTransition_positive {P F P' F' : Type*}
    (tbl : F → P → ℝ) (tbl' : F' → P' → ℝ)
    (past : P → P') (future : F' → F)
    (hcompat : ∀ f p, tbl' f (past p) = tbl (future f) p)
    {m : RealHankelCore P F tbl} (hm : ResponsePositive m) :
    ResponsePositive (realHankelTransition tbl tbl' past future hcompat m) :=
  fun f => hm (future f)

/-- Instrument normalization on the physical columns extends uniquely to the
whole response space because those columns span. -/
theorem hankelInstrument_normalization {P F O : Type*} [Fintype O]
    (tbl : F → P → ℝ)
    (A : O → RealHankelCore P F tbl →ₗ[ℝ] RealHankelCore P F tbl)
    (u : RealHankelCore P F tbl →ₗ[ℝ] ℝ)
    (hphysical : ∀ p, u (∑ o, A o (realHankelColumn tbl p)) =
      u (realHankelColumn tbl p)) :
    ∀ m, u (∑ o, A o m) = u m := by
  let lhs : RealHankelCore P F tbl →ₗ[ℝ] ℝ :=
    u.comp (∑ o, A o)
  have heq : lhs = u := by
    apply LinearMap.ext_on (realHankelColumn_span tbl)
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    simpa [lhs] using hphysical p
  intro m
  simpa [lhs, LinearMap.comp_apply] using LinearMap.congr_fun heq m

/-- Exact ordered-realization package on the table-native Hankel space. -/
theorem ordered_memory_exact {P F : Type*} [Finite F]
    (tbl : F → P → ℝ) (htable : ∀ f p, 0 ≤ tbl f p) :
    IsClosed {m : RealHankelCore P F tbl | ResponsePositive m}
    ∧ (∀ m : RealHankelCore P F tbl,
        ResponsePositive m → ResponsePositive (-m) → m = 0)
    ∧ (∀ m : RealHankelCore P F tbl,
        ∃ a b : RealHankelCore P F tbl,
          ResponsePositive a ∧ ResponsePositive b ∧ m = a - b)
    ∧ (∀ p, ResponsePositive (realHankelColumn tbl p)) := by
  letI := Fintype.ofFinite F
  refine ⟨?_, ?_, realHankelCone_generating tbl htable, fun p f => htable f p⟩
  · have hset : {m : RealHankelCore P F tbl | ResponsePositive m} =
        ⋂ f, {m : RealHankelCore P F tbl | 0 ≤ (m : F → ℝ) f} := by
      ext m
      simp [ResponsePositive]
    rw [hset]
    exact isClosed_iInter fun f =>
      isClosed_le continuous_const
        ((continuous_apply f).comp continuous_subtype_val)
  · intro m hm hneg
    apply Subtype.ext
    funext f
    have hp := hm f
    have hn := hneg f
    change (m : F → ℝ) f = 0
    simp only [Submodule.coe_neg, Pi.neg_apply] at hn
    linarith

end NCG
