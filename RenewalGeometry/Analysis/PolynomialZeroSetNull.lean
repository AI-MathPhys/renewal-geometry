/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The zero set of a nonzero real polynomial is Lebesgue-null

Infrastructure for `thm:howe-discriminant` of the spacetime–gauge duality paper.

* `volume_mvPolynomial_zeroSet_eq_zero`: for a nonzero polynomial `f ∈ ℝ[X_1, …, X_p]` the zero
  set `{x ∈ ℝ^p | f(x) = 0}` has Lebesgue measure zero.  Induction on `p` with Fubini
  (`MeasureTheory.Measure.measure_prod_null`): writing `f = ∑_k c_k(x') X_0^k`, the leading
  coefficient `c` is a nonzero polynomial in `p` variables, so `c(x') ≠ 0` almost everywhere,
  and on every such slice `f(·, x')` is a nonzero one-variable polynomial with finitely many
  roots;
* `interior_mvPolynomial_zeroSet_eq_empty`, `isOpen_mvPolynomial_nonzeroSet`,
  `dense_mvPolynomial_nonzeroSet`: the zero set has empty interior, and the set where `f ≠ 0`
  is open and dense;
* `mvPolynomial_nonzeroSet_open_dense_full_measure`: on every open region `U ⊆ ℝ^p` the set
  `{x ∈ U | f(x) ≠ 0}` is open, dense in `U` and of full measure in `U`.
-/

open MeasureTheory MvPolynomial

namespace RenewalGeometry

/-- The zero set of a real polynomial is closed, hence measurable. -/
theorem isClosed_mvPolynomial_zeroSet {σ : Type*} (f : MvPolynomial σ ℝ) :
    IsClosed {x : σ → ℝ | eval x f = 0} :=
  isClosed_singleton.preimage (MvPolynomial.continuous_eval f)

theorem measurableSet_mvPolynomial_zeroSet {p : ℕ} (f : MvPolynomial (Fin p) ℝ) :
    MeasurableSet {x : Fin p → ℝ | eval x f = 0} :=
  (isClosed_mvPolynomial_zeroSet f).measurableSet

/-- **The zero set of a nonzero real polynomial on `ℝ^p` is Lebesgue-null.** -/
theorem volume_mvPolynomial_zeroSet_eq_zero :
    ∀ {p : ℕ} (f : MvPolynomial (Fin p) ℝ), f ≠ 0 → volume {x : Fin p → ℝ | eval x f = 0} = 0
  | 0, f, hf => by
    have hempty : {x : Fin 0 → ℝ | eval x f = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      apply hf
      apply MvPolynomial.funext
      intro y
      rw [Subsingleton.elim y x, map_zero]
      exact hx
    rw [hempty, measure_empty]
  | p + 1, f, hf => by
    -- the one-variable form `f = g(X_0)` with coefficients in `ℝ[X_1, …, X_p]`
    set g := finSuccEquiv ℝ p f with hg
    have hg0 : g ≠ 0 := by
      intro h
      apply hf
      have := (finSuccEquiv ℝ p).injective (h.trans (map_zero _).symm)
      exact this
    set c := g.leadingCoeff with hc
    have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hIH := volume_mvPolynomial_zeroSet_eq_zero c hc0
    -- outside the null set `{c = 0}` every slice is a nonzero one-variable polynomial
    have hslice : ∀ s : Fin p → ℝ, eval s c ≠ 0 →
        volume {y : ℝ | eval (Fin.cons y s) f = 0} = 0 := by
      intro s hs
      have hne : g.map (eval s) ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q g.natDegree) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
        exact this
      have hfin : {y : ℝ | eval (Fin.cons y s) f = 0}.Finite := by
        have heq : {y : ℝ | eval (Fin.cons y s) f = 0} = {y | (g.map (eval s)).IsRoot y} := by
          ext y
          simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
          rw [eval_eq_eval_mv_eval', ← hg]
        rw [heq]
        exact Polynomial.finite_setOfPred_isRoot hne
      exact hfin.measure_zero volume
    -- transport along `ℝ^{p+1} ≃ ℝ × ℝ^p`
    set Z := {x : Fin (p + 1) → ℝ | eval x f = 0} with hZdef
    have hZ : MeasurableSet Z := measurableSet_mvPolynomial_zeroSet f
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℝ) 0
    have hpres := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) => ℝ) 0
    have hZS : Z = e ⁻¹' (e.symm ⁻¹' Z) := by
      ext x
      simp [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    rw [hZS, hpres.measure_preimage (e.symm.measurable hZ).nullMeasurableSet]
    -- swap the factors so that the single coordinate comes last
    set S' := {q : (Fin p → ℝ) × ℝ | eval (Fin.cons q.2 q.1) f = 0} with hS'def
    have hS' : e.symm ⁻¹' Z = Prod.swap ⁻¹' S' := by
      ext ⟨y, s⟩
      have hins : (Fin.insertNthEquiv (fun _ : Fin (p + 1) => ℝ) 0) (y, s) = Fin.cons y s := by
        rw [← Fin.insertNth_zero']
        rfl
      simp only [Set.mem_preimage, Prod.swap_prod_mk, hS'def, hZdef, Set.mem_setOf_eq, e,
        MeasurableEquiv.piFinSuccAbove_symm_apply, hins]
    have hS'meas : MeasurableSet S' := by
      have : S' = Prod.swap ⁻¹' (e.symm ⁻¹' Z) := by
        rw [hS', Set.preimage_preimage]
        simp
      rw [this]
      exact measurable_swap (e.symm.measurable hZ)
    have hswap : MeasurePreserving Prod.swap
        ((volume : Measure ℝ).prod (volume : Measure (Fin p → ℝ)))
        ((volume : Measure (Fin p → ℝ)).prod (volume : Measure ℝ)) :=
      MeasureTheory.Measure.measurePreserving_swap
    rw [hS']
    change ((volume : Measure ℝ).prod (volume : Measure (Fin p → ℝ))) (Prod.swap ⁻¹' S') = 0
    rw [hswap.measure_preimage hS'meas.nullMeasurableSet,
      MeasureTheory.Measure.measure_prod_null hS'meas]
    -- Fubini: almost every slice is null
    have hae : ∀ᵐ s ∂(volume : Measure (Fin p → ℝ)), eval s c ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using hIH
    filter_upwards [hae] with s hs
    have hfib : Prod.mk s ⁻¹' S' = {y : ℝ | eval (Fin.cons y s) f = 0} := by
      ext y
      rfl
    simp only [Pi.zero_apply]
    rw [hfib]
    exact hslice s hs

/-- The zero set of a nonzero real polynomial has empty interior. -/
theorem interior_mvPolynomial_zeroSet_eq_empty {p : ℕ} (f : MvPolynomial (Fin p) ℝ) (hf : f ≠ 0) :
    interior {x : Fin p → ℝ | eval x f = 0} = ∅ := by
  rw [← (IsOpen.measure_eq_zero_iff (volume : Measure (Fin p → ℝ)) isOpen_interior)]
  exact measure_mono_null interior_subset (volume_mvPolynomial_zeroSet_eq_zero f hf)

/-- The set where a real polynomial is nonzero is open. -/
theorem isOpen_mvPolynomial_nonzeroSet {σ : Type*} (f : MvPolynomial σ ℝ) :
    IsOpen {x : σ → ℝ | eval x f ≠ 0} :=
  (isClosed_mvPolynomial_zeroSet f).isOpen_compl

/-- The set where a nonzero real polynomial is nonzero is dense. -/
theorem dense_mvPolynomial_nonzeroSet {p : ℕ} (f : MvPolynomial (Fin p) ℝ) (hf : f ≠ 0) :
    Dense {x : Fin p → ℝ | eval x f ≠ 0} := by
  have h := interior_mvPolynomial_zeroSet_eq_empty f hf
  rw [interior_eq_empty_iff_dense_compl] at h
  exact h

/-- **Generic nonvanishing on open regions.**  For a nonzero real polynomial `f` and any open
region `U ⊆ ℝ^p`, the set `{x ∈ U | f(x) ≠ 0}` is open, dense in `U` (i.e. `U` lies in its
closure), and of full measure in `U` (its complement in `U` is null). -/
theorem mvPolynomial_nonzeroSet_open_dense_full_measure {p : ℕ} (f : MvPolynomial (Fin p) ℝ)
    (hf : f ≠ 0) (U : Set (Fin p → ℝ)) (hU : IsOpen U) :
    IsOpen {x ∈ U | eval x f ≠ 0} ∧ U ⊆ closure {x ∈ U | eval x f ≠ 0} ∧
      volume {x ∈ U | eval x f = 0} = 0 := by
  refine ⟨hU.inter (isOpen_mvPolynomial_nonzeroSet f), ?_, ?_⟩
  · exact (dense_mvPolynomial_nonzeroSet f hf).open_subset_closure_inter hU
  · exact measure_mono_null (fun x hx => hx.2) (volume_mvPolynomial_zeroSet_eq_zero f hf)

end RenewalGeometry
