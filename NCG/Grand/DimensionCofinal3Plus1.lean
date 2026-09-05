/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.DimensionK4Selector

/-!
# Cofinal stability and the selected spacetime dimension
  (`cor:dimension-cofinal-3plus1`, Gran-Tensor manuscript)

The persistence layer of the dimension-selection corollary: on
a cofinal system whose corrected source operators converge
(summably correctable mixed-Gram defects,
`thm:summable-mixed-Gram-correction`), spectral separation
persists to the canonical limit —

* `form_tendsto`: entrywise convergence of the corrected
  operators gives convergence of every quadratic form;
* `margin_persists`: a positive lower form margin persists to
  the limit (the pair-gap and threshold-rank lower clauses);
* `rank_ge_of_margin`: a positive-definite limit form on an
  `r`-dimensional witness subspace forces limit rank `≥ r`;
* `null_persists` and `rank_le_of_null`: vanishing
  source-loss/extra-writer tails persist, and a positive
  semidefinite limit with an `(n-r)`-dimensional null witness
  subspace has rank `≤ r`;
* `exact_rank_persistence`: together, the corrected threshold
  ranks persist exactly on the limit;
* `selected_spacetime_dimension` and
  `cofinal_dimension_selection`: persisted endpoint and edge
  threshold ranks `3` and `6` identify the local relation cell
  as `K₄` through the proved selector arithmetic
  (`thm:dimension-K4-selector`), and with the independently
  reconstructed one-dimensional clock the compiler-minimal
  active branch has `1 + 3` dimensions (DS.14).

The canonical limit quotient itself — its construction,
terminality among cofinal sufficient factors, and the
positive-semidefiniteness of the corrected limit Gram — is the
content of the proved records
`thm:joint-source-inductive-limit` (`commonCarrierIsometry`,
`commonCarrierMap_unique`), `thm:minimal-record`
(`minimal_record_universal`), and
`thm:summable-mixed-Gram-correction`
(`mixedGram_limit_posSemidef`), consumed here as the
positive-semidefinite limit hypothesis.
-/

open Matrix Filter
open scoped ComplexOrder Topology

namespace NCG
namespace DimensionCofinal

variable {n : Type} [Fintype n]

/-- The real quadratic form of a matrix. -/
noncomputable def qf (A : Matrix n n ℂ) (x : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

/-- Entrywise convergence of corrected operators gives
convergence of every quadratic form. -/
theorem form_tendsto (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ)
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop
      (𝓝 (A' i j))) (x : n → ℂ) :
    Tendsto (fun k => qf (A k) x) atTop (𝓝 (qf A' x)) := by
  have h1 : Tendsto (fun k => star x ⬝ᵥ (A k *ᵥ x)) atTop
      (𝓝 (star x ⬝ᵥ (A' *ᵥ x))) := by
    simp only [dotProduct, Matrix.mulVec]
    refine tendsto_finsetSum _ fun i _ => ?_
    exact tendsto_const_nhds.mul
      (tendsto_finsetSum _ fun j _ =>
        (hconv i j).mul tendsto_const_nhds)
  exact (Complex.continuous_re.tendsto _).comp h1

/-- A uniform positive lower form margin persists to the
limit — the pair-gap and threshold clauses. -/
theorem margin_persists (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ)
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop
      (𝓝 (A' i j)))
    (x : n → ℂ) (δ : ℝ) (hlow : ∀ k, δ ≤ qf (A k) x) :
    δ ≤ qf A' x :=
  ge_of_tendsto' (form_tendsto A A' hconv x) hlow

/-- Vanishing tails persist: if the forms tend to zero along
the corrected system, the limit form vanishes. -/
theorem null_persists (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ)
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop
      (𝓝 (A' i j)))
    (x : n → ℂ)
    (htail : Tendsto (fun k => qf (A k) x) atTop (𝓝 0)) :
    qf A' x = 0 :=
  tendsto_nhds_unique (form_tendsto A A' hconv x) htail

/-- A positive-definite limit form on an `r`-dimensional
witness subspace forces limit rank at least `r`. -/
theorem rank_ge_of_margin (A' : Matrix n n ℂ)
    (V : Submodule ℂ (n → ℂ))
    (hpos : ∀ x ∈ V, x ≠ 0 → 0 < qf A' x) :
    Module.finrank ℂ V ≤ A'.rank := by
  have hinj : Function.Injective
      (A'.mulVecLin.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxV⟩ hx0
    have hx : A' *ᵥ x = 0 := by
      rw [LinearMap.domRestrict_apply,
        Matrix.mulVecLin_apply] at hx0
      exact hx0
    by_cases hxz : x = 0
    · exact Subtype.ext hxz
    · exfalso
      have hq : qf A' x = 0 := by
        rw [qf, hx, dotProduct_zero, Complex.zero_re]
      exact absurd hq (ne_of_gt (hpos x hxV hxz))
  calc Module.finrank ℂ V
      = Module.finrank ℂ
        (LinearMap.range (A'.mulVecLin.domRestrict V)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank ℂ (LinearMap.range A'.mulVecLin) :=
        Submodule.finrank_mono (by
          rintro y ⟨⟨x, hxV⟩, rfl⟩
          exact ⟨x, rfl⟩)
    _ = A'.rank := by rw [Matrix.rank]

/-- A positive semidefinite limit whose form vanishes on a
witness subspace `W` has rank at most `n - dim W`. -/
theorem rank_le_of_null (A' : Matrix n n ℂ)
    (hA' : A'.PosSemidef) (W : Submodule ℂ (n → ℂ))
    (hnull : ∀ x ∈ W, qf A' x = 0) :
    A'.rank ≤ Fintype.card n - Module.finrank ℂ W := by
  have hker : W ≤ LinearMap.ker A'.mulVecLin := by
    intro x hxW
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hnn :=
      Matrix.PosSemidef.dotProduct_mulVec_nonneg hA' x
    obtain ⟨_, him⟩ := Complex.nonneg_iff.mp hnn
    have hform : star x ⬝ᵥ (A' *ᵥ x) = 0 := by
      apply Complex.ext
      · rw [Complex.zero_re]
        exact hnull x hxW
      · rw [Complex.zero_im]
        exact him.symm
    exact (hA'.dotProduct_mulVec_zero_iff x).mp hform
  have hWk : Module.finrank ℂ W
      ≤ Module.finrank ℂ (LinearMap.ker A'.mulVecLin) :=
    Submodule.finrank_mono hker
  have hrn :=
    LinearMap.finrank_range_add_finrank_ker A'.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  rw [Matrix.rank]
  omega

/-- **Exact threshold-rank persistence**: uniform positive
margins on an `r`-dimensional witness subspace together with
vanishing tails on an `(n-r)`-dimensional null witness force
the limit rank to be exactly `r`. -/
theorem exact_rank_persistence (A : ℕ → Matrix n n ℂ)
    (A' : Matrix n n ℂ) (r : ℕ)
    (hconv : ∀ i j, Tendsto (fun k => A k i j) atTop
      (𝓝 (A' i j)))
    (hA' : A'.PosSemidef)
    (V W : Submodule ℂ (n → ℂ))
    (hVr : Module.finrank ℂ V = r)
    (hWr : Module.finrank ℂ W = Fintype.card n - r)
    (hr : r ≤ Fintype.card n)
    (hlowV : ∀ x ∈ V, x ≠ 0 →
      ∃ δ > (0:ℝ), ∀ k, δ ≤ qf (A k) x)
    (htailW : ∀ x ∈ W,
      Tendsto (fun k => qf (A k) x) atTop (𝓝 0)) :
    A'.rank = r := by
  have h1 : r ≤ A'.rank := by
    rw [← hVr]
    refine rank_ge_of_margin A' V fun x hxV hx0 => ?_
    obtain ⟨δ, hδ, hlow⟩ := hlowV x hxV hx0
    exact lt_of_lt_of_le hδ
      (margin_persists A A' hconv x δ hlow)
  have h2 : A'.rank ≤ Fintype.card n - (Fintype.card n - r) :=
    hWr ▸ rank_le_of_null A' hA' W fun x hxW =>
      null_persists A A' hconv x (htailW x hxW)
  omega

/-- **DS.14 through the selector**: persisted endpoint and
edge threshold ranks `3` and `6` identify the local relation
cell as `K₄`, and with the one-dimensional clock the selected
spacetime dimension is `1 + 3 = 4`. -/
theorem selected_spacetime_dimension (N : ℕ) (hN : Even N)
    (h3 : 3 ≤ N) (hend : N - 1 = 3)
    (hedge : N.choose 2 = 6) :
    N = 4 ∧ 1 + (N - 1) = 4 := by
  have h4 := (dimension_K4_selector.2.1 N hN h3).2.2.2.mp
    ⟨hend, hedge⟩
  exact ⟨h4, by rw [hend]⟩

/-- The assembled cofinal selection: exact persisted ranks
matching the endpoint and edge thresholds of an even local
cell force the cell to be `K₄` and the compiler-minimal
active branch to `1 + 3` dimensions. -/
theorem cofinal_dimension_selection
    {nE nF : Type} [Fintype nE] [Fintype nF]
    (Aend' : Matrix nE nE ℂ) (Aedge' : Matrix nF nF ℂ)
    (N : ℕ) (hN : Even N) (h3 : 3 ≤ N)
    (hendrank : Aend'.rank = N - 1)
    (hedgerank : Aedge'.rank = N.choose 2)
    (hend3 : Aend'.rank = 3) (hedge6 : Aedge'.rank = 6) :
    N = 4 ∧ 1 + (N - 1) = 4 :=
  selected_spacetime_dimension N hN h3
    (hendrank ▸ hend3) (hedgerank ▸ hedge6)

end DimensionCofinal
end NCG
