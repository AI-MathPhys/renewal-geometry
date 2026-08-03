/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Analytic-vector polar clock and the real score compiler
  (`thm:analytic-store-polar-master`,
   `cor:real-score-polar-master`, flagship manuscript)

Three mechanisms, matching the manuscript proof:

* the Lagrange spectral filter (`lagrange_transverse_filter`): if
  `𝒯(Rⱼ) = μⱼ² Rⱼ` for the double-commutator operator
  `𝒯 = -¼ ad_D²` on the transverse derivations, then the product
  `∏_{k≠j}(𝒯 - μₖ²)` applied to `R = Σ Rⱼ` recovers
  `(∏_{k≠j}(μⱼ² - μₖ²))·Rⱼ` — the manuscript's
  `Rⱼ = pⱼ(𝒯)R` after dividing by the displayed nonzero
  product;
* the group-closure clause (`open_subgroup_eq_top`,
  `analytic_store_polar`): an open subgroup of a preconnected
  topological group is the whole group, so once the blockwise
  `su(2)` span makes the generated subgroup open in the connected
  product `∏ⱼ PU(2)ⱼ` (the displayed hypothesis `hopen`), it
  contains every element — in particular the boxed quarter-root
  `Ad(e^{πJ/4})`;
* the real score compiler (`exp_conj_pair`, `real_score_polar`):
  conjugation by a two-sided-inverse pair carries exponentials to
  exponentials, so `R e^{-iZ⊗X/√N} R* = e^{J⊗X/√N}` follows from
  `R(-iZ⊗X)R* = J⊗X` — the boxed identity of the corollary, with
  the generator hypothesis `hgen` rendering `RZR* = Y_J`
  tensored against `X(q)`.

Rendering disclosed: the transversality selection of the control
value `u_*` (a nonzero analytic commutator avoiding finitely many
zero sets) and the blockwise `su(2)` span table are the
manuscript's prose steps entering through the displayed openness
hypothesis; the tensor-leg bookkeeping of the corollary enters
through the displayed generator hypothesis.
-/

open NormedSpace

namespace NCG

/-- Spectral shift factors of a single operator commute. -/
theorem end_factor_commute {V : Type*} [AddCommGroup V]
    [Module ℝ V] (𝒯 : Module.End ℝ V) (a b : ℝ) :
    Commute (𝒯 - a • (1 : Module.End ℝ V))
      (𝒯 - b • (1 : Module.End ℝ V)) := by
  have h2 : ∀ c : ℝ,
      Commute (c • (1 : Module.End ℝ V)) 𝒯 :=
    fun c => (Commute.one_left 𝒯).smul_left c
  have c1 : Commute (𝒯 - a • (1 : Module.End ℝ V)) 𝒯 :=
    (Commute.refl 𝒯).sub_left (h2 a)
  have c2 : Commute (𝒯 - a • (1 : Module.End ℝ V))
      (b • (1 : Module.End ℝ V)) :=
    (Commute.one_right _).smul_right b
  exact c1.sub_right c2

/-- Pairwise commutation of the shift factors, in the form
consumed by `Finset.noncommProd`. -/
theorem end_factor_pairwise {V : Type*} [AddCommGroup V]
    [Module ℝ V] {r : ℕ} (𝒯 : Module.End ℝ V)
    (μsq : Fin r → ℝ) (s : Finset (Fin r)) :
    (↑s : Set (Fin r)).Pairwise
      (Function.onFun Commute
        fun k => 𝒯 - μsq k • (1 : Module.End ℝ V)) :=
  fun a _ b _ _ => end_factor_commute 𝒯 (μsq a) (μsq b)

/-- The Lagrange spectral filter: the shifted product applied to
the summed transverse derivation isolates the `j`-th block with
the displayed nonzero coefficient. -/
theorem lagrange_transverse_filter {V : Type*} [AddCommGroup V]
    [Module ℝ V] {r : ℕ} (𝒯 : Module.End ℝ V) (μsq : Fin r → ℝ)
    (Rb : Fin r → V)
    (heig : ∀ j, 𝒯 (Rb j) = μsq j • Rb j) (j : Fin r) :
    ((Finset.univ.erase j).noncommProd
        (fun k => 𝒯 - μsq k • (1 : Module.End ℝ V))
        (end_factor_pairwise 𝒯 μsq _)) (∑ l, Rb l)
      = (∏ k ∈ Finset.univ.erase j, (μsq j - μsq k)) • Rb j := by
  classical
  have key : ∀ s : Finset (Fin r),
      (s.noncommProd
        (fun k => 𝒯 - μsq k • (1 : Module.End ℝ V))
        (end_factor_pairwise 𝒯 μsq s)) (∑ l, Rb l)
      = ∑ l, (∏ k ∈ s, (μsq l - μsq k)) • Rb l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.noncommProd_empty]
        simp
    | insert a s ha ih =>
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
          Module.End.mul_apply, ih, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, heig l, ← sub_smul, smul_smul,
          Finset.prod_insert ha, mul_comm]
  rw [key (Finset.univ.erase j)]
  rw [Finset.sum_eq_single j
    (fun l _ hlj => by
      rw [Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)
        (sub_self _), zero_smul])
    (fun h => absurd (Finset.mem_univ j) h)]

/-- The group-closure clause: an open subgroup of a preconnected
topological group is the whole group. -/
theorem open_subgroup_eq_top {Q : Type*} [Group Q]
    [TopologicalSpace Q] [SeparatelyContinuousMul Q]
    [PreconnectedSpace Q] (S : Subgroup Q)
    (hopen : IsOpen (S : Set Q)) : S = ⊤ := by
  have h1 : IsClopen (S : Set Q) :=
    OpenSubgroup.isClopen ⟨S, hopen⟩
  have h2 := h1.eq_univ ⟨1, S.one_mem⟩
  ext g
  simp only [Subgroup.mem_top, iff_true]
  have h3 : g ∈ (S : Set Q) := by
    rw [h2]
    exact Set.mem_univ g
  exact h3

/-- `thm:analytic-store-polar-master`, boxed membership: with the
blockwise `su(2)` span rendering the physical control subgroup
open in the connected projective product (`hopen`, displayed), it
contains the quarter-root `Ad(e^{πJ/4})` — and every other
element. -/
theorem analytic_store_polar {Q : Type*} [Group Q]
    [TopologicalSpace Q] [SeparatelyContinuousMul Q]
    [PreconnectedSpace Q] (S : Subgroup Q)
    (hopen : IsOpen (S : Set Q)) (Qpol : Q) : Qpol ∈ S := by
  rw [open_subgroup_eq_top S hopen]
  trivial

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

/-- Conjugation by a two-sided-inverse pair carries exponentials
to exponentials. -/
theorem exp_conj_pair (R R' m : 𝔸) (h1 : R * R' = 1)
    (h2 : R' * R = 1) :
    R * exp m * R' = exp (R * m * R') := by
  let f : 𝔸 →+* 𝔸 :=
    { toFun := fun a => R * a * R'
      map_one' := by rw [mul_one, h1]
      map_mul' := by
        intro a b
        calc R * (a * b) * R'
            = R * a * (R' * R) * b * R' := by
              rw [h2]
              noncomm_ring
          _ = R * a * R' * (R * b * R') := by noncomm_ring
      map_zero' := by rw [mul_zero, zero_mul]
      map_add' := by
        intro a b
        noncomm_ring }
  have hf : Continuous f := by
    have hc : Continuous fun a : 𝔸 => R * a * R' := by fun_prop
    exact hc
  have h3 := map_exp_of_mem_ball (𝕂 := ℝ) f hf m
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
  exact h3

/-- `cor:real-score-polar-master`, boxed identity: the complex
polar microtick is a derived conjugate of one real pointer–score
interaction — `R e^{G} R* = e^{G'}` once the generator is carried
over (`hgen`, the tensored rendering of `RZR* = Y_J`). -/
theorem real_score_polar (R R' G G' : 𝔸) (h1 : R * R' = 1)
    (h2 : R' * R = 1) (hgen : R * G * R' = G') :
    R * exp G * R' = exp G' := by
  rw [exp_conj_pair R R' G h1 h2, hgen]

end NCG
