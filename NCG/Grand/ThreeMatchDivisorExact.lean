/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ThreeMatch

/-!
# Three-match transversality: the divisor contradiction

Machinery for `thm:ar-three-match`, addressing the fidelity-audit gap ("the
divisor lower bound — the entire analytic input — disclosed"): the record's
own argument is the divisor contradiction, formalized exactly here.

* `matched_prod_dvd_sub`: the common product of matched atom occurrences
  divides both retained endpoints and hence the nonzero difference `n − n'`;
* `matched_card_le_two` (**the three-match bound**): if every atom exceeds
  `z` and the collision gap satisfies `|n − n'| ≤ G < z³`, then at most two
  atom occurrences can be matched — three matched occurrences would give a
  common divisor `d > z³ > G ≥ |n − n'| > 0` of `n − n'`;
* `three_match_transversality`: combined with the proved twelve-slot
  pigeonhole (`NCG.triple_transversality`), after any predetermined partition
  of the twelve slots into four triples, at least two entire triples on
  **each** endpoint contain no matched atom.

The anchor bounds (`x_i > z_Y^{1-24δ_Y}` from `thm:ar-fixed-order-source`,
and the numeric comparison `Y^{1/5+o(1)} < (z_Y^{1-24δ_Y})³ = Y^{1/4-o(1)}`)
enter as the hypotheses `hz`, `hz'`, `hgap`, `hG`.
-/

open Finset

namespace NCG
namespace ThreeMatchDivisor

/-- The common product of matched atom occurrences divides both endpoints and
hence the difference `n − n'`. -/
theorem matched_prod_dvd_sub (n n' : ℤ) (x x' : Fin 12 → ℤ)
    (m : Fin 12 → Fin 12) (S : Finset (Fin 12))
    (hinj : Set.InjOn m S)
    (hmatch : ∀ i ∈ S, x' (m i) = x i)
    (hu : (∏ i, x i) ∣ n) (hu' : (∏ i, x' i) ∣ n') :
    (∏ i ∈ S, x i) ∣ n - n' := by
  have hdn : (∏ i ∈ S, x i) ∣ n :=
    dvd_trans (Finset.prod_dvd_prod_of_subset S Finset.univ x
      (Finset.subset_univ S)) hu
  have himage : ∏ i ∈ S, x i = ∏ j ∈ S.image m, x' j := by
    rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
    exact (Finset.prod_congr rfl hmatch).symm
  have hdn' : (∏ i ∈ S, x i) ∣ n' := by
    rw [himage]
    exact dvd_trans (Finset.prod_dvd_prod_of_subset (S.image m) Finset.univ x'
      (Finset.subset_univ _)) hu'
  exact dvd_sub hdn hdn'

/-- **The three-match bound**: with every atom exceeding `z > 0` on both
endpoints and a nonzero collision gap `|n − n'| ≤ G < z³`, at most two atom
occurrences can be matched by equal numerical values. -/
theorem matched_card_le_two (n n' : ℤ) (x x' : Fin 12 → ℤ)
    (m : Fin 12 → Fin 12) (M : Finset (Fin 12)) (z G : ℤ)
    (hinj : Set.InjOn m M)
    (hmatch : ∀ i ∈ M, x' (m i) = x i)
    (hu : (∏ i, x i) ∣ n) (hu' : (∏ i, x' i) ∣ n')
    (hz0 : 0 < z) (hz : ∀ i, z < x i)
    (hne : n ≠ n') (hgap : |n - n'| ≤ G) (hG : G < z ^ 3) :
    M.card ≤ 2 := by
  by_contra hcard
  have h3 : 3 ≤ M.card := by omega
  obtain ⟨S, hSM, hS3⟩ := Finset.exists_subset_card_eq h3
  have hdvd : (∏ i ∈ S, x i) ∣ n - n' :=
    matched_prod_dvd_sub n n' x x' m S (hinj.mono hSM)
      (fun i hi => hmatch i (hSM hi)) hu hu'
  have hlow : z ^ 3 < ∏ i ∈ S, x i := by
    have hprod : ∏ _i ∈ S, z < ∏ i ∈ S, x i := by
      refine Finset.prod_lt_prod_of_nonempty (fun i _ => hz0)
        (fun i _ => hz i) ?_
      rw [← Finset.card_pos, hS3]
      norm_num
    rwa [Finset.prod_const, hS3] at hprod
  have habs : (∏ i ∈ S, x i) ≤ |n - n'| := by
    refine Int.le_of_dvd ?_ ((dvd_abs _ _).mpr hdvd)
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  omega

/-- **Three-match transversality**: under the divisor hypotheses, for any
predetermined partitions of the twelve slots into four triples on the two
endpoints, at least two entire triples on each endpoint contain no matched
atom occurrence. -/
theorem three_match_transversality (n n' : ℤ) (x x' : Fin 12 → ℤ)
    (m : Fin 12 → Fin 12) (M : Finset (Fin 12)) (z G : ℤ)
    (P P' : Fin 12 → Fin 4)
    (hinj : Set.InjOn m M)
    (hmatch : ∀ i ∈ M, x' (m i) = x i)
    (hu : (∏ i, x i) ∣ n) (hu' : (∏ i, x' i) ∣ n')
    (hz0 : 0 < z) (hz : ∀ i, z < x i)
    (hne : n ≠ n') (hgap : |n - n'| ≤ G) (hG : G < z ^ 3) :
    2 ≤ (Finset.univ.filter (fun t : Fin 4 => ∀ s ∈ M, P s ≠ t)).card ∧
      2 ≤ (Finset.univ.filter
        (fun t : Fin 4 => ∀ s ∈ M.image m, P' s ≠ t)).card := by
  have hM := matched_card_le_two n n' x x' m M z G hinj hmatch hu hu'
    hz0 hz hne hgap hG
  refine ⟨NCG.triple_transversality P M hM, ?_⟩
  exact NCG.triple_transversality P' (M.image m)
    (le_trans Finset.card_image_le hM)

end ThreeMatchDivisor
end NCG
