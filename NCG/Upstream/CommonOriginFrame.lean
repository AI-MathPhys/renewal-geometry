/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CommonOriginUCP
import NCG.Lorentz.PositiveAveraging

/-!
# The common-origin spatial frame: second moment and deck character

The provable finite clauses of `prop:common-origin-pressure-frame`
(`manuscripts/renewal_emergence/renewal_emergence.tex`):

* `dirProfile_lower` — the tilted direction profile is uniformly
  bounded below by `r_* = λ₋(1−δ)/(3λ₊(1+δ))` on the spin box;
* `secondMoment_deck` — the spatial second moment
  `M_i(η) = Σ_{s,a} q_i(s|η) r_{i,a}(η_i s) v_{i,a} v_{i,a}ᵀ`
  is **deck even**: `M_i(−η) = M_i(η)`;
* `secondMoment_lower` — under the uniform Gram bound
  `Σ_a v_{i,a} v_{i,a}ᵀ ⪰ g_* I` and the profile lower bound,
  `M_i(η) ⪰ r_* g_* I` — deck-related orientation phases share one
  uniformly positive rank-three spatial second moment;
* `recordDeck_sign` — if the full resolved record `(s,a,b)` is
  immediately readable, the deck action `(s,a,b) ↦ (−s,a,b)` is a
  product of `9` disjoint transpositions of the `18` record values
  and has determinant `−1` — the nonzero determinant character.

The pressure-zero clause (`β = log 𝔞`), the Doob normalization, and
the connectivity of the signed cover (which needs primitivity)
remain unformalized; the record stays conditional with these lemmas
recorded as proved partial content.
-/

namespace NCG.CommonOrigin

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
/-- The uniform lower bound for the tilted direction profile on the
spin box: `r_{i,a}(u) ≥ λ₋(1−δ)/(3λ₊(1+δ))`. -/
theorem dirProfile_lower (lam : ι → Fin 3 → ℝ) (ε : ℝ)
    (bb : Fin 3 → ℝ) {B lamm lamp : ℝ}
    (hlamm : ∀ i a, lamm ≤ lam i a)
    (hlamp : ∀ i a, lam i a ≤ lamp) (hlamm0 : 0 < lamm)
    (hb : ∀ a, |bb a| ≤ B) (hδ : |ε| * B < 1)
    (i : ι) (a : Fin 3) {u : ℝ} (hu : |u| ≤ 1) :
    lamm * (1 - |ε| * B) / (3 * (lamp * (1 + |ε| * B)))
      ≤ dirProfile lam ε bb i a u := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb 0)
  have hδ0 : 0 ≤ |ε| * B := mul_nonneg (abs_nonneg ε) hB
  have habs : ∀ c : Fin 3, |ε * bb c * u| ≤ |ε| * B := by
    intro c
    rw [abs_mul, abs_mul]
    have h1 : |ε| * |bb c| ≤ |ε| * B :=
      mul_le_mul_of_nonneg_left (hb c) (abs_nonneg ε)
    have h2 : |ε| * |bb c| * |u| ≤ |ε| * |bb c| * 1 :=
      mul_le_mul_of_nonneg_left hu
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h3 : |ε| * |bb c| * 1 = |ε| * |bb c| := mul_one _
    linarith
  have hlamp0 : 0 < lamp := lt_of_lt_of_le hlamm0 (le_trans
    (hlamm i a) (hlamp i a))
  have hnum : lamm * (1 - |ε| * B) ≤ dirWeight lam ε bb i a u := by
    rw [dirWeight]
    have h1 : 1 - |ε| * B ≤ 1 + ε * bb a * u := by
      have h2 := (abs_le.mp (habs a)).1
      linarith
    have h3 : 0 ≤ 1 - |ε| * B := by linarith
    calc lamm * (1 - |ε| * B) ≤ lam i a * (1 - |ε| * B) :=
        mul_le_mul_of_nonneg_right (hlamm i a) h3
      _ ≤ lam i a * (1 + ε * bb a * u) :=
        mul_le_mul_of_nonneg_left h1
          (le_trans hlamm0.le (hlamm i a))
  have hden : ∑ c, dirWeight lam ε bb i c u
      ≤ 3 * (lamp * (1 + |ε| * B)) := by
    have h4 : ∀ c : Fin 3, dirWeight lam ε bb i c u
        ≤ lamp * (1 + |ε| * B) := by
      intro c
      rw [dirWeight]
      have h5 : 1 + ε * bb c * u ≤ 1 + |ε| * B := by
        have h6 := (abs_le.mp (habs c)).2
        linarith
      have h7 : 0 ≤ 1 + ε * bb c * u := by
        have h8 := (abs_le.mp (habs c)).1
        linarith
      calc lam i c * (1 + ε * bb c * u)
          ≤ lamp * (1 + ε * bb c * u) :=
            mul_le_mul_of_nonneg_right (hlamp i c) h7
        _ ≤ lamp * (1 + |ε| * B) :=
            mul_le_mul_of_nonneg_left h5 hlamp0.le
    calc ∑ c, dirWeight lam ε bb i c u
        ≤ ∑ _c : Fin 3, lamp * (1 + |ε| * B) :=
          Finset.sum_le_sum fun c _ => h4 c
      _ = 3 * (lamp * (1 + |ε| * B)) := by
          rw [Finset.sum_const]
          simp
  have hdenpos : 0 < ∑ c, dirWeight lam ε bb i c u :=
    Finset.sum_pos (fun c _ => dirWeight_pos lam ε bb
      (fun i' a' => lt_of_lt_of_le hlamm0 (hlamm i' a'))
      hb hδ i c hu) Finset.univ_nonempty
  have hd3 : (0 : ℝ) < 3 * (lamp * (1 + |ε| * B)) := by positivity
  rw [dirProfile, div_le_div_iff₀ hd3 hdenpos]
  calc lamm * (1 - |ε| * B) * (∑ c, dirWeight lam ε bb i c u)
      ≤ lamm * (1 - |ε| * B) * (3 * (lamp * (1 + |ε| * B))) := by
        refine mul_le_mul_of_nonneg_left hden ?_
        have h9 : (0 : ℝ) ≤ 1 - |ε| * B := by linarith
        exact mul_nonneg hlamm0.le h9
    _ ≤ dirWeight lam ε bb i a u
          * (3 * (lamp * (1 + |ε| * B))) :=
        mul_le_mul_of_nonneg_right hnum hd3.le

namespace IsingData

variable (D : IsingData ι)

/-- The resolved spatial second moment
`M_i(η) = Σ_{s,a} q_i(s|η) r_{i,a}(η_i s) v_{i,a} v_{i,a}ᵀ`. -/
noncomputable def secondMoment (r : ι → Fin 3 → ℝ → ℝ)
    (v : ι → Fin 3 → (Fin 3 → ℝ)) (i : ι) (η : ι → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ a, (D.q i 1 η * r i a (η i * 1))
      • vecMulVec (v i a) (v i a)
    + ∑ a, (D.q i (-1) η * r i a (η i * (-1)))
        • vecMulVec (v i a) (v i a)

omit [DecidableEq ι] [Fintype ι] in
/-- **Deck evenness**: `M_i(−η) = M_i(η)` — deck-related
orientation phases have the same spatial second moment. -/
theorem secondMoment_deck (r : ι → Fin 3 → ℝ → ℝ)
    (v : ι → Fin 3 → (Fin 3 → ℝ)) (i : ι) (η : ι → ℝ) :
    D.secondMoment r v i (-η) = D.secondMoment r v i η := by
  rw [secondMoment, secondMoment]
  have h1 : ∑ a, (D.q i 1 (-η) * r i a ((-η) i * 1))
      • vecMulVec (v i a) (v i a)
      = ∑ a, (D.q i (-1) η * r i a (η i * (-1)))
          • vecMulVec (v i a) (v i a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [D.q_deck, show (-η) i * 1 = η i * (-1) by
      rw [Pi.neg_apply]; ring]
  have h2 : ∑ a, (D.q i (-1) (-η) * r i a ((-η) i * (-1)))
      • vecMulVec (v i a) (v i a)
      = ∑ a, (D.q i 1 η * r i a (η i * 1))
          • vecMulVec (v i a) (v i a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [D.q_deck, neg_neg, show (-η) i * (-1) = η i * 1 by
      rw [Pi.neg_apply]; ring]
  rw [h1, h2, add_comm]

omit [DecidableEq ι] [Fintype ι] in
/-- The single-redraw direction average dominates `r_* g_* I`. -/
theorem dirAverage_lower (r : ι → Fin 3 → ℝ → ℝ)
    (v : ι → Fin 3 → (Fin 3 → ℝ)) (i : ι) {rstar gstar : ℝ}
    (hrstar : 0 ≤ rstar)
    (hrlow : ∀ a u, |u| ≤ 1 → rstar ≤ r i a u)
    (hgram : ((∑ a, vecMulVec (v i a) (v i a))
      - gstar • 1).PosSemidef)
    {u : ℝ} (hu : |u| ≤ 1) :
    ((∑ a, (r i a u) • vecMulVec (v i a) (v i a))
      - (rstar * gstar) • 1).PosSemidef := by
  have hkey : (∑ a, (r i a u) • vecMulVec (v i a) (v i a))
      - (rstar * gstar) • 1
      = (∑ a, (r i a u - rstar) • vecMulVec (v i a) (v i a))
        + rstar • ((∑ a, vecMulVec (v i a) (v i a))
            - gstar • 1) := by
    rw [smul_sub, Finset.smul_sum, smul_smul]
    have h1 : ∑ a, (r i a u - rstar)
        • vecMulVec (v i a) (v i a)
        = (∑ a, (r i a u) • vecMulVec (v i a) (v i a))
          - ∑ a, rstar • vecMulVec (v i a) (v i a) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sub_smul]
    rw [h1]
    abel
  rw [hkey]
  refine Matrix.PosSemidef.add ?_ ?_
  · exact posSemidef_sum_outer _
      (fun a => sub_nonneg.mpr (hrlow a u hu)) _
  · exact Matrix.PosSemidef.smul hgram hrstar

omit [DecidableEq ι] [Fintype ι] in
/-- **The uniform spatial ellipticity clause of
`prop:common-origin-pressure-frame`**: on the spin box,
`M_i(η) ⪰ r_* g_* I₃`. -/
theorem secondMoment_lower (r : ι → Fin 3 → ℝ → ℝ)
    (v : ι → Fin 3 → (Fin 3 → ℝ)) (i : ι) {rstar gstar : ℝ}
    (hrstar : 0 ≤ rstar)
    (hrlow : ∀ a u, |u| ≤ 1 → rstar ≤ r i a u)
    (hgram : ((∑ a, vecMulVec (v i a) (v i a))
      - gstar • 1).PosSemidef)
    {η : ι → ℝ} (hη : ∀ j, |η j| ≤ 1) :
    (D.secondMoment r v i η - (rstar * gstar) • 1).PosSemidef := by
  have hu1 : |η i * 1| ≤ 1 := by
    rw [mul_one]
    exact hη i
  have hu2 : |η i * (-1)| ≤ 1 := by
    rw [mul_neg_one, abs_neg]
    exact hη i
  have hq1 := D.q_pos i 1 η
  have hq2 := D.q_pos i (-1) η
  have hqsum := D.q_sum i η
  set T1 : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ a, (r i a (η i * 1)) • vecMulVec (v i a) (v i a) with hT1
  set T2 : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ a, (r i a (η i * (-1))) • vecMulVec (v i a) (v i a) with hT2
  have hM : D.secondMoment r v i η
      = D.q i 1 η • T1 + D.q i (-1) η • T2 := by
    rw [secondMoment, hT1, hT2, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul]
  have hsplit : D.secondMoment r v i η - (rstar * gstar) • 1
      = D.q i 1 η • (T1 - (rstar * gstar) • 1)
        + D.q i (-1) η • (T2 - (rstar * gstar) • 1) := by
    rw [hM]
    have h2 : D.q i 1 η • ((rstar * gstar)
        • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        + D.q i (-1) η • ((rstar * gstar) • 1)
        = (rstar * gstar) • 1 := by
      rw [smul_smul, smul_smul, ← add_smul]
      rw [show D.q i 1 η * (rstar * gstar)
          + D.q i (-1) η * (rstar * gstar)
          = (D.q i 1 η + D.q i (-1) η) * (rstar * gstar) by ring]
      rw [hqsum, one_mul]
    calc D.q i 1 η • T1 + D.q i (-1) η • T2
          - (rstar * gstar) • 1
        = D.q i 1 η • T1 + D.q i (-1) η • T2
          - (D.q i 1 η • ((rstar * gstar)
              • (1 : Matrix (Fin 3) (Fin 3) ℝ))
            + D.q i (-1) η • ((rstar * gstar) • 1)) := by
          rw [h2]
      _ = D.q i 1 η • (T1 - (rstar * gstar) • 1)
          + D.q i (-1) η • (T2 - (rstar * gstar) • 1) := by
          rw [smul_sub, smul_sub]
          abel
  rw [hsplit]
  refine Matrix.PosSemidef.add ?_ ?_
  · exact Matrix.PosSemidef.smul
      (dirAverage_lower r v i hrstar hrlow hgram hu1) hq1.le
  · exact Matrix.PosSemidef.smul
      (dirAverage_lower r v i hrstar hrlow hgram hu2) hq2.le

end IsingData

/-- The deck action on the resolved record values
`(s,a,b) ↦ (−s,a,b)`. -/
def recordDeck : Equiv.Perm (Bool × Fin 3 × Fin 3) :=
  Function.Involutive.toPerm (fun p => (!p.1, p.2)) (by
    rintro ⟨s, ab⟩
    simp)

/-- **The determinant character clause of
`prop:common-origin-pressure-frame`**: the deck action on the `18`
resolved record values is a product of `9` disjoint transpositions —
its determinant (permutation sign) is `−1`, representing the nonzero
classifying character. -/
theorem recordDeck_sign :
    Equiv.Perm.sign (recordDeck) = -1 := by decide

end NCG.CommonOrigin
