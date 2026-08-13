/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SobolevWeyl
import NCG.Grand.FinitePressureFlowMaxCut

/-!
# Exact finite operational Sobolev and Weyl bounds

This file supplies the coarea/Sobolev and finite spectral-counting layers of
the operational Sobolev-Weyl theorem.
-/

open scoped BigOperators

noncomputable section

namespace NCG

/-- Weighted L^(3/2) norm, written with real powers. -/
def weightedLThreeHalves
    {V : Type*} [Fintype V] (μ g : V → ℝ) : ℝ :=
  (∑ v, μ v * g v ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)

/-- Weighted finite Minkowski inequality at exponent 3/2. -/
theorem weightedLThreeHalves_add
    {V : Type*} [Fintype V]
    (μ g k : V → ℝ)
    (hμ : ∀ v, 0 ≤ μ v) (hg : ∀ v, 0 ≤ g v) (hk : ∀ v, 0 ≤ k v) :
    weightedLThreeHalves μ (g + k) ≤
      weightedLThreeHalves μ g + weightedLThreeHalves μ k := by
  let w : V → ℝ := fun v => μ v ^ ((2 : ℝ) / 3)
  have hw : ∀ v, 0 ≤ w v := fun v => Real.rpow_nonneg (hμ v) _
  have hpow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a ^ ((2 : ℝ) / 3) * b) ^ ((3 : ℝ) / 2) =
        a * b ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ha _) hb]
    rw [← Real.rpow_mul ha]
    norm_num
  have hmink := Real.Lp_add_le (s := (Finset.univ : Finset V))
    (f := fun v => w v * g v) (g := fun v => w v * k v)
    (p := (3 : ℝ) / 2) (by norm_num)
  unfold weightedLThreeHalves
  have hterm (v : V) (b : ℝ) (hb : 0 ≤ b) :
      |w v * b| ^ ((3 : ℝ) / 2) =
        μ v * b ^ ((3 : ℝ) / 2) := by
    rw [abs_of_nonneg (mul_nonneg (hw v) hb)]
    exact hpow (μ v) b (hμ v) hb
  simpa only [Finset.mem_univ, true_and, Pi.add_apply, one_div,
    show ((3 : ℝ) / 2)⁻¹ = (2 : ℝ) / 3 by norm_num,
    ← mul_add, hterm _ _ (add_nonneg (hg _) (hk _)),
    hterm _ _ (hg _), hterm _ _ (hk _)] using hmink

/-- Minkowski for an arbitrary finite sum of nonnegative functions. -/
theorem weightedLThreeHalves_finset_sum
    {V J : Type*} [Fintype V]
    (μ : V → ℝ) (F : J → V → ℝ) (s : Finset J)
    (hμ : ∀ v, 0 ≤ μ v) (hF : ∀ j v, 0 ≤ F j v) :
    weightedLThreeHalves μ (∑ j ∈ s, F j) ≤
      ∑ j ∈ s, weightedLThreeHalves μ (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedLThreeHalves]
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
      refine (weightedLThreeHalves_add μ (F j) (∑ i ∈ s, F i)
        hμ (hF j) ?_).trans (add_le_add (le_refl _) ih)
      intro v
      simp only [Finset.sum_apply]
      exact Finset.sum_nonneg fun i hi => hF i v

/-- Positive support of a finite nonnegative function. -/
def finitePositiveSupport
    {V : Type*} [Fintype V] (g : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => 0 < g v

/-- A positive-coefficient layer of a nonnegative layer cake lies in the
positive support of the represented function. -/
theorem layerCake_positiveLayer_subset_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → ℝ) (L : FiniteCutLayerCake g)
    (A : Finset V) (hA : 0 < L.coeff A) :
    A ⊆ finitePositiveSupport g := by
  classical
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ v, ?_⟩
  rw [L.expansion v]
  have hterm :
      L.coeff A * cutIndicator A v ≤
        ∑ B : Finset V, L.coeff B * cutIndicator B v := by
    apply Finset.single_le_sum
      (s := (Finset.univ : Finset (Finset V)))
      (f := fun B => L.coeff B * cutIndicator B v)
    · intro B hBA
      exact mul_nonneg (L.coeff_nonneg B) (by
        unfold cutIndicator
        split_ifs <;> norm_num)
    · exact Finset.mem_univ A
  have hind : cutIndicator A v = 1 := by simp [cutIndicator, hv]
  rw [hind, mul_one] at hterm
  exact hA.trans_le hterm

/-- Weighted norm of one nonnegative cut layer. -/
theorem weightedLThreeHalves_cutLayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (a : ℝ) (ha : 0 ≤ a) (A : Finset V) :
    weightedLThreeHalves μ (fun v => a * cutIndicator A v) =
      a * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) := by
  unfold weightedLThreeHalves
  have hmass : 0 ≤ ∑ v ∈ A, μ v :=
    Finset.sum_nonneg fun v hv => hμ v
  have hsum :
      (∑ v, μ v * (a * cutIndicator A v) ^ ((3 : ℝ) / 2)) =
        a ^ ((3 : ℝ) / 2) * ∑ v ∈ A, μ v := by
    rw [Finset.mul_sum]
    simp [cutIndicator, Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hsum, Real.mul_rpow (Real.rpow_nonneg ha _) hmass]
  rw [← Real.rpow_mul ha]
  norm_num

/-- Exact finite coarea Sobolev inequality on a half-volume support. -/
theorem finite_coarea_sobolev_three_halves
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (g : V → ℝ) (hg : ∀ v, 0 ≤ g v)
    (I h : ℝ) (hI : 0 ≤ I) (hh : 0 ≤ h)
    (hcut : ∀ A : Finset V,
      A ⊆ finitePositiveSupport g →
      I * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    I * weightedLThreeHalves μ g ≤
      h / 2 * ∑ u, ∑ v, c u v * |g u - g v| := by
  classical
  obtain ⟨L⟩ := finite_nonnegative_cut_layerCake g hg
  have hrepr : g = ∑ A : Finset V,
      (fun v => L.coeff A * cutIndicator A v) := by
    funext v
    simpa using L.expansion v
  have hnorm :
      weightedLThreeHalves μ g ≤
        ∑ A : Finset V,
          L.coeff A * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) := by
    conv_lhs => rw [hrepr]
    refine (weightedLThreeHalves_finset_sum μ
      (fun A v => L.coeff A * cutIndicator A v) Finset.univ hμ ?_).trans_eq ?_
    · intro A v
      exact mul_nonneg (L.coeff_nonneg A) (by
        unfold cutIndicator
        split_ifs <;> norm_num)
    · apply Finset.sum_congr rfl
      intro A _
      exact weightedLThreeHalves_cutLayer μ hμ
        (L.coeff A) (L.coeff_nonneg A) A
  calc
    I * weightedLThreeHalves μ g
        ≤ I * ∑ A, L.coeff A *
            (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hnorm hI
    _ = ∑ A, L.coeff A *
          (I * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A _
        ring
    _ ≤ ∑ A, L.coeff A * (h * finiteCutCapacity c A) := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hA : 0 < L.coeff A
      · exact mul_le_mul_of_nonneg_left
          (hcut A (layerCake_positiveLayer_subset_support g L A hA))
          (L.coeff_nonneg A)
      · have hz : L.coeff A = 0 :=
          le_antisymm (le_of_not_gt hA) (L.coeff_nonneg A)
        simp [hz]
    _ = h / 2 * ∑ u, ∑ v, c u v * |g u - g v| := by
      let L0 : FiniteCutLayerCake (fun v => g v - 0) := {
        coeff := L.coeff
        coeff_nonneg := L.coeff_nonneg
        expansion := fun v => by simpa using L.expansion v
        pair_expansion := fun u v => by simpa using L.pair_expansion u v }
      have hvar :
          (∑ u, ∑ v, c u v * |g u - g v|) =
            2 * ∑ A, L.coeff A * finiteCutCapacity c A := by
        simpa [L0] using
          cutLayerCake_weightedVariation c hsym g 0 L0
      calc
        (∑ A, L.coeff A * (h * finiteCutCapacity c A))
            = h * ∑ A, L.coeff A * finiteCutCapacity c A := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro A _
              ring
        _ = h / 2 * (2 * ∑ A,
              L.coeff A * finiteCutCapacity c A) := by ring
        _ = h / 2 * ∑ u, ∑ v, c u v * |g u - g v| := by rw [hvar]

/-- Ordered-edge normalization of the spatial Dirichlet energy. -/
def finiteSpatialEnergy
    {V : Type*} [Fintype V] (c : V → V → ℝ) (f : V → ℝ) : ℝ :=
  1 / 2 * ∑ u, ∑ v, c u v * (f u - f v) ^ 2

/-- Fourth-power edge variation controlled by degree, energy, and the
weighted sixth power. -/
theorem fourth_power_edge_variation_sq
    {V : Type*} [Fintype V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (D h : ℝ) (hD : 0 ≤ D) (hh : 0 < h)
    (hdegree : ∀ v, h ^ 2 * (∑ u, c u v) ≤ D * μ v) :
    h ^ 2 * (1 / 2 * ∑ u, ∑ v,
        c u v * |f u ^ 4 - f v ^ 4|) ^ 2 ≤
      32 * D * (∑ v, μ v * f v ^ 6) *
        finiteSpatialEnergy c f := by
  let x : V × V → ℝ := fun q =>
    Real.sqrt (c q.1 q.2) * (f q.1 ^ 3 + f q.2 ^ 3)
  let y : V × V → ℝ := fun q =>
    Real.sqrt (c q.1 q.2) * |f q.1 - f q.2|
  have hxy (u v : V) :
      c u v * |f u ^ 4 - f v ^ 4| ≤
        4 * (x (u, v) * y (u, v)) := by
    have hcroot : (Real.sqrt (c u v)) ^ 2 = c u v :=
      Real.sq_sqrt (hc u v)
    have hfactor :
        |f u ^ 4 - f v ^ 4| ≤
          4 * (f u ^ 3 + f v ^ 3) * |f u - f v| := by
      have hid :
          f u ^ 4 - f v ^ 4 =
            (f u - f v) *
              (f u ^ 3 + f u ^ 2 * f v + f u * f v ^ 2 + f v ^ 3) := by
        ring
      rw [hid, abs_mul]
      have hmiddle :
          f u ^ 3 + f u ^ 2 * f v + f u * f v ^ 2 + f v ^ 3 ≤
            4 * (f u ^ 3 + f v ^ 3) := by
        have hcross :=
          mul_nonneg (sq_nonneg (f u - f v))
            (add_nonneg (hf u) (hf v))
        ring_nf at hcross
        nlinarith [mul_nonneg (sq_nonneg (f u)) (hf u),
          mul_nonneg (sq_nonneg (f v)) (hf v)]
      have hpoly : 0 ≤
          f u ^ 3 + f u ^ 2 * f v + f u * f v ^ 2 + f v ^ 3 := by
        exact add_nonneg
          (add_nonneg
            (add_nonneg
              (mul_nonneg (sq_nonneg (f u)) (hf u))
              (mul_nonneg (sq_nonneg (f u)) (hf v)))
            (mul_nonneg (hf u) (sq_nonneg (f v))))
          (mul_nonneg (sq_nonneg (f v)) (hf v))
      rw [abs_of_nonneg hpoly]
      nlinarith [abs_nonneg (f u - f v)]
    unfold x y
    calc
      c u v * |f u ^ 4 - f v ^ 4|
          ≤ c u v *
              (4 * (f u ^ 3 + f v ^ 3) * |f u - f v|) :=
            mul_le_mul_of_nonneg_left hfactor (hc u v)
      _ = 4 * (Real.sqrt (c u v)) ^ 2 *
          (f u ^ 3 + f v ^ 3) * |f u - f v| := by
            rw [hcroot]
            ring
      _ = 4 * ((Real.sqrt (c u v) * (f u ^ 3 + f v ^ 3)) *
          (Real.sqrt (c u v) * |f u - f v|)) := by ring
  have hsum :
      (∑ u, ∑ v, c u v * |f u ^ 4 - f v ^ 4|) ≤
        4 * ∑ q : V × V, x q * y q := by
    calc
      (∑ u, ∑ v, c u v * |f u ^ 4 - f v ^ 4|)
          ≤ ∑ u, ∑ v, 4 * (x (u, v) * y (u, v)) :=
            Finset.sum_le_sum fun u _ =>
              Finset.sum_le_sum fun v _ => hxy u v
      _ = 4 * ∑ q : V × V, x q * y q := by
        rw [← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (V × V)) x y
  have hxsum :
      h ^ 2 * ∑ q : V × V, x q ^ 2 ≤
        4 * D * (∑ v, μ v * f v ^ 6) := by
    have hxpoint (u v : V) :
        x (u, v) ^ 2 ≤
          2 * (c u v * f u ^ 6 + c u v * f v ^ 6) := by
      unfold x
      rw [mul_pow, Real.sq_sqrt (hc u v)]
      have hsquare := sq_nonneg (f u ^ 3 - f v ^ 3)
      have hcmul := mul_nonneg (hc u v) hsquare
      nlinarith
    have hxraw :
        ∑ q : V × V, x q ^ 2 ≤
          4 * ∑ v, (∑ u, c u v) * f v ^ 6 := by
      calc
        (∑ q : V × V, x q ^ 2)
            = ∑ u, ∑ v, x (u, v) ^ 2 := by
                rw [← Finset.univ_product_univ, Finset.sum_product]
        _ ≤ ∑ u, ∑ v,
              2 * (c u v * f u ^ 6 + c u v * f v ^ 6) :=
            Finset.sum_le_sum fun u _ =>
              Finset.sum_le_sum fun v _ => hxpoint u v
        _ = 2 * (∑ u, ∑ v, c u v * f u ^ 6) +
              2 * (∑ u, ∑ v, c u v * f v ^ 6) := by
                calc
                  (∑ u, ∑ v,
                      2 * (c u v * f u ^ 6 + c u v * f v ^ 6))
                      = ∑ u, ∑ v,
                          (2 * (c u v * f u ^ 6) +
                            2 * (c u v * f v ^ 6)) := by
                              apply Finset.sum_congr rfl
                              intro u _
                              apply Finset.sum_congr rfl
                              intro v _
                              ring
                  _ = ∑ u, ((∑ v, 2 * (c u v * f u ^ 6)) +
                        (∑ v, 2 * (c u v * f v ^ 6))) := by
                          apply Finset.sum_congr rfl
                          intro u _
                          rw [Finset.sum_add_distrib]
                  _ = (∑ u, ∑ v, 2 * (c u v * f u ^ 6)) +
                        (∑ u, ∑ v, 2 * (c u v * f v ^ 6)) := by
                          rw [Finset.sum_add_distrib]
                  _ = 2 * (∑ u, ∑ v, c u v * f u ^ 6) +
                        2 * (∑ u, ∑ v, c u v * f v ^ 6) := by
                          apply congrArg₂ (· + ·)
                          · calc
                              (∑ u, ∑ v, 2 * (c u v * f u ^ 6))
                                  = ∑ u, 2 * (∑ v,
                                      c u v * f u ^ 6) := by
                                        apply Finset.sum_congr rfl
                                        intro u _
                                        rw [Finset.mul_sum]
                              _ = 2 * (∑ u, ∑ v,
                                  c u v * f u ^ 6) := by
                                    rw [Finset.mul_sum]
                          · calc
                              (∑ u, ∑ v, 2 * (c u v * f v ^ 6))
                                  = ∑ u, 2 * (∑ v,
                                      c u v * f v ^ 6) := by
                                        apply Finset.sum_congr rfl
                                        intro u _
                                        rw [Finset.mul_sum]
                              _ = 2 * (∑ u, ∑ v,
                                  c u v * f v ^ 6) := by
                                    rw [Finset.mul_sum]
        _ = 4 * ∑ v, (∑ u, c u v) * f v ^ 6 := by
          have hswap :
              (∑ u, ∑ v, c u v * f u ^ 6) =
                ∑ v, (∑ u, c u v) * f v ^ 6 := by
            calc
              (∑ u, ∑ v, c u v * f u ^ 6)
                  = ∑ u, (∑ v, c u v) * f u ^ 6 := by
                      apply Finset.sum_congr rfl
                      intro u _
                      rw [Finset.sum_mul]
              _ = ∑ u, (∑ v, c v u) * f u ^ 6 := by
                    apply Finset.sum_congr rfl
                    intro u _
                    congr 1
                    apply Finset.sum_congr rfl
                    intro v _
                    exact hsym u v
          have hdirect :
              (∑ u, ∑ v, c u v * f v ^ 6) =
                ∑ v, (∑ u, c u v) * f v ^ 6 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_mul]
          rw [hswap, hdirect]
          ring
    calc
      h ^ 2 * ∑ q : V × V, x q ^ 2
          ≤ h ^ 2 * (4 * ∑ v, (∑ u, c u v) * f v ^ 6) :=
            mul_le_mul_of_nonneg_left hxraw (sq_nonneg h)
      _ = 4 * ∑ v, (h ^ 2 * ∑ u, c u v) * f v ^ 6 := by
            calc
              h ^ 2 * (4 * ∑ v, (∑ u, c u v) * f v ^ 6)
                  = ∑ v, h ^ 2 *
                      (4 * ((∑ u, c u v) * f v ^ 6)) := by
                        calc
                          h ^ 2 * (4 * ∑ v,
                              (∑ u, c u v) * f v ^ 6)
                              = (h ^ 2 * 4) * ∑ v,
                                  (∑ u, c u v) * f v ^ 6 := by ring
                          _ = _ := by
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro v _
                            ring
              _ = 4 * ∑ v, (h ^ 2 * ∑ u, c u v) * f v ^ 6 := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro v _
                    ring
      _ ≤ 4 * ∑ v, (D * μ v) * f v ^ 6 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum
            intro v _
            exact mul_le_mul_of_nonneg_right (hdegree v) (by positivity)
      _ = 4 * D * (∑ v, μ v * f v ^ 6) := by
            calc
              4 * ∑ v, (D * μ v) * f v ^ 6
                  = 4 * ∑ v, D * (μ v * f v ^ 6) := by
                      apply congrArg (fun z : ℝ => 4 * z)
                      apply Finset.sum_congr rfl
                      intro v _
                      ring
              _ = 4 * (D * ∑ v, μ v * f v ^ 6) := by
                    congr 1
                    rw [Finset.mul_sum]
              _ = _ := by ring
  have hysum :
      ∑ q : V × V, y q ^ 2 =
        2 * finiteSpatialEnergy c f := by
    unfold y finiteSpatialEnergy
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [mul_pow, Real.sq_sqrt (hc _ _), sq_abs]
    ring
  have hxnonneg : 0 ≤ ∑ q : V × V, x q ^ 2 :=
    Finset.sum_nonneg fun q hq => sq_nonneg _
  have hynonneg : 0 ≤ ∑ q : V × V, y q ^ 2 :=
    Finset.sum_nonneg fun q hq => sq_nonneg _
  have hznonneg : 0 ≤ ∑ q : V × V, x q * y q := by
    apply Finset.sum_nonneg
    intro q hq
    have hfu3 : 0 ≤ f q.1 ^ 3 :=
      pow_nonneg (hf q.1) 3
    have hfv3 : 0 ≤ f q.2 ^ 3 :=
      pow_nonneg (hf q.2) 3
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hfu3 hfv3))
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
  have hsnonneg :
      0 ≤ ∑ u, ∑ v, c u v * |f u ^ 4 - f v ^ 4| :=
    Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv =>
        mul_nonneg (hc u v) (abs_nonneg _)
  have hsq :
      (1 / 2 * ∑ u, ∑ v, c u v * |f u ^ 4 - f v ^ 4|) ^ 2 ≤
        4 * (∑ q : V × V, x q * y q) ^ 2 := by
    nlinarith
  calc
    h ^ 2 * (1 / 2 * ∑ u, ∑ v,
        c u v * |f u ^ 4 - f v ^ 4|) ^ 2
        ≤ h ^ 2 * (4 * (∑ q : V × V, x q * y q) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg h)
    _ ≤ h ^ 2 * (4 * ((∑ q : V × V, x q ^ 2) *
          (∑ q : V × V, y q ^ 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcs (by norm_num))
              (sq_nonneg h)
    _ = 4 * (h ^ 2 * ∑ q : V × V, x q ^ 2) *
          (∑ q : V × V, y q ^ 2) := by ring
    _ ≤ 4 * (4 * D * (∑ v, μ v * f v ^ 6)) *
          (∑ q : V × V, y q ^ 2) := by
            gcongr
    _ = 32 * D * (∑ v, μ v * f v ^ 6) *
          finiteSpatialEnergy c f := by rw [hysum]; ring

/-- On a nonnegative half-volume support, the exact L6 Sobolev bound has
constant 32 D / I squared. -/
theorem finite_half_support_L6_sobolev
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (I D h : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hdegree : ∀ v, h ^ 2 * (∑ u, c u v) ≤ D * μ v)
    (hcut : ∀ A : Finset V,
      A ⊆ finitePositiveSupport f →
      I * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    (∑ v, μ v * f v ^ 6) ≤
      ((32 * D / I ^ 2) * finiteSpatialEnergy c f) ^ 3 := by
  let S : ℝ := ∑ v, μ v * f v ^ 6
  let E : ℝ := finiteSpatialEnergy c f
  have hS : 0 ≤ S := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (by positivity)
  have hE : 0 ≤ E := by
    unfold E finiteSpatialEnergy
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv =>
        mul_nonneg (hc u v) (sq_nonneg _)
  have hg4 : ∀ v, 0 ≤ f v ^ 4 := fun v => by positivity
  have hsupport4 :
      finitePositiveSupport (fun v => f v ^ 4) =
        finitePositiveSupport f := by
    ext v
    simp only [finitePositiveSupport, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hp
      by_contra hn
      have hz : f v = 0 := le_antisymm (le_of_not_gt hn) (hf v)
      simp [hz] at hp
    · intro hp
      exact pow_pos hp 4
  have hcut4 : ∀ A : Finset V,
      A ⊆ finitePositiveSupport (fun v => f v ^ 4) →
      I * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A := by
    intro A hA
    apply hcut A
    simpa [hsupport4] using hA
  have hcoarea := finite_coarea_sobolev_three_halves
    μ hμ c hc hsym (fun v => f v ^ 4) hg4 I h hI.le hh.le hcut4
  have hnorm :
      weightedLThreeHalves μ (fun v => f v ^ 4) = S ^ ((2 : ℝ) / 3) := by
    unfold weightedLThreeHalves S
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    change μ v * (f v ^ 4 : ℝ) ^ ((3 : ℝ) / 2) =
      μ v * f v ^ 6
    congr 1
    calc
      (f v ^ (4 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
          = (f v ^ (4 : ℝ)) ^ ((3 : ℝ) / 2) :=
              congrArg (fun z : ℝ => z ^ ((3 : ℝ) / 2))
                (Real.rpow_natCast (f v) 4).symm
      _ = f v ^ ((4 : ℝ) * ((3 : ℝ) / 2)) := by
            exact (Real.rpow_mul (hf v) (4 : ℝ) ((3 : ℝ) / 2)).symm
      _ = f v ^ (6 : ℝ) := by norm_num
      _ = f v ^ (6 : ℕ) := Real.rpow_natCast (f v) 6
  have hedge := fourth_power_edge_variation_sq
    μ hμ c hc hsym f hf D h hD hh hdegree
  rw [hnorm] at hcoarea
  change h ^ 2 * (1 / 2 * ∑ u, ∑ v,
      c u v * |f u ^ 4 - f v ^ 4|) ^ 2 ≤ 32 * D * S * E at hedge
  have hcoaSq :
      I ^ 2 * (S ^ ((2 : ℝ) / 3)) ^ 2 ≤
        h ^ 2 * (1 / 2 * ∑ u, ∑ v,
          c u v * |f u ^ 4 - f v ^ 4|) ^ 2 := by
    let R : ℝ := S ^ ((2 : ℝ) / 3)
    let Z : ℝ := ∑ u, ∑ v, c u v * |f u ^ 4 - f v ^ 4|
    have hR : 0 ≤ R := Real.rpow_nonneg hS _
    have hZ : 0 ≤ Z := Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv =>
        mul_nonneg (hc u v) (abs_nonneg _)
    have hleft : 0 ≤ I * R := mul_nonneg hI.le hR
    have hright : 0 ≤ h / 2 * Z :=
      mul_nonneg (div_nonneg hh.le (by norm_num)) hZ
    change I * R ≤ h / 2 * Z at hcoarea
    change I ^ 2 * R ^ 2 ≤ h ^ 2 * (1 / 2 * Z) ^ 2
    have hsquare := (sq_le_sq₀ hleft hright).2 hcoarea
    nlinarith
  have hmain :
      I ^ 2 * (S ^ ((2 : ℝ) / 3)) ^ 2 ≤ 32 * D * S * E :=
    hcoaSq.trans hedge
  by_cases hS0 : S = 0
  · change S ≤ ((32 * D / I ^ 2) * E) ^ 3
    rw [hS0]
    exact pow_nonneg (by positivity) 3
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hpow : (S ^ ((2 : ℝ) / 3)) ^ 2 = S * S ^ ((1 : ℝ) / 3) := by
      calc
        (S ^ ((2 : ℝ) / 3)) ^ (2 : ℕ)
            = (S ^ ((2 : ℝ) / 3)) ^ (2 : ℝ) :=
                (Real.rpow_natCast (S ^ ((2 : ℝ) / 3)) 2).symm
        _ = S ^ (((2 : ℝ) / 3) * (2 : ℝ)) :=
              (Real.rpow_mul hS ((2 : ℝ) / 3) 2).symm
        _ = S ^ (1 + ((1 : ℝ) / 3)) := by norm_num
        _ = S * S ^ ((1 : ℝ) / 3) := by
              rw [Real.rpow_add hSpos, Real.rpow_one]
    rw [hpow] at hmain
    have hroot :
        I ^ 2 * S ^ ((1 : ℝ) / 3) ≤ 32 * D * E := by
      nlinarith
    have hrootBound :
        S ^ ((1 : ℝ) / 3) ≤ (32 * D / I ^ 2) * E := by
      have hI2 : 0 < I ^ 2 := sq_pos_of_pos hI
      calc
        S ^ ((1 : ℝ) / 3) ≤ (32 * D * E) / I ^ 2 := by
          apply (le_div_iff₀ hI2).2
          nlinarith
        _ = (32 * D / I ^ 2) * E := by ring
    have hrhs : 0 ≤ (32 * D / I ^ 2) * E := by positivity
    have hcubed := pow_le_pow_left₀ (Real.rpow_nonneg hS _) hrootBound 3
    rw [← Real.rpow_mul_natCast hS ((1 : ℝ) / 3) 3] at hcubed
    norm_num at hcubed
    exact hcubed

/-- A weighted median certificate records that both strict sides of a level
carry at most half of the total mass. -/
structure FiniteWeightedMedianCertificate
    {V : Type*} [Fintype V] (μ f : V → ℝ) where
  value : ℝ
  lower_mass :
    2 * (∑ v ∈ Finset.univ.filter (fun v => f v < value), μ v) ≤ ∑ v, μ v
  upper_mass :
    2 * (∑ v ∈ Finset.univ.filter (fun v => value < f v), μ v) ≤ ∑ v, μ v

/-- Every real function on a nonempty finite weighted space with nonnegative
weights has a weighted median.  The proof chooses the first value whose
lower cumulative mass reaches one half. -/
theorem finite_weightedMedian_exists
    {V : Type*} [Fintype V] [Nonempty V]
    (μ f : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) :
    Nonempty (FiniteWeightedMedianCertificate μ f) := by
  classical
  let T : ℝ := ∑ v, μ v
  let lower : V → ℝ := fun v =>
    ∑ u ∈ Finset.univ.filter (fun u => f u ≤ f v), μ u
  let candidates : Finset V :=
    Finset.univ.filter (fun v => T ≤ 2 * lower v)
  have hT : 0 ≤ T := Finset.sum_nonneg fun v hv => hμ v
  obtain ⟨vmax, hvmax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) f Finset.univ_nonempty
  have hlowerMax : lower vmax = T := by
    unfold lower T
    rw [Finset.filter_eq_self.2]
    intro u hu
    exact hmax u (Finset.mem_univ u)
  have hvmaxCandidate : vmax ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ vmax, ?_⟩
    rw [hlowerMax]
    linarith
  have hcandidates : candidates.Nonempty := ⟨vmax, hvmaxCandidate⟩
  obtain ⟨vm, hvm, hmin⟩ :=
    Finset.exists_min_image candidates f hcandidates
  refine ⟨{
    value := f vm
    lower_mass := ?_
    upper_mass := ?_ }⟩
  · let L : Finset V := Finset.univ.filter (fun u => f u < f vm)
    by_contra hnot
    have hlarge : T < 2 * ∑ u ∈ L, μ u := lt_of_not_ge hnot
    have hLpos : 0 < ∑ u ∈ L, μ u := by linarith
    have hLnonempty : L.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hLpos
      simp at hLpos
    obtain ⟨u0, hu0L, hu0max⟩ := Finset.exists_max_image L f hLnonempty
    have hu0lt : f u0 < f vm :=
      (Finset.mem_filter.mp hu0L).2
    have hfilter :
        Finset.univ.filter (fun u => f u ≤ f u0) = L := by
      ext u
      constructor
      · intro hu
        have hle := (Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ u, hle.trans_lt hu0lt⟩
      · intro hu
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ u, hu0max u hu⟩
    have hu0Candidate : u0 ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u0, ?_⟩
      unfold lower
      rw [hfilter]
      exact hlarge.le
    have := hmin u0 hu0Candidate
    linarith
  · have hvmCandidate := (Finset.mem_filter.mp hvm).2
    let A : Finset V := Finset.univ.filter (fun u => f u ≤ f vm)
    let B : Finset V := Finset.univ.filter (fun u => f vm < f u)
    have hpartition : (∑ u ∈ A, μ u) + (∑ u ∈ B, μ u) = T := by
      unfold A B T
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset V) (fun u => f u ≤ f vm) μ]
      simp only [not_le]
    change T ≤ 2 * lower vm at hvmCandidate
    have hlower : lower vm = ∑ u ∈ A, μ u := by rfl
    rw [hlower] at hvmCandidate
    change 2 * (∑ u ∈ B, μ u) ≤ T
    linarith

/-- A global isoperimetric cut inequality restricts to the ordinary
mass^(2/3) inequality on every subset of a half-volume support. -/
theorem finite_cut_bound_on_half_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (g : V → ℝ)
    (I h : ℝ) (hI : 0 ≤ I)
    (hsupport :
      2 * (∑ v ∈ finitePositiveSupport g, μ v) ≤ ∑ v, μ v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, μ v) (∑ v ∈ Aᶜ, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    ∀ A : Finset V, A ⊆ finitePositiveSupport g →
      I * (∑ v ∈ A, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A := by
  classical
  intro A hA
  have hmassA : ∑ v ∈ A, μ v ≤ ∑ v ∈ finitePositiveSupport g, μ v :=
    Finset.sum_le_sum_of_subset_of_nonneg hA fun v hvA hvS => hμ v
  have hpartition :
      (∑ v ∈ A, μ v) + (∑ v ∈ Aᶜ, μ v) = ∑ v, μ v := by
    have hp := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset V) (fun v => v ∈ A) μ
    have hcomp : Aᶜ = Finset.univ.filter (fun v => ¬ v ∈ A) := by
      ext v
      simp
    rw [hcomp]
    simpa using hp
  have hhalf : ∑ v ∈ A, μ v ≤ ∑ v ∈ Aᶜ, μ v := by
    linarith
  simpa [min_eq_left hhalf] using hcut A

/-- Translation does not change the finite spatial Dirichlet energy. -/
theorem finiteSpatialEnergy_sub_const
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (f : V → ℝ) (a : ℝ) :
    finiteSpatialEnergy c (fun v => f v - a) = finiteSpatialEnergy c f := by
  unfold finiteSpatialEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Taking the positive part contracts every edge and hence the spatial
Dirichlet energy. -/
theorem finiteSpatialEnergy_posPart_le
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (f : V → ℝ) :
    finiteSpatialEnergy c (fun v => max (f v) 0) ≤ finiteSpatialEnergy c f := by
  unfold finiteSpatialEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (hc u v)
  have habs : |max (f u) 0 - max (f v) 0| ≤ |f u - f v| := by
    exact abs_sup_sub_sup_le_abs (f u) (f v) 0
  have hsquare := pow_le_pow_left₀ (abs_nonneg _) habs 2
  simpa [sq_abs] using hsquare

/-- Positive and negative parts split an even sixth power exactly. -/
theorem sixth_power_pos_neg_split (x : ℝ) :
    x ^ 6 = (max x 0) ^ 6 + (max (-x) 0) ^ 6 := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- Positive and negative truncations split edge energy without loss. -/
theorem finiteSpatialEnergy_pos_neg_sum_le
    {V : Type*} [Fintype V]
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (f : V → ℝ) :
    finiteSpatialEnergy c (fun v => max (f v) 0) +
      finiteSpatialEnergy c (fun v => max (-f v) 0) ≤
        finiteSpatialEnergy c f := by
  have hedge (x y : ℝ) :
      (max x 0 - max y 0) ^ 2 +
          (max (-x) 0 - max (-y) 0) ^ 2 ≤ (x - y) ^ 2 := by
    rcases le_total x 0 with hx | hx <;>
      rcases le_total y 0 with hy | hy
    · simp [max_eq_right hx, max_eq_right hy,
        max_eq_left (neg_nonneg.mpr hx), max_eq_left (neg_nonneg.mpr hy)]
      nlinarith
    · simp [max_eq_right hx, max_eq_left hy,
        max_eq_left (neg_nonneg.mpr hx), max_eq_right (neg_nonpos.mpr hy)]
      nlinarith
    · simp [max_eq_left hx, max_eq_right hy,
        max_eq_right (neg_nonpos.mpr hx), max_eq_left (neg_nonneg.mpr hy)]
      nlinarith
    · simp [max_eq_left hx, max_eq_left hy,
        max_eq_right (neg_nonpos.mpr hx), max_eq_right (neg_nonpos.mpr hy)]
  unfold finiteSpatialEnergy
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (hedge (f u) (f v)) (hc u v)

/-- Sixth-moment Sobolev estimate for a function centered at any weighted
median.  The constant remains 32 D / I squared because the two truncation
energies add to at most the original energy. -/
theorem finite_weightedMedian_centered_L6_sobolev
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (f : V → ℝ) (M : FiniteWeightedMedianCertificate μ f)
    (I D h : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hdegree : ∀ v, h ^ 2 * (∑ u, c u v) ≤ D * μ v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, μ v) (∑ v ∈ Aᶜ, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    (∑ v, μ v * (f v - M.value) ^ 6) ≤
      ((32 * D / I ^ 2) * finiteSpatialEnergy c f) ^ 3 := by
  let g : V → ℝ := fun v => f v - M.value
  let p : V → ℝ := fun v => max (g v) 0
  let n : V → ℝ := fun v => max (-g v) 0
  let C : ℝ := 32 * D / I ^ 2
  let Ep : ℝ := finiteSpatialEnergy c p
  let En : ℝ := finiteSpatialEnergy c n
  let E : ℝ := finiteSpatialEnergy c f
  have hpnonneg : ∀ v, 0 ≤ p v := fun v => by
    unfold p
    exact le_max_right _ _
  have hnnonneg : ∀ v, 0 ≤ n v := fun v => by
    unfold n
    exact le_max_right _ _
  have hsupportp :
      finitePositiveSupport p =
        Finset.univ.filter (fun v => M.value < f v) := by
    ext v
    simp [finitePositiveSupport, p, g, sub_pos]
  have hsupportn :
      finitePositiveSupport n =
        Finset.univ.filter (fun v => f v < M.value) := by
    ext v
    simp [finitePositiveSupport, n, g, sub_pos]
  have hhalfp : 2 * (∑ v ∈ finitePositiveSupport p, μ v) ≤ ∑ v, μ v := by
    rw [hsupportp]
    exact M.upper_mass
  have hhalfn : 2 * (∑ v ∈ finitePositiveSupport n, μ v) ≤ ∑ v, μ v := by
    rw [hsupportn]
    exact M.lower_mass
  have hcutp := finite_cut_bound_on_half_support
    μ hμ c p I h hI.le hhalfp hcut
  have hcutn := finite_cut_bound_on_half_support
    μ hμ c n I h hI.le hhalfn hcut
  have hpbound := finite_half_support_L6_sobolev
    μ hμ c hc hsym p hpnonneg I D h hI hD hh hdegree hcutp
  have hnbound := finite_half_support_L6_sobolev
    μ hμ c hc hsym n hnnonneg I D h hI hD hh hdegree hcutn
  change (∑ v, μ v * p v ^ 6) ≤ (C * Ep) ^ 3 at hpbound
  change (∑ v, μ v * n v ^ 6) ≤ (C * En) ^ 3 at hnbound
  have hC : 0 ≤ C := by
    unfold C
    positivity
  have hEp : 0 ≤ Ep := by
    unfold Ep finiteSpatialEnergy
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv =>
        mul_nonneg (hc u v) (sq_nonneg _)
  have hEn : 0 ≤ En := by
    unfold En finiteSpatialEnergy
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv =>
        mul_nonneg (hc u v) (sq_nonneg _)
  have henergy : Ep + En ≤ E := by
    unfold Ep En E p n
    calc
      finiteSpatialEnergy c (fun v => max (g v) 0) +
            finiteSpatialEnergy c (fun v => max (-g v) 0)
          ≤ finiteSpatialEnergy c g :=
            finiteSpatialEnergy_pos_neg_sum_le c hc g
      _ = finiteSpatialEnergy c f := by
            unfold g
            exact finiteSpatialEnergy_sub_const c f M.value
  have hsplit :
      (∑ v, μ v * (f v - M.value) ^ 6) =
        (∑ v, μ v * p v ^ 6) + (∑ v, μ v * n v ^ 6) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [← mul_add]
    unfold p n g
    rw [← sixth_power_pos_neg_split (f v - M.value)]
  rw [hsplit]
  calc
    (∑ v, μ v * p v ^ 6) + (∑ v, μ v * n v ^ 6)
        ≤ (C * Ep) ^ 3 + (C * En) ^ 3 := add_le_add hpbound hnbound
    _ ≤ (C * (Ep + En)) ^ 3 := by
      have hcross : 0 ≤ 3 * (C * Ep) * (C * En) *
          ((C * Ep) + (C * En)) := by positivity
      nlinarith
    _ ≤ (C * E) ^ 3 := by
      apply pow_le_pow_left₀ (mul_nonneg hC (add_nonneg hEp hEn)) _ 3
      exact mul_le_mul_of_nonneg_left henergy hC

/-- Weighted Cauchy-Schwarz for the mean functional. -/
theorem weighted_sum_sq_le_mass_mul_l2
    {V : Type*} [Fintype V]
    (μ x : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) :
    (∑ v, μ v * x v) ^ 2 ≤
      (∑ v, μ v) * (∑ v, μ v * x v ^ 2) := by
  let w : V → ℝ := fun v => Real.sqrt (μ v)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
    (fun v => w v) (fun v => w v * x v)
  calc
    (∑ v, μ v * x v) ^ 2
        = (∑ v, w v * (w v * x v)) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro v _
          rw [show w v * (w v * x v) = w v ^ 2 * x v by ring,
            Real.sq_sqrt (hμ v)]
    _ ≤ (∑ v, w v ^ 2) * (∑ v, (w v * x v) ^ 2) := hcs
    _ = (∑ v, μ v) * (∑ v, μ v * x v ^ 2) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro v _
        exact Real.sq_sqrt (hμ v)
      · apply Finset.sum_congr rfl
        intro v _
        rw [mul_pow, Real.sq_sqrt (hμ v)]

/-- Shifting a mean-zero function back from any constant center costs at
most a factor 64 in the sixth moment, equivalently a factor four in the
squared L6 norm. -/
theorem meanZero_shift_sixth_moment_le
    {V : Type*} [Fintype V]
    (μ f : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (a : ℝ) (hmean : ∑ v, μ v * f v = 0) :
    (∑ v, μ v * f v ^ 6) ≤
      64 * (∑ v, μ v * (f v - a) ^ 6) := by
  let x : V → ℝ := fun v => f v - a
  let T : ℝ := ∑ v, μ v
  let Q : ℝ := ∑ v, μ v * x v ^ 2
  let S : ℝ := ∑ v, μ v * x v ^ 6
  have hT : 0 ≤ T := Finset.sum_nonneg fun v hv => hμ v
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (by positivity)
  have hsumx : ∑ v, μ v * x v = -a * T := by
    unfold x T
    calc
      (∑ v, μ v * (f v - a))
          = (∑ v, μ v * f v) - a * ∑ v, μ v := by
            have hterm : ∀ v, μ v * (f v - a) = μ v * f v - μ v * a := by
              intro v
              ring
            simp_rw [hterm]
            rw [Finset.sum_sub_distrib]
            congr 1
            calc
              (∑ v, μ v * a) = ∑ v, a * μ v := by
                apply Finset.sum_congr rfl
                intro v _
                ring
              _ = a * ∑ v, μ v := by rw [Finset.mul_sum]
      _ = -a * ∑ v, μ v := by rw [hmean]; ring
  have hCS := weighted_sum_sq_le_mass_mul_l2 μ x hμ
  change (∑ v, μ v * x v) ^ 2 ≤ T * Q at hCS
  rw [hsumx] at hCS
  have hholder := holder_l2_l6_cube μ x hμ
  change Q ^ 3 ≤ S * T ^ 2 at hholder
  have ha6T : a ^ 6 * T ^ 3 ≤ Q ^ 3 := by
    have hsq : a ^ 2 * T ^ 2 ≤ T * Q := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hT
    have hbase : a ^ 2 * T ≤ Q := by
      by_cases hT0 : T = 0
      · simp [hT0, hQ]
      · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
        nlinarith
    have hcubed := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hT) hbase 3
    have hid : (a ^ 2 * T) ^ 3 = a ^ 6 * T ^ 3 := by
      rw [mul_pow]
      congr 1
      ring
    rw [hid] at hcubed
    exact hcubed
  have ha6mass : a ^ 6 * T ≤ S := by
    by_cases hT0 : T = 0
    · simp [hT0, hS]
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hchain : a ^ 6 * T ^ 3 ≤ S * T ^ 2 := ha6T.trans hholder
      nlinarith [sq_pos_of_pos hTpos]
  calc
    (∑ v, μ v * f v ^ 6)
        = ∑ v, μ v * (x v + a) ^ 6 := by
          apply Finset.sum_congr rfl
          intro v _
          unfold x
          congr 1
          ring
    _ ≤ ∑ v, μ v * (32 * (x v ^ 6 + a ^ 6)) := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (hμ v)
      have hadd := add_pow_le (abs_nonneg (x v)) (abs_nonneg a) 6
      calc
        (x v + a) ^ 6 = (|x v + a|) ^ 6 := by
          rw [Even.pow_abs (even_iff_two_dvd.mpr ⟨3, by norm_num⟩)]
        _ ≤ (|x v| + |a|) ^ 6 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 6
        _ ≤ 2 ^ (6 - 1) * (|x v| ^ 6 + |a| ^ 6) := hadd
        _ = 32 * (x v ^ 6 + a ^ 6) := by
          rw [Even.pow_abs (even_iff_two_dvd.mpr ⟨3, by norm_num⟩),
            Even.pow_abs (even_iff_two_dvd.mpr ⟨3, by norm_num⟩)]
          norm_num
    _ = 32 * (S + a ^ 6 * T) := by
      unfold S T
      calc
        (∑ v, μ v * (32 * (x v ^ 6 + a ^ 6)))
            = 32 * ∑ v, μ v * (x v ^ 6 + a ^ 6) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              ring
        _ = 32 * ((∑ v, μ v * x v ^ 6) + ∑ v, μ v * a ^ 6) := by
          congr 1
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = 32 * ((∑ v, μ v * x v ^ 6) + a ^ 6 * ∑ v, μ v) := by
          congr 2
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
    _ ≤ 32 * (S + S) := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl S) ha6mass) (by norm_num)
    _ = 64 * S := by ring

/-- The exact mean-zero finite Sobolev inequality with the manuscript
constant `C_S = 128 D / I²`. -/
theorem finite_meanZero_L6_sobolev
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (f : V → ℝ) (hmean : ∑ v, μ v * f v = 0)
    (I D h : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hdegree : ∀ v, h ^ 2 * (∑ u, c u v) ≤ D * μ v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, μ v) (∑ v ∈ Aᶜ, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    (∑ v, μ v * f v ^ 6) ≤
      ((128 * D / I ^ 2) * finiteSpatialEnergy c f) ^ 3 := by
  obtain ⟨M⟩ := finite_weightedMedian_exists μ f hμ
  have hcenter := finite_weightedMedian_centered_L6_sobolev
    μ hμ c hc hsym f M I D h hI hD hh hdegree hcut
  have hshift := meanZero_shift_sixth_moment_le μ f hμ M.value hmean
  calc
    (∑ v, μ v * f v ^ 6)
        ≤ 64 * (∑ v, μ v * (f v - M.value) ^ 6) := hshift
    _ ≤ 64 * (((32 * D / I ^ 2) * finiteSpatialEnergy c f) ^ 3) :=
      mul_le_mul_of_nonneg_left hcenter (by norm_num)
    _ = ((128 * D / I ^ 2) * finiteSpatialEnergy c f) ^ 3 := by ring

/-- The exact Poincare estimate obtained from the Sobolev inequality and a
uniform volume bound. -/
theorem finite_meanZero_poincare
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v)
    (hsym : ∀ u v, c u v = c v u)
    (f : V → ℝ) (hmean : ∑ v, μ v * f v = 0)
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : ∑ v, μ v ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, c u v) ≤ D * μ v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, μ v) (∑ v ∈ Aᶜ, μ v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity c A) :
    (∑ v, μ v * f v ^ 2) ≤
      (128 * D * Vstar ^ ((2 : ℝ) / 3) / I ^ 2) *
        finiteSpatialEnergy c f := by
  let CS : ℝ := 128 * D / I ^ 2
  let E : ℝ := finiteSpatialEnergy c f
  let A : ℝ := ∑ v, μ v * f v ^ 2
  let K : ℝ := (128 * D * Vstar ^ ((2 : ℝ) / 3) / I ^ 2) * E
  have hsob := finite_meanZero_L6_sobolev
    μ hμ c hc hsym f hmean I D h hI hD hh hdegree hcut
  change (∑ v, μ v * f v ^ 6) ≤ (CS * E) ^ 3 at hsob
  have hcube := poincare_from_sobolev_cube μ f hμ CS E Vstar
    hVstar hsob hvolume
  change A ^ 3 ≤ (CS * E) ^ 3 * Vstar ^ 2 at hcube
  have hA : 0 ≤ A := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (sq_nonneg _)
  have hE : 0 ≤ E := by
    unfold E finiteSpatialEnergy
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u hu =>
      Finset.sum_nonneg fun v hv => mul_nonneg (hc u v) (sq_nonneg _)
  have hCS : 0 ≤ CS := by unfold CS; positivity
  have hVpow : 0 ≤ Vstar ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hVstar _
  have hK : 0 ≤ K := by
    unfold K
    positivity
  have hVidentity : (Vstar ^ ((2 : ℝ) / 3)) ^ 3 = Vstar ^ 2 := by
    calc
      (Vstar ^ ((2 : ℝ) / 3)) ^ (3 : ℕ)
          = Vstar ^ (((2 : ℝ) / 3) * (3 : ℝ)) := by
              rw [← Real.rpow_natCast]
              exact (Real.rpow_mul hVstar ((2 : ℝ) / 3) 3).symm
      _ = Vstar ^ (2 : ℝ) := by norm_num
      _ = Vstar ^ (2 : ℕ) := Real.rpow_natCast Vstar 2
  have hKid : K ^ 3 = (CS * E) ^ 3 * Vstar ^ 2 := by
    unfold K CS
    rw [show 128 * D * Vstar ^ ((2 : ℝ) / 3) / I ^ 2 * E =
        (128 * D / I ^ 2 * E) * Vstar ^ ((2 : ℝ) / 3) by ring,
      mul_pow, hVidentity]
  rw [← hKid] at hcube
  exact (Odd.pow_le_pow (by decide : Odd 3)).mp hcube

/-- A Poincare inequality gives the advertised Rayleigh spectral floor for
every nonzero mean-zero eigenmode. -/
theorem finite_meanZero_eigenvalue_floor
    {V : Type*} [Fintype V]
    (μ : V → ℝ) (hμ : ∀ v, 0 ≤ μ v)
    (c : V → V → ℝ) (f : V → ℝ) (lam CP : ℝ)
    (hCP : 0 < CP)
    (hnorm : 0 < ∑ v, μ v * f v ^ 2)
    (hpoincare : ∑ v, μ v * f v ^ 2 ≤ CP * finiteSpatialEnergy c f)
    (heigen : finiteSpatialEnergy c f = lam * ∑ v, μ v * f v ^ 2) :
    1 / CP ≤ lam := by
  rw [heigen] at hpoincare
  have hcancel : 1 ≤ CP * lam := by
    have := hpoincare
    nlinarith
  exact (div_le_iff₀ hCP).2 (by simpa [mul_comm] using hcancel)

/-- Exact finite weighted interpolation between L1 and L6, in the
division-free fifth-power form used by Nash's argument. -/
theorem weighted_L1_L6_interpolation_fifth
    {V : Type*} [Fintype V]
    (μ f : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) :
    (∑ v, μ v * f v ^ 2) ^ 5 ≤
      (∑ v, μ v * |f v|) ^ 4 * (∑ v, μ v * f v ^ 6) := by
  let w : V → ℝ := fun v => μ v * |f v|
  let g : V → ℝ := fun v => |f v|
  have hw : ∀ v, 0 ≤ w v := fun v => mul_nonneg (hμ v) (abs_nonneg _)
  have hg : ∀ v, 0 ≤ g v := fun v => abs_nonneg _
  have hinterp := Real.inner_le_weight_mul_Lp_of_nonneg
    (Finset.univ : Finset V) (p := (5 : ℝ)) (by norm_num) w g hw hg
  have hL1 : 0 ≤ ∑ v, μ v * |f v| := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (abs_nonneg _)
  have hL2 : 0 ≤ ∑ v, μ v * f v ^ 2 := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (sq_nonneg _)
  have hL6 : 0 ≤ ∑ v, μ v * f v ^ 6 := Finset.sum_nonneg fun v hv =>
    mul_nonneg (hμ v) (by positivity)
  have hnormalized :
      (∑ v, μ v * f v ^ 2) ≤
        (∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
          (∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5) := by
    unfold w g at hinterp
    norm_num at hinterp
    have hleft :
        (∑ v, μ v * |f v| * |f v|) = ∑ v, μ v * f v ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      calc
        μ v * |f v| * |f v| = μ v * |f v| ^ 2 := by ring
        _ = μ v * f v ^ 2 := by rw [sq_abs]
    have hsixth :
        (∑ v, μ v * |f v| * |f v| ^ (5 : ℝ)) =
          ∑ v, μ v * f v ^ 6 := by
      apply Finset.sum_congr rfl
      intro v _
      have hp : |f v| ^ (5 : ℝ) = |f v| ^ (5 : ℕ) :=
        Real.rpow_natCast (|f v|) 5
      calc
        μ v * |f v| * |f v| ^ (5 : ℝ)
            = μ v * |f v| * |f v| ^ (5 : ℕ) := by rw [hp]
        _ = μ v * |f v| ^ 6 := by ring
        _ = μ v * f v ^ 6 := by
              rw [Even.pow_abs (by decide : Even 6)]
    have hsixthNat :
        (∑ v, μ v * |f v| * |f v| ^ (5 : ℕ)) =
          ∑ v, μ v * f v ^ 6 := by
      apply Finset.sum_congr rfl
      intro v _
      calc
        μ v * |f v| * |f v| ^ (5 : ℕ)
            = μ v * |f v| ^ 6 := by ring
        _ = μ v * f v ^ 6 := by
              rw [Even.pow_abs (by decide : Even 6)]
    calc
      (∑ v, μ v * f v ^ 2)
          = ∑ v, μ v * |f v| * |f v| := hleft.symm
      _ ≤ (∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
          (∑ v, μ v * |f v| * |f v| ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := hinterp
      _ = (∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
          (∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5) := by
            exact congrArg
              (fun z : ℝ => (∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
                z ^ ((1 : ℝ) / 5)) hsixthNat
  have hpow := pow_le_pow_left₀ hL2 hnormalized 5
  have hprod_nonneg :
      0 ≤ (∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
        (∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5) := by positivity
  calc
    (∑ v, μ v * f v ^ 2) ^ 5
        ≤ ((∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5) *
          (∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5)) ^ 5 := hpow
    _ = (∑ v, μ v * |f v|) ^ 4 * (∑ v, μ v * f v ^ 6) := by
      rw [mul_pow]
      have h1 : ((∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) =
          (∑ v, μ v * |f v|) ^ 4 := by
        rw [← Real.rpow_natCast]
        calc
          ((∑ v, μ v * |f v|) ^ ((4 : ℝ) / 5)) ^ (5 : ℝ)
              = (∑ v, μ v * |f v|) ^ (((4 : ℝ) / 5) * 5) :=
                (Real.rpow_mul hL1 _ _).symm
          _ = (∑ v, μ v * |f v|) ^ (4 : ℝ) := by norm_num
          _ = (∑ v, μ v * |f v|) ^ (4 : ℕ) := Real.rpow_natCast _ 4
      have h2 : ((∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) =
          ∑ v, μ v * f v ^ 6 := by
        rw [← Real.rpow_natCast]
        calc
          ((∑ v, μ v * f v ^ 6) ^ ((1 : ℝ) / 5)) ^ (5 : ℝ)
              = (∑ v, μ v * f v ^ 6) ^ (((1 : ℝ) / 5) * 5) :=
                (Real.rpow_mul hL6 _ _).symm
          _ = (∑ v, μ v * f v ^ 6) := by norm_num
      rw [h1, h2]

/-- Sobolev immediately implies the polynomial Nash inequality. -/
theorem finite_nash_cube_from_sobolev
    {V : Type*} [Fintype V]
    (μ f : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) (CS E : ℝ)
    (hsob : ∑ v, μ v * f v ^ 6 ≤ (CS * E) ^ 3) :
    (∑ v, μ v * f v ^ 2) ^ 5 ≤
      (CS * E) ^ 3 * (∑ v, μ v * |f v|) ^ 4 := by
  calc
    (∑ v, μ v * f v ^ 2) ^ 5
        ≤ (∑ v, μ v * |f v|) ^ 4 * (∑ v, μ v * f v ^ 6) :=
          weighted_L1_L6_interpolation_fifth μ f hμ
    _ ≤ (∑ v, μ v * |f v|) ^ 4 * (CS * E) ^ 3 :=
      mul_le_mul_of_nonneg_left hsob (by positivity)
    _ = (CS * E) ^ 3 * (∑ v, μ v * |f v|) ^ 4 := by ring

/-- Real-power form of the Nash inequality used by the heat differential
argument.  This is the exact cube root of `finite_nash_cube_from_sobolev`. -/
theorem finite_nash_from_sobolev
    {V : Type*} [Fintype V]
    (μ f : V → ℝ) (hμ : ∀ v, 0 ≤ μ v) (CS E : ℝ)
    (hCS : 0 ≤ CS) (hE : 0 ≤ E)
    (hsob : ∑ v, μ v * f v ^ 6 ≤ (CS * E) ^ 3) :
    (∑ v, μ v * f v ^ 2) ^ (5 / 3 : ℝ) ≤
      CS * E * (∑ v, μ v * |f v|) ^ (4 / 3 : ℝ) := by
  let A : ℝ := ∑ v, μ v * f v ^ 2
  let L : ℝ := ∑ v, μ v * |f v|
  have hA : 0 ≤ A := Finset.sum_nonneg fun v _ =>
    mul_nonneg (hμ v) (sq_nonneg _)
  have hL : 0 ≤ L := Finset.sum_nonneg fun v _ =>
    mul_nonneg (hμ v) (abs_nonneg _)
  have hcube := finite_nash_cube_from_sobolev μ f hμ CS E hsob
  change A ^ 5 ≤ (CS * E) ^ 3 * L ^ 4 at hcube
  have hlhs : (A ^ (5 / 3 : ℝ)) ^ (3 : ℕ) = A ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have hLpow : (L ^ (4 / 3 : ℝ)) ^ (3 : ℕ) = L ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  have hrhs : (CS * E * L ^ (4 / 3 : ℝ)) ^ (3 : ℕ) =
      (CS * E) ^ 3 * L ^ 4 := by
    rw [mul_pow, hLpow]
  rw [← hlhs, ← hrhs] at hcube
  exact (Odd.pow_le_pow (by decide : Odd 3)).mp hcube

/-- Number of eigenvalues in a closed interval `[0,R]`. -/
def finiteEigenvalueCount
    {J : Type*} [Fintype J] (lam : J → ℝ) (R : ℝ) : ℕ :=
  (Finset.univ.filter fun j => lam j ≤ R).card

/-- Positive-sector heat trace of a finite nonnegative spectrum. -/
def finitePositiveHeatTrace
    {J : Type*} [Fintype J] (lam : J → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < lam j), Real.exp (-t * lam j)

/-- At most one zero mode separates the full counting function from the
strictly positive counting function. -/
theorem finite_count_le_one_add_positive_count
    {J : Type*} [Fintype J]
    (lam : J → ℝ) (R : ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hzero : (Finset.univ.filter fun j => lam j = 0).card ≤ 1) :
    finiteEigenvalueCount lam R ≤
      1 + (Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R).card := by
  classical
  let Z : Finset J := Finset.univ.filter fun j => lam j = 0
  let P : Finset J := Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R
  let N : Finset J := Finset.univ.filter fun j => lam j ≤ R
  have hsubset : N ⊆ Z ∪ P := by
    intro j hj
    have hjR : lam j ≤ R := (Finset.mem_filter.mp hj).2
    rcases (hlam j).eq_or_lt with hz | hp
    · exact Finset.mem_union_left P (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hz.symm⟩)
    · exact Finset.mem_union_right Z
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp, hjR⟩)
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le Z P
  change N.card ≤ 1 + P.card
  calc
    N.card ≤ (Z ∪ P).card := hcard
    _ ≤ Z.card + P.card := hunion
    _ ≤ 1 + P.card := Nat.add_le_add_right hzero P.card

/-- The elementary heat-trace bound on the number of positive eigenvalues
below `R`. -/
theorem positive_count_le_exp_mul_heatTrace
    {J : Type*} [Fintype J]
    (lam : J → ℝ) (R t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R).card : ℝ) ≤
      Real.exp (t * R) * finitePositiveHeatTrace lam t := by
  classical
  let P : Finset J := Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R
  have hpoint (j : J) (hj : j ∈ P) :
      (1 : ℝ) ≤ Real.exp (t * R) * Real.exp (-t * lam j) := by
    have hjR : lam j ≤ R := (Finset.mem_filter.mp hj).2.2
    rw [← Real.exp_add]
    have hexp : 1 ≤ Real.exp (t * R + -t * lam j) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    exact hexp
  calc
    (P.card : ℝ) = ∑ j ∈ P, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ P, Real.exp (t * R) * Real.exp (-t * lam j) :=
      Finset.sum_le_sum fun j hj => hpoint j hj
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => 0 < lam j),
        Real.exp (t * R) * Real.exp (-t * lam j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.1⟩
      · intro j hjall hjP
        positivity
    _ = Real.exp (t * R) * finitePositiveHeatTrace lam t := by
      unfold finitePositiveHeatTrace
      rw [Finset.mul_sum]

/-- Exact optimization of the heat-trace estimate at `t=3/(2R)`, yielding
the manuscript's finite Weyl constant. -/
theorem finite_weyl_count_from_heatTrace
    {J : Type*} [Fintype J]
    (lam : J → ℝ) (R CS Vstar : ℝ)
    (hR : 0 < R) (hCS : 0 ≤ CS) (hV : 0 ≤ Vstar)
    (hlam : ∀ j, 0 ≤ lam j)
    (hzero : (Finset.univ.filter fun j => lam j = 0).card ≤ 1)
    (hheat : ∀ t : ℝ, 0 < t →
      finitePositiveHeatTrace lam t ≤
        4 * Vstar * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2)) :
    (finiteEigenvalueCount lam R : ℝ) ≤
      1 + 4 * Real.exp (3 / 2) * Vstar * (CS * R) ^ ((3 : ℝ) / 2) := by
  let t : ℝ := 3 / (2 * R)
  have ht : 0 < t := by unfold t; positivity
  have hcountNat := finite_count_le_one_add_positive_count lam R hlam hzero
  have hcount : (finiteEigenvalueCount lam R : ℝ) ≤
      1 + ((Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R).card : ℝ) := by
    exact_mod_cast hcountNat
  have hpositive := positive_count_le_exp_mul_heatTrace lam R t ht.le
  have hheatT := hheat t ht
  have hexp : Real.exp (t * R) = Real.exp (3 / 2) := by
    congr 1
    unfold t
    field_simp
  have hscale : 3 * CS / (2 * t) = CS * R := by
    unfold t
    field_simp
  calc
    (finiteEigenvalueCount lam R : ℝ)
        ≤ 1 + ((Finset.univ.filter fun j => 0 < lam j ∧ lam j ≤ R).card : ℝ) := hcount
    _ ≤ 1 + Real.exp (t * R) * finitePositiveHeatTrace lam t :=
      add_le_add_right hpositive 1
    _ ≤ 1 + Real.exp (t * R) *
        (4 * Vstar * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2)) := by
      gcongr
    _ = 1 + 4 * Real.exp (3 / 2) * Vstar *
        (CS * R) ^ ((3 : ℝ) / 2) := by rw [hexp, hscale]; ring

/-- Pointwise algebra converting Nash into growth of the inverse power. -/
theorem nash_inversePower_derivative_lower
    (u du CS L : ℝ) (hu : 0 < u) (hCS : 0 < CS) (hL : 0 < L)
    (hnash : u ^ (5 / 3 : ℝ) ≤ CS * (-du / 2) * L ^ (4 / 3 : ℝ)) :
    4 / (3 * CS * L ^ (4 / 3 : ℝ)) ≤
      du * (-(2 : ℝ) / 3) * u ^ (-(2 : ℝ) / 3 - 1) := by
  let d : ℝ := CS * L ^ (4 / 3 : ℝ)
  have hd : 0 < d := by unfold d; positivity
  have hu5 : 0 < u ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hu _
  have hq : 2 * u ^ (5 / 3 : ℝ) ≤ d * (-du) := by
    unfold d
    nlinarith
  have hinv : 0 < u ^ (-(5 : ℝ) / 3) := Real.rpow_pos_of_pos hu _
  have htwoinv : 0 ≤ 2 * u ^ (-(5 : ℝ) / 3) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hq htwoinv
  have hcancel : u ^ (5 / 3 : ℝ) * u ^ (-(5 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hu]
    norm_num
  have hfour : 4 ≤ 2 * d * (-du) * u ^ (-(5 : ℝ) / 3) := by
    calc
      (4 : ℝ) = 4 * (u ^ (5 / 3 : ℝ) * u ^ (-(5 : ℝ) / 3)) := by
            rw [hcancel, mul_one]
      _ = (2 * u ^ (5 / 3 : ℝ)) *
          (2 * u ^ (-(5 : ℝ) / 3)) := by ring
      _ ≤ (d * (-du)) * (2 * u ^ (-(5 : ℝ) / 3)) := hmul
      _ = 2 * d * (-du) * u ^ (-(5 : ℝ) / 3) := by ring
  have hid : u ^ (-(2 : ℝ) / 3 - 1) = u ^ (-(5 : ℝ) / 3) := by norm_num
  rw [hid]
  unfold d at *
  have hden : 0 < 3 * CS * L ^ (4 / 3 : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [hfour]

/-- A positive differentiable function with the Nash inverse-power
derivative bound has the integrated inverse-power lower estimate. -/
theorem inversePower_growth_from_derivative
    (u du : ℝ → ℝ) (a t : ℝ) (ht : 0 < t)
    (hu : ∀ s ∈ Set.Icc 0 t, 0 < u s)
    (hucont : ContinuousOn u (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt u (du s) s)
    (hlower : ∀ s ∈ Set.Ioo 0 t,
      a ≤ du s * (-(2 : ℝ) / 3) * u s ^ (-(2 : ℝ) / 3 - 1)) :
    a * t ≤ u t ^ (-(2 : ℝ) / 3) := by
  let F : ℝ → ℝ := fun s => u s ^ (-(2 : ℝ) / 3) - a * s
  have hpowcont : ContinuousOn (fun s => u s ^ (-(2 : ℝ) / 3)) (Set.Icc 0 t) := by
    exact hucont.rpow_const (fun s hs => Or.inl (hu s hs).ne')
  have hFcont : ContinuousOn F (Set.Icc 0 t) := hpowcont.sub (by fun_prop)
  have hFderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt F
      (du s * (-(2 : ℝ) / 3) * u s ^ (-(2 : ℝ) / 3 - 1) - a) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2.le⟩
    unfold F
    have hp : HasDerivAt (fun y => u y ^ (-(2 : ℝ) / 3))
        (du s * (-(2 : ℝ) / 3) * u s ^ (-(2 : ℝ) / 3 - 1)) s :=
      (hderiv s hs).rpow_const (p := (-(2 : ℝ) / 3))
        (Or.inl (hu s hsIcc).ne')
    have hlin : HasDerivAt (fun y : ℝ => a * y) a s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul a
    exact hp.sub hlin
  have hmono : MonotoneOn F (Set.Icc 0 t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hFcont
      (fun s hs => (hFderiv s (by simpa using hs)).hasDerivWithinAt)
      (fun s hs => by
        have h := hlower s (by simpa using hs)
        linarith)
  have hFt := hmono (by simp [ht.le]) (by simp [ht.le]) ht.le
  unfold F at hFt
  have h0 : 0 ≤ u 0 ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (hu 0 (by simp [ht.le])).le _
  nlinarith

/-- The exact inverse-power lower bound implies the manuscript heat-decay
upper bound.  It is stated separately so that semigroup calculus and final
constant extraction remain independently auditable. -/
theorem heat_decay_from_inversePower_lower
    (u CS L t : ℝ) (hu : 0 < u) (hCS : 0 < CS) (hL : 0 < L) (ht : 0 < t)
    (hlower : 4 * t / (3 * CS * L ^ (4 / 3 : ℝ)) ≤ u ^ (-(2 : ℝ) / 3)) :
    u ≤ L ^ 2 * (3 * CS / (4 * t)) ^ ((3 : ℝ) / 2) := by
  let B : ℝ := L ^ 2 * (3 * CS / (4 * t)) ^ ((3 : ℝ) / 2)
  have hB : 0 < B := by unfold B; positivity
  by_contra hn
  have hBu : B < u := lt_of_not_ge hn
  have hpow : u ^ (-(2 : ℝ) / 3) < B ^ (-(2 : ℝ) / 3) :=
    Real.rpow_lt_rpow_of_neg hB hBu (by norm_num)
  have hBid : B ^ (-(2 : ℝ) / 3) ≤
      4 * t / (3 * CS * L ^ (4 / 3 : ℝ)) := by
    unfold B
    have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
    have hq : 0 < 3 * CS / (4 * t) := by positivity
    rw [Real.mul_rpow hL2.le (Real.rpow_nonneg hq.le _)]
    have hLid : (L ^ 2 : ℝ) ^ (-(2 : ℝ) / 3) =
        (L ^ (4 / 3 : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
      norm_num
      exact Real.rpow_neg hL.le (4 / 3 : ℝ)
    have hqid :
        ((3 * CS / (4 * t)) ^ ((3 : ℝ) / 2)) ^ (-(2 : ℝ) / 3) =
          (3 * CS / (4 * t))⁻¹ := by
      rw [← Real.rpow_mul hq.le]
      norm_num
      rw [Real.rpow_neg_one]
      field_simp
    rw [hLid, hqid]
    field_simp
    norm_num
  exact (not_lt_of_ge hlower) (hpow.trans_le hBid)

/-- A finite heat-column package records exactly the positivity,
differentiability, dissipation, Nash, and L1-contraction identities used in
the heat-kernel proof. -/
structure FiniteHeatColumn (CS : ℝ) where
  l1 : ℝ
  l1_nonneg : 0 ≤ l1
  l2sq : ℝ → ℝ
  energy : ℝ → ℝ
  positive : ∀ t, 0 ≤ t → 0 < l2sq t
  continuous : ∀ T, 0 ≤ T → ContinuousOn l2sq (Set.Icc 0 T)
  dissipation : ∀ t, 0 < t → HasDerivAt l2sq (-2 * energy t) t
  nash_uncubed : ∀ t, 0 < t →
    l2sq t ^ (5 / 3 : ℝ) ≤ CS * energy t * l1 ^ (4 / 3 : ℝ)

/-- Every finite heat column satisfying the exposed Nash identities has the
required L2 decay. -/
theorem FiniteHeatColumn.l2_decay
    {CS : ℝ} (H : FiniteHeatColumn CS) (hCS : 0 < CS)
    (t : ℝ) (ht : 0 < t) (hl1 : 0 < H.l1) :
    H.l2sq t ≤ H.l1 ^ 2 * (3 * CS / (4 * t)) ^ ((3 : ℝ) / 2) := by
  let du : ℝ → ℝ := fun s => -2 * H.energy s
  have hpoint : ∀ s ∈ Set.Ioo 0 t,
      4 / (3 * CS * H.l1 ^ (4 / 3 : ℝ)) ≤
        du s * (-(2 : ℝ) / 3) * H.l2sq s ^ (-(2 : ℝ) / 3 - 1) := by
    intro s hs
    apply nash_inversePower_derivative_lower
      (H.l2sq s) (du s) CS H.l1 (H.positive s hs.1.le) hCS hl1
    unfold du
    convert H.nash_uncubed s hs.1 using 1 <;> ring
  have hgrowth := inversePower_growth_from_derivative
    H.l2sq du (4 / (3 * CS * H.l1 ^ (4 / 3 : ℝ))) t ht
    (fun s hs => H.positive s hs.1) (H.continuous t ht.le)
    (fun s hs => by simpa [du] using H.dissipation s hs.1) hpoint
  have hlower : 4 * t / (3 * CS * H.l1 ^ (4 / 3 : ℝ)) ≤
      H.l2sq t ^ (-(2 : ℝ) / 3) := by
    calc
      4 * t / (3 * CS * H.l1 ^ (4 / 3 : ℝ)) =
          (4 / (3 * CS * H.l1 ^ (4 / 3 : ℝ))) * t := by ring
      _ ≤ H.l2sq t ^ (-(2 : ℝ) / 3) := hgrowth
  exact heat_decay_from_inversePower_lower (H.l2sq t) CS H.l1 t
    (H.positive t ht.le) hCS hl1 ht hlower

/-- A finite spectral heat certificate packages the heat columns and the
diagonal trace identity needed for the Weyl estimate. -/
structure FiniteSpectralHeatCertificate
    {J V : Type*} [Fintype J] [Fintype V]
    (lam : J → ℝ) (μ : V → ℝ) (CS : ℝ) where
  column : V → FiniteHeatColumn CS
  column_l1 : ∀ v, (column v).l1 ≤ 2
  diagonal_bound : ∀ t, 0 < t →
    finitePositiveHeatTrace lam t ≤ ∑ v, μ v * (column v).l2sq (t / 2)

/-- The finite heat certificate yields the manuscript's heat-trace bound
with its explicit factor four. -/
theorem FiniteSpectralHeatCertificate.heatTrace_bound
    {J V : Type*} [Fintype J] [Fintype V]
    (lam : J → ℝ) (μ : V → ℝ) (CS Vstar : ℝ)
    (H : FiniteSpectralHeatCertificate lam μ CS)
    (hμ : ∀ v, 0 ≤ μ v) (hCS : 0 < CS)
    (hvolume : ∑ v, μ v ≤ Vstar) (hV : 0 ≤ Vstar)
    (hl1 : ∀ v, 0 < (H.column v).l1) :
    ∀ t, 0 < t → finitePositiveHeatTrace lam t ≤
      4 * Vstar * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2) := by
  intro t ht
  have ht2 : 0 < t / 2 := by positivity
  have hcol (v : V) : (H.column v).l2sq (t / 2) ≤
      4 * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2) := by
    have hd := (H.column v).l2_decay hCS (t / 2) ht2 (hl1 v)
    have hl1sq : (H.column v).l1 ^ 2 ≤ 4 := by
      nlinarith [(H.column v).l1_nonneg, H.column_l1 v]
    calc
      (H.column v).l2sq (t / 2)
          ≤ (H.column v).l1 ^ 2 *
            (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2) := by
              convert hd using 1 <;> ring
      _ ≤ 4 * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2) := by gcongr
  calc
    finitePositiveHeatTrace lam t ≤ ∑ v, μ v * (H.column v).l2sq (t / 2) :=
      H.diagonal_bound t ht
    _ ≤ ∑ v, μ v * (4 * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2)) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (hcol v) (hμ v)
    _ = (∑ v, μ v) * (4 * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2)) := by
      rw [Finset.sum_mul]
    _ ≤ Vstar * (4 * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2)) := by gcongr
    _ = 4 * Vstar * (3 * CS / (2 * t)) ^ ((3 : ℝ) / 2) := by ring

end NCG
