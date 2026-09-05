/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineRelativeEntropyQuadraticRemainderExact
import NCG.Grand.SampledVersusKilledExact

/-!
# Local faithfulness of Hermitian affine matrix paths

A positive-definite matrix remains positive definite under every sufficiently
small Hermitian affine perturbation.  The proof is quantitative: a spectral
floor for the base is split in half, and the other half absorbs the finitely
many eigenvalues of the perturbation.
-/

open Matrix Finset Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

open GeometricThresholdBank SampledVersusKilled

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 800000 in
-- Spectral minima and maxima over an arbitrary finite index type require
-- substantial elaboration through the matrix functional calculus.
/-- A faithful base has a faithful open affine neighborhood in every
Hermitian direction. -/
theorem exists_posDef_affine_neighborhood {σ d : Matrix n n ℂ}
    (hσ : σ.PosDef) (hd : d.IsHermitian) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Set.Ioo (-ε) ε, (σ + u • d).PosDef := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hempty =>
      letI : IsEmpty n := hempty
      refine ⟨1, one_pos, ?_⟩
      intro u hu
      have heq : σ + u • d = (1 : Matrix n n ℂ) := Subsingleton.elim _ _
      rw [heq]
      exact Matrix.PosDef.one
  | inr hnonempty =>
      letI : Nonempty n := hnonempty
      let hs : σ.IsHermitian := hσ.1
      have huniv : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty
      obtain ⟨i0, _, hi0⟩ :=
        Finset.exists_min_image Finset.univ hs.eigenvalues huniv
      let γ : ℝ := hs.eigenvalues i0
      let C : ℝ := (∑ i : n, |hd.eigenvalues i|) + 1
      have hγ : 0 < γ := by
        dsimp [γ, hs]
        exact hσ.eigenvalues_pos i0
      have hC : 0 < C := by
        dsimp [C]
        positivity
      let ε : ℝ := γ / (2 * C)
      have hε : 0 < ε := by
        dsimp [ε]
        positivity
      refine ⟨ε, hε, ?_⟩
      intro u hu
      have hσfloor :
          (σ - ((γ : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
        have heq : σ - ((γ : ℝ) : ℂ) • (1 : Matrix n n ℂ) =
            spectralFunction hs (fun x => id x - γ) := by
          rw [spectralFunction_sub, spectralFunction_id, spectralFunction_const]
        rw [heq]
        refine spectralFunction_posSemidef hs _ fun i => ?_
        exact sub_nonneg.mpr (hi0 i (Finset.mem_univ i))
      have hbase :
          (σ - (((γ / 2 : ℝ) : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosDef := by
        refine GRHRestoringShort.posDef_of_floor (γ := γ / 2) ?_ (by positivity)
        have heq :
            (σ - ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) -
                ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) =
              σ - (γ : ℂ) • (1 : Matrix n n ℂ) := by
          module
        rw [heq]
        exact hσfloor
      have heigen_bound : ∀ i : n, |hd.eigenvalues i| < C := by
        intro i
        have hle : |hd.eigenvalues i| ≤ ∑ j : n, |hd.eigenvalues j| :=
          Finset.single_le_sum (f := fun j : n => |hd.eigenvalues j|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        dsimp [C]
        linarith
      have hpert :
          (u • d + ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
        have heq : u • d + ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) =
            spectralFunction hd (fun x => u * x + γ / 2) := by
          rw [spectralFunction_add, smul_eq_spectralFunction hd u,
            spectralFunction_const]
        rw [heq]
        refine spectralFunction_posSemidef hd _ fun i => ?_
        have hui : |u * hd.eigenvalues i| < γ / 2 := by
          rw [abs_mul]
          have huabs : |u| < ε := (abs_lt).2 hu
          have hmul : |u| * |hd.eigenvalues i| < ε * C := by
            calc
              |u| * |hd.eigenvalues i| ≤ |u| * C :=
                mul_le_mul_of_nonneg_left (le_of_lt (heigen_bound i)) (abs_nonneg u)
              _ < ε * C := mul_lt_mul_of_pos_right huabs hC
          have heps : ε * C = γ / 2 := by
            dsimp [ε]
            field_simp
          linarith
        linarith [neg_abs_le (u * hd.eigenvalues i)]
      have hsum := hbase.add_posSemidef hpert
      have heq :
          (σ - ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) +
              (u • d + ((γ / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) =
            σ + u • d := by
        module
      rwa [heq] at hsum

/-- Positive definiteness is preserved on the whole affine segment between
two positive-definite endpoints. -/
theorem posDef_affine_of_mem_uIcc {σ d : Matrix n n ℂ}
    (hσ : σ.PosDef) {t u : ℝ} (ht : t ≠ 0)
    (hend : (σ + t • d).PosDef) (hu : u ∈ Set.uIcc 0 t) :
    (σ + u • d).PosDef := by
  let r : ℝ := u / t
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · rw [Set.uIcc_of_ge htneg.le] at hu
      exact ⟨div_nonneg_of_nonpos hu.2 htneg.le,
        (div_le_one_of_neg htneg).2 hu.1⟩
    · rw [Set.uIcc_of_le htpos.le] at hu
      exact ⟨div_nonneg hu.1 htpos.le, (div_le_one htpos).2 hu.2⟩
  have hcombo : ((1 - r) • σ + r • (σ + t • d)).PosDef := by
    rcases eq_or_lt_of_le hr.2 with hr1 | hr1
    · rw [hr1]
      simpa using hend
    · exact (hσ.smul (sub_pos.mpr hr1)).add_posSemidef
        (hend.posSemidef.smul hr.1)
  have heq : (1 - r) • σ + r • (σ + t • d) = σ + u • d := by
    have hrt : r * t = u := by
      dsimp [r]
      field_simp
    rw [smul_add, smul_smul, hrt]
    module
  rwa [heq] at hcombo

/-- If both endpoints of a Hermitian affine chord are faithful, then the
whole chord lies in a slightly larger open faithful interval. -/
theorem exists_faithful_open_interval_of_endpoints
    {σ d : Matrix n n ℂ} (hσ : σ.PosDef) (hd : d.IsHermitian)
    {t : ℝ} (hend : (σ + t • d).PosDef) :
    ∃ A B : ℝ,
      (∀ u ∈ Set.Ioo A B, (σ + u • d).PosDef) ∧
      Set.uIcc 0 t ⊆ Set.Ioo A B := by
  obtain ⟨ε0, hε0, hbase⟩ := exists_posDef_affine_neighborhood hσ hd
  have hdend : d.IsHermitian := hd
  obtain ⟨ε1, hε1, hendLocal⟩ :=
    exists_posDef_affine_neighborhood hend hdend
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · refine ⟨t - ε1, ε0, ?_, ?_⟩
    · intro u hu
      by_cases hut : u < t
      · have hs : u - t ∈ Set.Ioo (-ε1) ε1 := by
          constructor
          · linarith [hu.1]
          · linarith [hut, hε1]
        have hp := hendLocal (u - t) hs
        have heq : (σ + t • d) + (u - t) • d = σ + u • d := by module
        rwa [heq] at hp
      · by_cases hu0 : u ≤ 0
        · exact posDef_affine_of_mem_uIcc hσ htneg.ne hend
            (by rw [Set.uIcc_of_ge htneg.le]; exact ⟨le_of_not_gt hut, hu0⟩)
        · exact hbase u ⟨by linarith, hu.2⟩
    · intro u hu
      rw [Set.uIcc_of_ge htneg.le] at hu
      exact ⟨(sub_lt_self t hε1).trans_le hu.1, hu.2.trans_lt hε0⟩
  · refine ⟨-ε0, ε0, ?_, ?_⟩
    · intro u hu
      exact hbase u hu
    · simpa using (show (0 : ℝ) ∈ Set.Ioo (-ε0) ε0 by constructor <;> linarith)
  · refine ⟨-ε0, t + ε1, ?_, ?_⟩
    · intro u hu
      by_cases hu0 : u < 0
      · exact hbase u ⟨hu.1, by linarith⟩
      · by_cases hut : u ≤ t
        · exact posDef_affine_of_mem_uIcc hσ htpos.ne' hend
            (by rw [Set.uIcc_of_le htpos.le]; exact ⟨le_of_not_gt hu0, hut⟩)
        · have hs : u - t ∈ Set.Ioo (-ε1) ε1 := by
            constructor
            · linarith [le_of_not_ge hut, hε1]
            · linarith [hu.2]
          have hp := hendLocal (u - t) hs
          have heq : (σ + t • d) + (u - t) • d = σ + u • d := by module
          rwa [heq] at hp
    · intro u hu
      rw [Set.uIcc_of_le htpos.le] at hu
      exact ⟨(neg_lt_zero.mpr hε0).trans_le hu.1,
        hu.2.trans_lt (lt_add_of_pos_right t hε1)⟩

/-- The normalized affine entropy remainder needs only faithful endpoints;
the open faithful interval required by the FTC proof is automatic. -/
theorem two_mul_inv_sq_mul_affineRelativeEntropy_eq_bkmAverage_of_endpoints
    {σ d : Matrix n n ℂ} (hσ : σ.PosDef) (hd : d.IsHermitian)
    (htrace : d.trace.re = 0) {t : ℝ} (ht : t ≠ 0)
    (hend : (σ + t • d).PosDef) :
    2 * t⁻¹ ^ 2 * affineRelativeEntropy hσ.1 hd t =
      affineBkmQuadraticAverage hσ.1 hd t := by
  obtain ⟨A, B, hpos, hseg⟩ :=
    exists_faithful_open_interval_of_endpoints hσ hd hend
  exact two_mul_inv_sq_mul_affineRelativeEntropy_eq_bkmAverage
    hσ.1 hd htrace ht hpos hseg

end QRE
end NCG
