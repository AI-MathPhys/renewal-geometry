/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedGraphHeatKernel

/-!
# Operational Sobolev--Weyl theorem for finite weighted graphs

This file is the concrete manuscript-facing assembly: it combines the exact
coarea Sobolev constant with the canonical finite weighted-graph spectrum.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : FiniteWeightedGraph V)

def volume : ℝ := ∑ v, G.mass v

theorem volume_pos : 0 < G.volume := by
  unfold volume
  exact Finset.sum_pos (fun v _ => G.mass_pos v) Finset.univ_nonempty

def sqrtMass (v : V) : ℝ := Real.sqrt (G.mass v)

theorem symmetricLaplacian_mulVec_sqrtMass :
    Matrix.mulVec G.symmetricLaplacian G.sqrtMass = 0 := by
  ext v
  unfold Matrix.mulVec symmetricLaplacian sqrtMass degree
  have hsqrt (u : V) : Real.sqrt (G.mass u) ≠ 0 :=
    (Real.sqrt_pos.2 (G.mass_pos u)).ne'
  calc
    (∑ u, ((if v = u then (∑ x, G.conductance v x) *
        (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
          G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
            (Real.sqrt (G.mass u))⁻¹) * Real.sqrt (G.mass u)) =
        (∑ x, G.conductance v x) * (Real.sqrt (G.mass v))⁻¹ -
          ∑ u, G.conductance v u * (Real.sqrt (G.mass v))⁻¹ := by
            calc
              (∑ u, ((if v = u then (∑ x, G.conductance v x) *
                    (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) -
                  G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
                    (Real.sqrt (G.mass u))⁻¹) * Real.sqrt (G.mass u)) =
                  ∑ u, ((if v = u then (∑ x, G.conductance v x) *
                    (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) *
                      Real.sqrt (G.mass u) -
                    (G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
                      (Real.sqrt (G.mass u))⁻¹) * Real.sqrt (G.mass u)) := by
                        apply Finset.sum_congr rfl
                        intro u _
                        ring
              _ = (∑ u, (if v = u then (∑ x, G.conductance v x) *
                    (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) *
                      Real.sqrt (G.mass u)) -
                    ∑ u, (G.conductance v u * (Real.sqrt (G.mass v))⁻¹ *
                      (Real.sqrt (G.mass u))⁻¹) * Real.sqrt (G.mass u) := by
                        rw [Finset.sum_sub_distrib]
              _ = _ := by
                congr 1
                · rw [show (∑ u, (if v = u then (∑ x, G.conductance v x) *
                      (Real.sqrt (G.mass v))⁻¹ ^ 2 else 0) * Real.sqrt (G.mass u)) =
                    ∑ u, if v = u then
                      ((∑ x, G.conductance v x) *
                        (Real.sqrt (G.mass v))⁻¹ ^ 2) *
                          Real.sqrt (G.mass u) else 0 by
                        apply Finset.sum_congr rfl
                        intro u _
                        split_ifs <;> ring]
                  rw [Fintype.sum_ite_eq v]
                  field_simp [hsqrt v]
                · apply Finset.sum_congr rfl
                  intro u _
                  field_simp [hsqrt u]
    _ = 0 := by rw [Finset.sum_mul]; ring

/-- The finite weighted graph always has a canonical zero eigenvalue. -/
theorem exists_zero_eigenvalue : ∃ j, G.eigenvalue j = 0 := by
  have hsqrtNonzero : (WithLp.toLp 2 G.sqrtMass : EuclideanSpace ℝ V) ≠ 0 := by
    intro hz
    have hv := congrArg (fun x : EuclideanSpace ℝ V =>
      WithLp.ofLp x (Classical.choice inferInstance)) hz
    simp only [WithLp.ofLp_zero] at hv
    unfold sqrtMass at hv
    exact (Real.sqrt_pos.2 (G.mass_pos _)).ne' hv
  have hkernel : Matrix.toEuclideanLin G.symmetricLaplacian
      (WithLp.toLp 2 G.sqrtMass) = 0 := by
    rw [Matrix.toEuclideanLin_apply_piLp_toLp,
      G.symmetricLaplacian_mulVec_sqrtMass]
    rfl
  have hzeroSpectrum : 0 ∈ spectrum ℝ G.symmetricLaplacian := by
    rw [← Matrix.spectrum_toLpLin 2]
    exact Module.End.hasUnifEigenvalue_iff_mem_spectrum.mp
      (Module.End.HasUnifEigenvector.hasUnifEigenvalue (f :=
        Matrix.toEuclideanLin G.symmetricLaplacian) (μ := 0) (k := 1)
        (x := WithLp.toLp 2 G.sqrtMass) ⟨by
          rw [Module.End.genEigenspace_one]
          simp [hkernel], hsqrtNonzero⟩)
  rw [G.symmetricLaplacian_isHermitian.spectrum_real_eq_range_eigenvalues] at hzeroSpectrum
  rcases hzeroSpectrum with ⟨j, hj⟩
  exact ⟨j, hj⟩

/-- A zero eigenvalue has a constant weighted eigenfunction under the exact
Poincaré hypotheses. -/
theorem zero_eigenfunction_constant
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    {j : V} (hj : G.eigenvalue j = 0) :
    ∀ v, G.eigenfunction j v =
      (∑ u, G.mass u * G.eigenfunction j u) / G.volume := by
  let a : ℝ := (∑ u, G.mass u * G.eigenfunction j u) / G.volume
  let centered : V → ℝ := fun v => G.eigenfunction j v - a
  have hmean : ∑ v, G.mass v * centered v = 0 := by
    unfold centered a volume
    calc
      (∑ v, G.mass v *
          (G.eigenfunction j v -
            (∑ u, G.mass u * G.eigenfunction j u) / ∑ u, G.mass u)) =
          (∑ v, G.mass v * G.eigenfunction j v) -
            ((∑ u, G.mass u * G.eigenfunction j u) / ∑ u, G.mass u) *
              ∑ v, G.mass v := by
                rw [show (∑ v, G.mass v *
                    (G.eigenfunction j v -
                      (∑ u, G.mass u * G.eigenfunction j u) / ∑ u, G.mass u)) =
                    ∑ v, (G.mass v * G.eigenfunction j v -
                      G.mass v * ((∑ u, G.mass u * G.eigenfunction j u) /
                        ∑ u, G.mass u)) by
                          apply Finset.sum_congr rfl
                          intro v _
                          ring]
                rw [Finset.sum_sub_distrib]
                congr 1
                calc
                  (∑ v, G.mass v *
                      ((∑ u, G.mass u * G.eigenfunction j u) /
                        ∑ u, G.mass u)) =
                      (∑ v, G.mass v) *
                        ((∑ u, G.mass u * G.eigenfunction j u) /
                          ∑ u, G.mass u) := by rw [Finset.sum_mul]
                  _ = ((∑ u, G.mass u * G.eigenfunction j u) /
                        ∑ u, G.mass u) * ∑ v, G.mass v := by ring
      _ = 0 := by
        have hvol : (∑ u, G.mass u) ≠ 0 := G.volume_pos.ne'
        field_simp [hvol]
        ring
  have hp := finite_meanZero_poincare
    G.mass (fun v => (G.mass_pos v).le)
    G.conductance G.conductance_nonneg G.conductance_symm
    centered hmean I D h Vstar hI hD hh hVstar hvolume
    (fun v => by simpa [G.conductance_symm] using hdegree v) hcut
  rw [finiteSpatialEnergy_sub_const] at hp
  rw [G.eigenfunction_energy, hj] at hp
  norm_num at hp
  have hsum0 : ∑ v, G.mass v * centered v ^ 2 = 0 :=
    le_antisymm hp (Finset.sum_nonneg fun v _ =>
      mul_nonneg (G.mass_pos v).le (sq_nonneg _))
  intro v
  have hterm : G.mass v * centered v ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
      mul_nonneg (G.mass_pos u).le (sq_nonneg _))).mp hsum0 v (Finset.mem_univ v)
  have hsquare : centered v ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (G.mass_pos v).ne'
  have hz : centered v = 0 := sq_eq_zero_iff.mp hsquare
  exact sub_eq_zero.mp hz

/-- Under the manuscript hypotheses the canonical spectrum has at most one
zero eigenvalue. -/
theorem zero_eigenvalue_count_le_one
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A) :
    (Finset.univ.filter fun j => G.eigenvalue j = 0).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  have hi0 : G.eigenvalue i = 0 := (Finset.mem_filter.mp hi).2
  have hj0 : G.eigenvalue j = 0 := (Finset.mem_filter.mp hj).2
  by_contra hij
  have hiConst := G.zero_eigenfunction_constant I D h Vstar hI hD hh
    hVstar hvolume hdegree hcut hi0
  have hjConst := G.zero_eigenfunction_constant I D h Vstar hI hD hh
    hVstar hvolume hdegree hcut hj0
  let ai : ℝ := (∑ u, G.mass u * G.eigenfunction i u) / G.volume
  let aj : ℝ := (∑ u, G.mass u * G.eigenfunction j u) / G.volume
  have hii := G.eigenfunction_weighted_orthonormal i i
  have hjj := G.eigenfunction_weighted_orthonormal j j
  have hij0 := G.eigenfunction_weighted_orthonormal i j
  rw [if_pos rfl] at hii hjj
  rw [if_neg hij] at hij0
  have hai : ai ≠ 0 := by
    intro hai0
    rw [show (∑ v, G.mass v * G.eigenfunction i v * G.eigenfunction i v) = 0 by
      apply Finset.sum_eq_zero
      intro v _
      rw [hiConst v]
      change G.mass v * ai * ai = 0
      rw [hai0]
      ring] at hii
    norm_num at hii
  have haj : aj ≠ 0 := by
    intro haj0
    rw [show (∑ v, G.mass v * G.eigenfunction j v * G.eigenfunction j v) = 0 by
      apply Finset.sum_eq_zero
      intro v _
      rw [hjConst v]
      change G.mass v * aj * aj = 0
      rw [haj0]
      ring] at hjj
    norm_num at hjj
  have hcross : (∑ v, G.mass v * G.eigenfunction i v * G.eigenfunction j v) =
      ai * aj * G.volume := by
    unfold volume
    calc
      (∑ v, G.mass v * G.eigenfunction i v * G.eigenfunction j v) =
          ∑ v, ai * aj * G.mass v := by
            apply Finset.sum_congr rfl
            intro v _
            rw [hiConst v, hjConst v]
            change G.mass v * ai * aj = ai * aj * G.mass v
            ring
      _ = ai * aj * ∑ v, G.mass v := by rw [Finset.mul_sum]
  rw [hcross] at hij0
  exact (mul_ne_zero (mul_ne_zero hai haj) G.volume_pos.ne') hij0

/-- Weighted Fourier coefficient in the canonical Laplacian eigenbasis. -/
def spectralCoefficient (f : V → ℝ) (j : V) : ℝ :=
  ∑ v, G.mass v * f v * G.eigenfunction j v

/-- Exact weighted eigenfunction expansion of every vertex function. -/
theorem spectralExpansion (f : V → ℝ) (u : V) :
    ∑ j, G.spectralCoefficient f j * G.eigenfunction j u = f u := by
  unfold spectralCoefficient
  calc
    (∑ j, (∑ v, G.mass v * f v * G.eigenfunction j v) *
        G.eigenfunction j u) = ∑ j, ∑ v,
          (G.mass v * f v * G.eigenfunction j v) *
            G.eigenfunction j u := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
    _ = ∑ v, ∑ j, (G.mass v * f v * G.eigenfunction j v) *
          G.eigenfunction j u := Finset.sum_comm
    _ =
        ∑ v, G.mass v * f v *
          (∑ j, G.eigenfunction j v * G.eigenfunction j u) := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = f u := by
      rw [show (∑ v, G.mass v * f v *
          (∑ j, G.eigenfunction j v * G.eigenfunction j u)) =
          ∑ v, G.mass v * f v *
            (if v = u then (G.mass v)⁻¹ else 0) by
              apply Finset.sum_congr rfl
              intro v _
              rw [G.eigenfunction_completeness]]
      rw [show (∑ v, G.mass v * f v *
          (if v = u then (G.mass v)⁻¹ else 0)) =
          ∑ v, if v = u then G.mass v * f v * (G.mass v)⁻¹ else 0 by
            apply Finset.sum_congr rfl
            intro v _
            split_ifs <;> ring]
      rw [show (∑ v : V, if v = u then
          G.mass v * f v * (G.mass v)⁻¹ else 0) =
          G.mass u * f u * (G.mass u)⁻¹ by
            have hs := Finset.sum_eq_single u
              (s := (Finset.univ : Finset V))
              (f := fun v => if v = u then
                G.mass v * f v * (G.mass v)⁻¹ else 0)
              (fun b _ hbu => by rw [if_neg hbu])
              (fun hu => (hu (Finset.mem_univ u)).elim)
            simpa using hs]
      field_simp [(G.mass_pos u).ne']

theorem heatApply_linear_combination
    (t : ℝ) (a : V → ℝ) (F : V → V → ℝ) (u : V) :
    G.heatApply t (fun v => ∑ j, a j * F j v) u =
      ∑ j, a j * G.heatApply t (F j) u := by
  unfold heatApply
  change (∑ v, G.heatKernel t u v * ∑ j, a j * F j v) =
    ∑ j, a j * ∑ v, G.heatKernel t u v * F j v
  calc
    (∑ v, G.heatKernel t u v * ∑ j, a j * F j v) =
        ∑ v, ∑ j, G.heatKernel t u v * (a j * F j v) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ v, G.heatKernel t u v * (a j * F j v) := Finset.sum_comm
    _ = ∑ j, a j * ∑ v, G.heatKernel t u v * F j v := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring

/-- Spectral expansion of the concrete Markov heat action. -/
theorem heatApply_spectralExpansion (t : ℝ) (ht : 0 ≤ t)
    (f : V → ℝ) (u : V) :
    G.heatApply t f u =
      ∑ j, Real.exp (-t * G.eigenvalue j) *
        G.spectralCoefficient f j * G.eigenfunction j u := by
  have hfun : f = fun v => ∑ j,
      G.spectralCoefficient f j * G.eigenfunction j v := by
    funext v
    exact (G.spectralExpansion f v).symm
  conv_lhs => rw [hfun]
  rw [G.heatApply_linear_combination]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (G.heatApply_eigenfunction j t ht) u
  simp only [Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  ring

/-- Unit point mass at `v`, normalized with respect to the vertex mass. -/
def normalizedDelta (v u : V) : ℝ :=
  if u = v then (G.mass v)⁻¹ else 0

theorem spectralCoefficient_normalizedDelta (v j : V) :
    G.spectralCoefficient (G.normalizedDelta v) j = G.eigenfunction j v := by
  unfold spectralCoefficient normalizedDelta
  rw [show (∑ u, G.mass u * (if u = v then (G.mass v)⁻¹ else 0) *
      G.eigenfunction j u) =
      ∑ u, if u = v then G.mass u * (G.mass v)⁻¹ *
        G.eigenfunction j u else 0 by
          apply Finset.sum_congr rfl
          intro u _
          split_ifs <;> ring]
  rw [show (∑ u : V, if u = v then
      G.mass u * (G.mass v)⁻¹ * G.eigenfunction j u else 0) =
      G.mass v * (G.mass v)⁻¹ * G.eigenfunction j v by
        have hs := Finset.sum_eq_single v
          (s := (Finset.univ : Finset V))
          (f := fun u => if u = v then
            G.mass u * (G.mass v)⁻¹ * G.eigenfunction j u else 0)
          (fun b _ hbv => by rw [if_neg hbv])
          (fun hv => (hv (Finset.mem_univ v)).elim)
        simpa using hs]
  field_simp [(G.mass_pos v).ne']

theorem heatApply_normalizedDelta (t : ℝ) (v u : V) :
    G.heatApply t (G.normalizedDelta v) u =
      G.heatKernel t u v / G.mass v := by
  unfold heatApply normalizedDelta
  rw [show (∑ x, G.heatKernel t u x *
      (if x = v then (G.mass v)⁻¹ else 0)) =
      ∑ x, if x = v then G.heatKernel t u x * (G.mass v)⁻¹ else 0 by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring]
  rw [show (∑ x : V, if x = v then
      G.heatKernel t u x * (G.mass v)⁻¹ else 0) =
      G.heatKernel t u v * (G.mass v)⁻¹ by
        have hs := Finset.sum_eq_single v
          (s := (Finset.univ : Finset V))
          (f := fun x => if x = v then
            G.heatKernel t u x * (G.mass v)⁻¹ else 0)
          (fun b _ hbv => by rw [if_neg hbv])
          (fun hv => (hv (Finset.mem_univ v)).elim)
        simpa using hs]
  rw [div_eq_mul_inv]

/-- Canonical chosen zero mode. -/
def zeroIndex : V := Classical.choose G.exists_zero_eigenvalue

theorem zeroIndex_eigenvalue : G.eigenvalue G.zeroIndex = 0 :=
  Classical.choose_spec G.exists_zero_eigenvalue

/-- Positive-sector heat column based at `v`. -/
def positiveHeatColumn (v : V) (t : ℝ) (u : V) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
    Real.exp (-t * G.eigenvalue j) *
      G.eigenfunction j v * G.eigenfunction j u

def positiveHeatColumnL2Sq (v : V) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
    Real.exp (-2 * t * G.eigenvalue j) * G.eigenfunction j v ^ 2

def positiveHeatColumnEnergy (v : V) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
    G.eigenvalue j * Real.exp (-2 * t * G.eigenvalue j) *
      G.eigenfunction j v ^ 2

theorem positiveHeatColumn_mean_zero (v : V) (t : ℝ) :
    ∑ u, G.mass u * G.positiveHeatColumn v t u = 0 := by
  unfold positiveHeatColumn
  calc
    (∑ u, G.mass u *
        ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v *
            G.eigenfunction j u) =
        ∑ u, ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          G.mass u * (Real.exp (-t * G.eigenvalue j) *
            G.eigenfunction j v * G.eigenfunction j u) := by
              apply Finset.sum_congr rfl
              intro u _
              rw [Finset.mul_sum]
    _ =
        ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          ∑ u, G.mass u * (Real.exp (-t * G.eigenvalue j) *
            G.eigenfunction j v * G.eigenfunction j u) := Finset.sum_comm
    _ = ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          (Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v) *
            ∑ u, G.mass u * G.eigenfunction j u := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [G.eigenfunction_mean_zero (Finset.mem_filter.mp hj).2]
      ring

theorem positiveHeatColumn_l2sq (v : V) (t : ℝ) :
    ∑ u, G.mass u * G.positiveHeatColumn v t u ^ 2 =
      G.positiveHeatColumnL2Sq v t := by
  let P : Finset V := Finset.univ.filter fun j => 0 < G.eigenvalue j
  let a : V → ℝ := fun j => Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v
  unfold positiveHeatColumn positiveHeatColumnL2Sq
  change (∑ u, G.mass u * (∑ j ∈ P, a j * G.eigenfunction j u) ^ 2) =
    ∑ j ∈ P, Real.exp (-2 * t * G.eigenvalue j) * G.eigenfunction j v ^ 2
  rw [show (∑ u, G.mass u * (∑ j ∈ P, a j * G.eigenfunction j u) ^ 2) =
      ∑ i ∈ P, ∑ j ∈ P, a i * a j *
        (∑ u, G.mass u * G.eigenfunction i u * G.eigenfunction j u) by
    calc
      (∑ u, G.mass u * (∑ j ∈ P, a j * G.eigenfunction j u) ^ 2) =
          ∑ u, ∑ i ∈ P, ∑ j ∈ P,
            a i * a j * (G.mass u * G.eigenfunction i u *
              G.eigenfunction j u) := by
                apply Finset.sum_congr rfl
                intro u _
                rw [show (∑ j ∈ P, a j * G.eigenfunction j u) ^ 2 =
                    ∑ i ∈ P, ∑ j ∈ P,
                      (a i * G.eigenfunction i u) *
                        (a j * G.eigenfunction j u) by
                          rw [pow_two, Finset.sum_mul]
                          apply Finset.sum_congr rfl
                          intro i hi
                          rw [Finset.mul_sum]]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = ∑ i ∈ P, ∑ j ∈ P, ∑ u,
          a i * a j * (G.mass u * G.eigenfunction i u *
            G.eigenfunction j u) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
      _ = ∑ i ∈ P, ∑ j ∈ P, a i * a j *
          (∑ u, G.mass u * G.eigenfunction i u * G.eigenfunction j u) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              ]
  simp_rw [G.eigenfunction_weighted_orthonormal]
  rw [show (∑ i ∈ P, ∑ j ∈ P, a i * a j * (if i = j then 1 else 0)) =
      ∑ i ∈ P, a i ^ 2 by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (∑ j ∈ P, a i * a j * (if i = j then 1 else 0)) = a i ^ 2 by
      have hs := Finset.sum_eq_single i
        (s := P) (f := fun j => a i * a j * (if i = j then 1 else 0))
        (fun b hb hbi => by rw [if_neg (Ne.symm hbi)]; ring)
        (fun hiP => (hiP hi).elim)
      rw [hs]
      rw [if_pos rfl]
      ring]]
  apply Finset.sum_congr rfl
  intro j hj
  unfold a
  calc
    (Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v) ^ 2 =
        (Real.exp (-t * G.eigenvalue j) *
          Real.exp (-t * G.eigenvalue j)) * G.eigenfunction j v ^ 2 := by ring
    _ = Real.exp ((-t * G.eigenvalue j) +
          (-t * G.eigenvalue j)) * G.eigenfunction j v ^ 2 := by
            rw [Real.exp_add]
    _ = Real.exp (-2 * t * G.eigenvalue j) * G.eigenfunction j v ^ 2 := by
          rw [show (-t * G.eigenvalue j) + (-t * G.eigenvalue j) =
            -2 * t * G.eigenvalue j by ring]

/-- The concrete Dirichlet energy of a positive-sector heat column is its
spectral first moment. -/
theorem positiveHeatColumn_energy (v : V) (t : ℝ) :
    finiteSpatialEnergy G.conductance (G.positiveHeatColumn v t) =
      G.positiveHeatColumnEnergy v t := by
  let a : V → ℝ := fun j =>
    if 0 < G.eigenvalue j then
      Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v
    else 0
  let x : V → ℝ := ∑ j, a j • G.eigenvector j
  have hx (u : V) :
      x u / Real.sqrt (G.mass u) = G.positiveHeatColumn v t u := by
    unfold x a positiveHeatColumn eigenfunction
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : 0 < G.eigenvalue j
    · simp only [hj, if_true]
      ring
    · simp only [hj, if_false, zero_mul]
  have hfun : (fun u => x u / Real.sqrt (G.mass u)) =
      G.positiveHeatColumn v t := funext hx
  calc
    finiteSpatialEnergy G.conductance (G.positiveHeatColumn v t) =
        dotProduct (star x) (Matrix.mulVec G.symmetricLaplacian x) := by
          rw [G.symmetricLaplacian_quadraticForm x, hfun]
    _ = ∑ j, G.eigenvalue j * a j ^ 2 := by
          exact G.symmetricLaplacian_quadraticForm_eigenExpansion a
    _ = G.positiveHeatColumnEnergy v t := by
      unfold positiveHeatColumnEnergy a
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : 0 < G.eigenvalue j
      · simp only [hj, if_true]
        rw [show (Real.exp (-t * G.eigenvalue j) *
            G.eigenfunction j v) ^ 2 =
            Real.exp (-2 * t * G.eigenvalue j) *
              G.eigenfunction j v ^ 2 by
          calc
            (Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v) ^ 2 =
                (Real.exp (-t * G.eigenvalue j) *
                  Real.exp (-t * G.eigenvalue j)) *
                    G.eigenfunction j v ^ 2 := by ring
            _ = Real.exp ((-t * G.eigenvalue j) +
                  (-t * G.eigenvalue j)) * G.eigenfunction j v ^ 2 := by
                    rw [Real.exp_add]
            _ = Real.exp (-2 * t * G.eigenvalue j) *
                  G.eigenfunction j v ^ 2 := by
                    congr 2
                    ring]
        ring
      · simp only [hj, if_false, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

/-- Exact heat dissipation identity on the positive spectral sector. -/
theorem positiveHeatColumnL2Sq_hasDerivAt (v : V) (t : ℝ) :
    HasDerivAt (G.positiveHeatColumnL2Sq v)
      (-2 * G.positiveHeatColumnEnergy v t) t := by
  unfold positiveHeatColumnL2Sq positiveHeatColumnEnergy
  let P : Finset V := Finset.univ.filter (fun j => 0 < G.eigenvalue j)
  have hsum := HasDerivAt.sum (u := P)
    (fun j _ => by
      have hlin : HasDerivAt
          (fun s : ℝ => -2 * s * G.eigenvalue j)
          (-2 * G.eigenvalue j) t := by
        simpa only [id_eq, one_mul, mul_assoc] using
          ((hasDerivAt_id t).const_mul (-2)).mul_const (G.eigenvalue j)
      have hexp := hlin.exp
      convert hexp.const_mul (G.eigenfunction j v ^ 2) using 1 <;> ring)
  have hfun :
      (∑ j ∈ P, fun s : ℝ =>
        G.eigenfunction j v ^ 2 * Real.exp (-2 * s * G.eigenvalue j)) =
      (fun s : ℝ => ∑ j ∈ P,
        Real.exp (-2 * s * G.eigenvalue j) * G.eigenfunction j v ^ 2) := by
    funext s
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hder :
      (∑ j ∈ P, G.eigenfunction j v ^ 2 *
        (Real.exp (-2 * t * G.eigenvalue j) * (-2 * G.eigenvalue j))) =
      -2 * ∑ j ∈ P, G.eigenvalue j *
        Real.exp (-2 * t * G.eigenvalue j) * G.eigenfunction j v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, hder] at hsum
  exact hsum

theorem positiveHeatColumnL2Sq_continuous (v : V) :
    Continuous (G.positiveHeatColumnL2Sq v) := by
  exact continuous_iff_continuousAt.2 fun t =>
    (G.positiveHeatColumnL2Sq_hasDerivAt v t).continuousAt

/-- On a nontrivial graph, every vertex delta has a nonzero coefficient in
the positive spectral sector. -/
theorem exists_positive_eigenfunction_nonzero [Nontrivial V]
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v : V) :
    ∃ j, 0 < G.eigenvalue j ∧ G.eigenfunction j v ≠ 0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨u, huv⟩ := exists_ne v
  have hterm (j : V) :
      G.eigenfunction j v * G.eigenfunction j u =
        G.eigenfunction j v * G.eigenfunction j v := by
    by_cases hj : 0 < G.eigenvalue j
    · rw [hn j hj]
      ring
    · have hj0 : G.eigenvalue j = 0 :=
        le_antisymm (le_of_not_gt hj) (G.eigenvalue_nonnegative j)
      rw [G.zero_eigenfunction_constant I D h Vstar hI hD hh hVstar
        hvolume hdegree hcut hj0 u,
        G.zero_eigenfunction_constant I D h Vstar hI hD hh hVstar
        hvolume hdegree hcut hj0 v]
  have hcompUV := G.eigenfunction_completeness v u
  have hcompVV := G.eigenfunction_completeness v v
  simp only [if_neg (Ne.symm huv)] at hcompUV
  rw [if_pos rfl] at hcompVV
  have heq : (0 : ℝ) = (G.mass v)⁻¹ := by
    rw [← hcompUV, ← hcompVV]
    apply Finset.sum_congr rfl
    intro j _
    exact hterm j
  exact (inv_ne_zero (G.mass_pos v).ne') heq.symm

theorem positiveHeatColumnL2Sq_pos [Nontrivial V]
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v : V) (t : ℝ) :
    0 < G.positiveHeatColumnL2Sq v t := by
  obtain ⟨j, hjpos, hjne⟩ := G.exists_positive_eigenfunction_nonzero
    I D h Vstar hI hD hh hVstar hvolume hdegree hcut v
  unfold positiveHeatColumnL2Sq
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjpos⟩, ?_⟩
    exact mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hjne)

/-- The zero eigenspace contribution to the heat kernel is the constant
kernel `1 / volume`. -/
theorem zeroSector_kernel
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v u : V) :
    ∑ j ∈ Finset.univ.filter (fun j => G.eigenvalue j = 0),
      G.eigenfunction j v * G.eigenfunction j u = (G.volume)⁻¹ := by
  let z := G.zeroIndex
  have hz : G.eigenvalue z = 0 := G.zeroIndex_eigenvalue
  have hunique (j : V) (hj : G.eigenvalue j = 0) : j = z := by
    have hcard := G.zero_eigenvalue_count_le_one I D h Vstar hI hD hh
      hVstar hvolume hdegree hcut
    rw [Finset.card_le_one_iff] at hcard
    exact hcard
      (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩)
  have hsingle : Finset.univ.filter (fun j => G.eigenvalue j = 0) = {z} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hunique j, fun hj => hj ▸ hz⟩
  rw [hsingle, Finset.sum_singleton]
  have hconst := G.zero_eigenfunction_constant I D h Vstar hI hD hh
    hVstar hvolume hdegree hcut hz
  let c : ℝ := G.eigenfunction z v
  have hc (w : V) : G.eigenfunction z w = c := by
    change G.eigenfunction z w = G.eigenfunction z v
    rw [hconst w, hconst v]
  have hnorm := G.eigenfunction_weighted_norm z
  simp_rw [hc] at hnorm
  have hc2 : c ^ 2 * G.volume = 1 := by
    unfold volume
    rw [show (∑ w, G.mass w * c ^ 2) = c ^ 2 * ∑ w, G.mass w by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring] at hnorm
    exact hnorm
  rw [hc u]
  change c * c = (G.volume)⁻¹
  rw [show c * c = c ^ 2 by ring]
  exact eq_inv_of_mul_eq_one_left hc2

/-- Positive heat column equals the Markov heat column with its stationary
zero mode removed. -/
theorem positiveHeatColumn_eq_heatKernel_sub_stationary
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v u : V) (t : ℝ) (ht : 0 ≤ t) :
    G.positiveHeatColumn v t u =
      G.heatKernel t u v / G.mass v - (G.volume)⁻¹ := by
  have hspec := G.heatApply_spectralExpansion t ht (G.normalizedDelta v) u
  rw [G.heatApply_normalizedDelta] at hspec
  simp_rw [G.spectralCoefficient_normalizedDelta] at hspec
  have hnotpos (j : V) : ¬ 0 < G.eigenvalue j ↔ G.eigenvalue j = 0 := by
    exact ⟨fun h => le_antisymm (le_of_not_gt h) (G.eigenvalue_nonnegative j),
      fun h hp => by rw [h] at hp; exact lt_irrefl 0 hp⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset V) (fun j => 0 < G.eigenvalue j)
    (fun j => Real.exp (-t * G.eigenvalue j) *
      G.eigenfunction j v * G.eigenfunction j u)
  have hzero :
      ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 < G.eigenvalue j),
        Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v *
          G.eigenfunction j u = (G.volume)⁻¹ := by
    rw [show Finset.univ.filter (fun j => ¬ 0 < G.eigenvalue j) =
        Finset.univ.filter (fun j => G.eigenvalue j = 0) by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnotpos j]
    rw [show (∑ j ∈ Finset.univ.filter (fun j => G.eigenvalue j = 0),
        Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v *
          G.eigenfunction j u) =
        ∑ j ∈ Finset.univ.filter (fun j => G.eigenvalue j = 0),
          G.eigenfunction j v * G.eigenfunction j u by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
      simp]
    exact G.zeroSector_kernel I D h Vstar hI hD hh hVstar hvolume
      hdegree hcut v u
  unfold positiveHeatColumn
  have hall :
      (∑ j, Real.exp (-t * G.eigenvalue j) * G.eigenfunction j v *
        G.eigenfunction j u) = G.heatKernel t u v / G.mass v := hspec.symm
  linarith [hsplit, hzero, hall]

/-- The positive heat column has weighted L1 norm at most two. -/
theorem positiveHeatColumn_l1_le_two
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v : V) (t : ℝ) (ht : 0 ≤ t) :
    ∑ u, G.mass u * |G.positiveHeatColumn v t u| ≤ 2 := by
  have hkernel (u : V) : 0 ≤ G.heatKernel t u v :=
    (G.heatKernel_rowStochastic t ht).1 u v
  have hfirst : ∑ u, G.mass u *
      (G.heatKernel t u v / G.mass v) = 1 := by
    calc
      (∑ u, G.mass u * (G.heatKernel t u v / G.mass v)) =
          (∑ u, G.mass u * G.heatKernel t u v) / G.mass v := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ = 1 := by
        rw [G.heatKernel_weightedColumnSum t ht v]
        exact div_self (G.mass_pos v).ne'
  have hsecond : ∑ u, G.mass u * (G.volume)⁻¹ = 1 := by
    rw [← Finset.sum_mul]
    change G.volume * (G.volume)⁻¹ = 1
    exact mul_inv_cancel₀ G.volume_pos.ne'
  calc
    (∑ u, G.mass u * |G.positiveHeatColumn v t u|) =
        ∑ u, G.mass u *
          |G.heatKernel t u v / G.mass v - (G.volume)⁻¹| := by
            apply Finset.sum_congr rfl
            intro u _
            rw [G.positiveHeatColumn_eq_heatKernel_sub_stationary I D h Vstar
              hI hD hh hVstar hvolume hdegree hcut v u t ht]
    _ ≤ ∑ u, G.mass u *
          (G.heatKernel t u v / G.mass v + (G.volume)⁻¹) := by
      apply Finset.sum_le_sum
      intro u _
      have habs :
          |G.heatKernel t u v / G.mass v - (G.volume)⁻¹| ≤
            G.heatKernel t u v / G.mass v + (G.volume)⁻¹ := by
        rw [abs_le]
        constructor
        · have hstationary : 0 ≤ (G.volume)⁻¹ := inv_nonneg.mpr G.volume_pos.le
          linarith [div_nonneg (hkernel u) (G.mass_pos v).le]
        · have hstationary : 0 ≤ (G.volume)⁻¹ := inv_nonneg.mpr G.volume_pos.le
          linarith [div_nonneg (hkernel u) (G.mass_pos v).le]
      exact mul_le_mul_of_nonneg_left habs (G.mass_pos u).le
    _ = 2 := by
      rw [show (∑ u, G.mass u *
          (G.heatKernel t u v / G.mass v + (G.volume)⁻¹)) =
          (∑ u, G.mass u * (G.heatKernel t u v / G.mass v)) +
            ∑ u, G.mass u * (G.volume)⁻¹ by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        ring]
      rw [hfirst, hsecond]
      norm_num

theorem positiveHeatColumnEnergy_nonnegative (v : V) (t : ℝ) :
    0 ≤ G.positiveHeatColumnEnergy v t := by
  unfold positiveHeatColumnEnergy
  exact Finset.sum_nonneg fun j hj => mul_nonneg
    (mul_nonneg (G.eigenvalue_nonnegative j) (Real.exp_pos _).le)
    (sq_nonneg _)

theorem positiveHeatColumn_nash_uncubed
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v : V) (t : ℝ) (ht : 0 ≤ t) :
    G.positiveHeatColumnL2Sq v t ^ (5 / 3 : ℝ) ≤
      (128 * D / I ^ 2) * G.positiveHeatColumnEnergy v t *
        (2 : ℝ) ^ (4 / 3 : ℝ) := by
  let f := G.positiveHeatColumn v t
  let L : ℝ := ∑ u, G.mass u * |f u|
  have hsob := finite_meanZero_L6_sobolev G.mass
    (fun u => (G.mass_pos u).le) G.conductance G.conductance_nonneg
    G.conductance_symm f (G.positiveHeatColumn_mean_zero v t)
    I D h hI hD hh hdegree hcut
  have hCS : 0 ≤ 128 * D / I ^ 2 := by positivity
  have hnash := finite_nash_from_sobolev G.mass f
    (fun u => (G.mass_pos u).le) (128 * D / I ^ 2)
    (G.positiveHeatColumnEnergy v t) hCS
    (G.positiveHeatColumnEnergy_nonnegative v t)
    (by rw [← G.positiveHeatColumn_energy v t]; exact hsob)
  have hL : 0 ≤ L := Finset.sum_nonneg fun u _ =>
    mul_nonneg (G.mass_pos u).le (abs_nonneg _)
  have hLtwo : L ≤ 2 := G.positiveHeatColumn_l1_le_two I D h Vstar
    hI hD hh hVstar hvolume hdegree hcut v t ht
  have hLpow : L ^ (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hL hLtwo (by norm_num)
  have hbound := hnash.trans (mul_le_mul_of_nonneg_left hLpow
    (mul_nonneg hCS (G.positiveHeatColumnEnergy_nonnegative v t)))
  change G.positiveHeatColumnL2Sq v t ^ (5 / 3 : ℝ) ≤ _
  rw [← G.positiveHeatColumn_l2sq v t]
  exact hbound

/-- The weighted diagonal sum of the positive heat columns is exactly the
positive spectral heat trace. -/
theorem positiveHeatTrace_diagonal (t : ℝ) :
    finitePositiveHeatTrace G.eigenvalue t =
      ∑ v, G.mass v * G.positiveHeatColumnL2Sq v (t / 2) := by
  unfold finitePositiveHeatTrace positiveHeatColumnL2Sq
  calc
    (∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
        Real.exp (-t * G.eigenvalue j)) =
        ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          Real.exp (-t * G.eigenvalue j) *
            (∑ v, G.mass v * G.eigenfunction j v ^ 2) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [G.eigenfunction_weighted_norm j, mul_one]
    _ = ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          ∑ v, G.mass v *
            (Real.exp (-2 * (t / 2) * G.eigenvalue j) *
              G.eigenfunction j v ^ 2) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v _
              have hexp : Real.exp (-t * G.eigenvalue j) =
                  Real.exp (-2 * (t / 2) * G.eigenvalue j) := by
                congr 1
                ring
              rw [hexp]
              ring
    _ = ∑ v, ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
          G.mass v * (Real.exp (-2 * (t / 2) * G.eigenvalue j) *
            G.eigenfunction j v ^ 2) := Finset.sum_comm
    _ = ∑ v, G.mass v *
          ∑ j ∈ Finset.univ.filter (fun j => 0 < G.eigenvalue j),
            Real.exp (-2 * (t / 2) * G.eigenvalue j) *
              G.eigenfunction j v ^ 2 := by
                apply Finset.sum_congr rfl
                intro v _
                rw [Finset.mul_sum]

/-- Concrete Nash heat-column package on every nontrivial graph. -/
def positiveHeatColumnCertificate [Nontrivial V]
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (v : V) : FiniteHeatColumn (128 * D / I ^ 2) where
  l1 := 2
  l1_nonneg := by norm_num
  l2sq := G.positiveHeatColumnL2Sq v
  energy := G.positiveHeatColumnEnergy v
  positive := fun t _ => G.positiveHeatColumnL2Sq_pos I D h Vstar hI hD hh
    hVstar hvolume hdegree hcut v t
  continuous := fun T _ => (G.positiveHeatColumnL2Sq_continuous v).continuousOn
  dissipation := fun t _ => G.positiveHeatColumnL2Sq_hasDerivAt v t
  nash_uncubed := fun t ht => G.positiveHeatColumn_nash_uncubed
    I D h Vstar hI hD hh hVstar hvolume hdegree hcut v t ht.le

def spectralHeatCertificate [Nontrivial V]
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A) :
    FiniteSpectralHeatCertificate G.eigenvalue G.mass (128 * D / I ^ 2) where
  column := G.positiveHeatColumnCertificate I D h Vstar hI hD hh hVstar
    hvolume hdegree hcut
  column_l1 := fun _ => le_rfl
  diagonal_bound := fun t _ => (G.positiveHeatTrace_diagonal t).le

/-- The concrete positive heat trace obeys the manuscript bound. -/
theorem positiveHeatTrace_bound
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A) :
    ∀ t : ℝ, 0 < t → finitePositiveHeatTrace G.eigenvalue t ≤
      4 * Vstar * (3 * (128 * D / I ^ 2) / (2 * t)) ^ ((3 : ℝ) / 2) := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hsub =>
      letI : Subsingleton V := hsub
      intro t ht
      have hzero : ∀ j : V, G.eigenvalue j = 0 := by
        intro j
        obtain ⟨z, hz⟩ := G.exists_zero_eigenvalue
        exact congrArg G.eigenvalue (Subsingleton.elim j z) |>.trans hz
      unfold finitePositiveHeatTrace
      simp [hzero]
      exact mul_nonneg (mul_nonneg (by norm_num) hVstar)
        (Real.rpow_nonneg (by positivity) _)
  | inr hnon =>
      letI : Nontrivial V := hnon
      have hDpos : 0 < D := by
        by_contra hnot
        have hDzero : D = 0 := le_antisymm (le_of_not_gt hnot) hD
        let v0 : V := Classical.choice inferInstance
        obtain ⟨j, hjpos, hjne⟩ := G.exists_positive_eigenfunction_nonzero
          I D h Vstar hI hD hh hVstar hvolume hdegree hcut v0
        have hsob := finite_meanZero_L6_sobolev G.mass
          (fun u => (G.mass_pos u).le) G.conductance G.conductance_nonneg
          G.conductance_symm (G.eigenfunction j) (G.eigenfunction_mean_zero hjpos)
          I D h hI hD hh hdegree hcut
        rw [hDzero] at hsob
        norm_num at hsob
        have hterm : G.mass v0 * G.eigenfunction j v0 ^ 6 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
            mul_nonneg (G.mass_pos u).le (by positivity))).mp
              (le_antisymm hsob (Finset.sum_nonneg fun u _ =>
                mul_nonneg (G.mass_pos u).le (by positivity)))
              v0 (Finset.mem_univ v0)
        have hp6 : G.eigenfunction j v0 ^ 6 = 0 :=
          (mul_eq_zero.mp hterm).resolve_left (G.mass_pos v0).ne'
        exact hjne (by
          by_contra hne
          exact (pow_ne_zero 6 hne) hp6)
      exact (G.spectralHeatCertificate I D h Vstar hI hD hh hVstar hvolume
        hdegree hcut).heatTrace_bound G.eigenvalue G.mass
          (128 * D / I ^ 2) Vstar
          (fun v => (G.mass_pos v).le) (by
            exact div_pos (mul_pos (by norm_num) hDpos) (sq_pos_of_pos hI))
          hvolume hVstar
          (fun _ => by change 0 < (2 : ℝ); norm_num)

/-- Exact finite-graph Weyl counting law with the manuscript constant. -/
theorem eigenvalueCount_bound
    (I D h Vstar R : ℝ) (hI : 0 < I) (hD : 0 ≤ D) (hh : 0 < h)
    (hVstar : 0 ≤ Vstar) (hvolume : G.volume ≤ Vstar) (hR : 0 < R)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A) :
    (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
      1 + 4 * Real.exp (3 / 2) * Vstar *
        ((128 * D / I ^ 2) * R) ^ ((3 : ℝ) / 2) := by
  apply finite_weyl_count_from_heatTrace G.eigenvalue R
    (128 * D / I ^ 2) Vstar hR (by positivity) hVstar
    G.eigenvalue_nonnegative
    (G.zero_eigenvalue_count_le_one I D h Vstar hI hD hh hVstar
      hvolume hdegree hcut)
  exact G.positiveHeatTrace_bound I D h Vstar hI hD hh hVstar hvolume
    hdegree hcut

/-- The advertised positive spectral floor for every positive eigenmode. -/
theorem positiveEigenvalue_floor
    (I D h Vstar : ℝ) (hI : 0 < I) (hD : 0 < D) (hh : 0 < h)
    (hVstar : 0 < Vstar) (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ u, G.conductance u v) ≤ D * G.mass v)
    (hcut : ∀ A : Finset V,
      I * min (∑ v ∈ A, G.mass v) (∑ v ∈ Aᶜ, G.mass v) ^ ((2 : ℝ) / 3) ≤
        h * finiteCutCapacity G.conductance A)
    (j : V) (hj : 0 < G.eigenvalue j) :
    I ^ 2 / (128 * D * Vstar ^ ((2 : ℝ) / 3)) ≤ G.eigenvalue j := by
  have hp := finite_meanZero_poincare G.mass (fun v => (G.mass_pos v).le)
    G.conductance G.conductance_nonneg G.conductance_symm
    (G.eigenfunction j) (G.eigenfunction_mean_zero hj)
    I D h Vstar hI hD.le hh hVstar.le hvolume hdegree hcut
  have hCP : 0 < 128 * D * Vstar ^ ((2 : ℝ) / 3) / I ^ 2 := by positivity
  have hfloor := finite_meanZero_eigenvalue_floor G.mass
    (fun v => (G.mass_pos v).le) G.conductance (G.eigenfunction j)
    (G.eigenvalue j) (128 * D * Vstar ^ ((2 : ℝ) / 3) / I ^ 2)
    hCP (by rw [G.eigenfunction_weighted_norm]; norm_num) hp
    (by rw [G.eigenfunction_energy, G.eigenfunction_weighted_norm, mul_one])
  convert hfloor using 1 <;> field_simp <;> ring

/-- Compact-screen spectral tail for the canonical weighted spectrum. -/
theorem eigenfunction_spectralTail_bound
    (f : V → ℝ) (R : ℝ) (hR : 0 < R) :
    ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
        G.spectralCoefficient f j ^ 2 ≤
      R⁻¹ * ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2 := by
  simpa only [one_mul] using spectral_tail_bound
    (fun _ : V => (1 : ℝ)) (G.spectralCoefficient f) G.eigenvalue
    (fun _ => by norm_num) G.eigenvalue_nonnegative R hR

end FiniteWeightedGraph
end NCG
