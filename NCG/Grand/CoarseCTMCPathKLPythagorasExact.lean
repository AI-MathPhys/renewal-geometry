/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCPathLikelihoodExact

/-!
# Coarse continuous-time path-space KL Pythagoras

The key analytic step in the coarse path theorem is the finite rate/channel
chain rule.  On each visible coarse block, the sum of scalar CTMC divergences
splits into the divergence of the total coarse rates plus the total source
rate times the KL divergence of the conditional fine destination laws.
-/

open Finset

namespace NCG
namespace DrivenProcess
namespace CoarsePathKL

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Partition an off-diagonal fine sum into the within-cell block and
all visible coarse destination fibres. -/
theorem sum_offDiag_eq_internal_add_visible
    {S Z : Type*} [Fintype S] [DecidableEq S]
    [Fintype Z] [DecidableEq Z]
    (C : S → Z) (u : S) (f : S → ℝ) :
    (∑ v ∈ (univ.erase u), f v) =
      (∑ v ∈ univ.filter (fun v => C v = C u ∧ v ≠ u), f v) +
        ∑ z ∈ univ.erase (C u),
          ∑ v ∈ univ.filter (fun v => C v = z), f v := by
  classical
  let f0 : S → ℝ := fun v => if v = u then 0 else f v
  have hfiber := Finset.sum_fiberwise (univ : Finset S) C f0
  have hf0 :
      (∑ v : S, f0 v) = ∑ v ∈ univ.erase u, f v := by
    calc
      (∑ v : S, f0 v) =
          f0 u + ∑ v ∈ univ.erase u, f0 v :=
        (Finset.add_sum_erase univ f0 (mem_univ u)).symm
      _ = ∑ v ∈ univ.erase u, f v := by
        simp only [f0, if_pos, zero_add]
        apply Finset.sum_congr rfl
        intro v hv
        have hvu : v ≠ u := Finset.ne_of_mem_erase hv
        simp [f0, hvu]
  have hall :
      (∑ v ∈ univ.erase u, f v) =
        ∑ z : Z, ∑ v ∈ univ.filter (fun v => C v = z), f0 v := by
    exact hf0.symm.trans hfiber.symm
  rw [hall, ← Finset.add_sum_erase _ _ (mem_univ (C u))]
  congr 1
  · let sAll := univ.filter (fun v => C v = C u)
    let sInternal := univ.filter (fun v => C v = C u ∧ v ≠ u)
    have hsub : sInternal ⊆ sAll := by
      intro v hv
      simp only [sInternal, sAll, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv ⊢
      exact hv.1
    have hextra : ∀ v ∈ sAll, v ∉ sInternal → f0 v = 0 := by
      intro v hv hnot
      simp only [sAll, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [sInternal, Finset.mem_filter, Finset.mem_univ,
        true_and, not_and] at hnot
      have hvu : v = u := by
        by_contra hne
        exact hnot hv hne
      simp [f0, hvu]
    calc
      (∑ v ∈ sAll, f0 v) = ∑ v ∈ sInternal, f0 v :=
        (Finset.sum_subset hsub hextra).symm
      _ = ∑ v ∈ sInternal, f v := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvu : v ≠ u := (Finset.mem_filter.mp hv).2.2
        simp [f0, hvu]
  · apply Finset.sum_congr rfl
    intro z hz
    have hzu : z ≠ C u := Finset.ne_of_mem_erase hz
    apply Finset.sum_congr rfl
    intro v hv
    have hCv : C v = z := (Finset.mem_filter.mp hv).2
    have hvu : v ≠ u := by
      intro hvu
      subst v
      exact hzu hCv.symm
    simp [f0, hvu]

/-- Elementary rate/channel chain rule on one positive finite destination
block. -/
theorem phi_sum_eq_coarse_add_channel
    (s : Finset J) (a b : J → ℝ) (A B : ℝ)
    (ha : ∀ j ∈ s, 0 < a j) (hb : ∀ j ∈ s, 0 < b j)
    (hA : ∑ j ∈ s, a j = A) (hB : ∑ j ∈ s, b j = B)
    (hApos : 0 < A) (hBpos : 0 < B) :
    (∑ j ∈ s, Phi (a j) (b j)) =
      Phi A B +
        A * ∑ j ∈ s,
          (a j / A) * Real.log ((a j / A) / (b j / B)) := by
  have hlog : ∀ j ∈ s,
      Real.log ((a j / A) / (b j / B)) =
        Real.log (a j / b j) - Real.log (A / B) := by
    intro j hj
    have houter := Real.log_div
      (div_pos (ha j hj) hApos).ne'
      (div_pos (hb j hj) hBpos).ne'
    have haA := Real.log_div (ha j hj).ne' hApos.ne'
    have hbB := Real.log_div (hb j hj).ne' hBpos.ne'
    have hab := Real.log_div (ha j hj).ne' (hb j hj).ne'
    have hAB := Real.log_div hApos.ne' hBpos.ne'
    rw [houter, haA, hbB, hab, hAB]
    ring
  have hchannel :
      A * ∑ j ∈ s,
          (a j / A) * Real.log ((a j / A) / (b j / B)) =
        (∑ j ∈ s, a j * Real.log (a j / b j)) -
          A * Real.log (A / B) := by
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ s,
          A * ((a j / A) *
            Real.log ((a j / A) / (b j / B)))) =
        ∑ j ∈ s,
          a j * (Real.log (a j / b j) - Real.log (A / B)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hlog j hj]
            field_simp [hApos.ne']
      _ = (∑ j ∈ s, a j * Real.log (a j / b j)) -
          (∑ j ∈ s, a j) * Real.log (A / B) := by
            simp only [mul_sub, Finset.sum_sub_distrib,
              Finset.sum_mul]
      _ = (∑ j ∈ s, a j * Real.log (a j / b j)) -
          A * Real.log (A / B) := by rw [hA]
  rw [hchannel]
  unfold Phi
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB]
  ring

/-- Probability-vector version of the same finite chain rule. -/
theorem kl_sum_eq_coarse_add_channel
    (s : Finset J) (a b : J → ℝ) (A B : ℝ)
    (ha : ∀ j ∈ s, 0 < a j) (hb : ∀ j ∈ s, 0 < b j)
    (hA : ∑ j ∈ s, a j = A) (hB : ∑ j ∈ s, b j = B)
    (hApos : 0 < A) (hBpos : 0 < B) :
    (∑ j ∈ s, a j * Real.log (a j / b j)) =
      A * Real.log (A / B) +
        A * ∑ j ∈ s,
          (a j / A) * Real.log ((a j / A) / (b j / B)) := by
  have h := phi_sum_eq_coarse_add_channel s a b A B
    ha hb hA hB hApos hBpos
  unfold Phi at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  rw [hA, hB] at h
  linarith

/-- Gibbs nonnegativity for positive normalized finite vectors. -/
theorem finiteKL_nonneg
    (s : Finset J) (a b : J → ℝ)
    (ha : ∀ j ∈ s, 0 < a j) (hb : ∀ j ∈ s, 0 < b j)
    (ha1 : ∑ j ∈ s, a j = 1) (hb1 : ∑ j ∈ s, b j = 1) :
    0 ≤ ∑ j ∈ s, a j * Real.log (a j / b j) := by
  have hphi : 0 ≤ ∑ j ∈ s, Phi (a j) (b j) :=
    Finset.sum_nonneg fun j hj =>
      Phi_nonneg (ha j hj).le (hb j hj).le fun hzero =>
        False.elim ((hb j hj).ne' hzero)
  unfold Phi at hphi
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hphi
  rw [ha1, hb1] at hphi
  linarith

variable {S Z : Type*} [Fintype S] [DecidableEq S]
  [Fintype Z] [DecidableEq Z]

/-- Strong lumpability on every visible coarse destination block. -/
def StronglyLumpable (C : S → Z) (L : Matrix S S ℝ)
    (A : Matrix Z Z ℝ) : Prop :=
  ∀ u z, z ≠ C u →
    ∑ v ∈ univ.filter (fun v => C v = z), L u v = A (C u) z

/-- KL divergence between the conditional fine destination channels in one
visible coarse block. -/
noncomputable def destinationChannelKL
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (A Atilde : Matrix Z Z ℝ) (u : S) (z : Z) : ℝ :=
  ∑ v ∈ univ.filter (fun v => C v = z),
    (L u v / A (C u) z) *
      Real.log
        ((L u v / A (C u) z) /
          (Ltilde u v / Atilde (C u) z))

/-- Within-cell invisible rate divergence. -/
noncomputable def internalKLDensity
    (C : S → Z) (L Ltilde : Matrix S S ℝ) (u : S) : ℝ :=
  ∑ v ∈ univ.filter (fun v => C v = C u ∧ v ≠ u),
    Phi (L u v) (Ltilde u v)

/-- Pointwise coarse path-rate Pythagoras: total fine generator divergence is
coarse divergence plus visible destination-channel mismatch plus invisible
within-cell motion. -/
theorem generatorKLDensity_pythagoras
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (A Atilde : Matrix Z Z ℝ)
    (hLump : StronglyLumpable C L A)
    (hLumpTilde : StronglyLumpable C Ltilde Atilde)
    (hcoarsePos : ∀ u z, z ≠ C u →
      0 < A (C u) z ∧ 0 < Atilde (C u) z)
    (hfinePos : ∀ u z, z ≠ C u → ∀ v, C v = z →
      0 < L u v ∧ 0 < Ltilde u v)
    (u : S) :
    FinitePath.generatorKLDensity L Ltilde u =
      FinitePath.generatorKLDensity A Atilde (C u) +
        (∑ z ∈ univ.erase (C u),
          A (C u) z *
            destinationChannelKL C L Ltilde A Atilde u z) +
        internalKLDensity C L Ltilde u := by
  unfold FinitePath.generatorKLDensity internalKLDensity
  rw [sum_offDiag_eq_internal_add_visible C u
    (fun v => Phi (L u v) (Ltilde u v))]
  have hblock : ∀ z ∈ univ.erase (C u),
      (∑ v ∈ univ.filter (fun v => C v = z),
        Phi (L u v) (Ltilde u v)) =
        Phi (A (C u) z) (Atilde (C u) z) +
          A (C u) z *
            destinationChannelKL C L Ltilde A Atilde u z := by
    intro z hz
    have hzu : z ≠ C u := Finset.ne_of_mem_erase hz
    exact phi_sum_eq_coarse_add_channel
      (univ.filter (fun v => C v = z))
      (fun v => L u v) (fun v => Ltilde u v)
      (A (C u) z) (Atilde (C u) z)
      (fun v hv => (hfinePos u z hzu v (Finset.mem_filter.mp hv).2).1)
      (fun v hv => (hfinePos u z hzu v (Finset.mem_filter.mp hv).2).2)
      (hLump u z hzu) (hLumpTilde u z hzu)
      (hcoarsePos u z hzu).1 (hcoarsePos u z hzu).2
  rw [Finset.sum_congr rfl hblock, Finset.sum_add_distrib]
  unfold destinationChannelKL
  ring

theorem destinationChannelKL_nonneg
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (A Atilde : Matrix Z Z ℝ)
    (hLump : StronglyLumpable C L A)
    (hLumpTilde : StronglyLumpable C Ltilde Atilde)
    (u : S) (z : Z) (hzu : z ≠ C u)
    (hcoarsePos :
      0 < A (C u) z ∧ 0 < Atilde (C u) z)
    (hfinePos : ∀ v, C v = z →
      0 < L u v ∧ 0 < Ltilde u v) :
    0 ≤ destinationChannelKL C L Ltilde A Atilde u z := by
  unfold destinationChannelKL
  apply finiteKL_nonneg
  · intro v hv
    exact div_pos (hfinePos v (Finset.mem_filter.mp hv).2).1
      hcoarsePos.1
  · intro v hv
    exact div_pos (hfinePos v (Finset.mem_filter.mp hv).2).2
      hcoarsePos.2
  · rw [← Finset.sum_div, hLump u z hzu]
    exact div_self hcoarsePos.1.ne'
  · rw [← Finset.sum_div, hLumpTilde u z hzu]
    exact div_self hcoarsePos.2.ne'

theorem internalKLDensity_nonneg
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (hAC : ∀ u v, u ≠ v → Ltilde u v = 0 → L u v = 0)
    (u : S) :
    0 ≤ internalKLDensity C L Ltilde u := by
  unfold internalKLDensity
  apply Finset.sum_nonneg
  intro v hv
  have huv : u ≠ v := (Finset.mem_filter.mp hv).2.2.symm
  exact Phi_nonneg
    (hL.offDiag_nonneg u v huv)
    (hLtilde.offDiag_nonneg u v huv)
    (hAC u v huv)

/-- Pushforward mass/occupation weight through the coarse state record. -/
noncomputable def pushforwardWeight (C : S → Z) (weight : S → ℝ)
    (z : Z) : ℝ :=
  ∑ u ∈ univ.filter (fun u => C u = z), weight u

/-- Hidden initial-fibre mismatch. -/
noncomputable def initialFibreKL
    (C : S → Z) (p ptilde : S → ℝ) : ℝ :=
  ∑ z, pushforwardWeight C p z *
    ∑ u ∈ univ.filter (fun u => C u = z),
      (p u / pushforwardWeight C p z) *
        Real.log
          ((p u / pushforwardWeight C p z) /
            (ptilde u / pushforwardWeight C ptilde z))

/-- Exact initial KL chain rule through a finite state record. -/
theorem initialKL_chain_rule
    (C : S → Z) (p ptilde : S → ℝ)
    (hp : ∀ u, 0 < p u) (hptilde : ∀ u, 0 < ptilde u)
    (hcoarsePos : ∀ z,
      0 < pushforwardWeight C p z ∧
        0 < pushforwardWeight C ptilde z) :
    FinitePath.initialKL p ptilde =
      FinitePath.initialKL (pushforwardWeight C p)
        (pushforwardWeight C ptilde) +
      initialFibreKL C p ptilde := by
  unfold FinitePath.initialKL initialFibreKL
  have hfiber := Finset.sum_fiberwise (univ : Finset S) C
    (fun u => p u * Real.log (p u / ptilde u))
  rw [← hfiber]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  exact kl_sum_eq_coarse_add_channel
    (univ.filter (fun u => C u = z)) p ptilde
    (pushforwardWeight C p z) (pushforwardWeight C ptilde z)
    (fun u _ => hp u) (fun u _ => hptilde u)
    rfl rfl (hcoarsePos z).1 (hcoarsePos z).2

theorem initialFibreKL_nonneg
    (C : S → Z) (p ptilde : S → ℝ)
    (hp : ∀ u, 0 < p u) (hptilde : ∀ u, 0 < ptilde u)
    (hcoarsePos : ∀ z,
      0 < pushforwardWeight C p z ∧
        0 < pushforwardWeight C ptilde z) :
    0 ≤ initialFibreKL C p ptilde := by
  unfold initialFibreKL
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (hcoarsePos z).1.le
  apply finiteKL_nonneg
  · intro u hu
    exact div_pos (hp u) (hcoarsePos z).1
  · intro u hu
    exact div_pos (hptilde u) (hcoarsePos z).2
  · unfold pushforwardWeight
    rw [← Finset.sum_div]
    exact div_self (hcoarsePos z).1.ne'
  · unfold pushforwardWeight
    rw [← Finset.sum_div]
    exact div_self (hcoarsePos z).2.ne'

/-- Fibrewise regrouping of a weighted coarse observable. -/
theorem weighted_coarse_sum
    (C : S → Z) (weight : S → ℝ) (F : Z → ℝ) :
    (∑ u, weight u * F (C u)) =
      ∑ z, pushforwardWeight C weight z * F z := by
  unfold pushforwardWeight
  have hfiber := Finset.sum_fiberwise (univ : Finset S) C
    (fun u => weight u * F (C u))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(Finset.mem_filter.mp hu).2]

/-- Full finite-horizon KL Pythagoras at the compensated occupation level. -/
theorem coarse_path_KL_pythagoras
    (C : S → Z) (p ptilde : S → ℝ)
    (L Ltilde : Matrix S S ℝ) (A Atilde : Matrix Z Z ℝ)
    (theta : S → ℝ)
    (hp : ∀ u, 0 < p u) (hptilde : ∀ u, 0 < ptilde u)
    (hcoarseMassPos : ∀ z,
      0 < pushforwardWeight C p z ∧
        0 < pushforwardWeight C ptilde z)
    (hLump : StronglyLumpable C L A)
    (hLumpTilde : StronglyLumpable C Ltilde Atilde)
    (hcoarsePos : ∀ u z, z ≠ C u →
      0 < A (C u) z ∧ 0 < Atilde (C u) z)
    (hfinePos : ∀ u z, z ≠ C u → ∀ v, C v = z →
      0 < L u v ∧ 0 < Ltilde u v) :
    FinitePath.initialKL p ptilde +
        ∑ u, theta u * FinitePath.generatorKLDensity L Ltilde u =
      FinitePath.initialKL (pushforwardWeight C p)
          (pushforwardWeight C ptilde) +
        initialFibreKL C p ptilde +
        (∑ z, pushforwardWeight C theta z *
          FinitePath.generatorKLDensity A Atilde z) +
        (∑ u, theta u *
          ∑ z ∈ univ.erase (C u),
            A (C u) z *
              destinationChannelKL C L Ltilde A Atilde u z) +
        ∑ u, theta u * internalKLDensity C L Ltilde u := by
  rw [initialKL_chain_rule C p ptilde hp hptilde hcoarseMassPos]
  have hpoint := fun u =>
    generatorKLDensity_pythagoras C L Ltilde A Atilde
      hLump hLumpTilde hcoarsePos hfinePos u
  simp_rw [hpoint, mul_add]
  simp only [Finset.sum_add_distrib]
  rw [weighted_coarse_sum C theta
    (fun z => FinitePath.generatorKLDensity A Atilde z)]
  ring

/-- The visible destination-channel contribution is nonnegative. -/
theorem integrated_destination_KL_nonneg
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (A Atilde : Matrix Z Z ℝ) (theta : S → ℝ)
    (htheta : ∀ u, 0 ≤ theta u)
    (hLump : StronglyLumpable C L A)
    (hLumpTilde : StronglyLumpable C Ltilde Atilde)
    (hcoarsePos : ∀ u z, z ≠ C u →
      0 < A (C u) z ∧ 0 < Atilde (C u) z)
    (hfinePos : ∀ u z, z ≠ C u → ∀ v, C v = z →
      0 < L u v ∧ 0 < Ltilde u v) :
    0 ≤ ∑ u, theta u *
      ∑ z ∈ univ.erase (C u),
        A (C u) z *
          destinationChannelKL C L Ltilde A Atilde u z := by
  apply Finset.sum_nonneg
  intro u _
  apply mul_nonneg (htheta u)
  apply Finset.sum_nonneg
  intro z hz
  have hzu : z ≠ C u := Finset.ne_of_mem_erase hz
  exact mul_nonneg (hcoarsePos u z hzu).1.le
    (destinationChannelKL_nonneg C L Ltilde A Atilde
      hLump hLumpTilde u z hzu (hcoarsePos u z hzu)
      (hfinePos u z hzu))

/-- The invisible within-cell contribution is nonnegative. -/
theorem integrated_internal_KL_nonneg
    (C : S → Z) (L Ltilde : Matrix S S ℝ)
    (theta : S → ℝ) (htheta : ∀ u, 0 ≤ theta u)
    (hL : IsGenerator L) (hLtilde : IsGenerator Ltilde)
    (hAC : ∀ u v, u ≠ v → Ltilde u v = 0 → L u v = 0) :
    0 ≤ ∑ u, theta u * internalKLDensity C L Ltilde u :=
  Finset.sum_nonneg fun u _ =>
    mul_nonneg (htheta u)
      (internalKLDensity_nonneg C L Ltilde hL hLtilde hAC u)

end CoarsePathKL
end DrivenProcess
end NCG
