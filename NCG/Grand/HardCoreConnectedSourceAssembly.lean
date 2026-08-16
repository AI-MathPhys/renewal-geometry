/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HardCoreExclusionGreenProfile
import NCG.Grand.HardCoreDegreeBandedModulation

/-!
# Connected-source assembly for the all-degree hard-core corrector

The massive inverse on the full exclusion sheet is extended from a single
dipole to an arbitrary finite sum of adjacent first differences.  Because the
sheet already imposes all hard-core constraints simultaneously, positivity of
the massive operator treats intersecting collision channels at once.
-/

open Matrix Finset

namespace NCG.HardCoreExclusion

variable {N r : ℕ} [NeZero N]

/-- Green profile of an arbitrary source on the complete hard-core sheet. -/
noncomputable def sourceProfile (mass diffusion : ℝ)
    (b : Config N r → ℝ) : Config N r → ℝ :=
  (massiveOperator (N := N) (r := r) mass diffusion)⁻¹.mulVec b

/-- The arbitrary-source Green profile solves the exact massive cell equation. -/
theorem sourceProfile_cell_equation {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (b : Config N r → ℝ) :
    (massiveOperator (N := N) (r := r) mass diffusion).mulVec
        (sourceProfile mass diffusion b) = b := by
  have hunit := (massiveOperator_posDef (N := N) (r := r)
    hmass hdiffusion).isUnit
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  rw [sourceProfile, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]

/-- Testing the general cell equation gives the exact energy identity. -/
theorem sourceProfile_energy_identity {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (b : Config N r → ℝ) :
    mass * l2Sq (sourceProfile mass diffusion b)
        + diffusion * energy (sourceProfile mass diffusion b) =
      sourceProfile mass diffusion b ⬝ᵥ b := by
  let psi := sourceProfile mass diffusion b
  have heq := sourceProfile_cell_equation (N := N) (r := r)
    hmass hdiffusion b
  have htest := congrArg (fun z => psi ⬝ᵥ z) heq
  rw [← htest]
  simp only [massiveOperator, energy, l2Sq, psi, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Uniform massive Green estimate for every finite source. -/
theorem sourceProfile_uniform_bound {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (b : Config N r → ℝ) :
    mass ^ 2 * l2Sq (sourceProfile mass diffusion b) ≤ l2Sq b ∧
      mass * (diffusion * energy (sourceProfile mass diffusion b)) ≤ l2Sq b := by
  let psi := sourceProfile mass diffusion b
  have hid := sourceProfile_energy_identity (N := N) (r := r)
    hmass hdiffusion b
  have hcs := dotProduct_le_l2Norm_mul_l2Norm psi b
  have hbound : mass * l2Sq psi + diffusion * energy psi
      ≤ Real.sqrt (l2Sq psi) * Real.sqrt (l2Sq b) := by
    rw [hid]
    simpa [l2Norm] using hcs
  simpa [psi] using
    (massive_energy_scalar_bound (mass := mass) (U := l2Sq psi)
      (E := diffusion * energy psi) (S := l2Sq b) hmass
      (l2Sq_nonneg psi) (mul_nonneg hdiffusion (energy_nonneg psi))
      (l2Sq_nonneg b) hbound)

/-- Unweighted `L² + Dirichlet` estimate for an arbitrary finite source. -/
theorem sourceProfile_l2_energy_bound {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (b : Config N r → ℝ) :
    l2Sq (sourceProfile mass diffusion b)
        + diffusion * energy (sourceProfile mass diffusion b)
      ≤ l2Sq b / mass ^ 2 + l2Sq b / mass := by
  obtain ⟨hl2, henergy⟩ := sourceProfile_uniform_bound
    (N := N) (r := r) hmass hdiffusion b
  have hm2 : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hl2' : l2Sq (sourceProfile mass diffusion b) ≤ l2Sq b / mass ^ 2 := by
    rw [le_div_iff₀ hm2]
    simpa [mul_comm] using hl2
  have henergy' : diffusion * energy (sourceProfile mass diffusion b)
      ≤ l2Sq b / mass := by
    rw [le_div_iff₀ hmass]
    simpa [mul_comm] using henergy
  linarith

/-- One oriented, adjacent first-difference collision channel. -/
structure CollisionChannel (N r : ℕ) [NeZero N] where
  fromConfig : Config N r
  toConfig : Config N r
  adjacent : (graph N r).Adj fromConfig toConfig

/-- A finite connected collision source is a sum of adjacent first
differences.  Shared endpoints and spanning-tree choices are represented by
repetition in the finite channel type. -/
def collisionSource {C : Type*} [Fintype C]
    (channel : C → CollisionChannel N r) (weight : C → ℝ) :
    Config N r → ℝ :=
  ∑ c, weight c • dipoleSource (channel c).fromConfig (channel c).toConfig

/-- Every finite collision source is neutral. -/
theorem collisionSource_neutral {C : Type*} [Fintype C]
    (channel : C → CollisionChannel N r) (weight : C → ℝ) :
    ∑ z, collisionSource channel weight z = 0 := by
  classical
  simp only [collisionSource, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c hc
  rw [← Finset.mul_sum]
  simp [dipoleSource]

/-- The inverse of a finite collision source is the corresponding finite sum
of the individual dipole profiles. -/
theorem sourceProfile_collisionSource {C : Type*} [Fintype C]
    (mass diffusion : ℝ) (channel : C → CollisionChannel N r)
    (weight : C → ℝ) :
    sourceProfile mass diffusion (collisionSource channel weight) =
      ∑ c, weight c • profile mass diffusion
        (channel c).fromConfig (channel c).toConfig := by
  classical
  apply funext
  intro z
  simp only [sourceProfile, collisionSource, profile, Matrix.mulVec,
    dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro z' hz'
  ring

/-- The strict-coupling mass of the degree-`r` modulated cell problem. -/
noncomputable def modulatedMass (g θ q : ℝ) (r : ℕ) : ℝ :=
  (1 - |θ| * q) * g * r

theorem modulatedMass_pos {g θ q δ : ℝ} {r : ℕ}
    (hg : 0 < g) (hδ : 0 < δ)
    (hcoupling : |θ| * q ≤ 1 - δ) (hr : 0 < r) :
    0 < modulatedMass g θ q r := by
  have hfactor : 0 < 1 - |θ| * q := by linarith
  exact mul_pos (mul_pos hfactor hg) (by exact_mod_cast hr)

/-- Uniform fixed-ceiling profile estimate for arbitrary connected collision
sources in the strict-coupling regime. -/
theorem finite_ceiling_connected_profile_bound {R : ℕ}
    (g diffusion θ q δ : ℝ)
    (hg : 0 < g) (hdiffusion : 0 ≤ diffusion) (hδ : 0 < δ)
    (hcoupling : |θ| * q ≤ 1 - δ)
    (b : ∀ j : Fin R, Config N (j.1 + 2) → ℝ) :
    ∑ j : Fin R,
        (l2Sq (sourceProfile
            (modulatedMass g θ q (j.1 + 2)) diffusion (b j))
          + diffusion * energy (sourceProfile
            (modulatedMass g θ q (j.1 + 2)) diffusion (b j)))
      ≤ ∑ j : Fin R,
        (l2Sq (b j) / (modulatedMass g θ q (j.1 + 2)) ^ 2
          + l2Sq (b j) / modulatedMass g θ q (j.1 + 2)) := by
  apply Finset.sum_le_sum
  intro j hj
  exact sourceProfile_l2_energy_bound
    (modulatedMass_pos hg hδ hcoupling (by omega)) hdiffusion (b j)

/-- Exact `d/N` representation and its fixed-ceiling `N⁻²` estimate for the
complete connected-source profile. -/
theorem finite_ceiling_connected_corrector_bound {R : ℕ}
    (g diffusion θ q δ d D : ℝ)
    (hg : 0 < g) (hdiffusion : 0 ≤ diffusion) (hδ : 0 < δ)
    (hcoupling : |θ| * q ≤ 1 - δ)
    (hD : |d| ≤ D) (hD0 : 0 ≤ D)
    (b : ∀ j : Fin R, Config N (j.1 + 2) → ℝ) :
    ∑ j : Fin R,
        l2Sq (((d / N) : ℝ) • sourceProfile
          (modulatedMass g θ q (j.1 + 2)) diffusion (b j))
      ≤ D ^ 2 *
          (∑ j : Fin R,
            (l2Sq (b j) / (modulatedMass g θ q (j.1 + 2)) ^ 2
              + l2Sq (b j) / modulatedMass g θ q (j.1 + 2))) /
          N ^ 2 := by
  let pnorm : Fin R → ℝ := fun j =>
    l2Sq (sourceProfile (modulatedMass g θ q (j.1 + 2)) diffusion (b j))
  let cnorm : Fin R → ℝ := fun j =>
    l2Sq (((d / N) : ℝ) • sourceProfile
      (modulatedMass g θ q (j.1 + 2)) diffusion (b j))
  apply NCG.hard_core_fixed_degree_bound N d D
    (∑ j : Fin R,
      (l2Sq (b j) / (modulatedMass g θ q (j.1 + 2)) ^ 2
        + l2Sq (b j) / modulatedMass g θ q (j.1 + 2))) pnorm cnorm
  · exact Nat.pos_of_ne_zero (NeZero.ne N)
  · exact hD
  · exact hD0
  · intro j
    exact l2Sq_nonneg _
  · intro j
    exact l2Sq_smul _ _
  · calc
      ∑ j, pnorm j ≤ ∑ j,
          (pnorm j + diffusion * energy (sourceProfile
            (modulatedMass g θ q (j.1 + 2)) diffusion (b j))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact le_add_of_nonneg_right
          (mul_nonneg hdiffusion (energy_nonneg _))
      _ ≤ ∑ j : Fin R,
          (l2Sq (b j) / (modulatedMass g θ q (j.1 + 2)) ^ 2
            + l2Sq (b j) / modulatedMass g θ q (j.1 + 2)) := by
        simpa [pnorm] using finite_ceiling_connected_profile_bound
          (N := N) g diffusion θ q δ hg hdiffusion hδ hcoupling b

end NCG.HardCoreExclusion
