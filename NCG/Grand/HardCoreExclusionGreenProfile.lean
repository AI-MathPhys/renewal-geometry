/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import NCG.Grand.HardCoreCorrectorProfile

/-!
# Massive Green profiles on the three-dimensional hard-core exclusion sheet

This file constructs the finite configuration space used by the hard-core
corrector rather than treating the profile estimate as an abstract input.
Particles live on the three-dimensional discrete torus and configurations are
injective, so every collision channel is removed simultaneously.  The genuine
exclusion graph moves one particle by one coordinate step while preserving
injectivity.

The graph Laplacian is positive semidefinite.  Consequently the massive cell
operator `m I + diffusion L` is positive definite, its inverse exists, and a
neutral first-difference source has a unique Green profile.  The energy
identity and finite Cauchy--Schwarz give bounds independent of the torus size
and of the chosen exclusion edge.
-/

open Matrix Finset

namespace NCG.HardCoreExclusion

/-- The three-dimensional discrete torus of side length `N`. -/
abbrev Torus3 (N : ℕ) := Fin 3 → ZMod N

/-- Ordered `r`-particle configurations with the hard-core constraint. -/
abbrev Config (N r : ℕ) :=
  {x : Fin r → Torus3 N // Function.Injective x}

variable {N r : ℕ} [NeZero N]

/-- A directed elementary exclusion move: one particle advances by one unit
in one torus coordinate and every other particle is unchanged.  Both endpoint
configurations already satisfy the hard-core constraint. -/
def OneStep (x y : Config N r) : Prop :=
  ∃ (p : Fin r) (a : Fin 3),
    y.1 p = Function.update (x.1 p) a (x.1 p a + 1) ∧
    ∀ q, q ≠ p → y.1 q = x.1 q


/-- The undirected nearest-neighbour graph of the hard-core exclusion sheet. -/
def graph (N r : ℕ) [NeZero N] : SimpleGraph (Config N r) :=
  SimpleGraph.fromRel OneStep

noncomputable instance : DecidableRel (graph N r).Adj := Classical.decRel _

/-- Squared finite `L²` norm in counting measure. -/
def l2Sq {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ∑ i, (f i) ^ 2

/-- Finite `L²` norm in counting measure. -/
noncomputable def l2Norm {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  Real.sqrt (l2Sq f)

theorem l2Sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ l2Sq f := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (f i)

theorem l2Norm_sq {α : Type*} [Fintype α] (f : α → ℝ) :
    l2Norm f ^ 2 = l2Sq f := by
  rw [l2Norm, Real.sq_sqrt (l2Sq_nonneg f)]

/-- Finite real Cauchy--Schwarz in the profile norm. -/
theorem dotProduct_le_l2Norm_mul_l2Norm
    {α : Type*} [Fintype α] (f g : α → ℝ) :
    f ⬝ᵥ g ≤ l2Norm f * l2Norm g := by
  simpa [dotProduct, l2Norm, l2Sq] using
    (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset α) f g)

/-- Dirichlet energy of a profile on the exclusion sheet. -/
noncomputable def energy (f : Config N r → ℝ) : ℝ :=
  f ⬝ᵥ ((graph N r).lapMatrix ℝ).mulVec f

theorem energy_nonneg (f : Config N r → ℝ) : 0 ≤ energy f := by
  exact ((SimpleGraph.posSemidef_lapMatrix ℝ (graph N r)).dotProduct_mulVec_nonneg f)

/-- The massive finite-volume exclusion cell operator. -/
noncomputable def massiveOperator (mass diffusion : ℝ) :
    Matrix (Config N r) (Config N r) ℝ :=
  mass • 1 + diffusion • (graph N r).lapMatrix ℝ

theorem massiveOperator_posDef {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion) :
    (massiveOperator (N := N) (r := r) mass diffusion).PosDef := by
  exact (Matrix.PosDef.one.smul hmass).add_posSemidef
    ((SimpleGraph.posSemidef_lapMatrix ℝ (graph N r)).smul hdiffusion)

/-- The neutral first-difference source carried by an oriented exclusion edge. -/
def dipoleSource (x y : Config N r) : Config N r → ℝ :=
  Pi.single x 1 - Pi.single y 1

theorem dipoleSource_l2Sq {x y : Config N r} (hxy : x ≠ y) :
    l2Sq (dipoleSource x y) = 2 := by
  classical
  have hpoint : ∀ z : Config N r,
      ((if z = x then (1 : ℝ) else 0) - if z = y then 1 else 0) ^ 2
        = (if z = x then 1 else 0) + if z = y then 1 else 0 := by
    intro z
    by_cases hzx : z = x
    · subst z
      simp [hxy]
    · by_cases hzy : z = y
      · subst z
        simp [hxy, hzx]
      · simp [hzx, hzy]
  simp only [l2Sq, dipoleSource, Pi.sub_apply, Pi.single_apply]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  norm_num

/-- The exact finite-volume Green profile of a neutral collision-sheet source. -/
noncomputable def profile (mass diffusion : ℝ) (x y : Config N r) :
    Config N r → ℝ :=
  (massiveOperator (N := N) (r := r) mass diffusion)⁻¹.mulVec
    (dipoleSource x y)

theorem profile_cell_equation {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (x y : Config N r) :
    (massiveOperator (N := N) (r := r) mass diffusion).mulVec
        (profile mass diffusion x y) = dipoleSource x y := by
  have hunit := (massiveOperator_posDef (N := N) (r := r)
    hmass hdiffusion).isUnit
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  rw [profile, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]

/-- Testing the cell equation against its profile gives the exact massive
`L²` plus Dirichlet energy identity. -/
theorem profile_energy_identity {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    (x y : Config N r) :
    mass * l2Sq (profile mass diffusion x y)
      + diffusion * energy (profile mass diffusion x y)
      = profile mass diffusion x y ⬝ᵥ dipoleSource x y := by
  let psi := profile mass diffusion x y
  have heq := profile_cell_equation (N := N) (r := r)
    hmass hdiffusion x y
  have htest := congrArg (fun z => psi ⬝ᵥ z) heq
  rw [← htest]
  simp only [massiveOperator, energy, l2Sq, psi, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scalar core of the uniform Green estimate. -/
theorem massive_energy_scalar_bound
    {mass U E S : ℝ} (hmass : 0 < mass)
    (hU : 0 ≤ U) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hbound : mass * U + E ≤ Real.sqrt U * Real.sqrt S) :
    mass ^ 2 * U ≤ S ∧ mass * E ≤ S := by
  have ha : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have ha2 : Real.sqrt U ^ 2 = U := Real.sq_sqrt hU
  have hb2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hmassU : mass * U ≤ Real.sqrt U * Real.sqrt S := by linarith
  by_cases hzero : Real.sqrt U = 0
  · have hUz : U = 0 := by nlinarith
    subst U
    constructor
    · simpa using hS
    · have hEz : E = 0 := by nlinarith
      subst E
      simpa using hS
  · have hapos : 0 < Real.sqrt U := lt_of_le_of_ne ha (Ne.symm hzero)
    have hlinear : mass * Real.sqrt U ≤ Real.sqrt S := by
      nlinarith
    have hfirst : mass ^ 2 * U ≤ S := by
      nlinarith [sq_le_sq₀ (mul_nonneg hmass.le ha) hb |>.2 hlinear]
    have hsecond : mass * E ≤ S := by
      have hE' : E ≤ Real.sqrt U * Real.sqrt S :=
        (le_add_of_nonneg_left (mul_nonneg hmass.le hU)).trans hbound
      have hmul : mass * (Real.sqrt U * Real.sqrt S) ≤ S := by
        have hmul' := mul_le_mul_of_nonneg_right hlinear hb
        calc
          mass * (Real.sqrt U * Real.sqrt S)
              = (mass * Real.sqrt U) * Real.sqrt S := by ring
          _ ≤ Real.sqrt S * Real.sqrt S := hmul'
          _ = S := by nlinarith
      nlinarith
    exact ⟨hfirst, hsecond⟩

/-- Uniform finite-volume profile estimate for every hard-core exclusion edge.
The constants are independent of `N`, `r`, and the location of the edge. -/
theorem profile_uniform_bound {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    {x y : Config N r} (hxy : x ≠ y) :
    mass ^ 2 * l2Sq (profile mass diffusion x y) ≤ 2 ∧
      mass * (diffusion * energy (profile mass diffusion x y)) ≤ 2 := by
  let psi := profile mass diffusion x y
  have hid := profile_energy_identity (N := N) (r := r)
    hmass hdiffusion x y
  have hcs := dotProduct_le_l2Norm_mul_l2Norm psi (dipoleSource x y)
  have hsource : l2Norm (dipoleSource x y) = Real.sqrt 2 := by
    rw [l2Norm, dipoleSource_l2Sq hxy]
  rw [hsource] at hcs
  have hbound : mass * l2Sq psi + diffusion * energy psi
      ≤ Real.sqrt (l2Sq psi) * Real.sqrt 2 := by
    rw [hid]
    simpa [l2Norm] using hcs
  simpa [psi] using
    (massive_energy_scalar_bound (mass := mass) (U := l2Sq psi)
      (E := diffusion * energy psi) (S := 2) hmass
      (l2Sq_nonneg psi) (mul_nonneg hdiffusion (energy_nonneg psi))
      (by norm_num) hbound)

/-- The unweighted `L² + Dirichlet` form of the Green estimate. -/
theorem profile_l2_energy_bound {mass diffusion : ℝ}
    (hmass : 0 < mass) (hdiffusion : 0 ≤ diffusion)
    {x y : Config N r} (hxy : x ≠ y) :
    l2Sq (profile mass diffusion x y)
        + diffusion * energy (profile mass diffusion x y)
      ≤ 2 / mass ^ 2 + 2 / mass := by
  obtain ⟨hl2, henergy⟩ := profile_uniform_bound
    (N := N) (r := r) hmass hdiffusion hxy
  have hm2 : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hl2' : l2Sq (profile mass diffusion x y) ≤ 2 / mass ^ 2 := by
    rw [le_div_iff₀ hm2]
    nlinarith
  have henergy' : diffusion * energy (profile mass diffusion x y) ≤ 2 / mass := by
    rw [le_div_iff₀ hmass]
    nlinarith
  linarith

/-- Below every fixed Walsh-degree ceiling, all exact exclusion-sheet Green
profiles have one bound independent of the torus side length. -/
theorem finite_ceiling_profile_bound {R : ℕ} (g diffusion : ℝ)
    (hg : 0 < g) (hdiffusion : 0 ≤ diffusion)
    (x y : ∀ j : Fin R, Config N (j.1 + 2))
    (hxy : ∀ j, x j ≠ y j) :
    ∑ j : Fin R,
        (l2Sq (profile (N := N) (r := j.1 + 2)
            (g * (j.1 + 2)) diffusion (x j) (y j))
          + diffusion * energy
            (profile (N := N) (r := j.1 + 2)
              (g * (j.1 + 2)) diffusion (x j) (y j)))
      ≤ ∑ j : Fin R,
          (2 / (g * (j.1 + 2)) ^ 2 + 2 / (g * (j.1 + 2))) := by
  apply Finset.sum_le_sum
  intro j hj
  apply profile_l2_energy_bound
  · have hjpos : (0 : ℝ) < j.1 + 2 := by positivity
    positivity
  · exact hdiffusion
  · exact hxy j

/-- Squaring the manuscript's external `d/N` factor gives the exact
coefficient used by the finite-ceiling `N⁻²` estimate. -/
theorem l2Sq_smul (a : ℝ) {α : Type*} [Fintype α] (f : α → ℝ) :
    l2Sq (a • f) = a ^ 2 * l2Sq f := by
  simp only [l2Sq, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

/-- The concrete fixed-ceiling hard-core corrector estimate with the exact
external factor.  Its constant depends on the ceiling and renewal mass but
not on the torus side length. -/
theorem finite_ceiling_corrector_bound {R : ℕ} (g diffusion d D : ℝ)
    (hg : 0 < g) (hdiffusion : 0 ≤ diffusion)
    (hD : |d| ≤ D) (hD0 : 0 ≤ D)
    (x y : ∀ j : Fin R, Config N (j.1 + 2))
    (hxy : ∀ j, x j ≠ y j) :
    ∑ j : Fin R,
        l2Sq (((d / N) : ℝ) •
          profile (N := N) (r := j.1 + 2)
            (g * (j.1 + 2)) diffusion (x j) (y j))
      ≤ D ^ 2 *
          (∑ j : Fin R,
            (2 / (g * (j.1 + 2)) ^ 2 + 2 / (g * (j.1 + 2)))) /
          N ^ 2 := by
  let pnorm : Fin R → ℝ := fun j =>
    l2Sq (profile (N := N) (r := j.1 + 2)
      (g * (j.1 + 2)) diffusion (x j) (y j))
  let cnorm : Fin R → ℝ := fun j =>
    l2Sq (((d / N) : ℝ) •
      profile (N := N) (r := j.1 + 2)
        (g * (j.1 + 2)) diffusion (x j) (y j))
  apply NCG.hard_core_fixed_degree_bound N d D
    (∑ j : Fin R, (2 / (g * (j.1 + 2)) ^ 2 + 2 / (g * (j.1 + 2))))
    pnorm cnorm
  · exact Nat.pos_of_ne_zero (NeZero.ne N)
  · exact hD
  · exact hD0
  · intro j
    dsimp [pnorm]
    exact l2Sq_nonneg _
  · intro j
    dsimp [cnorm, pnorm]
    exact l2Sq_smul _ _
  · calc
      ∑ j, pnorm j ≤ ∑ j,
          (pnorm j + diffusion * energy
            (profile (N := N) (r := j.1 + 2)
              (g * (j.1 + 2)) diffusion (x j) (y j))) := by
            apply Finset.sum_le_sum
            intro j hj
            exact le_add_of_nonneg_right
              (mul_nonneg hdiffusion (energy_nonneg _))
      _ ≤ ∑ j : Fin R,
          (2 / (g * (j.1 + 2)) ^ 2 + 2 / (g * (j.1 + 2))) := by
            simpa [pnorm] using
              (finite_ceiling_profile_bound (N := N) g diffusion
                hg hdiffusion x y hxy)

end NCG.HardCoreExclusion
