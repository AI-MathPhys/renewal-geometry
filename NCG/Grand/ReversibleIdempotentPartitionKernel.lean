/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Lorentz.StationaryExchange
import NCG.Grand.TypedTransitionGeneratorAudit

/-!
# Reversible idempotent kernels are partition averagers

This is the structural core of `thm:accepted-joint-table`.  A finite
nonnegative stochastic kernel that is reversible for a faithful mass and
idempotent has positive-support components as its canonical partition, and
each row is the conditional stationary mass on its component.
-/

open Matrix

namespace NCG
namespace ReversibleIdempotentPartitionKernel

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Positive support relation of a finite kernel. -/
def supportRel (R : Matrix X X ℝ) (x y : X) : Prop := 0 < R x y

noncomputable instance supportRelDecidable (R : Matrix X X ℝ) :
    DecidableRel (supportRel R) := fun x y =>
  inferInstanceAs (Decidable (0 < R x y))

theorem supportRel_symmetric
    (R : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x)
    (hdb : ∀ x y, μ x * R x y = μ y * R y x) :
    Symmetric (supportRel R) := by
  intro x y hxy
  unfold supportRel at hxy ⊢
  have h := hdb x y
  nlinarith [hμ x, hμ y]

theorem supportRel_reflexive
    (R : Matrix X X ℝ)
    (hnonneg : ∀ x y, 0 ≤ R x y)
    (hrow : ∀ x, ∑ y, R x y = 1)
    (hsym : Symmetric (supportRel R))
    (hidem : R * R = R) :
    Reflexive (supportRel R) := by
  intro x
  have hex : ∃ y, 0 < R x y := by
    by_contra hall
    push Not at hall
    have hzero : ∀ y, R x y = 0 := by
      intro y
      exact le_antisymm (hall y) (hnonneg x y)
    have := hrow x
    simp_rw [hzero] at this
    norm_num at this
  obtain ⟨y, hxy⟩ := hex
  have hyx : 0 < R y x := hsym hxy
  have hentry := congrFun (congrFun hidem x) x
  rw [Matrix.mul_apply] at hentry
  unfold supportRel
  rw [← hentry]
  have hterm : 0 < R x y * R y x := mul_pos hxy hyx
  have hrest : 0 ≤ ∑ z ∈ Finset.univ.erase y, R x z * R z x := by
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (hnonneg x z) (hnonneg z x)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  nlinarith

theorem supportRel_transitive
    (R : Matrix X X ℝ)
    (hnonneg : ∀ x y, 0 ≤ R x y)
    (hidem : R * R = R) :
    Transitive (supportRel R) := by
  intro x y z hxy hyz
  have hentry := congrFun (congrFun hidem x) z
  rw [Matrix.mul_apply] at hentry
  unfold supportRel at hxy hyz ⊢
  rw [← hentry]
  have hterm : 0 < R x y * R y z := mul_pos hxy hyz
  have hrest : 0 ≤ ∑ w ∈ Finset.univ.erase y, R x w * R w z := by
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (hnonneg x w) (hnonneg w z)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  nlinarith

/-- Faithful reversibility, stochasticity, nonnegativity and idempotence make
positive support an equivalence relation. -/
def supportSetoid
    (R : Matrix X X ℝ) (μ : X → ℝ)
    (hnonneg : ∀ x y, 0 ≤ R x y)
    (hrow : ∀ x, ∑ y, R x y = 1)
    (hμ : ∀ x, 0 < μ x)
    (hdb : ∀ x y, μ x * R x y = μ y * R y x)
    (hidem : R * R = R) : Setoid X where
  r := supportRel R
  iseqv := {
    refl := supportRel_reflexive R hnonneg hrow
      (supportRel_symmetric R μ hμ hdb) hidem
    symm := by
      intro x y hxy
      exact supportRel_symmetric R μ hμ hdb hxy
    trans := by
      intro x y z hxy hyz
      exact supportRel_transitive R hnonneg hidem hxy hyz }

private theorem sum_subtype_eq_univ
    (p : X → Prop) [DecidablePred p] (f : X → ℝ)
    (hzero : ∀ z, ¬ p z → f z = 0) :
    (∑ z : {z // p z}, f z) = ∑ z, f z := by
  rw [← Finset.sum_subtype
    (p := p) (Finset.univ.filter p) (by simp) f]
  exact Finset.sum_subset (Finset.filter_subset p Finset.univ) (by
    intro z _ hz
    exact hzero z (by simpa using hz))

/-- Rows based at two points of the same positive-support component agree.
This is the finite irreducible-stationary-distribution argument restricted
to that component. -/
theorem rows_equal_of_supportRel
    (R : Matrix X X ℝ) (μ : X → ℝ)
    (hnonneg : ∀ x y, 0 ≤ R x y)
    (hrow : ∀ x, ∑ y, R x y = 1)
    (hμ : ∀ x, 0 < μ x)
    (hdb : ∀ x y, μ x * R x y = μ y * R y x)
    (hidem : R * R = R)
    {x y : X} (hxy : supportRel R x y) :
    (fun z => R x z) = fun z => R y z := by
  classical
  let S := supportSetoid R μ hnonneg hrow hμ hdb hidem
  let C := {z : X // S.r x z}
  let Q : C → C → ℝ := fun u v => R u v
  let α : C → ℝ := fun v => R x v
  let β : C → ℝ := fun v => R y v
  have hSxy : S.r x y := hxy
  have hQpos : ∀ u v, 0 < Q u v := by
    intro u v
    exact S.trans (S.symm u.property) v.property
  have hout (u : C) (z : X) (hz : ¬ S.r x z) : R u z = 0 := by
    apply le_antisymm
    · by_contra hnot
      have huz : S.r u z := lt_of_not_ge hnot
      exact hz (S.trans u.property huz)
    · exact hnonneg u z
  have hQrow : ∀ u, ∑ v, Q u v = 1 := by
    intro u
    change (∑ v : C, R u v) = 1
    rw [sum_subtype_eq_univ (fun z => S.r x z) (fun z => R u z)
      (hout u)]
    exact hrow u
  have hα1 : ∑ v, α v = 1 := by
    change (∑ v : C, R x v) = 1
    rw [sum_subtype_eq_univ (fun z => S.r x z) (fun z => R x z)]
    · exact hrow x
    · intro z hz
      exact le_antisymm (le_of_not_gt hz) (hnonneg x z)
  have hβ1 : ∑ v, β v = 1 := by
    change (∑ v : C, R y v) = 1
    rw [sum_subtype_eq_univ (fun z => S.r x z) (fun z => R y z)]
    · exact hrow y
    · exact hout ⟨y, hSxy⟩
  have hαstat : ∀ v, ∑ u, α u * Q u v = α v := by
    intro v
    change (∑ u : C, R x u * R u v) = R x v
    rw [sum_subtype_eq_univ (fun z => S.r x z)
      (fun z => R x z * R z v)]
    · simpa [Matrix.mul_apply] using congrFun (congrFun hidem x) v
    · intro z hz
      have hxz : R x z = 0 :=
        le_antisymm (le_of_not_gt hz) (hnonneg x z)
      simp [hxz]
  have hβstat : ∀ v, ∑ u, β u * Q u v = β v := by
    intro v
    change (∑ u : C, R y u * R u v) = R y v
    rw [sum_subtype_eq_univ (fun z => S.r x z)
      (fun z => R y z * R z v)]
    · simpa [Matrix.mul_apply] using congrFun (congrFun hidem y) v
    · intro z hz
      simp [hout ⟨y, hSxy⟩ z hz]
  have hab : α = β :=
    NCG.stationary_unique_of_pos hQpos hQrow hα1 hβ1 hαstat hβstat
  funext z
  by_cases hz : S.r x z
  · exact congrFun hab ⟨z, hz⟩
  · have hxz : R x z = 0 :=
      le_antisymm (le_of_not_gt hz) (hnonneg x z)
    have hyz : R y z = 0 := hout ⟨y, hSxy⟩ z hz
    rw [hxz, hyz]

/-- Total faithful mass of the positive-support component containing `x`. -/
noncomputable def classMass (R : Matrix X X ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ z, if supportRel R x z then μ z else 0

/-- Mass of a block of an independently presented finite partition. -/
noncomputable def partitionMass
    (T : Setoid X) [DecidableRel T.r] (μ : X → ℝ) (x : X) : ℝ :=
  ∑ z, if T.r x z then μ z else 0

theorem partitionMass_pos
    (T : Setoid X) [DecidableRel T.r]
    (μ : X → ℝ) (hμ : ∀ x, 0 < μ x) (x : X) :
    0 < partitionMass T μ x := by
  unfold partitionMass
  have hterm : (if T.r x x then μ x else 0) = μ x := by
    rw [if_pos (T.refl x)]
  have hrest :
      0 ≤ ∑ z ∈ Finset.univ.erase x, if T.r x z then μ z else 0 := by
    exact Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact (hμ z).le
      · exact le_rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hterm]
  linarith [hμ x]

theorem classMass_pos
    (R : Matrix X X ℝ) (μ : X → ℝ) (hμ : ∀ x, 0 < μ x)
    {x : X} (hxx : supportRel R x x) :
    0 < classMass R μ x := by
  classical
  unfold classMass
  have hterm : (if supportRel R x x then μ x else 0) = μ x := by
    rw [if_pos hxx]
  have hrest :
      0 ≤ ∑ z ∈ Finset.univ.erase x,
        if supportRel R x z then μ z else 0 := by
    exact Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact (hμ z).le
      · exact le_rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hterm]
  linarith [hμ x]

/-- Exact canonical partition formula.  The partition is not supplied as
auxiliary data: it is the positive-support setoid of the kernel itself. -/
theorem kernel_eq_partitionAverager
    (R : Matrix X X ℝ) (μ : X → ℝ)
    (hnonneg : ∀ x y, 0 ≤ R x y)
    (hrow : ∀ x, ∑ y, R x y = 1)
    (hμ : ∀ x, 0 < μ x)
    (hdb : ∀ x y, μ x * R x y = μ y * R y x)
    (hidem : R * R = R) :
    ∀ x y, R x y =
      if supportRel R x y then μ y / classMass R μ x else 0 := by
  classical
  let S := supportSetoid R μ hnonneg hrow hμ hdb hidem
  intro x y
  have hpoint : ∀ z, R x z =
      if supportRel R x z then μ z * (R x x / μ x) else 0 := by
    intro z
    by_cases hxz : supportRel R x z
    · rw [if_pos hxz]
      have hrows := rows_equal_of_supportRel R μ hnonneg hrow hμ hdb hidem hxz
      have hzx : R z x = R x x := congrFun hrows x |>.symm
      have hbalance := hdb x z
      rw [hzx] at hbalance
      field_simp [ne_of_gt (hμ x)]
      nlinarith
    · rw [if_neg hxz]
      exact le_antisymm (le_of_not_gt hxz) (hnonneg x z)
  have hnorm : (R x x / μ x) * classMass R μ x = 1 := by
    calc
      (R x x / μ x) * classMass R μ x =
          ∑ z, if supportRel R x z then
            μ z * (R x x / μ x) else 0 := by
            unfold classMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            split_ifs <;> ring
      _ = ∑ z, R x z := by
        apply Finset.sum_congr rfl
        intro z _
        exact (hpoint z).symm
      _ = 1 := hrow x
  by_cases hxy : supportRel R x y
  · rw [if_pos hxy, hpoint y, if_pos hxy]
    have hxx : supportRel R x x := S.refl x
    have hmass := classMass_pos R μ hμ hxx
    have hc : R x x / μ x = 1 / classMass R μ x :=
      (eq_div_iff (ne_of_gt hmass)).2 hnorm
    rw [hc]
    ring
  · rw [if_neg hxy, hpoint y, if_neg hxy]

/-- Uniqueness of the partition in the averaging representation: any setoid
whose conditional-mass averager is `R` must be the positive-support setoid. -/
theorem partition_unique_of_averager_formula
    (R : Matrix X X ℝ) (μ : X → ℝ) (hμ : ∀ x, 0 < μ x)
    (T : Setoid X) [DecidableRel T.r]
    (hformula : ∀ x y, R x y =
      if T.r x y then μ y / partitionMass T μ x else 0) :
    T = { r := supportRel R
          iseqv := {
            refl := fun x => by
              unfold supportRel
              rw [hformula x x, if_pos (T.refl x)]
              exact div_pos (hμ x) (partitionMass_pos T μ hμ x)
            symm := fun {x y} hxy => by
              unfold supportRel at hxy ⊢
              have hTxy : T.r x y := by
                by_contra hTnot
                rw [hformula x y, if_neg hTnot] at hxy
                linarith
              have hTyx := T.symm hTxy
              rw [hformula y x, if_pos hTyx]
              exact div_pos (hμ x) (partitionMass_pos T μ hμ y)
            trans := fun {x y z} hxy hyz => by
              unfold supportRel at hxy hyz ⊢
              have hTxy : T.r x y := by
                by_contra hTnot
                rw [hformula x y, if_neg hTnot] at hxy
                linarith
              have hTyz : T.r y z := by
                by_contra hTnot
                rw [hformula y z, if_neg hTnot] at hyz
                linarith
              rw [hformula x z, if_pos (T.trans hTxy hTyz)]
              exact div_pos (hμ z) (partitionMass_pos T μ hμ x) } } := by
  apply Setoid.ext
  intro x y
  change T.r x y ↔ supportRel R x y
  constructor
  · intro hxy
    unfold supportRel
    rw [hformula x y, if_pos hxy]
    exact div_pos (hμ y) (partitionMass_pos T μ hμ x)
  · intro hxy
    by_contra hnot
    unfold supportRel at hxy
    rw [hformula x y, if_neg hnot] at hxy
    linarith

/-- Stationary free action reconstructed from the faithful marginal. -/
noncomputable def stationaryFreeAction (μ : X → ℝ) (x : X) : ℝ :=
  -Real.log (μ x)

/-- Detailed balance makes the free-action increment exactly the negative
logarithmic transition ratio on every supported edge. -/
theorem supportedTransition_logRatio_add_freeAction_eq_zero
    (R : Matrix X X ℝ) (μ : X → ℝ)
    (hμ : ∀ x, 0 < μ x)
    (hdb : ∀ x y, μ x * R x y = μ y * R y x)
    {x y : X} (hxy : supportRel R x y) :
    Real.log (R x y / R y x) +
        stationaryFreeAction μ y - stationaryFreeAction μ x = 0 := by
  have hyx : 0 < R y x :=
    supportRel_symmetric R μ hμ hdb hxy
  have hratio : R x y / R y x = μ y / μ x := by
    apply (div_eq_div_iff hyx.ne' (hμ x).ne').2
    nlinarith [hdb x y]
  rw [hratio, Real.log_div (hμ y).ne' (hμ x).ne']
  unfold stationaryFreeAction
  ring

end ReversibleIdempotentPartitionKernel
end NCG
