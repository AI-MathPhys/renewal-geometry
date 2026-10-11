/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledUniqueness
import RenewalGeometry.Continuum.ActualJetKatoRealization

/-!
# Coupled uniqueness with a vector-valued first-order block, from bounds on a period cell

Generic companion of `GenCpl.coupled_unique` (`lem:generated-physical-identification`, coupled
spinors): the first-order block takes values in a finite-dimensional space `E` with a symmetric
positive bilinear form for which the principal operators are symmetric (the symmetriser), and
the zero-order bounds need only hold on one period cell `[t₀, t₁] × [0, 1]³` (periodicity extends
them).

* `cube`, `isCompact_cube`, `cube_subset`, `slab_of_cube` — the period cell and the periodic
  extension of inequalities;
* `bdd_cube`, `endBdd_cube` — continuous coefficients (and continuous families of linear maps)
  are bounded on the cell;
* **`coupled_unique_E`** — uniqueness for `(u, w)` with `u` wave-type and `w` symmetric
  hyperbolic (`∂_tw + Σ_jA^j∂_jw`, `A^j` `b`-symmetric), zero-order coupled.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.GenCplE

open SobolevOpen (pd)
open SymHypEnergy PeriodicCube SlabWaveHk GenHarmonic GenGauss ActualJetBridge GenCpl

set_option linter.unusedSectionVars false

/-! ### The period cell -/

/-- The period cell `[t₀, t₁] × [0, 1]³`. -/
def cube (t₀ t₁ : ℝ) : Set (ST 3) :=
  (fun p : ℝ × (Fin 3 → ℝ) => (Fin.cons p.1 p.2 : ST 3)) '' (Set.Icc t₀ t₁ ×ˢ Set.Icc 0 1)

theorem isCompact_cube (t₀ t₁ : ℝ) : IsCompact (cube t₀ t₁) :=
  (isCompact_Icc.prod isCompact_Icc).image continuous_cons2

theorem cube_subset_slab (t₀ t₁ : ℝ) : cube t₀ t₁ ⊆ slab t₀ t₁ := by
  rintro _ ⟨p, hp, rfl⟩
  exact hp.1

/-- **Periodic extension**: an inequality between periodic real functions on the cell holds on
the slab. -/
theorem slab_of_cube {f g : ST 3 → ℝ} (hf : IsSPeriodic f) (hg : IsSPeriodic g) {t₀ t₁ : ℝ}
    (h : ∀ x ∈ cube t₀ t₁, f x ≤ g x) : ∀ x ∈ slab t₀ t₁, f x ≤ g x := by
  intro x hx
  have hfr : (fun i => Int.fract (Fin.tail x i)) ∈ Set.Icc (0 : Fin 3 → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have h1 := (hf.slice (x 0)).apply_fract (Fin.tail x)
  have h2 := (hg.slice (x 0)).apply_fract (Fin.tail x)
  rw [Fin.cons_self_tail] at h1 h2
  rw [← h1, ← h2]
  exact h _ ⟨(x 0, _), ⟨hx, hfr⟩, rfl⟩

/-- Continuous coefficients are bounded on the cell. -/
theorem bdd_cube {E : Type*} [NormedAddCommGroup E] {f : ST 3 → E} (hf : Continuous f)
    (t₀ t₁ : ℝ) : ∃ C, 0 ≤ C ∧ ∀ x ∈ cube t₀ t₁, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cube t₀ t₁).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

/-- **Continuous families of linear maps are uniformly bounded on the cell.** -/
theorem endBdd_cube {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ST 3 → E →ₗ[ℝ] F}
    (hT : ∀ v, Continuous (fun y => T y v)) (t₀ t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ cube t₀ t₁, ∀ v, ‖T x v‖ ≤ C * ‖v‖ := by
  set L : ST 3 → E →L[ℝ] F := fun y => LinearMap.toContinuousLinearMap (T y)
  have hL : Continuous L := continuous_clm_apply.2 fun v => hT v
  obtain ⟨C, hC0, hC⟩ := bdd_cube hL t₀ t₁
  exact ⟨C, hC0, fun x hx v => ((L x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))⟩

/-! ### The vector-valued coupled uniqueness theorem -/

theorem norm_le_of_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (κ : E ≃ₗ[ℝ] (Fin n → ℝ)) :
    ∃ C, 0 ≤ C ∧ (∀ v, ‖κ v‖ ≤ C * ‖v‖) ∧ ∀ v, ‖v‖ ≤ C * ‖κ v‖ := by
  set L := LinearMap.toContinuousLinearMap κ.toLinearMap
  set L' := LinearMap.toContinuousLinearMap κ.symm.toLinearMap
  refine ⟨max ‖L‖ ‖L'‖, le_max_of_le_left (norm_nonneg _), fun v => ?_, fun v => ?_⟩
  · exact (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have : v = L' (κ v) := by simp [L']
    calc ‖v‖ = ‖L' (κ v)‖ := by rw [← this]
      _ ≤ ‖L'‖ * ‖κ v‖ := L'.le_opNorm _
      _ ≤ max ‖L‖ ‖L'‖ * ‖κ v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- **Uniqueness for coupled wave / symmetric first-order systems, vector-valued first-order
block, bounds on one period cell.** -/
theorem coupled_unique_E {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (bE : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hbs : ∀ v w, bE v w = bE w v)
    (hbp : ∀ v, v ≠ 0 → 0 < bE v v) {u : ST 3 → Fin k → ℝ} {w : ST 3 → E}
    {e gi θ : ST 3 → Fin 4 → Fin 4 → ℝ} {Aop : Fin 3 → ST 3 → E →ₗ[ℝ] E}
    {a t₀ t₁ b : ℝ} (ha : a < t₀) (h01 : t₀ < t₁) (hb : t₁ < b)
    (hu : ContDiff ℝ ∞ u) (hup : IsSPeriodic u) (hw : ContDiff ℝ ∞ w) (hwp : IsSPeriodic w)
    (he : ContDiff ℝ ∞ e) (hep : IsSPeriodic e)
    (he0 : ∀ x (c : Fin 3), e x c.succ 0 = 0) (he00 : ∀ x, 0 < e x 0 0)
    (hadapt : ∀ x μ ν, gi x μ ν = -(e x 0 μ * e x 0 ν) + ∑ c : Fin 3, e x c.succ μ * e x c.succ ν)
    (hθ : Continuous θ) (hθp : IsSPeriodic θ)
    (hcof : ∀ x, ∀ (v : Fin 4 → ℝ) γ, v γ = ∑ B, θ x B γ * ∑ β, e x B β * v β)
    (hA : ∀ j v, ContDiff ℝ ∞ (fun y => Aop j y v)) (hAp : ∀ j, IsSPeriodic (Aop j))
    (hAs : ∀ j y v v', bE (Aop j y v) v' = bE v (Aop j y v'))
    {K : ℝ} (hK : 0 ≤ K)
    (hequ : ∀ x ∈ cube t₀ t₁, ∀ i, |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i| ≤
      K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖))
    (heqw : ∀ x ∈ cube t₀ t₁, ‖pd w 0 x + ∑ j : Fin 3, Aop j x (pd w j.succ x)‖ ≤
      K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖))
    (h0 : ∀ y : Fin 3 → ℝ, u (Fin.cons t₀ y) = 0)
    (h0t : ∀ y : Fin 3 → ℝ, pd u 0 (Fin.cons t₀ y) = 0)
    (hw0 : ∀ y : Fin 3 → ℝ, w (Fin.cons t₀ y) = 0) :
    ∀ x ∈ slab t₀ t₁, u x = 0 ∧ w x = 0 := by
  obtain ⟨κ, hκ⟩ := ActualJetKato.exists_euclidean_coords bE hbs hbp
  obtain ⟨Cκ, hCκ0, hCκ1, hCκ2⟩ := norm_le_of_equiv κ
  set w' : ST 3 → Fin (Module.finrank ℝ E) → ℝ := fun y => κ (w y) with hw'
  set M : Fin 3 → ST 3 → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun j y i l =>
    κ (Aop j y (κ.symm (Pi.single l 1))) i with hM
  have hw's : ContDiff ℝ ∞ w' := (LinearMap.toContinuousLinearMap κ.toLinearMap).contDiff.comp hw
  have hw'p : IsSPeriodic w' := fun k' x => by simp only [hw', hwp k' x]
  have hpdw' : ∀ μ x, pd w' μ x = κ (pd w μ x) := fun μ x =>
    pd_clm (LinearMap.toContinuousLinearMap κ.toLinearMap) (hw.differentiable (by simp) x) μ
  -- the coefficient matrices
  have hMv : ∀ j y (v : Fin (Module.finrank ℝ E) → ℝ) i, ∑ l, M j y i l * v l = κ (Aop j y (κ.symm v)) i := by
    intro j y v i
    have hv : v = ∑ l, v l • (Pi.single l (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) := by
      funext q; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hM]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hMs : ∀ j x i l, M j x i l = M j x l i := by
    intro j x i l
    have e1 : ∀ i l, M j x i l =
        bE (Aop j x (κ.symm (Pi.single l 1))) (κ.symm (Pi.single i 1)) := by
      intro i l
      have h := hκ (κ (Aop j x (κ.symm (Pi.single l 1)))) (Pi.single i 1)
      rw [LinearEquiv.symm_apply_apply] at h
      rw [h]
      simp [Pi.single_apply, hM]
    rw [e1, e1, hAs, hbs]
  have hMc : ∀ j, ContDiff ℝ ∞ (M j) := by
    intro j
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun l => ?_
    have := (LinearMap.toContinuousLinearMap κ.toLinearMap).contDiff.comp
      (hA j (κ.symm (Pi.single l 1)))
    exact contDiff_pi.1 this i
  have hMp : ∀ j, IsSPeriodic (M j) := fun j k' x => by
    simp only [hM, hAp j k' x]
  -- periodic extension of the bounds
  have hpdu : ∀ β, IsSPeriodic (pd u β) := fun β => isSPeriodic_pd hup β
  have hpdpdu : ∀ β μ, IsSPeriodic (pd (pd u β) μ) := fun β μ => isSPeriodic_pd (hpdu β) μ
  have hpdw : ∀ μ, IsSPeriodic (pd w μ) := fun μ => isSPeriodic_pd hwp μ
  have hgip : IsSPeriodic gi := fun k' x => by
    funext μ ν; rw [hadapt, hadapt, hep k' x]
  have hequ' : ∀ x ∈ slab t₀ t₁, ∀ i, |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i| ≤
      K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖) := by
    intro x hx i
    refine slab_of_cube (f := fun x => |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i|)
      (g := fun x => K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖)) ?_ ?_ (fun x hx => hequ x hx i) x hx
    · intro k' y
      simp only [hgip k' y, hpdpdu _ _ k' y]
    · intro k' y
      simp only [hup k' y, hpdu _ k' y, hwp k' y]
  set K' := Cκ * K * (2 + Cκ) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have heqw' : ∀ x ∈ slab t₀ t₁, ‖(fun i => pd w' 0 x i + ∑ j : Fin 3, ∑ l, M j x i l *
      pd w' j.succ x l)‖ ≤ K' * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w' x‖) := by
    have hrow : ∀ x, (fun i => pd w' 0 x i + ∑ j : Fin 3, ∑ l, M j x i l * pd w' j.succ x l) =
        κ (pd w 0 x + ∑ j : Fin 3, Aop j x (pd w j.succ x)) := by
      intro x
      funext i
      simp only [hMv, hpdw', LinearEquiv.symm_apply_apply, map_add, map_sum, Pi.add_apply,
        Finset.sum_apply]
    intro x hx
    rw [hrow]
    refine slab_of_cube (f := fun x => ‖κ (pd w 0 x + ∑ j : Fin 3, Aop j x (pd w j.succ x))‖)
      (g := fun x => K' * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w' x‖)) ?_ ?_ (fun x hx => ?_) x hx
    · intro k' y
      simp only [hpdw _ k' y, hAp _ k' y]
    · intro k' y
      simp only [hup k' y, hpdu _ k' y, hw'p k' y]
    · have h1 := hCκ1 (pd w 0 x + ∑ j : Fin 3, Aop j x (pd w j.succ x))
      have h2 := heqw x hx
      have h3 := hCκ2 (w x)
      have hnn : 0 ≤ ‖u x‖ + ∑ γ, ‖pd u γ x‖ := by positivity
      have hw'n := norm_nonneg (w' x)
      calc ‖κ (pd w 0 x + ∑ j : Fin 3, Aop j x (pd w j.succ x))‖ ≤
          Cκ * (K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w x‖)) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hCκ0)
        _ ≤ Cκ * (K * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + Cκ * ‖w' x‖)) := by gcongr
        _ ≤ K' * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w' x‖) := by
            rw [hK']
            nlinarith [mul_nonneg hCκ0 hK, mul_nonneg (mul_nonneg hCκ0 hK) hnn,
              mul_nonneg (mul_nonneg hCκ0 hK) hw'n,
              mul_nonneg (mul_nonneg (mul_nonneg hCκ0 hK) hCκ0) hnn]
  have hequ'' : ∀ x ∈ slab t₀ t₁, ∀ i, |∑ μ, ∑ β, gi x μ β * pd (pd u β) μ x i| ≤
      (K * (1 + Cκ)) * (‖u x‖ + ∑ γ, ‖pd u γ x‖ + ‖w' x‖) := by
    intro x hx i
    refine (hequ' x hx i).trans ?_
    have h3 := hCκ2 (w x)
    have hnn : 0 ≤ ‖u x‖ + ∑ γ, ‖pd u γ x‖ := by positivity
    have hw'n := norm_nonneg (w' x)
    nlinarith [mul_nonneg hK hnn, mul_nonneg hK hw'n, mul_nonneg (mul_nonneg hK hCκ0) hnn,
      mul_le_mul_of_nonneg_left h3 hK]
  have hsol := coupled_unique (u := u) (w := w') (e := e) (gi := gi) (θ := θ) (M := M) ha h01 hb
    (hu.of_le (by norm_cast)).contDiffOn hup (hw's.of_le (by norm_cast)).contDiffOn hw'p
    (he.of_le (by norm_cast)).contDiffOn hep he0 he00 hadapt hθ.continuousOn hθp
    (fun x _ => hcof x) (fun j => ((hMc j).of_le (by norm_cast)).contDiffOn) hMp hMs
    (by positivity : (0 : ℝ) ≤ max (K * (1 + Cκ)) K') ?_ ?_ h0 h0t
    (fun y => by simp only [hw', hw0 y, map_zero])
  · intro x hx
    obtain ⟨h1, h2⟩ := hsol x hx
    refine ⟨h1, ?_⟩
    have : κ (w x) = 0 := h2
    simpa using this
  · intro x hx i
    exact (hequ'' x hx i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro x hx
    exact (heqw' x hx).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end RenewalGeometry.GenCplE
