/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Fast-clock lower bound for a general root race (`lem:supp-fast-clock`,
  emergent-spacetime manuscript)

For a finite family of root vectors `r_a ∈ ℝ³` (any finite index type, any vectors — not
only the six `A₃` roots of `eq:a3-roots-main`), nonnegative directed rates `k_a^±` and mesh
scale `h > 0`, the predictable bracket of `eq:bracket-drift-main` is
`𝓑_h = h² ∑_a (k_a^+ + k_a^-) r_a r_aᵀ`.

* `FastClock.fast_clock_bound` (`eq:supp-fast-clock-bound`): if `‖r_a‖ ≤ R` (Euclidean
  norm, `R > 0`) and `𝓑_h ⪰ c I₃` (quadratic-form inequality), then
  `∑_a (k_a^+ + k_a^-) ≥ 3c / (R² h²)` — the trace argument
  `3c ≤ tr 𝓑_h ≤ R² h² ∑_a (k_a^+ + k_a^-)`.
* `FastClock.fast_clock_bound_posSemidef`: the same with `𝓑_h ⪰ cI₃` in the Loewner sense
  `(𝓑_h - c I).PosSemidef`.
* `FastClock.fast_clock_bound_euclidean`: the same with `r_a ∈ EuclideanSpace ℝ (Fin 3)`
  and `‖r_a‖ ≤ R`.
* `FastClock.fast_clock_collapse` (the "in particular" clause): if the total rate is
  `O(h⁻¹)` as `h → 0⁺`, then every entry of `𝓑_h` is `O(h)` and `𝓑_h → 0`: the continuum
  bracket collapses.
* `FastClock.fast_clock_no_uniform_coercivity`: consequently no fixed `c > 0` can satisfy
  `𝓑_h ⪰ c I₃` along `h → 0⁺` for an `O(h⁻¹)` clock.
-/

open Matrix Finset Filter Asymptotics

namespace RenewalGeometry
namespace FastClock

variable {ι : Type*} [Fintype ι]

/-- The predictable bracket `𝓑_h = h² ∑_a (k_a^+ + k_a^-) r_a r_aᵀ`
(`eq:bracket-drift-main`) for a general finite root family `r`. -/
noncomputable def bracket (h : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (h ^ 2) • ∑ a, (kp a + km a) • vecMulVec (r a) (r a)

theorem bracket_apply (h : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ) (i j : Fin 3) :
    bracket h kp km r i j = h ^ 2 * ∑ a, (kp a + km a) * (r a i * r a j) := by
  unfold bracket
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rfl

/-- The trace of the bracket: `tr 𝓑_h = h² ∑_a (k_a^+ + k_a^-) ‖r_a‖²`. -/
theorem bracket_trace (h : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ) :
    ∑ i, bracket h kp km r i i = h ^ 2 * ∑ a, (kp a + km a) * ∑ i, r a i ^ 2 := by
  simp_rw [bracket_apply, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf

/-- `lem:supp-fast-clock`, `eq:supp-fast-clock-bound`: for any finite root family with
`‖r_a‖ ≤ R` (Euclidean, `∑ᵢ r_{a,i}² ≤ R²`), nonnegative rates and `𝓑_h ⪰ c I₃`,
`∑_a (k_a^+ + k_a^-) ≥ 3c/(R² h²)`. -/
theorem fast_clock_bound (h c R : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ)
    (hh : 0 < h) (hR : 0 < R) (hkp : ∀ a, 0 ≤ kp a) (hkm : ∀ a, 0 ≤ km a)
    (hr : ∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2)
    (hB : ∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (bracket h kp km r *ᵥ v)) :
    3 * c / (R ^ 2 * h ^ 2) ≤ ∑ a, (kp a + km a) := by
  -- diagonal entries: `c ≤ 𝓑_h i i`
  have hdiag : ∀ i, c ≤ bracket h kp km r i i := by
    intro i
    have := hB (Pi.single i 1)
    simpa [dotProduct, mulVec, Pi.single_apply] using this
  -- trace bound `3c ≤ tr 𝓑_h`
  have htr : 3 * c ≤ ∑ i, bracket h kp km r i i := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) fun i _ => hdiag i
    have h3 : (∑ _i : Fin 3, c) = 3 * c := by simp
    linarith
  rw [bracket_trace] at htr
  -- `tr 𝓑_h ≤ R² h² ∑ (k⁺ + k⁻)`
  have hle : ∑ a, (kp a + km a) * ∑ i, r a i ^ 2 ≤ R ^ 2 * ∑ a, (kp a + km a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [mul_comm (R ^ 2)]
    exact mul_le_mul_of_nonneg_left (hr a) (add_nonneg (hkp a) (hkm a))
  have hpos : 0 < R ^ 2 * h ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg h)]

/-- `lem:supp-fast-clock` with `𝓑_h ⪰ c I₃` in the Loewner sense. -/
theorem fast_clock_bound_posSemidef (h c R : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ)
    (hh : 0 < h) (hR : 0 < R) (hkp : ∀ a, 0 ≤ kp a) (hkm : ∀ a, 0 ≤ km a)
    (hr : ∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2)
    (hB : (bracket h kp km r - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    3 * c / (R ^ 2 * h ^ 2) ≤ ∑ a, (kp a + km a) := by
  refine fast_clock_bound h c R kp km r hh hR hkp hkm hr fun v => ?_
  have h0 := hB.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul] at h0
  have hvv : v ⬝ᵥ v = ∑ i, v i ^ 2 := by
    simp [dotProduct, sq]
  rw [hvv] at h0
  linarith

/-- `lem:supp-fast-clock` for roots in `EuclideanSpace ℝ (Fin 3)` with `‖r_a‖ ≤ R`. -/
theorem fast_clock_bound_euclidean (h c R : ℝ) (kp km : ι → ℝ)
    (r : ι → EuclideanSpace ℝ (Fin 3))
    (hh : 0 < h) (hR : 0 < R) (hkp : ∀ a, 0 ≤ kp a) (hkm : ∀ a, 0 ≤ km a)
    (hr : ∀ a, ‖r a‖ ≤ R)
    (hB : ∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2)
      ≤ v ⬝ᵥ (bracket h kp km (fun a => (r a : Fin 3 → ℝ)) *ᵥ v)) :
    3 * c / (R ^ 2 * h ^ 2) ≤ ∑ a, (kp a + km a) := by
  refine fast_clock_bound h c R kp km _ hh hR hkp hkm (fun a => ?_) hB
  have h1 := EuclideanSpace.norm_sq_eq (r a)
  have h2 : ‖r a‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hr a) 2
  simp only [Real.norm_eq_abs, sq_abs] at h1
  calc ∑ i, (r a : Fin 3 → ℝ) i ^ 2 = ‖r a‖ ^ 2 := by rw [h1]
    _ ≤ R ^ 2 := h2

/-- Entrywise control: `|𝓑_h i j| ≤ R² h² ∑_a (k_a^+ + k_a^-)` when `‖r_a‖ ≤ R`. -/
theorem bracket_entry_le (h R : ℝ) (kp km : ι → ℝ) (r : ι → Fin 3 → ℝ)
    (hkp : ∀ a, 0 ≤ kp a) (hkm : ∀ a, 0 ≤ km a)
    (hr : ∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2) (i j : Fin 3) :
    |bracket h kp km r i j| ≤ R ^ 2 * h ^ 2 * ∑ a, (kp a + km a) := by
  rw [bracket_apply, abs_mul, abs_of_nonneg (sq_nonneg h)]
  have hcoord : ∀ a k, r a k ^ 2 ≤ R ^ 2 := fun a k =>
    le_trans (Finset.single_le_sum (f := fun i => r a i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)) (hr a)
  have hprod : ∀ a, |r a i * r a j| ≤ R ^ 2 := by
    intro a
    rw [abs_mul]
    have h1 := hcoord a i
    have h2 := hcoord a j
    nlinarith [abs_nonneg (r a i), abs_nonneg (r a j), sq_abs (r a i), sq_abs (r a j),
      sq_nonneg (|r a i| - |r a j|)]
  have hsum : |∑ a, (kp a + km a) * (r a i * r a j)| ≤ R ^ 2 * ∑ a, (kp a + km a) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [abs_mul, abs_of_nonneg (add_nonneg (hkp a) (hkm a)), mul_comm (R ^ 2)]
    exact mul_le_mul_of_nonneg_left (hprod a) (add_nonneg (hkp a) (hkm a))
  calc h ^ 2 * |∑ a, (kp a + km a) * (r a i * r a j)|
      ≤ h ^ 2 * (R ^ 2 * ∑ a, (kp a + km a)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg h)
    _ = R ^ 2 * h ^ 2 * ∑ a, (kp a + km a) := by ring

/-- `lem:supp-fast-clock`, "in particular" clause: a total rate `O(h⁻¹)` (as `h → 0⁺`)
produces `𝓑_h = O(h)` entrywise and `𝓑_h → 0`, a collapsed continuum bracket. -/
theorem fast_clock_collapse (R : ℝ) (kp km : ℝ → ι → ℝ) (r : ι → Fin 3 → ℝ)
    (hkp : ∀ h a, 0 ≤ kp h a) (hkm : ∀ h a, 0 ≤ km h a)
    (hr : ∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2)
    (hrate : (fun h => ∑ a, (kp h a + km h a)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => h⁻¹)) :
    (∀ i j, (fun h => bracket h (kp h) (km h) r i j) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => h)) ∧
    Tendsto (fun h => bracket h (kp h) (km h) r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC⟩ := hrate.bound
  have hpos : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < h := self_mem_nhdsWithin
  have hentry : ∀ i j, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖bracket h (kp h) (km h) r i j‖ ≤ (R ^ 2 * C) * ‖h‖ := by
    intro i j
    filter_upwards [hC, hpos] with h hCh hh
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh]
    have hS : 0 ≤ ∑ a, (kp h a + km h a) :=
      Finset.sum_nonneg fun a _ => add_nonneg (hkp h a) (hkm h a)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hS,
      abs_of_pos (inv_pos.mpr hh)] at hCh
    have he := bracket_entry_le h R (kp h) (km h) r (hkp h) (hkm h) hr i j
    have hh2 : h ^ 2 * ∑ a, (kp h a + km h a) ≤ C * h := by
      have := mul_le_mul_of_nonneg_left hCh (sq_nonneg h)
      calc h ^ 2 * ∑ a, (kp h a + km h a) ≤ h ^ 2 * (C * h⁻¹) := this
        _ = C * h := by field_simp
    calc |bracket h (kp h) (km h) r i j| ≤ R ^ 2 * h ^ 2 * ∑ a, (kp h a + km h a) := he
      _ = R ^ 2 * (h ^ 2 * ∑ a, (kp h a + km h a)) := by ring
      _ ≤ R ^ 2 * (C * h) := mul_le_mul_of_nonneg_left hh2 (sq_nonneg R)
      _ = R ^ 2 * C * h := by ring
  have hO : ∀ i j, (fun h => bracket h (kp h) (km h) r i j) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => h) := fun i j => IsBigO.of_bound _ (hentry i j)
  refine ⟨hO, ?_⟩
  have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  exact (hO i j).trans_tendsto hid

/-- For an `O(h⁻¹)` clock no fixed `c > 0` gives `𝓑_h ⪰ c I₃` along `h → 0⁺`. -/
theorem fast_clock_no_uniform_coercivity (R c : ℝ) (kp km : ℝ → ι → ℝ)
    (r : ι → Fin 3 → ℝ) (hc : 0 < c)
    (hkp : ∀ h a, 0 ≤ kp h a) (hkm : ∀ h a, 0 ≤ km h a)
    (hr : ∀ a, ∑ i, r a i ^ 2 ≤ R ^ 2)
    (hrate : (fun h => ∑ a, (kp h a + km h a)) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => h⁻¹)) :
    ¬ ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v : Fin 3 → ℝ, c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (bracket h (kp h) (km h) r *ᵥ v) := by
  intro hev
  have hT := (fast_clock_collapse R kp km r hkp hkm hr hrate).2
  have h00 : Tendsto (fun h => bracket h (kp h) (km h) r 0 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (continuous_apply_apply (0 : Fin 3) (0 : Fin 3)).tendsto
      (0 : Matrix (Fin 3) (Fin 3) ℝ)
    exact this.comp hT
  have hlow : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ bracket h (kp h) (km h) r 0 0 := by
    filter_upwards [hev] with h hh
    have := hh (Pi.single 0 1)
    simpa [dotProduct, mulVec, Pi.single_apply] using this
  have hlt : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), bracket h (kp h) (km h) r 0 0 < c :=
    h00.eventually (gt_mem_nhds hc)
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := inferInstance
  obtain ⟨h, h1, h2⟩ := (hlow.and hlt).exists
  linarith

/-- Non-vacuity (sharp case): the three coordinate roots `r_a = e_a` with `k_a^+ = 1`,
`k_a^- = 0`, `h = 1` give `𝓑_1 = I₃ ⪰ 1·I₃`, and the bound `3 ≤ ∑_a (k_a^+ + k_a^-) = 3`
is attained. -/
example : 3 * 1 / ((1 : ℝ) ^ 2 * 1 ^ 2)
    ≤ ∑ a : Fin 3, ((fun _ => (1 : ℝ)) a + (fun _ => (0 : ℝ)) a) := by
  refine fast_clock_bound 1 1 1 (fun _ => 1) (fun _ => 0) (fun a => Pi.single a 1)
    one_pos one_pos (fun _ => zero_le_one) (fun _ => le_refl 0) (fun a => ?_) (fun v => ?_)
  · simp [Pi.single_apply, Finset.sum_ite_eq']
  · have hI : bracket 1 (fun _ : Fin 3 => (1 : ℝ)) (fun _ => 0) (fun a => Pi.single a 1)
        = 1 := by
      ext i j
      rw [bracket_apply]
      fin_cases i <;> fin_cases j <;> simp [Pi.single_apply]
    rw [hI, one_mulVec]
    simp [dotProduct, sq]

end FastClock
end RenewalGeometry
