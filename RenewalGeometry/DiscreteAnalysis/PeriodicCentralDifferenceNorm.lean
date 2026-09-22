/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp grid-scale source amplification
  (`prop:supp-current-derivative-loss`,
  `eq:supp-current-derivative-loss`; emergent-spacetime manuscript)

On a periodic grid of `m` sites (`ZMod m`), spacing `h > 0` and inner
product `h ∑ᵢ uᵢ vᵢ`, the central difference
`(D_h u)_i = (u_{i+1} - u_{i-1}) / (2h)` has squared operator norm
`‖D_h‖²_{2→2} = h⁻²` as soon as `4 ∣ m`.

* `periodicCentralDifference`, `gridNormSq`: the operator and the squared
  grid norm.
* `gridNormSq_centralDifference_le`: the upper bound
  `‖D_h u‖² ≤ h⁻² ‖u‖²` for every `u` and every `m ≠ 0` (no divisibility
  needed).
* `quarterWave`: the explicit period-four witness `0, 1, 0, -1, …`, which
  is mapped by `D_h` to its own shift divided by `h`
  (`centralDifference_quarterWave`), hence attains the bound
  (`gridNormSq_centralDifference_quarterWave`).  This replaces the paper's
  Fourier-multiplier argument (`i sin(2πk/m)/h`, maximum at `k = m/4`) by
  the real vector of that same frequency.
* `centralDifference_opNormSq`: the squared operator norm, as the supremum
  of `‖D_h u‖²` over unit vectors, equals `h⁻²`
  (`eq:supp-current-derivative-loss`).
* `exists_vanishing_norm_diverging_current`: the vector `𝔞_h = h^{1/2} v_h`
  with `‖𝔞_h‖² = h` and `‖D_h 𝔞_h‖² = h⁻¹`; a vanishing unscaled norm does
  not bound the differentiated current.
-/

open scoped BigOperators

namespace RenewalGeometry

variable {m : ℕ} [NeZero m]

/-- The periodic central difference `(D_h u)_i = (u_{i+1} - u_{i-1}) / (2h)`. -/
noncomputable def periodicCentralDifference (h : ℝ) (u : ZMod m → ℝ) (i : ZMod m) : ℝ :=
  (u (i + 1) - u (i - 1)) / (2 * h)

/-- The squared grid norm `‖u‖² = h ∑ᵢ uᵢ²`. -/
noncomputable def gridNormSq (h : ℝ) (u : ZMod m → ℝ) : ℝ := h * ∑ i, u i ^ 2

theorem periodicCentralDifference_smul (h c : ℝ) (u : ZMod m → ℝ) :
    periodicCentralDifference h (fun i => c * u i) =
      fun i => c * periodicCentralDifference h u i := by
  funext i; unfold periodicCentralDifference; ring

theorem gridNormSq_smul (h c : ℝ) (u : ZMod m → ℝ) :
    gridNormSq h (fun i => c * u i) = c ^ 2 * gridNormSq h u := by
  unfold gridNormSq
  have : ∑ i, (c * u i) ^ 2 = c ^ 2 * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]; ring

theorem gridNormSq_nonneg {h : ℝ} (hh : 0 ≤ h) (u : ZMod m → ℝ) :
    0 ≤ gridNormSq h u :=
  mul_nonneg hh (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Shift invariance of periodic sums (forward shift). -/
theorem sum_shift_add (g : ZMod m → ℝ) (a : ZMod m) :
    ∑ i : ZMod m, g (i + a) = ∑ i : ZMod m, g i :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

/-- Shift invariance of periodic sums (backward shift). -/
theorem sum_shift_sub (g : ZMod m → ℝ) (a : ZMod m) :
    ∑ i : ZMod m, g (i - a) = ∑ i : ZMod m, g i :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

/-- Upper bound `‖D_h u‖² ≤ h⁻² ‖u‖²` (triangle inequality on the two
shifts). -/
theorem gridNormSq_centralDifference_le {h : ℝ} (hh : 0 < h)
    (u : ZMod m → ℝ) :
    gridNormSq h (periodicCentralDifference h u) ≤ h⁻¹ ^ 2 * gridNormSq h u := by
  unfold gridNormSq periodicCentralDifference
  have hS : ∑ i, (u (i + 1) - u (i - 1)) ^ 2 ≤ 4 * ∑ i, u i ^ 2 := by
    calc ∑ i, (u (i + 1) - u (i - 1)) ^ 2
        ≤ ∑ i, (2 * u (i + 1) ^ 2 + 2 * u (i - 1) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [sq_nonneg (u (i + 1) + u (i - 1))]
      _ = 2 * ∑ i, u (i + 1) ^ 2 + 2 * ∑ i, u (i - 1) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 4 * ∑ i, u i ^ 2 := by
          rw [sum_shift_add (fun i => u i ^ 2) 1, sum_shift_sub (fun i => u i ^ 2) 1]
          ring
  have hrew : ∑ i, ((u (i + 1) - u (i - 1)) / (2 * h)) ^ 2 =
      (1 / (4 * h ^ 2)) * ∑ i, (u (i + 1) - u (i - 1)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [hrew]
  have h2 : 0 < h ^ 2 := by positivity
  calc h * (1 / (4 * h ^ 2) * ∑ i, (u (i + 1) - u (i - 1)) ^ 2)
      ≤ h * (1 / (4 * h ^ 2) * (4 * ∑ i, u i ^ 2)) := by
        gcongr
    _ = h⁻¹ ^ 2 * (h * ∑ i, u i ^ 2) := by
        field_simp

/-- The explicit period-four witness `0, 1, 0, -1, …` (the real part of the
Fourier mode `k = m/4`). -/
def quarterWave (i : ZMod m) : ℝ :=
  if i.val % 4 = 1 then 1 else if i.val % 4 = 3 then -1 else 0

theorem quarterWave_add_two (hm : 4 ∣ m) (i : ZMod m) :
    quarterWave (i + 2) = -quarterWave i := by
  have hm4 : 4 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) hm
  have h2 : (2 : ZMod m).val = 2 := by
    have : ((2 : ℕ) : ZMod m).val = 2 % m := ZMod.val_natCast m 2
    rw [Nat.cast_ofNat] at this
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  have hval : (i + 2).val % 4 = (i.val + 2) % 4 := by
    rw [ZMod.val_add, h2, Nat.mod_mod_of_dvd _ hm]
  unfold quarterWave
  rw [hval]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem quarterWave_sub_two (hm : 4 ∣ m) (i : ZMod m) :
    quarterWave (i - 2) = -quarterWave i := by
  have := quarterWave_add_two hm (i - 2)
  rw [sub_add_cancel] at this
  linarith

/-- `D_h` maps the quarter wave to its own forward shift divided by `h`. -/
theorem centralDifference_quarterWave (hm : 4 ∣ m) (h : ℝ) (hh : h ≠ 0)
    (i : ZMod m) :
    periodicCentralDifference h quarterWave i = quarterWave (i + 1) / h := by
  unfold periodicCentralDifference
  have : quarterWave (i - 1) = -quarterWave (i + 1) := by
    have h1 : i - 1 = (i + 1) - 2 := by ring
    rw [h1, quarterWave_sub_two hm]
  rw [this]
  field_simp
  ring

/-- The quarter wave attains the bound: `‖D_h v‖² = h⁻² ‖v‖²`. -/
theorem gridNormSq_centralDifference_quarterWave (hm : 4 ∣ m) {h : ℝ}
    (hh : 0 < h) :
    gridNormSq h (periodicCentralDifference h (quarterWave (m := m))) =
      h⁻¹ ^ 2 * gridNormSq h (quarterWave (m := m)) := by
  unfold gridNormSq
  have : ∑ i, periodicCentralDifference h (quarterWave (m := m)) i ^ 2 =
      h⁻¹ ^ 2 * ∑ i, quarterWave (m := m) i ^ 2 := by
    rw [← sum_shift_add (fun i => quarterWave (m := m) i ^ 2) 1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [centralDifference_quarterWave hm h hh.ne']
    field_simp
  rw [this]; ring

/-- The quarter wave is a nonzero vector (`v₁ = 1`). -/
theorem gridNormSq_quarterWave_pos (hm : 4 ∣ m) {h : ℝ} (hh : 0 < h) :
    0 < gridNormSq h (quarterWave (m := m)) := by
  have hm4 : 4 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) hm
  have : Fact (1 < m) := ⟨by omega⟩
  have h1 : quarterWave (m := m) 1 = 1 := by
    unfold quarterWave
    rw [ZMod.val_one]
    norm_num
  unfold gridNormSq
  apply mul_pos hh
  calc (0 : ℝ) < quarterWave (m := m) 1 ^ 2 := by rw [h1]; norm_num
    _ ≤ ∑ i, quarterWave (m := m) i ^ 2 :=
        Finset.single_le_sum (f := fun i => quarterWave (m := m) i ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ 1)

/-- The set of values `‖D_h u‖²` over unit vectors `‖u‖² = 1`. -/
def centralDifferenceRayleighSet (h : ℝ) : Set ℝ :=
  {r | ∃ u : ZMod m → ℝ, gridNormSq h u = 1 ∧
    r = gridNormSq h (periodicCentralDifference h u)}

/-- `h⁻²` is the greatest Rayleigh value: attained by the normalized quarter
wave and an upper bound for all unit vectors. -/
theorem centralDifference_isGreatest (hm : 4 ∣ m) {h : ℝ} (hh : 0 < h) :
    IsGreatest (centralDifferenceRayleighSet (m := m) h) (h⁻¹ ^ 2) := by
  constructor
  · set N := gridNormSq h (quarterWave (m := m)) with hN
    have hNpos : 0 < N := gridNormSq_quarterWave_pos hm hh
    refine ⟨fun i => (Real.sqrt N)⁻¹ * quarterWave i, ?_, ?_⟩
    · rw [gridNormSq_smul, inv_pow, Real.sq_sqrt hNpos.le, ← hN]
      exact inv_mul_cancel₀ hNpos.ne'
    · rw [periodicCentralDifference_smul, gridNormSq_smul,
        gridNormSq_centralDifference_quarterWave hm hh, ← hN]
      have hs : (Real.sqrt N)⁻¹ ^ 2 = N⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hNpos.le]
      rw [hs]
      field_simp
  · rintro r ⟨u, hu, rfl⟩
    have := gridNormSq_centralDifference_le hh u
    rw [hu, mul_one] at this
    exact this

/-- `eq:supp-current-derivative-loss`: `‖D_h‖²_{2→2} = h⁻²`, the squared
operator norm being the supremum of `‖D_h u‖²` over unit vectors. -/
theorem centralDifference_opNormSq (hm : 4 ∣ m) {h : ℝ} (hh : 0 < h) :
    sSup (centralDifferenceRayleighSet (m := m) h) = h⁻¹ ^ 2 :=
  (centralDifference_isGreatest hm hh).csSup_eq

/-- The paper's amplification witness `𝔞_h = h^{1/2} v_h`: its squared norm
is `h → 0` while `‖D_h 𝔞_h‖² = h⁻¹ → ∞`. -/
theorem exists_vanishing_norm_diverging_current (hm : 4 ∣ m) {h : ℝ}
    (hh : 0 < h) :
    ∃ a : ZMod m → ℝ, gridNormSq h a = h ∧
      gridNormSq h (periodicCentralDifference h a) = h⁻¹ := by
  obtain ⟨u, hu, hDu⟩ := (centralDifference_isGreatest hm hh).1
  refine ⟨fun i => Real.sqrt h * u i, ?_, ?_⟩
  · rw [gridNormSq_smul, Real.sq_sqrt hh.le, hu, mul_one]
  · rw [periodicCentralDifference_smul, gridNormSq_smul, ← hDu,
      Real.sq_sqrt hh.le]
    field_simp

end RenewalGeometry
