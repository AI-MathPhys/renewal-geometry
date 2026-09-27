/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.CoframeRenewalPacketExact
import RenewalGeometry.Analysis.UnitCubeRiemannSum

/-!
# Dirichlet-form limit of the coframe renewal packet on the torus

Paper `predictive_spectral_geometry`, label `thm:supp-general-renewal-process`, last clause
`eq:supp-general-form-limit`.

The packet of `CoframeRenewalPacketExact` is placed on the torus `Q_h = hℤ^d/ℤ^d`,
`h = 1/M`, with vertices `torusPoint M k = k/M`, `k ∈ (ℤ/Mℤ)^d`, for `ℤ^d`-periodic
coefficients, density and test function, and integer lattice directions.

* `dirichletForm_eq_energySum` (summation by parts on the torus):
  `-⟨f, L_h f⟩_{m_h} = Σ_x Σ_r c_h(x,r) |f(x+hr) - f(x)|²` (exact, finite).
* `abs_energySum_sub_riemannSum_le`: the finite energy is the Riemann sum of the energy
  density `½ Σ_r a_r (∂_r f)²` up to `O(h)`, for `f ∈ C²` and `a_r ∈ C¹` with global bounds.
* `tendsto_dirichletForm` (**`eq:supp-general-form-limit`**): as `h = 1/(n+1) → 0`,
  `-⟨f, L_h f⟩_{m_h} → ∫_{[0,1]^d} ½ Σ_r a_r (∂_r f)² dx`, and under the positive
  decomposition `ρ g⁻¹ = Σ_r a_r r rᵀ` the integrand is `½ g^{ij} ∂_i f ∂_j f ρ`
  (`energyDensity_eq_metricDensity`, `tendsto_dirichletForm_metric`).

The Riemann-sum convergence is `UnitCubeRiemannSum.tendsto_riemannSum`.  The test function
is real-valued (the paper's `∂_j \bar f` is `∂_j f`); the periodic extension of the paper is
the periodicity hypothesis here.
-/

open Finset Filter Topology MeasureTheory Set
open RenewalGeometry.LineTaylorRemainderBound RenewalGeometry.UnitCubeRiemannSum

namespace RenewalGeometry.CoframeRenewalPacket

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-! ### Periodicity and the torus grid -/

/-- `ℤ^d`-periodicity of a function on the chart. -/
def Periodic (φ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (x : Fin d → ℝ) (m : Fin d → ℤ), φ (x + fun i => (m i : ℝ)) = φ x

/-- The torus vertices `k/M`, `k ∈ (ℤ/Mℤ)^d`. -/
noncomputable def torusPoint (M : ℕ) (k : Fin d → ZMod M) : Fin d → ℝ :=
  fun i => ((k i).val : ℝ) / M

theorem torusPoint_eq_gridPoint (n : ℕ) (k : Fin d → ZMod (n + 1)) :
    torusPoint (n + 1) k = gridPoint (n + 1) k := rfl

/-- The lattice step `z/M`. -/
noncomputable def latticeStep (M : ℕ) (z : Fin d → ℤ) : Fin d → ℝ := fun i => (z i : ℝ) / M

theorem val_add_intCast_eq (M : ℕ) [NeZero M] (a : ZMod M) (z : ℤ) :
    ∃ q : ℤ, ((a + (z : ZMod M)).val : ℤ) = (a.val : ℤ) + z + (M : ℤ) * q := by
  have hcast : ((((a + (z : ZMod M)).val : ℤ) - (a.val : ℤ) - z : ℤ) : ZMod M) = 0 := by simp
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hcast
  exact ⟨q, by linarith⟩

/-- Shifting a torus vertex by an integer vector moves its point by `z/M` up to `ℤ^d`. -/
theorem exists_torusPoint_add (M : ℕ) [NeZero M] (k : Fin d → ZMod M) (z : Fin d → ℤ) :
    ∃ q : Fin d → ℤ, torusPoint M (k + fun i => (z i : ZMod M)) =
      torusPoint M k + latticeStep M z + fun i => (q i : ℝ) := by
  choose q hq using fun i => val_add_intCast_eq M (k i) (z i)
  refine ⟨q, ?_⟩
  funext i
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  simp only [torusPoint, latticeStep, Pi.add_apply]
  have h' : (((k i + (z i : ZMod M)).val : ℕ) : ℝ) =
      ((k i).val : ℝ) + (z i : ℝ) + (M : ℝ) * (q i : ℝ) := by
    exact_mod_cast hq i
  rw [h']
  field_simp

/-- Translation invariance of torus sums of periodic functions. -/
theorem sum_torus_add_latticeStep (M : ℕ) [NeZero M] (G : (Fin d → ℝ) → ℝ) (hG : Periodic G)
    (z : Fin d → ℤ) :
    ∑ k : Fin d → ZMod M, G (torusPoint M k + latticeStep M z) =
      ∑ k : Fin d → ZMod M, G (torusPoint M k) := by
  refine Fintype.sum_equiv (Equiv.addRight fun i => (z i : ZMod M))
    (fun k => G (torusPoint M k + latticeStep M z)) (fun k => G (torusPoint M k)) fun k => ?_
  obtain ⟨q, hq⟩ := exists_torusPoint_add M k z
  simp only [Equiv.coe_addRight]
  rw [hq, hG]

namespace CoframePacket

variable (P : CoframePacket d ι)

/-- Directions with integer coordinates (`R_d^+ ⊂ ℤ^d`). -/
def IntegerDirections : Prop := ∀ r, ∃ z : Fin d → ℤ, P.dir r = fun i => (z i : ℝ)

omit [Fintype ι] in
theorem smul_dir_eq_latticeStep (M : ℕ) {r : ι} {z : Fin d → ℤ}
    (hz : P.dir r = fun i => (z i : ℝ)) :
    (1 / (M : ℝ)) • P.dir r = latticeStep M z := by
  funext i
  simp [hz, latticeStep, div_eq_inv_mul]

/-- The Dirichlet form `-⟨f, L_h f⟩_{m_h}` on the torus `Q_h`, `h = 1/M`. -/
noncomputable def dirichletForm (M : ℕ) [NeZero M] (f : (Fin d → ℝ) → ℝ) : ℝ :=
  -∑ k : Fin d → ZMod M, P.mass (1 / M) (torusPoint M k) * f (torusPoint M k) *
    P.generator (1 / M) f (torusPoint M k)

/-- The finite energy `Σ_x Σ_r c_h(x,r) |f(x+hr) - f(x)|²`. -/
noncomputable def energySum (M : ℕ) [NeZero M] (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ k : Fin d → ZMod M, ∑ r, P.conductance (1 / M) (torusPoint M k) r *
    (f (torusPoint M k + (1 / (M : ℝ)) • P.dir r) - f (torusPoint M k)) ^ 2

/-- The energy density `½ Σ_r a_r (∂_r f)²`. -/
noncomputable def energyDensity (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 / 2) * ∑ r, P.coeff r x * (fderiv ℝ f x (P.dir r)) ^ 2

omit [Fintype ι] in
theorem periodic_conductance (h : ℝ) (r : ι) (ha : Periodic (P.coeff r)) :
    Periodic fun x => P.conductance h x r := by
  intro x m
  simp only [conductance]
  rw [ha x m, add_right_comm, ha (x + h • P.dir r) m]

/-! ### Summation by parts -/

/-- **Summation by parts on the torus.** `-⟨f, L_h f⟩_{m_h} = Σ_x Σ_r c_h(x,r) |f(x+hr) - f(x)|²`
for periodic `f`, coefficients and density (density nonvanishing, integer directions). -/
theorem dirichletForm_eq_energySum (M : ℕ) [NeZero M] (f : (Fin d → ℝ) → ℝ) (hf : Periodic f)
    (ha : ∀ r, Periodic (P.coeff r)) (hρ : ∀ x, P.density x ≠ 0) (hdir : P.IntegerDirections) :
    P.dirichletForm M f = P.energySum M f := by
  have hM : (1 / (M : ℝ)) ≠ 0 := by
    have := NeZero.ne M
    positivity
  have hmass : ∀ x, P.mass (1 / M) x ≠ 0 := fun x => mul_ne_zero (pow_ne_zero _ hM) (hρ x)
  set h : ℝ := 1 / (M : ℝ) with hh
  -- the forward and backward contributions of one direction
  let A : ι → (Fin d → ℝ) → ℝ := fun r x =>
    P.conductance h x r * f x * (f (x + h • P.dir r) - f x)
  let B : ι → (Fin d → ℝ) → ℝ := fun r x =>
    P.conductance h (x - h • P.dir r) r * f x * (f (x - h • P.dir r) - f x)
  have hterm : ∀ x, P.mass h x * f x * P.generator h f x = ∑ r, (A r x + B r x) := by
    intro x
    unfold generator forwardRate backwardRate
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [A, B]
    field_simp [hmass x]
    try ring
  have hB : ∀ r, Periodic (B r) := by
    intro r x m
    simp only [B]
    have hc : P.conductance h (x - h • P.dir r + fun i => (m i : ℝ)) r =
        P.conductance h (x - h • P.dir r) r := P.periodic_conductance h r (ha r) _ m
    rw [add_sub_right_comm, hc, hf x m, hf _ m]
  have hBshift : ∀ r, ∑ k : Fin d → ZMod M, B r (torusPoint M k) =
      ∑ k : Fin d → ZMod M, P.conductance h (torusPoint M k) r *
        f (torusPoint M k + h • P.dir r) * (f (torusPoint M k) - f (torusPoint M k + h • P.dir r)) := by
    intro r
    obtain ⟨z, hz⟩ := hdir r
    rw [← sum_torus_add_latticeStep M (B r) (hB r) z, ← P.smul_dir_eq_latticeStep M hz, ← hh]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [B, add_sub_cancel_right]
  unfold dirichletForm energySum
  simp only [← hh, hterm]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_add_distrib, hBshift r, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [A]
  ring

/-! ### The energy density approximation -/

/-- The per-direction constant of the `O(h)` energy estimate, with
`Q = F₁ ‖r‖ + F₂ ‖r‖² / 2` bounding the difference quotients and the derivative. -/
noncomputable def energyConstant (F1 F2 A0 A1 : ℝ) (r : Fin d → ℝ) : ℝ :=
  A1 * ‖r‖ * (F1 * ‖r‖ + F2 * ‖r‖ ^ 2 / 2) ^ 2 / 4 +
    A0 * (F1 * ‖r‖ + F2 * ‖r‖ ^ 2 / 2) * (F2 * ‖r‖ ^ 2) / 2

omit [Fintype ι] in
/-- One energy term: `c_h(x,r)(f(x+hr) - f(x))² = h^d [½ a_r(x) (∂_r f(x))² + O(h)]`. -/
theorem abs_energy_term_sub_le (hd : 2 ≤ d) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (F1 F2 : ℝ)
    (hF1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ F1) (hF2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ F2)
    (r : ι) (hC : ContDiff ℝ 1 (P.coeff r)) (A0 A1 : ℝ)
    (hA0 : ∀ y, ‖iteratedFDeriv ℝ 0 (P.coeff r) y‖ ≤ A0)
    (hA1 : ∀ y, ‖iteratedFDeriv ℝ 1 (P.coeff r) y‖ ≤ A1) :
    |P.conductance h x r * (f (x + h • P.dir r) - f x) ^ 2 -
        h ^ d * ((1 / 2) * P.coeff r x * (fderiv ℝ f x (P.dir r)) ^ 2)| ≤
      h ^ d * (h * energyConstant F1 F2 A0 A1 (P.dir r)) := by
  set φ := lineMap f x (P.dir r) with hφdef
  set α := lineMap (P.coeff r) x (P.dir r) with hαdef
  have hφ : ContDiff ℝ 2 φ := contDiff_lineMap hf x (P.dir r)
  have hα : ContDiff ℝ 1 α := contDiff_lineMap hC x (P.dir r)
  set D := fderiv ℝ f x (P.dir r) with hD
  set q := (φ h - φ 0) / h with hq
  set Q := F1 * ‖P.dir r‖ + F2 * ‖P.dir r‖ ^ 2 / 2 with hQ
  have hnr : 0 ≤ ‖P.dir r‖ := norm_nonneg _
  have hF1n : 0 ≤ F1 := (norm_nonneg _).trans (hF1 x)
  have hF2n : 0 ≤ F2 := (norm_nonneg _).trans (hF2 x)
  have hA0n : 0 ≤ A0 := (norm_nonneg _).trans (hA0 x)
  have hA1n : 0 ≤ A1 := (norm_nonneg _).trans (hA1 x)
  -- derivative bound and Taylor
  have hD1 : iteratedDeriv 1 φ 0 = D := iteratedDeriv_one_lineMap_zero hf (by norm_num) x (P.dir r)
  have hDb : |D| ≤ F1 * ‖P.dir r‖ := by
    have := abs_iteratedDeriv_lineMap_le_of_bound hf (k := 1) (by norm_num) hF1 x (P.dir r) 0
    rwa [hD1, pow_one] at this
  have hφ2 : ∀ t, |iteratedDeriv 2 φ t| ≤ F2 * ‖P.dir r‖ ^ 2 :=
    abs_iteratedDeriv_lineMap_le_of_bound hf le_rfl hF2 x (P.dir r)
  have htaylor : |φ h - (φ 0 + h * D)| ≤ F2 * ‖P.dir r‖ ^ 2 * h ^ 2 / 2 := by
    have := abs_sub_taylor_one_le φ _ hφ hφ2 0 h
    rwa [sub_zero, hD1, abs_of_pos hh] at this
  have hqD : |q - D| ≤ F2 * ‖P.dir r‖ ^ 2 * h / 2 := by
    have : q - D = (φ h - (φ 0 + h * D)) / h := by rw [hq]; field_simp; ring
    rw [this, abs_div, abs_of_pos hh, div_le_iff₀ hh]
    calc |φ h - (φ 0 + h * D)| ≤ F2 * ‖P.dir r‖ ^ 2 * h ^ 2 / 2 := htaylor
      _ = F2 * ‖P.dir r‖ ^ 2 * h / 2 * h := by ring
  have hqD' : |q - D| ≤ F2 * ‖P.dir r‖ ^ 2 / 2 := by
    refine hqD.trans ?_
    have : F2 * ‖P.dir r‖ ^ 2 * h ≤ F2 * ‖P.dir r‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hh1 (by positivity)
    linarith
  have hDQ : |D| ≤ Q := by rw [hQ]; linarith [show 0 ≤ F2 * ‖P.dir r‖ ^ 2 / 2 by positivity]
  have hqQ : |q| ≤ Q := by
    calc |q| = |(q - D) + D| := by ring_nf
      _ ≤ |q - D| + |D| := abs_add_le _ _
      _ ≤ F2 * ‖P.dir r‖ ^ 2 / 2 + F1 * ‖P.dir r‖ := add_le_add hqD' hDb
      _ = Q := by rw [hQ]; ring
  have hQn : 0 ≤ Q := (abs_nonneg _).trans hDQ
  -- coefficient bounds
  have hα1 : ∀ t, |iteratedDeriv 1 α t| ≤ A1 * ‖P.dir r‖ := by
    intro t
    have := abs_iteratedDeriv_lineMap_le_of_bound hC (k := 1) le_rfl hA1 x (P.dir r) t
    rwa [pow_one] at this
  have hαdiff : |α h - α 0| ≤ A1 * ‖P.dir r‖ * h := by
    have := abs_sub_le_of_deriv_bound α _ hα hα1 0 h
    rwa [sub_zero, abs_of_pos hh] at this
  have hα0 : |α 0| ≤ A0 := by
    have := abs_iteratedDeriv_lineMap_le_of_bound hC (k := 0) (by norm_num) hA0 x (P.dir r) 0
    simpa using this
  -- the algebraic identity
  have hfh : f (x + h • P.dir r) = φ h := by simp [φ, lineMap]
  have hf0 : f x = φ 0 := by simp [φ, lineMap]
  have hah : P.coeff r (x + h • P.dir r) = α h := by simp [α, lineMap]
  have ha0 : P.coeff r x = α 0 := by simp [α, lineMap]
  have hpow : h ^ (d - 2) * h ^ 2 = h ^ d := (pow_eq_pow_sub_two_mul h hd).symm
  have hident : P.conductance h x r * (f (x + h • P.dir r) - f x) ^ 2 -
      h ^ d * ((1 / 2) * P.coeff r x * D ^ 2) =
      h ^ d * ((α h - α 0) / 4 * q ^ 2 + 1 / 2 * α 0 * ((q - D) * (q + D))) := by
    unfold conductance
    rw [hfh, hf0, hah, ha0, ← hpow]
    have hq' : φ h - φ 0 = q * h := by rw [hq]; field_simp
    rw [hq']
    ring
  rw [hident, abs_mul, abs_of_pos (pow_pos hh d)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hh d).le
  have hq2 : q ^ 2 ≤ Q ^ 2 := by
    rw [← sq_abs q]
    exact pow_le_pow_left₀ (abs_nonneg _) hqQ 2
  have hqD2 : |q + D| ≤ 2 * Q := by
    calc |q + D| ≤ |q| + |D| := abs_add_le _ _
      _ ≤ Q + Q := add_le_add hqQ hDQ
      _ = 2 * Q := by ring
  calc |(α h - α 0) / 4 * q ^ 2 + 1 / 2 * α 0 * ((q - D) * (q + D))|
      ≤ |(α h - α 0) / 4 * q ^ 2| + |1 / 2 * α 0 * ((q - D) * (q + D))| := abs_add_le _ _
    _ = |α h - α 0| / 4 * q ^ 2 + 1 / 2 * |α 0| * (|q - D| * |q + D|) := by
        rw [abs_mul, abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg q)]
        norm_num
    _ ≤ A1 * ‖P.dir r‖ * h / 4 * Q ^ 2 +
        1 / 2 * A0 * (F2 * ‖P.dir r‖ ^ 2 * h / 2 * (2 * Q)) := by
        gcongr
    _ = h * energyConstant F1 F2 A0 A1 (P.dir r) := by
        unfold energyConstant
        rw [← hQ]
        ring

/-- **The finite energy is the Riemann sum of the energy density up to `O(h)`.** -/
theorem abs_energySum_sub_riemannSum_le (hd : 2 ≤ d) (M : ℕ) [NeZero M]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (F1 F2 : ℝ)
    (hF1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ F1) (hF2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ F2)
    (hC : ∀ r, ContDiff ℝ 1 (P.coeff r)) (A0 A1 : ι → ℝ)
    (hA0 : ∀ r y, ‖iteratedFDeriv ℝ 0 (P.coeff r) y‖ ≤ A0 r)
    (hA1 : ∀ r y, ‖iteratedFDeriv ℝ 1 (P.coeff r) y‖ ≤ A1 r) :
    |P.energySum M f - (1 / (M : ℝ)) ^ d * ∑ k : Fin d → ZMod M, P.energyDensity f (torusPoint M k)| ≤
      (1 / (M : ℝ)) * ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
  set h : ℝ := 1 / (M : ℝ) with hh
  have hhpos : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hM']
    exact_mod_cast hMpos
  unfold energySum energyDensity
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : Fin d → ZMod M,
      |∑ r, P.conductance h (torusPoint M k) r *
          (f (torusPoint M k + h • P.dir r) - f (torusPoint M k)) ^ 2 -
        h ^ d * ((1 / 2) * ∑ r, P.coeff r (torusPoint M k) *
          (fderiv ℝ f (torusPoint M k) (P.dir r)) ^ 2)| ≤
        h ^ d * (h * ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r)) := by
    intro k
    calc |∑ r, P.conductance h (torusPoint M k) r *
            (f (torusPoint M k + h • P.dir r) - f (torusPoint M k)) ^ 2 -
          h ^ d * ((1 / 2) * ∑ r, P.coeff r (torusPoint M k) *
            (fderiv ℝ f (torusPoint M k) (P.dir r)) ^ 2)|
        = |∑ r, (P.conductance h (torusPoint M k) r *
            (f (torusPoint M k + h • P.dir r) - f (torusPoint M k)) ^ 2 -
          h ^ d * ((1 / 2) * P.coeff r (torusPoint M k) *
            (fderiv ℝ f (torusPoint M k) (P.dir r)) ^ 2))| := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ ≤ ∑ r, h ^ d * (h * energyConstant F1 F2 (A0 r) (A1 r) (P.dir r)) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ =>
            P.abs_energy_term_sub_le hd h hhpos hh1 (torusPoint M k) f hf F1 F2 hF1 hF2 r (hC r)
              (A0 r) (A1 r) (hA0 r) (hA1 r))
      _ = h ^ d * (h * ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  calc |∑ k : Fin d → ZMod M, (∑ r, P.conductance h (torusPoint M k) r *
          (f (torusPoint M k + h • P.dir r) - f (torusPoint M k)) ^ 2 -
        h ^ d * ((1 / 2) * ∑ r, P.coeff r (torusPoint M k) *
          (fderiv ℝ f (torusPoint M k) (P.dir r)) ^ 2))|
      ≤ ∑ k : Fin d → ZMod M, (h ^ d * (h * ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r))) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm k)
    _ = h * ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, hh, ← mul_assoc, ← mul_pow, mul_one_div_cancel hM'.ne',
          one_pow, one_mul]

/-! ### The limit -/

theorem continuous_energyDensity (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hC : ∀ r, ContDiff ℝ 1 (P.coeff r)) : Continuous (P.energyDensity f) := by
  unfold energyDensity
  refine continuous_const.mul (continuous_finsetSum _ fun r _ => ?_)
  exact ((hC r).continuous).mul
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)

/-- **`eq:supp-general-form-limit`** (directional form).  For `ℤ^d`-periodic `f ∈ C²`,
periodic `C¹` coefficients with global bounds, periodic nonvanishing density and integer
directions, the torus Dirichlet forms of the packet at mesh `h = 1/(n+1)` converge:
`-⟨f, L_h f⟩_{m_h} → ∫_{[0,1]^d} ½ Σ_r a_r (∂_r f)² dx`. -/
theorem tendsto_dirichletForm (hd : 2 ≤ d) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hfp : Periodic f) (F1 F2 : ℝ)
    (hF1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ F1) (hF2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ F2)
    (hC : ∀ r, ContDiff ℝ 1 (P.coeff r)) (hap : ∀ r, Periodic (P.coeff r)) (A0 A1 : ι → ℝ)
    (hA0 : ∀ r y, ‖iteratedFDeriv ℝ 0 (P.coeff r) y‖ ≤ A0 r)
    (hA1 : ∀ r y, ‖iteratedFDeriv ℝ 1 (P.coeff r) y‖ ≤ A1 r)
    (hρ : ∀ x, P.density x ≠ 0) (hdir : P.IntegerDirections) :
    Tendsto (fun n : ℕ => P.dirichletForm (n + 1) f) atTop
      (𝓝 (∫ x in Icc (0 : Fin d → ℝ) 1, P.energyDensity f x)) := by
  set K : ℝ := ∑ r, energyConstant F1 F2 (A0 r) (A1 r) (P.dir r) with hK
  -- Riemann sums
  have hR : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ d *
      ∑ k : Fin d → ZMod (n + 1), P.energyDensity f (torusPoint (n + 1) k)) atTop
      (𝓝 (∫ x in Icc (0 : Fin d → ℝ) 1, P.energyDensity f x)) :=
    tendsto_riemannSum (P.energyDensity f) (P.continuous_energyDensity f hf hC)
  -- error term
  have hE : Tendsto (fun n : ℕ => P.energySum (n + 1) f - (1 / ((n : ℝ) + 1)) ^ d *
      ∑ k : Fin d → ZMod (n + 1), P.energyDensity f (torusPoint (n + 1) k)) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, |P.energySum (n + 1) f - (1 / ((n : ℝ) + 1)) ^ d *
        ∑ k : Fin d → ZMod (n + 1), P.energyDensity f (torusPoint (n + 1) k)| ≤
        (1 / ((n : ℝ) + 1)) * K := by
      intro n
      have := P.abs_energySum_sub_riemannSum_le hd (n + 1) f hf F1 F2 hF1 hF2 hC A0 A1 hA0 hA1
      push_cast at this
      exact this
    have hlim : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * K) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const K
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hlim
  have heq : ∀ n : ℕ, P.dirichletForm (n + 1) f =
      (1 / ((n : ℝ) + 1)) ^ d *
        ∑ k : Fin d → ZMod (n + 1), P.energyDensity f (torusPoint (n + 1) k) +
      (P.energySum (n + 1) f - (1 / ((n : ℝ) + 1)) ^ d *
        ∑ k : Fin d → ZMod (n + 1), P.energyDensity f (torusPoint (n + 1) k)) := by
    intro n
    rw [P.dirichletForm_eq_energySum (n + 1) f hfp hap hρ hdir]
    ring
  have := hR.add hE
  rw [add_zero] at this
  exact this.congr fun n => (heq n).symm

/-- Under the positive decomposition `ρ g⁻¹ = Σ_r a_r r rᵀ`, the energy density is the
paper's `½ g^{ij} ∂_i f ∂_j f ρ`. -/
theorem energyDensity_eq_metricDensity {ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hg : P.IsDecomposition ginv) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    P.energyDensity f x = (1 / 2) * ∑ i, ∑ j, ginv x i j * fderiv ℝ f x (Pi.single i 1) *
      fderiv ℝ f x (Pi.single j 1) * P.density x := by
  unfold energyDensity
  congr 1
  have hentry : ∀ i j, P.density x * ginv x i j = ∑ r, P.coeff r x * (P.dir r i * P.dir r j) := by
    intro i j
    have := congrFun (congrFun (hg x) i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  calc ∑ r, P.coeff r x * (fderiv ℝ f x (P.dir r)) ^ 2
      = ∑ r, ∑ i, ∑ j, P.coeff r x * (P.dir r i * P.dir r j) *
          (fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [fderiv_apply_eq_sum_single f x (P.dir r), sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, (∑ r, P.coeff r x * (P.dir r i * P.dir r j)) *
          (fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, ginv x i j * fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1) *
          P.density x := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← hentry i j]
        ring

/-- **`eq:supp-general-form-limit`** (metric form).  Under the positive decomposition
`ρ g⁻¹ = Σ_r a_r r rᵀ`, the torus Dirichlet forms converge to
`½ ∫_{[0,1]^d} g^{ij} ∂_i f ∂_j f ρ dx`. -/
theorem tendsto_dirichletForm_metric (hd : 2 ≤ d) {ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hg : P.IsDecomposition ginv) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hfp : Periodic f) (F1 F2 : ℝ)
    (hF1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ F1) (hF2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ F2)
    (hC : ∀ r, ContDiff ℝ 1 (P.coeff r)) (hap : ∀ r, Periodic (P.coeff r)) (A0 A1 : ι → ℝ)
    (hA0 : ∀ r y, ‖iteratedFDeriv ℝ 0 (P.coeff r) y‖ ≤ A0 r)
    (hA1 : ∀ r y, ‖iteratedFDeriv ℝ 1 (P.coeff r) y‖ ≤ A1 r)
    (hρ : ∀ x, P.density x ≠ 0) (hdir : P.IntegerDirections) :
    Tendsto (fun n : ℕ => P.dirichletForm (n + 1) f) atTop
      (𝓝 (∫ x in Icc (0 : Fin d → ℝ) 1, (1 / 2) * ∑ i, ∑ j, ginv x i j *
        fderiv ℝ f x (Pi.single i 1) * fderiv ℝ f x (Pi.single j 1) * P.density x)) := by
  have hfun : (fun x => (1 / 2) * ∑ i, ∑ j, ginv x i j * fderiv ℝ f x (Pi.single i 1) *
      fderiv ℝ f x (Pi.single j 1) * P.density x) = P.energyDensity f :=
    funext fun x => (P.energyDensity_eq_metricDensity hg f x).symm
  rw [hfun]
  exact P.tendsto_dirichletForm hd f hf hfp F1 F2 hF1 hF2 hC hap A0 A1 hA0 hA1 hρ hdir

end CoframePacket

end RenewalGeometry.CoframeRenewalPacket
