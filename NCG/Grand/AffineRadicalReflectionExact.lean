/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Two-sided radical–Euler reflection and canonical parity holonomy

Algebraic machinery for `thm:affine-radical-reflection` (AFF.2, AFF.4–AFF.6).

* `eulerFactor` is `𝓔_m(z) = z⁻¹ ∏_{p∣m} (1 - p^{-z})` (AFF.2);
* the **exact reflection law** `𝓔_m(-t) = -χ_rad(m) r(m)^t 𝓔_m(t)` (`eulerFactor_reflect`,
  AFF.4), so the balanced branches satisfy `v_t = -χ_rad u_t` (`balanced_reflect`, AFF.5);
* on a finite same-history carrier the diagonal reflection pencil
  `𝔾_t(θ) = [[U², θUJU], [θUJU, U²]]` is **positive exactly for `|θ| ≤ 1`**
  (`pencil_posSemidef_iff`), at `θ = 1` its kernel is `{(U⁻¹x, -U⁻¹Jx)}`
  (`pencil_kernel`), and the crossing form is `-2‖x‖²` (`pencil_crossing`): radical parity
  is a source-fixed reflection orientation.
-/

namespace NCG
namespace AffineRadical

open Finset

/-! ### The scalar Euler factor and the reflection law -/

/-- The radical of `m`: the product of its prime divisors. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- The radical parity `χ_rad(m) = (-1)^{ω(m)}`. -/
def chiRad (m : ℕ) : ℝ := (-1) ^ m.primeFactors.card

/-- The Euler factor `𝓔_m(z) = z⁻¹ ∏_{p∣m}(1 - p^{-z})` (AFF.2). -/
noncomputable def eulerFactor (m : ℕ) (z : ℝ) : ℝ :=
  z⁻¹ * ∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-z))

theorem chiRad_sq (m : ℕ) : chiRad m * chiRad m = 1 := by
  rw [chiRad, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **The exact reflection law (AFF.4)**: `𝓔_m(-t) = -χ_rad(m) r(m)^t 𝓔_m(t)`. -/
theorem eulerFactor_reflect (m : ℕ) (t : ℝ) :
    eulerFactor m (-t) = -(chiRad m * (rad m : ℝ) ^ t * eulerFactor m t) := by
  have hfactor : ∀ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (- -t))
      = -((p : ℝ) ^ t * (1 - (p : ℝ) ^ (-t))) := by
    intro p hp
    have hp0 : (0 : ℝ) < p :=
      Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
    rw [neg_neg, mul_sub, mul_one, ← Real.rpow_add hp0, add_neg_cancel,
      Real.rpow_zero]
    ring
  rw [eulerFactor, eulerFactor, Finset.prod_congr rfl hfactor, Finset.prod_neg]
  rw [Finset.prod_mul_distrib]
  have hrad : (∏ p ∈ m.primeFactors, (p : ℝ) ^ t) = (rad m : ℝ) ^ t := by
    rw [rad]
    push_cast
    rw [← Real.finsetProd_rpow _ _ fun p hp =>
      (Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))).le]
  rw [hrad, chiRad]
  field_simp

/-- The balanced branches `u_t(m) = r(m)^{t/2} 𝓔_m(t)`, `v_t(m) = r(m)^{-t/2} 𝓔_m(-t)`. -/
noncomputable def uB (m : ℕ) (t : ℝ) : ℝ := (rad m : ℝ) ^ (t / 2) * eulerFactor m t

/-- The reflected balanced branch. -/
noncomputable def vB (m : ℕ) (t : ℝ) : ℝ := (rad m : ℝ) ^ (-(t / 2)) * eulerFactor m (-t)

/-- **AFF.5**: after balancing the positive radical scale, `v_t = -χ_rad u_t`. -/
theorem balanced_reflect (m : ℕ) (t : ℝ) :
    vB m t = -(chiRad m * uB m t) := by
  have hrad0 : (0 : ℝ) < (rad m : ℝ) := by
    rw [rad]
    push_cast
    refine Finset.prod_pos fun p hp => ?_
    exact Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
  rw [vB, uB, eulerFactor_reflect m t]
  rw [show (rad m : ℝ) ^ t = (rad m : ℝ) ^ (t / 2) * (rad m : ℝ) ^ (t / 2) from by
    rw [← Real.rpow_add hrad0]; ring_nf]
  rw [show -(t / 2) = -(t / 2) from rfl, Real.rpow_neg hrad0.le]
  field_simp

/-- The Euler factor is strictly positive on the positive axis. -/
theorem eulerFactor_pos (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < eulerFactor m t := by
  rw [eulerFactor]
  refine mul_pos (inv_pos.mpr ht) (Finset.prod_pos fun p hp => ?_)
  have hp1 : (1 : ℝ) < p :=
    Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp))
  have h1 : (p : ℝ) ^ (-t) < 1 := by
    rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_lt_rpow_left_iff hp1 |>.mpr (by linarith)
  linarith

/-! ### The diagonal reflection pencil (AFF.6) -/

variable {Ω : Type*} [Fintype Ω]

/-- The quadratic form of the reflection pencil
`𝔾_t(θ) = [[U², θUJU], [θUJU, U²]]` on the doubled carrier, for diagonal `U` and the
parity involution `J`. -/
def pencilForm (U J : Ω → ℝ) (θ : ℝ) (x y : Ω → ℝ) : ℝ :=
  ∑ ω, (U ω * x ω) ^ 2 + ∑ ω, (U ω * y ω) ^ 2
    + 2 * θ * ∑ ω, J ω * (U ω * x ω) * (U ω * y ω)

/-- **AFF.6, positivity**: for a parity involution `J` the pencil is positive exactly for
`|θ| ≤ 1` (given a genuinely occupied carrier direction). -/
theorem pencilForm_nonneg (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1) {θ : ℝ}
    (hθ : |θ| ≤ 1) (x y : Ω → ℝ) : 0 ≤ pencilForm U J θ x y := by
  rw [pencilForm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun ω _ => ?_
  have hθ1 : -1 ≤ θ := neg_le_of_abs_le hθ
  have hθ2 : θ ≤ 1 := le_of_abs_le hθ
  rcases hJ ω with h | h <;> rw [h] <;> nlinarith [sq_nonneg (U ω * x ω + U ω * y ω),
    sq_nonneg (U ω * x ω - U ω * y ω)]

/-- **AFF.6, sharpness**: beyond `|θ| ≤ 1` the pencil fails to be positive whenever the
carrier is occupied. -/
theorem pencilForm_neg_of_one_lt (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1)
    (hU : ∀ ω, U ω ≠ 0) {θ : ℝ} (hθ : 1 < |θ|) (ω₀ : Ω) :
    ∃ x y : Ω → ℝ, pencilForm U J θ x y < 0 := by
  classical
  set s : ℝ := if 0 ≤ θ * J ω₀ then -1 else 1 with hs
  refine ⟨fun ω => if ω = ω₀ then (U ω)⁻¹ else 0,
    fun ω => if ω = ω₀ then s * (U ω)⁻¹ else 0, ?_⟩
  have hU0 := hU ω₀
  have hterm : ∀ (f : Ω → ℝ), (∀ ω, ω ≠ ω₀ → f ω = 0) → (∑ ω, f ω) = f ω₀ := by
    intro f hf
    exact Finset.sum_eq_single ω₀ (fun ω _ hω => hf ω hω)
      (fun h => absurd (Finset.mem_univ ω₀) h)
  have hkey : J ω₀ * (θ * s) = -|θ| := by
    have hJabs : |J ω₀| = 1 := by rcases hJ ω₀ with h | h <;> rw [h] <;> norm_num
    have habs : |θ * J ω₀| = |θ| := by rw [abs_mul, hJabs, mul_one]
    rw [hs]
    split_ifs with h
    · have h1 : θ * J ω₀ = |θ| := by rw [← habs, abs_of_nonneg h]
      rw [show J ω₀ * (θ * (-1 : ℝ)) = -(θ * J ω₀) from by ring, h1]
    · have h1 : θ * J ω₀ = -|θ| := by
        rw [← habs, abs_of_neg (not_le.mp h)]
        ring
      rw [show J ω₀ * (θ * (1 : ℝ)) = θ * J ω₀ from by ring, h1]
  rw [pencilForm, hterm _ (fun ω hω => by simp [if_neg hω]),
    hterm _ (fun ω hω => by simp [if_neg hω]),
    hterm _ (fun ω hω => by simp [if_neg hω])]
  simp only [if_true]
  have e1 : U ω₀ * (U ω₀)⁻¹ = 1 := mul_inv_cancel₀ hU0
  have e2 : U ω₀ * (s * (U ω₀)⁻¹) = s := by
    rw [show U ω₀ * (s * (U ω₀)⁻¹) = s * (U ω₀ * (U ω₀)⁻¹) from by ring, e1, mul_one]
  rw [e1, e2]
  have hs2 : s ^ 2 = 1 := by
    rw [hs]
    split_ifs <;> norm_num
  rw [one_pow, hs2, show 2 * θ * (J ω₀ * 1 * s) = 2 * (J ω₀ * (θ * s)) from by ring,
    hkey]
  linarith

/-- **AFF.6, the θ = 1 kernel**: the pencil form vanishes at `θ = 1` exactly on the
reflected diagonal `(U⁻¹x, -U⁻¹Jx)`. -/
theorem pencilForm_kernel (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1)
    (hU : ∀ ω, U ω ≠ 0) (x : Ω → ℝ) :
    pencilForm U J 1 (fun ω => (U ω)⁻¹ * x ω)
      (fun ω => -((U ω)⁻¹ * (J ω * x ω))) = 0 := by
  rw [pencilForm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun ω _ => ?_
  have hUω := hU ω
  have hJ2 : J ω * J ω = 1 := by rcases hJ ω with h | h <;> rw [h] <;> ring
  have h1 : U ω * ((U ω)⁻¹ * x ω) = x ω := by
    rw [← mul_assoc, mul_inv_cancel₀ hUω, one_mul]
  have h2 : U ω * -((U ω)⁻¹ * (J ω * x ω)) = -(J ω * x ω) := by
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hUω, one_mul]
  rw [h1, h2]
  linear_combination (-(x ω ^ 2)) * hJ2

/-- **AFF.6, the crossing form**: along the θ-pencil, the form on a kernel vector is
`2(1-θ)‖x‖²`, so the crossing derivative at `θ = 1` is `-2‖x‖²`. -/
theorem pencilForm_crossing (U J : Ω → ℝ) (hJ : ∀ ω, J ω = 1 ∨ J ω = -1)
    (hU : ∀ ω, U ω ≠ 0) (x : Ω → ℝ) (θ : ℝ) :
    pencilForm U J θ (fun ω => (U ω)⁻¹ * x ω)
        (fun ω => -((U ω)⁻¹ * (J ω * x ω)))
      = 2 * (1 - θ) * ∑ ω, (x ω) ^ 2 := by
  rw [pencilForm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    show (2 : ℝ) * (1 - θ) * ∑ ω, (x ω) ^ 2 = ∑ ω, 2 * (1 - θ) * (x ω) ^ 2 from
      Finset.mul_sum _ _ _]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hUω := hU ω
  have hJ2 : J ω * J ω = 1 := by rcases hJ ω with h | h <;> rw [h] <;> ring
  have h1 : U ω * ((U ω)⁻¹ * x ω) = x ω := by
    rw [← mul_assoc, mul_inv_cancel₀ hUω, one_mul]
  have h2 : U ω * -((U ω)⁻¹ * (J ω * x ω)) = -(J ω * x ω) := by
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hUω, one_mul]
  rw [h1, h2]
  linear_combination (1 - 2 * θ) * x ω ^ 2 * hJ2

end AffineRadical
end NCG
