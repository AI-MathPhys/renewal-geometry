/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.AffineRadicalReflectionExact
import NCG.Grand.MoorePenroseSchurExact

/-!
# Flat parameter transport and the boundary soft-loading obstruction

Exact formalization for `thm:affine-reflected-soft-loading` (AFF.7–AFF.10).

* the positive transport `D_{s←t} = U_s U_t⁻¹` is invertible, satisfies the exact cocycle
  law, and commutes with the parity involution (`transport_cocycle`, `transport_self`,
  `transport_comm_parity`): every positive parameter uses the same radical parity source;
* **AFF.7**: the signed boundary writer factors exactly as `M_{χ a_D} = -B_{D,t} V_t`
  (`soft_writer_factor`);
* **AFF.8**: after nuisance shorting the protected mixed coefficient is
  `-⟨Q s_Λ, Q B_{D,t} v_t⟩` (`protected_coefficient`);
* **AFF.9**: the source-minimal action is the Moore–Penrose value
  `⟨y, (LL*)† y⟩ = min ‖h‖²` (`source_minimal_action`, citing the repository's
  Moore–Penrose module);
* **AFF.10**: `t^{k-1} L(m) r(m)^{-t/2} ≤ u_t(m) ≤ t^{k-1} L(m) r(m)^{t/2}`
  (`uB_bounds`), from `x e^{-x} ≤ 1 - e^{-x} ≤ x` multiplied over the prime factors — the
  boundary loading has scale `t^{1-k}` at factor depth `k`.
-/

open Finset

namespace NCG
namespace AffineRadical

theorem rad_pos (m : ℕ) : (0 : ℝ) < (rad m : ℝ) := by
  rw [rad]
  push_cast
  exact Finset.prod_pos fun p hp =>
    Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))

theorem uB_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < uB m t :=
  mul_pos (Real.rpow_pos_of_pos (rad_pos m) _) (eulerFactor_pos m ht)

/-! ### Flat parameter transport -/

variable {Ω : Type*} (L2 : Ω → ℕ)

/-- The positive transport `D_{s←t} = U_s U_t⁻¹`, acting diagonally on the carrier. -/
noncomputable def transport (s t : ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun ω => uB (L2 ω) s / uB (L2 ω) t * f ω

/-- **The exact cocycle law.** -/
theorem transport_cocycle {s t r : ℝ} (ht : 0 < t) (f : Ω → ℝ) :
    transport L2 s t (transport L2 t r f) = transport L2 s r f := by
  funext ω
  rw [transport, transport, transport]
  have h := (uB_pos (L2 ω) ht).ne'
  field_simp

/-- The transport at equal parameters is the identity. -/
theorem transport_self {t : ℝ} (ht : 0 < t) (f : Ω → ℝ) :
    transport L2 t t f = f := by
  funext ω
  rw [transport, div_self (uB_pos (L2 ω) ht).ne', one_mul]

/-- The transport is invertible: `D_{s←t} D_{t←s} = 1`. -/
theorem transport_inv {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (f : Ω → ℝ) :
    transport L2 s t (transport L2 t s f) = f := by
  rw [transport_cocycle L2 ht, transport_self L2 hs]

/-- The transport commutes with the radical parity involution: every positive parameter
value uses the same radical parity source. -/
theorem transport_comm_parity (s t : ℝ) (f : Ω → ℝ) :
    transport L2 s t (fun ω => -chiRad (L2 ω) * f ω)
      = fun ω => -chiRad (L2 ω) * transport L2 s t f ω := by
  funext ω
  rw [transport, transport]
  ring

/-! ### AFF.7/AFF.8: the reflected boundary writer -/

/-- **AFF.7**: the signed boundary writer factors exactly through the reflected balanced
branch: `χ_rad a_D = -(a_D/u_t) v_t` pointwise. -/
theorem soft_writer_factor (a : Ω → ℝ) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    chiRad (L2 ω) * a ω = -(a ω / uB (L2 ω) t * vB (L2 ω) t) := by
  rw [balanced_reflect]
  have h := (uB_pos (L2 ω) ht).ne'
  field_simp

variable [Fintype Ω]

/-- **AFF.8**: after simultaneous nuisance shorting, the protected mixed coefficient of
the radical-parity writer is `-⟨Q s_Λ, Q B_{D,t} v_t⟩`. -/
theorem protected_coefficient
    (Q : EuclideanSpace ℝ Ω →L[ℝ] EuclideanSpace ℝ Ω)
    (sΛ w v : EuclideanSpace ℝ Ω) (a : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (hw : ∀ ω, w ω = chiRad (L2 ω) * a ω)
    (hv : ∀ ω, v ω = a ω / uB (L2 ω) t * vB (L2 ω) t) :
    (inner ℝ (Q sΛ) (Q w) : ℝ) = -(inner ℝ (Q sΛ) (Q v)) := by
  have hfun : w = -v := by
    ext ω
    rw [show (-v : EuclideanSpace ℝ Ω) ω = -(v ω) from rfl, hw, hv]
    exact soft_writer_factor L2 a ht ω
  rw [hfun, map_neg, inner_neg_right]

/-- **AFF.9**: the source-minimal action of the shorted response is the Moore–Penrose
value `⟨y, (LL*)† y⟩`, attained by the minimum-norm solution. -/
theorem source_minimal_action
    (L : EuclideanSpace ℝ Ω →L[ℝ] EuclideanSpace ℝ Ω) (v : EuclideanSpace ℝ Ω) :
    ‖MoorePenrose.minNormSolution L (L v)‖ ^ 2
        = inner ℝ (L v) (MoorePenrose.gramPinv (ContinuousLinearMap.adjoint L) (L v)) ∧
      L (MoorePenrose.minNormSolution L (L v)) = L v ∧
      ∀ h, L h = L v → ‖MoorePenrose.minNormSolution L (L v)‖ ≤ ‖h‖ :=
  ⟨MoorePenrose.norm_sq_minNormSolution L ⟨v, rfl⟩,
   MoorePenrose.minNormSolution_apply L ⟨v, rfl⟩,
   fun _ hh => MoorePenrose.norm_minNormSolution_le L hh⟩

/-! ### AFF.10: the soft-loading bounds -/

/-- The elementary bracket `x e^{-x} ≤ 1 - e^{-x} ≤ x`. -/
theorem one_sub_exp_bracket {x : ℝ} :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) ≤ x := by
  constructor
  · have h1 := Real.add_one_le_exp x
    have hy := Real.exp_pos x
    have hinv := inv_pos.mpr hy
    rw [Real.exp_neg]
    have hcancel : Real.exp x * (Real.exp x)⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
    nlinarith
  · have h2 := Real.add_one_le_exp (-x)
    linarith

/-- **AFF.10**: `t^{k-1} L(m) r(m)^{-t/2} ≤ u_t(m) ≤ t^{k-1} L(m) r(m)^{t/2}`. -/
theorem uB_bounds (m : ℕ) (hm : 1 < m) {t : ℝ} (ht : 0 < t) :
    t ^ (m.primeFactors.card - 1) * (∏ p ∈ m.primeFactors, Real.log p)
        * (rad m : ℝ) ^ (-(t / 2)) ≤ uB m t ∧
      uB m t ≤ t ^ (m.primeFactors.card - 1) * (∏ p ∈ m.primeFactors, Real.log p)
        * (rad m : ℝ) ^ (t / 2) := by
  have hk : 1 ≤ m.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hm)
  have hlogpos : ∀ p ∈ m.primeFactors, (0 : ℝ) < Real.log p := fun p hp =>
    Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt
      (Nat.prime_of_mem_primeFactors hp)))
  have hfac : ∀ p ∈ m.primeFactors,
      (1 : ℝ) - (p : ℝ) ^ (-t) = 1 - Real.exp (-(t * Real.log p)) := by
    intro p hp
    have hp0 : (0 : ℝ) < p :=
      Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
    rw [Real.rpow_def_of_pos hp0,
      show Real.log p * -t = -(t * Real.log p) from by ring]
  -- per-factor bracket
  have hup : ∀ p ∈ m.primeFactors, (1 : ℝ) - (p : ℝ) ^ (-t) ≤ t * Real.log p := by
    intro p hp
    rw [hfac p hp]
    exact one_sub_exp_bracket.2
  have hlow : ∀ p ∈ m.primeFactors,
      t * Real.log p * Real.exp (-(t * Real.log p)) ≤ 1 - (p : ℝ) ^ (-t) := by
    intro p hp
    rw [hfac p hp]
    exact one_sub_exp_bracket.1
  have hfacnn : ∀ p ∈ m.primeFactors, (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-t) := by
    intro p hp
    refine le_trans ?_ (hlow p hp)
    have := hlogpos p hp
    positivity
  -- product bounds
  have hprod_up : (∏ p ∈ m.primeFactors, ((1 : ℝ) - (p : ℝ) ^ (-t)))
      ≤ ∏ p ∈ m.primeFactors, t * Real.log p :=
    Finset.prod_le_prod hfacnn hup
  have hprod_low : (∏ p ∈ m.primeFactors, t * Real.log p * Real.exp (-(t * Real.log p)))
      ≤ ∏ p ∈ m.primeFactors, ((1 : ℝ) - (p : ℝ) ^ (-t)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) hlow
    have := hlogpos p hp
    positivity
  -- identify the two product bounds
  have hup_val : (∏ p ∈ m.primeFactors, t * Real.log p)
      = t ^ m.primeFactors.card * ∏ p ∈ m.primeFactors, Real.log p := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hlow_val : (∏ p ∈ m.primeFactors, t * Real.log p * Real.exp (-(t * Real.log p)))
      = t ^ m.primeFactors.card * (∏ p ∈ m.primeFactors, Real.log p)
        * (rad m : ℝ) ^ (-t) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      ← Real.exp_sum]
    congr 1
    rw [show (∑ p ∈ m.primeFactors, -(t * Real.log p))
        = -(t * ∑ p ∈ m.primeFactors, Real.log p) from by
      simp [Finset.mul_sum]]
    rw [show (∑ p ∈ m.primeFactors, Real.log p) = Real.log ((rad m : ℕ) : ℝ) from ?_]
    · rw [Real.rpow_def_of_pos (rad_pos m),
        show Real.log ((rad m : ℕ) : ℝ) * -t = -(t * Real.log ((rad m : ℕ) : ℝ))
          from by ring]
    · rw [rad]
      push_cast
      exact (Real.log_prod fun p hp =>
        (Nat.cast_pos.mpr (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))).ne').symm
  -- assemble via `uB = r^{t/2} · t⁻¹ · ∏`
  have hEt : eulerFactor m t = t⁻¹ * ∏ p ∈ m.primeFactors, ((1 : ℝ) - (p : ℝ) ^ (-t)) :=
    rfl
  have htpow : t⁻¹ * t ^ m.primeFactors.card = t ^ (m.primeFactors.card - 1) := by
    have h1 : t ^ m.primeFactors.card = t ^ (m.primeFactors.card - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [h1, show t⁻¹ * (t ^ (m.primeFactors.card - 1) * t)
      = t ^ (m.primeFactors.card - 1) * (t⁻¹ * t) from by ring,
      inv_mul_cancel₀ ht.ne', mul_one]
  have hrhalf : (0 : ℝ) < (rad m : ℝ) ^ (t / 2) := Real.rpow_pos_of_pos (rad_pos m) _
  constructor
  · -- lower bound
    have h1 : t⁻¹ * (t ^ m.primeFactors.card * (∏ p ∈ m.primeFactors, Real.log p)
        * (rad m : ℝ) ^ (-t)) ≤ eulerFactor m t := by
      rw [hEt]
      have := mul_le_mul_of_nonneg_left (hlow_val ▸ hprod_low) (inv_pos.mpr ht).le
      exact this
    have h2 := mul_le_mul_of_nonneg_left h1 hrhalf.le
    calc t ^ (m.primeFactors.card - 1) * (∏ p ∈ m.primeFactors, Real.log p)
          * (rad m : ℝ) ^ (-(t / 2))
        = (rad m : ℝ) ^ (t / 2) * (t⁻¹ * (t ^ m.primeFactors.card
            * (∏ p ∈ m.primeFactors, Real.log p) * (rad m : ℝ) ^ (-t))) := by
          rw [show (rad m : ℝ) ^ (t / 2) * (t⁻¹ * (t ^ m.primeFactors.card
              * (∏ p ∈ m.primeFactors, Real.log p) * (rad m : ℝ) ^ (-t)))
            = (t⁻¹ * t ^ m.primeFactors.card)
              * (∏ p ∈ m.primeFactors, Real.log p)
              * ((rad m : ℝ) ^ (t / 2) * (rad m : ℝ) ^ (-t)) from by ring, htpow,
            ← Real.rpow_add (rad_pos m),
            show t / 2 + -t = -(t / 2) from by ring]
      _ ≤ (rad m : ℝ) ^ (t / 2) * eulerFactor m t := h2
      _ = uB m t := rfl
  · -- upper bound
    have h1 : eulerFactor m t ≤ t⁻¹ * (t ^ m.primeFactors.card
        * ∏ p ∈ m.primeFactors, Real.log p) := by
      rw [hEt]
      have := mul_le_mul_of_nonneg_left (hup_val ▸ hprod_up) (inv_pos.mpr ht).le
      exact this
    have h2 := mul_le_mul_of_nonneg_left h1 hrhalf.le
    calc uB m t = (rad m : ℝ) ^ (t / 2) * eulerFactor m t := rfl
      _ ≤ (rad m : ℝ) ^ (t / 2) * (t⁻¹ * (t ^ m.primeFactors.card
          * ∏ p ∈ m.primeFactors, Real.log p)) := h2
      _ = t ^ (m.primeFactors.card - 1) * (∏ p ∈ m.primeFactors, Real.log p)
          * (rad m : ℝ) ^ (t / 2) := by
          rw [show (rad m : ℝ) ^ (t / 2) * (t⁻¹ * (t ^ m.primeFactors.card
              * ∏ p ∈ m.primeFactors, Real.log p))
            = (t⁻¹ * t ^ m.primeFactors.card)
              * (∏ p ∈ m.primeFactors, Real.log p) * (rad m : ℝ) ^ (t / 2) from by
              ring, htpow]

end AffineRadical
end NCG
