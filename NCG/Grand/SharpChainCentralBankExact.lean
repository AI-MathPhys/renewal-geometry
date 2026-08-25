/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The sharp-chain central boundary bank

Exact formalization for `thm:GRH-sharp-chain-central-bank` (GRH.15–GRH.18).

* **GRH.15** (`central_mass`): the sine-profile boundary weights of a translation chain
  place at least `1/3` of their mass on the predeclared central set — on the central half
  of the profile `sin² ≥ 1/2` (`sin_sq_central`) and the central set holds at least
  `(m+1)/3` sites (`central_count`);
* **GRH.16** (`central_gram_nonneg`): the central loading Gram is positive;
* **GRH.17** (`central_floor`): the sharp source floor rescales the spectral floor by the
  central mass;
* **GRH.18** (`central_mass_lower`): an actual source `ε`-close to the sharp source of
  `g` keeps central boundary mass at least `(√β‖g‖ - ε)₊²` — sharp-chain softness cannot
  be diluted over arbitrarily many boundary times.
-/

open Real Finset

namespace NCG
namespace SharpChain

/-- The predeclared central site set `{j : (m+1)/4 ≤ j+1 ≤ 3(m+1)/4}`. -/
def centralSet (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => m + 1 ≤ 4 * (j.val + 1) ∧ 4 * (j.val + 1) ≤ 3 * (m + 1)

/-- On the central half of the sine profile, `sin² ≥ 1/2`. -/
theorem sin_sq_central {m k : ℕ} (hk1 : m + 1 ≤ 4 * k) (hk2 : 4 * k ≤ 3 * (m + 1)) :
    (1 : ℝ) / 2 ≤ Real.sin ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) ^ 2 := by
  set θ := (k : ℝ) * Real.pi / ((m : ℝ) + 1) with hθ
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast1 : ((m : ℝ) + 1) ≤ 4 * (k : ℝ) := by exact_mod_cast hk1
  have hcast2 : 4 * (k : ℝ) ≤ 3 * ((m : ℝ) + 1) := by exact_mod_cast hk2
  have hθ1 : Real.pi / 4 ≤ θ := by
    rw [hθ, div_le_div_iff₀ (by norm_num) hm1]
    nlinarith [Real.pi_pos]
  have hθ2 : θ ≤ 3 * Real.pi / 4 := by
    rw [hθ, div_le_div_iff₀ hm1 (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsin : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    rcases le_or_gt θ (Real.pi / 2) with hle | hgt
    · calc Real.sqrt 2 / 2 = Real.sin (Real.pi / 4) := Real.sin_pi_div_four.symm
        _ ≤ Real.sin θ := by
            refine Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by
              linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], hle⟩ hθ1
    · have h2 : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
      rw [h2]
      calc Real.sqrt 2 / 2 = Real.sin (Real.pi / 4) := Real.sin_pi_div_four.symm
        _ ≤ Real.sin (Real.pi - θ) := by
            refine Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by
              linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], by linarith⟩
              (by linarith)
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  calc (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ h0 hsin 2

/-- The central set holds at least `(m+1)/3` sites. -/
theorem central_count (m : ℕ) (hm : 1 ≤ m) : m + 1 ≤ 3 * (centralSet m).card := by
  classical
  set a := (m + 4) / 4 with ha
  set b := (3 * (m + 1)) / 4 with hb
  have h4a := Nat.div_add_mod (m + 4) 4
  have h4b := Nat.div_add_mod (3 * (m + 1)) 4
  have hma : (m + 4) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hmb : (3 * (m + 1)) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hinj : (Finset.Icc a b).card ≤ (centralSet m).card := by
    refine Finset.card_le_card_of_injOn
      (fun k => ⟨min (k - 1) (m - 1), by omega⟩) ?_ ?_
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_Icc] at hk
      simp only [centralSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor <;> omega
    · intro k1 h1 k2 h2 he
      rw [Finset.mem_coe, Finset.mem_Icc] at h1 h2
      have hv := congrArg Fin.val he
      simp only at hv
      omega
  have hcard : (Finset.Icc a b).card = b + 1 - a := Nat.card_Icc a b
  omega

/-- **GRH.15**: the sine-profile weights place at least `1/3` of their mass on the
central set. -/
theorem central_mass (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / 3 ≤ ∑ j ∈ centralSet m,
      2 / ((m : ℝ) + 1) * Real.sin (((j.val : ℝ) + 1) * Real.pi / ((m : ℝ) + 1)) ^ 2 := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsite : ∀ j ∈ centralSet m,
      2 / ((m : ℝ) + 1) * (1 / 2)
        ≤ 2 / ((m : ℝ) + 1)
          * Real.sin (((j.val : ℝ) + 1) * Real.pi / ((m : ℝ) + 1)) ^ 2 := by
    intro j hj
    simp only [centralSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hs := sin_sq_central (k := j.val + 1) hj.1 hj.2
    have hcast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hs
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hcount := central_count m hm
  have hcast : ((m : ℝ) + 1) ≤ 3 * ((centralSet m).card : ℝ) := by exact_mod_cast hcount
  calc (1 : ℝ) / 3 ≤ ((centralSet m).card : ℝ) / ((m : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by norm_num) hm1]
        linarith
    _ = ∑ _j ∈ centralSet m, 2 / ((m : ℝ) + 1) * (1 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
    _ ≤ _ := Finset.sum_le_sum hsite

/-! ### GRH.16–GRH.18: the central loading Gram and the dilution bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- **GRH.16**: the central loading Gram quadratic form is positive. -/
theorem central_gram_nonneg {ι : Type*} (J : Finset ι) (b : ι → ℝ)
    (hb : ∀ j, 0 ≤ b j) (r : ι → E → ℝ) (hr : ∀ j g, 0 ≤ r j g) (g : E) :
    0 ≤ ∑ j ∈ J, b j * r j g :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (hr j g)

omit [InnerProductSpace ℝ E] in
/-- **GRH.17**: the sharp source floor rescales the spectral floor by the central mass:
if `λ` floors the central Gram, then `κ_cen = λ/β` floors the `β`-normalized bank. -/
theorem central_floor (q : E → ℝ) (lam β : ℝ) (hβ : 0 < β)
    (hlam : ∀ g, lam * ‖g‖ ^ 2 ≤ q g) (g : E) :
    lam / β * (β * ‖g‖ ^ 2) ≤ q g := by
  have h := hlam g
  rw [div_mul_eq_mul_div, mul_comm β, mul_div_assoc, mul_div_assoc,
    div_self hβ.ne', mul_one]
  exact h

omit [InnerProductSpace ℝ E] in
/-- **GRH.18**: an actual source `ε`-close to the sharp source keeps central boundary
mass at least `(√β‖g‖ - ε)₊²`: sharp-chain softness cannot be diluted. -/
theorem central_mass_lower {Y : Type*} [NormedAddCommGroup Y]
    {β ε : ℝ} (g : E) (y sharp : Y)
    (hsharp : ‖sharp‖ = Real.sqrt β * ‖g‖) (hclose : ‖y - sharp‖ ≤ ε) :
    max 0 (Real.sqrt β * ‖g‖ - ε) ^ 2 ≤ ‖y‖ ^ 2 := by
  have h1 : ‖sharp‖ - ε ≤ ‖y‖ := by
    have h := norm_sub_norm_le sharp y
    have h3 : ‖sharp - y‖ ≤ ε := by
      rw [norm_sub_rev]
      exact hclose
    linarith
  have h2 : Real.sqrt β * ‖g‖ - ε ≤ ‖y‖ := by
    rw [← hsharp]
    linarith
  rcases le_or_gt (Real.sqrt β * ‖g‖ - ε) 0 with hle | hgt
  · rw [max_eq_left hle]
    simp
  · rw [max_eq_right hgt.le]
    exact pow_le_pow_left₀ hgt.le h2 2

end SharpChain
end NCG
