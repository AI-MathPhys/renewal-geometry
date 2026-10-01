/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The three-site odd grid of the exact finite action (`N = 3`, `h = 1/3`, `V = 27`)
  (`eq:supp-exact-phase-derivative`, `eq:supp-exact-transverse-space`,
  `eq:supp-certified-weak-split`, `eq:supp-exact-harmonic-mass-column` (`[δ_c, δ_d] = 0`);
  emergent-spacetime manuscript)

The exact-action certificates of the emergent-spacetime manuscript are stated for the unchanged
finite action on the `N = 3` odd grid.  The action itself (the canonical Hamiltonian of the
reconstructed phase-compatible action after stationary-connection and Legendre elimination) is
not written in the paper; this file encodes, exactly and over `ℝ`, the part of the three-site
data that the paper *does* define, and proves the dimension counts on which the weak/active
multiplier split rests.

* `Site = (ℤ/3)³` (`V = 27` sites); `shift i` is the literal shift `S_i`.
* `phaseDeriv i = 3 (S_i - S_i⁻¹)`.  `phaseDerivC_character` proves that this is the paper's
  odd-grid phase derivative `\widehat{δ_i u}(k) = i κ_i(k) \hat u(k)`,
  `κ_i(k) = 2 h⁻¹ sin(π h k_i)` at `h = 1/3` (`eq:supp-exact-phase-derivative`), on every Fourier
  character `χ_k`, with `k_i` the symmetric representative in `{-1, 0, 1}`.
* `phaseDeriv_comm` (`[δ_c, δ_d] = 0`, the commuting phase translations of
  `eq:supp-exact-harmonic-mass-column`), `phaseDeriv_skew` (skew-adjointness),
  `phaseDeriv_const`, `phaseDeriv_eq_zero_iff`.
* `grad φ = (δ₁φ, δ₂φ, δ₃φ)` and the constant shifts `constShift`:
  `ker_grad` (kernel = constants), `finrank_range_grad` (`dim 𝒢 = 26 = V - 1`),
  `finrank_range_constShift` (`dim ℋ = 3`), `range_grad_inf_range_constShift` (`𝒢 ∩ ℋ = 0`),
  `finrank_weakSpace` (`dim (𝒢 ⊕ ℋ) = 29`, the weak split `ℝ²⁹ = ℋ ⊕ 𝒢` of
  `eq:supp-certified-weak-split`).
* `transverse` = the shifts orthogonal to the weak space; `mem_transverse_iff`: these are exactly
  the mean-zero shifts with `Σ_i δ_i β_i = 0` (the real-space form of
  `eq:supp-exact-transverse-space`), and `finrank_transverse` (`dim 𝒯_h = 52 = 2(V - 1)`).
* `finrank_meanZeroLapse` (`26`), and `multiplier_count`: `108 = 4V = 1 + 78 + 29`
  (mean lapse, active `78 = 26 + 52`, weak `29`), the multiplier count of
  `ass:supp-graded-exact-chart`.
-/

open Module Finset

namespace RenewalGeometry
namespace ExactThreeSite

/-- Sites of the `N = 3` odd grid: `(ℤ/3)³`, `V = 27`. -/
abbrev Site := Fin 3 → ZMod 3

/-- The coordinate unit vector `e_i`. -/
def unitVec (i : Fin 3) : Site := Pi.single i 1

theorem card_site : Fintype.card Site = 27 := by
  simp [Site, ZMod.card]

/-- The literal shift `(S_i u)(x) = u(x + e_i)`. -/
def shift (i : Fin 3) : (Site → ℝ) →ₗ[ℝ] (Site → ℝ) :=
  LinearMap.funLeft ℝ ℝ fun x => x + unitVec i

/-- The inverse shift `(S_i⁻¹ u)(x) = u(x - e_i)`. -/
def shiftInv (i : Fin 3) : (Site → ℝ) →ₗ[ℝ] (Site → ℝ) :=
  LinearMap.funLeft ℝ ℝ fun x => x - unitVec i

/-- The odd-grid phase derivative at `N = 3`: `δ_i = 3 (S_i - S_i⁻¹)`. -/
def phaseDeriv (i : Fin 3) : (Site → ℝ) →ₗ[ℝ] (Site → ℝ) :=
  (3 : ℝ) • (shift i - shiftInv i)

theorem phaseDeriv_apply (i : Fin 3) (u : Site → ℝ) (x : Site) :
    phaseDeriv i u x = 3 * (u (x + unitVec i) - u (x - unitVec i)) := by
  simp [phaseDeriv, shift, shiftInv, LinearMap.funLeft_apply]

/-! ## Faithfulness: the Fourier symbol `i κ_i(k)` -/

section Symbol

open Complex Real

/-- The Fourier character `χ_k(x) = ∏_j exp(2π i k_j x_j / 3)`. -/
noncomputable def character (k x : Site) : ℂ := ∏ j, ZMod.stdAddChar (k j * x j)

/-- The complexified phase derivative `δ_i = 3 (S_i - S_i⁻¹)` on `ℂ`-valued fields. -/
def phaseDerivC (i : Fin 3) (u : Site → ℂ) : Site → ℂ :=
  fun x => 3 * (u (x + unitVec i) - u (x - unitVec i))

theorem phaseDerivC_ofReal (i : Fin 3) (u : Site → ℝ) (x : Site) :
    phaseDerivC i (fun y => (u y : ℂ)) x = (phaseDeriv i u x : ℂ) := by
  simp [phaseDerivC, phaseDeriv_apply]

/-- The symmetric representative of `a ∈ ℤ/3` in `{-1, 0, 1}` (the Fourier index range of the
odd grid). -/
def symRep (a : ZMod 3) : ℤ := if a.val ≤ 1 then (a.val : ℤ) else (a.val : ℤ) - 3

theorem character_add (k x y : Site) : character k (x + y) = character k x * character k y := by
  simp only [character, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]

theorem character_unitVec (k : Site) (i : Fin 3) :
    character k (unitVec i) = ZMod.stdAddChar (k i) := by
  rw [character, Fintype.prod_eq_single i]
  · simp [unitVec]
  · intro j hj
    simp [unitVec, Pi.single_apply, hj]

theorem character_neg_unitVec (k : Site) (i : Fin 3) :
    character k (-unitVec i) = ZMod.stdAddChar (-k i) := by
  rw [character, Fintype.prod_eq_single i]
  · simp [unitVec]
  · intro j hj
    simp [unitVec, Pi.single_apply, hj]

private theorem exp_sub_exp_neg (θ : ℝ) :
    Complex.exp (θ * I) - Complex.exp (-(θ * I)) = I * (2 * Real.sin θ) := by
  rw [Complex.ofReal_sin, Complex.sin, show -(↑θ * I) = -↑θ * I by ring]
  linear_combination (Complex.exp (↑θ * I) - Complex.exp (-↑θ * I)) * Complex.I_sq

theorem symRep_cast (a : ZMod 3) : (((symRep a : ℤ)) : ZMod 3) = a := by
  revert a; decide

theorem symRep_cases (a : ZMod 3) : symRep a = -1 ∨ symRep a = 0 ∨ symRep a = 1 := by
  revert a; decide

/-- `3 (ψ(a) - ψ(-a)) = i · 2 h⁻¹ sin(π h ã)` at `h = 1/3`, for the standard character `ψ` of
`ℤ/3` and the symmetric representative `ã ∈ {-1, 0, 1}` of `a` (`sin(2π/3) = sin(π/3)`). -/
theorem stdAddChar_sub_neg (a : ZMod 3) :
    (3 : ℂ) * (ZMod.stdAddChar a - ZMod.stdAddChar (-a))
      = I * ((2 * 3 * Real.sin (π * (1 / 3) * symRep a) : ℝ) : ℂ) := by
  have key : ∀ m : ℤ, (3 : ℂ) * (ZMod.stdAddChar ((m : ℤ) : ZMod 3)
      - ZMod.stdAddChar (((-m : ℤ)) : ZMod 3))
      = I * ((2 * 3 * Real.sin (2 * π * m / 3) : ℝ) : ℂ) := by
    intro m
    rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
    have e1 : (2 * (π : ℂ) * I * (m : ℂ) / ((3 : ℕ) : ℂ)) = ((2 * π * m / 3 : ℝ) : ℂ) * I := by
      push_cast; ring
    have e2 : (2 * (π : ℂ) * I * (((-m : ℤ)) : ℂ) / ((3 : ℕ) : ℂ))
        = -(((2 * π * m / 3 : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [e1, e2, exp_sub_exp_neg]
    push_cast
    ring
  have hneg : (((-symRep a : ℤ)) : ZMod 3) = -a := by rw [Int.cast_neg, symRep_cast]
  have hsin : Real.sin (2 * π * (symRep a : ℝ) / 3) = Real.sin (π * (1 / 3) * symRep a) := by
    rcases symRep_cases a with h | h | h <;> rw [h] <;>
      simp only [Int.cast_neg, Int.cast_one, Int.cast_zero]
    · rw [show 2 * π * -1 / 3 = -(π - π * (1 / 3) * 1) by ring, Real.sin_neg, Real.sin_pi_sub,
        show π * (1 / 3) * -1 = -(π * (1 / 3) * 1) by ring, Real.sin_neg]
    · simp
    · rw [show 2 * π * 1 / 3 = π - π * (1 / 3) * 1 by ring, Real.sin_pi_sub]
  have := key (symRep a)
  rw [symRep_cast, hneg, hsin] at this
  exact this

/-- **Faithfulness of `δ_i` (`eq:supp-exact-phase-derivative`).**  On every Fourier character,
`δ_i χ_k = i κ_i(k) χ_k` with `κ_i(k) = 2 h⁻¹ sin(π h k_i)`, `h = 1/3`, and `k_i ∈ {-1, 0, 1}`
the symmetric representative.  Hence `3 (S_i - S_i⁻¹)` is exactly the paper's odd-grid phase
derivative at `N = 3`. -/
theorem phaseDerivC_character (i : Fin 3) (k : Site) (x : Site) :
    phaseDerivC i (character k) x
      = I * ((2 * (1 / (1 / 3 : ℝ)) * Real.sin (π * (1 / 3) * symRep (k i)) : ℝ) : ℂ)
        * character k x := by
  have h1 : character k (x + unitVec i) = ZMod.stdAddChar (k i) * character k x := by
    rw [character_add, character_unitVec, mul_comm]
  have h2 : character k (x - unitVec i) = ZMod.stdAddChar (-k i) * character k x := by
    rw [sub_eq_add_neg, character_add, character_neg_unitVec, mul_comm]
  simp only [phaseDerivC, h1, h2]
  rw [← sub_mul, ← mul_assoc, stdAddChar_sub_neg]
  norm_num

end Symbol

/-! ## Algebraic properties of the phase derivatives -/

theorem shift_comm_apply (i j : Fin 3) (x : Site) :
    x + unitVec i + unitVec j = x + unitVec j + unitVec i := by abel

/-- **Commuting phase translations** `[δ_i, δ_j] = 0`. -/
theorem phaseDeriv_comm (i j : Fin 3) :
    (phaseDeriv i).comp (phaseDeriv j) = (phaseDeriv j).comp (phaseDeriv i) := by
  ext u x
  simp only [LinearMap.comp_apply, phaseDeriv_apply]
  have e1 : x + unitVec i + unitVec j = x + unitVec j + unitVec i := by abel
  have e2 : x + unitVec i - unitVec j = x - unitVec j + unitVec i := by abel
  have e3 : x - unitVec i + unitVec j = x + unitVec j - unitVec i := by abel
  have e4 : x - unitVec i - unitVec j = x - unitVec j - unitVec i := by abel
  rw [e1, e2, e3, e4]
  ring

/-- Commutation for arbitrary constant-coefficient translations `δ_c = Σ c_i δ_i`. -/
theorem phaseDeriv_comb_comm (c d : Fin 3 → ℝ) :
    (∑ i, c i • phaseDeriv i).comp (∑ j, d j • phaseDeriv j)
      = (∑ j, d j • phaseDeriv j).comp (∑ i, c i • phaseDeriv i) := by
  refine LinearMap.ext fun u => funext fun x => ?_
  have hc : ∀ i j, phaseDeriv i (phaseDeriv j u) = phaseDeriv j (phaseDeriv i u) := fun i j =>
    congrArg (fun T => T u) (phaseDeriv_comm i j)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hc]
  ring

theorem sum_shift (u : Site → ℝ) (v : Site) : ∑ x, u (x + v) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl

theorem sum_shift_sub (u : Site → ℝ) (v : Site) : ∑ x, u (x - v) = ∑ x, u x :=
  Fintype.sum_equiv (Equiv.subRight v) _ _ fun _ => rfl

/-- **Skew-adjointness** of `δ_i` for the site pairing. -/
theorem phaseDeriv_skew (i : Fin 3) (u v : Site → ℝ) :
    ∑ x, phaseDeriv i u x * v x = -∑ x, u x * phaseDeriv i v x := by
  simp only [phaseDeriv_apply]
  have h1 : ∑ x, u (x + unitVec i) * v x = ∑ x, u x * v (x - unitVec i) := by
    rw [← sum_shift_sub (fun x => u (x + unitVec i) * v x) (unitVec i)]
    simp
  have h2 : ∑ x, u (x - unitVec i) * v x = ∑ x, u x * v (x + unitVec i) := by
    rw [← sum_shift (fun x => u (x - unitVec i) * v x) (unitVec i)]
    simp
  have l : ∑ x, 3 * (u (x + unitVec i) - u (x - unitVec i)) * v x
      = 3 * (∑ x, u (x + unitVec i) * v x - ∑ x, u (x - unitVec i) * v x) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  have r : ∑ x, u x * (3 * (v (x + unitVec i) - v (x - unitVec i)))
      = 3 * (∑ x, u x * v (x + unitVec i) - ∑ x, u x * v (x - unitVec i)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  rw [l, r, h1, h2]
  ring

/-- The phase derivative of a field sums to zero. -/
theorem sum_phaseDeriv (i : Fin 3) (u : Site → ℝ) : ∑ x, phaseDeriv i u x = 0 := by
  have := phaseDeriv_skew i u (fun _ => 1)
  simpa [phaseDeriv_apply] using this

/-- `δ_i` annihilates constants. -/
theorem phaseDeriv_const (i : Fin 3) (c : ℝ) : phaseDeriv i (fun _ => c) = 0 := by
  ext x; simp [phaseDeriv_apply]

theorem unitVec_add_unitVec (i : Fin 3) : unitVec i + unitVec i = -unitVec i := by
  ext j
  by_cases h : j = i
  · subst h; simp [unitVec]; decide
  · simp [unitVec, Pi.single_apply, h]

/-- `δ_i u = 0` iff `u` is invariant under the shift `e_i` (at `N = 3`, `S_i² = S_i⁻¹`). -/
theorem phaseDeriv_eq_zero_iff (i : Fin 3) (u : Site → ℝ) :
    phaseDeriv i u = 0 ↔ ∀ x, u (x + unitVec i) = u x := by
  constructor
  · intro h x
    have hx := congrFun h (x - unitVec i)
    rw [phaseDeriv_apply, Pi.zero_apply, sub_add_cancel] at hx
    have e : x - unitVec i - unitVec i = x + unitVec i := by
      rw [sub_sub, unitVec_add_unitVec, sub_neg_eq_add]
    rw [e] at hx
    linarith
  · intro h
    ext x
    rw [phaseDeriv_apply, Pi.zero_apply]
    have := h (x - unitVec i)
    rw [sub_add_cancel] at this
    rw [h x, this]
    ring

/-! ## The gradient, the constant shifts, and the weak split `ℝ²⁹ = ℋ ⊕ 𝒢` -/

/-- Constant fields `c ↦ (x ↦ c)`. -/
def constField : ℝ →ₗ[ℝ] (Site → ℝ) where
  toFun c := fun _ => c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The discrete gradient `φ ↦ (δ₁φ, δ₂φ, δ₃φ)` (longitudinal shifts). -/
def grad : (Site → ℝ) →ₗ[ℝ] (Fin 3 → Site → ℝ) := LinearMap.pi fun i => phaseDeriv i

/-- The literal constant shifts `c ↦ (i, x) ↦ c_i` (the space `ℋ`). -/
def constShift : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Site → ℝ) :=
  LinearMap.pi fun i => constField.comp (LinearMap.proj i)

theorem invariant_add_nsmul {u : Site → ℝ} {v : Site} (h : ∀ x, u (x + v) = u x) (n : ℕ)
    (x : Site) : u (x + n • v) = u x := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ← add_assoc, h, ih]

theorem site_decomp (x : Site) :
    x = (x 0).val • unitVec 0 + (x 1).val • unitVec 1 + (x 2).val • unitVec 2 := by
  ext j
  fin_cases j <;> simp [unitVec, Pi.single_apply] <;>
    rw [ZMod.cast_eq_val, Pi.natCast_apply, ZMod.natCast_zmod_val]

/-- **Kernel of the gradient = constants.** -/
theorem ker_grad : LinearMap.ker grad = LinearMap.range constField := by
  ext u
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    have hi : ∀ i, ∀ x, u (x + unitVec i) = u x := fun i =>
      (phaseDeriv_eq_zero_iff i u).mp (congrFun h i)
    refine ⟨u 0, ?_⟩
    funext x
    show u 0 = u x
    rw [site_decomp x, invariant_add_nsmul (hi 2), invariant_add_nsmul (hi 1),
      ← zero_add ((x 0).val • unitVec 0), invariant_add_nsmul (hi 0)]
  · rintro ⟨c, rfl⟩
    funext i
    exact phaseDeriv_const i c

theorem constField_injective : Function.Injective constField := fun a b h =>
  congrFun h 0

theorem finrank_site : finrank ℝ (Site → ℝ) = 27 := by
  rw [Module.finrank_fintype_fun_eq_card, card_site]

/-- **`dim 𝒢 = 26 = V - 1`** (the gradient indices of `thm:supp-certified-weak-rank`). -/
theorem finrank_range_grad : finrank ℝ (LinearMap.range grad) = 26 := by
  have h := grad.finrank_range_add_finrank_ker
  rw [ker_grad, LinearMap.finrank_range_of_inj constField_injective, finrank_site,
    Module.finrank_self] at h
  omega

theorem constShift_injective : Function.Injective constShift := by
  intro a b h
  funext i
  exact congrFun (congrFun h i) 0

/-- **`dim ℋ = 3`.** -/
theorem finrank_range_constShift : finrank ℝ (LinearMap.range constShift) = 3 := by
  rw [LinearMap.finrank_range_of_inj constShift_injective]
  simp

/-- **`𝒢 ∩ ℋ = 0`**: a gradient sums to zero over the grid, a constant shift sums to `27 c`. -/
theorem range_grad_inf_range_constShift :
    LinearMap.range grad ⊓ LinearMap.range constShift = ⊥ := by
  rw [eq_bot_iff]
  rintro β ⟨⟨φ, rfl⟩, ⟨c, hc⟩⟩
  rw [Submodule.mem_bot]
  have hc0 : c = 0 := by
    funext i
    have h1 := sum_phaseDeriv i φ
    have h2 : ∀ x, phaseDeriv i φ x = c i := fun x => (congrFun (congrFun hc i) x).symm
    simp only [h2, Finset.sum_const, Finset.card_univ, card_site, nsmul_eq_mul] at h1
    simpa using h1
  rw [← hc, hc0, map_zero]

/-- The weak multiplier space `𝒢 ⊕ ℋ` (gradient shifts plus constant shifts). -/
def weakSpace : Submodule ℝ (Fin 3 → Site → ℝ) :=
  LinearMap.range grad ⊔ LinearMap.range constShift

/-- **`dim (ℋ ⊕ 𝒢) = 29`** (`eq:supp-certified-weak-split`). -/
theorem finrank_weakSpace : finrank ℝ weakSpace = 29 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range grad)
    (LinearMap.range constShift)
  rw [range_grad_inf_range_constShift, finrank_bot, finrank_range_grad,
    finrank_range_constShift] at h
  rw [weakSpace]
  omega

/-! ## The transverse shift space `𝒯_h` -/

/-- The site pairing of shift fields `⟨β, β'⟩ = Σ_{i,x} β_i(x) β'_i(x)`. -/
def shiftPairing : LinearMap.BilinForm ℝ (Fin 3 → Site → ℝ) :=
  LinearMap.mk₂ ℝ (fun β β' => ∑ i, ∑ x, β i x * β' i x)
    (fun a b c => by simp [add_mul, Finset.sum_add_distrib])
    (fun r a b => by simp [Finset.mul_sum, mul_assoc])
    (fun a b c => by simp [mul_add, Finset.sum_add_distrib])
    (fun r a b => by simp [Finset.mul_sum, mul_left_comm])

theorem shiftPairing_apply (β β' : Fin 3 → Site → ℝ) :
    shiftPairing β β' = ∑ i, ∑ x, β i x * β' i x := rfl

theorem shiftPairing_isRefl : shiftPairing.IsRefl := by
  intro a b h
  rw [shiftPairing_apply] at h ⊢
  simpa [mul_comm] using h

theorem shiftPairing_separating (β : Fin 3 → Site → ℝ) (h : ∀ γ, shiftPairing β γ = 0) :
    β = 0 := by
  funext i x
  have := h (Pi.single i (Pi.single x 1))
  rw [shiftPairing_apply, Fintype.sum_eq_single i] at this
  · rw [Fintype.sum_eq_single x] at this
    · simpa using this
    · intro y hy; simp [Pi.single_apply, hy]
  · intro j hj; simp [Pi.single_apply, hj]

theorem shiftPairing_symm (β γ : Fin 3 → Site → ℝ) : shiftPairing β γ = shiftPairing γ β := by
  simp only [shiftPairing_apply, mul_comm]

theorem shiftPairing_nondegenerate : shiftPairing.Nondegenerate :=
  ⟨shiftPairing_separating, fun β h =>
    shiftPairing_separating β fun γ => by rw [shiftPairing_symm]; exact h γ⟩

/-- The transverse shift space: shifts orthogonal to the weak space. -/
def transverse : Submodule ℝ (Fin 3 → Site → ℝ) := shiftPairing.orthogonal weakSpace

/-- The discrete divergence `Σ_i δ_i β_i`. -/
def divergence (β : Fin 3 → Site → ℝ) : Site → ℝ := ∑ i, phaseDeriv i (β i)

/-- **Real-space form of `eq:supp-exact-transverse-space`.** A shift is transverse iff it has
zero mean (`\hat β(0) = 0`) and zero phase divergence (`κ(k)ᵀ \hat β(k) = 0`). -/
theorem mem_transverse_iff (β : Fin 3 → Site → ℝ) :
    β ∈ transverse ↔ divergence β = 0 ∧ ∀ i, ∑ x, β i x = 0 := by
  have hgrad : ∀ φ : Site → ℝ, shiftPairing (grad φ) β = -∑ x, φ x * divergence β x := by
    intro φ
    rw [shiftPairing_apply]
    simp only [grad, LinearMap.pi_apply]
    rw [Finset.sum_congr rfl fun i _ => phaseDeriv_skew i φ (β i)]
    simp only [divergence, Finset.sum_apply, Finset.mul_sum, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have hconst : ∀ c : Fin 3 → ℝ, shiftPairing (constShift c) β = ∑ i, c i * ∑ x, β i x := by
    intro c
    rw [shiftPairing_apply]
    simp [constShift, constField, Finset.mul_sum]
  constructor
  · intro h
    have hw : ∀ w ∈ weakSpace, shiftPairing w β = 0 := fun w hw => h w hw
    refine ⟨?_, fun i => ?_⟩
    · funext x
      have := hw (grad (Pi.single x 1))
        (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
      rw [hgrad, Fintype.sum_eq_single x] at this
      · simpa using this
      · intro y hy; simp [Pi.single_apply, hy]
    · have := hw (constShift (Pi.single i 1))
        (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
      rw [hconst, Fintype.sum_eq_single i] at this
      · simpa using this
      · intro j hj; simp [Pi.single_apply, hj]
  · rintro ⟨hdiv, hmean⟩ w hw
    obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨φ, rfl⟩ := hg
    obtain ⟨c, rfl⟩ := hh
    show shiftPairing (grad φ + constShift c) β = 0
    rw [map_add, LinearMap.add_apply, hgrad, hconst, hdiv]
    simp [hmean]

/-- **`dim 𝒯_h = 52 = 2(V - 1)`** (`eq:supp-exact-transverse-space`). -/
theorem finrank_transverse : finrank ℝ transverse = 52 := by
  rw [transverse, LinearMap.BilinForm.finrank_orthogonal shiftPairing_nondegenerate,
    finrank_weakSpace, Module.finrank_pi_fintype]
  simp [finrank_site]

/-! ## Lapse and the multiplier count -/

/-- Mean-zero (nonconstant) lapse perturbations. -/
def meanZeroLapse : Submodule ℝ (Site → ℝ) :=
  LinearMap.ker (∑ x : Site, LinearMap.proj (R := ℝ) (φ := fun _ : Site => ℝ) x)

theorem finrank_meanZeroLapse : finrank ℝ meanZeroLapse = 26 := by
  set m : (Site → ℝ) →ₗ[ℝ] ℝ := ∑ x : Site, LinearMap.proj (R := ℝ) (φ := fun _ : Site => ℝ) x
  have hm : Function.Surjective m := by
    intro r
    refine ⟨fun _ => r / 27, ?_⟩
    simp [m, Finset.sum_apply, card_site]
    ring
  have h := m.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hm, finrank_top, Module.finrank_self, finrank_site] at h
  show finrank ℝ (LinearMap.ker m) = 26
  omega

/-- **Multiplier count of `ass:supp-graded-exact-chart`.**  The `4V = 108` multiplier
coordinates `λ = (N, β)` split as the mean lapse (`1`), the active block (nonconstant lapse
`26` plus transverse shifts `52`, i.e. `78`) and the weak block (`𝒢 ⊕ ℋ`, `29`). -/
theorem multiplier_count :
    finrank ℝ ((Site → ℝ) × (Fin 3 → Site → ℝ)) = 108 ∧
      finrank ℝ meanZeroLapse + finrank ℝ transverse = 78 ∧
      1 + (finrank ℝ meanZeroLapse + finrank ℝ transverse) + finrank ℝ weakSpace = 108 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Module.finrank_prod, finrank_site, Module.finrank_pi_fintype]
    simp [finrank_site]
  · rw [finrank_meanZeroLapse, finrank_transverse]
  · rw [finrank_meanZeroLapse, finrank_transverse, finrank_weakSpace]

end ExactThreeSite
end RenewalGeometry
