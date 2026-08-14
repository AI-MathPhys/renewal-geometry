/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact first-chaos spectrum and projection–persistence tradeoff
  (`thm:projection-persistence-tradeoff`,
  Gran-Tensor manuscript)

The unmodulated flip–interchange regulator on the discrete
three-torus `(ZMod N)³`: every site carries a two-state
renewal flag flipping `H → P` at rate `4λ/5` and `P → H` at
rate `2λ/3`, while neighbouring flags exchange at rate
`κN²` per directed edge.  For a centred single-site
observable `φ` (the `π`-mean-zero condition
`(4/5)φ(P) + (2/3)φ(H) = 0`) the bundled theorem proves,
for **general `N`**:

* the boxed first-chaos generator identity
  `𝓛⁰ Φ(c) = Φ(κN²Δ_N c − (22λ/15)c)` — flip part acting
  by the local renewal eigenvalue `−22λ/15`, interchange
  part by the discrete exchange Laplacian;
* the boxed exact Fourier decay rate: on the torus
  character `e_k`,
  `𝓛⁰ Φ(e_k) = −Λ_{k,N} Φ(e_k)` with
  `Λ_{k,N} = 22λ/15 + 4κN² ∑_j sin²(πk_j/N)`;
* the first nonconstant spatial mode has
  `Λ = λ(22/15 + q_N)` with
  `q_N = 4(κ/λ)N² sin²(π/N)` — the boxed renewal-clock
  persistence `A_N(s) = exp[−s(22/15 + q_N)]`;
* the boxed dwell spectral-calculus identity: the
  completed-private dwell transform
  `F_W(z) = 8z²/((5−z)(3−z))` evaluated at the slowest
  nonconstant interchange eigenvalue `z = 1/(1+q_N)`
  equals exactly
  `E(q_N) = (8/15)/((q_N+4/5)(q_N+2/3))`;
* the boxed tradeoff chain: if `E(q_N) ≤ ε` then
  `q_N ≥ (√(1+120/ε) − 11)/15`, hence
  `A_N(s) ≤ exp[−(s/15)(11 + √(1+120/ε))]` — projection
  accuracy tending to zero and persistence of one
  nonconstant spatial mode are incompatible.

The identification of `E(q_N)` with the operator-norm
error `ε_N^{proj}` of the dwell-averaged pure interchange
relative to the count projection (the renewal-probability
dwell-operator layer) is the manuscript's renewal-clock
layer; its exact spectral input — the value of the dwell
transform at the slowest interchange eigenvalue — is
proved here, together with the full generator model.
-/

open Complex Real

namespace NCG
namespace FlipInterchange

variable {N : ℕ} [NeZero N]

/-- Sites of the discrete three-torus. -/
abbrev Site (N : ℕ) := Fin 3 → ZMod N

/-- Two-state flag configurations (`true` = `P`). -/
abbrev Config (N : ℕ) := Site N → Bool

/-- Renewal flip rates: `H → P` at `4λ/5`, `P → H` at
`2λ/3`. -/
noncomputable def flipRate (lam : ℝ) (s : Bool) : ℂ :=
  if s then ((2 * lam / 3 : ℝ) : ℂ) else ((4 * lam / 5 : ℝ) : ℂ)

/-- Flip the flag at one site. -/
def flipAt (η : Config N) (x : Site N) : Config N :=
  Function.update η x (!(η x))

/-- Exchange the flags at two sites. -/
def swapAt (η : Config N) (x y : Site N) : Config N :=
  fun z => if z = x then η y else if z = y then η x else η z

/-- The unit lattice vector in direction `j`. -/
def unitVec (j : Fin 3) : Site N := Pi.single j 1

/-- The unmodulated flip–interchange generator `𝓛⁰`. -/
noncomputable def gen (lam kappa : ℝ)
    (f : Config N → ℂ) (η : Config N) : ℂ :=
  (∑ x, flipRate lam (η x) * (f (flipAt η x) - f η))
  + ((kappa * (N : ℝ) ^ 2 : ℝ) : ℂ) *
      ∑ x, ∑ j : Fin 3, (f (swapAt η x (x + unitVec j)) - f η)

/-- First-chaos observable `Φ(c)(η) = ∑_x c_x φ(η_x)`. -/
noncomputable def chaos (φ : Bool → ℂ) (c : Site N → ℂ)
    (η : Config N) : ℂ :=
  ∑ x, c x * φ (η x)

/-- The discrete exchange Laplacian on the torus. -/
noncomputable def discLap (c : Site N → ℂ) (z : Site N) : ℂ :=
  ∑ j : Fin 3, (c (z + unitVec j) + c (z - unitVec j) - 2 * c z)

/-- The additive character `m ↦ e^{2πi m/N}` of `ZMod N`. -/
noncomputable def chr (m : ZMod N) : ℂ :=
  Complex.exp (2 * (π : ℂ) * Complex.I * (m.val : ℂ) / (N : ℂ))

/-- Torus Fourier mode `e_k(x) = ∏_j e^{2πi k_j x_j / N}`. -/
noncomputable def fourierMode (k x : Site N) : ℂ :=
  ∏ j : Fin 3, chr (k j * x j)

/-- The boxed decay rate
`Λ_{k,N} = 22λ/15 + 4κN² ∑_j sin²(πk_j/N)`. -/
noncomputable def decayRate (lam kappa : ℝ) (k : Site N) : ℝ :=
  22 * lam / 15 + 4 * kappa * (N : ℝ) ^ 2 *
    ∑ j : Fin 3, Real.sin (π * ((k j).val : ℝ) / (N : ℝ)) ^ 2

/-- The completed-private dwell transform
`F_W(z) = 8z²/((5−z)(3−z))`. -/
noncomputable def dwellPGF (z : ℝ) : ℝ :=
  8 * z ^ 2 / ((5 - z) * (3 - z))

/-- The boxed projection-error floor
`E(q) = (8/15)/((q+4/5)(q+2/3))`. -/
noncomputable def Ebound (q : ℝ) : ℝ :=
  (8 / 15) / ((q + 4 / 5) * (q + 2 / 3))

/-- The interchange-to-renewal rate ratio
`q_N = 4(κ/λ)N² sin²(π/N)`. -/
noncomputable def qRatio (lam kappa : ℝ) (N : ℕ) : ℝ :=
  4 * (kappa / lam) * (N : ℝ) ^ 2 * Real.sin (π / (N : ℝ)) ^ 2

section SumLemmas

private theorem shift_sum (v : Site N) (g : Site N → ℂ) :
    ∑ x, g (x + v) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)

private theorem flip_diff (φ : Bool → ℂ) (c : Site N → ℂ)
    (η : Config N) (x : Site N) :
    chaos φ c (flipAt η x) - chaos φ c η
      = c x * (φ (!(η x)) - φ (η x)) := by
  unfold chaos flipAt
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single x
    (fun z _ hz => by rw [Function.update_of_ne hz]; ring)
    (fun h => absurd (Finset.mem_univ x) h)]
  rw [Function.update_self]
  ring

private theorem swap_diff (φ : Bool → ℂ) (c : Site N → ℂ)
    (η : Config N) (x y : Site N) :
    chaos φ c (swapAt η x y) - chaos φ c η
      = (c x - c y) * (φ (η y) - φ (η x)) := by
  unfold chaos swapAt
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ z : Site N,
      c z * φ (if z = x then η y
        else if z = y then η x else η z) - c z * φ (η z)
      = (if z = x then c z * (φ (η y) - φ (η x)) else 0)
        + (if z = y then c z * (φ (η x) - φ (η y)) else 0) := by
    intro z
    by_cases hzx : z = x
    · subst hzx
      by_cases hzy : z = y
      · subst hzy
        simp
      · rw [if_pos rfl, if_pos rfl, if_neg hzy]
        ring
    · rw [if_neg hzx, if_neg hzx]
      by_cases hzy : z = y
      · subst hzy
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hzy, if_neg hzy]
        ring
  rw [Finset.sum_congr rfl fun z _ => hpt z,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ x
      (fun z => c z * (φ (η y) - φ (η x))),
    Finset.sum_ite_eq' Finset.univ y
      (fun z => c z * (φ (η x) - φ (η y)))]
  simp only [Finset.mem_univ, if_true]
  ring

private theorem swap_part (φ : Bool → ℂ) (c : Site N → ℂ)
    (η : Config N) :
    ∑ x, ∑ j : Fin 3,
        (chaos φ c (swapAt η x (x + unitVec j)) - chaos φ c η)
      = ∑ z, discLap c z * φ (η z) := by
  have hstep : ∀ (j : Fin 3),
      ∑ x, ((c x - c (x + unitVec j)) *
          (φ (η (x + unitVec j)) - φ (η x)))
        = ∑ z, ((c (z + unitVec j) + c (z - unitVec j)
            - 2 * c z) * φ (η z)) := by
    intro j
    have e1 : ∑ x, (c x * φ (η (x + unitVec j)))
        = ∑ z, (c (z - unitVec j) * φ (η z)) := by
      rw [← shift_sum (unitVec j)
        (fun z => c (z - unitVec j) * φ (η z))]
      exact Finset.sum_congr rfl fun x _ => by
        rw [add_sub_cancel_right]
    have e3 : ∑ x, (c (x + unitVec j) * φ (η (x + unitVec j)))
        = ∑ z, (c z * φ (η z)) :=
      shift_sum (unitVec j) (fun z => c z * φ (η z))
    calc ∑ x, ((c x - c (x + unitVec j)) *
            (φ (η (x + unitVec j)) - φ (η x)))
        = ∑ x, (c x * φ (η (x + unitVec j))
            - c x * φ (η x)
            - c (x + unitVec j) * φ (η (x + unitVec j))
            + c (x + unitVec j) * φ (η x)) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ((∑ x, (c x * φ (η (x + unitVec j))))
            - ∑ x, (c x * φ (η x))
            - ∑ x, (c (x + unitVec j) * φ (η (x + unitVec j))))
            + ∑ x, (c (x + unitVec j) * φ (η x)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib]
      _ = ((∑ z, (c (z - unitVec j) * φ (η z)))
            - ∑ x, (c x * φ (η x))
            - ∑ z, (c z * φ (η z)))
            + ∑ x, (c (x + unitVec j) * φ (η x)) := by
          rw [e1, e3]
      _ = ∑ z, ((c (z + unitVec j) + c (z - unitVec j)
            - 2 * c z) * φ (η z)) := by
          have hpack : ∑ z, ((c (z + unitVec j)
              + c (z - unitVec j) - 2 * c z) * φ (η z))
              = ((∑ z, (c (z - unitVec j) * φ (η z)))
                - ∑ z, (c z * φ (η z))
                - ∑ z, (c z * φ (η z)))
                + ∑ z, (c (z + unitVec j) * φ (η z)) := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
              ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun z _ => by ring
          rw [hpack]
  calc ∑ x, ∑ j : Fin 3,
        (chaos φ c (swapAt η x (x + unitVec j)) - chaos φ c η)
      = ∑ x, ∑ j : Fin 3, ((c x - c (x + unitVec j)) *
          (φ (η (x + unitVec j)) - φ (η x))) :=
        Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun j _ => swap_diff φ c η _ _
    _ = ∑ j : Fin 3, ∑ x, ((c x - c (x + unitVec j)) *
          (φ (η (x + unitVec j)) - φ (η x))) :=
        Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ z, ((c (z + unitVec j)
          + c (z - unitVec j) - 2 * c z) * φ (η z)) :=
        Finset.sum_congr rfl fun j _ => hstep j
    _ = ∑ z, ∑ j : Fin 3, ((c (z + unitVec j)
          + c (z - unitVec j) - 2 * c z) * φ (η z)) :=
        Finset.sum_comm
    _ = ∑ z, discLap c z * φ (η z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [discLap, Finset.sum_mul]

end SumLemmas

section Character

omit [NeZero N] in
private theorem chr_zero : chr (0 : ZMod N) = 1 := by
  unfold chr
  rw [ZMod.val_zero]
  rw [show (2 * (π : ℂ) * Complex.I * ((0 : ℕ) : ℂ) / (N : ℂ))
      = 0 from by push_cast; ring]
  exact Complex.exp_zero

private theorem chr_add (m m' : ZMod N) :
    chr (m + m') = chr m * chr m' := by
  unfold chr
  rw [← Complex.exp_add, ZMod.val_add]
  have hN : ((N : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨d, hd⟩ : ∃ d : ℕ,
      m.val + m'.val = (m.val + m'.val) % N + N * d :=
    ⟨(m.val + m'.val) / N,
      (Nat.mod_add_div (m.val + m'.val) N).symm⟩
  have key : (((m.val + m'.val) % N : ℕ) : ℂ)
      = (m.val : ℂ) + (m'.val : ℂ) - (N : ℂ) * (d : ℂ) := by
    have := congrArg (fun t : ℕ => (t : ℂ)) hd
    push_cast at this
    linear_combination -this
  rw [key]
  have hsplit : (2 * (π : ℂ) * Complex.I *
      ((m.val : ℂ) + (m'.val : ℂ) - (N : ℂ) * (d : ℂ)) / (N : ℂ))
      = (2 * (π : ℂ) * Complex.I * (m.val : ℂ) / (N : ℂ)
          + 2 * (π : ℂ) * Complex.I * (m'.val : ℂ) / (N : ℂ))
        + ((-(d : ℤ) : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [hsplit, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem chr_neg (m : ZMod N) :
    chr (-m) = (chr m)⁻¹ := by
  have h := chr_add m (-m)
  rw [add_neg_cancel, chr_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

private theorem chr_cos (m : ZMod N) :
    chr m + chr (-m) - 2
      = ((-4 * Real.sin (π * (m.val : ℝ) / (N : ℝ)) ^ 2 : ℝ) : ℂ) := by
  set θ : ℝ := π * (m.val : ℝ) / (N : ℝ) with hθ
  have h1 : chr m = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    unfold chr
    congr 1
    rw [hθ]
    push_cast
    ring
  have h2 : chr (-m)
      = Complex.exp (-(((2 * θ : ℝ) : ℂ) * Complex.I)) := by
    rw [chr_neg, h1, ← Complex.exp_neg]
  rw [h1, h2, show -(((2 * θ : ℝ) : ℂ) * Complex.I)
      = (-((2 * θ : ℝ) : ℂ)) * Complex.I from by ring,
    Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  have hc := Complex.cos_two_mul ((θ : ℝ) : ℂ)
  have hs := Complex.sin_sq_add_cos_sq ((θ : ℝ) : ℂ)
  have h2θ : ((2 * θ : ℝ) : ℂ) = 2 * ((θ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2θ]
  push_cast [Complex.ofReal_sin]
  linear_combination 2 * hc + 4 * hs

private theorem fourier_shift (k x : Site N) (j : Fin 3)
    (t : ZMod N) :
    fourierMode k (x + Pi.single j t)
      = chr (k j * t) * fourierMode k x := by
  unfold fourierMode
  have hpt : ∀ i : Fin 3,
      chr (k i * ((x + Pi.single j t : Site N) i))
        = chr (k i * x i) * (if i = j then chr (k j * t) else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Pi.add_apply, Pi.single_eq_same,
        mul_add, chr_add]
    · rw [if_neg hij, Pi.add_apply,
        Pi.single_eq_of_ne hij, add_zero, mul_one]
  rw [Finset.prod_congr rfl fun i _ => hpt i,
    Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ j
      (fun _ => chr (k j * t))]
  simp only [Finset.mem_univ, if_true]
  ring

private theorem discLap_fourier (k z : Site N) :
    discLap (fourierMode k) z
      = ((-4 * ∑ j : Fin 3,
          Real.sin (π * ((k j).val : ℝ) / (N : ℝ)) ^ 2 : ℝ) : ℂ)
        * fourierMode k z := by
  unfold discLap
  have hadd : ∀ j : Fin 3, fourierMode k (z + unitVec j)
      = chr (k j) * fourierMode k z := by
    intro j
    rw [unitVec, fourier_shift, mul_one]
  have hsub : ∀ j : Fin 3, fourierMode k (z - unitVec j)
      = chr (-(k j)) * fourierMode k z := by
    intro j
    rw [unitVec, sub_eq_add_neg, ← Pi.single_neg,
      fourier_shift, mul_neg_one]
  calc ∑ j : Fin 3, (fourierMode k (z + unitVec j)
        + fourierMode k (z - unitVec j)
        - 2 * fourierMode k z)
      = ∑ j : Fin 3, ((chr (k j) + chr (-(k j)) - 2)
          * fourierMode k z) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hadd j, hsub j]
        ring
    _ = (∑ j : Fin 3, (chr (k j) + chr (-(k j)) - 2))
        * fourierMode k z := by rw [Finset.sum_mul]
    _ = ((-4 * ∑ j : Fin 3,
          Real.sin (π * ((k j).val : ℝ) / (N : ℝ)) ^ 2 : ℝ) : ℂ)
        * fourierMode k z := by
        congr 1
        rw [Finset.sum_congr rfl fun j _ => chr_cos (k j)]
        push_cast
        rw [Finset.mul_sum]

end Character

section Spectrum

/-- The boxed first-chaos generator identity
`𝓛⁰ Φ(c) = Φ(κN²Δ_N c − (22λ/15)c)`. -/
theorem gen_first_chaos (lam kappa : ℝ) (φ : Bool → ℂ)
    (hφ : (4 / 5 : ℂ) * φ true + (2 / 3 : ℂ) * φ false = 0)
    (c : Site N → ℂ) (η : Config N) :
    gen lam kappa (chaos φ c) η
      = chaos φ (fun x =>
          ((kappa * (N : ℝ) ^ 2 : ℝ) : ℂ) * discLap c x
            - ((22 * lam / 15 : ℝ) : ℂ) * c x) η := by
  have hkey : ∀ s : Bool,
      flipRate lam s * (φ (!s) - φ s)
        = -((22 * lam / 15 : ℝ) : ℂ) * φ s := by
    intro s
    cases s
    · simp only [flipRate, Bool.not_false]
      push_cast
      linear_combination (lam : ℂ) * hφ
    · simp only [flipRate, Bool.not_true]
      push_cast
      linear_combination (lam : ℂ) * hφ
  have hflip : ∑ x, flipRate lam (η x) *
        (chaos φ c (flipAt η x) - chaos φ c η)
      = ∑ x, -((22 * lam / 15 : ℝ) : ℂ) * (c x * φ (η x)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [flip_diff]
    calc flipRate lam (η x) * (c x * (φ (!(η x)) - φ (η x)))
        = c x * (flipRate lam (η x) * (φ (!(η x)) - φ (η x))) := by
          ring
      _ = c x * (-((22 * lam / 15 : ℝ) : ℂ) * φ (η x)) := by
          rw [hkey (η x)]
      _ = -((22 * lam / 15 : ℝ) : ℂ) * (c x * φ (η x)) := by
          ring
  unfold gen
  rw [hflip, swap_part]
  unfold chaos
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun x _ => ?_).symm
  ring

/-- The boxed exact Fourier decay rate
`𝓛⁰ Φ(e_k) = −Λ_{k,N} Φ(e_k)`. -/
theorem gen_fourier_decay (lam kappa : ℝ) (φ : Bool → ℂ)
    (hφ : (4 / 5 : ℂ) * φ true + (2 / 3 : ℂ) * φ false = 0)
    (k : Site N) (η : Config N) :
    gen lam kappa (chaos φ (fourierMode k)) η
      = -((decayRate lam kappa k : ℝ) : ℂ)
          * chaos φ (fourierMode k) η := by
  rw [gen_first_chaos lam kappa φ hφ]
  unfold chaos
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [discLap_fourier]
  unfold decayRate
  push_cast
  ring

end Spectrum

section Tradeoff

omit [NeZero N] in
/-- The first nonconstant spatial mode carries the
renewal-clock decay rate `λ(22/15 + q_N)`. -/
theorem decayRate_first_mode (lam kappa : ℝ)
    (hlam : lam ≠ 0) (hN : 1 < N) :
    decayRate lam kappa (Pi.single 0 1 : Site N)
      = lam * (22 / 15 + qRatio lam kappa N) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  unfold decayRate qRatio
  rw [Fin.sum_univ_three]
  rw [show ((Pi.single 0 1 : Site N) 0) = 1 from
      Pi.single_eq_same 0 1,
    show ((Pi.single 0 1 : Site N) 1) = 0 from
      Pi.single_eq_of_ne (by decide) 1,
    show ((Pi.single 0 1 : Site N) 2) = 0 from
      Pi.single_eq_of_ne (by decide) 1]
  rw [ZMod.val_one, ZMod.val_zero]
  push_cast
  rw [mul_zero, zero_div, Real.sin_zero]
  rw [show (π * 1 / (N : ℝ)) = π / (N : ℝ) from by ring]
  field_simp
  ring

/-- The boxed dwell spectral-calculus identity
`F_W(1/(1+q)) = E(q)`. -/
theorem dwell_spectral (q : ℝ) (hq : 0 ≤ q) :
    dwellPGF (1 / (1 + q)) = Ebound q := by
  unfold dwellPGF Ebound
  have h1 : (1 + q) ≠ 0 := by positivity
  have h2 : (5 : ℝ) - 1 / (1 + q) ≠ 0 := by
    have : 1 / (1 + q) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h0 : 0 < 1 / (1 + q) := by positivity
    intro h
    nlinarith
  have h3 : (3 : ℝ) - 1 / (1 + q) ≠ 0 := by
    have : 1 / (1 + q) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h0 : 0 < 1 / (1 + q) := by positivity
    intro h
    nlinarith
  have h4 : (q + 4 / 5) ≠ 0 := by positivity
  have h5 : (q + 2 / 3) ≠ 0 := by positivity
  have hA : ((5 : ℝ) - 1 / (1 + q)) * (3 - 1 / (1 + q)) ≠ 0 :=
    mul_ne_zero h2 h3
  have hB : ((q + 4 / 5) * (q + 2 / 3)) ≠ 0 :=
    mul_ne_zero h4 h5
  rw [div_eq_div_iff hA hB]
  field_simp
  ring

/-- The boxed ratio floor: `E(q) ≤ ε` forces
`q ≥ (√(1+120/ε) − 11)/15`. -/
theorem ratio_floor (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 < ε)
    (hεE : Ebound q ≤ ε) :
    (Real.sqrt (1 + 120 / ε) - 11) / 15 ≤ q := by
  unfold Ebound at hεE
  have hD : (0 : ℝ) < (q + 4 / 5) * (q + 2 / 3) := by positivity
  have h1 : 8 / 15 ≤ ε * ((q + 4 / 5) * (q + 2 / 3)) :=
    (div_le_iff₀ hD).mp hεE
  have h2 : 1 + 120 / ε ≤ (15 * q + 11) ^ 2 := by
    have h120 : 120 / ε ≤ 225 * ((q + 4 / 5) * (q + 2 / 3)) := by
      rw [div_le_iff₀ hε]
      nlinarith
    nlinarith
  have h3 : Real.sqrt (1 + 120 / ε) ≤ 15 * q + 11 := by
    rw [show (15 * q + 11 : ℝ)
        = Real.sqrt ((15 * q + 11) ^ 2) from
      (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt h2
  linarith

/-- The boxed persistence collapse:
`A_N(s) ≤ exp[−(s/15)(11 + √(1+120/ε))]`. -/
theorem persistence_collapse (q ε s : ℝ) (hq : 0 ≤ q)
    (hε : 0 < ε) (hs : 0 ≤ s) (hεE : Ebound q ≤ ε) :
    Real.exp (-(s * (22 / 15 + q)))
      ≤ Real.exp (-(s / 15 * (11 + Real.sqrt (1 + 120 / ε)))) := by
  have hfloor := ratio_floor q ε hq hε hεE
  rw [Real.exp_le_exp]
  have h4 : s * ((11 + Real.sqrt (1 + 120 / ε)) / 15)
      ≤ s * (22 / 15 + q) :=
    mul_le_mul_of_nonneg_left (by linarith) hs
  nlinarith [h4]

end Tradeoff

/-- `thm:projection-persistence-tradeoff` (exact
first-chaos spectrum and projection–persistence
tradeoff): the flip–interchange generator identity, the
exact Fourier decay rates `Λ_{k,N}` for general `N`, the
first-mode renewal-clock rate `λ(22/15 + q_N)`, the
dwell spectral value `F_W(1/(1+q_N)) = E(q_N)`, and the
boxed tradeoff chain. -/
theorem projection_persistence_tradeoff
    {N : ℕ} [NeZero N] (lam kappa ε s : ℝ) (φ : Bool → ℂ)
    (hφ : (4 / 5 : ℂ) * φ true + (2 / 3 : ℂ) * φ false = 0)
    (hlam : 0 < lam) (hkappa : 0 ≤ kappa) (hN : 1 < N)
    (hε : 0 < ε) (hs : 0 ≤ s) :
    -- (i) boxed first-chaos generator identity
    (∀ (c : Site N → ℂ) (η : Config N),
      gen lam kappa (chaos φ c) η
        = chaos φ (fun x =>
            ((kappa * (N : ℝ) ^ 2 : ℝ) : ℂ) * discLap c x
              - ((22 * lam / 15 : ℝ) : ℂ) * c x) η)
    -- (ii) boxed exact Fourier decay rate `Λ_{k,N}`
    ∧ (∀ (k : Site N) (η : Config N),
      gen lam kappa (chaos φ (fourierMode k)) η
        = -((decayRate lam kappa k : ℝ) : ℂ)
            * chaos φ (fourierMode k) η)
    -- (iii) first nonconstant mode in renewal units
    ∧ decayRate lam kappa (Pi.single 0 1 : Site N)
        = lam * (22 / 15 + qRatio lam kappa N)
    -- (iv) boxed dwell spectral calculus `F_W(1/(1+q)) = E(q)`
    ∧ dwellPGF (1 / (1 + qRatio lam kappa N))
        = Ebound (qRatio lam kappa N)
    -- (v) boxed ratio floor
    ∧ (Ebound (qRatio lam kappa N) ≤ ε →
        (Real.sqrt (1 + 120 / ε) - 11) / 15
          ≤ qRatio lam kappa N)
    -- (vi) boxed persistence collapse
    ∧ (Ebound (qRatio lam kappa N) ≤ ε →
        Real.exp (-(s * (22 / 15 + qRatio lam kappa N)))
          ≤ Real.exp
              (-(s / 15 * (11 + Real.sqrt (1 + 120 / ε))))) := by
  have hq : 0 ≤ qRatio lam kappa N := by
    unfold qRatio
    have : 0 ≤ kappa / lam := div_nonneg hkappa hlam.le
    positivity
  exact ⟨gen_first_chaos lam kappa φ hφ,
    gen_fourier_decay lam kappa φ hφ,
    decayRate_first_mode lam kappa hlam.ne' hN,
    dwell_spectral _ hq,
    fun h => ratio_floor _ ε hq hε h,
    fun h => persistence_collapse _ ε s hq hε hs h⟩

end FlipInterchange
end NCG
