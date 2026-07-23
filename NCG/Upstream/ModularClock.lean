/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Modular eigenoperators: reset symmetry and the cycle obstruction

Covers, from `manuscripts/renewal_emergence/renewal_emergence.tex`:

* `prop:transitive-common-beta` — a transitive unitary reset
  symmetry commuting with the stationary state forces one common
  modular exponent;
* `thm:finite-cycle-beta-obstruction` — a closed reset cycle whose
  product is a nonzero scalar multiple of a modular-invariant
  projection forces the exponent sum to vanish; in particular a
  common exponent on a recurrent cycle must be zero.

The modular eigenoperator relation is carried in its
finite-dimensional multiplicative form `ρ S = e^β S ρ` (criterion
(iii) of `thm:modular-eigenoperator-criteria`, equivalent to the
flow and commutator forms), over any complex algebra in which the
faithful stationary state is represented by a regular element.
-/

namespace NCG.Upstream

variable {A : Type*} [Ring A] [Algebra ℂ A] [NoZeroSMulDivisors ℂ A]

/-- The modular eigenoperator relation in multiplicative form
(criterion (iii) of `thm:modular-eigenoperator-criteria`):
`ρ S = e^β S ρ`. -/
def IsModularEigen (ρ : A) (S : A) (β : ℝ) : Prop :=
  ρ * S = (Real.exp β : ℂ) • (S * ρ)

/-- **Proposition `prop:transitive-common-beta` (uniqueness)**: the
modular exponent of a nonzero eigenoperator is unique (for a regular
stationary element). -/
theorem modularEigen_unique {ρ S : A} {β β' : ℝ}
    (hreg : ∀ x : A, x * ρ = 0 → x = 0) (hS : S ≠ 0)
    (h1 : IsModularEigen ρ S β) (h2 : IsModularEigen ρ S β') :
    β = β' := by
  have h3 : (Real.exp β : ℂ) • (S * ρ)
      = (Real.exp β' : ℂ) • (S * ρ) := by
    rw [← h1, ← h2]
  have h4 : ((Real.exp β : ℂ) - Real.exp β') • (S * ρ) = 0 := by
    rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.mp h4 with h | h
  · have h5 : (Real.exp β : ℂ) = Real.exp β' := sub_eq_zero.mp h
    have h6 : Real.exp β = Real.exp β' := by exact_mod_cast h5
    exact Real.exp_injective h6
  · exact absurd (hreg S h) hS

/-- **Proposition `prop:transitive-common-beta` (transport)**: a
unitary commuting with `ρ` transports the eigenoperator relation,
with the same exponent, onto the phase-permuted reset operator. -/
theorem modularEigen_conjugate {ρ U Ui S S' : A} {β : ℝ} (ζ : ℂ)
    (hζ : ζ ≠ 0) (hUiU : Ui * U = 1) (hUUi : U * Ui = 1)
    (hUcomm : U * ρ = ρ * U)
    (hperm : U * S * Ui = ζ • S')
    (hS : IsModularEigen ρ S β) :
    IsModularEigen ρ S' β := by
  have hUicomm : ρ * Ui = Ui * ρ := by
    calc ρ * Ui = (Ui * U) * ρ * Ui := by rw [hUiU, one_mul]
      _ = Ui * (U * ρ) * Ui := by noncomm_ring
      _ = Ui * (ρ * U) * Ui := by rw [hUcomm]
      _ = Ui * ρ * (U * Ui) := by noncomm_ring
      _ = Ui * ρ := by rw [hUUi, mul_one]
  have hkey : ρ * (U * S * Ui)
      = (Real.exp β : ℂ) • ((U * S * Ui) * ρ) := by
    calc ρ * (U * S * Ui) = (ρ * U) * S * Ui := by noncomm_ring
      _ = (U * ρ) * S * Ui := by rw [← hUcomm]
      _ = U * (ρ * S) * Ui := by noncomm_ring
      _ = U * ((Real.exp β : ℂ) • (S * ρ)) * Ui := by rw [hS]
      _ = (Real.exp β : ℂ) • (U * S * (ρ * Ui)) := by
          rw [mul_smul_comm, smul_mul_assoc]
          congr 1
          noncomm_ring
      _ = (Real.exp β : ℂ) • (U * S * (Ui * ρ)) := by rw [hUicomm]
      _ = (Real.exp β : ℂ) • ((U * S * Ui) * ρ) := by
          congr 1
          noncomm_ring
  rw [hperm, mul_smul_comm, smul_mul_assoc, smul_comm] at hkey
  exact smul_right_injective A hζ hkey

/-- **Proposition `prop:transitive-common-beta`**: if a group of
unitaries commuting with the stationary element permutes the nonzero
reset operators up to phase and acts transitively on labels, all
modular exponents coincide. -/
theorem transitive_common_beta {ι : Type*} (ρ : A) (S : ι → A)
    (βv : ι → ℝ)
    (hreg : ∀ x : A, x * ρ = 0 → x = 0) (hSne : ∀ e, S e ≠ 0)
    (heig : ∀ e, IsModularEigen ρ (S e) (βv e))
    (htrans : ∀ e e' : ι, ∃ (U Ui : A) (ζ : ℂ), ζ ≠ 0
      ∧ Ui * U = 1 ∧ U * Ui = 1 ∧ U * ρ = ρ * U
      ∧ U * S e * Ui = ζ • S e')
    (e e' : ι) : βv e = βv e' := by
  obtain ⟨U, Ui, ζ, hζ, hUiU, hUUi, hUcomm, hperm⟩ := htrans e e'
  exact modularEigen_unique hreg (hSne e')
    (modularEigen_conjugate ζ hζ hUiU hUUi hUcomm hperm (heig e))
    (heig e')

/-- **Theorem `thm:finite-cycle-beta-obstruction` (product law)**:
products of modular eigenoperators are eigenoperators with summed
exponent. -/
theorem modularEigen_mul {ρ S T : A} {β γ : ℝ}
    (hS : IsModularEigen ρ S β) (hT : IsModularEigen ρ T γ) :
    IsModularEigen ρ (S * T) (β + γ) := by
  unfold IsModularEigen at *
  calc ρ * (S * T) = (ρ * S) * T := by noncomm_ring
    _ = ((Real.exp β : ℂ) • (S * ρ)) * T := by rw [hS]
    _ = (Real.exp β : ℂ) • (S * (ρ * T)) := by
        rw [smul_mul_assoc]
        congr 1
        noncomm_ring
    _ = (Real.exp β : ℂ) • (S * ((Real.exp γ : ℂ) • (T * ρ))) := by
        rw [hT]
    _ = ((Real.exp β : ℂ) * (Real.exp γ : ℂ)) • (S * (T * ρ)) := by
        rw [mul_smul_comm, smul_smul]
    _ = (Real.exp (β + γ) : ℂ) • ((S * T) * ρ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        congr 1
        noncomm_ring

/-- The identity is an eigenoperator with exponent zero. -/
theorem modularEigen_one (ρ : A) : IsModularEigen ρ 1 0 := by
  unfold IsModularEigen
  rw [mul_one, one_mul, Real.exp_zero]
  norm_num

/-- **Theorem `thm:finite-cycle-beta-obstruction` (cycle
products)**: the ordered product of a list of eigenoperators is an
eigenoperator whose exponent is the sum. -/
theorem modularEigen_list_prod (ρ : A) :
    ∀ l : List (A × ℝ), (∀ p ∈ l, IsModularEigen ρ p.1 p.2) →
      IsModularEigen ρ (l.map Prod.fst).prod (l.map Prod.snd).sum
  | [], _ => by
      simpa using modularEigen_one ρ
  | p :: l, h => by
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact modularEigen_mul (h p List.mem_cons_self)
        (modularEigen_list_prod ρ l fun q hq =>
          h q (List.mem_cons_of_mem p hq))

/-- **Theorem `thm:finite-cycle-beta-obstruction`**: if a closed
reset cycle of modular eigenoperators has product a nonzero scalar
multiple of a projection commuting with the stationary element (the
scalar return on a modular-invariant corner), then the exponent sum
vanishes. -/
theorem finite_cycle_beta_obstruction (ρ : A) (l : List (A × ℝ))
    (heig : ∀ p ∈ l, IsModularEigen ρ p.1 p.2)
    (c : ℂ) (hc : c ≠ 0) (P : A) (hPne : P ≠ 0)
    (hprod : (l.map Prod.fst).prod = c • P)
    (hPcomm : P * ρ = ρ * P)
    (hreg : ∀ x : A, x * ρ = 0 → x = 0) :
    (l.map Prod.snd).sum = 0 := by
  have h1 := modularEigen_list_prod ρ l heig
  rw [hprod] at h1
  unfold IsModularEigen at h1
  rw [mul_smul_comm, smul_mul_assoc, smul_comm] at h1
  have h2 : ρ * P
      = (Real.exp ((l.map Prod.snd).sum) : ℂ) • (P * ρ) :=
    smul_right_injective A hc h1
  rw [← hPcomm] at h2
  have h3 : ((1 : ℂ) - (Real.exp ((l.map Prod.snd).sum) : ℂ))
      • (P * ρ) = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · have h4 : (Real.exp ((l.map Prod.snd).sum) : ℂ) = 1 :=
      (sub_eq_zero.mp h).symm
    have h5 : Real.exp ((l.map Prod.snd).sum) = 1 := by
      exact_mod_cast h4
    calc (l.map Prod.snd).sum
        = Real.log (Real.exp ((l.map Prod.snd).sum)) :=
          (Real.log_exp _).symm
      _ = 0 := by rw [h5, Real.log_one]
  · exact absurd (hreg P h) hPne

/-- **Theorem `thm:finite-cycle-beta-obstruction` (common
exponent)**: if all exponents on a nonempty scalar-return cycle
share one value `β`, then `β = 0`. -/
theorem finite_cycle_common_beta_zero (ρ : A) (l : List (A × ℝ))
    (heig : ∀ p ∈ l, IsModularEigen ρ p.1 p.2)
    (c : ℂ) (hc : c ≠ 0) (P : A) (hPne : P ≠ 0)
    (hprod : (l.map Prod.fst).prod = c • P)
    (hPcomm : P * ρ = ρ * P)
    (hreg : ∀ x : A, x * ρ = 0 → x = 0)
    (β : ℝ) (hall : ∀ p ∈ l, p.2 = β) (hne : l ≠ []) :
    β = 0 := by
  have hsum := finite_cycle_beta_obstruction ρ l heig c hc P hPne
    hprod hPcomm hreg
  have hmap : (l.map Prod.snd).sum = l.length * β := by
    have hrep : l.map Prod.snd = List.replicate l.length β := by
      apply List.eq_replicate_iff.mpr
      constructor
      · rw [List.length_map]
      · intro b hb
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
        exact hall p hp
    rw [hrep, List.sum_replicate, nsmul_eq_mul]
  rw [hmap] at hsum
  have hlen : (l.length : ℝ) ≠ 0 := by
    have h0 : 0 < l.length := List.length_pos_iff.mpr hne
    positivity
  exact (mul_eq_zero.mp hsum).resolve_left hlen

end NCG.Upstream
