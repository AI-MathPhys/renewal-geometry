/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The common-origin resolved transition balance

Scalar layer of the common-origin model of `manuscripts/renewal_emergence/renewal_emergence.tex`
(App. common-origin): the finite-volume Ising heat-bath data and the
**boxed resolved transition balance** of `thm:common-origin-balance`,

`μ_{Λ,θ}(η) w_{i,s,a,b}(η) = μ_{Λ,θ}(ξ) w_{i,η_i,a,b}(ξ)`,
`ξ = η^{i,s}`,

together with the structural facts consumed by the UCP layer:

* `m_update_self`, `m_neg` — locality and oddness of the local field;
* `energy_update` — the single-site energy increment
  `E(η^{i,s}) − E(η) = (s − η_i) m_i(η)` (double counting over the
  symmetric neighbourhoods);
* `q_pos`, `q_sum` — the heat-bath probabilities are a positive
  probability law on `{±1}`;
* `q_deck` — deck reversal `q_i(s|−η) = q_i(−s|η)`, and
  `update_neg` — deck reversal commutes with single-site redraw;
* `heat_bath_balance` — classical single-site detailed balance for
  the Gibbs weight `μ ∝ e^{θE}`;
* `resolved_balance` — the boxed identity, for **arbitrary** site
  weights `ν`, direction-record profile `r` (a function of the
  orientation argument `u = η_i s`), and internal weights `κ`;
* `dirProfile_pos`, `dirProfile_sum` — the tilted direction-record
  profile `r_{i,a}(u) = λ_{i,a}(1+εb_a u)/Σ_c λ_{i,c}(1+εb_c u)` is
  a positive probability law for `|u| ≤ 1` when `δ = |ε|max_a|b_a| < 1`.

The redraw value `s` and the spins are arbitrary reals; the `±1`
constraint is only needed (and assumed, as `|u| ≤ 1`) for the
direction-profile positivity.
-/

namespace NCG.CommonOrigin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite-volume Ising data: symmetric neighbourhoods without
self-loops and an inverse temperature. -/
structure IsingData (ι : Type*) where
  /-- The neighbourhood of each site. -/
  N : ι → Finset ι
  N_symm : ∀ i j : ι, i ∈ N j ↔ j ∈ N i
  N_irrefl : ∀ i : ι, i ∉ N i
  /-- The inverse temperature. -/
  θ : ℝ

namespace IsingData

variable (D : IsingData ι)

/-- The local field `m_i(η) = Σ_{j∼i} η_j`. -/
def m (i : ι) (η : ι → ℝ) : ℝ := ∑ j ∈ D.N i, η j

/-- The Ising energy `E(η) = ½ Σ_i η_i m_i(η)`. -/
noncomputable def energy (η : ι → ℝ) : ℝ :=
  (∑ i, η i * D.m i η) / 2

/-- The unnormalized Gibbs weight `μ_{Λ,θ}(η) = e^{θ E(η)}`. -/
noncomputable def gibbs (η : ι → ℝ) : ℝ :=
  Real.exp (D.θ * D.energy η)

/-- The heat-bath redraw probability
`q_i(s|η) = e^{θ s m_i(η)} / (2 cosh(θ m_i(η)))`. -/
noncomputable def q (i : ι) (s : ℝ) (η : ι → ℝ) : ℝ :=
  Real.exp (D.θ * s * D.m i η) / (2 * Real.cosh (D.θ * D.m i η))

omit [DecidableEq ι] in
theorem gibbs_pos (η : ι → ℝ) : 0 < D.gibbs η := Real.exp_pos _

omit [DecidableEq ι] [Fintype ι] in
theorem q_pos (i : ι) (s : ℝ) (η : ι → ℝ) : 0 < D.q i s η :=
  div_pos (Real.exp_pos _)
    (mul_pos two_pos (Real.cosh_pos _))

omit [DecidableEq ι] [Fintype ι] in
/-- The heat-bath law is normalized over the two redraw values. -/
theorem q_sum (i : ι) (η : ι → ℝ) :
    D.q i 1 η + D.q i (-1) η = 1 := by
  have h1 : 0 < Real.exp (D.θ * D.m i η)
      + Real.exp (-(D.θ * D.m i η)) := by positivity
  rw [q, q, ← add_div,
    show D.θ * 1 * D.m i η = D.θ * D.m i η by ring,
    show D.θ * (-1) * D.m i η = -(D.θ * D.m i η) by ring,
    Real.cosh_eq]
  field_simp

omit [Fintype ι] in
/-- Locality: the local field at `i` does not see the spin at `i`. -/
theorem m_update_self (i : ι) (η : ι → ℝ) (s : ℝ) :
    D.m i (Function.update η i s) = D.m i η := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := fun h => D.N_irrefl i (h ▸ hj)
  exact Function.update_of_ne hji s η

omit [DecidableEq ι] [Fintype ι] in
/-- Oddness of the local field under deck reversal. -/
theorem m_neg (i : ι) (η : ι → ℝ) : D.m i (-η) = -(D.m i η) := by
  rw [m, m, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

omit [DecidableEq ι] [Fintype ι] in
/-- Deck reversal of the heat-bath law: `q_i(s|−η) = q_i(−s|η)`. -/
theorem q_deck (i : ι) (s : ℝ) (η : ι → ℝ) :
    D.q i s (-η) = D.q i (-s) η := by
  rw [q, q, D.m_neg]
  rw [show D.θ * s * -D.m i η = D.θ * -s * D.m i η by ring,
    show D.θ * -D.m i η = -(D.θ * D.m i η) by ring,
    Real.cosh_neg]

omit [Fintype ι] in
/-- Deck reversal commutes with single-site redraw:
`(−η)^{i,s} = −(η^{i,−s})`. -/
theorem update_neg (i : ι) (η : ι → ℝ) (s : ℝ) :
    Function.update (-η) i s = -(Function.update η i (-s)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Pi.neg_apply, Function.update_self,
      neg_neg]
  · rw [Function.update_of_ne hj, Pi.neg_apply, Pi.neg_apply,
      Function.update_of_ne hj]

/-- **Single-site energy increment**:
`E(η^{i,s}) = E(η) + (s − η_i) m_i(η)`, by double counting over the
symmetric self-loop-free neighbourhoods. -/
theorem energy_update (i : ι) (η : ι → ℝ) (s : ℝ) :
    D.energy (Function.update η i s)
      = D.energy η + (s - η i) * D.m i η := by
  set η' := Function.update η i s with hη'
  have hdiag : η' i * D.m i η' - η i * D.m i η
      = (s - η i) * D.m i η := by
    rw [hη', Function.update_self, D.m_update_self]
    ring
  have hoff : ∀ k, k ≠ i →
      η' k * D.m k η' - η k * D.m k η
        = (if k ∈ D.N i then η k * (s - η i) else 0) := by
    intro k hk
    have h1 : η' k = η k := Function.update_of_ne hk s η
    have h3 : ∀ j ∈ D.N k,
        η' j - η j = (if j = i then s - η i else 0) := by
      intro j _
      by_cases hj : j = i
      · subst hj
        rw [hη', Function.update_self, if_pos rfl]
      · rw [hη', Function.update_of_ne hj, sub_self, if_neg hj]
    have h2 : D.m k η' - D.m k η
        = (if k ∈ D.N i then s - η i else 0) := by
      rw [m, m, ← Finset.sum_sub_distrib, Finset.sum_congr rfl h3,
        Finset.sum_ite_eq' (D.N k) i]
      by_cases hik : k ∈ D.N i
      · rw [if_pos ((D.N_symm i k).mpr hik), if_pos hik]
      · rw [if_neg (fun h => hik ((D.N_symm i k).mp h)),
          if_neg hik]
    rw [h1, show η k * D.m k η' - η k * D.m k η
        = η k * (D.m k η' - D.m k η) by ring, h2]
    by_cases hik : k ∈ D.N i
    · rw [if_pos hik, if_pos hik]
    · rw [if_neg hik, if_neg hik, mul_zero]
  have h4 : ∑ k, (η' k * D.m k η' - η k * D.m k η)
      = 2 * ((s - η i) * D.m i η) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag]
    have h5 : ∑ k ∈ Finset.univ.erase i,
        (η' k * D.m k η' - η k * D.m k η)
          = ∑ k ∈ Finset.univ.erase i,
              (if k ∈ D.N i then η k * (s - η i) else 0) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact hoff k (Finset.ne_of_mem_erase hk)
    rw [h5, Finset.sum_ite_mem]
    have h6 : (Finset.univ.erase i) ∩ D.N i = D.N i := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_erase,
        Finset.mem_univ, and_true,
        and_iff_right_iff_imp]
      intro hk hki
      rw [hki] at hk
      exact D.N_irrefl i hk
    rw [h6]
    have h7 : ∑ k ∈ D.N i, η k * (s - η i)
        = (s - η i) * D.m i η := by
      rw [m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h7]
    ring
  have h8 : ∑ k, (η' k * D.m k η' - η k * D.m k η)
      = (∑ k, η' k * D.m k η') - ∑ k, η k * D.m k η := by
    rw [Finset.sum_sub_distrib]
  rw [h8] at h4
  rw [energy, energy]
  linarith

/-- **Classical single-site detailed balance** for the Gibbs weight:
`μ(η) q_i(s|η) = μ(η^{i,s}) q_i(η_i|η^{i,s})`. -/
theorem heat_bath_balance (i : ι) (η : ι → ℝ) (s : ℝ) :
    D.gibbs η * D.q i s η
      = D.gibbs (Function.update η i s)
        * D.q i (η i) (Function.update η i s) := by
  set ξ := Function.update η i s with hξ
  have hm : D.m i ξ = D.m i η := D.m_update_self i η s
  have henergy : D.energy ξ = D.energy η + (s - η i) * D.m i η :=
    D.energy_update i η s
  have hexp : Real.exp (D.θ * D.energy η)
      * Real.exp (D.θ * s * D.m i η)
      = Real.exp (D.θ * D.energy ξ)
        * Real.exp (D.θ * η i * D.m i η) := by
    rw [← Real.exp_add, ← Real.exp_add, henergy]
    congr 1
    ring
  have hc : (2 * Real.cosh (D.θ * D.m i η)) ≠ 0 :=
    (mul_pos two_pos (Real.cosh_pos _)).ne'
  rw [gibbs, gibbs, q, q, hm, ← mul_div_assoc, ← mul_div_assoc,
    div_eq_div_iff hc hc]
  exact congrArg
    (fun t => t * (2 * Real.cosh (D.θ * D.m i η))) hexp

/-- The resolved transition weight
`w_{i,s,a,b}(η) = ν_i q_i(s|η) r_{i,a}(η_i s) κ_b`, for arbitrary
site weights, direction-record profile and internal weights. -/
noncomputable def w {α β : Type*} (ν : ι → ℝ) (r : ι → α → ℝ → ℝ)
    (κ : β → ℝ) (i : ι) (s : ℝ) (a : α) (b : β) (η : ι → ℝ) : ℝ :=
  ν i * D.q i s η * r i a (η i * s) * κ b

/-- **Theorem `thm:common-origin-balance` (boxed resolved transition
balance)**: `μ_{Λ,θ}(η) w_{i,s,a,b}(η) = μ_{Λ,θ}(ξ) w_{i,η_i,a,b}(ξ)`
with `ξ = η^{i,s}` — the reverse elementary transition has fixed
redraw value `η_i` and the same direction and internal records. -/
theorem resolved_balance {α β : Type*} (ν : ι → ℝ)
    (r : ι → α → ℝ → ℝ) (κ : β → ℝ) (i : ι) (s : ℝ) (a : α) (b : β)
    (η : ι → ℝ) :
    D.gibbs η * D.w ν r κ i s a b η
      = D.gibbs (Function.update η i s)
        * D.w ν r κ i (η i) a b (Function.update η i s) := by
  set ξ := Function.update η i s with hξ
  have hbal := D.heat_bath_balance i η s
  have hr : r i a (ξ i * η i) = r i a (η i * s) := by
    rw [hξ, Function.update_self, mul_comm]
  rw [w, w, hr]
  calc D.gibbs η * (ν i * D.q i s η * r i a (η i * s) * κ b)
      = (D.gibbs η * D.q i s η)
          * (ν i * r i a (η i * s) * κ b) := by ring
    _ = (D.gibbs ξ * D.q i (η i) ξ)
          * (ν i * r i a (η i * s) * κ b) := by rw [hbal]
    _ = D.gibbs ξ * (ν i * D.q i (η i) ξ * r i a (η i * s) * κ b)
        := by ring

end IsingData

/-! ## The tilted direction-record profile -/

/-- The tilted direction weight `λ_{i,a}(1 + ε b_a u)`. -/
def dirWeight {ι α : Type*} (lam : ι → α → ℝ) (ε : ℝ) (bb : α → ℝ)
    (i : ι) (a : α) (u : ℝ) : ℝ :=
  lam i a * (1 + ε * bb a * u)

/-- The direction-record profile
`r_{i,a}(u) = λ_{i,a}(1+εb_a u)/Σ_c λ_{i,c}(1+εb_c u)`. -/
noncomputable def dirProfile {ι α : Type*} [Fintype α]
    (lam : ι → α → ℝ) (ε : ℝ) (bb : α → ℝ) (i : ι) (a : α)
    (u : ℝ) : ℝ :=
  dirWeight lam ε bb i a u / ∑ c, dirWeight lam ε bb i c u

theorem dirWeight_pos {ι α : Type*} (lam : ι → α → ℝ) (ε : ℝ)
    (bb : α → ℝ) {B : ℝ} (hlam : ∀ i a, 0 < lam i a)
    (hb : ∀ a, |bb a| ≤ B) (hδ : |ε| * B < 1)
    (i : ι) (a : α) {u : ℝ} (hu : |u| ≤ 1) :
    0 < dirWeight lam ε bb i a u := by
  have h1 : |ε * bb a * u| < 1 := by
    rw [abs_mul, abs_mul]
    have h4 : |ε| * |bb a| ≤ |ε| * B :=
      mul_le_mul_of_nonneg_left (hb a) (abs_nonneg ε)
    have h5 : |ε| * |bb a| * |u| ≤ |ε| * |bb a| * 1 :=
      mul_le_mul_of_nonneg_left hu
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc |ε| * |bb a| * |u| ≤ |ε| * |bb a| * 1 := h5
      _ = |ε| * |bb a| := mul_one _
      _ ≤ |ε| * B := h4
      _ < 1 := hδ
  have h6 : -(1 : ℝ) < ε * bb a * u := (abs_lt.mp h1).1
  rw [dirWeight]
  refine mul_pos (hlam i a) ?_
  linarith

theorem dirProfile_pos {ι α : Type*} [Fintype α] [Nonempty α]
    (lam : ι → α → ℝ) (ε : ℝ) (bb : α → ℝ) {B : ℝ}
    (hlam : ∀ i a, 0 < lam i a) (hb : ∀ a, |bb a| ≤ B)
    (hδ : |ε| * B < 1) (i : ι) (a : α) {u : ℝ} (hu : |u| ≤ 1) :
    0 < dirProfile lam ε bb i a u :=
  div_pos (dirWeight_pos lam ε bb hlam hb hδ i a hu)
    (Finset.sum_pos
      (fun c _ => dirWeight_pos lam ε bb hlam hb hδ i c hu)
      Finset.univ_nonempty)

/-- The direction-record profile is a probability law over the
direction records. -/
theorem dirProfile_sum {ι α : Type*} [Fintype α] [Nonempty α]
    (lam : ι → α → ℝ) (ε : ℝ) (bb : α → ℝ) {B : ℝ}
    (hlam : ∀ i a, 0 < lam i a) (hb : ∀ a, |bb a| ≤ B)
    (hδ : |ε| * B < 1) (i : ι) {u : ℝ} (hu : |u| ≤ 1) :
    ∑ a, dirProfile lam ε bb i a u = 1 := by
  have hden : 0 < ∑ c, dirWeight lam ε bb i c u :=
    Finset.sum_pos
      (fun c _ => dirWeight_pos lam ε bb hlam hb hδ i c hu)
      Finset.univ_nonempty
  have h2 : ∑ a, dirProfile lam ε bb i a u
      = (∑ a, dirWeight lam ε bb i a u)
        / ∑ c, dirWeight lam ε bb i c u := by
    simp only [dirProfile]
    rw [Finset.sum_div]
  rw [h2]
  exact div_self hden.ne'

end NCG.CommonOrigin
