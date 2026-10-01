/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.FiniteLaplaceSandwich

/-!
# Finite sub-stochastic Markov path sums, capped retries and the Gibbs mean bound

Infrastructure for the explicit accept/reject cylinders of
`thm:main-explicit-operational-family` (emergent-spacetime manuscript, Appendix
`supp:homogeneous-dynamics`).  Everything is finite and elementary.

**Paths.**  Given alphabets `F : ℕ → Finset ℝ` and a start value `x₀`, `paths F x₀ k` is the
finite set of real sequences `q` with `q 0 = x₀`, `q j ∈ F j` for `1 ≤ j ≤ k` and `q j = 0` for
`j > k` (`mem_paths`).  `sum_paths_succ` is the one-stage decomposition of a path sum.

**Path weights.**  For a stage kernel `K j x y ≥ 0` the weight of a path is
`weight K k q = ∏_{j<k} K j (q j) (q (j+1))`.  If every row has mass `≤ 1` then
* `mass_le_one`: the total weight is `≤ 1`;
* `one_sub_mul_le_mass`: if every row has mass `≥ 1 − η`, the total weight is `≥ 1 − kη`;
* `expect_addSum_le`: the weighted sum of an additive path functional
  `∑_{j<k} c j (q j) (q (j+1))` is bounded by `∑_{j<k} B_j` as soon as every one-step mean
  `∑_y K j x y c j x y` is bounded by `B_j`;
* `failMass_add_mass`, `failMass_le`: with a defect `D j x = 1 − ∑_y K j x y` (the probability
  of stopping at stage `j` from `x`), the total stopping mass plus the total path weight is `1`,
  and the stopping mass is at most `kη` if every defect is at most `η`.

**Capped retries.**  `retryLaw G p a R` is the law (on `Option ℝ`, `none` = cap exhausted) of the
accept/reject trial loop: propose `y ∈ G` with probability `p y`, accept with probability `a y`,
otherwise retry, with at most `R` proposals.  It is defined by its first-trial recursion, and
`retryLaw_none`, `retryLaw_some` give the closed forms `(1 − Z)^R` and
`p y a y ∑_{i<R} (1 − Z)^i` (`Z = ∑_y p y a y`); `retryLaw_total` shows it is a probability law,
`retryLaw_some_le` that each accepted value has probability at most the accepted row
`p y a y / Z`, and `retryLaw_none_le_exp` gives `(1 − Z)^R ≤ exp (−Z_* R)` for `Z ≥ Z_*`.

**Gibbs mean.**  `gibbs_mean_le_softMin`: the mean cost under the normalized Boltzmann row
`exp(−c/ε)/∑ exp(−c/ε)` is at most the normalized soft minimum
`FiniteLaplace.softMin ε G c = −ε log(#G⁻¹ ∑ exp(−c/ε))` (Gibbs' inequality; the gap is
`ε` times the relative entropy to the uniform row), hence at most `c y₀ + ε log #G`
for every `y₀ ∈ G` by `FiniteLaplace.softMin_le` (the entropy–energy estimate
`lem:supp-entropy-energy` for one row).
-/

namespace RenewalGeometry.FiniteMarkovPaths

open Finset

noncomputable section

open Classical

/-! ### Paths through finite alphabets -/

/-- The base path: `x₀` at time `0`, zero afterwards. -/
def basePath (x₀ : ℝ) : ℕ → ℝ := fun j => if j = 0 then x₀ else 0

/-- The finite set of `k`-stage paths through the alphabets `F`: `q 0 = x₀`, `q j ∈ F j` for
`1 ≤ j ≤ k`, and `q j = 0` for `j > k`. -/
def paths (F : ℕ → Finset ℝ) (x₀ : ℝ) : ℕ → Finset (ℕ → ℝ)
  | 0 => {basePath x₀}
  | k + 1 => (paths F x₀ k).biUnion fun q => (F (k + 1)).image fun y => Function.update q (k + 1) y

variable {F : ℕ → Finset ℝ} {x₀ : ℝ}

/-- Membership in `paths F x₀ k`. -/
theorem mem_paths {k : ℕ} {q : ℕ → ℝ} (hq : q ∈ paths F x₀ k) :
    q 0 = x₀ ∧ (∀ j, 1 ≤ j → j ≤ k → q j ∈ F j) ∧ ∀ j, k < j → q j = 0 := by
  induction k generalizing q with
  | zero =>
    simp only [paths, mem_singleton] at hq
    subst hq
    refine ⟨by simp [basePath], fun j h1 h2 => by omega, fun j hj => ?_⟩
    simp [basePath]; omega
  | succ k ih =>
    simp only [paths, mem_biUnion, mem_image] at hq
    obtain ⟨q', hq', y, hy, rfl⟩ := hq
    obtain ⟨h0, h1, h2⟩ := ih hq'
    refine ⟨?_, fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact h0
    · by_cases hj : j = k + 1
      · subst hj; rw [Function.update_self]; exact hy
      · rw [Function.update_of_ne hj]; exact h1 j hj1 (by omega)
    · rw [Function.update_of_ne (by omega)]; exact h2 j (by omega)

/-- Every coordinate `j ≤ k` of a path lies in its alphabet when `x₀ ∈ F 0`. -/
theorem mem_alphabet (hx₀ : x₀ ∈ F 0) {k : ℕ} {q : ℕ → ℝ} (hq : q ∈ paths F x₀ k) {j : ℕ}
    (hj : j ≤ k) : q j ∈ F j := by
  obtain ⟨h0, h1, -⟩ := mem_paths hq
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [h0]; exact hx₀
  · exact h1 j hpos hj

/-- **One-stage decomposition of a path sum.** -/
theorem sum_paths_succ (g : (ℕ → ℝ) → ℝ) (k : ℕ) :
    ∑ q ∈ paths F x₀ (k + 1), g q
      = ∑ q ∈ paths F x₀ k, ∑ y ∈ F (k + 1), g (Function.update q (k + 1) y) := by
  rw [paths, sum_biUnion]
  · refine sum_congr rfl fun q _ => ?_
    rw [sum_image]
    intro y _ y' _ h
    have := congrFun h (k + 1)
    simpa using this
  · intro q hq q' hq' hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image] at hp hp'
    obtain ⟨y, -, rfl⟩ := hp
    obtain ⟨y', -, h⟩ := hp'
    apply hne
    funext j
    by_cases hj : j = k + 1
    · subst hj
      rw [(mem_paths (Finset.mem_coe.1 hq)).2.2 _ (by omega),
        (mem_paths (Finset.mem_coe.1 hq')).2.2 _ (by omega)]
    · have := congrFun h j
      rw [Function.update_of_ne hj, Function.update_of_ne hj] at this
      exact this.symm

/-! ### Path weights -/

/-- The weight `∏_{j<k} K j (q j) (q (j+1))` of a `k`-stage path. -/
def weight (K : ℕ → ℝ → ℝ → ℝ) (k : ℕ) (q : ℕ → ℝ) : ℝ :=
  ∏ j ∈ range k, K j (q j) (q (j + 1))

/-- The additive path functional `∑_{j<k} c j (q j) (q (j+1))`. -/
def addSum (c : ℕ → ℝ → ℝ → ℝ) (k : ℕ) (q : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range k, c j (q j) (q (j + 1))

theorem weight_update (K : ℕ → ℝ → ℝ → ℝ) (k : ℕ) (q : ℕ → ℝ) (y : ℝ) :
    weight K (k + 1) (Function.update q (k + 1) y) = weight K k q * K k (q k) y := by
  unfold weight
  rw [prod_range_succ, Function.update_self, Function.update_of_ne (by omega)]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hj := mem_range.1 hj
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem addSum_update (c : ℕ → ℝ → ℝ → ℝ) (k : ℕ) (q : ℕ → ℝ) (y : ℝ) :
    addSum c (k + 1) (Function.update q (k + 1) y) = addSum c k q + c k (q k) y := by
  unfold addSum
  rw [sum_range_succ, Function.update_self, Function.update_of_ne (by omega)]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.1 hj
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

variable {K : ℕ → ℝ → ℝ → ℝ}

theorem weight_nonneg (hK0 : ∀ j x y, 0 ≤ K j x y) (k : ℕ) (q : ℕ → ℝ) : 0 ≤ weight K k q :=
  prod_nonneg fun j _ => hK0 _ _ _

/-- The total weight of `k`-stage paths. -/
def mass (F : ℕ → Finset ℝ) (x₀ : ℝ) (K : ℕ → ℝ → ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ q ∈ paths F x₀ k, weight K k q

theorem mass_zero : mass F x₀ K 0 = 1 := by
  simp [mass, paths, weight]

theorem mass_succ (k : ℕ) :
    mass F x₀ K (k + 1) = ∑ q ∈ paths F x₀ k, weight K k q * ∑ y ∈ F (k + 1), K k (q k) y := by
  unfold mass
  rw [sum_paths_succ]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => weight_update K k q y

theorem mass_nonneg (hK0 : ∀ j x y, 0 ≤ K j x y) (k : ℕ) : 0 ≤ mass F x₀ K k :=
  sum_nonneg fun q _ => weight_nonneg hK0 k q

/-- **Sub-stochastic rows give total weight at most one.** -/
theorem mass_le_one (hx₀ : x₀ ∈ F 0) (hK0 : ∀ j x y, 0 ≤ K j x y)
    (hK1 : ∀ j x, x ∈ F j → ∑ y ∈ F (j + 1), K j x y ≤ 1) (k : ℕ) : mass F x₀ K k ≤ 1 := by
  induction k with
  | zero => rw [mass_zero]
  | succ k ih =>
    rw [mass_succ]
    calc ∑ q ∈ paths F x₀ k, weight K k q * ∑ y ∈ F (k + 1), K k (q k) y
        ≤ ∑ q ∈ paths F x₀ k, weight K k q * 1 :=
          sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
            (hK1 k (q k) (mem_alphabet hx₀ hq le_rfl)) (weight_nonneg hK0 k q)
      _ ≤ 1 := by simpa [mass] using ih

/-- **Rows of mass at least `1 − η` give total weight at least `1 − kη`.** -/
theorem one_sub_mul_le_mass (hx₀ : x₀ ∈ F 0) (hK0 : ∀ j x y, 0 ≤ K j x y)
    (hK1 : ∀ j x, x ∈ F j → ∑ y ∈ F (j + 1), K j x y ≤ 1) {η : ℝ} (k : ℕ)
    (hη : ∀ j < k, ∀ x ∈ F j, 1 - η ≤ ∑ y ∈ F (j + 1), K j x y) :
    1 - k * η ≤ mass F x₀ K k := by
  induction k with
  | zero => rw [mass_zero]; simp
  | succ k ih =>
    have ih' := ih fun j hj => hη j (by omega)
    have hle := mass_le_one hx₀ hK0 hK1 (x₀ := x₀) k
    rw [mass_succ]
    have : ∑ q ∈ paths F x₀ k, weight K k q * (1 - η)
        ≤ ∑ q ∈ paths F x₀ k, weight K k q * ∑ y ∈ F (k + 1), K k (q k) y :=
      sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
        (hη k (by omega) (q k) (mem_alphabet hx₀ hq le_rfl)) (weight_nonneg hK0 k q)
    rw [← sum_mul] at this
    change mass F x₀ K k * (1 - η) ≤ _ at this
    have hη0 : 0 ≤ η := by
      have h1 := hη 0 (by omega) x₀ hx₀
      have h2 := hK1 0 x₀ hx₀
      linarith
    push_cast
    nlinarith

/-- **Expectation of an additive path functional.**  If every one-step mean
`∑_y K j x y c j x y` is at most `B_j ≥ 0`, the weighted sum of `∑_{j<k} c j (q j) (q (j+1))`
over `k`-stage paths is at most `∑_{j<k} B_j`. -/
theorem expect_addSum_le (hx₀ : x₀ ∈ F 0) (hK0 : ∀ j x y, 0 ≤ K j x y)
    (hK1 : ∀ j x, x ∈ F j → ∑ y ∈ F (j + 1), K j x y ≤ 1) (c : ℕ → ℝ → ℝ → ℝ)
    (hc : ∀ j x y, 0 ≤ c j x y) (B : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B j) (k : ℕ)
    (hB : ∀ j < k, ∀ x ∈ F j, ∑ y ∈ F (j + 1), K j x y * c j x y ≤ B j) :
    ∑ q ∈ paths F x₀ k, weight K k q * addSum c k q ≤ ∑ j ∈ range k, B j := by
  induction k with
  | zero => simp [addSum]
  | succ k ih =>
    have ih' := ih fun j hj => hB j (by omega)
    rw [sum_paths_succ, sum_range_succ]
    have hstep : ∀ q ∈ paths F x₀ k,
        ∑ y ∈ F (k + 1), weight K (k + 1) (Function.update q (k + 1) y) *
          addSum c (k + 1) (Function.update q (k + 1) y)
        ≤ weight K k q * addSum c k q + weight K k q * B k := by
      intro q hq
      have hx := mem_alphabet hx₀ hq le_rfl
      have hw := weight_nonneg hK0 k q
      have hA : 0 ≤ addSum c k q := sum_nonneg fun j _ => hc _ _ _
      simp_rw [weight_update, addSum_update]
      have e : ∑ y ∈ F (k + 1), weight K k q * K k (q k) y * (addSum c k q + c k (q k) y)
          = weight K k q * addSum c k q * ∑ y ∈ F (k + 1), K k (q k) y
            + weight K k q * ∑ y ∈ F (k + 1), K k (q k) y * c k (q k) y := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun y _ => by ring
      rw [e]
      have h1 := hK1 k (q k) hx
      have h2 := hB k (by omega) (q k) hx
      have := mul_nonneg hw hA
      nlinarith [mul_le_mul_of_nonneg_left h2 hw]
    calc ∑ q ∈ paths F x₀ k, ∑ y ∈ F (k + 1), weight K (k + 1) (Function.update q (k + 1) y) *
          addSum c (k + 1) (Function.update q (k + 1) y)
        ≤ ∑ q ∈ paths F x₀ k, (weight K k q * addSum c k q + weight K k q * B k) :=
          sum_le_sum hstep
      _ = ∑ q ∈ paths F x₀ k, weight K k q * addSum c k q + mass F x₀ K k * B k := by
          rw [sum_add_distrib, mass, sum_mul]
      _ ≤ ∑ j ∈ range k, B j + 1 * B k := by
          gcongr
          · exact hB0 k
          · exact mass_le_one hx₀ hK0 hK1 k
      _ = ∑ j ∈ range k, B j + B k := by ring

/-- The total stopping (failure) mass: the probability of stopping at some stage `j < k`, where
`D j x` is the probability of stopping at stage `j` from the value `x`. -/
def failMass (F : ℕ → Finset ℝ) (x₀ : ℝ) (K : ℕ → ℝ → ℝ → ℝ) (D : ℕ → ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range k, ∑ q ∈ paths F x₀ j, weight K j q * D j (q j)

/-- **Conservation of probability**: stopping mass plus path weight is one. -/
theorem failMass_add_mass (hx₀ : x₀ ∈ F 0) {D : ℕ → ℝ → ℝ}
    (hKD : ∀ j x, x ∈ F j → ∑ y ∈ F (j + 1), K j x y + D j x = 1) (k : ℕ) :
    failMass F x₀ K D k + mass F x₀ K k = 1 := by
  induction k with
  | zero => simp [failMass, mass_zero]
  | succ k ih =>
    rw [failMass, sum_range_succ, ← failMass, mass_succ]
    have : ∑ q ∈ paths F x₀ k, weight K k q * ∑ y ∈ F (k + 1), K k (q k) y
        = mass F x₀ K k - ∑ q ∈ paths F x₀ k, weight K k q * D k (q k) := by
      rw [mass, ← sum_sub_distrib]
      refine sum_congr rfl fun q hq => ?_
      have := hKD k (q k) (mem_alphabet hx₀ hq le_rfl)
      rw [show ∑ y ∈ F (k + 1), K k (q k) y = 1 - D k (q k) by linarith]
      ring
    rw [this]
    linarith

/-- **Union bound for the stopping mass.** -/
theorem failMass_le (hx₀ : x₀ ∈ F 0) (hK0 : ∀ j x y, 0 ≤ K j x y)
    (hK1 : ∀ j x, x ∈ F j → ∑ y ∈ F (j + 1), K j x y ≤ 1) {D : ℕ → ℝ → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (k : ℕ) (hD : ∀ j < k, ∀ x ∈ F j, D j x ≤ η) :
    failMass F x₀ K D k ≤ k * η := by
  unfold failMass
  calc ∑ j ∈ range k, ∑ q ∈ paths F x₀ j, weight K j q * D j (q j)
      ≤ ∑ j ∈ range k, ∑ q ∈ paths F x₀ j, weight K j q * η := by
        refine sum_le_sum fun j hj => sum_le_sum fun q hq => ?_
        exact mul_le_mul_of_nonneg_left
          (hD j (mem_range.1 hj) (q j) (mem_alphabet hx₀ hq le_rfl)) (weight_nonneg hK0 j q)
    _ = ∑ j ∈ range k, mass F x₀ K j * η := by
        refine sum_congr rfl fun j _ => ?_
        rw [mass, sum_mul]
    _ ≤ ∑ _j ∈ range k, 1 * η :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (mass_le_one hx₀ hK0 hK1 j) hη
    _ = k * η := by simp

/-! ### The capped accept/reject trial loop -/

/-- The law of the capped accept/reject loop on `Option ℝ` (`none`: the cap is exhausted).
With `R + 1` proposals left: propose `y ∈ G` with probability `p y`, accept it with probability
`a y`; otherwise (probability `1 − ∑_y p y a y`) continue with `R` proposals left. -/
def retryLaw (G : Finset ℝ) (p a : ℝ → ℝ) : ℕ → Option ℝ → ℝ
  | 0, o => if o = none then 1 else 0
  | R + 1, o =>
      (match o with
        | none => 0
        | some y => if y ∈ G then p y * a y else 0)
      + (1 - ∑ y ∈ G, p y * a y) * retryLaw G p a R o

variable {G : Finset ℝ} {p a : ℝ → ℝ}

/-- The cap is exhausted with probability `(1 − Z)^R`. -/
theorem retryLaw_none (R : ℕ) :
    retryLaw G p a R none = (1 - ∑ y ∈ G, p y * a y) ^ R := by
  induction R with
  | zero => simp [retryLaw]
  | succ R ih => simp only [retryLaw, ih, zero_add, pow_succ]; ring

/-- The value `y ∈ G` is the accepted proposal with probability `p y a y ∑_{i<R} (1 − Z)^i`. -/
theorem retryLaw_some (R : ℕ) (y : ℝ) :
    retryLaw G p a R (some y)
      = (if y ∈ G then p y * a y else 0) * ∑ i ∈ range R, (1 - ∑ z ∈ G, p z * a z) ^ i := by
  induction R with
  | zero => simp [retryLaw]
  | succ R ih =>
    simp only [retryLaw, ih]
    rw [geom_sum_succ]
    ring

/-- The capped loop is a probability law: accepted mass plus exhaustion mass is one. -/
theorem retryLaw_total (R : ℕ) :
    ∑ y ∈ G, retryLaw G p a R (some y) + retryLaw G p a R none = 1 := by
  simp_rw [retryLaw_some, retryLaw_none]
  rw [← sum_mul]
  rw [sum_congr rfl (fun y hy => if_pos hy)]
  set Z := ∑ y ∈ G, p y * a y
  have := mul_neg_geom_sum (1 - Z) R
  rw [show 1 - (1 - Z) = Z by ring] at this
  linarith

theorem retryLaw_some_nonneg (hp : ∀ y, 0 ≤ p y) (ha : ∀ y, 0 ≤ a y)
    (hZ : ∑ y ∈ G, p y * a y ≤ 1) (R : ℕ) (y : ℝ) : 0 ≤ retryLaw G p a R (some y) := by
  rw [retryLaw_some]
  refine mul_nonneg ?_ (sum_nonneg fun i _ => pow_nonneg (by linarith) _)
  split_ifs
  · exact mul_nonneg (hp y) (ha y)
  · exact le_rfl

/-- Each accepted value has probability at most the accepted row `p y a y / Z`. -/
theorem retryLaw_some_le (hp : ∀ y, 0 ≤ p y) (ha : ∀ y, 0 ≤ a y)
    (hZ0 : 0 < ∑ y ∈ G, p y * a y) (hZ : ∑ y ∈ G, p y * a y ≤ 1) (R : ℕ) {y : ℝ} (hy : y ∈ G) :
    retryLaw G p a R (some y) ≤ p y * a y / ∑ z ∈ G, p z * a z := by
  rw [retryLaw_some, if_pos hy]
  set Z := ∑ z ∈ G, p z * a z
  have hgeom := mul_neg_geom_sum (1 - Z) R
  rw [show 1 - (1 - Z) = Z by ring] at hgeom
  have hpow : 0 ≤ (1 - Z) ^ R := pow_nonneg (by linarith) _
  have hS : ∑ i ∈ range R, (1 - Z) ^ i ≤ 1 / Z := by
    rw [le_div_iff₀ hZ0]; linarith
  calc p y * a y * ∑ i ∈ range R, (1 - Z) ^ i ≤ p y * a y * (1 / Z) :=
        mul_le_mul_of_nonneg_left hS (mul_nonneg (hp y) (ha y))
    _ = p y * a y / Z := by ring

/-- `(1 − Z)^R ≤ exp(−Z_* R)` when `Z_* ≤ Z ≤ 1`. -/
theorem retryLaw_none_le_exp {Zlow : ℝ} (hZl : Zlow ≤ ∑ y ∈ G, p y * a y)
    (hZ : ∑ y ∈ G, p y * a y ≤ 1) (R : ℕ) :
    retryLaw G p a R none ≤ Real.exp (-(Zlow * R)) := by
  rw [retryLaw_none]
  set Z := ∑ y ∈ G, p y * a y
  calc (1 - Z) ^ R ≤ Real.exp (-Z) ^ R :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg Z) R
    _ = Real.exp (-(Z * R)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(Zlow * R)) := by
        apply Real.exp_le_exp.2
        have : (0:ℝ) ≤ R := Nat.cast_nonneg R
        nlinarith

/-! ### The Gibbs mean bound -/

/-- **Gibbs mean bound.**  On a finite nonempty grid, the mean cost under the normalized
Boltzmann row `exp(−c/ε)/∑ exp(−c/ε)` is at most the normalized soft minimum. -/
theorem gibbs_mean_le_softMin {ε : ℝ} (hε : 0 < ε) (hG : G.Nonempty) (c : ℝ → ℝ) :
    ∑ y ∈ G, Real.exp (-c y / ε) / (∑ z ∈ G, Real.exp (-c z / ε)) * c y
      ≤ FiniteLaplace.softMin ε G c := by
  set S := ∑ z ∈ G, Real.exp (-c z / ε) with hSdef
  have hS : 0 < S := sum_pos (fun z _ => Real.exp_pos _) hG
  set n : ℝ := (G.card : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hG.card_pos
  set Q : ℝ → ℝ := fun y => Real.exp (-c y / ε) / S with hQ
  have hQpos : ∀ y, 0 < Q y := fun y => div_pos (Real.exp_pos _) hS
  have hQsum : ∑ y ∈ G, Q y = 1 := by
    rw [hQ]; simp only; rw [← sum_div, div_self hS.ne']
  -- `c y = -ε (log (Q y) + log S)`
  have hc : ∀ y, c y = -ε * (Real.log (Q y) + Real.log S) := by
    intro y
    rw [← Real.log_mul (hQpos y).ne' hS.ne', hQ]
    simp only
    rw [div_mul_cancel₀ _ hS.ne', Real.log_exp]
    field_simp
  -- Gibbs: `∑ Q log (n Q) ≥ 0`
  have hgibbs : 0 ≤ ∑ y ∈ G, Q y * Real.log (n * Q y) := by
    have h1 : ∀ y ∈ G, Q y - 1 / n ≤ Q y * Real.log (n * Q y) := by
      intro y _
      have hx : 0 < n * Q y := mul_pos hn0 (hQpos y)
      have := Real.one_sub_inv_le_log_of_pos hx
      have hQy := hQpos y
      calc Q y - 1 / n = Q y * (1 - (n * Q y)⁻¹) := by field_simp
        _ ≤ Q y * Real.log (n * Q y) := mul_le_mul_of_nonneg_left this hQy.le
    have h2 := sum_le_sum h1
    rw [sum_sub_distrib, hQsum, sum_const, nsmul_eq_mul, ← hn, mul_one_div_cancel hn0.ne',
      sub_self] at h2
    exact h2
  have hlogn : ∀ y, Real.log (n * Q y) = Real.log n + Real.log (Q y) := fun y =>
    Real.log_mul hn0.ne' (hQpos y).ne'
  have hmean : ∑ y ∈ G, Q y * c y
      = -ε * ∑ y ∈ G, Q y * Real.log (n * Q y) + ε * Real.log n - ε * Real.log S := by
    simp_rw [hc, hlogn]
    have : ∀ y ∈ G, Q y * (-ε * (Real.log (Q y) + Real.log S))
        = -ε * (Q y * (Real.log n + Real.log (Q y))) + ε * Real.log n * Q y
          - ε * Real.log S * Q y := fun y _ => by ring
    rw [sum_congr rfl this, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
      hQsum]
    ring
  have hsoft : FiniteLaplace.softMin ε G c = ε * Real.log n - ε * Real.log S := by
    unfold FiniteLaplace.softMin
    rw [← hSdef, Real.log_mul (inv_pos.2 hn0).ne' hS.ne', Real.log_inv]
    ring
  have hrw : ∑ y ∈ G, Real.exp (-c y / ε) / S * c y = ∑ y ∈ G, Q y * c y := rfl
  rw [hrw, hmean, hsoft]
  have := mul_nonneg hε.le hgibbs
  linarith

/-- **Entropy–energy bound for one row** (`lem:supp-entropy-energy`, one stage): the mean cost
under the Boltzmann row is at most `c y₀ + ε log #G` for every `y₀ ∈ G`. -/
theorem gibbs_mean_le {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℝ) {y₀ : ℝ} (hy₀ : y₀ ∈ G) :
    ∑ y ∈ G, Real.exp (-c y / ε) / (∑ z ∈ G, Real.exp (-c z / ε)) * c y
      ≤ c y₀ + ε * Real.log G.card :=
  (gibbs_mean_le_softMin hε ⟨y₀, hy₀⟩ c).trans (FiniteLaplace.softMin_le hε c hy₀)

end

end RenewalGeometry.FiniteMarkovPaths
