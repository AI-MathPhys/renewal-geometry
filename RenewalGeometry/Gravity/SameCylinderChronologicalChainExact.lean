/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ChronologicalThomsonExact

/-!
# The corrected chronological chain of the same-cylinder compiler
  (`thm:main-same-cylinder-einstein` clause (ii), `eq:main-same-cylinder-probability`,
  `eq:supp-same-cylinder-chain-cost`, `eq:supp-same-cylinder-badprob`;
  emergent-spacetime manuscript, Appendix `supp:same-cylinder`)

**Finite chronological chains.**  Stage spaces are finite types `S j` (`j : ℕ`).
`Path S J` is the finite type of chronological paths `(x₀, x₁, …, x_J)`, realised as the
left-nested product `S 0 × S 1 × ⋯ × S J` (`Path.init`, `Path.cur`, `Path.last`,
`sum_path_succ`).  Given stage marginals `ν j` and stage couplings `π j` on `S j × S (j+1)`,
the corrected rows are `K_j(y | x) = π_j(x,y) / ν_j(x)` (`corrKernel`) and the path law is
`ν₀(x₀) ∏_j K_j(x_j, x_{j+1})` (`chainLaw`).  If the marginals are faithful and each `π j` is a
coupling of `ν j` and `ν (j+1)` (`j < N`), then for `J ≤ N`
* `marginal_eq`: `X_J ∼ ν_J`;
* `pairLaw_eq`: the pair `(X_j, X_{j+1})` has law `π_j` for every `j < J` (`pairObs`);
* `chainLaw_total`, `chainLaw_nonneg'`: the path law is a probability law;
* `expectedCost_eq`: `𝔼 ∑_j c_j(X_j, X_{j+1}) = ∑_j 𝔼_{π_j} c_j` (`pathCost`);
* `markov_path`: Markov's inequality for the finite path law.

**The Thomson-corrected chain.**  `ChronoChain S` packages the hypotheses of the theorem:
faithful prescribed marginals `ν_j`, stochastic common-action comparators `Q_j`, and at every
stage the Thomson correction exists (`d_j = ν_{j+1} - ν_j Q_j ∈ Ran 𝓛_j`) with leverage at most
`1/2`.  Its stage couplings are `π_j^T = R_j + h_j^*` with `u_j = 𝓛_j^† d_j`
(`corrCoupling`, via `ChronologicalThomson.thomsonPinv`), and its path law uses the corrected
rows `K_j^T = π_j^T / ν_j`.  The occurrence energy is `𝓔_occ,j = ⟨d_j, 𝓛_j^† d_j⟩`
(`occEnergy`).
* `ChronoChain.expectedCost_le`: `eq:supp-same-cylinder-chain-cost`,
  `𝔼 C ≤ ∑_j (m_j + √(𝓔_occ,j 𝒱_j))` (by `SameCylinderTransfer.thomson_transfer`);
* `ChronoChain.clause_ii`: under the writer scale `eq:main-same-cylinder-writer-scale`
  (`WriterScale`), `𝔼 C_h ≤ (M₀ + √(M₁V₀)) T h⁴` and
  `Pr{C_h > h²} ≤ (M₀ + √(M₁V₀)) T h²` (`eq:supp-same-cylinder-badprob`, hence
  `eq:main-same-cylinder-probability`);
* `eventually_successful_ae`: along any common coupling of the cutoff chains (random paths
  `X n` on one probability space with the prescribed path laws, no independence assumed),
  if `∑ h_n² < ∞` then almost surely `C_{h_n} ≤ h_n²` for all large `n` (first Borel–Cantelli).

Scoped hypotheses: the constants satisfy `M₀ ≥ 0` (needed only to pass from `∑_j τ_j ≤ T` to
the bound with `T`), the durations `τ_j` are nonnegative, and `h > 0`.
-/

universe u

namespace RenewalGeometry
namespace SameCylinderChronologicalChain

open Finset MeasureTheory Filter
open SameCylinderTransfer ChronologicalThomson

noncomputable section

/-! ## Finite chronological paths -/

/-- Chronological paths `(x₀, …, x_J)` through the stage spaces, as the left-nested product
`S 0 × S 1 × ⋯ × S J`. -/
def Path (S : ℕ → Type u) : ℕ → Type u
  | 0 => S 0
  | J + 1 => Path S J × S (J + 1)

variable {S : ℕ → Type u}

/-- The path with its last state removed. -/
def Path.init {J : ℕ} (p : Path S (J + 1)) : Path S J := (p : Path S J × S (J + 1)).1
/-- The last state of a path of positive length. -/
def Path.cur {J : ℕ} (p : Path S (J + 1)) : S (J + 1) := (p : Path S J × S (J + 1)).2
/-- Append a state to a path. -/
def Path.snoc {J : ℕ} (p : Path S J) (y : S (J + 1)) : Path S (J + 1) :=
  ((p, y) : Path S J × S (J + 1))

/-- The final state `x_J` of a path. -/
def Path.last : {J : ℕ} → Path S J → S J
  | 0, x => x
  | _ + 1, p => p.cur

@[simp] theorem Path.init_snoc {J} (p : Path S J) (y : S (J+1)) : (Path.snoc p y).init = p := rfl
@[simp] theorem Path.cur_snoc {J} (p : Path S J) (y : S (J+1)) : (Path.snoc p y).cur = y := rfl
@[simp] theorem Path.last_succ {J} (p : Path S (J+1)) : p.last = p.cur := rfl

/-- Paths through finite stage spaces form a finite type. -/
instance Path.instFintype [∀ j, Fintype (S j)] : ∀ J, Fintype (Path S J)
  | 0 => inferInstanceAs (Fintype (S 0))
  | J + 1 => letI := Path.instFintype J; inferInstanceAs (Fintype (Path S J × S (J + 1)))

/-- One-stage decomposition of a path sum. -/
theorem sum_path_succ [∀ j, Fintype (S j)] {J : ℕ} (f : Path S (J + 1) → ℝ) :
    ∑ p, f p = ∑ p : Path S J, ∑ y : S (J + 1), f (Path.snoc p y) :=
  Fintype.sum_prod_type (f := (f : Path S J × S (J + 1) → ℝ))

/-- The pair observable `f(X_j, X_{j+1})` on paths of length `J` (zero if `J ≤ j`). -/
def pairObs (j : ℕ) (f : S j → S (j + 1) → ℝ) : ∀ J, Path S J → ℝ
  | 0, _ => 0
  | J + 1, p => if h : J = j then (h ▸ f) p.init.last p.cur else pairObs j f J p.init

theorem pairObs_self (j : ℕ) (f : S j → S (j + 1) → ℝ) (p : Path S (j+1)) :
    pairObs j f (j+1) p = f p.init.last p.cur := by
  simp [pairObs]

theorem pairObs_of_ne (j J : ℕ) (f : S j → S (j + 1) → ℝ) (p : Path S (J+1)) (h : J ≠ j) :
    pairObs j f (J+1) p = pairObs j f J p.init := by
  simp [pairObs, h]


section Chain
variable [∀ j, Fintype (S j)]

/-- The Markov path law `ν₀(x₀) ∏_{j<J} K_j(x_j, x_{j+1})`. -/
def pathLaw (ν0 : S 0 → ℝ) (K : ∀ j, S j → S (j + 1) → ℝ) : ∀ J, Path S J → ℝ
  | 0, x => ν0 x
  | J + 1, p => pathLaw ν0 K J p.init * K J p.init.last p.cur

/-- The corrected rows `K_j(y | x) = π_j(x,y) / ν_j(x)`. -/
def corrKernel (ν : ∀ j, S j → ℝ) (π : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) (x : S j)
    (y : S (j + 1)) : ℝ := π j x y / ν j x

/-- The path law of the chain with corrected rows `π_j / ν_j` started at `ν₀`. -/
def chainLaw (ν : ∀ j, S j → ℝ) (π : ∀ j, S j → S (j + 1) → ℝ) : ∀ J, Path S J → ℝ :=
  pathLaw (ν 0) (corrKernel ν π)

/-- The additive path cost `C = ∑_{j<J} c_j(X_j, X_{j+1})`. -/
def pathCost (c : ∀ j, S j → S (j + 1) → ℝ) : ∀ J, Path S J → ℝ
  | 0, _ => 0
  | J + 1, p => pathCost c J p.init + c J p.init.last p.cur

variable (ν : ∀ j, S j → ℝ) (π : ∀ j, S j → S (j + 1) → ℝ) {N : ℕ}

omit [∀ j, Fintype (S j)] in
/-- `C = ∑_{j<J} c_j(X_j, X_{j+1})` written with the pair observables. -/
theorem pathCost_eq_sum_pairObs (c : ∀ j, S j → S (j + 1) → ℝ) :
    ∀ J (p : Path S J), pathCost c J p = ∑ j ∈ range J, pairObs j (c j) J p
  | 0, _ => by simp [pathCost]
  | J + 1, p => by
    rw [Finset.sum_range_succ, pairObs_self]
    have : ∀ j ∈ range J, pairObs j (c j) (J + 1) p = pairObs j (c j) J p.init :=
      fun j hj => pairObs_of_ne j J (c j) p (by have := Finset.mem_range.1 hj; omega)
    rw [Finset.sum_congr rfl this, ← pathCost_eq_sum_pairObs c J p.init]
    rfl

omit [∀ j, Fintype (S j)] in
theorem chainLaw_succ {J : ℕ} (p : Path S J) (y : S (J+1)) :
    chainLaw ν π (J+1) (Path.snoc p y) = chainLaw ν π J p * (π J p.last y / ν J p.last) := rfl

variable (hν : ∀ j ≤ N, ∀ x, 0 < ν j x) (hπ : ∀ j < N, ∀ x y, 0 ≤ π j x y)
  (hsrc : ∀ j < N, ∀ x, ∑ y, π j x y = ν j x)
  (htgt : ∀ j < N, ∀ y, ∑ x, π j x y = ν (j + 1) y)
include hν hπ hsrc htgt

omit [∀ j, Fintype (S j)] hπ hsrc htgt in
/-- The path law is nonnegative. -/
theorem chainLaw_nonneg' (hπ : ∀ j < N, ∀ x y, 0 ≤ π j x y) :
    ∀ J ≤ N, ∀ p, 0 ≤ chainLaw ν π J p
  | 0, _, p => (hν 0 (Nat.zero_le _) p).le
  | J + 1, hJ, p => by
    have := chainLaw_nonneg' hπ J (by omega) p.init
    exact mul_nonneg this (div_nonneg (hπ J (by omega) _ _) (hν J (by omega) _).le)

omit hπ hsrc in
/-- The chain has the prescribed marginal at the last stage: `X_J ∼ ν_J`. -/
theorem marginal_eq : ∀ J ≤ N, ∀ f : S J → ℝ,
    ∑ p, chainLaw ν π J p * f p.last = ∑ x, ν J x * f x
  | 0, _, f => rfl
  | J + 1, hJ, f => by
    rw [sum_path_succ]
    simp only [chainLaw_succ, Path.last_succ, Path.cur_snoc]
    have hswap : ∑ p : Path S J, ∑ y : S (J+1),
          chainLaw ν π J p * (π J p.last y / ν J p.last) * f y
        = ∑ y : S (J+1), (∑ p : Path S J, chainLaw ν π J p * (fun x => π J x y / ν J x) p.last)
            * f y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_mul]
    rw [hswap]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [marginal_eq J (by omega) (fun x => π J x y / ν J x)]
    have : ∑ x, ν J x * (π J x y / ν J x) = ν (J+1) y := by
      rw [← htgt J (by omega) y]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp [(hν J (by omega) x).ne']
    rw [this]


omit hπ htgt in
/-- Extending the path by one corrected step does not change the law of the prefix. -/
theorem extend_eq {J : ℕ} (hJ : J + 1 ≤ N) (g : Path S J → ℝ) :
    ∑ p : Path S (J + 1), chainLaw ν π (J + 1) p * g p.init = ∑ p, chainLaw ν π J p * g p := by
  rw [sum_path_succ]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [chainLaw_succ, Path.init_snoc]
  have hrow : ∑ y, π J p.last y / ν J p.last = 1 := by
    rw [← Finset.sum_div, hsrc J (by omega), div_self (hν J (by omega) _).ne']
  calc ∑ y, chainLaw ν π J p * (π J p.last y / ν J p.last) * g p
      = chainLaw ν π J p * g p * ∑ y, π J p.last y / ν J p.last := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = chainLaw ν π J p * g p := by rw [hrow, mul_one]

omit hπ in
/-- The pair `(X_j, X_{j+1})` has law `π_j` (`j < J ≤ N`). -/
theorem pairLaw_eq (j : ℕ) (f : S j → S (j + 1) → ℝ) :
    ∀ J ≤ N, j < J → ∑ p, chainLaw ν π J p * pairObs j f J p = ∑ x, ∑ y, π j x y * f x y
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | J + 1, hJ, hj => by
    by_cases hJj : J = j
    · subst hJj
      rw [sum_path_succ]
      simp only [pairObs_self, Path.init_snoc, Path.cur_snoc, chainLaw_succ]
      have : ∀ p : Path S J, ∑ y, chainLaw ν π J p * (π J p.last y / ν J p.last) * f p.last y
          = chainLaw ν π J p * (fun x => ∑ y, π J x y / ν J x * f x y) p.last := by
        intro p; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      rw [Finset.sum_congr rfl fun p _ => this p,
        marginal_eq ν π hν htgt J (by omega) (fun x => ∑ y, π J x y / ν J x * f x y)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp [(hν J (by omega) x).ne']
    · have hjJ : j < J := by omega
      have h1 : ∀ p : Path S (J + 1), pairObs j f (J + 1) p = pairObs j f J p.init :=
        fun p => pairObs_of_ne j J f p hJj
      simp only [h1]
      rw [extend_eq ν π hν hsrc hJ (pairObs j f J)]
      exact pairLaw_eq j f J (by omega) hjJ

omit hπ in
/-- `𝔼 ∑_j c_j(X_j, X_{j+1}) = ∑_j 𝔼_{π_j} c_j`. -/
theorem expectedCost_eq (c : ∀ j, S j → S (j + 1) → ℝ) {J : ℕ} (hJ : J ≤ N) :
    ∑ p, chainLaw ν π J p * pathCost c J p = ∑ j ∈ range J, ∑ x, ∑ y, π j x y * c j x y := by
  simp only [pathCost_eq_sum_pairObs, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj =>
    pairLaw_eq ν π hν hsrc htgt j (c j) J hJ (Finset.mem_range.1 hj)

omit hπ in
/-- The path law is a probability law. -/
theorem chainLaw_total (h1 : ∑ x, ν 0 x = 1) {J : ℕ} (hJ : J ≤ N) :
    ∑ p, chainLaw ν π J p = 1 := by
  have key : ∀ J ≤ N, ∑ x, ν J x = 1 := by
    intro J hJ
    induction J with
    | zero => exact h1
    | succ J ih =>
      rw [← ih (by omega)]
      simp_rw [← htgt J (by omega)]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => hsrc J (by omega) x
  have := marginal_eq ν π hν htgt J hJ (fun _ => 1)
  simp only [mul_one] at this
  rw [this, key J hJ]

omit hsrc htgt in
/-- Markov's inequality for the finite path law: `Pr{C > a} ≤ 𝔼 C / a`. -/
theorem markov_path {J : ℕ} (hJ : J ≤ N) (C : Path S J → ℝ) (hC : ∀ p, 0 ≤ C p) {a : ℝ}
    (ha : 0 < a) :
    ∑ p, chainLaw ν π J p * (if a < C p then 1 else 0) ≤ (∑ p, chainLaw ν π J p * C p) / a := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun p _ => ?_
  have hl := chainLaw_nonneg' ν π hν hπ J hJ p
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hl
  split_ifs with h
  · rw [le_div_iff₀ ha]; linarith
  · exact div_nonneg (hC p) ha.le

end Chain
