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
open SameCylinderTransfer ChronologicalThomson Matrix

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
/-- A pair observable of a nonnegative function is nonnegative. -/
theorem pairObs_nonneg (j : ℕ) (f : S j → S (j + 1) → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    ∀ J (p : Path S J), 0 ≤ pairObs j f J p
  | 0, _ => le_rfl
  | J + 1, p => by
    by_cases h : J = j
    · subst h; rw [pairObs_self]; exact hf _ _
    · rw [pairObs_of_ne j J f p h]; exact pairObs_nonneg j f hf J p.init

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

/-! ## The Thomson-corrected chronological chain -/

section Thomson

variable {S : ℕ → Type u} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]

/-- The stage defect `d_j = ν_{j+1} - ρ_{j+1}`, `ρ_{j+1} = ν_j Q_j`
(`eq:main-same-cylinder-reference`). -/
def stageDefect (ν : ∀ j, S j → ℝ) (Q : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) : S (j + 1) → ℝ :=
  fun y => ν (j + 1) y - targetMarginal (ν j) (Q j) y

/-- The Thomson potential `u_j = 𝓛_j^† d_j` (`eq:main-thomson-correction`). -/
def stagePot (ν : ∀ j, S j → ℝ) (Q : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) : S (j + 1) → ℝ :=
  thomsonPinv (ν j) (Q j) *ᵥ stageDefect ν Q j

/-- The corrected coupling `π_j^T = R_j + h_j^*`, `R_j = ν_j Q_j`,
`h_j^*(x,y) = R_j(x,y)(u_j(y) - (Q_j u_j)(x))` (`eq:main-thomson-correction`). -/
def corrCoupling (ν : ∀ j, S j → ℝ) (Q : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) :
    S j → S (j + 1) → ℝ :=
  fun x y => refCoupling (ν j) (Q j) x y + thomsonCorrection (ν j) (Q j) (stagePot ν Q j) x y

/-- The occurrence energy `𝓔_occ,j = ⟨d_j, 𝓛_j^† d_j⟩` (`eq:main-occurrence-energy`). -/
def occEnergy (ν : ∀ j, S j → ℝ) (Q : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) : ℝ :=
  stageDefect ν Q j ⬝ᵥ stagePot ν Q j

/-- The data of the corrected chronological process at one cutoff, with the hypotheses of
`thm:main-same-cylinder-einstein` that concern it: `J` chronological stages, faithful prescribed
marginals `ν_j` (`ν_0` a probability law), stochastic common-action comparators `Q_j`, and at
every stage the Thomson correction exists (`d_j ∈ Ran 𝓛_j`) on the comparator support with
leverage at most `1/2`. -/
structure ChronoChain (S : ℕ → Type u) [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)] where
  /-- Number of chronological stages. -/
  J : ℕ
  /-- Prescribed chronological marginals. -/
  ν : ∀ j, S j → ℝ
  /-- Common-action comparators `Q_j(y | x)`. -/
  Q : ∀ j, S j → S (j + 1) → ℝ
  ν_pos : ∀ j ≤ J, ∀ x, 0 < ν j x
  ν_total : ∑ x, ν 0 x = 1
  Q_nonneg : ∀ j < J, ∀ x y, 0 ≤ Q j x y
  Q_row : ∀ j < J, ∀ x, ∑ y, Q j x y = 1
  defect_mem : ∀ j < J, stageDefect ν Q j ∈ Set.range (thomsonMatrix (ν j) (Q j)).mulVec
  leverage : ∀ j < J, ∀ x y, Q j x y ≠ 0 →
    |stagePot ν Q j y - rowAvg (Q j) (stagePot ν Q j) x| ≤ 1 / 2

namespace ChronoChain

variable (ch : ChronoChain S)

/-- The path law of the corrected process (rows `K_j^T = π_j^T / ν_j`). -/
def law : Path S ch.J → ℝ := chainLaw ch.ν (corrCoupling ch.ν ch.Q) ch.J

/-- The reference mean `m_j = 𝔼_{R_j} c_j`. -/
def refMean (c : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ x, ∑ y, refCoupling (ch.ν j) (ch.Q j) x y * c j x y

/-- The reference variance `𝒱_j = 𝒱_{R_j}(c_j)` (`eq:supp-same-cylinder-variance`). -/
def refVar (c : ∀ j, S j → S (j + 1) → ℝ) (j : ℕ) : ℝ :=
  cylVariance (refCoupling (ch.ν j) (ch.Q j)) (ch.Q j) (c j)

/-- `u_j = 𝓛_j^† d_j` solves `𝓛_j u_j = d_j`. -/
theorem pot_solves {j : ℕ} (hj : j < ch.J) :
    thomsonMatrix (ch.ν j) (ch.Q j) *ᵥ stagePot ch.ν ch.Q j = stageDefect ch.ν ch.Q j :=
  pinv_solves (ch.ν j) (ch.Q j) (thomsonPinv_isPenroseInverse _ _) (ch.defect_mem j hj)

/-- Clause (i) for the stage couplings: `π_j^T ≥ 0` with marginals `ν_j`, `ν_{j+1}`. -/
theorem corr_spec {j : ℕ} (hj : j < ch.J) :
    (∀ x y, 0 ≤ corrCoupling ch.ν ch.Q j x y) ∧
    (∀ x, ∑ y, corrCoupling ch.ν ch.Q j x y = ch.ν j x) ∧
    (∀ y, ∑ x, corrCoupling ch.ν ch.Q j x y = ch.ν (j + 1) y) :=
  thomson_leverage (ch.ν j) (ch.Q j) (ch.ν_pos j hj.le) (ch.Q_nonneg j hj) (ch.Q_row j hj)
    (ch.ν (j + 1)) (stagePot ch.ν ch.Q j) (ch.pot_solves hj) (ch.leverage j hj)

/-- The corrected path law is nonnegative. -/
theorem law_nonneg (p : Path S ch.J) : 0 ≤ ch.law p :=
  chainLaw_nonneg' ch.ν _ ch.ν_pos (fun _ hj => (ch.corr_spec hj).1) ch.J le_rfl p

/-- The corrected path law is a probability law. -/
theorem law_total : ∑ p, ch.law p = 1 :=
  chainLaw_total ch.ν _ ch.ν_pos (fun _ hj => (ch.corr_spec hj).2.1)
    (fun _ hj => (ch.corr_spec hj).2.2) ch.ν_total le_rfl

/-- The corrected process has the prescribed pair laws: `(X_j, X_{j+1}) ∼ π_j^T`; in particular
its chronological marginals are the prescribed `ν_j`. -/
theorem pair_law (j : ℕ) (hj : j < ch.J) (f : S j → S (j + 1) → ℝ) :
    ∑ p, ch.law p * pairObs j f ch.J p = ∑ x, ∑ y, corrCoupling ch.ν ch.Q j x y * f x y :=
  pairLaw_eq ch.ν _ ch.ν_pos (fun _ hj => (ch.corr_spec hj).2.1)
    (fun _ hj => (ch.corr_spec hj).2.2) j f ch.J le_rfl hj

/-- `occEnergy ≥ 0`: it is the squared `R⁻¹`-norm of the Thomson correction. -/
theorem occEnergy_nonneg {j : ℕ} (hj : j < ch.J) : 0 ≤ occEnergy ch.ν ch.Q j := by
  obtain ⟨-, -, -, hE⟩ := thomson_min_norm (ch.ν j) (ch.Q j) (ch.ν_pos j hj.le)
    (ch.Q_nonneg j hj) (ch.Q_row j hj) (thomsonPinv_isPenroseInverse _ _) (ch.defect_mem j hj)
  have : occEnergy ch.ν ch.Q j
      = invWeightNormSq (refCoupling (ch.ν j) (ch.Q j))
          (thomsonCorrection (ch.ν j) (ch.Q j) (stagePot ch.ν ch.Q j)) := hE.symm
  rw [this]
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg (ch.ν_pos j hj.le x).le (ch.Q_nonneg j hj x y))

/-- One stage of `eq:supp-same-cylinder-chain-cost`:
`𝔼_{π_j^T} c_j ≤ m_j + √(𝓔_occ,j 𝒱_j)`. -/
theorem stage_cost_le (c : ∀ j, S j → S (j + 1) → ℝ) {j : ℕ} (hj : j < ch.J) :
    ∑ x, ∑ y, corrCoupling ch.ν ch.Q j x y * c j x y
      ≤ ch.refMean c j + Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j) := by
  have hu : ∀ y, thomsonOperator (ch.ν j) (ch.Q j) (stagePot ch.ν ch.Q j) y
      = stageDefect ch.ν ch.Q j y := by
    intro y
    rw [← thomsonMatrix_mulVec, ch.pot_solves hj]
  have ht := thomson_transfer (ch.ν j) (ch.Q j) (fun x => (ch.ν_pos j hj.le x).le)
    (ch.Q_nonneg j hj) (ch.Q_row j hj) _ _ hu (c j)
  have := (abs_le.1 ht).2
  unfold refMean refVar occEnergy
  simp only [corrCoupling]
  rw [dotProduct]
  linarith

/-- `eq:supp-same-cylinder-chain-cost`: for the corrected chronological process,
`𝔼 ∑_j c_j(X_j, X_{j+1}) ≤ ∑_j (m_j + √(𝓔_occ,j 𝒱_j))`. -/
theorem expectedCost_le (c : ∀ j, S j → S (j + 1) → ℝ) :
    ∑ p, ch.law p * pathCost c ch.J p
      ≤ ∑ j ∈ range ch.J,
          (ch.refMean c j + Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j)) := by
  unfold law
  rw [expectedCost_eq ch.ν _ ch.ν_pos (fun _ hj => (ch.corr_spec hj).2.1)
    (fun _ hj => (ch.corr_spec hj).2.2) c le_rfl]
  exact Finset.sum_le_sum fun j hj => ch.stage_cost_le c (Finset.mem_range.1 hj)

/-- The failure probability `Pr{C > a}` of the corrected process. -/
def failProb (c : ∀ j, S j → S (j + 1) → ℝ) (a : ℝ) : ℝ :=
  ∑ p, ch.law p * (if a < pathCost c ch.J p then 1 else 0)

end ChronoChain

/-- The writer scale `eq:main-same-cylinder-writer-scale` at cutoff `h`, with the standing
conditions `c_{h,j} ≥ 0` and `τ_{h,j} ≥ 0`. -/
structure WriterScale (ch : ChronoChain S) (c : ∀ j, S j → S (j + 1) → ℝ) (τ : ℕ → ℝ)
    (h M₀ M₁ V₀ T : ℝ) : Prop where
  cost_nonneg : ∀ j < ch.J, ∀ x y, 0 ≤ c j x y
  dur_nonneg : ∀ j < ch.J, 0 ≤ τ j
  mean_le : ∀ j < ch.J, ch.refMean c j ≤ M₀ * τ j * h ^ 4
  occ_le : ∀ j < ch.J, occEnergy ch.ν ch.Q j ≤ M₁ * τ j * h ^ 4
  var_le : ∀ j < ch.J, ch.refVar c j ≤ V₀ * τ j * h ^ 4
  dur_total : ∑ j ∈ range ch.J, τ j ≤ T

namespace ChronoChain

variable (ch : ChronoChain S)

/-- The reference variance is nonnegative. -/
theorem refVar_nonneg (c : ∀ j, S j → S (j + 1) → ℝ) {j : ℕ} (hj : j < ch.J) :
    0 ≤ ch.refVar c j :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (ch.ν_pos j hj.le x).le (ch.Q_nonneg j hj x y)) (sq_nonneg _)

/-- **`thm:main-same-cylinder-einstein`, clause (ii)** (`eq:main-same-cylinder-probability`,
`eq:supp-same-cylinder-badprob`).  For the corrected chronological process and
`C_h = ∑_j c_{h,j}(X_j, X_{j+1})`, under the writer scale,
`𝔼 C_h ≤ (M₀ + √(M₁V₀)) T h⁴` and `Pr{C_h > h²} ≤ (M₀ + √(M₁V₀)) T h²` (so `= O(h²)`). -/
theorem clause_ii (c : ∀ j, S j → S (j + 1) → ℝ) (τ : ℕ → ℝ) {h M₀ M₁ V₀ T : ℝ}
    (hh : 0 < h) (hM₀ : 0 ≤ M₀) (hs : WriterScale ch c τ h M₀ M₁ V₀ T) :
    ∑ p, ch.law p * pathCost c ch.J p ≤ (M₀ + Real.sqrt (M₁ * V₀)) * T * h ^ 4 ∧
    ch.failProb c (h ^ 2) ≤ (M₀ + Real.sqrt (M₁ * V₀)) * T * h ^ 2 := by
  set K := M₀ + Real.sqrt (M₁ * V₀) with hK
  have hK0 : 0 ≤ K := add_nonneg hM₀ (Real.sqrt_nonneg _)
  have hstage : ∀ j ∈ range ch.J,
      ch.refMean c j + Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j)
        ≤ K * (τ j * h ^ 4) := by
    intro j hj
    have hj := Finset.mem_range.1 hj
    have hτ := hs.dur_nonneg j hj
    have ht0 : 0 ≤ τ j * h ^ 4 := mul_nonneg hτ (by positivity)
    have hE0 := ch.occEnergy_nonneg hj
    have hV0 := ch.refVar_nonneg c hj
    have hEV : occEnergy ch.ν ch.Q j * ch.refVar c j ≤ (M₁ * V₀) * (τ j * h ^ 4) ^ 2 := by
      have := mul_le_mul (hs.occ_le j hj) (hs.var_le j hj) hV0 (hE0.trans (hs.occ_le j hj))
      nlinarith
    have hsq : Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j)
        ≤ Real.sqrt (M₁ * V₀) * (τ j * h ^ 4) := by
      calc Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j)
          ≤ Real.sqrt ((M₁ * V₀) * (τ j * h ^ 4) ^ 2) := Real.sqrt_le_sqrt hEV
        _ = Real.sqrt (M₁ * V₀) * (τ j * h ^ 4) := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq ht0]
    have := hs.mean_le j hj
    rw [hK]; nlinarith
  have hE : ∑ p, ch.law p * pathCost c ch.J p ≤ K * T * h ^ 4 := by
    calc ∑ p, ch.law p * pathCost c ch.J p
        ≤ ∑ j ∈ range ch.J,
            (ch.refMean c j + Real.sqrt (occEnergy ch.ν ch.Q j * ch.refVar c j)) :=
          ch.expectedCost_le c
      _ ≤ ∑ j ∈ range ch.J, K * (τ j * h ^ 4) := Finset.sum_le_sum hstage
      _ = K * (∑ j ∈ range ch.J, τ j) * h ^ 4 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
      _ ≤ K * T * h ^ 4 := by
          gcongr
          exact hs.dur_total
  refine ⟨hE, ?_⟩
  have hC : ∀ p, 0 ≤ pathCost c ch.J p := by
    intro p
    rw [pathCost_eq_sum_pairObs]
    refine Finset.sum_nonneg fun j hj => ?_
    exact pairObs_nonneg j (c j) (hs.cost_nonneg j (Finset.mem_range.1 hj)) ch.J p
  have hM := markov_path ch.ν (corrCoupling ch.ν ch.Q) ch.ν_pos
    (fun _ hj => (ch.corr_spec hj).1) le_rfl (pathCost c ch.J) hC (by positivity : 0 < h ^ 2)
  unfold failProb
  calc ∑ p, ch.law p * (if h ^ 2 < pathCost c ch.J p then 1 else 0)
      ≤ (∑ p, ch.law p * pathCost c ch.J p) / h ^ 2 := hM
    _ ≤ (K * T * h ^ 4) / h ^ 2 := by gcongr
    _ = K * T * h ^ 2 := by field_simp

end ChronoChain

end Thomson

/-! ## Borel–Cantelli along a common coupling -/

section BorelCantelli

variable {S : ℕ → ℕ → Type u} [∀ n j, Fintype (S n j)] [∀ n j, DecidableEq (S n j)]

/-- Under a coupling with the prescribed path law, the failure event has probability
`Pr{C > a}` of the finite chain (as an upper bound). -/
theorem measure_fail_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : ℕ → Type u} [∀ j, Fintype (T j)] [∀ j, DecidableEq (T j)] (ch : ChronoChain T)
    (c : ∀ j, T j → T (j + 1) → ℝ) (a : ℝ) (X : Ω → Path T ch.J)
    (hlaw : ∀ p, μ (X ⁻¹' {p}) = ENNReal.ofReal (ch.law p)) :
    μ {ω | a < pathCost c ch.J (X ω)} ≤ ENNReal.ofReal (ch.failProb c a) := by
  classical
  set F := Finset.univ.filter fun p : Path T ch.J => a < pathCost c ch.J p
  have hset : {ω | a < pathCost c ch.J (X ω)} = ⋃ p ∈ F, X ⁻¹' {p} := by
    ext ω; simp [F]
  rw [hset]
  refine (measure_biUnion_finset_le F _).trans ?_
  simp only [hlaw]
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => ch.law_nonneg p]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold ChronoChain.failProb
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp

/-- **`thm:main-same-cylinder-einstein`, final assertion** (first Borel–Cantelli).  Let the
cutoffs `h_n > 0` satisfy `∑ h_n² < ∞`, and let the corrected chronological chains at all
cutoffs obey the writer scale with common constants `M₀ ≥ 0, M₁, V₀, T`.  Along any common
coupling — random paths `X n : Ω → Path` on one measure space whose laws are the corrected path
laws; no independence between cutoffs or between stages is assumed — the successful residual
branch `C_{h_n} ≤ h_n²` occurs for all large `n`, almost surely. -/
theorem eventually_successful_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ch : ∀ n, ChronoChain (S n)) (c : ∀ n j, S n j → S n (j + 1) → ℝ) (τ : ℕ → ℕ → ℝ)
    (h : ℕ → ℝ) {M₀ M₁ V₀ T : ℝ} (hM₀ : 0 ≤ M₀) (hh : ∀ n, 0 < h n)
    (hs : ∀ n, WriterScale (ch n) (c n) (τ n) (h n) M₀ M₁ V₀ T)
    (hsum : Summable fun n => h n ^ 2)
    (X : ∀ n, Ω → Path (S n) (ch n).J)
    (hlaw : ∀ n p, μ (X n ⁻¹' {p}) = ENNReal.ofReal ((ch n).law p)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, pathCost (c n) (ch n).J (X n ω) ≤ h n ^ 2 := by
  set K := (M₀ + Real.sqrt (M₁ * V₀)) * T
  have hbound : ∀ n, μ {ω | h n ^ 2 < pathCost (c n) (ch n).J (X n ω)}
      ≤ ENNReal.ofReal (K * h n ^ 2) := fun n =>
    (measure_fail_le μ (ch n) (c n) (h n ^ 2) (X n) (hlaw n)).trans
      (ENNReal.ofReal_le_ofReal ((ch n).clause_ii (c n) (τ n) (hh n) hM₀ (hs n)).2)
  have htsum : (∑' n, μ {ω | h n ^ 2 < pathCost (c n) (ch n).J (X n ω)}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    have hK : 0 ≤ K := by
      by_contra hneg
      replace hneg := lt_of_not_ge hneg
      -- if `K < 0`, the probability bound at `n = 0` would be negative
      have h1 := ((ch 0).clause_ii (c 0) (τ 0) (hh 0) hM₀ (hs 0)).2
      have h2 : 0 ≤ (ch 0).failProb (c 0) (h 0 ^ 2) :=
        Finset.sum_nonneg fun p _ =>
          mul_nonneg ((ch 0).law_nonneg p) (by split_ifs <;> norm_num)
      have h3 : K * h 0 ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by have := hh 0; positivity)
      linarith
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hK (sq_nonneg _))
      (hsum.mul_left K)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω] with n hn
  exact not_lt.1 hn

end BorelCantelli

/-! ## Non-vacuity -/

section NonVacuity

/-- The one-point stage spaces. -/
abbrev UnitStages : ℕ → Type := fun _ => Unit

/-- A one-stage corrected chronological chain on one-point stage spaces. -/
def unitChain : ChronoChain UnitStages where
  J := 1
  ν := fun _ _ => 1
  Q := fun _ _ _ => 1
  ν_pos := fun _ _ _ => one_pos
  ν_total := by simp
  Q_nonneg := fun _ _ _ _ => zero_le_one
  Q_row := fun _ _ _ => by simp
  defect_mem := fun j _ => ⟨0, by
    funext y
    simp [stageDefect, targetMarginal]⟩
  leverage := fun j _ x y _ => by
    have h0 : stageDefect (S := UnitStages) (fun _ _ => 1) (fun _ _ _ => 1) j = 0 := by
      funext y; simp [stageDefect, targetMarginal]
    simp [stagePot, h0, rowAvg]

/-- The deterministic random path on a point. -/
def unitPath : Unit → Path UnitStages unitChain.J := fun _ => Path.snoc () ()

/-- The writer-scale packet is satisfiable (zero cost, zero durations). -/
example : WriterScale unitChain (fun _ _ _ => 0) (fun _ => 0) 1 0 0 0 0 where
  cost_nonneg := fun _ _ _ _ => le_rfl
  dur_nonneg := fun _ _ => le_rfl
  mean_le := fun _ _ => by simp [ChronoChain.refMean]
  occ_le := fun j hj => by
    have := unitChain.occEnergy_nonneg hj
    have h0 : stageDefect (S := UnitStages) (fun _ _ => 1) (fun _ _ _ => 1) j = 0 := by
      funext y; simp [stageDefect, targetMarginal]
    simp [occEnergy, unitChain, h0]
  var_le := fun j _ => by
    simp [ChronoChain.refVar, cylVariance, sourceAvg]
  dur_total := by simp [unitChain]

/-- The Borel–Cantelli packet is satisfiable: Dirac coupling on a point, `h_n = 2^{-n}`. -/
example : ∀ᵐ ω ∂(Measure.dirac () : Measure Unit), ∀ᶠ n in atTop,
    pathCost (S := UnitStages) (fun _ _ _ => 0) unitChain.J (unitPath ω) ≤
      ((1 / 2 : ℝ) ^ n) ^ 2 := by
  have hlaw1 : ∀ p : Path UnitStages unitChain.J, unitChain.law p = 1 := by
    intro p
    have h0 : stageDefect (S := UnitStages) (fun _ _ => 1) (fun _ _ _ => 1) 0 = 0 := by
      funext y; simp [stageDefect, targetMarginal]
    simp [ChronoChain.law, unitChain, chainLaw, pathLaw, corrKernel, corrCoupling,
      refCoupling, thomsonCorrection, stagePot, h0, rowAvg]
  refine eventually_successful_ae (S := fun _ => UnitStages) (Measure.dirac ())
    (fun _ => unitChain) (fun _ _ _ _ => 0) (fun _ _ => 0) (fun n => (1 / 2 : ℝ) ^ n)
    (M₀ := 0) (M₁ := 0) (V₀ := 0) (T := 0) le_rfl (fun n => by positivity) (fun n => ?_)
    ?_ (fun _ => unitPath) ?_
  · exact
      { cost_nonneg := fun _ _ _ _ => le_rfl
        dur_nonneg := fun _ _ => le_rfl
        mean_le := fun _ _ => by simp [ChronoChain.refMean]
        occ_le := fun j hj => by
          have h0 : stageDefect (S := UnitStages) (fun _ _ => 1) (fun _ _ _ => 1) j = 0 := by
            funext y; simp [stageDefect, targetMarginal]
          simp [occEnergy, unitChain, h0]
        var_le := fun j _ => by simp [ChronoChain.refVar, cylVariance, sourceAvg]
        dur_total := by simp [unitChain] }
  · have : (fun n => ((1 / 2 : ℝ) ^ n) ^ 2) = fun n => (1 / 4 : ℝ) ^ n := by
      funext n; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro n p
    have hp : unitPath () = p := rfl
    rw [hlaw1 p, Measure.dirac_apply_of_mem (show () ∈ unitPath ⁻¹' {p} from hp)]
    simp
end NonVacuity

end
end SameCylinderChronologicalChain
end RenewalGeometry
