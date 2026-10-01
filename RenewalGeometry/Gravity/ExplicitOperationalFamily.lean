/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.FiniteMarkovPathSums
import RenewalGeometry.Analysis.PiecewiseAffineH1
import RenewalGeometry.Gravity.FiniteHomogeneousStationarityExact
import RenewalGeometry.Gravity.VacuumRegulatorStationarity

/-!
# The explicit finite accept/reject operational family with an Einstein limit
(`thm:main-explicit-operational-family`, closing sentence of `mt:vacuum`;
emergent-spacetime manuscript, Appendix `supp:homogeneous-dynamics`)

**The cylinders.**  An `AcceptRejectCylinder` is a genuinely finite stochastic trial process:
`stages` time stages, finite proposal alphabets `alphabet j ⊆ ℝ`, a start value, a stage cost
`cost x y`, a temperature `ε` and a retry cap `R`.  At stage `j` the source `x` proposes
`y` uniformly from `alphabet (j+1)` and accepts it with probability `exp(−cost x y/ε)`; after `R`
rejected proposals the history fails.  The one-stage law is
`FiniteMarkovPaths.retryLaw` (defined by its first-trial recursion), the law of a successful
path `q` is the product `pathProb q` of the accepted-value probabilities, and `failureProb` is
the total exhaustion probability; `outcomeLaw` is the resulting law on `Option (ℕ → ℝ)`
(`none` = failure), a probability law (`outcomeLaw_univ`).

**The explicit family** (`explicitCylinder`), for `T, ω, q₀ > 0`, `σ = ±1` and `M` stages,
follows `eq:supp-explicit-scales`: step `s = T/M`, rank-one cost
`rankOneCost σ ω s x y = (A₀/s)(y − x − σωs(x+y)/2)²` (`eq:main-rank-one-cost`, `A₀ = 8/3`),
mesh `δ_M = M⁻³`, temperature `ε_M = M⁻⁵/(1 + log M)`, alphabets `F₀ = {q₀}` and
`F_k = δ_M ℤ ∩ [L_k, U_k]` with `L₀ = q₀/2`, `U₀ = 3q₀/2`, `L_{k+1} = r L_k − δ_M`,
`U_{k+1} = r U_k + δ_M`, `r = (1 + σωs/2)/(1 − σωs/2)`, and the retry cap
`R_M = ⌈7 log M / Z_M⌉` with the explicit row-wise acceptance lower bound `Z_M`.

**Main results** (for `M ≥ M₀`, constants independent of `M`):
* `explicit_failureProb_le`: the retry-failure probability is at most `M⁻⁶`;
* `explicit_energy_le`: `E[ℰ_M; success] ≤ C M⁻⁴`, `ℰ_M = A₀ Σ_j R_j²/s`,
  `R_j = q_{j+1} − q_j − σωs q̄_j` (entropy–energy estimate via
  `FiniteMarkovPaths.gibbs_mean_le` and `FiniteLaplace.softMin_le`);
* `explicit_deviation_le`: `E[max_j |q_j − q₀ e^{σωτ_j}|; success] ≤ C M⁻²`;
* `explicit_firstVariation_le`: for every Lipschitz scale test `φ` with `φ(0) = φ(T) = 0` and
  every bounded lapse test `ψ`, the expected absolute first variation of the finite action
  `S_d` (`eq:main-discrete-homogeneous-action`, `B₀ = A₀ω²`) in the direction
  `(δq_j, δs_j) = (φ(τ_j), s ψ(τ_j))` — including the lapse constraint — is `O(M⁻²)`;
* `explicit_coupling_ae`: under **any** coupling of the cutoffs on a common probability space,
  by the first Borel–Cantelli lemma (`MeasureTheory.ae_eventually_notMem`, i.e.
  `measure_limsup_atTop_eq_zero`), almost surely failures occur only finitely often,
  `ℰ_M → 0`, the piecewise-affine paths converge uniformly and in `H¹(0,T)` to
  `q₀ e^{σωt}`, and the attached `A₃` root-race regulators `κ_j = q_j^{−4/3}`,
  `k = κ_j/(8h²)`, `m = q_j² h³` (`eq:main-stochastic-root-rates`) are positive, have
  predictable bracket `κ_j I` and converge (logarithmically, uniformly in `j`) to the de Sitter
  regulator with `H = 2σω/3`, whose metric solves `G + Λg = 0` with `Λ = 3H² = 4ω²/3`;
* `explicit_operational_family`: **`thm:main-explicit-operational-family`** (packaging);
* `vacuum_regulators_with_operational_realization`: **`mt:vacuum`** with its closing sentence.
-/

open Finset Filter Topology MeasureTheory

namespace RenewalGeometry.ExplicitOperationalFamily

open FiniteMarkovPaths

noncomputable section

/-! ### Finite accept/reject cylinders -/

/-- The normalization `A₀ = 8/3` of the finite homogeneous action. -/
def A₀ : ℝ := 8 / 3

theorem A₀_pos : 0 < A₀ := by norm_num [A₀]

/-- The rank-one cost `E_s(x,y) = (A₀/s)(y − x − σωs(x+y)/2)²` (`eq:main-rank-one-cost`). -/
def rankOneCost (σ ω s : ℝ) (x y : ℝ) : ℝ := A₀ / s * (y - x - σ * ω * s * (x + y) / 2) ^ 2

/-- A finite accept/reject cylinder with uniform proposals and a retry cap. -/
structure AcceptRejectCylinder where
  /-- the number `M` of time stages -/
  stages : ℕ
  /-- the calibrated lapse-weighted step `s` -/
  step : ℝ
  /-- the start value `q₀` -/
  start : ℝ
  /-- the finite proposal alphabets (stage `j` values lie in `alphabet j`) -/
  alphabet : ℕ → Finset ℝ
  /-- the stage cost `E(x,y)` -/
  cost : ℝ → ℝ → ℝ
  /-- the temperature `ε` -/
  temperature : ℝ
  /-- the maximal number of proposals per stage -/
  retryCap : ℕ

namespace AcceptRejectCylinder

variable (C : AcceptRejectCylinder)

/-- Uniform proposal weight on `alphabet (j+1)`. -/
def proposal (j : ℕ) (_y : ℝ) : ℝ := ((C.alphabet (j + 1)).card : ℝ)⁻¹

/-- Acceptance probability `a(x,y) = exp(−E(x,y)/ε)` (`eq:supp-explicit-acceptance`). -/
def acceptance (x y : ℝ) : ℝ := Real.exp (-C.cost x y / C.temperature)

/-- Total acceptance probability of one proposal from `x` at stage `j`. -/
def totalAcceptance (j : ℕ) (x : ℝ) : ℝ :=
  ∑ y ∈ C.alphabet (j + 1), C.proposal j y * C.acceptance x y

/-- The law of the capped trial loop from `x` at stage `j` (`none`: the cap is exhausted). -/
def stageLaw (j : ℕ) (x : ℝ) : Option ℝ → ℝ :=
  retryLaw (C.alphabet (j + 1)) (C.proposal j) (C.acceptance x) C.retryCap

/-- Probability that stage `j` from `x` accepts `y`. -/
def kernel (j : ℕ) (x y : ℝ) : ℝ := C.stageLaw j x (some y)

/-- Probability that stage `j` from `x` exhausts the retry cap. -/
def exhaustion (j : ℕ) (x : ℝ) : ℝ := C.stageLaw j x none

/-- The finite set of complete successful histories. -/
def successPaths : Finset (ℕ → ℝ) := paths C.alphabet C.start C.stages

/-- Probability of a complete successful history. -/
def pathProb (q : ℕ → ℝ) : ℝ := weight C.kernel C.stages q

/-- Total retry-failure probability. -/
def failureProb : ℝ := failMass C.alphabet C.start C.kernel C.exhaustion C.stages

/-- `E[g; success]`. -/
def successExpect (g : (ℕ → ℝ) → ℝ) : ℝ := ∑ q ∈ C.successPaths, C.pathProb q * g q

open Classical in
/-- The law of the outcome (`some q`: the successful history `q`; `none`: failure). -/
def outcomeLaw (S : Set (Option (ℕ → ℝ))) : ℝ :=
  (∑ q ∈ C.successPaths, if some q ∈ S then C.pathProb q else 0) +
    if none ∈ S then C.failureProb else 0

/-- Well-formedness: nonnegative cost, positive temperature, start in `alphabet 0`. -/
structure WellFormed : Prop where
  cost_nonneg : ∀ x y, 0 ≤ C.cost x y
  temperature_pos : 0 < C.temperature
  start_mem : C.start ∈ C.alphabet 0

variable {C}

theorem acceptance_pos (x y : ℝ) : 0 < C.acceptance x y := Real.exp_pos _

theorem acceptance_le_one (hC : C.WellFormed) (x y : ℝ) : C.acceptance x y ≤ 1 := by
  unfold acceptance
  rw [Real.exp_le_one_iff]
  have := hC.cost_nonneg x y
  have := hC.temperature_pos
  have : 0 ≤ C.cost x y / C.temperature := div_nonneg (by assumption) (le_of_lt (by assumption))
  rw [neg_div]; linarith

theorem proposal_nonneg (j : ℕ) (y : ℝ) : 0 ≤ C.proposal j y := inv_nonneg.2 (Nat.cast_nonneg _)

theorem totalAcceptance_nonneg (j : ℕ) (x : ℝ) : 0 ≤ C.totalAcceptance j x :=
  sum_nonneg fun y _ => mul_nonneg (proposal_nonneg j y) (acceptance_pos x y).le

theorem totalAcceptance_le_one (hC : C.WellFormed) (j : ℕ) (x : ℝ) :
    C.totalAcceptance j x ≤ 1 := by
  unfold totalAcceptance
  calc ∑ y ∈ C.alphabet (j + 1), C.proposal j y * C.acceptance x y
      ≤ ∑ y ∈ C.alphabet (j + 1), C.proposal j y * 1 :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (acceptance_le_one hC x y)
          (proposal_nonneg j y)
    _ ≤ 1 := by
        simp only [mul_one, proposal, sum_const, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos (C.alphabet (j + 1)).card with h | h
        · rw [h]; simp
        · rw [mul_inv_cancel₀ (by exact_mod_cast h.ne')]

theorem totalAcceptance_pos (j : ℕ) (x : ℝ) (hne : (C.alphabet (j + 1)).Nonempty) :
    0 < C.totalAcceptance j x :=
  sum_pos (fun y _ => mul_pos (inv_pos.2 (by exact_mod_cast hne.card_pos)) (acceptance_pos x y))
    hne

theorem kernel_nonneg (hC : C.WellFormed) (j : ℕ) (x y : ℝ) : 0 ≤ C.kernel j x y :=
  retryLaw_some_nonneg (fun y => proposal_nonneg j y) (fun y => (acceptance_pos x y).le)
    (totalAcceptance_le_one hC j x) _ y

theorem exhaustion_nonneg (hC : C.WellFormed) (j : ℕ) (x : ℝ) : 0 ≤ C.exhaustion j x := by
  unfold exhaustion stageLaw
  rw [retryLaw_none]
  have := totalAcceptance_le_one hC j x
  unfold totalAcceptance at this
  exact pow_nonneg (by linarith) _

theorem kernel_sum_add_exhaustion (j : ℕ) (x : ℝ) :
    ∑ y ∈ C.alphabet (j + 1), C.kernel j x y + C.exhaustion j x = 1 :=
  retryLaw_total _

theorem kernel_sum_le_one (hC : C.WellFormed) (j : ℕ) (x : ℝ) :
    ∑ y ∈ C.alphabet (j + 1), C.kernel j x y ≤ 1 := by
  have := kernel_sum_add_exhaustion (C := C) j x
  have := exhaustion_nonneg hC j x
  linarith

/-- The total probability of the outcome law is one. -/
theorem failureProb_add_mass (hC : C.WellFormed) :
    C.failureProb + ∑ q ∈ C.successPaths, C.pathProb q = 1 :=
  failMass_add_mass hC.start_mem (fun j x _ => kernel_sum_add_exhaustion j x) C.stages

theorem pathProb_nonneg (hC : C.WellFormed) (q : ℕ → ℝ) : 0 ≤ C.pathProb q :=
  weight_nonneg (kernel_nonneg hC) _ q

theorem mass_le_one' (hC : C.WellFormed) : ∑ q ∈ C.successPaths, C.pathProb q ≤ 1 :=
  mass_le_one hC.start_mem (kernel_nonneg hC) (fun j x _ => kernel_sum_le_one hC j x) _

theorem failureProb_nonneg (hC : C.WellFormed) : 0 ≤ C.failureProb := by
  have := failureProb_add_mass hC
  have := mass_le_one' hC
  linarith

open Classical in
/-- The outcome law is a probability law. -/
theorem outcomeLaw_univ (hC : C.WellFormed) : C.outcomeLaw Set.univ = 1 := by
  simp only [outcomeLaw, Set.mem_univ, if_true]
  rw [add_comm]; exact failureProb_add_mass hC

theorem outcomeLaw_nonneg (hC : C.WellFormed) (S : Set (Option (ℕ → ℝ))) :
    0 ≤ C.outcomeLaw S := by
  classical
  unfold outcomeLaw
  refine add_nonneg (sum_nonneg fun q _ => ?_) ?_
  · split_ifs
    · exact pathProb_nonneg hC q
    · exact le_rfl
  · split_ifs
    · exact failureProb_nonneg hC
    · exact le_rfl

theorem successExpect_mono (hC : C.WellFormed) {g h : (ℕ → ℝ) → ℝ}
    (hgh : ∀ q ∈ C.successPaths, g q ≤ h q) : C.successExpect g ≤ C.successExpect h :=
  sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hgh q hq) (pathProb_nonneg hC q)

theorem successExpect_nonneg (hC : C.WellFormed) {g : (ℕ → ℝ) → ℝ}
    (hg : ∀ q ∈ C.successPaths, 0 ≤ g q) : 0 ≤ C.successExpect g :=
  sum_nonneg fun q hq => mul_nonneg (pathProb_nonneg hC q) (hg q hq)

theorem successExpect_add (g h : (ℕ → ℝ) → ℝ) :
    C.successExpect (fun q => g q + h q) = C.successExpect g + C.successExpect h := by
  unfold successExpect; rw [← sum_add_distrib]; exact sum_congr rfl fun q _ => by ring

theorem successExpect_const_mul (c : ℝ) (g : (ℕ → ℝ) → ℝ) :
    C.successExpect (fun q => c * g q) = c * C.successExpect g := by
  unfold successExpect; rw [mul_sum]; exact sum_congr rfl fun q _ => by ring

theorem successExpect_const_le (hC : C.WellFormed) {c : ℝ} (hc : 0 ≤ c) :
    C.successExpect (fun _ => c) ≤ c := by
  unfold successExpect
  rw [← sum_mul]
  calc (∑ q ∈ C.successPaths, C.pathProb q) * c ≤ 1 * c :=
        mul_le_mul_of_nonneg_right (mass_le_one' hC) hc
    _ = c := one_mul c

/-- **The one-stage mean cost is at most the Gibbs bound.**  For `x` with a candidate `y₀` in the
next alphabet, the mean cost of the capped trial loop is at most `E(x,y₀) + ε log #F_{j+1}`. -/
theorem kernel_mean_cost_le (hC : C.WellFormed) (j : ℕ) (x : ℝ) {y₀ : ℝ}
    (hy₀ : y₀ ∈ C.alphabet (j + 1)) :
    ∑ y ∈ C.alphabet (j + 1), C.kernel j x y * C.cost x y
      ≤ C.cost x y₀ + C.temperature * Real.log (C.alphabet (j + 1)).card := by
  have hne : (C.alphabet (j + 1)).Nonempty := ⟨y₀, hy₀⟩
  have hZ0 := totalAcceptance_pos (C := C) j x hne
  have hZ1 := totalAcceptance_le_one hC j x
  have hn : (0 : ℝ) < (C.alphabet (j + 1)).card := by exact_mod_cast hne.card_pos
  -- kernel ≤ accepted row = Boltzmann row
  have hrow : ∀ y ∈ C.alphabet (j + 1), C.kernel j x y
      ≤ Real.exp (-C.cost x y / C.temperature) /
        ∑ z ∈ C.alphabet (j + 1), Real.exp (-C.cost x z / C.temperature) := by
    intro y hy
    have h := retryLaw_some_le (G := C.alphabet (j + 1)) (p := C.proposal j)
      (a := C.acceptance x) (fun y => proposal_nonneg j y) (fun y => (acceptance_pos x y).le)
      hZ0 hZ1 C.retryCap hy
    refine h.trans (le_of_eq ?_)
    simp only [proposal, acceptance]
    rw [← mul_sum, mul_div_mul_left _ _ (inv_pos.2 hn).ne']
  calc ∑ y ∈ C.alphabet (j + 1), C.kernel j x y * C.cost x y
      ≤ ∑ y ∈ C.alphabet (j + 1), Real.exp (-C.cost x y / C.temperature) /
          (∑ z ∈ C.alphabet (j + 1), Real.exp (-C.cost x z / C.temperature)) * C.cost x y :=
        sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hrow y hy) (hC.cost_nonneg x y)
    _ ≤ C.cost x y₀ + C.temperature * Real.log (C.alphabet (j + 1)).card :=
        gibbs_mean_le hC.temperature_pos (C.cost x) hy₀

end AcceptRejectCylinder

/-! ### The explicit family: definitions -/

/-- The stationary multiplier `r = (1 + σωs/2)/(1 − σωs/2)`. -/
def ratio (ω σ s : ℝ) : ℝ := (1 + σ * ω * s / 2) / (1 - σ * ω * s / 2)

/-- The mesh `δ_M = M⁻³`. -/
def mesh (M : ℕ) : ℝ := 1 / (M : ℝ) ^ 3

/-- The temperature schedule `ε_M = M⁻⁵/(1 + log M)` (`eq:supp-explicit-scales`). -/
def temp (M : ℕ) : ℝ := 1 / (M : ℝ) ^ 5 / (1 + Real.log M)

/-- Lower support edge `L_k = r^k q₀/2 − δ Σ_{i<k} r^i` (so `L₀ = q₀/2`, `L_{k+1} = r L_k − δ`). -/
def lowerEdge (T ω q₀ σ : ℝ) (M k : ℕ) : ℝ :=
  ratio ω σ (T / M) ^ k * (q₀ / 2) - mesh M * ∑ i ∈ range k, ratio ω σ (T / M) ^ i

/-- Upper support edge `U_k = r^k 3q₀/2 + δ Σ_{i<k} r^i` (so `U₀ = 3q₀/2`, `U_{k+1} = r U_k + δ`). -/
def upperEdge (T ω q₀ σ : ℝ) (M k : ℕ) : ℝ :=
  ratio ω σ (T / M) ^ k * (3 * q₀ / 2) + mesh M * ∑ i ∈ range k, ratio ω σ (T / M) ^ i

/-- The grid `δℤ ∩ [L, U]`. -/
def meshGrid (δ L U : ℝ) : Finset ℝ := (Icc ⌈L / δ⌉ ⌊U / δ⌋).image fun i : ℤ => (i : ℝ) * δ

/-- The finite proposal alphabets: `F₀ = {q₀}`, `F_k = δ_M ℤ ∩ [L_k, U_k]` for `k ≥ 1`. -/
def alphabetOf (T ω q₀ σ : ℝ) (M k : ℕ) : Finset ℝ :=
  if k = 0 then {q₀} else meshGrid (mesh M) (lowerEdge T ω q₀ σ M k) (upperEdge T ω q₀ σ M k)

/-- The growth constant `Γ = e^{2ωT}` bounding `r^{±k}`, `k ≤ M`. -/
def growth (T ω : ℝ) : ℝ := Real.exp (2 * ω * T)

/-- The grid-cardinality constant `N = 2q₀Γ + 1` (`#F_k ≤ N M³`). -/
def gridConst (T ω q₀ : ℝ) : ℝ := 2 * q₀ * growth T ω + 1

/-- The cost constant `c = 9A₀/(4T)` (the nearest grid target costs at most `c M⁻⁵`). -/
def costConst (T : ℝ) : ℝ := 9 * A₀ / (4 * T)

/-- The explicit row-wise acceptance lower bound `Z_M = e^{−c(1 + log M)}/(N M³)`. -/
def accLower (T ω q₀ : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-(costConst T * (1 + Real.log M))) / (gridConst T ω q₀ * (M : ℝ) ^ 3)

/-- The retry cap `R_M = ⌈7 log M / Z_M⌉`. -/
def retryCapOf (T ω q₀ : ℝ) (M : ℕ) : ℕ := ⌈7 * Real.log M / accLower T ω q₀ M⌉₊

/-- **The explicit finite accept/reject cylinder with `M` stages.** -/
def explicitCylinder (T ω q₀ σ : ℝ) (M : ℕ) : AcceptRejectCylinder where
  stages := M
  step := T / M
  start := q₀
  alphabet := alphabetOf T ω q₀ σ M
  cost := rankOneCost σ ω (T / M)
  temperature := temp M
  retryCap := retryCapOf T ω q₀ M

/-- The threshold `M₀` from which all estimates hold. -/
def threshold (T ω q₀ : ℝ) : ℕ := ⌈ω * T + 4 * growth T ω ^ 2 / q₀ + ω ^ 3 * T ^ 3 + 2⌉₊

/-- The residual `R_j = q_{j+1} − q_j − σωs q̄_j` (`eq:supp-homogeneous-residual`). -/
def residual (σ ω s : ℝ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  q (j + 1) - q j - σ * ω * s * ((q j + q (j + 1)) / 2)

/-- The residual energy `ℰ_M = A₀ Σ_{j<M} R_j²/s`. -/
def residualEnergy (σ ω : ℝ) (M : ℕ) (s : ℝ) (q : ℕ → ℝ) : ℝ :=
  A₀ * ∑ j ∈ range M, residual σ ω s q j ^ 2 / s

/-- The stationary profile `q₀ e^{σωt}`. -/
def stationaryProfile (q₀ σ ω : ℝ) (t : ℝ) : ℝ := q₀ * Real.exp (σ * ω * t)

/-- The maximal nodal deviation `max_{j ≤ M} |q_j − q₀ e^{σωτ_j}|`, `τ_j = j s`. -/
def maxDeviation (q₀ σ ω : ℝ) (M : ℕ) (s : ℝ) (q : ℕ → ℝ) : ℝ :=
  (range (M + 1)).sup' nonempty_range_add_one fun j => |q j - stationaryProfile q₀ σ ω (j * s)|

/-! ### Elementary estimates -/

section Estimates

variable {T ω q₀ σ : ℝ}

theorem residualEnergy_eq_addSum (σ ω : ℝ) (M : ℕ) (s : ℝ) (q : ℕ → ℝ) :
    residualEnergy σ ω M s q = addSum (fun _ => rankOneCost σ ω s) M q := by
  unfold residualEnergy addSum rankOneCost residual
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

theorem residualEnergy_nonneg (σ ω : ℝ) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (q : ℕ → ℝ) :
    0 ≤ residualEnergy σ ω M s q :=
  mul_nonneg A₀_pos.le (sum_nonneg fun j _ => div_nonneg (sq_nonneg _) hs)

theorem one_le_growth (hT : 0 < T) (hω : 0 < ω) : 1 ≤ growth T ω :=
  Real.one_le_exp (by positivity)

theorem growth_pos : 0 < growth T ω := Real.exp_pos _

/-- `(1+x)/(1−x) ≤ e^{4x}` for `0 ≤ x ≤ 1/2`. -/
theorem ratio_base_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 + x) / (1 - x) ≤ Real.exp (4 * x) := by
  have h1 : 0 < 1 - x := by linarith
  calc (1 + x) / (1 - x) ≤ 1 + 4 * x := by
        rw [div_le_iff₀ h1]; nlinarith
    _ ≤ Real.exp (4 * x) := by have := Real.add_one_le_exp (4 * x); linarith

theorem one_le_ratio_base {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : 1 ≤ (1 + x) / (1 - x) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- Two-sided bounds `e^{−4x} ≤ r ≤ e^{4x}` and `max r 1 ≤ e^{4x}` with `x = ωs/2 ∈ [0, 1/2]`. -/
theorem ratio_bounds (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hx0 : 0 ≤ ω * s / 2)
    (hx : ω * s / 2 ≤ 1 / 2) :
    0 < ratio ω σ s ∧ Real.exp (-(4 * (ω * s / 2))) ≤ ratio ω σ s ∧
      max (ratio ω σ s) 1 ≤ Real.exp (4 * (ω * s / 2)) := by
  set x := ω * s / 2 with hxdef
  have hb := ratio_base_le_exp hx0 hx
  have h1 := one_le_ratio_base hx0 (by linarith)
  have hpos : 0 < (1 + x) / (1 - x) := by linarith
  rcases hσ with rfl | rfl
  · have hr : ratio ω 1 s = (1 + x) / (1 - x) := by unfold ratio; rw [hxdef]; ring_nf
    rw [hr]
    refine ⟨hpos, ?_, max_le hb (by linarith [Real.add_one_le_exp (4 * x)])⟩
    have : Real.exp (-(4 * x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · have hr : ratio ω (-1) s = ((1 + x) / (1 - x))⁻¹ := by
      unfold ratio; rw [hxdef, inv_div]; ring_nf
    rw [hr]
    refine ⟨inv_pos.2 hpos, ?_, ?_⟩
    · rw [Real.exp_neg]; exact inv_anti₀ hpos hb
    · refine max_le ?_ (by linarith [Real.add_one_le_exp (4 * x)])
      exact (inv_le_one_of_one_le₀ h1).trans (by linarith [Real.add_one_le_exp (4 * x)])

/-- Facts valid from the threshold on. -/
theorem large_facts (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) {M : ℕ}
    (hM : threshold T ω q₀ ≤ M) :
    (2 : ℝ) ≤ M ∧ ω * T ≤ M ∧ 4 * growth T ω ^ 2 / q₀ ≤ (M : ℝ) ^ 2 ∧
      ω ^ 3 * T ^ 3 ≤ (M : ℝ) ^ 2 := by
  have hX : ω * T + 4 * growth T ω ^ 2 / q₀ + ω ^ 3 * T ^ 3 + 2 ≤ M :=
    (Nat.le_ceil _).trans (by exact_mod_cast hM)
  have h1 : 0 ≤ ω * T := by positivity
  have h2 : 0 ≤ 4 * growth T ω ^ 2 / q₀ := by have := growth_pos (T := T) (ω := ω); positivity
  have h3 : 0 ≤ ω ^ 3 * T ^ 3 := by positivity
  have hM2 : (2 : ℝ) ≤ M := by linarith
  have hMM : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  refine ⟨hM2, by linarith, by linarith, by linarith⟩

theorem threshold_pos (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) : 1 ≤ threshold T ω q₀ := by
  have := large_facts hT hω hq₀ (le_refl (threshold T ω q₀))
  exact_mod_cast (show (1 : ℝ) ≤ threshold T ω q₀ by linarith [this.1])

/-- From the threshold on, `x = ω(T/M)/2 ∈ (0, 1/2]`. -/
theorem half_step_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) {M : ℕ}
    (hM : threshold T ω q₀ ≤ M) : 0 < ω * (T / M) / 2 ∧ ω * (T / M) / 2 ≤ 1 / 2 := by
  obtain ⟨hM2, hωT, -, -⟩ := large_facts hT hω hq₀ hM
  have hMpos : (0 : ℝ) < M := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), mul_div_assoc', div_le_iff₀ hMpos]
  linarith

/-- From the threshold on, `Γ⁻¹ ≤ r^k ≤ Γ` and `max r 1 ^ k ≤ Γ` for `k ≤ M`. -/
theorem ratio_pow_bounds (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k ≤ M) :
    0 < ratio ω σ (T / M) ^ k ∧ (growth T ω)⁻¹ ≤ ratio ω σ (T / M) ^ k ∧
      ratio ω σ (T / M) ^ k ≤ growth T ω ∧ max (ratio ω σ (T / M)) 1 ^ k ≤ growth T ω := by
  obtain ⟨hx0, hx⟩ := half_step_le hT hω hq₀ hM
  obtain ⟨hr0, hlo, hhi⟩ := ratio_bounds hσ (s := T / M) hx0.le hx
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hkM : (k : ℝ) ≤ M := by exact_mod_cast hk
  have hexp : 4 * (ω * (T / M) / 2) * k ≤ 2 * ω * T := by
    have : 4 * (ω * (T / M) / 2) * M = 2 * ω * T := by field_simp; ring
    rw [← this]; gcongr
  have hmax : max (ratio ω σ (T / M)) 1 ^ k ≤ growth T ω := by
    calc max (ratio ω σ (T / M)) 1 ^ k ≤ Real.exp (4 * (ω * (T / M) / 2)) ^ k :=
          pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) hhi k
      _ = Real.exp (4 * (ω * (T / M) / 2) * k) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ growth T ω := Real.exp_le_exp.2 hexp
  refine ⟨pow_pos hr0 k, ?_, ?_, hmax⟩
  · calc (growth T ω)⁻¹ = Real.exp (-(2 * ω * T)) := by rw [growth, Real.exp_neg]
      _ ≤ Real.exp (-(4 * (ω * (T / M) / 2) * k)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(4 * (ω * (T / M) / 2))) ^ k := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ ratio ω σ (T / M) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le hlo k
  · exact (pow_le_pow_left₀ hr0.le (le_max_left _ 1) k).trans hmax

theorem lowerEdge_succ (T ω q₀ σ : ℝ) (M k : ℕ) :
    lowerEdge T ω q₀ σ M (k + 1) = ratio ω σ (T / M) * lowerEdge T ω q₀ σ M k - mesh M := by
  unfold lowerEdge; rw [geom_sum_succ, pow_succ]; ring

theorem upperEdge_succ (T ω q₀ σ : ℝ) (M k : ℕ) :
    upperEdge T ω q₀ σ M (k + 1) = ratio ω σ (T / M) * upperEdge T ω q₀ σ M k + mesh M := by
  unfold upperEdge; rw [geom_sum_succ, pow_succ]; ring

/-- The lower amplitude bound `q₋ = q₀/(4Γ)`. -/
def qLower (T ω q₀ : ℝ) : ℝ := q₀ / (4 * growth T ω)

/-- The upper amplitude bound `q₊ = 2q₀Γ`. -/
def qUpper (T ω q₀ : ℝ) : ℝ := 2 * q₀ * growth T ω

theorem qLower_pos (hq₀ : 0 < q₀) : 0 < qLower T ω q₀ := by
  unfold qLower; have := growth_pos (T := T) (ω := ω); positivity

/-- From the threshold on, the support edges satisfy `q₋ ≤ L_k ≤ U_k ≤ q₊` for `k ≤ M`. -/
theorem edges_bounds (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k ≤ M) :
    qLower T ω q₀ ≤ lowerEdge T ω q₀ σ M k ∧ lowerEdge T ω q₀ σ M k ≤ upperEdge T ω q₀ σ M k ∧
      upperEdge T ω q₀ σ M k ≤ qUpper T ω q₀ := by
  obtain ⟨hM2, -, hG, -⟩ := large_facts hT hω hq₀ hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hΓ1 := one_le_growth hT hω (T := T)
  have hΓ0 : 0 < growth T ω := growth_pos
  obtain ⟨hrk, hlo, hhi, -⟩ := ratio_pow_bounds hT hω hq₀ hσ hM hk
  set Γ := growth T ω
  set r := ratio ω σ (T / M)
  set S := ∑ i ∈ range k, r ^ i
  have hr0 : 0 < r := (ratio_bounds hσ (half_step_le hT hω hq₀ hM).1.le
    (half_step_le hT hω hq₀ hM).2).1
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => pow_nonneg hr0.le i
  have hS : S ≤ M * Γ := by
    calc S ≤ ∑ _i ∈ range k, Γ := sum_le_sum fun i hi =>
          (ratio_pow_bounds hT hω hq₀ hσ hM (k := i) (by have := mem_range.1 hi; omega)).2.2.1
      _ = k * Γ := by simp
      _ ≤ M * Γ := by gcongr
  have hδ : mesh M * S ≤ Γ / (M : ℝ) ^ 2 := by
    calc mesh M * S ≤ mesh M * (M * Γ) :=
          mul_le_mul_of_nonneg_left hS (by unfold mesh; positivity)
      _ = Γ / (M : ℝ) ^ 2 := by unfold mesh; field_simp
  have hδ0 : 0 ≤ mesh M * S := mul_nonneg (by unfold mesh; positivity) hS0
  -- `Γ/M² ≤ q₀/(4Γ)`
  have hsmall : Γ / (M : ℝ) ^ 2 ≤ q₀ / (4 * Γ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ hq₀] at hG
    nlinarith
  have hrq : Γ⁻¹ * (q₀ / 2) ≤ r ^ k * (q₀ / 2) := mul_le_mul_of_nonneg_right hlo (by positivity)
  have hΓinv : Γ⁻¹ * (q₀ / 2) = 2 * (q₀ / (4 * Γ)) := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold lowerEdge qLower
    show q₀ / (4 * Γ) ≤ r ^ k * (q₀ / 2) - mesh M * S
    linarith
  · unfold lowerEdge upperEdge
    show r ^ k * (q₀ / 2) - mesh M * S ≤ r ^ k * (3 * q₀ / 2) + mesh M * S
    nlinarith
  · unfold upperEdge qUpper
    show r ^ k * (3 * q₀ / 2) + mesh M * S ≤ 2 * q₀ * Γ
    have h1 : r ^ k * (3 * q₀ / 2) ≤ Γ * (3 * q₀ / 2) := mul_le_mul_of_nonneg_right hhi (by positivity)
    have h2 : q₀ / (4 * Γ) ≤ q₀ * Γ / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith

/-! ### The mesh grid -/

theorem mem_meshGrid {δ L U y : ℝ} (hδ : 0 < δ) (hy : y ∈ meshGrid δ L U) : L ≤ y ∧ y ≤ U := by
  unfold meshGrid at hy
  rw [mem_image] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  rw [mem_Icc] at hi
  constructor
  · have h1 : L / δ ≤ (i : ℝ) := (Int.ceil_le.1 hi.1)
    rwa [div_le_iff₀ hδ] at h1
  · have h2 : (i : ℝ) ≤ U / δ := (Int.le_floor.1 hi.2)
    rwa [le_div_iff₀ hδ] at h2

theorem floor_mem_meshGrid {δ L U z : ℝ} (hδ : 0 < δ) (hL : L ≤ z - δ) (hU : z ≤ U) :
    (⌊z / δ⌋ : ℝ) * δ ∈ meshGrid δ L U ∧ |(⌊z / δ⌋ : ℝ) * δ - z| ≤ δ := by
  have hf1 : (⌊z / δ⌋ : ℝ) ≤ z / δ := Int.floor_le _
  have hf2 : z / δ - 1 < (⌊z / δ⌋ : ℝ) := Int.sub_one_lt_floor _
  have hz1 : (⌊z / δ⌋ : ℝ) * δ ≤ z := by rwa [le_div_iff₀ hδ] at hf1
  have hz2 : z - δ < (⌊z / δ⌋ : ℝ) * δ := by
    have := (mul_lt_mul_of_pos_right hf2 hδ)
    rwa [sub_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at this
  refine ⟨?_, ?_⟩
  · unfold meshGrid
    rw [mem_image]
    refine ⟨⌊z / δ⌋, ?_, rfl⟩
    rw [mem_Icc]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ hδ]; linarith
    · exact Int.floor_mono (div_le_div_of_nonneg_right hU hδ.le)
  · rw [abs_le]; constructor <;> linarith

theorem card_meshGrid_le {δ L U : ℝ} (hδ : 0 < δ) (hLU : L ≤ U) :
    ((meshGrid δ L U).card : ℝ) ≤ (U - L) / δ + 1 := by
  have hcard : (meshGrid δ L U).card ≤ (Icc ⌈L / δ⌉ ⌊U / δ⌋).card := card_image_le
  rw [Int.card_Icc] at hcard
  have h1 : ((⌊U / δ⌋ + 1 - ⌈L / δ⌉).toNat : ℝ) ≤ (U - L) / δ + 1 := by
    have hcast : (((⌊U / δ⌋ + 1 - ⌈L / δ⌉).toNat : ℤ) : ℝ)
        = ((max (⌊U / δ⌋ + 1 - ⌈L / δ⌉) 0 : ℤ) : ℝ) := by rw [Int.toNat_eq_max]
    rw [show (((⌊U / δ⌋ + 1 - ⌈L / δ⌉).toNat : ℕ) : ℝ)
        = (((⌊U / δ⌋ + 1 - ⌈L / δ⌉).toNat : ℤ) : ℝ) by norm_cast, hcast]
    have hUL : 0 ≤ (U - L) / δ := div_nonneg (by linarith) hδ.le
    rw [Int.cast_max]
    refine max_le ?_ (by simp; linarith)
    push_cast
    have := Int.floor_le (U / δ)
    have := Int.le_ceil (L / δ)
    rw [sub_div] at hUL ⊢
    linarith
  calc ((meshGrid δ L U).card : ℝ) ≤ ((⌊U / δ⌋ + 1 - ⌈L / δ⌉).toNat : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (U - L) / δ + 1 := h1

end Estimates

/-! ### The explicit alphabets -/

section Alphabets

variable {T ω q₀ σ : ℝ}

theorem mesh_pos {M : ℕ} (hM : (1 : ℝ) ≤ M) : 0 < mesh M := by unfold mesh; positivity

theorem alphabetOf_zero (T ω q₀ σ : ℝ) (M : ℕ) : alphabetOf T ω q₀ σ M 0 = {q₀} := by
  simp [alphabetOf]

theorem alphabetOf_succ (T ω q₀ σ : ℝ) (M k : ℕ) :
    alphabetOf T ω q₀ σ M (k + 1)
      = meshGrid (mesh M) (lowerEdge T ω q₀ σ M (k + 1)) (upperEdge T ω q₀ σ M (k + 1)) := by
  simp [alphabetOf]

/-- Alphabet values lie between the support edges. -/
theorem alphabet_sub_edges (hq₀ : 0 < q₀) {M : ℕ} (hM1 : (1 : ℝ) ≤ M) {k : ℕ} {x : ℝ}
    (hx : x ∈ alphabetOf T ω q₀ σ M k) :
    lowerEdge T ω q₀ σ M k ≤ x ∧ x ≤ upperEdge T ω q₀ σ M k := by
  rcases k with _ | k
  · rw [alphabetOf_zero, mem_singleton] at hx
    subst hx
    simp only [lowerEdge, upperEdge, pow_zero, one_mul, range_zero, sum_empty, mul_zero,
      sub_zero, add_zero]
    constructor <;> linarith
  · rw [alphabetOf_succ] at hx
    exact mem_meshGrid (mesh_pos hM1) hx

/-- From the threshold on, all alphabet values `k ≤ M` lie in `[q₋, q₊]`, `q₋ > 0`. -/
theorem alphabet_bounds (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k ≤ M) {x : ℝ}
    (hx : x ∈ alphabetOf T ω q₀ σ M k) : qLower T ω q₀ ≤ x ∧ x ≤ qUpper T ω q₀ := by
  have hM1 : (1 : ℝ) ≤ M := by linarith [(large_facts hT hω hq₀ hM).1]
  obtain ⟨h1, -, h3⟩ := edges_bounds hT hω hq₀ hσ hM hk
  obtain ⟨hx1, hx2⟩ := alphabet_sub_edges hq₀ hM1 hx
  exact ⟨h1.trans hx1, hx2.trans h3⟩

/-- **Nearest grid target**: every source `x ∈ F_k`, `k < M`, has a proposal `y ∈ F_{k+1}`
with `|y − r x| ≤ δ_M`. -/
theorem near_target (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k < M) {x : ℝ}
    (hx : x ∈ alphabetOf T ω q₀ σ M k) :
    ∃ y ∈ alphabetOf T ω q₀ σ M (k + 1), |y - ratio ω σ (T / M) * x| ≤ mesh M := by
  have hM1 : (1 : ℝ) ≤ M := by linarith [(large_facts hT hω hq₀ hM).1]
  have hr0 : 0 < ratio ω σ (T / M) := (ratio_bounds hσ (half_step_le hT hω hq₀ hM).1.le
    (half_step_le hT hω hq₀ hM).2).1
  obtain ⟨hx1, hx2⟩ := alphabet_sub_edges hq₀ hM1 hx
  obtain ⟨hmem, hnear⟩ := floor_mem_meshGrid (z := ratio ω σ (T / M) * x) (mesh_pos hM1)
    (L := lowerEdge T ω q₀ σ M (k + 1)) (U := upperEdge T ω q₀ σ M (k + 1))
    (by rw [lowerEdge_succ]; nlinarith) (by rw [upperEdge_succ]; nlinarith [mesh_pos hM1])
  exact ⟨_, by rw [alphabetOf_succ]; exact hmem, hnear⟩

theorem alphabet_nonempty (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k ≤ M) :
    (alphabetOf T ω q₀ σ M k).Nonempty := by
  induction k with
  | zero => rw [alphabetOf_zero]; exact singleton_nonempty _
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih (by omega)
    obtain ⟨y, hy, -⟩ := near_target hT hω hq₀ hσ hM (by omega) hx
    exact ⟨y, hy⟩

/-- `#F_k ≤ N M³` for `1 ≤ k ≤ M`. -/
theorem card_alphabet_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k ≤ M) :
    ((alphabetOf T ω q₀ σ M (k + 1)).card : ℝ) ≤ gridConst T ω q₀ * (M : ℝ) ^ 3 ∨ M ≤ k := by
  rcases Nat.lt_or_ge k M with hkM | hkM
  · left
    have hM1 : (1 : ℝ) ≤ M := by linarith [(large_facts hT hω hq₀ hM).1]
    obtain ⟨h1, h2, h3⟩ := edges_bounds hT hω hq₀ hσ hM (k := k + 1) (by omega)
    have hq := (qLower_pos hq₀ (T := T) (ω := ω)).le
    rw [alphabetOf_succ]
    refine (card_meshGrid_le (mesh_pos hM1) h2).trans ?_
    have hδ : mesh M = 1 / (M : ℝ) ^ 3 := rfl
    rw [hδ, div_div_eq_mul_div, div_one]
    have hM3 : (1 : ℝ) ≤ (M : ℝ) ^ 3 := one_le_pow₀ hM1
    unfold gridConst
    unfold qUpper at h3
    nlinarith
  · right; exact hkM

/-- The rank-one cost in completed-square form `(A₀/s)(d (y − r x))²`, `d = 1 − σωs/2`. -/
theorem rankOneCost_eq (σ ω s x y : ℝ) (hd : 1 - σ * ω * s / 2 ≠ 0) :
    rankOneCost σ ω s x y = A₀ / s * ((1 - σ * ω * s / 2) * (y - ratio ω σ s * x)) ^ 2 := by
  have hd2 : 2 - σ * ω * s ≠ 0 := by intro h; apply hd; linarith
  unfold rankOneCost ratio
  congr 2
  field_simp
  ring

theorem rankOneCost_nonneg {σ ω s : ℝ} (hs : 0 ≤ s) (x y : ℝ) : 0 ≤ rankOneCost σ ω s x y :=
  mul_nonneg (div_nonneg A₀_pos.le hs) (sq_nonneg _)

/-- **Cost of the nearest target**: `E(x, y) ≤ c M⁻⁵` with `c = 9A₀/(4T)`. -/
theorem near_cost (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k < M) {x : ℝ}
    (hx : x ∈ alphabetOf T ω q₀ σ M k) :
    ∃ y ∈ alphabetOf T ω q₀ σ M (k + 1),
      rankOneCost σ ω (T / M) x y ≤ costConst T / (M : ℝ) ^ 5 := by
  obtain ⟨y, hy, hnear⟩ := near_target hT hω hq₀ hσ hM hk hx
  refine ⟨y, hy, ?_⟩
  obtain ⟨hx0, hxh⟩ := half_step_le hT hω hq₀ hM
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hd : |1 - σ * ω * (T / M) / 2| ≤ 3 / 2 := by
    rw [abs_le]; rcases hσ with rfl | rfl <;> constructor <;> nlinarith
  have hd0 : 1 - σ * ω * (T / M) / 2 ≠ 0 := by
    rcases hσ with rfl | rfl <;> nlinarith
  rw [rankOneCost_eq σ ω (T / M) x y hd0]
  have hsq : ((1 - σ * ω * (T / M) / 2) * (y - ratio ω σ (T / M) * x)) ^ 2
      ≤ (3 / 2) ^ 2 * mesh M ^ 2 := by
    rw [← mul_pow]
    apply sq_le_sq'
    · rw [abs_le] at hd hnear
      nlinarith [abs_nonneg (y - ratio ω σ (T / M) * x), mesh_pos (M := M) (by linarith)]
    · calc (1 - σ * ω * (T / M) / 2) * (y - ratio ω σ (T / M) * x)
          ≤ |(1 - σ * ω * (T / M) / 2) * (y - ratio ω σ (T / M) * x)| := le_abs_self _
        _ = |1 - σ * ω * (T / M) / 2| * |y - ratio ω σ (T / M) * x| := abs_mul _ _
        _ ≤ 3 / 2 * mesh M := mul_le_mul hd hnear (abs_nonneg _) (by norm_num)
  calc A₀ / (T / M) * ((1 - σ * ω * (T / M) / 2) * (y - ratio ω σ (T / M) * x)) ^ 2
      ≤ A₀ / (T / M) * ((3 / 2) ^ 2 * mesh M ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg A₀_pos.le (by positivity))
    _ = costConst T / (M : ℝ) ^ 5 := by
        unfold costConst mesh; field_simp; ring

/-- The explicit cylinder is well formed from `M ≥ 1` on. -/
theorem explicit_wellFormed (hT : 0 < T) {M : ℕ} (hM : 1 ≤ M) :
    (explicitCylinder T ω q₀ σ M).WellFormed := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨fun x y => rankOneCost_nonneg (by positivity) x y, ?_, ?_⟩
  · show 0 < temp M
    unfold temp
    have := Real.log_nonneg hMr
    positivity
  · show q₀ ∈ alphabetOf T ω q₀ σ M 0
    rw [alphabetOf_zero]; exact mem_singleton_self _

theorem temp_pos {M : ℕ} (hM : (1 : ℝ) ≤ M) : 0 < temp M := by
  unfold temp; have := Real.log_nonneg hM; positivity

theorem gridConst_pos (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) : 1 ≤ gridConst T ω q₀ := by
  unfold gridConst; have := growth_pos (T := T) (ω := ω); nlinarith

theorem accLower_pos (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) {M : ℕ} (hM : (1 : ℝ) ≤ M) :
    0 < accLower T ω q₀ M := by
  unfold accLower
  have := gridConst_pos hT hω hq₀
  have : 0 < (M : ℝ) := by linarith
  positivity

/-- **Row-wise acceptance lower bound** `Z_k(x) ≥ Z_M` for `x ∈ F_k`, `k < M`. -/
theorem accLower_le_totalAcceptance (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) {k : ℕ} (hk : k < M) {x : ℝ}
    (hx : x ∈ alphabetOf T ω q₀ σ M k) :
    accLower T ω q₀ M ≤ (explicitCylinder T ω q₀ σ M).totalAcceptance k x := by
  obtain ⟨y₀, hy₀, hc⟩ := near_cost hT hω hq₀ hσ hM hk hx
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hlog := Real.log_nonneg hM1
  set Cy := explicitCylinder T ω q₀ σ M
  have hcard : ((Cy.alphabet (k + 1)).card : ℝ) ≤ gridConst T ω q₀ * (M : ℝ) ^ 3 := by
    rcases card_alphabet_le hT hω hq₀ hσ hM (k := k) hk.le with h | h
    · exact h
    · omega
  have hcard0 : (0 : ℝ) < (Cy.alphabet (k + 1)).card := by
    exact_mod_cast Finset.card_pos.2 ⟨y₀, hy₀⟩
  have hexp : Real.exp (-(costConst T * (1 + Real.log M))) ≤ Cy.acceptance x y₀ := by
    show _ ≤ Real.exp (-rankOneCost σ ω (T / M) x y₀ / temp M)
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (temp_pos hM1)]
    calc rankOneCost σ ω (T / M) x y₀ ≤ costConst T / (M : ℝ) ^ 5 := hc
      _ = costConst T * (1 + Real.log M) * temp M := by
          unfold temp; field_simp
  calc accLower T ω q₀ M
      = (gridConst T ω q₀ * (M : ℝ) ^ 3)⁻¹ * Real.exp (-(costConst T * (1 + Real.log M))) := by
        unfold accLower; ring
    _ ≤ ((Cy.alphabet (k + 1)).card : ℝ)⁻¹ * Cy.acceptance x y₀ := by
        gcongr
    _ = Cy.proposal k y₀ * Cy.acceptance x y₀ := rfl
    _ ≤ Cy.totalAcceptance k x :=
        single_le_sum (f := fun y => Cy.proposal k y * Cy.acceptance x y)
          (fun y _ => mul_nonneg (AcceptRejectCylinder.proposal_nonneg k y)
            (AcceptRejectCylinder.acceptance_pos x y).le) hy₀

/-- **Retry failure** `≤ M⁻⁶`. -/
theorem explicit_failureProb_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) :
    (explicitCylinder T ω q₀ σ M).failureProb ≤ 1 / (M : ℝ) ^ 6 := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : 1 ≤ M := by exact_mod_cast hM1
  set Cy := explicitCylinder T ω q₀ σ M
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1'
  have hA := accLower_pos hT hω hq₀ hM1
  have hR : 7 * Real.log M ≤ accLower T ω q₀ M * Cy.retryCap := by
    have h := Nat.le_ceil (7 * Real.log M / accLower T ω q₀ M)
    show 7 * Real.log M ≤ accLower T ω q₀ M * (retryCapOf T ω q₀ M : ℝ)
    rw [div_le_iff₀ hA] at h
    unfold retryCapOf; linarith
  have hD : ∀ j < Cy.stages, ∀ x ∈ Cy.alphabet j, Cy.exhaustion j x ≤ 1 / (M : ℝ) ^ 7 := by
    intro j hj x hx
    have h1 := retryLaw_none_le_exp (G := Cy.alphabet (j + 1)) (p := Cy.proposal j)
      (a := Cy.acceptance x) (accLower_le_totalAcceptance hT hω hq₀ hσ hM hj hx)
      (AcceptRejectCylinder.totalAcceptance_le_one hC j x) Cy.retryCap
    refine h1.trans ?_
    calc Real.exp (-(accLower T ω q₀ M * Cy.retryCap)) ≤ Real.exp (-(7 * Real.log M)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = 1 / (M : ℝ) ^ 7 := by
          rw [Real.exp_neg, show (7 : ℝ) * Real.log M = (7 : ℕ) * Real.log M by norm_num,
            Real.exp_nat_mul, Real.exp_log hMpos, one_div]
  have := failMass_le hC.start_mem (AcceptRejectCylinder.kernel_nonneg hC)
    (fun j x _ => AcceptRejectCylinder.kernel_sum_le_one hC j x) (by positivity) Cy.stages hD
  refine this.trans (le_of_eq ?_)
  show (M : ℝ) * (1 / (M : ℝ) ^ 7) = 1 / (M : ℝ) ^ 6
  field_simp

/-- The energy constant `C_E = c + log N + 3`. -/
def energyConst (T ω q₀ : ℝ) : ℝ := costConst T + Real.log (gridConst T ω q₀) + 3

theorem energyConst_nonneg (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) : 0 ≤ energyConst T ω q₀ := by
  unfold energyConst costConst
  have := Real.log_nonneg (gridConst_pos hT hω hq₀)
  have := A₀_pos
  positivity

/-- **Entropy–energy estimate** `E[ℰ_M; success] ≤ C_E M⁻⁴` (`eq:supp-explicit-energy`). -/
theorem explicit_energy_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) :
    (explicitCylinder T ω q₀ σ M).successExpect (residualEnergy σ ω M (T / M))
      ≤ energyConst T ω q₀ / (M : ℝ) ^ 4 := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : 1 ≤ M := by exact_mod_cast hM1
  set Cy := explicitCylinder T ω q₀ σ M
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1'
  have hlogM := Real.log_nonneg hM1
  have hN := gridConst_pos hT hω hq₀
  have hlogN := Real.log_nonneg hN
  set B : ℝ := costConst T / (M : ℝ) ^ 5 + temp M * Real.log (gridConst T ω q₀ * (M : ℝ) ^ 3)
  have hc0 : 0 ≤ costConst T := by unfold costConst; have := A₀_pos; positivity
  have hB0 : 0 ≤ B := by
    have := temp_pos hM1
    have : 0 ≤ Real.log (gridConst T ω q₀ * (M : ℝ) ^ 3) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ hM1))
    positivity
  have hstep : ∀ j < Cy.stages, ∀ x ∈ Cy.alphabet j,
      ∑ y ∈ Cy.alphabet (j + 1), Cy.kernel j x y * (fun _ => rankOneCost σ ω (T / M)) j x y
        ≤ B := by
    intro j hj x hx
    obtain ⟨y₀, hy₀, hc⟩ := near_cost hT hω hq₀ hσ hM hj hx
    have h := AcceptRejectCylinder.kernel_mean_cost_le hC j x hy₀
    refine h.trans ?_
    have hcard : ((Cy.alphabet (j + 1)).card : ℝ) ≤ gridConst T ω q₀ * (M : ℝ) ^ 3 := by
      rcases card_alphabet_le hT hω hq₀ hσ hM (k := j) (le_of_lt hj) with h | h
      · exact h
      · exact absurd hj (by show ¬ j < M; omega)
    have hcard0 : (0 : ℝ) < (Cy.alphabet (j + 1)).card := by
      exact_mod_cast Finset.card_pos.2 ⟨y₀, hy₀⟩
    have hlog := Real.log_le_log hcard0 hcard
    have := temp_pos hM1
    show rankOneCost σ ω (T / M) x y₀ + temp M * Real.log (Cy.alphabet (j + 1)).card ≤ B
    exact add_le_add hc (mul_le_mul_of_nonneg_left hlog (temp_pos hM1).le)
  have h := expect_addSum_le hC.start_mem (AcceptRejectCylinder.kernel_nonneg hC)
    (fun j x _ => AcceptRejectCylinder.kernel_sum_le_one hC j x)
    (fun _ => rankOneCost σ ω (T / M)) (fun _ x y => rankOneCost_nonneg (by positivity) x y)
    (fun _ => B) (fun _ => hB0) Cy.stages hstep
  have hE : Cy.successExpect (residualEnergy σ ω M (T / M))
      = ∑ q ∈ paths Cy.alphabet Cy.start Cy.stages,
          weight Cy.kernel Cy.stages q * addSum (fun _ => rankOneCost σ ω (T / M)) Cy.stages q := by
    unfold AcceptRejectCylinder.successExpect AcceptRejectCylinder.successPaths
      AcceptRejectCylinder.pathProb
    exact sum_congr rfl fun q _ => by rw [residualEnergy_eq_addSum]; rfl
  rw [hE]
  refine h.trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  show (M : ℝ) * B ≤ energyConst T ω q₀ / (M : ℝ) ^ 4
  have hlog3 : Real.log (gridConst T ω q₀ * (M : ℝ) ^ 3) = Real.log (gridConst T ω q₀) + 3 * Real.log M := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
  have hkey : Real.log (gridConst T ω q₀) + 3 * Real.log M
      ≤ (Real.log (gridConst T ω q₀) + 3) * (1 + Real.log M) := by nlinarith
  have hMB : (M : ℝ) * B = costConst T / (M : ℝ) ^ 4
      + (Real.log (gridConst T ω q₀) + 3 * Real.log M) / (1 + Real.log M) / (M : ℝ) ^ 4 := by
    simp only [B, hlog3, temp]
    field_simp
  rw [hMB]
  have h2 : (Real.log (gridConst T ω q₀) + 3 * Real.log M) / (1 + Real.log M)
      ≤ Real.log (gridConst T ω q₀) + 3 := by
    rw [div_le_iff₀ (by linarith)]; exact hkey
  have h4 : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
  unfold energyConst
  rw [show costConst T / (M : ℝ) ^ 4 + (Real.log (gridConst T ω q₀) + 3 * Real.log M)
      / (1 + Real.log M) / (M : ℝ) ^ 4 = (costConst T + (Real.log (gridConst T ω q₀)
      + 3 * Real.log M) / (1 + Real.log M)) / (M : ℝ) ^ 4 by ring]
  apply div_le_div_of_nonneg_right _ h4.le
  linarith

end Alphabets

/-! ### Deterministic path estimates (`lem:supp-homogeneous-euler-control`) -/

section PathEstimates

variable {T ω q₀ σ : ℝ}

/-- The forced recurrence `q_{j+1} = r q_j + R_j/d`, `d = 1 − σωs/2`. -/
theorem forced_recurrence (σ ω s : ℝ) (q : ℕ → ℝ) (j : ℕ) (hd : 1 - σ * ω * s / 2 ≠ 0) :
    q (j + 1) = ratio ω σ s * q j + residual σ ω s q j / (1 - σ * ω * s / 2) := by
  have hd2 : 2 - σ * ω * s ≠ 0 := by intro h; apply hd; linarith
  unfold ratio residual
  field_simp
  ring

/-- `|R_j| ≤ R_j²/(2λs) + λs/2` summed: `Σ_{j<M} |R_j| ≤ ℰ/(2A₀λ) + λMs/2`. -/
theorem sum_abs_residual_le (σ ω : ℝ) (M : ℕ) {s : ℝ} (hs : 0 < s) (q : ℕ → ℝ) {lam : ℝ}
    (hlam : 0 < lam) :
    ∑ j ∈ range M, |residual σ ω s q j|
      ≤ residualEnergy σ ω M s q / (2 * A₀ * lam) + lam * (M * s) / 2 := by
  have hA := A₀_pos
  have hterm : ∀ j ∈ range M, |residual σ ω s q j|
      ≤ residual σ ω s q j ^ 2 / s / (2 * lam) + lam * s / 2 := by
    intro j _
    set R := residual σ ω s q j
    have h := sq_nonneg (|R| - lam * s)
    rw [div_div, div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    have : R ^ 2 = |R| ^ 2 := (sq_abs R).symm
    nlinarith
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div, residualEnergy]
  field_simp

/-- **Path control** (`eq:supp-homogeneous-path-control`): along a successful history,
`|q_j − q₀ r^j| ≤ 2Γ Σ_{i<M} |R_i|` for `j ≤ M`. -/
theorem abs_sub_stationary_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) (q : ℕ → ℝ) (hq0 : q 0 = q₀) :
    ∀ j ≤ M, |q j - q₀ * ratio ω σ (T / M) ^ j|
      ≤ 2 * growth T ω * ∑ i ∈ range M, |residual σ ω (T / M) q i| := by
  obtain ⟨hx0, hx⟩ := half_step_le hT hω hq₀ hM
  obtain ⟨hr0, -, hrmax⟩ := ratio_bounds hσ hx0.le hx
  set r := ratio ω σ (T / M)
  set ρ := max r 1
  set d := 1 - σ * ω * (T / M) / 2
  have hd : 1 / 2 ≤ d := by simp only [d]; rcases hσ with rfl | rfl <;> nlinarith
  have hd0 : d ≠ 0 := by linarith
  have hρ1 : 1 ≤ ρ := le_max_right _ _
  have hrρ : r ≤ ρ := le_max_left _ _
  -- the weighted induction `|e_j| ≤ ρ^j · 2 Σ_{i<j} |R_i|`
  have key : ∀ j, |q j - q₀ * r ^ j| ≤ ρ ^ j * (2 * ∑ i ∈ range j, |residual σ ω (T / M) q i|) := by
    intro j
    induction j with
    | zero => simp [hq0]
    | succ j ih =>
      have hrec := forced_recurrence σ ω (T / M) q j hd0
      have he : q (j + 1) - q₀ * r ^ (j + 1)
          = r * (q j - q₀ * r ^ j) + residual σ ω (T / M) q j / d := by
        rw [hrec, pow_succ]; ring
      rw [he, sum_range_succ]
      set S := ∑ i ∈ range j, |residual σ ω (T / M) q i|
      set R := residual σ ω (T / M) q j
      have hS0 : 0 ≤ S := sum_nonneg fun i _ => abs_nonneg _
      have hRd : |R / d| ≤ 2 * |R| := by
        rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < d), div_le_iff₀ (by linarith)]
        nlinarith [abs_nonneg R]
      have hρj : 1 ≤ ρ ^ (j + 1) := one_le_pow₀ hρ1
      calc |r * (q j - q₀ * r ^ j) + R / d| ≤ |r * (q j - q₀ * r ^ j)| + |R / d| := abs_add_le _ _
        _ = r * |q j - q₀ * r ^ j| + |R / d| := by rw [abs_mul, abs_of_pos hr0]
        _ ≤ ρ * (ρ ^ j * (2 * S)) + 2 * |R| := by
            gcongr
        _ ≤ ρ ^ (j + 1) * (2 * (S + |R|)) := by
            have h' : |R| ≤ ρ ^ (j + 1) * |R| := by nlinarith [abs_nonneg R]
            rw [pow_succ] at h' ⊢
            nlinarith [h']
  intro j hj
  refine (key j).trans ?_
  have hρj : ρ ^ j ≤ growth T ω := (ratio_pow_bounds hT hω hq₀ hσ hM hj).2.2.2
  have hSj : ∑ i ∈ range j, |residual σ ω (T / M) q i| ≤ ∑ i ∈ range M, |residual σ ω (T / M) q i| :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hj) fun i _ _ => abs_nonneg _
  have hS0 : 0 ≤ ∑ i ∈ range j, |residual σ ω (T / M) q i| := sum_nonneg fun i _ => abs_nonneg _
  calc ρ ^ j * (2 * ∑ i ∈ range j, |residual σ ω (T / M) q i|)
      ≤ growth T ω * (2 * ∑ i ∈ range M, |residual σ ω (T / M) q i|) := by
        apply mul_le_mul hρj (by linarith) (by linarith) (le_trans zero_le_one
          (one_le_growth hT hω))
    _ = 2 * growth T ω * ∑ i ∈ range M, |residual σ ω (T / M) q i| := by ring

/-- The profile constant `2 q₀ e^{ωT} ω³T³/9`. -/
def profileConst (T ω q₀ : ℝ) : ℝ := 2 * q₀ * Real.exp (ω * T) * (ω ^ 3 * T ^ 3 / 9)

/-- **Second-order stationary-profile estimate**: `|q₀ r^j − q₀ e^{σωτ_j}| ≤ c_P M⁻²`, `j ≤ M`
(from `FiniteHomogeneousStationarity.log_profile_error_le`). -/
theorem stationary_sub_profile_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) {j : ℕ} (hj : j ≤ M) :
    |q₀ * ratio ω σ (T / M) ^ j - stationaryProfile q₀ σ ω (j * (T / M))|
      ≤ profileConst T ω q₀ / (M : ℝ) ^ 2 := by
  obtain ⟨hx0, hx⟩ := half_step_le hT hω hq₀ hM
  obtain ⟨hM2, -, -, hω3⟩ := large_facts hT hω hq₀ hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hs : 0 < T / M := by positivity
  set r := ratio ω σ (T / M)
  have hr0 : 0 < r := (ratio_bounds hσ hx0.le hx).1
  have hrec : FiniteHomogeneousStationarity.SatisfiesRecurrence ω σ M (fun j => q₀ * r ^ j)
      (fun _ => T / M) := by
    intro i _
    refine ⟨by linarith, ?_⟩
    simp only [pow_succ, r, ratio]; ring
  have hlog := FiniteHomogeneousStationarity.log_profile_error_le ω σ (1 / 2) (T / M) hω hσ
    (by norm_num) (by norm_num) hx M (fun j => q₀ * r ^ j) (fun _ => T / M) (by simpa using hq₀)
    (fun _ _ => hs) (fun _ _ => le_rfl) hrec j hj
  have hτ : ∀ k : ℕ, FiniteHomogeneousStationarity.renewalTime (fun _ => T / M) k = k * (T / M) := by
    intro k; simp [FiniteHomogeneousStationarity.renewalTime]
  simp only [hτ, pow_zero, mul_one] at hlog
  set u := Real.log (q₀ * r ^ j / q₀) - σ * ω * (j * (T / M))
  have hlam : ω ^ 3 * (M * (T / M)) * (T / M) ^ 2 / (12 * (1 - (1 / 2) ^ 2))
      = ω ^ 3 * T ^ 3 / 9 / (M : ℝ) ^ 2 := by field_simp; ring
  rw [hlam] at hlog
  have hu1 : |u| ≤ 1 := by
    refine hlog.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (M : ℝ)]
  have hrj : q₀ * r ^ j = stationaryProfile q₀ σ ω (j * (T / M)) * Real.exp u := by
    have hpos : 0 < q₀ * r ^ j / q₀ := by positivity
    have hu : Real.exp u = (q₀ * r ^ j / q₀) / Real.exp (σ * ω * (j * (T / M))) := by
      simp only [u]; rw [Real.exp_sub, Real.exp_log hpos]
    rw [hu]; unfold stationaryProfile; field_simp
  have hprof : stationaryProfile q₀ σ ω (j * (T / M)) ≤ q₀ * Real.exp (ω * T) := by
    unfold stationaryProfile
    apply mul_le_mul_of_nonneg_left _ hq₀.le
    apply Real.exp_le_exp.2
    have hjT : (j : ℝ) * (T / M) ≤ T := by
      rw [mul_div_assoc', div_le_iff₀ hMpos]; nlinarith [(by exact_mod_cast hj : (j : ℝ) ≤ M)]
    have hj0 : 0 ≤ (j : ℝ) * (T / M) := by positivity
    rcases hσ with rfl | rfl <;> nlinarith
  have hprof0 : 0 ≤ stationaryProfile q₀ σ ω (j * (T / M)) := by
    unfold stationaryProfile; positivity
  rw [hrj, show stationaryProfile q₀ σ ω (j * (T / M)) * Real.exp u
      - stationaryProfile q₀ σ ω (j * (T / M))
      = stationaryProfile q₀ σ ω (j * (T / M)) * (Real.exp u - 1) by ring, abs_mul,
    abs_of_nonneg hprof0]
  calc stationaryProfile q₀ σ ω (j * (T / M)) * |Real.exp u - 1|
      ≤ q₀ * Real.exp (ω * T) * (2 * |u|) :=
        mul_le_mul hprof (Real.abs_exp_sub_one_le hu1) (abs_nonneg _) (by positivity)
    _ ≤ q₀ * Real.exp (ω * T) * (2 * (ω ^ 3 * T ^ 3 / 9 / (M : ℝ) ^ 2)) := by gcongr
    _ = profileConst T ω q₀ / (M : ℝ) ^ 2 := by unfold profileConst; ring

/-- **Nodal deviation** along a successful history:
`max_j |q_j − q₀ e^{σωτ_j}| ≤ 2Γ Σ_j |R_j| + c_P M⁻²`. -/
theorem maxDeviation_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) (q : ℕ → ℝ) (hq0 : q 0 = q₀) :
    maxDeviation q₀ σ ω M (T / M) q
      ≤ 2 * growth T ω * ∑ i ∈ range M, |residual σ ω (T / M) q i|
        + profileConst T ω q₀ / (M : ℝ) ^ 2 := by
  unfold maxDeviation
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hj := Nat.lt_succ_iff.1 (mem_range.1 hj)
  have h1 := abs_sub_stationary_le hT hω hq₀ hσ hM q hq0 j hj
  have h2 := stationary_sub_profile_le hT hω hq₀ hσ hM hj
  calc |q j - stationaryProfile q₀ σ ω (j * (T / M))|
      ≤ |q j - q₀ * ratio ω σ (T / M) ^ j|
        + |q₀ * ratio ω σ (T / M) ^ j - stationaryProfile q₀ σ ω (j * (T / M))| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2

/-- Expected absolute residual sum `E[Σ_j |R_j|; success] ≤ (C_E/(2A₀) + T/2) M⁻²`. -/
theorem explicit_sumAbsResidual_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) :
    (explicitCylinder T ω q₀ σ M).successExpect
        (fun q => ∑ i ∈ range M, |residual σ ω (T / M) q i|)
      ≤ (energyConst T ω q₀ / (2 * A₀) + T / 2) / (M : ℝ) ^ 2 := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1'
  have hs : 0 < T / M := by positivity
  set lam : ℝ := 1 / (M : ℝ) ^ 2
  have hlam : 0 < lam := by positivity
  have hA := A₀_pos
  calc (explicitCylinder T ω q₀ σ M).successExpect
        (fun q => ∑ i ∈ range M, |residual σ ω (T / M) q i|)
      ≤ (explicitCylinder T ω q₀ σ M).successExpect
        (fun q => (2 * A₀ * lam)⁻¹ * residualEnergy σ ω M (T / M) q + lam * (M * (T / M)) / 2) :=
        AcceptRejectCylinder.successExpect_mono hC fun q _ => by
          have := sum_abs_residual_le σ ω M hs q hlam
          calc _ ≤ _ := this
            _ = _ := by ring
    _ = (2 * A₀ * lam)⁻¹ * (explicitCylinder T ω q₀ σ M).successExpect
          (residualEnergy σ ω M (T / M))
        + (explicitCylinder T ω q₀ σ M).successExpect (fun _ => lam * (M * (T / M)) / 2) := by
        rw [AcceptRejectCylinder.successExpect_add, AcceptRejectCylinder.successExpect_const_mul]
    _ ≤ (2 * A₀ * lam)⁻¹ * (energyConst T ω q₀ / (M : ℝ) ^ 4) + lam * (M * (T / M)) / 2 := by
        gcongr
        · exact explicit_energy_le hT hω hq₀ hσ hM
        · exact AcceptRejectCylinder.successExpect_const_le hC (by positivity)
    _ = (energyConst T ω q₀ / (2 * A₀) + T / 2) / (M : ℝ) ^ 2 := by
        simp only [lam]; field_simp

/-- The deviation constant. -/
def deviationConst (T ω q₀ : ℝ) : ℝ :=
  2 * growth T ω * (energyConst T ω q₀ / (2 * A₀) + T / 2) + profileConst T ω q₀

/-- **`E[max_j |q_j − q₀ e^{σωτ_j}|; success] ≤ C M⁻²`** (`eq:main-stochastic-profile`). -/
theorem explicit_deviation_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {M : ℕ} (hM : threshold T ω q₀ ≤ M) :
    (explicitCylinder T ω q₀ σ M).successExpect (maxDeviation q₀ σ ω M (T / M))
      ≤ deviationConst T ω q₀ / (M : ℝ) ^ 2 := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1'
  have hP : 0 ≤ profileConst T ω q₀ := by unfold profileConst; positivity
  have hΓ := growth_pos (T := T) (ω := ω)
  calc (explicitCylinder T ω q₀ σ M).successExpect (maxDeviation q₀ σ ω M (T / M))
      ≤ (explicitCylinder T ω q₀ σ M).successExpect (fun q =>
          2 * growth T ω * ∑ i ∈ range M, |residual σ ω (T / M) q i|
            + profileConst T ω q₀ / (M : ℝ) ^ 2) :=
        AcceptRejectCylinder.successExpect_mono hC fun q hq =>
          maxDeviation_le hT hω hq₀ hσ hM q (mem_paths hq).1
    _ = 2 * growth T ω * (explicitCylinder T ω q₀ σ M).successExpect
          (fun q => ∑ i ∈ range M, |residual σ ω (T / M) q i|)
        + (explicitCylinder T ω q₀ σ M).successExpect (fun _ => profileConst T ω q₀ / (M : ℝ) ^ 2) := by
        rw [AcceptRejectCylinder.successExpect_add, AcceptRejectCylinder.successExpect_const_mul]
    _ ≤ 2 * growth T ω * ((energyConst T ω q₀ / (2 * A₀) + T / 2) / (M : ℝ) ^ 2)
        + profileConst T ω q₀ / (M : ℝ) ^ 2 := by
        gcongr
        · exact explicit_sumAbsResidual_le hT hω hq₀ hσ hM
        · exact AcceptRejectCylinder.successExpect_const_le hC (by positivity)
    _ = deviationConst T ω q₀ / (M : ℝ) ^ 2 := by unfold deviationConst; ring

end PathEstimates

/-! ### First variations of the finite action (`eq:supp-homogeneous-euler-bound`) -/

section FirstVariation

open FiniteHomogeneousStationarity

/-- The first variation of the finite action `S_d` (`eq:main-discrete-homogeneous-action`, with
`B₀ = A₀ω²`) at `(q, s_j ≡ s)` in the direction `(δq_j, δs_j) = (w_j, s n_j)`: the derivative
at `ε = 0` of `ε ↦ S_d(q + εw, s + ε s n)`. -/
def firstVariation (ω : ℝ) (M : ℕ) (s : ℝ) (w n q : ℕ → ℝ) : ℝ :=
  deriv (fun ε : ℝ => discreteAction A₀ (A₀ * ω ^ 2) M (fun j => q j + ε * w j)
    (fun j => s + ε * (s * n j))) 0

/-- The first variation against a scale test `φ` and a lapse test `ψ` sampled at the nodes
`τ_j = j T/M`. -/
def testVariation (ω T : ℝ) (M : ℕ) (φ ψ : ℝ → ℝ) (q : ℕ → ℝ) : ℝ :=
  firstVariation ω M (T / M) (fun j => φ (j * (T / M))) (fun j => ψ (j * (T / M))) q

/-- The derivative of one edge term along the variation line. -/
def edgeDeriv (A B s : ℝ) (q w n : ℕ → ℝ) (j : ℕ) : ℝ :=
  A * (2 * (q (j + 1) - q j) * (w (j + 1) - w j) * s - (q (j + 1) - q j) ^ 2 * (s * n j)) / s ^ 2
    + B * (s * n j * ((q j + q (j + 1)) / 2) ^ 2
      + s * (2 * ((q j + q (j + 1)) / 2) * ((w j + w (j + 1)) / 2)))

theorem hasDerivAt_edge (A B s : ℝ) (hs : s ≠ 0) (q w n : ℕ → ℝ) (j : ℕ) :
    HasDerivAt (fun ε : ℝ => edgeTerm A B (fun j => q j + ε * w j) (fun j => s + ε * (s * n j)) j)
      (edgeDeriv A B s q w n j) 0 := by
  have hD : HasDerivAt (fun ε : ℝ => s + ε * (s * n j)) (s * n j) 0 :=
    (hasDerivAt_mul_const _).const_add s
  have hdq : HasDerivAt (fun ε : ℝ => (q (j + 1) - q j) + ε * (w (j + 1) - w j))
      (w (j + 1) - w j) 0 := (hasDerivAt_mul_const _).const_add _
  have hm : HasDerivAt (fun ε : ℝ => (q j + q (j + 1)) / 2 + ε * ((w j + w (j + 1)) / 2))
      ((w j + w (j + 1)) / 2) 0 := (hasDerivAt_mul_const _).const_add _
  have h1 := ((hdq.mul hdq).const_mul A).fun_div hD (by simpa using hs)
  have h2 := (hD.const_mul B).mul (hm.mul hm)
  have h := h1.add h2
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)).congr_deriv ?_
  · simp only [Pi.add_apply, Pi.mul_apply, edgeTerm, midAmp]; ring
  · simp only [edgeDeriv, Pi.mul_apply, zero_mul, add_zero]; field_simp; ring

/-- The first variation is the explicit sum `−Σ_j edgeDeriv`. -/
theorem hasDerivAt_action_line (A B s : ℝ) (hs : s ≠ 0) (M : ℕ) (q w n : ℕ → ℝ) :
    HasDerivAt (fun ε : ℝ => discreteAction A B M (fun j => q j + ε * w j)
        (fun j => s + ε * (s * n j)))
      (-∑ j ∈ range M, edgeDeriv A B s q w n j) 0 := by
  unfold discreteAction
  exact (HasDerivAt.fun_sum fun j _ => hasDerivAt_edge A B s hs q w n j).neg

/-- The variation coefficient `β_j = (w_{j+1} − w_j)/s − σω w̄_j − σω q̄_j n_j`. -/
def variationCoeff (σ ω s : ℝ) (q w n : ℕ → ℝ) (j : ℕ) : ℝ :=
  (w (j + 1) - w j) / s - σ * ω * ((w j + w (j + 1)) / 2) - σ * ω * ((q j + q (j + 1)) / 2) * n j

/-- Per-edge square factorization of the variation (`B₀ = A₀ω²`, `σ = ±1`). -/
theorem edgeDeriv_eq (A σ ω s : ℝ) (hσ : σ = 1 ∨ σ = -1) (hs : s ≠ 0) (q w n : ℕ → ℝ) (j : ℕ) :
    edgeDeriv A (A * ω ^ 2) s q w n j
      = A * (2 * residual σ ω s q j * variationCoeff σ ω s q w n j
          - residual σ ω s q j ^ 2 * n j / s)
        + 2 * A * σ * ω * (q (j + 1) * w (j + 1) - q j * w j) := by
  rcases hσ with rfl | rfl <;>
  · simp only [edgeDeriv, residual, variationCoeff]
    field_simp
    ring

/-- **Variation bound** (`eq:supp-homogeneous-euler-bound` in `L¹` form): for endpoint-vanishing
`w` (`w_0 = w_M = 0`), `|δS_d| ≤ 2A₀ Σ_j |R_j||β_j| + ‖n‖_∞ ℰ`. -/
theorem abs_firstVariation_le (σ ω s : ℝ) (hσ : σ = 1 ∨ σ = -1) (hs : 0 < s) (M : ℕ)
    (q w n : ℕ → ℝ) (hw0 : w 0 = 0) (hwM : w M = 0) {Kb Kn : ℝ}
    (hβ : ∀ j < M, |variationCoeff σ ω s q w n j| ≤ Kb) (hn : ∀ j < M, |n j| ≤ Kn) :
    |firstVariation ω M s w n q|
      ≤ 2 * A₀ * Kb * ∑ j ∈ range M, |residual σ ω s q j| + Kn * residualEnergy σ ω M s q := by
  have hA := A₀_pos
  rw [firstVariation, (hasDerivAt_action_line A₀ (A₀ * ω ^ 2) s hs.ne' M q w n).deriv]
  have hsum : ∑ j ∈ range M, edgeDeriv A₀ (A₀ * ω ^ 2) s q w n j
      = ∑ j ∈ range M, A₀ * (2 * residual σ ω s q j * variationCoeff σ ω s q w n j
          - residual σ ω s q j ^ 2 * n j / s) := by
    simp_rw [edgeDeriv_eq A₀ σ ω s hσ hs.ne' q w n]
    have htel : ∑ x ∈ range M, 2 * A₀ * σ * ω * (q (x + 1) * w (x + 1) - q x * w x) = 0 := by
      rw [← mul_sum, sum_range_sub (fun j => q j * w j), hwM, hw0]; ring
    rw [sum_add_distrib, htel, add_zero]
  rw [hsum, abs_neg]
  have hterm : ∀ j ∈ range M, |A₀ * (2 * residual σ ω s q j * variationCoeff σ ω s q w n j
      - residual σ ω s q j ^ 2 * n j / s)|
      ≤ 2 * A₀ * Kb * |residual σ ω s q j| + Kn * (A₀ * (residual σ ω s q j ^ 2 / s)) := by
    intro j hj
    have hj := mem_range.1 hj
    set R := residual σ ω s q j
    have h1 : |2 * R * variationCoeff σ ω s q w n j| ≤ 2 * |R| * Kb := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (hβ j hj) (by positivity)
    have h2 : |R ^ 2 * n j / s| ≤ R ^ 2 / s * Kn := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg R), abs_of_pos hs, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left (hn j hj) (by positivity)
    rw [abs_mul, abs_of_pos hA]
    calc A₀ * |2 * R * variationCoeff σ ω s q w n j - R ^ 2 * n j / s|
        ≤ A₀ * (|2 * R * variationCoeff σ ω s q w n j| + |R ^ 2 * n j / s|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) hA.le
      _ ≤ A₀ * (2 * |R| * Kb + R ^ 2 / s * Kn) := by gcongr
      _ = 2 * A₀ * Kb * |R| + Kn * (A₀ * (R ^ 2 / s)) := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, residualEnergy, ← mul_sum]

variable {T ω q₀ σ : ℝ}

/-- Along a successful history and for a Lipschitz scale test vanishing at `0` and `T` and a
bounded lapse test, the variation coefficients are uniformly bounded. -/
theorem variationCoeff_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {q : ℕ → ℝ}
    (hq : q ∈ (explicitCylinder T ω q₀ σ M).successPaths) {φ ψ : ℝ → ℝ} {Kφ : NNReal}
    (hφ : LipschitzOnWith Kφ φ (Set.Icc 0 T)) (hφ0 : φ 0 = 0) {Kψ : ℝ}
    (hψ : ∀ t ∈ Set.Icc 0 T, |ψ t| ≤ Kψ) {j : ℕ} (hj : j < M) :
    |variationCoeff σ ω (T / M) q (fun j => φ (j * (T / M))) (fun j => ψ (j * (T / M))) j|
      ≤ Kφ + ω * (Kφ * T) + ω * (qUpper T ω q₀ * Kψ) := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hs : 0 < T / M := by positivity
  have hnode : ∀ k ≤ M, (k : ℝ) * (T / M) ∈ Set.Icc 0 T := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ hMpos]
    nlinarith [(by exact_mod_cast hk : (k : ℝ) ≤ M)]
  have hφb : ∀ k ≤ M, |φ (k * (T / M))| ≤ Kφ * T := by
    intro k hk
    have h := hφ.dist_le_mul _ (hnode k hk) 0 ⟨le_rfl, hT.le⟩
    rw [Real.dist_eq, Real.dist_eq, hφ0, sub_zero, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ k * (T / M) by positivity)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hnode k hk).2 Kφ.2)
  have hdiff : |(φ ((j + 1 : ℕ) * (T / M)) - φ (j * (T / M))) / (T / M)| ≤ Kφ := by
    have h := hφ.dist_le_mul _ (hnode (j + 1) hj) _ (hnode j hj.le)
    rw [Real.dist_eq, Real.dist_eq] at h
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    refine h.trans (le_of_eq ?_)
    push_cast
    rw [show ((j : ℝ) + 1) * (T / M) - j * (T / M) = T / M by ring, abs_of_pos hs]
  have hqb : ∀ k ≤ M, 0 ≤ q k ∧ q k ≤ qUpper T ω q₀ := by
    intro k hk
    have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT (M := M)
      (by exact_mod_cast (show (1 : ℝ) ≤ M by linarith))
    obtain ⟨h1, h2⟩ := alphabet_bounds hT hω hq₀ hσ hM hk (mem_alphabet hC.start_mem hq hk)
    exact ⟨(qLower_pos hq₀).le.trans h1, h2⟩
  have hψb : ∀ k ≤ M, |ψ (k * (T / M))| ≤ Kψ := fun k hk => hψ _ (hnode k hk)
  have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  unfold variationCoeff
  have hqU0 : 0 ≤ qUpper T ω q₀ := by
    unfold qUpper; have := growth_pos (T := T) (ω := ω); positivity
  have hw : |σ * ω * ((φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2)| ≤ ω * (Kφ * T) := by
    have hab : |(φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2| ≤ Kφ * T := by
      rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have := abs_add_le (φ (j * (T / M))) (φ ((j + 1 : ℕ) * (T / M)))
      have := hφb j hj.le
      have := hφb (j + 1) hj
      linarith
    rw [abs_mul, abs_mul, hσa, one_mul, abs_of_pos hω]
    exact mul_le_mul_of_nonneg_left hab hω.le
  have hqn : |σ * ω * ((q j + q (j + 1)) / 2) * ψ (j * (T / M))| ≤ ω * (qUpper T ω q₀ * Kψ) := by
    obtain ⟨h1, h2⟩ := hqb j hj.le
    obtain ⟨h3, h4⟩ := hqb (j + 1) hj
    have hqa : |(q j + q (j + 1)) / 2| ≤ qUpper T ω q₀ := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_mul, abs_mul, hσa, one_mul, abs_of_pos hω, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hqa (hψb j hj.le) (abs_nonneg _) hqU0) hω.le
  calc |(φ ((j + 1 : ℕ) * (T / M)) - φ (j * (T / M))) / (T / M)
        - σ * ω * ((φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2)
        - σ * ω * ((q j + q (j + 1)) / 2) * ψ (j * (T / M))|
      ≤ |(φ ((j + 1 : ℕ) * (T / M)) - φ (j * (T / M))) / (T / M)|
        + |σ * ω * ((φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2)|
        + |σ * ω * ((q j + q (j + 1)) / 2) * ψ (j * (T / M))| := by
        have := abs_sub (((φ ((j + 1 : ℕ) * (T / M)) - φ (j * (T / M))) / (T / M))
          - σ * ω * ((φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2))
          (σ * ω * ((q j + q (j + 1)) / 2) * ψ (j * (T / M)))
        have := abs_sub ((φ ((j + 1 : ℕ) * (T / M)) - φ (j * (T / M))) / (T / M))
          (σ * ω * ((φ (j * (T / M)) + φ ((j + 1 : ℕ) * (T / M))) / 2))
        linarith
    _ ≤ Kφ + ω * (Kφ * T) + ω * (qUpper T ω q₀ * Kψ) := by
        linarith

end FirstVariation

/-! ### Expected first variation, Borel–Cantelli, and convergence -/

section Limits

variable {T ω q₀ σ : ℝ}

/-- **Expected absolute first variation is `O(M⁻²)`** for every Lipschitz scale test vanishing at
the endpoints and every bounded lapse test (smooth tests are covered by
`ContDiffOn.exists_lipschitzOnWith`). -/
theorem explicit_firstVariation_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) {φ ψ : ℝ → ℝ} {Kφ : NNReal} (hφ : LipschitzOnWith Kφ φ (Set.Icc 0 T))
    (hφ0 : φ 0 = 0) (hφT : φ T = 0) {Kψ : ℝ} (hψ : ∀ t ∈ Set.Icc 0 T, |ψ t| ≤ Kψ) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ M, threshold T ω q₀ ≤ M →
      (explicitCylinder T ω q₀ σ M).successExpect (fun q => |testVariation ω T M φ ψ q|)
        ≤ Cφ / (M : ℝ) ^ 2 := by
  have hKψ : 0 ≤ Kψ := (abs_nonneg _).trans (hψ 0 ⟨le_rfl, hT.le⟩)
  have hqU0 : 0 ≤ qUpper T ω q₀ := by
    unfold qUpper; have := growth_pos (T := T) (ω := ω); positivity
  set Kb : ℝ := Kφ + ω * (Kφ * T) + ω * (qUpper T ω q₀ * Kψ)
  have hKb : 0 ≤ Kb := by have := Kφ.2; positivity
  have hEC := energyConst_nonneg hT hω hq₀
  have hA := A₀_pos
  refine ⟨2 * A₀ * Kb * (energyConst T ω q₀ / (2 * A₀) + T / 2) + Kψ * energyConst T ω q₀,
    by positivity, fun M hM => ?_⟩
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1' : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1'
  have hs : 0 < T / M := by positivity
  have hpt : ∀ q ∈ (explicitCylinder T ω q₀ σ M).successPaths,
      |testVariation ω T M φ ψ q| ≤ 2 * A₀ * Kb * ∑ i ∈ range M, |residual σ ω (T / M) q i|
        + Kψ * residualEnergy σ ω M (T / M) q := by
    intro q hq
    refine abs_firstVariation_le σ ω (T / M) hσ hs M q _ _ (by simpa using hφ0) ?_
      (fun j hj => variationCoeff_le hT hω hq₀ hσ hM hq hφ hφ0 hψ hj) (fun j hj => ?_)
    · show φ ((M : ℝ) * (T / M)) = 0
      rw [mul_div_cancel₀ _ hMpos.ne']; exact hφT
    · refine hψ _ ⟨by positivity, ?_⟩
      rw [mul_div_assoc', div_le_iff₀ hMpos]
      nlinarith [(by exact_mod_cast hj.le : (j : ℝ) ≤ M)]
  have hE := explicit_energy_le hT hω hq₀ hσ hM
  have hR := explicit_sumAbsResidual_le hT hω hq₀ hσ hM
  calc (explicitCylinder T ω q₀ σ M).successExpect (fun q => |testVariation ω T M φ ψ q|)
      ≤ (explicitCylinder T ω q₀ σ M).successExpect (fun q =>
          2 * A₀ * Kb * ∑ i ∈ range M, |residual σ ω (T / M) q i|
            + Kψ * residualEnergy σ ω M (T / M) q) :=
        AcceptRejectCylinder.successExpect_mono hC hpt
    _ = 2 * A₀ * Kb * (explicitCylinder T ω q₀ σ M).successExpect
          (fun q => ∑ i ∈ range M, |residual σ ω (T / M) q i|)
        + Kψ * (explicitCylinder T ω q₀ σ M).successExpect (residualEnergy σ ω M (T / M)) := by
        rw [AcceptRejectCylinder.successExpect_add, AcceptRejectCylinder.successExpect_const_mul,
          AcceptRejectCylinder.successExpect_const_mul]
    _ ≤ 2 * A₀ * Kb * ((energyConst T ω q₀ / (2 * A₀) + T / 2) / (M : ℝ) ^ 2)
        + Kψ * (energyConst T ω q₀ / (M : ℝ) ^ 4) := by gcongr
    _ ≤ 2 * A₀ * Kb * ((energyConst T ω q₀ / (2 * A₀) + T / 2) / (M : ℝ) ^ 2)
        + Kψ * (energyConst T ω q₀ / (M : ℝ) ^ 2) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ hKψ
        exact div_le_div_of_nonneg_left hEC (by positivity)
          (pow_le_pow_right₀ (by linarith) (by norm_num))
    _ = (2 * A₀ * Kb * (energyConst T ω q₀ / (2 * A₀) + T / 2) + Kψ * energyConst T ω q₀)
          / (M : ℝ) ^ 2 := by ring

/-- `|e^u − e^v| ≤ e^m |u − v|` for `u, v ≤ m`. -/
theorem abs_exp_sub_exp_le {u v m : ℝ} (hu : u ≤ m) (hv : v ≤ m) :
    |Real.exp u - Real.exp v| ≤ Real.exp m * |u - v| := by
  wlog huv : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hv hu (by linarith)
  have h1 : Real.exp u - Real.exp v = Real.exp u * (1 - Real.exp (-(u - v))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (-(u - v)) ≤ u - v := by linarith [Real.add_one_le_exp (-(u - v))]
  have h3 : 0 ≤ 1 - Real.exp (-(u - v)) := by
    have : Real.exp (-(u - v)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  rw [h1, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h3), abs_of_nonneg (by linarith)]
  exact mul_le_mul (Real.exp_le_exp.2 hu) h2 h3 (Real.exp_pos _).le

/-- `|log x − log y| ≤ |x − y|/c` for `x, y ≥ c > 0`. -/
theorem abs_log_sub_log_le {x y c : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [abs_le]
  have h1 : Real.log x - Real.log y ≤ (x - y) / y := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [sub_div, div_self hy0.ne']; exact this
  have h2 : Real.log y - Real.log x ≤ (y - x) / x := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [sub_div, div_self hx0.ne']; exact this
  have h3 : (x - y) / y ≤ |x - y| / c := by
    rcases le_total 0 (x - y) with h | h
    · rw [abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hc hy
    · exact (div_nonpos_of_nonpos_of_nonneg h hy0.le).trans (by positivity)
  have h4 : (y - x) / x ≤ |x - y| / c := by
    rcases le_total 0 (y - x) with h | h
    · rw [abs_sub_comm, abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hc hx
    · exact (div_nonpos_of_nonpos_of_nonneg h hx0.le).trans (by positivity)
  constructor <;> linarith

/-- The nodal error bound `2Γ(1/(2A₀) + T/2)/M + c_P/M²` on a good history. -/
def nodalErr (T ω q₀ : ℝ) (M : ℕ) : ℝ :=
  2 * growth T ω * (1 / (2 * A₀) + T / 2) / M + profileConst T ω q₀ / (M : ℝ) ^ 2

/-- The amplitude error bound on the cells: nodal error plus `q₀ ω e^{ωT} T/M`. -/
def ampErr (T ω q₀ : ℝ) (M : ℕ) : ℝ :=
  nodalErr T ω q₀ M + q₀ * ω * Real.exp (ω * T) * (T / M)

/-- The slope error bound on the cells. -/
def slopeErr (T ω q₀ : ℝ) (M : ℕ) : ℝ :=
  ω * ampErr T ω q₀ M + Real.sqrt (1 / (A₀ * T) / M)

theorem hasDerivAt_stationaryProfile (q₀ σ ω t : ℝ) :
    HasDerivAt (stationaryProfile q₀ σ ω) (σ * ω * stationaryProfile q₀ σ ω t) t := by
  unfold stationaryProfile
  have h := ((hasDerivAt_id t).const_mul (σ * ω)).exp.const_mul q₀
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => by simp)).congr_deriv ?_
  simp only [id]; ring

/-- **Deterministic estimates on a good history** (`ℰ_M ≤ M⁻²`): nodal, uniform, slope and
logarithmic errors. -/
theorem good_history_estimates (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) {q : ℕ → ℝ}
    (hq : q ∈ (explicitCylinder T ω q₀ σ M).successPaths)
    (hE : residualEnergy σ ω M (T / M) q ≤ 1 / (M : ℝ) ^ 2) :
    (∀ t ∈ Set.Icc 0 T, |PiecewiseAffine.affineInterp M (T / M) q t - stationaryProfile q₀ σ ω t| ≤ ampErr T ω q₀ M)
    ∧ PiecewiseAffine.h1DistSq (PiecewiseAffine.affineInterp M (T / M) q) (stationaryProfile q₀ σ ω) 0 T
        ≤ T * (ampErr T ω q₀ M ^ 2 + slopeErr T ω q₀ M ^ 2)
    ∧ (∀ j ≤ M, |Real.log (q j) - Real.log q₀ - σ * ω * (j * (T / M))|
        ≤ nodalErr T ω q₀ M / qLower T ω q₀)
    ∧ (∀ j ≤ M, qLower T ω q₀ ≤ q j) := by
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1
  have hs : 0 < T / M := by positivity
  have hA := A₀_pos
  have hΓ := growth_pos (T := T) (ω := ω)
  have hq0 : q 0 = q₀ := (mem_paths hq).1
  have hqb : ∀ k ≤ M, qLower T ω q₀ ≤ q k := fun k hk =>
    (alphabet_bounds hT hω hq₀ hσ hM hk (mem_alphabet hC.start_mem hq hk)).1
  -- the residual sum on a good history
  have hsum : ∑ i ∈ range M, |residual σ ω (T / M) q i| ≤ (1 / (2 * A₀) + T / 2) / M := by
    have h := sum_abs_residual_le σ ω M hs q (lam := 1 / M) (by positivity)
    refine h.trans ?_
    have : residualEnergy σ ω M (T / M) q / (2 * A₀ * (1 / M)) ≤ (1 / (M : ℝ) ^ 2) / (2 * A₀ * (1 / M)) :=
      div_le_div_of_nonneg_right hE (by positivity)
    calc residualEnergy σ ω M (T / M) q / (2 * A₀ * (1 / M)) + 1 / M * (M * (T / M)) / 2
        ≤ (1 / (M : ℝ) ^ 2) / (2 * A₀ * (1 / M)) + 1 / M * (M * (T / M)) / 2 := by linarith
      _ = (1 / (2 * A₀) + T / 2) / M := by field_simp
  -- nodal errors
  have hnode : ∀ j ≤ M, |q j - stationaryProfile q₀ σ ω (j * (T / M))| ≤ nodalErr T ω q₀ M := by
    intro j hj
    have h1 := abs_sub_stationary_le hT hω hq₀ hσ hM q hq0 j hj
    have h2 := stationary_sub_profile_le hT hω hq₀ hσ hM hj
    calc |q j - stationaryProfile q₀ σ ω (j * (T / M))|
        ≤ |q j - q₀ * ratio ω σ (T / M) ^ j|
          + |q₀ * ratio ω σ (T / M) ^ j - stationaryProfile q₀ σ ω (j * (T / M))| :=
          abs_sub_le _ _ _
      _ ≤ 2 * growth T ω * ((1 / (2 * A₀) + T / 2) / M) + profileConst T ω q₀ / (M : ℝ) ^ 2 := by
          gcongr; exact h1.trans (by gcongr)
      _ = nodalErr T ω q₀ M := by unfold nodalErr; ring
  -- Lipschitz bound for the profile on `[0, T]`
  have hlip : ∀ a ∈ Set.Icc 0 T, ∀ b ∈ Set.Icc 0 T,
      |stationaryProfile q₀ σ ω a - stationaryProfile q₀ σ ω b|
        ≤ q₀ * ω * Real.exp (ω * T) * |a - b| := by
    intro a ha b hb
    have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    have hbd : ∀ c ∈ Set.Icc 0 T, σ * ω * c ≤ ω * T := by
      intro c hc
      rcases hσ with rfl | rfl
      · nlinarith [hc.1, hc.2]
      · nlinarith [hc.1, hc.2]
    unfold stationaryProfile
    rw [← mul_sub, abs_mul, abs_of_pos hq₀]
    have := abs_exp_sub_exp_le (hbd a ha) (hbd b hb)
    rw [show σ * ω * a - σ * ω * b = σ * ω * (a - b) by ring, abs_mul, abs_mul, hσa, one_mul,
      abs_of_pos hω] at this
    calc q₀ * |Real.exp (σ * ω * a) - Real.exp (σ * ω * b)|
        ≤ q₀ * (Real.exp (ω * T) * (ω * |a - b|)) := mul_le_mul_of_nonneg_left this hq₀.le
      _ = q₀ * ω * Real.exp (ω * T) * |a - b| := by ring
  have hcellnode : ∀ j < M, ∀ t ∈ Set.Icc ((j : ℝ) * (T / M)) (((j : ℝ) + 1) * (T / M)),
      t ∈ Set.Icc 0 T ∧ (j : ℝ) * (T / M) ∈ Set.Icc 0 T ∧ ((j + 1 : ℕ) : ℝ) * (T / M) ∈ Set.Icc 0 T
        ∧ |t - j * (T / M)| ≤ T / M ∧ |t - ((j + 1 : ℕ) : ℝ) * (T / M)| ≤ T / M := by
    intro j hj t ht
    have hjM : ((j : ℝ) + 1) ≤ M := by exact_mod_cast hj
    have hup : ((j : ℝ) + 1) * (T / M) ≤ T := by
      rw [mul_div_assoc', div_le_iff₀ hMpos]; nlinarith
    have hj0 : 0 ≤ (j : ℝ) * (T / M) := by positivity
    push_cast
    refine ⟨⟨hj0.trans ht.1, ht.2.trans hup⟩, ⟨hj0, by nlinarith [ht.1, ht.2]⟩,
      ⟨by positivity, hup⟩, ?_, ?_⟩
    · rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
    · rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
  have hA' : ∀ j < M, ∀ t ∈ Set.Icc ((j : ℝ) * (T / M)) (((j : ℝ) + 1) * (T / M)),
      |q j - stationaryProfile q₀ σ ω t| ≤ ampErr T ω q₀ M ∧
        |q (j + 1) - stationaryProfile q₀ σ ω t| ≤ ampErr T ω q₀ M := by
    intro j hj t ht
    obtain ⟨htT, hjT, hj1T, hd1, hd2⟩ := hcellnode j hj t ht
    have hexp0 : 0 ≤ q₀ * ω * Real.exp (ω * T) := by positivity
    constructor
    · calc |q j - stationaryProfile q₀ σ ω t|
          ≤ |q j - stationaryProfile q₀ σ ω (j * (T / M))|
            + |stationaryProfile q₀ σ ω (j * (T / M)) - stationaryProfile q₀ σ ω t| :=
            abs_sub_le _ _ _
        _ ≤ nodalErr T ω q₀ M + q₀ * ω * Real.exp (ω * T) * (T / M) := by
            gcongr
            · exact hnode j hj.le
            · refine (hlip _ hjT _ htT).trans ?_
              rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hd1 hexp0
        _ = ampErr T ω q₀ M := rfl
    · calc |q (j + 1) - stationaryProfile q₀ σ ω t|
          ≤ |q (j + 1) - stationaryProfile q₀ σ ω ((j + 1 : ℕ) * (T / M))|
            + |stationaryProfile q₀ σ ω ((j + 1 : ℕ) * (T / M)) - stationaryProfile q₀ σ ω t| :=
            abs_sub_le _ _ _
        _ ≤ nodalErr T ω q₀ M + q₀ * ω * Real.exp (ω * T) * (T / M) := by
            gcongr
            · exact hnode (j + 1) hj
            · refine (hlip _ hj1T _ htT).trans ?_
              rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hd2 hexp0
        _ = ampErr T ω q₀ M := rfl
  -- slope errors
  have hB' : ∀ j < M, ∀ t ∈ Set.Icc ((j : ℝ) * (T / M)) (((j : ℝ) + 1) * (T / M)),
      |(q (j + 1) - q j) / (T / M) - σ * ω * stationaryProfile q₀ σ ω t| ≤ slopeErr T ω q₀ M := by
    intro j hj t ht
    obtain ⟨h1, h2⟩ := hA' j hj t ht
    set R := residual σ ω (T / M) q j
    have hv : (q (j + 1) - q j) / (T / M) - σ * ω * stationaryProfile q₀ σ ω t
        = σ * ω * ((q j - stationaryProfile q₀ σ ω t + (q (j + 1) - stationaryProfile q₀ σ ω t)) / 2)
          + R / (T / M) := by
      simp only [R, residual]; field_simp; ring
    have hσa : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    have hR2 : R ^ 2 ≤ (T / M) * (1 / (M : ℝ) ^ 2) / A₀ := by
      have hsingle : A₀ * (R ^ 2 / (T / M)) ≤ residualEnergy σ ω M (T / M) q := by
        unfold residualEnergy
        apply mul_le_mul_of_nonneg_left _ hA.le
        exact single_le_sum (f := fun i => residual σ ω (T / M) q i ^ 2 / (T / M))
          (fun i _ => div_nonneg (sq_nonneg _) hs.le) (mem_range.2 hj)
      rw [le_div_iff₀ hA]
      have := hsingle.trans hE
      rw [mul_div_assoc', div_le_iff₀ hs] at this
      linarith
    have hRs : |R / (T / M)| ≤ Real.sqrt (1 / (A₀ * T) / M) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc R ^ 2 ≤ (T / M) * (1 / (M : ℝ) ^ 2) / A₀ := hR2
        _ = 1 / (A₀ * T) / M * (T / M) ^ 2 := by field_simp
    rw [hv]
    calc |σ * ω * ((q j - stationaryProfile q₀ σ ω t
            + (q (j + 1) - stationaryProfile q₀ σ ω t)) / 2) + R / (T / M)|
        ≤ |σ * ω * ((q j - stationaryProfile q₀ σ ω t
            + (q (j + 1) - stationaryProfile q₀ σ ω t)) / 2)| + |R / (T / M)| := abs_add_le _ _
      _ ≤ ω * ampErr T ω q₀ M + Real.sqrt (1 / (A₀ * T) / M) := by
          gcongr
          rw [abs_mul, abs_mul, hσa, one_mul, abs_of_pos hω]
          apply mul_le_mul_of_nonneg_left _ hω.le
          rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          have := abs_add_le (q j - stationaryProfile q₀ σ ω t)
            (q (j + 1) - stationaryProfile q₀ σ ω t)
          linarith
      _ = slopeErr T ω q₀ M := rfl
  obtain ⟨hsup, -, hh1⟩ := PiecewiseAffine.affineInterp_sup_le_and_h1DistSq_le hs hM1 q
    (hasDerivAt_stationaryProfile q₀ σ ω) hA' hB'
  have hMT : (M : ℝ) * (T / M) = T := by field_simp
  rw [hMT] at hsup hh1
  refine ⟨fun t ht => hsup t ht, hh1, fun j hj => ?_, hqb⟩
  -- logarithmic nodal error
  have hqL := qLower_pos hq₀ (T := T) (ω := ω)
  have hprofL : qLower T ω q₀ ≤ stationaryProfile q₀ σ ω (j * (T / M)) := by
    unfold qLower stationaryProfile growth
    have hjT : (j : ℝ) * (T / M) ≤ T := by
      rw [mul_div_assoc', div_le_iff₀ hMpos]; nlinarith [(by exact_mod_cast hj : (j : ℝ) ≤ M)]
    have hj0 : 0 ≤ (j : ℝ) * (T / M) := by positivity
    have hlow : -(ω * T) ≤ σ * ω * (j * (T / M)) := by
      rcases hσ with rfl | rfl <;> nlinarith
    have h1 : Real.exp (-(ω * T)) ≤ Real.exp (σ * ω * (j * (T / M))) := Real.exp_le_exp.2 hlow
    have h2 : 1 / (4 * Real.exp (2 * ω * T)) ≤ Real.exp (-(ω * T)) := by
      rw [div_le_iff₀ (by positivity), Real.exp_neg, inv_mul_eq_div,
        le_div_iff₀ (Real.exp_pos _)]
      have : Real.exp (ω * T) ≤ Real.exp (2 * ω * T) := Real.exp_le_exp.2 (by nlinarith)
      nlinarith [Real.exp_pos (ω * T)]
    calc q₀ / (4 * Real.exp (2 * ω * T)) = q₀ * (1 / (4 * Real.exp (2 * ω * T))) := by ring
      _ ≤ q₀ * Real.exp (σ * ω * (j * (T / M))) := by
          apply mul_le_mul_of_nonneg_left (h2.trans h1) hq₀.le
  have hlogprof : Real.log (stationaryProfile q₀ σ ω (j * (T / M)))
      = Real.log q₀ + σ * ω * (j * (T / M)) := by
    unfold stationaryProfile
    rw [Real.log_mul hq₀.ne' (Real.exp_pos _).ne', Real.log_exp]
  have := abs_log_sub_log_le hqL (hqb j hj) hprofL
  rw [hlogprof] at this
  calc |Real.log (q j) - Real.log q₀ - σ * ω * (j * (T / M))|
      = |Real.log (q j) - (Real.log q₀ + σ * ω * (j * (T / M)))| := by ring_nf
    _ ≤ |q j - stationaryProfile q₀ σ ω (j * (T / M))| / qLower T ω q₀ := this
    _ ≤ nodalErr T ω q₀ M / qLower T ω q₀ := div_le_div_of_nonneg_right (hnode j hj) hqL.le

theorem nodalErr_tendsto : Tendsto (nodalErr T ω q₀) atTop (𝓝 0) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (2 * growth T ω * (1 / (2 * A₀) + T / 2))
  have h2 : Tendsto (fun M : ℕ => profileConst T ω q₀ / (M : ℝ) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (profileConst T ω q₀)).mul
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simp only [mul_zero] at this
    refine this.congr fun M => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · field_simp
  have h := h1.add h2
  rw [zero_add] at h
  exact h

theorem ampErr_tendsto : Tendsto (ampErr T ω q₀) atTop (𝓝 0) := by
  have h := (nodalErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).add
    ((tendsto_const_div_atTop_nhds_zero_nat T).const_mul (q₀ * ω * Real.exp (ω * T)))
  rw [mul_zero, zero_add] at h
  exact h

theorem slopeErr_tendsto : Tendsto (slopeErr T ω q₀) atTop (𝓝 0) := by
  have h1 := (ampErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).const_mul ω
  have h2 := (tendsto_const_div_atTop_nhds_zero_nat (1 / (A₀ * T))).sqrt
  rw [mul_zero] at h1
  rw [Real.sqrt_zero] at h2
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-! ### Borel–Cantelli under an arbitrary coupling -/

/-- The path of an outcome (`0` on failure). -/
def pathOf (o : Option (ℕ → ℝ)) : ℕ → ℝ := o.getD 0

/-- The good outcomes at cutoff `M`: success with `ℰ_M ≤ M⁻²`. -/
def goodOutcomes (T ω q₀ σ : ℝ) (M : ℕ) : Set (Option (ℕ → ℝ)) :=
  {o | ∃ q ∈ (explicitCylinder T ω q₀ σ M).successPaths, o = some q ∧
    residualEnergy σ ω M (T / M) q ≤ 1 / (M : ℝ) ^ 2}

/-- The bad outcomes have probability at most `(1 + C_E)/M²` (failure `≤ M⁻⁶` plus Markov's
inequality for `ℰ_M`). -/
theorem outcomeLaw_bad_le (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {M : ℕ} (hM : threshold T ω q₀ ≤ M) :
    (explicitCylinder T ω q₀ σ M).outcomeLaw (goodOutcomes T ω q₀ σ M)ᶜ
      ≤ (1 + energyConst T ω q₀) / (M : ℝ) ^ 2 := by
  classical
  have hM2 := (large_facts hT hω hq₀ hM).1
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1
  set Cy := explicitCylinder T ω q₀ σ M
  have hnone : (none : Option (ℕ → ℝ)) ∈ (goodOutcomes T ω q₀ σ M)ᶜ := by
    rintro ⟨q, -, h, -⟩; exact Option.some_ne_none q h.symm
  have hE2 : ∑ q ∈ Cy.successPaths, Cy.pathProb q * residualEnergy σ ω M (T / M) q
      ≤ energyConst T ω q₀ / (M : ℝ) ^ 4 := explicit_energy_le hT hω hq₀ hσ hM
  have h3 := explicit_failureProb_le hT hω hq₀ hσ hM
  have hEC := energyConst_nonneg hT hω hq₀
  have h4 : (M : ℝ) ^ 2 * (energyConst T ω q₀ / (M : ℝ) ^ 4) = energyConst T ω q₀ / (M : ℝ) ^ 2 := by
    field_simp
  have h5 : 1 / (M : ℝ) ^ 6 ≤ 1 / (M : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
  unfold AcceptRejectCylinder.outcomeLaw
  rw [if_pos hnone]
  refine le_trans (add_le_add (sum_le_sum
    (g := fun q => (M : ℝ) ^ 2 * (Cy.pathProb q * residualEnergy σ ω M (T / M) q))
    fun q hq => ?_) h3) ?_
  · have hw := AcceptRejectCylinder.pathProb_nonneg hC q
    have hE0 := residualEnergy_nonneg σ ω M (by positivity : (0:ℝ) ≤ T / M) q
    split_ifs with hbad
    · have hlt : 1 / (M : ℝ) ^ 2 < residualEnergy σ ω M (T / M) q := by
        by_contra hle
        exact hbad ⟨q, hq, rfl, not_lt.1 hle⟩
      have : 1 ≤ (M : ℝ) ^ 2 * residualEnergy σ ω M (T / M) q := by
        rw [div_lt_iff₀ (by positivity)] at hlt; linarith
      nlinarith
    · positivity
  · rw [← mul_sum]
    calc (M : ℝ) ^ 2 * ∑ q ∈ Cy.successPaths, Cy.pathProb q * residualEnergy σ ω M (T / M) q
          + 1 / (M : ℝ) ^ 6
        ≤ (M : ℝ) ^ 2 * (energyConst T ω q₀ / (M : ℝ) ^ 4) + 1 / (M : ℝ) ^ 6 := by gcongr
      _ ≤ (1 + energyConst T ω q₀) / (M : ℝ) ^ 2 := by rw [h4, add_div]; linarith

/-- **Borel–Cantelli under any common coupling.**  If the `M`-th cutoff outcome `O M` has the law of
the explicit cylinder (for `M ≥ M₀`), then almost surely, for all large `M`, the history succeeds
and has residual energy at most `M⁻²`. -/
theorem explicit_coupling_good (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (O : ℕ → Ω → Option (ℕ → ℝ))
    (hlaw : ∀ M, threshold T ω q₀ ≤ M → ∀ S,
      P (O M ⁻¹' S) = ENNReal.ofReal ((explicitCylinder T ω q₀ σ M).outcomeLaw S)) :
    ∀ᵐ x ∂P, ∀ᶠ M in atTop, O M x ∈ goodOutcomes T ω q₀ σ M := by
  classical
  set bad : ℕ → Set Ω := fun M =>
    if threshold T ω q₀ ≤ M then O M ⁻¹' (goodOutcomes T ω q₀ σ M)ᶜ else ∅
  set b : ℕ → ℝ := fun M => (1 + energyConst T ω q₀) * (1 / (M : ℝ) ^ 2)
  have hb0 : ∀ M, 0 ≤ b M := fun M => by
    have := energyConst_nonneg hT hω hq₀; simp only [b]; positivity
  have hbs : Summable b := (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left _
  have hle : ∀ M, P (bad M) ≤ ENNReal.ofReal (b M) := by
    intro M
    simp only [bad]
    split_ifs with hM
    · rw [hlaw M hM]
      apply ENNReal.ofReal_le_ofReal
      refine (outcomeLaw_bad_le hT hω hq₀ hσ hM).trans (le_of_eq ?_)
      simp only [b]; ring
    · simp
  have hsum : ∑' M, P (bad M) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg hb0 hbs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx, eventually_ge_atTop (threshold T ω q₀)] with M hM hMth
  simp only [bad, if_pos hMth, Set.mem_preimage, Set.mem_compl_iff, not_not] at hM
  exact hM

/-! ### The attached `A₃` root race -/

/-- The proper-time conductance `κ_j = q_j^{−4/3}`. -/
def rootConductance (q : ℕ → ℝ) (j : ℕ) : ℝ := q j ^ (-(4 / 3 : ℝ))

/-- The root rate `k_{α,h,j} = κ_j/(8h²)` (`eq:main-stochastic-root-rates`). -/
def rootRateOf (q : ℕ → ℝ) (j : ℕ) (h : ℝ) : ℝ := rootConductance q j / (8 * h ^ 2)

/-- The vertex mass `m_{h,j} = ϱ_j h³ = q_j² h³` (`eq:main-stochastic-root-rates`). -/
def vertexMassOf (q : ℕ → ℝ) (j : ℕ) (h : ℝ) : ℝ := q j ^ 2 * h ^ 3

/-- The predictable spatial bracket of the twelve `A₃` jumps `hα` at rate `k`. -/
def rootBracketOf (q : ℕ → ℝ) (j : ℕ) (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (rootRateOf q j h * h ^ 2) • ∑ r, Matrix.vecMulVec (a3Roots r) (a3Roots r)

/-- The `A₃` root identity gives `𝓑_j = κ_j I`. -/
theorem rootBracketOf_eq (q : ℕ → ℝ) (j : ℕ) {h : ℝ} (hh : h ≠ 0) :
    rootBracketOf q j h = rootConductance q j • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [rootBracketOf, relational_flat_vacuum.1, smul_smul]
  congr 1
  unfold rootRateOf
  field_simp

/-- The log of the normalized reconstructed spatial scale `κ_j⁻¹/κ⁻¹(q₀)` is `(4/3) log(q_j/q₀)`. -/
theorem log_inv_rootConductance (q : ℕ → ℝ) (j : ℕ) (hq : 0 < q j) (hq₀ : 0 < q₀) :
    Real.log (rootConductance q j)⁻¹ - Real.log (q₀ ^ (4 / 3 : ℝ))
      = 4 / 3 * (Real.log (q j) - Real.log q₀) := by
  unfold rootConductance
  rw [Real.log_inv, Real.log_rpow hq, Real.log_rpow hq₀]
  ring

end Limits

/-! ### Almost-sure convergence and the main theorem -/

section Main

variable {T ω q₀ σ : ℝ}

theorem h1DistSq_nonneg' (f g : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ PiecewiseAffine.h1DistSq f g 0 T :=
  add_nonneg (intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _)
    (intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _)

/-- **Almost-sure convergence under any common coupling of the cutoffs.**  Failures occur only
finitely often, `ℰ_M → 0`, the successful piecewise-affine paths converge uniformly and in
`H¹(0,T)` to `q₀ e^{σωt}`, and the attached `A₃` root-race regulators are positive, have bracket
`κ_j I`, and their normalized spatial scale `log(κ_j⁻¹/q₀^{4/3})` converges uniformly in `j` to
`2Hτ_j`, `H = 2σω/3`. -/
theorem explicit_coupling_ae (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) (hσ : σ = 1 ∨ σ = -1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (O : ℕ → Ω → Option (ℕ → ℝ))
    (hlaw : ∀ M, threshold T ω q₀ ≤ M → ∀ S,
      P (O M ⁻¹' S) = ENNReal.ofReal ((explicitCylinder T ω q₀ σ M).outcomeLaw S)) :
    ∀ᵐ x ∂P,
      (∀ᶠ M in atTop, ∃ q ∈ (explicitCylinder T ω q₀ σ M).successPaths, O M x = some q) ∧
      Tendsto (fun M : ℕ => residualEnergy σ ω M (T / M) (pathOf (O M x))) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun M : ℕ => PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x)))
        (stationaryProfile q₀ σ ω) atTop (Set.Icc 0 T) ∧
      Tendsto (fun M : ℕ => PiecewiseAffine.h1DistSq
        (PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x))) (stationaryProfile q₀ σ ω) 0 T)
        atTop (𝓝 0) ∧
      (∀ᶠ M in atTop, ∀ j ≤ M, ∀ h : ℝ, 0 < h →
        0 < rootRateOf (pathOf (O M x)) j h ∧ 0 < vertexMassOf (pathOf (O M x)) j h ∧
        rootBracketOf (pathOf (O M x)) j h
          = rootConductance (pathOf (O M x)) j • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
      (∀ η > 0, ∀ᶠ M in atTop, ∀ j ≤ M,
        |Real.log (rootConductance (pathOf (O M x)) j)⁻¹ - Real.log (q₀ ^ (4 / 3 : ℝ))
          - 2 * (2 * σ * ω / 3) * (j * (T / M))| ≤ η) := by
  filter_upwards [explicit_coupling_good hT hω hq₀ hσ P O hlaw] with x hx
  have hgood : ∀ᶠ M in atTop, threshold T ω q₀ ≤ M ∧
      ∃ q ∈ (explicitCylinder T ω q₀ σ M).successPaths, O M x = some q ∧
        residualEnergy σ ω M (T / M) q ≤ 1 / (M : ℝ) ^ 2 := by
    filter_upwards [hx, eventually_ge_atTop (threshold T ω q₀)] with M hM hMth
    exact ⟨hMth, hM⟩
  have hest : ∀ᶠ M in atTop, threshold T ω q₀ ≤ M ∧
      (∃ q ∈ (explicitCylinder T ω q₀ σ M).successPaths, O M x = some q) ∧
      residualEnergy σ ω M (T / M) (pathOf (O M x)) ≤ 1 / (M : ℝ) ^ 2 ∧
      (∀ t ∈ Set.Icc 0 T, |PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x)) t
        - stationaryProfile q₀ σ ω t| ≤ ampErr T ω q₀ M) ∧
      PiecewiseAffine.h1DistSq (PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x)))
        (stationaryProfile q₀ σ ω) 0 T ≤ T * (ampErr T ω q₀ M ^ 2 + slopeErr T ω q₀ M ^ 2) ∧
      (∀ j ≤ M, |Real.log (pathOf (O M x) j) - Real.log q₀ - σ * ω * (j * (T / M))|
        ≤ nodalErr T ω q₀ M / qLower T ω q₀) ∧
      (∀ j ≤ M, qLower T ω q₀ ≤ pathOf (O M x) j) := by
    filter_upwards [hgood] with M ⟨hMth, q, hq, hO, hE⟩
    have hp : pathOf (O M x) = q := by rw [hO]; rfl
    rw [hp]
    exact ⟨hMth, ⟨q, hq, hO⟩, hE, good_history_estimates hT hω hq₀ hσ hMth hq hE⟩
  have hqL := qLower_pos hq₀ (T := T) (ω := ω)
  refine ⟨hest.mono fun M h => h.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ℰ_M → 0`
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with M hM
      exact residualEnergy_nonneg σ ω M (by positivity) _
    · filter_upwards [hest] with M hM
      have hM1 : (1 : ℝ) ≤ M := by
        have := (large_facts hT hω hq₀ hM.1).1; linarith
      refine hM.2.2.1.trans ?_
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · -- uniform convergence
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hest, (ampErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).eventually
      (gt_mem_nhds hε)] with M hM hA t ht
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hM.2.2.2.1 t ht) hA
  · -- `H¹` convergence
    have hlim : Tendsto (fun M : ℕ => T * (ampErr T ω q₀ M ^ 2 + slopeErr T ω q₀ M ^ 2)) atTop
        (𝓝 0) := by
      have := (((ampErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).pow 2).add
        ((slopeErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).pow 2)).const_mul T
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun M => h1DistSq_nonneg' _ _ hT.le) ?_
    filter_upwards [hest] with M hM
    exact hM.2.2.2.2.1
  · -- positive regulators and the `A₃` bracket
    filter_upwards [hest] with M hM j hj h hh
    have hqj : 0 < pathOf (O M x) j := hqL.trans_le (hM.2.2.2.2.2.2 j hj)
    have hκ : 0 < rootConductance (pathOf (O M x)) j := Real.rpow_pos_of_pos hqj _
    refine ⟨by unfold rootRateOf; positivity, by unfold vertexMassOf; positivity,
      rootBracketOf_eq _ j hh.ne'⟩
  · -- logarithmic convergence of the regulators
    intro η hη
    have hev := (nodalErr_tendsto (T := T) (ω := ω) (q₀ := q₀)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 3 / 4 * η * qLower T ω q₀ by positivity))
    filter_upwards [hest, hev] with M hM hN j hj
    have hqj : 0 < pathOf (O M x) j := hqL.trans_le (hM.2.2.2.2.2.2 j hj)
    rw [show Real.log (rootConductance (pathOf (O M x)) j)⁻¹ - Real.log (q₀ ^ (4 / 3 : ℝ))
        - 2 * (2 * σ * ω / 3) * (j * (T / M))
        = 4 / 3 * (Real.log (pathOf (O M x) j) - Real.log q₀ - σ * ω * (j * (T / M))) by
      rw [log_inv_rootConductance _ j hqj hq₀]; ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    have h1 := hM.2.2.2.2.2.1 j hj
    have h2 : nodalErr T ω q₀ M / qLower T ω q₀ ≤ 3 / 4 * η := by
      rw [div_le_iff₀ hqL]; exact hN
    nlinarith

/-- The cosmological constant of the limit: `Λ = 3H² = 4ω²/3` for `H = 2σω/3`, `σ = ±1`. -/
theorem limit_cosmological_constant (hσ : σ = 1 ∨ σ = -1) :
    RelationalDeSitterBranch.cosmologicalCoefficient (2 * σ * ω / 3) = 4 * ω ^ 2 / 3 := by
  unfold RelationalDeSitterBranch.cosmologicalCoefficient
  rcases hσ with rfl | rfl <;> ring

/-- **`thm:main-explicit-operational-family`** (statement).  For `T, ω, q₀ > 0` and `σ = ±1`
there are genuinely finite accept/reject cylinders (`M` stages, finite positive proposal
alphabets with `F₀ = {q₀}`, calibrated step `T/M`, rank-one costs, positive temperature, finite
retry cap; the outcome law is a probability law) and constants independent of `M` such that, for
`M ≥ M₀`: the retry failure is at most `M⁻⁶`; `E[ℰ_M; success] ≤ C M⁻⁴` and
`E[max_j |q_j − q₀e^{σωτ_j}|; success] ≤ C M⁻²` (and the same bounds with `2C` conditionally on
success); the expected absolute first variation of `S_d` against every fixed Lipschitz scale test
vanishing at `0, T` and every bounded lapse test is `O(M⁻²)`; under any common coupling the
conclusions of `explicit_coupling_ae` hold almost surely; and the limiting de Sitter regulator
with `H = 2σω/3` solves the Einstein equation with `Λ = 3H² = 4ω²/3`. -/
def ExplicitOperationalFamilyStatement.{u} (T ω q₀ σ : ℝ) : Prop :=
  ∃ (cyl : ℕ → AcceptRejectCylinder) (M₀ : ℕ) (C : ℝ), 1 ≤ M₀ ∧ 0 ≤ C ∧
    (∀ M, M₀ ≤ M →
      (cyl M).stages = M ∧ (cyl M).step = T / M ∧ (cyl M).start = q₀ ∧
      (cyl M).alphabet 0 = {q₀} ∧
      (∀ j ≤ M, (cyl M).alphabet j |>.Nonempty) ∧ (∀ j ≤ M, ∀ x ∈ (cyl M).alphabet j, 0 < x) ∧
      (cyl M).cost = rankOneCost σ ω (T / M) ∧ (cyl M).WellFormed ∧
      (cyl M).outcomeLaw Set.univ = 1 ∧
      (cyl M).failureProb ≤ 1 / (M : ℝ) ^ 6 ∧
      (cyl M).successExpect (residualEnergy σ ω M (T / M)) ≤ C / (M : ℝ) ^ 4 ∧
      (cyl M).successExpect (maxDeviation q₀ σ ω M (T / M)) ≤ C / (M : ℝ) ^ 2 ∧
      (cyl M).successExpect (residualEnergy σ ω M (T / M)) / (1 - (cyl M).failureProb)
        ≤ 2 * C / (M : ℝ) ^ 4 ∧
      (cyl M).successExpect (maxDeviation q₀ σ ω M (T / M)) / (1 - (cyl M).failureProb)
        ≤ 2 * C / (M : ℝ) ^ 2) ∧
    (∀ (φ ψ : ℝ → ℝ) (Kφ : NNReal) (Kψ : ℝ), LipschitzOnWith Kφ φ (Set.Icc 0 T) → φ 0 = 0 →
      φ T = 0 → (∀ t ∈ Set.Icc 0 T, |ψ t| ≤ Kψ) →
      ∃ Cφ : ℝ, ∀ M, M₀ ≤ M →
        (cyl M).successExpect (fun q => |testVariation ω T M φ ψ q|) ≤ Cφ / (M : ℝ) ^ 2) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (O : ℕ → Ω → Option (ℕ → ℝ)),
      (∀ M, M₀ ≤ M → ∀ S, P (O M ⁻¹' S) = ENNReal.ofReal ((cyl M).outcomeLaw S)) →
      ∀ᵐ x ∂P,
        (∀ᶠ M in atTop, ∃ q ∈ (cyl M).successPaths, O M x = some q) ∧
        Tendsto (fun M : ℕ => residualEnergy σ ω M (T / M) (pathOf (O M x))) atTop (𝓝 0) ∧
        TendstoUniformlyOn (fun M : ℕ => PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x)))
          (stationaryProfile q₀ σ ω) atTop (Set.Icc 0 T) ∧
        Tendsto (fun M : ℕ => PiecewiseAffine.h1DistSq
          (PiecewiseAffine.affineInterp M (T / M) (pathOf (O M x))) (stationaryProfile q₀ σ ω) 0 T)
          atTop (𝓝 0) ∧
        (∀ᶠ M in atTop, ∀ j ≤ M, ∀ h : ℝ, 0 < h →
          0 < rootRateOf (pathOf (O M x)) j h ∧ 0 < vertexMassOf (pathOf (O M x)) j h ∧
          rootBracketOf (pathOf (O M x)) j h
            = rootConductance (pathOf (O M x)) j • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
        (∀ η > 0, ∀ᶠ M in atTop, ∀ j ≤ M,
          |Real.log (rootConductance (pathOf (O M x)) j)⁻¹ - Real.log (q₀ ^ (4 / 3 : ℝ))
            - 2 * (2 * σ * ω / 3) * (j * (T / M))| ≤ η)) ∧
    (∀ t, RelationalDeSitterBranch.ricciTensor (2 * σ * ω / 3) t
        - (RelationalDeSitterBranch.scalarCurvature (2 * σ * ω / 3) / 2) •
          RelationalDeSitterBranch.lorentzMetric (2 * σ * ω / 3) t
        + RelationalDeSitterBranch.cosmologicalCoefficient (2 * σ * ω / 3) •
          RelationalDeSitterBranch.lorentzMetric (2 * σ * ω / 3) t = 0) ∧
    RelationalDeSitterBranch.cosmologicalCoefficient (2 * σ * ω / 3) = 4 * ω ^ 2 / 3

/-- Conditional bound: `X/(1 − f) ≤ 2B` when `0 ≤ X ≤ B` and `f ≤ 1/2`. -/
theorem div_one_sub_le_two_mul {X B f : ℝ} (hX : 0 ≤ X) (hXB : X ≤ B) (hf : f ≤ 1 / 2) :
    X / (1 - f) ≤ 2 * B := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **`thm:main-explicit-operational-family`.** -/
theorem explicit_operational_family.{u} (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀)
    (hσ : σ = 1 ∨ σ = -1) : ExplicitOperationalFamilyStatement.{u} T ω q₀ σ := by
  set C := max (energyConst T ω q₀) (deviationConst T ω q₀)
  have hEC := energyConst_nonneg hT hω hq₀
  have hC0 : 0 ≤ C := le_max_of_le_left hEC
  refine ⟨explicitCylinder T ω q₀ σ, threshold T ω q₀, C, threshold_pos hT hω hq₀, hC0,
    fun M hM => ?_, fun φ ψ Kφ Kψ hφ hφ0 hφT hψ => ?_, fun P O hlaw => ?_, fun t => ?_,
    limit_cosmological_constant hσ⟩
  · have hM2 := (large_facts hT hω hq₀ hM).1
    have hMpos : (0 : ℝ) < M := by linarith
    have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
    have hWF := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1
    have hf := explicit_failureProb_le hT hω hq₀ hσ hM
    have hf2 : (explicitCylinder T ω q₀ σ M).failureProb ≤ 1 / 2 := by
      refine hf.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hM2 6]
    have hE : (explicitCylinder T ω q₀ σ M).successExpect (residualEnergy σ ω M (T / M))
        ≤ C / (M : ℝ) ^ 4 := (explicit_energy_le hT hω hq₀ hσ hM).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have hD : (explicitCylinder T ω q₀ σ M).successExpect (maxDeviation q₀ σ ω M (T / M))
        ≤ C / (M : ℝ) ^ 2 := (explicit_deviation_le hT hω hq₀ hσ hM).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
    have hE0 : 0 ≤ (explicitCylinder T ω q₀ σ M).successExpect (residualEnergy σ ω M (T / M)) :=
      AcceptRejectCylinder.successExpect_nonneg hWF fun q _ =>
        residualEnergy_nonneg σ ω M (by positivity) q
    have hD0 : 0 ≤ (explicitCylinder T ω q₀ σ M).successExpect (maxDeviation q₀ σ ω M (T / M)) :=
      AcceptRejectCylinder.successExpect_nonneg hWF fun q _ =>
        (abs_nonneg _).trans (Finset.le_sup' (fun j => |q j - stationaryProfile q₀ σ ω (j * (T / M))|)
          (mem_range.2 (Nat.succ_pos M)))
    refine ⟨rfl, rfl, rfl, alphabetOf_zero T ω q₀ σ M,
      fun j hj => alphabet_nonempty hT hω hq₀ hσ hM hj,
      fun j hj x hx => (qLower_pos hq₀).trans_le (alphabet_bounds hT hω hq₀ hσ hM hj hx).1,
      rfl, hWF, AcceptRejectCylinder.outcomeLaw_univ hWF, hf, hE, hD, ?_, ?_⟩
    · have := div_one_sub_le_two_mul hE0 hE hf2
      rwa [mul_div_assoc]
    · have := div_one_sub_le_two_mul hD0 hD hf2
      rwa [mul_div_assoc]
  · obtain ⟨Cφ, -, h⟩ := explicit_firstVariation_le hT hω hq₀ hσ (σ := σ) hφ hφ0 hφT hψ
    exact ⟨Cφ, h⟩
  · exact explicit_coupling_ae hT hω hq₀ hσ P O hlaw
  · exact RelationalDeSitterBranch.einstein_cosmological_vacuum _ t

/-- Non-vacuity: the statement is instantiated at `T = ω = q₀ = 1`, `σ = 1`. -/
example : ExplicitOperationalFamilyStatement.{0} 1 1 1 1 :=
  explicit_operational_family one_pos one_pos one_pos (Or.inl rfl)

/-- **`mt:vacuum`** with its closing sentence: all clauses (i)–(vi) for the de Sitter branch of
Hubble rate `H > 0` (`VacuumRegulatorStationarity.vacuum_regulator_assembly_with_stationarity`),
and, for every horizon `T > 0` and initial amplitude `q₀ > 0`, the explicit finite positive
accept/reject realization of `thm:main-explicit-operational-family` on the expanding branch
`σ = 1`, `ω = 3H/2`, whose regulators converge to the same branch (`2σω/3 = H`). -/
theorem vacuum_regulators_with_operational_realization.{u} (H : ℝ) (hH : 0 < H) :
    (IsStationaryRenewalSolution (3 * H ^ 2) Set.univ (VacuumRegulatorStationarity.profile H)
        (fun t => H * VacuumRegulatorStationarity.profile H t) (fun _ => 1) id ∧
      (∀ (σ b h : ℝ), 0 < H → (σ = 1 ∨ σ = -1) → 0 ≤ b → b < 1 → (3 * H / 2) * h / 2 ≤ b →
        ∀ (M : ℕ) (q s : ℕ → ℝ), 0 < q 0 → (∀ j < M, 0 < s j) → (∀ j < M, s j ≤ h) →
          FiniteHomogeneousStationarity.SatisfiesRecurrence (3 * H / 2) σ M q s →
          ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) -
              σ * H * FiniteHomogeneousStationarity.renewalTime s j|
            ≤ (2 / 3) * ((3 * H / 2) ^ 3 * FiniteHomogeneousStationarity.renewalTime s M * h ^ 2 /
              (12 * (1 - b ^ 2)))) ∧
      (∀ t, RelationalDeSitterBranch.speedDensity H t = Real.exp (3 * H * t) ∧
        RelationalDeSitterBranch.spatialMetric H t = Real.exp (2 * H * t) • 1 ∧
        RelationalDeSitterBranch.lapse H t = 1 ∧ RelationalDeSitterBranch.shift H t = 0) ∧
      (∀ t, RelationalDeSitterBranch.ricciTensor H t -
          (RelationalDeSitterBranch.scalarCurvature H / 2) • RelationalDeSitterBranch.lorentzMetric H t
          + RelationalDeSitterBranch.cosmologicalCoefficient H •
            RelationalDeSitterBranch.lorentzMetric H t = 0) ∧
      RelationalDeSitterBranch.cosmologicalCoefficient H = 3 * H ^ 2 ∧
      Summable (RelationalDeSitterBranch.normalizedTorsionDefect H) ∧
      Summable (RelationalDeSitterBranch.normalizedCurvatureDefect H) ∧
      Summable (RelationalDeSitterBranch.normalizedPalatiniDefect H)) ∧
    2 * 1 * (3 * H / 2) / 3 = H ∧
    ∀ T q₀ : ℝ, 0 < T → 0 < q₀ → ExplicitOperationalFamilyStatement.{u} T (3 * H / 2) q₀ 1 :=
  ⟨VacuumRegulatorStationarity.vacuum_regulator_assembly_with_stationarity H hH.le, by ring,
    fun _ _ hT hq₀ => explicit_operational_family hT (by positivity) hq₀ (Or.inl rfl)⟩

end Main

/-! ### Non-vacuity of the coupling hypothesis: the independent coupling -/

section Coupling

/-- The outcome space `Option (ℕ → ℝ)` with the discrete σ-algebra. -/
def Outcome : Type := Option (ℕ → ℝ)

instance : MeasurableSpace Outcome := ⊤

open Classical in
/-- The law of the explicit cylinder as a measure on outcomes (a point mass at failure below the
threshold). -/
def outcomeMeasure (T ω q₀ σ : ℝ) (M : ℕ) : Measure Outcome :=
  if threshold T ω q₀ ≤ M ∧ 1 ≤ M ∧ 0 < T then
    (∑ q ∈ (explicitCylinder T ω q₀ σ M).successPaths,
        ENNReal.ofReal ((explicitCylinder T ω q₀ σ M).pathProb q) • Measure.dirac (α := Outcome) (some q))
      + ENNReal.ofReal (explicitCylinder T ω q₀ σ M).failureProb • Measure.dirac (α := Outcome) none
  else Measure.dirac (α := Outcome) none

theorem outcomeMeasure_apply {T ω q₀ σ : ℝ} (hT : 0 < T) {M : ℕ} (hM : threshold T ω q₀ ≤ M)
    (hM1 : 1 ≤ M) (S : Set Outcome) :
    outcomeMeasure T ω q₀ σ M S
      = ENNReal.ofReal ((explicitCylinder T ω q₀ σ M).outcomeLaw S) := by
  classical
  have hC := explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hT hM1
  simp only [outcomeMeasure, if_pos (⟨hM, hM1, hT⟩ : threshold T ω q₀ ≤ M ∧ 1 ≤ M ∧ 0 < T)]
  rw [Measure.add_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  unfold AcceptRejectCylinder.outcomeLaw
  rw [ENNReal.ofReal_add (sum_nonneg fun q _ => by
      split_ifs
      · exact AcceptRejectCylinder.pathProb_nonneg hC q
      · exact le_rfl) (by split_ifs; exacts [AcceptRejectCylinder.failureProb_nonneg hC, le_rfl]),
    ENNReal.ofReal_sum_of_nonneg (fun q _ => by
      split_ifs
      · exact AcceptRejectCylinder.pathProb_nonneg hC q
      · exact le_rfl)]
  congr 1
  · refine sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rw [Measure.dirac_apply_of_mem (α := Outcome) (a := some q) (s := S) h]; simp
    · rw [Measure.dirac_apply' (α := Outcome) (some q)
        (MeasurableSpace.measurableSet_top : MeasurableSet[⊤] S),
        Set.indicator_of_notMem (α := Outcome) (s := S) (a := some q) h]; simp
  · split_ifs with h
    · rw [Measure.dirac_apply_of_mem (α := Outcome) (a := none) (s := S) h]; simp
    · rw [Measure.dirac_apply' (α := Outcome) none
        (MeasurableSpace.measurableSet_top : MeasurableSet[⊤] S),
        Set.indicator_of_notMem (α := Outcome) (s := S) (a := none) h]; simp

instance outcomeMeasure_isProb {T ω q₀ σ : ℝ} (M : ℕ) :
    IsProbabilityMeasure (outcomeMeasure T ω q₀ σ M) := by
  classical
  by_cases hM : threshold T ω q₀ ≤ M ∧ 1 ≤ M ∧ 0 < T
  · constructor
    have h1 := AcceptRejectCylinder.outcomeLaw_univ
      (explicit_wellFormed (ω := ω) (q₀ := q₀) (σ := σ) hM.2.2 hM.2.1)
    rw [outcomeMeasure_apply hM.2.2 hM.1 hM.2.1]
    exact (congrArg ENNReal.ofReal h1).trans ENNReal.ofReal_one
  · have : outcomeMeasure T ω q₀ σ M = Measure.dirac (α := Outcome) none := by
      unfold outcomeMeasure; rw [if_neg hM]
    constructor
    rw [this]
    exact Measure.dirac_apply_of_mem (α := Outcome) (a := none) (s := Set.univ) trivial

/-- **The independent coupling exists.**  On the infinite product of the cylinder laws, the
coordinate outcomes have exactly the laws required in `explicit_coupling_ae`; hence its coupling
hypothesis is satisfiable. -/
theorem independent_coupling (T ω q₀ σ : ℝ) (hT : 0 < T) (hω : 0 < ω) (hq₀ : 0 < q₀) :
    ∃ (P : Measure (ℕ → Outcome)) (O : ℕ → (ℕ → Outcome) → Option (ℕ → ℝ)),
      IsProbabilityMeasure P ∧ ∀ M, threshold T ω q₀ ≤ M → ∀ S,
        P (O M ⁻¹' S) = ENNReal.ofReal ((explicitCylinder T ω q₀ σ M).outcomeLaw S) := by
  refine ⟨Measure.infinitePi (outcomeMeasure T ω q₀ σ), fun M x => x M, inferInstance,
    fun M hM S => ?_⟩
  have hM1 : 1 ≤ M := (threshold_pos hT hω hq₀).trans hM
  have hmeas : Measurable fun x : ℕ → Outcome => x M := measurable_pi_apply M
  change (Measure.infinitePi (outcomeMeasure T ω q₀ σ))
    ((fun x : ℕ → Outcome => x M) ⁻¹' (S : Set Outcome)) = _
  rw [← Measure.map_apply hmeas (MeasurableSpace.measurableSet_top : MeasurableSet[⊤] (S : Set Outcome)),
    Measure.infinitePi_map_eval]
  exact outcomeMeasure_apply hT hM hM1 S

end Coupling

end

end RenewalGeometry.ExplicitOperationalFamily
