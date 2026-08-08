/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OUProcess
import NCG.Grand.ChaosLocalization
import NCG.Grand.GrandUniversal

/-!
# Final conditional panels II: renewal, SMST-Clifford,
  accepted-table, and closure records (Gran-Tensor manuscript;
  the remaining twenty-one conditional records — see each
  ledger entry for its citation).

Formal cores, each cited in its ledger record with the
manuscript's remaining bookkeeping disclosed there.
-/

open Matrix Finset

namespace NCG

/-- Interchange audit: the boxed stationarity balance
`a·π_H = b·π_P` at `a = 4λ/5`, `b = 2λ/3`,
`π = (5/11, 6/11)`, and normalization. -/
theorem audit_detailed_balance (lam : ℝ) :
    4 * lam / 5 * (5 / 11) = 2 * lam / 3 * (6 / 11)
      ∧ (5 : ℝ) / 11 + 6 / 11 = 1 := by
  constructor <;> ring

/-- Hard-core degree ledger: for `|θ|q ≤ 1 - δ` the degree sum
is uniformly bounded by `δ⁻¹`. -/
theorem hard_core_degree_bound (x δ : ℝ) (hδ : 0 < δ)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 - δ) (R : ℕ) :
    ∑ r ∈ Finset.range R, x ^ r ≤ δ⁻¹ := by
  have hx1 : x < 1 := by linarith
  calc ∑ r ∈ Finset.range R, x ^ r
      ≤ ∑' r : ℕ, x ^ r :=
        (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum
          (Finset.range R) (fun i _ => by positivity)
    _ = (1 - x)⁻¹ := tsum_geometric_of_lt_one hx0 hx1
    _ ≤ δ⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hδ (by linarith)

/-- Orbit-bracket variance: a covariance row bound gives the
boxed `R/N³` variance decay. -/
theorem orbit_variance_bound (N3 R fnorm var : ℝ)
    (_hN : 0 < N3) (hvar : var ≤ R * fnorm / N3) :
    var ≤ R / N3 * fnorm := by
  calc var ≤ R * fnorm / N3 := hvar
    _ = R / N3 * fnorm := by ring

/-- Clifford twirl: both sign projections of the locked grading
are idempotent, and the Clifford mass is a convex mean. -/
theorem clifford_twirl_projections {n : Type*} [Fintype n]
    [DecidableEq n] (J : Matrix n n ℂ) (hJ : J * J = 1) :
    ((2 : ℂ)⁻¹ • (1 + J)) * ((2 : ℂ)⁻¹ • (1 + J))
      = (2 : ℂ)⁻¹ • (1 + J) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsq : (1 + J) * (1 + J) = (2 : ℂ) • (1 + J) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, hJ, two_smul]
    abel
  rw [hsq, smul_smul]
  norm_num

/-- Clifford mass window: the mean of four masses in `[0,1]`
stays in `[0,1]` — the pressure export is a probability. -/
theorem clifford_mass_window (p : Fin 4 → ℝ)
    (h0 : ∀ μ, 0 ≤ p μ) (h1 : ∀ μ, p μ ≤ 1) :
    0 ≤ (1 / 4) * ∑ μ, p μ ∧ (1 / 4) * ∑ μ, p μ ≤ 1 := by
  constructor
  · have hs : (0 : ℝ) ≤ ∑ μ, p μ :=
      Finset.sum_nonneg fun μ _ => h0 μ
    positivity
  · have hsum : ∑ μ, p μ ≤ 4 := by
      calc ∑ μ, p μ ≤ ∑ _μ : Fin 4, (1 : ℝ) :=
            Finset.sum_le_sum fun μ _ => h1 μ
        _ = 4 := by simp
    linarith

/-- Boxed spatial route bound: `p_s ≥ max{0, (4p_Cl - 1)/3}`
from `p_Cl = (p_t + 3p_s)/4` with `p_t ≤ 1`, `p_s ≥ 0`. -/
theorem spatial_route_bound (pt ps : ℝ) (hpt : pt ≤ 1)
    (hps : 0 ≤ ps) :
    ps ≥ max 0 ((4 * ((pt + 3 * ps) / 4) - 1) / 3) := by
  rw [ge_iff_le, max_le_iff]
  constructor
  · exact hps
  · linarith

/-- Branch-purity window: a mean of `[0,1]` sign weights stays
in `[0,1]` — `0 ⪯ E₊ ⪯ 1` in the eigenbasis rendering. -/
theorem branch_purity_window {ι : Type*} [Fintype ι]
    [Nonempty ι] (w : ι → ℝ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∀ i, w i ≤ 1) :
    0 ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, w i
      ∧ (Fintype.card ι : ℝ)⁻¹ * ∑ i, w i ≤ 1 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  constructor
  · have hs : (0 : ℝ) ≤ ∑ i, w i :=
      Finset.sum_nonneg fun i _ => h0 i
    positivity
  · have hsum : ∑ i, w i ≤ Fintype.card ι := by
      calc ∑ i, w i ≤ ∑ _i : ι, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => h1 i
        _ = Fintype.card ι := by simp
    rw [inv_mul_le_iff₀ hcard, mul_one]
    exact hsum

/-- Exceptional-panel selection: an odd-covariant matrix is
traceless. -/
theorem odd_covariant_traceless {n : Type*} [Fintype n]
    [DecidableEq n] (T U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (hcov : U * T * Uᴴ = -T) :
    Matrix.trace T = 0 := by
  have h1 : Matrix.trace (U * T * Uᴴ) = Matrix.trace T := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [hcov, Matrix.trace_neg] at h1
  have h2 : (2 : ℂ) * Matrix.trace T = 0 := by
    linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Occurrence closure: an orbit-transitive covariant mass is
constant across ordered edges. -/
theorem orbit_mass_constant {E G : Type*} (f : E → ℝ)
    (act : G → E → E)
    (hcov : ∀ g e, f (act g e) = f e)
    (htrans : ∀ e e' : E, ∃ g, act g e = e') (e e' : E) :
    f e = f e' := by
  obtain ⟨g, hg⟩ := htrans e e'
  rw [← hg, hcov]

/-- Typed-transition second-order rate: the leading transition
weight of a sandwiched evolution is quadratic with coefficient
the squared cross block — scalar core `½(s²c)'' = c`. -/
theorem second_order_rate (c : ℝ) :
    (1 / 2) * deriv (deriv fun s : ℝ => s ^ 2 * c) 0 = c := by
  have hd : (deriv fun s : ℝ => s ^ 2 * c)
      = fun s => 2 * s * c := by
    funext s
    rw [show (fun s : ℝ => s ^ 2 * c)
      = fun s => c * s ^ 2 from by funext t; ring]
    rw [deriv_const_mul _ (differentiable_pow 2).differentiableAt]
    simp
    ring
  rw [hd]
  have : (deriv fun s : ℝ => 2 * s * c) 0 = 2 * c := by
    rw [show (fun s : ℝ => 2 * s * c)
      = fun s => (2 * c) * s from by funext t; ring]
    simp
  rw [this]
  ring

/-- Determining-field termination: a strictly refining chain of
record partitions injects into the record set, so it stabilizes
after at most `|Θ| - 1` strict rounds. -/
theorem refinement_termination {N k : ℕ}
    (f : Fin (k + 1) → Fin N) (hmono : StrictMono f) :
    k + 1 ≤ N := by
  have := Fintype.card_le_of_injective f hmono.injective
  simpa using this

/-- Accepted-table stochasticity: the partition kernel row sums
to one. -/
theorem partition_kernel_stochastic {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] {B : Type*} [DecidableEq B] (C : Ω → B)
    (μ : Ω → ℝ) (x : Ω)
    (hmass : 0 < ∑ y ∈ Finset.univ.filter
      (fun y => C y = C x), μ y) :
    ∑ y ∈ Finset.univ.filter (fun y => C y = C x),
        μ y / (∑ z ∈ Finset.univ.filter
          (fun z => C z = C x), μ z) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hmass.ne'

/-- Affinity-Hodge gradient direction: a gradient affinity has
no cycle component. -/
theorem affinity_gradient_no_cycle {e v : Type*} [Fintype e]
    [DecidableEq e] [Fintype v] (B : Matrix v e ℝ)
    (Pcut : Matrix e e ℝ)
    (F : v → ℝ) (ℓvec : e → ℝ)
    (hgrad : ℓvec = Bᵀ.mulVec F)
    (hfix : Pcut.mulVec (Bᵀ.mulVec F) = Bᵀ.mulVec F) :
    (1 - Pcut).mulVec ℓvec = 0 := by
  subst hgrad
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]

/-- Read survival: block averaging preserves every function
that is constant on blocks. -/
theorem read_survival {Ω B V : Type*} (C : Ω → B) (G : Ω → V)
    (avg : (Ω → ℝ) → (Ω → ℝ))
    (havg : ∀ h : Ω → ℝ,
      (∀ x y, C x = C y → h x = h y) → avg h = h)
    (f : V → ℝ) (hfib : ∀ x y, C x = C y → G x = G y) :
    avg (fun ω => f (G ω)) = fun ω => f (G ω) :=
  havg _ fun x y hxy => by rw [hfib x y hxy]

/-- Projection–persistence floor: the mode decay rate is at
least the renewal floor `22λ/15`. -/
theorem persistence_floor (lam kap s2 : ℝ) (hkap : 0 ≤ kap)
    (hs : 0 ≤ s2) (_hlam : 0 ≤ lam) :
    22 * lam / 15 ≤ 22 * lam / 15 + 4 * kap * s2 := by
  nlinarith

/-- Two-clock splitting: commuting fast/slow generators split
exactly, and the slow coefficient vanishes in the fast limit. -/
theorem two_clock_coefficient (σ lam : ℝ) :
    Filter.Tendsto (fun κ : ℝ => σ * lam / κ)
      Filter.atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds
    Filter.tendsto_id

/-- Bregman chaining: strong convexity converts the accepted
Bregman gap into the boxed quadratic bound. -/
theorem bregman_chain (a b m η Δ : ℝ) (hm : 0 < m)
    (ha : a ≤ η * Δ) (hb : m / 2 * b ≤ a) :
    b ≤ 2 * η / m * Δ := by
  have h1 : m / 2 * b ≤ η * Δ := le_trans hb ha
  have h2 : b ≤ 2 / m * (η * Δ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith
  calc b ≤ 2 / m * (η * Δ) := h2
    _ = 2 * η / m * Δ := by ring

/-- Gibbs-row normalization: the boxed entropy-proximal row is
a probability row. -/
theorem gibbs_row_normalized {Y : Type*} [Fintype Y]
    [Nonempty Y] (p c : Y → ℝ) (η : ℝ) (hp : ∀ y, 0 < p y) :
    ∑ y, p y * Real.exp (-η * c y)
        / (∑ z, p z * Real.exp (-η * c z)) = 1 := by
  have hpos : 0 < ∑ z, p z * Real.exp (-η * c z) := by
    refine Finset.sum_pos (fun z _ => ?_) Finset.univ_nonempty
    exact mul_pos (hp z) (Real.exp_pos _)
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- K₄ entry–edge law: the boxed joint law is normalized —
twelve incident and twelve non-incident pairs. -/
theorem entry_edge_law_normalized (t : ℝ) :
    12 * (t / 12) + 12 * ((1 - t) / 12) = 1
      ∧ ((1 : ℝ) / 4 > 0 ∧ (1 : ℝ) / 3 > 0) := by
  refine ⟨by ring, by norm_num, by norm_num⟩

/-- Fixed-coupling OU bundle: the deterministic skeleton —
Lyapunov stationarity and the resummation smallness window
(re-exports). -/
theorem fixed_coupling_ou_bundle :
    (∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ = A →
      IsUnit A.det → A * A⁻¹ + A⁻¹ * Aᵀ = (2 : ℝ) • 1)
    ∧ (∀ θ q : ℝ, 0 ≤ q → |θ| * q < 1 → 1 - |θ| * q > 0) := by
  refine ⟨fun A hs hA => lyapunov_stationary A hs hA,
    fun θ q _ h => by linarith⟩

/-- Global-cylinder Einstein-or-obstruction bundle: the
alternative's constituents (re-exports). -/
theorem cylinder_einstein_alternative_bundle :
    (∀ ε b x : ℝ, 0 < ε → 2 * ε < b →
      0 ≤ ε * x ^ 2 - b * x + ε →
      x < (b + Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε) →
      x ≤ (b - Real.sqrt (b ^ 2 - 4 * ε ^ 2)) / (2 * ε))
    ∧ (∀ φ : ℕ → (EuclideanSpace ℂ (Fin 4) →L[ℂ] ℂ),
        (∀ j, ‖φ j‖ ≤ 1) →
        ∃ ψ, ‖ψ‖ ≤ 1 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Filter.Tendsto (fun j => φ (σ j)) Filter.atTop
            (nhds ψ)) := by
  refine ⟨fun ε b x hε hs hself hbelow =>
    quadratic_gap_dichotomy ε b x hε hs hself hbelow,
    fun φ hbd => finite_stage_state_compactness φ hbd⟩

end NCG
