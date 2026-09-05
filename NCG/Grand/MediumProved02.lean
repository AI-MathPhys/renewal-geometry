/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact01

/-!
# Medium exact records, batch 02 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `cth:GT-adjacent-defect-insufficient` — the moving Dirac family
  `Λ_n = δ_{sin(log(n+1))}` on `[-1,1]` with identity bonding maps:
  vanishing adjacent defects, explicit subsequences landing on `δ_1` and
  `δ_{-1}`, and failure of the tail diameter `D_N → 0`.
* `cth:GT-triangular-weaker-than-summability` — the Dirac family
  `Λ_n = δ_{(-1)^n/√n}`: tail diameter at most `2/√N` (so `D_N → 0`)
  while the adjacent defects are not summable.
* `thm:GT-low-island-relative-moment` — the low-island Loewner windows
  (LIR.5–LIR.6), nonvanishing of island heads, the normalized carrier
  bound (LIR.7), the sublevel tail estimate (LIR.8) in the `ℓ²` operator
  norm, and the attained generalized-eigenvalue characterization of the
  least admissible relative edge.
* `thm:NS-critical-centred-target` — on the finite Fourier Galerkin model
  of the critical packet: `ψ` is the orthogonal projection of `v` to the
  physical source carrier, the incidence identities (NSE.8), the exact
  dispersion action (NSE.9), and the one-modulus characterization of
  `𝒱_c = 0` with `Φ_c = q_c = 0` on that branch.
* `thm:NS-centred-dispersion-escape` — the payment/dispersion density
  identity (NSE.23), summability and vanishing of the dispersion masses,
  and the Chebyshev escape bound (NSE.24).
* `thm:NS-centred-boundary-counterflow` — the coherent payment and
  counterflow split (NSE.25–NSE.26) with the uniqueness of the
  proportional positive replay, and the exact one-dimensional
  Kantorovich–Rubinstein identity (NSE.27) on a finite scale grid.
* `thm:NS-two-centre-critical-dipole` — the discrete critical-energy
  spectral law of the Galerkin model: the two-sided mass and separation
  bounds (NSE.30), the dipole action floors (NSE.31), and the
  far-leverage moment bound (NSE.32).
* `thm:NS-centred-critical-commutator` — the exact centred commutator
  identities (NSE.33), the Fourier alias expansion (NSE.34), and the
  ordered alias bound (NSE.35) on the Galerkin model.
* `thm:RPESM-sector-patched-line` — the sector-patched reflected line on a
  finite reflection-stable cover: the fibrewise isometry (RTH.11), the
  reflected coherent amplitude (RTH.12) with positivity and basis
  independence, the minimum half-carrier (RTH.13) with the rank formula,
  the global-frame/Čech-coboundary equivalence (RTH.14), and the patched
  line one-form (RTH.15) on the discrete edge model.
* `thm:GT-source-metric-cofinal` — cofinal reserve–geometry separation on
  one finite comparison carrier: convergence of the normalized horizon
  Gramians to `∫₀ᵀ e^{-tH}P_B e^{-tH} dt` (SMET.27), convergence of the
  dynamic residuals to `Y^*(I - P_H^{P_B})Y` (SMET.28) for the orthogonal
  projection onto `span{e^{-tH} Ran P_B : t ≥ 0}` under the uniform closing
  of the normalized Tikhonov tails (SMET.26), and closure of the
  limit-card physical-metric Tikhonov tail; on the finite carrier the
  trace-norm and operator-norm topologies are the matrix topology.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset Filter
open scoped ComplexOrder Topology

-- decidability/fintype instances enter only through spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
-- shared section variables feed the spectral instances of some proofs only
set_option linter.unusedSectionVars false

namespace NCG

/-! ### Vanishing adjacent defects do not select a continuum

Records `cth:GT-adjacent-defect-insufficient` and
`cth:GT-triangular-weaker-than-summability`.

Rendering: the witness families are Dirac masses `Λ_n = δ_{x_n}` on the
fixed carrier `X_n = [-1,1]` with identity bonding maps, so the projective
transport metric restricts on Dirac masses to the distance of the base
points; the families are therefore represented by their base-point
sequences `x : ℕ → ℝ`.  The adjacent defect is `δ_n = |x_{n+1} - x_n|` and
the complete tail diameter is `D_N = sup {|x_m - x_n| : m, n ≥ N}`.
Landing on `δ_{±1}` is rendered as a strictly monotone subsequence of base
points converging to `±1`, and `D_N ↛ 0` is the stated failure. -/

section AdjacentDefectWitnessSection

namespace AdjacentDefectWitness

/-- The adjacent defect `δ_n = d(Λ_{n+1}, Λ_n) = |x_{n+1} - x_n|` of a moving
Dirac family represented by its base points. -/
noncomputable def adjacentDefect (x : ℕ → ℝ) (n : ℕ) : ℝ := |x (n + 1) - x n|

/-- The complete tail diameter `D_N = sup {d(Λ_m, Λ_n) : m, n ≥ N}` of a
moving Dirac family represented by its base points. -/
noncomputable def tailDiam (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ m, N ≤ m ∧ ∃ n, N ≤ n ∧ d = |x m - x n|}

/-- Upper bound for the tail diameter from a uniform pairwise bound. -/
theorem tailDiam_le {x : ℕ → ℝ} {N : ℕ} {c : ℝ}
    (h : ∀ m n, N ≤ m → N ≤ n → |x m - x n| ≤ c) : tailDiam x N ≤ c := by
  refine Real.sSup_le ?_ (le_trans (abs_nonneg _) (h N N le_rfl le_rfl))
  rintro d ⟨m, hm, n, hn, rfl⟩
  exact h m n hm hn

/-- Lower bound for the tail diameter by any occupied pair. -/
theorem le_tailDiam {x : ℕ → ℝ} {N m n : ℕ} {c : ℝ}
    (hb : ∀ m' n', N ≤ m' → N ≤ n' → |x m' - x n'| ≤ c)
    (hm : N ≤ m) (hn : N ≤ n) : |x m - x n| ≤ tailDiam x N := by
  refine le_csSup ⟨c, ?_⟩ ⟨m, hm, n, hn, rfl⟩
  rintro d ⟨m', hm', n', hn', rfl⟩
  exact hb m' n' hm' hn'

/-- The tail diameter of a bounded family is nonnegative. -/
theorem tailDiam_nonneg {x : ℕ → ℝ} {N : ℕ} {c : ℝ}
    (hb : ∀ m n, N ≤ m → N ≤ n → |x m - x n| ≤ c) : 0 ≤ tailDiam x N := by
  have h0 := le_tailDiam hb le_rfl le_rfl (m := N) (n := N)
  simpa using h0

/-- Base points of the moving Dirac family `Λ_n = δ_{sin(log(n+1))}`. -/
noncomputable def sinLogPoint (n : ℕ) : ℝ := Real.sin (Real.log (n + 1))

/-- The landing subsequence `n_k = ⌊exp(2πk + θ)⌋` aimed at the phase `θ`. -/
noncomputable def landing (θ : ℝ) (k : ℕ) : ℕ :=
  ⌊Real.exp (k * (2 * Real.pi) + θ)⌋₊

/-- The landing subsequence brackets its exponential clock. -/
theorem landing_bracket (θ : ℝ) (k : ℕ) :
    Real.exp (k * (2 * Real.pi) + θ) < landing θ k + 1 ∧
      (landing θ k : ℝ) ≤ Real.exp (k * (2 * Real.pi) + θ) := by
  constructor
  · exact_mod_cast Nat.lt_floor_add_one (Real.exp (k * (2 * Real.pi) + θ))
  · exact Nat.floor_le (Real.exp_nonneg _)

/-- The landing subsequence is strictly monotone for nonnegative phases. -/
theorem landing_strictMono {θ : ℝ} (hθ : 0 ≤ θ) : StrictMono (landing θ) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hbr := landing_bracket θ k
  have htk : (0 : ℝ) ≤ k * (2 * Real.pi) + θ := by
    have h1 : (0:ℝ) ≤ (k:ℝ) * (2 * Real.pi) := by positivity
    linarith [hθ]
  have h1 : (landing θ k : ℝ) + 1 ≤ Real.exp ((k + 1 : ℕ) * (2 * Real.pi) + θ) := by
    have hstep : Real.exp ((k + 1 : ℕ) * (2 * Real.pi) + θ)
        = Real.exp (k * (2 * Real.pi) + θ) * Real.exp (2 * Real.pi) := by
      rw [← Real.exp_add]
      push_cast
      ring_nf
    have hexp1 : (1 : ℝ) ≤ Real.exp (k * (2 * Real.pi) + θ) := Real.one_le_exp htk
    have hexp2 : 2 * Real.pi + 1 ≤ Real.exp (2 * Real.pi) := Real.add_one_le_exp _
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    rw [hstep]
    nlinarith [hbr.2]
  have h2 : landing θ k + 1 ≤ landing θ (k + 1) := by
    rw [landing]
    refine Nat.le_floor ?_
    exact_mod_cast h1
  omega

/-- The landing subsequence lands on `sin θ`: the base points of the
sin-log Dirac family along `n_k = ⌊exp(2πk + θ)⌋` converge to `sin θ`. -/
theorem landing_tendsto (θ : ℝ) :
    Tendsto (fun k => sinLogPoint (landing θ k)) atTop (𝓝 (Real.sin θ)) := by
  set t : ℕ → ℝ := fun k => k * (2 * Real.pi) + θ with ht
  set ε : ℕ → ℝ := fun k => Real.log (landing θ k + 1) - t k with hε
  have hεbounds : ∀ k, 0 ≤ ε k ∧ ε k ≤ Real.exp (-(t k)) := by
    intro k
    have hbr := landing_bracket θ k
    have hpos : (0 : ℝ) < (landing θ k : ℝ) + 1 := by positivity
    constructor
    · have hlog : t k ≤ Real.log (landing θ k + 1) := by
        have h1 : Real.exp (t k) ≤ (landing θ k : ℝ) + 1 := (hbr.1).le
        calc t k = Real.log (Real.exp (t k)) := (Real.log_exp _).symm
          _ ≤ Real.log ((landing θ k : ℝ) + 1) :=
              Real.log_le_log (Real.exp_pos _) h1
      simpa [hε] using sub_nonneg.mpr hlog
    · have h1 : (landing θ k : ℝ) + 1 ≤ Real.exp (t k) + 1 := by
        linarith [hbr.2]
      have h2 : Real.log ((landing θ k : ℝ) + 1)
          ≤ Real.log (Real.exp (t k) + 1) :=
        Real.log_le_log hpos h1
      have hfact : Real.exp (t k) + 1
          = Real.exp (t k) * (1 + Real.exp (-(t k))) := by
        rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h3 : Real.log (Real.exp (t k) + 1)
          = t k + Real.log (1 + Real.exp (-(t k))) := by
        rw [hfact, Real.log_mul (Real.exp_ne_zero _) (by positivity),
          Real.log_exp]
      have h4 : Real.log (1 + Real.exp (-(t k))) ≤ Real.exp (-(t k)) := by
        have := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < 1 + Real.exp (-(t k)) by positivity)
        linarith
      simp only [hε]
      linarith
  have htlim : Tendsto t atTop atTop := by
    refine tendsto_atTop_add_const_right _ θ ?_
    exact Tendsto.atTop_mul_const (by positivity)
      tendsto_natCast_atTop_atTop
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    refine squeeze_zero (fun k => (hεbounds k).1)
      (fun k => (hεbounds k).2) ?_
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr htlim)
  have hval : ∀ k, sinLogPoint (landing θ k) = Real.sin (θ + ε k) := by
    intro k
    have hlog : Real.log ((landing θ k : ℝ) + 1) = θ + ε k + (k : ℤ) * (2 * Real.pi) := by
      simp only [hε, ht]
      push_cast
      ring
    rw [sinLogPoint, hlog, Real.sin_add_int_mul_two_pi]
  have hcont : Tendsto (fun k => Real.sin (θ + ε k)) atTop (𝓝 (Real.sin θ)) := by
    have h1 : Tendsto (fun k => θ + ε k) atTop (𝓝 θ) := by
      simpa using tendsto_const_nhds.add hεlim
    exact (Real.continuous_sin.tendsto θ).comp h1
  simpa only [hval] using hcont

/-- **`cth:GT-adjacent-defect-insufficient`**: for the moving Dirac family
`Λ_n = δ_{sin(log(n+1))}` on `X_n = [-1,1]` with identity bonding maps, the
base points stay in the carrier, the adjacent defects vanish, there are
strictly monotone subsequences landing on `δ_1` and `δ_{-1}`, and the
complete tail diameter does not vanish: no exactly projective family can
track the literal laws on their own moving screens. -/
theorem adjacent_defect_insufficient :
    (∀ n, sinLogPoint n ∈ Set.Icc (-1 : ℝ) 1) ∧
      Tendsto (adjacentDefect sinLogPoint) atTop (𝓝 0) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => sinLogPoint (φ k)) atTop (𝓝 1)) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => sinLogPoint (φ k)) atTop (𝓝 (-1))) ∧
      ¬ Tendsto (tailDiam sinLogPoint) atTop (𝓝 0) := by
  have hcarrier : ∀ n, sinLogPoint n ∈ Set.Icc (-1 : ℝ) 1 := fun n =>
    ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hbound : ∀ N, ∀ m n, N ≤ m → N ≤ n →
      |sinLogPoint m - sinLogPoint n| ≤ 2 := by
    intro N m n _ _
    have h1 := hcarrier m
    have h2 := hcarrier n
    rw [abs_sub_le_iff]
    constructor <;> [skip; skip] <;>
      · obtain ⟨ha, hb⟩ := h1
        obtain ⟨hc, hd⟩ := h2
        linarith
  refine ⟨hcarrier, ?_, ?_, ?_, ?_⟩
  · -- vanishing adjacent defects, via the sine Lipschitz bound
    have hle : ∀ n : ℕ, adjacentDefect sinLogPoint n ≤ 1 / (n + 1) := by
      intro n
      have hlip : |sinLogPoint (n + 1) - sinLogPoint n|
          ≤ |Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1)| := by
        have h := Real.lipschitzWith_sin.dist_le_mul
          (Real.log ((n:ℝ) + 1 + 1)) (Real.log ((n:ℝ) + 1))
        simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
        have hcast : sinLogPoint (n + 1) = Real.sin (Real.log ((n:ℝ) + 1 + 1)) := by
          rw [sinLogPoint]
          push_cast
          ring_nf
        rw [hcast, sinLogPoint]
        exact h
      have hd : Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1) ≤ 1 / (n + 1) := by
        have hq : Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1)
            = Real.log (((n:ℝ) + 1 + 1) / ((n:ℝ) + 1)) := by
          rw [Real.log_div (by positivity) (by positivity)]
        rw [hq]
        have h1 := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < ((n:ℝ) + 1 + 1) / ((n:ℝ) + 1) by positivity)
        have h2 : ((n:ℝ) + 1 + 1) / ((n:ℝ) + 1) - 1 = 1 / ((n:ℝ) + 1) := by
          field_simp
          ring
        linarith
      have hmono : Real.log ((n:ℝ) + 1) ≤ Real.log ((n:ℝ) + 1 + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have habs : |Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1)|
          = Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1) :=
        abs_of_nonneg (by linarith)
      calc adjacentDefect sinLogPoint n
          = |sinLogPoint (n + 1) - sinLogPoint n| := rfl
        _ ≤ |Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1)| := hlip
        _ = Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1) := habs
        _ ≤ 1 / (n + 1) := hd
    exact squeeze_zero (fun n => abs_nonneg _) hle
      tendsto_one_div_add_atTop_nhds_zero_nat
  · -- landing on δ_1 with phase π/2
    refine ⟨landing (Real.pi / 2), landing_strictMono (by positivity), ?_⟩
    have h := landing_tendsto (Real.pi / 2)
    simpa [Real.sin_pi_div_two] using h
  · -- landing on δ_{-1} with phase π + π/2
    have hθ : (0:ℝ) ≤ Real.pi + Real.pi / 2 := by positivity
    refine ⟨landing (Real.pi + Real.pi / 2), landing_strictMono hθ, ?_⟩
    have h := landing_tendsto (Real.pi + Real.pi / 2)
    have hsin : Real.sin (Real.pi + Real.pi / 2) = -1 := by
      have := Real.sin_pi_sub (-(Real.pi / 2))
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
      ring
    rwa [hsin] at h
  · -- the tail diameter cannot vanish
    intro hcon
    obtain ⟨φp, hφpmono, hφp⟩ :
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (fun k => sinLogPoint (φ k)) atTop (𝓝 1) := by
      refine ⟨landing (Real.pi / 2), landing_strictMono (by positivity), ?_⟩
      have h := landing_tendsto (Real.pi / 2)
      simpa [Real.sin_pi_div_two] using h
    obtain ⟨φm, hφmmono, hφm⟩ :
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (fun k => sinLogPoint (φ k)) atTop (𝓝 (-1)) := by
      have hθ : (0:ℝ) ≤ Real.pi + Real.pi / 2 := by positivity
      refine ⟨landing (Real.pi + Real.pi / 2), landing_strictMono hθ, ?_⟩
      have h := landing_tendsto (Real.pi + Real.pi / 2)
      have hsin : Real.sin (Real.pi + Real.pi / 2) = -1 := by
        rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
        ring
      rwa [hsin] at h
    -- eventually the tail diameter is below 1/2
    have hsmall : ∀ᶠ N in atTop, tailDiam sinLogPoint N < 1 / 2 :=
      hcon.eventually (eventually_lt_nhds (by norm_num))
    obtain ⟨N, hN⟩ := hsmall.exists
    -- find late indices with values above 1/2 and below -1/2
    have hp : ∀ᶠ k in atTop, sinLogPoint (φp k) > 1 / 2 :=
      hφp.eventually (eventually_gt_nhds (by norm_num))
    have hm : ∀ᶠ k in atTop, sinLogPoint (φm k) < -(1 / 2) :=
      hφm.eventually (eventually_lt_nhds (by norm_num))
    obtain ⟨kp, hkp⟩ := (hp.and (eventually_ge_atTop N)).exists
    obtain ⟨km, hkm⟩ := (hm.and (eventually_ge_atTop N)).exists
    have hφpN : N ≤ φp kp := le_trans hkp.2 (hφpmono.le_apply)
    have hφmN : N ≤ φm km := le_trans hkm.2 (hφmmono.le_apply)
    have hge : (1 : ℝ) ≤ |sinLogPoint (φp kp) - sinLogPoint (φm km)| := by
      have h1 := hkp.1
      have h2 := hkm.1
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hle := le_tailDiam (hbound N) hφpN hφmN
    linarith

/-- Base points of the moving Dirac family `Λ_n = δ_{(-1)^n/√n}`. -/
noncomputable def altPoint (n : ℕ) : ℝ := (-1) ^ n / Real.sqrt n

/-- The modulus of the alternating base point is `1/√n`. -/
theorem abs_altPoint (n : ℕ) : |altPoint n| = 1 / Real.sqrt n := by
  rw [altPoint, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **`cth:GT-triangular-weaker-than-summability`**: for the moving Dirac
family `Λ_n = δ_{(-1)^n/√n}` on `X_n = [-1,1]` with identity bonding maps,
the base points stay in the carrier, the complete tail diameter obeys
`D_N ≤ 2/√N` and vanishes, while the adjacent defects are not summable:
triangular coherence is strictly weaker than summability. -/
theorem triangular_weaker_than_summability :
    (∀ n, altPoint n ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∀ N : ℕ, 1 ≤ N → tailDiam altPoint N ≤ 2 / Real.sqrt N) ∧
      Tendsto (tailDiam altPoint) atTop (𝓝 0) ∧
      ¬ Summable (adjacentDefect altPoint) := by
  have habs : ∀ n : ℕ, 1 ≤ n → |altPoint n| ≤ 1 / Real.sqrt n := fun n _ =>
    (abs_altPoint n).le
  have hcarrier : ∀ n, altPoint n ∈ Set.Icc (-1 : ℝ) 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [altPoint]
    · have h1 : (1:ℝ) ≤ Real.sqrt n := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hpos)
      have h2 : |altPoint n| ≤ 1 := by
        rw [abs_altPoint]
        rw [div_le_one (by linarith)]
        exact h1
      constructor <;> [exact neg_le_of_abs_le h2; exact le_of_abs_le h2]
  have hpair : ∀ N : ℕ, 1 ≤ N → ∀ m n, N ≤ m → N ≤ n →
      |altPoint m - altPoint n| ≤ 2 / Real.sqrt N := by
    intro N hN m n hm hn
    have hNpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    have hb : ∀ j : ℕ, N ≤ j → |altPoint j| ≤ 1 / Real.sqrt N := by
      intro j hj
      have h1 : Real.sqrt N ≤ Real.sqrt j := Real.sqrt_le_sqrt (by exact_mod_cast hj)
      calc |altPoint j| = 1 / Real.sqrt j := abs_altPoint j
        _ ≤ 1 / Real.sqrt N := by
            apply one_div_le_one_div_of_le hNpos h1
    calc |altPoint m - altPoint n| ≤ |altPoint m| + |altPoint n| := abs_sub _ _
      _ ≤ 1 / Real.sqrt N + 1 / Real.sqrt N := add_le_add (hb m hm) (hb n hn)
      _ = 2 / Real.sqrt N := by ring
  refine ⟨hcarrier, fun N hN => tailDiam_le (hpair N hN), ?_, ?_⟩
  · -- the tail diameter vanishes
    have hub : ∀ᶠ N : ℕ in atTop, tailDiam altPoint N ≤ 2 / Real.sqrt N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact tailDiam_le (hpair N hN)
    have hlb : ∀ᶠ N : ℕ in atTop, 0 ≤ tailDiam altPoint N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact tailDiam_nonneg (hpair N hN)
    have hlim : Tendsto (fun N : ℕ => 2 / Real.sqrt N) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
    exact squeeze_zero' hlb hub hlim
  · -- the adjacent defects are not summable
    intro hsum
    have hge : ∀ n : ℕ, 1 / ((n:ℝ) + 1) ≤ adjacentDefect altPoint n := by
      intro n
      have h1 : |altPoint (n + 1)| ≤ adjacentDefect altPoint n := by
        rw [adjacentDefect]
        rcases Nat.even_or_odd n with he | ho
        · -- n even: x n ≥ 0, x (n+1) ≤ 0
          have hxn : 0 ≤ altPoint n := by
            rw [altPoint, he.neg_one_pow]
            positivity
          have hxn1 : altPoint (n + 1) ≤ 0 := by
            rw [altPoint, Odd.neg_one_pow (by exact he.add_one), neg_div]
            exact neg_nonpos.mpr (by positivity)
          rw [abs_of_nonpos hxn1, abs_of_nonpos (by linarith)]
          linarith
        · -- n odd: x n ≤ 0, x (n+1) ≥ 0
          have hxn : altPoint n ≤ 0 := by
            rw [altPoint, ho.neg_one_pow, neg_div]
            exact neg_nonpos.mpr (by positivity)
          have hxn1 : 0 ≤ altPoint (n + 1) := by
            rw [altPoint, Even.neg_one_pow (by simpa using ho.add_one)]
            positivity
          rw [abs_of_nonneg hxn1, abs_of_nonneg (by linarith)]
          linarith
      have h2 : 1 / ((n:ℝ) + 1) ≤ |altPoint (n + 1)| := by
        rw [abs_altPoint]
        have hsq : Real.sqrt ((n:ℕ) + 1 : ℕ) ≤ (n:ℝ) + 1 := by
          push_cast
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) + 1 by positivity),
            Real.sqrt_nonneg ((n:ℝ) + 1), Nat.cast_nonneg (α := ℝ) n,
            sq_nonneg (Real.sqrt ((n:ℝ) + 1) - 1)]
        have hpos : (0:ℝ) < Real.sqrt ((n:ℕ) + 1 : ℕ) := by
          apply Real.sqrt_pos.mpr
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) n]
        apply one_div_le_one_div_of_le hpos
        exact hsq
      exact le_trans h2 h1
    have hharm : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) hge hsum
    have hharm' : Summable (fun n : ℕ => 1 / (n:ℝ)) := by
      have := (summable_nat_add_iff 1).mpr hharm
      simpa [add_comm] using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n:ℝ)) 1).mp
        (by simpa [Nat.cast_add, Nat.cast_one] using hharm)
    exact Real.not_summable_one_div_natCast hharm'

end AdjacentDefectWitness

end AdjacentDefectWitnessSection

/-! ### Low-island relative-moment reduction

Record `thm:GT-low-island-relative-moment` (LIR.1–LIR.8).

Rendering: the finite source card is `E = (m → ℂ)`, the carrier is
`𝒦 = (k → ℂ)`, the source-to-carrier map is the matrix `Q`, and
`K₀ = QᴴQ`, `A = D - K₀ ⪰ 0`, `P = 1_{[0,ρ]}(A)` (the island projection
`NCG.LowIsland.islandProj`), `K_j = QᴴW_jQ`, `Ω = I + ∑_j W_j`.  The
window (LIR.2) and relative edges (LIR.4) are the manuscript Loewner
hypotheses; the domain condition on `W_j^{1/2}` is vacuous on the finite
carrier.  LIR.5–LIR.6 are proved as Loewner inequalities, LIR.7 for the
normalized carrier of an arbitrary unit island vector, and LIR.8 in the
vectorwise `ℓ²` operator-norm form
`√R‖(1-Π_R)Q P x‖ ≤ √(κ⋆ d₊)‖x‖` for every `x`, which is exactly the
claimed operator-norm bound.  The least admissible relative edge is the
attained largest generalized Rayleigh quotient of `PK_jP` relative to
`PK₀P` on the island, and a failed relative bound returns an attained
unit island polarization. -/

section LowIslandRelativeMoment

open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur

namespace LowIslandRM

/-- Real scalars are self-adjoint in `ℂ`. -/
theorem ofReal_isSelfAdjoint (c : ℝ) : IsSelfAdjoint ((c : ℝ) : ℂ) := by
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

section VectorHelpers

variable {m : Type*} [Fintype m]

/-- The real part of the self-pairing is the sum of squared moduli. -/
theorem self_dot_re (v : m → ℂ) : (star v ⬝ᵥ v).re = ∑ j, ‖v j‖ ^ 2 := by
  rw [star_dot_self_eq_sum_sq]
  exact Complex.ofReal_re _

/-- The self-pairing is the complex lift of its real part. -/
theorem self_dot_ofReal (v : m → ℂ) : star v ⬝ᵥ v = (((star v ⬝ᵥ v).re : ℝ) : ℂ) := by
  rw [star_dot_self_eq_sum_sq, Complex.ofReal_re]

/-- The real self-pairing of a nonzero vector is positive. -/
theorem self_dot_pos {v : m → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [self_dot_re]
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
  have : v i ≠ 0 := by simpa using hi
  positivity

/-- Quadratic scaling of a real pairing under real rescaling. -/
theorem dot_smul_smul (a : ℝ) (M : Matrix m m ℂ) (v : m → ℂ) :
    (star ((a : ℂ) • v) ⬝ᵥ (M *ᵥ ((a : ℂ) • v))).re
      = a ^ 2 * (star v ⬝ᵥ (M *ᵥ v)).re := by
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring_nf

/-- The unit rescaling of a nonzero vector. -/
noncomputable def unitize (v : m → ℂ) : m → ℂ :=
  (((Real.sqrt (star v ⬝ᵥ v).re)⁻¹ : ℝ) : ℂ) • v

/-- The unit rescaling has unit self-pairing. -/
theorem unitize_dot {v : m → ℂ} (hv : v ≠ 0) : star (unitize v) ⬝ᵥ unitize v = 1 := by
  have hc := self_dot_pos hv
  unfold unitize
  rw [star_dot_self_eq_sum_sq, Complex.ofReal_eq_one]
  have hterm : ∀ i, ‖((((Real.sqrt (star v ⬝ᵥ v).re)⁻¹ : ℝ) : ℂ) • v) i‖ ^ 2
      = ((Real.sqrt (star v ⬝ᵥ v).re)⁻¹) ^ 2 * ‖v i‖ ^ 2 := by
    intro i
    rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
  simp only [hterm]
  rw [← Finset.mul_sum, ← self_dot_re, inv_pow, Real.sq_sqrt hc.le]
  exact inv_mul_cancel₀ hc.ne'

/-- Sandwich reduction of forms of `P M P` through a Hermitian `P`. -/
theorem sandwich_dot {P : Matrix m m ℂ} (hP : P.IsHermitian) (M : Matrix m m ℂ)
    (x : m → ℂ) :
    star x ⬝ᵥ ((P * M * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) := by
  rw [show P * M * P = P * (M * P) by rw [Matrix.mul_assoc], ← Matrix.mulVec_mulVec,
    adjoint_dot, hP.eq, Matrix.mulVec_mulVec]

/-- The self-pairing against a Hermitian idempotent is the squared norm of
the projected vector. -/
theorem proj_dot {P : Matrix m m ℂ} (hP : P.IsHermitian) (hidem : P * P = P)
    (x : m → ℂ) : star x ⬝ᵥ (P *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) :=
  calc star x ⬝ᵥ (P *ᵥ x) = star x ⬝ᵥ ((P * P) *ᵥ x) := by rw [hidem]
    _ = star (Pᴴ *ᵥ x) ⬝ᵥ (P *ᵥ x) := by rw [← Matrix.mulVec_mulVec, adjoint_dot]
    _ = star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by rw [hP.eq]

end VectorHelpers

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {J : Type*} [Fintype J]
variable {D : Matrix m m ℂ} {Q : Matrix k m ℂ}

section IslandData

variable (hA : (D - Qᴴ * Q).PosSemidef) (ρ : ℝ)

omit [DecidableEq k] in
/-- The island projection is idempotent. -/
theorem islandProj_idem :
    LowIsland.islandProj hA.1 ρ * LowIsland.islandProj hA.1 ρ
      = LowIsland.islandProj hA.1 ρ := by
  unfold LowIsland.islandProj
  rw [spectralFunction_mul]
  refine spectralFunction_congr hA.1 fun i => ?_
  split_ifs <;> norm_num

omit [DecidableEq k] in
/-- The island projection fixes its own range vectors. -/
theorem islandProj_fix (x : m → ℂ) :
    LowIsland.islandProj hA.1 ρ *ᵥ (LowIsland.islandProj hA.1 ρ *ᵥ x)
      = LowIsland.islandProj hA.1 ρ *ᵥ x := by
  rw [Matrix.mulVec_mulVec, islandProj_idem hA ρ]

/-- A nonzero island projection carries a unit island vector. -/
theorem exists_unit_island (hne : LowIsland.islandProj hA.1 ρ ≠ 0) :
    ∃ v, LowIsland.islandProj hA.1 ρ *ᵥ v = v ∧ star v ⬝ᵥ v = 1 := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hx : ∃ x, P *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (Matrix.ext fun i j => ?_)
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨x, hx⟩ := hx
  refine ⟨unitize (P *ᵥ x), ?_, unitize_dot hx⟩
  unfold unitize
  rw [Matrix.mulVec_smul, hPdef, islandProj_fix hA ρ]

end IslandData

section MainData

variable (hA : (D - Qᴴ * Q).PosSemidef) {ρ dlo dhi : ℝ}
variable {kap : J → ℝ} {W : J → Matrix k k ℂ}

omit [DecidableEq k] in
/-- `P K₀ P` is Hermitian. -/
theorem islandGram_isHermitian (ρ : ℝ) :
    (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q)
      * LowIsland.islandProj hA.1 ρ).IsHermitian := by
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hK : (Qᴴ * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self Q
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.eq, hK.eq]
  simp only [Matrix.mul_assoc]

omit [DecidableEq k] in
/-- `P (Qᴴ M Q) P` is Hermitian for Hermitian `M`. -/
theorem islandWeight_isHermitian {M : Matrix k k ℂ} (hM : M.IsHermitian) (ρ : ℝ) :
    (LowIsland.islandProj hA.1 ρ * (Qᴴ * M * Q)
      * LowIsland.islandProj hA.1 ρ).IsHermitian := by
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hK : (Qᴴ * M * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hM.eq]
    simp only [Matrix.mul_assoc]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP.eq, hK.eq]
  simp only [Matrix.mul_assoc]

omit [DecidableEq k] in
/-- **LIR.5, Loewner form**: `(d₋-ρ)P ⪯ PK₀P ⪯ d₊P` on the island. -/
theorem island_window (_hρ0 : 0 ≤ ρ)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef) :
    (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ
        - ((dlo - ρ : ℝ) : ℂ) • LowIsland.islandProj hA.1 ρ).PosSemidef ∧
      (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
        - LowIsland.islandProj hA.1 ρ * (Qᴴ * Q)
          * LowIsland.islandProj hA.1 ρ).PosSemidef := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hsplit : ∀ x : m → ℂ,
      star x ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ x)
        = star x ⬝ᵥ ((P * D * P) *ᵥ x)
          - star x ⬝ᵥ ((P * (D - Qᴴ * Q) * P) *ᵥ x) := by
    intro x
    rw [sandwich_dot hP, sandwich_dot hP, sandwich_dot hP, Matrix.sub_mulVec,
      dotProduct_sub]
    ring
  have hPAP := LowIsland.island_remainder_bound hA ρ
  constructor
  · refine posSemidef_of_re_form ((islandGram_isHermitian hA ρ).sub ?_) fun x => ?_
    · exact hP.smul (ofReal_isSelfAdjoint _)
    · have h1 := re_form_nonneg hlow x
      have h2 := re_form_nonneg hPAP x
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h1 h2 ⊢
      rw [hsplit, Complex.sub_re]
      have hsm : ∀ c : ℝ, (star x ⬝ᵥ (((c : ℂ) • P) *ᵥ x)).re
          = c * (star x ⬝ᵥ (P *ᵥ x)).re := by
        intro c
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
      rw [hsm] at h1 h2 ⊢
      have hsub : ((dlo : ℝ) - ρ) * (star x ⬝ᵥ (P *ᵥ x)).re
          = dlo * (star x ⬝ᵥ (P *ᵥ x)).re - ρ * (star x ⬝ᵥ (P *ᵥ x)).re := by ring
      rw [hsub]
      linarith
  · refine posSemidef_of_re_form (Matrix.IsHermitian.sub ?_ (islandGram_isHermitian hA ρ))
      fun x => ?_
    · exact hP.smul (ofReal_isSelfAdjoint _)
    · have h1 := re_form_nonneg hhi x
      have hApsd : (P * (D - Qᴴ * Q) * P).PosSemidef := by
        have := hA.mul_mul_conjTranspose_same P
        rwa [hP.eq] at this
      have h2 := re_form_nonneg hApsd x
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at h1 ⊢
      rw [hsplit, Complex.sub_re]
      linarith

/-- Island heads never vanish: `Qv ≠ 0` for every nonzero island vector. -/
theorem island_head_ne_zero (hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef)
    {v : m → ℂ} (hv : LowIsland.islandProj hA.1 ρ *ᵥ v = v) (hvne : v ≠ 0) :
    Q *ᵥ v ≠ 0 := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  intro hQv
  have hfloor := re_form_nonneg (island_window hA hρ0 hlow hhi).1 v
  have hform : star v ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ v)
      = star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) := by
    rw [sandwich_dot (LowIsland.islandProj_isHermitian hA.1 ρ), hv,
      ← Matrix.mulVec_mulVec, adjoint_dot, Matrix.conjTranspose_conjTranspose]
  have hPv : star v ⬝ᵥ ((((dlo - ρ : ℝ) : ℂ) • P) *ᵥ v)
      = ((dlo - ρ : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
    rw [Matrix.smul_mulVec, hv, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hform, hPv, hQv] at hfloor
  have hpos := self_dot_pos hvne
  have hre : (((dlo - ρ : ℝ) : ℂ) * (star v ⬝ᵥ v)).re
      = (dlo - ρ) * (star v ⬝ᵥ v).re := Complex.re_ofReal_mul _ _
  rw [hre] at hfloor
  simp only [dotProduct_zero, Complex.zero_re] at hfloor
  nlinarith

omit [Fintype J] in
/-- The relative edges are nonnegative once the island is occupied. -/
theorem kappa_nonneg (hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hne : LowIsland.islandProj hA.1 ρ ≠ 0)
    (hW : ∀ j, (W j).PosSemidef)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hkap : ∀ j, ((kap j : ℂ)
        • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
      - LowIsland.islandProj hA.1 ρ * (Qᴴ * W j * Q)
        * LowIsland.islandProj hA.1 ρ).PosSemidef) (j : J) :
    0 ≤ kap j := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  obtain ⟨v, hv, hunit⟩ := exists_unit_island hA ρ hne
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hunit
    simp at hunit
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hK0 : star v ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ v)
      = star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) := by
    rw [sandwich_dot hP, hv, ← Matrix.mulVec_mulVec, adjoint_dot,
      Matrix.conjTranspose_conjTranspose]
  have hKj : star v ⬝ᵥ ((P * (Qᴴ * W j * Q) * P) *ᵥ v)
      = star (Q *ᵥ v) ⬝ᵥ (W j *ᵥ (Q *ᵥ v)) := by
    rw [sandwich_dot hP, hv, LowIsland.dot_conj_weight]
  have hQv : Q *ᵥ v ≠ 0 := island_head_ne_zero hA hρ0 hd hlow hhi hv hvne
  have hnum := re_form_nonneg (hW j) (Q *ᵥ v)
  have hedge := re_form_nonneg (hkap j) v
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hK0, hKj] at hedge
  have hden := self_dot_pos hQv
  nlinarith

/-- **LIR.6, Loewner form**: `PQᴴΩQP ⪯ κ⋆ PK₀P ⪯ κ⋆ d₊ P` with
`Ω = I + ∑ W_j` and `κ⋆ = 1 + ∑ κ_j`. -/
theorem island_weighted_window (hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hne : LowIsland.islandProj hA.1 ρ ≠ 0)
    (hW : ∀ j, (W j).PosSemidef)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hkap : ∀ j, ((kap j : ℂ)
        • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
      - LowIsland.islandProj hA.1 ρ * (Qᴴ * W j * Q)
        * LowIsland.islandProj hA.1 ρ).PosSemidef) :
    (((1 + ∑ j, kap j : ℝ) : ℂ)
        • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
      - LowIsland.islandProj hA.1 ρ
          * (Qᴴ * ((1 : Matrix k k ℂ) + ∑ j, W j) * Q)
          * LowIsland.islandProj hA.1 ρ).PosSemidef ∧
      ((((1 + ∑ j, kap j) * dhi : ℝ) : ℂ) • LowIsland.islandProj hA.1 ρ
        - ((1 + ∑ j, kap j : ℝ) : ℂ)
            • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q)
              * LowIsland.islandProj hA.1 ρ)).PosSemidef := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hkapnn : ∀ j, 0 ≤ kap j := fun j =>
    kappa_nonneg hA hρ0 hd hne hW hlow hhi hkap j
  have hstar : (0 : ℝ) ≤ 1 + ∑ j, kap j := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hkapnn j
    linarith
  constructor
  · -- expand Ω and telescope against the relative edges
    have hexp : P * (Qᴴ * ((1 : Matrix k k ℂ) + ∑ j, W j) * Q) * P
        = P * (Qᴴ * Q) * P + ∑ j, P * (Qᴴ * W j * Q) * P := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum,
        Matrix.sum_mul]
    have hsm : (((1 + ∑ j, kap j : ℝ) : ℂ)) • (P * (Qᴴ * Q) * P)
        = P * (Qᴴ * Q) * P + ∑ j, ((kap j : ℝ) : ℂ) • (P * (Qᴴ * Q) * P) := by
      push_cast
      rw [add_smul, one_smul, Finset.sum_smul]
    rw [hexp, hsm]
    have hgoal : P * (Qᴴ * Q) * P + ∑ j, ((kap j : ℝ) : ℂ) • (P * (Qᴴ * Q) * P)
          - (P * (Qᴴ * Q) * P + ∑ j, P * (Qᴴ * W j * Q) * P)
        = ∑ j, (((kap j : ℝ) : ℂ) • (P * (Qᴴ * Q) * P)
            - P * (Qᴴ * W j * Q) * P) := by
      rw [Finset.sum_sub_distrib]
      abel
    rw [hgoal]
    exact Matrix.posSemidef_sum _ fun j _ => hkap j
  · -- rescale the upper island window by the nonnegative κ⋆
    have hup := (island_window hA hρ0 hlow hhi).2
    have hfact : ((((1 + ∑ j, kap j) * dhi : ℝ) : ℂ)) • P
          - (((1 + ∑ j, kap j : ℝ) : ℂ)) • (P * (Qᴴ * Q) * P)
        = (((1 + ∑ j, kap j : ℝ) : ℂ))
            • (((dhi : ℂ)) • P - P * (Qᴴ * Q) * P) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul]
    rw [hfact]
    have hnn : (0 : ℂ) ≤ ((1 + ∑ j, kap j : ℝ) : ℂ) := by
      rw [Complex.le_def]
      constructor
      · simpa using hstar
      · simp
    exact hup.smul hnn

omit [DecidableEq k] in
/-- Continuity of the real quadratic form of a fixed matrix. -/
theorem continuous_re_form (M : Matrix k k ℂ) :
    Continuous fun z : k → ℂ => (star z ⬝ᵥ (M *ᵥ z)).re := by
  refine Complex.continuous_re.comp ?_
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ ?_
  · exact (continuous_apply i).star
  · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

omit [DecidableEq k] in
/-- Continuity of the real self-pairing. -/
theorem continuous_re_dot : Continuous fun z : k → ℂ => (star z ⬝ᵥ z).re := by
  refine Complex.continuous_re.comp ?_
  simp only [dotProduct]
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i).star).mul (continuous_apply i)

/-- **LIR.7**: the normalized carrier `w = Qv/‖Qv‖` of every unit island
vector is a unit carrier vector of weighted mass at most `κ⋆`. -/
theorem island_carrier_bound (hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hne : LowIsland.islandProj hA.1 ρ ≠ 0)
    (hW : ∀ j, (W j).PosSemidef)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hkap : ∀ j, ((kap j : ℂ)
        • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
      - LowIsland.islandProj hA.1 ρ * (Qᴴ * W j * Q)
        * LowIsland.islandProj hA.1 ρ).PosSemidef)
    {v : m → ℂ} (hv : LowIsland.islandProj hA.1 ρ *ᵥ v = v)
    (hunit : star v ⬝ᵥ v = 1) :
    star (unitize (Q *ᵥ v)) ⬝ᵥ unitize (Q *ᵥ v) = 1 ∧
      (star (unitize (Q *ᵥ v)) ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j)
        *ᵥ unitize (Q *ᵥ v))).re ≤ 1 + ∑ j, kap j := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hunit
    simp at hunit
  have hQv : Q *ᵥ v ≠ 0 := island_head_ne_zero hA hρ0 hd hlow hhi hv hvne
  have hc := self_dot_pos hQv
  refine ⟨unitize_dot hQv, ?_⟩
  -- the un-normalized weighted mass obeys the island edge
  have hwin := (island_weighted_window hA hρ0 hd hne hW hlow hhi hkap).1
  have hform := re_form_nonneg hwin v
  have hΩ : star v ⬝ᵥ ((P * (Qᴴ * ((1 : Matrix k k ℂ) + ∑ j, W j) * Q) * P) *ᵥ v)
      = star (Q *ᵥ v) ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ (Q *ᵥ v)) := by
    rw [sandwich_dot hP, hv, LowIsland.dot_conj_weight]
  have hK0 : star v ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ v)
      = star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) := by
    rw [sandwich_dot hP, hv, ← Matrix.mulVec_mulVec, adjoint_dot,
      Matrix.conjTranspose_conjTranspose]
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hΩ, hK0] at hform
  -- rescale to the unit carrier
  have hsq : ((Real.sqrt (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re)⁻¹) ^ 2
      = ((star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hc.le]
  have hscale := dot_smul_smul (Real.sqrt (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re)⁻¹
    ((1 : Matrix k k ℂ) + ∑ j, W j) (Q *ᵥ v)
  unfold unitize
  rw [hscale, hsq]
  rw [inv_mul_le_iff₀ hc]
  calc (star (Q *ᵥ v) ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ (Q *ᵥ v))).re
      ≤ (1 + ∑ j, kap j) * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re := by linarith
    _ = (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re * (1 + ∑ j, kap j) := by ring

/-- **LIR.8** (vectorwise `ℓ²` operator-norm form): for every source vector
`x`, `R‖(1-Π_R)QPx‖² ≤ κ⋆d₊‖x‖²`, hence
`√R‖(1-Π_R)QPx‖ ≤ √(κ⋆d₊)‖x‖`. -/
theorem island_tail_norm (hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hne : LowIsland.islandProj hA.1 ρ ≠ 0)
    (hW : ∀ j, (W j).PosSemidef)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hhi : (((dhi : ℂ)) • LowIsland.islandProj hA.1 ρ
      - LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ).PosSemidef)
    (hkap : ∀ j, ((kap j : ℂ)
        • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
      - LowIsland.islandProj hA.1 ρ * (Qᴴ * W j * Q)
        * LowIsland.islandProj hA.1 ρ).PosSemidef)
    (R : ℝ) (x : m → ℂ) :
    R * (star (((1 : Matrix k k ℂ)
          - LowIsland.sublevelProj (LowIsland.weightSum_posSemidef hW).1 R)
          *ᵥ (Q *ᵥ (LowIsland.islandProj hA.1 ρ *ᵥ x)))
        ⬝ᵥ (((1 : Matrix k k ℂ)
          - LowIsland.sublevelProj (LowIsland.weightSum_posSemidef hW).1 R)
          *ᵥ (Q *ᵥ (LowIsland.islandProj hA.1 ρ *ᵥ x)))).re
      ≤ (1 + ∑ j, kap j) * dhi * (star x ⬝ᵥ x).re := by
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  set z := Q *ᵥ (P *ᵥ x) with hzdef
  set Pi1 := (1 : Matrix k k ℂ)
    - LowIsland.sublevelProj (LowIsland.weightSum_posSemidef hW).1 R with hPi1
  -- the spectral tail estimate at `z`
  have hPi1herm : Pi1.IsHermitian := by
    rw [hPi1]
    exact Matrix.isHermitian_one.sub
      (LowIsland.sublevelProj_projection (LowIsland.weightSum_posSemidef hW).1 R).1
  have hPi1idem : Pi1 * Pi1 = Pi1 := by
    rw [hPi1, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul,
      (LowIsland.sublevelProj_projection (LowIsland.weightSum_posSemidef hW).1 R).2,
      Matrix.mul_one]
    abel
  have htail := re_form_nonneg
    (LowIsland.sublevel_tail_psd (LowIsland.weightSum_posSemidef hW) R) z
  have hq : star z ⬝ᵥ (Pi1 *ᵥ z) = star (Pi1 *ᵥ z) ⬝ᵥ (Pi1 *ᵥ z) := by
    rw [LowIsland.dot_conj Pi1 z, hPi1herm.eq, hPi1idem]
  have hsm2 : star z ⬝ᵥ (((R : ℂ) • Pi1) *ᵥ z)
      = (R : ℂ) * (star z ⬝ᵥ (Pi1 *ᵥ z)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hsm2, hq,
    Complex.re_ofReal_mul] at htail
  -- the weighted island mass bounds the carrier form
  have hwin := island_weighted_window hA hρ0 hd hne hW hlow hhi hkap
  have hform1 := re_form_nonneg hwin.1 (P *ᵥ x)
  have hfix : P *ᵥ (P *ᵥ x) = P *ᵥ x := islandProj_fix hA ρ x
  have hΩ : star (P *ᵥ x) ⬝ᵥ ((P * (Qᴴ * ((1 : Matrix k k ℂ) + ∑ j, W j) * Q) * P)
      *ᵥ (P *ᵥ x)) = star z ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ z) := by
    rw [sandwich_dot hP, hfix, hzdef]
    exact (LowIsland.dot_conj_weight Q ((1 : Matrix k k ℂ) + ∑ j, W j)
      (P *ᵥ x)).symm
  have hK0 : star (P *ᵥ x) ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ (P *ᵥ x))
      = star z ⬝ᵥ z := by
    rw [sandwich_dot hP, hfix, hzdef, ← Matrix.mulVec_mulVec, adjoint_dot,
      Matrix.conjTranspose_conjTranspose]
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hΩ, hK0] at hform1
  -- the island head mass is bounded by `d₊` on `Px`
  have hform2 := re_form_nonneg hwin.2 (P *ᵥ x)
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hK0, hfix] at hform2
  -- `‖Px‖ ≤ ‖x‖` for the Hermitian idempotent island projection
  have hidem : P * P = P := islandProj_idem hA ρ
  have hcontr : (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
    have h1 : star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = star x ⬝ᵥ (P *ᵥ x) :=
      (proj_dot hP hidem x).symm
    have hyx : star (P *ᵥ x) ⬝ᵥ x = star x ⬝ᵥ (P *ᵥ x) := by
      have h := adjoint_dot P x x
      rw [hP.eq] at h
      exact h.symm
    have h2 : star (x - P *ᵥ x) ⬝ᵥ (x - P *ᵥ x)
        = star x ⬝ᵥ x - star x ⬝ᵥ (P *ᵥ x) := by
      rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hyx, h1]
      ring
    have h4 : 0 ≤ (star (x - P *ᵥ x) ⬝ᵥ (x - P *ᵥ x)).re := by
      rw [self_dot_re]
      positivity
    have h5 := congrArg Complex.re h2
    rw [Complex.sub_re] at h5
    have h6 := congrArg Complex.re h1
    linarith
  -- `dhi` and `κ⋆` are nonnegative
  obtain ⟨w, hw, hwunit⟩ := exists_unit_island hA ρ hne
  have hdhi : 0 ≤ dhi := by
    have h1 := LowIsland.island_floor hA hlow hw hwunit
    have h2 := LowIsland.island_mass_upper hA hhi hw hwunit
    linarith
  have hkapnn : ∀ j, 0 ≤ kap j := fun j =>
    kappa_nonneg hA hρ0 hd hne hW hlow hhi hkap j
  have hstar : (0 : ℝ) ≤ 1 + ∑ j, kap j := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hkapnn j
    linarith
  have hchain : (star z ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ z)).re
      ≤ (1 + ∑ j, kap j) * dhi * (star x ⬝ᵥ x).re := by
    calc (star z ⬝ᵥ (((1 : Matrix k k ℂ) + ∑ j, W j) *ᵥ z)).re
        ≤ (1 + ∑ j, kap j) * (star z ⬝ᵥ z).re := by linarith
      _ ≤ (1 + ∑ j, kap j) * dhi * (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x)).re := by
          linarith
      _ ≤ (1 + ∑ j, kap j) * dhi * (star x ⬝ᵥ x).re := by
          exact mul_le_mul_of_nonneg_left hcontr (mul_nonneg hstar hdhi)
  linarith

/-- The island Rayleigh-ratio set of a carrier weight relative to the head
Gram: the generalized eigenvalue quotients over unit island vectors. -/
def edgeRatios (P : Matrix m m ℂ) (Q : Matrix k m ℂ) (Wj : Matrix k k ℂ) :
    Set ℝ :=
  {r | ∃ v, P *ᵥ v = v ∧ star v ⬝ᵥ v = 1 ∧
    r = (star (Q *ᵥ v) ⬝ᵥ (Wj *ᵥ (Q *ᵥ v))).re / (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re}

set_option maxHeartbeats 800000 in
-- the compactness extraction and the Loewner equivalence instantiate the
-- island spectral calculus repeatedly; the default budget is too small
/-- **LIR: attained least relative edge.**  On the finite card, the least
admissible relative edge `κ_j` is the attained largest generalized Rayleigh
quotient of `PK_jP` relative to `PK₀P` on the island: the quotient set has a
greatest element `κm`, the relative-edge inequality (LIR.4) holds for `c`
exactly when `κm ≤ c`, and every failed relative bound returns an attained
unit island polarization. -/
theorem relative_edge_attained (_hρ0 : 0 ≤ ρ) (hd : ρ < dlo)
    (hne : LowIsland.islandProj hA.1 ρ ≠ 0)
    (hlow : (LowIsland.islandProj hA.1 ρ * D * LowIsland.islandProj hA.1 ρ
      - ((dlo : ℂ)) • LowIsland.islandProj hA.1 ρ).PosSemidef)
    {Wj : Matrix k k ℂ} (hWj : Wj.IsHermitian) :
    ∃ κm : ℝ, IsGreatest (edgeRatios (LowIsland.islandProj hA.1 ρ) Q Wj) κm ∧
      (∀ c : ℝ, (((c : ℝ) : ℂ)
          • (LowIsland.islandProj hA.1 ρ * (Qᴴ * Q) * LowIsland.islandProj hA.1 ρ)
        - LowIsland.islandProj hA.1 ρ * (Qᴴ * Wj * Q)
          * LowIsland.islandProj hA.1 ρ).PosSemidef ↔ κm ≤ c) ∧
      ∀ c : ℝ, c < κm → ∃ v, LowIsland.islandProj hA.1 ρ *ᵥ v = v ∧
        star v ⬝ᵥ v = 1 ∧
        c * (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re
          < (star (Q *ᵥ v) ⬝ᵥ (Wj *ᵥ (Q *ᵥ v))).re := by
  classical
  set P := LowIsland.islandProj hA.1 ρ with hPdef
  have hP := LowIsland.islandProj_isHermitian hA.1 ρ
  set Sph := {v : m → ℂ | P *ᵥ v = v ∧ star v ⬝ᵥ v = 1} with hSph
  set num : (m → ℂ) → ℝ := fun v => (star (Q *ᵥ v) ⬝ᵥ (Wj *ᵥ (Q *ᵥ v))).re
    with hnum
  set den : (m → ℂ) → ℝ := fun v => (star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v)).re with hden
  -- the denominator is uniformly positive on the island sphere
  have hdenpos : ∀ v ∈ Sph, 0 < den v := by
    rintro v ⟨hv, hunit⟩
    have := LowIsland.island_floor hA hlow hv hunit
    rw [hden]
    dsimp only
    linarith
  -- compactness of the island sphere
  have hQcont : Continuous fun v : m → ℂ => Q *ᵥ v :=
    continuous_const.matrix_mulVec continuous_id
  have hclosed : IsClosed Sph := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_id) (isClosed_eq ?_ continuous_const)
    · exact continuous_const.matrix_mulVec continuous_id
    · simp only [dotProduct]
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).star).mul (continuous_apply i)
  have hbounded : Bornology.IsBounded Sph := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, ?_⟩
    rintro v ⟨_, hunit⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsum : ∑ j, ‖v j‖ ^ 2 = 1 := by
      have := self_dot_re v
      rw [hunit] at this
      simpa using this.symm
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
    have hterm : ‖v i‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hcompact : IsCompact Sph := Metric.isCompact_of_isClosed_isBounded
    hclosed hbounded
  have hnonempty : Sph.Nonempty := by
    obtain ⟨v, hv, hunit⟩ := exists_unit_island hA ρ hne
    exact ⟨v, hv, hunit⟩
  -- the Rayleigh quotient attains its maximum on the sphere
  have hcont : ContinuousOn (fun v => num v / den v) Sph := by
    refine ContinuousOn.div ?_ ?_ fun v hv => (hdenpos v hv).ne'
    · exact ((continuous_re_form Wj).comp hQcont).continuousOn
    · exact (continuous_re_dot.comp hQcont).continuousOn
  obtain ⟨vs, hvs, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  refine ⟨num vs / den vs, ⟨⟨vs, hvs.1, hvs.2, rfl⟩, ?_⟩, fun c => ⟨?_, ?_⟩, ?_⟩
  · -- upper bound of the ratio set
    rintro r ⟨v, hv1, hv2, rfl⟩
    exact hmax (show v ∈ Sph from ⟨hv1, hv2⟩)
  · -- a valid Loewner edge dominates the attained quotient
    intro hpsd
    have hform := re_form_nonneg hpsd vs
    have hK0 : star vs ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ vs)
        = star (Q *ᵥ vs) ⬝ᵥ (Q *ᵥ vs) := by
      rw [sandwich_dot hP, hvs.1, ← Matrix.mulVec_mulVec, adjoint_dot,
        Matrix.conjTranspose_conjTranspose]
    have hKj : star vs ⬝ᵥ ((P * (Qᴴ * Wj * Q) * P) *ᵥ vs)
        = star (Q *ᵥ vs) ⬝ᵥ (Wj *ᵥ (Q *ᵥ vs)) := by
      rw [sandwich_dot hP, hvs.1, LowIsland.dot_conj_weight]
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hK0, hKj] at hform
    rw [div_le_iff₀ (hdenpos vs hvs)]
    change (star (Q *ᵥ vs) ⬝ᵥ (Wj *ᵥ (Q *ᵥ vs))).re
        ≤ c * (star (Q *ᵥ vs) ⬝ᵥ (Q *ᵥ vs)).re
    linarith
  · -- a dominating scalar is a valid Loewner edge
    intro hc
    refine posSemidef_of_re_form
      (Matrix.IsHermitian.sub ((islandGram_isHermitian hA ρ).smul
        (ofReal_isSelfAdjoint c)) (islandWeight_isHermitian hA hWj ρ))
      fun x => ?_
    have hfix : P *ᵥ (P *ᵥ x) = P *ᵥ x := islandProj_fix hA ρ x
    have hK0 : star x ⬝ᵥ ((P * (Qᴴ * Q) * P) *ᵥ x)
        = star (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Q *ᵥ (P *ᵥ x)) := by
      rw [sandwich_dot hP, ← Matrix.mulVec_mulVec, adjoint_dot,
        Matrix.conjTranspose_conjTranspose]
    have hKj : star x ⬝ᵥ ((P * (Qᴴ * Wj * Q) * P) *ᵥ x)
        = star (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Wj *ᵥ (Q *ᵥ (P *ᵥ x))) := by
      rw [sandwich_dot hP]
      exact (LowIsland.dot_conj_weight Q Wj (P *ᵥ x)).symm
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hK0, hKj]
    by_cases hz : Q *ᵥ (P *ᵥ x) = 0
    · rw [hz]
      simp
    · -- normalize the island component and use the attained maximum
      have hy : P *ᵥ x ≠ 0 := by
        intro h0
        rw [h0, Matrix.mulVec_zero] at hz
        exact hz rfl
      set a := (Real.sqrt (star (P *ᵥ x) ⬝ᵥ (P *ᵥ x)).re)⁻¹ with hadef
      have hcpos := self_dot_pos hy
      have hapos : 0 < a := by
        rw [hadef]
        positivity
      have humem : unitize (P *ᵥ x) ∈ Sph := by
        refine ⟨?_, unitize_dot hy⟩
        unfold unitize
        rw [Matrix.mulVec_smul, hfix]
      have hratio : num (unitize (P *ᵥ x)) / den (unitize (P *ᵥ x))
          ≤ num vs / den vs := hmax humem
      have hQu : Q *ᵥ unitize (P *ᵥ x) = (a : ℂ) • (Q *ᵥ (P *ᵥ x)) := by
        unfold unitize
        rw [Matrix.mulVec_smul, hadef]
      have hnum_scale : num (unitize (P *ᵥ x))
          = a ^ 2 * (star (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Wj *ᵥ (Q *ᵥ (P *ᵥ x)))).re := by
        rw [hnum]
        dsimp only
        rw [hQu]
        exact dot_smul_smul a Wj (Q *ᵥ (P *ᵥ x))
      have hden_scale : den (unitize (P *ᵥ x))
          = a ^ 2 * (star (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Q *ᵥ (P *ᵥ x))).re := by
        rw [hden]
        dsimp only
        rw [hQu]
        have hone := dot_smul_smul a 1 (Q *ᵥ (P *ᵥ x))
        rw [Matrix.one_mulVec, Matrix.one_mulVec] at hone
        exact hone
      have hdenu : 0 < den (unitize (P *ᵥ x)) := hdenpos _ humem
      have hkey : num (unitize (P *ᵥ x)) ≤ c * den (unitize (P *ᵥ x)) := by
        have h1 : num (unitize (P *ᵥ x)) / den (unitize (P *ᵥ x)) ≤ c :=
          le_trans hratio hc
        rwa [div_le_iff₀ hdenu] at h1
      rw [hnum_scale, hden_scale] at hkey
      have ha2 : 0 < a ^ 2 := by positivity
      nlinarith
  · -- a failed edge returns the attained island polarization
    intro c hclt
    refine ⟨vs, hvs.1, hvs.2, ?_⟩
    have hdvs := hdenpos vs hvs
    have h1 : c < num vs / den vs := hclt
    rw [lt_div_iff₀ hdvs] at h1
    rw [hnum, hden] at h1
    dsimp only at h1
    linarith

end MainData

end LowIslandRM

end LowIslandRelativeMoment

/-! ### Exact critical centring and dispersion action

Record `thm:NS-critical-centred-target` (NSE.8–NSE.9).

Rendering: the abstract clauses (orthogonal-projection characterization of
`ψ` onto the physical carrier `ℋ_e = e^⊥` and the incidence identities
NSE.8) are proved on an arbitrary complex inner-product space, reusing the
`NSPay` packet of `EasyExact01`.  The spectral clauses (the exact value of
`𝒱_c` in NSE.9 through `‖A^{1/2}u‖⁴/‖A^{1/4}u‖²` and the one-modulus
characterization of `𝒱_c = 0`) are proved on the finite spectral Galerkin
model of the critical packet: a finite frequency card `K` with strictly
positive moduli `κ` of `Λ = A^{1/2}` and amplitudes `u`, with
`e = Λ^{1/2}u`, `v = Λ^{3/2}u`, `Λu` the diagonal actions (NSE.1). -/

section CriticalCentredTarget

open scoped ComplexInnerProductSpace

namespace NSCentred

section AbstractProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **NSE.8 (projection clause)**: the centred target `ψ = v - κ̄e` is the
orthogonal projection of `v` to the physical source carrier
`ℋ_e = {x : Re⟪x,e⟫ = 0}` (NSE.5): it lies in the carrier, it is the
unique closest carrier point to `v`, and it satisfies the incidence
identities `Re⟪ψ,e⟫ = 0`, `Φ_c = -Re⟪c,ψ⟫`. -/
theorem centred_is_projection (e c v : H) (he : e ≠ 0)
    (hce : (⟪c, e⟫).re = 0) :
    (⟪NSPay.centred e v, e⟫).re = 0 ∧
      NSPay.work c v = -(⟪c, NSPay.centred e v⟫).re ∧
      ∀ x : H, (⟪x, e⟫).re = 0 →
        ‖v - NSPay.centred e v‖ ≤ ‖v - x‖ ∧
          (‖v - x‖ = ‖v - NSPay.centred e v‖ → x = NSPay.centred e v) := by
  refine ⟨NSPay.re_inner_centred_right e v he, NSPay.work_eq_centred e c v hce,
    fun x hx => ?_⟩
  have hdiff : v - NSPay.centred e v = ((NSPay.centre e v : ℝ) : ℂ) • e := by
    unfold NSPay.centred
    abel
  have hsplit : ‖v - x‖ ^ 2
      = ‖v - NSPay.centred e v‖ ^ 2 + ‖NSPay.centred e v - x‖ ^ 2 := by
    have hdec : v - x = (v - NSPay.centred e v) + (NSPay.centred e v - x) := by
      abel
    have hcross : (⟪v - NSPay.centred e v, NSPay.centred e v - x⟫).re = 0 := by
      rw [hdiff, NSPay.re_inner_ofReal_smul_left, inner_sub_right,
        Complex.sub_re, NSPay.re_inner_centred_left e v he, cre_inner_symm e x,
        hx, sub_zero, mul_zero]
    rw [hdec, cnorm_add_sq, hcross]
    ring
  have hle : ‖v - NSPay.centred e v‖ ^ 2 ≤ ‖v - x‖ ^ 2 := by
    rw [hsplit]
    nlinarith [sq_nonneg ‖NSPay.centred e v - x‖]
  constructor
  · by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (v - x), norm_nonneg (v - NSPay.centred e v)]
  · intro heq
    have hz : ‖NSPay.centred e v - x‖ ^ 2 = 0 := by
      rw [heq] at hsplit
      linarith
    have := (pow_eq_zero_iff two_ne_zero).mp hz
    rw [norm_eq_zero, sub_eq_zero] at this
    exact this.symm

end AbstractProjection

section GalerkinModel

variable {K : Type*} [Fintype K]

/-- The Galerkin energy vector `e = A^{1/4}u = Λ^{1/2}u` (NSE.1). -/
noncomputable def galE (κ : K → ℝ) (u : K → ℂ) : EuclideanSpace ℂ K :=
  WithLp.toLp 2 fun j => ((Real.sqrt (κ j) : ℝ) : ℂ) * u j

/-- The Galerkin critical target `v = A^{3/4}u = Λ^{3/2}u` (NSE.1). -/
noncomputable def galV (κ : K → ℝ) (u : K → ℂ) : EuclideanSpace ℂ K :=
  WithLp.toLp 2 fun j => ((κ j : ℝ) : ℂ) * (((Real.sqrt (κ j) : ℝ) : ℂ) * u j)

/-- The Galerkin frequency image `Λu = A^{1/2}u`. -/
noncomputable def galLam (κ : K → ℝ) (u : K → ℂ) : EuclideanSpace ℂ K :=
  WithLp.toLp 2 fun j => ((κ j : ℝ) : ℂ) * u j

omit [Fintype K] in
/-- Componentwise form of the energy vector. -/
theorem galE_apply (κ : K → ℝ) (u : K → ℂ) (j : K) :
    galE κ u j = ((Real.sqrt (κ j) : ℝ) : ℂ) * u j := rfl

omit [Fintype K] in
/-- Componentwise form of the critical target. -/
theorem galV_apply (κ : K → ℝ) (u : K → ℂ) (j : K) :
    galV κ u j = ((κ j : ℝ) : ℂ) * (((Real.sqrt (κ j) : ℝ) : ℂ) * u j) := rfl

omit [Fintype K] in
/-- Componentwise form of the frequency image. -/
theorem galLam_apply (κ : K → ℝ) (u : K → ℂ) (j : K) :
    galLam κ u j = ((κ j : ℝ) : ℂ) * u j := rfl

/-- The squared energy norm `‖e‖² = ∑ κ_j ‖u_j‖²`. -/
theorem galE_norm_sq {κ : K → ℝ} (hκ : ∀ j, 0 ≤ κ j) (u : K → ℂ) :
    ‖galE κ u‖ ^ 2 = ∑ j, κ j * ‖u j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [galE_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hκ j)]

/-- The squared frequency norm `‖Λu‖² = ∑ κ_j² ‖u_j‖²`. -/
theorem galLam_norm_sq (κ : K → ℝ) (u : K → ℂ) :
    ‖galLam κ u‖ ^ 2 = ∑ j, κ j ^ 2 * ‖u j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [galLam_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]

/-- The spectral pairing identity `Re⟪e,v⟫ = ‖Λu‖²` (behind NSE.6). -/
theorem re_inner_galE_galV {κ : K → ℝ} (hκ : ∀ j, 0 ≤ κ j) (u : K → ℂ) :
    (⟪galE κ u, galV κ u⟫).re = ‖galLam κ u‖ ^ 2 := by
  rw [galLam_norm_sq, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [galE_apply, galV_apply, RCLike.inner_apply]
  have hsq : ((Real.sqrt (κ j) : ℝ) : ℂ) * ((Real.sqrt (κ j) : ℝ) : ℂ)
      = ((κ j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκ j)]
  have hexp : ((κ j : ℝ) : ℂ) * (((Real.sqrt (κ j) : ℝ) : ℂ) * u j)
      * (starRingEnd ℂ) (((Real.sqrt (κ j) : ℝ) : ℂ) * u j)
      = ((κ j ^ 2 : ℝ) : ℂ) * (u j * (starRingEnd ℂ) (u j)) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (((κ j : ℝ) : ℂ) * u j * (starRingEnd ℂ) (u j)) * hsq
  rw [hexp, Complex.mul_conj']
  rw [show ((κ j ^ 2 : ℝ) : ℂ) * (‖u j‖ : ℂ) ^ 2
      = ((κ j ^ 2 * ‖u j‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.ofReal_re]

/-- The critical frequency centre in the Galerkin model:
`κ̄ = ‖A^{1/2}u‖²/‖A^{1/4}u‖²` (NSE.6). -/
theorem galerkin_centre {κ : K → ℝ} (hκ : ∀ j, 0 ≤ κ j) (u : K → ℂ) :
    NSPay.centre (galE κ u) (galV κ u)
      = ‖galLam κ u‖ ^ 2 / ‖galE κ u‖ ^ 2 := by
  unfold NSPay.centre
  rw [re_inner_galE_galV hκ]

omit [Fintype K] in
/-- The energy vector of a nonzero packet is nonzero. -/
theorem galE_ne_zero {κ : K → ℝ} (hκ : ∀ j, 0 < κ j) {u : K → ℂ}
    (hu : u ≠ 0) : galE κ u ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
  intro hcon
  have hzero : galE κ u j = 0 := by rw [hcon]; rfl
  rw [galE_apply] at hzero
  have hs : ((Real.sqrt (κ j) : ℝ) : ℂ) ≠ 0 := by
    simpa using (Real.sqrt_pos.mpr (hκ j)).ne'
  exact hj (by simpa [hs] using hzero)

/-- **NSE.9**: the exact dispersion action
`𝒱_c = 𝒟_c - ‖A^{1/2}u‖⁴/‖A^{1/4}u‖²` with `0 ≤ 𝒱_c ≤ 𝒟_c`. -/
theorem dispersion_action {κ : K → ℝ} (hκ : ∀ j, 0 < κ j) {u : K → ℂ}
    (hu : u ≠ 0) :
    NSPay.vres (galE κ u) (galV κ u)
        = ‖galV κ u‖ ^ 2 - ‖galLam κ u‖ ^ 2 ^ 2 / ‖galE κ u‖ ^ 2 ∧
      0 ≤ NSPay.vres (galE κ u) (galV κ u) ∧
      NSPay.vres (galE κ u) (galV κ u) ≤ ‖galV κ u‖ ^ 2 := by
  have he := galE_ne_zero hκ hu
  have hepos : 0 < ‖galE κ u‖ ^ 2 := by
    have := norm_pos_iff.mpr he
    positivity
  have hsplit := NSPay.target_normsq_split (galE κ u) (galV κ u) he
  have hcentre := galerkin_centre (fun j => (hκ j).le) u
  have hV0 : 0 ≤ NSPay.vres (galE κ u) (galV κ u) := by
    unfold NSPay.vres
    positivity
  refine ⟨?_, hV0, ?_⟩
  · rw [hcentre] at hsplit
    rw [hsplit]
    field_simp
    ring
  · nlinarith [sq_nonneg (NSPay.centre (galE κ u) (galV κ u)),
      sq_nonneg ‖galE κ u‖]

/-- **NSE.9 (one-modulus characterization)**: the dispersion action vanishes
exactly when the spectral energy of `u` is supported on one frequency
modulus of `Λ`. -/
theorem dispersion_action_zero_iff {κ : K → ℝ} (hκ : ∀ j, 0 < κ j)
    {u : K → ℂ} (hu : u ≠ 0) :
    NSPay.vres (galE κ u) (galV κ u) = 0
      ↔ ∃ ρ : ℝ, ∀ j, u j ≠ 0 → κ j = ρ := by
  have he := galE_ne_zero hκ hu
  constructor
  · intro hV
    refine ⟨NSPay.centre (galE κ u) (galV κ u), fun j hj => ?_⟩
    have hpsi : NSPay.centred (galE κ u) (galV κ u) = 0 := by
      unfold NSPay.vres at hV
      rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hV
    have hjz : NSPay.centred (galE κ u) (galV κ u) j = 0 := by
      rw [hpsi]; rfl
    unfold NSPay.centred at hjz
    have hcomp : galV κ u j
        - ((NSPay.centre (galE κ u) (galV κ u) : ℝ) : ℂ) * galE κ u j = 0 := by
      simpa using hjz
    rw [galV_apply, galE_apply] at hcomp
    have hfact : ((Real.sqrt (κ j) : ℝ) : ℂ)
        * ((((κ j : ℝ) : ℂ) - ((NSPay.centre (galE κ u) (galV κ u) : ℝ) : ℂ))
          * u j) = 0 := by
      rw [← hcomp]
      ring
    have hs : ((Real.sqrt (κ j) : ℝ) : ℂ) ≠ 0 := by
      simpa using (Real.sqrt_pos.mpr (hκ j)).ne'
    have hmid : (((κ j : ℝ) : ℂ) - ((NSPay.centre (galE κ u) (galV κ u) : ℝ) : ℂ))
        * u j = 0 := by
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h hs
      · exact h
    rcases mul_eq_zero.mp hmid with h | h
    · have := sub_eq_zero.mp h
      exact_mod_cast this
    · exact absurd h hj
  · rintro ⟨ρ, hρ⟩
    have hcentre : NSPay.centre (galE κ u) (galV κ u) = ρ := by
      have hnum : (⟪galE κ u, galV κ u⟫).re = ρ * ‖galE κ u‖ ^ 2 := by
        rw [re_inner_galE_galV (fun j => (hκ j).le), galLam_norm_sq,
          galE_norm_sq (fun j => (hκ j).le), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : u j = 0
        · rw [hj]
          simp
        · rw [hρ j hj]
          ring
      unfold NSPay.centre
      rw [hnum]
      have hepos : ‖galE κ u‖ ^ 2 ≠ 0 := by
        have := norm_pos_iff.mpr he
        positivity
      field_simp
    have hpsi : NSPay.centred (galE κ u) (galV κ u) = 0 := by
      unfold NSPay.centred
      rw [hcentre]
      have hext : galV κ u = ((ρ : ℝ) : ℂ) • galE κ u := by
        ext j
        have hsm : (((ρ : ℝ) : ℂ) • galE κ u) j = ((ρ : ℝ) : ℂ) * galE κ u j := rfl
        rw [galV_apply, hsm, galE_apply]
        by_cases hj : u j = 0
        · rw [hj]
          ring
        · rw [hρ j hj]
      rw [hext, sub_self]
    unfold NSPay.vres
    rw [hpsi, norm_zero]
    norm_num

/-- **NSE.9 (vanishing branch)**: on the one-modulus branch the critical
work and record rate vanish: `Φ_c = q_c = 0`. -/
theorem one_modulus_branch {κ : K → ℝ} (_hκ : ∀ j, 0 < κ j)
    {u : K → ℂ} (c : EuclideanSpace ℂ K) {ν : ℝ} (hν : 0 ≤ ν)
    (hce : (⟪c, galE κ u⟫).re = 0)
    (hV : NSPay.vres (galE κ u) (galV κ u) = 0) :
    NSPay.work c (galV κ u) = 0 ∧ NSPay.record ν c (galV κ u) = 0 := by
  have hpsi : NSPay.centred (galE κ u) (galV κ u) = 0 := by
    unfold NSPay.vres at hV
    rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hV
  have hwork : NSPay.work c (galV κ u) = 0 := by
    rw [NSPay.work_eq_centred (galE κ u) c (galV κ u) hce, hpsi,
      inner_zero_right]
    simp
  refine ⟨hwork, ?_⟩
  unfold NSPay.record
  rw [hwork]
  refine max_eq_right ?_
  nlinarith [sq_nonneg ‖galV κ u‖, mul_nonneg hν (sq_nonneg ‖galV κ u‖)]

end GalerkinModel

end NSCentred

end CriticalCentredTarget

/-! ### Canonical two-centre/far-leverage dipole

Record `thm:NS-two-centre-critical-dipole` (NSE.28–NSE.32).

Rendering: on the finite spectral Galerkin model of `NSCentred`, the
critical-energy law `ω` (NSE.28) is the finite probability weight
`ω_j = κ_j‖u_j‖²/‖e‖²`; its mean `m`, variance `s²`, second moment `r²`,
half absolute deviation `a`, and leverage `𝔏 = s²/a²` are finite sums
(NSE.29).  The setup identities (`ω` is a probability law with mean `κ̄`,
`𝒱_c = ‖e‖²s²`, `𝒟_c = ‖e‖²r²`, `𝔏 ≥ 4`), the Paley–Zygmund masses and
separation (NSE.30), the dipole action floors (NSE.31) for
`ψ_± = 1_{Ω_±}(Λ)ψ` (rendered as the frequency-restricted sums of
`‖ψ_j‖²`), and the far-leverage moment bound (NSE.32) are all proved
exactly. -/

section TwoCentreDipole

open scoped ComplexInnerProductSpace

namespace NSDipole

open NSCentred

variable {K : Type*} [Fintype K]

/-- The critical-energy probability weight `ω_j = κ_j‖u_j‖²/‖e‖²`
(NSE.28). -/
noncomputable def omegaW (κ : K → ℝ) (u : K → ℂ) (j : K) : ℝ :=
  κ j * ‖u j‖ ^ 2 / ‖galE κ u‖ ^ 2

/-- The spectral mean `m = ∑ ω_j κ_j` (NSE.28). -/
noncomputable def specMean (κ : K → ℝ) (u : K → ℂ) : ℝ :=
  ∑ j, omegaW κ u j * κ j

/-- The spectral variance `s² = ∑ ω_j (κ_j - m)²` (NSE.29). -/
noncomputable def specVar (κ : K → ℝ) (u : K → ℂ) : ℝ :=
  ∑ j, omegaW κ u j * (κ j - specMean κ u) ^ 2

/-- The spectral second moment `r² = ∑ ω_j κ_j²` (NSE.29). -/
noncomputable def specSecond (κ : K → ℝ) (u : K → ℂ) : ℝ :=
  ∑ j, omegaW κ u j * κ j ^ 2

/-- The half absolute deviation `a = ½∑ ω_j |κ_j - m|` (NSE.29). -/
noncomputable def specDev (κ : K → ℝ) (u : K → ℂ) : ℝ :=
  (∑ j, omegaW κ u j * |κ j - specMean κ u|) / 2

/-- The leverage `𝔏 = s²/a²` (NSE.29). -/
noncomputable def specLev (κ : K → ℝ) (u : K → ℂ) : ℝ :=
  specVar κ u / specDev κ u ^ 2

omit [Fintype K] in
/-- Weighted finite Cauchy–Schwarz: `(∑ wY)² ≤ (∑ wY²)(∑ w)`. -/
theorem weighted_cs {w Y : K → ℝ} (hw : ∀ j, 0 ≤ w j) (s : Finset K) :
    (∑ j ∈ s, w j * Y j) ^ 2
      ≤ (∑ j ∈ s, w j * Y j ^ 2) * ∑ j ∈ s, w j := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun j => Real.sqrt (w j) * Y j) (fun j => Real.sqrt (w j))
  have h1 : ∀ j ∈ s, Real.sqrt (w j) * Y j * Real.sqrt (w j) = w j * Y j := by
    intro j _
    have := Real.mul_self_sqrt (hw j)
    linear_combination Y j * this
  have h2 : ∀ j ∈ s, (Real.sqrt (w j) * Y j) ^ 2 = w j * Y j ^ 2 := by
    intro j _
    have := Real.mul_self_sqrt (hw j)
    linear_combination Y j ^ 2 * this
  have h3 : ∀ j ∈ s, (Real.sqrt (w j)) ^ 2 = w j := fun j _ => Real.sq_sqrt (hw j)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3]
    at h
  exact h

section PZ

variable {w X : K → ℝ}

/-- Paley–Zygmund mass bound for a nonnegative weighted variable with mean
`a` and second moment at most `s₂`. -/
theorem pz_mass (hw : ∀ j, 0 ≤ w j) (_hX : ∀ j, 0 ≤ X j)
    (hsum1 : ∑ j, w j = 1) {a s2 : ℝ} (ha : ∑ j, w j * X j = a)
    (hapos : 0 < a) (hs2 : ∑ j, w j * X j ^ 2 ≤ s2) :
    a ^ 2 / (4 * s2) ≤ ∑ j ∈ Finset.univ.filter fun j => a / 2 ≤ X j, w j := by
  classical
  set S := Finset.univ.filter fun j => a / 2 ≤ X j with hS
  have hsplit : ∑ j ∈ S, w j * X j + ∑ j ∈ Finset.univ.filter
      (fun j => ¬ (a / 2 ≤ X j)), w j * X j = a := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact ha
  have hlowterm : ∀ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)),
      w j * X j ≤ w j * (a / 2) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact mul_le_mul_of_nonneg_left (le_of_not_ge hj.2) (hw j)
  have hlowsum : ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j
      ≤ 1 := by
    rw [← hsum1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => hw j
  have hlow : ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j
      ≤ a / 2 := by
    calc ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j
        ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * (a / 2) :=
          Finset.sum_le_sum hlowterm
      _ = (∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j) * (a / 2) := by
          rw [← Finset.sum_mul]
      _ ≤ 1 * (a / 2) := by
          have := mul_le_mul_of_nonneg_right hlowsum (by linarith : (0:ℝ) ≤ a / 2)
          linarith
      _ = a / 2 := one_mul _
  have hhigh : a / 2 ≤ ∑ j ∈ S, w j * X j := by linarith
  have hcs := weighted_cs (Y := X) hw S
  have hsub2 : ∑ j ∈ S, w j * X j ^ 2 ≤ s2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) fun j _ _ => ?_) hs2
    exact mul_nonneg (hw j) (by positivity)
  have hs2pos : 0 < s2 := by
    have hfull := weighted_cs (Y := X) hw Finset.univ
    rw [hsum1, mul_one, ha] at hfull
    nlinarith
  have hSw : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg fun j _ => hw j
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * s2)]
  nlinarith [hcs, mul_le_mul_of_nonneg_right hsub2 hSw]

/-- Paley–Zygmund second-moment floor: the upper-half region carries at
least `a²/2` of the second moment. -/
theorem pz_second (hw : ∀ j, 0 ≤ w j) (hX : ∀ j, 0 ≤ X j)
    (hsum1 : ∑ j, w j = 1) {a : ℝ} (ha : ∑ j, w j * X j = a) (hapos : 0 < a) :
    a ^ 2 / 2 ≤ ∑ j ∈ Finset.univ.filter fun j => a / 2 ≤ X j, w j * X j ^ 2 := by
  classical
  have hfull : a ^ 2 ≤ ∑ j, w j * X j ^ 2 := by
    have hcs := weighted_cs (Y := X) hw Finset.univ
    rw [hsum1, mul_one, ha] at hcs
    exact hcs
  have hsplit : (∑ j ∈ Finset.univ.filter fun j => a / 2 ≤ X j, w j * X j ^ 2)
      + ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j ^ 2
      = ∑ j, w j * X j ^ 2 := Finset.sum_filter_add_sum_filter_not _ _ _
  have hlowterm : ∀ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)),
      w j * X j ^ 2 ≤ (a / 2) * (w j * X j) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hXj := le_of_not_ge hj.2
    have hstep := mul_le_mul_of_nonneg_left hXj (mul_nonneg (hw j) (hX j))
    nlinarith [hstep]
  have hlowfull : ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j
      ≤ a := by
    rw [← ha]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => mul_nonneg (hw j) (hX j)
  have hlow : ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j ^ 2
      ≤ (a / 2) * a := by
    calc ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)), w j * X j ^ 2
        ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)),
            (a / 2) * (w j * X j) := Finset.sum_le_sum hlowterm
      _ = (a / 2) * ∑ j ∈ Finset.univ.filter (fun j => ¬ (a / 2 ≤ X j)),
            w j * X j := by rw [Finset.mul_sum]
      _ ≤ (a / 2) * a := by
          exact mul_le_mul_of_nonneg_left hlowfull (by linarith)
  nlinarith

end PZ

section DipoleData

variable {κ : K → ℝ} {u : K → ℂ}

/-- The energy normalization is positive on a nonzero packet. -/
theorem galE_sq_pos (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) : 0 < ‖galE κ u‖ ^ 2 := by
  have := norm_pos_iff.mpr (galE_ne_zero hκ hu)
  positivity

/-- The critical-energy weights are nonnegative. -/
theorem omegaW_nonneg (hκ : ∀ j, 0 < κ j) (j : K) : 0 ≤ omegaW κ u j := by
  unfold omegaW
  have := (hκ j).le
  positivity

/-- `ω` is a probability law: `∑ ω_j = 1` (NSE.28). -/
theorem sum_omegaW (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    ∑ j, omegaW κ u j = 1 := by
  unfold omegaW
  rw [← Finset.sum_div, ← galE_norm_sq (fun j => (hκ j).le) u,
    div_self (galE_sq_pos hκ hu).ne']

/-- The spectral mean is the critical frequency centre `κ̄` (NSE.28). -/
theorem specMean_eq_centre (hκ : ∀ j, 0 < κ j) (_hu : u ≠ 0) :
    specMean κ u = NSPay.centre (galE κ u) (galV κ u) := by
  rw [galerkin_centre (fun j => (hκ j).le), galLam_norm_sq]
  unfold specMean omegaW
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Componentwise form of the centred target on the Galerkin model. -/
theorem centred_apply (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) (j : K) :
    NSPay.centred (galE κ u) (galV κ u) j
      = ((Real.sqrt (κ j) : ℝ) : ℂ) * (((κ j - specMean κ u : ℝ) : ℂ) * u j) := by
  have hsub : NSPay.centred (galE κ u) (galV κ u) j
      = galV κ u j - ((NSPay.centre (galE κ u) (galV κ u) : ℝ) : ℂ) * galE κ u j :=
    rfl
  rw [hsub, galV_apply, galE_apply, ← specMean_eq_centre hκ hu]
  push_cast
  ring

/-- The squared component of the centred target through the spectral law. -/
theorem centred_normsq_apply (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) (j : K) :
    ‖NSPay.centred (galE κ u) (galV κ u) j‖ ^ 2
      = ‖galE κ u‖ ^ 2 * (omegaW κ u j * (κ j - specMean κ u) ^ 2) := by
  rw [centred_apply hκ hu, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold omegaW
  rw [mul_pow, mul_pow, Real.sq_sqrt (hκ j).le, sq_abs]
  have hEn : ‖galE κ u‖ ≠ 0 := norm_ne_zero_iff.mpr (galE_ne_zero hκ hu)
  field_simp

/-- **NSE.29 identities**: `𝒱_c = ‖e‖²s²` and `𝒟_c = ‖e‖²r²`. -/
theorem action_moment_identities (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    NSPay.vres (galE κ u) (galV κ u) = ‖galE κ u‖ ^ 2 * specVar κ u ∧
      ‖galV κ u‖ ^ 2 = ‖galE κ u‖ ^ 2 * specSecond κ u := by
  constructor
  · unfold NSPay.vres
    rw [EuclideanSpace.norm_sq_eq]
    unfold specVar
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => centred_normsq_apply hκ hu j
  · rw [EuclideanSpace.norm_sq_eq]
    unfold specSecond omegaW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [galV_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hEn : ‖galE κ u‖ ≠ 0 := norm_ne_zero_iff.mpr (galE_ne_zero hκ hu)
    rw [mul_pow, mul_pow, Real.sq_sqrt (hκ j).le, sq_abs]
    field_simp

/-- The centred spectral law has mean zero. -/
theorem centred_mean_zero (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    ∑ j, omegaW κ u j * (κ j - specMean κ u) = 0 := by
  have hexp : ∀ j, omegaW κ u j * (κ j - specMean κ u)
      = omegaW κ u j * κ j - omegaW κ u j * specMean κ u := fun j => by ring
  simp only [hexp]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_omegaW hκ hu, one_mul]
  exact sub_self _

/-- The two one-sided deviations both have expectation `a` (NSE.29). -/
theorem dev_split (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    ∑ j, omegaW κ u j * max (specMean κ u - κ j) 0 = specDev κ u ∧
      ∑ j, omegaW κ u j * max (κ j - specMean κ u) 0 = specDev κ u := by
  have hqp : ∀ j, max (κ j - specMean κ u) 0 - max (specMean κ u - κ j) 0
        = κ j - specMean κ u ∧
      max (κ j - specMean κ u) 0 + max (specMean κ u - κ j) 0
        = |κ j - specMean κ u| := by
    intro j
    rcases le_total (κ j) (specMean κ u) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith),
        abs_of_nonpos (by linarith)]
      constructor <;> ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith),
        abs_of_nonneg (by linarith)]
      constructor <;> ring
  have hsub : ∑ j, omegaW κ u j * max (κ j - specMean κ u) 0
      - ∑ j, omegaW κ u j * max (specMean κ u - κ j) 0 = 0 := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ j, omegaW κ u j * max (κ j - specMean κ u) 0
        - omegaW κ u j * max (specMean κ u - κ j) 0
        = omegaW κ u j * (κ j - specMean κ u) := fun j => by
      rw [← mul_sub, (hqp j).1]
    simp only [hterm]
    exact centred_mean_zero hκ hu
  have hadd : ∑ j, omegaW κ u j * max (κ j - specMean κ u) 0
      + ∑ j, omegaW κ u j * max (specMean κ u - κ j) 0
      = 2 * specDev κ u := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j, omegaW κ u j * max (κ j - specMean κ u) 0
        + omegaW κ u j * max (specMean κ u - κ j) 0
        = omegaW κ u j * |κ j - specMean κ u| := fun j => by
      rw [← mul_add, (hqp j).2]
    simp only [hterm]
    unfold specDev
    ring
  constructor <;> linarith

/-- The second moment of a nonzero packet is positive. -/
theorem specSecond_pos (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    0 < specSecond κ u := by
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hu
  refine Finset.sum_pos' (fun j _ => mul_nonneg (omegaW_nonneg hκ j) (by positivity))
    ⟨j0, Finset.mem_univ j0, ?_⟩
  have hω : 0 < omegaW κ u j0 := by
    unfold omegaW
    have hE := galE_sq_pos hκ hu
    have hn : (0:ℝ) < ‖u j0‖ ^ 2 := by
      have : u j0 ≠ 0 := by simpa using hj0
      positivity
    have := hκ j0
    positivity
  have := hκ j0
  positivity

/-- The squared incidence ratio is the variance over the second moment:
`δ_c² = s²/r²` (NSE.29). -/
theorem deltaC_sq (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) :
    NSPay.deltaC (galE κ u) (galV κ u) ^ 2
      = specVar κ u / specSecond κ u := by
  obtain ⟨hvres, hdis⟩ := action_moment_identities hκ hu
  have hE := galE_sq_pos hκ hu
  have hr := specSecond_pos hκ hu
  have hVnn : 0 ≤ NSPay.vres (galE κ u) (galV κ u) := by
    unfold NSPay.vres
    positivity
  have hDpos : 0 < ‖galV κ u‖ ^ 2 := by
    rw [hdis]
    positivity
  unfold NSPay.deltaC
  rw [Real.sq_sqrt (div_nonneg hVnn hDpos.le), hvres, hdis]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Positivity of the variance and the half deviation on a packet with a
positive incidence-ratio floor. -/
theorem specVar_specDev_pos (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u)) :
    0 < specVar κ u ∧ 0 < specDev κ u := by
  have hr := specSecond_pos hκ hu
  have hVar : 0 < specVar κ u := by
    have hd2 := deltaC_sq hκ hu
    have hpos : 0 < NSPay.deltaC (galE κ u) (galV κ u) ^ 2 := by nlinarith
    rw [hd2] at hpos
    have := div_pos_iff.mp hpos
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  refine ⟨hVar, ?_⟩
  by_contra hcon
  push Not at hcon
  have hzero : specDev κ u = 0 := by
    have hnn : 0 ≤ specDev κ u := by
      unfold specDev
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
        mul_nonneg (omegaW_nonneg (u := u) hκ j) (abs_nonneg (κ j - specMean κ u))
      linarith
    linarith
  -- vanishing absolute deviation kills every centred term, hence the variance
  have hsum0 : ∑ j, omegaW κ u j * |κ j - specMean κ u| = 0 := by
    unfold specDev at hzero
    linarith
  have hterms : ∀ j ∈ Finset.univ, omegaW κ u j * |κ j - specMean κ u| = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (omegaW_nonneg hκ j) (abs_nonneg _)).mp hsum0
  have hVar0 : specVar κ u = 0 := by
    unfold specVar
    refine Finset.sum_eq_zero fun j hj => ?_
    have h := hterms j hj
    rcases mul_eq_zero.mp h with h1 | h2
    · rw [h1, zero_mul]
    · rw [abs_eq_zero] at h2
      rw [h2]
      ring
  linarith

/-- **NSE.29 floor**: the leverage always satisfies `𝔏 ≥ 4`. -/
theorem leverage_ge_four (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u)) :
    4 ≤ specLev κ u := by
  obtain ⟨hVar, hDev⟩ := specVar_specDev_pos hκ hu hδ0 hδ
  have hcs := weighted_cs (w := omegaW κ u) (Y := fun j => |κ j - specMean κ u|)
    (omegaW_nonneg hκ) Finset.univ
  rw [sum_omegaW hκ hu, mul_one] at hcs
  have habs : ∀ j ∈ Finset.univ,
      omegaW κ u j * |κ j - specMean κ u| ^ 2
        = omegaW κ u j * (κ j - specMean κ u) ^ 2 := fun j _ => by
    rw [sq_abs]
  rw [Finset.sum_congr rfl habs] at hcs
  have h2a : ∑ j, omegaW κ u j * |κ j - specMean κ u| = 2 * specDev κ u := by
    unfold specDev
    ring
  rw [h2a] at hcs
  unfold specLev
  rw [le_div_iff₀ (by positivity)]
  have hvar : specVar κ u = ∑ j, omegaW κ u j * (κ j - specMean κ u) ^ 2 := rfl
  rw [hvar]
  nlinarith [hcs]

/-- **NSE.30 (mass bounds)**: both dipole shoulders carry mass at least
`1/(4L₀)`. -/
theorem two_centre_mass (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 L0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u))
    (hL : specLev κ u ≤ L0) :
    1 / (4 * L0) ≤ ∑ j ∈ Finset.univ.filter
        (fun j => κ j ≤ specMean κ u - specDev κ u / 2), omegaW κ u j ∧
      1 / (4 * L0) ≤ ∑ j ∈ Finset.univ.filter
        (fun j => specMean κ u + specDev κ u / 2 ≤ κ j), omegaW κ u j := by
  classical
  obtain ⟨hVar, hDev⟩ := specVar_specDev_pos hκ hu hδ0 hδ
  obtain ⟨hm, hp⟩ := dev_split hκ hu
  have hL0 : 0 < L0 := by
    have := leverage_ge_four hκ hu hδ0 hδ
    linarith
  have hlev : specVar κ u ≤ L0 * specDev κ u ^ 2 := by
    unfold specLev at hL
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  have hbridge : ∀ M : ℝ, specDev κ u ^ 2 / (4 * specVar κ u) ≤ M
      → 1 / (4 * L0) ≤ M := by
    intro M hM
    refine le_trans ?_ hM
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  constructor
  · -- minus shoulder via the deviation `max (m - κ) 0`
    have hX2 : ∑ j, omegaW κ u j * max (specMean κ u - κ j) 0 ^ 2
        ≤ specVar κ u := by
      refine Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (omegaW_nonneg hκ j)
      rcases le_total (κ j) (specMean κ u) with h | h
      · rw [max_eq_left (by linarith)]
        nlinarith
      · rw [max_eq_right (by linarith)]
        simpa using sq_nonneg (κ j - specMean κ u)
    have hpz := pz_mass (omegaW_nonneg hκ)
      (fun j => le_max_right _ _) (sum_omegaW hκ hu) hm hDev hX2
    have hset : (Finset.univ.filter
          fun j => specDev κ u / 2 ≤ max (specMean κ u - κ j) 0)
        = Finset.univ.filter
          (fun j => κ j ≤ specMean κ u - specDev κ u / 2) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [le_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        left
        linarith
    rw [hset] at hpz
    exact hbridge _ hpz
  · -- plus shoulder via the deviation `max (κ - m) 0`
    have hX2 : ∑ j, omegaW κ u j * max (κ j - specMean κ u) 0 ^ 2
        ≤ specVar κ u := by
      refine Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (omegaW_nonneg hκ j)
      rcases le_total (specMean κ u) (κ j) with h | h
      · rw [max_eq_left (by linarith)]
      · rw [max_eq_right (by linarith)]
        simpa using sq_nonneg (κ j - specMean κ u)
    have hpz := pz_mass (omegaW_nonneg hκ)
      (fun j => le_max_right _ _) (sum_omegaW hκ hu) hp hDev hX2
    have hset : (Finset.univ.filter
          fun j => specDev κ u / 2 ≤ max (κ j - specMean κ u) 0)
        = Finset.univ.filter
          (fun j => specMean κ u + specDev κ u / 2 ≤ κ j) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [le_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h
        left
        linarith
    rw [hset] at hpz
    exact hbridge _ hpz

/-- **NSE.30 (separation)**: the dipole shoulders are separated by at least
`(δ₀/√L₀)r`. -/
theorem two_centre_separation (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 L0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u))
    (hL : specLev κ u ≤ L0) :
    ∀ i ∈ Finset.univ.filter
        (fun j => κ j ≤ specMean κ u - specDev κ u / 2),
      ∀ j ∈ Finset.univ.filter
        (fun j => specMean κ u + specDev κ u / 2 ≤ κ j),
      δ0 / Real.sqrt L0 * Real.sqrt (specSecond κ u) ≤ κ j - κ i := by
  classical
  obtain ⟨hVar, hDev⟩ := specVar_specDev_pos hκ hu hδ0 hδ
  have hr := specSecond_pos hκ hu
  have hL0 : 0 < L0 := by
    have := leverage_ge_four hκ hu hδ0 hδ
    linarith
  have hlev : specVar κ u ≤ L0 * specDev κ u ^ 2 := by
    unfold specLev at hL
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  -- `δ₀ r ≤ s`
  have hδr : δ0 * Real.sqrt (specSecond κ u) ≤ Real.sqrt (specVar κ u) := by
    have hd2 := deltaC_sq hκ hu
    have hdnn : 0 ≤ NSPay.deltaC (galE κ u) (galV κ u) := le_trans hδ0.le hδ
    have hsq : δ0 ^ 2 * specSecond κ u ≤ specVar κ u := by
      have h1 : δ0 ^ 2 ≤ NSPay.deltaC (galE κ u) (galV κ u) ^ 2 := by nlinarith
      rw [hd2, le_div_iff₀ hr] at h1
      linarith
    have h2 : (δ0 * Real.sqrt (specSecond κ u)) ^ 2 ≤ specVar κ u := by
      rw [mul_pow, Real.sq_sqrt hr.le]
      exact hsq
    calc δ0 * Real.sqrt (specSecond κ u)
        = Real.sqrt ((δ0 * Real.sqrt (specSecond κ u)) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (specVar κ u) := Real.sqrt_le_sqrt h2
  -- `s ≤ a √L₀`
  have hsa : Real.sqrt (specVar κ u) ≤ specDev κ u * Real.sqrt L0 := by
    have h2 : specVar κ u ≤ (specDev κ u * Real.sqrt L0) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hL0.le]
      nlinarith
    calc Real.sqrt (specVar κ u) ≤ Real.sqrt ((specDev κ u * Real.sqrt L0) ^ 2) :=
        Real.sqrt_le_sqrt h2
      _ = specDev κ u * Real.sqrt L0 := Real.sqrt_sq (by positivity)
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  have hsep : specDev κ u ≤ κ j - κ i := by
    have h1 := hi.2
    have h2 := hj.2
    linarith
  have hfin : δ0 / Real.sqrt L0 * Real.sqrt (specSecond κ u) ≤ specDev κ u := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc δ0 * Real.sqrt (specSecond κ u) ≤ Real.sqrt (specVar κ u) := hδr
      _ ≤ specDev κ u * Real.sqrt L0 := hsa
  linarith

/-- **NSE.31**: both dipole shoulders carry at least `𝒱_c/(2L₀)` of the
centred source action. -/
theorem dipole_action_floor (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 L0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u))
    (hL : specLev κ u ≤ L0) :
    NSPay.vres (galE κ u) (galV κ u) / (2 * L0)
        ≤ ∑ j ∈ Finset.univ.filter
            (fun j => κ j ≤ specMean κ u - specDev κ u / 2),
            ‖NSPay.centred (galE κ u) (galV κ u) j‖ ^ 2 ∧
      NSPay.vres (galE κ u) (galV κ u) / (2 * L0)
        ≤ ∑ j ∈ Finset.univ.filter
            (fun j => specMean κ u + specDev κ u / 2 ≤ κ j),
            ‖NSPay.centred (galE κ u) (galV κ u) j‖ ^ 2 := by
  classical
  obtain ⟨hVar, hDev⟩ := specVar_specDev_pos hκ hu hδ0 hδ
  obtain ⟨hm, hp⟩ := dev_split hκ hu
  obtain ⟨hvres, _⟩ := action_moment_identities hκ hu
  have hE := galE_sq_pos hκ hu
  have hL0 : 0 < L0 := by
    have := leverage_ge_four hκ hu hδ0 hδ
    linarith
  have hlev : specVar κ u ≤ L0 * specDev κ u ^ 2 := by
    unfold specLev at hL
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  have hkey : ∀ (X : K → ℝ) (S : Finset K),
      (∀ j ∈ S, X j ^ 2 = (κ j - specMean κ u) ^ 2)
      → specDev κ u ^ 2 / 2 ≤ ∑ j ∈ S, omegaW κ u j * X j ^ 2
      → NSPay.vres (galE κ u) (galV κ u) / (2 * L0)
          ≤ ∑ j ∈ S, ‖NSPay.centred (galE κ u) (galV κ u) j‖ ^ 2 := by
    intro X S hXS hfloor
    have hsum : ∑ j ∈ S, ‖NSPay.centred (galE κ u) (galV κ u) j‖ ^ 2
        = ‖galE κ u‖ ^ 2 * ∑ j ∈ S, omegaW κ u j * (κ j - specMean κ u) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => centred_normsq_apply hκ hu j
    have hXsum : ∑ j ∈ S, omegaW κ u j * X j ^ 2
        = ∑ j ∈ S, omegaW κ u j * (κ j - specMean κ u) ^ 2 :=
      Finset.sum_congr rfl fun j hj => by rw [hXS j hj]
    rw [hsum, hvres]
    rw [hXsum] at hfloor
    rw [div_le_iff₀ (by positivity)]
    have hfloor2 : specVar κ u / L0 ≤ 2 * (specDev κ u ^ 2 / 2) := by
      rw [div_le_iff₀ hL0]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfloor (le_of_lt hE)]
  constructor
  · have hpz := pz_second (omegaW_nonneg hκ) (fun j => le_max_right _ _)
      (sum_omegaW hκ hu) hm hDev
    have hset : (Finset.univ.filter
          fun j => specDev κ u / 2 ≤ max (specMean κ u - κ j) 0)
        = Finset.univ.filter
          (fun j => κ j ≤ specMean κ u - specDev κ u / 2) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [le_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        left
        linarith
    rw [hset] at hpz
    refine hkey _ _ (fun j hj => ?_) hpz
    rw [Finset.mem_filter] at hj
    rw [max_eq_left (by linarith [hj.2, hDev] : (0:ℝ) ≤ specMean κ u - κ j)]
    ring
  · have hpz := pz_second (omegaW_nonneg hκ) (fun j => le_max_right _ _)
      (sum_omegaW hκ hu) hp hDev
    have hset : (Finset.univ.filter
          fun j => specDev κ u / 2 ≤ max (κ j - specMean κ u) 0)
        = Finset.univ.filter
          (fun j => specMean κ u + specDev κ u / 2 ≤ κ j) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [le_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        left
        linarith
    rw [hset] at hpz
    refine hkey _ _ (fun j hj => ?_) hpz
    rw [Finset.mem_filter] at hj
    rw [max_eq_left (by linarith [hj.2, hDev] : (0:ℝ) ≤ κ j - specMean κ u)]

/-- **NSE.32**: the far-leverage moment bound — beyond radius `Ra`, the
centred spectral action is at least `s²(1 - 2R/𝔏)₊`. -/
theorem far_leverage_moment (hκ : ∀ j, 0 < κ j) (hu : u ≠ 0) {δ0 : ℝ}
    (hδ0 : 0 < δ0) (hδ : δ0 ≤ NSPay.deltaC (galE κ u) (galV κ u))
    {R : ℝ} (hR : 0 < R) :
    specVar κ u * max (1 - 2 * R / specLev κ u) 0
      ≤ ∑ j ∈ Finset.univ.filter
          (fun j => R * specDev κ u < |κ j - specMean κ u|),
          omegaW κ u j * (κ j - specMean κ u) ^ 2 := by
  classical
  obtain ⟨hVar, hDev⟩ := specVar_specDev_pos hκ hu hδ0 hδ
  have hTnn : 0 ≤ ∑ j ∈ Finset.univ.filter
      (fun j => R * specDev κ u < |κ j - specMean κ u|),
      omegaW κ u j * (κ j - specMean κ u) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (omegaW_nonneg hκ j) (by positivity)
  rcases le_or_gt (1 - 2 * R / specLev κ u) 0 with hneg | hpos
  · rw [max_eq_right hneg, mul_zero]
    exact hTnn
  · rw [max_eq_left hpos.le]
    -- the near region carries at most `2Ra²`
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => R * specDev κ u < |κ j - specMean κ u|)
      (fun j => omegaW κ u j * (κ j - specMean κ u) ^ 2)
    have hlowterm : ∀ j ∈ Finset.univ.filter
        (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
        omegaW κ u j * (κ j - specMean κ u) ^ 2
          ≤ R * specDev κ u * (omegaW κ u j * |κ j - specMean κ u|) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have habs := not_lt.mp hj.2
      have hω := omegaW_nonneg (u := u) hκ j
      have h1 : (κ j - specMean κ u) ^ 2 = |κ j - specMean κ u| ^ 2 := by
        rw [sq_abs]
      have h2 : |κ j - specMean κ u| ^ 2
          ≤ R * specDev κ u * |κ j - specMean κ u| := by
        have h3 := abs_nonneg (κ j - specMean κ u)
        nlinarith
      rw [h1]
      calc omegaW κ u j * |κ j - specMean κ u| ^ 2
          ≤ omegaW κ u j * (R * specDev κ u * |κ j - specMean κ u|) :=
            mul_le_mul_of_nonneg_left h2 hω
        _ = R * specDev κ u * (omegaW κ u j * |κ j - specMean κ u|) := by ring
    have hlowsum : ∑ j ∈ Finset.univ.filter
        (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
        omegaW κ u j * (κ j - specMean κ u) ^ 2
        ≤ R * specDev κ u * (2 * specDev κ u) := by
      calc ∑ j ∈ Finset.univ.filter
            (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
            omegaW κ u j * (κ j - specMean κ u) ^ 2
          ≤ ∑ j ∈ Finset.univ.filter
            (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
            R * specDev κ u * (omegaW κ u j * |κ j - specMean κ u|) :=
            Finset.sum_le_sum hlowterm
        _ = R * specDev κ u * ∑ j ∈ Finset.univ.filter
            (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
            omegaW κ u j * |κ j - specMean κ u| := by rw [Finset.mul_sum]
        _ ≤ R * specDev κ u * (2 * specDev κ u) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hsub : ∑ j ∈ Finset.univ.filter
                (fun j => ¬ (R * specDev κ u < |κ j - specMean κ u|)),
                omegaW κ u j * |κ j - specMean κ u|
                ≤ ∑ j, omegaW κ u j * |κ j - specMean κ u| :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun j _ _ => mul_nonneg (omegaW_nonneg hκ j) (abs_nonneg _)
            have h2a : ∑ j, omegaW κ u j * |κ j - specMean κ u|
                = 2 * specDev κ u := by
              unfold specDev
              ring
            linarith
    -- assemble through `𝔏 = s²/a²`
    have hLid : specVar κ u * (2 * R / specLev κ u)
        = 2 * R * specDev κ u ^ 2 := by
      unfold specLev
      field_simp [hVar.ne', hDev.ne']
    have hvar : specVar κ u = ∑ j, omegaW κ u j * (κ j - specMean κ u) ^ 2 := rfl
    nlinarith [hsplit, hlowsum, hLid, hvar]

end DipoleData

end NSDipole

end TwoCentreDipole

/-! ### Source-paid centred-dispersion escape

Record `thm:NS-centred-dispersion-escape` (NSE.23–NSE.24).

Rendering: the chronology carrier is an abstract measure space `(T, μ)`
with measurable unit-record packets `I k`, measurable critical record rate
`q = q_c(t)` and dispersion action `V = 𝒱_c(t)`, and `V > 0` on the
record-positive set (the branch guard `NSPay.vres_pos` of the critical
packet).  On `{q > 0}` the payment norm is `‖c_c^pay‖ = q_c/√𝒱_c`
(NSE.13), so the dispersion measure `λ_k^disp` (NSE.22) has density
`1_{I_k∩{q>0}}q_c/√𝒱_c` and the critical payment measure `π_k^c` has
density `1_{I_k∩{q>0}}q_c`.  NSE.23 is the exact Radon–Nikodym
factorization `π_k^c = √𝒱_c·λ_k^disp`; the finite native length (NSE.19)
enters as the interface hypothesis that the global dispersion stock is
finite, giving summable and vanishing masses through packet disjointness;
NSE.24 is the Chebyshev escape estimate with its vanishing limit. -/

section DispersionEscape

open MeasureTheory
open scoped ENNReal

namespace NSEscape

variable {T : Type*} [MeasurableSpace T] (μ : Measure T)
variable (I : ℕ → Set T) (q V : T → ℝ)

/-- The dispersion stock density `1_{I_k∩{q>0}} q_c/√𝒱_c` (NSE.22). -/
noncomputable def dispDensity (k : ℕ) : T → ℝ≥0∞ :=
  (I k ∩ {t | 0 < q t}).indicator fun t =>
    ENNReal.ofReal (q t / Real.sqrt (V t))

/-- The dispersion measure `λ_k^disp` (NSE.22). -/
noncomputable def dispMeasure (k : ℕ) : Measure T :=
  μ.withDensity (dispDensity I q V k)

/-- The critical payment density `1_{I_k∩{q>0}} q_c`. -/
noncomputable def payDensity (k : ℕ) : T → ℝ≥0∞ :=
  (I k ∩ {t | 0 < q t}).indicator fun t => ENNReal.ofReal (q t)

/-- The critical payment measure `π_k^c` with `dπ_k^c = q_c dt` on the
record-positive part of the packet. -/
noncomputable def payMeasure (k : ℕ) : Measure T :=
  μ.withDensity (payDensity I q k)

variable {μ I q V}

/-- The record-positive part of a packet is measurable. -/
theorem measurableSet_packet (hI : ∀ k, MeasurableSet (I k))
    (hq : Measurable q) (k : ℕ) :
    MeasurableSet (I k ∩ {t | 0 < q t}) :=
  (hI k).inter (measurableSet_lt measurable_const hq)

/-- The dispersion density is measurable. -/
theorem measurable_dispDensity (hI : ∀ k, MeasurableSet (I k))
    (hq : Measurable q) (hV : Measurable V) (k : ℕ) :
    Measurable (dispDensity I q V k) :=
  ((hq.div (hV.sqrt)).ennreal_ofReal).indicator (measurableSet_packet hI hq k)

/-- **NSE.23**: the critical payment measure factorizes exactly over the
dispersion measure with Radon–Nikodym density `√𝒱_c`. -/
theorem pay_eq_disp_withDensity (hI : ∀ k, MeasurableSet (I k))
    (hq : Measurable q) (hV : Measurable V)
    (hpos : ∀ t, 0 < q t → 0 < V t) (k : ℕ) :
    payMeasure μ I q k
      = (dispMeasure μ I q V k).withDensity
          fun t => ENNReal.ofReal (Real.sqrt (V t)) := by
  unfold payMeasure dispMeasure
  rw [← withDensity_mul μ (measurable_dispDensity hI hq hV k)
    (hV.sqrt.ennreal_ofReal)]
  congr 1
  funext t
  by_cases ht : t ∈ I k ∩ {t | 0 < q t}
  · rw [Pi.mul_apply]
    unfold dispDensity payDensity
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have hqt : 0 < q t := ht.2
    have hVt : 0 < V t := hpos t hqt
    have hs : Real.sqrt (V t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hVt)
    rw [← ENNReal.ofReal_mul (div_nonneg hqt.le (Real.sqrt_nonneg _)),
      div_mul_cancel₀ _ hs]
  · rw [Pi.mul_apply]
    unfold dispDensity payDensity
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]

/-- The total dispersion mass of one packet as a set integral. -/
theorem dispMeasure_univ (hI : ∀ k, MeasurableSet (I k)) (hq : Measurable q)
    (k : ℕ) :
    dispMeasure μ I q V k Set.univ
      = ∫⁻ t in I k ∩ {t | 0 < q t},
          ENNReal.ofReal (q t / Real.sqrt (V t)) ∂μ := by
  unfold dispMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold dispDensity
  rw [lintegral_indicator (measurableSet_packet hI hq k)]

/-- **NSE.24 (escape estimate)**: the payment mass of every fixed
centred-dispersion head is Chebyshev-dominated by the dispersion stock. -/
theorem escape_bound (hI : ∀ k, MeasurableSet (I k)) (hq : Measurable q)
    (hV : Measurable V) (hpos : ∀ t, 0 < q t → 0 < V t)
    {R : ℝ} (_hR : 0 ≤ R) (k : ℕ) :
    payMeasure μ I q k {t | V t ≤ R}
      ≤ ENNReal.ofReal (Real.sqrt R) * dispMeasure μ I q V k Set.univ := by
  have hRset : MeasurableSet {t | V t ≤ R} :=
    measurableSet_le hV measurable_const
  unfold payMeasure
  rw [withDensity_apply _ hRset]
  have hmono : ∀ t ∈ {t | V t ≤ R}, payDensity I q k t
      ≤ ENNReal.ofReal (Real.sqrt R) * dispDensity I q V k t := by
    intro t ht
    by_cases htk : t ∈ I k ∩ {t | 0 < q t}
    · unfold payDensity dispDensity
      rw [Set.indicator_of_mem htk, Set.indicator_of_mem htk]
      have hqt : 0 < q t := htk.2
      have hVt : 0 < V t := hpos t hqt
      have hs : 0 < Real.sqrt (V t) := Real.sqrt_pos.mpr hVt
      have hqle : q t ≤ Real.sqrt R * (q t / Real.sqrt (V t)) := by
        have hsle : Real.sqrt (V t) ≤ Real.sqrt R := Real.sqrt_le_sqrt ht
        rw [mul_div_assoc', le_div_iff₀ hs]
        have := mul_le_mul_of_nonneg_left hsle hqt.le
        linarith [mul_comm (q t) (Real.sqrt R)]
      calc ENNReal.ofReal (q t)
          ≤ ENNReal.ofReal (Real.sqrt R * (q t / Real.sqrt (V t))) :=
            ENNReal.ofReal_le_ofReal hqle
        _ = ENNReal.ofReal (Real.sqrt R)
            * ENNReal.ofReal (q t / Real.sqrt (V t)) :=
            ENNReal.ofReal_mul (Real.sqrt_nonneg R)
    · unfold payDensity dispDensity
      rw [Set.indicator_of_notMem htk, Set.indicator_of_notMem htk, mul_zero]
  calc ∫⁻ t in {t | V t ≤ R}, payDensity I q k t ∂μ
      ≤ ∫⁻ t in {t | V t ≤ R},
          ENNReal.ofReal (Real.sqrt R) * dispDensity I q V k t ∂μ :=
        setLIntegral_mono' hRset hmono
    _ = ENNReal.ofReal (Real.sqrt R)
        * ∫⁻ t in {t | V t ≤ R}, dispDensity I q V k t ∂μ :=
        lintegral_const_mul _ (measurable_dispDensity hI hq hV k)
    _ ≤ ENNReal.ofReal (Real.sqrt R) * dispMeasure μ I q V k Set.univ := by
        refine mul_le_mul' le_rfl ?_
        unfold dispMeasure
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        exact setLIntegral_le_lintegral _ _

/-- **NSE.23/NSE.24 (assembled record)**: under packet disjointness and the
finite global dispersion stock (the NSE.19 interface), the dispersion
masses are summable and vanish, and every fixed centred-dispersion head is
escaped: `π_k^c{𝒱_c ≤ R} ≤ √R λ_k^disp(I_k) → 0`. -/
theorem dispersion_escape (hI : ∀ k, MeasurableSet (I k)) (hq : Measurable q)
    (hV : Measurable V) (hpos : ∀ t, 0 < q t → 0 < V t)
    (hdisj : Pairwise (Function.onFun Disjoint I))
    (hfin : (∫⁻ t in {t | 0 < q t},
      ENNReal.ofReal (q t / Real.sqrt (V t)) ∂μ) ≠ ⊤) :
    Summable (fun k => (dispMeasure μ I q V k Set.univ).toReal) ∧
      Tendsto (fun k => (dispMeasure μ I q V k Set.univ).toReal) atTop (𝓝 0) ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ k, (payMeasure μ I q k {t | V t ≤ R}).toReal
          ≤ Real.sqrt R * (dispMeasure μ I q V k Set.univ).toReal) ∧
        Tendsto (fun k => (payMeasure μ I q k {t | V t ≤ R}).toReal)
          atTop (𝓝 0) := by
  -- the total dispersion stock dominates the disjoint packet masses
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun k => I k ∩ {t | 0 < q t}) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hsum : (∑' k, dispMeasure μ I q V k Set.univ) ≠ ⊤ := by
    have hcalc : (∑' k, dispMeasure μ I q V k Set.univ)
        = ∫⁻ t in ⋃ k, (I k ∩ {t | 0 < q t}),
            ENNReal.ofReal (q t / Real.sqrt (V t)) ∂μ := by
      rw [lintegral_iUnion (fun k => measurableSet_packet hI hq k) hdisj']
      exact tsum_congr fun k => dispMeasure_univ hI hq k
    rw [hcalc]
    refine ne_top_of_le_ne_top hfin (lintegral_mono_set ?_)
    exact Set.iUnion_subset fun k => Set.inter_subset_right
  have hfink : ∀ k, dispMeasure μ I q V k Set.univ ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hsum (ENNReal.le_tsum k)
  have hsummable : Summable (fun k => (dispMeasure μ I q V k Set.univ).toReal) :=
    ENNReal.summable_toReal hsum
  have htends : Tendsto (fun k => (dispMeasure μ I q V k Set.univ).toReal)
      atTop (𝓝 0) := hsummable.tendsto_atTop_zero
  refine ⟨hsummable, htends, fun R hR => ?_⟩
  have hbound : ∀ k, (payMeasure μ I q k {t | V t ≤ R}).toReal
      ≤ Real.sqrt R * (dispMeasure μ I q V k Set.univ).toReal := by
    intro k
    have h2 := escape_bound (μ := μ) hI hq hV hpos hR k
    have hne : ENNReal.ofReal (Real.sqrt R) * dispMeasure μ I q V k Set.univ
        ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfink k)
    calc (payMeasure μ I q k {t | V t ≤ R}).toReal
        ≤ (ENNReal.ofReal (Real.sqrt R)
            * dispMeasure μ I q V k Set.univ).toReal :=
          ENNReal.toReal_mono hne h2
      _ = Real.sqrt R * (dispMeasure μ I q V k Set.univ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg R)]
  refine ⟨hbound, ?_⟩
  have hlim : Tendsto
      (fun k => Real.sqrt R * (dispMeasure μ I q V k Set.univ).toReal)
      atTop (𝓝 0) := by
    have := htends.const_mul (Real.sqrt R)
    simpa using this
  exact squeeze_zero (fun k => ENNReal.toReal_nonneg) hbound hlim

end NSEscape

end DispersionEscape

/-! ### Coherent payment and balanced scale counterflow

Record `thm:NS-centred-boundary-counterflow` (NSE.25–NSE.27).

Rendering: the signed viscosity-shorted boundary power on the finite scale
interval `[a,b]` is rendered on the uniform scale grid `κ_i = a + h·i`,
`i < n`, `h > 0`, as a signed cell-mass vector `p : ℕ → ℝ` (cell values
integrated over cells, so scale integrals are sums over `range n`).  The
coherent/counterflow split (NSE.25–NSE.26) is exact componentwise algebra
with `q_c = ∫p`, `P = ∫p₊`, `N = ∫p₋`, plus the uniqueness of the
proportional positive replay.  The minimum open-boundary transport cost
(NSE.27) is an `IsLeast` over all nonnegative couplings of the counterflow
marginals with cost `∑ γ_{ij}|κ_i - κ_j|`; the attained minimum is the
exact discrete Kantorovich–Rubinstein CDF cost
`h ∑_r |∑_{i≤r}(p_cf⁺ - p_cf⁻)_i|`, proved by duality (a discrete
`1`-Lipschitz potential) and an explicit inductive transport plan. -/

section BoundaryCounterflow

namespace NSCounterflow

/-- The grid CDF (partial sum) of a signed cell-mass vector. -/
noncomputable def cdf (d : ℕ → ℝ) (r : ℕ) : ℝ := ∑ i ∈ Finset.range (r + 1), d i

/-- A nonnegative coupling of two cell-mass vectors on the grid `range n`. -/
def IsCoupling (n : ℕ) (μ ν : ℕ → ℝ) (γ : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ γ i j) ∧
    (∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j = μ i) ∧
    ∀ j ∈ Finset.range n, ∑ i ∈ Finset.range n, γ i j = ν j

/-- The unit-spacing transport cost of a coupling. -/
noncomputable def costU (n : ℕ) (γ : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j * |(i : ℝ) - (j : ℝ)|

/-- `sign x · x = |x|`. -/
theorem sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    ring
  · rw [h, mul_zero, abs_zero]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- The real sign has modulus at most one. -/
theorem abs_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h]
    norm_num
  · rw [h, Real.sign_zero]
    norm_num
  · rw [Real.sign_of_pos h]
    norm_num

/-- The discrete Kantorovich dual potential of a signed vector. -/
noncomputable def dualPot (d : ℕ → ℝ) (i : ℕ) : ℝ :=
  -∑ r ∈ Finset.range i, Real.sign (cdf d r)

/-- The dual potential moves by at most one per grid step. -/
theorem dualPot_lip (d : ℕ → ℝ) (i j : ℕ) :
    |dualPot d i - dualPot d j| ≤ |(i : ℝ) - (j : ℝ)| := by
  have key : ∀ a b : ℕ, a ≤ b →
      |dualPot d b - dualPot d a| ≤ (b : ℝ) - (a : ℝ) := by
    intro a b hab
    unfold dualPot
    rw [show -∑ r ∈ Finset.range b, Real.sign (cdf d r)
        - -∑ r ∈ Finset.range a, Real.sign (cdf d r)
        = -(∑ r ∈ Finset.range b, Real.sign (cdf d r)
          - ∑ r ∈ Finset.range a, Real.sign (cdf d r)) by ring, abs_neg,
      ← Finset.sum_Ico_eq_sub _ hab]
    calc |∑ r ∈ Finset.Ico a b, Real.sign (cdf d r)|
        ≤ ∑ r ∈ Finset.Ico a b, |Real.sign (cdf d r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.Ico a b, (1 : ℝ) :=
          Finset.sum_le_sum fun r _ => abs_sign_le_one _
      _ = (b : ℝ) - (a : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          rw [Nat.cast_sub hab]
  rcases le_total i j with hij | hij
  · have h := key i j hij
    rw [abs_sub_comm] at h
    calc |dualPot d i - dualPot d j| ≤ (j : ℝ) - (i : ℝ) := h
      _ ≤ |(j : ℝ) - (i : ℝ)| := le_abs_self _
      _ = |(i : ℝ) - (j : ℝ)| := abs_sub_comm _ _
  · have h := key j i hij
    calc |dualPot d i - dualPot d j| ≤ (i : ℝ) - (j : ℝ) := h
      _ ≤ |(i : ℝ) - (j : ℝ)| := le_abs_self _

/-- **Abel pairing**: the dual potential pairs with a balanced vector to the
total CDF mass. -/
theorem dual_pairing (n : ℕ) (d : ℕ → ℝ)
    (hbal : ∑ i ∈ Finset.range n, d i = 0) :
    ∑ i ∈ Finset.range n, dualPot d i * d i
      = ∑ r ∈ Finset.range n, |cdf d r| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have habel := Finset.sum_range_by_parts (dualPot d) d n
  have hsmul : ∀ (a b : ℝ), a • b = a * b := fun a b => smul_eq_mul a b
  have hstep : ∀ i, dualPot d (i + 1) - dualPot d i = -Real.sign (cdf d i) := by
    intro i
    unfold dualPot
    rw [Finset.sum_range_succ]
    ring
  have hGn : ∑ i ∈ Finset.range n, d i = 0 := hbal
  rw [hGn, smul_zero, zero_sub] at habel
  have hterm : ∀ i ∈ Finset.range (n - 1),
      (dualPot d (i + 1) - dualPot d i) • ∑ j ∈ Finset.range (i + 1), d j
        = -|cdf d i| := by
    intro i _
    rw [hsmul, hstep i]
    have : (∑ j ∈ Finset.range (i + 1), d j) = cdf d i := rfl
    rw [this]
    rw [show -Real.sign (cdf d i) * cdf d i
      = -(Real.sign (cdf d i) * cdf d i) by ring, sign_mul_self]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, neg_neg] at habel
  have hlast : |cdf d (n - 1)| = 0 := by
    have h1 : cdf d (n - 1) = ∑ i ∈ Finset.range n, d i := by
      unfold cdf
      rw [show n - 1 + 1 = n from by omega]
    rw [h1, hbal, abs_zero]
  have hsplit : ∑ r ∈ Finset.range n, |cdf d r|
      = ∑ r ∈ Finset.range (n - 1), |cdf d r| + |cdf d (n - 1)| := by
    rw [← Finset.sum_range_succ, show n - 1 + 1 = n from by omega]
  rw [hsplit, hlast, add_zero]
  have hpi : ∀ i ∈ Finset.range n, dualPot d i • d i = dualPot d i * d i :=
    fun i _ => smul_eq_mul _ _
  rw [← Finset.sum_congr rfl hpi]
  exact habel

/-- The coupling pairing of a potential against the marginals. -/
theorem coupling_pairing (n : ℕ) {μ ν : ℕ → ℝ} {γ : ℕ → ℕ → ℝ}
    (hγ : IsCoupling n μ ν γ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j * (f i - f j)
      = ∑ i ∈ Finset.range n, f i * μ i
        - ∑ j ∈ Finset.range n, f j * ν j := by
  have hexp : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      γ i j * (f i - f j) = γ i j * f i - γ i j * f j := by
    intro i _ j _
    ring
  have h1 : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j * (f i - f j)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j * f i
        - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i j * f j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => hexp i hi j hj
  rw [h1]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_mul, hγ.2.1 i hi, mul_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_mul, hγ.2.2 j hj, mul_comm]

/-- **NSE.27, lower bound**: every coupling of balanced marginals pays at
least the CDF cost. -/
theorem coupling_lower_bound (n : ℕ) {μ ν : ℕ → ℝ} {γ : ℕ → ℕ → ℝ}
    (hbal : ∑ i ∈ Finset.range n, μ i = ∑ i ∈ Finset.range n, ν i)
    (hγ : IsCoupling n μ ν γ) :
    ∑ r ∈ Finset.range n, |cdf (fun i => μ i - ν i) r| ≤ costU n γ := by
  set d : ℕ → ℝ := fun i => μ i - ν i with hd
  have hd0 : ∑ i ∈ Finset.range n, d i = 0 := by
    rw [hd]
    rw [Finset.sum_sub_distrib, hbal, sub_self]
  have hpair := dual_pairing n d hd0
  have hcp := coupling_pairing n hγ (dualPot d)
  have hfd : ∑ i ∈ Finset.range n, dualPot d i * μ i
      - ∑ j ∈ Finset.range n, dualPot d j * ν j
      = ∑ i ∈ Finset.range n, dualPot d i * d i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd]
    ring
  have hval : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      γ i j * (dualPot d i - dualPot d j)
      = ∑ r ∈ Finset.range n, |cdf d r| := by
    rw [hcp, hfd, hpair]
  calc ∑ r ∈ Finset.range n, |cdf d r|
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          γ i j * (dualPot d i - dualPot d j) := hval.symm
    _ ≤ |∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          γ i j * (dualPot d i - dualPot d j)| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range n, |∑ j ∈ Finset.range n,
          γ i j * (dualPot d i - dualPot d j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          |γ i j * (dualPot d i - dualPot d j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ costU n γ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hγ.1 i j)]
        exact mul_le_mul_of_nonneg_left (dualPot_lip d i j) (hγ.1 i j)

set_option maxHeartbeats 1000000 in
-- the inductive transport plan forces repeated grid-sum resplits; the
-- default heartbeat budget is too small
/-- **NSE.27, attainment**: balanced nonnegative marginals admit a coupling
whose cost is at most the CDF cost. -/
theorem exists_coupling : ∀ (n : ℕ) (μ ν : ℕ → ℝ), (∀ i, 0 ≤ μ i) →
    (∀ i, 0 ≤ ν i) →
    (∑ i ∈ Finset.range n, μ i = ∑ i ∈ Finset.range n, ν i) →
    ∃ γ, IsCoupling n μ ν γ ∧
      costU n γ ≤ ∑ r ∈ Finset.range n, |cdf (fun i => μ i - ν i) r| := by
  intro n
  induction n with
  | zero =>
    intro μ ν _ _ _
    refine ⟨fun _ _ => 0, ⟨fun i j => le_rfl, ?_, ?_⟩, ?_⟩
    · intro i hi
      exact absurd hi (by simp)
    · intro j hj
      exact absurd hj (by simp)
    · unfold costU
      simp
  | succ n ih =>
    have key : ∀ μ ν : ℕ → ℝ, (∀ i, 0 ≤ μ i) → (∀ i, 0 ≤ ν i) →
        (∑ i ∈ Finset.range (n + 1), μ i = ∑ i ∈ Finset.range (n + 1), ν i) →
        ν 0 ≤ μ 0 →
        ∃ γ, IsCoupling (n + 1) μ ν γ ∧
          costU (n + 1) γ
            ≤ ∑ r ∈ Finset.range (n + 1), |cdf (fun i => μ i - ν i) r| := by
      intro μ ν hμ hν hbal hc
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- a single cell: everything stays in place at zero cost
        have h1 : μ 0 = ν 0 := by
          rw [Finset.sum_range_one, Finset.sum_range_one] at hbal
          exact hbal
        refine ⟨fun i j => if i = 0 ∧ j = 0 then μ 0 else 0,
          ⟨fun i j => ?_, fun i hi => ?_, fun j hj => ?_⟩, ?_⟩
        · dsimp only
          split_ifs with h
          · exact hμ 0
          · exact le_rfl
        · rw [Finset.mem_range] at hi
          interval_cases i
          rw [Finset.sum_range_one]
          simp
        · rw [Finset.mem_range] at hj
          interval_cases j
          rw [Finset.sum_range_one]
          simp [h1]
        · unfold costU
          rw [Finset.sum_range_one, Finset.sum_range_one]
          simp
      · -- shift the first-cell surplus into the reduced grid
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        set δ := μ 0 - ν 0 with hδdef
        have hδ : 0 ≤ δ := by
          rw [hδdef]
          linarith
        set μ' : ℕ → ℝ := fun i => μ (i + 1) + if i = 0 then δ else 0
          with hμ'def
        set ν' : ℕ → ℝ := fun i => ν (i + 1) with hν'def
        have hμ'nn : ∀ i, 0 ≤ μ' i := by
          intro i
          rw [hμ'def]
          dsimp only
          split_ifs with h
          · have := hμ (i + 1)
            linarith
          · have := hμ (i + 1)
            linarith
        have hν'nn : ∀ i, 0 ≤ ν' i := fun i => hν (i + 1)
        have hifsum : ∑ i ∈ Finset.range (m + 2), μ i
            = (∑ i ∈ Finset.range (m + 1), μ (i + 1)) + μ 0 :=
          Finset.sum_range_succ' μ (m + 1)
        have hifsumν : ∑ i ∈ Finset.range (m + 2), ν i
            = (∑ i ∈ Finset.range (m + 1), ν (i + 1)) + ν 0 :=
          Finset.sum_range_succ' ν (m + 1)
        have hbal' : ∑ i ∈ Finset.range (m + 1), μ' i
            = ∑ i ∈ Finset.range (m + 1), ν' i := by
          have hμ'sum : ∑ i ∈ Finset.range (m + 1), μ' i
              = (∑ i ∈ Finset.range (m + 1), μ (i + 1)) + δ := by
            rw [hμ'def]
            rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0 fun _ => δ]
            simp
          rw [hμ'sum, hν'def]
          rw [hifsum, hifsumν] at hbal
          rw [hδdef]
          linarith
        obtain ⟨γ', hγ', hcost'⟩ := ih μ' ν' hμ'nn hν'nn hbal'
        set fr := if μ' 0 = 0 then (0 : ℝ) else δ / μ' 0 with hfrdef
        have hμ'0 : μ' 0 = μ 1 + δ := by
          rw [hμ'def]
          norm_num
        have hδle : δ ≤ μ' 0 := by
          rw [hμ'0]
          have := hμ 1
          linarith
        have hfr01 : 0 ≤ fr ∧ fr ≤ 1 := by
          rw [hfrdef]
          split_ifs with h
          · norm_num
          · have hpos : 0 < μ' 0 := lt_of_le_of_ne (hμ'nn 0) (Ne.symm h)
            constructor
            · positivity
            · rw [div_le_one hpos]
              exact hδle
        have hfrmul : fr * μ' 0 = δ := by
          rw [hfrdef]
          split_ifs with h
          · rw [zero_mul]
            rw [h] at hδle
            linarith
          · rw [div_mul_cancel₀ _ h]
        set γ : ℕ → ℕ → ℝ := fun i j =>
          if j = 0 then (if i = 0 then ν 0 else 0)
          else if i = 0 then fr * γ' 0 (j - 1)
          else if i = 1 then (1 - fr) * γ' 0 (j - 1)
          else γ' (i - 1) (j - 1) with hγdef
        have hγnn : ∀ i j, 0 ≤ γ i j := by
          intro i j
          rw [hγdef]
          dsimp only
          split_ifs with h1 h2 h2 h3
          · exact hν 0
          · exact le_rfl
          · exact mul_nonneg hfr01.1 (hγ'.1 0 (j - 1))
          · exact mul_nonneg (by linarith [hfr01.2]) (hγ'.1 0 (j - 1))
          · exact hγ'.1 (i - 1) (j - 1)
        have hγ00 : γ 0 0 = ν 0 := by
          rw [hγdef]
          norm_num
        have hγi0 : ∀ i, i ≠ 0 → γ i 0 = 0 := by
          intro i hi
          rw [hγdef]
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hi]
        have hγ0j : ∀ j, γ 0 (j + 1) = fr * γ' 0 j := by
          intro j
          rw [hγdef]
          dsimp only
          rw [ite_eq_right (Nat.succ_ne_zero j), ite_eq_left rfl]
          norm_num
        have hγ1j : ∀ j, γ 1 (j + 1) = (1 - fr) * γ' 0 j := by
          intro j
          rw [hγdef]
          dsimp only
          rw [ite_eq_right (Nat.succ_ne_zero j), ite_eq_right one_ne_zero, ite_eq_left rfl]
          norm_num
        have hγij : ∀ i j, γ (i + 2) (j + 1) = γ' (i + 1) j := by
          intro i j
          rw [hγdef]
          dsimp only
          rw [ite_eq_right (Nat.succ_ne_zero j), ite_eq_right (by omega : ¬ i + 2 = 0),
            ite_eq_right (by omega : ¬ i + 2 = 1)]
          norm_num
        have hrow0mem : (0 : ℕ) ∈ Finset.range (m + 1) := by
          simp
        -- row marginals
        have hrow : ∀ i ∈ Finset.range (m + 2),
            ∑ j ∈ Finset.range (m + 2), γ i j = μ i := by
          intro i hi
          rw [Finset.sum_range_succ' (fun j => γ i j) (m + 1)]
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · rw [hγ00]
            have hterm : ∀ j, γ 0 (j + 1) = fr * γ' 0 j := hγ0j
            rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum,
              hγ'.2.1 0 hrow0mem, hfrmul]
            rw [hδdef]
            ring
          · rcases Nat.eq_zero_or_pos (i - 1) with hi1 | hi2
            · have hione : i = 1 := by omega
              subst hione
              rw [hγi0 1 one_ne_zero]
              rw [Finset.sum_congr rfl fun j _ => hγ1j j, ← Finset.mul_sum,
                hγ'.2.1 0 hrow0mem]
              linear_combination hμ'0 - hfrmul
            · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
              rw [hγi0 _ (by omega)]
              rw [Finset.sum_congr rfl fun j _ => hγij i' j]
              have hmem : i' + 1 ∈ Finset.range (m + 1) := by
                rw [Finset.mem_range] at hi ⊢
                omega
              rw [hγ'.2.1 (i' + 1) hmem]
              have hval : μ' (i' + 1) = μ (i' + 2) := by
                rw [hμ'def]
                dsimp only
                rw [ite_eq_right (Nat.succ_ne_zero i'), add_zero]
              rw [hval, add_zero]
        -- column marginals
        have hcol : ∀ j ∈ Finset.range (m + 2),
            ∑ i ∈ Finset.range (m + 2), γ i j = ν j := by
          intro j hj
          rw [Finset.sum_range_succ' (fun i => γ i j) (m + 1)]
          rcases Nat.eq_zero_or_pos j with rfl | hjpos
          · rw [hγ00]
            have hterm : ∀ i, γ (i + 1) 0 = 0 := fun i =>
              hγi0 (i + 1) (Nat.succ_ne_zero i)
            rw [Finset.sum_congr rfl fun i _ => hterm i]
            simp
          · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            rw [hγ0j j']
            rw [Finset.sum_range_succ' (fun i => γ (i + 1) (j' + 1)) m]
            rw [hγ1j j']
            rw [Finset.sum_congr rfl fun i _ => hγij i j']
            have hmem : j' ∈ Finset.range (m + 1) := by
              rw [Finset.mem_range] at hj ⊢
              omega
            have hcol' := hγ'.2.2 j' hmem
            rw [Finset.sum_range_succ' (fun i => γ' i j') m] at hcol'
            rw [hν'def] at hcol'
            dsimp only at hcol'
            linarith [hcol']
        -- cost accounting: the plan pays exactly `δ` more than the reduced one
        have habs0 : ∀ j : ℕ, |((0 : ℕ) : ℝ) - (((j + 1 : ℕ)) : ℝ)|
            = (j : ℝ) + 1 := by
          intro j
          push_cast
          rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) j])]
          ring
        have habs1 : ∀ j : ℕ, |((1 : ℕ) : ℝ) - (((j + 1 : ℕ)) : ℝ)| = (j : ℝ) := by
          intro j
          push_cast
          rw [show (1 : ℝ) - ((j : ℝ) + 1) = -(j : ℝ) by ring, abs_neg,
            abs_of_nonneg (Nat.cast_nonneg j)]
        have habs2 : ∀ i j : ℕ, |(((i + 2 : ℕ)) : ℝ) - (((j + 1 : ℕ)) : ℝ)|
            = |(((i + 1 : ℕ)) : ℝ) - ((j : ℕ) : ℝ)| := by
          intro i j
          congr 1
          push_cast
          ring
        set R : ℕ → ℝ := fun i =>
          ∑ j ∈ Finset.range (m + 2), γ i j * |(i : ℝ) - (j : ℝ)| with hRdef
        have hrow_split : ∀ i : ℕ,
            R i = ∑ j ∈ Finset.range (m + 1),
              γ i (j + 1) * |(i : ℝ) - (((j + 1 : ℕ)) : ℝ)| := by
          intro i
          rw [hRdef]
          dsimp only
          rw [Finset.sum_range_succ'
            (fun j => γ i j * |(i : ℝ) - (j : ℝ)|) (m + 1)]
          have hz : γ i 0 * |(i : ℝ) - ((0 : ℕ) : ℝ)| = 0 := by
            rcases Nat.eq_zero_or_pos i with rfl | hipos
            · simp
            · rw [hγi0 i (by omega), zero_mul]
          rw [hz, add_zero]
        set S1 := ∑ j ∈ Finset.range (m + 1), γ' 0 j * (j : ℝ) with hS1def
        have hR0 : R 0 = fr * S1 + δ := by
          rw [hrow_split 0, hS1def]
          have hterm : ∀ j ∈ Finset.range (m + 1),
              γ 0 (j + 1) * |((0 : ℕ) : ℝ) - (((j + 1 : ℕ)) : ℝ)|
                = fr * (γ' 0 j * (j : ℝ)) + fr * γ' 0 j := by
            intro j _
            rw [hγ0j j, habs0 j]
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, hγ'.2.1 0 hrow0mem, hfrmul,
            ← hS1def]
        have hR1 : R 1 = (1 - fr) * S1 := by
          rw [hrow_split 1, hS1def]
          have hterm : ∀ j ∈ Finset.range (m + 1),
              γ 1 (j + 1) * |((1 : ℕ) : ℝ) - (((j + 1 : ℕ)) : ℝ)|
                = (1 - fr) * (γ' 0 j * (j : ℝ)) := by
            intro j _
            rw [hγ1j j, habs1 j]
            ring
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hS1def]
        have hRi : ∀ i : ℕ, R (i + 2)
            = ∑ j ∈ Finset.range (m + 1),
                γ' (i + 1) j * |(((i + 1 : ℕ)) : ℝ) - ((j : ℕ) : ℝ)| := by
          intro i
          rw [hrow_split (i + 2)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hγij i j, habs2 i j]
        have hcost'split : costU (m + 1) γ'
            = S1 + ∑ i ∈ Finset.range m,
                ∑ j ∈ Finset.range (m + 1),
                  γ' (i + 1) j * |(((i + 1 : ℕ)) : ℝ) - ((j : ℕ) : ℝ)| := by
          unfold costU
          rw [Finset.sum_range_succ' (fun i =>
            ∑ j ∈ Finset.range (m + 1), γ' i j * |(i : ℝ) - (j : ℝ)|) m]
          rw [hS1def]
          have hzero : ∑ j ∈ Finset.range (m + 1),
              γ' 0 j * |((0 : ℕ) : ℝ) - (j : ℝ)|
              = ∑ j ∈ Finset.range (m + 1), γ' 0 j * (j : ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show |((0 : ℕ) : ℝ) - (j : ℝ)| = (j : ℝ) by
              push_cast
              rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg j)]]
          rw [hzero]
          ring
        have hcostγ : costU (m + 2) γ = costU (m + 1) γ' + δ := by
          have hsplit1 : costU (m + 2) γ
              = (∑ i ∈ Finset.range (m + 1), R (i + 1)) + R 0 := by
            unfold costU
            rw [← hRdef]
            exact Finset.sum_range_succ' R (m + 1)
          have hsplit2 : ∑ i ∈ Finset.range (m + 1), R (i + 1)
              = (∑ i ∈ Finset.range m, R (i + 2)) + R 1 :=
            Finset.sum_range_succ' (fun i => R (i + 1)) m
          rw [hsplit1, hsplit2, hR0, hR1, hcost'split]
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.range m) => hRi i]
          ring
        -- the CDF telescopes across the shift
        have hcdf' : ∀ r : ℕ, cdf (fun i => μ' i - ν' i) r
            = cdf (fun i => μ i - ν i) (r + 1) := by
          intro r
          unfold cdf
          rw [Finset.sum_range_succ' (fun i => μ i - ν i) (r + 1)]
          have hterm : ∀ i ∈ Finset.range (r + 1),
              μ' i - ν' i = (μ (i + 1) - ν (i + 1))
                + if i = 0 then δ else 0 := by
            intro i _
            rw [hμ'def, hν'def]
            dsimp only
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
            Finset.sum_ite_eq' (Finset.range (r + 1)) 0 fun _ => δ]
          have h0mem : (0 : ℕ) ∈ Finset.range (r + 1) := by simp
          rw [ite_eq_left h0mem, hδdef]
        have hcdfsum : ∑ r ∈ Finset.range (m + 2),
            |cdf (fun i => μ i - ν i) r|
            = (∑ r ∈ Finset.range (m + 1), |cdf (fun i => μ' i - ν' i) r|)
              + δ := by
          rw [Finset.sum_range_succ'
            (fun r => |cdf (fun i => μ i - ν i) r|) (m + 1)]
          have h0 : |cdf (fun i => μ i - ν i) 0| = δ := by
            unfold cdf
            rw [Finset.sum_range_one, hδdef, abs_of_nonneg (by
              rw [← hδdef]
              exact hδ)]
          rw [h0]
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hcdf' r]
        refine ⟨γ, ⟨hγnn, hrow, hcol⟩, ?_⟩
        rw [hcostγ, hcdfsum]
        linarith
    intro μ ν hμ hν hbal
    rcases le_total (ν 0) (μ 0) with hc | hc
    · exact key μ ν hμ hν hbal hc
    · obtain ⟨γ, hγ, hcost⟩ := key ν μ hν hμ hbal.symm hc
      refine ⟨fun i j => γ j i, ⟨fun i j => hγ.1 j i, fun i hi => hγ.2.2 i hi,
        fun j hj => hγ.2.1 j hj⟩, ?_⟩
      have hcosteq : costU (n + 1) (fun i j => γ j i) = costU (n + 1) γ := by
        unfold costU
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [abs_sub_comm]
      have hcdfeq : ∀ r : ℕ, |cdf (fun i => μ i - ν i) r|
          = |cdf (fun i => ν i - μ i) r| := by
        intro r
        have hneg : cdf (fun i => μ i - ν i) r
            = -cdf (fun i => ν i - μ i) r := by
          unfold cdf
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [hneg, abs_neg]
      rw [hcosteq]
      calc costU (n + 1) γ
          ≤ ∑ r ∈ Finset.range (n + 1), |cdf (fun i => ν i - μ i) r| := hcost
        _ = ∑ r ∈ Finset.range (n + 1), |cdf (fun i => μ i - ν i) r| :=
            Finset.sum_congr rfl fun r _ => (hcdfeq r).symm


/-- The positive part `p₊` of the boundary power. -/
noncomputable def posPart (p : ℕ → ℝ) (i : ℕ) : ℝ := max (p i) 0

/-- The negative part `p₋` of the boundary power. -/
noncomputable def negPart (p : ℕ → ℝ) (i : ℕ) : ℝ := max (-p i) 0

/-- The coherent payment `p̂^pay = (q_c/P)p₊` (NSE.25). -/
noncomputable def coherentPay (n : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, p k) / (∑ k ∈ Finset.range n, posPart p k)
    * posPart p i

/-- The positive counterflow `p_cf⁺ = (N/P)p₊` (NSE.25). -/
noncomputable def cfPlus (n : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, negPart p k) / (∑ k ∈ Finset.range n, posPart p k)
    * posPart p i

/-- Pointwise the signed power is the difference of its parts. -/
theorem posPart_sub_negPart (p : ℕ → ℝ) (i : ℕ) :
    posPart p i - negPart p i = p i := by
  unfold posPart negPart
  rcases le_total (p i) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- **NSE.26**: the exact coherent/counterflow split of the boundary power,
with the coherent payment carrying the total `q_c = ∫p` and both
counterflow parts carrying the mass `N`. -/
theorem counterflow_split (n : ℕ) (p : ℕ → ℝ)
    (hP : 0 < ∑ k ∈ Finset.range n, posPart p k) :
    (∀ i, p i = coherentPay n p i + cfPlus n p i - negPart p i) ∧
      ∑ i ∈ Finset.range n, coherentPay n p i = ∑ i ∈ Finset.range n, p i ∧
      ∑ i ∈ Finset.range n, cfPlus n p i
        = ∑ i ∈ Finset.range n, negPart p i := by
  have hPN : ∑ k ∈ Finset.range n, p k
      = (∑ k ∈ Finset.range n, posPart p k)
        - ∑ k ∈ Finset.range n, negPart p k := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_congr rfl fun i _ => (posPart_sub_negPart p i).symm)
  refine ⟨fun i => ?_, ?_, ?_⟩
  · unfold coherentPay cfPlus
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_mul, hPN]
    rw [show ∑ k ∈ Finset.range n, posPart p k
        - ∑ k ∈ Finset.range n, negPart p k
        + ∑ k ∈ Finset.range n, negPart p k
        = ∑ k ∈ Finset.range n, posPart p k by ring]
    rw [mul_comm, mul_div_assoc, div_self hP.ne', mul_one]
    rw [← posPart_sub_negPart p i]
  · unfold coherentPay
    rw [← Finset.mul_sum, div_mul_cancel₀ _ hP.ne']
  · unfold cfPlus
    rw [← Finset.mul_sum, div_mul_cancel₀ _ hP.ne']

/-- **NSE.26 (uniqueness)**: the coherent payment is the unique proportional
positive replay of the actual payment with total `q_c`. -/
theorem coherent_unique (n : ℕ) (p : ℕ → ℝ)
    (hP : 0 < ∑ k ∈ Finset.range n, posPart p k) (c : ℝ)
    (hc : ∑ i ∈ Finset.range n, c * posPart p i
      = ∑ i ∈ Finset.range n, p i) :
    ∀ i, c * posPart p i = coherentPay n p i := by
  intro i
  have hcval : c = (∑ k ∈ Finset.range n, p k)
      / ∑ k ∈ Finset.range n, posPart p k := by
    rw [← Finset.mul_sum] at hc
    rw [eq_div_iff hP.ne']
    exact hc
  unfold coherentPay
  rw [hcval]

set_option maxHeartbeats 400000 in
-- assembling both transport bounds re-elaborates the grid sums; the default
-- heartbeat budget is too small
/-- **NSE.27**: on the finite scale interval `[a,b]` with uniform grid
`κ_i = a + h·i`, the minimum open-boundary transport cost of the balanced
counterflow `(p_cf⁺, p_cf⁻)` is attained and equals the exact
Kantorovich–Rubinstein CDF cost `h∑_r|∑_{i≤r}(p_cf⁺-p_cf⁻)_i|`. -/
theorem counterflow_transport (n : ℕ) (a h : ℝ) (hh : 0 < h) (p : ℕ → ℝ)
    (hP : 0 < ∑ k ∈ Finset.range n, posPart p k) :
    IsLeast {c : ℝ | ∃ γ, IsCoupling n (cfPlus n p) (negPart p) γ ∧
        c = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          γ i j * |(a + h * i) - (a + h * j)|}
      (h * ∑ r ∈ Finset.range n,
        |cdf (fun i => cfPlus n p i - negPart p i) r|) := by
  have hplusnn : ∀ i, 0 ≤ cfPlus n p i := by
    intro i
    unfold cfPlus posPart negPart
    have h1 : 0 ≤ ∑ k ∈ Finset.range n, max (-p k) 0 :=
      Finset.sum_nonneg fun k _ => le_max_right _ _
    have h2 : 0 ≤ max (p i) 0 := le_max_right _ _
    positivity
  have hminusnn : ∀ i, 0 ≤ negPart p i := fun i => le_max_right _ _
  have hbal : ∑ i ∈ Finset.range n, cfPlus n p i
      = ∑ i ∈ Finset.range n, negPart p i :=
    (counterflow_split n p hP).2.2
  have hcostconv : ∀ γ : ℕ → ℕ → ℝ,
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        γ i j * |(a + h * i) - (a + h * j)| = h * costU n γ := by
    intro γ
    unfold costU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (a + h * i) - (a + h * j) = h * ((i : ℝ) - (j : ℝ)) by ring,
      abs_mul, abs_of_pos hh]
    ring
  constructor
  · -- attainment: the inductive plan meets the duality floor
    obtain ⟨γ, hγ, hcost⟩ := exists_coupling n (cfPlus n p) (negPart p)
      hplusnn hminusnn hbal
    have hlow := coupling_lower_bound n hbal hγ
    have heq : costU n γ
        = ∑ r ∈ Finset.range n, |cdf (fun i => cfPlus n p i - negPart p i) r| :=
      le_antisymm hcost hlow
    exact ⟨γ, hγ, by rw [hcostconv γ, heq]⟩
  · -- duality lower bound for every admissible plan
    rintro c ⟨γ, hγ, rfl⟩
    rw [hcostconv γ]
    exact mul_le_mul_of_nonneg_left (coupling_lower_bound n hbal hγ) hh.le

end NSCounterflow

end BoundaryCounterflow

/-! ### Exact centred commutator and donor ancestry boundary

Record `thm:NS-centred-critical-commutator` (NSE.33–NSE.35).

Rendering: the exact finite Fourier Galerkin model of the periodic packet:
divergence-free, reflection-real velocity modes `û : ℤ³ → ℂ³` supported on
a finite symmetric mean-free frequency grid `S`.  The advection
`((u·∇)v)^(k) = i∑_{p+q=k}(û(p)·q)v̂(q)`, the Leray projector
`P_kw = w - (k·w/|k|²)k`, `𝒩_uv = P((u·∇)v)`, the multiplier `Λ = |k|`,
and `Φ_c = -Re⟪A^{-1/4}𝒩_uu, A^{3/4}u⟫` are the literal Fourier formulas
(NSE.1–NSE.2).  NSE.33 (both the `Λ` and the centred `Λ-κ̄I` commutator
forms) and the alias expansion NSE.34 are proved exactly on the model, and
NSE.35 is the reverse triangle inequality for the euclidean moduli of every
ordered alias `p + q = k`. -/

section CentredCommutator

namespace NSCommutator

/-- The frequency lattice `ℤ³`. -/
abbrev Z3 := Fin 3 → ℤ

/-- The complex velocity fibre `ℂ³`. -/
abbrev V3 := Fin 3 → ℂ

/-- The euclidean frequency modulus `|k|`. -/
noncomputable def nrm (k : Z3) : ℝ :=
  ‖(WithLp.toLp 2 fun c => ((k c : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 3))‖

/-- The real-frequency pairing `k·w` of a lattice vector against a mode. -/
noncomputable def dotZ (k : Z3) (w : V3) : ℂ := ∑ c, ((k c : ℝ) : ℂ) * w c

/-- The manuscript mode pairing `x·conj y`. -/
noncomputable def dotc (x y : V3) : ℂ := ∑ c, x c * (starRingEnd ℂ) (y c)

/-- The field pairing over the frequency grid. -/
noncomputable def pairS (S : Finset Z3) (f g : Z3 → V3) : ℂ :=
  ∑ k ∈ S, dotc (f k) (g k)

/-- The Fourier advection `((u·∇)v)^(k) = i∑_{p∈S}(û(p)·(k-p))v̂(k-p)`. -/
noncomputable def adv (S : Finset Z3) (u v : Z3 → V3) (k : Z3) : V3 :=
  fun c => ∑ p ∈ S, Complex.I * dotZ (k - p) (u p) * v (k - p) c

/-- The Fourier Leray projector `P_kw = w - (k·w/|k|²)k`. -/
noncomputable def leray (k : Z3) (w : V3) : V3 :=
  fun c => w c - dotZ k w / ((nrm k : ℝ) : ℂ) ^ 2 * ((k c : ℝ) : ℂ)

/-- The projected nonlinearity `𝒩_uv = P((u·∇)v)`. -/
noncomputable def NL (S : Finset Z3) (u v : Z3 → V3) (k : Z3) : V3 :=
  leray k (adv S u v k)

/-- The critical multiplier `Λ`: multiplication by `|k|`. -/
noncomputable def lam (f : Z3 → V3) (k : Z3) : V3 :=
  fun c => ((nrm k : ℝ) : ℂ) * f k c

/-- The centred multiplier `Λ - κ̄I`. -/
noncomputable def lamShift (kb : ℝ) (f : Z3 → V3) (k : Z3) : V3 :=
  fun c => ((nrm k - kb : ℝ) : ℂ) * f k c

/-- The reduced source `c = A^{-1/4}𝒩_uu` (NSE.1). -/
noncomputable def redSource (S : Finset Z3) (u : Z3 → V3) (k : Z3) : V3 :=
  fun c => (((Real.sqrt (nrm k))⁻¹ : ℝ) : ℂ) * NL S u u k c

/-- The critical target `v = A^{3/4}u` (NSE.1). -/
noncomputable def critTarget (u : Z3 → V3) (k : Z3) : V3 :=
  fun c => ((nrm k * Real.sqrt (nrm k) : ℝ) : ℂ) * u k c

/-- The critical work `Φ_c = -Re⟪c,v⟫` of the Galerkin packet (NSE.2). -/
noncomputable def PhiC (S : Finset Z3) (u : Z3 → V3) : ℝ :=
  -(pairS S (redSource S u) (critTarget u)).re

/-! #### Mode-pairing calculus -/

/-- Left scalar comes out of the pairing. -/
theorem dotc_scale_left (a : ℂ) (x y : V3) :
    dotc (fun c => a * x c) y = a * dotc x y := by
  unfold dotc
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- A real right scalar comes out of the pairing unconjugated. -/
theorem dotc_scale_right (a : ℝ) (x y : V3) :
    dotc x (fun c => ((a : ℝ) : ℂ) * y c) = ((a : ℝ) : ℂ) * dotc x y := by
  unfold dotc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- A complex right scalar comes out conjugated. -/
theorem dotc_scale_right' (a : ℂ) (x y : V3) :
    dotc x (fun c => a * y c) = (starRingEnd ℂ) a * dotc x y := by
  unfold dotc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  ring

/-- The pairing is additive in differences on the left. -/
theorem dotc_sub_left (x₁ x₂ y : V3) :
    dotc (fun c => x₁ c - x₂ c) y = dotc x₁ y - dotc x₂ y := by
  unfold dotc
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The pairing is additive in differences on the right. -/
theorem dotc_sub_right (x y₁ y₂ : V3) :
    dotc x (fun c => y₁ c - y₂ c) = dotc x y₁ - dotc x y₂ := by
  unfold dotc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sub]
  ring

/-- The pairing against the zero mode vanishes on the left. -/
theorem dotc_zero_left (y : V3) : dotc 0 y = 0 := by
  unfold dotc
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Pi.zero_apply, zero_mul]

/-- The pairing against the zero mode vanishes on the right. -/
theorem dotc_zero_right (x : V3) : dotc x 0 = 0 := by
  unfold dotc
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Pi.zero_apply, map_zero, mul_zero]

/-- Conjugate symmetry of the mode pairing. -/
theorem dotc_conj_symm (x y : V3) :
    dotc x y = (starRingEnd ℂ) (dotc y x) := by
  unfold dotc
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

/-- Complex scalars come out of the frequency pairing. -/
theorem dotZ_scale (k : Z3) (a : ℂ) (w : V3) :
    dotZ k (fun c => a * w c) = a * dotZ k w := by
  unfold dotZ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The frequency pairing is additive in the lattice argument. -/
theorem dotZ_sub_first (a b : Z3) (w : V3) :
    dotZ (a - b) w = dotZ a w - dotZ b w := by
  unfold dotZ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.sub_apply]
  push_cast
  ring

/-- The conjugated frequency pairing is the pairing of the conjugate mode. -/
theorem conj_dotZ (k : Z3) (w : V3) :
    (starRingEnd ℂ) (dotZ k w) = dotZ k fun c => (starRingEnd ℂ) (w c) := by
  unfold dotZ
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, Complex.conj_ofReal]

/-- Pairing the lattice direction on the left gives the conjugated
frequency pairing. -/
theorem dotc_kvec_left (k : Z3) (y : V3) :
    dotc (fun c => ((k c : ℝ) : ℂ)) y = (starRingEnd ℂ) (dotZ k y) := by
  rw [conj_dotZ]
  unfold dotc dotZ
  rfl

/-- Pairing the lattice direction on the right gives the frequency
pairing. -/
theorem dotc_kvec_right (k : Z3) (x : V3) :
    dotc x (fun c => ((k c : ℝ) : ℂ)) = dotZ k x := by
  unfold dotc dotZ
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.conj_ofReal]
  ring

/-- The Leray projector drops in the left slot of a divergence-free
pairing. -/
theorem dotc_leray_left {k : Z3} (z : V3) {w : V3} (hw : dotZ k w = 0) :
    dotc (leray k z) w = dotc z w := by
  unfold leray
  rw [dotc_sub_left]
  have hker : dotc (fun c => dotZ k z / ((nrm k : ℝ) : ℂ) ^ 2
      * ((k c : ℝ) : ℂ)) w = 0 := by
    rw [dotc_scale_left, dotc_kvec_left, hw, map_zero, mul_zero]
  rw [hker, sub_zero]

/-- The Leray projector drops in the right slot against a divergence-free
mode. -/
theorem dotc_leray_right {k : Z3} {x : V3} (hx : dotZ k x = 0) (z : V3) :
    dotc x (leray k z) = dotc x z := by
  unfold leray
  rw [dotc_sub_right]
  have hker : dotc x (fun c => dotZ k z / ((nrm k : ℝ) : ℂ) ^ 2
      * ((k c : ℝ) : ℂ)) = 0 := by
    rw [dotc_scale_right', dotc_kvec_right, hx, mul_zero]
  rw [hker, sub_zero]

/-- Expansion of an advection pairing in the left slot. -/
theorem dotc_adv_left (S : Finset Z3) (u x : Z3 → V3) (k : Z3) (w : V3) :
    dotc (adv S u x k) w
      = ∑ p ∈ S, Complex.I * dotZ (k - p) (u p) * dotc (x (k - p)) w := by
  unfold adv dotc
  beta_reduce
  have hc : ∀ c : Fin 3,
      (∑ p ∈ S, Complex.I * dotZ (k - p) (u p) * x (k - p) c)
          * (starRingEnd ℂ) (w c)
        = ∑ p ∈ S, Complex.I * dotZ (k - p) (u p)
            * (x (k - p) c * (starRingEnd ℂ) (w c)) := by
    intro c
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hc c,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

/-- Expansion of an advection pairing in the right slot. -/
theorem dotc_adv_right (S : Finset Z3) (u y : Z3 → V3) (k : Z3) (x : V3) :
    dotc x (adv S u y k)
      = ∑ p ∈ S, -Complex.I * (starRingEnd ℂ) (dotZ (k - p) (u p))
          * dotc x (y (k - p)) := by
  unfold adv dotc
  beta_reduce
  have hswap : ∀ c : Fin 3, x c * (starRingEnd ℂ)
      (∑ p ∈ S, Complex.I * dotZ (k - p) (u p) * y (k - p) c)
      = ∑ p ∈ S, -Complex.I * (starRingEnd ℂ) (dotZ (k - p) (u p))
          * (x c * (starRingEnd ℂ) (y (k - p) c)) := by
    intro c
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, map_mul, Complex.conj_I]
    ring
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hswap c,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

/-! #### Grid reindexing -/

/-- Transport of a doubly indexed grid sum along the alias shift
`(k,p) ↦ (k-p,p)`, given vanishing off the shifted grid. -/
theorem sum_shift_sub (S : Finset Z3) (F H : Z3 → Z3 → ℂ)
    (hF : ∀ k ∈ S, ∀ p ∈ S, k - p ∉ S → F k p = 0)
    (hH : ∀ a ∈ S, ∀ p ∈ S, a + p ∉ S → H a p = 0)
    (hmatch : ∀ k ∈ S, ∀ p ∈ S, k - p ∈ S → F k p = H (k - p) p) :
    ∑ k ∈ S, ∑ p ∈ S, F k p = ∑ a ∈ S, ∑ p ∈ S, H a p := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  rw [← Finset.sum_filter_add_sum_filter_not (S ×ˢ S)
    (fun kp => kp.1 - kp.2 ∈ S) (fun kp => F kp.1 kp.2)]
  rw [← Finset.sum_filter_add_sum_filter_not (S ×ˢ S)
    (fun kp => kp.1 + kp.2 ∈ S) (fun kp => H kp.1 kp.2)]
  have hF0 : ∑ kp ∈ (S ×ˢ S).filter (fun kp => ¬ kp.1 - kp.2 ∈ S),
      F kp.1 kp.2 = 0 := by
    refine Finset.sum_eq_zero fun kp hkp => ?_
    rw [Finset.mem_filter, Finset.mem_product] at hkp
    exact hF kp.1 hkp.1.1 kp.2 hkp.1.2 hkp.2
  have hH0 : ∑ kp ∈ (S ×ˢ S).filter (fun kp => ¬ kp.1 + kp.2 ∈ S),
      H kp.1 kp.2 = 0 := by
    refine Finset.sum_eq_zero fun kp hkp => ?_
    rw [Finset.mem_filter, Finset.mem_product] at hkp
    exact hH kp.1 hkp.1.1 kp.2 hkp.1.2 hkp.2
  rw [hF0, hH0, add_zero, add_zero]
  refine Finset.sum_nbij' (fun kp => (kp.1 - kp.2, kp.2))
    (fun ab => (ab.1 + ab.2, ab.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, p⟩ hkp
    rw [Finset.mem_filter, Finset.mem_product] at hkp ⊢
    refine ⟨⟨hkp.2, hkp.1.2⟩, ?_⟩
    dsimp only
    rw [sub_add_cancel]
    exact hkp.1.1
  · rintro ⟨a, p⟩ hab
    rw [Finset.mem_filter, Finset.mem_product] at hab ⊢
    refine ⟨⟨hab.2, hab.1.2⟩, ?_⟩
    dsimp only
    rw [add_sub_cancel_right]
    exact hab.1.1
  · rintro ⟨k, p⟩ _
    dsimp only
    rw [sub_add_cancel]
  · rintro ⟨a, p⟩ _
    dsimp only
    rw [add_sub_cancel_right]
  · rintro ⟨k, p⟩ hkp
    rw [Finset.mem_filter, Finset.mem_product] at hkp
    exact hmatch k hkp.1.1 p hkp.1.2 hkp.2

section MainData

variable (S : Finset Z3) (u : Z3 → V3)
variable (hsupp : ∀ k, k ∉ S → u k = 0)
variable (hreal : ∀ k c, u (-k) c = (starRingEnd ℂ) (u k c))
variable (hdiv : ∀ k, dotZ k (u k) = 0)
variable (hS : ∀ k : Z3, k ∈ S ↔ -k ∈ S)
variable (h0 : (0 : Z3) ∉ S)

/-- Nonzero lattice frequencies have positive modulus. -/
theorem nrm_pos {k : Z3} (hk : k ≠ 0) : 0 < nrm k := by
  unfold nrm
  rw [norm_pos_iff]
  intro hcon
  refine hk (funext fun c => ?_)
  have hc := congrFun (congrArg WithLp.ofLp hcon) c
  simp only [WithLp.ofLp_zero, Pi.zero_apply] at hc
  have hcast : ((k c : ℤ) : ℝ) = 0 := hc
  exact_mod_cast hcast

include hdiv h0 in
/-- The critical work through the unprojected advection pairing. -/
theorem PhiC_eq_adv : PhiC S u = -(pairS S (adv S u u) (lam u)).re := by
  unfold PhiC
  congr 2
  unfold pairS
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkne : k ≠ 0 := by
    intro h
    rw [h] at hk
    exact h0 hk
  have hnpos := nrm_pos hkne
  have hs : Real.sqrt (nrm k) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
  have hscal : dotc (redSource S u k) (critTarget u k)
      = ((nrm k : ℝ) : ℂ) * dotc (NL S u u k) (u k) := by
    unfold redSource critTarget
    rw [dotc_scale_left, dotc_scale_right, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp
  rw [hscal]
  have hdrop : dotc (NL S u u k) (u k) = dotc (adv S u u k) (u k) := by
    unfold NL
    exact dotc_leray_left _ (hdiv k)
  rw [hdrop]
  have hlam : dotc (adv S u u k) (lam u k)
      = ((nrm k : ℝ) : ℂ) * dotc (adv S u u k) (u k) := by
    unfold lam
    rw [dotc_scale_right]
  rw [hlam]

include hreal hdiv hS in
/-- **Skew cancellation**: the advection pairing is antisymmetric over
grid-supported modes. -/
theorem adv_skew (x y : Z3 → V3) (hx : ∀ k, k ∉ S → x k = 0)
    (hy : ∀ k, k ∉ S → y k = 0) :
    pairS S (adv S u x) y + pairS S x (adv S u y) = 0 := by
  classical
  have hA : pairS S (adv S u x) y
      = ∑ k ∈ S, ∑ p ∈ S,
          Complex.I * dotZ (k - p) (u p) * dotc (x (k - p)) (y k) := by
    unfold pairS
    exact Finset.sum_congr rfl fun k _ => dotc_adv_left S u x k (y k)
  have hB : pairS S x (adv S u y)
      = ∑ k ∈ S, ∑ p ∈ S,
          -Complex.I * dotZ (k - p) (u (-p)) * dotc (x k) (y (k - p)) := by
    unfold pairS
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotc_adv_right S u y k (x k)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [conj_dotZ]
    have hfn : (fun c => (starRingEnd ℂ) (u p c)) = u (-p) := by
      funext c
      rw [← hreal p c]
    rw [hfn]
  have hBneg : pairS S x (adv S u y)
      = ∑ k ∈ S, ∑ p ∈ S,
          -Complex.I * dotZ (k + p) (u p) * dotc (x k) (y (k + p)) := by
    rw [hB]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_equiv (Equiv.neg Z3) (fun p => ?_) fun p hp => ?_
    · rw [Equiv.neg_apply]
      exact hS p
    · rw [Equiv.neg_apply, ← sub_eq_add_neg]
  have hcancel : ∑ k ∈ S, ∑ p ∈ S,
      Complex.I * dotZ (k - p) (u p) * dotc (x (k - p)) (y k)
      = ∑ a ∈ S, ∑ p ∈ S,
          -(-Complex.I * dotZ (a + p) (u p) * dotc (x a) (y (a + p))) := by
    refine sum_shift_sub S _ _ ?_ ?_ ?_
    · intro k _ p _ hkp
      rw [hx _ hkp, dotc_zero_left, mul_zero]
    · intro a _ p _ hap
      rw [hy _ hap, dotc_zero_right, mul_zero, neg_zero]
    · intro k _ p _ hkp
      rw [sub_add_cancel]
      have hzk : dotZ (k - p) (u p) = dotZ k (u p) := by
        rw [dotZ_sub_first, hdiv p, sub_zero]
      rw [hzk]
      ring
  rw [hA, hBneg, hcancel, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  ring

end MainData

/-- The frequency pairing is additive in differences of modes. -/
theorem dotZ_sub_right (k : Z3) (y₁ y₂ : V3) :
    dotZ k (fun c => y₁ c - y₂ c) = dotZ k y₁ - dotZ k y₂ := by
  unfold dotZ
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- Conjugate symmetry of the grid pairing. -/
theorem pairS_conj_symm (S : Finset Z3) (f g : Z3 → V3) :
    pairS S f g = (starRingEnd ℂ) (pairS S g f) := by
  unfold pairS
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => dotc_conj_symm _ _

section MainTheorems

variable (S : Finset Z3) (u : Z3 → V3)
variable (hsupp : ∀ k, k ∉ S → u k = 0)
variable (hreal : ∀ k c, u (-k) c = (starRingEnd ℂ) (u k c))
variable (hdiv : ∀ k, dotZ k (u k) = 0)
variable (hS : ∀ k : Z3, k ∈ S ↔ -k ∈ S)
variable (h0 : (0 : Z3) ∉ S)

include hsupp hreal hdiv hS h0 in
/-- **NSE.33**: the exact centred commutator identities
`2Φ_c = -Re⟪[Λ,𝒩_u]u,u⟫ = -Re⟪[Λ-κ̄I,𝒩_u]u,u⟫` on the Galerkin model,
for every centring constant `κ̄`. -/
theorem centred_commutator (kb : ℝ) :
    2 * PhiC S u
        = -(pairS S (fun k => fun c =>
            lam (NL S u u) k c - NL S u (lam u) k c) u).re ∧
      2 * PhiC S u
        = -(pairS S (fun k => fun c =>
            lamShift kb (NL S u u) k c - NL S u (lamShift kb u) k c) u).re := by
  -- support of the frequency-weighted field
  have hlamsupp : ∀ k, k ∉ S → lam u k = 0 := by
    intro k hk
    funext c
    unfold lam
    rw [hsupp k hk]
    rw [Pi.zero_apply, mul_zero]
  -- the split of the commutator pairing
  have hcomm : pairS S (fun k => fun c =>
      lam (NL S u u) k c - NL S u (lam u) k c) u
      = pairS S (lam (NL S u u)) u - pairS S (NL S u (lam u)) u := by
    unfold pairS
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => dotc_sub_left _ _ _
  -- the frequency weight shuffles across the pairing
  have hT1 : pairS S (lam (NL S u u)) u = pairS S (NL S u u) (lam u) := by
    unfold pairS
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : dotc (lam (NL S u u) k) (u k)
        = ((nrm k : ℝ) : ℂ) * dotc (NL S u u k) (u k) := by
      unfold lam
      rw [dotc_scale_left]
    have h2 : dotc (NL S u u k) (lam u k)
        = ((nrm k : ℝ) : ℂ) * dotc (NL S u u k) (u k) := by
      unfold lam
      rw [dotc_scale_right]
    rw [h1, h2]
  -- the Leray projector drops against divergence-free right slots
  have hlamdiv : ∀ k, dotZ k (lam u k) = 0 := by
    intro k
    unfold lam
    rw [dotZ_scale, hdiv, mul_zero]
  have hT1' : pairS S (NL S u u) (lam u) = pairS S (adv S u u) (lam u) := by
    unfold pairS
    exact Finset.sum_congr rfl fun k _ => dotc_leray_left _ (hlamdiv k)
  have hT2 : pairS S (NL S u (lam u)) u = pairS S (adv S u (lam u)) u := by
    unfold pairS
    exact Finset.sum_congr rfl fun k _ => dotc_leray_left _ (hdiv k)
  -- skew cancellation and conjugate symmetry
  have hskew := adv_skew S u hreal hdiv hS (lam u) u hlamsupp hsupp
  have hconj : pairS S (lam u) (adv S u u)
      = (starRingEnd ℂ) (pairS S (adv S u u) (lam u)) :=
    pairS_conj_symm S _ _
  have hPhi := PhiC_eq_adv S u hdiv h0
  set t := (pairS S (adv S u u) (lam u)).re with htdef
  have hT2re : (pairS S (NL S u (lam u)) u).re = -t := by
    rw [hT2]
    have h1 : pairS S (adv S u (lam u)) u = -pairS S (lam u) (adv S u u) := by
      linear_combination hskew
    rw [h1, hconj, Complex.neg_re, Complex.conj_re, htdef]
  have hfirst : 2 * PhiC S u
      = -(pairS S (fun k => fun c =>
          lam (NL S u u) k c - NL S u (lam u) k c) u).re := by
    rw [hcomm, Complex.sub_re, hT1, hT1', hT2re, hPhi, htdef]
    ring
  refine ⟨hfirst, ?_⟩
  -- the centring constant cancels in the commutator field
  have hadvlin : ∀ k, adv S u (lamShift kb u) k
      = fun c => adv S u (lam u) k c - ((kb : ℝ) : ℂ) * adv S u u k c := by
    intro k
    funext c
    unfold adv lamShift lam
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    ring
  have hlerlin : ∀ (k : Z3) (w₁ w₂ : V3) (a : ℂ) (c : Fin 3),
      leray k (fun c => w₁ c - a * w₂ c) c = leray k w₁ c - a * leray k w₂ c := by
    intro k w₁ w₂ a c
    unfold leray
    rw [dotZ_sub_right]
    have hz : dotZ k (fun c => a * w₂ c) = a * dotZ k w₂ := dotZ_scale k a w₂
    rw [hz]
    ring
  have hNLlin : ∀ k c, NL S u (lamShift kb u) k c
      = NL S u (lam u) k c - ((kb : ℝ) : ℂ) * NL S u u k c := by
    intro k c
    unfold NL
    rw [hadvlin k]
    exact hlerlin k _ _ _ c
  have hfield : (fun k => fun c =>
      lamShift kb (NL S u u) k c - NL S u (lamShift kb u) k c)
      = fun k => fun c => lam (NL S u u) k c - NL S u (lam u) k c := by
    funext k c
    rw [hNLlin k c]
    unfold lamShift lam
    push_cast
    ring
  rw [hfield]
  exact hfirst

include hsupp hreal hdiv hS h0 in
/-- **NSE.34**: the exact Fourier alias expansion of the centred
commutator work,
`2Φ_c = -Re∑_{p+q=k} i(|k|-|q|)(û(p)·q)û(q)·conj(û(k))`. -/
theorem centred_commutator_fourier :
    2 * PhiC S u
      = -(∑ p ∈ S, ∑ q ∈ S, Complex.I * ((nrm (p + q) - nrm q : ℝ) : ℂ)
          * dotZ q (u p) * dotc (u q) (u (p + q))).re := by
  classical
  -- the two advection pairings as double grid sums
  have hlamdiv : ∀ k, dotZ k (lam u k) = 0 := by
    intro k
    unfold lam
    rw [dotZ_scale, hdiv, mul_zero]
  have hT1 : pairS S (adv S u u) (lam u)
      = ∑ k ∈ S, ∑ p ∈ S, Complex.I * dotZ (k - p) (u p)
          * (((nrm k : ℝ) : ℂ) * dotc (u (k - p)) (u k)) := by
    unfold pairS
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotc_adv_left S u u k (lam u k)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h2 : dotc (u (k - p)) (lam u k)
        = ((nrm k : ℝ) : ℂ) * dotc (u (k - p)) (u k) := by
      unfold lam
      rw [dotc_scale_right]
    rw [h2]
  have hT2 : pairS S (adv S u (lam u)) u
      = ∑ k ∈ S, ∑ p ∈ S, Complex.I * dotZ (k - p) (u p)
          * (((nrm (k - p) : ℝ) : ℂ) * dotc (u (k - p)) (u k)) := by
    unfold pairS
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotc_adv_left S u (lam u) k (u k)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h2 : dotc (lam u (k - p)) (u k)
        = ((nrm (k - p) : ℝ) : ℂ) * dotc (u (k - p)) (u k) := by
      unfold lam
      rw [dotc_scale_left]
    rw [h2]
  -- the alias reindexing to donor-frequency variables
  have hshift : ∑ k ∈ S, ∑ p ∈ S,
      Complex.I * ((nrm k - nrm (k - p) : ℝ) : ℂ) * dotZ (k - p) (u p)
        * dotc (u (k - p)) (u k)
      = ∑ q ∈ S, ∑ p ∈ S,
          Complex.I * ((nrm (p + q) - nrm q : ℝ) : ℂ) * dotZ q (u p)
            * dotc (u q) (u (p + q)) := by
    refine sum_shift_sub S _ _ ?_ ?_ ?_
    · intro k _ p _ hkp
      rw [hsupp _ hkp, dotc_zero_left, mul_zero]
    · intro a _ p _ hap
      have hpa : p + a = a + p := by abel
      rw [hpa, hsupp _ hap, dotc_zero_right, mul_zero]
    · intro k _ p _ hkp
      have hk : p + (k - p) = k := by abel
      rw [hk]
  -- assemble the real parts through the commutator identities
  have hskew := adv_skew S u hreal hdiv hS (lam u) u (by
    intro k hk
    funext c
    unfold lam
    rw [hsupp k hk]
    rw [Pi.zero_apply, mul_zero]) hsupp
  have hconj : pairS S (lam u) (adv S u u)
      = (starRingEnd ℂ) (pairS S (adv S u u) (lam u)) :=
    pairS_conj_symm S _ _
  have hPhi := PhiC_eq_adv S u hdiv h0
  set t := (pairS S (adv S u u) (lam u)).re with htdef
  have hT2re : (pairS S (adv S u (lam u)) u).re = -t := by
    have h1 : pairS S (adv S u (lam u)) u = -pairS S (lam u) (adv S u u) := by
      linear_combination hskew
    rw [h1, hconj, Complex.neg_re, Complex.conj_re, htdef]
  have hdiff : pairS S (adv S u u) (lam u) - pairS S (adv S u (lam u)) u
      = ∑ q ∈ S, ∑ p ∈ S,
          Complex.I * ((nrm (p + q) - nrm q : ℝ) : ℂ) * dotZ q (u p)
            * dotc (u q) (u (p + q)) := by
    rw [hT1, hT2, ← hshift, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    ring
  have hswap : ∑ p ∈ S, ∑ q ∈ S, Complex.I * ((nrm (p + q) - nrm q : ℝ) : ℂ)
      * dotZ q (u p) * dotc (u q) (u (p + q))
      = ∑ q ∈ S, ∑ p ∈ S, Complex.I * ((nrm (p + q) - nrm q : ℝ) : ℂ)
          * dotZ q (u p) * dotc (u q) (u (p + q)) := Finset.sum_comm
  rw [hswap, ← hdiff, Complex.sub_re, hT2re, hPhi, htdef]
  ring

/-- **NSE.35**: every ordered alias `p + q = k` satisfies
`||k|-|q|| ≤ |p|` — the reverse triangle inequality of the euclidean
frequency moduli. -/
theorem ordered_alias_bound (p q : Z3) : |nrm (p + q) - nrm q| ≤ nrm p := by
  unfold nrm
  have hadd : (WithLp.toLp 2 fun c => (((p + q) c : ℤ) : ℝ)
        : EuclideanSpace ℝ (Fin 3))
      = (WithLp.toLp 2 fun c => ((p c : ℤ) : ℝ))
        + WithLp.toLp 2 fun c => ((q c : ℤ) : ℝ) := by
    rw [← WithLp.toLp_add]
    congr 1
    funext c
    change (((p + q) c : ℤ) : ℝ) = ((p c : ℤ) : ℝ) + ((q c : ℤ) : ℝ)
    rw [Pi.add_apply]
    push_cast
    ring
  calc |‖(WithLp.toLp 2 fun c => (((p + q) c : ℤ) : ℝ)
        : EuclideanSpace ℝ (Fin 3))‖
      - ‖(WithLp.toLp 2 fun c => ((q c : ℤ) : ℝ)
        : EuclideanSpace ℝ (Fin 3))‖|
      ≤ ‖(WithLp.toLp 2 fun c => (((p + q) c : ℤ) : ℝ)
          : EuclideanSpace ℝ (Fin 3))
        - WithLp.toLp 2 fun c => ((q c : ℤ) : ℝ)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(WithLp.toLp 2 fun c => ((p c : ℤ) : ℝ)
        : EuclideanSpace ℝ (Fin 3))‖ := by
      rw [hadd, add_sub_cancel_right]

end MainTheorems

end NSCommutator

end CentredCommutator

/-! ### Sector-patched reflected line and coherent half-amplitude

Record `thm:RPESM-sector-patched-line` (RTH.11–RTH.15).

Rendering: the finite reflection-stable cover is a finite discrete base `X`
with reflection `θ`, patch sets `U α ⊆ X` and unitary transition cocycle
`g`; sections of the line are patch families `v α` with `v α = g α β · v β`
on overlaps; the reflection acts on scalars by `Θ(f)(x) = conj(f(θx))`; the
base state `ω` is a reflection-positive linear functional.  RTH.11 is the
fibrewise isometry of the square-partition patching map into the trivial
bundle `X × ℂ^A`.  RTH.12 gives the reflected coherent amplitude as a sum
of reflected squares, hence a reflection-positive reweighting for every PSD
`K`, invariant under unitary central sector frame changes.  RTH.13
identifies `Z_{K,b} = ω(z) = Tr(K^{1/2}S_bK^{1/2})`, proves
`R = K^{1/2}S_bK^{1/2} ⪰ 0`, renders the minimum half-carrier dimension as
the attained `IsLeast` of all Gram factorizations of `R` at `rank R`, and
provides an explicit two-sector witness that omitting the off-diagonal
entries of `K` replaces the pure (coherent) carrier state by a mixture.
RTH.14 is the global-scalar-half-frame/Čech-coboundary equivalence, with
the Real compatibility on the reflection-real branch rendered as the global
patch independence of the reflected frame defect.  RTH.15 is the exact
patching of the multiplicative line one-form `η = (ds/s)·a` on the discrete
edge model, the determination of its modulus (`2Reη`) by the section and
connection moduli, and an explicit witness that the phase (`Imη`) is
independent line data. -/

section SectorPatchedLine

open scoped ComplexOrder

namespace RPESMLine

variable {X : Type*} [Fintype X] {A : Type*} [Fintype A] [DecidableEq A]

/-- The scalar reflection `Θ(f)(x) = conj(f(θx))`. -/
noncomputable def refl (θ : X → X) (f : X → ℂ) : X → ℂ :=
  fun x => (starRingEnd ℂ) (f (θ x))

omit [Fintype X] [DecidableEq A] in
/-- **RTH.11**: the square-partition patching map `J_xv = (ψ_α(x)v_α)_α`
is a fibrewise isometry: it carries the patch-invariant line pairing of any
two compatible sections to the standard fibre pairing of the trivial
bundle, and cover data enter only through the partition identity. -/
theorem patching_isometry (U : A → Set X) (ψ : A → X → ℝ) (g : A → A → X → ℂ)
    (hpart : ∀ x, ∑ a, ψ a x ^ 2 = 1)
    (hψsupp : ∀ a x, x ∉ U a → ψ a x = 0)
    (hgunit : ∀ a b x, x ∈ U a → x ∈ U b → ‖g a b x‖ = 1)
    (v w : A → X → ℂ)
    (hv : ∀ a b x, x ∈ U a → x ∈ U b → v a x = g a b x * v b x)
    (hw : ∀ a b x, x ∈ U a → x ∈ U b → w a x = g a b x * w b x)
    (x : X) (a₀ : A) (hx : x ∈ U a₀) :
    ∑ a, (starRingEnd ℂ) (ψ a x * v a x) * (ψ a x * w a x)
      = (starRingEnd ℂ) (v a₀ x) * w a₀ x := by
  have hterm : ∀ a, (starRingEnd ℂ) (ψ a x * v a x) * (ψ a x * w a x)
      = ((ψ a x ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (v a₀ x) * w a₀ x) := by
    intro a
    by_cases ha : x ∈ U a
    · have hva := hv a a₀ x ha hx
      have hwa := hw a a₀ x ha hx
      have hgu := hgunit a a₀ x ha hx
      have hgg : (starRingEnd ℂ) (g a a₀ x) * g a a₀ x = 1 := by
        rw [Complex.conj_mul']
        rw [show ((‖g a a₀ x‖ : ℝ) : ℂ) ^ 2 = ((‖g a a₀ x‖ ^ 2 : ℝ) : ℂ) by
          push_cast
          ring]
        rw [hgu]
        norm_num
      rw [hva, hwa, map_mul, map_mul, Complex.conj_ofReal]
      push_cast
      linear_combination (((ψ a x : ℝ) : ℂ) * ((ψ a x : ℝ) : ℂ)
        * (starRingEnd ℂ) (v a₀ x) * w a₀ x) * hgg
    · rw [hψsupp a x ha]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_mul,
    ← Complex.ofReal_sum]
  rw [show ∑ a, (ψ a x ^ 2 : ℝ) = 1 from hpart x]
  rw [Complex.ofReal_one, one_mul]

/-- The reflected coherent amplitude `z_{K,b} = ∑Θ(b_α)K_{βα}b_β`
(RTH.12). -/
noncomputable def cohAmp (θ : X → X) (K : Matrix A A ℂ) (b : A → X → ℂ) :
    X → ℂ :=
  fun x => ∑ α, ∑ β, refl θ (b α) x * K β α * b β x

/-- The `γ`-filtered sector section `d_γ = ∑_α (K^{1/2})^*_{γα}b_α`. -/
noncomputable def filtSec {K : Matrix A A ℂ} (hK : K.PosSemidef)
    (b : A → X → ℂ) (γ : A) : X → ℂ :=
  fun y => ∑ α, (starRingEnd ℂ) (psdSqrt hK.1 γ α) * b α y

/-- **RTH.12 (reflected squares)**: for PSD `K` the coherent amplitude is
the sum of reflected squares of the filtered sections. -/
theorem cohAmp_eq_sum_sq (θ : X → X) {K : Matrix A A ℂ} (hK : K.PosSemidef)
    (b : A → X → ℂ) :
    cohAmp θ K b
      = fun x => ∑ γ, refl θ (filtSec hK b γ) x * filtSec hK b γ x := by
  funext x
  unfold cohAmp filtSec refl
  have hRH : (psdSqrt hK.1)ᴴ = psdSqrt hK.1 := (psdSqrt_posSemidef hK.1).1
  have hKexp : ∀ β α : A, K β α
      = ∑ γ, (starRingEnd ℂ) (psdSqrt hK.1 γ β) * psdSqrt hK.1 γ α := by
    intro β α
    have h1 : K = (psdSqrt hK.1)ᴴ * psdSqrt hK.1 := by
      rw [hRH]
      exact (psdSqrt_mul_self hK).symm
    have h2 := congrFun (congrFun h1 β) α
    refine h2.trans ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun γ _ => by
      rw [Matrix.conjTranspose_apply]
      rfl
  calc ∑ α, ∑ β, (starRingEnd ℂ) (b α (θ x)) * K β α * b β x
      = ∑ α, ∑ β, ∑ γ, psdSqrt hK.1 γ α * (starRingEnd ℂ) (b α (θ x))
          * ((starRingEnd ℂ) (psdSqrt hK.1 γ β) * b β x) := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [hKexp β α, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = ∑ γ, ∑ α, ∑ β, psdSqrt hK.1 γ α * (starRingEnd ℂ) (b α (θ x))
          * ((starRingEnd ℂ) (psdSqrt hK.1 γ β) * b β x) := by
        have hswap1 : ∀ α : A, (∑ β, ∑ γ, psdSqrt hK.1 γ α
              * (starRingEnd ℂ) (b α (θ x))
              * ((starRingEnd ℂ) (psdSqrt hK.1 γ β) * b β x))
            = ∑ γ, ∑ β, psdSqrt hK.1 γ α * (starRingEnd ℂ) (b α (θ x))
              * ((starRingEnd ℂ) (psdSqrt hK.1 γ β) * b β x) := fun α =>
          Finset.sum_comm
        rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hswap1 α]
        exact Finset.sum_comm
    _ = ∑ γ, (starRingEnd ℂ) (∑ α, (starRingEnd ℂ) (psdSqrt hK.1 γ α)
          * b α (θ x)) * ∑ β, (starRingEnd ℂ) (psdSqrt hK.1 γ β) * b β x := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [map_mul, Complex.conj_conj]

/-- **RTH.12 (reflection positivity)**: for every PSD sector-coherence
matrix the coherent amplitude is a reflection-positive reweighting of every
reflection-positive base state. -/
theorem cohAmp_reflection_positive (θ : X → X) {K : Matrix A A ℂ}
    (hK : K.PosSemidef) (b : A → X → ℂ) (ω : (X → ℂ) →ₗ[ℂ] ℂ)
    (hRP : ∀ f : X → ℂ, 0 ≤ ω (fun x => refl θ f x * f x)) :
    ∀ f : X → ℂ, 0 ≤ ω (fun x => refl θ f x * (cohAmp θ K b x * f x)) := by
  intro f
  have hfun : (fun x => refl θ f x * (cohAmp θ K b x * f x))
      = ∑ γ, fun x => refl θ (fun y => filtSec hK b γ y * f y) x
          * (filtSec hK b γ x * f x) := by
    funext x
    have hz := congrFun (cohAmp_eq_sum_sq θ hK b) x
    rw [Finset.sum_apply, hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    unfold refl
    beta_reduce
    rw [map_mul]
    ring
  rw [hfun, map_sum]
  exact Finset.sum_nonneg fun γ _ => hRP _

omit [Fintype X] [DecidableEq A] in
/-- **RTH.12 (basis independence)**: the coherent amplitude is invariant
under every unitary central sector frame change. -/
theorem cohAmp_basis_independent (θ : X → X) (K : Matrix A A ℂ)
    (b : A → X → ℂ) (lam : A → ℂ) (hlam : ∀ a, ‖lam a‖ = 1) :
    cohAmp θ (Matrix.of fun β α => lam β * K β α * (starRingEnd ℂ) (lam α))
        (fun a x => (lam a)⁻¹ * b a x)
      = cohAmp θ K b := by
  funext x
  unfold cohAmp refl
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hα : lam α ≠ 0 := by
    intro h
    have := hlam α
    rw [h, norm_zero] at this
    norm_num at this
  have hβ : lam β ≠ 0 := by
    intro h
    have := hlam β
    rw [h, norm_zero] at this
    norm_num at this
  have hαc : (starRingEnd ℂ) (lam α) ≠ 0 := by
    intro h
    apply hα
    have h2 := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_zero] at h2
  rw [Matrix.of_apply, map_mul, map_inv₀]
  field_simp [hαc]

/-- The base reflected sector Gram `S_b` (RTH.13). -/
noncomputable def reflGram (θ : X → X) (ω : (X → ℂ) →ₗ[ℂ] ℂ)
    (b : A → X → ℂ) : Matrix A A ℂ :=
  Matrix.of fun α β => ω (fun x => refl θ (b α) x * b β x)

/-- The reflected sector Gram of a reflection-positive state is PSD. -/
theorem reflGram_posSemidef (θ : X → X) (ω : (X → ℂ) →ₗ[ℂ] ℂ)
    (hRP : ∀ f : X → ℂ, 0 ≤ ω (fun x => refl θ f x * f x))
    (hsymm : ∀ f g : X → ℂ, ω (fun x => refl θ f x * g x)
      = (starRingEnd ℂ) (ω (fun x => refl θ g x * f x)))
    (b : A → X → ℂ) : (reflGram θ ω b).PosSemidef := by
  have hherm : (reflGram θ ω b).IsHermitian := by
    ext α β
    rw [Matrix.conjTranspose_apply]
    unfold reflGram
    rw [Matrix.of_apply, Matrix.of_apply, hsymm (b β) (b α),
      Complex.star_def, Complex.conj_conj]
  refine posSemidef_of_re_form hherm fun c => ?_
  · have hcomp : star c ⬝ᵥ ((reflGram θ ω b) *ᵥ c)
        = ∑ α, ∑ β, (starRingEnd ℂ) (c α) * c β
            * ω (fun x => refl θ (b α) x * b β x) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, reflGram,
        Matrix.of_apply]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Complex.star_def]
      ring
    have hlin : ∀ α β, (starRingEnd ℂ) (c α) * c β
        * ω (fun x => refl θ (b α) x * b β x)
        = ω (fun x => (starRingEnd ℂ) (c α) * c β
            * (refl θ (b α) x * b β x)) := by
      intro α β
      have h := ω.map_smul ((starRingEnd ℂ) (c α) * c β)
        (fun x => refl θ (b α) x * b β x)
      rw [smul_eq_mul] at h
      rw [← h]
      congr 1
    have hexpand : (fun x => refl θ (fun y => ∑ α, c α * b α y) x
          * ∑ β, c β * b β x)
        = ∑ α, ∑ β, fun x => (starRingEnd ℂ) (c α) * c β
            * (refl θ (b α) x * b β x) := by
      funext x
      simp only [Finset.sum_apply]
      unfold refl
      beta_reduce
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [map_mul]
      ring
    have hfold : ∀ α, ∑ β, ω (fun x => (starRingEnd ℂ) (c α) * c β
        * (refl θ (b α) x * b β x))
        = ω (∑ β, fun x => (starRingEnd ℂ) (c α) * c β
            * (refl θ (b α) x * b β x)) := fun α => (map_sum ω _ _).symm
    rw [hcomp, Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) =>
      Finset.sum_congr rfl fun β (_ : β ∈ Finset.univ) => hlin α β]
    rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hfold α,
      ← map_sum, ← hexpand]
    exact (Complex.le_def.mp (hRP _)).1

/-- **RTH.13 (partition value)**: the coherent partition value is the
half-carrier trace, `Z_{K,b} = ω(z_{K,b}) = Tr(K^{1/2}S_bK^{1/2})`. -/
theorem cohAmp_trace (θ : X → X) {K : Matrix A A ℂ} (hK : K.PosSemidef)
    (ω : (X → ℂ) →ₗ[ℂ] ℂ) (b : A → X → ℂ) :
    ω (cohAmp θ K b)
      = Matrix.trace (psdSqrt hK.1 * reflGram θ ω b * psdSqrt hK.1) := by
  have hcyc : Matrix.trace (psdSqrt hK.1 * reflGram θ ω b * psdSqrt hK.1)
      = Matrix.trace (reflGram θ ω b * (psdSqrt hK.1 * psdSqrt hK.1)) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [hcyc, psdSqrt_mul_self hK]
  have hfn : cohAmp θ K b
      = ∑ α, ∑ β, fun x => refl θ (b α) x * K β α * b β x := by
    funext x
    unfold cohAmp
    simp only [Finset.sum_apply]
  have hpull : ∀ α β, ω (fun x => refl θ (b α) x * K β α * b β x)
      = K β α * ω (fun x => refl θ (b α) x * b β x) := by
    intro α β
    have h := ω.map_smul (K β α) (fun x => refl θ (b α) x * b β x)
    rw [smul_eq_mul] at h
    rw [← h]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hinner : ∀ α, ω (∑ β, fun x => refl θ (b α) x * K β α * b β x)
      = ∑ β, K β α * ω (fun x => refl θ (b α) x * b β x) := by
    intro α
    rw [map_sum]
    exact Finset.sum_congr rfl fun β _ => hpull α β
  rw [hfn, map_sum]
  rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hinner α]
  unfold Matrix.trace Matrix.diag
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  unfold reflGram
  rw [Matrix.of_apply]
  ring

/-- The half-carrier operator `R = K^{1/2}S_bK^{1/2}` is PSD (RTH.13). -/
theorem halfCarrier_posSemidef {K : Matrix A A ℂ} (hK : K.PosSemidef)
    {Sb : Matrix A A ℂ} (hSb : Sb.PosSemidef) :
    (psdSqrt hK.1 * Sb * psdSqrt hK.1).PosSemidef := by
  have hRH : (psdSqrt hK.1)ᴴ = psdSqrt hK.1 := (psdSqrt_posSemidef hK.1).1
  have := hSb.mul_mul_conjTranspose_same (psdSqrt hK.1)
  rwa [hRH] at this

/-- **RTH.13 (minimum half-carrier)**: the dimensions of Gram
factorizations of a PSD matrix `R` attain their least value at `rank R`:
`dim ℋ^min_{K,b} = rank R`. -/
theorem halfCarrier_min_dim {R : Matrix A A ℂ} (hR : R.PosSemidef) :
    IsLeast {d : ℕ | ∃ V : Matrix (Fin d) A ℂ, Vᴴ * V = R} R.rank := by
  classical
  constructor
  · -- an explicit factorization with `rank R` rows from the spectral theorem
    set lam := hR.1.eigenvalues with hlam
    set W : Matrix A A ℂ := Matrix.diagonal
        (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))
      * (star (hR.1.eigenvectorUnitary : Matrix A A ℂ)) with hWdef
    have hWfact : Wᴴ * W = R := by
      rw [hWdef, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
      have hstar : (star (hR.1.eigenvectorUnitary : Matrix A A ℂ))ᴴ
          = (hR.1.eigenvectorUnitary : Matrix A A ℂ) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      rw [hstar]
      have hdiagstar : (star fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))
          = fun i => ((Real.sqrt (lam i) : ℝ) : ℂ) := by
        funext i
        rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
      rw [hdiagstar]
      calc (hR.1.eigenvectorUnitary : Matrix A A ℂ)
            * Matrix.diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))
            * (Matrix.diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))
              * star (hR.1.eigenvectorUnitary : Matrix A A ℂ))
          = (hR.1.eigenvectorUnitary : Matrix A A ℂ)
            * (Matrix.diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))
              * Matrix.diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)))
            * star (hR.1.eigenvectorUnitary : Matrix A A ℂ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R := by
            rw [Matrix.diagonal_mul_diagonal]
            have hdd : (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)
                * ((Real.sqrt (lam i) : ℝ) : ℂ))
                = RCLike.ofReal ∘ hR.1.eigenvalues := by
              funext i
              rw [← Complex.ofReal_mul,
                Real.mul_self_sqrt (hR.eigenvalues_nonneg i)]
              rfl
            rw [hdd]
            conv_rhs => rw [hR.1.spectral_theorem]
            rw [Unitary.conjStarAlgAut_apply]
    have hWzero : ∀ i, lam i = 0 → ∀ a, W i a = 0 := by
      intro i hi a
      rw [hWdef, Matrix.diagonal_mul, hi, Real.sqrt_zero, Complex.ofReal_zero,
        zero_mul]
    -- restrict to the nonzero-eigenvalue rows
    set V₀ : Matrix {i // lam i ≠ 0} A ℂ := Matrix.of fun i a => W i.1 a
      with hV₀def
    have hV₀fact : V₀ᴴ * V₀ = R := by
      rw [← hWfact]
      ext a b
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hsub : ∑ i : {i // lam i ≠ 0}, V₀ᴴ a i * V₀ i b
          = ∑ i ∈ Finset.univ.filter (fun i => lam i ≠ 0),
              (starRingEnd ℂ) (W i a) * W i b := by
        calc ∑ i : {i // lam i ≠ 0}, V₀ᴴ a i * V₀ i b
            = ∑ i : {i // lam i ≠ 0}, (starRingEnd ℂ) (W i.1 a) * W i.1 b := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Matrix.conjTranspose_apply, hV₀def, Matrix.of_apply,
                Matrix.of_apply, Complex.star_def]
          _ = ∑ i ∈ Finset.univ.filter (fun i => lam i ≠ 0),
              (starRingEnd ℂ) (W i a) * W i b :=
            (Finset.sum_subtype (Finset.univ.filter fun i => lam i ≠ 0)
              (fun i => by simp)
              (fun i => (starRingEnd ℂ) (W i a) * W i b)).symm
      rw [hsub]
      rw [Finset.sum_filter_of_ne]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply, Complex.star_def]
      · intro i _ hne
        by_contra hzero
        rw [hWzero i hzero a, map_zero, zero_mul] at hne
        exact hne rfl
    -- transport the row index to `Fin (rank R)`
    have hcard : Fintype.card {i // lam i ≠ 0} = R.rank :=
      (hR.1.rank_eq_card_non_zero_eigs).symm
    set e : Fin R.rank ≃ {i // lam i ≠ 0} :=
      (Fintype.equivFinOfCardEq hcard).symm with hedef
    refine ⟨Matrix.of fun j a => V₀ (e j) a, ?_⟩
    refine Eq.trans ?_ hV₀fact
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ j, (Matrix.of fun j a => V₀ (e j) a)ᴴ a j
          * (Matrix.of fun j a => V₀ (e j) a) j b
        = ∑ j, V₀ᴴ a (e j) * V₀ (e j) b := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
            Matrix.of_apply, Matrix.of_apply]
      _ = ∑ i, V₀ᴴ a i * V₀ i b :=
          Equiv.sum_comp e (fun i => V₀ᴴ a i * V₀ i b)
  · -- no factorization has fewer rows than the rank
    rintro d ⟨V, hV⟩
    calc R.rank = (Vᴴ * V).rank := by rw [hV]
      _ = V.rank := V.rank_conjTranspose_mul_self
      _ ≤ Fintype.card (Fin d) := V.rank_le_card_height
      _ = d := Fintype.card_fin d

/-- **RTH.13 (off-diagonal witness)**: on the two-sector card with unit
base Gram, the full coherence matrix yields the coherent half-carrier
`R = K` satisfying the pure-state equation, while its diagonal truncation
yields the incoherent mixture `R = I`, which violates it. -/
theorem offdiagonal_mixture_witness :
    ∃ K : Matrix (Fin 2) (Fin 2) ℂ, ∃ hK : K.PosSemidef,
      Matrix.diagonal (fun i => K i i) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      psdSqrt hK.1 * (1 : Matrix (Fin 2) (Fin 2) ℂ) * psdSqrt hK.1 = K ∧
      psdSqrt (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).1
          * (1 : Matrix (Fin 2) (Fin 2) ℂ)
          * psdSqrt (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).1
        = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      K * K = Matrix.trace K • K ∧
      ¬ ((1 : Matrix (Fin 2) (Fin 2) ℂ) * 1
          = Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) • 1) := by
  have hones : (Matrix.of fun _ _ => (1 : ℂ)
      : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
    refine posSemidef_of_re_form ?_ fun x => ?_
    · ext i j
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
        Complex.star_def, map_one]
    · have hform : star x ⬝ᵥ ((Matrix.of fun _ _ => (1 : ℂ)) *ᵥ x)
          = (starRingEnd ℂ) (x 0 + x 1) * (x 0 + x 1) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
          Fin.sum_univ_two, one_mul, Complex.star_def, map_add]
        ring
      rw [hform, Complex.conj_mul']
      rw [show ((‖x 0 + x 1‖ : ℝ) : ℂ) ^ 2 = ((‖x 0 + x 1‖ ^ 2 : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.ofReal_re]
      positivity
  refine ⟨Matrix.of fun _ _ => (1 : ℂ), hones, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal]
  · rw [Matrix.mul_one]
    exact psdSqrt_mul_self hones
  · rw [Matrix.mul_one]
    exact psdSqrt_mul_self
      (Matrix.PosSemidef.one : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef)
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have htr : Matrix.trace
        (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
      rw [Matrix.trace, Fin.sum_univ_two]
      norm_num
    rw [htr, Matrix.smul_apply]
    simp only [Matrix.of_apply, smul_eq_mul]
    norm_num
  · intro hcon
    have h00 := congrFun (congrFun hcon 0) 0
    rw [Matrix.one_mul, Matrix.trace_one, Matrix.smul_apply] at h00
    rw [Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    norm_num [Fintype.card_fin] at h00

/-- **RTH.14**: a global scalar half-frame exists exactly when the unitary
Čech cocycle is a coboundary `g_{αβ} = u_β⁻¹u_α`. -/
theorem global_frame_iff_coboundary (U : A → Set X) (g : A → A → X → ℂ) :
    (∃ t : A → X → ℂ, (∀ a x, x ∈ U a → ‖t a x‖ = 1) ∧
        ∀ a b x, x ∈ U a → x ∈ U b → t a x = g a b x * t b x)
      ↔ ∃ u : A → X → ℂ, (∀ a x, x ∈ U a → ‖u a x‖ = 1) ∧
          ∀ a b x, x ∈ U a → x ∈ U b → g a b x = (u b x)⁻¹ * u a x := by
  constructor
  · rintro ⟨t, htunit, htcompat⟩
    refine ⟨t, htunit, fun a b x ha hb => ?_⟩
    have hb0 : t b x ≠ 0 := by
      intro h
      have := htunit b x hb
      rw [h, norm_zero] at this
      norm_num at this
    rw [htcompat a b x ha hb]
    field_simp
  · rintro ⟨u, huunit, hucob⟩
    refine ⟨u, huunit, fun a b x ha hb => ?_⟩
    have hb0 : u b x ≠ 0 := by
      intro h
      have := huunit b x hb
      rw [h, norm_zero] at this
      norm_num at this
    rw [hucob a b x ha hb]
    field_simp

/-- **RTH.14 (Real compatibility)**: on the reflection-real branch the
reflected frame defect of a global unit frame is patch independent: the
Real structure descends to one global unit line datum. -/
theorem reflection_real_frame_defect (U : A → Set X) (θ : X → X)
    (g : A → A → X → ℂ) (hUθ : ∀ a x, x ∈ U a → θ x ∈ U a)
    (hgunit : ∀ a b x, x ∈ U a → x ∈ U b → ‖g a b x‖ = 1)
    (hgreal : ∀ a b x, x ∈ U a → x ∈ U b
      → (starRingEnd ℂ) (g a b (θ x)) = g a b x)
    (t : A → X → ℂ) (htunit : ∀ a x, x ∈ U a → ‖t a x‖ = 1)
    (htcompat : ∀ a b x, x ∈ U a → x ∈ U b → t a x = g a b x * t b x) :
    ∀ a b x, x ∈ U a → x ∈ U b →
      (starRingEnd ℂ) (t a (θ x)) * (t a x)⁻¹
        = (starRingEnd ℂ) (t b (θ x)) * (t b x)⁻¹ := by
  intro a b x ha hb
  have hgx0 : g a b x ≠ 0 := by
    intro h
    have := hgunit a b x ha hb
    rw [h, norm_zero] at this
    norm_num at this
  have htb0 : t b x ≠ 0 := by
    intro h
    have := htunit b x hb
    rw [h, norm_zero] at this
    norm_num at this
  have h1 : t a x = g a b x * t b x := htcompat a b x ha hb
  have h2 : t a (θ x) = g a b (θ x) * t b (θ x) :=
    htcompat a b (θ x) (hUθ a x ha) (hUθ b x hb)
  rw [h1, h2, map_mul, hgreal a b x ha hb, mul_inv]
  field_simp

/-- **RTH.15 (global patching)**: the multiplicative line one-form
`η = (ds/s)·a` patches globally on the discrete edge model. -/
theorem line_one_form_patches (U : A → Set X) (g : A → A → X → ℂ)
    (hgunit : ∀ a b x, x ∈ U a → x ∈ U b → ‖g a b x‖ = 1)
    (s : A → X → ℂ) (hs : ∀ a x, x ∈ U a → s a x ≠ 0)
    (hscompat : ∀ a b x, x ∈ U a → x ∈ U b → s a x = g a b x * s b x)
    (conn : A → A → X → X → ℂ)
    (hconn : ∀ a b x y, x ∈ U a → x ∈ U b → y ∈ U a → y ∈ U b →
      conn a a x y * g a b y = conn b b x y * g a b x) :
    ∀ a b x y, x ∈ U a → x ∈ U b → y ∈ U a → y ∈ U b →
      s a y / s a x * conn a a x y = s b y / s b x * conn b b x y := by
  intro a b x y hxa hxb hya hyb
  have hgx0 : g a b x ≠ 0 := by
    intro h
    have := hgunit a b x hxa hxb
    rw [h, norm_zero] at this
    norm_num at this
  have hgy0 : g a b y ≠ 0 := by
    intro h
    have := hgunit a b y hya hyb
    rw [h, norm_zero] at this
    norm_num at this
  have hsxb : s b x ≠ 0 := hs b x hxb
  have hsyb : s b y ≠ 0 := hs b y hyb
  rw [hscompat a b x hxa hxb, hscompat a b y hya hyb]
  have hc := hconn a b x y hxa hxb hya hyb
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (mul_ne_zero hgx0 hsxb) hsxb]
  linear_combination (s b y * s b x) * hc

/-- **RTH.15 (the modulus determines `2Reη`)**: the modulus of the patched
line one-form is determined by the section and connection moduli. -/
theorem line_one_form_modulus (s : A → X → ℂ) (conn : A → A → X → X → ℂ)
    (a : A) (x y : X) :
    ‖s a y / s a x * conn a a x y‖
      = ‖s a y‖ / ‖s a x‖ * ‖conn a a x y‖ := by
  rw [norm_mul, norm_div]

/-- **RTH.15 (the phase is independent line data)**: two line data with
identical moduli can carry different one-form phases. -/
theorem line_one_form_phase_witness :
    ∃ s s' : Unit → Bool → ℂ, ∃ conn : Unit → Unit → Bool → Bool → ℂ,
      (∀ a x, ‖s' a x‖ = ‖s a x‖) ∧
      (∀ a x y, ‖conn a a x y‖ = 1) ∧
      s () true / s () false * conn () () false true
        ≠ s' () true / s' () false * conn () () false true := by
  refine ⟨fun _ _ => 1, fun _ x => cond x Complex.I 1,
    fun _ _ _ _ => 1, ?_, ?_, ?_⟩
  · intro a x
    rcases x with _ | _
    · norm_num
    · norm_num [Complex.norm_I]
  · intro a x y
    norm_num
  · intro hcon
    norm_num at hcon
    have him := congrArg Complex.im hcon
    rw [Complex.one_im, Complex.I_im] at him
    norm_num at him

end RPESMLine

end SectorPatchedLine

/-! ### Cofinal reserve–geometry separation -/

section SourceMetricCofinal

open MeasureTheory
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open NCG.MetricTransport NCG.SourceAction NCG.LowIslandRM
open scoped Matrix.Norms.Operator

namespace MetricCofinal

variable {h : Type*} [Fintype h] [DecidableEq h]

/-! #### Continuous-linear-map calculus for horizon integrals -/

/-- Matrix-to-vector application against a fixed vector, as a continuous
linear map on the comparison carrier. -/
noncomputable def mulVecCLM (x : h → ℂ) : Matrix h h ℂ →L[ℂ] (h → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ x
      map_add' := fun A B => Matrix.add_mulVec A B x
      map_smul' := fun c A => by
        simp [Matrix.smul_mulVec] }

omit [DecidableEq h] in
/-- Application of the matrix-to-vector map. -/
theorem mulVecCLM_apply (x : h → ℂ) (A : Matrix h h ℂ) :
    mulVecCLM x A = A *ᵥ x := rfl

/-- Pairing against a fixed vector as a continuous linear map. -/
noncomputable def dotCLM (x : h → ℂ) : (h → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => star x ⬝ᵥ v
      map_add' := fun a b => dotProduct_add _ a b
      map_smul' := fun c v => by
        simp [dotProduct_smul] }

omit [DecidableEq h] in
/-- Application of the pairing map. -/
theorem dotCLM_apply (x v : h → ℂ) : dotCLM x v = star x ⬝ᵥ v := rfl

/-- Conjugate transposition as a real-linear continuous map. -/
noncomputable def conjTransposeCLM :
    Matrix h h ℂ →L[ℝ] Matrix h h ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by
        ext i j
        simp [Matrix.conjTranspose_apply] }

omit [DecidableEq h] in
/-- Application of the conjugate-transposition map. -/
theorem conjTransposeCLM_apply (A : Matrix h h ℂ) :
    conjTransposeCLM A = Aᴴ := rfl

/-- Continuity of the horizon integrand. -/
theorem continuous_horizon_integrand (Hm P : Matrix h h ℂ) :
    Continuous fun t => clock Hm t * P * clock Hm t :=
  ((continuous_clock Hm).matrix_mul continuous_const).matrix_mul
    (continuous_clock Hm)

/-- Continuity of the clock orbit of a vector. -/
theorem continuous_clock_orbit (Hm P : Matrix h h ℂ) (x : h → ℂ) :
    Continuous fun t => clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)) :=
  (continuous_clock Hm).matrix_mulVec
    (continuous_const.matrix_mulVec
      ((continuous_clock Hm).matrix_mulVec continuous_const))

/-- The horizon Gramian applied to a vector is the interval integral of the
clock orbit. -/
theorem horizonGramian_mulVec (Hm P : Matrix h h ℂ) (T : ℝ) (x : h → ℂ) :
    horizonGramian Hm P T *ᵥ x
      = ∫ t in (0 : ℝ)..T, clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)) := by
  have hI := (continuous_horizon_integrand Hm P).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  have hcomm := (mulVecCLM x).intervalIntegral_comp_comm hI
  unfold horizonGramian
  calc (∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t) *ᵥ x
      = mulVecCLM x (∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t) := rfl
    _ = ∫ t in (0 : ℝ)..T, mulVecCLM x (clock Hm t * P * clock Hm t) :=
        hcomm.symm
    _ = ∫ t in (0 : ℝ)..T, clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [mulVecCLM_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The quadratic form of the horizon Gramian is the interval integral of
the clock-orbit forms. -/
theorem dot_horizonGramian (Hm P : Matrix h h ℂ) (T : ℝ) (x : h → ℂ) :
    star x ⬝ᵥ (horizonGramian Hm P T *ᵥ x)
      = ∫ t in (0 : ℝ)..T,
          star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))) := by
  rw [horizonGramian_mulVec]
  have hI := (continuous_clock_orbit Hm P x).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  have hcomm := (dotCLM x).intervalIntegral_comp_comm hI
  calc star x ⬝ᵥ (∫ t in (0 : ℝ)..T, clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))
      = dotCLM x (∫ t in (0 : ℝ)..T,
          clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))) := rfl
    _ = ∫ t in (0 : ℝ)..T,
          dotCLM x (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))) := hcomm.symm
    _ = ∫ t in (0 : ℝ)..T,
          star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))) := rfl

/-- The horizon Gramian of Hermitian data is Hermitian. -/
theorem horizonGramian_isHermitian {Hm P : Matrix h h ℂ}
    (hH : Hm.IsHermitian) (hP : P.IsHermitian) (T : ℝ) :
    (horizonGramian Hm P T).IsHermitian := by
  have hI := (continuous_horizon_integrand Hm P).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  have hcomm := conjTransposeCLM.intervalIntegral_comp_comm hI
  unfold Matrix.IsHermitian horizonGramian
  calc (∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t)ᴴ
      = conjTransposeCLM (∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t) :=
        rfl
    _ = ∫ t in (0 : ℝ)..T, conjTransposeCLM (clock Hm t * P * clock Hm t) :=
        hcomm.symm
    _ = ∫ t in (0 : ℝ)..T, clock Hm t * P * clock Hm t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [conjTransposeCLM_apply, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, clock_conjTranspose hH, hP.eq,
          Matrix.mul_assoc]

/-- The horizon Gramian of a PSD entrance projection is PSD. -/
theorem horizonGramian_posSemidef {Hm P : Matrix h h ℂ}
    (hH : Hm.IsHermitian) (hP : P.PosSemidef) {T : ℝ} (hT : 0 ≤ T) :
    (horizonGramian Hm P T).PosSemidef := by
  refine posSemidef_of_re_form (horizonGramian_isHermitian hH hP.1 T)
    fun x => ?_
  rw [dot_horizonGramian]
  have hI : IntervalIntegrable
      (fun t => star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))))
      MeasureTheory.volume 0 T := by
    have hc : Continuous
        (fun t => star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))) :=
      (dotCLM x).continuous.comp (continuous_clock_orbit Hm P x)
    exact hc.intervalIntegrable 0 T
  have hre := Complex.reCLM.intervalIntegral_comp_comm hI
  have hre' : (∫ t in (0 : ℝ)..T,
        star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re
      = ∫ t in (0 : ℝ)..T,
          (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re := by
    simpa using hre.symm
  rw [hre']
  refine intervalIntegral.integral_nonneg hT fun t _ => ?_
  have hpsd : (clock Hm t * P * clock Hm t).PosSemidef := by
    have := hP.mul_mul_conjTranspose_same (clock Hm t)
    rwa [clock_conjTranspose hH] at this
  have hform := re_form_nonneg hpsd x
  rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hform

/-! #### The scalar vanishing lemma -/

/-- A continuous nonnegative function with vanishing horizon integral
vanishes on the horizon. -/
theorem eq_zero_of_integral_zero {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hc : Continuous φ) (hnn : ∀ t, 0 ≤ φ t)
    (hzero : ∫ t in (0 : ℝ)..T, φ t = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, φ t = 0 := by
  intro t0 ht0
  by_contra hne
  have hpos : 0 < φ t0 := lt_of_le_of_ne (hnn t0) (Ne.symm hne)
  have hev : ∀ᶠ t in 𝓝 t0, φ t0 / 2 < φ t :=
    (hc.tendsto t0).eventually (eventually_gt_nhds (by linarith))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  set a := max 0 (t0 - δ / 2) with ha
  set b := min T (t0 + δ / 2) with hb
  have ha0 : 0 ≤ a := le_max_left _ _
  have hbT : b ≤ T := min_le_left _ _
  have ha_le : a ≤ t0 := max_le ht0.1 (by linarith)
  have hb_ge : t0 ≤ b := le_min ht0.2 (by linarith)
  have hab : a < b := by
    rcases lt_or_eq_of_le ha_le with hlt | heq
    · exact lt_of_lt_of_le hlt hb_ge
    · have h0 : t0 = 0 := by
        by_contra h0ne
        have ht0pos : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm h0ne)
        have : a < t0 := max_lt ht0pos (by linarith)
        linarith [heq ▸ this]
      have haz : a = 0 := by rw [heq, h0]
      have hbpos : 0 < b := lt_min hT (by rw [h0]; linarith)
      rw [haz]
      exact hbpos
  have hbound : ∀ t ∈ Set.Icc a b, φ t0 / 2 ≤ φ t := by
    intro t ht
    refine le_of_lt (hδ ?_)
    rw [Real.dist_eq, abs_sub_lt_iff]
    have h1 : t0 - δ / 2 ≤ a := le_max_right _ _
    have h2 : b ≤ t0 + δ / 2 := min_le_right _ _
    constructor <;> [skip; skip] <;>
      · obtain ⟨hta, htb⟩ := ht
        linarith
  have hmid : (b - a) * (φ t0 / 2) ≤ ∫ t in a..b, φ t := by
    have h1 := intervalIntegral.integral_mono_on hab.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := φ t0 / 2))
      (hc.intervalIntegrable a b) hbound
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h1
  have h0a : 0 ≤ ∫ t in (0 : ℝ)..a, φ t :=
    intervalIntegral.integral_nonneg ha0 fun t _ => hnn t
  have hbT' : 0 ≤ ∫ t in b..T, φ t :=
    intervalIntegral.integral_nonneg hbT fun t _ => hnn t
  have hsplit1 : (∫ t in (0 : ℝ)..a, φ t) + ∫ t in a..b, φ t
      = ∫ t in (0 : ℝ)..b, φ t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  have hsplit2 : (∫ t in (0 : ℝ)..b, φ t) + ∫ t in b..T, φ t
      = ∫ t in (0 : ℝ)..T, φ t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 b) (hc.intervalIntegrable b T)
  have hquarter : 0 < (b - a) * (φ t0 / 2) := by
    have : 0 < b - a := by linarith
    positivity
  linarith

/-! #### Analytic continuation of the clock orbit -/

/-- The clock curve is real-analytic. -/
theorem clock_analyticOnNhd (Hm : Matrix h h ℂ) :
    AnalyticOnNhd ℝ (fun t : ℝ => clock Hm t) Set.univ := by
  have h1 : AnalyticOnNhd ℝ (fun t : ℝ => (-t) • Hm) Set.univ := by
    have hfn : (fun t : ℝ => (-t) • Hm)
        = fun t : ℝ => ((ContinuousLinearMap.id ℝ ℝ).smulRight (-Hm)) t := by
      funext t
      simp [neg_smul, smul_neg]
    rw [hfn]
    exact fun x _ => ((ContinuousLinearMap.id ℝ ℝ).smulRight (-Hm)).analyticAt x
  have h2 : AnalyticOnNhd ℝ
      (NormedSpace.exp : Matrix h h ℂ → Matrix h h ℂ) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  have h3 := h2.comp h1 (Set.mapsTo_univ _ _)
  exact h3

/-- The projected clock orbit of a vector is real-analytic. -/
theorem clock_orbit_analyticOnNhd (Hm P : Matrix h h ℂ) (x : h → ℂ) :
    AnalyticOnNhd ℝ (fun t : ℝ => P *ᵥ (clock Hm t *ᵥ x)) Set.univ := by
  have h1 := clock_analyticOnNhd Hm
  set L : Matrix h h ℂ →ₗ[ℝ] (h → ℂ) :=
    { toFun := fun A => P *ᵥ (A *ᵥ x)
      map_add' := fun A B => by
        rw [Matrix.add_mulVec, Matrix.mulVec_add]
      map_smul' := fun c A => by
        simp [Matrix.smul_mulVec, Matrix.mulVec_smul] } with hL
  have h2 : AnalyticOnNhd ℝ
      (fun A : Matrix h h ℂ => P *ᵥ (A *ᵥ x)) Set.univ := by
    intro A _
    exact (LinearMap.toContinuousLinearMap L).analyticAt A
  have h3 := h2.comp h1 (Set.mapsTo_univ _ _)
  exact h3

/-- A projected clock orbit vanishing on the horizon vanishes for all
times: the identity theorem for the real-analytic orbit. -/
theorem clock_orbit_vanish_extend {Hm P : Matrix h h ℂ} {x : h → ℂ}
    {T : ℝ} (hT : 0 < T)
    (hzero : ∀ t ∈ Set.Icc (0 : ℝ) T, P *ᵥ (clock Hm t *ᵥ x) = 0) :
    ∀ t : ℝ, P *ᵥ (clock Hm t *ᵥ x) = 0 := by
  have hana := clock_orbit_analyticOnNhd Hm P x
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℝ), P *ᵥ (clock Hm t *ᵥ x) = 0 := by
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), P *ᵥ (clock Hm t *ᵥ x) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      exact hzero t ⟨ht.1.le, ht.2.le⟩
    refine hev.frequently.filter_mono (nhdsWithin_mono 0 fun t ht => ?_)
    exact Set.mem_compl_singleton_iff.mpr (ne_of_gt ht)
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ (0 : ℝ)) hfreq
  intro t
  simpa using heq (Set.mem_univ t)

/-! #### The kernel of the horizon Gramian -/

/-- **Kernel characterization**: a vector is annihilated by the horizon
Gramian exactly when its projected clock orbit vanishes for all
nonnegative times. -/
theorem horizonGramian_mulVec_eq_zero_iff {Hm P : Matrix h h ℂ}
    (hH : Hm.IsHermitian) (hP : P.IsHermitian) (hidem : P * P = P)
    {T : ℝ} (hT : 0 < T) (x : h → ℂ) :
    horizonGramian Hm P T *ᵥ x = 0
      ↔ ∀ t : ℝ, 0 ≤ t → P *ᵥ (clock Hm t *ᵥ x) = 0 := by
  constructor
  · intro hx
    have hφ_eq : ∀ t,
        (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re
          = ∑ i, ‖(P *ᵥ (clock Hm t *ᵥ x)) i‖ ^ 2 := by
      intro t
      have h1 : star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))
          = star (clock Hm t *ᵥ x) ⬝ᵥ (P *ᵥ (clock Hm t *ᵥ x)) := by
        rw [adjoint_dot, clock_conjTranspose hH]
      rw [h1, proj_dot hP hidem, self_dot_re]
    have hφ_nn : ∀ t,
        0 ≤ (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re := by
      intro t
      rw [hφ_eq]
      positivity
    have hφ_cont : Continuous
        fun t => (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re :=
      Complex.continuous_re.comp
        ((dotCLM x).continuous.comp (continuous_clock_orbit Hm P x))
    have hint : ∫ t in (0 : ℝ)..T,
        (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re = 0 := by
      have hd := dot_horizonGramian Hm P T x
      rw [hx, dotProduct_zero] at hd
      have hI : IntervalIntegrable
          (fun t => star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x))))
          MeasureTheory.volume 0 T :=
        ((dotCLM x).continuous.comp
          (continuous_clock_orbit Hm P x)).intervalIntegrable 0 T
      have hre := Complex.reCLM.intervalIntegral_comp_comm hI
      have hre' : (∫ t in (0 : ℝ)..T,
            star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re
          = ∫ t in (0 : ℝ)..T,
              (star x ⬝ᵥ (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))).re := by
        simpa using hre.symm
      rw [← hre', ← hd, Complex.zero_re]
    have hIcc := eq_zero_of_integral_zero hT hφ_cont hφ_nn hint
    have hvan : ∀ t ∈ Set.Icc (0 : ℝ) T, P *ᵥ (clock Hm t *ᵥ x) = 0 := by
      intro t ht
      have h0 := hIcc t ht
      rw [hφ_eq] at h0
      funext i
      have hterm : ‖(P *ᵥ (clock Hm t *ᵥ x)) i‖ ^ 2 = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => by positivity)).mp h0 i
          (Finset.mem_univ i)
        exact this
      have := (pow_eq_zero_iff two_ne_zero).mp hterm
      rw [norm_eq_zero] at this
      simpa using this
    exact fun t _ => clock_orbit_vanish_extend hT hvan t
  · intro hvan
    rw [horizonGramian_mulVec]
    have hzero : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)) = (0 : h → ℂ) := by
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      rw [hvan t ht.1, Matrix.mulVec_zero]
    calc (∫ t in (0 : ℝ)..T, clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ x)))
        = ∫ _ in (0 : ℝ)..T, (0 : h → ℂ) :=
          intervalIntegral.integral_congr hzero
      _ = 0 := intervalIntegral.integral_zero

/-! #### The semigroup-cyclic carrier and its projection -/

/-- The semigroup-cyclic source carrier
`span{e^{-tH} Ran P : t ≥ 0}` (the closure is automatic on the finite
comparison carrier). -/
def cyclicCarrier (Hm P : Matrix h h ℂ) : Submodule ℂ (h → ℂ) :=
  Submodule.span ℂ {y | ∃ t : ℝ, 0 ≤ t ∧ ∃ v, y = clock Hm t *ᵥ (P *ᵥ v)}

/-- The dynamic projection `P_H^{P_B}`: the support projection of the
horizon Gramian. -/
noncomputable def dynProj {Hm P : Matrix h h ℂ} (hH : Hm.IsHermitian)
    (hP : P.IsHermitian) (T : ℝ) : Matrix h h ℂ :=
  supportProj (horizonGramian_isHermitian hH hP T)

omit [DecidableEq h] in
/-- A Hermitian idempotent is PSD. -/
theorem posSemidef_of_hermitian_idem {P : Matrix h h ℂ}
    (hP : P.IsHermitian) (hidem : P * P = P) : P.PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hidem] at this

/-- **The dynamic projection is the orthogonal projection onto the
semigroup-cyclic carrier**: it is Hermitian, idempotent, and fixes exactly
the carrier. -/
theorem dynProj_char {Hm P : Matrix h h ℂ} (hH : Hm.IsHermitian)
    (hP : P.IsHermitian) (hidem : P * P = P) {T : ℝ} (hT : 0 < T) :
    (dynProj hH hP T).IsHermitian ∧
      dynProj hH hP T * dynProj hH hP T = dynProj hH hP T ∧
      ∀ x : h → ℂ, dynProj hH hP T *ᵥ x = x ↔ x ∈ cyclicCarrier Hm P := by
  have hPsd : P.PosSemidef := posSemidef_of_hermitian_idem hP hidem
  have hW : (horizonGramian Hm P T).PosSemidef :=
    horizonGramian_posSemidef hH hPsd hT.le
  have hproofirr : dynProj hH hP T = supportProj hW.1 := rfl
  refine ⟨(supportProj_posSemidef _).1, supportProj_idem _, fun x => ?_⟩
  constructor
  · -- fixed vectors lie in the Gramian range, which lands in the carrier
    intro hfix
    have hxw : x = horizonGramian Hm P T
        *ᵥ (pinv (horizonGramian_isHermitian hH hP T) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, SourceAction.mul_pinv_eq_supportProj]
      exact hfix.symm
    rw [hxw, horizonGramian_mulVec]
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl (cyclicCarrier Hm P)
    set π : (h → ℂ) →L[ℂ] q :=
      LinearMap.toContinuousLinearMap
        (Submodule.projectionOnto q (cyclicCarrier Hm P) hq.symm) with hπ
    have hker : ∀ y : h → ℂ, π y = 0 ↔ y ∈ cyclicCarrier Hm P := by
      intro y
      have hk := Submodule.ker_projectionOnto hq.symm
      constructor
      · intro h0
        have : y ∈ LinearMap.ker
            (Submodule.projectionOnto q (cyclicCarrier Hm P) hq.symm) :=
          LinearMap.mem_ker.mpr h0
        rwa [hk] at this
      · intro hmem
        have : y ∈ LinearMap.ker
            (Submodule.projectionOnto q (cyclicCarrier Hm P) hq.symm) := by
          rw [hk]
          exact hmem
        exact LinearMap.mem_ker.mp this
    refine (hker _).mp ?_
    set w := pinv (horizonGramian_isHermitian hH hP T) *ᵥ x with hwdef
    have hI := (continuous_clock_orbit Hm P w).intervalIntegrable
      (μ := MeasureTheory.volume) 0 T
    have hcomm := π.intervalIntegral_comp_comm hI
    rw [← hcomm]
    have hzero : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        π (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ w))) = (0 : q) := by
      intro t ht
      rw [Set.uIcc_of_le hT.le] at ht
      refine (hker _).mpr (Submodule.subset_span ?_)
      exact ⟨t, ht.1, clock Hm t *ᵥ w, rfl⟩
    calc (∫ t in (0 : ℝ)..T, π (clock Hm t *ᵥ (P *ᵥ (clock Hm t *ᵥ w))))
        = ∫ _ in (0 : ℝ)..T, (0 : q) :=
          intervalIntegral.integral_congr hzero
      _ = 0 := intervalIntegral.integral_zero
  · -- the fixed-point set contains the carrier generators
    intro hmem
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro w ⟨t, htnn, v, rfl⟩
      obtain ⟨y, hydef⟩ : ∃ y, clock Hm t *ᵥ (P *ᵥ v) = y := ⟨_, rfl⟩
      rw [hydef]
      have hWsupp : horizonGramian Hm P T *ᵥ (dynProj hH hP T *ᵥ y)
          = horizonGramian Hm P T *ᵥ y := by
        rw [Matrix.mulVec_mulVec, hproofirr, mul_supportProj hW]
      have hWz : horizonGramian Hm P T *ᵥ (y - dynProj hH hP T *ᵥ y) = 0 := by
        rw [Matrix.mulVec_sub, hWsupp, sub_self]
      have horb := (horizonGramian_mulVec_eq_zero_iff hH hP hidem hT
        (y - dynProj hH hP T *ᵥ y)).mp hWz
      have hz_y : star (y - dynProj hH hP T *ᵥ y) ⬝ᵥ y = 0 := by
        nth_rewrite 3 [← hydef]
        rw [adjoint_dot, clock_conjTranspose hH, adjoint_dot, hP.eq,
          horb t htnn]
        simp
      have hsupp_z : dynProj hH hP T *ᵥ (y - dynProj hH hP T *ᵥ y) = 0 := by
        have h1 : dynProj hH hP T *ᵥ (dynProj hH hP T *ᵥ y)
            = dynProj hH hP T *ᵥ y := by
          rw [Matrix.mulVec_mulVec, hproofirr, supportProj_idem]
        rw [Matrix.mulVec_sub, h1, sub_self]
      have hz_supp : star (y - dynProj hH hP T *ᵥ y)
          ⬝ᵥ (dynProj hH hP T *ᵥ y) = 0 := by
        rw [adjoint_dot, hproofirr, (supportProj_posSemidef hW.1).1.eq,
          ← hproofirr, hsupp_z]
        simp
      have hzz : star (y - dynProj hH hP T *ᵥ y)
          ⬝ᵥ (y - dynProj hH hP T *ᵥ y) = 0 := by
        rw [dotProduct_sub, hz_y, hz_supp, sub_zero]
      have hz0 : y - dynProj hH hP T *ᵥ y = 0 := by
        by_contra hzne
        have := self_dot_pos hzne
        rw [hzz] at this
        simp at this
      have := sub_eq_zero.mp hz0
      exact this.symm
    · rw [Matrix.mulVec_zero]
    · intro a b _ _ ha hb
      rw [Matrix.mulVec_add, ha, hb]
    · intro c a _ ha
      rw [Matrix.mulVec_smul, ha]

/-! #### Convergence calculus on the comparison carrier -/

set_option maxHeartbeats 2000000 in
-- unfolding the composed matrix product against the direct one crosses the
-- generic-index multiplication instance; the default budget is too small
/-- Products of convergent matrix families converge. -/
theorem tendsto_matrix_mul {α m n p : Type*} [Fintype n] {l : Filter α}
    {A : α → Matrix m n ℂ} {B : α → Matrix n p ℂ} {Al : Matrix m n ℂ}
    {Bl : Matrix n p ℂ} (hA : Tendsto A l (𝓝 Al))
    (hB : Tendsto B l (𝓝 Bl)) :
    Tendsto (fun s => A s * B s) l (𝓝 (Al * Bl)) := by
  have hc : Continuous fun q : Matrix m n ℂ × Matrix n p ℂ => q.1 * q.2 :=
    continuous_fst.matrix_mul continuous_snd
  exact Filter.Tendsto.congr (fun _ => rfl)
    ((hc.tendsto (Al, Bl)).comp (hA.prodMk_nhds hB))

/-- The uniform clock bound over the compact clock chart of a convergent
family of generators. -/
theorem clock_uniform_bound {T : ℝ} {Hs : ℕ → Matrix h h ℂ}
    {Hl : Matrix h h ℂ} (hH : Tendsto Hs atTop (𝓝 Hl)) :
    ∃ C : ℝ, ∀ t ∈ Set.uIcc (0 : ℝ) T, ∀ n, ‖clock (Hs n) t‖ ≤ C := by
  have hjoint : Continuous fun p : ℝ × Matrix h h ℂ =>
      ‖NormedSpace.exp ((-p.1) • p.2)‖ :=
    (NormedSpace.exp_continuous.comp
      ((continuous_fst.neg).smul continuous_snd)).norm
  have hK : IsCompact ((Set.uIcc (0 : ℝ) T) ×ˢ insert Hl (Set.range Hs)) :=
    isCompact_uIcc.prod hH.isCompact_insert_range
  obtain ⟨C, hC⟩ := hK.bddAbove_image hjoint.continuousOn
  have hCb : ∀ t ∈ Set.uIcc (0 : ℝ) T, ∀ A ∈ insert Hl (Set.range Hs),
      (fun p : ℝ × Matrix h h ℂ => ‖NormedSpace.exp ((-p.1) • p.2)‖) (t, A)
        ≤ C := by
    intro t ht A hA
    exact hC (Set.mem_image_of_mem _ (Set.mk_mem_prod ht hA))
  exact ⟨C, fun t ht n => hCb t ht (Hs n) (Set.mem_insert_of_mem _ ⟨n, rfl⟩)⟩

set_option maxHeartbeats 1000000 in
-- the dominated-convergence unification crosses the scoped operator-norm
-- and Pi topologies; the default budget is too small
/-- **SMET.27 (kernel form)**: the normalized horizon Gramians converge on
the comparison carrier whenever the clocks and the entrance projections
converge; dominated convergence over the horizon window. -/
theorem horizonGramian_tendsto {T : ℝ} {Hs Ps : ℕ → Matrix h h ℂ}
    {Hl Pl : Matrix h h ℂ}
    (hH : Tendsto Hs atTop (𝓝 Hl)) (hP : Tendsto Ps atTop (𝓝 Pl)) :
    Tendsto (fun n => horizonGramian (Hs n) (Ps n) T) atTop
      (𝓝 (horizonGramian Hl Pl T)) := by
  obtain ⟨C, hCb⟩ := clock_uniform_bound (T := T) hH
  obtain ⟨CP, hCP⟩ := (hP.norm).bddAbove_range
  have hCPb : ∀ n, ‖Ps n‖ ≤ CP := fun n => hCP ⟨n, rfl⟩
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix h h ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (h → h → ℂ))
  unfold horizonGramian
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun n t => clock (Hs n) t * Ps n * clock (Hs n) t)
    (f := fun t => clock Hl t * Pl * clock Hl t)
    (fun _ => C * CP * C) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun n =>
      (continuous_horizon_integrand (Hs n) (Ps n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun n => ?_
    refine MeasureTheory.ae_of_all _ fun t ht => ?_
    have ht' : t ∈ Set.uIcc (0 : ℝ) T := Set.uIoc_subset_uIcc ht
    have h1 : ‖clock (Hs n) t‖ ≤ C := hCb t ht' n
    have h2 := hCPb n
    calc ‖clock (Hs n) t * Ps n * clock (Hs n) t‖
        ≤ ‖clock (Hs n) t * Ps n‖ * ‖clock (Hs n) t‖ := norm_mul_le _ _
      _ ≤ ‖clock (Hs n) t‖ * ‖Ps n‖ * ‖clock (Hs n) t‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ C * CP * C := by
          have h3 : (0 : ℝ) ≤ ‖clock (Hs n) t‖ := norm_nonneg _
          have h4 : (0 : ℝ) ≤ ‖Ps n‖ := norm_nonneg _
          have hC0 : (0 : ℝ) ≤ C := le_trans h3 h1
          have hCP0 : (0 : ℝ) ≤ CP := le_trans h4 h2
          have h5 : ‖clock (Hs n) t‖ * ‖Ps n‖ ≤ C * CP :=
            mul_le_mul h1 h2 h4 hC0
          exact mul_le_mul h5 h1 h3 (mul_nonneg hC0 hCP0)
  · exact intervalIntegrable_const
  · refine MeasureTheory.ae_of_all _ fun t _ => ?_
    have hclk : Tendsto (fun n => clock (Hs n) t) atTop (𝓝 (clock Hl t)) :=
      (NormedSpace.exp_continuous.tendsto _).comp (hH.const_smul (-t))
    exact tendsto_matrix_mul (tendsto_matrix_mul hclk hP) hclk

/-- Matrix inversion is continuous along families converging to a matrix
with nonvanishing determinant. -/
theorem tendsto_matrix_inv {A : ℕ → Matrix h h ℂ} {Al : Matrix h h ℂ}
    (hA : Tendsto A atTop (𝓝 Al)) (hdet : Al.det ≠ 0) :
    Tendsto (fun n => (A n)⁻¹) atTop (𝓝 Al⁻¹) := by
  have hdetc : Tendsto (fun n => (A n).det) atTop (𝓝 Al.det) :=
    ((continuous_id.matrix_det).tendsto Al).comp hA
  have hadjc : Tendsto (fun n => (A n).adjugate) atTop (𝓝 Al.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto Al).comp hA
  have hfun : ∀ B : Matrix h h ℂ, B⁻¹ = B.det⁻¹ • B.adjugate := by
    intro B
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hfun]
  exact (hdetc.inv₀ hdet).smul hadjc

/-- The Tikhonov contraction of a PSD Gramian is the spectral function
`λ ↦ λ/(λ+δ)`, and the regularized Gramian is nonsingular. -/
theorem tikhonov_spectral {W : Matrix h h ℂ} (hW : W.PosSemidef) {δ : ℝ}
    (hδ : 0 < δ) :
    (W + (δ : ℂ) • 1).det ≠ 0 ∧
      W * (W + (δ : ℂ) • 1)⁻¹
        = spectralFunction hW.1 (fun l => l / (l + δ)) := by
  have hsum : spectralFunction hW.1 (fun l => l + δ) = W + (δ : ℂ) • 1 := by
    have h1 : spectralFunction hW.1 (fun l => l + δ)
        = spectralFunction hW.1 id + spectralFunction hW.1 (fun _ => δ) :=
      spectralFunction_add hW.1 id (fun _ => δ)
    rw [h1, spectralFunction_id, spectralFunction_const]
  have hne : ∀ i, hW.1.eigenvalues i + δ ≠ 0 := fun i => by
    have := hW.eigenvalues_nonneg i
    positivity
  have hinv1 : (W + (δ : ℂ) • 1)
      * spectralFunction hW.1 (fun l => (l + δ)⁻¹) = 1 := by
    rw [← hsum, spectralFunction_mul]
    have h2 : spectralFunction hW.1 (fun l => (l + δ) * (l + δ)⁻¹)
        = spectralFunction hW.1 (fun _ => 1) :=
      spectralFunction_congr hW.1 fun i => mul_inv_cancel₀ (hne i)
    rw [h2, spectralFunction_const]
    simp
  have hdet : (W + (δ : ℂ) • 1).det ≠ 0 := by
    intro h0
    have hd : ((W + (δ : ℂ) • 1)
        * spectralFunction hW.1 (fun l => (l + δ)⁻¹)).det = 1 := by
      rw [hinv1, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at hd
    exact zero_ne_one hd
  refine ⟨hdet, ?_⟩
  have hinveq : (W + (δ : ℂ) • 1)⁻¹
      = spectralFunction hW.1 (fun l => (l + δ)⁻¹) :=
    Matrix.inv_eq_right_inv hinv1
  have hm := spectralFunction_mul hW.1 id (fun l => (l + δ)⁻¹)
  rw [spectralFunction_id] at hm
  rw [hinveq, hm]
  refine spectralFunction_congr hW.1 fun i => ?_
  simp only [id_eq]
  rw [div_eq_mul_inv]

/-- The Tikhonov contractions of a PSD Gramian converge to its support
projection as the regularization closes. -/
theorem tendsto_tikhonov_supportProj {W : Matrix h h ℂ} (hW : W.PosSemidef) :
    Tendsto (fun δ : ℝ => spectralFunction hW.1 (fun l => l / (l + δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (supportProj hW.1)) := by
  have hrw : ∀ f : ℝ → ℝ, spectralFunction hW.1 f
      = (hW.1.eigenvectorUnitary : Matrix h h ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ fun i => f (hW.1.eigenvalues i))
        * star (hW.1.eigenvectorUnitary : Matrix h h ℂ) := by
    intro f
    unfold spectralFunction
    rw [Unitary.conjStarAlgAut_apply]
  have hvec : Tendsto (fun δ : ℝ => (RCLike.ofReal ∘ fun i =>
      hW.1.eigenvalues i / (hW.1.eigenvalues i + δ) : h → ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (RCLike.ofReal ∘ fun i =>
        if 0 < hW.1.eigenvalues i then 1 else 0)) := by
    rw [tendsto_pi_nhds]
    intro i
    simp only [Function.comp]
    have hreal : Tendsto (fun δ : ℝ =>
        hW.1.eigenvalues i / (hW.1.eigenvalues i + δ)) (𝓝[>] (0 : ℝ))
        (𝓝 (if 0 < hW.1.eigenvalues i then 1 else 0)) := by
      rcases lt_or_eq_of_le (hW.eigenvalues_nonneg i) with hpos | hzero
      · rw [ite_eq_left hpos]
        have hcont : Tendsto (fun δ : ℝ =>
            hW.1.eigenvalues i / (hW.1.eigenvalues i + δ)) (𝓝 (0 : ℝ))
            (𝓝 (hW.1.eigenvalues i / (hW.1.eigenvalues i + 0))) := by
          refine Tendsto.div tendsto_const_nhds
            (tendsto_const_nhds.add tendsto_id) ?_
          rw [add_zero]
          exact hpos.ne'
        have h2 := hcont.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        rwa [add_zero, div_self hpos.ne'] at h2
      · rw [← hzero]
        simp
    exact (RCLike.continuous_ofReal.tendsto _).comp hreal
  have hdiag := ((continuous_id.matrix_diagonal
    (R := ℂ) (n := h)).tendsto _).comp hvec
  have hc : Continuous fun D : Matrix h h ℂ =>
      (hW.1.eigenvectorUnitary : Matrix h h ℂ) * D
        * star (hW.1.eigenvectorUnitary : Matrix h h ℂ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hcomp := (hc.tendsto _).comp hdiag
  have hgoal : (fun δ : ℝ => spectralFunction hW.1 (fun l => l / (l + δ)))
      = fun δ : ℝ => (hW.1.eigenvectorUnitary : Matrix h h ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ fun i =>
            hW.1.eigenvalues i / (hW.1.eigenvalues i + δ))
        * star (hW.1.eigenvectorUnitary : Matrix h h ℂ) :=
    funext fun δ => hrw _
  have hsupp : supportProj hW.1
      = (hW.1.eigenvectorUnitary : Matrix h h ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ fun i =>
            if 0 < hW.1.eigenvalues i then 1 else 0)
        * star (hW.1.eigenvectorUnitary : Matrix h h ℂ) := by
    unfold supportProj
    exact hrw _
  rw [hgoal, hsupp]
  exact hcomp

/-! #### The manuscript data of one aligned card -/

variable {e f : Type*} [Fintype e] [DecidableEq e] [Fintype f]

/-- The source projection `P_B = supp Σ_{B,M}` of one aligned card
(SMET.2/SMET.8). -/
noncomputable def srcProj (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : Matrix h h ℂ :=
  supportProj (sigma_posSemidef B hM).1

/-- The source projection is Hermitian. -/
theorem srcProj_isHermitian (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : (srcProj B hM).IsHermitian :=
  (supportProj_posSemidef _).1

/-- The source projection is idempotent. -/
theorem srcProj_idem (B : Matrix h e ℂ) {M : Matrix e e ℂ}
    (hM : M.IsHermitian) : srcProj B hM * srcProj B hM = srcProj B hM :=
  supportProj_idem _

/-- The normalized Tikhonov residual `R̂_{T,δ} = Y^*(1-Ŵ(Ŵ+δ)⁻¹)Y`. -/
noncomputable def tikhResidual (Hm P : Matrix h h ℂ) (Y : Matrix h f ℂ)
    (T δ : ℝ) : Matrix f f ℂ :=
  Yᴴ * ((1 : Matrix h h ℂ) - horizonGramian Hm P T
    * (horizonGramian Hm P T + (δ : ℂ) • 1)⁻¹) * Y

/-- The dynamic residual `R_dyn = Y^*(1-P_H^{P_B})Y`. -/
noncomputable def dynResidual {Hm P : Matrix h h ℂ} (hH : Hm.IsHermitian)
    (hP : P.IsHermitian) (T : ℝ) (Y : Matrix h f ℂ) : Matrix f f ℂ :=
  Yᴴ * ((1 : Matrix h h ℂ) - dynProj hH hP T) * Y

set_option maxHeartbeats 1000000 in
-- the ε/3 assembly of SMET.28 instantiates the full spectral and dominated
-- convergence calculus several times; the default budget is too small
/-- **`thm:GT-source-metric-cofinal`**: cofinal reserve–geometry separation
on one finite comparison carrier.  Under null-cost consistency, the uniform
reserve window (SMET.25), convergence of the clocks, targets, and source
projections, and the uniform closing of the normalized Tikhonov tails
(SMET.26), the normalized horizon Gramians converge to
`∫₀ᵀ e^{-tH}P_B e^{-tH} dt` (SMET.27), the dynamic residuals converge to
`Y^*(1-P_H^{P_B})Y` for the orthogonal projection `P_H^{P_B}` onto
`span{e^{-tH} Ran P_B : t ≥ 0}` (SMET.28), and the physical-metric
Tikhonov tail closes at the limit card as well. -/
theorem source_metric_cofinal
    {T : ℝ} (hT : 0 < T)
    (B : ℕ → Matrix h e ℂ) (M : ℕ → Matrix e e ℂ)
    (hM : ∀ n, (M n).PosSemidef)
    (H : ℕ → Matrix h h ℂ) (hHherm : ∀ n, (H n).IsHermitian)
    (Y : ℕ → Matrix h f ℂ) (Hlim : Matrix h h ℂ) (hHlim : Hlim.IsHermitian)
    (Plim : Matrix h h ℂ) (Ylim : Matrix h f ℂ)
    (_hnull : ∀ n, NullCost (B n) (M n))
    {glo ghi : ℝ} (_hglo : 0 < glo)
    (_hwin : ∀ n,
      (sigma (B n) (hM n).1
          - (glo : ℂ) • srcProj (B n) (hM n).1).PosSemidef ∧
        ((ghi : ℂ) • srcProj (B n) (hM n).1
          - sigma (B n) (hM n).1).PosSemidef)
    (hHconv : Tendsto H atTop (𝓝 Hlim))
    (hPconv : Tendsto (fun n => srcProj (B n) (hM n).1) atTop (𝓝 Plim))
    (hYconv : Tendsto Y atTop (𝓝 Ylim))
    (hTikh : ∀ ε : ℝ, 0 < ε → ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ᶠ n in atTop,
        ‖tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ
          - dynResidual (hHherm n) (srcProj_isHermitian (B n) (hM n).1) T
              (Y n)‖ ≤ ε) :
    Tendsto (fun n => horizonGramian (H n) (srcProj (B n) (hM n).1) T) atTop
        (𝓝 (horizonGramian Hlim Plim T)) ∧
      (∀ n, ∀ x : h → ℂ,
        dynProj (hHherm n) (srcProj_isHermitian (B n) (hM n).1) T *ᵥ x = x
          ↔ x ∈ cyclicCarrier (H n) (srcProj (B n) (hM n).1)) ∧
      ∃ Pinf : Matrix h h ℂ, Pinf.IsHermitian ∧ Pinf * Pinf = Pinf ∧
        (∀ x : h → ℂ, Pinf *ᵥ x = x ↔ x ∈ cyclicCarrier Hlim Plim) ∧
        Tendsto (fun n => dynResidual (hHherm n)
            (srcProj_isHermitian (B n) (hM n).1) T (Y n)) atTop
          (𝓝 (Ylimᴴ * ((1 : Matrix h h ℂ) - Pinf) * Ylim)) ∧
        Tendsto (fun δ => tikhResidual Hlim Plim Ylim T δ) (𝓝[>] (0 : ℝ))
          (𝓝 (Ylimᴴ * ((1 : Matrix h h ℂ) - Pinf) * Ylim)) := by
  classical
  -- the limit source projection is an orthogonal projection
  have hPlimherm : Plim.IsHermitian := by
    have h1 : Tendsto (fun n => (srcProj (B n) (hM n).1)ᴴ) atTop (𝓝 Plimᴴ) :=
      ((continuous_id.matrix_conjTranspose).tendsto Plim).comp hPconv
    have h2 : (fun n => (srcProj (B n) (hM n).1)ᴴ)
        = fun n => srcProj (B n) (hM n).1 :=
      funext fun n => (srcProj_isHermitian (B n) (hM n).1).eq
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hPconv
  have hPlimidem : Plim * Plim = Plim := by
    have h1 : Tendsto
        (fun n => srcProj (B n) (hM n).1 * srcProj (B n) (hM n).1) atTop
        (𝓝 (Plim * Plim)) := tendsto_matrix_mul hPconv hPconv
    have h2 : (fun n => srcProj (B n) (hM n).1 * srcProj (B n) (hM n).1)
        = fun n => srcProj (B n) (hM n).1 :=
      funext fun n => srcProj_idem (B n) (hM n).1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hPconv
  have hPlimpsd : Plim.PosSemidef :=
    posSemidef_of_hermitian_idem hPlimherm hPlimidem
  have hWlim : (horizonGramian Hlim Plim T).PosSemidef :=
    horizonGramian_posSemidef hHlim hPlimpsd hT.le
  -- SMET.27
  have h27 := horizonGramian_tendsto (T := T) hHconv hPconv
  -- the per-card carrier identification
  have hchar : ∀ n, ∀ x : h → ℂ,
      dynProj (hHherm n) (srcProj_isHermitian (B n) (hM n).1) T *ᵥ x = x
        ↔ x ∈ cyclicCarrier (H n) (srcProj (B n) (hM n).1) := fun n =>
    (dynProj_char (hHherm n) (srcProj_isHermitian (B n) (hM n).1)
      (srcProj_idem (B n) (hM n).1) hT).2.2
  obtain ⟨hc1, hc2, hc3⟩ := dynProj_char hHlim hPlimherm hPlimidem hT
  -- the target conjugation converges
  have hYlimH : Tendsto (fun n => (Y n)ᴴ) atTop (𝓝 Ylimᴴ) :=
    ((continuous_id.matrix_conjTranspose).tendsto Ylim).comp hYconv
  -- the limit-card Tikhonov tail closes on the dynamic projection
  have htail : Tendsto (fun δ => tikhResidual Hlim Plim Ylim T δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Ylimᴴ * ((1 : Matrix h h ℂ) - dynProj hHlim hPlimherm T)
        * Ylim)) := by
    have hEq : ∀ᶠ δ in 𝓝[>] (0 : ℝ), tikhResidual Hlim Plim Ylim T δ
        = Ylimᴴ * ((1 : Matrix h h ℂ)
            - spectralFunction hWlim.1 (fun l => l / (l + δ))) * Ylim := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      unfold tikhResidual
      rw [(tikhonov_spectral hWlim hδ).2]
    have hlim : Tendsto (fun δ : ℝ => Ylimᴴ * ((1 : Matrix h h ℂ)
        - spectralFunction hWlim.1 (fun l => l / (l + δ))) * Ylim)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Ylimᴴ * ((1 : Matrix h h ℂ) - supportProj hWlim.1) * Ylim)) := by
      refine tendsto_matrix_mul (tendsto_matrix_mul tendsto_const_nhds ?_)
        tendsto_const_nhds
      exact tendsto_const_nhds.sub (tendsto_tikhonov_supportProj hWlim)
    have hproof : supportProj hWlim.1 = dynProj hHlim hPlimherm T := rfl
    rw [hproof] at hlim
    exact Filter.Tendsto.congr' (hEq.mono fun δ hδ => hδ.symm) hlim
  -- the Tikhonov residuals converge at every fixed regularization
  have hF1 : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n =>
        tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ) atTop
        (𝓝 (tikhResidual Hlim Plim Ylim T δ)) := by
    intro δ hδ
    have hdet := (tikhonov_spectral hWlim hδ).1
    have hWn : Tendsto (fun n =>
        horizonGramian (H n) (srcProj (B n) (hM n).1) T + (δ : ℂ) • 1)
        atTop (𝓝 (horizonGramian Hlim Plim T + (δ : ℂ) • 1)) :=
      h27.add tendsto_const_nhds
    have hinv := tendsto_matrix_inv hWn hdet
    unfold tikhResidual
    exact tendsto_matrix_mul (tendsto_matrix_mul hYlimH
      (tendsto_const_nhds.sub (tendsto_matrix_mul h27 hinv))) hYconv
  -- SMET.28 by the ε/3 assembly through the uniform Tikhonov tails
  have h28 : Tendsto (fun n => dynResidual (hHherm n)
      (srcProj_isHermitian (B n) (hM n).1) T (Y n)) atTop
      (𝓝 (Ylimᴴ * ((1 : Matrix h h ℂ) - dynProj hHlim hPlimherm T)
        * Ylim)) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨δ0, hδ0pos, hδ0⟩ := hTikh (ε / 4) (by positivity)
    have htail_ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        dist (tikhResidual Hlim Plim Ylim T δ)
          (Ylimᴴ * ((1 : Matrix h h ℂ) - dynProj hHlim hPlimherm T) * Ylim)
          < ε / 4 :=
      Metric.tendsto_nhds.mp htail (ε / 4) (by positivity)
    have hIoo_ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo (0 : ℝ) δ0 :=
      Filter.eventually_mem_set.mpr (Ioo_mem_nhdsGT hδ0pos)
    obtain ⟨δ, hδtail, hδIoo⟩ := (htail_ev.and hIoo_ev).exists
    have hδpos : 0 < δ := hδIoo.1
    have hδle : δ ≤ δ0 := hδIoo.2.le
    have hTikh_n := hδ0 δ hδpos hδle
    have hF1_ev : ∀ᶠ n in atTop,
        dist (tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ)
          (tikhResidual Hlim Plim Ylim T δ) < ε / 4 :=
      Metric.tendsto_nhds.mp (hF1 δ hδpos) (ε / 4) (by positivity)
    filter_upwards [hTikh_n, hF1_ev] with n h1 h2
    have h3 : dist (dynResidual (hHherm n)
        (srcProj_isHermitian (B n) (hM n).1) T (Y n))
        (tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ) ≤ ε / 4 := by
      rw [dist_comm, dist_eq_norm]
      exact h1
    calc dist (dynResidual (hHherm n)
          (srcProj_isHermitian (B n) (hM n).1) T (Y n))
          (Ylimᴴ * ((1 : Matrix h h ℂ) - dynProj hHlim hPlimherm T) * Ylim)
        ≤ dist (dynResidual (hHherm n)
              (srcProj_isHermitian (B n) (hM n).1) T (Y n))
            (tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ)
          + dist (tikhResidual (H n) (srcProj (B n) (hM n).1) (Y n) T δ)
              (tikhResidual Hlim Plim Ylim T δ)
          + dist (tikhResidual Hlim Plim Ylim T δ)
              (Ylimᴴ * ((1 : Matrix h h ℂ) - dynProj hHlim hPlimherm T)
                * Ylim) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  exact ⟨h27, hchar, dynProj hHlim hPlimherm T, hc1, hc2, hc3, h28, htail⟩

end MetricCofinal

end SourceMetricCofinal

end NCG
