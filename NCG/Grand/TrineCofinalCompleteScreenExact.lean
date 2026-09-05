import NCG.Grand.TrineTransportExtras

/-!
# Cofinal trine transport on an arbitrary complete current screen

The earlier implementation used functions on a finite screen.  The argument
only needs completeness of the total-variation carrier.  This file states and
proves that Banach-space theorem: summable adjacent defects make all three
positive outcomes converge, every bounded linear carrier/current
reconstruction and payoff converges, every continuous slack construction
converges, and normalization is valid precisely on a nonzero-limit branch.
-/

open Filter Topology

namespace NCG.TrineCofinalCompleteScreen

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Summable adjacent total-variation defects give a limit for each of the
three positive outcomes on any complete current-screen carrier. -/
theorem positive_outcomes_converge
    (rho : Fin 3 → ℕ → B) (epsilon : ℕ → ℝ)
    (hstep : ∀ k n, dist (rho k n) (rho k (n + 1)) ≤ epsilon n)
    (hsum : Summable epsilon) :
    ∃ limit : Fin 3 → B, ∀ k, Tendsto (rho k) atTop (𝓝 (limit k)) := by
  have hc (k : Fin 3) : CauchySeq (rho k) :=
    cauchySeq_of_dist_le_of_summable epsilon (hstep k) hsum
  choose limit hlimit using fun k => cauchySeq_tendsto_of_complete (hc k)
  exact ⟨limit, hlimit⟩

/-- Coordinatewise convergence of all three outcomes is convergence of the
entire trine packet in the product Banach space. -/
theorem packet_tendsto
    (rho : Fin 3 → ℕ → B) (limit : Fin 3 → B)
    (hrho : ∀ k, Tendsto (rho k) atTop (𝓝 (limit k))) :
    Tendsto (fun n k => rho k n) atTop (𝓝 limit) := by
  rw [tendsto_pi_nhds]
  exact hrho

/-- Every bounded linear reconstruction of the three positive outcomes—hence
the carrier and complex-current Fourier maps—converges on the same screen. -/
theorem bounded_linear_reconstruction_converges
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    (rho : Fin 3 → ℕ → B) (limit : Fin 3 → B)
    (hrho : ∀ k, Tendsto (rho k) atTop (𝓝 (limit k)))
    (L : (Fin 3 → B) →L[ℝ] C) :
    Tendsto (fun n => L (fun k => rho k n)) atTop (𝓝 (L limit)) :=
  L.continuous.continuousAt.tendsto.comp (packet_tendsto rho limit hrho)

/-- Any bounded transported payoff is a continuous linear functional of the
current measure and therefore converges. -/
theorem bounded_payoff_converges
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    (zeta : ℕ → C) (zetaLimit : C)
    (hzeta : Tendsto zeta atTop (𝓝 zetaLimit))
    (payoff : C →L[ℝ] ℂ) :
    Tendsto (fun n => payoff (zeta n)) atTop (𝓝 (payoff zetaLimit)) :=
  payoff.continuous.continuousAt.tendsto.comp hzeta

/-- Every continuous slack/cancellation construction passes to the cofinal
limit.  The manuscript's `τ - 2|ζ|` is one such map because variation is
1-Lipschitz. -/
theorem continuous_slack_converges
    {T Z S : Type*} [TopologicalSpace T] [TopologicalSpace Z]
    [TopologicalSpace S]
    (tau : ℕ → T) (zeta : ℕ → Z) (tauLimit : T) (zetaLimit : Z)
    (htau : Tendsto tau atTop (𝓝 tauLimit))
    (hzeta : Tendsto zeta atTop (𝓝 zetaLimit))
    (slack : T × Z → S) (hslack : Continuous slack) :
    Tendsto (fun n => slack (tau n, zeta n)) atTop
      (𝓝 (slack (tauLimit, zetaLimit))) :=
  hslack.continuousAt.tendsto.comp (htau.prodMk_nhds hzeta)

/-- Division is continuous exactly on a branch with nonzero limiting
partition amplitude; the unnormalized current remains valid without it. -/
theorem normalized_amplitude_converges
    (tau : ℕ → ℝ) (zeta : ℕ → ℂ) (tauLimit : ℝ) (zetaLimit : ℂ)
    (htau : Tendsto tau atTop (𝓝 tauLimit))
    (hzeta : Tendsto zeta atTop (𝓝 zetaLimit))
    (hfloor : tauLimit ≠ 0) :
    Tendsto (fun n => zeta n / (tau n : ℂ)) atTop
      (𝓝 (zetaLimit / (tauLimit : ℂ))) := by
  have htauC : Tendsto (fun n => (tau n : ℂ)) atTop (𝓝 (tauLimit : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp htau
  have hne : (tauLimit : ℂ) ≠ 0 := by exact_mod_cast hfloor
  exact hzeta.div htauC hne

/-- Bundled general-current-screen form of the Gran--Tensor theorem. -/
theorem cofinal_positive_outcome_and_current_transport
    (rho : Fin 3 → ℕ → B) (epsilon : ℕ → ℝ)
    (hstep : ∀ k n, dist (rho k n) (rho k (n + 1)) ≤ epsilon n)
    (hsum : Summable epsilon) :
    ∃ limit : Fin 3 → B,
      (∀ k, Tendsto (rho k) atTop (𝓝 (limit k))) ∧
      (∀ {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
        (L : (Fin 3 → B) →L[ℝ] C),
        Tendsto (fun n => L (fun k => rho k n)) atTop (𝓝 (L limit))) := by
  obtain ⟨limit, hlimit⟩ := positive_outcomes_converge rho epsilon hstep hsum
  refine ⟨limit, hlimit, ?_⟩
  intro C _ _ L
  exact bounded_linear_reconstruction_converges rho limit hlimit L

end NCG.TrineCofinalCompleteScreen
