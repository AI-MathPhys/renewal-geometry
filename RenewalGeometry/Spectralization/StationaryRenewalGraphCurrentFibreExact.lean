/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Spectralization.FiniteGraphSpectralUniversalityFibreExact
import RenewalGeometry.Spectralization.CanonicalGraphSpectralizationExact
/-!
# Stationary renewal graphs and the cycle-current realization fibre

This file covers `def:supp-renewal-graph`, `def:supp-current-polytope`,
`thm:supp-graph-realization` and `cor:supp-fibre-dimension` of
`predictive_spectral_geometry`.

* `StationaryRenewalGraph` bundles positive normalized masses, nonnegative
  off-diagonal rates, the mass-stationarity equation and connectedness of the
  positive-conductance support, with the derived flux `q = m k`, symmetric
  conductance `c = (q + qᵀ)/2` and antisymmetric current `j = (q - qᵀ)/2`.
* `SimpleOrientation` is a simple undirected graph presented through one
  orientation of each edge; `incidenceReal`/`incidence` are its oriented
  incidence matrices and `currentPolytope`/`closedCurrentPolytope` are the
  open and closed admissible cycle-current boxes `{j ∈ ker B : |j_e| < c_e}`.
* `stationary_markov_realization_fibre` assembles (R1)–(R4): the reversible
  realization `k = c/m`, the current realizations `k = (c + j)/m`, the unique
  converse decomposition `q = c + j`, independence of the Hodge–Dirac matrix
  from the current, and the bijection of the strict polytope with the
  positive-edge stationary realizations.
* `fibre_dimension_and_faithfulness` gives `dim J(G,c) = |E| - |V| + 1`, the
  tree criterion, and non-faithfulness of the metric spectralization when the
  first Betti number is positive.
-/

open Matrix Finset

namespace RenewalGeometry
namespace StationaryRenewalGraphFibre

open FiniteWeightedGraphHodgeDirac StationaryFluxAdjoint
  FiniteGraphSpectralUniversalityFibre CanonicalGraphSpectralization

set_option linter.unusedSectionVars false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### `def:supp-renewal-graph` -/

/-- **`def:supp-renewal-graph`.**  A stationary finite renewal graph: positive
masses summing to one, nonnegative off-diagonal rates (the diagonal is
normalized to zero since the generator ignores it), the mass-stationarity
equation `∑_y (q_xy - q_yx) = 0` for the flux `q_xy = m_x k_xy`, and
connectedness of the positive-conductance support of `c = (q + qᵀ)/2`. -/
structure StationaryRenewalGraph (V : Type*) [Fintype V] [DecidableEq V] where
  mass : V → ℝ
  rate : V → V → ℝ
  mass_pos : ∀ x, 0 < mass x
  mass_sum : ∑ x, mass x = 1
  rate_diag : ∀ x, rate x x = 0
  rate_nonneg : ∀ x y, x ≠ y → 0 ≤ rate x y
  stationary : ∀ x, ∑ y, (mass x * rate x y - mass y * rate y x) = 0
  connected : ConductanceConnected
    (symmetrizedConductance (fun x y => mass x * rate x y))

namespace StationaryRenewalGraph

variable (R : StationaryRenewalGraph V)

/-- The generator `(L f)(x) = ∑_{y ≠ x} k_xy (f(y) - f(x))` of
`def:supp-renewal-graph` (the `y = x` term vanishes identically). -/
def generator (f : V → ℝ) : V → ℝ := fun x => ∑ y, R.rate x y * (f y - f x)

theorem generator_eq_sum_erase (f : V → ℝ) (x : V) :
    R.generator f x = ∑ y ∈ univ.erase x, R.rate x y * (f y - f x) := by
  unfold generator
  rw [Finset.sum_erase]
  simp

/-- The stationary flux `q_xy = m_x k_xy`. -/
def flux (x y : V) : ℝ := R.mass x * R.rate x y

/-- The symmetric conductance `c_xy = (q_xy + q_yx)/2`. -/
def conductance : V → V → ℝ := symmetrizedConductance R.flux

/-- The antisymmetric current `j_xy = (q_xy - q_yx)/2`. -/
def current (x y : V) : ℝ := (R.flux x y - R.flux y x) / 2

theorem conductance_symm (x y : V) : R.conductance x y = R.conductance y x := by
  simp [conductance, symmetrizedConductance, add_comm]

theorem current_antisymm (x y : V) : R.current y x = - R.current x y := by
  simp only [current]
  ring

theorem flux_eq_conductance_add_current (x y : V) :
    R.flux x y = R.conductance x y + R.current x y := by
  simp only [conductance, symmetrizedConductance, current]
  ring

theorem flux_diag (x : V) : R.flux x x = 0 := by
  simp [flux, R.rate_diag]

theorem flux_nonneg (x y : V) : 0 ≤ R.flux x y := by
  by_cases h : x = y
  · subst h
    rw [R.flux_diag]
  · exact mul_nonneg (R.mass_pos x).le (R.rate_nonneg x y h)

theorem current_diag (x : V) : R.current x x = 0 := by
  simp [current]

/-- The stationarity equation in flux form. -/
theorem stationary_balance (x : V) : ∑ y, R.flux x y = ∑ y, R.flux y x := by
  have h := R.stationary x
  rw [Finset.sum_sub_distrib, sub_eq_zero] at h
  exact h

/-- Stationarity is the divergence-free equation for the current. -/
theorem sum_current_eq_zero (x : V) : ∑ y, R.current x y = 0 := by
  unfold current
  rw [← Finset.sum_div, Finset.sum_sub_distrib, R.stationary_balance x, sub_self, zero_div]

/-- The generator is the flux generator of `StationaryFluxAdjoint`. -/
theorem generator_eq_fluxGenerator (f : V → ℝ) :
    R.generator f = fluxGenerator R.mass R.flux f := by
  funext x
  unfold generator fluxGenerator flux
  rw [eq_div_iff (R.mass_pos x).ne', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Every stationary renewal graph satisfies the hypotheses of
`thm:supp-graph-square` (`canonical_graph_spectralization`). -/
theorem spectralization : SpectralizationConclusion R.mass R.rate :=
  canonical_graph_spectralization R.mass R.rate R.mass_pos
    (fun x y => by
      by_cases h : x = y
      · subst h
        rw [R.rate_diag]
      · exact R.rate_nonneg x y h)
    R.stationary_balance R.connected

end StationaryRenewalGraph

/-! ### Simple oriented graphs and the incidence matrix -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A simple undirected graph on `V` with edge set `E`, presented through one
chosen orientation of every edge: no two edges join the same unordered pair
and no edge is a loop. -/
structure SimpleOrientation (V E : Type*) where
  tail : E → V
  head : E → V
  parallel_eq : ∀ e e', tail e = tail e' → head e = head e' → e = e'
  not_antiparallel : ∀ e e', tail e = head e' → head e = tail e' → False

namespace SimpleOrientation

variable (G : SimpleOrientation V E)

theorem tail_ne_head (e : E) : G.tail e ≠ G.head e :=
  fun h => G.not_antiparallel e e h h.symm

/-- The undirected adjacency relation of the graph. -/
def Adjacent (x y : V) : Prop :=
  ∃ e, (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x)

theorem not_adjacent_self (x : V) : ¬ G.Adjacent x x := by
  rintro ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> exact G.tail_ne_head e (h1.trans h2.symm)

/-- Connectedness of the undirected graph. -/
def Connected : Prop := ∀ x y, Relation.ReflTransGen G.Adjacent x y

/-- The real oriented incidence matrix `B : ℝ^E → ℝ^V`,
`B_{x e} = [tail e = x] - [head e = x]`. -/
def incidenceReal : Matrix V E ℝ :=
  fun x e => (if G.tail e = x then 1 else 0) - (if G.head e = x then 1 else 0)

/-- The same incidence matrix with complex entries, as used by the cycle
projector of `FiniteGraphSpectralUniversalityFibre`. -/
def incidence : Matrix V E ℂ :=
  fun x e => (if G.tail e = x then 1 else 0) - (if G.head e = x then 1 else 0)

theorem incidence_eq_map : G.incidence = G.incidenceReal.map ((↑) : ℝ → ℂ) := by
  ext x e
  simp only [incidence, incidenceReal, Matrix.map_apply]
  split_ifs <;> simp

theorem star_incidence_apply (x : V) (e : E) : star (G.incidence x e) = G.incidence x e := by
  unfold incidence
  split_ifs <;> simp

theorem incidenceReal_mulVec_apply (j : E → ℝ) (x : V) :
    (G.incidenceReal *ᵥ j) x =
      ∑ e, ((if G.tail e = x then j e else 0) - (if G.head e = x then j e else 0)) := by
  simp only [Matrix.mulVec, dotProduct, incidenceReal, sub_mul, ite_mul, one_mul, zero_mul]

theorem incidence_mulVec_apply (w : E → ℂ) (x : V) :
    (G.incidence *ᵥ w) x = ∑ e, ((G.incidenceReal x e : ℝ) : ℂ) * w e := by
  rw [incidence_eq_map]
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- The complex stationarity equation of `FiniteGraphSpectralUniversalityFibre`
for a real current is the real kernel equation `B j = 0`. -/
theorem isStationaryCurrent_incidence_iff (j : E → ℝ) :
    IsStationaryCurrent G.incidence j ↔ G.incidenceReal *ᵥ j = 0 := by
  unfold IsStationaryCurrent
  have h : ∀ x, (G.incidence *ᵥ fun e => (j e : ℂ)) x = ((G.incidenceReal *ᵥ j) x : ℂ) := by
    intro x
    rw [incidence_mulVec_apply]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    rfl
  constructor
  · intro hz
    funext x
    have := congrFun hz x
    rw [h x] at this
    simpa using this
  · intro hz
    funext x
    rw [h x, hz]
    simp

/-! ### Conductances, currents and fluxes on ordered pairs -/

/-- The symmetric conductance on ordered pairs induced by edge conductances
`c : E → ℝ` (zero off the graph). -/
def pairConductance (c : E → ℝ) (x y : V) : ℝ :=
  ∑ e, if (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x) then c e else 0

/-- The antisymmetric current on ordered pairs induced by an oriented current
`j : E → ℝ` (extended by `j_{ē} = -j_e`, zero off the graph). -/
def pairCurrent (j : E → ℝ) (x y : V) : ℝ :=
  ∑ e, ((if G.tail e = x ∧ G.head e = y then j e else 0) -
    (if G.tail e = y ∧ G.head e = x then j e else 0))

/-- The stationary flux `q_xy = c_xy + j_xy` of `eq:supp-current-realization`. -/
def pairFlux (c j : E → ℝ) (x y : V) : ℝ :=
  G.pairConductance c x y + G.pairCurrent j x y

/-- The rates `k_xy = (c_xy + j_xy)/m_x` of `eq:supp-current-realization`. -/
noncomputable def rates (m : V → ℝ) (c j : E → ℝ) (x y : V) : ℝ :=
  G.pairFlux c j x y / m x

/-- The reversible realization `k_xy = c_xy / m_x` of
`eq:supp-reversible-realization`. -/
noncomputable def reversibleRates (m : V → ℝ) (c : E → ℝ) : V → V → ℝ :=
  G.rates m c 0

theorem pairConductance_symm (c : E → ℝ) (x y : V) :
    G.pairConductance c y x = G.pairConductance c x y := by
  unfold pairConductance
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : G.tail e = x ∧ G.head e = y <;> by_cases h' : G.tail e = y ∧ G.head e = x <;>
    simp [h, h']

theorem pairCurrent_antisymm (j : E → ℝ) (x y : V) :
    G.pairCurrent j y x = - G.pairCurrent j x y := by
  unfold pairCurrent
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem pairCurrent_zero (x y : V) : G.pairCurrent 0 x y = 0 := by
  simp [pairCurrent]

theorem pairConductance_tail_head (c : E → ℝ) (e : E) :
    G.pairConductance c (G.tail e) (G.head e) = c e := by
  unfold pairConductance
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne
    rw [if_neg]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hne (G.parallel_eq e' e h1 h2)
    · exact G.not_antiparallel e' e h1 h2
  · intro h
    exact absurd (Finset.mem_univ e) h

theorem pairCurrent_tail_head (j : E → ℝ) (e : E) :
    G.pairCurrent j (G.tail e) (G.head e) = j e := by
  unfold pairCurrent
  rw [Finset.sum_eq_single e]
  · have := G.tail_ne_head e
    simp [this]
  · intro e' _ hne
    rw [if_neg, if_neg, sub_zero]
    · rintro ⟨h1, h2⟩
      exact G.not_antiparallel e' e h1 h2
    · rintro ⟨h1, h2⟩
      exact hne (G.parallel_eq e' e h1 h2)
  · intro h
    exact absurd (Finset.mem_univ e) h

theorem pairConductance_head_tail (c : E → ℝ) (e : E) :
    G.pairConductance c (G.head e) (G.tail e) = c e := by
  rw [pairConductance_symm, pairConductance_tail_head]

theorem pairCurrent_head_tail (j : E → ℝ) (e : E) :
    G.pairCurrent j (G.head e) (G.tail e) = - j e := by
  rw [pairCurrent_antisymm, pairCurrent_tail_head]

theorem pairConductance_eq_zero_of_not_adjacent (c : E → ℝ) {x y : V}
    (h : ¬ G.Adjacent x y) : G.pairConductance c x y = 0 := by
  unfold pairConductance
  apply Finset.sum_eq_zero
  intro e _
  rw [if_neg]
  intro hc
  exact h ⟨e, hc⟩

theorem pairCurrent_eq_zero_of_not_adjacent (j : E → ℝ) {x y : V}
    (h : ¬ G.Adjacent x y) : G.pairCurrent j x y = 0 := by
  unfold pairCurrent
  apply Finset.sum_eq_zero
  intro e _
  rw [if_neg, if_neg, sub_zero]
  · intro hc
    exact h ⟨e, Or.inr hc⟩
  · intro hc
    exact h ⟨e, Or.inl hc⟩

theorem pairConductance_pos_of_adjacent (c : E → ℝ) (hc : ∀ e, 0 < c e) {x y : V}
    (h : G.Adjacent x y) : 0 < G.pairConductance c x y := by
  obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · rw [pairConductance_tail_head]
    exact hc e
  · rw [pairConductance_head_tail]
    exact hc e

theorem pairFlux_diag (c j : E → ℝ) (x : V) : G.pairFlux c j x x = 0 := by
  simp [pairFlux, pairConductance_eq_zero_of_not_adjacent G c (G.not_adjacent_self x),
    pairCurrent_eq_zero_of_not_adjacent G j (G.not_adjacent_self x)]

/-- Inside the closed box `|j_e| ≤ c_e` every directed flux is nonnegative. -/
theorem pairFlux_nonneg (c j : E → ℝ) (hj : ∀ e, |j e| ≤ c e) (x y : V) :
    0 ≤ G.pairFlux c j x y := by
  unfold pairFlux pairConductance pairCurrent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro e _
  have h := abs_le.mp (hj e)
  by_cases hP : G.tail e = x ∧ G.head e = y
  · obtain ⟨rfl, rfl⟩ := hP
    have hQ : ¬ (G.tail e = G.head e ∧ G.head e = G.tail e) := fun h => G.tail_ne_head e h.1
    simp [hQ]
    linarith [h.1, h.2]
  · by_cases hQ : G.tail e = y ∧ G.head e = x
    · obtain ⟨rfl, rfl⟩ := hQ
      simp [hP]
      linarith [h.1, h.2]
    · simp [hP, hQ]

theorem pairFlux_tail_head (c j : E → ℝ) (e : E) :
    G.pairFlux c j (G.tail e) (G.head e) = c e + j e := by
  rw [pairFlux, pairConductance_tail_head, pairCurrent_tail_head]

theorem pairFlux_head_tail (c j : E → ℝ) (e : E) :
    G.pairFlux c j (G.head e) (G.tail e) = c e - j e := by
  rw [pairFlux, pairConductance_head_tail, pairCurrent_head_tail]
  ring

/-- Summing the pair current over the second vertex gives the incidence
divergence `(B j)(x)`. -/
theorem sum_pairCurrent (j : E → ℝ) (x : V) :
    ∑ y, G.pairCurrent j x y = (G.incidenceReal *ᵥ j) x := by
  rw [incidenceReal_mulVec_apply]
  unfold pairCurrent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : G.tail e = x
    · simp [h]
    · simp [h]
  · by_cases h : G.head e = x
    · simp [h]
    · simp [h]

/-- The mass-stationarity defect of the flux `c + j` is twice the incidence
divergence of `j`: `∑_y (q_xy - q_yx) = 2 (B j)(x)`. -/
theorem sum_pairFlux_sub (c j : E → ℝ) (x : V) :
    ∑ y, (G.pairFlux c j x y - G.pairFlux c j y x) = 2 * (G.incidenceReal *ᵥ j) x := by
  rw [← sum_pairCurrent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [pairFlux]
  rw [pairConductance_symm G c x y, pairCurrent_antisymm G j x y]
  ring

/-! ### `def:supp-current-polytope` -/

/-- **`def:supp-current-polytope`.**  The admissible cycle-current polytope
`J(G,c) = {j ∈ ker B : |j_e| < c_e for every e}`. -/
def currentPolytope (c : E → ℝ) : Set (E → ℝ) :=
  {j | G.incidenceReal *ᵥ j = 0 ∧ ∀ e, |j e| < c e}

/-- The closed fibre of `def:supp-current-polytope`, in which some directed
rates may vanish. -/
def closedCurrentPolytope (c : E → ℝ) : Set (E → ℝ) :=
  {j | G.incidenceReal *ᵥ j = 0 ∧ ∀ e, |j e| ≤ c e}

/-- The polytope is the strict fibre of `FiniteGraphSpectralUniversalityFibre`
for the complex incidence matrix. -/
theorem currentPolytope_eq_fibre (c : E → ℝ) :
    G.currentPolytope c = GraphSpectralFibre G.incidence c := by
  ext j
  simp only [currentPolytope, GraphSpectralFibre, Set.mem_ofPred_eq,
    isStationaryCurrent_incidence_iff]

theorem currentPolytope_subset_closed (c : E → ℝ) :
    G.currentPolytope c ⊆ G.closedCurrentPolytope c :=
  fun _ hj => ⟨hj.1, fun e => (hj.2 e).le⟩

theorem zero_mem_currentPolytope (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    (0 : E → ℝ) ∈ G.currentPolytope c := by
  refine ⟨by simp, fun e => ?_⟩
  simpa using hc e

/-! ### Stationary Markov realizations of the metric triple `(m, G, c)` -/

/-- A rate matrix `k` is a stationary Markov realization of the metric graph
triple `(m, G, c)`: zero diagonal, nonnegative rates, mass stationarity, and
symmetrized flux equal to the edge conductances `c` (zero off the graph). -/
structure IsRealization (m : V → ℝ) (c : E → ℝ) (k : V → V → ℝ) : Prop where
  diag : ∀ x, k x x = 0
  nonneg : ∀ x y, x ≠ y → 0 ≤ k x y
  stationary : ∀ x, ∑ y, (m x * k x y - m y * k y x) = 0
  conductance : ∀ x y,
    symmetrizedConductance (fun x y => m x * k x y) x y = G.pairConductance c x y

variable {m : V → ℝ}

theorem mass_mul_rates (hm : ∀ x, 0 < m x) (c j : E → ℝ) (x y : V) :
    m x * G.rates m c j x y = G.pairFlux c j x y := by
  unfold rates
  rw [mul_div_cancel₀ _ (hm x).ne']

/-- **(R4)**: the symmetrized flux of every current realization is the fixed
conductance, independently of `j`. -/
theorem symmetrizedConductance_rates (hm : ∀ x, 0 < m x) (c j : E → ℝ) (x y : V) :
    symmetrizedConductance (fun x y => m x * G.rates m c j x y) x y =
      G.pairConductance c x y := by
  simp only [symmetrizedConductance, mass_mul_rates G hm, pairFlux]
  rw [pairConductance_symm G c x y, pairCurrent_antisymm G j x y]
  ring

/-- **(R4)**: the Hodge–Dirac matrix of every current realization is the
Hodge–Dirac matrix of `(m, c)`. -/
theorem dirac_rates (hm : ∀ x, 0 < m x) (c j : E → ℝ) :
    dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j x y)) =
      dirac m (G.pairConductance c) := by
  congr 1
  funext x y
  exact symmetrizedConductance_rates G hm c j x y

theorem rates_tail_head (c j : E → ℝ) (e : E) :
    G.rates m c j (G.tail e) (G.head e) = (c e + j e) / m (G.tail e) := by
  rw [rates, pairFlux_tail_head]

theorem rates_head_tail (c j : E → ℝ) (e : E) :
    G.rates m c j (G.head e) (G.tail e) = (c e - j e) / m (G.head e) := by
  rw [rates, pairFlux_head_tail]

/-- **(R2)**, closed form: every current in the closed polytope gives a
stationary Markov realization. -/
theorem isRealization_rates (hm : ∀ x, 0 < m x) (c : E → ℝ) {j : E → ℝ}
    (hj : j ∈ G.closedCurrentPolytope c) : G.IsRealization m c (G.rates m c j) where
  diag x := by simp [rates, pairFlux_diag]
  nonneg x y _ := div_nonneg (G.pairFlux_nonneg c j hj.2 x y) (hm x).le
  stationary x := by
    simp only [mass_mul_rates G hm]
    rw [sum_pairFlux_sub, hj.1]
    simp
  conductance := symmetrizedConductance_rates G hm c j

/-- **(R2)**, strict form: inside the open polytope both directed rates of
every edge are strictly positive. -/
theorem rates_pos_of_mem (hm : ∀ x, 0 < m x) (c : E → ℝ) {j : E → ℝ}
    (hj : j ∈ G.currentPolytope c) (e : E) :
    0 < G.rates m c j (G.tail e) (G.head e) ∧ 0 < G.rates m c j (G.head e) (G.tail e) := by
  have h := abs_lt.mp (hj.2 e)
  rw [rates_tail_head, rates_head_tail]
  exact ⟨div_pos (by linarith) (hm _), div_pos (by linarith) (hm _)⟩

/-- **(R1)**: the reversible realization `k = c/m` is a stationary
realization satisfying detailed balance `m_x k_xy = m_y k_yx`. -/
theorem isRealization_reversibleRates (hm : ∀ x, 0 < m x) (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    G.IsRealization m c (G.reversibleRates m c) ∧
      ∀ x y, m x * G.reversibleRates m c x y = m y * G.reversibleRates m c y x := by
  refine ⟨G.isRealization_rates hm c
    (G.currentPolytope_subset_closed c (G.zero_mem_currentPolytope c hc)), ?_⟩
  intro x y
  simp only [reversibleRates, mass_mul_rates G hm, pairFlux, pairCurrent_zero, add_zero]
  exact (pairConductance_symm G c x y).symm

/-- The current `j_e = (q_{tail e, head e} - q_{head e, tail e})/2` read off a
rate matrix, `q = m k`. -/
def currentOf (m : V → ℝ) (k : V → V → ℝ) (e : E) : ℝ :=
  (m (G.tail e) * k (G.tail e) (G.head e) - m (G.head e) * k (G.head e) (G.tail e)) / 2

theorem currentOf_rates (hm : ∀ x, 0 < m x) (c j : E → ℝ) :
    G.currentOf m (G.rates m c j) = j := by
  funext e
  simp only [currentOf, mass_mul_rates G hm, pairFlux_tail_head, pairFlux_head_tail]
  ring

variable {G}

/-- Every stationary realization has flux `q = c + j` for its own current. -/
theorem IsRealization.flux_eq (hm : ∀ x, 0 < m x) {c : E → ℝ} {k : V → V → ℝ}
    (hk : G.IsRealization m c k) (x y : V) :
    m x * k x y = G.pairFlux c (G.currentOf m k) x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [hk.diag, pairFlux_diag]
    simp
  by_cases hadj : G.Adjacent x y
  · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hadj
    · have hc := hk.conductance (G.tail e) (G.head e)
      rw [pairConductance_tail_head] at hc
      simp only [symmetrizedConductance] at hc
      rw [pairFlux_tail_head]
      simp only [currentOf]
      linarith
    · have hc := hk.conductance (G.tail e) (G.head e)
      rw [pairConductance_tail_head] at hc
      simp only [symmetrizedConductance] at hc
      rw [pairFlux_head_tail]
      simp only [currentOf]
      linarith
  · have hc := hk.conductance x y
    rw [pairConductance_eq_zero_of_not_adjacent G c hadj] at hc
    simp only [symmetrizedConductance] at hc
    have h1 := mul_nonneg (hm x).le (hk.nonneg x y hxy)
    have h2 := mul_nonneg (hm y).le (hk.nonneg y x (Ne.symm hxy))
    simp only [pairFlux, pairConductance_eq_zero_of_not_adjacent G c hadj,
      pairCurrent_eq_zero_of_not_adjacent G _ hadj, add_zero]
    linarith

/-- The current of a stationary realization is divergence free. -/
theorem IsRealization.incidence_currentOf (hm : ∀ x, 0 < m x) {c : E → ℝ}
    {k : V → V → ℝ} (hk : G.IsRealization m c k) :
    G.incidenceReal *ᵥ G.currentOf m k = 0 := by
  funext x
  have h := G.sum_pairFlux_sub c (G.currentOf m k) x
  simp only [← hk.flux_eq hm] at h
  rw [hk.stationary x] at h
  simp only [Pi.zero_apply]
  linarith

/-- The current of a stationary realization lies in the closed box. -/
theorem IsRealization.abs_currentOf_le (hm : ∀ x, 0 < m x) {c : E → ℝ}
    {k : V → V → ℝ} (hk : G.IsRealization m c k) (e : E) :
    |G.currentOf m k e| ≤ c e := by
  have hc := hk.conductance (G.tail e) (G.head e)
  rw [pairConductance_tail_head] at hc
  simp only [symmetrizedConductance] at hc
  have h1 := mul_nonneg (hm (G.tail e)).le (hk.nonneg (G.tail e) (G.head e) (G.tail_ne_head e))
  have h2 := mul_nonneg (hm (G.head e)).le (hk.nonneg (G.head e) (G.tail e) (G.tail_ne_head e).symm)
  rw [abs_le]
  unfold currentOf
  constructor <;> linarith

theorem IsRealization.currentOf_mem_closed (hm : ∀ x, 0 < m x) {c : E → ℝ}
    {k : V → V → ℝ} (hk : G.IsRealization m c k) :
    G.currentOf m k ∈ G.closedCurrentPolytope c :=
  ⟨hk.incidence_currentOf hm, hk.abs_currentOf_le hm⟩

/-- With strictly positive directed rates on every edge the current lies in
the open polytope. -/
theorem IsRealization.currentOf_mem (hm : ∀ x, 0 < m x) {c : E → ℝ}
    {k : V → V → ℝ} (hk : G.IsRealization m c k)
    (hpos : ∀ e, 0 < k (G.tail e) (G.head e) ∧ 0 < k (G.head e) (G.tail e)) :
    G.currentOf m k ∈ G.currentPolytope c := by
  refine ⟨hk.incidence_currentOf hm, fun e => ?_⟩
  have hc := hk.conductance (G.tail e) (G.head e)
  rw [pairConductance_tail_head] at hc
  simp only [symmetrizedConductance] at hc
  have h1 := mul_pos (hm (G.tail e)) (hpos e).1
  have h2 := mul_pos (hm (G.head e)) (hpos e).2
  rw [abs_lt]
  unfold currentOf
  constructor <;> linarith

/-- **(R3)**: every stationary realization is of the form `k = (c + j)/m`
for its own current. -/
theorem IsRealization.eq_rates (hm : ∀ x, 0 < m x) {c : E → ℝ} {k : V → V → ℝ}
    (hk : G.IsRealization m c k) : k = G.rates m c (G.currentOf m k) := by
  funext x y
  unfold rates
  rw [← hk.flux_eq hm x y, mul_div_cancel_left₀ _ (hm x).ne']

/-- **(R3)**: the decomposition `q = c + j` of a stationary realization is
unique, with `j` in the closed polytope. -/
theorem IsRealization.existsUnique_current (hm : ∀ x, 0 < m x) {c : E → ℝ}
    {k : V → V → ℝ} (hk : G.IsRealization m c k) :
    ∃! j, j ∈ G.closedCurrentPolytope c ∧ k = G.rates m c j := by
  refine ⟨G.currentOf m k, ⟨hk.currentOf_mem_closed hm, hk.eq_rates hm⟩, ?_⟩
  rintro j ⟨_, hj⟩
  rw [hj, currentOf_rates G hm]

variable (G)

/-- The realization map `j ↦ (c + j)/m` is injective. -/
theorem rates_injective (hm : ∀ x, 0 < m x) (c : E → ℝ) :
    Function.Injective (G.rates m c) := by
  intro j₁ j₂ h
  have := congrArg (G.currentOf m) h
  rwa [currentOf_rates G hm, currentOf_rates G hm] at this

/-- **`eq:supp-realization-fibre`**, closed form: the closed current polytope
is in bijection with the stationary Markov realizations of `(m, G, c)`. -/
noncomputable def closedRealizationEquiv (hm : ∀ x, 0 < m x) (c : E → ℝ) :
    G.closedCurrentPolytope c ≃ {k : V → V → ℝ // G.IsRealization m c k} where
  toFun j := ⟨G.rates m c j.1, G.isRealization_rates hm c j.2⟩
  invFun k := ⟨G.currentOf m k.1, k.2.currentOf_mem_closed hm⟩
  left_inv j := Subtype.ext (currentOf_rates G hm c j.1)
  right_inv k := Subtype.ext (k.2.eq_rates hm).symm

/-- **`eq:supp-realization-fibre`**: the open current polytope `J(G,c)` is in
bijection with the stationary Markov realizations of `(m, G, c)` having
strictly positive directed rates on every edge. -/
noncomputable def realizationEquiv (hm : ∀ x, 0 < m x) (c : E → ℝ) :
    G.currentPolytope c ≃
      {k : V → V → ℝ // G.IsRealization m c k ∧
        ∀ e, 0 < k (G.tail e) (G.head e) ∧ 0 < k (G.head e) (G.tail e)} where
  toFun j := ⟨G.rates m c j.1,
    G.isRealization_rates hm c (G.currentPolytope_subset_closed c j.2),
    G.rates_pos_of_mem hm c j.2⟩
  invFun k := ⟨G.currentOf m k.1, k.2.1.currentOf_mem hm k.2.2⟩
  left_inv j := Subtype.ext (currentOf_rates G hm c j.1)
  right_inv k := Subtype.ext (k.2.1.eq_rates hm).symm

variable {G} in
/-- A stationary realization of a connected graph with positive edge
conductances and normalized masses is a stationary finite renewal graph in
the sense of `def:supp-renewal-graph`. -/
def IsRealization.toStationaryRenewalGraph (hm : ∀ x, 0 < m x) (hsum : ∑ x, m x = 1)
    {c : E → ℝ} (hc : ∀ e, 0 < c e) (hG : G.Connected) {k : V → V → ℝ}
    (hk : G.IsRealization m c k) : StationaryRenewalGraph V where
  mass := m
  rate := k
  mass_pos := hm
  mass_sum := hsum
  rate_diag := hk.diag
  rate_nonneg := hk.nonneg
  stationary := hk.stationary
  connected := by
    intro x y
    have hfun : symmetrizedConductance (fun x y => m x * k x y) = G.pairConductance c := by
      funext x y
      exact hk.conductance x y
    rw [hfun]
    exact Relation.ReflTransGen.mono
      (fun a b hab => G.pairConductance_pos_of_adjacent c hc hab) x y (hG x y)

/-- Conversely a stationary finite renewal graph whose conductance is carried
by `(G, c)` is a stationary realization of `(m, G, c)`. -/
theorem isRealization_of_stationaryRenewalGraph (R : StationaryRenewalGraph V)
    (c : E → ℝ) (hc : ∀ x y, R.conductance x y = G.pairConductance c x y) :
    G.IsRealization R.mass c R.rate where
  diag := R.rate_diag
  nonneg := R.rate_nonneg
  stationary := R.stationary
  conductance := hc

/-- **`thm:supp-graph-realization`.**  For positive masses and positive edge
conductances: (R1) the reversible realization `c/m` is stationary with
detailed balance; (R2) every `j ∈ J(G,c)` gives a stationary realization
`(c + j)/m` with strictly positive directed edge rates; (R3) every
stationary realization with masses `m` and conductances `c` is uniquely
`(c + j)/m` with `j` in the closed polytope; (R4) the Hodge–Dirac matrix of
every current realization is that of `(m, c)`; and the open polytope is in
bijection with the positive-edge stationary realizations
(`eq:supp-realization-fibre`). -/
theorem stationary_markov_realization_fibre (hm : ∀ x, 0 < m x) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) :
    (G.IsRealization m c (G.reversibleRates m c) ∧
      ∀ x y, m x * G.reversibleRates m c x y = m y * G.reversibleRates m c y x) ∧
    (∀ j ∈ G.currentPolytope c, G.IsRealization m c (G.rates m c j) ∧
      ∀ e, 0 < G.rates m c j (G.tail e) (G.head e) ∧
        0 < G.rates m c j (G.head e) (G.tail e)) ∧
    (∀ k, G.IsRealization m c k →
      ∃! j, j ∈ G.closedCurrentPolytope c ∧ k = G.rates m c j) ∧
    (∀ j, dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j x y)) =
      dirac m (G.pairConductance c)) ∧
    Nonempty (G.currentPolytope c ≃
      {k : V → V → ℝ // G.IsRealization m c k ∧
        ∀ e, 0 < k (G.tail e) (G.head e) ∧ 0 < k (G.head e) (G.tail e)}) :=
  ⟨G.isRealization_reversibleRates hm c hc,
    fun j hj => ⟨G.isRealization_rates hm c (G.currentPolytope_subset_closed c hj),
      G.rates_pos_of_mem hm c hj⟩,
    fun _ hk => hk.existsUnique_current hm,
    fun j => G.dirac_rates hm c j,
    ⟨G.realizationEquiv hm c⟩⟩

/-! ### `cor:supp-fibre-dimension` -/

/-- Graph connectedness gives the algebraic connectedness criterion of the
cycle projector: the transpose incidence kills only constant potentials. -/
theorem isConnectedIncidence [Nonempty V] (hG : G.Connected) :
    IsConnectedIncidence G.incidence := by
  refine ⟨?_, ?_⟩
  · funext e
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_incidence_apply,
      mul_one]
    simp only [incidence, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      sub_self, Pi.zero_apply]
  · intro x hx
    have hedge : ∀ e, x (G.tail e) = x (G.head e) := by
      intro e
      have h := congrFun hx e
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        star_incidence_apply] at h
      simp only [incidence, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at h
      exact sub_eq_zero.mp h
    have hadj : ∀ a b, G.Adjacent a b → x a = x b := by
      rintro a b ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact hedge e
      · exact (hedge e).symm
    have hconst : ∀ a b, Relation.ReflTransGen G.Adjacent a b → x a = x b := by
      intro a b h
      induction h with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
    obtain ⟨v₀⟩ := ‹Nonempty V›
    refine ⟨x v₀, funext fun v => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact (hconst v₀ v (hG v₀ v)).symm

/-- `dim J(G,c) = |E| - |V| + 1`: the ambient cycle space of the polytope has
dimension the first Betti number. -/
theorem currentPolytope_finrank [Nonempty V] (hG : G.Connected) :
    Module.finrank ℂ (LinearMap.ker G.incidence.mulVecLin) =
      Fintype.card E + 1 - Fintype.card V :=
  cycleKernel_finrank (G.isConnectedIncidence hG)

/-- The reversible realization is the only one exactly when `G` is a tree
(`|E| + 1 = |V|`). -/
theorem currentPolytope_finrank_eq_zero_iff_tree [Nonempty V] (hG : G.Connected) :
    Module.finrank ℂ (LinearMap.ker G.incidence.mulVecLin) = 0 ↔
      Fintype.card E + 1 = Fintype.card V :=
  cycleKernel_finrank_eq_zero_iff_treeCard (G.isConnectedIncidence hG)

/-- A nonzero real kernel vector of the incidence matrix can be scaled into
the open polytope. -/
theorem exists_ne_zero_mem_currentPolytope_of_kernel (c : E → ℝ) (hc : ∀ e, 0 < c e)
    {j₀ : E → ℝ} (hj₀ : G.incidenceReal *ᵥ j₀ = 0) (hne : j₀ ≠ 0) :
    ∃ j ∈ G.currentPolytope c, j ≠ 0 := by
  obtain ⟨e₀, _⟩ := Function.ne_iff.mp hne
  obtain ⟨emin, -, hmin⟩ := Finset.exists_min_image univ c ⟨e₀, Finset.mem_univ e₀⟩
  set M : ℝ := ∑ e, |j₀ e| with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun e _ => abs_nonneg _)
  have hle : ∀ e, |j₀ e| ≤ M := fun e =>
    Finset.single_le_sum (f := fun e => |j₀ e|) (fun e _ => abs_nonneg _) (Finset.mem_univ e)
  have hM1 : M + 1 ≠ 0 := by linarith
  set ε : ℝ := c emin / (M + 1) with hε_def
  have hε : 0 < ε := div_pos (hc emin) (by linarith)
  refine ⟨ε • j₀, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_smul, hj₀, smul_zero]
  · intro e
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hε]
    calc ε * |j₀ e| ≤ ε * M := mul_le_mul_of_nonneg_left (hle e) hε.le
      _ < ε * (M + 1) := mul_lt_mul_of_pos_left (by linarith) hε
      _ = c emin := by rw [hε_def, div_mul_cancel₀ _ hM1]
      _ ≤ c e := hmin e (Finset.mem_univ e)
  · exact smul_ne_zero hε.ne' hne

/-- For a connected graph with `b₁(G) > 0` the open polytope contains a
nonzero current. -/
theorem exists_ne_zero_mem_currentPolytope [Nonempty V] (hG : G.Connected) (c : E → ℝ)
    (hc : ∀ e, 0 < c e) (hb : Fintype.card V < Fintype.card E + 1) :
    ∃ j ∈ G.currentPolytope c, j ≠ 0 := by
  have hdim := G.currentPolytope_finrank hG
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker G.incidence.mulVecLin) := by omega
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hzker : G.incidence *ᵥ (z : E → ℂ) = 0 := by
    have := z.2
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have hre : G.incidenceReal *ᵥ (fun e => ((z : E → ℂ) e).re) = 0 := by
    funext x
    have h := congrArg Complex.re (congrFun hzker x)
    rw [incidence_mulVec_apply, Complex.re_sum] at h
    simp only [Complex.re_ofReal_mul, Pi.zero_apply, Complex.zero_re] at h
    simpa [Matrix.mulVec, dotProduct] using h
  have him : G.incidenceReal *ᵥ (fun e => ((z : E → ℂ) e).im) = 0 := by
    funext x
    have h := congrArg Complex.im (congrFun hzker x)
    rw [incidence_mulVec_apply, Complex.im_sum] at h
    simp only [Complex.im_ofReal_mul, Pi.zero_apply, Complex.zero_im] at h
    simpa [Matrix.mulVec, dotProduct] using h
  by_cases hreZ : (fun e => ((z : E → ℂ) e).re) = 0
  · have himZ : (fun e => ((z : E → ℂ) e).im) ≠ 0 := by
      intro himZ
      apply hz
      apply Subtype.ext
      funext e
      have h1 := congrFun hreZ e
      have h2 := congrFun himZ e
      simp only [Pi.zero_apply] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact G.exists_ne_zero_mem_currentPolytope_of_kernel c hc him himZ
  · exact G.exists_ne_zero_mem_currentPolytope_of_kernel c hc hre hreZ

/-- Non-faithfulness: with `b₁(G) > 0` two distinct stationary realizations
share the same Hodge–Dirac matrix. -/
theorem spectralization_not_faithful [Nonempty V] (hG : G.Connected) (hm : ∀ x, 0 < m x)
    (c : E → ℝ) (hc : ∀ e, 0 < c e) (hb : Fintype.card V < Fintype.card E + 1) :
    ∃ j₁ ∈ G.currentPolytope c, ∃ j₂ ∈ G.currentPolytope c,
      G.rates m c j₁ ≠ G.rates m c j₂ ∧
      dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j₁ x y)) =
        dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j₂ x y)) := by
  obtain ⟨j, hj, hne⟩ := G.exists_ne_zero_mem_currentPolytope hG c hc hb
  refine ⟨j, hj, 0, G.zero_mem_currentPolytope c hc, ?_, ?_⟩
  · intro heq
    exact hne (G.rates_injective hm c heq)
  · rw [G.dirac_rates hm c j, G.dirac_rates hm c 0]

/-- **`cor:supp-fibre-dimension`.**  For connected `G`: the cycle space
carrying `J(G,c)` has dimension `|E| - |V| + 1 = b₁(G)`; the reversible
realization is unique exactly when `G` is a tree; and when `b₁(G) > 0` the
metric spectralization is not faithful (two distinct realizations share the
Hodge–Dirac matrix). -/
theorem fibre_dimension_and_faithfulness [Nonempty V] (hG : G.Connected)
    (hm : ∀ x, 0 < m x) (c : E → ℝ) (hc : ∀ e, 0 < c e) :
    Module.finrank ℂ (LinearMap.ker G.incidence.mulVecLin) =
        Fintype.card E + 1 - Fintype.card V ∧
      (Module.finrank ℂ (LinearMap.ker G.incidence.mulVecLin) = 0 ↔
        Fintype.card E + 1 = Fintype.card V) ∧
      (Fintype.card V < Fintype.card E + 1 →
        ∃ j₁ ∈ G.currentPolytope c, ∃ j₂ ∈ G.currentPolytope c,
          G.rates m c j₁ ≠ G.rates m c j₂ ∧
          dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j₁ x y)) =
            dirac m (symmetrizedConductance (fun x y => m x * G.rates m c j₂ x y))) :=
  ⟨G.currentPolytope_finrank hG, G.currentPolytope_finrank_eq_zero_iff_tree hG,
    fun hb => G.spectralization_not_faithful hG hm c hc hb⟩

end SimpleOrientation

end

end StationaryRenewalGraphFibre
end RenewalGeometry
