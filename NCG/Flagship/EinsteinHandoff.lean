/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# One-sequence Einstein–matter handoff
  (`thm:Einstein-extension-master`, flagship manuscript)

The provable limit-passage core of the handoff:

* `one_sequence_limit`: the compactness/defect skeleton — a
  regulator sequence confined to a compact container whose
  continuous Euler–Lagrange residual is bounded by vanishing
  defects has a subsequence converging to a zero-residual point;
* `lambda_cov_coefficient`: the boxed coefficient identity —
  with `Λ_cov = Λ_H/(2χ)`, the limiting equation reads
  `2χ(G + Λ_cov g) = 2χG + Λ_H g`;
* `noether_on_shell`: the boxed conservation — the off-shell
  Noether identity `∇E + E_A ∂Φ = 0` (diffeomorphism
  invariance, displayed) on the matter shell `E_A = 0` gives
  `∇T = 0` for the on-shell stress tensor;
* `einstein_extension`: the assembly — under (C1)–(C7) rendered
  as the compact container, the vanishing defect envelope, and
  the coefficient convergence, a subsequence converges to a
  limit satisfying `2χ(G_{μν} + Λ_cov g_{μν}) = T_{μν}` and the
  on-shell conservation clause.

Rendering disclosed: the identification of the abstract state
space with the gauge-fixed metric/connection/matter data, the
Sobolev/Rellich origin of the compact container, the
concentration-measure upgrade, and the Gauss–Codazzi
substitution producing the covariant action are the manuscript's
PDE layer (Mathlib has no geometric compactness theory); the
subsequential limit passage, the coefficient identity, and the
on-shell Noether reduction are proved here.  The four continuum
clauses are independently audited by the proved
`thm:ESSC-independence-master`.
-/

namespace NCG

/-- The compactness/defect skeleton: a sequence in a compact
container whose continuous residual is bounded by vanishing
defects has a subsequence converging to a zero-residual
point. -/
theorem one_sequence_limit {X E : Type*} [TopologicalSpace X]
    [FirstCountableTopology X]
    [NormedAddCommGroup E] {K : Set X} (hK : IsCompact K)
    (x : ℕ → X) (hx : ∀ h, x h ∈ K)
    (F : X → E) (hF : ContinuousOn F K)
    (defect : ℕ → ℝ)
    (hd : Filter.Tendsto defect Filter.atTop (nhds 0))
    (hFd : ∀ h, ‖F (x h)‖ ≤ defect h) :
    ∃ (a : X) (φ : ℕ → ℕ), a ∈ K ∧ StrictMono φ
      ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a)
      ∧ F a = 0 := by
  obtain ⟨a, haK, φ, hφ, hconv⟩ := hK.tendsto_subseq hx
  refine ⟨a, φ, haK, hφ, hconv, ?_⟩
  have hFconv : Filter.Tendsto (fun k => F (x (φ k)))
      Filter.atTop (nhds (F a)) :=
    Filter.Tendsto.comp (hF a haK)
      (tendsto_nhdsWithin_iff.mpr
        ⟨hconv, Filter.Eventually.of_forall
          fun k => hx (φ k)⟩)
  have hnorm : Filter.Tendsto (fun k => ‖F (x (φ k))‖)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun k => norm_nonneg _)
      (fun k => hFd (φ k)) ?_
    exact hd.comp hφ.tendsto_atTop
  have hF0 : Filter.Tendsto (fun k => ‖F (x (φ k))‖)
      Filter.atTop (nhds ‖F a‖) := hFconv.norm
  have : ‖F a‖ = 0 := tendsto_nhds_unique hF0 hnorm
  exact norm_eq_zero.mp this

/-- The boxed coefficient identity: with `Λ_cov = Λ_H/(2χ)` the
limiting equation `2χ(G + Λ_cov g) = T` reads
`2χG + Λ_H g = T`. -/
theorem lambda_cov_coefficient {V : Type*} [AddCommGroup V]
    [Module ℝ V] (χ ΛH : ℝ) (hχ : χ ≠ 0) (G g : V) :
    (2 * χ) • (G + (ΛH / (2 * χ)) • g)
      = (2 * χ) • G + ΛH • g := by
  rw [smul_add, smul_smul]
  congr 2
  field_simp

/-- The boxed on-shell conservation: the off-shell Noether
identity `∇E + Σ_A E_A ∂Φ_A = 0` on the matter shell `E_A = 0`
gives `∇E = 0` — for `E = 2χ(G + Λ_cov g) - T` with the Bianchi
and metricity inputs `∇(2χ(G + Λ_cov g)) = 0` this is
`∇T = 0`. -/
theorem noether_on_shell {W : Type*} [AddCommGroup W]
    {A : Type*} [Fintype A]
    (divE : W) (EA : A → W)
    (hnoether : divE + ∑ a, EA a = 0)
    (hshell : ∀ a, EA a = 0) :
    divE = 0 := by
  have hsum : ∑ a, EA a = 0 :=
    Finset.sum_eq_zero fun a _ => hshell a
  rwa [hsum, add_zero] at hnoether

/-- `thm:Einstein-extension-master`: the assembled handoff —
under the compact container (C5)–(C6), the vanishing defect
envelope (C1)–(C4)+(C6), and the coefficient data (C7), a
subsequence of the regulator sequence converges to a limit
whose Einstein–matter residual vanishes:
`2χ(G_{μν} + Λ_cov g_{μν}) = T_{μν}`, and the on-shell Noether
clause holds. -/
theorem einstein_extension {X V : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [NormedAddCommGroup V]
    -- the finite Einstein–matter residual of a state
    (E : X → V)
    -- (C5)–(C6): compact container from the history-Gram and
    -- Sobolev/Rellich margins (displayed)
    {K : Set X} (hK : IsCompact K)
    (x : ℕ → X) (hx : ∀ h, x h ∈ K)
    (hE : ContinuousOn E K)
    -- (C1)–(C4), (C6): the finite stationarity equation holds up
    -- to the defect envelope, and all defects vanish
    (defect : ℕ → ℝ)
    (hd : Filter.Tendsto defect Filter.atTop (nhds 0))
    (hEd : ∀ h, ‖E (x h)‖ ≤ defect h)
    -- (C7): coefficient convergence
    (χ ΛH : ℝ) (hχ : χ ≠ 0)
    -- Noether data at the limit (diffeomorphism invariance,
    -- displayed) and matter shell
    {W : Type*} [AddCommGroup W] {A : Type*} [Fintype A]
    (divT : X → W) (EA : X → A → W)
    (hnoether : ∀ a, divT a + ∑ i, EA a i = 0)
    (hshell : ∀ a i, EA a i = 0) :
    -- subsequential limit with vanishing Einstein–matter
    -- residual
    (∃ (a : X) (φ : ℕ → ℕ), a ∈ K ∧ StrictMono φ
      ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds a)
      ∧ E a = 0)
    -- the boxed coefficient identity
    ∧ (∀ G g : Matrix (Fin 4) (Fin 4) ℝ,
        (2 * χ) • (G + (ΛH / (2 * χ)) • g)
          = (2 * χ) • G + ΛH • g)
    -- the boxed on-shell conservation
    ∧ (∀ a : X, divT a = 0) :=
  ⟨one_sequence_limit hK x hx E hE defect hd hEd,
    fun G g => lambda_cov_coefficient χ ΛH hχ G g,
    fun a => noether_on_shell (divT a) (EA a)
      (hnoether a) (hshell a)⟩

end NCG
