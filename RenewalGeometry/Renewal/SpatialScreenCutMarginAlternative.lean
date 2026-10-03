/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Renewal.EfficientCutConstantScreen

/-!
# Cut margin and compact-screen alternative (`thm:main-spatial-screen`,
  emergent-spacetime manuscript)

Assembles the two branches of `thm:main-spatial-screen` from the paper's own hypotheses
(volume bound `μ(V) ≤ V_*`, weighted degree bound, capacity–conductance comparison
`a₋ h c ≤ u ≤ a₊ h c` of `eq:main-capacity-conductance`, and the EFFICIENT cut margin):

* spectral identities for the canonical weighted spectrum: `energy_eq_sum_eigenvalue_mul_sq`
  (`𝓔(f) = Σ_j λ_j ĉ_j²`), `spectralLowPart_add_spectralHighPart`
  (`f = P_R f + (I - P_R) f`, `P_R = 1_{[0,R]}(Δ)`), `weightedL2_spectralHighPart`
  (`‖(I - P_R) f‖²_{L²(μ)} = Σ_{λ_j > R} ĉ_j²`) and `screenTail_L2`
  (`‖(I - P_R) f‖²_{L²(μ)} ≤ R⁻¹ 𝓔(f)`, `eq:main-screen-tail` in its stated form);
* `spatialScreen_positiveBranch`: under the hypotheses with `I^eff ≥ I_*^eff > 0`, the spatial
  cut constant satisfies `a₋ I^sp ≤ I^eff ≤ a₊ I^sp` and `I^sp ≥ I_*^eff/a₊ > 0`, and the
  Sobolev, Poincaré, Weyl-count and `L²` screen-tail bounds hold with the cutoff-independent
  constants `C_S = 128 D/(I_*^eff/a₊)²`, `C_P = V_*^{2/3} C_S` (via
  `renewalSpatialPositiveScreen_of_efficientCut`);
* `spatialScreen_neckBranch`: along a sequence of regulators with `0 < I^eff_j → 0`, the
  minimizing cuts give normalized potentials of total `u`-variation `1` pairing with the cut
  demand to `(I^eff_j)⁻¹ → ∞` (`eq:main-neck-obstruction`);
* `zeroCapacity_cut_of_efficientCutConstant_eq_zero`: if `I^eff = 0` at finite cutoff, a
  minimizing half-volume cut has zero capacity (the disconnected-support cut retained
  directly).
-/

open scoped BigOperators Topology

noncomputable section

namespace RenewalGeometry
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : FiniteWeightedGraph V)

/-! ### Spectral identities -/

omit [Nonempty V] in
theorem eigenvector_eq_sqrt_mul_eigenfunction (j v : V) :
    G.eigenvector j v = Real.sqrt (G.mass v) * G.eigenfunction j v := by
  unfold eigenfunction
  have hs : Real.sqrt (G.mass v) ≠ 0 := (Real.sqrt_pos.2 (G.mass_pos v)).ne'
  field_simp

/-- Spectral energy identity: `𝓔(f) = Σ_j λ_j ĉ_j(f)²`. -/
theorem energy_eq_sum_eigenvalue_mul_sq (f : V → ℝ) :
    finiteSpatialEnergy G.conductance f =
      ∑ j, G.eigenvalue j * G.spectralCoefficient f j ^ 2 := by
  set x : V → ℝ := fun v => Real.sqrt (G.mass v) * f v with hx
  have hxf : (fun v => x v / Real.sqrt (G.mass v)) = f := by
    funext v
    have hs : Real.sqrt (G.mass v) ≠ 0 := (Real.sqrt_pos.2 (G.mass_pos v)).ne'
    simp only [hx]
    field_simp
  have hq := G.symmetricLaplacian_quadraticForm x
  rw [hxf] at hq
  have hexp : (∑ j, G.spectralCoefficient f j • G.eigenvector j) = x := by
    funext v
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, G.eigenvector_eq_sqrt_mul_eigenfunction]
    have := G.spectralExpansion f v
    rw [hx]
    simp only
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have he := G.symmetricLaplacian_quadraticForm_eigenExpansion (G.spectralCoefficient f)
  rw [hexp] at he
  rw [← hq, he]

/-- The low spectral part `P_R f = Σ_{λ_j ≤ R} ĉ_j φ_j`, `P_R = 1_{[0,R]}(Δ)`. -/
def spectralLowPart (R : ℝ) (f : V → ℝ) (u : V) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬ R < G.eigenvalue j),
    G.spectralCoefficient f j * G.eigenfunction j u

/-- The high spectral part `(I - P_R) f = Σ_{λ_j > R} ĉ_j φ_j`. -/
def spectralHighPart (R : ℝ) (f : V → ℝ) (u : V) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
    G.spectralCoefficient f j * G.eigenfunction j u

theorem spectralLowPart_add_spectralHighPart (R : ℝ) (f : V → ℝ) (u : V) :
    G.spectralLowPart R f u + G.spectralHighPart R f u = f u := by
  unfold spectralLowPart spectralHighPart
  rw [add_comm, Finset.sum_filter_add_sum_filter_not, G.spectralExpansion f u]

omit [Nonempty V] in
/-- `‖(I - P_R) f‖²_{L²(μ)} = Σ_{λ_j > R} ĉ_j²` (weighted orthonormality). -/
theorem weightedL2_spectralHighPart (R : ℝ) (f : V → ℝ) :
    ∑ v, G.mass v * G.spectralHighPart R f v ^ 2 =
      ∑ j ∈ Finset.univ.filter (fun j => R < G.eigenvalue j),
        G.spectralCoefficient f j ^ 2 := by
  set S := Finset.univ.filter (fun j => R < G.eigenvalue j)
  set a := G.spectralCoefficient f
  unfold spectralHighPart
  calc ∑ v, G.mass v * (∑ j ∈ S, a j * G.eigenfunction j v) ^ 2
      = ∑ v, ∑ j ∈ S, ∑ k ∈ S,
          a j * a k * (G.mass v * G.eigenfunction j v * G.eigenfunction k v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ j ∈ S, ∑ k ∈ S,
          a j * a k * ∑ v, G.mass v * G.eigenfunction j v * G.eigenfunction k v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j ∈ S, a j ^ 2 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp_rw [G.eigenfunction_weighted_orthonormal]
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq S j, if_pos hj, sq]

/-- `eq:main-screen-tail`: `‖(I - P_R) f‖²_{L²(μ)} ≤ R⁻¹ 𝓔(f)`. -/
theorem screenTail_L2 (f : V → ℝ) (R : ℝ) (hR : 0 < R) :
    ∑ v, G.mass v * G.spectralHighPart R f v ^ 2 ≤
      R⁻¹ * finiteSpatialEnergy G.conductance f := by
  rw [G.weightedL2_spectralHighPart, G.energy_eq_sum_eigenvalue_mul_sq]
  exact G.eigenfunction_spectralTail_bound f R hR

/-! ### The positive branch -/

/-- **`thm:main-spatial-screen`, positive branch.**  Under `μ(V) ≤ V_*`, the weighted degree
bound `h² Σ_u c_uv ≤ D m_v` (i.e. `Σ_u c_uv ≤ D h⁻² m_v`), the capacity–conductance comparison
`a₋ h c ≤ u ≤ a₊ h c` and `I^eff ≥ I_*^eff > 0`: the cut constants compare as
`a₋ I^sp ≤ I^eff ≤ a₊ I^sp`, `I^sp ≥ I_*^sp := I_*^eff/a₊ > 0`, and every mean-zero `f` obeys
the `L⁶` Sobolev bound with `C_S = 128 D / (I_*^sp)²` (in the form `‖f‖₆⁶ ≤ (C_S 𝓔(f))³`), the
Poincaré bound with `C_P = V_*^{2/3} C_S`; the counting function obeys
`N(R) ≤ 1 + 4 e^{3/2} V_* (C_S R)^{3/2}`; and the spectral screens obey
`‖(I - P_R) f‖²_{L²(μ)} ≤ R⁻¹ 𝓔(f)`.  All constants depend only on `D, V_*, I_*^eff, a₊`. -/
theorem spatialScreen_positiveBranch (u : V → V → ℝ)
    (D h Vstar aminus aplus Istar : ℝ)
    (hD : 0 < D) (hh : 0 < h) (hVstar : 0 < Vstar)
    (haminus : 0 ≤ aminus) (haplus : 0 < aplus)
    (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ x, G.conductance x v) ≤ D * G.mass v)
    (hlow : ∀ x y, aminus * (h * G.conductance x y) ≤ u x y)
    (hup : ∀ x y, u x y ≤ aplus * (h * G.conductance x y))
    (hIstar : 0 < Istar) (hI : Istar ≤ G.efficientCutConstant u) :
    (aminus * G.spatialCutConstant h ≤ G.efficientCutConstant u ∧
      G.efficientCutConstant u ≤ aplus * G.spatialCutConstant h) ∧
    0 < Istar / aplus ∧ Istar / aplus ≤ G.spatialCutConstant h ∧
    (∀ f : V → ℝ, (∑ v, G.mass v * f v = 0) →
      ∑ v, G.mass v * f v ^ 6 ≤
        ((128 * D / (Istar / aplus) ^ 2) * finiteSpatialEnergy G.conductance f) ^ 3) ∧
    (∀ f : V → ℝ, (∑ v, G.mass v * f v = 0) →
      ∑ v, G.mass v * f v ^ 2 ≤
        (128 * D * Vstar ^ ((2 : ℝ) / 3) / (Istar / aplus) ^ 2) *
          finiteSpatialEnergy G.conductance f) ∧
    (∀ R, 0 < R → (finiteEigenvalueCount G.eigenvalue R : ℝ) ≤
      1 + 4 * Real.exp (3 / 2) * Vstar * ((128 * D / (Istar / aplus) ^ 2) * R) ^ ((3 : ℝ) / 2)) ∧
    (∀ (f : V → ℝ) (R : ℝ), 0 < R →
      ∑ v, G.mass v * G.spectralHighPart R f v ^ 2 ≤
        R⁻¹ * finiteSpatialEnergy G.conductance f) := by
  obtain ⟨hpos, hsp, S, hCP, -⟩ := G.renewalSpatialPositiveScreen_of_efficientCut u D h Vstar
    aminus aplus Istar hD hh hVstar haminus haplus hvolume hdegree hlow hup hIstar hI
  refine ⟨G.cutConstant_comparison u h aminus aplus hh.le haminus hlow hup, hpos, hsp,
    S.sobolev, fun f hf => ?_, S.counting, fun f R hR => G.screenTail_L2 f R hR⟩
  rw [← hCP]
  exact S.poincare f hf

/-! ### Zero-capacity cuts -/

omit [Nonempty V] in
/-- If the efficient cut constant vanishes at finite cutoff, a minimizing half-volume cut has
zero efficient capacity (a disconnected-support cut, retained directly). -/
theorem zeroCapacity_cut_of_efficientCutConstant_eq_zero (u : V → V → ℝ)
    (hne : ∃ A, G.IsHalfVolumeCut A) (h0 : G.efficientCutConstant u = 0) :
    ∃ A, G.IsHalfVolumeCut A ∧ finiteCutCapacity u A = 0 := by
  obtain ⟨A, hA, hAeq⟩ := G.exists_minimizing_cut u hne
  refine ⟨A, hA, ?_⟩
  have hratio : G.cutRatio u A = 0 := by rw [hAeq]; exact h0
  unfold cutRatio at hratio
  have hpos : 0 < G.setMass A ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hA.1 _
  rcases div_eq_zero_iff.mp hratio with h | h
  · exact h
  · exact absurd h hpos.ne'

end FiniteWeightedGraph

/-! ### The collapsing branch -/

/-- **`thm:main-spatial-screen`, neck branch** (`eq:main-neck-obstruction`).  Along a
sequence of regulators with symmetric nonnegative efficient capacities, half-volume cuts, and
`0 < I^eff_j → 0`, minimizing cuts `A_j` exist whose normalized potentials `φ_j` have total
`u`-variation `1` and pair with the cut demand to `(I^eff_j)⁻¹`, which tends to `+∞`. -/
theorem spatialScreen_neckBranch {V : ℕ → Type*} [∀ j, Fintype (V j)] [∀ j, Nonempty (V j)]
    [∀ j, DecidableEq (V j)] (G : ∀ j, FiniteWeightedGraph (V j))
    (u : ∀ j, V j → V j → ℝ) (hsym : ∀ j x y, u j x y = u j y x)
    (hu : ∀ j x y, 0 ≤ u j x y) (hne : ∀ j, ∃ A, (G j).IsHalfVolumeCut A)
    (hpos : ∀ j, 0 < (G j).efficientCutConstant (u j))
    (hzero : Filter.Tendsto (fun j => (G j).efficientCutConstant (u j)) Filter.atTop (𝓝 0)) :
    ∃ A : ∀ j, Finset (V j),
      (∀ j, (G j).IsHalfVolumeCut (A j) ∧ 0 < finiteCutCapacity (u j) (A j) ∧
        (1 / 2) * ∑ x, ∑ y, u j x y *
          |FiniteWeightedGraph.neckPotential (u j) (A j) x -
            FiniteWeightedGraph.neckPotential (u j) (A j) y| = 1 ∧
        |∑ v, (G j).cutDemand (A j) v * FiniteWeightedGraph.neckPotential (u j) (A j) v| =
          ((G j).efficientCutConstant (u j))⁻¹) ∧
      Filter.Tendsto (fun j => |∑ v, (G j).cutDemand (A j) v *
        FiniteWeightedGraph.neckPotential (u j) (A j) v|) Filter.atTop Filter.atTop := by
  have h := fun j => (G j).neck_witness_of_minimizing_cut (u j) (hsym j) (hu j) (hne j) (hpos j)
  choose A hA using h
  refine ⟨A, hA, ?_⟩
  have heq : (fun j => |∑ v, (G j).cutDemand (A j) v *
      FiniteWeightedGraph.neckPotential (u j) (A j) v|) =
      fun j => ((G j).efficientCutConstant (u j))⁻¹ := funext fun j => (hA j).2.2.2
  rw [heq]
  exact tendsto_inv_atTop_of_tendsto_zero _ (Filter.Eventually.of_forall hpos) hzero

/-! ### Non-vacuity: the two-point regulator -/

namespace SpatialScreenTwoPoint

/-- The two-point regulator with unit masses and conductance `ε` between the two points. -/
def twoPoint (ε : ℝ) (hε : 0 ≤ ε) : FiniteWeightedGraph (Fin 2) where
  mass := fun _ => 1
  conductance := fun x y => if x = y then 0 else ε
  mass_pos := fun _ => one_pos
  conductance_nonneg := fun x y => by split_ifs <;> linarith
  conductance_symm := fun x y => by
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h]

theorem finset_fin_two (A : Finset (Fin 2)) :
    A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Finset.univ := by
  revert A; decide

/-- The efficient cut constant of the two-point regulator with `u = c` is `ε`. -/
theorem efficientCutConstant_twoPoint (ε : ℝ) (hε : 0 ≤ ε) :
    (twoPoint ε hε).efficientCutConstant (twoPoint ε hε).conductance = ε := by
  set G := twoPoint ε hε
  have hcut : ∀ A, G.IsHalfVolumeCut A → G.cutRatio G.conductance A = ε := by
    intro A hA
    obtain ⟨h1, h2⟩ := hA
    rcases finset_fin_two A with rfl | rfl | rfl | rfl
    · simp [FiniteWeightedGraph.setMass] at h1
    · simp [FiniteWeightedGraph.cutRatio, FiniteWeightedGraph.setMass, finiteCutCapacity, G,
        twoPoint, show ({0} : Finset (Fin 2))ᶜ = {1} from by decide]
    · simp [FiniteWeightedGraph.cutRatio, FiniteWeightedGraph.setMass, finiteCutCapacity, G,
        twoPoint, show ({1} : Finset (Fin 2))ᶜ = {0} from by decide]
    · simp [FiniteWeightedGraph.setMass, FiniteWeightedGraph.volume, G, twoPoint] at h2
  have h0 : G.IsHalfVolumeCut {0} := by
    constructor <;> simp [FiniteWeightedGraph.setMass, FiniteWeightedGraph.volume, G, twoPoint]
  apply le_antisymm
  · calc G.efficientCutConstant G.conductance ≤ G.cutRatio G.conductance {0} :=
          G.cutConstant_le_cutRatio _ G.conductance_nonneg h0
      _ = ε := hcut _ h0
  · unfold FiniteWeightedGraph.efficientCutConstant FiniteWeightedGraph.cutConstant
    refine le_csInf ⟨_, ⟨{0}, h0, rfl⟩⟩ ?_
    rintro r ⟨A, hA, rfl⟩
    exact (hcut A hA).ge

/-- Non-vacuity of the positive branch: the unit two-point regulator satisfies every hypothesis
(`V_* = 2`, `D = 1`, `h = 1`, `a₋ = a₊ = 1`, `u = c`, `I_*^eff = 1`). -/
example : ∀ f : Fin 2 → ℝ, ∀ R : ℝ, 0 < R →
    ∑ v, (twoPoint 1 zero_le_one).mass v *
        (twoPoint 1 zero_le_one).spectralHighPart R f v ^ 2 ≤
      R⁻¹ * finiteSpatialEnergy (twoPoint 1 zero_le_one).conductance f := by
  have h := (twoPoint 1 zero_le_one).spatialScreen_positiveBranch
    (twoPoint 1 zero_le_one).conductance 1 1 2 1 1 1 one_pos one_pos two_pos zero_le_one one_pos
    (by simp [FiniteWeightedGraph.volume, twoPoint])
    (fun v => by
      fin_cases v <;> simp [twoPoint, Fin.sum_univ_two])
    (fun x y => by simp) (fun x y => by simp) one_pos
    (by rw [efficientCutConstant_twoPoint])
  exact h.2.2.2.2.2.2

/-- Non-vacuity of the neck branch: the two-point regulators with conductance `1/(j+1)`. -/
example : ∃ A : ∀ _ : ℕ, Finset (Fin 2), Filter.Tendsto (fun j : ℕ =>
    |∑ v, (twoPoint (1 / ((j : ℝ) + 1)) (by positivity)).cutDemand (A j) v *
      FiniteWeightedGraph.neckPotential
        (twoPoint (1 / ((j : ℝ) + 1)) (by positivity)).conductance (A j) v|)
      Filter.atTop Filter.atTop := by
  obtain ⟨A, -, hA⟩ := spatialScreen_neckBranch (V := fun _ => Fin 2)
    (fun j => twoPoint (1 / ((j : ℝ) + 1)) (by positivity))
    (fun j => (twoPoint (1 / ((j : ℝ) + 1)) (by positivity)).conductance)
    (fun j => (twoPoint _ _).conductance_symm) (fun j => (twoPoint _ _).conductance_nonneg)
    (fun j => ⟨{0}, by
      constructor <;> simp [FiniteWeightedGraph.setMass, FiniteWeightedGraph.volume, twoPoint]⟩)
    (fun j => by rw [efficientCutConstant_twoPoint]; positivity)
    (by
      simp only [efficientCutConstant_twoPoint]
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
  exact ⟨A, hA⟩

end SpatialScreenTwoPoint

end RenewalGeometry
