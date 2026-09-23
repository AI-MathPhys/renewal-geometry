/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Renewal.RenewalSpatialPositiveScreen

/-!
# Operational Sobolev, Poincaré and compact-screen bounds from the efficient
  cut constant (`thm:supp-spatial-screen`, `thm:main-spatial-screen`,
  `eq:main-cut-constant`, `eq:main-cut-comparison`, `eq:main-cut-demand`,
  `eq:main-neck-obstruction`; emergent-spacetime manuscript)

On a finite weighted graph `G` (masses `m_v`, symmetric conductances `c_uv`)
with cell scale `h` and efficient capacities `u_uv`:

* `cutConstant w` is the cut constant `min_{0 < μ(A) ≤ μ(V)/2} w(∂A)/μ(A)^{2/3}`
  of `eq:main-cut-constant` for the edge weights `w`; `efficientCutConstant u`
  (`I^eff`) and `spatialCutConstant h` (`I^sp`, weights `h c`) are its two
  instances.
* `cutConstant_comparison`: the capacity–conductance comparison
  `a₋ h c ≤ u ≤ a₊ h c` (`eq:main-capacity-conductance`) gives
  `a₋ I^sp ≤ I^eff ≤ a₊ I^sp` (`eq:main-cut-comparison`).
* `spatialCutMargin_of_efficientCut`: `I^eff ≥ I_* > 0` yields the spatial
  cut margin `I^sp ≥ I_*/a₊` (`eq:supp-cut-isoperimetry`) in the form used by
  the finite Sobolev–Weyl theorem.
* `renewalSpatialPositiveScreen_of_efficientCut` (**the theorem**): under
  `μ(V) ≤ V_*`, the weighted degree bound `eq:supp-weighted-degree`, the
  comparison and `I^eff ≥ I_* > 0`, the graph carries the complete
  `RenewalSpatialPositiveScreen` package with constant `I_*/a₊`: the
  `L⁶` Sobolev and Poincaré bounds `eq:supp-sobolev`/`eq:supp-poincare`,
  the positive spectral floor, the Weyl counting law
  `eq:supp-global-weyl-count`, and the spectral screen tail
  `eq:supp-screen-count-tail` (`tail` field: the spectral mass above `R` is
  bounded by `R⁻¹ 𝓔(f)`).
* Neck obstruction (`neck_witness`, `neck_witness_of_minimizing_cut`,
  `tendsto_inv_atTop_of_tendsto_zero`): for a half-volume cut `A` of positive
  capacity the potential `φ = 1_A / u(∂A)` has total `u`-variation `1` and
  pairs with the mean-zero demand `b_A` of `eq:main-cut-demand` to
  `μ(A)^{2/3}/u(∂A)`; for a minimizing cut this is `(I^eff)⁻¹`, which tends
  to `+∞` along any family with `I^eff → 0⁺` (`eq:main-neck-obstruction`).
-/

open scoped BigOperators Topology

noncomputable section

namespace RenewalGeometry
namespace FiniteWeightedGraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : FiniteWeightedGraph V)

/-! ### Cut constants -/

/-- Mass `μ(A)` of a vertex set. -/
def setMass (A : Finset V) : ℝ := ∑ v ∈ A, G.mass v

omit [Nonempty V] [DecidableEq V] in
theorem setMass_nonneg (A : Finset V) : 0 ≤ G.setMass A :=
  Finset.sum_nonneg fun v _ => (G.mass_pos v).le

omit [Nonempty V] in
theorem setMass_compl (A : Finset V) : G.setMass Aᶜ = G.volume - G.setMass A := by
  unfold setMass volume
  rw [← Finset.sum_add_sum_compl A]
  ring

/-- A half-volume cut: `0 < μ(A) ≤ μ(V)/2`. -/
def IsHalfVolumeCut (A : Finset V) : Prop :=
  0 < G.setMass A ∧ G.setMass A ≤ G.volume / 2

/-- Normalized cut ratio `w(∂A)/μ(A)^{2/3}` for edge weights `w`. -/
def cutRatio (w : V → V → ℝ) (A : Finset V) : ℝ :=
  finiteCutCapacity w A / G.setMass A ^ ((2 : ℝ) / 3)

/-- The cut constant `min_{0 < μ(A) ≤ μ(V)/2} w(∂A)/μ(A)^{2/3}` of
`eq:main-cut-constant` (as an infimum over the finite family of half-volume
cuts; `0` if there is none). -/
def cutConstant (w : V → V → ℝ) : ℝ :=
  sInf ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A})

/-- The efficient cut constant `I^eff` (weights: efficient capacities `u`). -/
def efficientCutConstant (u : V → V → ℝ) : ℝ := G.cutConstant u

/-- The analytic spatial cut constant `I^sp` (weights `h c`). -/
def spatialCutConstant (h : ℝ) : ℝ :=
  G.cutConstant fun x y => h * G.conductance x y

omit [Nonempty V] in
theorem finiteCutCapacity_nonneg (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    (A : Finset V) : 0 ≤ finiteCutCapacity w A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hw _ _

omit [Nonempty V] in
/-- The cut capacity of a symmetric weight is complement-invariant. -/
theorem finiteCutCapacity_compl (w : V → V → ℝ) (hsym : ∀ x y, w x y = w y x)
    (A : Finset V) : finiteCutCapacity w Aᶜ = finiteCutCapacity w A := by
  unfold finiteCutCapacity
  rw [compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsym y x

omit [Nonempty V] in
theorem cutRatio_nonneg (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y) (A : Finset V) :
    0 ≤ G.cutRatio w A :=
  div_nonneg (finiteCutCapacity_nonneg w hw A)
    (Real.rpow_nonneg (G.setMass_nonneg A) _)

omit [Nonempty V] in
theorem cutRatio_mono {w w' : V → V → ℝ} (hle : ∀ x y, w x y ≤ w' x y)
    (A : Finset V) : G.cutRatio w A ≤ G.cutRatio w' A := by
  unfold cutRatio
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (G.setMass_nonneg A) _)
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hle _ _

omit [Nonempty V] in
theorem cutRatio_smul (a : ℝ) (w : V → V → ℝ) (A : Finset V) :
    G.cutRatio (fun x y => a * w x y) A = a * G.cutRatio w A := by
  unfold cutRatio finiteCutCapacity
  simp only [← Finset.mul_sum]
  ring

theorem bddBelow_cutRatio_image (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y) :
    BddBelow ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A}) := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, _, rfl⟩
  exact G.cutRatio_nonneg w hw A

theorem cutConstant_nonneg (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y) :
    0 ≤ G.cutConstant w := by
  unfold cutConstant
  rcases ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A}).eq_empty_or_nonempty
    with hempty | hne
  · rw [hempty, Real.sInf_empty]
  · exact le_csInf hne (by rintro r ⟨A, _, rfl⟩; exact G.cutRatio_nonneg w hw A)

/-- The cut constant is a lower bound for every half-volume cut ratio. -/
theorem cutConstant_le_cutRatio (w : V → V → ℝ) (hw : ∀ x y, 0 ≤ w x y)
    {A : Finset V} (hA : G.IsHalfVolumeCut A) :
    G.cutConstant w ≤ G.cutRatio w A :=
  csInf_le (G.bddBelow_cutRatio_image w hw) ⟨A, hA, rfl⟩

omit [Nonempty V] in
/-- The cut constant is attained by a minimizing half-volume cut. -/
theorem exists_minimizing_cut (w : V → V → ℝ)
    (hne : ∃ A, G.IsHalfVolumeCut A) :
    ∃ A, G.IsHalfVolumeCut A ∧ G.cutRatio w A = G.cutConstant w := by
  obtain ⟨A₀, hA₀⟩ := hne
  have hfin : ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A}).Finite :=
    Set.toFinite _
  have hne' : ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A}).Nonempty :=
    ⟨_, ⟨A₀, hA₀, rfl⟩⟩
  have hmem := Set.Nonempty.csInf_mem hne' hfin
  obtain ⟨A, hA, hAeq⟩ := hmem
  exact ⟨A, hA, hAeq⟩

omit [Nonempty V] in
/-- If the half-volume family is empty, the cut constant is `0`. -/
theorem cutConstant_eq_zero_of_empty (w : V → V → ℝ)
    (hempty : ¬ ∃ A, G.IsHalfVolumeCut A) : G.cutConstant w = 0 := by
  unfold cutConstant
  have : ((fun A => G.cutRatio w A) '' {A | G.IsHalfVolumeCut A}) = ∅ := by
    rw [Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro A hA
    exact hempty ⟨A, hA⟩
  rw [this, Real.sInf_empty]

/-- Upper comparison: `w ≤ a w'` edgewise gives `I(w) ≤ a I(w')`. -/
theorem cutConstant_le_mul {w w' : V → V → ℝ} (a : ℝ)
    (hw : ∀ x y, 0 ≤ w x y)
    (hle : ∀ x y, w x y ≤ a * w' x y) :
    G.cutConstant w ≤ a * G.cutConstant w' := by
  by_cases hne : ∃ A, G.IsHalfVolumeCut A
  · obtain ⟨A, hA, hAeq⟩ := G.exists_minimizing_cut w' hne
    calc G.cutConstant w ≤ G.cutRatio w A := G.cutConstant_le_cutRatio w hw hA
      _ ≤ G.cutRatio (fun x y => a * w' x y) A := G.cutRatio_mono hle A
      _ = a * G.cutRatio w' A := G.cutRatio_smul a w' A
      _ = a * G.cutConstant w' := by rw [hAeq]
  · rw [G.cutConstant_eq_zero_of_empty w hne, G.cutConstant_eq_zero_of_empty w' hne]
    simp

/-- Lower comparison: `a w' ≤ w` edgewise gives `a I(w') ≤ I(w)`. -/
theorem mul_cutConstant_le {w w' : V → V → ℝ} (a : ℝ) (ha : 0 ≤ a)
    (hw' : ∀ x y, 0 ≤ w' x y)
    (hle : ∀ x y, a * w' x y ≤ w x y) :
    a * G.cutConstant w' ≤ G.cutConstant w := by
  by_cases hne : ∃ A, G.IsHalfVolumeCut A
  · obtain ⟨A₀, hA₀⟩ := hne
    unfold cutConstant
    refine le_csInf ⟨_, ⟨A₀, hA₀, rfl⟩⟩ ?_
    rintro r ⟨A, hA, rfl⟩
    calc a * G.cutConstant w' ≤ a * G.cutRatio w' A :=
          mul_le_mul_of_nonneg_left (G.cutConstant_le_cutRatio w' hw' hA) ha
      _ = G.cutRatio (fun x y => a * w' x y) A := (G.cutRatio_smul a w' A).symm
      _ ≤ G.cutRatio w A := G.cutRatio_mono hle A
  · rw [G.cutConstant_eq_zero_of_empty w hne, G.cutConstant_eq_zero_of_empty w' hne]
    simp

/-- `eq:main-cut-comparison`: the capacity–conductance comparison
`a₋ h c ≤ u ≤ a₊ h c` gives `a₋ I^sp ≤ I^eff ≤ a₊ I^sp`. -/
theorem cutConstant_comparison (u : V → V → ℝ) (h aminus aplus : ℝ)
    (hh : 0 ≤ h) (haminus : 0 ≤ aminus)
    (hlow : ∀ x y, aminus * (h * G.conductance x y) ≤ u x y)
    (hup : ∀ x y, u x y ≤ aplus * (h * G.conductance x y)) :
    aminus * G.spatialCutConstant h ≤ G.efficientCutConstant u ∧
      G.efficientCutConstant u ≤ aplus * G.spatialCutConstant h := by
  have hhc : ∀ x y, 0 ≤ h * G.conductance x y := fun x y =>
    mul_nonneg hh (G.conductance_nonneg x y)
  have hu : ∀ x y, 0 ≤ u x y := fun x y =>
    le_trans (mul_nonneg haminus (hhc x y)) (hlow x y)
  exact ⟨G.mul_cutConstant_le aminus haminus hhc hlow,
    G.cutConstant_le_mul aplus hu hup⟩

/-! ### From the efficient margin to the spatial cut margin -/

/-- A positive lower bound `I` on the spatial cut constant is exactly the
`SpatialCutMargin` (`eq:supp-cut-isoperimetry`) with constant `I`: for every
cut `A`, `I · min(μ(A), μ(Aᶜ))^{2/3} ≤ h c(∂A)`. -/
def spatialCutMargin_of_le (h I : ℝ) (hh : 0 ≤ h) (hI : 0 < I)
    (hle : I ≤ G.spatialCutConstant h) : G.SpatialCutMargin h where
  constant := I
  constant_pos := hI
  cut := by
    intro A
    have hhc : ∀ x y, 0 ≤ h * G.conductance x y := fun x y =>
      mul_nonneg hh (G.conductance_nonneg x y)
    have hcap : h * finiteCutCapacity G.conductance A =
        finiteCutCapacity (fun x y => h * G.conductance x y) A := by
      unfold finiteCutCapacity
      simp only [Finset.mul_sum]
    have hcapnn : 0 ≤ h * finiteCutCapacity G.conductance A := by
      rw [hcap]
      exact finiteCutCapacity_nonneg _ hhc A
    change I * min (G.setMass A) (G.setMass Aᶜ) ^ ((2 : ℝ) / 3) ≤
      h * finiteCutCapacity G.conductance A
    -- the key inequality for a half-volume cut `B`
    have key : ∀ B : Finset V, G.IsHalfVolumeCut B →
        I * G.setMass B ^ ((2 : ℝ) / 3) ≤
          finiteCutCapacity (fun x y => h * G.conductance x y) B := by
      intro B hB
      have h1 : I ≤ G.cutRatio (fun x y => h * G.conductance x y) B :=
        le_trans hle (G.cutConstant_le_cutRatio _ hhc hB)
      have hpos : 0 < G.setMass B ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hB.1 _
      unfold cutRatio at h1
      rwa [le_div_iff₀ hpos] at h1
    have hA0 : 0 ≤ G.setMass A := G.setMass_nonneg A
    have hAc0 : 0 ≤ G.setMass Aᶜ := G.setMass_nonneg Aᶜ
    have hcompl := G.setMass_compl A
    by_cases hmin : min (G.setMass A) (G.setMass Aᶜ) = 0
    · rw [hmin, Real.zero_rpow (by norm_num), mul_zero]
      exact hcapnn
    have hminpos : 0 < min (G.setMass A) (G.setMass Aᶜ) :=
      lt_of_le_of_ne (le_min hA0 hAc0) (Ne.symm hmin)
    by_cases hhalf : G.setMass A ≤ G.volume / 2
    · -- `A` itself is a half-volume cut
      have hApos : 0 < G.setMass A := lt_of_lt_of_le hminpos (min_le_left _ _)
      have hmin' : min (G.setMass A) (G.setMass Aᶜ) = G.setMass A := by
        apply min_eq_left
        rw [hcompl]
        linarith
      rw [hmin', hcap]
      exact key A ⟨hApos, hhalf⟩
    · -- the complement is a half-volume cut
      rw [not_le] at hhalf
      have hAcpos : 0 < G.setMass Aᶜ := lt_of_lt_of_le hminpos (min_le_right _ _)
      have hAchalf : G.setMass Aᶜ ≤ G.volume / 2 := by
        rw [hcompl]
        linarith
      have hmin' : min (G.setMass A) (G.setMass Aᶜ) = G.setMass Aᶜ := by
        apply min_eq_right
        rw [hcompl]
        linarith
      rw [hmin', hcap, ← finiteCutCapacity_compl _
        (fun x y => by rw [G.conductance_symm x y]) A]
      exact key Aᶜ ⟨hAcpos, hAchalf⟩

/-- `I^eff ≥ I_* > 0` and the upper comparison `u ≤ a₊ h c` give
`I^sp ≥ I_*/a₊` (`I^sp_* := I^eff_*/a₊ > 0`). -/
theorem spatialCutConstant_ge_of_efficient (u : V → V → ℝ) (h aplus Istar : ℝ)
    (hh : 0 ≤ h) (haplus : 0 < aplus) (hu : ∀ x y, 0 ≤ u x y)
    (hup : ∀ x y, u x y ≤ aplus * (h * G.conductance x y))
    (hI : Istar ≤ G.efficientCutConstant u) :
    Istar / aplus ≤ G.spatialCutConstant h := by
  have hhc : ∀ x y, 0 ≤ h * G.conductance x y := fun x y =>
    mul_nonneg hh (G.conductance_nonneg x y)
  have := G.cutConstant_le_mul aplus hu hup
  rw [div_le_iff₀ haplus, mul_comm]
  exact le_trans hI this

/-- **`thm:supp-spatial-screen`.**  Under `μ(V) ≤ V_*`, the weighted degree
bound `h² Σ_u c_uv ≤ D m_v` (`eq:supp-weighted-degree`), the
capacity–conductance comparison `a₋ h c ≤ u ≤ a₊ h c`
(`eq:main-capacity-conductance`) and `I^eff ≥ I_* > 0`, the spatial cut
constant satisfies `I^sp ≥ I_*/a₊ > 0` and the graph carries the full
`RenewalSpatialPositiveScreen` package with constant `I_*/a₊`: the `L⁶`
Sobolev bound `eq:supp-sobolev` (with `C_S = 128 D/(I_*/a₊)²`), the Poincaré
bound `eq:supp-poincare` (with `C_P = V_*^{2/3} C_S`), the positive spectral
floor `C_P⁻¹`, the Weyl counting law `eq:supp-global-weyl-count`, and the
compact-screen tail `eq:supp-screen-count-tail`. -/
theorem renewalSpatialPositiveScreen_of_efficientCut (u : V → V → ℝ)
    (D h Vstar aminus aplus Istar : ℝ)
    (hD : 0 < D) (hh : 0 < h) (hVstar : 0 < Vstar)
    (haminus : 0 ≤ aminus) (haplus : 0 < aplus)
    (hvolume : G.volume ≤ Vstar)
    (hdegree : ∀ v, h ^ 2 * (∑ x, G.conductance x v) ≤ D * G.mass v)
    (hlow : ∀ x y, aminus * (h * G.conductance x y) ≤ u x y)
    (hup : ∀ x y, u x y ≤ aplus * (h * G.conductance x y))
    (hIstar : 0 < Istar) (hI : Istar ≤ G.efficientCutConstant u) :
    0 < Istar / aplus ∧
    Istar / aplus ≤ G.spatialCutConstant h ∧
    ∃ S : G.RenewalSpatialPositiveScreen (Istar / aplus) D h Vstar,
      S.poincareConstant =
          128 * D * Vstar ^ ((2 : ℝ) / 3) / (Istar / aplus) ^ 2 ∧
      S.spectralFloor =
          (Istar / aplus) ^ 2 / (128 * D * Vstar ^ ((2 : ℝ) / 3)) := by
  have hhc : ∀ x y, 0 ≤ h * G.conductance x y := fun x y =>
    mul_nonneg hh.le (G.conductance_nonneg x y)
  have hu : ∀ x y, 0 ≤ u x y := fun x y =>
    le_trans (mul_nonneg haminus (hhc x y)) (hlow x y)
  have hIpos : 0 < Istar / aplus := div_pos hIstar haplus
  have hsp : Istar / aplus ≤ G.spatialCutConstant h :=
    G.spatialCutConstant_ge_of_efficient u h aplus Istar hh.le haplus hu hup hI
  refine ⟨hIpos, hsp, ?_⟩
  exact G.renewalSpatialPositiveScreen D h Vstar hD hh hVstar hvolume hdegree
    (G.spatialCutMargin_of_le h (Istar / aplus) hh.le hIpos hsp)

/-! ### The neck obstruction witness -/

/-- The mean-zero cut demand `b_A` of `eq:main-cut-demand`. -/
def cutDemand (A : Finset V) (v : V) : ℝ :=
  G.setMass A ^ ((2 : ℝ) / 3) *
    (G.mass v * cutIndicator A v / G.setMass A -
      G.mass v * cutIndicator Aᶜ v / G.setMass Aᶜ)

/-- The normalized cut potential `φ = 1_A / u(∂A)`. -/
def neckPotential (u : V → V → ℝ) (A : Finset V) (v : V) : ℝ :=
  cutIndicator A v / finiteCutCapacity u A

omit [Nonempty V] in
/-- The neck witness: for a half-volume cut `A` with positive efficient
capacity, `φ = 1_A/u(∂A)` has total `u`-variation
`(1/2) Σ_{x,y} u_xy |φ(x) - φ(y)| = 1` (the ordered-pair form of
`Σ_e u_e |dφ(e)| = 1`) and pairs with the demand to
`|Σ_v b_A(v) φ(v)| = μ(A)^{2/3}/u(∂A) = (u(∂A)/μ(A)^{2/3})⁻¹`. -/
theorem neck_witness (u : V → V → ℝ) (hsym : ∀ x y, u x y = u y x)
    (A : Finset V) (hA : G.IsHalfVolumeCut A)
    (hcap : 0 < finiteCutCapacity u A) :
    (1 / 2) * ∑ x, ∑ y, u x y *
        |neckPotential u A x - neckPotential u A y| = 1 ∧
      |∑ v, G.cutDemand A v * neckPotential u A v| =
        (G.cutRatio u A)⁻¹ := by
  constructor
  · have hvar := cutIndicator_weightedVariation u hsym A
    have hrw : ∀ x y, u x y * |neckPotential u A x - neckPotential u A y|
        = (u x y * |cutIndicator A x - cutIndicator A y|) /
          finiteCutCapacity u A := by
      intro x y
      unfold neckPotential
      rw [← sub_div, abs_div, abs_of_pos hcap]
      ring
    simp_rw [hrw, ← Finset.sum_div, hvar]
    field_simp
  · have hpair : ∑ v, G.cutDemand A v * neckPotential u A v =
        G.setMass A ^ ((2 : ℝ) / 3) / finiteCutCapacity u A := by
      unfold cutDemand neckPotential
      have hterm : ∀ v, G.setMass A ^ ((2 : ℝ) / 3) *
          (G.mass v * cutIndicator A v / G.setMass A -
            G.mass v * cutIndicator Aᶜ v / G.setMass Aᶜ) *
          (cutIndicator A v / finiteCutCapacity u A) =
          if v ∈ A then G.setMass A ^ ((2 : ℝ) / 3) / finiteCutCapacity u A *
            (G.mass v / G.setMass A) else 0 := by
        intro v
        by_cases hv : v ∈ A
        · have hvc : v ∉ Aᶜ := fun h => (Finset.mem_compl.mp h) hv
          simp only [cutIndicator, hv, hvc, ite_true, ite_false]
          ring
        · simp only [cutIndicator, hv, ite_false]
          ring
      simp_rw [hterm]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
        ← Finset.sum_div]
      have hA0 : G.setMass A ≠ 0 := hA.1.ne'
      unfold setMass at hA0 ⊢
      rw [div_self hA0, mul_one]
    rw [hpair, abs_of_nonneg (div_nonneg (Real.rpow_nonneg (G.setMass_nonneg A) _)
      hcap.le)]
    unfold cutRatio
    rw [inv_div]

/-- For a minimizing half-volume cut of positive capacity, the neck witness
pairs to exactly `(I^eff)⁻¹` (`eq:main-neck-obstruction`). -/
theorem neck_witness_of_minimizing_cut (u : V → V → ℝ)
    (hsym : ∀ x y, u x y = u y x) (hu : ∀ x y, 0 ≤ u x y)
    (hne : ∃ A, G.IsHalfVolumeCut A) (hIeff : 0 < G.efficientCutConstant u) :
    ∃ A, G.IsHalfVolumeCut A ∧ 0 < finiteCutCapacity u A ∧
      (1 / 2) * ∑ x, ∑ y, u x y *
          |neckPotential u A x - neckPotential u A y| = 1 ∧
      |∑ v, G.cutDemand A v * neckPotential u A v| =
        (G.efficientCutConstant u)⁻¹ := by
  obtain ⟨A, hA, hAeq⟩ := G.exists_minimizing_cut u hne
  have hratio : 0 < G.cutRatio u A := by
    rw [hAeq]
    exact hIeff
  have hcap : 0 < finiteCutCapacity u A := by
    by_contra hcontra
    have h0 : finiteCutCapacity u A = 0 :=
      le_antisymm (not_lt.mp hcontra) (finiteCutCapacity_nonneg u hu A)
    unfold cutRatio at hratio
    rw [h0, zero_div] at hratio
    exact lt_irrefl _ hratio
  obtain ⟨h1, h2⟩ := G.neck_witness u hsym A hA hcap
  refine ⟨A, hA, hcap, h1, ?_⟩
  rw [h2, hAeq]
  rfl

end FiniteWeightedGraph

/-- Along any family with positive cut constants tending to zero, the neck
witnesses `(I^eff)⁻¹` tend to `+∞` (`eq:main-neck-obstruction`). -/
theorem tendsto_inv_atTop_of_tendsto_zero {ι : Type*} {l : Filter ι}
    (I : ι → ℝ) (hpos : ∀ᶠ j in l, 0 < I j)
    (hzero : Filter.Tendsto I l (𝓝 0)) :
    Filter.Tendsto (fun j => (I j)⁻¹) l Filter.atTop := by
  have : Filter.Tendsto I l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  exact this.inv_tendsto_nhdsGT_zero

end RenewalGeometry
